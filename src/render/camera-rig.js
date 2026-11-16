// Perspective + top-down orthographic cameras with OrbitControls, mode switching and animated fit.
import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';

/** World height visible through the orthographic camera at zoom 1. */
export const ORTHO_FRUSTUM_H = 20;
const ORTHO_HEIGHT = 200;
const FIT_MS = 350;
const FOV = 40;

const _v = new THREE.Vector3();
const _right = new THREE.Vector3();
const _up = new THREE.Vector3();
const _fwd = new THREE.Vector3();
const _corner = new THREE.Vector3();
const WORLD_UP = new THREE.Vector3(0, 1, 0);

function easeOutCubic(t) { return 1 - Math.pow(1 - t, 3); }

export class CameraRig {
  /**
   * @param {HTMLElement} dom element receiving pointer events (the canvas)
   * @param {() => void} onChange called whenever a camera moved
   */
  constructor(dom, onChange) {
    this.onChange = onChange;
    this.aspect = 1;
    this.mode = 'perspective';
    /** @type {null|object} */ this.tween = null;
    this.lastDir = new THREE.Vector3(0, 0.78, 0.62).normalize();

    this.persp = new THREE.PerspectiveCamera(FOV, 1, 0.1, 2000);
    this.persp.position.set(0, 19, 15);

    this.ortho = new THREE.OrthographicCamera(-10, 10, 10, -10, 0.1, 2000);
    this.ortho.up.set(0, 0, -1);
    this.ortho.position.set(0, ORTHO_HEIGHT, 0);

    this.cp = new OrbitControls(this.persp, dom);
    this.cp.enableDamping = true;
    this.cp.dampingFactor = 0.12;
    this.cp.maxPolarAngle = Math.PI / 2 - 0.04;
    this.cp.minPolarAngle = 0.04;
    this.cp.minDistance = 2;
    this.cp.maxDistance = 600;
    this.cp.screenSpacePanning = true;
    this.cp.mouseButtons = { LEFT: THREE.MOUSE.ROTATE, MIDDLE: THREE.MOUSE.DOLLY, RIGHT: THREE.MOUSE.PAN };

    this.co = new OrbitControls(this.ortho, dom);
    this.co.enableDamping = true;
    this.co.dampingFactor = 0.12;
    this.co.enableRotate = false;
    this.co.screenSpacePanning = true;
    this.co.minZoom = 0.04;
    this.co.maxZoom = 40;
    this.co.mouseButtons = { LEFT: THREE.MOUSE.PAN, MIDDLE: THREE.MOUSE.DOLLY, RIGHT: THREE.MOUSE.PAN };
    this.co.touches = { ONE: THREE.TOUCH.PAN, TWO: THREE.TOUCH.DOLLY_PAN };
    this.co.enabled = false;

    this._change = () => this.onChange();
    this._start = () => { this.tween = null; };
    for (const c of [this.cp, this.co]) {
      c.addEventListener('change', this._change);
      c.addEventListener('start', this._start);
    }
    this.userEnabled = true;
  }

  get camera() { return this.mode === 'top' ? this.ortho : this.persp; }
  get controls() { return this.mode === 'top' ? this.co : this.cp; }

  /** Enable or disable user navigation (disabled during node drags). */
  setUserEnabled(on) {
    this.userEnabled = on;
    this.controls.enabled = on;
  }

  setSize(w, h) {
    this.aspect = w / Math.max(1, h);
    this.persp.aspect = this.aspect;
    this.persp.updateProjectionMatrix();
    const half = ORTHO_FRUSTUM_H / 2;
    this.ortho.left = -half * this.aspect;
    this.ortho.right = half * this.aspect;
    this.ortho.top = half;
    this.ortho.bottom = -half;
    this.ortho.updateProjectionMatrix();
    this.onChange();
  }

  /** Per-frame: advance a running tween, apply damping. */
  update(now) {
    if (this.tween) this._stepTween(now);
    this.controls.update();
  }

  _stepTween(now) {
    const tw = this.tween;
    const p = Math.min(1, (now - tw.t0) / FIT_MS);
    const e = easeOutCubic(p);
    const c = this.controls;
    c.target.lerpVectors(tw.fromTarget, tw.toTarget, e);
    if (tw.toZoom !== undefined) this.ortho.zoom = tw.fromZoom + (tw.toZoom - tw.fromZoom) * e;
    if (tw.toPos) this.persp.position.lerpVectors(tw.fromPos, tw.toPos, e);
    if (tw.toZoom !== undefined) {
      this.ortho.position.set(c.target.x, ORTHO_HEIGHT, c.target.z);
      this.ortho.updateProjectionMatrix();
    }
    if (p >= 1) this.tween = null;
    c.update();
    this.onChange();
  }

  setMode(mode) {
    const next = mode === 'top' ? 'top' : 'perspective';
    if (next === this.mode) return;
    this.tween = null;
    const half = Math.tan(THREE.MathUtils.degToRad(FOV / 2));
    if (next === 'top') {
      const target = this.cp.target.clone();
      _v.copy(this.persp.position).sub(target);
      const dist = Math.max(0.5, _v.length());
      this.lastDir.copy(_v).normalize();
      const visibleH = 2 * dist * half;
      this.ortho.zoom = THREE.MathUtils.clamp(ORTHO_FRUSTUM_H / visibleH, this.co.minZoom, this.co.maxZoom);
      this.ortho.updateProjectionMatrix();
      this.ortho.position.set(target.x, ORTHO_HEIGHT, target.z);
      this.co.target.copy(target);
      this.cp.enabled = false;
      this.mode = 'top';
      this.co.enabled = this.userEnabled;
      this.co.update();
    } else {
      const target = this.co.target.clone();
      const visibleH = ORTHO_FRUSTUM_H / this.ortho.zoom;
      const dist = THREE.MathUtils.clamp(visibleH / (2 * half), this.cp.minDistance, this.cp.maxDistance);
      if (this.lastDir.y < 0.1) this.lastDir.set(0, 0.78, 0.62).normalize();
      this.persp.position.copy(target).addScaledVector(this.lastDir, dist);
      this.cp.target.copy(target);
      this.co.enabled = false;
      this.mode = 'perspective';
      this.cp.enabled = this.userEnabled;
      this.cp.update();
    }
    this.onChange();
  }

  /**
   * Frame a world-space box.
   * @param {THREE.Box3} box
   * @param {boolean} animate
   */
  fitBox(box, animate) {
    if (box.isEmpty()) return;
    const center = box.getCenter(new THREE.Vector3());
    const c = this.controls;
    const tw = { t0: performance.now(), fromTarget: c.target.clone(), toTarget: center };
    if (this.mode === 'top') {
      const size = box.getSize(_v);
      const visibleH = Math.max(size.z, size.x / this.aspect) * 1.15 + 1;
      tw.fromZoom = this.ortho.zoom;
      tw.toZoom = THREE.MathUtils.clamp(ORTHO_FRUSTUM_H / visibleH, this.co.minZoom, this.co.maxZoom);
    } else {
      _fwd.copy(c.target).sub(this.persp.position).normalize().multiplyScalar(1);
      if (_fwd.lengthSq() < 1e-6) _fwd.set(0, -0.78, -0.62).normalize();
      _right.crossVectors(_fwd, WORLD_UP);
      if (_right.lengthSq() < 1e-6) _right.set(1, 0, 0);
      _right.normalize();
      _up.crossVectors(_right, _fwd).normalize();
      const tanV = Math.tan(THREE.MathUtils.degToRad(FOV / 2));
      const tanH = tanV * this.aspect;
      // Smallest distance at which every corner of the box is inside the frustum.
      let need = 0;
      for (let i = 0; i < 8; i++) {
        _corner.set(i & 1 ? box.max.x : box.min.x, i & 2 ? box.max.y : box.min.y, i & 4 ? box.max.z : box.min.z).sub(center);
        const depth = _corner.dot(_fwd);
        need = Math.max(need, Math.abs(_corner.dot(_right)) / tanH - depth, Math.abs(_corner.dot(_up)) / tanV - depth);
      }
      const dist = THREE.MathUtils.clamp(need * 1.1 + 1, 4, this.cp.maxDistance);
      tw.fromPos = this.persp.position.clone();
      tw.toPos = center.clone().addScaledVector(_fwd, -dist);
    }
    if (animate) {
      this.tween = tw;
      this.onChange();
    } else {
      tw.t0 = -1e9;
      this.tween = tw;
      this._stepTween(performance.now());
    }
  }

  getState() {
    const cam = this.camera;
    const t = this.controls.target;
    return {
      mode: this.mode,
      position: [cam.position.x, cam.position.y, cam.position.z],
      target: [t.x, t.y, t.z],
      zoom: this.mode === 'top' ? this.ortho.zoom : this.persp.zoom,
    };
  }

  setState(s) {
    if (!s || typeof s !== 'object') return;
    this.tween = null;
    if (s.mode === 'top' || s.mode === 'perspective') this.setMode(s.mode);
    const c = this.controls;
    if (Array.isArray(s.target)) c.target.set(s.target[0], s.target[1], s.target[2]);
    if (Array.isArray(s.position)) this.camera.position.set(s.position[0], s.position[1], s.position[2]);
    if (typeof s.zoom === 'number' && s.zoom > 0) {
      this.camera.zoom = s.zoom;
      this.camera.updateProjectionMatrix();
    }
    c.update();
    this.onChange();
  }

  dispose() {
    for (const c of [this.cp, this.co]) {
      c.removeEventListener('change', this._change);
      c.removeEventListener('start', this._start);
      c.dispose();
    }
  }
}
