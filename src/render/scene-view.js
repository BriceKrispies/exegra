// Three.js renderer for Exegra scenes. A pure function of (scene, placement, selection,
// highlight, camera): it holds no domain state. See docs/module-contracts.md "Renderer".
import * as THREE from 'three';
import { CSS2DRenderer, CSS2DObject } from 'three/addons/renderers/CSS2DRenderer.js';
import { Line2 } from 'three/addons/lines/Line2.js';
import { LineMaterial } from 'three/addons/lines/LineMaterial.js';
import { LineGeometry } from 'three/addons/lines/LineGeometry.js';
import { readPalette, lighten, darken } from './palette.js';
import { GeometryCache, shapeSpec, shapeTop, shapePickY, SLAB_T, LEVEL_DY } from './geometry.js';
import { arcCurve, loopCurve, POINTS } from './curves.js';
import { CameraRig } from './camera-rig.js';
import { createLabelParts, setLabelText, layoutLabels } from './labels.js';

const MOVE_ANIM_MS = 220;
const CLICK_PX = 4;
/** A finger moves more than a mouse during a tap. */
const TAP_PX_TOUCH = 10;
/** A finger has to rest this long on a node before dragging it moves the node rather than the camera. */
const TOUCH_HOLD_MS = 350;
const EDGE_PULSE_MS = 600;
/** How long one message takes to travel from its sender to its receiver. */
const FLOW_MS = 1400;
/**
 * A message's clock advances by at most this much per rendered frame, so it is drawn in at least
 * FLOW_MS / FLOW_FRAME_MS frames: where frames are slow (software rendering of a large scene) the
 * message travels more slowly instead of vanishing after a handful of frames, before it can be read.
 */
const FLOW_FRAME_MS = FLOW_MS / 24;
const NODE_PULSE_MS = 520;
const CLUTTER_MS = 120;
const CONTAINER_DRAG_BAND = 0.5;
const ACTIVE_RAISE = 0.08;
const PARALLEL_GAP = 0.3;
const DEFAULT_PLACEMENT = { x: 0, z: 0, w: 2.6, d: 1.6, level: 0 };

const ARROW_UP = new THREE.Vector3(0, 1, 0);
const _p = new THREE.Vector3();
const _q = new THREE.Quaternion();
const _tanV = new THREE.Vector3();

const easeOutCubic = (t) => 1 - Math.pow(1 - t, 3);

/**
 * @typedef {Object} SceneCallbacks
 * @property {(id:string|null)=>void} [onSelect]
 * @property {(id:string|null)=>void} [onHover]
 * @property {(id:string)=>void} [onActivate]
 * @property {(moves:{id:string,x:number,z:number}[])=>void} [onMoveEnd]
 * @property {(from:string,to:string)=>void} [onConnect]
 */

/**
 * Create the scene view inside `host`.
 * @param {HTMLElement} host positioned block element; filled with the canvas and the label layer
 * @param {SceneCallbacks} callbacks
 */
export function createSceneView(host, callbacks = {}) {
  const cb = {
    onSelect() {}, onHover() {}, onActivate() {}, onMoveEnd() {}, onConnect() {},
    ...callbacks,
  };
  const palette = readPalette();
  const redColor = palette.role('red');
  const accentColor = palette.accent;

  // ---------------------------------------------------------------- DOM / GL
  if (getComputedStyle(host).position === 'static') host.style.position = 'relative';
  host.style.overflow = 'hidden';

  const renderer = new THREE.WebGLRenderer({ antialias: true, powerPreference: 'high-performance' });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
  const canvas = renderer.domElement;
  canvas.setAttribute('role', 'img');
  canvas.setAttribute('aria-label', 'Architecture scene; use the explorer and inspector panels for a non-visual equivalent');
  canvas.dataset.testid = 'scene-canvas';
  canvas.style.display = 'block';
  host.appendChild(canvas);

  const css = new CSS2DRenderer();
  const layer = css.domElement;
  layer.classList.add('scene-labels');
  layer.style.position = 'absolute';
  layer.style.left = '0';
  layer.style.top = '0';
  layer.style.pointerEvents = 'none';
  host.appendChild(layer);

  const scene = new THREE.Scene();
  scene.background = palette.surface.clone();
  scene.matrixWorldAutoUpdate = false;

  scene.add(new THREE.HemisphereLight(0xdfe6f0, 0x2a2f37, 1.5));
  const key = new THREE.DirectionalLight(0xffffff, 1.9);
  key.position.set(-8, 16, 10);
  scene.add(key);

  const grid = new THREE.GridHelper(240, 240, palette.grid2, palette.grid1);
  grid.position.y = -0.01;
  grid.material.transparent = true;
  grid.material.opacity = 0.8;
  scene.add(grid);

  // ------------------------------------------------------------------ state
  const geoms = new GeometryCache();
  /** @type {Map<string, THREE.Material>} */
  const matCache = new Map();
  /** @type {Set<LineMaterial>} */
  const lineMats = new Set();
  const colorCache = new Map();
  let width = 1;
  let height = 1;

  /** @type {Map<string, any>} */ const nodes = new Map();
  /** @type {Map<string, any>} */ const edges = new Map();
  const animating = new Set();
  const dirtyEdges = new Set();
  const pulsingNodes = new Set();
  /** @type {{es:any, t0:number, mesh:THREE.Mesh}[]} */ let edgePulses = [];
  /**
   * Messages in flight: a marker carrying the event's name, moving along a scene
   * edge, or along a straight segment for a message from outside, one with no
   * declared relationship, or one that was dropped.
   * @type {{kind:string, event:string, from:string|null, to:string|null, t0:number, mesh:THREE.Mesh, label:any, es?:any, reverse?:boolean, a?:THREE.Vector3, b?:THREE.Vector3}[]}
   */
  let flows = [];

  let selSet = new Set();
  let hlActive = false;
  let hlSet = new Set();
  let hoverNs = null;
  let hoverEs = null;
  let mode = 'select';
  let connectSource = null;

  let renderDirty = true;
  let matricesDirty = true;
  let labelsDirty = true;
  let needMeasure = true;
  let listsDirty = true;
  let lastClutter = -1e9;
  let visibleLabels = 0;
  let bodyList = [];
  let edgeList = [];
  let labelItems = [];
  let raf = 0;
  let disposed = false;

  let fpsAvg = 0;
  let frameMsAvg = 0;
  let lastRenderT = 0;

  const rig = new CameraRig(canvas, () => { renderDirty = true; labelsDirty = true; });

  const touch = () => { renderDirty = true; matricesDirty = true; labelsDirty = true; };
  const ensureMatrices = () => {
    if (matricesDirty) { scene.updateMatrixWorld(); matricesDirty = false; }
  };

  // -------------------------------------------------------------- materials
  function cached(k, make) {
    let m = matCache.get(k);
    if (!m) { m = make(); matCache.set(k, m); }
    return m;
  }

  const EMISSIVE = {
    hover: [new THREE.Color(1, 1, 1), 0.1],
    selected: [accentColor, 0.28],
    active: [accentColor, 0.2],
    violated: [redColor, 0.18],
    pulse: [accentColor, 0.45],
  };

  function bodyMaterial(role, op, emph, slab) {
    return cached(`b|${slab ? 1 : 0}|${role}|${op}|${emph}`, () => {
      const m = new THREE.MeshStandardMaterial({ roughness: 0.8, metalness: 0.05 });
      if (slab) {
        m.color.copy(palette.body(role)).lerp(palette.surface, 0.35);
        m.transparent = true;
        m.depthWrite = false;
        const base = emph === 'selected' || emph === 'pulse' ? 0.3 : emph === 'hover' ? 0.24 : 0.18;
        m.opacity = base * op;
        m.roughness = 1;
      } else {
        m.color.copy(palette.body(role));
        const em = EMISSIVE[emph];
        if (em) { m.emissive.copy(em[0]); m.emissiveIntensity = em[1]; }
        if (op < 1) { m.transparent = true; m.opacity = op; }
      }
      return m;
    });
  }

  function outlineColor(role, emph, slab) {
    switch (emph) {
      case 'selected': case 'active': case 'pulse': return accentColor;
      case 'violated': return redColor;
      case 'hover': return lighten(palette.raw[role] ?? palette.raw.neutral, 0.55);
      default: return slab ? lighten(palette.line(role), 0.05) : darken(palette.body(role), 0.55);
    }
  }

  function outlineMaterial(role, op, emph, slab) {
    return cached(`o|${slab ? 1 : 0}|${role}|${op}|${emph}`, () => {
      const o = slab && emph === 'none' ? 0.75 * op : op;
      return new THREE.LineBasicMaterial({ color: outlineColor(role, emph, slab).clone(), transparent: o < 1, opacity: o });
    });
  }

  function makeLineMaterial(params, color) {
    const m = new LineMaterial(params);
    m.color = color.clone();
    m.resolution.set(width, height);
    lineMats.add(m);
    return m;
  }

  function ringMaterial(kind, op) {
    return cached(`r|${kind}|${op}`, () => makeLineMaterial(
      { linewidth: 2.5, transparent: op < 1, opacity: op },
      kind === 'red' ? redColor : accentColor,
    ));
  }

  function edgeColor(role, status, bright) {
    const k = `${role}|${status ?? ''}|${bright}`;
    let c = colorCache.get(k);
    if (!c) {
      let base = palette.line(role);
      if (status === 'violated') base = redColor.clone();
      else if (status === 'active') base = accentColor.clone();
      c = bright ? lighten(base, bright) : base;
      colorCache.set(k, c);
    }
    return c;
  }

  function edgeMaterial(color, line, w, op) {
    return cached(`e|${color.getHexString()}|${line}|${w}|${op}`, () => {
      const dashed = line === 'dashed' || line === 'dotted';
      const dotted = line === 'dotted';
      return makeLineMaterial({
        linewidth: w,
        dashed,
        dashSize: dotted ? 0.08 : 0.35,
        gapSize: dotted ? 0.14 : 0.2,
        transparent: op < 1,
        opacity: op,
      }, color);
    });
  }

  function arrowMaterial(color, op) {
    return cached(`a|${color.getHexString()}|${op}`, () => new THREE.MeshBasicMaterial({
      color: color.clone(), transparent: op < 1, opacity: op,
    }));
  }

  const markerMaterial = new THREE.MeshBasicMaterial({ color: accentColor.clone() });
  const flowMaterial = new THREE.MeshBasicMaterial({ color: accentColor.clone() });
  const undeclaredFlowMaterial = new THREE.MeshBasicMaterial({ color: redColor.clone() });
  const previewMaterial = makeLineMaterial({ linewidth: 2, dashed: true, dashSize: 0.3, gapSize: 0.18 }, accentColor);

  // ------------------------------------------------------------ id helpers
  function resolveNode(id) {
    if (id == null) return null;
    const n = nodes.get(id);
    if (n) return n;
    for (const ns of nodes.values()) if (ns.node.entityId === id) return ns;
    return null;
  }
  function resolveEdge(id) {
    if (id == null) return null;
    const e = edges.get(id);
    if (e) return e;
    for (const es of edges.values()) if (es.edge.entityId === id) return es;
    return null;
  }
  const nodeEntity = (ns) => ns.node.entityId ?? ns.id;
  const edgeEntity = (es) => es.edge.entityId ?? es.id;
  const hitEntity = (hit) => (hit.kind === 'node' ? nodeEntity(hit.ns) : edgeEntity(hit.es));

  const isSel = (id, entityId) => selSet.has(id) || (entityId != null && selSet.has(entityId));

  // ------------------------------------------------------------------ nodes
  const nodeSig = (n) => JSON.stringify([
    n.shape, n.color, n.label, n.sublabel ?? '', n.status ?? '', !!n.dimmed, n.badges ?? [],
    n.parent ?? null, !!n.container, !!n.collapsed, n.entityId ?? '',
  ]);

  function setBodyShape(ns) {
    const slab = ns.node.shape === 'container';
    ns.slab = slab;
    ns.body.geometry = geoms.shape(ns.node.shape);
    if (ns.outline) { ns.body.remove(ns.outline); ns.outline = null; }
    const eg = geoms.edges(ns.node.shape);
    if (eg) {
      ns.outline = new THREE.LineSegments(eg, outlineMaterial('neutral', 1, 'none', slab));
      ns.body.add(ns.outline);
    }
    ns.visKey = '';
    ns.label.center.set(slab ? 0 : 0.5, 1);
    ns.labelItem.container = slab;
  }

  function createNode(node, p) {
    const ns = {
      id: node.id,
      node,
      sig: nodeSig(node),
      slab: false,
      group: new THREE.Group(),
      body: new THREE.Mesh(geoms.shape('box'), bodyMaterial('neutral', 1, 'none', false)),
      outline: null,
      parts: createLabelParts(node.entityId ?? node.id),
      label: null,
      labelItem: null,
      labelCls: '',
      labelHidden: false,
      cur: { x: p.x, z: p.z, w: p.w, d: p.d },
      want: { x: p.x, z: p.z, w: p.w, d: p.d },
      anim: null,
      level: p.level ?? 0,
      baseY: 0,
      raise: 0,
      top: 0,
      parentId: node.parent ?? null,
      children: [],
      edges: new Set(),
      visKey: '',
      emph: 'none',
      hl: true,
      ringSel: null,
      ringBad: null,
      pulseT0: -1,
      placeDirty: true,
    };
    ns.body.userData.ns = ns;
    ns.group.add(ns.body);
    ns.label = new CSS2DObject(ns.parts.el);
    ns.group.add(ns.label);
    ns.labelItem = { obj: ns.label, group: 4, force: false, container: false, size: 1, w: 0, h: 0, show: true, dist: 0, sx: 0, sy: 0 };
    setBodyShape(ns);
    setLabelText(ns.parts, node);
    scene.add(ns.group);
    return ns;
  }

  function updateNode(ns, node) {
    const shapeChanged = ns.node.shape !== node.shape;
    ns.node = node;
    ns.sig = nodeSig(node);
    ns.parentId = node.parent ?? null;
    ns.parts.el.dataset.entityId = node.entityId ?? node.id;
    if (setLabelText(ns.parts, node)) { ns.labelItem.w = 0; needMeasure = true; }
    if (shapeChanged) setBodyShape(ns);
    ns.visKey = '';
    ns.placeDirty = true;
  }

  function disposeNode(ns) {
    ns.group.remove(ns.label);
    scene.remove(ns.group);
    animating.delete(ns);
    pulsingNodes.delete(ns);
    for (const es of ns.edges) dirtyEdges.delete(es);
    if (hoverNs === ns) hoverNs = null;
    if (connectSource === ns.id) connectSource = null;
    if (drag && drag.ns === ns) drag = null;
  }

  function nodeSelected(ns) {
    return isSel(ns.id, ns.node.entityId) || connectSource === ns.id;
  }
  function nodeOpacity(ns) {
    let o = ns.node.dimmed ? 0.25 : 1;
    if (hlActive && !ns.hl) o = Math.min(o, 0.2);
    return o;
  }
  function nodeEmphasis(ns) {
    if (ns.pulseT0 >= 0) return 'pulse';
    if (nodeSelected(ns)) return 'selected';
    if (ns.node.status === 'violated') return 'violated';
    if (ns.node.status === 'active') return 'active';
    if (hoverNs === ns) return 'hover';
    return 'none';
  }

  function ensureRing(ns, which, on, op) {
    const prop = which === 'sel' ? 'ringSel' : 'ringBad';
    let ring = ns[prop];
    if (!on) {
      if (ring) ring.visible = false;
      return;
    }
    if (!ring) {
      ring = new Line2(geoms.unitRect, ringMaterial(which === 'sel' ? 'accent' : 'red', 1));
      ring.frustumCulled = false;
      ring.position.y = 0.02;
      ns.group.add(ring);
      ns[prop] = ring;
      ns.placeDirty = true;
    }
    ring.visible = true;
    ring.material = ringMaterial(which === 'sel' ? 'accent' : 'red', op);
  }

  function updateLabelClass(ns) {
    let cls = 'scene-label';
    if (ns.slab) cls += ' scene-label--container';
    if (nodeSelected(ns)) cls += ' scene-label--selected';
    if (ns.node.dimmed || (hlActive && !ns.hl)) cls += ' scene-label--dimmed';
    if (ns.node.status) cls += ` scene-label--status-${ns.node.status}`;
    if (ns.labelHidden) cls += ' scene-label--hidden';
    if (cls !== ns.labelCls) { ns.labelCls = cls; ns.parts.el.className = cls; }
  }

  function refreshNode(ns) {
    const op = nodeOpacity(ns);
    const emph = nodeEmphasis(ns);
    ns.emph = emph;
    const raise = !ns.slab && ns.node.status === 'active' ? ACTIVE_RAISE : 0;
    if (raise !== ns.raise) { ns.raise = raise; ns.placeDirty = true; }
    const k = `${ns.node.color}|${op}|${emph}`;
    if (k !== ns.visKey) {
      ns.visKey = k;
      ns.body.material = bodyMaterial(ns.node.color, op, emph, ns.slab);
      if (ns.outline) ns.outline.material = outlineMaterial(ns.node.color, op, emph, ns.slab);
    }
    ensureRing(ns, 'sel', nodeSelected(ns), op);
    ensureRing(ns, 'bad', ns.node.status === 'violated', op);
    updateLabelClass(ns);
    if (ns.placeDirty) placeNode(ns);
  }

  /** Apply `cur` to the node's objects. */
  function placeNode(ns) {
    ns.placeDirty = false;
    const c = ns.cur;
    const g = ns.group;
    g.position.set(c.x, ns.baseY + ns.raise, c.z);
    if (ns.slab) {
      ns.body.scale.set(c.w, SLAB_T, c.d);
      ns.body.position.y = 0;
      ns.body.rotation.x = 0;
      ns.label.position.set(-c.w / 2 + 0.05, SLAB_T + 0.02, -c.d / 2 + 0.02);
      ns.top = ns.baseY + SLAB_T;
    } else {
      const spec = shapeSpec(ns.node.shape);
      const dims = spec.dims(c.w, c.d);
      ns.body.scale.set(dims[0], dims[1], dims[2]);
      ns.body.position.y = spec.lift ?? 0;
      ns.body.rotation.x = spec.tilt ?? 0;
      const top = shapeTop(ns.node.shape, c.w, c.d);
      ns.top = ns.baseY + ns.raise + top;
      ns.label.position.set(0, top + 0.1, 0);
    }
    ns.labelItem.size = c.w;
    for (const r of [ns.ringSel, ns.ringBad]) if (r) r.scale.set(c.w + 0.2, 1, c.d + 0.2);
    for (const es of ns.edges) dirtyEdges.add(es);
    matricesDirty = true;
    renderDirty = true;
    labelsDirty = true;
  }

  // ------------------------------------------------------------------ edges
  function lineStyle(es) {
    return es.edge.line === 'dashed' || es.edge.line === 'dotted';
  }

  function createEdge(edge, a, b) {
    const es = {
      id: edge.id,
      edge,
      a, b,
      self: edge.from === edge.to,
      sig: '',
      pts: new Float32Array(POINTS * 3),
      tan: [0, 1, 0],
      idx: 0,
      count: 1,
      lateral: 0,
      flip: false,
      geom: new LineGeometry(),
      line: null,
      arrow: null,
      labelObj: null,
      matKey: '',
      sel: false,
      inc: false,
      hl: true,
    };
    es.geom.setPositions(es.pts);
    es.line = new Line2(es.geom, edgeMaterial(palette.line('neutral'), 'solid', 2, 1));
    es.line.computeLineDistances();
    es.line.frustumCulled = false;
    es.line.userData.es = es;
    es.arrow = new THREE.Mesh(geoms.arrow, arrowMaterial(palette.line('neutral'), 1));
    es.arrow.frustumCulled = false;
    es.arrow.userData.es = es;
    scene.add(es.line, es.arrow);
    a.edges.add(es);
    b.edges.add(es);
    applyEdgeLabel(es);
    return es;
  }

  function applyEdgeLabel(es) {
    const text = es.edge.label;
    if (text && !es.labelObj) {
      const el = document.createElement('div');
      el.className = 'scene-edge-label';
      es.labelObj = new CSS2DObject(el);
      es.labelObj.visible = false;
      scene.add(es.labelObj);
    }
    if (es.labelObj) {
      es.labelObj.element.dataset.entityId = es.edge.entityId ?? es.id;
      es.labelObj.element.textContent = text ?? '';
    }
    if (!text && es.labelObj) {
      scene.remove(es.labelObj);
      es.labelObj = null;
    }
  }

  function disposeEdge(es) {
    scene.remove(es.line, es.arrow);
    es.geom.dispose();
    if (es.labelObj) scene.remove(es.labelObj);
    es.a.edges.delete(es);
    es.b.edges.delete(es);
    dirtyEdges.delete(es);
    edgePulses = edgePulses.filter((p) => { if (p.es === es) { scene.remove(p.mesh); return false; } return true; });
    flows = flows.filter((f) => { if (f.es === es) { endFlow(f); return false; } return true; });
    if (hoverEs === es) hoverEs = null;
  }

  const rectA = { x: 0, z: 0, w: 0, d: 0, top: 0 };
  const rectB = { x: 0, z: 0, w: 0, d: 0, top: 0 };
  function fillRect(r, ns) {
    r.x = ns.cur.x; r.z = ns.cur.z; r.w = ns.cur.w; r.d = ns.cur.d; r.top = ns.top;
  }

  function updateEdgeCurve(es) {
    fillRect(rectA, es.a);
    if (es.self) {
      loopCurve(es.pts, es.tan, rectA, es.idx);
    } else {
      fillRect(rectB, es.b);
      arcCurve(es.pts, es.tan, rectA, rectB, es.lateral, es.flip);
    }
    const geom = es.geom;
    const attr = geom.attributes.instanceStart;
    const arr = attr.data.array;
    const pts = es.pts;
    for (let i = 0; i < POINTS - 1; i++) {
      const o = i * 6;
      const s = i * 3;
      arr[o] = pts[s]; arr[o + 1] = pts[s + 1]; arr[o + 2] = pts[s + 2];
      arr[o + 3] = pts[s + 3]; arr[o + 4] = pts[s + 4]; arr[o + 5] = pts[s + 5];
    }
    attr.data.needsUpdate = true;
    geom.boundingSphere = null;
    geom.boundingBox = null;
    const ds = geom.attributes.instanceDistanceStart;
    if (ds) {
      const darr = ds.data.array;
      let acc = 0;
      for (let i = 0; i < POINTS - 1; i++) {
        const s = i * 3;
        const len = Math.hypot(pts[s + 3] - pts[s], pts[s + 4] - pts[s + 1], pts[s + 5] - pts[s + 2]);
        darr[i * 2] = acc;
        acc += len;
        darr[i * 2 + 1] = acc;
      }
      ds.data.needsUpdate = true;
    }
    const e = (POINTS - 1) * 3;
    es.arrow.position.set(pts[e], pts[e + 1], pts[e + 2]);
    _tanV.set(es.tan[0], es.tan[1], es.tan[2]);
    es.arrow.quaternion.copy(_q.setFromUnitVectors(ARROW_UP, _tanV));
    if (es.labelObj) {
      const m = Math.floor(POINTS / 2) * 3;
      es.labelObj.position.set(pts[m], pts[m + 1] + 0.1, pts[m + 2]);
    }
    matricesDirty = true;
    renderDirty = true;
  }

  function flushEdges() {
    if (!dirtyEdges.size) return;
    for (const es of dirtyEdges) updateEdgeCurve(es);
    dirtyEdges.clear();
  }

  function edgeOpacity(es) {
    // With something selected, the relationships of the selection stay at full
    // strength and the rest recede, so a dense scene stays readable.
    const focus = es.sel || es.inc || hoverEs === es || es.edge.status === 'violated' || es.edge.status === 'active';
    let o = focus ? 1 : selSet.size ? 0.28 : 0.8;
    if (es.edge.dimmed) o = Math.min(o, 0.25);
    if (hlActive && !es.hl) o = Math.min(o, 0.2);
    return o;
  }

  function refreshEdge(es) {
    const sel = isSel(es.id, es.edge.entityId);
    const inc = es.a.sel || es.b.sel;
    const hover = hoverEs === es;
    es.sel = sel;
    es.inc = inc;
    const bright = sel ? 0.35 : hover ? 0.3 : inc ? 0.3 : 0;
    const w = sel ? 3.5 : hover ? 3 : inc ? 2.6 : 1.7;
    const op = edgeOpacity(es);
    const color = edgeColor(es.edge.color, es.edge.status, bright);
    const k = `${color.getHexString()}|${es.edge.line}|${w}|${op}`;
    if (k !== es.matKey) {
      es.matKey = k;
      es.line.material = edgeMaterial(color, es.edge.line ?? 'solid', w, op);
      es.arrow.material = arrowMaterial(color, op);
    }
    if (es.labelObj) es.labelObj.visible = sel || hover;
  }

  function regroupEdges() {
    const groups = new Map();
    for (const es of edges.values()) {
      const k = es.self ? `s|${es.a.id}` : (es.a.id < es.b.id ? `${es.a.id}|${es.b.id}` : `${es.b.id}|${es.a.id}`);
      let list = groups.get(k);
      if (!list) { list = []; groups.set(k, list); }
      list.push(es);
    }
    for (const list of groups.values()) {
      list.sort((x, y) => (x.id < y.id ? -1 : x.id > y.id ? 1 : 0));
      const n = list.length;
      list.forEach((es, i) => {
        const lateral = es.self ? 0 : (i - (n - 1) / 2) * PARALLEL_GAP;
        const flip = !es.self && es.a.id > es.b.id;
        if (es.idx !== i || es.count !== n || es.lateral !== lateral || es.flip !== flip) {
          es.idx = i; es.count = n; es.lateral = lateral; es.flip = flip;
          dirtyEdges.add(es);
        }
      });
    }
  }

  // ------------------------------------------------------------- flags etc.
  function recomputeFlags() {
    for (const ns of nodes.values()) {
      ns.sel = nodeSelected(ns);
      ns.hl = !hlActive || hlSet.has(ns.id) || hlSet.has(ns.node.entityId);
    }
    for (const es of edges.values()) {
      es.hl = !hlActive || hlSet.has(es.id) || hlSet.has(es.edge.entityId) || (es.a.hl && es.b.hl);
    }
  }

  function refreshAll() {
    recomputeFlags();
    for (const ns of nodes.values()) refreshNode(ns);
    for (const es of edges.values()) refreshEdge(es);
    renderDirty = true;
    labelsDirty = true;
  }

  function rebuildLists() {
    if (!listsDirty) return;
    listsDirty = false;
    bodyList = [];
    labelItems = [];
    for (const ns of nodes.values()) { bodyList.push(ns.body); labelItems.push(ns.labelItem); }
    edgeList = [];
    for (const es of edges.values()) edgeList.push(es.line, es.arrow);
  }

  // --------------------------------------------------------------- setScene
  function setPlacement(ns, p, isNew, now) {
    ns.level = p.level ?? 0;
    const want = ns.want;
    want.x = p.x; want.z = p.z; want.w = p.w; want.d = p.d;
    if (isNew) {
      ns.cur.x = p.x; ns.cur.z = p.z; ns.cur.w = p.w; ns.cur.d = p.d;
      ns.anim = null;
      ns.placeDirty = true;
      return;
    }
    const cur = ns.cur;
    const same = (o) => Math.abs(o.x - p.x) < 1e-4 && Math.abs(o.z - p.z) < 1e-4
      && Math.abs(o.w - p.w) < 1e-4 && Math.abs(o.d - p.d) < 1e-4;
    if (ns.anim && same(ns.anim.to)) return;
    if (!ns.anim && same(cur)) return;
    ns.anim = {
      t0: now,
      from: { x: cur.x, z: cur.z, w: cur.w, d: cur.d },
      to: { x: p.x, z: p.z, w: p.w, d: p.d },
    };
    animating.add(ns);
    renderDirty = true;
  }

  function setScene(sceneModel, placement) {
    const now = performance.now();
    const wasEmpty = nodes.size === 0;
    const pl = placement ?? {};
    const seen = new Set();

    for (const node of sceneModel?.nodes ?? []) {
      seen.add(node.id);
      const p = pl[node.id] ?? nodes.get(node.id)?.want ?? DEFAULT_PLACEMENT;
      let ns = nodes.get(node.id);
      const isNew = !ns;
      if (isNew) {
        ns = createNode(node, p);
        nodes.set(node.id, ns);
        listsDirty = true;
      } else if (ns.sig !== nodeSig(node)) {
        updateNode(ns, node);
      }
      setPlacement(ns, { ...DEFAULT_PLACEMENT, ...p }, isNew, now);
    }
    for (const [id, ns] of nodes) {
      if (seen.has(id)) continue;
      // drop edges attached to the node first
      for (const es of [...ns.edges]) { disposeEdge(es); edges.delete(es.id); }
      disposeNode(ns);
      nodes.delete(id);
      listsDirty = true;
    }

    // hierarchy and vertical placement
    for (const ns of nodes.values()) ns.children.length = 0;
    for (const ns of nodes.values()) {
      ns.parentId = ns.node.parent ?? null;
      const parent = ns.parentId ? nodes.get(ns.parentId) : null;
      if (parent) parent.children.push(ns);
    }
    for (const ns of nodes.values()) {
      const parent = ns.parentId ? nodes.get(ns.parentId) : null;
      const base = ns.slab ? ns.level * LEVEL_DY : (parent ? parent.level * LEVEL_DY + SLAB_T : 0);
      if (base !== ns.baseY) { ns.baseY = base; ns.placeDirty = true; }
    }

    // edges
    const seenE = new Set();
    for (const edge of sceneModel?.edges ?? []) {
      const a = nodes.get(edge.from);
      const b = nodes.get(edge.to);
      if (!a || !b) continue;
      seenE.add(edge.id);
      const sig = JSON.stringify([edge.from, edge.to, edge.line, edge.color, edge.label ?? '', !!edge.lifted,
        edge.status ?? '', !!edge.dimmed, edge.entityId ?? '']);
      let es = edges.get(edge.id);
      if (es && (es.a !== a || es.b !== b)) { disposeEdge(es); edges.delete(edge.id); es = null; }
      if (!es) {
        es = createEdge(edge, a, b);
        es.sig = sig;
        edges.set(edge.id, es);
        listsDirty = true;
        dirtyEdges.add(es);
      } else if (es.sig !== sig) {
        es.sig = sig;
        es.edge = edge;
        es.matKey = '';
        applyEdgeLabel(es);
        dirtyEdges.add(es);
      }
    }
    for (const [id, es] of edges) {
      if (seenE.has(id)) continue;
      disposeEdge(es);
      edges.delete(id);
      listsDirty = true;
    }
    regroupEdges();

    for (const ns of nodes.values()) if (ns.placeDirty) placeNode(ns);
    refreshAll();
    needMeasure = true;
    touch();
    if (wasEmpty && nodes.size > 0) fit(null, false);
  }

  // -------------------------------------------------------------- animation
  function stepAnimations(now) {
    if (animating.size) {
      for (const ns of animating) {
        const a = ns.anim;
        if (!a) { animating.delete(ns); continue; }
        const p = Math.min(1, (now - a.t0) / MOVE_ANIM_MS);
        const e = easeOutCubic(p);
        const c = ns.cur;
        c.x = a.from.x + (a.to.x - a.from.x) * e;
        c.z = a.from.z + (a.to.z - a.from.z) * e;
        c.w = a.from.w + (a.to.w - a.from.w) * e;
        c.d = a.from.d + (a.to.d - a.from.d) * e;
        placeNode(ns);
        if (p >= 1) { ns.anim = null; animating.delete(ns); }
      }
    }
    if (pulsingNodes.size) {
      for (const ns of pulsingNodes) {
        if (now - ns.pulseT0 >= NODE_PULSE_MS) {
          ns.pulseT0 = -1;
          pulsingNodes.delete(ns);
          refreshNode(ns);
        }
      }
      renderDirty = true;
    }
    if (edgePulses.length) {
      flushEdges();
      const rest = [];
      for (const pl of edgePulses) {
        const u = (now - pl.t0) / EDGE_PULSE_MS;
        if (u >= 1) { scene.remove(pl.mesh); continue; }
        const f = Math.max(0, u) * (POINTS - 1);
        const i = Math.min(POINTS - 2, Math.floor(f));
        const t = f - i;
        const pts = pl.es.pts;
        pl.mesh.position.set(
          pts[i * 3] + (pts[i * 3 + 3] - pts[i * 3]) * t,
          pts[i * 3 + 1] + (pts[i * 3 + 4] - pts[i * 3 + 1]) * t,
          pts[i * 3 + 2] + (pts[i * 3 + 5] - pts[i * 3 + 2]) * t,
        );
        pl.mesh.visible = true;
        rest.push(pl);
      }
      edgePulses = rest;
      matricesDirty = true;
      renderDirty = true;
    }
    if (flows.length) {
      flushEdges();
      const rest = [];
      for (const fl of flows) {
        fl.elapsed += Math.min(FLOW_FRAME_MS, Math.max(0, now - fl.last));
        fl.last = now;
        const u = fl.elapsed / FLOW_MS;
        if (u >= 1) { endFlow(fl); continue; }
        const e = u < 0.5 ? 2 * u * u : 1 - (-2 * u + 2) ** 2 / 2;
        if (fl.es) {
          const f = (fl.reverse ? 1 - e : e) * (POINTS - 1);
          const i = Math.min(POINTS - 2, Math.floor(f));
          const t = f - i;
          const pts = fl.es.pts;
          fl.mesh.position.set(
            pts[i * 3] + (pts[i * 3 + 3] - pts[i * 3]) * t,
            pts[i * 3 + 1] + (pts[i * 3 + 4] - pts[i * 3 + 1]) * t,
            pts[i * 3 + 2] + (pts[i * 3 + 5] - pts[i * 3 + 2]) * t,
          );
        } else if (fl.a && fl.b) {
          fl.mesh.position.lerpVectors(fl.a, fl.b, e);
        }
        fl.mesh.visible = true;
        rest.push(fl);
      }
      flows = rest;
      matricesDirty = true;
      renderDirty = true;
    }
  }

  /** The middle of a node's body. */
  function nodeCentre(ns) {
    return new THREE.Vector3(ns.group.position.x, (ns.baseY + ns.top) / 2, ns.group.position.z);
  }

  function endFlow(fl) {
    fl.mesh.remove(fl.label);
    scene.remove(fl.mesh);
  }

  /**
   * Send markers along the paths of one message (see src/core/flows.js FlowPath).
   * @param {any[]} paths
   * @param {string} eventName shown next to the marker
   */
  function flow(paths, eventName) {
    const now = performance.now();
    // Only the current step's message is in flight: a new step replaces the previous one's markers,
    // so stepping quickly or playing never piles labels up.
    for (const f of flows) endFlow(f);
    flows = [];
    for (const p of paths ?? []) {
      if (p.kind === 'local') { pulse([p.node]); continue; }
      /** @type {any} */
      const item = { kind: p.kind, event: eventName, from: p.from ?? null, to: p.to ?? null, last: now, elapsed: 0 };
      if (p.kind === 'edge') {
        const es = resolveEdge(p.edgeId);
        if (!es) continue;
        item.es = es;
        item.reverse = p.reverse === true;
      } else {
        const a = p.from ? resolveNode(p.from) : null;
        const b = p.to ? resolveNode(p.to) : null;
        if (p.kind === 'enter') {
          if (!b) continue;
          item.b = nodeCentre(b);
          item.a = item.b.clone().add(new THREE.Vector3(0, 3.5, 1.5));
        } else if (p.kind === 'lost') {
          if (!a) continue;
          item.a = nodeCentre(a);
          item.b = item.a.clone().add(new THREE.Vector3(0, 2.5, 0));
        } else {
          if (!a || !b) continue;
          item.a = nodeCentre(a);
          item.b = nodeCentre(b);
        }
      }
      const mesh = new THREE.Mesh(geoms.marker, p.kind === 'undeclared' ? undeclaredFlowMaterial : flowMaterial);
      mesh.scale.setScalar(1.9);
      mesh.visible = false;
      mesh.frustumCulled = false;
      const el = document.createElement('div');
      el.className = `scene-flow-label scene-flow-label--${p.kind}`;
      el.dataset.flowKind = p.kind;
      el.textContent = p.kind === 'undeclared' ? `${eventName} · no declared relationship`
        : p.kind === 'unshown' ? `${eventName} · via ${p.relationship} (not drawn in this view)`
        : p.kind === 'lost' ? `${eventName} · dropped`
          : p.kind === 'enter' ? `${eventName} ↓` : eventName;
      item.label = new CSS2DObject(el);
      item.label.position.set(0, 0.32, 0);
      mesh.add(item.label);
      item.mesh = mesh;
      scene.add(mesh);
      flows.push(item);
    }
    renderDirty = true;
    matricesDirty = true;
  }

  /** Messages currently in flight, with how far each has travelled (0 to 1) as last drawn. */
  function getFlows() {
    return flows.map((f) => ({ kind: f.kind, event: f.event, from: f.from, to: f.to, edge: f.es ? (f.es.edge.entityId ?? f.es.id) : null, reverse: f.reverse === true, progress: Math.min(1, f.elapsed / FLOW_MS) }));
  }

  // ---------------------------------------------------------------- clutter
  function runClutter(now) {
    lastClutter = now;
    labelsDirty = false;
    rebuildLists();
    ensureMatrices();
    rig.camera.updateMatrixWorld();
    for (const ns of nodes.values()) {
      const it = ns.labelItem;
      const selected = nodeSelected(ns);
      const hovered = hoverNs === ns;
      it.force = selected || hovered;
      it.group = selected ? 0 : hovered ? 1 : (hlActive && ns.hl) ? 2 : ns.slab ? 3 : 4;
      if (it.w === 0) {
        const w = ns.parts.el.offsetWidth;
        if (w > 0) { it.w = w; it.h = ns.parts.el.offsetHeight; }
      }
    }
    layoutLabels(labelItems, rig.camera, width, height);
    let shown = 0;
    for (const ns of nodes.values()) {
      const hide = !ns.labelItem.show;
      if (hide !== ns.labelHidden) { ns.labelHidden = hide; updateLabelClass(ns); }
      if (!hide) shown++;
    }
    for (const es of edges.values()) if (es.labelObj?.visible) shown++;
    visibleLabels = shown;
  }

  // ------------------------------------------------------------------ picking
  const raycaster = new THREE.Raycaster();
  raycaster.params.Line2 = { threshold: 6 };
  const ndc = new THREE.Vector2();

  function setRay(cx, cy) {
    const r = canvas.getBoundingClientRect();
    ndc.set(((cx - r.left) / Math.max(1, r.width)) * 2 - 1, -((cy - r.top) / Math.max(1, r.height)) * 2 + 1);
    ensureMatrices();
    rig.camera.updateMatrixWorld();
    raycaster.setFromCamera(ndc, rig.camera);
  }

  /** @returns {{kind:'node', ns:any, point:THREE.Vector3}|{kind:'edge', es:any, point:THREE.Vector3}|null} */
  function pick(cx, cy) {
    flushEdges();
    rebuildLists();
    setRay(cx, cy);
    const hits = raycaster.intersectObjects(bodyList, false);
    let slabHit = null;
    for (const h of hits) {
      const ns = h.object.userData.ns;
      if (!ns.slab) return { kind: 'node', ns, point: h.point };
      if (!slabHit || ns.level > slabHit.ns.level) slabHit = { kind: 'node', ns, point: h.point };
    }
    const eh = raycaster.intersectObjects(edgeList, false);
    if (eh.length) return { kind: 'edge', es: eh[0].object.userData.es, point: eh[0].point };
    return slabHit;
  }

  function inBorderBand(ns, pt) {
    const c = ns.cur;
    const dx = Math.min(pt.x - (c.x - c.w / 2), c.x + c.w / 2 - pt.x);
    const dz = Math.min(pt.z - (c.z - c.d / 2), c.z + c.d / 2 - pt.z);
    return Math.min(dx, dz) < CONTAINER_DRAG_BAND;
  }

  // ------------------------------------------------------------ interaction
  const cleanups = [];
  const listen = (target, type, fn, opts) => {
    target.addEventListener(type, fn, opts);
    cleanups.push(() => target.removeEventListener(type, fn, opts));
  };

  let press = null;
  let drag = null;
  let hoverPending = null; // {x,y} | 'clear'
  const plane = new THREE.Plane(new THREE.Vector3(0, 1, 0), 0);
  const groundHit = new THREE.Vector3();

  function groundPoint(cx, cy, y) {
    setRay(cx, cy);
    plane.constant = -y;
    return raycaster.ray.intersectPlane(plane, groundHit);
  }

  function updateCursor() {
    let c = '';
    if (drag) c = 'grabbing';
    else if (mode === 'connect') c = 'crosshair';
    else if (hoverNs || hoverEs) c = 'pointer';
    canvas.style.cursor = c;
  }

  function setHover(hit) {
    const nextNs = hit && hit.kind === 'node' ? hit.ns : null;
    const nextEs = hit && hit.kind === 'edge' ? hit.es : null;
    if (nextNs === hoverNs && nextEs === hoverEs) return;
    const prevNs = hoverNs;
    const prevEs = hoverEs;
    hoverNs = nextNs;
    hoverEs = nextEs;
    if (prevNs) refreshNode(prevNs);
    if (prevEs) refreshEdge(prevEs);
    if (nextNs) refreshNode(nextNs);
    if (nextEs) refreshEdge(nextEs);
    renderDirty = true;
    labelsDirty = true;
    updateCursor();
    cb.onHover(hit ? hitEntity(hit) : null);
  }

  function leavesOf(ns, out) {
    if (!ns.children.length) out.push(ns);
    else for (const c of ns.children) leavesOf(c, out);
    return out;
  }

  function startDrag(ns) {
    const y = ns.group.position.y;
    const p0 = groundPoint(press.x, press.y, y);
    if (!p0) { press.dragNs = null; rig.setUserEnabled(true); return; }
    const leaves = leavesOf(ns, []);
    const slabs = new Set();
    for (const leaf of leaves) {
      let cur = leaf.parentId ? nodes.get(leaf.parentId) : null;
      while (cur) { slabs.add(cur); cur = cur.parentId ? nodes.get(cur.parentId) : null; }
    }
    if (ns.slab) slabs.add(ns);
    const slabList = [...slabs].filter((s) => s.children.length).sort((a, b) => b.level - a.level);
    const pads = slabList.map((s) => {
      let minX = Infinity; let maxX = -Infinity; let minZ = Infinity; let maxZ = -Infinity;
      for (const c of s.children) {
        minX = Math.min(minX, c.cur.x - c.cur.w / 2); maxX = Math.max(maxX, c.cur.x + c.cur.w / 2);
        minZ = Math.min(minZ, c.cur.z - c.cur.d / 2); maxZ = Math.max(maxZ, c.cur.z + c.cur.d / 2);
      }
      return {
        ns: s,
        l: minX - (s.cur.x - s.cur.w / 2), r: (s.cur.x + s.cur.w / 2) - maxX,
        t: minZ - (s.cur.z - s.cur.d / 2), b: (s.cur.z + s.cur.d / 2) - maxZ,
      };
    });
    for (const n of [...leaves, ...slabList]) { n.anim = null; animating.delete(n); }
    drag = {
      ns, y,
      offX: ns.cur.x - p0.x, offZ: ns.cur.z - p0.z,
      anchor: { x: ns.cur.x, z: ns.cur.z },
      leaves: leaves.map((n) => ({ ns: n, x: n.cur.x, z: n.cur.z })),
      pads,
    };
    updateCursor();
  }

  function moveDrag(ev) {
    const p = groundPoint(ev.clientX, ev.clientY, drag.y);
    if (!p) return;
    const dx = p.x + drag.offX - drag.anchor.x;
    const dz = p.z + drag.offZ - drag.anchor.z;
    for (const l of drag.leaves) { l.ns.cur.x = l.x + dx; l.ns.cur.z = l.z + dz; placeNode(l.ns); }
    for (const pd of drag.pads) {
      let minX = Infinity; let maxX = -Infinity; let minZ = Infinity; let maxZ = -Infinity;
      for (const c of pd.ns.children) {
        minX = Math.min(minX, c.cur.x - c.cur.w / 2); maxX = Math.max(maxX, c.cur.x + c.cur.w / 2);
        minZ = Math.min(minZ, c.cur.z - c.cur.d / 2); maxZ = Math.max(maxZ, c.cur.z + c.cur.d / 2);
      }
      const l = minX - pd.l; const r = maxX + pd.r; const t = minZ - pd.t; const b = maxZ + pd.b;
      pd.ns.cur.x = (l + r) / 2; pd.ns.cur.w = r - l;
      pd.ns.cur.z = (t + b) / 2; pd.ns.cur.d = b - t;
      placeNode(pd.ns);
    }
    flushEdges();
  }

  function endDrag() {
    const d = drag;
    drag = null;
    rig.setUserEnabled(true);
    updateCursor();
    const moves = d.leaves.map((l) => ({ id: l.ns.id, x: l.ns.cur.x, z: l.ns.cur.z }));
    if (moves.length) cb.onMoveEnd(moves);
  }

  function cancelConnect() {
    if (!connectSource) return;
    const ns = nodes.get(connectSource);
    connectSource = null;
    preview.visible = false;
    if (ns) refreshNode(ns);
    touch();
  }

  function handleClick(cx, cy) {
    const hit = pick(cx, cy);
    if (mode === 'connect') {
      if (!hit || hit.kind !== 'node') { cancelConnect(); return; }
      if (!connectSource) {
        connectSource = hit.ns.id;
        refreshNode(hit.ns);
        updatePreview(cx, cy);
        touch();
      } else {
        const from = nodes.get(connectSource);
        const to = hit.ns;
        cancelConnect();
        if (from) cb.onConnect(nodeEntity(from), nodeEntity(to));
      }
      return;
    }
    cb.onSelect(hit ? hitEntity(hit) : null);
  }

  // connect preview line
  const previewGeom = new LineGeometry();
  previewGeom.setPositions([0, 0, 0, 0, 0, 0]);
  const preview = new Line2(previewGeom, previewMaterial);
  preview.frustumCulled = false;
  preview.visible = false;
  scene.add(preview);

  function updatePreview(cx, cy) {
    const src = connectSource ? nodes.get(connectSource) : null;
    if (!src) { preview.visible = false; return; }
    const sy = src.top + 0.05;
    const p = groundPoint(cx, cy, sy);
    if (!p) return;
    const arr = previewGeom.attributes.instanceStart.data.array;
    arr[0] = src.cur.x; arr[1] = sy; arr[2] = src.cur.z;
    arr[3] = p.x; arr[4] = sy; arr[5] = p.z;
    previewGeom.attributes.instanceStart.data.needsUpdate = true;
    previewGeom.boundingSphere = null;
    previewGeom.boundingBox = null;
    preview.visible = true;
    matricesDirty = true;
    renderDirty = true;
  }

  /** Pixels a press may travel and still count as a click or tap. */
  const slop = (p) => (p.touch ? TAP_PX_TOUCH : CLICK_PX);

  function onPointerDown(ev) {
    if (ev.button !== 0) return;
    // A second finger turns the gesture into a pinch or two-finger pan: no tap, no node drag.
    if (press && press.id !== ev.pointerId) {
      press.multi = true;
      clearTimeout(press.holdTimer);
      if (press.dragNs && !drag) { press.dragNs = null; rig.setUserEnabled(true); }
      return;
    }
    const touch = ev.pointerType === 'touch' || ev.pointerType === 'pen';
    press = { x: ev.clientX, y: ev.clientY, dragNs: null, id: ev.pointerId, touch, armed: !touch, multi: false, holdTimer: 0 };
    if (ev.shiftKey || mode !== 'select') return;
    const hit = pick(ev.clientX, ev.clientY);
    if (hit && hit.kind === 'node') {
      const ns = hit.ns;
      if (!ns.slab || inBorderBand(ns, hit.point)) {
        press.dragNs = ns;
        if (!touch) {
          rig.setUserEnabled(false);
          try { canvas.setPointerCapture(ev.pointerId); } catch { /* not capturable */ }
        } else {
          // Touch: a swipe that starts on a node still orbits; a press held still arms the node drag.
          const p = press;
          p.holdTimer = window.setTimeout(() => {
            if (press !== p || p.multi || !p.dragNs) return;
            p.armed = true;
            rig.setUserEnabled(false);
            try { canvas.setPointerCapture(p.id); } catch { /* not capturable */ }
          }, TOUCH_HOLD_MS);
        }
      }
    }
  }

  function onPointerMove(ev) {
    if (press && ev.pointerId !== press.id) return;
    if (press && press.dragNs && !drag) {
      const moved = Math.hypot(ev.clientX - press.x, ev.clientY - press.y) > slop(press);
      if (moved && press.armed) startDrag(press.dragNs);
      else if (moved) { clearTimeout(press.holdTimer); press.dragNs = null; }
    }
    if (drag) { moveDrag(ev); return; }
    if (press) return;
    if (ev.target !== canvas) { hoverPending = 'clear'; return; }
    hoverPending = { x: ev.clientX, y: ev.clientY };
    if (connectSource) updatePreview(ev.clientX, ev.clientY);
  }

  function onPointerUp(ev) {
    if (!press) return;
    if (ev.pointerId !== press.id) return; // the second finger of a pinch
    const p = press;
    press = null;
    clearTimeout(p.holdTimer);
    if (drag) { endDrag(); return; }
    if (p.dragNs && p.armed) rig.setUserEnabled(true);
    if (ev.type === 'pointercancel' || p.multi) return;
    if (Math.hypot(ev.clientX - p.x, ev.clientY - p.y) > slop(p)) return;
    handleClick(ev.clientX, ev.clientY);
  }

  function onDblClick(ev) {
    if (mode !== 'select') return;
    const hit = pick(ev.clientX, ev.clientY);
    if (hit) cb.onActivate(hitEntity(hit));
  }

  function onKeyDown(ev) {
    if (ev.key === 'Escape' && connectSource) cancelConnect();
  }

  listen(host, 'pointerdown', onPointerDown, { capture: true });
  listen(window, 'pointermove', onPointerMove);
  listen(window, 'pointerup', onPointerUp);
  listen(window, 'pointercancel', onPointerUp);
  listen(canvas, 'dblclick', onDblClick);
  listen(window, 'keydown', onKeyDown);
  listen(canvas, 'pointerleave', () => { if (!press) hoverPending = 'clear'; });

  function processHover() {
    if (!hoverPending || press || drag) return;
    const h = hoverPending;
    hoverPending = null;
    if (h === 'clear') { setHover(null); return; }
    setHover(pick(h.x, h.y));
  }

  // ----------------------------------------------------------------- resize
  function resize() {
    width = Math.max(1, host.clientWidth);
    height = Math.max(1, host.clientHeight);
    renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
    renderer.setSize(width, height);
    css.setSize(width, height);
    rig.setSize(width, height);
    for (const m of lineMats) m.resolution.set(width, height);
    touch();
  }
  const ro = new ResizeObserver(() => { if (!disposed) resize(); });
  ro.observe(host);
  resize();

  // ------------------------------------------------------------------- loop
  function frame() {
    raf = requestAnimationFrame(frame);
    const now = performance.now();
    rig.update(now);
    stepAnimations(now);
    processHover();
    flushEdges();
    if (labelsDirty && now - lastClutter >= CLUTTER_MS) runClutter(now);
    if (!renderDirty) return;
    renderDirty = false;
    ensureMatrices();
    const t0 = performance.now();
    renderer.render(scene, rig.camera);
    css.render(scene, rig.camera);
    const t1 = performance.now();
    frameMsAvg = frameMsAvg ? frameMsAvg * 0.9 + (t1 - t0) * 0.1 : t1 - t0;
    if (lastRenderT) {
      const dt = t0 - lastRenderT;
      if (dt > 0 && dt < 500) {
        const inst = 1000 / dt;
        fpsAvg = fpsAvg ? fpsAvg * 0.9 + inst * 0.1 : inst;
      }
    }
    lastRenderT = t0;
    if (needMeasure) { needMeasure = false; labelsDirty = true; }
  }
  raf = requestAnimationFrame(frame);

  // -------------------------------------------------------------------- API
  function boxOf(list) {
    const box = new THREE.Box3();
    for (const ns of list) {
      const c = ns.cur;
      box.expandByPoint(_p.set(c.x - c.w / 2, ns.baseY, c.z - c.d / 2));
      box.expandByPoint(_p.set(c.x + c.w / 2, Math.max(ns.top, ns.baseY + 0.1), c.z + c.d / 2));
    }
    return box;
  }

  function fit(ids, animate = true) {
    flushEdges();
    let list = [];
    if (ids && ids.length) {
      const set = new Set();
      for (const id of ids) {
        const ns = resolveNode(id);
        if (ns) { set.add(ns); continue; }
        const es = resolveEdge(id);
        if (es) { set.add(es.a); set.add(es.b); }
      }
      list = [...set];
    }
    if (!list.length) list = [...nodes.values()];
    if (!list.length) return;
    const box = boxOf(list);
    // Fitting a single small node keeps its surroundings in view instead of filling the viewport with it.
    const size = box.getSize(new THREE.Vector3());
    const MIN_EXTENT = 14;
    const padX = Math.max(0, (MIN_EXTENT - size.x) / 2);
    const padZ = Math.max(0, (MIN_EXTENT * 0.6 - size.z) / 2);
    if (padX || padZ) box.expandByVector(new THREE.Vector3(padX, 0, padZ));
    rig.fitBox(box, animate);
  }

  function setSelection(ids) {
    selSet = new Set(ids ?? []);
    refreshAll();
  }

  function setHighlight(ids) {
    hlActive = Array.isArray(ids);
    hlSet = new Set(hlActive ? ids : []);
    refreshAll();
  }

  function setMode(next) {
    const m = next === 'connect' ? 'connect' : 'select';
    if (m === mode) return;
    mode = m;
    cancelConnect();
    updateCursor();
  }

  function setCameraMode(m) {
    rig.setMode(m);
    touch();
  }

  function pulse(ids) {
    const now = performance.now();
    for (const id of ids ?? []) {
      const ns = resolveNode(id);
      if (ns) {
        ns.pulseT0 = now;
        pulsingNodes.add(ns);
        refreshNode(ns);
        continue;
      }
      const es = resolveEdge(id);
      if (es) {
        const mesh = new THREE.Mesh(geoms.marker, markerMaterial);
        mesh.visible = false;
        mesh.frustumCulled = false;
        scene.add(mesh);
        edgePulses.push({ es, t0: now, mesh });
      }
    }
    renderDirty = true;
    matricesDirty = true;
  }

  function getStats() {
    const info = renderer.info.render;
    return {
      fps: Math.round(fpsAvg * 10) / 10,
      frameMs: Math.round(frameMsAvg * 100) / 100,
      drawCalls: info.calls,
      triangles: info.triangles,
      nodes: nodes.size,
      edges: edges.size,
      labels: visibleLabels,
    };
  }

  function screenPoint(id) {
    flushEdges();
    let x; let y; let z;
    const ns = resolveNode(id);
    if (ns) {
      x = ns.cur.x;
      z = ns.cur.z;
      if (ns.slab) { y = ns.top; z = ns.cur.z - ns.cur.d / 2 + 0.2; }
      else y = ns.baseY + ns.raise + shapePickY(ns.node.shape, ns.cur.w, ns.cur.d);
    } else {
      const es = resolveEdge(id);
      if (!es) return null;
      const m = Math.floor(POINTS / 2) * 3;
      x = es.pts[m]; y = es.pts[m + 1]; z = es.pts[m + 2];
    }
    rig.camera.updateMatrixWorld();
    _p.set(x, y, z).project(rig.camera);
    const r = canvas.getBoundingClientRect();
    return { x: r.left + (_p.x * 0.5 + 0.5) * r.width, y: r.top + (-_p.y * 0.5 + 0.5) * r.height };
  }

  function dispose() {
    if (disposed) return;
    disposed = true;
    cancelAnimationFrame(raf);
    ro.disconnect();
    for (const c of cleanups.splice(0)) c();
    rig.dispose();
    for (const es of [...edges.values()]) disposeEdge(es);
    for (const ns of nodes.values()) disposeNode(ns);
    edges.clear();
    nodes.clear();
    for (const p of edgePulses) scene.remove(p.mesh);
    edgePulses = [];
    for (const f of flows) endFlow(f);
    flows = [];
    flowMaterial.dispose();
    undeclaredFlowMaterial.dispose();
    previewGeom.dispose();
    markerMaterial.dispose();
    for (const m of matCache.values()) m.dispose();
    matCache.clear();
    previewMaterial.dispose();
    lineMats.clear();
    geoms.dispose();
    grid.geometry.dispose();
    grid.material.dispose();
    renderer.dispose();
    renderer.forceContextLoss();
    canvas.remove();
    layer.remove();
  }

  return {
    setScene,
    setSelection,
    setHighlight,
    setMode,
    setCameraMode,
    fit: (ids) => fit(ids, true),
    getCamera: () => rig.getState(),
    setCamera: (state) => { rig.setState(state); touch(); },
    pulse,
    flow,
    getFlows,
    getStats,
    screenPoint,
    dispose,
  };
}
