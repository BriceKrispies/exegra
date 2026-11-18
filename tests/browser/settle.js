// A condition to wait for instead of a fixed sleep: the scene and the interface have stopped moving.
// Motion here is CSS transitions (the sheets), the camera tween (fit) and the nodes easing to a new layout.

/**
 * Resolves once, for several animation frames in a row, no CSS animation is running, the camera has not moved
 * and no scene node has moved on screen.
 * @param {import('@playwright/test').Page} page
 * @param {{frames?: number, timeout?: number}} [opts]
 */
export function settled(page, opts = {}) {
  const frames = opts.frames ?? 4;
  return page.evaluate(({ frames: need, timeout }) => new Promise((resolve, reject) => {
    const t0 = performance.now();
    let last = '';
    let still = 0;
    const sample = () => {
      const x = /** @type {any} */ (window).__exegra;
      const running = document.getAnimations().filter((a) => a.playState === 'running').length;
      let sig = '';
      if (x?.view && x.session?.scene) {
        sig += JSON.stringify(x.view.getCamera());
        for (const n of x.session.scene.nodes) {
          const p = x.view.screenPoint(n.id);
          sig += p ? `|${p.x.toFixed(1)},${p.y.toFixed(1)}` : '|-';
        }
      }
      still = sig === last && running === 0 ? still + 1 : 0;
      last = sig;
      if (still >= need) resolve(undefined);
      else if (performance.now() - t0 > timeout) reject(new Error('the scene did not settle'));
      else requestAnimationFrame(sample);
    };
    requestAnimationFrame(sample);
  }), { frames, timeout: opts.timeout ?? 10_000 });
}
