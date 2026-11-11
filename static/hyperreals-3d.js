/* ==========================================================================
   Lectures on the Hyperreals — Spatial 3D & Reader Comfort Script
   - Preserves native <model stagemode="orbit"> on Apple Vision Pro (visionOS Safari)
   - Hydrates interactive WebGL <model-viewer> + AR Quick Look on iPhone & Desktop
   - Provides persisted Light/Dark/Auto theme & A-/A+ font scaling
   ========================================================================== */

(function () {
  "use strict";

  const STORAGE_THEME = "hr-reader-theme";
  const STORAGE_SCALE = "hr-reader-scale";

  // 1. Upgrade viewport meta for iPhone safe areas & accessible pinch-to-zoom
  const vp = document.querySelector('meta[name="viewport"]');
  if (vp) {
    vp.setAttribute(
      "content",
      "width=device-width, initial-scale=1, viewport-fit=cover"
    );
  }

  // 2. Apply saved theme & font scale immediately
  const root = document.documentElement;
  try {
    const savedTheme = localStorage.getItem(STORAGE_THEME);
    if (savedTheme === "light" || savedTheme === "dark") {
      root.setAttribute("data-theme", savedTheme);
    }
    const savedScale = parseFloat(localStorage.getItem(STORAGE_SCALE) || "1");
    if (!Number.isNaN(savedScale) && savedScale >= 0.85 && savedScale <= 1.35) {
      root.style.setProperty("--hr-reader-scale", String(savedScale));
    }
  } catch (_) {}

  function initReaderControls() {
    const header = document.querySelector("body > header");
    if (!header || header.querySelector(".hr-reader-controls")) return;

    const bar = document.createElement("div");
    bar.className = "hr-reader-controls";
    bar.setAttribute("aria-label", "Reader display settings");

    const themeBtn = document.createElement("button");
    themeBtn.type = "button";
    themeBtn.className = "hr-ctrl-btn";
    const updateThemeLabel = () => {
      const cur = root.getAttribute("data-theme") || "auto";
      themeBtn.textContent =
        cur === "dark" ? "☾ Dark" : cur === "light" ? "☀ Light" : "◐ Auto";
      themeBtn.title = "Cycle color theme (Auto / Dark / Light)";
    };
    updateThemeLabel();

    themeBtn.addEventListener("click", () => {
      const cur = root.getAttribute("data-theme") || "auto";
      const next = cur === "auto" ? "dark" : cur === "dark" ? "light" : "auto";
      if (next === "auto") {
        root.removeAttribute("data-theme");
      } else {
        root.setAttribute("data-theme", next);
      }
      try {
        localStorage.setItem(STORAGE_THEME, next);
      } catch (_) {}
      updateThemeLabel();
    });

    const decBtn = document.createElement("button");
    decBtn.type = "button";
    decBtn.className = "hr-ctrl-btn hide-mobile";
    decBtn.textContent = "A−";
    decBtn.title = "Decrease text size";

    const incBtn = document.createElement("button");
    incBtn.type = "button";
    incBtn.className = "hr-ctrl-btn hide-mobile";
    incBtn.textContent = "A+";
    incBtn.title = "Increase text size";

    const adjustScale = (delta) => {
      const cur =
        parseFloat(root.style.getPropertyValue("--hr-reader-scale") || "1") || 1;
      const next = Math.min(1.3, Math.max(0.88, Math.round((cur + delta) * 100) / 100));
      root.style.setProperty("--hr-reader-scale", String(next));
      try {
        localStorage.setItem(STORAGE_SCALE, String(next));
      } catch (_) {}
    };

    decBtn.addEventListener("click", () => adjustScale(-0.07));
    incBtn.addEventListener("click", () => adjustScale(0.07));

    bar.appendChild(decBtn);
    bar.appendChild(incBtn);
    bar.appendChild(themeBtn);
    header.appendChild(bar);
  }

  function initSpatial3DStages() {
    const stages = document.querySelectorAll(".spatial-stage");
    if (!stages.length) return;

    const hasNativeHTMLModel = "HTMLModelElement" in window;

    if (hasNativeHTMLModel) {
      stages.forEach((stage) => {
        stage.setAttribute("data-mode", "visionos-native");
        const badge = stage.querySelector(".spatial-stage-badge");
        if (badge) {
          badge.textContent = "Vision Pro Native 3D · Gaze & Pinch to Orbit";
        }
      });
      return;
    }

    // Non-visionOS (iPhone, iPad, Mac, Desktop): load <model-viewer> once and hydrate fallbacks
    stages.forEach((stage) => {
      stage.setAttribute("data-mode", "webgl-fallback");
      const badge = stage.querySelector(".spatial-stage-badge");
      if (badge) {
        badge.textContent = "Interactive 3D · Drag to Orbit · Vision Pro Ready";
      }
      const fb = stage.querySelector(".spatial-model-fallback");
      if (!fb || fb.querySelector("model-viewer")) return;

      const glb = fb.getAttribute("data-glb");
      const usdz = fb.getAttribute("data-usdz");
      const alt = fb.getAttribute("data-alt") || "3D mathematical sculpture";

      const mv = document.createElement("model-viewer");
      if (glb) mv.setAttribute("src", glb);
      if (usdz) mv.setAttribute("ios-src", usdz);
      mv.setAttribute("alt", alt);
      mv.setAttribute("loading", "eager");
      mv.setAttribute("camera-controls", "");
      mv.setAttribute("touch-action", "pan-y");
      mv.setAttribute("auto-rotate", "");
      mv.setAttribute("rotation-per-second", "14deg");
      mv.setAttribute("shadow-intensity", "0.85");
      mv.setAttribute("exposure", "1.05");
      mv.setAttribute("ar", "");
      mv.setAttribute("ar-modes", "quick-look webxr scene-viewer");
      fb.appendChild(mv);
    });

    if (!document.querySelector('script[data-model-viewer-loader="1"]')) {
      const s = document.createElement("script");
      s.type = "module";
      s.src =
        "https://ajax.googleapis.com/ajax/libs/model-viewer/3.5.0/model-viewer.min.js";
      s.setAttribute("data-model-viewer-loader", "1");
      document.head.appendChild(s);
    }
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", () => {
      initReaderControls();
      initSpatial3DStages();
    });
  } else {
    initReaderControls();
    initSpatial3DStages();
  }
})();
