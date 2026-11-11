import VersoManual
import Book.Meta
import Book.Part1Foundations
import Book.Part2Analysis
import Book.Part3Internal
import Book.Part4Frameworks
import Book.Part5Applications

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option linter.verso.markup.emph false

#doc (Manual) "Lectures on the Hyperreals — Interactive Lean 4 & Spatial Edition" =>
%%%
tag := "lectures-on-the-hyperreals"
authors := ["Alok Singh (Formalization & Interactive Verso Edition)", "After Robert Goldblatt (GTM 188, Springer 1998)"]
%%%

```rawHtml
<div class="hr-hero-card">
  <img class="hr-hero-art" src="static/diagrams/hero_observatory.jpg" alt="Infinitesimal Microscope and Infinite Telescope Observatory Illustration" />
  <div class="hr-hero-body">
    <div class="hr-badge-row">
      <span class="hr-pill gold">✦ 100% Mechanically Verified in Lean 4.35</span>
      <span class="hr-pill emerald">◈ Apple Vision Pro Native Stereoscopic 3D</span>
      <span class="hr-pill">📱 Tuned for iPhone &amp; Spatial Safari</span>
    </div>
    <p style="margin: 0.3rem 0 0.7rem 0; color: #e2e8f0; font-family: -apple-system, BlinkMacSystemFont, system-ui, sans-serif; font-size: 0.98rem; line-height: 1.58;">
      A complete, axiom-clean autoformalization and visual companion to Robert Goldblatt's classic
      <em>Lectures on the Hyperreals: An Introduction to Nonstandard Analysis</em> (Graduate Texts in Mathematics 188)—from
      ultrafilters and Łoś's Transfer Principle to Loeb measure, Ramsey theory, <em>p</em>-adic completions, and hyperfinite Hahn–Banach.
    </p>
    <div class="hr-stats-grid">
      <div class="hr-stat-box">
        <span class="hr-stat-num">59,556</span>
        <span class="hr-stat-label">Lines of Lean 4</span>
      </div>
      <div class="hr-stat-box">
        <span class="hr-stat-num">4,248</span>
        <span class="hr-stat-label">Kernel Declarations</span>
      </div>
      <div class="hr-stat-box">
        <span class="hr-stat-num">0 / 0</span>
        <span class="hr-stat-label">Sorrys / Custom Axioms</span>
      </div>
      <div class="hr-stat-box">
        <span class="hr-stat-num">5 Parts · 20 Ch</span>
        <span class="hr-stat-label">Full Textbook Scope</span>
      </div>
    </div>
  </div>
</div>
```

```spatial3d (model := "hyperreal_telescope") (title := "3D Stage I · The Hyperreal Observatory — Halos, Galaxies & the Shadow Map")
<strong>Scroll &amp; Orbit in 3D:</strong> Above the silver standard real axis <code>ℝ</code> floats the magnified sapphire halo <code>hal(0) = 𝕀</code> containing nested cyan (<code>ε</code>) and violet (<code>ε²</code>) infinitesimal rings, projecting down via the golden <code>shadow</code> beam onto <code>0 ∈ ℝ</code>, flanked by emerald and coral unlimited galaxies <code>gal(±ω)</code>.
```

```rawHtml
<div class="hr-intuition">
  <strong>Reading on iPhone &amp; Apple Vision Pro:</strong>
  On <strong>Apple Vision Pro</strong>, every 3D stage uses Safari's native HTML <code>&lt;model stagemode="orbit" src="...usdz"&gt;</code> element so sculptures appear in <em>true stereoscopic 3D depth right inside the page as you scroll</em>—look and pinch-drag to orbit, or tap <strong>View 3D / AR</strong> to pull them into your room. On <strong>iPhone &amp; Mac</strong>, each stage hydrates a smooth WebGL 3D viewer with vertical scroll pass-through and one-tap iOS AR Quick Look. Tap or hover any identifier inside the Lean 4 blocks to inspect its live kernel signature!
</div>
```

Formalizing an entire graduate mathematics textbook end-to-end without a single `sorry` sits at the frontier where modern agentic coding and formal verification meet. Following Google DeepMind's *AlphaProof* silver-medal breakthrough at IMO 2024 in Lean 4, the 2025–2026 wave—including gold-medal olympiad reasoning, DeepMind's *AlphaProof* and *AlphaEvolve* research verification workflows, Harmonic's Aristotle, and agentic Lean 4 provers—has shifted the horizon from isolated competition puzzles to *cohesive, multi-thousand-theorem mathematical libraries* where definitions across 20 chapters interlock cleanly and every proof term passes Lean's minimal kernel checker (`propext`, `Classical.choice`, `Quot.sound` only).

Dive into any of the five parts below, or use the search bar and chapter drawer at top left:

{include 0 Book.Part1Foundations}

{include 0 Book.Part2Analysis}

{include 0 Book.Part3Internal}

{include 0 Book.Part4Frameworks}

{include 0 Book.Part5Applications}
