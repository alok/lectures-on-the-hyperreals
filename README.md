# Lectures on the Hyperreals — Complete Lean 4 Autoformalization

Complete, kernel-verified, **`sorry`-free**, **custom-`axiom`-free** Lean 4 formalization of Robert Goldblatt's classic graduate textbook:

> **Robert Goldblatt**, *Lectures on the Hyperreals: An Introduction to Nonstandard Analysis*, Graduate Texts in Mathematics, vol. 188, Springer-Verlag, New York, 1998.

Every mathematical chapter of the book (**Parts I–V, Chapters 1–19**) is formalized end-to-end in Lean `v4.35.0` against Mathlib `v4.35.0`, and Chapter 20's 41-entry bibliography is documented in [`COVERAGE.md`](./COVERAGE.md).

---

## Interactive Verso Book & Spatial 3D Edition (iPhone & Apple Vision Pro)

- **Read Online**: **[https://alok.blog/lectures-on-the-hyperreals/](https://alok.blog/lectures-on-the-hyperreals/)** *(GitHub Pages: `alok.github.io/lectures-on-the-hyperreals/`)*

An interactive, illustrated **Verso** (`Verso.Genre.Manual`) companion book spanning all 5 Parts and 20 Chapters, crafted for effortless reading on **iPhone** and **Apple Vision Pro**:

- **Live-Elaborated Lean 4 + SubVerso Signatures**: Every chapter imports `LecturesOnTheHyperreals` directly so `#check` blocks and examples elaborate against the real kernel declarations—tap or hover any symbol to inspect its full Lean 4 type signature and documentation inline.
- **Native Stereoscopic 3D Inline on Apple Vision Pro**: Five custom mathematical 3D sculptures (`static/models/*.usdz`, strict RealityKit-validated via `usdchecker --arkit --strict`) render natively inside the page via visionOS Safari's `<model stagemode="orbit" interactive="interactive">` portal so you see genuine stereoscopic 3D depth right as you scroll, with automatic WebGL `<model-viewer>` + one-tap iOS AR Quick Look fallback (`*.glb` + `*.usdz`) on iPhone, iPad, and Mac.
- **Custom Mathematical Diagrams & Editorial Art**: Painted observatory cover art (`static/diagrams/hero_observatory.jpg`), custom site emblem (`static/logo.svg`), and 8 vector mathematical diagrams (`static/diagrams/*.svg`) illustrating Keisler's infinitesimal microscope, free ultrafilter voting, the Incremental Equation, halo topology, overflow/saturation, Zakon superstructures, Loeb measure, and the Part V applications quartet.
- **Mobile & Spatial Ergonomics**: Charter / Apple New York serif prose, zero horizontal overflow on narrow phone viewports, safe-area insets, full-width Prev/Next chapter cards, and persisted **Auto / Dark / Light** + **A− / A+** reader controls.

```bash
# Regenerate all 5 USDZ/GLB 3D sculptures and 9 SVG illustrations
uv run --with numpy --with trimesh --with scipy --with networkx python scripts/generate_assets.py

# Build the multi-page interactive Verso website into _out/html-multi/ (published via docs/)
lake exe generate-book
```

---

## Key Metrics & Kernel Verification

| Metric | Value |
|---|---|
| **Lean 4 / Mathlib Toolchain** | `leanprover/lean4:v4.35.0` / `mathlib v4.35.0` |
| **Mathematical Chapters Covered** | **19 / 19** (`Ch01`–`Ch19`, plus Ch. 20 bibliography in `COVERAGE.md`) |
| **Total Lean Source Lines** | **59,556 lines** across 21 `.lean` files |
| **Source-Level Declarations** | **3,491** (`2,681` theorems & lemmas + `810` definitions, structures & inductives) |
| **Compiled `Goldblatt.*` Kernel Constants** | **4,248** (`3,008` theorems + `1,149` definitions/inductives + projections) |
| **`sorry` / `sorryAx` Count** | **0** |
| **Custom `axiom` Count** | **0** *(only Lean core `propext`, `Classical.choice`, `Quot.sound`)* |

### Build & Run the Kernel Axiom Audit

```bash
# Build all 19 chapters and the root umbrella library
lake build

# Verify 0 sorryAx and 0 custom axioms across all 4,248 Goldblatt.* kernel constants
lake env lean scripts/verify_axioms.lean
```

Output of `lake env lean scripts/verify_axioms.lean`:

```text
Verified `Goldblatt.*` kernel declarations : 4248
  Theorems / lemmas                        : 3008
  Definitions / inductives / structures    : 1149
  Declarations using `sorryAx`             : 0
  Disallowed / custom axioms               : 0
KERNEL AUDIT PASSED: 0 sorryAx, 0 custom axioms (only propext, Classical.choice, Quot.sound).
```

---

## Repository Architecture

```text
LecturesOnTheHyperreals.lean                       -- Root umbrella module importing Ch01–Ch19
scripts/verify_axioms.lean                         -- Lean 4 kernel MetaM axiom & sorryAx verifier
COVERAGE.md                                        -- Detailed §-by-§ theorem map (Ch01–Ch20)
LecturesOnTheHyperreals/
├── Ch01_WhatAreTheHyperreals.lean      (1,215 L)  -- Part I: Foundations
├── Ch02_LargeSets.lean                 (1,492 L)
├── Ch03_UltrapowerConstruction.lean      (868 L)
├── Ch04_TransferPrinciple.lean         (2,754 L)
├── Ch05_HyperrealsGreatAndSmall.lean   (1,562 L)
├── Ch06_Convergence.lean               (2,580 L)  -- Part II: Elementary Analysis
├── Ch07_ContinuousFunctions.lean       (2,847 L)
├── Ch08_Differentiation.lean           (3,319 L)
├── Ch09_RiemannIntegral.lean           (2,991 L)
├── Ch10_Topology.lean                  (2,681 L)
├── Ch11_InternalSets.lean              (2,245 L)  -- Part III: Internal & External Entities
├── Ch12_InternalFunctions.lean         (1,679 L)
├── Ch13_UniversesFrameworks.lean      (12,047 L)  -- Part IV: Nonstandard Frameworks
├── Ch14_Enlargements.lean              (2,187 L)
├── Ch15_PermanenceSaturation.lean      (3,156 L)
├── Ch16_LoebMeasure.lean               (4,160 L)  -- Part V: Applications
├── Ch17_RamseyTheory.lean              (2,064 L)
├── Ch18_Completion.lean                (5,078 L)
└── Ch19_HyperfiniteApproximation.lean  (4,489 L)
```

### Mathematical Highlights Across All Five Parts

1. **Part I — Foundations (`Ch01`–`Ch05`, 7,891 lines)**
   - Historical infinitesimal calculus (Archimedes' exhaustion, Leibniz's product rule, Euler's infinite binomial products), Dedekind cuts vs. Cantor Cauchy sequences, Zorn's Lemma construction of free ultrafilters, concrete ultrapower construction of `ℝ*`, `ℕ*`, `ℤ*`, `ℚ*` with `|ℝ*| = 2^𝔠`, first-order partial-function `*-transforms` and Łoś's Theorem / Transfer Principle, halos, galaxies, the standard-part quotient `𝕃 ⧸ 𝕀 ≃+* ℝ`, and Goldblatt's nonstandard proof of Euclid's infinitude of primes via `N! + 1` in `ℕ*`.
2. **Part II — Elementary Analysis (`Ch06`–`Ch10`, 14,418 lines)**
   - Nonstandard sequence & series calculus (Bolzano–Weierstrass, Cauchy criterion, `limsup`/`liminf` via shadows, Oresme/ratio/root/Leibniz tests), microcontinuity, Thomae's ruler function, hyperfinite-grid shadow proofs of IVT, EVT, and Heine–Cantor, Banach's Contraction Fixed-Point Theorem, Cauchy's 1821 Sum Theorem, the Incremental Equation (`Δf = f'(x) Δx + η Δx`), nonstandard Inverse Function Theorem, multivariable total derivatives & Taylor series, shadow Riemann integration & Fundamental Theorem of Calculus, Robinson's Compactness Criterion (proved directly without Heine–Borel), and both Robinson's S-topology and the interval topology on `ℝ*`.
3. **Part III — Internal and External Entities (`Ch11`–`Ch12`, 3,924 lines)**
   - `[A_n]` internal sets and `[f_n]` internal partial functions, internal least-number/induction/completeness principles, overflow, underflow, halo permanence, countable (`ℵ₁`-) saturation, uncountability of infinite internal sets, closedness of shadows of internal sets, hyperfinite sets & internal `*ℕ`-cardinality, the **Hyperfinite Pigeonhole Principle**, and hyperfinite summation (`∫_a^b f(x) dx = sh(∑_{x ∈ P} *f(x) dx)`).
4. **Part IV — Nonstandard Frameworks (`Ch13`–`Ch15`, 17,390 lines)**
   - Full cumulative superstructure `Entity X : Type u` over any base type `X` with Kuratowski tuples, bounded-quantifier (`Δ₀`) language `ℒ_𝕌`, Zakon bounded-rank ultrapower collapse & Łoś's Theorem, `*𝒫(A)` = internal subsets of `*A`, Internal Set & Function Definition Principles, unification bridges back to Chapters 11–12, **Theorem 14.2.1** (Concurrence ↔ FIP ↔ Hyperfinite Approximation), **Theorem 14.3.1** (Existence of Enlargements via fine ultrafilters on `Finset I`), Robinson's Sequential Lemma, and **Theorem 15.4.2** (Countable Saturation ↔ Countable Comprehensiveness).
5. **Part V — Applications (`Ch16`–`Ch19`, 15,791 lines)**
   - **Chapter 16 (Loeb Measure)**: Carathéodory extension, **Peter Loeb's Theorem**, single-internal-set `IsMuApproximable` characterization, and construction of Lebesgue measure on both `[0, 1]` and all of `ℝ` via hyperfinite counting Loeb measure (`S = {k/N : |k| ≤ N²}`).
   - **Chapter 17 (Ramsey Theory)**: `R(3, 3) = 6`, direct nonstandard proof of chain/antichain dichotomy in infinite posets, **Infinite Ramsey's Theorem** via `omegaNat ∈ ℕ*`, **Finite Ramsey's Theorem** deduced from Infinite Ramsey via ultrapower transfer, and the **Paris–Harrington Partition Theorem** for relatively large finite sets.
   - **Chapter 18 (Completion by Enlargement)**: Intrinsic `(ℚ_𝕃 ⧸ ℚ_𝕀) ≃+*o ℝ`, **Metric & Banach Nonstandard Hulls** (`MetricCompletion M ≃ᵢ UniformSpace.Completion M`, `BanachCompletion E ≃ₗᵢ[ℝ] UniformSpace.Completion E`), $p$-adic integers `(ℤ* ⧸ I_p) ≃+* ℤ_[p]` and fields `ℚ_[p]`, formal power series `R⟦X⟧` via hyperpolynomials, and hyperfinite base-$p$ expansions.
   - **Chapter 19 (Hyperfinite Approximation)**: Nonstandard fine-ultrafilter proofs of the **De Bruijn–Erdős Graph `k`-Colouring Theorem**, **Stone's Representation Theorem & Full Stone Space Duality** (`B ≃o Clopens (StoneSpace B)`), Birkhoff/Stone distributive lattice prime filter representation, and both Goldblatt's `V⁺` hyperfinite-dimensional proof and Luxemburg's FIP proof of the **Hahn–Banach Extension Theorem** (proved from scratch without importing Mathlib's `HahnBanach`).

---

## Context: Whole-Book Autoformalization in the AlphaProof & AlphaProof Code Era (2025–2026)

This repository was engineered using multi-agent, kernel-gated autoformalization inspired by the 2025–2026 wave of Lean 4 formal verification systems:

- **AlphaProof** (*Nature*, November 2025) demonstrated reinforcement-learning mastery of olympiad-level mathematical reasoning inside Lean 4, followed by **AlphaProof Nexus** scaling library-aware premise selection over Mathlib.
- **AlphaProof Code** (Google DeepMind, November 10, 2026) showed that coordinated teams of concurrent agents, gated strictly by Lean 4's small trusted kernel (`0` `sorryAx`, `0` unverified axioms), can synthesize millions of lines of modular Lean 4 proofs (such as full machine-code verification of `libsignal` on AArch64) without hallucination drift because every intermediate claim must pass the Lean kernel before integration.
- Alongside academic and industrial whole-paper / monograph pipelines (**ATLAS / AutoformBot**, **Aristotle**, **Gauss**, **Seed-Prover**, **Leanstral**), textbook-scale autoformalization requires **architectural decomposition**:
  1. Establishing a shared, lock-free foundational spine (`Ch01` → `Ch02` → `Ch03` → `Ch05` → `Ch11` → `Ch12`) whose types (`ℝ*`, `ℕ*`, `ℤ*`, `ℚ*`, `IsInternal`, `IsHyperfinite`, `InternalPartialFun`, `shadow`) match both Mathlib idioms and the textbook's conceptual tower;
  2. Isolating leaf/branch developments (`Ch04`, `Ch06`–`Ch10`, `Ch13`–`Ch19`) in child namespaces (`Goldblatt.ChXX`) so concurrent prover agents can elaborate tens of thousands of lines in parallel with zero Lake build-lock contention or cross-chapter symbol collisions; and
  3. Enforcing a programmatic `MetaM` environment audit (`scripts/verify_axioms.lean`) verifying that every theorem in the umbrella build rests solely on `propext`, `Classical.choice`, and `Quot.sound`.

See [`COVERAGE.md`](./COVERAGE.md) for the complete section-by-section index of formalized definitions, theorems, and exercises.
