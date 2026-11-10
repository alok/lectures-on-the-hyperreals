import LecturesOnTheHyperreals.Ch05_HyperrealsGreatAndSmall
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Chapter 8: Differentiation

Formalization of Robert Goldblatt, *Lectures on the Hyperreals: An Introduction to Nonstandard
Analysis* (GTM 188, Springer, 1998), Chapter 8 (pp. 91–104):

* **§8.1 The Derivative via Infinitesimals (pp. 91–92)**:
  * Nonstandard derivative predicates `HasNSCDerivAt`, `HasNSCDerivWithinAt`,
    `HasNSCRightDerivAt`, and `HasNSCLeftDerivAt`.
  * **Theorem 8.1.1** (`hasDerivAt_iff_hasNSCDerivAt`, `hasDerivWithinAt_iff_hasNSCDerivWithinAt`):
    exact equivalence between classical Weierstrass/filter derivatives and the nonstandard
    infinitesimal Newton-quotient characterization.
  * Uniqueness of the nonstandard derivative (`HasNSCDerivAt.unique`), shadow representation
    `sh((f(x + ε) - f(x)) / ε) = f'(x)` (`HasNSCDerivAt.shadow_div`), **Exercise 8.1.2**
    computing `d/dx (sin x) = cos x` and `d/dx (cos x) = -sin x` directly from `Ch05`
    trigonometric infinitesimals, and non-differentiability of `|x|` at `0`
    (`not_exists_hasNSCDerivAt_abs_zero`).
* **§8.2 Increments and Differentials (pp. 92–93)**:
  * **Theorem 8.2.1** (`HasNSCDerivAt.infClose_starFun`, `HasNSCDerivAt.continuousAt`):
    differentiability at `x` implies microcontinuity and classical continuity at `x`.
  * Increment `nscIncrement` (`Δf`) and differential `nscDifferential` (`df = f'(x) Δx`), showing
    `(Δf - df) / Δx ≈ₕ 0` for nonzero infinitesimal `Δx`.
  * **Theorem 8.2.2 (Incremental Equation)** (`hasNSCDerivAt_iff_incremental_eq`):
    `HasNSCDerivAt f f' x ↔ ∀ Δx, IsInfinitesimal Δx → ∃ η, IsInfinitesimal η ∧
      *f(x + Δx) = f(x) + f' Δx + η Δx`.
* **§8.3 Rules for Derivatives (p. 94)**:
  * Direct nonstandard infinitesimal proofs of the constant, identity, scalar multiple, negation,
    sum, difference, **Leibniz product**, natural power, reciprocal, and **quotient** rules.
* **§8.4 Chain Rule (pp. 94–95)**:
  * Nonstandard proof of `HasNSCDerivAt.comp` via the Incremental Equation (Theorem 8.2.2),
    completely avoiding classical `Δu = 0` case splits.
* **§8.5 Critical Point Theorem, Rolle's Theorem, and Mean Value Theorem (pp. 95–96)**:
  * **Critical Point Theorem** (`HasNSCDerivAt.eq_zero_of_isLocalMax`,
    `HasNSCDerivAt.eq_zero_of_isLocalMin`) proved by comparing `+ε` and `-ε` Newton quotients.
  * Nonstandard Extreme Value Theorem on `[a, b]` via hyperfinite grid maximization + `shadow`,
    deducing **Rolle's Theorem** (`rolle_nsc`), **Mean Value Theorem** (`mvt_nsc`), **Cauchy's
    Generalized MVT** (`cauchy_mvt_nsc`), and zero/sign-of-derivative monotonicity criteria.
* **§8.6 Inverse Function Theorem (pp. 96–97)**:
  * Goldblatt's nonstandard proof of continuity and differentiability (`g'(y) = 1 / f'(x)`) of the
    inverse of a continuous strictly monotone function on `(a, b)`.
* **§8.7–8.8 Partial Derivatives and Total Differentiability in `ℝ²` (pp. 97–100)**:
  * Hyperreal plane closeness vs. infinitesimal Euclidean distance, `HasNSCPartialDeriv₁`,
    `HasNSCPartialDeriv₂`, `HasNSCTotalDerivAt`, **Theorem 8.7.1 (Incremental Equation for Two
    Variables)** from smoothness via hyperreal transfer of 1D MVT, **Exercises 8.8(1)–(2)**, and
    the **Multivariable Chain Rule**.
* **§8.9–8.10 Taylor Series and Higher-Order Incremental Approximation (pp. 100–103)**:
  * Taylor polynomials `taylorPoly`, remainders `taylorRemainder`, nonstandard convergence
    characterization via unlimited `N ∈ ℕ*`, Lagrange remainder and its hyperreal transfer,
    Maclaurin convergence for `cos x` and `exp x` (**Exercise 8.9.1**), **Theorem 8.10.1**,
    **Exercise 8.10.2** (Peano Taylor approximation without continuity of `f^{(n)}`), second
    symmetric difference quotient, and the second-derivative local extremum test.
* **§8.11–8.12 Extending the Incremental Equation (pp. 103–104)**:
  * Points well inside `*(a, b)` (`IsWellInsideIoo`), **Theorem 8.11.1** characterizing continuity
    of `f'` on `(a, b)` via the hyperreal incremental equation on points well inside `*(a, b)`,
    and **Exercises 8.12(1)–(2)** including `f(x) = x² sin(1/x)`.
-/

noncomputable section

namespace Goldblatt.Ch08

open Filter
open Hyperreal (ofSeq ofSeq_lt_ofSeq ofSeq_le_ofSeq ofSeq_surjective)
open scoped Topology BigOperators

/-! ## Algebraic Helpers for `starFun` and Internal Filter Bridges -/

/-- `starFun` of a constant function evaluates to the coerced constant. -/
@[simp]
theorem starFun_const (c : ℝ) (x : ℝ*) : starFun (fun _ ↦ c) x = (c : ℝ*) :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` preserves pointwise addition of functions `ℝ → ℝ`. -/
@[simp]
theorem starFun_add (f g : ℝ → ℝ) (x : ℝ*) :
    starFun (fun t ↦ f t + g t) x = starFun f x + starFun g x :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` preserves pointwise subtraction of functions `ℝ → ℝ`. -/
@[simp]
theorem starFun_sub (f g : ℝ → ℝ) (x : ℝ*) :
    starFun (fun t ↦ f t - g t) x = starFun f x - starFun g x :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` preserves pointwise negation of functions `ℝ → ℝ`. -/
@[simp]
theorem starFun_neg (f : ℝ → ℝ) (x : ℝ*) :
    starFun (fun t ↦ -f t) x = -starFun f x :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` preserves pointwise multiplication of functions `ℝ → ℝ`. -/
@[simp]
theorem starFun_mul (f g : ℝ → ℝ) (x : ℝ*) :
    starFun (fun t ↦ f t * g t) x = starFun f x * starFun g x :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` preserves scalar multiplication by a real constant. -/
@[simp]
theorem starFun_const_mul (c : ℝ) (f : ℝ → ℝ) (x : ℝ*) :
    starFun (fun t ↦ c * f t) x = (c : ℝ*) * starFun f x :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` preserves natural-number powers of functions `ℝ → ℝ`. -/
@[simp]
theorem starFun_pow (f : ℝ → ℝ) (n : ℕ) (x : ℝ*) :
    starFun (fun t ↦ f t ^ n) x = starFun f x ^ n :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` preserves pointwise reciprocals of functions `ℝ → ℝ`. -/
@[simp]
theorem starFun_inv (g : ℝ → ℝ) (x : ℝ*) :
    starFun (fun t ↦ (g t)⁻¹) x = (starFun g x)⁻¹ :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` preserves pointwise quotients of functions `ℝ → ℝ`. -/
@[simp]
theorem starFun_div (f g : ℝ → ℝ) (x : ℝ*) :
    starFun (fun t ↦ f t / g t) x = starFun f x / starFun g x :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starSet` of an open downward ray `(-∞, b)` is `(-∞, (b : ℝ*))`. -/
@[simp]
theorem starSet_Iio (b : ℝ) :
    starSet (Set.Iio b) = Set.Iio (b : ℝ*) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp only [ofSeq_mem_starSet, Set.mem_Iio]
  exact ⟨ofSeq_lt_ofSeq.2, ofSeq_lt_ofSeq.1⟩

/-- Internal bridge: classical `Tendsto g (𝓝[A \ {x}] x) (𝓝 L)` is equivalent to `starFun g`
mapping every `x + Δx ∈ *A` with nonzero infinitesimal `Δx` infinitely close to `L`. -/
private theorem tendsto_nhdsWithin_sdiff_singleton_iff {g : ℝ → ℝ} {A : Set ℝ} {x L : ℝ} :
    Tendsto g (𝓝[A \ {x}] x) (𝓝 L) ↔
      ∀ Δx : ℝ*, IsInfinitesimal Δx → Δx ≠ 0 → (x : ℝ*) + Δx ∈ starSet A →
        starFun g ((x : ℝ*) + Δx) ≈ₕ (L : ℝ*) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro hg Δx hΔ hne hmem ε hε
    obtain ⟨δ, hδ, hball⟩ := hg ε hε
    have hlt : |Δx| < (δ : ℝ*) := hΔ δ hδ
    rcases ofSeq_surjective Δx with ⟨r, rfl⟩
    have hr_lt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |r n| < δ := ofSeq_lt_ofSeq.1 hlt
    have hr_ne : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ≠ 0 :=
      Ultrafilter.eventually_not.2 fun h0 ↦ hne (Germ.coe_eq.2 h0)
    have hr_A : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), x + r n ∈ A :=
      ofSeq_mem_starSet.1 hmem
    refine ofSeq_lt_ofSeq.2 (((hr_lt.and hr_ne).and hr_A).mono fun n ⟨⟨hn_lt, hn_ne⟩, hn_A⟩ ↦ ?_)
    change |g (x + r n) - L| < ε
    have hmem_diff : x + r n ∈ A \ {x} :=
      ⟨hn_A, fun heq ↦ hn_ne (by linarith [Set.mem_singleton_iff.1 heq])⟩
    have hdist : dist (x + r n) x < δ := by
      simpa only [Real.dist_eq, add_sub_cancel_left] using hn_lt
    simpa only [Real.dist_eq] using hball hmem_diff hdist
  · intro h ε hε
    by_contra hnot
    push Not at hnot
    have hex : ∀ n : ℕ, ∃ y : ℝ, (y ∈ A ∧ y ≠ x) ∧ |y - x| < ((n : ℝ) + 1)⁻¹ ∧ ε ≤ |g y - L| := by
      intro n
      obtain ⟨y, hy_mem, hy_dist, hy_ge⟩ := hnot (((n : ℝ) + 1)⁻¹) (by positivity)
      exact ⟨y, ⟨hy_mem.1, hy_mem.2⟩, by simpa [Real.dist_eq] using hy_dist,
        by simpa [Real.dist_eq] using hy_ge⟩
    choose y hy using hex
    let r : ℕ → ℝ := fun n ↦ y n - x
    have hr_inf : IsInfinitesimal (ofSeq r) := by
      apply ofSeq_infinitesimal_of_tendsto_zero
      refine squeeze_zero_norm (fun n ↦ ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [Real.norm_eq_abs, one_div] using (hy n).2.1.le
    have hr_ne : ofSeq r ≠ 0 := by
      intro h0
      have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), y n - x = 0 := Germ.coe_eq.1 h0
      obtain ⟨n, hn⟩ := hev.exists
      exact (hy n).1.2 (sub_eq_zero.1 hn)
    have hr_mem : (x : ℝ*) + ofSeq r ∈ starSet A := by
      have heq : (x : ℝ*) + ofSeq r = ofSeq y :=
        Germ.coe_eq.2 (Eventually.of_forall fun n ↦ add_sub_cancel x (y n))
      rw [heq, ofSeq_mem_starSet]
      exact Eventually.of_forall fun n ↦ (hy n).1.1
    have hclose : starFun g ((x : ℝ*) + ofSeq r) ≈ₕ (L : ℝ*) := h (ofSeq r) hr_inf hr_ne hr_mem
    have hlt_eps : |starFun g ((x : ℝ*) + ofSeq r) - (L : ℝ*)| < (ε : ℝ*) := hclose ε hε
    have heq : (x : ℝ*) + ofSeq r = ofSeq y :=
      Germ.coe_eq.2 (Eventually.of_forall fun n ↦ add_sub_cancel x (y n))
    rw [heq] at hlt_eps
    have hge_eps : (ε : ℝ*) ≤ |starFun g (ofSeq y) - (L : ℝ*)| :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (hy n).2.2)
    exact not_lt_of_ge hge_eps hlt_eps

/-- Internal bridge: classical `ContinuousAt f x` is equivalent to microcontinuity at `x`. -/
private theorem continuousAt_iff_infClose_starFun {f : ℝ → ℝ} {x : ℝ} :
    ContinuousAt f x ↔ ∀ Δx : ℝ*, IsInfinitesimal Δx → starFun f ((x : ℝ*) + Δx) ≈ₕ (f x : ℝ*) := by
  rw [Metric.continuousAt_iff]
  constructor
  · intro hf Δx hΔ ε hε
    obtain ⟨δ, hδ, hball⟩ := hf ε hε
    have hlt : |Δx| < (δ : ℝ*) := hΔ δ hδ
    rcases ofSeq_surjective Δx with ⟨r, rfl⟩
    have hr_lt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |r n| < δ := ofSeq_lt_ofSeq.1 hlt
    refine ofSeq_lt_ofSeq.2 (hr_lt.mono fun n hn ↦ ?_)
    change |f (x + r n) - f x| < ε
    have hdist : dist (x + r n) x < δ := by
      simpa only [Real.dist_eq, add_sub_cancel_left] using hn
    simpa only [Real.dist_eq] using hball hdist
  · intro h ε hε
    by_contra hnot
    push Not at hnot
    have hex : ∀ n : ℕ, ∃ y : ℝ, |y - x| < ((n : ℝ) + 1)⁻¹ ∧ ε ≤ |f y - f x| := by
      intro n
      obtain ⟨y, hy_dist, hy_ge⟩ := hnot (((n : ℝ) + 1)⁻¹) (by positivity)
      exact ⟨y, by simpa [Real.dist_eq] using hy_dist, by simpa [Real.dist_eq] using hy_ge⟩
    choose y hy using hex
    let r : ℕ → ℝ := fun n ↦ y n - x
    have hr_inf : IsInfinitesimal (ofSeq r) := by
      apply ofSeq_infinitesimal_of_tendsto_zero
      refine squeeze_zero_norm (fun n ↦ ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [Real.norm_eq_abs, one_div] using (hy n).1.le
    have hclose := h (ofSeq r) hr_inf ε hε
    have heq : (x : ℝ*) + ofSeq r = ofSeq y :=
      Germ.coe_eq.2 (Eventually.of_forall fun n ↦ add_sub_cancel x (y n))
    rw [heq] at hclose
    have hge : (ε : ℝ*) ≤ |starFun f (ofSeq y) - (f x : ℝ*)| :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (hy n).2)
    exact not_lt_of_ge hge hclose

/-- Internal bridge: `ContinuousOn f A` implies microcontinuity at every `c ∈ A` along points
in `*A`. -/
private theorem continuousOn_infClose_starFun {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (hf : ContinuousOn f A) (hc : c ∈ A) {y : ℝ*} (hyA : y ∈ starSet A) (hyc : y ≈ₕ (c : ℝ*)) :
    starFun f y ≈ₕ (f c : ℝ*) := by
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hf c hc) ε hε
  have hlt : |y - (c : ℝ*)| < (δ : ℝ*) := hyc δ hδ
  rcases ofSeq_surjective y with ⟨r, rfl⟩
  have hr_lt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |r n - c| < δ := ofSeq_lt_ofSeq.1 hlt
  have hr_A : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ A := ofSeq_mem_starSet.1 hyA
  refine ofSeq_lt_ofSeq.2 ((hr_A.and hr_lt).mono fun n ⟨hnA, hnlt⟩ ↦ ?_)
  change |f (r n) - f c| < ε
  have hdist : dist (r n) c < δ := by simpa only [Real.dist_eq] using hnlt
  simpa only [Real.dist_eq] using hball hnA hdist

/-! ## §8.1 The Derivative via Infinitesimals (pp. 91–92) -/

/-- Goldblatt §8.1, Theorem 8.1.1 (p. 91): Nonstandard characterization of `f'(x) = f'`:
for every nonzero infinitesimal `Δx ∈ ℝ*`, the hyperreal Newton quotient
`(*f(x + Δx) - f(x)) / Δx` is infinitely close to `f'`. -/
def HasNSCDerivAt (f : ℝ → ℝ) (f' : ℝ) (x : ℝ) : Prop :=
  ∀ Δx : ℝ*, IsInfinitesimal Δx → Δx ≠ 0 →
    (starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx ≈ₕ (f' : ℝ*)

/-- Nonstandard derivative of `f` within a subset `A ⊆ ℝ` at `x ∈ ℝ`: for every nonzero
infinitesimal `Δx` with `x + Δx ∈ *A`, the Newton quotient is infinitely close to `f'`. -/
def HasNSCDerivWithinAt (f : ℝ → ℝ) (f' : ℝ) (A : Set ℝ) (x : ℝ) : Prop :=
  ∀ Δx : ℝ*, IsInfinitesimal Δx → Δx ≠ 0 → (x : ℝ*) + Δx ∈ starSet A →
    (starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx ≈ₕ (f' : ℝ*)

/-- Goldblatt §8.1 (p. 92): Right-hand nonstandard derivative at `x`, requiring the Newton
quotient to be infinitely close to `f'` for all positive infinitesimals `Δx > 0`. -/
def HasNSCRightDerivAt (f : ℝ → ℝ) (f' : ℝ) (x : ℝ) : Prop :=
  ∀ Δx : ℝ*, IsPosInfinitesimal Δx →
    (starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx ≈ₕ (f' : ℝ*)

/-- Goldblatt §8.1 (p. 92): Left-hand nonstandard derivative at `x`, requiring the Newton
quotient to be infinitely close to `f'` for all negative infinitesimals `Δx < 0`. -/
def HasNSCLeftDerivAt (f : ℝ → ℝ) (f' : ℝ) (x : ℝ) : Prop :=
  ∀ Δx : ℝ*, IsNegInfinitesimal Δx →
    (starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx ≈ₕ (f' : ℝ*)

/-- `HasNSCDerivWithinAt` on `Set.univ` coincides with `HasNSCDerivAt`. -/
@[simp]
theorem hasNSCDerivWithinAt_univ_iff {f : ℝ → ℝ} {f' x : ℝ} :
    HasNSCDerivWithinAt f f' Set.univ x ↔ HasNSCDerivAt f f' x := by
  simp [HasNSCDerivWithinAt, HasNSCDerivAt]

/-- Equivalence between `HasDerivWithinAt` and `HasNSCDerivWithinAt` on any subset `A ⊆ ℝ`. -/
theorem hasDerivWithinAt_iff_hasNSCDerivWithinAt {f : ℝ → ℝ} {f' : ℝ} {A : Set ℝ} {x : ℝ} :
    HasDerivWithinAt f f' A x ↔ HasNSCDerivWithinAt f f' A x := by
  rw [hasDerivWithinAt_iff_tendsto_slope, tendsto_nhdsWithin_sdiff_singleton_iff]
  constructor
  · intro h Δx hΔ hne hmem
    have h1 := h Δx hΔ hne hmem
    have heq : starFun (slope f x) ((x : ℝ*) + Δx) =
        (starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx := by
      rcases ofSeq_surjective Δx with ⟨r, rfl⟩
      refine Germ.coe_eq.2 (Eventually.of_forall fun n ↦ ?_)
      simp [slope_def_field]
    rwa [heq] at h1
  · intro h Δx hΔ hne hmem
    have h1 := h Δx hΔ hne hmem
    have heq : starFun (slope f x) ((x : ℝ*) + Δx) =
        (starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx := by
      rcases ofSeq_surjective Δx with ⟨r, rfl⟩
      refine Germ.coe_eq.2 (Eventually.of_forall fun n ↦ ?_)
      simp [slope_def_field]
    rwa [heq]

/-- **Goldblatt Theorem 8.1.1 (pp. 91–92)**: `f' ∈ ℝ` is the classical derivative of `f` at `x ∈ ℝ`
if and only if `(*f(x + Δx) - f(x)) / Δx ≈ₕ f'` for every nonzero infinitesimal `Δx ∈ ℝ*`. -/
theorem hasDerivAt_iff_hasNSCDerivAt {f : ℝ → ℝ} {f' x : ℝ} :
    HasDerivAt f f' x ↔ HasNSCDerivAt f f' x := by
  rw [← hasDerivWithinAt_univ, hasDerivWithinAt_iff_hasNSCDerivWithinAt,
    hasNSCDerivWithinAt_univ_iff]

/-- Goldblatt §8.1 (p. 92): Classical right-hand derivative `HasDerivWithinAt f f' (Set.Ioi x) x`
is equivalent to `HasNSCRightDerivAt f f' x`. -/
theorem hasDerivWithinAt_Ioi_iff_hasNSCRightDerivAt {f : ℝ → ℝ} {f' x : ℝ} :
    HasDerivWithinAt f f' (Set.Ioi x) x ↔ HasNSCRightDerivAt f f' x := by
  rw [hasDerivWithinAt_iff_hasNSCDerivWithinAt]
  constructor
  · intro h Δx hpos
    have hinf : IsInfinitesimal Δx := isInfinitesimal_iff_trichotomy.2 (Or.inl hpos)
    have hmem : (x : ℝ*) + Δx ∈ starSet (Set.Ioi x) := by
      rw [starSet_Ioi, Set.mem_Ioi]
      linarith [hpos.1]
    exact h Δx hinf hpos.1.ne' hmem
  · intro h Δx hinf _ hmem
    rw [starSet_Ioi, Set.mem_Ioi] at hmem
    have hpos : 0 < Δx := by linarith
    exact h Δx ⟨hpos, fun r hr ↦ (le_abs_self Δx).trans_lt (hinf r hr)⟩

/-- Goldblatt §8.1 (p. 92): Classical left-hand derivative `HasDerivWithinAt f f' (Set.Iio x) x`
is equivalent to `HasNSCLeftDerivAt f f' x`. -/
theorem hasDerivWithinAt_Iio_iff_hasNSCLeftDerivAt {f : ℝ → ℝ} {f' x : ℝ} :
    HasDerivWithinAt f f' (Set.Iio x) x ↔ HasNSCLeftDerivAt f f' x := by
  rw [hasDerivWithinAt_iff_hasNSCDerivWithinAt]
  constructor
  · intro h Δx hneg
    have hinf : IsInfinitesimal Δx := isInfinitesimal_iff_trichotomy.2 (Or.inr (Or.inl hneg))
    have hmem : (x : ℝ*) + Δx ∈ starSet (Set.Iio x) := by
      rw [starSet_Iio, Set.mem_Iio]
      linarith [hneg.1]
    exact h Δx hinf hneg.1.ne hmem
  · intro h Δx hinf _ hmem
    rw [starSet_Iio, Set.mem_Iio] at hmem
    have hneg : Δx < 0 := by linarith
    refine h Δx ⟨hneg, fun r hr ↦ ?_⟩
    have habs : -Δx < (-r : ℝ*) := by
      simpa [abs_of_neg hneg] using hinf (-r) (neg_pos.2 hr)
    linarith

/-- Goldblatt §8.1 (p. 92): Two-sided nonstandard differentiability holds iff both right-hand
and left-hand nonstandard derivatives exist and equal `f'`. -/
theorem hasNSCDerivAt_iff_right_and_left {f : ℝ → ℝ} {f' x : ℝ} :
    HasNSCDerivAt f f' x ↔ HasNSCRightDerivAt f f' x ∧ HasNSCLeftDerivAt f f' x := by
  constructor
  · intro h
    exact ⟨fun Δx hpos ↦ h Δx (isInfinitesimal_iff_trichotomy.2 (Or.inl hpos)) hpos.1.ne',
           fun Δx hneg ↦ h Δx (isInfinitesimal_iff_trichotomy.2 (Or.inr (Or.inl hneg))) hneg.1.ne⟩
  · rintro ⟨hr, hl⟩ Δx hinf hne
    rcases isInfinitesimal_iff_trichotomy.1 hinf with hpos | hneg | rfl
    · exact hr Δx hpos
    · exact hl Δx hneg
    · exact absurd rfl hne

/-- Uniqueness of the nonstandard derivative at `x` (proved directly using `Hyperreal.epsilon`). -/
theorem HasNSCDerivAt.unique {f : ℝ → ℝ} {f₁ f₂ x : ℝ}
    (h₁ : HasNSCDerivAt f f₁ x) (h₂ : HasNSCDerivAt f f₂ x) : f₁ = f₂ := by
  have heps_ne : Hyperreal.epsilon ≠ 0 := Hyperreal.epsilon_pos.ne'
  have hc₁ := h₁ Hyperreal.epsilon isInfinitesimal_epsilon heps_ne
  have hc₂ := h₂ Hyperreal.epsilon isInfinitesimal_epsilon heps_ne
  exact coe_eq_of_infClose (hc₁.symm.trans hc₂)

/-- If `HasNSCDerivAt f f' x`, then Mathlib's `deriv f x` equals `f'`. -/
theorem HasNSCDerivAt.deriv_eq {f : ℝ → ℝ} {f' x : ℝ} (h : HasNSCDerivAt f f' x) :
    deriv f x = f' :=
  (hasDerivAt_iff_hasNSCDerivAt.2 h).deriv

/-- Goldblatt §8.1 (p. 92): When `HasNSCDerivAt f f' x`, the Newton quotient is limited and its
shadow is `f'` for every nonzero infinitesimal `Δx`. -/
theorem HasNSCDerivAt.isLimited_newtonQuotient {f : ℝ → ℝ} {f' x : ℝ}
    (h : HasNSCDerivAt f f' x) {Δx : ℝ*} (hΔ : IsInfinitesimal Δx) (hne : Δx ≠ 0) :
    IsLimited ((starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx) := by
  have hclose := h Δx hΔ hne
  have heq : (starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx =
      (f' : ℝ*) + ((starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx - (f' : ℝ*)) := by ring
  rw [heq]
  exact (isLimited_coe f').add hclose.isLimited

/-- Goldblatt §8.1 (p. 92): `f'(x) = sh((*f(x + ε) - f(x)) / ε)` for every nonzero
infinitesimal `ε`. -/
theorem HasNSCDerivAt.shadow_div {f : ℝ → ℝ} {f' x : ℝ}
    (h : HasNSCDerivAt f f' x) {ε : ℝ*} (hε : IsInfinitesimal ε) (hne : ε ≠ 0) :
    shadow ((starFun f ((x : ℝ*) + ε) - (f x : ℝ*)) / ε) = f' :=
  shadow_eq_of_infClose (h ε hε hne)

/-- Addition formula for `starFun Real.sin` lifted from `Real.sin_add`. -/
theorem starFun_sin_add (u v : ℝ*) :
    starFun Real.sin (u + v) =
      starFun Real.sin u * starFun Real.cos v + starFun Real.cos u * starFun Real.sin v := by
  rcases ofSeq_surjective u with ⟨r, rfl⟩
  rcases ofSeq_surjective v with ⟨s, rfl⟩
  exact Germ.coe_eq.2 (Eventually.of_forall fun n ↦ Real.sin_add (r n) (s n))

/-- Addition formula for `starFun Real.cos` lifted from `Real.cos_add`. -/
theorem starFun_cos_add (u v : ℝ*) :
    starFun Real.cos (u + v) =
      starFun Real.cos u * starFun Real.cos v - starFun Real.sin u * starFun Real.sin v := by
  rcases ofSeq_surjective u with ⟨r, rfl⟩
  rcases ofSeq_surjective v with ⟨s, rfl⟩
  exact Germ.coe_eq.2 (Eventually.of_forall fun n ↦ Real.cos_add (r n) (s n))

/-- **Goldblatt Exercise 8.1.2 (p. 92)**: Direct nonstandard proof that the derivative of `sin x`
is `cos x` at every `x ∈ ℝ`, using Theorem 8.1.1 and Exercise 5.7(2) (`sin ε / ε ≈ₕ 1`,
`(cos ε - 1) / ε ≈ₕ 0`). -/
theorem hasNSCDerivAt_sin (x : ℝ) : HasNSCDerivAt Real.sin (Real.cos x) x := by
  intro ε hε hne
  have hquot : (starFun Real.sin ((x : ℝ*) + ε) - (Real.sin x : ℝ*)) / ε =
      (Real.sin x : ℝ*) * ((starFun Real.cos ε - 1) / ε) +
        (Real.cos x : ℝ*) * (starFun Real.sin ε / ε) := by
    rw [starFun_sin_add, starFun_coe, starFun_coe]
    ring
  rw [hquot]
  have h1 : (Real.sin x : ℝ*) * ((starFun Real.cos ε - 1) / ε) ≈ₕ (Real.sin x : ℝ*) * 0 :=
    InfClose.mul_left_of_isLimited (isLimited_coe (Real.sin x))
      (starFun_cos_sub_one_div_infClose_zero hε hne)
  have h2 : (Real.cos x : ℝ*) * (starFun Real.sin ε / ε) ≈ₕ (Real.cos x : ℝ*) * 1 :=
    InfClose.mul_left_of_isLimited (isLimited_coe (Real.cos x))
      (starFun_sin_div_infClose_one hε hne)
  simpa using h1.add h2

/-- Direct nonstandard proof that the derivative of `cos x` is `-sin x` at every `x ∈ ℝ`. -/
theorem hasNSCDerivAt_cos (x : ℝ) : HasNSCDerivAt Real.cos (-Real.sin x) x := by
  intro ε hε hne
  have hquot : (starFun Real.cos ((x : ℝ*) + ε) - (Real.cos x : ℝ*)) / ε =
      (Real.cos x : ℝ*) * ((starFun Real.cos ε - 1) / ε) -
        (Real.sin x : ℝ*) * (starFun Real.sin ε / ε) := by
    rw [starFun_cos_add, starFun_coe, starFun_coe]
    ring
  rw [hquot]
  have h1 : (Real.cos x : ℝ*) * ((starFun Real.cos ε - 1) / ε) ≈ₕ (Real.cos x : ℝ*) * 0 :=
    InfClose.mul_left_of_isLimited (isLimited_coe (Real.cos x))
      (starFun_cos_sub_one_div_infClose_zero hε hne)
  have h2 : (Real.sin x : ℝ*) * (starFun Real.sin ε / ε) ≈ₕ (Real.sin x : ℝ*) * 1 :=
    InfClose.mul_left_of_isLimited (isLimited_coe (Real.sin x))
      (starFun_sin_div_infClose_one hε hne)
  simpa using h1.sub h2

/-- Right-hand nonstandard derivative of `|x|` at `0` is `+1`. -/
theorem hasNSCRightDerivAt_abs_zero : HasNSCRightDerivAt abs 1 0 := by
  intro Δx hpos
  have hquot : (starFun abs (((0 : ℝ) : ℝ*) + Δx) - ((abs (0 : ℝ) : ℝ) : ℝ*)) / Δx =
      ((1 : ℝ) : ℝ*) := by
    rw [starFun_abs, abs_zero, Hyperreal.coe_zero, zero_add, sub_zero, abs_of_pos hpos.1,
      div_self hpos.1.ne', Hyperreal.coe_one]
  rw [hquot]

/-- Left-hand nonstandard derivative of `|x|` at `0` is `-1`. -/
theorem hasNSCLeftDerivAt_abs_zero : HasNSCLeftDerivAt abs (-1) 0 := by
  intro Δx hneg
  have hquot : (starFun abs (((0 : ℝ) : ℝ*) + Δx) - ((abs (0 : ℝ) : ℝ) : ℝ*)) / Δx =
      ((-1 : ℝ) : ℝ*) := by
    rw [starFun_abs, abs_zero, Hyperreal.coe_zero, zero_add, sub_zero, abs_of_neg hneg.1,
      neg_div_self hneg.1.ne, Hyperreal.coe_neg, Hyperreal.coe_one]
  rw [hquot]

/-- Nonstandard proof that `|x|` is not differentiable at `0`: `Δx = +ε` gives Newton quotient `+1`
whereas `Δx = -ε` gives `-1`. -/
theorem not_exists_hasNSCDerivAt_abs_zero : ¬ ∃ L : ℝ, HasNSCDerivAt abs L 0 := by
  rintro ⟨L, hL⟩
  rw [hasNSCDerivAt_iff_right_and_left] at hL
  have heps_pos : IsPosInfinitesimal Hyperreal.epsilon :=
    ⟨Hyperreal.epsilon_pos, fun _ hr ↦ Hyperreal.epsilon_lt_of_pos hr⟩
  have heps_neg : IsNegInfinitesimal (-Hyperreal.epsilon) := by
    refine ⟨neg_lt_zero.2 Hyperreal.epsilon_pos, fun r hr ↦ ?_⟩
    have hlt := Hyperreal.epsilon_lt_of_pos (neg_pos.2 hr)
    rw [Hyperreal.coe_neg] at hlt
    linarith
  have h1 : (1 : ℝ) = L := coe_eq_of_infClose
    ((hasNSCRightDerivAt_abs_zero Hyperreal.epsilon heps_pos).symm.trans
      (hL.1 Hyperreal.epsilon heps_pos))
  have h2 : (-1 : ℝ) = L := coe_eq_of_infClose
    ((hasNSCLeftDerivAt_abs_zero (-Hyperreal.epsilon) heps_neg).symm.trans
      (hL.2 (-Hyperreal.epsilon) heps_neg))
  linarith

/-! ## §8.2 Increments, Differentials, Continuity, and the Incremental Equation (pp. 92–93) -/

/-- Goldblatt §8.2 (p. 92): The increment `Δf(x, Δx) = *f(x + Δx) - f(x)` of `f` at `x`
corresponding to a hyperreal increment `Δx`. -/
def nscIncrement (f : ℝ → ℝ) (x : ℝ) (Δx : ℝ*) : ℝ* :=
  starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)

/-- Goldblatt §8.2 (p. 93): The differential `df = f'(x) Δx` along the tangent line at `x`. -/
def nscDifferential (f' : ℝ) (Δx : ℝ*) : ℝ* :=
  (f' : ℝ*) * Δx

/-- Goldblatt §8.2 (p. 92): If `HasNSCDerivAt f f' x` and `Δx` is infinitesimal, then the increment
`Δf = *f(x + Δx) - f(x)` is infinitesimal (`Δf = (Δf / Δx) * Δx`). -/
theorem HasNSCDerivAt.isInfinitesimal_increment {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasNSCDerivAt f f' x) {Δx : ℝ*} (hΔ : IsInfinitesimal Δx) :
    IsInfinitesimal (nscIncrement f x Δx) := by
  by_cases hne : Δx = 0
  · subst hne
    simp [nscIncrement, isInfinitesimal_zero]
  · have hmul : nscIncrement f x Δx = (nscIncrement f x Δx / Δx) * Δx :=
      (div_mul_cancel₀ _ hne).symm
    rw [hmul]
    exact (hf.isLimited_newtonQuotient hΔ hne).mul_isInfinitesimal hΔ

/-- **Goldblatt Theorem 8.2.1 (Microcontinuity, p. 92)**: If `f` is differentiable at `x ∈ ℝ`,
then `*f(x + Δx) ≈ₕ f(x)` for every infinitesimal `Δx ∈ ℝ*`. -/
theorem HasNSCDerivAt.infClose_starFun {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasNSCDerivAt f f' x) {Δx : ℝ*} (hΔ : IsInfinitesimal Δx) :
    starFun f ((x : ℝ*) + Δx) ≈ₕ (f x : ℝ*) :=
  hf.isInfinitesimal_increment hΔ

/-- Variant of Theorem 8.2.1: if `HasNSCDerivAt f f' x` and `y ≈ₕ x`, then `*f(y) ≈ₕ f(x)`. -/
theorem HasNSCDerivAt.infClose_of_infClose {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasNSCDerivAt f f' x) {y : ℝ*} (hy : y ≈ₕ (x : ℝ*)) :
    starFun f y ≈ₕ (f x : ℝ*) := by
  have hy_eq : y = (x : ℝ*) + (y - (x : ℝ*)) := by ring
  rw [hy_eq]
  exact hf.infClose_starFun hy

/-- **Goldblatt Theorem 8.2.1 (p. 92)**: If `f` is differentiable at `x ∈ ℝ`, then `f` is
continuous at `x`. -/
theorem HasNSCDerivAt.continuousAt {f : ℝ → ℝ} {f' x : ℝ} (hf : HasNSCDerivAt f f' x) :
    ContinuousAt f x :=
  continuousAt_iff_infClose_starFun.2 fun _ hΔ ↦ hf.infClose_starFun hΔ

/-- Goldblatt §8.2 (p. 93): For infinitesimal `Δx`, the differential `df = f'(x) Δx` is
infinitesimal, and `Δf ≈ₕ df`. -/
theorem HasNSCDerivAt.isInfinitesimal_differential (f' : ℝ) {Δx : ℝ*} (hΔ : IsInfinitesimal Δx) :
    IsInfinitesimal (nscDifferential f' Δx) :=
  (isLimited_coe f').mul_isInfinitesimal hΔ

/-- Goldblatt §8.2 (p. 93): `Δf ≈ₕ df` for any infinitesimal increment `Δx`. -/
theorem HasNSCDerivAt.increment_infClose_differential {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasNSCDerivAt f f' x) {Δx : ℝ*} (hΔ : IsInfinitesimal Δx) :
    nscIncrement f x Δx ≈ₕ nscDifferential f' Δx :=
  (hf.isInfinitesimal_increment hΔ).sub (HasNSCDerivAt.isInfinitesimal_differential f' hΔ)

/-- Goldblatt §8.2 (p. 93): `Δf - df` is infinitely smaller than `Δx`:
`(Δf - df) / Δx ≈ₕ 0` for every nonzero infinitesimal `Δx`. -/
theorem HasNSCDerivAt.increment_sub_differential_div_infClose_zero {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasNSCDerivAt f f' x) {Δx : ℝ*} (hΔ : IsInfinitesimal Δx) (hne : Δx ≠ 0) :
    (nscIncrement f x Δx - nscDifferential f' Δx) / Δx ≈ₕ 0 := by
  rw [infClose_zero_iff]
  have heq : (nscIncrement f x Δx - nscDifferential f' Δx) / Δx =
      (starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx - (f' : ℝ*) := by
    unfold nscIncrement nscDifferential
    rw [sub_div, mul_div_cancel_right₀ _ hne]
  rw [heq]
  exact hf Δx hΔ hne

/-- **Goldblatt Theorem 8.2.2 (Incremental Equation, p. 93)**:
`HasNSCDerivAt f f' x` holds if and only if for every infinitesimal `Δx ∈ ℝ*` (including `Δx = 0`)
there exists an infinitesimal `η ∈ ℝ*` such that
`*f(x + Δx) = f(x) + f' * Δx + η * Δx`. -/
theorem hasNSCDerivAt_iff_incremental_eq {f : ℝ → ℝ} {f' x : ℝ} :
    HasNSCDerivAt f f' x ↔
      ∀ Δx : ℝ*, IsInfinitesimal Δx →
        ∃ η : ℝ*, IsInfinitesimal η ∧
          starFun f ((x : ℝ*) + Δx) = (f x : ℝ*) + (f' : ℝ*) * Δx + η * Δx := by
  constructor
  · intro hf Δx hΔ
    by_cases hne : Δx = 0
    · subst hne
      exact ⟨0, isInfinitesimal_zero, by simp⟩
    · refine ⟨(starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx - (f' : ℝ*), hf Δx hΔ hne, ?_⟩
      have hmul : ((starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx) * Δx =
          starFun f ((x : ℝ*) + Δx) - (f x : ℝ*) := div_mul_cancel₀ _ hne
      linarith
  · intro h Δx hΔ hne
    obtain ⟨η, hη, heq⟩ := h Δx hΔ
    have hquot : (starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx - (f' : ℝ*) = η := by
      have hsub : starFun f ((x : ℝ*) + Δx) - (f x : ℝ*) = ((f' : ℝ*) + η) * Δx := by linarith
      rw [hsub, mul_div_cancel_right₀ _ hne]
      ring
    unfold InfClose
    rwa [hquot]

/-- Forward projection of Theorem 8.2.2 (Goldblatt p. 93). -/
theorem HasNSCDerivAt.exists_incremental_eq {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasNSCDerivAt f f' x) {Δx : ℝ*} (hΔ : IsInfinitesimal Δx) :
    ∃ η : ℝ*, IsInfinitesimal η ∧
      starFun f ((x : ℝ*) + Δx) = (f x : ℝ*) + (f' : ℝ*) * Δx + η * Δx :=
  hasNSCDerivAt_iff_incremental_eq.1 hf Δx hΔ

/-! ## §8.3 Rules for Derivatives via Infinitesimals (p. 94) -/

/-- Constant rule via infinitesimals: `d/dx (c) = 0`. -/
theorem hasNSCDerivAt_const (c x : ℝ) : HasNSCDerivAt (fun _ ↦ c) 0 x := by
  intro Δx _ _
  simp [InfClose.refl]

/-- Identity rule via infinitesimals: `d/dx (x) = 1`. -/
theorem hasNSCDerivAt_id (x : ℝ) : HasNSCDerivAt (fun t ↦ t) 1 x := by
  intro Δx _ hne
  have hid : starFun (fun t ↦ t) ((x : ℝ*) + Δx) = (x : ℝ*) + Δx :=
    congrFun starFun_id ((x : ℝ*) + Δx)
  have h : (starFun (fun t ↦ t) ((x : ℝ*) + Δx) - (x : ℝ*)) / Δx = (1 : ℝ*) := by
    rw [hid, add_sub_cancel_left, div_self hne]
  rw [h]
  exact InfClose.refl _

/-- Negation rule via infinitesimals: `(-f)'(x) = -f'(x)`. -/
theorem HasNSCDerivAt.neg {f : ℝ → ℝ} {f' x : ℝ} (hf : HasNSCDerivAt f f' x) :
    HasNSCDerivAt (fun t ↦ -f t) (-f') x := by
  intro Δx hΔ hne
  have heq : (starFun (fun t ↦ -f t) ((x : ℝ*) + Δx) - (-f x : ℝ)) / Δx =
      -((starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx) := by
    rw [starFun_neg, Hyperreal.coe_neg]
    ring
  rw [heq, Hyperreal.coe_neg]
  exact (hf Δx hΔ hne).neg

/-- Scalar multiple rule via infinitesimals: `(c * f)'(x) = c * f'(x)`. -/
theorem HasNSCDerivAt.const_mul (c : ℝ) {f : ℝ → ℝ} {f' x : ℝ} (hf : HasNSCDerivAt f f' x) :
    HasNSCDerivAt (fun t ↦ c * f t) (c * f') x := by
  intro Δx hΔ hne
  have heq : (starFun (fun t ↦ c * f t) ((x : ℝ*) + Δx) - ((c * f x : ℝ) : ℝ*)) / Δx =
      (c : ℝ*) * ((starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx) := by
    rw [starFun_const_mul, Hyperreal.coe_mul]
    ring
  rw [heq, Hyperreal.coe_mul]
  exact InfClose.mul_left_of_isLimited (isLimited_coe c) (hf Δx hΔ hne)

/-- **Goldblatt §8.3(1) (Sum Rule, p. 94)**: `(f + g)'(x) = f'(x) + g'(x)` proved via
infinitesimals. -/
theorem HasNSCDerivAt.add {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasNSCDerivAt f f' x) (hg : HasNSCDerivAt g g' x) :
    HasNSCDerivAt (fun t ↦ f t + g t) (f' + g') x := by
  intro Δx hΔ hne
  have heq : (starFun (fun t ↦ f t + g t) ((x : ℝ*) + Δx) - ((f x + g x : ℝ) : ℝ*)) / Δx =
      (starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx +
        (starFun g ((x : ℝ*) + Δx) - (g x : ℝ*)) / Δx := by
    rw [starFun_add, Hyperreal.coe_add]
    ring
  rw [heq, Hyperreal.coe_add]
  exact (hf Δx hΔ hne).add (hg Δx hΔ hne)

/-- Difference rule via infinitesimals: `(f - g)'(x) = f'(x) - g'(x)`. -/
theorem HasNSCDerivAt.sub {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasNSCDerivAt f f' x) (hg : HasNSCDerivAt g g' x) :
    HasNSCDerivAt (fun t ↦ f t - g t) (f' - g') x := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- **Goldblatt §8.3(2) (Leibniz Product Rule, p. 94)**:
`(f * g)'(x) = f'(x) g(x) + f(x) g'(x)`, proved using Goldblatt's exact infinitesimal decomposition
`Δ(fg) / Δx = (Δf / Δx) g(x) + f(x) (Δg / Δx) + Δf (Δg / Δx)`. -/
theorem HasNSCDerivAt.mul {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasNSCDerivAt f f' x) (hg : HasNSCDerivAt g g' x) :
    HasNSCDerivAt (fun t ↦ f t * g t) (f' * g x + f x * g') x := by
  intro Δx hΔ hne
  set Δf := starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)
  set Δg := starFun g ((x : ℝ*) + Δx) - (g x : ℝ*)
  have hdecomp :
      (starFun (fun t ↦ f t * g t) ((x : ℝ*) + Δx) - ((f x * g x : ℝ) : ℝ*)) / Δx =
        (Δf / Δx) * (g x : ℝ*) + (f x : ℝ*) * (Δg / Δx) + Δf * (Δg / Δx) := by
    rw [starFun_mul, Hyperreal.coe_mul]
    have hf_eq : starFun f ((x : ℝ*) + Δx) = (f x : ℝ*) + Δf := by ring
    have hg_eq : starFun g ((x : ℝ*) + Δx) = (g x : ℝ*) + Δg := by ring
    rw [hf_eq, hg_eq]
    ring
  rw [hdecomp]
  have h1 : (Δf / Δx) * (g x : ℝ*) ≈ₕ (f' : ℝ*) * (g x : ℝ*) := by
    rw [mul_comm, mul_comm (f' : ℝ*)]
    exact InfClose.mul_left_of_isLimited (isLimited_coe (g x)) (hf Δx hΔ hne)
  have h2 : (f x : ℝ*) * (Δg / Δx) ≈ₕ (f x : ℝ*) * (g' : ℝ*) :=
    InfClose.mul_left_of_isLimited (isLimited_coe (f x)) (hg Δx hΔ hne)
  have h3 : Δf * (Δg / Δx) ≈ₕ 0 := by
    rw [infClose_zero_iff]
    exact (hf.isInfinitesimal_increment hΔ).mul_isLimited (hg.isLimited_newtonQuotient hΔ hne)
  have htarget : (((f' * g x + f x * g' : ℝ)) : ℝ*) =
      (f' : ℝ*) * (g x : ℝ*) + (f x : ℝ*) * (g' : ℝ*) + 0 := by
    push_cast
    ring
  rw [htarget]
  exact (h1.add h2).add h3

/-- Power rule `d/dx (x^n) = n x^(n-1)` proved directly by induction from the nonstandard
Leibniz product rule. -/
theorem hasNSCDerivAt_pow (n : ℕ) (x : ℝ) :
    HasNSCDerivAt (fun t ↦ t ^ n) ((n : ℝ) * x ^ (n - 1)) x := by
  induction n with
  | zero =>
      simpa using hasNSCDerivAt_const 1 x
  | succ k ih =>
      have hmul := ih.mul (hasNSCDerivAt_id x)
      have hderiv : ((k : ℝ) * x ^ (k - 1)) * x + x ^ k * 1 = ((k + 1 : ℕ) : ℝ) * x ^ k := by
        cases k with
        | zero => simp
        | succ m =>
            simp only [Nat.add_sub_cancel]
            push_cast
            ring
      have hfn : (fun t : ℝ ↦ t ^ (k + 1)) = (fun t : ℝ ↦ t ^ k * t) := by
        ext t
        exact pow_succ t k
      rw [hfn, Nat.add_sub_cancel, ← hderiv]
      exact hmul

/-- Reciprocal rule `(1 / g)'(x) = -g'(x) / g(x)^2` proved directly via infinitesimals. -/
theorem HasNSCDerivAt.inv {g : ℝ → ℝ} {g' x : ℝ}
    (hg : HasNSCDerivAt g g' x) (hgx : g x ≠ 0) :
    HasNSCDerivAt (fun t ↦ (g t)⁻¹) (-g' / (g x) ^ 2) x := by
  intro Δx hΔ hne
  have hg_close : starFun g ((x : ℝ*) + Δx) ≈ₕ (g x : ℝ*) := hg.infClose_starFun hΔ
  have hgx_app : IsAppreciable (g x : ℝ*) := isAppreciable_coe_iff.2 hgx
  have hgΔ_app : IsAppreciable (starFun g ((x : ℝ*) + Δx)) := by
    have : starFun g ((x : ℝ*) + Δx) = (g x : ℝ*) + (starFun g ((x : ℝ*) + Δx) - (g x : ℝ*)) := by
      ring
    rw [this]
    exact hgx_app.add_isInfinitesimal hg_close
  have hgΔ_ne : starFun g ((x : ℝ*) + Δx) ≠ 0 := hgΔ_app.ne_zero
  have hgx_ne : (g x : ℝ*) ≠ 0 := hgx_app.ne_zero
  have hquot :
      (starFun (fun t ↦ (g t)⁻¹) ((x : ℝ*) + Δx) - ((g x)⁻¹ : ℝ)) / Δx =
        (-((starFun g ((x : ℝ*) + Δx) - (g x : ℝ*)) / Δx)) /
          (starFun g ((x : ℝ*) + Δx) * (g x : ℝ*)) := by
    rw [starFun_inv, Hyperreal.coe_inv]
    field_simp [hgΔ_ne, hgx_ne, hne]
    ring
  rw [hquot]
  have hnum_close : -((starFun g ((x : ℝ*) + Δx) - (g x : ℝ*)) / Δx) ≈ₕ -(g' : ℝ*) :=
    (hg Δx hΔ hne).neg
  have hnum_lim : IsLimited (-((starFun g ((x : ℝ*) + Δx) - (g x : ℝ*)) / Δx)) :=
    (hg.isLimited_newtonQuotient hΔ hne).neg
  have hden_close : starFun g ((x : ℝ*) + Δx) * (g x : ℝ*) ≈ₕ (g x : ℝ*) * (g x : ℝ*) :=
    InfClose.mul hgΔ_app.1 hgx_app.1 hg_close (InfClose.refl _)
  have hden_app : IsAppreciable (starFun g ((x : ℝ*) + Δx) * (g x : ℝ*)) :=
    hgΔ_app.mul hgx_app
  have htarget : (((-g' / (g x) ^ 2 : ℝ)) : ℝ*) = (-(g' : ℝ*)) / ((g x : ℝ*) * (g x : ℝ*)) := by
    rw [sq, Hyperreal.coe_div, Hyperreal.coe_neg, Hyperreal.coe_mul]
  rw [htarget]
  exact InfClose.div hnum_lim hden_app hnum_close hden_close

/-- **Goldblatt §8.3(3) (Quotient Rule, p. 94)**:
`(f / g)'(x) = (f'(x) g(x) - f(x) g'(x)) / g(x)^2` when `g(x) ≠ 0`. -/
theorem HasNSCDerivAt.div {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasNSCDerivAt f f' x) (hg : HasNSCDerivAt g g' x) (hgx : g x ≠ 0) :
    HasNSCDerivAt (fun t ↦ f t / g t) ((f' * g x - f x * g') / (g x) ^ 2) x := by
  have hmul := hf.mul (hg.inv hgx)
  have hval : f' * (g x)⁻¹ + f x * (-g' / (g x) ^ 2) = (f' * g x - f x * g') / (g x) ^ 2 := by
    field_simp [hgx]
    ring
  have hfn : (fun t : ℝ ↦ f t / g t) = (fun t : ℝ ↦ f t * (g t)⁻¹) := by
    ext t
    exact div_eq_mul_inv (f t) (g t)
  rw [hfn, ← hval]
  exact hmul

/-! ## §8.4 Chain Rule via the Incremental Equation (pp. 94–95) -/

/-- **Goldblatt §8.4 (Chain Rule, pp. 94–95)**:
If `f` is differentiable at `x` with derivative `f'` and `g` is differentiable at `f(x)` with
derivative `g'`, then `g ∘ f` is differentiable at `x` with derivative `g' * f'`.

Proved in a few lines via the **Incremental Equation (Theorem 8.2.2)** applied to the infinitesimal
increment `Δf = *f(x + Δx) - f(x)`, completely avoiding classical `Δf = 0` case splits! -/
theorem HasNSCDerivAt.comp {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hg : HasNSCDerivAt g g' (f x)) (hf : HasNSCDerivAt f f' x) :
    HasNSCDerivAt (g ∘ f) (g' * f') x := by
  intro Δx hΔ hne
  set Δf : ℝ* := starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)
  have hΔf : IsInfinitesimal Δf := hf.isInfinitesimal_increment hΔ
  obtain ⟨η, hη, hinc⟩ := hg.exists_incremental_eq hΔf
  have hcomp_eq : starFun (g ∘ f) ((x : ℝ*) + Δx) = starFun g ((f x : ℝ*) + Δf) := by
    rw [starFun_comp, Function.comp_apply]
    congr 1
    unfold Δf
    ring
  have hquot :
      (starFun (g ∘ f) ((x : ℝ*) + Δx) - (((g ∘ f) x : ℝ) : ℝ*)) / Δx =
        ((g' : ℝ*) + η) * (Δf / Δx) := by
    rw [Function.comp_apply, hcomp_eq, hinc]
    have : ((g (f x) : ℝ*) + (g' : ℝ*) * Δf + η * Δf - (g (f x) : ℝ*)) =
        ((g' : ℝ*) + η) * Δf := by ring
    rw [this, mul_div_assoc]
  rw [hquot, Hyperreal.coe_mul]
  have h1 : (g' : ℝ*) + η ≈ₕ (g' : ℝ*) := by
    unfold InfClose
    simpa using hη
  have hlim1 : IsLimited ((g' : ℝ*) + η) := (isLimited_coe g').add hη.isLimited
  exact InfClose.mul hlim1 (hf.isLimited_newtonQuotient hΔ hne) h1 (hf Δx hΔ hne)

/-! ## §8.5 Critical Point Theorem, Rolle's Theorem, and Mean Value Theorem (pp. 95–96) -/

/-- **Goldblatt §8.5 (Critical Point Theorem for Local Maxima, p. 95)**:
If `f` has a local maximum at `x` and `HasNSCDerivAt f f' x`, then `f' = 0`.
Proved directly by comparing Newton quotients at `+ε > 0` (`≤ 0`) and `-ε < 0` (`≥ 0`). -/
theorem HasNSCDerivAt.eq_zero_of_isLocalMax {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasNSCDerivAt f f' x) (hmax : IsLocalMax f x) : f' = 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hmax
  have hle_star : ∀ Δx : ℝ*, IsInfinitesimal Δx → starFun f ((x : ℝ*) + Δx) ≤ (f x : ℝ*) := by
    intro Δx hΔ
    have hlt : |Δx| < (δ : ℝ*) := hΔ δ hδ
    rcases ofSeq_surjective Δx with ⟨r, rfl⟩
    have hr_lt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |r n| < δ := ofSeq_lt_ofSeq.1 hlt
    refine ofSeq_le_ofSeq.2 (hr_lt.mono fun n hn ↦ ?_)
    exact hball (by simpa [Real.dist_eq] using hn)
  set ε : ℝ* := Hyperreal.epsilon
  have hε_pos : 0 < ε := Hyperreal.epsilon_pos
  have hε_ne : ε ≠ 0 := hε_pos.ne'
  have hε_inf : IsInfinitesimal ε := isInfinitesimal_epsilon
  have hq_pos_nonpos : (starFun f ((x : ℝ*) + ε) - (f x : ℝ*)) / ε ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hle_star ε hε_inf)) hε_pos.le
  have hf'_le : f' ≤ 0 :=
    coe_le_of_infClose_le (hf ε hε_inf hε_ne).symm hq_pos_nonpos (InfClose.refl _)
  have hneg_inf : IsInfinitesimal (-ε) := hε_inf.neg
  have hneg_lt : -ε < 0 := neg_lt_zero.2 hε_pos
  have hq_neg_nonneg : 0 ≤ (starFun f ((x : ℝ*) + (-ε)) - (f x : ℝ*)) / (-ε) :=
    div_nonneg_of_nonpos (sub_nonpos.2 (hle_star (-ε) hneg_inf)) hneg_lt.le
  have hf'_ge : 0 ≤ f' :=
    coe_le_of_infClose_le (InfClose.refl _) hq_neg_nonneg (hf (-ε) hneg_inf hneg_lt.ne)
  exact le_antisymm hf'_le hf'_ge

/-- **Goldblatt §8.5 (Critical Point Theorem for Local Minima, p. 95)**:
If `f` has a local minimum at `x` and `HasNSCDerivAt f f' x`, then `f' = 0`. -/
theorem HasNSCDerivAt.eq_zero_of_isLocalMin {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasNSCDerivAt f f' x) (hmin : IsLocalMin f x) : f' = 0 := by
  have hneg : -f' = 0 := hf.neg.eq_zero_of_isLocalMax hmin.neg
  linarith

/-- Goldblatt §8.5 (p. 95): Critical Point Theorem for a maximum or minimum on an open interval
`(a, b)`. -/
theorem HasNSCDerivAt.eq_zero_of_extr_Ioo {f : ℝ → ℝ} {f' a b x : ℝ}
    (hx : x ∈ Set.Ioo a b) (hf : HasNSCDerivAt f f' x)
    (hextr : IsMaxOn f (Set.Ioo a b) x ∨ IsMinOn f (Set.Ioo a b) x) : f' = 0 := by
  rcases hextr with hmax | hmin
  · exact hf.eq_zero_of_isLocalMax (hmax.isLocalMax (Ioo_mem_nhds hx.1 hx.2))
  · exact hf.eq_zero_of_isLocalMin (hmin.isLocalMin (Ioo_mem_nhds hx.1 hx.2))

/-- Nonstandard proof of the **Extreme Value Theorem** (maximum on `[a, b]`):
partition `[a, b]` into hyperfinitely many grid points `a + (k / (n + 1)) * (b - a)`, take the
finite grid maximum at each `n`, and let `c = shadow x* ∈ [a, b]`. -/
theorem exists_isMaxOn_Icc_via_shadow {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ c ∈ Set.Icc a b, IsMaxOn f (Set.Icc a b) c := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · refine ⟨a, ⟨le_rfl, le_rfl⟩, fun y hy ↦ ?_⟩
    change f y ≤ f a
    rw [le_antisymm hy.2 hy.1]
  · let grid : ℕ → ℕ → ℝ := fun n k ↦ a + ((k : ℝ) / ((n : ℝ) + 1)) * (b - a)
    have hgrid_mem : ∀ n : ℕ, ∀ k ∈ Finset.range (n + 2), grid n k ∈ Set.Icc a b := by
      intro n k hk
      have hkle : (k : ℝ) ≤ (n : ℝ) + 1 := by
        have : k ≤ n + 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        exact_mod_cast this
      have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h0 : 0 ≤ ((k : ℝ) / ((n : ℝ) + 1)) * (b - a) := by positivity
      have h1 : ((k : ℝ) / ((n : ℝ) + 1)) * (b - a) ≤ b - a := by
        have hdiv : (k : ℝ) / ((n : ℝ) + 1) ≤ 1 := (div_le_one hd).2 hkle
        nlinarith
      exact ⟨by linarith, by linarith⟩
    have hex_max : ∀ n : ℕ, ∃ k ∈ Finset.range (n + 2),
        ∀ j ∈ Finset.range (n + 2), f (grid n j) ≤ f (grid n k) :=
      fun n ↦ Finset.exists_max_image (Finset.range (n + 2)) (fun k ↦ f (grid n k))
        (Finset.nonempty_range_iff.2 (by omega))
    choose kSeq hkSeq using hex_max
    let xStar : ℝ* := ofSeq (fun n ↦ grid n (kSeq n))
    have hx_mem : xStar ∈ starSet (Set.Icc a b) :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ hgrid_mem n (kSeq n) (hkSeq n).1)
    have hx_Icc : (a : ℝ*) ≤ xStar ∧ xStar ≤ (b : ℝ*) := by
      simpa [starSet_Icc] using hx_mem
    have hx_lim : IsLimited xStar :=
      isLimited_iff_exists_real.2 ⟨a - 1, b + 1,
        (Hyperreal.coe_lt_coe.2 (by linarith)).trans_le hx_Icc.1,
        hx_Icc.2.trans_lt (Hyperreal.coe_lt_coe.2 (by linarith))⟩
    let c : ℝ := shadow xStar
    have hc_close : xStar ≈ₕ (c : ℝ*) := infClose_shadow hx_lim
    have hc_mem : c ∈ Set.Icc a b :=
      ⟨coe_le_of_infClose_le (InfClose.refl _) hx_Icc.1 hc_close,
       coe_le_of_infClose_le hc_close.symm hx_Icc.2 (InfClose.refl _)⟩
    have hfx_close : starFun f xStar ≈ₕ (f c : ℝ*) :=
      continuousOn_infClose_starFun hf hc_mem hx_mem hc_close
    refine ⟨c, hc_mem, fun y hy ↦ ?_⟩
    let jSeq : ℕ → ℕ := fun n ↦ ⌊((y - a) / (b - a)) * ((n : ℝ) + 1)⌋₊
    have hj_mem : ∀ n : ℕ, jSeq n ∈ Finset.range (n + 2) := by
      intro n
      rw [Finset.mem_range, Nat.lt_succ_iff]
      have hsub : b - a > 0 := sub_pos.2 hlt
      have hrat_le : (y - a) / (b - a) ≤ 1 := (div_le_one hsub).2 (by linarith [hy.2])
      have hprod_le : ((y - a) / (b - a)) * ((n : ℝ) + 1) ≤ ((n + 1 : ℕ) : ℝ) := by
        push_cast
        nlinarith
      exact Nat.floor_le_of_le hprod_le
    let yStar : ℝ* := ofSeq (fun n ↦ grid n (jSeq n))
    have hy_mem : yStar ∈ starSet (Set.Icc a b) :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ hgrid_mem n (jSeq n) (hj_mem n))
    have hy_close : yStar ≈ₕ (y : ℝ*) := by
      apply ofSeq_infinitesimal_of_tendsto_zero
      refine squeeze_zero_norm (fun n ↦ ?_)
        (by simpa [one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (b - a))
      change |grid n (jSeq n) - y| ≤ (b - a) * ((n : ℝ) + 1)⁻¹
      have hsub : 0 < b - a := sub_pos.2 hlt
      have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hnn : 0 ≤ ((y - a) / (b - a)) * ((n : ℝ) + 1) := by
        have : 0 ≤ y - a := sub_nonneg.2 hy.1
        positivity
      have hfl_le := Nat.floor_le hnn
      have hlt_fl := Nat.lt_floor_add_one (((y - a) / (b - a)) * ((n : ℝ) + 1))
      have hlo : grid n (jSeq n) ≤ y := by
        unfold grid
        have h1 : ((jSeq n : ℝ) / ((n : ℝ) + 1)) * (b - a) ≤ y - a := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hd]
          have h2 := mul_le_mul_of_nonneg_right hfl_le hsub.le
          have h3 : ((y - a) / (b - a)) * ((n : ℝ) + 1) * (b - a) = (y - a) * ((n : ℝ) + 1) := by
            field_simp [hsub.ne']
          linarith
        linarith
      have hhi : y - (b - a) / ((n : ℝ) + 1) ≤ grid n (jSeq n) := by
        unfold grid
        have h1 : y - a - (b - a) / ((n : ℝ) + 1) ≤ ((jSeq n : ℝ) / ((n : ℝ) + 1)) * (b - a) := by
          have h2 := mul_lt_mul_of_pos_right hlt_fl hsub
          have h3 : ((y - a) / (b - a)) * ((n : ℝ) + 1) * (b - a) = (y - a) * ((n : ℝ) + 1) := by
            field_simp [hsub.ne']
          have h4 : (y - a) * ((n : ℝ) + 1) - (b - a) ≤ (jSeq n : ℝ) * (b - a) := by linarith
          have h5 : ((y - a) * ((n : ℝ) + 1) - (b - a)) / ((n : ℝ) + 1) =
              y - a - (b - a) / ((n : ℝ) + 1) := by
            field_simp [hd.ne']
          have h6 := div_le_div_of_nonneg_right h4 hd.le
          rw [h5, ← div_mul_eq_mul_div] at h6
          exact h6
        linarith
      rw [abs_le]
      exact ⟨by linarith [div_eq_mul_inv (b - a) ((n : ℝ) + 1)],
             by linarith [div_eq_mul_inv (b - a) ((n : ℝ) + 1)]⟩
    have hfy_close : starFun f yStar ≈ₕ (f y : ℝ*) :=
      continuousOn_infClose_starFun hf hy hy_mem hy_close
    have hfy_le_fx : starFun f yStar ≤ starFun f xStar :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (hkSeq n).2 (jSeq n) (hj_mem n))
    exact coe_le_of_infClose_le hfy_close.symm hfy_le_fx hfx_close

/-- Nonstandard proof of the **Extreme Value Theorem** (minimum on `[a, b]`). -/
theorem exists_isMinOn_Icc_via_shadow {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ c ∈ Set.Icc a b, IsMinOn f (Set.Icc a b) c := by
  obtain ⟨c, hc_mem, hc_max⟩ := exists_isMaxOn_Icc_via_shadow hab hf.neg
  refine ⟨c, hc_mem, fun y hy ↦ ?_⟩
  change f c ≤ f y
  have hle : -f y ≤ -f c := hc_max hy
  linarith

/-- **Goldblatt §8.5 (Rolle's Theorem, p. 96)**:
If `f` is continuous on `[a, b]` (`a < b`), differentiable on `(a, b)` in the nonstandard sense,
and `f a = f b`, then `f' c = 0` for some `c ∈ (a, b)`. -/
theorem rolle_nsc {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasNSCDerivAt f (f' x) x)
    (heq : f a = f b) :
    ∃ c ∈ Set.Ioo a b, f' c = 0 := by
  obtain ⟨xMax, hxMax_mem, hxMax⟩ := exists_isMaxOn_Icc_via_shadow hab.le hcont
  obtain ⟨xMin, hxMin_mem, hxMin⟩ := exists_isMinOn_Icc_via_shadow hab.le hcont
  by_cases hMaxIoo : xMax ∈ Set.Ioo a b
  · exact ⟨xMax, hMaxIoo, (hderiv xMax hMaxIoo).eq_zero_of_extr_Ioo hMaxIoo
      (Or.inl (fun y hy ↦ hxMax (Set.Ioo_subset_Icc_self hy)))⟩
  · by_cases hMinIoo : xMin ∈ Set.Ioo a b
    · exact ⟨xMin, hMinIoo, (hderiv xMin hMinIoo).eq_zero_of_extr_Ioo hMinIoo
        (Or.inr (fun y hy ↦ hxMin (Set.Ioo_subset_Icc_self hy)))⟩
    · have hMaxVal : f xMax = f a := by
        rcases eq_or_lt_of_le hxMax_mem.1 with rfl | hgt
        · rfl
        · rcases eq_or_lt_of_le hxMax_mem.2 with rfl | hlt
          · exact heq.symm
          · exact absurd ⟨hgt, hlt⟩ hMaxIoo
      have hMinVal : f xMin = f a := by
        rcases eq_or_lt_of_le hxMin_mem.1 with rfl | hgt
        · rfl
        · rcases eq_or_lt_of_le hxMin_mem.2 with rfl | hlt
          · exact heq.symm
          · exact absurd ⟨hgt, hlt⟩ hMinIoo
      set mid : ℝ := (a + b) / 2
      have hmid : mid ∈ Set.Ioo a b := ⟨by linarith [show mid = (a + b) / 2 from rfl],
        by linarith [show mid = (a + b) / 2 from rfl]⟩
      have hconst : ∀ y ∈ Set.Icc a b, f y = f a := fun y hy ↦
        le_antisymm (hMaxVal ▸ hxMax hy) (hMinVal ▸ hxMin hy)
      have hmid_max : IsMaxOn f (Set.Ioo a b) mid := fun y hy ↦ by
        change f y ≤ f mid
        rw [hconst y (Set.Ioo_subset_Icc_self hy), hconst mid (Set.Ioo_subset_Icc_self hmid)]
      exact ⟨mid, hmid, (hderiv mid hmid).eq_zero_of_extr_Ioo hmid (Or.inl hmid_max)⟩

/-- Goldblatt §8.5 (p. 96): Special case of Rolle's Theorem with `f(a) = f(b) = 0`. -/
theorem rolle_zero_nsc {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasNSCDerivAt f (f' x) x)
    (ha : f a = 0) (hb : f b = 0) :
    ∃ c ∈ Set.Ioo a b, f' c = 0 :=
  rolle_nsc hab hcont hderiv (ha.trans hb.symm)

/-- **Goldblatt §8.5 (Mean Value Theorem, p. 96)**:
If `f` is continuous on `[a, b]` (`a < b`) and has nonstandard derivative `f'` on `(a, b)`, then
`f' c = (f b - f a) / (b - a)` for some `c ∈ (a, b)`. -/
theorem mvt_nsc {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasNSCDerivAt f (f' x) x) :
    ∃ c ∈ Set.Ioo a b, f' c = (f b - f a) / (b - a) := by
  set m : ℝ := (f b - f a) / (b - a)
  let h : ℝ → ℝ := fun x ↦ f x - m * (x - a)
  have hh_cont : ContinuousOn h (Set.Icc a b) :=
    hcont.sub (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
  have hh_deriv : ∀ x ∈ Set.Ioo a b, HasNSCDerivAt h (f' x - m) x := by
    intro x hx
    have hsub_a : HasNSCDerivAt (fun t ↦ t - a) 1 x := by
      simpa using (hasNSCDerivAt_id x).sub (hasNSCDerivAt_const a x)
    have hlin : HasNSCDerivAt (fun t ↦ m * (t - a)) (m * 1) x := hsub_a.const_mul m
    simpa using (hderiv x hx).sub hlin
  have hh_eq : h a = h b := by
    unfold h m
    have hba : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
    field_simp [hba]
    ring
  obtain ⟨c, hc, hc0⟩ := rolle_nsc hab hh_cont hh_deriv hh_eq
  exact ⟨c, hc, sub_eq_zero.1 hc0⟩

/-- **Cauchy's Generalized Mean Value Theorem** proved from `rolle_nsc`:
`(f b - f a) * g' c = (g b - g a) * f' c` for some `c ∈ (a, b)`. -/
theorem cauchy_mvt_nsc {f f' g g' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_deriv : ∀ x ∈ Set.Ioo a b, HasNSCDerivAt f (f' x) x)
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_deriv : ∀ x ∈ Set.Ioo a b, HasNSCDerivAt g (g' x) x) :
    ∃ c ∈ Set.Ioo a b, (f b - f a) * g' c = (g b - g a) * f' c := by
  let h : ℝ → ℝ := fun x ↦ (f b - f a) * (g x - g a) - (g b - g a) * (f x - f a)
  have hh_cont : ContinuousOn h (Set.Icc a b) :=
    (continuousOn_const.mul (hg_cont.sub continuousOn_const)).sub
      (continuousOn_const.mul (hf_cont.sub continuousOn_const))
  have hh_deriv : ∀ x ∈ Set.Ioo a b,
      HasNSCDerivAt h ((f b - f a) * g' x - (g b - g a) * f' x) x := by
    intro x hx
    have h1 := ((hg_deriv x hx).sub (hasNSCDerivAt_const (g a) x)).const_mul (f b - f a)
    have h2 := ((hf_deriv x hx).sub (hasNSCDerivAt_const (f a) x)).const_mul (g b - g a)
    simpa using h1.sub h2
  have hh_eq : h a = h b := by
    unfold h
    ring
  obtain ⟨c, hc, hc0⟩ := rolle_nsc hab hh_cont hh_deriv hh_eq
  exact ⟨c, hc, sub_eq_zero.1 hc0⟩

/-- **Goldblatt §8.5 (Zero Derivative Implies Constant, p. 96)**:
If `f` is continuous on `[a, b]` and `f'(x) = 0` on `(a, b)`, then `f` is constant on `[a, b]`. -/
theorem constant_of_hasNSCDerivAt_zero {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasNSCDerivAt f 0 x) :
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f x = f y := by
  intro x hx y hy
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · have hsub : Set.Icc x y ⊆ Set.Icc a b := fun t ht ↦ ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
    have hsub_oo : Set.Ioo x y ⊆ Set.Ioo a b := fun t ht ↦
      ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩
    obtain ⟨c, _, hc⟩ := mvt_nsc hlt (hcont.mono hsub) (fun t ht ↦ hderiv t (hsub_oo ht))
    have hyx : y - x ≠ 0 := sub_ne_zero.2 hlt.ne'
    have h0 : f y - f x = 0 := (div_eq_zero_iff.1 hc.symm).resolve_right hyx
    linarith
  · rfl
  · have hsub : Set.Icc y x ⊆ Set.Icc a b := fun t ht ↦ ⟨hy.1.trans ht.1, ht.2.trans hx.2⟩
    have hsub_oo : Set.Ioo y x ⊆ Set.Ioo a b := fun t ht ↦
      ⟨hy.1.trans_lt ht.1, ht.2.trans_le hx.2⟩
    obtain ⟨c, _, hc⟩ := mvt_nsc hgt (hcont.mono hsub) (fun t ht ↦ hderiv t (hsub_oo ht))
    have hxy : x - y ≠ 0 := sub_ne_zero.2 hgt.ne'
    have h0 : f x - f y = 0 := (div_eq_zero_iff.1 hc.symm).resolve_right hxy
    linarith

/-- **Goldblatt §8.5 (Nonnegative Derivative Implies Monotone Increasing, p. 96)**. -/
theorem monotoneOn_of_hasNSCDerivAt_nonneg {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasNSCDerivAt f (f' x) x)
    (hnn : ∀ x ∈ Set.Ioo a b, 0 ≤ f' x) :
    MonotoneOn f (Set.Icc a b) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · have hsub : Set.Icc x y ⊆ Set.Icc a b := fun t ht ↦ ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
    have hsub_oo : Set.Ioo x y ⊆ Set.Ioo a b := fun t ht ↦
      ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩
    obtain ⟨c, hc, hceq⟩ := mvt_nsc hlt (hcont.mono hsub) (fun t ht ↦ hderiv t (hsub_oo ht))
    have hc_nn : 0 ≤ (f y - f x) / (y - x) := hceq ▸ hnn c (hsub_oo hc)
    have hpos : 0 < y - x := sub_pos.2 hlt
    have : 0 ≤ f y - f x := (div_nonneg_iff.1 hc_nn).resolve_right
      (fun h ↦ not_lt_of_ge h.2 hpos) |>.1
    linarith

/-- **Goldblatt §8.5 (Positive Derivative Implies Strictly Increasing, p. 96)**. -/
theorem strictMonoOn_of_hasNSCDerivAt_pos {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasNSCDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f' x) :
    StrictMonoOn f (Set.Icc a b) := by
  intro x hx y hy hlt
  have hsub : Set.Icc x y ⊆ Set.Icc a b := fun t ht ↦ ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
  have hsub_oo : Set.Ioo x y ⊆ Set.Ioo a b := fun t ht ↦
    ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩
  obtain ⟨c, hc, hceq⟩ := mvt_nsc hlt (hcont.mono hsub) (fun t ht ↦ hderiv t (hsub_oo ht))
  have hc_pos : 0 < (f y - f x) / (y - x) := hceq ▸ hpos c (hsub_oo hc)
  have hyx : 0 < y - x := sub_pos.2 hlt
  have hmul : 0 * (y - x) < f y - f x := (lt_div_iff₀ hyx).1 hc_pos
  linarith

/-- **Goldblatt §8.5 (Nonpositive Derivative Implies Decreasing / Antitone, p. 96)**. -/
theorem antitoneOn_of_hasNSCDerivAt_nonpos {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasNSCDerivAt f (f' x) x)
    (hnp : ∀ x ∈ Set.Ioo a b, f' x ≤ 0) :
    AntitoneOn f (Set.Icc a b) := by
  have hmono := monotoneOn_of_hasNSCDerivAt_nonneg hcont.neg
    (fun x hx ↦ (hderiv x hx).neg) (fun x hx ↦ neg_nonneg.2 (hnp x hx))
  intro x hx y hy hxy
  exact neg_le_neg_iff.1 (hmono hx hy hxy)

/-- **Goldblatt §8.5 (Negative Derivative Implies Strictly Decreasing, p. 96)**. -/
theorem strictAntiOn_of_hasNSCDerivAt_neg {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasNSCDerivAt f (f' x) x)
    (hneg : ∀ x ∈ Set.Ioo a b, f' x < 0) :
    StrictAntiOn f (Set.Icc a b) := by
  have hstrict := strictMonoOn_of_hasNSCDerivAt_pos hcont.neg
    (fun x hx ↦ (hderiv x hx).neg) (fun x hx ↦ neg_pos.2 (hneg x hx))
  intro x hx y hy hlt
  exact neg_lt_neg_iff.1 (hstrict hx hy hlt)

/-! ## §8.6 Inverse Function Theorem in One Dimension (pp. 96–97) -/

/-- Goldblatt §8.6 (p. 96) helper: if `u ∈ ℝ*` is not infinitely close to `(x : ℝ*)` and
`(x : ℝ*) < u`, then for any `b > x` there is a standard real `r ∈ (x, b)` with `(r : ℝ*) < u`. -/
theorem exists_real_Ioo_lt_of_not_infClose {u : ℝ*} {x b : ℝ}
    (hnot : ¬ (u ≈ₕ (x : ℝ*))) (hxu : (x : ℝ*) < u) (hxb : x < b) :
    ∃ r ∈ Set.Ioo x b, (r : ℝ*) < u := by
  unfold InfClose IsInfinitesimal at hnot
  push Not at hnot
  obtain ⟨δ, hδ, hle⟩ := hnot
  have hsub_pos : 0 < u - (x : ℝ*) := sub_pos.2 hxu
  rw [abs_of_pos hsub_pos] at hle
  let ε : ℝ := min (δ / 2) ((b - x) / 2)
  have hε_pos : 0 < ε := lt_min (half_pos hδ) (by linarith)
  have hε_lt_δ : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hε_lt_bx : ε < b - x := (min_le_right _ _).trans_lt (half_lt_self (sub_pos.2 hxb))
  refine ⟨x + ε, ⟨by linarith, by linarith⟩, ?_⟩
  have hlt_δ : ((x + ε : ℝ) : ℝ*) < (x : ℝ*) + (δ : ℝ*) := by
    rw [Hyperreal.coe_add]
    exact add_lt_add_right (Hyperreal.coe_lt_coe.2 hε_lt_δ) (x : ℝ*)
  linarith

/-- Symmetric helper: if `u ∈ ℝ*` is not infinitely close to `(x : ℝ*)` and `u < (x : ℝ*)`,
then for any `a < x` there is a standard real `r ∈ (a, x)` with `u < (r : ℝ*)`. -/
theorem exists_real_Ioo_gt_of_not_infClose {u : ℝ*} {a x : ℝ}
    (hnot : ¬ (u ≈ₕ (x : ℝ*))) (hux : u < (x : ℝ*)) (hax : a < x) :
    ∃ r ∈ Set.Ioo a x, u < (r : ℝ*) := by
  have hnot_neg : ¬ ((-u) ≈ₕ ((-x : ℝ) : ℝ*)) := by
    intro h
    apply hnot
    simpa using h.neg
  obtain ⟨s, hs_mem, hs_lt⟩ := exists_real_Ioo_lt_of_not_infClose hnot_neg
    (by rw [Hyperreal.coe_neg]; exact neg_lt_neg hux) (neg_lt_neg hax)
  refine ⟨-s, ⟨by linarith [hs_mem.2], by linarith [hs_mem.1]⟩, ?_⟩
  rw [Hyperreal.coe_neg]
  exact lt_neg.1 hs_lt

/-- **Goldblatt §8.6 (Inverse Function Theorem — Strictly Increasing Case, pp. 96–97)**:
Let `f` be continuous and strictly increasing on `(a, b)`, and let `g` be an inverse of `f` on
`(a, b)` (so `g (f t) = t` for all `t ∈ (a, b)`, and `f (g w) = w` with `g w ∈ (a, b)` whenever
`w ∈ f '' (a, b)`, e.g. `g = Function.invFunOn f (Set.Ioo a b)`). If `x ∈ (a, b)` and
`HasNSCDerivAt f f' x` with `f' ≠ 0`, then `HasNSCDerivAt g f'⁻¹ (f x)`.

Proved by Goldblatt's exact nonstandard argument:
1. By IVT on `[x₁, x₂] ⊂ (a, b)`, `(f x₁, f x₂) ⊆ f '' (a, b)` is an open interval around `y = f x`.
2. For nonzero infinitesimal `Δy`, `u := *g(y + Δy)` satisfies `u ≈ₕ x` (otherwise a real
   `r ∈ (a, b)`
   strictly between `u` and `x` would map to `f r` strictly between `y + Δy` and `y`, impossible!).
3. Thus `Δx := u - x` is a nonzero infinitesimal with `Δy = *f(x + Δx) - f(x)`, and
   `Δx / Δy = 1 / (Δy / Δx) ≈ₕ 1 / f'` by appreciable division! -/
theorem HasNSCDerivAt.inverse_strictMonoOn {f g : ℝ → ℝ} {f' a b x : ℝ}
    (hx : x ∈ Set.Ioo a b)
    (hf_cont : ContinuousOn f (Set.Ioo a b))
    (hf_mono : StrictMonoOn f (Set.Ioo a b))
    (hg_left : ∀ t ∈ Set.Ioo a b, g (f t) = t)
    (hg_right : ∀ w ∈ f '' Set.Ioo a b, g w ∈ Set.Ioo a b ∧ f (g w) = w)
    (hf_deriv : HasNSCDerivAt f f' x) (hf'_ne : f' ≠ 0) :
    HasNSCDerivAt g f'⁻¹ (f x) := by
  set y : ℝ := f x
  let x₁ : ℝ := (a + x) / 2
  let x₂ : ℝ := (x + b) / 2
  have hx₁_def : x₁ = (a + x) / 2 := rfl
  have hx₂_def : x₂ = (x + b) / 2 := rfl
  have hx₁_Ioo : x₁ ∈ Set.Ioo a b := ⟨by linarith [hx.1, hx₁_def],
    by linarith [hx.1, hx.2, hx₁_def]⟩
  have hx₂_Ioo : x₂ ∈ Set.Ioo a b := ⟨by linarith [hx.1, hx.2, hx₂_def],
    by linarith [hx.2, hx₂_def]⟩
  have hx₁x : x₁ < x := by linarith [hx.1, hx₁_def]
  have hxx₂ : x < x₂ := by linarith [hx.2, hx₂_def]
  have hfx₁_lt : f x₁ < y := hf_mono hx₁_Ioo hx hx₁x
  have hlt_fx₂ : y < f x₂ := hf_mono hx hx₂_Ioo hxx₂
  have hIoo_sub_img : Set.Ioo (f x₁) (f x₂) ⊆ f '' Set.Ioo a b := by
    intro w hw
    have hsub : Set.Icc x₁ x₂ ⊆ Set.Ioo a b := fun t ht ↦
      ⟨hx₁_Ioo.1.trans_le ht.1, ht.2.trans_lt hx₂_Ioo.2⟩
    have hw_Icc : w ∈ Set.Icc (f x₁) (f x₂) := ⟨hw.1.le, hw.2.le⟩
    obtain ⟨t, ht_Icc, hft⟩ :=
      intermediate_value_Icc (hx₁x.trans hxx₂).le (hf_cont.mono hsub) hw_Icc
    exact ⟨t, hsub ht_Icc, hft⟩
  intro Δy hΔy hΔy_ne
  have hyΔ_mem : (y : ℝ*) + Δy ∈ starSet (Set.Ioo (f x₁) (f x₂)) := by
    rw [starSet_Ioo]
    set δ : ℝ := min (y - f x₁) (f x₂ - y)
    have hδ_pos : 0 < δ := lt_min (sub_pos.2 hfx₁_lt) (sub_pos.2 hlt_fx₂)
    have hlt_δ : |Δy| < (δ : ℝ*) := hΔy δ hδ_pos
    rcases abs_lt.1 hlt_δ with ⟨hlo, hhi⟩
    have hδ1 : (δ : ℝ*) ≤ ((y - f x₁ : ℝ) : ℝ*) := Hyperreal.coe_le_coe.2 (min_le_left _ _)
    have hδ2 : (δ : ℝ*) ≤ ((f x₂ - y : ℝ) : ℝ*) := Hyperreal.coe_le_coe.2 (min_le_right _ _)
    rw [Hyperreal.coe_sub] at hδ1 hδ2
    exact ⟨by linarith, by linarith⟩
  set u : ℝ* := starFun g ((y : ℝ*) + Δy)
  have hu_prop : u ∈ starSet (Set.Ioo a b) ∧ starFun f u = (y : ℝ*) + Δy := by
    rcases ofSeq_surjective Δy with ⟨s, rfl⟩
    have hs_mem : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), y + s n ∈ Set.Ioo (f x₁) (f x₂) :=
      ofSeq_mem_starSet.1 hyΔ_mem
    refine ⟨ofSeq_mem_starSet.2 (hs_mem.mono fun n hn ↦ (hg_right _ (hIoo_sub_img hn)).1),
            Germ.coe_eq.2 (hs_mem.mono fun n hn ↦ (hg_right _ (hIoo_sub_img hn)).2)⟩
  -- Goldblatt's nonstandard proof that `u ≈ₕ x` (no real lies strictly between `u` and `x`)
  have hu_close : u ≈ₕ (x : ℝ*) := by
    by_contra hnot
    rcases lt_trichotomy (x : ℝ*) u with hxu | heq | hux
    · obtain ⟨r, hr_Ioo, hru⟩ := exists_real_Ioo_lt_of_not_infClose hnot hxu hx.2
      have hr_ab : r ∈ Set.Ioo a b := ⟨hx.1.trans hr_Ioo.1, hr_Ioo.2⟩
      have hfr_lt_fu : (f r : ℝ*) < starFun f u := by
        obtain ⟨q, hq⟩ := ofSeq_surjective u
        have hu_ab' : ofSeq q ∈ starSet (Set.Ioo a b) := hq.symm ▸ hu_prop.1
        have hru' : (r : ℝ*) < ofSeq q := hq.symm ▸ hru
        rw [← hq]
        have hq_ab : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), q n ∈ Set.Ioo a b :=
          ofSeq_mem_starSet.1 hu_ab'
        have hq_gt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r < q n := ofSeq_lt_ofSeq.1 hru'
        exact ofSeq_lt_ofSeq.2 ((hq_ab.and hq_gt).mono fun n ⟨hn_ab, hn_gt⟩ ↦
          hf_mono hr_ab hn_ab hn_gt)
      rw [hu_prop.2] at hfr_lt_fu
      have hy_close : (y : ℝ*) + Δy ≈ₕ (y : ℝ*) := by
        unfold InfClose
        simpa using hΔy
      have hfr_le_y : f r ≤ y :=
        coe_le_of_infClose_le (InfClose.refl _) hfr_lt_fu.le hy_close
      exact not_lt_of_ge hfr_le_y (hf_mono hx hr_ab hr_Ioo.1)
    · exact hnot (heq ▸ InfClose.refl _)
    · obtain ⟨r, hr_Ioo, hur⟩ := exists_real_Ioo_gt_of_not_infClose hnot hux hx.1
      have hr_ab : r ∈ Set.Ioo a b := ⟨hr_Ioo.1, hr_Ioo.2.trans hx.2⟩
      have hfu_lt_fr : starFun f u < (f r : ℝ*) := by
        obtain ⟨q, hq⟩ := ofSeq_surjective u
        have hu_ab' : ofSeq q ∈ starSet (Set.Ioo a b) := hq.symm ▸ hu_prop.1
        have hur' : ofSeq q < (r : ℝ*) := hq.symm ▸ hur
        rw [← hq]
        have hq_ab : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), q n ∈ Set.Ioo a b :=
          ofSeq_mem_starSet.1 hu_ab'
        have hq_lt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), q n < r := ofSeq_lt_ofSeq.1 hur'
        exact ofSeq_lt_ofSeq.2 ((hq_ab.and hq_lt).mono fun n ⟨hn_ab, hn_lt⟩ ↦
          hf_mono hn_ab hr_ab hn_lt)
      rw [hu_prop.2] at hfu_lt_fr
      have hy_close : (y : ℝ*) ≈ₕ (y : ℝ*) + Δy := by
        unfold InfClose
        simpa using hΔy.neg
      have hy_le_fr : y ≤ f r :=
        coe_le_of_infClose_le hy_close hfu_lt_fr.le (InfClose.refl _)
      exact not_lt_of_ge hy_le_fr (hf_mono hr_ab hx hr_Ioo.2)
  set Δx : ℝ* := u - (x : ℝ*)
  have hΔx_inf : IsInfinitesimal Δx := hu_close
  have hxΔ_eq : (x : ℝ*) + Δx = u := add_sub_cancel _ _
  have hΔy_eq : starFun f ((x : ℝ*) + Δx) - (f x : ℝ*) = Δy := by
    rw [hxΔ_eq, hu_prop.2]
    unfold y
    ring
  have hΔx_ne : Δx ≠ 0 := by
    intro h0
    apply hΔy_ne
    rw [← hΔy_eq, h0, add_zero, starFun_coe, sub_self]
  have hgy : g y = x := hg_left x hx
  have hquot_eq : (starFun g ((y : ℝ*) + Δy) - (g y : ℝ*)) / Δy =
      1 / ((starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx) := by
    rw [hgy, hΔy_eq]
    change Δx / Δy = 1 / (Δy / Δx)
    rw [one_div_div]
  rw [hquot_eq]
  have hf_quot_close : (starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx ≈ₕ (f' : ℝ*) :=
    hf_deriv Δx hΔx_inf hΔx_ne
  have hf'_app : IsAppreciable (f' : ℝ*) := isAppreciable_coe_iff.2 hf'_ne
  have hf_quot_app : IsAppreciable ((starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx) := by
    have : (starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx =
        (f' : ℝ*) + ((starFun f ((x : ℝ*) + Δx) - (f x : ℝ*)) / Δx - (f' : ℝ*)) := by ring
    rw [this]
    exact hf'_app.add_isInfinitesimal hf_quot_close
  have htarget : ((f'⁻¹ : ℝ) : ℝ*) = (1 : ℝ*) / (f' : ℝ*) := by
    rw [Hyperreal.coe_inv, one_div]
  rw [htarget]
  exact InfClose.div (isLimited_coe 1) hf_quot_app (InfClose.refl _) hf_quot_close

/-- **Goldblatt §8.6 (Inverse Function Theorem — Strictly Decreasing Case, pp. 96–97)**. -/
theorem HasNSCDerivAt.inverse_strictAntiOn {f g : ℝ → ℝ} {f' a b x : ℝ}
    (hx : x ∈ Set.Ioo a b)
    (hf_cont : ContinuousOn f (Set.Ioo a b))
    (hf_anti : StrictAntiOn f (Set.Ioo a b))
    (hg_left : ∀ t ∈ Set.Ioo a b, g (f t) = t)
    (hg_right : ∀ w ∈ f '' Set.Ioo a b, g w ∈ Set.Ioo a b ∧ f (g w) = w)
    (hf_deriv : HasNSCDerivAt f f' x) (hf'_ne : f' ≠ 0) :
    HasNSCDerivAt g f'⁻¹ (f x) := by
  let fn : ℝ → ℝ := fun t ↦ -f t
  let gn : ℝ → ℝ := fun w ↦ g (-w)
  have hfn_mono : StrictMonoOn fn (Set.Ioo a b) :=
    fun u hu v hv huv ↦ neg_lt_neg (hf_anti hu hv huv)
  have hgn_left : ∀ t ∈ Set.Ioo a b, gn (fn t) = t := fun t ht ↦ by
    simp [gn, fn, hg_left t ht]
  have hgn_right : ∀ w ∈ fn '' Set.Ioo a b, gn w ∈ Set.Ioo a b ∧ fn (gn w) = w := by
    rintro w ⟨t, ht, rfl⟩
    have hw_mem : f t ∈ f '' Set.Ioo a b := ⟨t, ht, rfl⟩
    obtain ⟨h1, h2⟩ := hg_right (f t) hw_mem
    refine ⟨by simpa [gn, fn] using h1, ?_⟩
    simp [gn, fn, h2]
  have hgn_deriv : HasNSCDerivAt gn (-f')⁻¹ (-f x) :=
    HasNSCDerivAt.inverse_strictMonoOn (f := fn) (g := gn) hx hf_cont.neg hfn_mono
      hgn_left hgn_right hf_deriv.neg (neg_ne_zero.2 hf'_ne)
  have hg_comp : HasNSCDerivAt (gn ∘ fun w ↦ -w) ((-f')⁻¹ * (-1)) (f x) :=
    hgn_deriv.comp (hasNSCDerivAt_id (f x)).neg
  have hfn_eq : (gn ∘ fun w ↦ -w) = g := by
    ext w
    simp [gn]
  have hval : (-f')⁻¹ * (-1 : ℝ) = f'⁻¹ := by
    field_simp [hf'_ne]
  rwa [hfn_eq, hval] at hg_comp

/-- Specialization of Goldblatt §8.6 to `Function.invFunOn f (Set.Ioo a b)` for any strictly
monotone (increasing or decreasing) continuous function on `(a, b)`. -/
theorem HasNSCDerivAt.invFunOn_Ioo {f : ℝ → ℝ} {f' a b x : ℝ}
    (hx : x ∈ Set.Ioo a b)
    (hf_cont : ContinuousOn f (Set.Ioo a b))
    (hf_mono : StrictMonoOn f (Set.Ioo a b) ∨ StrictAntiOn f (Set.Ioo a b))
    (hf_deriv : HasNSCDerivAt f f' x) (hf'_ne : f' ≠ 0) :
    HasNSCDerivAt (Function.invFunOn f (Set.Ioo a b)) f'⁻¹ (f x) := by
  have hinj : Set.InjOn f (Set.Ioo a b) := by
    rcases hf_mono with hm | ha
    · exact hm.injOn
    · exact ha.injOn
  have hleft : ∀ t ∈ Set.Ioo a b, Function.invFunOn f (Set.Ioo a b) (f t) = t :=
    fun t ht ↦ hinj.leftInvOn_invFunOn ht
  have hright : ∀ w ∈ f '' Set.Ioo a b,
      Function.invFunOn f (Set.Ioo a b) w ∈ Set.Ioo a b ∧
        f (Function.invFunOn f (Set.Ioo a b) w) = w := by
    rintro w ⟨t, ht, rfl⟩
    exact ⟨(hinj.leftInvOn_invFunOn ht).symm ▸ ht, Function.invFunOn_eq ⟨t, ht, rfl⟩⟩
  rcases hf_mono with hm | ha
  · exact hf_deriv.inverse_strictMonoOn hx hf_cont hm hleft hright hf'_ne
  · exact hf_deriv.inverse_strictAntiOn hx hf_cont ha hleft hright hf'_ne

/-! ## §8.7–8.8 Partial Derivatives, Smoothness, and Total Differentiability in `ℝ²` (pp. 97–100) -/

/-- Fixing the second argument of `starFun₂ f` at a standard real `b` agrees with `starFun`. -/
@[simp]
theorem starFun₂_coe_right (f : ℝ → ℝ → ℝ) (x : ℝ*) (b : ℝ) :
    starFun₂ f x (b : ℝ*) = starFun (fun t ↦ f t b) x :=
  Germ.inductionOn x fun _ ↦ rfl

/-- Fixing the first argument of `starFun₂ f` at a standard real `a` agrees with `starFun`. -/
@[simp]
theorem starFun₂_coe_left (f : ℝ → ℝ → ℝ) (a : ℝ) (y : ℝ*) :
    starFun₂ f (a : ℝ*) y = starFun (fun t ↦ f a t) y :=
  Germ.inductionOn y fun _ ↦ rfl

/-- Goldblatt §8.7 (p. 97): Infinite closeness in the hyperreal plane `*ℝ² = ℝ* × ℝ*`:
`(x₁, y₁) ≈ (x₂, y₂)` iff `x₁ ≈ₕ x₂` and `y₁ ≈ₕ y₂`. -/
def InfClose₂ (p q : ℝ* × ℝ*) : Prop :=
  p.1 ≈ₕ q.1 ∧ p.2 ≈ₕ q.2

/-- Goldblatt §8.7 (p. 97): Hyperreal Euclidean distance `√((x₁ - x₂)² + (y₁ - y₂)²)` in `*ℝ²`. -/
def hyperEuclideanDist (p q : ℝ* × ℝ*) : ℝ* :=
  starFun Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

/-- Goldblatt §8.7 (pp. 97–98): `(x₁, y₁)` and `(x₂, y₂)` in `*ℝ²` are infinitely close if and only
if their hyperreal Euclidean distance `√((x₁ - x₂)² + (y₁ - y₂)²)` is infinitesimal. -/
theorem infClose₂_iff_isInfinitesimal_hyperEuclideanDist {p q : ℝ* × ℝ*} :
    InfClose₂ p q ↔ IsInfinitesimal (hyperEuclideanDist p q) := by
  constructor
  · rintro ⟨hx, hy⟩
    unfold hyperEuclideanDist
    have hnn : 0 ≤ (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hsq_inf : IsInfinitesimal ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2) := by
      simpa [sq] using (IsInfinitesimal.mul hx hx).add (IsInfinitesimal.mul hy hy)
    exact isInfinitesimal_starFun_sqrt hnn hsq_inf
  · intro hdist
    have hnn_dist : 0 ≤ hyperEuclideanDist p q := by
      unfold hyperEuclideanDist
      rcases ofSeq_surjective ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2) with ⟨s, hseq⟩
      rw [← hseq]
      exact ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ Real.sqrt_nonneg (s n))
    have habs_dist : |hyperEuclideanDist p q| = hyperEuclideanDist p q := abs_of_nonneg hnn_dist
    have hle₁ : |p.1 - q.1| ≤ |hyperEuclideanDist p q| := by
      rw [habs_dist]
      unfold hyperEuclideanDist
      rcases ofSeq_surjective (p.1 - q.1) with ⟨u, hu⟩
      rcases ofSeq_surjective (p.2 - q.2) with ⟨v, hv⟩
      rw [← hu, ← hv]
      refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
      change |u n| ≤ Real.sqrt ((u n) ^ 2 + (v n) ^ 2)
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hle₂ : |p.2 - q.2| ≤ |hyperEuclideanDist p q| := by
      rw [habs_dist]
      unfold hyperEuclideanDist
      rcases ofSeq_surjective (p.1 - q.1) with ⟨u, hu⟩
      rcases ofSeq_surjective (p.2 - q.2) with ⟨v, hv⟩
      rw [← hu, ← hv]
      refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
      change |v n| ≤ Real.sqrt ((u n) ^ 2 + (v n) ^ 2)
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith)
    exact ⟨isInfinitesimal_of_abs_le hdist hle₁, isInfinitesimal_of_abs_le hdist hle₂⟩

/-- Goldblatt §8.7 (p. 98): Nonstandard continuity of `f : ℝ → ℝ → ℝ` at a real point `(a, b)`:
`x ≈ₕ a` and `y ≈ₕ b` imply `*f(x, y) ≈ₕ f(a, b)`. -/
def IsNSCContinuous₂At (f : ℝ → ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x y : ℝ*, x ≈ₕ (a : ℝ*) → y ≈ₕ (b : ℝ*) → starFun₂ f x y ≈ₕ (f a b : ℝ*)

/-- Equivalence between classical continuity `ContinuousAt (Function.uncurry f) (a, b)` on `ℝ × ℝ`
and nonstandard two-variable microcontinuity `IsNSCContinuous₂At f a b`. -/
theorem continuousAt_uncurry_iff_isNSCContinuous₂At {f : ℝ → ℝ → ℝ} {a b : ℝ} :
    ContinuousAt (Function.uncurry f) (a, b) ↔ IsNSCContinuous₂At f a b := by
  rw [Metric.continuousAt_iff]
  constructor
  · intro hf x y hx hy ε hε
    obtain ⟨δ, hδ, hball⟩ := hf ε hε
    have hxlt : |x - (a : ℝ*)| < (δ : ℝ*) := hx δ hδ
    have hylt : |y - (b : ℝ*)| < (δ : ℝ*) := hy δ hδ
    rcases ofSeq_surjective x with ⟨u, rfl⟩
    rcases ofSeq_surjective y with ⟨v, rfl⟩
    have hu : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |u n - a| < δ := ofSeq_lt_ofSeq.1 hxlt
    have hv : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |v n - b| < δ := ofSeq_lt_ofSeq.1 hylt
    refine ofSeq_lt_ofSeq.2 ((hu.and hv).mono fun n ⟨hnu, hnv⟩ ↦ ?_)
    change |f (u n) (v n) - f a b| < ε
    have hdist : dist (u n, v n) (a, b) < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by simpa only [Real.dist_eq] using hnu, by simpa only [Real.dist_eq] using hnv⟩
    simpa only [Real.dist_eq, Function.uncurry_apply_pair] using hball hdist
  · intro h ε hε
    by_contra hnot
    push Not at hnot
    have hex : ∀ n : ℕ, ∃ p : ℝ × ℝ,
        |p.1 - a| < ((n : ℝ) + 1)⁻¹ ∧ |p.2 - b| < ((n : ℝ) + 1)⁻¹ ∧
          ε ≤ |f p.1 p.2 - f a b| := by
      intro n
      obtain ⟨p, hp_dist, hp_ge⟩ := hnot (((n : ℝ) + 1)⁻¹) (by positivity)
      rw [Prod.dist_eq, max_lt_iff] at hp_dist
      exact ⟨p, by simpa [Real.dist_eq] using hp_dist.1,
        by simpa [Real.dist_eq] using hp_dist.2,
        by simpa [Real.dist_eq, Function.uncurry] using hp_ge⟩
    choose p hp using hex
    let x : ℝ* := ofSeq (fun n ↦ (p n).1)
    let y : ℝ* := ofSeq (fun n ↦ (p n).2)
    have hx : x ≈ₕ (a : ℝ*) := by
      apply ofSeq_infinitesimal_of_tendsto_zero
      refine squeeze_zero_norm (fun n ↦ ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [Real.norm_eq_abs, one_div] using (hp n).1.le
    have hy : y ≈ₕ (b : ℝ*) := by
      apply ofSeq_infinitesimal_of_tendsto_zero
      refine squeeze_zero_norm (fun n ↦ ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [Real.norm_eq_abs, one_div] using (hp n).2.1.le
    have hlt := h x y hx hy ε hε
    have hge : (ε : ℝ*) ≤ |starFun₂ f x y - (f a b : ℝ*)| :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (hp n).2.2)
    exact not_lt_of_ge hge hlt

/-- Goldblatt §8.7 (p. 97): Nonstandard first partial derivative `f_x(a, b) = fx`. -/
def HasNSCPartialDeriv₁ (f : ℝ → ℝ → ℝ) (fx : ℝ) (a b : ℝ) : Prop :=
  HasNSCDerivAt (fun x ↦ f x b) fx a

/-- Goldblatt §8.7 (p. 97): Nonstandard second partial derivative `f_y(a, b) = fy`. -/
def HasNSCPartialDeriv₂ (f : ℝ → ℝ → ℝ) (fy : ℝ) (a b : ℝ) : Prop :=
  HasNSCDerivAt (fun y ↦ f a y) fy b

/-- Goldblatt §8.7 (p. 97): Infinitesimal difference-quotient characterization of `f_x(a, b)`. -/
theorem hasNSCPartialDeriv₁_iff {f : ℝ → ℝ → ℝ} {fx a b : ℝ} :
    HasNSCPartialDeriv₁ f fx a b ↔
      ∀ Δx : ℝ*, IsInfinitesimal Δx → Δx ≠ 0 →
        (starFun₂ f ((a : ℝ*) + Δx) (b : ℝ*) - (f a b : ℝ*)) / Δx ≈ₕ (fx : ℝ*) := by
  simp [HasNSCPartialDeriv₁, HasNSCDerivAt]

/-- Goldblatt §8.7 (p. 97): Infinitesimal difference-quotient characterization of `f_y(a, b)`. -/
theorem hasNSCPartialDeriv₂_iff {f : ℝ → ℝ → ℝ} {fy a b : ℝ} :
    HasNSCPartialDeriv₂ f fy a b ↔
      ∀ Δy : ℝ*, IsInfinitesimal Δy → Δy ≠ 0 →
        (starFun₂ f (a : ℝ*) ((b : ℝ*) + Δy) - (f a b : ℝ*)) / Δy ≈ₕ (fy : ℝ*) := by
  simp [HasNSCPartialDeriv₂, HasNSCDerivAt]

/-- Goldblatt §8.7 (p. 98): Two-variable increment `Δf = *f(a + Δx, b + Δy) - f(a, b)`. -/
def nscIncrement₂ (f : ℝ → ℝ → ℝ) (a b : ℝ) (Δx Δy : ℝ*) : ℝ* :=
  starFun₂ f ((a : ℝ*) + Δx) ((b : ℝ*) + Δy) - (f a b : ℝ*)

/-- Goldblatt §8.7 (p. 98): Total differential `df = f_x(a, b) Δx + f_y(a, b) Δy`. -/
def nscTotalDifferential (fx fy : ℝ) (Δx Δy : ℝ*) : ℝ* :=
  (fx : ℝ*) * Δx + (fy : ℝ*) * Δy

/-- Goldblatt §8.7 (p. 98): `f` is *smooth* at `(a, b)` with partial derivative functions `fx, fy`
if `fx` and `fy` are the nonstandard partial derivatives of `f` on an open disk of radius `r > 0`
around `(a, b)` and both `fx` and `fy` are continuous at `(a, b)`. -/
def IsNSCSmoothAt (f fx fy : ℝ → ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    (∀ x y : ℝ, (x - a) ^ 2 + (y - b) ^ 2 < r ^ 2 →
      HasNSCPartialDeriv₁ f (fx x y) x y ∧ HasNSCPartialDeriv₂ f (fy x y) x y) ∧
    IsNSCContinuous₂At fx a b ∧ IsNSCContinuous₂At fy a b

/-- Nonstandard total differentiability (the two-variable incremental equation of Goldblatt
Theorem 8.7.1, p. 98): for all infinitesimals `Δx, Δy`, there exist infinitesimals `η₁, η₂` with
`*f(a + Δx, b + Δy) = f(a, b) + fx * Δx + fy * Δy + η₁ * Δx + η₂ * Δy`. -/
def HasNSCTotalDerivAt (f : ℝ → ℝ → ℝ) (fx fy : ℝ) (a b : ℝ) : Prop :=
  ∀ Δx Δy : ℝ*, IsInfinitesimal Δx → IsInfinitesimal Δy →
    ∃ η₁ η₂ : ℝ*, IsInfinitesimal η₁ ∧ IsInfinitesimal η₂ ∧
      starFun₂ f ((a : ℝ*) + Δx) ((b : ℝ*) + Δy) =
        (f a b : ℝ*) + (fx : ℝ*) * Δx + (fy : ℝ*) * Δy + η₁ * Δx + η₂ * Δy

/-- Total differentiability at `(a, b)` implies `HasNSCPartialDeriv₁ f fx a b`. -/
theorem HasNSCTotalDerivAt.hasNSCPartialDeriv₁ {f : ℝ → ℝ → ℝ} {fx fy a b : ℝ}
    (h : HasNSCTotalDerivAt f fx fy a b) : HasNSCPartialDeriv₁ f fx a b := by
  rw [HasNSCPartialDeriv₁, hasNSCDerivAt_iff_incremental_eq]
  intro Δx hΔx
  obtain ⟨η₁, η₂, hη₁, _, heq⟩ := h Δx 0 hΔx isInfinitesimal_zero
  refine ⟨η₁, hη₁, ?_⟩
  simpa using heq

/-- Total differentiability at `(a, b)` implies `HasNSCPartialDeriv₂ f fy a b`. -/
theorem HasNSCTotalDerivAt.hasNSCPartialDeriv₂ {f : ℝ → ℝ → ℝ} {fx fy a b : ℝ}
    (h : HasNSCTotalDerivAt f fx fy a b) : HasNSCPartialDeriv₂ f fy a b := by
  rw [HasNSCPartialDeriv₂, hasNSCDerivAt_iff_incremental_eq]
  intro Δy hΔy
  obtain ⟨η₁, η₂, _, hη₂, heq⟩ := h 0 Δy isInfinitesimal_zero hΔy
  refine ⟨η₂, hη₂, ?_⟩
  simpa using heq

/-- Sharp form of **Goldblatt Theorem 8.7.1 (Incremental Equation for Two Variables, pp. 98–99)**:
if `f_x(a, b)` exists at `(a, b)`, `f_y` exists on an open disk around `(a, b)`, and `f_y` is
continuous at `(a, b)`, then `f` satisfies the two-variable incremental equation at `(a, b)`.

Proved by Goldblatt's exact argument: apply the 1D incremental equation to `x ↦ f(x, b)` at `a`,
and apply hyperreal transfer of the 1D Mean Value Theorem (`mvt_nsc`) to the family
`y ↦ f(a + x₀, y)` on `[b, b + y₀]`, obtaining `c` between `b` and `b + Δy` (`c ≈ₕ b`) with
`*f(a + Δx, b + Δy) - *f(a + Δx, b) = *f_y(a + Δx, c) Δy = (f_y(a, b) + δ) Δy`! -/
theorem hasNSCTotalDerivAt_of_partialDeriv₁_and_cont_partialDeriv₂
    {f fy : ℝ → ℝ → ℝ} {fx_ab a b r : ℝ} (hr : 0 < r)
    (hfx : HasNSCPartialDeriv₁ f fx_ab a b)
    (hfy : ∀ x y : ℝ, (x - a) ^ 2 + (y - b) ^ 2 < r ^ 2 → HasNSCPartialDeriv₂ f (fy x y) x y)
    (hfy_cont : IsNSCContinuous₂At fy a b) :
    HasNSCTotalDerivAt f fx_ab (fy a b) a b := by
  -- Real 1D MVT lemma for `y ↦ f (a + x₀) y` when `|x₀| < r / 2` and `|y₀| < r / 2`
  have hreal_mvt : ∀ x₀ y₀ : ℝ, |x₀| < r / 2 → |y₀| < r / 2 →
      ∃ c₀ : ℝ, |c₀ - b| ≤ |y₀| ∧ f (a + x₀) (b + y₀) - f (a + x₀) b = fy (a + x₀) c₀ * y₀ := by
    intro x₀ y₀ hx₀ hy₀
    have hdisk : ∀ t : ℝ, |t - b| ≤ |y₀| → ((a + x₀) - a) ^ 2 + (t - b) ^ 2 < r ^ 2 := by
      intro t ht
      have hx_sq : x₀ ^ 2 < (r / 2) ^ 2 := sq_lt_sq.2 (by rwa [abs_of_pos (half_pos hr)])
      have hy_sq : |y₀| ^ 2 < (r / 2) ^ 2 :=
        sq_lt_sq.2 (by simpa [abs_of_pos (half_pos hr)] using hy₀)
      have ht_sq : (t - b) ^ 2 ≤ |y₀| ^ 2 := by
        rw [← sq_abs (t - b)]
        exact pow_le_pow_left₀ (abs_nonneg _) ht 2
      have hsum : ((a + x₀) - a) ^ 2 + (t - b) ^ 2 < (r / 2) ^ 2 + (r / 2) ^ 2 := by
        have : (a + x₀) - a = x₀ := by ring
        rw [this]
        linarith
      linarith [sq_nonneg r]
    have hg_deriv_all : ∀ t : ℝ, |t - b| ≤ |y₀| →
        HasNSCDerivAt (fun y ↦ f (a + x₀) y) (fy (a + x₀) t) t :=
      fun t ht ↦ hfy (a + x₀) t (hdisk t ht)
    rcases lt_trichotomy 0 y₀ with hy_pos | rfl | hy_neg
    · have hcont : ContinuousOn (fun y ↦ f (a + x₀) y) (Set.Icc b (b + y₀)) := by
        intro t ht
        have htb : |t - b| ≤ |y₀| := by
          rw [abs_of_nonneg (sub_nonneg.2 ht.1), abs_of_pos hy_pos]
          linarith [ht.2]
        exact (hg_deriv_all t htb).continuousAt.continuousWithinAt
      have hderiv : ∀ t ∈ Set.Ioo b (b + y₀),
          HasNSCDerivAt (fun y ↦ f (a + x₀) y) (fy (a + x₀) t) t := by
        intro t ht
        have htb : |t - b| ≤ |y₀| := by
          rw [abs_of_pos (sub_pos.2 ht.1), abs_of_pos hy_pos]
          linarith [ht.2]
        exact hg_deriv_all t htb
      obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := mvt_nsc (lt_add_of_pos_right b hy_pos) hcont hderiv
      refine ⟨c₀, ?_, ?_⟩
      · rw [abs_of_pos (sub_pos.2 hc₀_mem.1), abs_of_pos hy_pos]
        linarith [hc₀_mem.2]
      · have hsub : (b + y₀) - b = y₀ := by ring
        rw [hsub] at hc₀_eq
        exact ((eq_div_iff hy_pos.ne').1 hc₀_eq).symm
    · exact ⟨b, by simp, by simp⟩
    · have hcont : ContinuousOn (fun y ↦ f (a + x₀) y) (Set.Icc (b + y₀) b) := by
        intro t ht
        have htb : |t - b| ≤ |y₀| := by
          rw [abs_of_nonpos (sub_nonpos.2 ht.2), abs_of_neg hy_neg]
          linarith [ht.1]
        exact (hg_deriv_all t htb).continuousAt.continuousWithinAt
      have hderiv : ∀ t ∈ Set.Ioo (b + y₀) b,
          HasNSCDerivAt (fun y ↦ f (a + x₀) y) (fy (a + x₀) t) t := by
        intro t ht
        have htb : |t - b| ≤ |y₀| := by
          rw [abs_of_neg (sub_neg.2 ht.2), abs_of_neg hy_neg]
          linarith [ht.1]
        exact hg_deriv_all t htb
      obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := mvt_nsc (add_lt_of_neg_right b hy_neg) hcont hderiv
      refine ⟨c₀, ?_, ?_⟩
      · rw [abs_of_neg (sub_neg.2 hc₀_mem.2), abs_of_neg hy_neg]
        linarith [hc₀_mem.1]
      · have hne : b - (b + y₀) ≠ 0 := by linarith
        have hmul := (eq_div_iff hne).1 hc₀_eq
        linarith
  -- Now take infinitesimals `Δx, Δy`
  intro Δx Δy hΔx hΔy
  -- Summand (iii): increment of `x ↦ f x b` at `a`
  obtain ⟨ε, hε, hinc_x⟩ := hfx.exists_incremental_eq hΔx
  -- Summand (iv): hyperreal transfer of `hreal_mvt`
  have hlt_x : |Δx| < ((r / 2 : ℝ) : ℝ*) := hΔx (r / 2) (half_pos hr)
  have hlt_y : |Δy| < ((r / 2 : ℝ) : ℝ*) := hΔy (r / 2) (half_pos hr)
  rcases ofSeq_surjective Δx with ⟨u, rfl⟩
  rcases ofSeq_surjective Δy with ⟨v, rfl⟩
  have hu_lt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |u n| < r / 2 := ofSeq_lt_ofSeq.1 hlt_x
  have hv_lt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |v n| < r / 2 := ofSeq_lt_ofSeq.1 hlt_y
  let cSeq : ℕ → ℝ := fun n ↦
    if h : |u n| < r / 2 ∧ |v n| < r / 2 then (hreal_mvt (u n) (v n) h.1 h.2).choose else b
  let c : ℝ* := ofSeq cSeq
  have hc_bound : |c - (b : ℝ*)| ≤ |ofSeq v| := by
    refine ofSeq_le_ofSeq.2 ((hu_lt.and hv_lt).mono fun n hn ↦ ?_)
    change |cSeq n - b| ≤ |v n|
    simp only [cSeq, hn, and_self, ↓reduceDIte]
    exact (hreal_mvt (u n) (v n) hn.1 hn.2).choose_spec.1
  have hc_close : c ≈ₕ (b : ℝ*) := isInfinitesimal_of_abs_le hΔy hc_bound
  have hmvt_star :
      starFun₂ f ((a : ℝ*) + ofSeq u) ((b : ℝ*) + ofSeq v) -
          starFun₂ f ((a : ℝ*) + ofSeq u) (b : ℝ*) =
        starFun₂ fy ((a : ℝ*) + ofSeq u) c * ofSeq v := by
    refine Germ.coe_eq.2 ((hu_lt.and hv_lt).mono fun n hn ↦ ?_)
    change f (a + u n) (b + v n) - f (a + u n) b = fy (a + u n) (cSeq n) * v n
    simp only [cSeq, hn, and_self, ↓reduceDIte]
    exact (hreal_mvt (u n) (v n) hn.1 hn.2).choose_spec.2
  have ha_close : (a : ℝ*) + ofSeq u ≈ₕ (a : ℝ*) := by
    unfold InfClose
    simpa using hΔx
  have hfy_close : starFun₂ fy ((a : ℝ*) + ofSeq u) c ≈ₕ (fy a b : ℝ*) :=
    hfy_cont ((a : ℝ*) + ofSeq u) c ha_close hc_close
  set δ : ℝ* := starFun₂ fy ((a : ℝ*) + ofSeq u) c - (fy a b : ℝ*)
  refine ⟨ε, δ, hε, hfy_close, ?_⟩
  have hinc_x' : starFun₂ f ((a : ℝ*) + ofSeq u) (b : ℝ*) =
      (f a b : ℝ*) + (fx_ab : ℝ*) * ofSeq u + ε * ofSeq u := by
    simpa [starFun₂_coe_right] using hinc_x
  have hfy_eq : starFun₂ fy ((a : ℝ*) + ofSeq u) c = (fy a b : ℝ*) + δ := by
    unfold δ
    ring
  rw [hfy_eq] at hmvt_star
  linarith

/-- **Goldblatt Theorem 8.7.1 (Incremental Equation for Two Variables, p. 98)**:
If `f` is smooth at `(a, b)`, then for all infinitesimals `Δx, Δy`,
`Δf = df + ε Δx + δ Δy` for some infinitesimals `ε, δ`. -/
theorem IsNSCSmoothAt.hasNSCTotalDerivAt {f fx fy : ℝ → ℝ → ℝ} {a b : ℝ}
    (hsmooth : IsNSCSmoothAt f fx fy a b) :
    HasNSCTotalDerivAt f (fx a b) (fy a b) a b := by
  obtain ⟨r, hr, hpart, _, hfy_cont⟩ := hsmooth
  have h0 : (a - a) ^ 2 + (b - b) ^ 2 < r ^ 2 := by
    simp [sq_pos_of_pos hr]
  exact hasNSCTotalDerivAt_of_partialDeriv₁_and_cont_partialDeriv₂ hr
    (hpart a b h0).1 (fun x y hxy ↦ (hpart x y hxy).2) hfy_cont

/-- **Goldblatt Exercise 8.8(1) (p. 100)**: Total differentiability at `(a, b)` implies
microcontinuity (`IsNSCContinuous₂At`) and classical continuity at `(a, b)`. -/
theorem HasNSCTotalDerivAt.isNSCContinuous₂At {f : ℝ → ℝ → ℝ} {fx fy a b : ℝ}
    (h : HasNSCTotalDerivAt f fx fy a b) : IsNSCContinuous₂At f a b := by
  intro x y hx hy
  obtain ⟨η₁, η₂, hη₁, hη₂, heq⟩ := h (x - (a : ℝ*)) (y - (b : ℝ*)) hx hy
  have hx_eq : (a : ℝ*) + (x - (a : ℝ*)) = x := add_sub_cancel _ _
  have hy_eq : (b : ℝ*) + (y - (b : ℝ*)) = y := add_sub_cancel _ _
  rw [hx_eq, hy_eq] at heq
  have hdiff : starFun₂ f x y - (f a b : ℝ*) =
      ((fx : ℝ*) + η₁) * (x - (a : ℝ*)) + ((fy : ℝ*) + η₂) * (y - (b : ℝ*)) := by linarith
  unfold InfClose
  rw [hdiff]
  exact (((isLimited_coe fx).add hη₁.isLimited).mul_isInfinitesimal hx).add
    (((isLimited_coe fy).add hη₂.isLimited).mul_isInfinitesimal hy)

/-- **Goldblatt Exercise 8.8(1) (p. 100)**: If `f` is smooth at `(a, b)`, then `f` is continuous
at `(a, b)` (both nonstandardly and classically). -/
theorem IsNSCSmoothAt.isNSCContinuous₂At {f fx fy : ℝ → ℝ → ℝ} {a b : ℝ}
    (hsmooth : IsNSCSmoothAt f fx fy a b) : IsNSCContinuous₂At f a b :=
  hsmooth.hasNSCTotalDerivAt.isNSCContinuous₂At

/-- Classical corollary of Exercise 8.8(1): smoothness at `(a, b)` implies `ContinuousAt`
on `ℝ × ℝ`. -/
theorem IsNSCSmoothAt.continuousAt_uncurry {f fx fy : ℝ → ℝ → ℝ} {a b : ℝ}
    (hsmooth : IsNSCSmoothAt f fx fy a b) : ContinuousAt (Function.uncurry f) (a, b) :=
  continuousAt_uncurry_iff_isNSCContinuous₂At.2 hsmooth.isNSCContinuous₂At

/-- **Goldblatt Exercise 8.8(2) (p. 100)**: If `f` satisfies the 2D incremental equation at `(a, b)`
and `Δx, Δy` are infinitesimals not both zero, then `Δl = √(Δx² + Δy²) ≠ 0` and
`(Δf - df) / Δl ≈ₕ 0` (`Δf - df` is infinitely smaller than the Euclidean distance `Δl`). -/
theorem HasNSCTotalDerivAt.increment_sub_totalDifferential_div_dist_infClose_zero
    {f : ℝ → ℝ → ℝ} {fx fy a b : ℝ} (h : HasNSCTotalDerivAt f fx fy a b)
    {Δx Δy : ℝ*} (hΔx : IsInfinitesimal Δx) (hΔy : IsInfinitesimal Δy)
    (hne : Δx ≠ 0 ∨ Δy ≠ 0) :
    starFun Real.sqrt (Δx ^ 2 + Δy ^ 2) ≠ 0 ∧
      (nscIncrement₂ f a b Δx Δy - nscTotalDifferential fx fy Δx Δy) /
        starFun Real.sqrt (Δx ^ 2 + Δy ^ 2) ≈ₕ 0 := by
  obtain ⟨ε, δ, hε, hδ, heq⟩ := h Δx Δy hΔx hΔy
  have hdiff : nscIncrement₂ f a b Δx Δy - nscTotalDifferential fx fy Δx Δy =
      ε * Δx + δ * Δy := by
    unfold nscIncrement₂ nscTotalDifferential
    linarith
  rcases ofSeq_surjective Δx with ⟨u, rfl⟩
  rcases ofSeq_surjective Δy with ⟨v, rfl⟩
  rcases ofSeq_surjective ε with ⟨e, rfl⟩
  rcases ofSeq_surjective δ with ⟨d, rfl⟩
  have huv_ne : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), u n ≠ 0 ∨ v n ≠ 0 := by
    rcases hne with h1 | h2
    · exact (Ultrafilter.eventually_not.2 fun h0 ↦ h1 (Germ.coe_eq.2 h0)).mono fun _ hn ↦ Or.inl hn
    · exact (Ultrafilter.eventually_not.2 fun h0 ↦ h2 (Germ.coe_eq.2 h0)).mono fun _ hn ↦ Or.inr hn
  have hsqrt_pos : ∀ n : ℕ, u n ≠ 0 ∨ v n ≠ 0 → 0 < Real.sqrt ((u n) ^ 2 + (v n) ^ 2) := by
    intro n hn
    apply Real.sqrt_pos.2
    rcases hn with hu0 | hv0
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hu0) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hv0)
  refine ⟨?_, ?_⟩
  · intro h0
    have hev0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), Real.sqrt ((u n) ^ 2 + (v n) ^ 2) = 0 :=
      Germ.coe_eq.1 h0
    obtain ⟨n, hn_ne, hn_eq⟩ := (huv_ne.and hev0).exists
    exact (hsqrt_pos n hn_ne).ne' hn_eq
  · rw [infClose_zero_iff, hdiff]
    have hsum_inf : IsInfinitesimal (|ofSeq e| + |ofSeq d|) := hε.abs.add hδ.abs
    have hsum_nn : 0 ≤ |ofSeq e| + |ofSeq d| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    refine isInfinitesimal_of_abs_le hsum_inf ?_
    rw [abs_of_nonneg hsum_nn]
    refine ofSeq_le_ofSeq.2 (huv_ne.mono fun n hn ↦ ?_)
    change |(e n * u n + d n * v n) / Real.sqrt ((u n) ^ 2 + (v n) ^ 2)| ≤ |e n| + |d n|
    set L : ℝ := Real.sqrt ((u n) ^ 2 + (v n) ^ 2)
    have hL_pos : 0 < L := hsqrt_pos n hn
    have hu_le : |u n| ≤ L := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hv_le : |v n| ≤ L := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith)
    rw [abs_div, abs_of_pos hL_pos, div_le_iff₀ hL_pos]
    calc |e n * u n + d n * v n|
        ≤ |e n * u n| + |d n * v n| := abs_add_le _ _
      _ = |e n| * |u n| + |d n| * |v n| := by rw [abs_mul, abs_mul]
      _ ≤ |e n| * L + |d n| * L := by gcongr
      _ = (|e n| + |d n|) * L := by ring

/-- **Goldblatt Exercise 8.8(2) (p. 100)** specialized directly to smooth functions `f`. -/
theorem IsNSCSmoothAt.increment_sub_totalDifferential_div_dist_infClose_zero
    {f fx fy : ℝ → ℝ → ℝ} {a b : ℝ} (hsmooth : IsNSCSmoothAt f fx fy a b)
    {Δx Δy : ℝ*} (hΔx : IsInfinitesimal Δx) (hΔy : IsInfinitesimal Δy)
    (hne : Δx ≠ 0 ∨ Δy ≠ 0) :
    starFun Real.sqrt (Δx ^ 2 + Δy ^ 2) ≠ 0 ∧
      (nscIncrement₂ f a b Δx Δy - nscTotalDifferential (fx a b) (fy a b) Δx Δy) /
        starFun Real.sqrt (Δx ^ 2 + Δy ^ 2) ≈ₕ 0 :=
  hsmooth.hasNSCTotalDerivAt.increment_sub_totalDifferential_div_dist_infClose_zero hΔx hΔy hne

/-- **Multivariable Chain Rule via the 2D Incremental Equation**:
If `f : ℝ → ℝ → ℝ` has nonstandard total derivative `(fx, fy)` at `(x t, y t)` and `x, y : ℝ → ℝ`
have nonstandard derivatives `x', y'` at `t`, then `s ↦ f (x s) (y s)` has nonstandard derivative
`fx * x' + fy * y'` at `t`. -/
theorem HasNSCTotalDerivAt.comp₂ {f : ℝ → ℝ → ℝ} {x y : ℝ → ℝ} {fx fy x' y' t : ℝ}
    (hf : HasNSCTotalDerivAt f fx fy (x t) (y t))
    (hx : HasNSCDerivAt x x' t) (hy : HasNSCDerivAt y y' t) :
    HasNSCDerivAt (fun s ↦ f (x s) (y s)) (fx * x' + fy * y') t := by
  intro Δt hΔt hne
  set Δx : ℝ* := starFun x ((t : ℝ*) + Δt) - (x t : ℝ*)
  set Δy : ℝ* := starFun y ((t : ℝ*) + Δt) - (y t : ℝ*)
  have hΔx : IsInfinitesimal Δx := hx.isInfinitesimal_increment hΔt
  have hΔy : IsInfinitesimal Δy := hy.isInfinitesimal_increment hΔt
  obtain ⟨η₁, η₂, hη₁, hη₂, hinc⟩ := hf Δx Δy hΔx hΔy
  have hcomp_eq : starFun (fun s ↦ f (x s) (y s)) ((t : ℝ*) + Δt) =
      starFun₂ f ((x t : ℝ*) + Δx) ((y t : ℝ*) + Δy) := by
    have hx_eq : (x t : ℝ*) + Δx = starFun x ((t : ℝ*) + Δt) := add_sub_cancel _ _
    have hy_eq : (y t : ℝ*) + Δy = starFun y ((t : ℝ*) + Δt) := add_sub_cancel _ _
    rw [hx_eq, hy_eq]
    rcases ofSeq_surjective ((t : ℝ*) + Δt) with ⟨r, hr⟩
    rw [← hr]
    rfl
  have hquot :
      (starFun (fun s ↦ f (x s) (y s)) ((t : ℝ*) + Δt) - ((f (x t) (y t) : ℝ) : ℝ*)) / Δt =
        ((fx : ℝ*) + η₁) * (Δx / Δt) + ((fy : ℝ*) + η₂) * (Δy / Δt) := by
    rw [hcomp_eq, hinc]
    have hsub : ((f (x t) (y t) : ℝ*) + (fx : ℝ*) * Δx + (fy : ℝ*) * Δy + η₁ * Δx + η₂ * Δy) -
        (f (x t) (y t) : ℝ*) = ((fx : ℝ*) + η₁) * Δx + ((fy : ℝ*) + η₂) * Δy := by ring
    rw [hsub, add_div, mul_div_assoc, mul_div_assoc]
  rw [hquot]
  have h1 : ((fx : ℝ*) + η₁) * (Δx / Δt) ≈ₕ (fx : ℝ*) * (x' : ℝ*) := by
    have hc : (fx : ℝ*) + η₁ ≈ₕ (fx : ℝ*) := by unfold InfClose; simpa using hη₁
    exact InfClose.mul ((isLimited_coe fx).add hη₁.isLimited)
      (hx.isLimited_newtonQuotient hΔt hne) hc (hx Δt hΔt hne)
  have h2 : ((fy : ℝ*) + η₂) * (Δy / Δt) ≈ₕ (fy : ℝ*) * (y' : ℝ*) := by
    have hc : (fy : ℝ*) + η₂ ≈ₕ (fy : ℝ*) := by unfold InfClose; simpa using hη₂
    exact InfClose.mul ((isLimited_coe fy).add hη₂.isLimited)
      (hy.isLimited_newtonQuotient hΔt hne) hc (hy Δt hΔt hne)
  have htarget : (((fx * x' + fy * y' : ℝ)) : ℝ*) =
      (fx : ℝ*) * (x' : ℝ*) + (fy : ℝ*) * (y' : ℝ*) := by
    push_cast
    rfl
  rw [htarget]
  exact h1.add h2

/-- Two-parameter multivariable chain rule for partial derivatives of
`z(u, v) = f(x(u, v), y(u, v))`. -/
theorem HasNSCTotalDerivAt.partialDeriv₁_comp₂
    {f x y : ℝ → ℝ → ℝ} {fx fy xu yu u v : ℝ}
    (hf : HasNSCTotalDerivAt f fx fy (x u v) (y u v))
    (hx : HasNSCPartialDeriv₁ x xu u v) (hy : HasNSCPartialDeriv₁ y yu u v) :
    HasNSCPartialDeriv₁ (fun s w ↦ f (x s w) (y s w)) (fx * xu + fy * yu) u v :=
  hf.comp₂ (x := fun s ↦ x s v) (y := fun s ↦ y s v) hx hy

/-- Second partial derivative version of the two-parameter multivariable chain rule. -/
theorem HasNSCTotalDerivAt.partialDeriv₂_comp₂
    {f x y : ℝ → ℝ → ℝ} {fx fy xv yv u v : ℝ}
    (hf : HasNSCTotalDerivAt f fx fy (x u v) (y u v))
    (hx : HasNSCPartialDeriv₂ x xv u v) (hy : HasNSCPartialDeriv₂ y yv u v) :
    HasNSCPartialDeriv₂ (fun s w ↦ f (x s w) (y s w)) (fx * xv + fy * yv) u v :=
  hf.comp₂ (x := fun w ↦ x u w) (y := fun w ↦ y u w) hx hy

/-! ## §8.9 Taylor Series and Hyperreal Lagrange Remainder (pp. 100–102) -/

/-- Nonstandard finite-sum rule for `HasNSCDerivAt`. -/
theorem hasNSCDerivAt_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {f' : ι → ℝ} {x : ℝ}
    (hf : ∀ i ∈ s, HasNSCDerivAt (f i) (f' i) x) :
    HasNSCDerivAt (fun t ↦ ∑ i ∈ s, f i t) (∑ i ∈ s, f' i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using hasNSCDerivAt_const 0 x
  | insert a s ha ih =>
      have hfn : (fun t : ℝ ↦ ∑ i ∈ insert a s, f i t) =
          (fun t : ℝ ↦ f a t + ∑ i ∈ s, f i t) := by
        ext t
        exact Finset.sum_insert ha
      rw [hfn, Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- Nonstandard derivative of `(t - a)^k`: `d/dt ((t - a)^k) = k * (t - a)^(k - 1)`. -/
theorem hasNSCDerivAt_sub_pow (a : ℝ) (k : ℕ) (t : ℝ) :
    HasNSCDerivAt (fun s ↦ (s - a) ^ k) ((k : ℝ) * (t - a) ^ (k - 1)) t := by
  have hsub : HasNSCDerivAt (fun s ↦ s - a) 1 t := by
    simpa using (hasNSCDerivAt_id t).sub (hasNSCDerivAt_const a t)
  have hcomp := HasNSCDerivAt.comp (f := fun s ↦ s - a) (hasNSCDerivAt_pow k (t - a)) hsub
  simpa [Function.comp_def] using hcomp

/-- Goldblatt §8.9 (p. 100): The `n`-th Taylor polynomial of `f` centred at `a`:
`P_n(x) = ∑_{k=0}^n (f^{(k)}(a) / k!) (x - a)^k`. -/
def taylorPoly (f : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (deriv^[k] f a / (k.factorial : ℝ)) * (x - a) ^ k

/-- Goldblatt §8.9 (p. 100, eq. (vii)): The `n`-th Taylor remainder `R_n(x) = f(x) - P_n(x)`. -/
def taylorRemainder (f : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  f x - taylorPoly f a n x

/-- `P_0(x) = f(a)`. -/
@[simp]
theorem taylorPoly_zero (f : ℝ → ℝ) (a x : ℝ) :
    taylorPoly f a 0 x = f a := by
  simp [taylorPoly]

/-- `P_n(a) = f(a)` for every `n ∈ ℕ`. -/
@[simp]
theorem taylorPoly_self (f : ℝ → ℝ) (a : ℝ) (n : ℕ) :
    taylorPoly f a n a = f a := by
  unfold taylorPoly
  rw [Finset.sum_range_succ']
  simp

/-- `R_n(a) = 0` for every `n ∈ ℕ`. -/
@[simp]
theorem taylorRemainder_self (f : ℝ → ℝ) (a : ℝ) (n : ℕ) :
    taylorRemainder f a n a = 0 := by
  simp [taylorRemainder]

/-- Step difference `P_{n+1}(x) - P_n(x) = (f^{(n+1)}(a) / (n+1)!) (x - a)^{n+1}`. -/
theorem taylorPoly_succ_sub (f : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ) :
    taylorPoly f a (n + 1) x - taylorPoly f a n x =
      (deriv^[n + 1] f a / ((n + 1).factorial : ℝ)) * (x - a) ^ (n + 1) := by
  unfold taylorPoly
  rw [Finset.sum_range_succ]
  ring

/-- Goldblatt §8.9 (p. 101): Hypersequence extension `*F(N, x)` of `F(n, x) = f^{(n)}(x)` to
`N ∈ ℕ*` and `x ∈ ℝ*`. -/
def starIterDeriv (f : ℝ → ℝ) (N : ℕ*) (x : ℝ*) : ℝ* :=
  Germ.map₂ (fun n t ↦ deriv^[n] f t) N x

/-- Hyperreal power `x ^ N` for `x ∈ ℝ*` and `N ∈ ℕ*`. -/
def starRealPow (x : ℝ*) (N : ℕ*) : ℝ* :=
  Germ.map₂ (fun t n ↦ t ^ n) x N

/-- Hypersequence extension `*P_N(x)` of `P_n(x) = taylorPoly f a n x` to `N ∈ ℕ*` and `x ∈ ℝ*`. -/
def starTaylorPoly (f : ℝ → ℝ) (a : ℝ) (N : ℕ*) (x : ℝ*) : ℝ* :=
  Germ.map₂ (fun n t ↦ taylorPoly f a n t) N x

/-- Goldblatt §8.9 (p. 100, eq. (vii) by transfer): `R_N(x) = f(x) - P_N(x)` for all `N ∈ ℕ*`. -/
theorem starSeq_taylorRemainder_eq (f : ℝ → ℝ) (a x : ℝ) (N : ℕ*) :
    starSeq (fun n ↦ taylorRemainder f a n x) N =
      (f x : ℝ*) - starSeq (fun n ↦ taylorPoly f a n x) N :=
  Germ.inductionOn N fun _ ↦ rfl

/-- Goldblatt §8.9 (p. 101): By transfer,
`P_{N+1}(x) - P_N(x) = f^{(N+1)}(a) (x - a)^{N+1} / (N+1)!`
continues to hold for every hypernatural `N ∈ ℕ*` (including unlimited `N`). -/
theorem starSeq_taylorPoly_succ_sub (f : ℝ → ℝ) (a x : ℝ) (N : ℕ*) :
    starSeq (fun n ↦ taylorPoly f a (n + 1) x) N - starSeq (fun n ↦ taylorPoly f a n x) N =
      (starIterDeriv f (N + 1) (a : ℝ*) / Hypernat.toHyperreal (hyperFactorial (N + 1))) *
        starRealPow ((x - a : ℝ) : ℝ*) (N + 1) := by
  induction N using Germ.inductionOn with | _ m =>
  exact Germ.coe_eq.2 (Eventually.of_forall fun i ↦ taylorPoly_succ_sub f a (m i) x)

/-- Internal sequence-limit bridge: `s_n → L` iff `starSeq s N ≈ₕ L` for all unlimited `N ∈ ℕ*`. -/
private theorem tendsto_atTop_iff_infClose_unlimited {s : ℕ → ℝ} {L : ℝ} :
    Tendsto s atTop (𝓝 L) ↔ ∀ N : ℕ*, IsUnlimitedNat N → starSeq s N ≈ₕ (L : ℝ*) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro hs N hN ε hε
    obtain ⟨M, hM⟩ := hs ε hε
    have hltM : (M : ℕ*) < N := hN M
    induction N using Germ.inductionOn with | _ a =>
    have ha : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), M < a i := Germ.coe_lt.1 hltM
    refine ofSeq_lt_ofSeq.2 (ha.mono fun i hi ↦ ?_)
    change |s (a i) - L| < ε
    simpa only [Real.dist_eq] using hM (a i) hi.le
  · intro h ε hε
    by_contra hnot
    push Not at hnot
    have hex : ∀ k : ℕ, ∃ m : ℕ, k + 1 ≤ m ∧ ε ≤ |s m - L| := by
      intro k
      obtain ⟨m, hkm, hge⟩ := hnot (k + 1)
      exact ⟨m, hkm, by simpa only [Real.dist_eq] using hge⟩
    choose a ha using hex
    let N : ℕ* := (a : ℕ*)
    have hN_unl : IsUnlimitedNat N := by
      intro n
      have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), n < a i := by
        have hat : ∀ᶠ i in atTop, n < a i :=
          eventually_atTop.2 ⟨n, fun i hi ↦ by have := (ha i).1; omega⟩
        exact hat.filter_mono Nat.hyperfilter_le_atTop
      exact Germ.coe_lt.2 hev
    have hlt := h N hN_unl ε hε
    have hge : (ε : ℝ*) ≤ |starSeq s N - (L : ℝ*)| :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun i ↦ (ha i).2)
    exact not_lt_of_ge hge hlt

/-- **Goldblatt §8.9 (p. 100)**: The Taylor series of `f` at `x` centred on `a` converges to `L ∈ ℝ`
if and only if `P_N(x) ≈ₕ L` for every unlimited hypernatural `N ∈ ℕ*`. -/
theorem tendsto_taylorPoly_iff_infClose_unlimited {f : ℝ → ℝ} {a x L : ℝ} :
    Tendsto (fun n ↦ taylorPoly f a n x) atTop (𝓝 L) ↔
      ∀ N : ℕ*, IsUnlimitedNat N → starSeq (fun n ↦ taylorPoly f a n x) N ≈ₕ (L : ℝ*) :=
  tendsto_atTop_iff_infClose_unlimited

/-- **Goldblatt §8.9 (p. 101)**: The Taylor series of `f` at `x` converges to `f(x)` if and only if
the remainder `R_N(x)` is infinitesimal for every unlimited hypernatural `N ∈ ℕ*`. -/
theorem tendsto_taylorPoly_self_iff_isInfinitesimal_remainder {f : ℝ → ℝ} {a x : ℝ} :
    Tendsto (fun n ↦ taylorPoly f a n x) atTop (𝓝 (f x)) ↔
      ∀ N : ℕ*, IsUnlimitedNat N →
        IsInfinitesimal (starSeq (fun n ↦ taylorRemainder f a n x) N) := by
  rw [tendsto_taylorPoly_iff_infClose_unlimited]
  constructor
  · intro h N hN
    rw [starSeq_taylorRemainder_eq]
    exact (h N hN).symm
  · intro h N hN
    have hrem := h N hN
    rw [starSeq_taylorRemainder_eq] at hrem
    exact InfClose.symm hrem

/-- Key differentiation identity: `d/dt (R_{n+1}(f, a, t)) = R_n(f', a, t)`. -/
theorem hasNSCDerivAt_taylorRemainder_succ {f : ℝ → ℝ} {a t : ℝ} (n : ℕ)
    (hf : DifferentiableAt ℝ f t) :
    HasNSCDerivAt (taylorRemainder f a (n + 1)) (taylorRemainder (deriv f) a n t) t := by
  have hf_nsc : HasNSCDerivAt f (deriv f t) t :=
    hasDerivAt_iff_hasNSCDerivAt.1 hf.hasDerivAt
  have hpoly_eq : taylorPoly f a (n + 1) =
      (fun s : ℝ ↦ f a + ∑ j ∈ Finset.range (n + 1),
        (deriv^[j + 1] f a / ((j + 1).factorial : ℝ)) * (s - a) ^ (j + 1)) := by
    ext s
    unfold taylorPoly
    rw [Finset.sum_range_succ']
    simp [add_comm]
  have hsum_deriv : HasNSCDerivAt
      (fun s : ℝ ↦ ∑ j ∈ Finset.range (n + 1),
        (deriv^[j + 1] f a / ((j + 1).factorial : ℝ)) * (s - a) ^ (j + 1))
      (taylorPoly (deriv f) a n t) t := by
    unfold taylorPoly
    refine hasNSCDerivAt_sum (Finset.range (n + 1)) fun j _ ↦ ?_
    have hterm := (hasNSCDerivAt_sub_pow a (j + 1) t).const_mul
      (deriv^[j + 1] f a / ((j + 1).factorial : ℝ))
    have hcoef : (deriv^[j + 1] f a / ((j + 1).factorial : ℝ)) *
        (((j + 1 : ℕ) : ℝ) * (t - a) ^ j) =
        (deriv^[j] (deriv f) a / (j.factorial : ℝ)) * (t - a) ^ j := by
      rw [Function.iterate_succ_apply, Nat.factorial_succ]
      push_cast
      have hne : (j : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hne]
    simpa only [Nat.add_sub_cancel, hcoef] using hterm
  have hpoly_deriv : HasNSCDerivAt (taylorPoly f a (n + 1)) (taylorPoly (deriv f) a n t) t := by
    rw [hpoly_eq]
    simpa using (hasNSCDerivAt_const (f a) t).add hsum_deriv
  exact hf_nsc.sub hpoly_deriv

/-- Helper step via `cauchy_mvt_nsc`: for `x ≠ a` and `m ≥ 1`, if `g` is continuous on the closed
interval between `a` and `x`, differentiable on the open interval between `a` and `x`, and
`g a = 0`, then there is `c₁` strictly between `a` and `x` (`min a x < c₁ < max a x`) such that
`g x / (x - a)^m = g' c₁ / (m * (c₁ - a)^(m - 1))`. -/
private theorem exists_cauchy_step_between {g g' : ℝ → ℝ} {a x : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hxa : x ≠ a)
    (hg_cont : ContinuousOn g (Set.Icc (min a x) (max a x)))
    (hg_deriv : ∀ t ∈ Set.Ioo (min a x) (max a x), HasNSCDerivAt g (g' t) t)
    (hga : g a = 0) :
    ∃ c₁ ∈ Set.Ioo (min a x) (max a x),
      g x * ((m : ℝ) * (c₁ - a) ^ (m - 1)) = (x - a) ^ m * g' c₁ := by
  let p : ℝ → ℝ := fun t ↦ (t - a) ^ m
  have hp_cont : ContinuousOn p (Set.Icc (min a x) (max a x)) :=
    (continuousOn_id.sub continuousOn_const).pow m
  have hp_deriv : ∀ t ∈ Set.Ioo (min a x) (max a x),
      HasNSCDerivAt p ((m : ℝ) * (t - a) ^ (m - 1)) t :=
    fun t _ ↦ hasNSCDerivAt_sub_pow a m t
  have hpa : p a = 0 := by
    simp [p, zero_pow (Nat.ne_of_gt hm)]
  rcases lt_or_gt_of_ne hxa with hlt | hgt
  · have hmin : min a x = x := min_eq_right hlt.le
    have hmax : max a x = a := max_eq_left hlt.le
    rw [hmin, hmax] at hg_cont hg_deriv hp_cont hp_deriv ⊢
    obtain ⟨c₁, hc₁, heq⟩ := cauchy_mvt_nsc hlt hg_cont hg_deriv hp_cont hp_deriv
    refine ⟨c₁, hc₁, ?_⟩
    rw [hga, hpa] at heq
    linarith
  · have hmin : min a x = a := min_eq_left hgt.le
    have hmax : max a x = x := max_eq_right hgt.le
    rw [hmin, hmax] at hg_cont hg_deriv hp_cont hp_deriv ⊢
    obtain ⟨c₁, hc₁, heq⟩ := cauchy_mvt_nsc hgt hg_cont hg_deriv hp_cont hp_deriv
    refine ⟨c₁, hc₁, ?_⟩
    rw [hga, hpa] at heq
    linarith

/-- **Lagrange Form of the Taylor Remainder** (Goldblatt §8.9, p. 101, eq. (viii), strict version):
proved self-containedly by induction on `n` from our nonstandard `mvt_nsc` and `cauchy_mvt_nsc`! -/
theorem taylorRemainder_lagrange_strict {f : ℝ → ℝ} {u v a x : ℝ} (n : ℕ)
    (ha : a ∈ Set.Ioo u v) (hx : x ∈ Set.Ioo u v) (hxa : x ≠ a)
    (hdiff : ∀ k ≤ n, ∀ t ∈ Set.Ioo u v, DifferentiableAt ℝ (deriv^[k] f) t) :
    ∃ c ∈ Set.Ioo (min a x) (max a x),
      taylorRemainder f a n x =
        (deriv^[n + 1] f c / ((n + 1).factorial : ℝ)) * (x - a) ^ (n + 1) := by
  induction n generalizing f x with
  | zero =>
      have hIcc_sub : Set.Icc (min a x) (max a x) ⊆ Set.Ioo u v := fun t ht ↦
        ⟨(lt_min ha.1 hx.1).trans_le ht.1, ht.2.trans_lt (max_lt ha.2 hx.2)⟩
      have hf_deriv : ∀ t ∈ Set.Ioo (min a x) (max a x), HasNSCDerivAt f (deriv f t) t :=
        fun t ht ↦ hasDerivAt_iff_hasNSCDerivAt.1
          (hdiff 0 (Nat.zero_le 0) t (hIcc_sub (Set.Ioo_subset_Icc_self ht))).hasDerivAt
      have hf_cont : ContinuousOn f (Set.Icc (min a x) (max a x)) := fun t ht ↦
        (hdiff 0 (Nat.zero_le 0) t (hIcc_sub ht)).continuousAt.continuousWithinAt
      let g0 : ℝ → ℝ := fun t ↦ f t - f a
      have hg0_cont : ContinuousOn g0 (Set.Icc (min a x) (max a x)) :=
        hf_cont.sub continuousOn_const
      have hg0_deriv : ∀ t ∈ Set.Ioo (min a x) (max a x), HasNSCDerivAt g0 (deriv f t) t :=
        fun t ht ↦ by simpa [g0] using (hf_deriv t ht).sub (hasNSCDerivAt_const (f a) t)
      obtain ⟨c, hc, hceq⟩ := exists_cauchy_step_between (le_refl 1) hxa
        hg0_cont hg0_deriv (sub_self (f a))
      refine ⟨c, hc, ?_⟩
      dsimp only [g0] at hceq
      simp only [taylorRemainder, taylorPoly_zero, zero_add, Nat.factorial_one, Nat.cast_one,
        div_one, pow_one, Function.iterate_one]
      simp only [Nat.cast_one, tsub_self, pow_zero, mul_one, pow_one] at hceq
      linarith
  | succ m ih =>
      have hIcc_sub : Set.Icc (min a x) (max a x) ⊆ Set.Ioo u v := fun t ht ↦
        ⟨(lt_min ha.1 hx.1).trans_le ht.1, ht.2.trans_lt (max_lt ha.2 hx.2)⟩
      have hrem_cont :
          ContinuousOn (taylorRemainder f a (m + 1)) (Set.Icc (min a x) (max a x)) := by
        intro t ht
        exact (hasDerivAt_iff_hasNSCDerivAt.2
          (hasNSCDerivAt_taylorRemainder_succ m
            (hdiff 0 (Nat.zero_le _) t (hIcc_sub ht)))).continuousAt.continuousWithinAt
      have hrem_deriv : ∀ t ∈ Set.Ioo (min a x) (max a x),
          HasNSCDerivAt (taylorRemainder f a (m + 1)) (taylorRemainder (deriv f) a m t) t :=
        fun t ht ↦ hasNSCDerivAt_taylorRemainder_succ m
          (hdiff 0 (Nat.zero_le _) t (hIcc_sub (Set.Ioo_subset_Icc_self ht)))
      obtain ⟨c₁, hc₁, hc₁_eq⟩ := exists_cauchy_step_between (by omega : 1 ≤ m + 2) hxa
        hrem_cont hrem_deriv (taylorRemainder_self f a (m + 1))
      have hc₁_uv : c₁ ∈ Set.Ioo u v := hIcc_sub (Set.Ioo_subset_Icc_self hc₁)
      have hc₁_ne : c₁ ≠ a := by
        rcases lt_or_gt_of_ne hxa with hlt | hgt
        · rw [max_eq_left hlt.le] at hc₁
          exact hc₁.2.ne
        · rw [min_eq_left hgt.le] at hc₁
          exact hc₁.1.ne'
      have hdiff' : ∀ k ≤ m, ∀ t ∈ Set.Ioo u v, DifferentiableAt ℝ (deriv^[k] (deriv f)) t := by
        intro k hk t ht
        rw [← Function.iterate_succ_apply]
        exact hdiff (k + 1) (Nat.succ_le_succ hk) t ht
      obtain ⟨c, hc, hc_eq⟩ := ih hc₁_uv hc₁_ne hdiff'
      have hc_in : c ∈ Set.Ioo (min a x) (max a x) := by
        rcases lt_or_gt_of_ne hxa with hlt | hgt
        · have hc₁_lt : c₁ < a := by simpa [max_eq_left hlt.le] using hc₁.2
          have hx_lt_c₁ : x < c₁ := by simpa [min_eq_right hlt.le] using hc₁.1
          rw [min_eq_right hc₁_lt.le, max_eq_left hc₁_lt.le] at hc
          rw [min_eq_right hlt.le, max_eq_left hlt.le]
          exact ⟨hx_lt_c₁.trans hc.1, hc.2⟩
        · have ha_lt_c₁ : a < c₁ := by simpa [min_eq_left hgt.le] using hc₁.1
          have hc₁_lt_x : c₁ < x := by simpa [max_eq_right hgt.le] using hc₁.2
          rw [min_eq_left ha_lt_c₁.le, max_eq_right ha_lt_c₁.le] at hc
          rw [min_eq_left hgt.le, max_eq_right hgt.le]
          exact ⟨hc.1, hc.2.trans hc₁_lt_x⟩
      refine ⟨c, hc_in, ?_⟩
      rw [hc_eq, ← Function.iterate_succ_apply] at hc₁_eq
      have hc₁_pow_ne : (c₁ - a) ^ (m + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hc₁_ne)
      have hm2_ne : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      have hfac_ne : ((m + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have hfac_succ : ((m + 2).factorial : ℝ) = ((m + 2 : ℕ) : ℝ) * ((m + 1).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_succ (m + 1)
      rw [show m + 1 + 1 = m + 2 by omega, hfac_succ]
      have hcancel : taylorRemainder f a (m + 1) x * ((m + 2 : ℕ) : ℝ) =
          (deriv^[m + 2] f c / ((m + 1).factorial : ℝ)) * (x - a) ^ (m + 2) := by
        apply mul_right_cancel₀ hc₁_pow_ne
        calc taylorRemainder f a (m + 1) x * ((m + 2 : ℕ) : ℝ) * (c₁ - a) ^ (m + 1)
            = taylorRemainder f a (m + 1) x * (((m + 2 : ℕ) : ℝ) * (c₁ - a) ^ (m + 1)) := by ring
          _ = (x - a) ^ (m + 2) *
                ((deriv^[m + 2] f c / ((m + 1).factorial : ℝ)) * (c₁ - a) ^ (m + 1)) := hc₁_eq
          _ = (deriv^[m + 2] f c / ((m + 1).factorial : ℝ)) * (x - a) ^ (m + 2) *
                (c₁ - a) ^ (m + 1) := by ring
      field_simp [hm2_ne, hfac_ne] at hcancel ⊢
      linarith

/-- **Lagrange Form of the Taylor Remainder** (for all `x ∈ (u, v)`, including `x = a`). -/
theorem taylorRemainder_lagrange {f : ℝ → ℝ} {u v a x : ℝ} (n : ℕ)
    (ha : a ∈ Set.Ioo u v) (hx : x ∈ Set.Ioo u v)
    (hdiff : ∀ k ≤ n, ∀ t ∈ Set.Ioo u v, DifferentiableAt ℝ (deriv^[k] f) t) :
    ∃ c ∈ Set.Icc (min a x) (max a x),
      taylorRemainder f a n x =
        (deriv^[n + 1] f c / ((n + 1).factorial : ℝ)) * (x - a) ^ (n + 1) := by
  by_cases hxa : x = a
  · subst hxa
    exact ⟨x, ⟨by simp, by simp⟩, by simp⟩
  · obtain ⟨c, hc, hceq⟩ := taylorRemainder_lagrange_strict n ha hx hxa hdiff
    exact ⟨c, Set.Ioo_subset_Icc_self hc, hceq⟩

/-- **Goldblatt §8.9 (Hyperreal Transfer of Lagrange's Remainder, p. 101, eq. (viii))**:
If `f` is infinitely differentiable on `(u, v)` containing `a`, then for every `N ∈ ℕ*` and every
`x ∈ *(u, v)`, there exists `c ∈ ℝ*` between `a` and `x` (`min a x ≤ c ≤ max a x`) such that
`*f(x) - *P_N(x) = *f^{(N+1)}(c) * (x - a)^{N+1} / (N + 1)!`. -/
theorem hyperreal_taylorRemainder_lagrange {f : ℝ → ℝ} {u v a : ℝ}
    (ha : a ∈ Set.Ioo u v)
    (hdiff : ∀ k : ℕ, ∀ t ∈ Set.Ioo u v, DifferentiableAt ℝ (deriv^[k] f) t)
    (N : ℕ*) {x : ℝ*} (hx : x ∈ starSet (Set.Ioo u v)) :
    ∃ c : ℝ*, min (a : ℝ*) x ≤ c ∧ c ≤ max (a : ℝ*) x ∧
      starFun f x - starTaylorPoly f a N x =
        (starIterDeriv f (N + 1) c / Hypernat.toHyperreal (hyperFactorial (N + 1))) *
          starRealPow (x - (a : ℝ*)) (N + 1) := by
  induction N using Germ.inductionOn with | _ m =>
  rcases ofSeq_surjective x with ⟨s, rfl⟩
  have hs : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), s i ∈ Set.Ioo u v := ofSeq_mem_starSet.1 hx
  let cSeq : ℕ → ℝ := fun i ↦
    if h : s i ∈ Set.Ioo u v then
      (taylorRemainder_lagrange (m i) ha h (fun k _ ↦ hdiff k)).choose
    else a
  refine ⟨ofSeq cSeq, ?_, ?_, ?_⟩
  · have hmin_eq : min (a : ℝ*) (ofSeq s) = ofSeq (fun i ↦ min a (s i)) := rfl
    rw [hmin_eq]
    refine ofSeq_le_ofSeq.2 (hs.mono fun i hi ↦ ?_)
    simp only [cSeq, hi, ↓reduceDIte]
    exact (taylorRemainder_lagrange (m i) ha hi (fun k _ ↦ hdiff k)).choose_spec.1.1
  · have hmax_eq : max (a : ℝ*) (ofSeq s) = ofSeq (fun i ↦ max a (s i)) := rfl
    rw [hmax_eq]
    refine ofSeq_le_ofSeq.2 (hs.mono fun i hi ↦ ?_)
    simp only [cSeq, hi, ↓reduceDIte]
    exact (taylorRemainder_lagrange (m i) ha hi (fun k _ ↦ hdiff k)).choose_spec.1.2
  · refine Germ.coe_eq.2 (hs.mono fun i hi ↦ ?_)
    change f (s i) - taylorPoly f a (m i) (s i) =
      (deriv^[m i + 1] f (cSeq i) / ((m i + 1).factorial : ℝ)) * (s i - a) ^ (m i + 1)
    simp only [cSeq, hi, ↓reduceDIte]
    exact (taylorRemainder_lagrange (m i) ha hi (fun k _ ↦ hdiff k)).choose_spec.2

/-- Goldblatt Exercise 6.11(10) (cited in §8.9, p. 101): for every `x ∈ ℝ` and unlimited `N ∈ ℕ*`,
`x ^ N / N!` is infinitesimal. -/
theorem isInfinitesimal_starSeq_pow_div_factorial (x : ℝ) {N : ℕ*} (hN : IsUnlimitedNat N) :
    IsInfinitesimal (starSeq (fun n : ℕ ↦ x ^ n / (n.factorial : ℝ)) N) := by
  have htend : Tendsto (fun n : ℕ ↦ x ^ n / (n.factorial : ℝ)) atTop (𝓝 0) :=
    (Real.summable_pow_div_factorial x).tendsto_atTop_zero
  simpa [InfClose] using tendsto_atTop_iff_infClose_unlimited.1 htend N hN

/-- Four-cycle characterization of `deriv^[k] Real.cos` (Goldblatt §8.9, p. 101):
`cos^{(k)}` is always one of `cos`, `-sin`, `-cos`, or `sin`. -/
theorem iterDeriv_cos_four_cases (k : ℕ) :
    deriv^[k] Real.cos = Real.cos ∨
      deriv^[k] Real.cos = -Real.sin ∨
      deriv^[k] Real.cos = -Real.cos ∨
      deriv^[k] Real.cos = Real.sin := by
  induction k with
  | zero => exact Or.inl rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h1 | h2 | h3 | h4
      · right; left
        rw [h1]
        ext t
        exact (Real.hasDerivAt_cos t).deriv
      · right; right; left
        rw [h2]
        ext t
        exact (Real.hasDerivAt_sin t).neg.deriv
      · right; right; right
        rw [h3]
        ext t
        simp
      · left
        rw [h4]
        ext t
        exact (Real.hasDerivAt_sin t).deriv

/-- **Goldblatt §8.9 (Maclaurin Remainder of `cos x`, p. 101)**:
For every `x ∈ ℝ` and unlimited `N ∈ ℕ*`, the Maclaurin remainder `R_N(x)` of `cos` is
infinitesimal (since `|cos^{(N+1)}(c)| ≤ 1` is limited and `x^{N+1} / (N+1)!` is infinitesimal). -/
theorem isInfinitesimal_maclaurinRemainder_cos (x : ℝ) {N : ℕ*} (hN : IsUnlimitedNat N) :
    IsInfinitesimal (starSeq (fun n ↦ taylorRemainder Real.cos 0 n x) N) := by
  have hdiff_cos : ∀ k : ℕ, ∀ t ∈ Set.Ioo (-(|x| + 1)) (|x| + 1),
      DifferentiableAt ℝ (deriv^[k] Real.cos) t := by
    intro k t _
    rcases iterDeriv_cos_four_cases k with h | h | h | h <;> rw [h]
    · exact Real.differentiableAt_cos
    · exact Real.differentiableAt_sin.neg
    · exact Real.differentiableAt_cos.neg
    · exact Real.differentiableAt_sin
  have h0 : (0 : ℝ) ∈ Set.Ioo (-(|x| + 1)) (|x| + 1) :=
    ⟨by linarith [abs_nonneg x], by linarith [abs_nonneg x]⟩
  have hx_mem : (x : ℝ*) ∈ starSet (Set.Ioo (-(|x| + 1)) (|x| + 1)) :=
    coe_mem_starSet.2 ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  obtain ⟨c, _, _, hrem_eq⟩ := hyperreal_taylorRemainder_lagrange h0 hdiff_cos N hx_mem
  have hlhs : starFun Real.cos (x : ℝ*) - starTaylorPoly Real.cos 0 N (x : ℝ*) =
      starSeq (fun n ↦ taylorRemainder Real.cos 0 n x) N :=
    Germ.inductionOn N fun _ ↦ rfl
  rw [hlhs] at hrem_eq
  have hcos_bdd : |starIterDeriv Real.cos (N + 1) c| ≤ 1 := by
    induction N using Germ.inductionOn with | _ m =>
    rcases ofSeq_surjective c with ⟨s, rfl⟩
    refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun i ↦ ?_)
    change |deriv^[m i + 1] Real.cos (s i)| ≤ 1
    rcases iterDeriv_cos_four_cases (m i + 1) with h | h | h | h <;> rw [h]
    · exact Real.abs_cos_le_one (s i)
    · simpa using Real.abs_sin_le_one (s i)
    · simpa using Real.abs_cos_le_one (s i)
    · exact Real.abs_sin_le_one (s i)
  have hcos_lim : IsLimited (starIterDeriv Real.cos (N + 1) c) :=
    isLimited_iff_abs_le_real.2 ⟨1, zero_le_one, by simpa using hcos_bdd⟩
  have hN1_unl : IsUnlimitedNat (N + 1) := by
    intro n
    have hlt := hN n
    induction N using Germ.inductionOn with | _ m =>
    refine Germ.coe_lt.2 ((Germ.coe_lt.1 hlt).mono fun i hi ↦ ?_)
    have hi' : n < m i := hi
    change n < m i + 1
    omega
  have hpow_fac_eq : starRealPow (((x - 0 : ℝ) : ℝ*)) (N + 1) /
      Hypernat.toHyperreal (hyperFactorial (N + 1)) =
      starSeq (fun n : ℕ ↦ x ^ n / (n.factorial : ℝ)) (N + 1) := by
    induction N using Germ.inductionOn with | _ m =>
    exact Germ.coe_eq.2 (Eventually.of_forall fun i ↦ by simp)
  have hpow_inf : IsInfinitesimal (starRealPow (((x - 0 : ℝ) : ℝ*)) (N + 1) /
      Hypernat.toHyperreal (hyperFactorial (N + 1))) := by
    rw [hpow_fac_eq]
    exact isInfinitesimal_starSeq_pow_div_factorial x hN1_unl
  have hrhs_eq : (starIterDeriv Real.cos (N + 1) c /
      Hypernat.toHyperreal (hyperFactorial (N + 1))) *
      starRealPow (((x - 0 : ℝ) : ℝ*)) (N + 1) =
      starIterDeriv Real.cos (N + 1) c *
        (starRealPow (((x - 0 : ℝ) : ℝ*)) (N + 1) /
          Hypernat.toHyperreal (hyperFactorial (N + 1))) := by
    ring
  rw [← Hyperreal.coe_sub] at hrem_eq
  rw [hrem_eq, hrhs_eq]
  exact hcos_lim.mul_isInfinitesimal hpow_inf

/-- **Goldblatt §8.9 (p. 101)**: The Maclaurin series of `cos` converges to `cos x` for all
`x ∈ ℝ`. -/
theorem tendsto_maclaurin_cos (x : ℝ) :
    Tendsto (fun n ↦ taylorPoly Real.cos 0 n x) atTop (𝓝 (Real.cos x)) :=
  tendsto_taylorPoly_self_iff_isInfinitesimal_remainder.2
    fun _ hN ↦ isInfinitesimal_maclaurinRemainder_cos x hN

/-- Every iterated derivative of `Real.exp` is `Real.exp`. -/
theorem iterDeriv_exp (k : ℕ) : deriv^[k] Real.exp = Real.exp := by
  induction k with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, Real.deriv_exp]

/-- **Goldblatt Exercise 8.9.1 (p. 102)**: For every `x ∈ ℝ` and unlimited `N ∈ ℕ*`, the Maclaurin
remainder `R_N(x)` of `e^x` is infinitesimal. -/
theorem isInfinitesimal_maclaurinRemainder_exp (x : ℝ) {N : ℕ*} (hN : IsUnlimitedNat N) :
    IsInfinitesimal (starSeq (fun n ↦ taylorRemainder Real.exp 0 n x) N) := by
  have hdiff_exp : ∀ k : ℕ, ∀ t ∈ Set.Ioo (-(|x| + 1)) (|x| + 1),
      DifferentiableAt ℝ (deriv^[k] Real.exp) t := by
    intro k t _
    rw [iterDeriv_exp]
    exact Real.differentiableAt_exp
  have h0 : (0 : ℝ) ∈ Set.Ioo (-(|x| + 1)) (|x| + 1) :=
    ⟨by linarith [abs_nonneg x], by linarith [abs_nonneg x]⟩
  have hx_mem : (x : ℝ*) ∈ starSet (Set.Ioo (-(|x| + 1)) (|x| + 1)) :=
    coe_mem_starSet.2 ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  obtain ⟨c, _, hc_hi, hrem_eq⟩ := hyperreal_taylorRemainder_lagrange h0 hdiff_exp N hx_mem
  have hlhs : starFun Real.exp (x : ℝ*) - starTaylorPoly Real.exp 0 N (x : ℝ*) =
      starSeq (fun n ↦ taylorRemainder Real.exp 0 n x) N :=
    Germ.inductionOn N fun _ ↦ rfl
  rw [hlhs] at hrem_eq
  have hc_le_abs : c ≤ (|x| : ℝ*) := by
    have hmax_le : max ((0 : ℝ) : ℝ*) (x : ℝ*) ≤ (|x| : ℝ*) := by
      have : max (0 : ℝ) x ≤ |x| := max_le (abs_nonneg x) (le_abs_self x)
      exact_mod_cast this
    exact hc_hi.trans hmax_le
  have hexp_lim : IsLimited (starIterDeriv Real.exp (N + 1) c) := by
    refine isLimited_iff_abs_le_real.2 ⟨Real.exp |x|, (Real.exp_pos |x|).le, ?_⟩
    induction N using Germ.inductionOn with | _ m =>
    rcases ofSeq_surjective c with ⟨s, rfl⟩
    have hs_le : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), s i ≤ |x| := ofSeq_le_ofSeq.1 hc_le_abs
    refine ofSeq_le_ofSeq.2 (hs_le.mono fun i hi ↦ ?_)
    change |deriv^[m i + 1] Real.exp (s i)| ≤ Real.exp |x|
    rw [iterDeriv_exp, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 hi
  have hN1_unl : IsUnlimitedNat (N + 1) := by
    intro n
    have hlt := hN n
    induction N using Germ.inductionOn with | _ m =>
    refine Germ.coe_lt.2 ((Germ.coe_lt.1 hlt).mono fun i hi ↦ ?_)
    have hi' : n < m i := hi
    change n < m i + 1
    omega
  have hpow_fac_eq : starRealPow (((x - 0 : ℝ) : ℝ*)) (N + 1) /
      Hypernat.toHyperreal (hyperFactorial (N + 1)) =
      starSeq (fun n : ℕ ↦ x ^ n / (n.factorial : ℝ)) (N + 1) := by
    induction N using Germ.inductionOn with | _ m =>
    exact Germ.coe_eq.2 (Eventually.of_forall fun i ↦ by simp)
  have hpow_inf : IsInfinitesimal (starRealPow (((x - 0 : ℝ) : ℝ*)) (N + 1) /
      Hypernat.toHyperreal (hyperFactorial (N + 1))) := by
    rw [hpow_fac_eq]
    exact isInfinitesimal_starSeq_pow_div_factorial x hN1_unl
  have hrhs_eq : (starIterDeriv Real.exp (N + 1) c /
      Hypernat.toHyperreal (hyperFactorial (N + 1))) *
      starRealPow (((x - 0 : ℝ) : ℝ*)) (N + 1) =
      starIterDeriv Real.exp (N + 1) c *
        (starRealPow (((x - 0 : ℝ) : ℝ*)) (N + 1) /
          Hypernat.toHyperreal (hyperFactorial (N + 1))) := by
    ring
  rw [← Hyperreal.coe_sub] at hrem_eq
  rw [hrem_eq, hrhs_eq]
  exact hexp_lim.mul_isInfinitesimal hpow_inf

/-- **Goldblatt Exercise 8.9.1 (p. 102)**: The Maclaurin series of `e^x` converges to `e^x` at
every `x ∈ ℝ`. -/
theorem tendsto_maclaurin_exp (x : ℝ) :
    Tendsto (fun n ↦ taylorPoly Real.exp 0 n x) atTop (𝓝 (Real.exp x)) :=
  tendsto_taylorPoly_self_iff_isInfinitesimal_remainder.2
    fun _ hN ↦ isInfinitesimal_maclaurinRemainder_exp x hN

/-! ## §8.10 Incremental Approximation by Taylor's Formula (pp. 102–103) -/

/-- **Goldblatt Theorem 8.10.1 (pp. 102–103)**:
If `f^{(n)}` exists on an open interval `(u, v)` containing `x ∈ ℝ` (`n ≥ 1`) and `f^{(n)}` is
continuous at `x`, then for every infinitesimal `Δx ∈ ℝ*`, there exists an infinitesimal `η ∈ ℝ*`
such that
`*f(x + Δx) = ∑_{k=0}^n (f^{(k)}(x) / k!) Δx^k + η Δx^n`. -/
theorem taylor_incremental_of_cont_iterDeriv {f : ℝ → ℝ} {u v x : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hx : x ∈ Set.Ioo u v)
    (hdiff : ∀ k < n, ∀ t ∈ Set.Ioo u v, DifferentiableAt ℝ (deriv^[k] f) t)
    (hcont : ContinuousAt (deriv^[n] f) x) :
    ∀ Δx : ℝ*, IsInfinitesimal Δx →
      ∃ η : ℝ*, IsInfinitesimal η ∧
        starFun f ((x : ℝ*) + Δx) =
          (∑ k ∈ Finset.range (n + 1),
            ((deriv^[k] f x / (k.factorial : ℝ) : ℝ) : ℝ*) * Δx ^ k) + η * Δx ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  intro Δx hΔx
  set δ : ℝ := min (x - u) (v - x)
  have hδ : 0 < δ := lt_min (sub_pos.2 hx.1) (sub_pos.2 hx.2)
  have hlt : |Δx| < (δ : ℝ*) := hΔx δ hδ
  rcases ofSeq_surjective Δx with ⟨r, rfl⟩
  have hr_mem : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), x + r i ∈ Set.Ioo u v := by
    refine (ofSeq_lt_ofSeq.1 hlt).mono fun i hi ↦ ?_
    rcases abs_lt.1 hi with ⟨hlo, hhi⟩
    exact ⟨by linarith [min_le_left (x - u) (v - x)], by linarith [min_le_right (x - u) (v - x)]⟩
  have hdiff' : ∀ k ≤ m, ∀ t ∈ Set.Ioo u v, DifferentiableAt ℝ (deriv^[k] f) t :=
    fun k hk ↦ hdiff k (Nat.lt_succ_of_le hk)
  let cSeq : ℕ → ℝ := fun i ↦
    if h : x + r i ∈ Set.Ioo u v then
      (taylorRemainder_lagrange m hx h hdiff').choose
    else x
  let c : ℝ* := ofSeq cSeq
  have hc_mem : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
      cSeq i ∈ Set.Icc (min x (x + r i)) (max x (x + r i)) := by
    refine hr_mem.mono fun i hi ↦ ?_
    simp only [cSeq, hi, ↓reduceDIte]
    exact (taylorRemainder_lagrange m hx hi hdiff').choose_spec.1
  have hc_bound : |c - (x : ℝ*)| ≤ |ofSeq r| := by
    refine ofSeq_le_ofSeq.2 (hc_mem.mono fun i hcc ↦ ?_)
    change |cSeq i - x| ≤ |r i|
    rw [abs_le]
    rcases le_total 0 (r i) with hnn | hnp
    · rw [abs_of_nonneg hnn]
      rw [min_eq_left (by linarith), max_eq_right (by linarith)] at hcc
      exact ⟨by linarith [hcc.1], by linarith [hcc.2]⟩
    · rw [abs_of_nonpos hnp]
      rw [min_eq_right (by linarith), max_eq_left (by linarith)] at hcc
      exact ⟨by linarith [hcc.1], by linarith [hcc.2]⟩
  have hc_inf : IsInfinitesimal (c - (x : ℝ*)) := isInfinitesimal_of_abs_le hΔx hc_bound
  have hfn_close : starFun (deriv^[m + 1] f) c ≈ₕ ((deriv^[m + 1] f x : ℝ) : ℝ*) := by
    have hceq : c = (x : ℝ*) + (c - (x : ℝ*)) := by ring
    rw [hceq]
    exact continuousAt_iff_infClose_starFun.1 hcont (c - (x : ℝ*)) hc_inf
  set η : ℝ* := (starFun (deriv^[m + 1] f) c - ((deriv^[m + 1] f x : ℝ) : ℝ*)) /
    (((m + 1).factorial : ℝ) : ℝ*)
  have hη : IsInfinitesimal η := by
    unfold η
    rw [div_eq_mul_inv]
    exact hfn_close.mul_isLimited (isLimited_coe (((m + 1).factorial : ℝ))⁻¹)
  refine ⟨η, hη, ?_⟩
  have hpoly_star :
      ofSeq (fun i ↦ taylorPoly f x m (x + r i)) =
        ∑ k ∈ Finset.range (m + 1),
          ((deriv^[k] f x / (k.factorial : ℝ) : ℝ) : ℝ*) * (ofSeq r) ^ k := by
    have hsum_ofSeq : ∀ (K : ℕ) (g : ℕ → ℕ → ℝ),
        ofSeq (fun i ↦ ∑ k ∈ Finset.range K, g k i) =
          ∑ k ∈ Finset.range K, ofSeq (g k) := by
      intro K g
      induction K with
      | zero => exact Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ Finset.sum_range_zero _)
      | succ K ih =>
          rw [Finset.sum_range_succ, ← ih]
          exact Germ.coe_eq.2 (Eventually.of_forall fun i ↦ Finset.sum_range_succ _ K)
    unfold taylorPoly
    have h1 := hsum_ofSeq (m + 1)
      (fun k i ↦ (deriv^[k] f x / (k.factorial : ℝ)) * ((x + r i) - x) ^ k)
    rw [h1]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    exact Germ.coe_eq.2 (Eventually.of_forall fun i ↦ by simp)
  have hlag_star :
      starFun f ((x : ℝ*) + ofSeq r) - ofSeq (fun i ↦ taylorPoly f x m (x + r i)) =
        (starFun (deriv^[m + 1] f) c / (((m + 1).factorial : ℝ) : ℝ*)) * (ofSeq r) ^ (m + 1) := by
    refine Germ.coe_eq.2 (hr_mem.mono fun i hi ↦ ?_)
    change f (x + r i) - taylorPoly f x m (x + r i) =
      (deriv^[m + 1] f (cSeq i) / ((m + 1).factorial : ℝ)) * (r i) ^ (m + 1)
    simp only [cSeq, hi, ↓reduceDIte]
    have hspec := (taylorRemainder_lagrange m hx hi hdiff').choose_spec.2
    simpa [taylorRemainder] using hspec
  rw [Finset.sum_range_succ, ← hpoly_star]
  have hcoef_split :
      ((deriv^[m + 1] f x / ((m + 1).factorial : ℝ) : ℝ) : ℝ*) + η =
        starFun (deriv^[m + 1] f) c / (((m + 1).factorial : ℝ) : ℝ*) := by
    unfold η
    rw [Hyperreal.coe_div]
    ring
  linear_combination hlag_star - hcoef_split * (ofSeq r) ^ (m + 1)

/-- **Goldblatt Exercise 8.10.2 (Secant Form of Taylor Remainder, p. 103)**:
For `n ≥ 1` and `x ≠ a` in `(u, v)`, if ONLY `f', ..., f^{(n)}` exist on `(u, v)` (no `(n+1)`-th
derivative required!), there exists `c` strictly between `a` and `x` (`c ≠ a`) such that
`R_n(x) = ((f^{(n)}(c) - f^{(n)}(a)) / ((c - a) * (n + 1)!)) * (x - a)^{n+1}`. -/
theorem taylorRemainder_secant_form {f : ℝ → ℝ} {u v a x : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (ha : a ∈ Set.Ioo u v) (hx : x ∈ Set.Ioo u v) (hxa : x ≠ a)
    (hdiff : ∀ k < n, ∀ t ∈ Set.Ioo u v, DifferentiableAt ℝ (deriv^[k] f) t) :
    ∃ c ∈ Set.Ioo (min a x) (max a x),
      taylorRemainder f a n x =
        ((deriv^[n] f c - deriv^[n] f a) / ((c - a) * ((n + 1).factorial : ℝ))) *
          (x - a) ^ (n + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  induction m generalizing f x with
  | zero =>
      have hIcc_sub : Set.Icc (min a x) (max a x) ⊆ Set.Ioo u v := fun t ht ↦
        ⟨(lt_min ha.1 hx.1).trans_le ht.1, ht.2.trans_lt (max_lt ha.2 hx.2)⟩
      have hrem_cont : ContinuousOn (taylorRemainder f a 1) (Set.Icc (min a x) (max a x)) := by
        intro t ht
        exact (hasDerivAt_iff_hasNSCDerivAt.2
          (hasNSCDerivAt_taylorRemainder_succ 0
            (hdiff 0 (by omega) t (hIcc_sub ht)))).continuousAt.continuousWithinAt
      have hrem_deriv : ∀ t ∈ Set.Ioo (min a x) (max a x),
          HasNSCDerivAt (taylorRemainder f a 1) (taylorRemainder (deriv f) a 0 t) t :=
        fun t ht ↦ hasNSCDerivAt_taylorRemainder_succ 0
          (hdiff 0 (by omega) t (hIcc_sub (Set.Ioo_subset_Icc_self ht)))
      obtain ⟨c, hc, hceq⟩ := exists_cauchy_step_between (by omega : 1 ≤ 2) hxa
        hrem_cont hrem_deriv (taylorRemainder_self f a 1)
      have hc_ne : c - a ≠ 0 := by
        rcases lt_or_gt_of_ne hxa with hlt | hgt
        · rw [max_eq_left hlt.le] at hc
          exact sub_ne_zero.2 hc.2.ne
        · rw [min_eq_left hgt.le] at hc
          exact sub_ne_zero.2 hc.1.ne'
      refine ⟨c, hc, ?_⟩
      simp only [zero_add, taylorRemainder, taylorPoly_zero, Function.iterate_one] at hceq ⊢
      have hfac2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num
      rw [hfac2]
      have h2ne : (c - a) * 2 ≠ 0 := mul_ne_zero hc_ne two_ne_zero
      field_simp [h2ne]
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at hceq
      change (f x - taylorPoly f a 1 x) * (c - a) * 2 = (deriv f c - deriv f a) * (x - a) ^ 2
      linarith
  | succ m ih =>
      have hIcc_sub : Set.Icc (min a x) (max a x) ⊆ Set.Ioo u v := fun t ht ↦
        ⟨(lt_min ha.1 hx.1).trans_le ht.1, ht.2.trans_lt (max_lt ha.2 hx.2)⟩
      have hrem_cont :
          ContinuousOn (taylorRemainder f a (m + 2)) (Set.Icc (min a x) (max a x)) := by
        intro t ht
        exact (hasDerivAt_iff_hasNSCDerivAt.2
          (hasNSCDerivAt_taylorRemainder_succ (m + 1)
            (hdiff 0 (by omega) t (hIcc_sub ht)))).continuousAt.continuousWithinAt
      have hrem_deriv : ∀ t ∈ Set.Ioo (min a x) (max a x),
          HasNSCDerivAt (taylorRemainder f a (m + 2)) (taylorRemainder (deriv f) a (m + 1) t) t :=
        fun t ht ↦ hasNSCDerivAt_taylorRemainder_succ (m + 1)
          (hdiff 0 (by omega) t (hIcc_sub (Set.Ioo_subset_Icc_self ht)))
      obtain ⟨c₁, hc₁, hc₁_eq⟩ := exists_cauchy_step_between (by omega : 1 ≤ m + 3) hxa
        hrem_cont hrem_deriv (taylorRemainder_self f a (m + 2))
      have hc₁_uv : c₁ ∈ Set.Ioo u v := hIcc_sub (Set.Ioo_subset_Icc_self hc₁)
      have hc₁_ne : c₁ ≠ a := by
        rcases lt_or_gt_of_ne hxa with hlt | hgt
        · rw [max_eq_left hlt.le] at hc₁
          exact hc₁.2.ne
        · rw [min_eq_left hgt.le] at hc₁
          exact hc₁.1.ne'
      have hdiff' : ∀ k < m + 1, ∀ t ∈ Set.Ioo u v, DifferentiableAt ℝ (deriv^[k] (deriv f)) t := by
        intro k hk t ht
        rw [← Function.iterate_succ_apply]
        exact hdiff (k + 1) (Nat.succ_lt_succ hk) t ht
      obtain ⟨c, hc, hc_eq⟩ := ih hc₁_uv hc₁_ne (by omega) hdiff'
      have hc_in : c ∈ Set.Ioo (min a x) (max a x) := by
        rcases lt_or_gt_of_ne hxa with hlt | hgt
        · have hc₁_lt : c₁ < a := by simpa [max_eq_left hlt.le] using hc₁.2
          have hx_lt_c₁ : x < c₁ := by simpa [min_eq_right hlt.le] using hc₁.1
          rw [min_eq_right hc₁_lt.le, max_eq_left hc₁_lt.le] at hc
          rw [min_eq_right hlt.le, max_eq_left hlt.le]
          exact ⟨hx_lt_c₁.trans hc.1, hc.2⟩
        · have ha_lt_c₁ : a < c₁ := by simpa [min_eq_left hgt.le] using hc₁.1
          have hc₁_lt_x : c₁ < x := by simpa [max_eq_right hgt.le] using hc₁.2
          rw [min_eq_left ha_lt_c₁.le, max_eq_right ha_lt_c₁.le] at hc
          rw [min_eq_left hgt.le, max_eq_right hgt.le]
          exact ⟨hc.1, hc.2.trans hc₁_lt_x⟩
      have hc_ne : c - a ≠ 0 := by
        rcases lt_or_gt_of_ne hxa with hlt | hgt
        · rw [max_eq_left hlt.le] at hc_in
          exact sub_ne_zero.2 hc_in.2.ne
        · rw [min_eq_left hgt.le] at hc_in
          exact sub_ne_zero.2 hc_in.1.ne'
      refine ⟨c, hc_in, ?_⟩
      rw [hc_eq, ← Function.iterate_succ_apply] at hc₁_eq
      have hc₁_pow_ne : (c₁ - a) ^ (m + 2) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hc₁_ne)
      have hm3_ne : ((m + 3 : ℕ) : ℝ) ≠ 0 := by positivity
      have hfac2_ne : ((m + 2).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have hfac_succ : ((m + 3).factorial : ℝ) = ((m + 3 : ℕ) : ℝ) * ((m + 2).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_succ (m + 2)
      have hcancel : taylorRemainder f a (m + 2) x * ((m + 3 : ℕ) : ℝ) =
          ((deriv^[m + 2] f c - deriv^[m + 2] f a) / ((c - a) * ((m + 2).factorial : ℝ))) *
            (x - a) ^ (m + 3) := by
        apply mul_right_cancel₀ hc₁_pow_ne
        calc taylorRemainder f a (m + 2) x * ((m + 3 : ℕ) : ℝ) * (c₁ - a) ^ (m + 2)
            = taylorRemainder f a (m + 2) x * (((m + 3 : ℕ) : ℝ) * (c₁ - a) ^ (m + 2)) := by ring
          _ = (x - a) ^ (m + 3) *
                (((deriv^[m + 2] f c - deriv^[m + 2] f a) / ((c - a) * ((m + 2).factorial : ℝ))) *
                  (c₁ - a) ^ (m + 2)) := hc₁_eq
          _ = ((deriv^[m + 2] f c - deriv^[m + 2] f a) / ((c - a) * ((m + 2).factorial : ℝ))) *
                (x - a) ^ (m + 3) * (c₁ - a) ^ (m + 2) := by ring
      rw [show m + 1 + 1 + 1 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega, hfac_succ]
      field_simp [hc_ne, hm3_ne, hfac2_ne] at hcancel ⊢
      linarith

/-- **Goldblatt Exercise 8.10.2 (Peano Taylor Formula without Continuity of `f^{(n)}`, p. 103)**:
Theorem 8.10.1 holds WITHOUT assuming continuity of `f^{(n)}` — in fact, `f^{(n)}` need ONLY exist
at the single point `x` (`HasNSCDerivAt (deriv^[n - 1] f) (deriv^[n] f x) x`), provided
`f, f', ..., f^{(n-1)}` exist on `(u, v)`! -/
theorem taylor_incremental_peano {f : ℝ → ℝ} {u v x : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hx : x ∈ Set.Ioo u v)
    (hdiff_prev : ∀ k, k + 1 < n → ∀ t ∈ Set.Ioo u v, DifferentiableAt ℝ (deriv^[k] f) t)
    (hderiv_at_x : HasNSCDerivAt (deriv^[n - 1] f) (deriv^[n] f x) x) :
    ∀ Δx : ℝ*, IsInfinitesimal Δx →
      ∃ η : ℝ*, IsInfinitesimal η ∧
        starFun f ((x : ℝ*) + Δx) =
          (∑ k ∈ Finset.range (n + 1),
            ((deriv^[k] f x / (k.factorial : ℝ) : ℝ) : ℝ*) * Δx ^ k) + η * Δx ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  cases m with
  | zero =>
      intro Δx hΔx
      simp only [zero_add, tsub_self, Function.iterate_zero, Function.iterate_one] at hderiv_at_x ⊢
      obtain ⟨η, hη, heq⟩ := hderiv_at_x.exists_incremental_eq hΔx
      refine ⟨η, hη, ?_⟩
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp only [Function.iterate_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero,
        mul_one, Function.iterate_one, Nat.factorial_one, pow_one]
      exact heq
  | succ p =>
      intro Δx hΔx
      by_cases hΔ0 : Δx = 0
      · subst hΔ0
        refine ⟨0, isInfinitesimal_zero, ?_⟩
        rw [Finset.sum_range_succ']
        simp [zero_pow (by omega : p + 2 ≠ 0)]
      · set δ : ℝ := min (x - u) (v - x)
        have hδ : 0 < δ := lt_min (sub_pos.2 hx.1) (sub_pos.2 hx.2)
        have hlt : |Δx| < (δ : ℝ*) := hΔx δ hδ
        rcases ofSeq_surjective Δx with ⟨r, rfl⟩
        have hr_ne : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), r i ≠ 0 :=
          Ultrafilter.eventually_not.2 fun h0 ↦ hΔ0 (Germ.coe_eq.2 h0)
        have hr_mem : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), x + r i ∈ Set.Ioo u v := by
          refine (ofSeq_lt_ofSeq.1 hlt).mono fun i hi ↦ ?_
          rcases abs_lt.1 hi with ⟨hlo, hhi⟩
          exact ⟨by linarith [min_le_left (x - u) (v - x)],
                 by linarith [min_le_right (x - u) (v - x)]⟩
        have hdiff_p : ∀ k < p + 1, ∀ t ∈ Set.Ioo u v, DifferentiableAt ℝ (deriv^[k] f) t :=
          fun k hk ↦ hdiff_prev k (by omega)
        let cSeq : ℕ → ℝ := fun i ↦
          if h : x + r i ∈ Set.Ioo u v ∧ r i ≠ 0 then
            (taylorRemainder_secant_form (by omega : 1 ≤ p + 1) hx h.1
              (by intro heq; exact h.2 (by linarith)) hdiff_p).choose
          else x + 1
        let c : ℝ* := ofSeq cSeq
        have hc_strict : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
            cSeq i ∈ Set.Ioo (min x (x + r i)) (max x (x + r i)) := by
          refine (hr_mem.and hr_ne).mono fun i hi ↦ ?_
          dsimp only [cSeq]
          rw [dite_eq_left_of_eq_true (eq_true hi)]
          exact (taylorRemainder_secant_form (by omega : 1 ≤ p + 1) hx hi.1
            (by intro heq; exact hi.2 (by linarith)) hdiff_p).choose_spec.1
        have hc_bound : |c - (x : ℝ*)| ≤ |ofSeq r| := by
          refine ofSeq_le_ofSeq.2 (hc_strict.mono fun i hi ↦ ?_)
          change |cSeq i - x| ≤ |r i|
          rw [abs_le]
          rcases le_total 0 (r i) with hnn | hnp
          · rw [abs_of_nonneg hnn]
            rw [min_eq_left (by linarith), max_eq_right (by linarith)] at hi
            exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
          · rw [abs_of_nonpos hnp]
            rw [min_eq_right (by linarith), max_eq_left (by linarith)] at hi
            exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
        have hΔc_inf : IsInfinitesimal (c - (x : ℝ*)) := isInfinitesimal_of_abs_le hΔx hc_bound
        have hΔc_ne : c - (x : ℝ*) ≠ 0 := by
          intro h0
          have hev0 : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), cSeq i - x = 0 := Germ.coe_eq.1 h0
          obtain ⟨i, hi_in, hi_eq⟩ := (hc_strict.and hev0).exists
          have hci : cSeq i = x := sub_eq_zero.1 hi_eq
          rw [hci] at hi_in
          rcases le_or_gt x (x + r i) with hle | hgt
          · rw [min_eq_left hle] at hi_in
            exact lt_irrefl x hi_in.1
          · rw [max_eq_left hgt.le] at hi_in
            exact lt_irrefl x hi_in.2
        simp only [Nat.add_sub_cancel] at hderiv_at_x
        have hsec_close :
            (starFun (deriv^[p + 1] f) c - ((deriv^[p + 1] f x : ℝ) : ℝ*)) / (c - (x : ℝ*)) ≈ₕ
              ((deriv^[p + 2] f x : ℝ) : ℝ*) := by
          have hceq : c = (x : ℝ*) + (c - (x : ℝ*)) := by ring
          simpa [← hceq] using hderiv_at_x (c - (x : ℝ*)) hΔc_inf hΔc_ne
        set η : ℝ* :=
          ((starFun (deriv^[p + 1] f) c - ((deriv^[p + 1] f x : ℝ) : ℝ*)) / (c - (x : ℝ*)) -
            ((deriv^[p + 2] f x : ℝ) : ℝ*)) / (((p + 2).factorial : ℝ) : ℝ*)
        have hη : IsInfinitesimal η := by
          unfold η
          rw [div_eq_mul_inv]
          exact hsec_close.mul_isLimited (isLimited_coe (((p + 2).factorial : ℝ))⁻¹)
        refine ⟨η, hη, ?_⟩
        have hpoly_star :
            ofSeq (fun i ↦ taylorPoly f x (p + 1) (x + r i)) =
              ∑ k ∈ Finset.range (p + 2),
                ((deriv^[k] f x / (k.factorial : ℝ) : ℝ) : ℝ*) * (ofSeq r) ^ k := by
          have hsum_ofSeq : ∀ (K : ℕ) (g : ℕ → ℕ → ℝ),
              ofSeq (fun i ↦ ∑ k ∈ Finset.range K, g k i) =
                ∑ k ∈ Finset.range K, ofSeq (g k) := by
            intro K g
            induction K with
            | zero => exact Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ Finset.sum_range_zero _)
            | succ K ih =>
                rw [Finset.sum_range_succ, ← ih]
                exact Germ.coe_eq.2 (Eventually.of_forall fun i ↦ Finset.sum_range_succ _ K)
          unfold taylorPoly
          have h1 := hsum_ofSeq (p + 2)
            (fun k i ↦ (deriv^[k] f x / (k.factorial : ℝ)) * ((x + r i) - x) ^ k)
          rw [h1]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          exact Germ.coe_eq.2 (Eventually.of_forall fun i ↦ by simp)
        have hsec_star :
            starFun f ((x : ℝ*) + ofSeq r) - ofSeq (fun i ↦ taylorPoly f x (p + 1) (x + r i)) =
              (((starFun (deriv^[p + 1] f) c - ((deriv^[p + 1] f x : ℝ) : ℝ*)) / (c - (x : ℝ*))) /
                (((p + 2).factorial : ℝ) : ℝ*)) * (ofSeq r) ^ (p + 2) := by
          refine Germ.coe_eq.2 ((hr_mem.and hr_ne).mono fun i hi ↦ ?_)
          change f (x + r i) - taylorPoly f x (p + 1) (x + r i) =
            (((deriv^[p + 1] f (cSeq i) - deriv^[p + 1] f x) / (cSeq i - x)) /
              ((p + 2).factorial : ℝ)) * (r i) ^ (p + 2)
          dsimp only [cSeq]
          rw [dite_eq_left_of_eq_true (eq_true hi)]
          have hspec := (taylorRemainder_secant_form (by omega : 1 ≤ p + 1) hx hi.1
            (by intro heq; exact hi.2 (by linarith)) hdiff_p).choose_spec.2
          rw [div_div]
          simpa [taylorRemainder] using hspec
        rw [show p + 1 + 1 = p + 2 by omega, Finset.sum_range_succ, ← hpoly_star]
        have hcoef_split :
            ((deriv^[p + 2] f x / ((p + 2).factorial : ℝ) : ℝ) : ℝ*) + η =
              ((starFun (deriv^[p + 1] f) c - ((deriv^[p + 1] f x : ℝ) : ℝ*)) / (c - (x : ℝ*))) /
                (((p + 2).factorial : ℝ) : ℝ*) := by
          unfold η
          rw [Hyperreal.coe_div]
          ring
        linear_combination hsec_star - hcoef_split * (ofSeq r) ^ (p + 2)

/-- **Second Symmetric Difference Quotient Formula** deduced from the `n = 2` Peano Taylor
formula (`taylor_incremental_peano`):
if `f` is differentiable near `x` and `HasNSCDerivAt (deriv f) f'' x`, then for every nonzero
infinitesimal `Δx`,
`(*f(x + Δx) - 2 f(x) + *f(x - Δx)) / Δx² ≈ₕ f''`. -/
theorem second_symmetric_diff_quotient_infClose {f : ℝ → ℝ} {u v x f'' : ℝ}
    (hx : x ∈ Set.Ioo u v)
    (hdiff : ∀ t ∈ Set.Ioo u v, DifferentiableAt ℝ f t)
    (hderiv₂ : HasNSCDerivAt (deriv f) f'' x)
    {Δx : ℝ*} (hΔx : IsInfinitesimal Δx) (hne : Δx ≠ 0) :
    (starFun f ((x : ℝ*) + Δx) - 2 * (f x : ℝ*) + starFun f ((x : ℝ*) - Δx)) / Δx ^ 2 ≈ₕ
      (f'' : ℝ*) := by
  have hf''_eq : deriv^[2] f x = f'' := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
    exact hderiv₂.deriv_eq
  have hpeano := taylor_incremental_peano (n := 2) (by omega) hx
    (fun k hk t ht ↦ by
      have hk0 : k = 0 := by omega
      subst hk0
      exact hdiff t ht)
    (by simpa [Function.iterate_one, hf''_eq] using hderiv₂)
  obtain ⟨η₁, hη₁, heq₁⟩ := hpeano Δx hΔx
  obtain ⟨η₂, hη₂, heq₂⟩ := hpeano (-Δx) hΔx.neg
  have hsub_eq : (x : ℝ*) - Δx = (x : ℝ*) + (-Δx) := by ring
  rw [hsub_eq]
  have hsum_simp : ∀ δ : ℝ*,
      (∑ k ∈ Finset.range 3, ((deriv^[k] f x / (k.factorial : ℝ) : ℝ) : ℝ*) * δ ^ k) =
        (f x : ℝ*) + ((deriv f x : ℝ) : ℝ*) * δ + ((f'' / 2 : ℝ) : ℝ*) * δ ^ 2 := by
    intro δ
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have hfac2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num
    simp only [Function.iterate_zero, id_eq, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero,
      mul_one, Function.iterate_one, Nat.factorial_one, pow_one, hf''_eq, hfac2]
  rw [hsum_simp] at heq₁ heq₂
  have hnum :
      starFun f ((x : ℝ*) + Δx) - 2 * (f x : ℝ*) + starFun f ((x : ℝ*) + (-Δx)) =
        ((f'' : ℝ*) + η₁ + η₂) * Δx ^ 2 := by
    have hhalf_add : ((f'' / 2 : ℝ) : ℝ*) * Δx ^ 2 + ((f'' / 2 : ℝ) : ℝ*) * (-Δx) ^ 2 =
        (f'' : ℝ*) * Δx ^ 2 := by
      rw [neg_sq, ← add_mul, ← Hyperreal.coe_add, add_halves]
    rw [heq₁, heq₂]
    linear_combination hhalf_add
  have hsq_ne : Δx ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have hquot :
      (starFun f ((x : ℝ*) + Δx) - 2 * (f x : ℝ*) + starFun f ((x : ℝ*) + (-Δx))) / Δx ^ 2 -
        (f'' : ℝ*) = η₁ + η₂ := by
    rw [hnum, mul_div_cancel_right₀ _ hsq_ne]
    ring
  unfold InfClose
  rw [hquot]
  exact hη₁.add hη₂

/-- **Second-Derivative Strict Local Minimum Test** via Peano Taylor approximation:
if `f` is differentiable on `(u, v)` containing `x`, `deriv f x = 0`, and
`HasNSCDerivAt (deriv f) f'' x` with `0 < f''`, then `f` has a strict local minimum at `x`
(`∀ᶠ y in 𝓝[≠] x, f x < f y`, and in particular `IsLocalMin f x`). -/
theorem strictLocalMin_of_second_deriv_pos {f : ℝ → ℝ} {u v x f'' : ℝ}
    (hx : x ∈ Set.Ioo u v)
    (hdiff : ∀ t ∈ Set.Ioo u v, DifferentiableAt ℝ f t)
    (hcrit : deriv f x = 0)
    (hderiv₂ : HasNSCDerivAt (deriv f) f'' x) (hpos : 0 < f'') :
    (∀ᶠ y in 𝓝[≠] x, f x < f y) ∧ IsLocalMin f x := by
  have hf''_eq : deriv^[2] f x = f'' := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
    exact hderiv₂.deriv_eq
  have hpeano := taylor_incremental_peano (n := 2) (by omega) hx
    (fun k hk t ht ↦ by
      have hk0 : k = 0 := by omega
      subst hk0
      exact hdiff t ht)
    (by simpa [Function.iterate_one, hf''_eq] using hderiv₂)
  have hstar_gt : ∀ Δx : ℝ*, IsInfinitesimal Δx → Δx ≠ 0 →
      (f x : ℝ*) < starFun f ((x : ℝ*) + Δx) := by
    intro Δx hΔx hne
    obtain ⟨η, hη, heq⟩ := hpeano Δx hΔx
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at heq
    have hfac2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num
    simp only [Function.iterate_zero, id_eq, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero,
      mul_one, Function.iterate_one, Nat.factorial_one, pow_one, hcrit, Hyperreal.coe_zero,
      zero_mul, add_zero, hf''_eq, hfac2] at heq
    have hη_gt : -((f'' / 4 : ℝ) : ℝ*) < η := (abs_lt.1 (hη (f'' / 4) (by positivity))).1
    have hcoef_pos : 0 < ((f'' / 2 : ℝ) : ℝ*) + η := by
      have hquarter : (0 : ℝ*) < ((f'' / 4 : ℝ) : ℝ*) := Hyperreal.coe_pos.2 (by positivity)
      have hhalf : ((f'' / 2 : ℝ) : ℝ*) = ((f'' / 4 : ℝ) : ℝ*) + ((f'' / 4 : ℝ) : ℝ*) := by
        rw [← Hyperreal.coe_add]
        congr 1
        ring
      linarith
    have hsq_pos : 0 < Δx ^ 2 := sq_pos_of_ne_zero hne
    have hprod_pos : 0 < (((f'' / 2 : ℝ) : ℝ*) + η) * Δx ^ 2 := mul_pos hcoef_pos hsq_pos
    have hdiff_eq : starFun f ((x : ℝ*) + Δx) - (f x : ℝ*) =
        (((f'' / 2 : ℝ) : ℝ*) + η) * Δx ^ 2 := by linarith
    linarith
  have hpunct : ∀ᶠ y in 𝓝[≠] x, f x < f y := by
    by_contra hnot
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hnot
    push Not at hnot
    have hex : ∀ n : ℕ, ∃ y : ℝ, |y - x| < ((n : ℝ) + 1)⁻¹ ∧ y ≠ x ∧ f y ≤ f x := by
      intro n
      obtain ⟨y, hy_dist, hy_ne, hy_le⟩ := hnot (((n : ℝ) + 1)⁻¹) (by positivity)
      exact ⟨y, by simpa [Real.dist_eq] using hy_dist, hy_ne, hy_le⟩
    choose y hy using hex
    let Δx : ℝ* := ofSeq (fun n ↦ y n - x)
    have hΔx_inf : IsInfinitesimal Δx := by
      apply ofSeq_infinitesimal_of_tendsto_zero
      refine squeeze_zero_norm (fun n ↦ ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [Real.norm_eq_abs, one_div] using (hy n).1.le
    have hΔx_ne : Δx ≠ 0 := by
      intro h0
      obtain ⟨n, hn⟩ := (Germ.coe_eq.1 h0).exists
      exact (hy n).2.1 (sub_eq_zero.1 hn)
    have hgt := hstar_gt Δx hΔx_inf hΔx_ne
    have hxΔ : (x : ℝ*) + Δx = ofSeq y :=
      Germ.coe_eq.2 (Eventually.of_forall fun n ↦ add_sub_cancel x (y n))
    rw [hxΔ] at hgt
    have hle : starFun f (ofSeq y) ≤ (f x : ℝ*) :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (hy n).2.2)
    exact not_lt_of_ge hle hgt
  refine ⟨hpunct, ?_⟩
  rw [eventually_nhdsWithin_iff] at hpunct
  refine hpunct.mono fun y hy ↦ ?_
  by_cases hyx : y = x
  · subst hyx
    exact le_rfl
  · exact (hy hyx).le

/-- **Second-Derivative Strict Local Maximum Test** via Peano Taylor approximation (`f'' < 0`). -/
theorem strictLocalMax_of_second_deriv_neg {f : ℝ → ℝ} {u v x f'' : ℝ}
    (hx : x ∈ Set.Ioo u v)
    (hdiff : ∀ t ∈ Set.Ioo u v, DifferentiableAt ℝ f t)
    (hcrit : deriv f x = 0)
    (hderiv₂ : HasNSCDerivAt (deriv f) f'' x) (hneg : f'' < 0) :
    (∀ᶠ y in 𝓝[≠] x, f y < f x) ∧ IsLocalMax f x := by
  have hdiff_neg : ∀ t ∈ Set.Ioo u v, DifferentiableAt ℝ (-f) t := fun t ht ↦ (hdiff t ht).neg
  have hderiv_neg_eq : deriv (-f) = -deriv f := by
    ext t
    exact deriv.neg
  have hcrit_neg : deriv (-f) x = 0 := by simp [hderiv_neg_eq, hcrit]
  have hderiv₂_neg : HasNSCDerivAt (deriv (-f)) (-f'') x := by
    rw [hderiv_neg_eq]
    exact hderiv₂.neg
  obtain ⟨hpunct, hmin⟩ := strictLocalMin_of_second_deriv_pos hx hdiff_neg hcrit_neg
    hderiv₂_neg (neg_pos.2 hneg)
  exact ⟨hpunct.mono fun y hy ↦ neg_lt_neg_iff.1 hy,
         hmin.mono fun y hy ↦ neg_le_neg_iff.1 hy⟩

/-! ## §8.11–8.12 Extending the Incremental Equation and `x² sin(1/x)` (pp. 103–104) -/

/-- Goldblatt §8.11 (p. 103): A hyperreal `x ∈ ℝ*` is *well inside* `*(a, b)` if `a < x < b`
and `x` is not infinitely close to either endpoint `a` or `b`. -/
def IsWellInsideIoo (x : ℝ*) (a b : ℝ) : Prop :=
  (a : ℝ*) < x ∧ x < (b : ℝ*) ∧ ¬ (x ≈ₕ (a : ℝ*)) ∧ ¬ (x ≈ₕ (b : ℝ*))

/-- Goldblatt §8.11 (p. 103): `x` is well inside `*(a, b)` iff its entire halo lies in `*(a, b)`
(`a < x + Δx < b` for every infinitesimal `Δx`). -/
theorem isWellInsideIoo_iff_halo_subset {x : ℝ*} {a b : ℝ} :
    IsWellInsideIoo x a b ↔ ∀ Δx : ℝ*, IsInfinitesimal Δx → x + Δx ∈ starSet (Set.Ioo a b) := by
  simp only [starSet_Ioo, Set.mem_Ioo]
  constructor
  · rintro ⟨hax, hxb, hna, hnb⟩ Δx hΔx
    unfold InfClose IsInfinitesimal at hna hnb
    push Not at hna hnb
    obtain ⟨δ₁, hδ₁, hle₁⟩ := hna
    obtain ⟨δ₂, hδ₂, hle₂⟩ := hnb
    rw [abs_of_pos (sub_pos.2 hax)] at hle₁
    rw [abs_of_neg (sub_neg.2 hxb)] at hle₂
    have hlt₁ : |Δx| < ((δ₁ / 2 : ℝ) : ℝ*) := hΔx (δ₁ / 2) (half_pos hδ₁)
    have hlt₂ : |Δx| < ((δ₂ / 2 : ℝ) : ℝ*) := hΔx (δ₂ / 2) (half_pos hδ₂)
    have hhalf₁ : ((δ₁ / 2 : ℝ) : ℝ*) < (δ₁ : ℝ*) := Hyperreal.coe_lt_coe.2 (half_lt_self hδ₁)
    have hhalf₂ : ((δ₂ / 2 : ℝ) : ℝ*) < (δ₂ : ℝ*) := Hyperreal.coe_lt_coe.2 (half_lt_self hδ₂)
    rcases abs_lt.1 hlt₁ with ⟨hlo₁, _⟩
    rcases abs_lt.1 hlt₂ with ⟨_, hhi₂⟩
    exact ⟨by linarith, by linarith⟩
  · intro h
    have h0 := h 0 isInfinitesimal_zero
    rw [add_zero] at h0
    refine ⟨h0.1, h0.2, ?_, ?_⟩
    · intro hxa
      have hbad := h ((a : ℝ*) - x) hxa.symm
      linarith [hbad.1]
    · intro hxb
      have hbad := h ((b : ℝ*) - x) hxb.symm
      linarith [hbad.2]

/-- Goldblatt §8.12(1a) (p. 104): `x` is well inside `*(a, b)` iff `x` is limited and
`shadow x ∈ (a, b)`. -/
theorem isWellInsideIoo_iff_shadow_mem {x : ℝ*} {a b : ℝ} :
    IsWellInsideIoo x a b ↔ IsLimited x ∧ shadow x ∈ Set.Ioo a b := by
  constructor
  · rintro ⟨hax, hxb, hna, hnb⟩
    have hlim : IsLimited x := isLimited_iff_exists_real.2 ⟨a, b, hax, hxb⟩
    have hx_sh : x ≈ₕ (shadow x : ℝ*) := infClose_shadow hlim
    have ha_le : a ≤ shadow x := coe_le_of_infClose_le (InfClose.refl _) hax.le hx_sh
    have hb_ge : shadow x ≤ b := coe_le_of_infClose_le hx_sh.symm hxb.le (InfClose.refl _)
    have ha_ne : shadow x ≠ a := fun heq ↦ hna (heq ▸ hx_sh)
    have hb_ne : shadow x ≠ b := fun heq ↦ hnb (heq ▸ hx_sh)
    exact ⟨hlim, ⟨lt_of_le_of_ne ha_le ha_ne.symm, lt_of_le_of_ne hb_ge hb_ne⟩⟩
  · rintro ⟨hlim, hsh_mem⟩
    have hx_sh : x ≈ₕ (shadow x : ℝ*) := infClose_shadow hlim
    rw [isWellInsideIoo_iff_halo_subset]
    intro Δx hΔx
    rw [starSet_Ioo, Set.mem_Ioo]
    set s : ℝ := shadow x
    set δ : ℝ := min (s - a) (b - s)
    have hδ : 0 < δ := lt_min (sub_pos.2 hsh_mem.1) (sub_pos.2 hsh_mem.2)
    have hsum_inf : IsInfinitesimal ((x - (s : ℝ*)) + Δx) := IsInfinitesimal.add hx_sh hΔx
    have hlt : |(x - (s : ℝ*)) + Δx| < ((δ / 2 : ℝ) : ℝ*) := hsum_inf (δ / 2) (half_pos hδ)
    rcases abs_lt.1 hlt with ⟨hlo, hhi⟩
    have hδ1 : ((δ / 2 : ℝ) : ℝ*) < ((s - a : ℝ) : ℝ*) :=
      Hyperreal.coe_lt_coe.2 ((half_lt_self hδ).trans_le (min_le_left _ _))
    have hδ2 : ((δ / 2 : ℝ) : ℝ*) < ((b - s : ℝ) : ℝ*) :=
      Hyperreal.coe_lt_coe.2 ((half_lt_self hδ).trans_le (min_le_right _ _))
    rw [Hyperreal.coe_sub] at hδ1 hδ2
    exact ⟨by linarith, by linarith⟩

/-- **Goldblatt Exercise 8.12(1a) (p. 104)**:
If `f` has derivative `f'` on `(a, b)` and `f'` is continuous on `(a, b)`, then for every `x` well
inside `*(a, b)` and every nonzero infinitesimal `Δx`,
`(*f(x + Δx) - *f(x)) / Δx ≈ₕ *f'(x)`.
Proved by hyperreal transfer of the standard Mean Value Theorem (`mvt_nsc`), `shadow x ∈ (a, b)`,
and continuity of `f'`! -/
theorem newtonQuotient_infClose_starFun_deriv_of_wellInside {f f' : ℝ → ℝ} {a b : ℝ}
    (hderiv : ∀ t ∈ Set.Ioo a b, HasNSCDerivAt f (f' t) t)
    (hf'_cont : ContinuousOn f' (Set.Ioo a b))
    {x Δx : ℝ*} (hx : IsWellInsideIoo x a b) (hΔx : IsInfinitesimal Δx) (hne : Δx ≠ 0) :
    (starFun f (x + Δx) - starFun f x) / Δx ≈ₕ starFun f' x := by
  have hx_ab : x ∈ starSet (Set.Ioo a b) :=
    by simpa using isWellInsideIoo_iff_halo_subset.1 hx 0 isInfinitesimal_zero
  have hxΔ_ab : x + Δx ∈ starSet (Set.Ioo a b) := isWellInsideIoo_iff_halo_subset.1 hx Δx hΔx
  obtain ⟨hx_lim, hs_mem⟩ := isWellInsideIoo_iff_shadow_mem.1 hx
  set s : ℝ := shadow x
  have hx_s : x ≈ₕ (s : ℝ*) := infClose_shadow hx_lim
  -- Real MVT on `(a, b)` between `u₀` and `u₀ + d₀` when `d₀ ≠ 0`
  have hreal_mvt : ∀ u₀ d₀ : ℝ, u₀ ∈ Set.Ioo a b → u₀ + d₀ ∈ Set.Ioo a b → d₀ ≠ 0 →
      ∃ c₀ ∈ Set.Ioo a b, |c₀ - u₀| ≤ |d₀| ∧ (f (u₀ + d₀) - f u₀) / d₀ = f' c₀ := by
    intro u₀ d₀ hu₀ hu₀d hd₀
    rcases lt_or_gt_of_ne hd₀ with hneg | hpos
    · have hsub : Set.Icc (u₀ + d₀) u₀ ⊆ Set.Ioo a b := fun t ht ↦
        ⟨hu₀d.1.trans_le ht.1, ht.2.trans_lt hu₀.2⟩
      have hcont : ContinuousOn f (Set.Icc (u₀ + d₀) u₀) := fun t ht ↦
        (hderiv t (hsub ht)).continuousAt.continuousWithinAt
      obtain ⟨c₀, hc₀, hceq⟩ := mvt_nsc (add_lt_of_neg_right u₀ hneg) hcont
        (fun t ht ↦ hderiv t (hsub (Set.Ioo_subset_Icc_self ht)))
      refine ⟨c₀, hsub (Set.Ioo_subset_Icc_self hc₀), ?_, ?_⟩
      · rw [abs_of_neg (sub_neg.2 hc₀.2), abs_of_neg hneg]
        linarith [hc₀.1]
      · have hquot_eq : (f u₀ - f (u₀ + d₀)) / (u₀ - (u₀ + d₀)) =
            (f (u₀ + d₀) - f u₀) / d₀ := by
          field_simp [hd₀, show u₀ - (u₀ + d₀) ≠ 0 by linarith]
          ring
        rw [← hquot_eq, ← hceq]
    · have hsub : Set.Icc u₀ (u₀ + d₀) ⊆ Set.Ioo a b := fun t ht ↦
        ⟨hu₀.1.trans_le ht.1, ht.2.trans_lt hu₀d.2⟩
      have hcont : ContinuousOn f (Set.Icc u₀ (u₀ + d₀)) := fun t ht ↦
        (hderiv t (hsub ht)).continuousAt.continuousWithinAt
      obtain ⟨c₀, hc₀, hceq⟩ := mvt_nsc (lt_add_of_pos_right u₀ hpos) hcont
        (fun t ht ↦ hderiv t (hsub (Set.Ioo_subset_Icc_self ht)))
      refine ⟨c₀, hsub (Set.Ioo_subset_Icc_self hc₀), ?_, ?_⟩
      · rw [abs_of_pos (sub_pos.2 hc₀.1), abs_of_pos hpos]
        linarith [hc₀.2]
      · have hsub_eq : (u₀ + d₀) - u₀ = d₀ := by ring
        rw [hsub_eq] at hceq
        exact hceq.symm
  rcases ofSeq_surjective x with ⟨u, rfl⟩
  rcases ofSeq_surjective Δx with ⟨d, rfl⟩
  have hu_ab : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), u i ∈ Set.Ioo a b := ofSeq_mem_starSet.1 hx_ab
  have hud_ab : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), u i + d i ∈ Set.Ioo a b :=
    ofSeq_mem_starSet.1 hxΔ_ab
  have hd_ne : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), d i ≠ 0 :=
    Ultrafilter.eventually_not.2 fun h0 ↦ hne (Germ.coe_eq.2 h0)
  let cSeq : ℕ → ℝ := fun i ↦
    if h : (u i ∈ Set.Ioo a b ∧ u i + d i ∈ Set.Ioo a b) ∧ d i ≠ 0 then
      (hreal_mvt (u i) (d i) h.1.1 h.1.2 h.2).choose
    else s
  let c : ℝ* := ofSeq cSeq
  have hc_ab : c ∈ starSet (Set.Ioo a b) := by
    refine ofSeq_mem_starSet.2 (((hu_ab.and hud_ab).and hd_ne).mono fun i hi ↦ ?_)
    dsimp only [cSeq]
    rw [dite_eq_left_of_eq_true (eq_true hi)]
    exact (hreal_mvt (u i) (d i) hi.1.1 hi.1.2 hi.2).choose_spec.1
  have hc_x : c ≈ₕ ofSeq u := by
    refine isInfinitesimal_of_abs_le hΔx ?_
    refine ofSeq_le_ofSeq.2 (((hu_ab.and hud_ab).and hd_ne).mono fun i hi ↦ ?_)
    change |cSeq i - u i| ≤ |d i|
    dsimp only [cSeq]
    rw [dite_eq_left_of_eq_true (eq_true hi)]
    exact (hreal_mvt (u i) (d i) hi.1.1 hi.1.2 hi.2).choose_spec.2.1
  have hquot_eq : (starFun f (ofSeq u + ofSeq d) - starFun f (ofSeq u)) / ofSeq d =
      starFun f' c := by
    refine Germ.coe_eq.2 (((hu_ab.and hud_ab).and hd_ne).mono fun i hi ↦ ?_)
    change (f (u i + d i) - f (u i)) / d i = f' (cSeq i)
    dsimp only [cSeq]
    rw [dite_eq_left_of_eq_true (eq_true hi)]
    exact (hreal_mvt (u i) (d i) hi.1.1 hi.1.2 hi.2).choose_spec.2.2
  rw [hquot_eq]
  have hc_s : c ≈ₕ (s : ℝ*) := hc_x.trans hx_s
  have hfc_s : starFun f' c ≈ₕ (f' s : ℝ*) :=
    continuousOn_infClose_starFun hf'_cont hs_mem hc_ab hc_s
  have hfx_s : starFun f' (ofSeq u) ≈ₕ (f' s : ℝ*) :=
    continuousOn_infClose_starFun hf'_cont hs_mem hx_ab hx_s
  exact hfc_s.trans hfx_s.symm

/-- **Goldblatt Exercise 8.12(1b) (p. 104)**:
If `f` has continuous derivative `f'` on `(a, b)`, then for every `x` well inside `*(a, b)` and
every infinitesimal `Δx`, `*f(x + Δx) = *f(x) + *f'(x) Δx + η Δx` for some infinitesimal `η`. -/
theorem incremental_eq_of_wellInside {f f' : ℝ → ℝ} {a b : ℝ}
    (hderiv : ∀ t ∈ Set.Ioo a b, HasNSCDerivAt f (f' t) t)
    (hf'_cont : ContinuousOn f' (Set.Ioo a b))
    {x Δx : ℝ*} (hx : IsWellInsideIoo x a b) (hΔx : IsInfinitesimal Δx) :
    ∃ η : ℝ*, IsInfinitesimal η ∧
      starFun f (x + Δx) = starFun f x + starFun f' x * Δx + η * Δx := by
  by_cases hne : Δx = 0
  · subst hne
    exact ⟨0, isInfinitesimal_zero, by simp⟩
  · have hclose := newtonQuotient_infClose_starFun_deriv_of_wellInside hderiv hf'_cont hx hΔx hne
    refine ⟨(starFun f (x + Δx) - starFun f x) / Δx - starFun f' x, hclose, ?_⟩
    have hmul : ((starFun f (x + Δx) - starFun f x) / Δx) * Δx =
        starFun f (x + Δx) - starFun f x := div_mul_cancel₀ _ hne
    linarith

/-- **Goldblatt Theorem 8.11.1 (Extending the Incremental Equation, pp. 103–104)**:
Let `f` have derivative `f'` on `(a, b)`. Then `f'` is continuous on `(a, b)` if and only if for
every hyperreal `x` well inside `*(a, b)` and every infinitesimal `Δx`,
`*f(x + Δx) = *f(x) + *f'(x) Δx + η Δx` for some infinitesimal `η`. -/
theorem continuousOn_deriv_iff_wellInside_incremental_eq {f f' : ℝ → ℝ} {a b : ℝ}
    (hderiv : ∀ t ∈ Set.Ioo a b, HasNSCDerivAt f (f' t) t) :
    ContinuousOn f' (Set.Ioo a b) ↔
      ∀ x : ℝ*, IsWellInsideIoo x a b → ∀ Δx : ℝ*, IsInfinitesimal Δx →
        ∃ η : ℝ*, IsInfinitesimal η ∧
          starFun f (x + Δx) = starFun f x + starFun f' x * Δx + η * Δx := by
  constructor
  · intro hf'_cont x hx Δx hΔx
    exact incremental_eq_of_wellInside hderiv hf'_cont hx hΔx
  · intro hinc c hc
    -- Prove `ContinuousAt f' c` (which implies `ContinuousWithinAt f' (Set.Ioo a b) c`)
    refine ContinuousAt.continuousWithinAt ?_
    rw [continuousAt_iff_infClose_starFun]
    intro Δ hΔ
    by_cases hΔ0 : Δ = 0
    · subst hΔ0
      simp [InfClose.refl]
    · set x : ℝ* := (c : ℝ*) + Δ
      have hx_well : IsWellInsideIoo x a b := by
        rw [isWellInsideIoo_iff_shadow_mem]
        have hx_close : x ≈ₕ (c : ℝ*) := by unfold x InfClose; simpa using hΔ
        have hx_lim : IsLimited x := (isLimited_coe c).add hΔ.isLimited
        rw [shadow_eq_of_infClose hx_close]
        exact ⟨hx_lim, hc⟩
      obtain ⟨ε, hε, heq_c⟩ := (hderiv c hc).exists_incremental_eq hΔ
      obtain ⟨ε', hε', heq_x⟩ := hinc x hx_well (-Δ) hΔ.neg
      have hx_sub : x + (-Δ) = (c : ℝ*) := by
        unfold x
        ring
      rw [hx_sub, starFun_coe] at heq_x
      have hmul_eq : (starFun f' x - (f' c : ℝ*)) * Δ = (ε - ε') * Δ := by
        unfold x at heq_x ⊢
        linarith
      have hdiff_eq : starFun f' x - (f' c : ℝ*) = ε - ε' := mul_right_cancel₀ hΔ0 hmul_eq
      unfold InfClose
      rw [show starFun f' ((c : ℝ*) + Δ) - (f' c : ℝ*) = starFun f' x - (f' c : ℝ*) from rfl,
          hdiff_eq]
      exact hε.sub hε'

/-- Goldblatt Exercise 8.12(2) (p. 104): The pathological differentiable function
`f(x) = x² sin(1/x)` for `x ≠ 0` and `f(0) = 0`. -/
def sqMulSinInv (x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ 2 * Real.sin (1 / x)

/-- Nonstandard derivative of `sqMulSinInv` at `0` is `0` (Goldblatt Exercise 8.12(2a), p. 104). -/
theorem hasNSCDerivAt_sqMulSinInv_zero : HasNSCDerivAt sqMulSinInv 0 0 := by
  intro Δx hΔx hne
  rw [Hyperreal.coe_zero, infClose_zero_iff]
  rcases ofSeq_surjective Δx with ⟨r, rfl⟩
  have hr_ne : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), r i ≠ 0 :=
    Ultrafilter.eventually_not.2 fun h0 ↦ hne (Germ.coe_eq.2 h0)
  refine isInfinitesimal_of_abs_le hΔx ?_
  refine ofSeq_le_ofSeq.2 (hr_ne.mono fun i hi ↦ ?_)
  change |(sqMulSinInv (0 + r i) - sqMulSinInv 0) / r i| ≤ |r i|
  simp only [sqMulSinInv, zero_add, hi, ↓reduceIte, sub_zero]
  have hquot : (r i ^ 2 * Real.sin (1 / r i)) / r i = r i * Real.sin (1 / r i) := by
    field_simp [hi]
  rw [hquot, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

/-- At any `x ≠ 0`, `sqMulSinInv` has nonstandard derivative `2 x sin(1/x) - cos(1/x)`
(proved directly using our nonstandard product, chain, reciprocal, and sine rules!). -/
theorem hasNSCDerivAt_sqMulSinInv_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    HasNSCDerivAt sqMulSinInv (2 * x * Real.sin (1 / x) - Real.cos (1 / x)) x := by
  let g : ℝ → ℝ := fun t ↦ t ^ 2 * Real.sin t⁻¹
  have hsin_inv : HasNSCDerivAt (fun t ↦ Real.sin t⁻¹)
      (Real.cos x⁻¹ * (-1 / x ^ 2)) x :=
    (hasNSCDerivAt_sin x⁻¹).comp ((hasNSCDerivAt_id x).inv hx)
  have hpow2 : HasNSCDerivAt (fun t ↦ t ^ 2) (2 * x) x := by
    simpa using hasNSCDerivAt_pow 2 x
  have hg_deriv : HasNSCDerivAt g (2 * x * Real.sin (1 / x) - Real.cos (1 / x)) x := by
    have hmul := hpow2.mul hsin_inv
    have hval : (2 * x) * Real.sin x⁻¹ + x ^ 2 * (Real.cos x⁻¹ * (-1 / x ^ 2)) =
        2 * x * Real.sin (1 / x) - Real.cos (1 / x) := by
      have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
      rw [one_div]
      field_simp [hx2]
      ring
    rwa [hval] at hmul
  intro Δx hΔx hne
  have hx_app : IsAppreciable ((x : ℝ*) + Δx) :=
    (isAppreciable_coe_iff.2 hx).add_isInfinitesimal hΔx
  have hxΔ_ne : (x : ℝ*) + Δx ≠ 0 := hx_app.ne_zero
  have hfg_star : starFun sqMulSinInv ((x : ℝ*) + Δx) = starFun g ((x : ℝ*) + Δx) := by
    rcases ofSeq_surjective Δx with ⟨r, rfl⟩
    have hr_ne : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), x + r i ≠ 0 :=
      Ultrafilter.eventually_not.2 fun h0 ↦ hxΔ_ne (Germ.coe_eq.2 h0)
    refine Germ.coe_eq.2 (hr_ne.mono fun i hi ↦ ?_)
    simp [sqMulSinInv, g, hi, one_div]
  have hfg_x : sqMulSinInv x = g x := by simp [sqMulSinInv, g, hx, one_div]
  rw [hfg_star, hfg_x]
  exact hg_deriv Δx hΔx hne

/-- **Goldblatt Exercise 8.12(2a) (p. 104)**: `sqMulSinInv` is differentiable everywhere (in
particular `deriv sqMulSinInv 0 = 0`), yet its derivative `deriv sqMulSinInv` is NOT continuous
at `0`. -/
theorem sqMulSinInv_deriv_exists_and_not_continuousAt_zero :
    HasNSCDerivAt sqMulSinInv 0 0 ∧
      (∀ x : ℝ, DifferentiableAt ℝ sqMulSinInv x) ∧
      ¬ ContinuousAt (deriv sqMulSinInv) 0 := by
  refine ⟨hasNSCDerivAt_sqMulSinInv_zero, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0
    · subst hx
      exact (hasDerivAt_iff_hasNSCDerivAt.2 hasNSCDerivAt_sqMulSinInv_zero).differentiableAt
    · exact (hasDerivAt_iff_hasNSCDerivAt.2
        (hasNSCDerivAt_sqMulSinInv_of_ne_zero hx)).differentiableAt
  · intro hcont
    let xSeq : ℕ → ℝ := fun n ↦ 1 / (2 * Real.pi * ((n : ℝ) + 1))
    have hx_ne : ∀ n : ℕ, xSeq n ≠ 0 := fun n ↦ by
      unfold xSeq
      have hpi : 0 < Real.pi := Real.pi_pos
      positivity
    have hx_inf : IsInfinitesimal (ofSeq xSeq) := by
      apply ofSeq_infinitesimal_of_tendsto_zero
      refine squeeze_zero_norm (fun n ↦ ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      unfold xSeq
      have hpi : 2 ≤ Real.pi := Real.two_le_pi
      have hd1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact one_div_le_one_div_of_le hd1 (by nlinarith)
    have hderiv_val : ∀ n : ℕ, deriv sqMulSinInv (xSeq n) = -1 := by
      intro n
      rw [(hasNSCDerivAt_sqMulSinInv_of_ne_zero (hx_ne n)).deriv_eq]
      have hinv : 1 / xSeq n = ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
        unfold xSeq
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
        push_cast
        field_simp [hpi, hn1]
      have hsin : Real.sin (1 / xSeq n) = 0 := by
        rw [hinv, show ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) = ((2 * (n + 1) : ℕ) : ℝ) * Real.pi by
          push_cast; ring]
        exact Real.sin_nat_mul_pi (2 * (n + 1))
      have hcos : Real.cos (1 / xSeq n) = 1 := by
        rw [hinv]
        exact Real.cos_nat_mul_two_pi (n + 1)
      rw [hsin, hcos]
      ring
    have hclose := continuousAt_iff_infClose_starFun.1 hcont (ofSeq xSeq) hx_inf
    rw [Hyperreal.coe_zero, zero_add, hasNSCDerivAt_sqMulSinInv_zero.deriv_eq] at hclose
    have hstar_eq : starFun (deriv sqMulSinInv) (ofSeq xSeq) = ((-1 : ℝ) : ℝ*) :=
      Germ.coe_eq.2 (Eventually.of_forall hderiv_val)
    rw [hstar_eq] at hclose
    have heq : (-1 : ℝ) = 0 := coe_eq_of_infClose hclose
    norm_num at heq

/-- **Goldblatt Exercise 8.12(2b) (p. 104)**:
For any unlimited hypernatural `N ∈ ℕ*`, let `x = 1 / (2 π N) ∈ *(0, 1)`. Then `x` is a positive
infinitesimal (so NOT well inside `*(0, 1)`), and there exists an infinitesimal `Δx ∈ ℝ*` (with
`x + Δx ∈ *(0, 1)`) such that for EVERY infinitesimal `η ∈ ℝ*`,
`*f(x + Δx) ≠ *f(x) + *f'(x) Δx + η Δx`! -/
theorem sqMulSinInv_fails_incremental_eq_at_unlimited {N : ℕ*} (hN : IsUnlimitedNat N) :
    let x : ℝ* := 1 / (2 * (Real.pi : ℝ*) * Hypernat.toHyperreal N)
    x ∈ starSet (Set.Ioo 0 1) ∧
      ¬ IsWellInsideIoo x 0 1 ∧
      ∃ Δx : ℝ*, IsInfinitesimal Δx ∧ x + Δx ∈ starSet (Set.Ioo 0 1) ∧
        ∀ η : ℝ*, IsInfinitesimal η →
          starFun sqMulSinInv (x + Δx) ≠
            starFun sqMulSinInv x + starFun (deriv sqMulSinInv) x * Δx + η * Δx := by
  intro x
  have hN_unl_real : IsPosUnlimited (Hypernat.toHyperreal N) :=
    isUnlimitedNat_iff_isPosUnlimited.1 hN
  have hden_unl : IsUnlimited (2 * (Real.pi : ℝ*) * Hypernat.toHyperreal N) := by
    rw [isUnlimited_iff_pos_or_neg]
    left
    intro r
    have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
    have hgt := hN_unl_real (r / (2 * Real.pi))
    have hmul := mul_lt_mul_of_pos_left hgt (Hyperreal.coe_pos.2 h2pi_pos)
    have hlhs : ((2 * Real.pi : ℝ) : ℝ*) * ((r / (2 * Real.pi) : ℝ) : ℝ*) = (r : ℝ*) := by
      rw [← Hyperreal.coe_mul, mul_div_cancel₀ r h2pi_pos.ne']
    have hrhs : ((2 * Real.pi : ℝ) : ℝ*) * Hypernat.toHyperreal N =
        2 * (Real.pi : ℝ*) * Hypernat.toHyperreal N := by
      push_cast
      rfl
    rwa [hlhs, hrhs] at hmul
  have hx_inf : IsInfinitesimal x := by
    unfold x
    rw [one_div]
    exact hden_unl.inv_isInfinitesimal
  have hx_pos : 0 < x := by
    unfold x
    have hN1 : (1 : ℝ*) < Hypernat.toHyperreal N := hN_unl_real 1
    have hpi : (0 : ℝ*) < (Real.pi : ℝ*) := Hyperreal.coe_pos.2 Real.pi_pos
    positivity
  have hx_lt1 : x < 1 := by
    have := hx_inf 1 one_pos
    rwa [abs_of_pos hx_pos] at this
  have hx_mem : x ∈ starSet (Set.Ioo 0 1) := by
    rw [starSet_Ioo, Set.mem_Ioo]
    exact ⟨by simpa using hx_pos, by simpa using hx_lt1⟩
  have hx_not_well : ¬ IsWellInsideIoo x 0 1 := fun hw ↦
    hw.2.2.1 (by simpa [InfClose] using hx_inf)
  -- Choose `x' = 1 / (2 π N + π) ∈ *(0, 1)` and `Δx = x' - x`
  let x' : ℝ* := 1 / (2 * (Real.pi : ℝ*) * Hypernat.toHyperreal N + (Real.pi : ℝ*))
  have hden'_unl : IsUnlimited (2 * (Real.pi : ℝ*) * Hypernat.toHyperreal N + (Real.pi : ℝ*)) :=
    hden_unl.add_isLimited (isLimited_coe Real.pi)
  have hx'_inf : IsInfinitesimal x' := by
    unfold x'
    rw [one_div]
    exact hden'_unl.inv_isInfinitesimal
  have hx'_pos : 0 < x' := by
    unfold x'
    have hN1 : (1 : ℝ*) < Hypernat.toHyperreal N := hN_unl_real 1
    have hpi : (0 : ℝ*) < (Real.pi : ℝ*) := Hyperreal.coe_pos.2 Real.pi_pos
    positivity
  have hx'_lt1 : x' < 1 := by
    have := hx'_inf 1 one_pos
    rwa [abs_of_pos hx'_pos] at this
  have hx'_mem : x' ∈ starSet (Set.Ioo 0 1) := by
    rw [starSet_Ioo, Set.mem_Ioo]
    exact ⟨by simpa using hx'_pos, by simpa using hx'_lt1⟩
  let Δx : ℝ* := x' - x
  have hΔx_inf : IsInfinitesimal Δx := hx'_inf.sub hx_inf
  have hxΔ_eq : x + Δx = x' := add_sub_cancel _ _
  have hΔx_ne : Δx ≠ 0 := by
    have hlt_x' : x' < x := by
      unfold x' x
      have hN1 : (1 : ℝ*) < Hypernat.toHyperreal N := hN_unl_real 1
      have hpi : (0 : ℝ*) < (Real.pi : ℝ*) := Hyperreal.coe_pos.2 Real.pi_pos
      have hd_pos : 0 < 2 * (Real.pi : ℝ*) * Hypernat.toHyperreal N := by positivity
      have hd_lt : 2 * (Real.pi : ℝ*) * Hypernat.toHyperreal N <
          2 * (Real.pi : ℝ*) * Hypernat.toHyperreal N + (Real.pi : ℝ*) := by linarith
      simpa only [one_div] using inv_strictAnti₀ hd_pos hd_lt
    exact sub_ne_zero.2 hlt_x'.ne
  -- Evaluate `*f(x) = 0`, `*f(x') = 0`, and `*f'(x) = -1`
  have hvals : starFun sqMulSinInv x = 0 ∧
      starFun sqMulSinInv x' = 0 ∧
      starFun (deriv sqMulSinInv) x = -1 := by
    have hN_ge1 : (1 : ℕ*) ≤ N := (hN 0).le |> fun _ ↦ (hN 1).le
    induction N using Germ.inductionOn with | _ m =>
    have hm1 : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 1 ≤ m i :=
      (Germ.coe_lt.1 (hN 0)).mono fun _ hi ↦ hi
    have hx_germ : x = ofSeq (fun i ↦ 1 / (2 * Real.pi * (m i : ℝ))) := rfl
    have hx'_germ : x' = ofSeq (fun i ↦ 1 / (2 * Real.pi * (m i : ℝ) + Real.pi)) := rfl
    rw [hx_germ, hx'_germ]
    refine ⟨?_, ?_, ?_⟩
    · refine Germ.coe_eq.2 (hm1.mono fun i hi ↦ ?_)
      have hmi_pos : (0 : ℝ) < (m i : ℝ) := Nat.cast_pos.2 (by omega)
      have hpi_pos : 0 < Real.pi := Real.pi_pos
      have hti_ne : (1 / (2 * Real.pi * (m i : ℝ)) : ℝ) ≠ 0 := by positivity
      change sqMulSinInv (1 / (2 * Real.pi * (m i : ℝ))) = 0
      simp only [sqMulSinInv, hti_ne, ↓reduceIte]
      have hinv : 1 / (1 / (2 * Real.pi * (m i : ℝ))) = ((2 * m i : ℕ) : ℝ) * Real.pi := by
        push_cast
        field_simp [hpi_pos.ne', hmi_pos.ne']
      rw [hinv, Real.sin_nat_mul_pi, mul_zero]
    · refine Germ.coe_eq.2 (hm1.mono fun i hi ↦ ?_)
      have hmi_pos : (0 : ℝ) < (m i : ℝ) := Nat.cast_pos.2 (by omega)
      have hpi_pos : 0 < Real.pi := Real.pi_pos
      have hti_ne : (1 / (2 * Real.pi * (m i : ℝ) + Real.pi) : ℝ) ≠ 0 := by positivity
      change sqMulSinInv (1 / (2 * Real.pi * (m i : ℝ) + Real.pi)) = 0
      simp only [sqMulSinInv, hti_ne, ↓reduceIte]
      have hinv : 1 / (1 / (2 * Real.pi * (m i : ℝ) + Real.pi)) =
          ((2 * m i + 1 : ℕ) : ℝ) * Real.pi := by
        push_cast
        field_simp [(by positivity : 2 * Real.pi * (m i : ℝ) + Real.pi ≠ 0)]
      rw [hinv, Real.sin_nat_mul_pi, mul_zero]
    · refine Germ.coe_eq.2 (hm1.mono fun i hi ↦ ?_)
      have hmi_pos : (0 : ℝ) < (m i : ℝ) := Nat.cast_pos.2 (by omega)
      have hpi_pos : 0 < Real.pi := Real.pi_pos
      have hti_ne : (1 / (2 * Real.pi * (m i : ℝ)) : ℝ) ≠ 0 := by positivity
      change deriv sqMulSinInv (1 / (2 * Real.pi * (m i : ℝ))) = -1
      rw [(hasNSCDerivAt_sqMulSinInv_of_ne_zero hti_ne).deriv_eq]
      have hinv : 1 / (1 / (2 * Real.pi * (m i : ℝ))) = 2 * Real.pi * (m i : ℝ) := by
        field_simp [hpi_pos.ne', hmi_pos.ne']
      have hsin : Real.sin (2 * Real.pi * (m i : ℝ)) = 0 := by
        rw [show 2 * Real.pi * (m i : ℝ) = ((2 * m i : ℕ) : ℝ) * Real.pi by push_cast; ring]
        exact Real.sin_nat_mul_pi (2 * m i)
      have hcos : Real.cos (2 * Real.pi * (m i : ℝ)) = 1 := by
        rw [show 2 * Real.pi * (m i : ℝ) = (m i : ℝ) * (2 * Real.pi) by ring]
        exact Real.cos_nat_mul_two_pi (m i)
      rw [hinv, hsin, hcos]
      ring
  refine ⟨hx_mem, hx_not_well, Δx, hΔx_inf, hxΔ_eq ▸ hx'_mem, fun η hη heq ↦ ?_⟩
  rw [hxΔ_eq, hvals.1, hvals.2.1, hvals.2.2] at heq
  have hmul0 : (η - 1) * Δx = 0 := by linarith
  have hη1 : η = ((1 : ℝ) : ℝ*) := by
    have : η - 1 = 0 := (mul_eq_zero.1 hmul0).resolve_right hΔx_ne
    linarith [Hyperreal.coe_one]
  rw [hη1] at hη
  exact one_ne_zero (isInfinitesimal_coe_iff.1 hη)

end Goldblatt.Ch08
end
