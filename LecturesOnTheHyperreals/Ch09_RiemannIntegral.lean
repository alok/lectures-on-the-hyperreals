import LecturesOnTheHyperreals.Ch05_HyperrealsGreatAndSmall
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# Chapter 9: The Riemann Integral

Formalization of Robert Goldblatt, *Lectures on the Hyperreals*, Chapter 9 (pp. 105–112):

* **§9.1 Riemann Sums (pp. 105–108)**:
  - Standard partitions `IntervalPartition a b`, upper/lower Darboux sums (`upperDarbouxSum`,
    `lowerDarbouxSum`), and ordinary left-endpoint Riemann sums (`partitionRiemannSum`).
  - Partition refinements, `lowerDarbouxSum_le_upperDarbouxSum` (`L_a^b(f, P_1) ≤ U_a^b(f, P_2)`),
    and the characterization of Darboux/Riemann integrability (`IsDarbouxIntegrableOn`,
    `isDarbouxIntegrableOn_iff_eps`).
  - Step-size partitions `P_{Δx}` (`stepPartition`), real step-size sums (`stepUpperSum`,
    `stepLowerSum`, `stepRiemannSum`), and their hyperreal extensions (`hyperStepUpperSum`,
    `hyperStepLowerSum`, `hyperStepSum`) via `starFun`.
  - **Theorem 9.1.1** (`hyperStepLowerSum_infClose_hyperStepUpperSum`, pp. 107–108): for continuous
    `f` on `[a, b]` and any positive infinitesimal `Δx`, `L_a^b(f, Δx) ≈ₕ U_a^b(f, Δx)`.
  - **Exercise 9.1.2** (`stepUpperSum_sub_stepLowerSum_le_of_monotoneOn`,
    `stepUpperSum_sub_stepLowerSum_le_of_antitoneOn`,
    `hyperStepLowerSum_infClose_hyperStepUpperSum_of_monotonic`, p. 108): Theorem 9.1.1 for
    nondecreasing, nonincreasing, and monotonic functions.
* **§9.2 The Integral as the Shadow of Riemann Sums (pp. 108–110)**:
  - Limitedness and infinite closeness of `hyperStepSum f a b dx₁ ≈ₕ hyperStepSum f a b dx₂` for
    any two positive infinitesimals `dx₁, dx₂`.
  - Nonstandard integral `hyperIntegral f a b := shadow (hyperStepSum f a b Hyperreal.epsilon)`,
    proof of standard Darboux integrability (`isDarbouxIntegrableOn_hyperIntegral`), right-hand
    limit `lim_{Δx → 0⁺} S_a^b(f, Δx)` (`tendsto_stepRiemannSum_nhdsWithin_Ioi`), and full
    equivalence `∃ I, IsDarbouxIntegrableOn f a b I ↔ ∀ Δx > 0 infinitesimal, U(f, Δx) ≈ₕ L(f, Δx)`.
  - **Exercise 9.2.1** (`riemannSumEq`, `upperSumEq`, `lowerSumEq`, `hyperRiemannSum`,
    `hyperUpperSumEq`, `hyperLowerSumEq`, p. 110): equal-subdivision sums for unlimited `N ∈ ℕ*`,
    direct bridge to Mathlib's `∫ x in a..b, f x`, and explicit evaluations of
    `∫_0^b x dx = b^2 / 2` and `∫_0^b x^2 dx = b^3 / 3` via power-sum formulas and `shadow`.
* **§9.3 Standard Properties of the Integral via Infinitesimals (pp. 108–110)**:
  - Constant rule, scalar linearity, additivity, monotonicity, boundedness, triangle inequality, and
    interval additivity / Chasles' juxtaposition (`∫_a^b f = ∫_a^c f + ∫_c^b f`, eq. (iv) &
    **Exercise 9.3.1**).
* **§9.4 Differentiating the Area Function & Fundamental Theorem of Calculus (pp. 111–112)**:
  - **Theorem 9.4.1 (FTC Part 1)**: Nonstandard proof that `(starFun F (c + Δx) - F c) / Δx ≈ₕ f c`
    for the area function `F(x) = shadow (hyperRiemannSum f a x omegaNat)`, deducing `HasDerivAt`
    on `(a, b)` and `HasDerivWithinAt` on `[a, b]` (including endpoints).
  - **Theorem 9.4.2 (FTC Part 2)**: Both Goldblatt's `G - F` constant-difference proof and the
    direct hyperfinite telescoping proof `∑ (G(x_{k+1}) - G(x_k)) = ∑ (f(x_k) Δx + η_k Δx)`.
* **§9.5 Average Function Values & Mean Value Theorems for Integrals (pp. 111–112)**:
  - Sample averages `sampleAverage`, `hyperSampleAverage`, and Goldblatt §9.5 (`Av(N) ≈ₕ
    (b - a)⁻¹ ∫_a^b f`).
  - First Mean Value Theorem for Integrals and Weighted Mean Value Theorem for Integrals proved via
    hyperfinite Riemann sums, `shadow`, Extreme Value Theorem, and Intermediate Value Theorem.
-/

noncomputable section

namespace Goldblatt.Ch09

open Filter
open Hyperreal (ofSeq ofSeq_lt_ofSeq ofSeq_le_ofSeq ofSeq_surjective)
open scoped Topology BigOperators

/-! ## §9.0 Nonstandard Microcontinuity and Derivative Slope Lemmas -/

/-- Microcontinuity on a set `A ⊆ ℝ` (Goldblatt Theorem 7.1.1): if `f` is continuous within `A`
at `c`, then for every `x ∈ *A` with `x ≈ₕ c`, `*f(x) ≈ₕ f(c)`. -/
theorem infClose_starFun_of_continuousWithinAt {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (hf : ContinuousWithinAt f A c) {x : ℝ*} (hxA : x ∈ starSet A) (hxc : x ≈ₕ (c : ℝ*)) :
    starFun f x ≈ₕ (f c : ℝ*) := by
  intro r hr
  rw [Metric.continuousWithinAt_iff] at hf
  obtain ⟨δ, hδ, hball⟩ := hf r hr
  rcases ofSeq_surjective x with ⟨s, rfl⟩
  have hsA : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), s n ∈ A := ofSeq_mem_starSet.1 hxA
  have hlt : |ofSeq s - (c : ℝ*)| < (δ : ℝ*) := hxc δ hδ
  have hsδ : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |s n - c| < δ := ofSeq_lt_ofSeq.1 hlt
  change ofSeq (fun n ↦ |f (s n) - f c|) < (r : ℝ*)
  refine ofSeq_lt_ofSeq.2 ((hsA.and hsδ).mono fun n ⟨hnA, hnδ⟩ ↦ ?_)
  simpa [Real.dist_eq] using hball hnA (by simpa [Real.dist_eq] using hnδ)

/-- Uniform microcontinuity on a closed interval `[a, b]` (Goldblatt Theorem 7.7.2, referenced in
Theorem 9.1.1, p. 108): if `f` is continuous on `[a, b]`, then for any `x, y ∈ *[a, b]` with
`x ≈ₕ y`, we have `*f(x) ≈ₕ *f(y)`. -/
theorem infClose_starFun_of_continuousOn_Icc {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) {x y : ℝ*}
    (hx : x ∈ Set.Icc (a : ℝ*) (b : ℝ*)) (hy : y ∈ Set.Icc (a : ℝ*) (b : ℝ*))
    (hxy : x ≈ₕ y) : starFun f x ≈ₕ starFun f y := by
  have hx_lim : IsLimited x :=
    isLimited_iff_exists_real.2 ⟨a - 1, b + 1,
      (Hyperreal.coe_lt_coe.2 (by linarith)).trans_le hx.1,
      hx.2.trans_lt (Hyperreal.coe_lt_coe.2 (by linarith))⟩
  set r : ℝ := shadow x
  have hxr : x ≈ₕ (r : ℝ*) := infClose_shadow hx_lim
  have hyr : y ≈ₕ (r : ℝ*) := hxy.symm.trans hxr
  have hr_mem : r ∈ Set.Icc a b :=
    ⟨coe_le_of_infClose_le (InfClose.refl _) hx.1 hxr,
     coe_le_of_infClose_le hxr.symm hx.2 (InfClose.refl _)⟩
  have hx_star : x ∈ starSet (Set.Icc a b) := by rwa [starSet_Icc]
  have hy_star : y ∈ starSet (Set.Icc a b) := by rwa [starSet_Icc]
  have hfx : starFun f x ≈ₕ (f r : ℝ*) :=
    infClose_starFun_of_continuousWithinAt (hf r hr_mem) hx_star hxr
  have hfy : starFun f y ≈ₕ (f r : ℝ*) :=
    infClose_starFun_of_continuousWithinAt (hf r hr_mem) hy_star hyr
  exact hfx.trans hfy.symm

/-- Sandwich principle for infinite closeness: if `u ≤ w ≤ v` and both `u ≈ₕ z` and `v ≈ₕ z`,
then `w ≈ₕ z`. -/
theorem infClose_of_le_of_le {u v w z : ℝ*} (huw : u ≤ w) (hwv : w ≤ v)
    (huz : u ≈ₕ z) (hvz : v ≈ₕ z) : w ≈ₕ z := by
  intro r hr
  have h1 : |u - z| < (r : ℝ*) := huz r hr
  have h2 : |v - z| < (r : ℝ*) := hvz r hr
  rw [abs_lt] at h1 h2 ⊢
  exact ⟨by linarith, by linarith⟩

/-- Nonstandard characterization of `HasDerivWithinAt` on `A ⊆ ℝ` (Goldblatt Theorem 8.1.1):
if for every nonzero infinitesimal `dx` with `c + dx ∈ *A` we have
`(*F(c + dx) - F(c)) / dx ≈ₕ L`, then `HasDerivWithinAt F L A c`. -/
theorem hasDerivWithinAt_of_infClose_slope {F : ℝ → ℝ} {A : Set ℝ} {c L : ℝ}
    (h : ∀ dx : ℝ*, IsInfinitesimal dx → dx ≠ 0 → (c : ℝ*) + dx ∈ starSet A →
      (starFun F ((c : ℝ*) + dx) - (F c : ℝ*)) / dx ≈ₕ (L : ℝ*)) :
    HasDerivWithinAt F L A c := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  by_contra hnot
  rw [Metric.tendsto_nhdsWithin_nhds] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hex⟩ := hnot
  choose x hx_mem hx_dist hx_bad using fun n : ℕ ↦
    hex (((n : ℝ) + 1)⁻¹) (by positivity)
  let dx : ℝ* := ofSeq (fun n ↦ x n - c)
  have hdx_inf : IsInfinitesimal dx := by
    refine ofSeq_infinitesimal_of_tendsto_zero ?_
    refine Metric.tendsto_atTop.2 fun r hr ↦ ?_
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hr
    refine ⟨N, fun n hn ↦ ?_⟩
    have hlt1 : |x n - c| < ((n : ℝ) + 1)⁻¹ := by simpa [Real.dist_eq] using hx_dist n
    have hle : ((n : ℝ) + 1)⁻¹ ≤ ((N : ℝ) + 1)⁻¹ :=
      inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    simpa [Real.dist_eq] using hlt1.trans (hle.trans_lt (by simpa [one_div] using hN))
  have hdx_ne : dx ≠ 0 := by
    intro h0
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), x n - c = 0 := Germ.coe_eq.1 h0
    obtain ⟨n, hn⟩ := hev.exists
    exact (hx_mem n).2 (sub_eq_zero.1 hn)
  have hcdx_eq : (c : ℝ*) + dx = ofSeq x :=
    Germ.coe_eq.2 (Eventually.of_forall fun n ↦ add_sub_cancel c (x n))
  have hmemA : (c : ℝ*) + dx ∈ starSet A := by
    rw [hcdx_eq, ofSeq_mem_starSet]
    exact Eventually.of_forall fun n ↦ (hx_mem n).1
  have hclose := h dx hdx_inf hdx_ne hmemA ε hε
  have hslope_ge : (ε : ℝ*) ≤ |(starFun F ((c : ℝ*) + dx) - (F c : ℝ*)) / dx - (L : ℝ*)| := by
    rw [hcdx_eq]
    refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
    change ε ≤ |(F (x n) - F c) / (x n - c) - L|
    have hb := hx_bad n
    rw [Real.dist_eq, slope_def_field] at hb
    exact hb
  exact lt_irrefl _ (hclose.trans_le hslope_ge)

/-- Nonstandard characterization of `HasDerivAt` (Goldblatt Theorem 8.1.1, referenced on p. 112):
if for every nonzero infinitesimal `dx`, `(*F(c + dx) - F(c)) / dx ≈ₕ L`, then
`HasDerivAt F L c`. -/
theorem hasDerivAt_of_infClose_slope {F : ℝ → ℝ} {c L : ℝ}
    (h : ∀ dx : ℝ*, IsInfinitesimal dx → dx ≠ 0 →
      (starFun F ((c : ℝ*) + dx) - (F c : ℝ*)) / dx ≈ₕ (L : ℝ*)) :
    HasDerivAt F L c := by
  rw [← hasDerivWithinAt_univ]
  exact hasDerivWithinAt_of_infClose_slope fun dx hinf hne _ ↦ h dx hinf hne

/-! ## §9.1 Partitions, Upper/Lower Darboux Sums, and Step-Size Riemann Sums -/

/-- Goldblatt §9.1 (p. 105): A finite partition `P = {x_0, ..., x_n}` of `[a, b]` with
`a = x_0 ≤ x_1 ≤ ... ≤ x_n = b`. -/
structure IntervalPartition (a b : ℝ) where
  /-- Number of subintervals in `P`. -/
  n : ℕ
  /-- Sequence of partition points `x_0, ..., x_n`. -/
  pts : ℕ → ℝ
  /-- Left endpoint `x_0 = a`. -/
  pts_zero : pts 0 = a
  /-- Right endpoint `x_n = b`. -/
  pts_last : pts n = b
  /-- Monotonicity `x_k ≤ x_{k+1}` for `k < n`. -/
  mono : ∀ k < n, pts k ≤ pts (k + 1)

namespace IntervalPartition

/-- Monotonicity of partition points across arbitrary indices `i ≤ j ≤ P.n`. -/
theorem pts_le_pts {a b : ℝ} (P : IntervalPartition a b) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ P.n) : P.pts i ≤ P.pts j := by
  induction j with
  | zero =>
    have : i = 0 := Nat.eq_zero_of_le_zero hij
    subst this
    exact le_rfl
  | succ k ih =>
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · exact (ih (Nat.lt_succ_iff.1 hlt) (Nat.le_of_succ_le hj)).trans
        (P.mono k (Nat.lt_of_succ_le hj))

/-- Every `IntervalPartition a b` witnesses `a ≤ b`. -/
theorem le_endpoints {a b : ℝ} (P : IntervalPartition a b) : a ≤ b := by
  have h := P.pts_le_pts (Nat.zero_le P.n) le_rfl
  rwa [P.pts_zero, P.pts_last] at h

/-- Every partition point `P.pts k` (`k ≤ P.n`) lies in `[a, b]`. -/
theorem pts_mem_Icc {a b : ℝ} (P : IntervalPartition a b) {k : ℕ} (hk : k ≤ P.n) :
    P.pts k ∈ Set.Icc a b := by
  refine ⟨?_, ?_⟩
  · have h := P.pts_le_pts (Nat.zero_le k) hk
    rwa [P.pts_zero] at h
  · have h := P.pts_le_pts hk le_rfl
    rwa [P.pts_last] at h

/-- Every subinterval `[P.pts k, P.pts (k + 1)]` (`k < P.n`) is contained in `[a, b]`. -/
theorem subinterval_subset_Icc {a b : ℝ} (P : IntervalPartition a b) {k : ℕ} (hk : k < P.n) :
    Set.Icc (P.pts k) (P.pts (k + 1)) ⊆ Set.Icc a b :=
  Set.Icc_subset_Icc (P.pts_mem_Icc hk.le).1 (P.pts_mem_Icc (Nat.succ_le_of_lt hk)).2

/-- Every subinterval width `Δx_{k+1} = x_{k+1} - x_k` (`k < P.n`) is nonnegative. -/
theorem width_nonneg {a b : ℝ} (P : IntervalPartition a b) {k : ℕ} (hk : k < P.n) :
    0 ≤ P.pts (k + 1) - P.pts k :=
  sub_nonneg.2 (P.mono k hk)

/-- Telescoping sum of subinterval widths: `∑_{k < n} (x_{k+1} - x_k) = b - a`. -/
theorem sum_widths {a b : ℝ} (P : IntervalPartition a b) :
    ∑ k ∈ Finset.range P.n, (P.pts (k + 1) - P.pts k) = b - a := by
  rw [Finset.sum_range_sub, P.pts_last, P.pts_zero]

/-- Trivial 1-subinterval partition `{a, b}` of `[a, b]` for `a ≤ b`. -/
def single (a b : ℝ) (hab : a ≤ b) : IntervalPartition a b where
  n := 1
  pts k := if k = 0 then a else b
  pts_zero := rfl
  pts_last := rfl
  mono k hk := by
    have hk0 : k = 0 := Nat.lt_one_iff.1 hk
    subst hk0
    simpa using hab

open Classical in
/-- Finite set of partition points `{x_0, ..., x_n}` of `P`. -/
def pointFinset {a b : ℝ} (P : IntervalPartition a b) : Finset ℝ :=
  (Finset.range (P.n + 1)).image P.pts

/-- The left endpoint `a` belongs to `P.pointFinset`. -/
theorem left_mem_pointFinset {a b : ℝ} (P : IntervalPartition a b) : a ∈ P.pointFinset := by
  classical
  exact Finset.mem_image.2 ⟨0, Finset.mem_range.2 (Nat.succ_pos P.n), P.pts_zero⟩

/-- The right endpoint `b` belongs to `P.pointFinset`. -/
theorem right_mem_pointFinset {a b : ℝ} (P : IntervalPartition a b) : b ∈ P.pointFinset := by
  classical
  exact Finset.mem_image.2 ⟨P.n, Finset.mem_range.2 (Nat.lt_succ_self P.n), P.pts_last⟩

/-- Every point of `P.pointFinset` lies in `[a, b]`. -/
theorem mem_Icc_of_mem_pointFinset {a b : ℝ} (P : IntervalPartition a b) {x : ℝ}
    (hx : x ∈ P.pointFinset) : x ∈ Set.Icc a b := by
  classical
  rcases Finset.mem_image.1 hx with ⟨k, hk, rfl⟩
  exact P.pts_mem_Icc (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

/-- Construct an `IntervalPartition a b` by sorting any `Finset ℝ` containing `a` and `b`
inside `[a, b]`. -/
def ofFinset {a b : ℝ} (S : Finset ℝ) (ha : a ∈ S) (hb : b ∈ S)
    (hsub : ∀ x ∈ S, x ∈ Set.Icc a b) : IntervalPartition a b where
  n := S.card - 1
  pts k := if hk : k < S.card then S.orderEmbOfFin rfl ⟨k, hk⟩ else b
  pts_zero := by
    have hpos : 0 < S.card := Finset.card_pos.2 ⟨a, ha⟩
    simp only [hpos, ↓reduceDIte, Finset.orderEmbOfFin_zero rfl hpos]
    exact le_antisymm (Finset.min'_le S a ha) (Finset.le_min' S _ _ fun x hx ↦ (hsub x hx).1)
  pts_last := by
    have hpos : 0 < S.card := Finset.card_pos.2 ⟨a, ha⟩
    have hlt : S.card - 1 < S.card := Nat.sub_lt hpos Nat.zero_lt_one
    simp only [hlt, ↓reduceDIte, Finset.orderEmbOfFin_last rfl hpos]
    exact le_antisymm (Finset.max'_le S _ _ fun x hx ↦ (hsub x hx).2) (Finset.le_max' S b hb)
  mono k hk := by
    have hk1 : k + 1 < S.card := by omega
    have hk0 : k < S.card := by omega
    simp only [hk0, hk1, ↓reduceDIte]
    exact (S.orderEmbOfFin rfl).monotone (Nat.le_succ k)

/-- Every element of `S` occurs as a partition point of `ofFinset S ha hb hsub`. -/
theorem mem_pts_ofFinset {a b : ℝ} {S : Finset ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (hsub : ∀ x ∈ S, x ∈ Set.Icc a b) {x : ℝ} (hx : x ∈ S) :
    ∃ j ≤ (ofFinset S ha hb hsub).n, (ofFinset S ha hb hsub).pts j = x := by
  have hx_range : x ∈ Set.range (S.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hx
  rcases hx_range with ⟨⟨j, hj⟩, rfl⟩
  refine ⟨j, ?_, ?_⟩
  · change j ≤ S.card - 1
    omega
  · simp [ofFinset, hj]

open Classical in
/-- Common refinement `P₁ ∨ P₂` obtained by merging and sorting the partition points of `P₁`
and `P₂`. -/
def commonRefinement {a b : ℝ} (P₁ P₂ : IntervalPartition a b) : IntervalPartition a b :=
  ofFinset (P₁.pointFinset ∪ P₂.pointFinset)
    (Finset.mem_union_left _ P₁.left_mem_pointFinset)
    (Finset.mem_union_left _ P₁.right_mem_pointFinset)
    (fun _ hx ↦ by
      rcases Finset.mem_union.1 hx with h1 | h2
      · exact P₁.mem_Icc_of_mem_pointFinset h1
      · exact P₂.mem_Icc_of_mem_pointFinset h2)

/-- Every partition point of `P₁` occurs among the partition points of `commonRefinement P₁ P₂`. -/
theorem exists_pts_commonRefinement_left {a b : ℝ} (P₁ P₂ : IntervalPartition a b)
    {k : ℕ} (hk : k ≤ P₁.n) :
    ∃ j ≤ (commonRefinement P₁ P₂).n, (commonRefinement P₁ P₂).pts j = P₁.pts k := by
  classical
  exact mem_pts_ofFinset _ _ _ (Finset.mem_union_left _
    (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hk), rfl⟩))

/-- Every partition point of `P₂` occurs among the partition points of `commonRefinement P₁ P₂`. -/
theorem exists_pts_commonRefinement_right {a b : ℝ} (P₁ P₂ : IntervalPartition a b)
    {k : ℕ} (hk : k ≤ P₂.n) :
    ∃ j ≤ (commonRefinement P₁ P₂).n, (commonRefinement P₁ P₂).pts j = P₂.pts k := by
  classical
  exact mem_pts_ofFinset _ _ _ (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hk), rfl⟩))

end IntervalPartition

/-- Goldblatt §9.1 (p. 105): Upper Darboux/Riemann sum `U_a^b(f, P) = ∑_{i=1}^n M_i Δx_i`. -/
def upperDarbouxSum {a b : ℝ} (f : ℝ → ℝ) (P : IntervalPartition a b) : ℝ :=
  ∑ k ∈ Finset.range P.n,
    sSup (f '' Set.Icc (P.pts k) (P.pts (k + 1))) * (P.pts (k + 1) - P.pts k)

/-- Goldblatt §9.1 (p. 105): Lower Darboux/Riemann sum `L_a^b(f, P) = ∑_{i=1}^n m_i Δx_i`. -/
def lowerDarbouxSum {a b : ℝ} (f : ℝ → ℝ) (P : IntervalPartition a b) : ℝ :=
  ∑ k ∈ Finset.range P.n,
    sInf (f '' Set.Icc (P.pts k) (P.pts (k + 1))) * (P.pts (k + 1) - P.pts k)

/-- Goldblatt §9.1 (p. 105): Ordinary left-endpoint Riemann sum
`S_a^b(f, P) = ∑_{i=1}^n f(x_{i-1}) Δx_i`. -/
def partitionRiemannSum {a b : ℝ} (f : ℝ → ℝ) (P : IntervalPartition a b) : ℝ :=
  ∑ k ∈ Finset.range P.n, f (P.pts k) * (P.pts (k + 1) - P.pts k)

/-- Helper: splitting a finite sum `∑ j < idx m` along a monotone index map
`0 = idx 0 ≤ ... ≤ idx m`. -/
private theorem sum_range_split_mono {idx : ℕ → ℕ} (h0 : idx 0 = 0)
    (hmono : ∀ k, idx k ≤ idx (k + 1)) (g : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range (idx m), g j =
      ∑ k ∈ Finset.range m, ∑ j ∈ Finset.Ico (idx k) (idx (k + 1)), g j := by
  induction m with
  | zero => simp [h0]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.sum_range_add_sum_Ico g (hmono k)]

/-- Goldblatt §9.1 (p. 106): `m(b - a) ≤ L(f, P) ≤ S(f, P) ≤ U(f, P) ≤ M(b - a)` for any
explicit lower/upper bounds `m ≤ f(x) ≤ M` on `[a, b]`. -/
theorem darboux_sum_bounds {a b m M : ℝ} {f : ℝ → ℝ} (P : IntervalPartition a b)
    (hlow : ∀ x ∈ Set.Icc a b, m ≤ f x) (hhigh : ∀ x ∈ Set.Icc a b, f x ≤ M) :
    m * (b - a) ≤ lowerDarbouxSum f P ∧
    lowerDarbouxSum f P ≤ partitionRiemannSum f P ∧
    partitionRiemannSum f P ≤ upperDarbouxSum f P ∧
    upperDarbouxSum f P ≤ M * (b - a) := by
  have hb_below : ∀ k < P.n, BddBelow (f '' Set.Icc (P.pts k) (P.pts (k + 1))) := by
    intro k hk
    refine ⟨m, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hlow x (P.subinterval_subset_Icc hk hx)
  have hb_above : ∀ k < P.n, BddAbove (f '' Set.Icc (P.pts k) (P.pts (k + 1))) := by
    intro k hk
    refine ⟨M, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hhigh x (P.subinterval_subset_Icc hk hx)
  have hne : ∀ k < P.n, (f '' Set.Icc (P.pts k) (P.pts (k + 1))).Nonempty := fun k hk ↦
    ⟨f (P.pts k), P.pts k, ⟨le_rfl, P.mono k hk⟩, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc m * (b - a)
        = ∑ k ∈ Finset.range P.n, m * (P.pts (k + 1) - P.pts k) := by
          rw [← Finset.mul_sum, P.sum_widths]
      _ ≤ lowerDarbouxSum f P := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          have hk' := Finset.mem_range.1 hk
          refine mul_le_mul_of_nonneg_right (le_csInf (hne k hk') ?_) (P.width_nonneg hk')
          rintro _ ⟨x, hx, rfl⟩
          exact hlow x (P.subinterval_subset_Icc hk' hx)
  · refine Finset.sum_le_sum fun k hk ↦ ?_
    have hk' := Finset.mem_range.1 hk
    exact mul_le_mul_of_nonneg_right
      (csInf_le (hb_below k hk') ⟨P.pts k, ⟨le_rfl, P.mono k hk'⟩, rfl⟩) (P.width_nonneg hk')
  · refine Finset.sum_le_sum fun k hk ↦ ?_
    have hk' := Finset.mem_range.1 hk
    exact mul_le_mul_of_nonneg_right
      (le_csSup (hb_above k hk') ⟨P.pts k, ⟨le_rfl, P.mono k hk'⟩, rfl⟩) (P.width_nonneg hk')
  · calc upperDarbouxSum f P
        ≤ ∑ k ∈ Finset.range P.n, M * (P.pts (k + 1) - P.pts k) := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          have hk' := Finset.mem_range.1 hk
          refine mul_le_mul_of_nonneg_right (csSup_le (hne k hk') ?_) (P.width_nonneg hk')
          rintro _ ⟨x, hx, rfl⟩
          exact hhigh x (P.subinterval_subset_Icc hk' hx)
      _ = M * (b - a) := by rw [← Finset.mul_sum, P.sum_widths]

/-- Refinement monotonicity: if every partition point of `P` is a partition point of `Q`, then
`L(f, P) ≤ L(f, Q)` and `U(f, Q) ≤ U(f, P)`. -/
theorem darboux_sum_refinement {a b : ℝ} {f : ℝ → ℝ}
    (hbdd_below : BddBelow (f '' Set.Icc a b)) (hbdd_above : BddAbove (f '' Set.Icc a b))
    (P Q : IntervalPartition a b)
    (href : ∀ k ≤ P.n, ∃ j ≤ Q.n, Q.pts j = P.pts k) :
    lowerDarbouxSum f P ≤ lowerDarbouxSum f Q ∧ upperDarbouxSum f Q ≤ upperDarbouxSum f P := by
  by_cases hPn : 0 < P.n
  · have hex_ge : ∀ k < P.n, ∃ j : ℕ, j ≤ Q.n ∧ P.pts k ≤ Q.pts j := by
      intro k hk
      obtain ⟨j, hj, hjeq⟩ := href k hk.le
      exact ⟨j, hj, hjeq.symm.le⟩
    let idx : ℕ → ℕ := fun k ↦ if hk : k < P.n then Nat.find (hex_ge k hk) else Q.n
    have hidx_le : ∀ k, idx k ≤ Q.n := by
      intro k
      by_cases hk : k < P.n
      · simp only [idx, hk, ↓reduceDIte]
        exact (Nat.find_spec (hex_ge k hk)).1
      · simp [idx, hk]
    have hidx_eq : ∀ k ≤ P.n, Q.pts (idx k) = P.pts k := by
      intro k hk
      rcases eq_or_lt_of_le hk with rfl | hlt
      · simp [idx, Q.pts_last, P.pts_last]
      · simp only [idx, hlt, ↓reduceDIte]
        have hspec := Nat.find_spec (hex_ge k hlt)
        obtain ⟨j₀, hj₀_le, hj₀_eq⟩ := href k hk
        have hmin : Nat.find (hex_ge k hlt) ≤ j₀ :=
          Nat.find_min' (hex_ge k hlt) ⟨hj₀_le, hj₀_eq.symm.le⟩
        exact le_antisymm ((Q.pts_le_pts hmin hj₀_le).trans_eq hj₀_eq) hspec.2
    have hidx_zero : idx 0 = 0 := by
      simp only [idx, hPn, ↓reduceDIte]
      exact Nat.eq_zero_of_le_zero (Nat.find_min' (hex_ge 0 hPn)
        ⟨Nat.zero_le Q.n, by rw [P.pts_zero, Q.pts_zero]⟩)
    have hidx_last : idx P.n = Q.n := by simp [idx]
    have hidx_mono : ∀ k, idx k ≤ idx (k + 1) := by
      intro k
      by_cases hk1 : k + 1 < P.n
      · have hk0 : k < P.n := Nat.lt_of_succ_lt hk1
        simp only [idx, hk0, hk1, ↓reduceDIte]
        have hspec1 := Nat.find_spec (hex_ge (k + 1) hk1)
        exact Nat.find_min' (hex_ge k hk0)
          ⟨hspec1.1, (P.mono k hk0).trans hspec1.2⟩
      · simp only [idx, hk1, ↓reduceDIte]
        exact hidx_le k
    have hsub_Ico : ∀ k < P.n, ∀ j ∈ Finset.Ico (idx k) (idx (k + 1)),
        j < Q.n ∧ Set.Icc (Q.pts j) (Q.pts (j + 1)) ⊆ Set.Icc (P.pts k) (P.pts (k + 1)) := by
      intro k hk j hj
      have hj_mem := Finset.mem_Ico.1 hj
      have hj_lt : j < Q.n := hj_mem.2.trans_le (hidx_le (k + 1))
      refine ⟨hj_lt, Set.Icc_subset_Icc ?_ ?_⟩
      · rw [← hidx_eq k hk.le]
        exact Q.pts_le_pts hj_mem.1 hj_lt.le
      · rw [← hidx_eq (k + 1) (Nat.succ_le_of_lt hk)]
        exact Q.pts_le_pts (Nat.succ_le_of_lt hj_mem.2) (hidx_le (k + 1))
    have hwidth_Ico : ∀ k < P.n,
        ∑ j ∈ Finset.Ico (idx k) (idx (k + 1)), (Q.pts (j + 1) - Q.pts j) =
          P.pts (k + 1) - P.pts k := by
      intro k hk
      rw [Finset.sum_Ico_sub Q.pts (hidx_mono k),
          hidx_eq (k + 1) (Nat.succ_le_of_lt hk), hidx_eq k hk.le]
    refine ⟨?_, ?_⟩
    · unfold lowerDarbouxSum
      rw [← hidx_last, sum_range_split_mono hidx_zero hidx_mono]
      refine Finset.sum_le_sum fun k hk ↦ ?_
      have hk' := Finset.mem_range.1 hk
      rw [← hwidth_Ico k hk', Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj ↦ ?_
      obtain ⟨hj_lt, hj_sub⟩ := hsub_Ico k hk' j hj
      have hneQ : (f '' Set.Icc (Q.pts j) (Q.pts (j + 1))).Nonempty :=
        ⟨f (Q.pts j), Q.pts j, ⟨le_rfl, Q.mono j hj_lt⟩, rfl⟩
      have hbddP : BddBelow (f '' Set.Icc (P.pts k) (P.pts (k + 1))) :=
        hbdd_below.mono (Set.image_mono (P.subinterval_subset_Icc hk'))
      exact mul_le_mul_of_nonneg_right
        (csInf_le_csInf hbddP hneQ (Set.image_mono hj_sub)) (Q.width_nonneg hj_lt)
    · unfold upperDarbouxSum
      rw [← hidx_last, sum_range_split_mono hidx_zero hidx_mono]
      refine Finset.sum_le_sum fun k hk ↦ ?_
      have hk' := Finset.mem_range.1 hk
      rw [← hwidth_Ico k hk', Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj ↦ ?_
      obtain ⟨hj_lt, hj_sub⟩ := hsub_Ico k hk' j hj
      have hneQ : (f '' Set.Icc (Q.pts j) (Q.pts (j + 1))).Nonempty :=
        ⟨f (Q.pts j), Q.pts j, ⟨le_rfl, Q.mono j hj_lt⟩, rfl⟩
      have hbddP : BddAbove (f '' Set.Icc (P.pts k) (P.pts (k + 1))) :=
        hbdd_above.mono (Set.image_mono (P.subinterval_subset_Icc hk'))
      exact mul_le_mul_of_nonneg_right
        (csSup_le_csSup hbddP hneQ (Set.image_mono hj_sub)) (Q.width_nonneg hj_lt)
  · have hPn0 : P.n = 0 := Nat.eq_zero_of_not_pos hPn
    have hab_eq : a = b := P.pts_zero.symm.trans (hPn0 ▸ P.pts_last)
    have hQwidth : ∀ j < Q.n, Q.pts (j + 1) - Q.pts j = 0 := by
      intro j hj
      have h1 := Q.pts_mem_Icc hj.le
      have h2 := Q.pts_mem_Icc (Nat.succ_le_of_lt hj)
      linarith [h1.1, h1.2, h2.1, h2.2]
    have hLP : lowerDarbouxSum f P = 0 := by simp [lowerDarbouxSum, hPn0]
    have hUP : upperDarbouxSum f P = 0 := by simp [upperDarbouxSum, hPn0]
    have hLQ : lowerDarbouxSum f Q = 0 :=
      Finset.sum_eq_zero fun j hj ↦ by rw [hQwidth j (Finset.mem_range.1 hj), mul_zero]
    have hUQ : upperDarbouxSum f Q = 0 :=
      Finset.sum_eq_zero fun j hj ↦ by rw [hQwidth j (Finset.mem_range.1 hj), mul_zero]
    simp [hLP, hUP, hLQ, hUQ]

/-- Goldblatt §9.1 (p. 106): Every lower Darboux sum is `≤` every upper Darboux sum:
`L_a^b(f, P₁) ≤ U_a^b(f, P₂)`. -/
theorem lowerDarbouxSum_le_upperDarbouxSum {a b : ℝ} {f : ℝ → ℝ}
    (hbdd_below : BddBelow (f '' Set.Icc a b)) (hbdd_above : BddAbove (f '' Set.Icc a b))
    (P₁ P₂ : IntervalPartition a b) :
    lowerDarbouxSum f P₁ ≤ upperDarbouxSum f P₂ := by
  let Q := IntervalPartition.commonRefinement P₁ P₂
  have h1 := (darboux_sum_refinement hbdd_below hbdd_above P₁ Q
    fun _ hk ↦ IntervalPartition.exists_pts_commonRefinement_left P₁ P₂ hk).1
  have h2 := (darboux_sum_refinement hbdd_below hbdd_above P₂ Q
    fun _ hk ↦ IntervalPartition.exists_pts_commonRefinement_right P₁ P₂ hk).2
  rcases hbdd_below with ⟨m, hm⟩
  rcases hbdd_above with ⟨M, hM⟩
  have hmid : lowerDarbouxSum f Q ≤ upperDarbouxSum f Q := by
    have hb := darboux_sum_bounds Q (fun x hx ↦ hm ⟨x, hx, rfl⟩) (fun x hx ↦ hM ⟨x, hx, rfl⟩)
    exact hb.2.1.trans hb.2.2.1
  exact (h1.trans hmid).trans h2

/-- Goldblatt §9.1 (p. 106): `f` is Darboux/Riemann integrable on `[a, b]` with integral `I` if `f`
is bounded on `[a, b]` and `I` is simultaneously the `IsLUB` of all lower sums `L_a^b(f, P)` and the
`IsGLB` of all upper sums `U_a^b(f, P)`. -/
def IsDarbouxIntegrableOn (f : ℝ → ℝ) (a b : ℝ) (I : ℝ) : Prop :=
  a ≤ b ∧ BddBelow (f '' Set.Icc a b) ∧ BddAbove (f '' Set.Icc a b) ∧
  IsLUB {L : ℝ | ∃ P : IntervalPartition a b, L = lowerDarbouxSum f P} I ∧
  IsGLB {U : ℝ | ∃ P : IntervalPartition a b, U = upperDarbouxSum f P} I

/-- Goldblatt §9.1 (p. 106, conditions (1) and (2)): `IsDarbouxIntegrableOn f a b I` holds iff
(1) `L_a^b(f, P) ≤ I ≤ U_a^b(f, P)` for all partitions `P`, and
(2) for every real `ε > 0` there is a partition `P` with `U_a^b(f, P) - L_a^b(f, P) < ε`. -/
theorem isDarbouxIntegrableOn_iff_eps {f : ℝ → ℝ} {a b I : ℝ} :
    IsDarbouxIntegrableOn f a b I ↔
      a ≤ b ∧ BddBelow (f '' Set.Icc a b) ∧ BddAbove (f '' Set.Icc a b) ∧
      (∀ P : IntervalPartition a b, lowerDarbouxSum f P ≤ I ∧ I ≤ upperDarbouxSum f P) ∧
      (∀ ε : ℝ, 0 < ε → ∃ P : IntervalPartition a b,
        upperDarbouxSum f P - lowerDarbouxSum f P < ε) := by
  constructor
  · rintro ⟨hab, hbel, habv, hlub, hglb⟩
    refine ⟨hab, hbel, habv, fun P ↦ ⟨hlub.1 ⟨P, rfl⟩, hglb.1 ⟨P, rfl⟩⟩, fun ε hε ↦ ?_⟩
    have hneL : ({L : ℝ | ∃ P : IntervalPartition a b, L = lowerDarbouxSum f P}).Nonempty :=
      ⟨lowerDarbouxSum f (IntervalPartition.single a b hab), IntervalPartition.single a b hab, rfl⟩
    have hneU : ({U : ℝ | ∃ P : IntervalPartition a b, U = upperDarbouxSum f P}).Nonempty :=
      ⟨upperDarbouxSum f (IntervalPartition.single a b hab), IntervalPartition.single a b hab, rfl⟩
    obtain ⟨L₀, ⟨P₁, rfl⟩, hL₀⟩ := exists_lt_of_lt_csSup hneL (by linarith [hlub.csSup_eq hneL] :
      I - ε / 2 < sSup {L : ℝ | ∃ P : IntervalPartition a b, L = lowerDarbouxSum f P})
    obtain ⟨U₀, ⟨P₂, rfl⟩, hU₀⟩ := exists_lt_of_csInf_lt hneU (by linarith [hglb.csInf_eq hneU] :
      sInf {U : ℝ | ∃ P : IntervalPartition a b, U = upperDarbouxSum f P} < I + ε / 2)
    let Q := IntervalPartition.commonRefinement P₁ P₂
    have h1 := (darboux_sum_refinement hbel habv P₁ Q
      fun _ hk ↦ IntervalPartition.exists_pts_commonRefinement_left P₁ P₂ hk).1
    have h2 := (darboux_sum_refinement hbel habv P₂ Q
      fun _ hk ↦ IntervalPartition.exists_pts_commonRefinement_right P₁ P₂ hk).2
    exact ⟨Q, by linarith⟩
  · rintro ⟨hab, hbel, habv, hbounds, heps⟩
    refine ⟨hab, hbel, habv, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rintro _ ⟨P, rfl⟩
      exact (hbounds P).1
    · intro M hM
      by_contra hlt
      push Not at hlt
      obtain ⟨P, hP⟩ := heps (I - M) (sub_pos.2 hlt)
      have hLP : lowerDarbouxSum f P ≤ M := hM ⟨P, rfl⟩
      have hUP : I ≤ upperDarbouxSum f P := (hbounds P).2
      linarith
    · rintro _ ⟨P, rfl⟩
      exact (hbounds P).2
    · intro m hm
      by_contra hgt
      push Not at hgt
      obtain ⟨P, hP⟩ := heps (m - I) (sub_pos.2 hgt)
      have hUP : m ≤ upperDarbouxSum f P := hm ⟨P, rfl⟩
      have hLP : lowerDarbouxSum f P ≤ I := (hbounds P).1
      linarith

/-- Goldblatt §9.1 (p. 106): Step-size partition `P_{Δx}` of `[a, b]` into `n = ⌈(b - a)/Δx⌉₊`
subintervals of width `Δx` together with a last subinterval `[x_{n-1}, b]` of width `≤ Δx`. -/
def stepPartition (a b : ℝ) (hab : a ≤ b) (dx : ℝ) (hdx : 0 < dx) : IntervalPartition a b where
  n := ⌈(b - a) / dx⌉₊
  pts k := min (a + (k : ℝ) * dx) b
  pts_zero := by simp [hab]
  pts_last := by
    have hceil : (b - a) / dx ≤ (⌈(b - a) / dx⌉₊ : ℝ) := Nat.le_ceil _
    have hmul : b - a ≤ (⌈(b - a) / dx⌉₊ : ℝ) * dx := (div_le_iff₀ hdx).1 hceil
    exact min_eq_right (by linarith)
  mono k _ := min_le_min_right b
    (by nlinarith [show (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) by exact_mod_cast Nat.le_succ k])

/-- For `k < (stepPartition a b hab dx hdx).n`, the `k`-th step-partition point is `a + k * dx`. -/
theorem stepPartition_pts_of_lt {a b dx : ℝ} (hab : a ≤ b) (hdx : 0 < dx) {k : ℕ}
    (hk : k < (stepPartition a b hab dx hdx).n) :
    (stepPartition a b hab dx hdx).pts k = a + (k : ℝ) * dx := by
  have hlt : (k : ℝ) < (b - a) / dx := Nat.lt_ceil.1 hk
  have hmul : (k : ℝ) * dx < b - a := (lt_div_iff₀ hdx).1 hlt
  exact min_eq_left (by linarith)

/-- Every subinterval of `stepPartition a b hab dx hdx` has width at most `dx`. -/
theorem stepPartition_width_le {a b dx : ℝ} (hab : a ≤ b) (hdx : 0 < dx) {k : ℕ}
    (hk : k < (stepPartition a b hab dx hdx).n) :
    (stepPartition a b hab dx hdx).pts (k + 1) - (stepPartition a b hab dx hdx).pts k ≤ dx := by
  rw [stepPartition_pts_of_lt hab hdx hk]
  change min (a + ((k + 1 : ℕ) : ℝ) * dx) b - (a + (k : ℝ) * dx) ≤ dx
  have hmin : min (a + ((k + 1 : ℕ) : ℝ) * dx) b ≤ a + ((k + 1 : ℕ) : ℝ) * dx := min_le_left _ _
  have hcast : ((k + 1 : ℕ) : ℝ) * dx = (k : ℝ) * dx + dx := by push_cast; ring
  linarith

open Classical in
/-- Goldblatt §9.1 (p. 106): Upper step-size Riemann sum `U_a^b(f, Δx)` for `Δx ∈ ℝ`. -/
def stepUpperSum (f : ℝ → ℝ) (a b : ℝ) (dx : ℝ) : ℝ :=
  if h : a ≤ b ∧ 0 < dx then upperDarbouxSum f (stepPartition a b h.1 dx h.2) else 0

open Classical in
/-- Goldblatt §9.1 (p. 106): Lower step-size Riemann sum `L_a^b(f, Δx)` for `Δx ∈ ℝ`. -/
def stepLowerSum (f : ℝ → ℝ) (a b : ℝ) (dx : ℝ) : ℝ :=
  if h : a ≤ b ∧ 0 < dx then lowerDarbouxSum f (stepPartition a b h.1 dx h.2) else 0

open Classical in
/-- Goldblatt §9.1 (p. 106): Ordinary step-size Riemann sum `S_a^b(f, Δx)` for `Δx ∈ ℝ`. -/
def stepRiemannSum (f : ℝ → ℝ) (a b : ℝ) (dx : ℝ) : ℝ :=
  if h : a ≤ b ∧ 0 < dx then partitionRiemannSum f (stepPartition a b h.1 dx h.2) else 0

/-- Unfolding `stepUpperSum` when `a ≤ b` and `0 < dx`. -/
theorem stepUpperSum_of_pos (f : ℝ → ℝ) {a b dx : ℝ} (hab : a ≤ b) (hdx : 0 < dx) :
    stepUpperSum f a b dx = upperDarbouxSum f (stepPartition a b hab dx hdx) := by
  simp [stepUpperSum, hab, hdx]

/-- Unfolding `stepLowerSum` when `a ≤ b` and `0 < dx`. -/
theorem stepLowerSum_of_pos (f : ℝ → ℝ) {a b dx : ℝ} (hab : a ≤ b) (hdx : 0 < dx) :
    stepLowerSum f a b dx = lowerDarbouxSum f (stepPartition a b hab dx hdx) := by
  simp [stepLowerSum, hab, hdx]

/-- Unfolding `stepRiemannSum` when `a ≤ b` and `0 < dx`. -/
theorem stepRiemannSum_of_pos (f : ℝ → ℝ) {a b dx : ℝ} (hab : a ≤ b) (hdx : 0 < dx) :
    stepRiemannSum f a b dx = partitionRiemannSum f (stepPartition a b hab dx hdx) := by
  simp [stepRiemannSum, hab, hdx]

/-- Goldblatt §9.1 (p. 106): Hyperreal extension `U_a^b(f, Δx)` (`Δx ∈ ℝ*`) via `starFun`. -/
def hyperStepUpperSum (f : ℝ → ℝ) (a b : ℝ) (dx : ℝ*) : ℝ* :=
  starFun (stepUpperSum f a b) dx

/-- Goldblatt §9.1 (p. 106): Hyperreal extension `L_a^b(f, Δx)` (`Δx ∈ ℝ*`) via `starFun`. -/
def hyperStepLowerSum (f : ℝ → ℝ) (a b : ℝ) (dx : ℝ*) : ℝ* :=
  starFun (stepLowerSum f a b) dx

/-- Goldblatt §9.1 (p. 106): Hyperreal extension `S_a^b(f, Δx)` (`Δx ∈ ℝ*`) via `starFun`. -/
def hyperStepSum (f : ℝ → ℝ) (a b : ℝ) (dx : ℝ*) : ℝ* :=
  starFun (stepRiemannSum f a b) dx

/-- Degenerate-interval step-size sums vanish identically on `[a, a]`. -/
@[simp]
theorem stepSums_self (f : ℝ → ℝ) (a dx : ℝ) :
    stepUpperSum f a a dx = 0 ∧ stepLowerSum f a a dx = 0 ∧ stepRiemannSum f a a dx = 0 := by
  by_cases hdx : 0 < dx
  · have hn : (stepPartition a a le_rfl dx hdx).n = 0 := by simp [stepPartition]
    simp [stepUpperSum_of_pos f le_rfl hdx, stepLowerSum_of_pos f le_rfl hdx,
      stepRiemannSum_of_pos f le_rfl hdx, upperDarbouxSum, lowerDarbouxSum,
      partitionRiemannSum, hn]
  · simp [stepUpperSum, stepLowerSum, stepRiemannSum, hdx]

/-- Goldblatt §9.1 (p. 106): Transfer of `m(b - a) ≤ L(f, Δx) ≤ S(f, Δx) ≤ U(f, Δx) ≤ M(b - a)`
to all positive hyperreals `Δx > 0`. -/
theorem hyperStepSum_bounds {a b m M : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hlow : ∀ x ∈ Set.Icc a b, m ≤ f x) (hhigh : ∀ x ∈ Set.Icc a b, f x ≤ M)
    {dx : ℝ*} (hdx : 0 < dx) :
    ((m * (b - a) : ℝ) : ℝ*) ≤ hyperStepLowerSum f a b dx ∧
    hyperStepLowerSum f a b dx ≤ hyperStepSum f a b dx ∧
    hyperStepSum f a b dx ≤ hyperStepUpperSum f a b dx ∧
    hyperStepUpperSum f a b dx ≤ ((M * (b - a) : ℝ) : ℝ*) := by
  rcases ofSeq_surjective dx with ⟨s, rfl⟩
  have hs : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < s j := ofSeq_lt_ofSeq.1 hdx
  refine ⟨ofSeq_le_ofSeq.2 ?_, ofSeq_le_ofSeq.2 ?_, ofSeq_le_ofSeq.2 ?_, ofSeq_le_ofSeq.2 ?_⟩
  · refine hs.mono fun j hj ↦ ?_
    change m * (b - a) ≤ stepLowerSum f a b (s j)
    rw [stepLowerSum_of_pos f hab hj]
    exact (darboux_sum_bounds _ hlow hhigh).1
  · refine hs.mono fun j hj ↦ ?_
    change stepLowerSum f a b (s j) ≤ stepRiemannSum f a b (s j)
    rw [stepLowerSum_of_pos f hab hj, stepRiemannSum_of_pos f hab hj]
    exact (darboux_sum_bounds _ hlow hhigh).2.1
  · refine hs.mono fun j hj ↦ ?_
    change stepRiemannSum f a b (s j) ≤ stepUpperSum f a b (s j)
    rw [stepRiemannSum_of_pos f hab hj, stepUpperSum_of_pos f hab hj]
    exact (darboux_sum_bounds _ hlow hhigh).2.2.1
  · refine hs.mono fun j hj ↦ ?_
    change stepUpperSum f a b (s j) ≤ M * (b - a)
    rw [stepUpperSum_of_pos f hab hj]
    exact (darboux_sum_bounds _ hlow hhigh).2.2.2

/-- Goldblatt §9.1 (p. 106): Transfer of `L_a^b(f, Δx) ≤ U_a^b(f, Δy)` to all positive
hyperreals `Δx, Δy > 0`. -/
theorem hyperStepLowerSum_le_hyperStepUpperSum {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hbdd_below : BddBelow (f '' Set.Icc a b)) (hbdd_above : BddAbove (f '' Set.Icc a b))
    {dx dy : ℝ*} (hdx : 0 < dx) (hdy : 0 < dy) :
    hyperStepLowerSum f a b dx ≤ hyperStepUpperSum f a b dy := by
  rcases ofSeq_surjective dx with ⟨s, rfl⟩
  rcases ofSeq_surjective dy with ⟨t, rfl⟩
  have hs : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < s j := ofSeq_lt_ofSeq.1 hdx
  have ht : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < t j := ofSeq_lt_ofSeq.1 hdy
  refine ofSeq_le_ofSeq.2 ((hs.and ht).mono fun j ⟨hjs, hjt⟩ ↦ ?_)
  change stepLowerSum f a b (s j) ≤ stepUpperSum f a b (t j)
  rw [stepLowerSum_of_pos f hab hjs, stepUpperSum_of_pos f hab hjt]
  exact lowerDarbouxSum_le_upperDarbouxSum hbdd_below hbdd_above _ _

/-- Goldblatt Theorem 9.1.1 (pp. 107–108), real oscillation witness before transfer:
for continuous `f` on `[a, b]` (`a ≤ b`) and real `Δx > 0`, there exist `c(Δx), d(Δx) ∈ [a, b]`
such that `|c(Δx) - d(Δx)| ≤ Δx` and
`0 ≤ U_a^b(f, Δx) - L_a^b(f, Δx) ≤ (f(c(Δx)) - f(d(Δx)))(b - a)`. -/
theorem exists_oscillation_witness_stepSum {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ c d : ℝ → ℝ, ∀ dx : ℝ, 0 < dx →
      c dx ∈ Set.Icc a b ∧ d dx ∈ Set.Icc a b ∧
      |c dx - d dx| ≤ dx ∧
      0 ≤ stepUpperSum f a b dx - stepLowerSum f a b dx ∧
      stepUpperSum f a b dx - stepLowerSum f a b dx ≤ (f (c dx) - f (d dx)) * (b - a) := by
  have hex : ∀ dx : ℝ, ∃ cp dp : ℝ,
      (0 < dx → cp ∈ Set.Icc a b ∧ dp ∈ Set.Icc a b ∧ |cp - dp| ≤ dx ∧
        0 ≤ stepUpperSum f a b dx - stepLowerSum f a b dx ∧
        stepUpperSum f a b dx - stepLowerSum f a b dx ≤ (f cp - f dp) * (b - a)) := by
    intro dx
    by_cases hdx : 0 < dx
    · rcases eq_or_lt_of_le hab with rfl | hlt
      · refine ⟨a, a, fun _ ↦ ?_⟩
        simp [hdx.le]
      · let P := stepPartition a b hab dx hdx
        have hPn : 0 < P.n := Nat.ceil_pos.2 (div_pos (sub_pos.2 hlt) hdx)
        have hsub_ext : ∀ k < P.n, ∃ ck dk : ℝ,
            ck ∈ Set.Icc (P.pts k) (P.pts (k + 1)) ∧
            dk ∈ Set.Icc (P.pts k) (P.pts (k + 1)) ∧
            f ck = sSup (f '' Set.Icc (P.pts k) (P.pts (k + 1))) ∧
            f dk = sInf (f '' Set.Icc (P.pts k) (P.pts (k + 1))) := by
          intro k hk
          have hne : (Set.Icc (P.pts k) (P.pts (k + 1))).Nonempty := ⟨P.pts k, le_rfl, P.mono k hk⟩
          have hcont : ContinuousOn f (Set.Icc (P.pts k) (P.pts (k + 1))) :=
            hf.mono (P.subinterval_subset_Icc hk)
          obtain ⟨ck, hck_mem, hck_max⟩ := isCompact_Icc.exists_isMaxOn hne hcont
          obtain ⟨dk, hdk_mem, hdk_min⟩ := isCompact_Icc.exists_isMinOn hne hcont
          have hbdd_abv : BddAbove (f '' Set.Icc (P.pts k) (P.pts (k + 1))) :=
            ⟨f ck, by rintro _ ⟨x, hx, rfl⟩; exact hck_max hx⟩
          have hbdd_bel : BddBelow (f '' Set.Icc (P.pts k) (P.pts (k + 1))) :=
            ⟨f dk, by rintro _ ⟨x, hx, rfl⟩; exact hdk_min hx⟩
          have hsup : f ck = sSup (f '' Set.Icc (P.pts k) (P.pts (k + 1))) :=
            le_antisymm (le_csSup hbdd_abv ⟨ck, hck_mem, rfl⟩)
              (csSup_le ⟨f ck, ck, hck_mem, rfl⟩ (by rintro _ ⟨x, hx, rfl⟩; exact hck_max hx))
          have hinf : f dk = sInf (f '' Set.Icc (P.pts k) (P.pts (k + 1))) :=
            le_antisymm
              (le_csInf ⟨f dk, dk, hdk_mem, rfl⟩ fun _ ⟨x, hx, hfx⟩ ↦ hfx ▸ hdk_min hx)
              (csInf_le hbdd_bel ⟨dk, hdk_mem, rfl⟩)
          exact ⟨ck, dk, hck_mem, hdk_mem, hsup, hinf⟩
        let cSub : ℕ → ℝ := fun k ↦ if hk : k < P.n then (hsub_ext k hk).choose else a
        let dSub : ℕ → ℝ := fun k ↦
          if hk : k < P.n then (hsub_ext k hk).choose_spec.choose else a
        have hcSub_spec : ∀ k (hk : k < P.n),
            cSub k ∈ Set.Icc (P.pts k) (P.pts (k + 1)) ∧
            dSub k ∈ Set.Icc (P.pts k) (P.pts (k + 1)) ∧
            f (cSub k) = sSup (f '' Set.Icc (P.pts k) (P.pts (k + 1))) ∧
            f (dSub k) = sInf (f '' Set.Icc (P.pts k) (P.pts (k + 1))) := by
          intro k hk
          simp only [cSub, dSub, hk, ↓reduceDIte]
          exact (hsub_ext k hk).choose_spec.choose_spec
        obtain ⟨k₀, hk₀_mem, hk₀_max⟩ :=
          Finset.exists_max_image (Finset.range P.n) (fun k ↦ f (cSub k) - f (dSub k))
            (Finset.nonempty_range_iff.2 hPn.ne')
        have hk₀ : k₀ < P.n := Finset.mem_range.1 hk₀_mem
        obtain ⟨hck₀, hdk₀, _, _⟩ := hcSub_spec k₀ hk₀
        refine ⟨cSub k₀, dSub k₀, fun _ ↦ ⟨P.subinterval_subset_Icc hk₀ hck₀,
          P.subinterval_subset_Icc hk₀ hdk₀, ?_, ?_, ?_⟩⟩
        · have hw : P.pts (k₀ + 1) - P.pts k₀ ≤ dx := stepPartition_width_le hab hdx hk₀
          rw [abs_le]
          exact ⟨by linarith [hck₀.1, hdk₀.2], by linarith [hck₀.2, hdk₀.1]⟩
        · rw [stepUpperSum_of_pos f hab hdx, stepLowerSum_of_pos f hab hdx]
          have hne_ab : (Set.Icc a b).Nonempty := ⟨a, le_rfl, hab⟩
          obtain ⟨xm, _, hxm⟩ := isCompact_Icc.exists_isMinOn hne_ab hf
          obtain ⟨xM, _, hxM⟩ := isCompact_Icc.exists_isMaxOn hne_ab hf
          have hb := darboux_sum_bounds P hxm hxM
          linarith [hb.2.1, hb.2.2.1]
        · rw [stepUpperSum_of_pos f hab hdx, stepLowerSum_of_pos f hab hdx]
          change upperDarbouxSum f P - lowerDarbouxSum f P ≤ _
          unfold upperDarbouxSum lowerDarbouxSum
          rw [← Finset.sum_sub_distrib]
          calc ∑ k ∈ Finset.range P.n,
                (sSup (f '' Set.Icc (P.pts k) (P.pts (k + 1))) * (P.pts (k + 1) - P.pts k) -
                 sInf (f '' Set.Icc (P.pts k) (P.pts (k + 1))) * (P.pts (k + 1) - P.pts k))
              = ∑ k ∈ Finset.range P.n,
                  (f (cSub k) - f (dSub k)) * (P.pts (k + 1) - P.pts k) := by
                refine Finset.sum_congr rfl fun k hk ↦ ?_
                obtain ⟨_, _, hsup, hinf⟩ := hcSub_spec k (Finset.mem_range.1 hk)
                rw [← hsup, ← hinf, sub_mul]
            _ ≤ ∑ k ∈ Finset.range P.n,
                  (f (cSub k₀) - f (dSub k₀)) * (P.pts (k + 1) - P.pts k) := by
                refine Finset.sum_le_sum fun k hk ↦ ?_
                exact mul_le_mul_of_nonneg_right (hk₀_max k hk)
                  (P.width_nonneg (Finset.mem_range.1 hk))
            _ = (f (cSub k₀) - f (dSub k₀)) * (b - a) := by
                rw [← Finset.mul_sum, P.sum_widths]
    · exact ⟨a, a, fun h ↦ (hdx h).elim⟩
  choose c d hcd using hex
  exact ⟨c, d, hcd⟩

/-- **Goldblatt Theorem 9.1.1** (pp. 107–108): If `f` is continuous on `[a, b]` (`a ≤ b`), then
for any positive infinitesimal `Δx`, `L_a^b(f, Δx) ≈ₕ U_a^b(f, Δx)`. -/
theorem hyperStepLowerSum_infClose_hyperStepUpperSum {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) {dx : ℝ*} (hdx : IsPosInfinitesimal dx) :
    hyperStepLowerSum f a b dx ≈ₕ hyperStepUpperSum f a b dx := by
  obtain ⟨c, d, hcd⟩ := exists_oscillation_witness_stepSum hab hf
  rcases ofSeq_surjective dx with ⟨s, rfl⟩
  have hs_pos : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < s j := ofSeq_lt_ofSeq.1 hdx.1
  let C : ℝ* := starFun c (ofSeq s)
  let D : ℝ* := starFun d (ofSeq s)
  have hC_mem : C ∈ Set.Icc (a : ℝ*) (b : ℝ*) := by
    rw [← starSet_Icc]
    exact ofSeq_mem_starSet.2 (hs_pos.mono fun j hj ↦ (hcd (s j) hj).1)
  have hD_mem : D ∈ Set.Icc (a : ℝ*) (b : ℝ*) := by
    rw [← starSet_Icc]
    exact ofSeq_mem_starSet.2 (hs_pos.mono fun j hj ↦ (hcd (s j) hj).2.1)
  have hCD_le : |C - D| ≤ ofSeq s :=
    ofSeq_le_ofSeq.2 (hs_pos.mono fun j hj ↦ (hcd (s j) hj).2.2.1)
  have hdx_inf : IsInfinitesimal (ofSeq s) := isInfinitesimal_iff_trichotomy.2 (Or.inl hdx)
  have hCD_close : C ≈ₕ D :=
    isInfinitesimal_of_abs_le hdx_inf (hCD_le.trans (le_abs_self _))
  have hfCD_close : starFun f C ≈ₕ starFun f D :=
    infClose_starFun_of_continuousOn_Icc hf hC_mem hD_mem hCD_close
  have hbound_inf : IsInfinitesimal ((starFun f C - starFun f D) * ((b - a : ℝ) : ℝ*)) :=
    hfCD_close.mul_isLimited (isLimited_coe (b - a))
  have hnonneg : 0 ≤ hyperStepUpperSum f a b (ofSeq s) - hyperStepLowerSum f a b (ofSeq s) :=
    ofSeq_le_ofSeq.2 (hs_pos.mono fun j hj ↦ (hcd (s j) hj).2.2.2.1)
  have hupper : hyperStepUpperSum f a b (ofSeq s) - hyperStepLowerSum f a b (ofSeq s) ≤
      (starFun f C - starFun f D) * ((b - a : ℝ) : ℝ*) :=
    ofSeq_le_ofSeq.2 (hs_pos.mono fun j hj ↦ (hcd (s j) hj).2.2.2.2)
  symm
  refine isInfinitesimal_of_abs_le hbound_inf ?_
  rw [abs_of_nonneg hnonneg]
  exact hupper.trans (le_abs_self _)

/-- **Goldblatt Exercise 9.1.2 (Part 1, p. 108)**: If `f` is nondecreasing on `[a, b]` (`a ≤ b`),
then for every real `Δx > 0`, `U_a^b(f, Δx) - L_a^b(f, Δx) ≤ Δx (f(b) - f(a))`. -/
theorem stepUpperSum_sub_stepLowerSum_le_of_monotoneOn {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Set.Icc a b)) {dx : ℝ} (hdx : 0 < dx) :
    stepUpperSum f a b dx - stepLowerSum f a b dx ≤ dx * (f b - f a) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  · rw [stepUpperSum_of_pos f hab hdx, stepLowerSum_of_pos f hab hdx]
    let P := stepPartition a b hab dx hdx
    change upperDarbouxSum f P - lowerDarbouxSum f P ≤ dx * (f b - f a)
    unfold upperDarbouxSum lowerDarbouxSum
    rw [← Finset.sum_sub_distrib]
    calc ∑ k ∈ Finset.range P.n,
          (sSup (f '' Set.Icc (P.pts k) (P.pts (k + 1))) * (P.pts (k + 1) - P.pts k) -
           sInf (f '' Set.Icc (P.pts k) (P.pts (k + 1))) * (P.pts (k + 1) - P.pts k))
        ≤ ∑ k ∈ Finset.range P.n, (f (P.pts (k + 1)) - f (P.pts k)) * dx := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          have hk' := Finset.mem_range.1 hk
          have hsub := P.subinterval_subset_Icc hk'
          have hne : (f '' Set.Icc (P.pts k) (P.pts (k + 1))).Nonempty :=
            ⟨f (P.pts k), P.pts k, ⟨le_rfl, P.mono k hk'⟩, rfl⟩
          have hsup : sSup (f '' Set.Icc (P.pts k) (P.pts (k + 1))) ≤ f (P.pts (k + 1)) :=
            csSup_le hne fun _ ⟨x, hx, hfx⟩ ↦
              hfx ▸ hf (hsub hx) (P.pts_mem_Icc (Nat.succ_le_of_lt hk')) hx.2
          have hinf : f (P.pts k) ≤ sInf (f '' Set.Icc (P.pts k) (P.pts (k + 1))) :=
            le_csInf hne fun _ ⟨x, hx, hfx⟩ ↦
              hfx ▸ hf (P.pts_mem_Icc hk'.le) (hsub hx) hx.1
          have hdiff_nn : 0 ≤ f (P.pts (k + 1)) - f (P.pts k) :=
            sub_nonneg.2 (hf (P.pts_mem_Icc hk'.le)
              (P.pts_mem_Icc (Nat.succ_le_of_lt hk')) (P.mono k hk'))
          rw [← sub_mul]
          exact mul_le_mul (by linarith) (stepPartition_width_le hab hdx hk')
            (P.width_nonneg hk') hdiff_nn
      _ = dx * ∑ k ∈ Finset.range P.n, (f (P.pts (k + 1)) - f (P.pts k)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
      _ = dx * (f b - f a) := by
          rw [Finset.sum_range_sub (fun k ↦ f (P.pts k)), P.pts_last, P.pts_zero]

/-- **Goldblatt Exercise 9.1.2 (Part 2, p. 108)**: If `f` is nonincreasing on `[a, b]` (`a ≤ b`),
then for every real `Δx > 0`, `U_a^b(f, Δx) - L_a^b(f, Δx) ≤ Δx (f(a) - f(b))`. -/
theorem stepUpperSum_sub_stepLowerSum_le_of_antitoneOn {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : AntitoneOn f (Set.Icc a b)) {dx : ℝ} (hdx : 0 < dx) :
    stepUpperSum f a b dx - stepLowerSum f a b dx ≤ dx * (f a - f b) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  · rw [stepUpperSum_of_pos f hab hdx, stepLowerSum_of_pos f hab hdx]
    let P := stepPartition a b hab dx hdx
    change upperDarbouxSum f P - lowerDarbouxSum f P ≤ dx * (f a - f b)
    unfold upperDarbouxSum lowerDarbouxSum
    rw [← Finset.sum_sub_distrib]
    calc ∑ k ∈ Finset.range P.n,
          (sSup (f '' Set.Icc (P.pts k) (P.pts (k + 1))) * (P.pts (k + 1) - P.pts k) -
           sInf (f '' Set.Icc (P.pts k) (P.pts (k + 1))) * (P.pts (k + 1) - P.pts k))
        ≤ ∑ k ∈ Finset.range P.n, (f (P.pts k) - f (P.pts (k + 1))) * dx := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          have hk' := Finset.mem_range.1 hk
          have hsub := P.subinterval_subset_Icc hk'
          have hne : (f '' Set.Icc (P.pts k) (P.pts (k + 1))).Nonempty :=
            ⟨f (P.pts k), P.pts k, ⟨le_rfl, P.mono k hk'⟩, rfl⟩
          have hsup : sSup (f '' Set.Icc (P.pts k) (P.pts (k + 1))) ≤ f (P.pts k) :=
            csSup_le hne fun _ ⟨x, hx, hfx⟩ ↦
              hfx ▸ hf (P.pts_mem_Icc hk'.le) (hsub hx) hx.1
          have hinf : f (P.pts (k + 1)) ≤ sInf (f '' Set.Icc (P.pts k) (P.pts (k + 1))) :=
            le_csInf hne fun _ ⟨x, hx, hfx⟩ ↦
              hfx ▸ hf (hsub hx) (P.pts_mem_Icc (Nat.succ_le_of_lt hk')) hx.2
          have hdiff_nn : 0 ≤ f (P.pts k) - f (P.pts (k + 1)) :=
            sub_nonneg.2 (hf (P.pts_mem_Icc hk'.le)
              (P.pts_mem_Icc (Nat.succ_le_of_lt hk')) (P.mono k hk'))
          rw [← sub_mul]
          exact mul_le_mul (by linarith) (stepPartition_width_le hab hdx hk')
            (P.width_nonneg hk') hdiff_nn
      _ = dx * ∑ k ∈ Finset.range P.n, -(f (P.pts (k + 1)) - f (P.pts k)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun _ _ ↦ by ring
      _ = dx * (f a - f b) := by
          rw [Finset.sum_neg_distrib, Finset.sum_range_sub (fun k ↦ f (P.pts k)),
            P.pts_last, P.pts_zero]
          ring

/-- Goldblatt Exercise 9.1.2 (p. 108): `f` is monotonic on `[a, b]` if it is nondecreasing or
nonincreasing on `[a, b]`. -/
def IsMonotonicOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  MonotoneOn f (Set.Icc a b) ∨ AntitoneOn f (Set.Icc a b)

/-- **Goldblatt Exercise 9.1.2 (Part 3, p. 108)**: Theorem 9.1.1 holds for monotonic functions:
if `f` is monotonic on `[a, b]` (`a ≤ b`), then `L_a^b(f, Δx) ≈ₕ U_a^b(f, Δx)` for every positive
infinitesimal `Δx`. -/
theorem hyperStepLowerSum_infClose_hyperStepUpperSum_of_monotonic {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf : IsMonotonicOn f a b) {dx : ℝ*} (hdx : IsPosInfinitesimal dx) :
    hyperStepLowerSum f a b dx ≈ₕ hyperStepUpperSum f a b dx := by
  have hdx_inf : IsInfinitesimal dx := isInfinitesimal_iff_trichotomy.2 (Or.inl hdx)
  rcases ofSeq_surjective dx with ⟨s, rfl⟩
  have hs : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < s j := ofSeq_lt_ofSeq.1 hdx.1
  rcases hf with hmono | hanti
  · have hbound := hyperStepSum_bounds hab
      (fun x hx ↦ hmono ⟨le_rfl, hab⟩ hx hx.1)
      (fun x hx ↦ hmono hx ⟨hab, le_rfl⟩ hx.2) hdx.1
    have hnn : 0 ≤ hyperStepUpperSum f a b (ofSeq s) - hyperStepLowerSum f a b (ofSeq s) := by
      linarith [hbound.2.1, hbound.2.2.1]
    have hle : hyperStepUpperSum f a b (ofSeq s) - hyperStepLowerSum f a b (ofSeq s) ≤
        ofSeq s * ((f b - f a : ℝ) : ℝ*) :=
      ofSeq_le_ofSeq.2 (hs.mono fun j hj ↦
        stepUpperSum_sub_stepLowerSum_le_of_monotoneOn hab hmono hj)
    have hinf := hdx_inf.mul_isLimited (isLimited_coe (f b - f a))
    symm
    refine isInfinitesimal_of_abs_le hinf ?_
    rw [abs_of_nonneg hnn]
    exact hle.trans (le_abs_self _)
  · have hbound := hyperStepSum_bounds hab
      (fun x hx ↦ hanti hx ⟨hab, le_rfl⟩ hx.2)
      (fun x hx ↦ hanti ⟨le_rfl, hab⟩ hx hx.1) hdx.1
    have hnn : 0 ≤ hyperStepUpperSum f a b (ofSeq s) - hyperStepLowerSum f a b (ofSeq s) := by
      linarith [hbound.2.1, hbound.2.2.1]
    have hle : hyperStepUpperSum f a b (ofSeq s) - hyperStepLowerSum f a b (ofSeq s) ≤
        ofSeq s * ((f a - f b : ℝ) : ℝ*) :=
      ofSeq_le_ofSeq.2 (hs.mono fun j hj ↦
        stepUpperSum_sub_stepLowerSum_le_of_antitoneOn hab hanti hj)
    have hinf := hdx_inf.mul_isLimited (isLimited_coe (f a - f b))
    symm
    refine isInfinitesimal_of_abs_le hinf ?_
    rw [abs_of_nonneg hnn]
    exact hle.trans (le_abs_self _)

/-! ## §9.2 The Integral as the Shadow of Riemann Sums -/

/-- Boundedness helper for continuous functions on `[a, b]`. -/
theorem bddBelow_bddAbove_of_continuousOn {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    BddBelow (f '' Set.Icc a b) ∧ BddAbove (f '' Set.Icc a b) :=
  ⟨(isCompact_Icc.image_of_continuousOn hf).bddBelow,
   (isCompact_Icc.image_of_continuousOn hf).bddAbove⟩

/-- Boundedness helper for monotonic functions on `[a, b]` (`a ≤ b`). -/
theorem bddBelow_bddAbove_of_isMonotonicOn {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : IsMonotonicOn f a b) :
    BddBelow (f '' Set.Icc a b) ∧ BddAbove (f '' Set.Icc a b) := by
  rcases hf with hmono | hanti
  · exact ⟨⟨f a, fun _ ⟨x, hx, hfx⟩ ↦ hfx ▸ hmono ⟨le_rfl, hab⟩ hx hx.1⟩,
           ⟨f b, fun _ ⟨x, hx, hfx⟩ ↦ hfx ▸ hmono hx ⟨hab, le_rfl⟩ hx.2⟩⟩
  · exact ⟨⟨f b, fun _ ⟨x, hx, hfx⟩ ↦ hfx ▸ hanti hx ⟨hab, le_rfl⟩ hx.2⟩,
           ⟨f a, fun _ ⟨x, hx, hfx⟩ ↦ hfx ▸ hanti ⟨le_rfl, hab⟩ hx hx.1⟩⟩

/-- Goldblatt §9.2 (p. 109): For `a ≤ b`, bounded `f` on `[a, b]`, and any positive hyperreal
`Δx > 0`, `L_a^b(f, Δx)`, `S_a^b(f, Δx)`, and `U_a^b(f, Δx)` are all limited. -/
theorem hyperStepSums_isLimited {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hbdd_below : BddBelow (f '' Set.Icc a b)) (hbdd_above : BddAbove (f '' Set.Icc a b))
    {dx : ℝ*} (hdx : 0 < dx) :
    IsLimited (hyperStepLowerSum f a b dx) ∧
    IsLimited (hyperStepSum f a b dx) ∧
    IsLimited (hyperStepUpperSum f a b dx) := by
  rcases hbdd_below with ⟨m, hm⟩
  rcases hbdd_above with ⟨M, hM⟩
  have hb := hyperStepSum_bounds hab
    (fun x hx ↦ hm ⟨x, hx, rfl⟩) (fun x hx ↦ hM ⟨x, hx, rfl⟩) hdx
  have h1 : (((m * (b - a) - 1 : ℝ)) : ℝ*) < ((m * (b - a) : ℝ) : ℝ*) :=
    Hyperreal.coe_lt_coe.2 (by linarith)
  have h2 : ((M * (b - a) : ℝ) : ℝ*) < (((M * (b - a) + 1 : ℝ)) : ℝ*) :=
    Hyperreal.coe_lt_coe.2 (by linarith)
  refine ⟨isLimited_iff_exists_real.2 ⟨m * (b - a) - 1, M * (b - a) + 1,
      h1.trans_le hb.1, (hb.2.1.trans (hb.2.2.1.trans hb.2.2.2)).trans_lt h2⟩,
    isLimited_iff_exists_real.2 ⟨m * (b - a) - 1, M * (b - a) + 1,
      h1.trans_le (hb.1.trans hb.2.1), (hb.2.2.1.trans hb.2.2.2).trans_lt h2⟩,
    isLimited_iff_exists_real.2 ⟨m * (b - a) - 1, M * (b - a) + 1,
      h1.trans_le (hb.1.trans (hb.2.1.trans hb.2.2.1)), hb.2.2.2.trans_lt h2⟩⟩

/-- Goldblatt §9.2 (p. 109): For `a ≤ b` and continuous `f` on `[a, b]`, `hyperStepSum f a b dx`
is limited for every `dx > 0` in `ℝ*`. -/
theorem hyperStepSum_isLimited_of_continuousOn {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) {dx : ℝ*} (hdx : 0 < dx) :
    IsLimited (hyperStepSum f a b dx) := by
  obtain ⟨hbel, habv⟩ := bddBelow_bddAbove_of_continuousOn hf
  exact (hyperStepSums_isLimited hab hbel habv hdx).2.1

/-- Goldblatt §9.2 (pp. 108–109): Whenever `L_a^b(f, Δx) ≈ₕ U_a^b(f, Δx)` for positive
infinitesimals, any two positive infinitesimals `Δx₁, Δx₂` produce infinitely close lower sums,
upper sums, and ordinary Riemann sums! -/
theorem hyperStepSums_infClose_of_oscillation {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hbdd_below : BddBelow (f '' Set.Icc a b)) (hbdd_above : BddAbove (f '' Set.Icc a b))
    (hOsc : ∀ dx : ℝ*, IsPosInfinitesimal dx →
      hyperStepLowerSum f a b dx ≈ₕ hyperStepUpperSum f a b dx)
    {dx₁ dx₂ : ℝ*} (hdx₁ : IsPosInfinitesimal dx₁) (hdx₂ : IsPosInfinitesimal dx₂) :
    hyperStepLowerSum f a b dx₁ ≈ₕ hyperStepLowerSum f a b dx₂ ∧
    hyperStepUpperSum f a b dx₁ ≈ₕ hyperStepUpperSum f a b dx₂ ∧
    hyperStepSum f a b dx₁ ≈ₕ hyperStepSum f a b dx₂ := by
  have hL₁U₂ : hyperStepLowerSum f a b dx₁ ≤ hyperStepUpperSum f a b dx₂ :=
    hyperStepLowerSum_le_hyperStepUpperSum hab hbdd_below hbdd_above hdx₁.1 hdx₂.1
  have hL₂U₁ : hyperStepLowerSum f a b dx₂ ≤ hyperStepUpperSum f a b dx₁ :=
    hyperStepLowerSum_le_hyperStepUpperSum hab hbdd_below hbdd_above hdx₂.1 hdx₁.1
  have hLU₁ := hOsc dx₁ hdx₁
  have hLU₂ := hOsc dx₂ hdx₂
  have hL₁L₂ : hyperStepLowerSum f a b dx₁ ≈ₕ hyperStepLowerSum f a b dx₂ := by
    rw [InfClose, ← infClose_zero_iff]
    refine infClose_of_le_of_le
      (u := hyperStepLowerSum f a b dx₁ - hyperStepUpperSum f a b dx₁)
      (v := hyperStepUpperSum f a b dx₂ - hyperStepLowerSum f a b dx₂)
      (by linarith) (by linarith) ?_ ?_
    · exact infClose_zero_iff.2 hLU₁
    · exact infClose_zero_iff.2 hLU₂.symm
  have hU₁U₂ : hyperStepUpperSum f a b dx₁ ≈ₕ hyperStepUpperSum f a b dx₂ :=
    hLU₁.symm.trans (hL₁L₂.trans hLU₂)
  rcases hbdd_below with ⟨m, hm⟩
  rcases hbdd_above with ⟨M, hM⟩
  have hb₁ := hyperStepSum_bounds hab
    (fun x hx ↦ hm ⟨x, hx, rfl⟩) (fun x hx ↦ hM ⟨x, hx, rfl⟩) hdx₁.1
  have hb₂ := hyperStepSum_bounds hab
    (fun x hx ↦ hm ⟨x, hx, rfl⟩) (fun x hx ↦ hM ⟨x, hx, rfl⟩) hdx₂.1
  have hS₁L₁ : hyperStepSum f a b dx₁ ≈ₕ hyperStepLowerSum f a b dx₁ :=
    infClose_of_le_of_le hb₁.2.1 hb₁.2.2.1 (InfClose.refl _) hLU₁.symm
  have hS₂L₂ : hyperStepSum f a b dx₂ ≈ₕ hyperStepLowerSum f a b dx₂ :=
    infClose_of_le_of_le hb₂.2.1 hb₂.2.2.1 (InfClose.refl _) hLU₂.symm
  exact ⟨hL₁L₂, hU₁U₂, hS₁L₁.trans (hL₁L₂.trans hS₂L₂.symm)⟩

/-- Goldblatt §9.2 (p. 109): For continuous `f` on `[a, b]` (`a ≤ b`) and any two positive
infinitesimals `Δx₁, Δx₂`, `hyperStepSum f a b Δx₁ ≈ₕ hyperStepSum f a b Δx₂`. -/
theorem hyperStepSum_infClose_of_continuousOn {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    {dx₁ dx₂ : ℝ*} (hdx₁ : IsPosInfinitesimal dx₁) (hdx₂ : IsPosInfinitesimal dx₂) :
    hyperStepSum f a b dx₁ ≈ₕ hyperStepSum f a b dx₂ := by
  obtain ⟨hbel, habv⟩ := bddBelow_bddAbove_of_continuousOn hf
  exact (hyperStepSums_infClose_of_oscillation hab hbel habv
    (fun _ hdx ↦ hyperStepLowerSum_infClose_hyperStepUpperSum hab hf hdx) hdx₁ hdx₂).2.2

/-- **Goldblatt §9.2 (eq. (iii), p. 109)**: Nonstandard definition of the definite integral
`∫_a^b f(x) dx := sh(S_a^b(f, ε))` as the shadow of the step-size Riemann sum at `ε`. -/
def hyperIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  shadow (hyperStepSum f a b Hyperreal.epsilon)

/-- The canonical infinitesimal `Hyperreal.epsilon = [(1/n)]` is a positive infinitesimal. -/
theorem isPosInfinitesimal_epsilon : IsPosInfinitesimal Hyperreal.epsilon :=
  epsilon_pos_infinitesimal

/-- Goldblatt §9.2 (p. 109): For every positive infinitesimal `Δx`, `L(f, Δx)`, `S(f, Δx)`, and
`U(f, Δx)` are infinitely close to `hyperIntegral f a b`, with shadow `hyperIntegral f a b`. -/
theorem hyperStepSums_infClose_hyperIntegral {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hbdd_below : BddBelow (f '' Set.Icc a b)) (hbdd_above : BddAbove (f '' Set.Icc a b))
    (hOsc : ∀ dx : ℝ*, IsPosInfinitesimal dx →
      hyperStepLowerSum f a b dx ≈ₕ hyperStepUpperSum f a b dx)
    {dx : ℝ*} (hdx : IsPosInfinitesimal dx) :
    hyperStepLowerSum f a b dx ≈ₕ (hyperIntegral f a b : ℝ*) ∧
    hyperStepSum f a b dx ≈ₕ (hyperIntegral f a b : ℝ*) ∧
    hyperStepUpperSum f a b dx ≈ₕ (hyperIntegral f a b : ℝ*) ∧
    shadow (hyperStepSum f a b dx) = hyperIntegral f a b := by
  have hlim_eps := (hyperStepSums_isLimited hab hbdd_below hbdd_above Hyperreal.epsilon_pos).2.1
  have hSeps : hyperStepSum f a b Hyperreal.epsilon ≈ₕ (hyperIntegral f a b : ℝ*) :=
    infClose_shadow hlim_eps
  have hcl := hyperStepSums_infClose_of_oscillation hab hbdd_below hbdd_above hOsc
    hdx isPosInfinitesimal_epsilon
  have hS : hyperStepSum f a b dx ≈ₕ (hyperIntegral f a b : ℝ*) := hcl.2.2.trans hSeps
  have hLU := hOsc dx hdx
  rcases hbdd_below with ⟨m, hm⟩
  rcases hbdd_above with ⟨M, hM⟩
  have hb := hyperStepSum_bounds hab
    (fun x hx ↦ hm ⟨x, hx, rfl⟩) (fun x hx ↦ hM ⟨x, hx, rfl⟩) hdx.1
  have hSL : hyperStepSum f a b dx ≈ₕ hyperStepLowerSum f a b dx :=
    infClose_of_le_of_le hb.2.1 hb.2.2.1 (InfClose.refl _) hLU.symm
  have hL : hyperStepLowerSum f a b dx ≈ₕ (hyperIntegral f a b : ℝ*) := hSL.symm.trans hS
  have hU : hyperStepUpperSum f a b dx ≈ₕ (hyperIntegral f a b : ℝ*) := hLU.symm.trans hL
  exact ⟨hL, hS, hU, shadow_eq_of_infClose hS⟩

/-- **Goldblatt §9.2 (p. 109)**: Whenever `L_a^b(f, Δx) ≈ₕ U_a^b(f, Δx)` for positive
infinitesimals, `f` is Darboux integrable on `[a, b]` with integral `hyperIntegral f a b`! -/
theorem isDarbouxIntegrableOn_hyperIntegral {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hbdd_below : BddBelow (f '' Set.Icc a b)) (hbdd_above : BddAbove (f '' Set.Icc a b))
    (hOsc : ∀ dx : ℝ*, IsPosInfinitesimal dx →
      hyperStepLowerSum f a b dx ≈ₕ hyperStepUpperSum f a b dx) :
    IsDarbouxIntegrableOn f a b (hyperIntegral f a b) := by
  rw [isDarbouxIntegrableOn_iff_eps]
  have hcl := hyperStepSums_infClose_hyperIntegral hab hbdd_below hbdd_above hOsc
    isPosInfinitesimal_epsilon
  rcases ofSeq_surjective Hyperreal.epsilon with ⟨s, hs_eq⟩
  have hs_pos : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < s j :=
    ofSeq_lt_ofSeq.1 (hs_eq ▸ Hyperreal.epsilon_pos)
  refine ⟨hab, hbdd_below, hbdd_above, fun P ↦ ⟨?_, ?_⟩, fun c hc ↦ ?_⟩
  · -- Condition (1a): `L(f, P) ≤ hyperIntegral f a b`
    have hle : (lowerDarbouxSum f P : ℝ*) ≤ hyperStepUpperSum f a b Hyperreal.epsilon := by
      rw [← hs_eq]
      refine ofSeq_le_ofSeq.2 (hs_pos.mono fun j hj ↦ ?_)
      change lowerDarbouxSum f P ≤ stepUpperSum f a b (s j)
      rw [stepUpperSum_of_pos f hab hj]
      exact lowerDarbouxSum_le_upperDarbouxSum hbdd_below hbdd_above P _
    exact coe_le_of_infClose_le (InfClose.refl _) hle hcl.2.2.1
  · -- Condition (1b): `hyperIntegral f a b ≤ U(f, P)`
    have hle : hyperStepLowerSum f a b Hyperreal.epsilon ≤ (upperDarbouxSum f P : ℝ*) := by
      rw [← hs_eq]
      refine ofSeq_le_ofSeq.2 (hs_pos.mono fun j hj ↦ ?_)
      change stepLowerSum f a b (s j) ≤ upperDarbouxSum f P
      rw [stepLowerSum_of_pos f hab hj]
      exact lowerDarbouxSum_le_upperDarbouxSum hbdd_below hbdd_above _ P
    exact coe_le_of_infClose_le hcl.1.symm hle (InfClose.refl _)
  · -- Condition (2): existential transfer from `dx = ε`!
    have hdiff_inf : IsInfinitesimal
        (hyperStepUpperSum f a b Hyperreal.epsilon - hyperStepLowerSum f a b Hyperreal.epsilon) :=
      (hOsc Hyperreal.epsilon isPosInfinitesimal_epsilon).symm
    have hlt : hyperStepUpperSum f a b Hyperreal.epsilon -
        hyperStepLowerSum f a b Hyperreal.epsilon < (c : ℝ*) :=
      (le_abs_self _).trans_lt (hdiff_inf c hc)
    rw [← hs_eq] at hlt
    have hev_lt : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ),
        stepUpperSum f a b (s j) - stepLowerSum f a b (s j) < c :=
      ofSeq_lt_ofSeq.1 hlt
    obtain ⟨j, hj_pos, hj_lt⟩ := (hs_pos.and hev_lt).exists
    rw [stepUpperSum_of_pos f hab hj_pos, stepLowerSum_of_pos f hab hj_pos] at hj_lt
    exact ⟨stepPartition a b hab (s j) hj_pos, hj_lt⟩

/-- **Goldblatt §9.2 (p. 109)**: Every continuous function on `[a, b]` (`a ≤ b`) is Darboux/Riemann
integrable with integral `hyperIntegral f a b`. -/
theorem isDarbouxIntegrableOn_of_continuousOn {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    IsDarbouxIntegrableOn f a b (hyperIntegral f a b) := by
  obtain ⟨hbel, habv⟩ := bddBelow_bddAbove_of_continuousOn hf
  exact isDarbouxIntegrableOn_hyperIntegral hab hbel habv
    fun _ hdx ↦ hyperStepLowerSum_infClose_hyperStepUpperSum hab hf hdx

/-- **Goldblatt §9.2 (p. 109)**: Every monotonic function on `[a, b]` (`a ≤ b`) is Darboux/Riemann
integrable with integral `hyperIntegral f a b`. -/
theorem isDarbouxIntegrableOn_of_isMonotonicOn {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : IsMonotonicOn f a b) :
    IsDarbouxIntegrableOn f a b (hyperIntegral f a b) := by
  obtain ⟨hbel, habv⟩ := bddBelow_bddAbove_of_isMonotonicOn hab hf
  exact isDarbouxIntegrableOn_hyperIntegral hab hbel habv
    fun _ hdx ↦ hyperStepLowerSum_infClose_hyperStepUpperSum_of_monotonic hab hf hdx

/-- Algebraic Darboux comparison lemma: for any standard partition `P` of `[a, b]`, bounds
`m ≤ f(x) ≤ M` on `[a, b]`, and real `Δx > 0`,
`U_a^b(f, Δx) - L_a^b(f, Δx) ≤ (U_a^b(f, P) - L_a^b(f, P)) + P.pointFinset.card * (M - m) * Δx`. -/
theorem stepUpperSum_sub_stepLowerSum_le_partition {a b m M : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hlow : ∀ x ∈ Set.Icc a b, m ≤ f x) (hhigh : ∀ x ∈ Set.Icc a b, f x ≤ M)
    (P : IntervalPartition a b) {dx : ℝ} (hdx : 0 < dx) :
    stepUpperSum f a b dx - stepLowerSum f a b dx ≤
      (upperDarbouxSum f P - lowerDarbouxSum f P) + (P.pointFinset.card : ℝ) * (M - m) * dx := by
  classical
  have hMm_nn : 0 ≤ M - m := sub_nonneg.2 ((hlow a ⟨le_rfl, hab⟩).trans (hhigh a ⟨le_rfl, hab⟩))
  rcases eq_or_lt_of_le hab with rfl | hlt
  · have hP0 := darboux_sum_bounds P hlow hhigh
    simp only [sub_self, mul_zero] at hP0
    have hdiff_nn : 0 ≤ upperDarbouxSum f P - lowerDarbouxSum f P := by
      linarith [hP0.1, hP0.2.1, hP0.2.2.1, hP0.2.2.2]
    have hcard_nn : 0 ≤ (P.pointFinset.card : ℝ) * (M - m) * dx := by positivity
    simp only [(stepSums_self f a dx).1, (stepSums_self f a dx).2.1, sub_self]
    linarith
  · rw [stepUpperSum_of_pos f hab hdx, stepLowerSum_of_pos f hab hdx]
    let R := stepPartition a b hab dx hdx
    have hRn : 0 < R.n := Nat.ceil_pos.2 (div_pos (sub_pos.2 hlt) hdx)
    have hbel : BddBelow (f '' Set.Icc a b) := ⟨m, fun _ ⟨x, hx, hfx⟩ ↦ hfx ▸ hlow x hx⟩
    have habv : BddAbove (f '' Set.Icc a b) := ⟨M, fun _ ⟨x, hx, hfx⟩ ↦ hfx ▸ hhigh x hx⟩
    let S : Finset ℝ := P.pointFinset ∪ R.pointFinset
    let Q := IntervalPartition.commonRefinement P R
    have hQP := darboux_sum_refinement hbel habv P Q
      fun _ hk ↦ IntervalPartition.exists_pts_commonRefinement_left P R hk
    have hUQ_LQ_le : upperDarbouxSum f Q - lowerDarbouxSum f Q ≤
        upperDarbouxSum f P - lowerDarbouxSum f P := by linarith [hQP.1, hQP.2]
    -- Strictly increasing property of `Q.pts` on `j ≤ Q.n`
    have hQ_strict : ∀ i j : ℕ, i < j → j ≤ Q.n → Q.pts i < Q.pts j := by
      intro i j hij hj
      have hjS : j < S.card := by
        change j ≤ S.card - 1 at hj
        have hpos : 0 < S.card :=
          Finset.card_pos.2 ⟨a, Finset.mem_union_left _ P.left_mem_pointFinset⟩
        omega
      have hiS : i < S.card := hij.trans hjS
      change (if hk : i < S.card then S.orderEmbOfFin rfl ⟨i, hk⟩ else b) <
        (if hk : j < S.card then S.orderEmbOfFin rfl ⟨j, hk⟩ else b)
      simp only [hiS, hjS, ↓reduceDIte]
      exact (S.orderEmbOfFin rfl).strictMono hij
    -- Index embedding `idx` of `R` into `Q`
    have hex_ge : ∀ k < R.n, ∃ j : ℕ, j ≤ Q.n ∧ R.pts k ≤ Q.pts j := by
      intro k hk
      obtain ⟨j, hj, hjeq⟩ := IntervalPartition.exists_pts_commonRefinement_right P R hk.le
      exact ⟨j, hj, hjeq.symm.le⟩
    let idx : ℕ → ℕ := fun k ↦ if hk : k < R.n then Nat.find (hex_ge k hk) else Q.n
    have hidx_le : ∀ k, idx k ≤ Q.n := fun k ↦ by
      by_cases hk : k < R.n
      · simp only [idx, hk, ↓reduceDIte]; exact (Nat.find_spec (hex_ge k hk)).1
      · simp [idx, hk]
    have hidx_eq : ∀ k ≤ R.n, Q.pts (idx k) = R.pts k := by
      intro k hk
      rcases eq_or_lt_of_le hk with rfl | hlt_k
      · simp [idx, Q.pts_last, R.pts_last]
      · simp only [idx, hlt_k, ↓reduceDIte]
        have hspec := Nat.find_spec (hex_ge k hlt_k)
        obtain ⟨j₀, hj₀_le, hj₀_eq⟩ := IntervalPartition.exists_pts_commonRefinement_right P R hk
        have hmin : Nat.find (hex_ge k hlt_k) ≤ j₀ :=
          Nat.find_min' (hex_ge k hlt_k) ⟨hj₀_le, hj₀_eq.symm.le⟩
        exact le_antisymm ((Q.pts_le_pts hmin hj₀_le).trans_eq hj₀_eq) hspec.2
    have hidx_zero : idx 0 = 0 := by
      simp only [idx, hRn, ↓reduceDIte]
      exact Nat.eq_zero_of_le_zero (Nat.find_min' (hex_ge 0 hRn)
        ⟨Nat.zero_le Q.n, by rw [R.pts_zero, Q.pts_zero]⟩)
    have hidx_last : idx R.n = Q.n := by simp [idx]
    have hidx_mono : ∀ k, idx k ≤ idx (k + 1) := fun k ↦ by
      by_cases hk1 : k + 1 < R.n
      · have hk0 : k < R.n := Nat.lt_of_succ_lt hk1
        simp only [idx, hk0, hk1, ↓reduceDIte]
        have hspec1 := Nat.find_spec (hex_ge (k + 1) hk1)
        exact Nat.find_min' (hex_ge k hk0) ⟨hspec1.1, (R.mono k hk0).trans hspec1.2⟩
      · simp only [idx, hk1, ↓reduceDIte]; exact hidx_le k
    let oscR : ℕ → ℝ := fun k ↦
      (sSup (f '' Set.Icc (R.pts k) (R.pts (k + 1))) -
       sInf (f '' Set.Icc (R.pts k) (R.pts (k + 1)))) * (R.pts (k + 1) - R.pts k)
    let oscQ : ℕ → ℝ := fun j ↦
      (sSup (f '' Set.Icc (Q.pts j) (Q.pts (j + 1))) -
       sInf (f '' Set.Icc (Q.pts j) (Q.pts (j + 1)))) * (Q.pts (j + 1) - Q.pts j)
    have hUR_LR : upperDarbouxSum f R - lowerDarbouxSum f R = ∑ k ∈ Finset.range R.n, oscR k := by
      unfold upperDarbouxSum lowerDarbouxSum oscR
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ ↦ (sub_mul _ _ _).symm
    have hUQ_LQ : upperDarbouxSum f Q - lowerDarbouxSum f Q =
        ∑ k ∈ Finset.range R.n, ∑ j ∈ Finset.Ico (idx k) (idx (k + 1)), oscQ j := by
      unfold upperDarbouxSum lowerDarbouxSum oscQ
      rw [← Finset.sum_sub_distrib, ← hidx_last, sum_range_split_mono hidx_zero hidx_mono]
      refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ (sub_mul _ _ _).symm
    let bad : Finset ℕ := (Finset.range R.n).filter (fun k ↦ idx k + 2 ≤ idx (k + 1))
    -- Every `k ∉ bad` has `oscR k = ∑ j ∈ Ico (idx k) (idx (k+1)), oscQ j`!
    have hgood_eq : ∀ k ∈ Finset.range R.n, k ∉ bad →
        oscR k - ∑ j ∈ Finset.Ico (idx k) (idx (k + 1)), oscQ j = 0 := by
      intro k hk hnotbad
      have hk' : k < R.n := Finset.mem_range.1 hk
      have hle1 : idx (k + 1) ≤ idx k + 1 := by
        simp only [bad, Finset.mem_filter, hk, true_and, not_le] at hnotbad
        omega
      rcases eq_or_lt_of_le (hidx_mono k) with heq | hlt_idx
      · have hpts_eq : R.pts (k + 1) = R.pts k := by
          rw [← hidx_eq (k + 1) (Nat.succ_le_of_lt hk'), ← hidx_eq k hk'.le, ← heq]
        simp [oscR, hpts_eq, ← heq]
      · have heq1 : idx (k + 1) = idx k + 1 := by omega
        rw [heq1, Nat.Ico_succ_singleton, Finset.sum_singleton]
        simp only [oscR, oscQ, ← heq1,
          hidx_eq k hk'.le, hidx_eq (k + 1) (Nat.succ_le_of_lt hk'), sub_self]
    -- Every `k ∈ bad` has `oscR k - ∑ oscQ ≤ (M - m) * dx`
    have hbad_bound : ∀ k ∈ bad,
        oscR k - ∑ j ∈ Finset.Ico (idx k) (idx (k + 1)), oscQ j ≤ (M - m) * dx := by
      intro k hk
      have hk' : k < R.n := Finset.mem_range.1 (Finset.mem_of_mem_filter k hk)
      have hoscQ_nn : 0 ≤ ∑ j ∈ Finset.Ico (idx k) (idx (k + 1)), oscQ j := by
        refine Finset.sum_nonneg fun j hj ↦ ?_
        have hj_lt : j < Q.n := (Finset.mem_Ico.1 hj).2.trans_le (hidx_le (k + 1))
        have hbelQ : BddBelow (f '' Set.Icc (Q.pts j) (Q.pts (j + 1))) :=
          hbel.mono (Set.image_mono (Q.subinterval_subset_Icc hj_lt))
        have habvQ : BddAbove (f '' Set.Icc (Q.pts j) (Q.pts (j + 1))) :=
          habv.mono (Set.image_mono (Q.subinterval_subset_Icc hj_lt))
        have hmemQ : f (Q.pts j) ∈ f '' Set.Icc (Q.pts j) (Q.pts (j + 1)) :=
          ⟨Q.pts j, ⟨le_rfl, Q.mono j hj_lt⟩, rfl⟩
        have hle_sup := (csInf_le hbelQ hmemQ).trans (le_csSup habvQ hmemQ)
        exact mul_nonneg (sub_nonneg.2 hle_sup) (Q.width_nonneg hj_lt)
      have hneR : (f '' Set.Icc (R.pts k) (R.pts (k + 1))).Nonempty :=
        ⟨f (R.pts k), R.pts k, ⟨le_rfl, R.mono k hk'⟩, rfl⟩
      have hsupR : sSup (f '' Set.Icc (R.pts k) (R.pts (k + 1))) ≤ M :=
        csSup_le hneR fun _ ⟨x, hx, hfx⟩ ↦ hfx ▸ hhigh x (R.subinterval_subset_Icc hk' hx)
      have hinfR : m ≤ sInf (f '' Set.Icc (R.pts k) (R.pts (k + 1))) :=
        le_csInf hneR fun _ ⟨x, hx, hfx⟩ ↦ hfx ▸ hlow x (R.subinterval_subset_Icc hk' hx)
      have hoscR_le : oscR k ≤ (M - m) * dx :=
        mul_le_mul (by linarith) (stepPartition_width_le hab hdx hk')
          (R.width_nonneg hk') hMm_nn
      linarith
    -- Injectivity of `k ↦ Q.pts (idx k + 1)` from `bad` into `P.pointFinset`!
    have hbad_card : bad.card ≤ P.pointFinset.card := by
      refine Finset.card_le_card_of_injOn (fun k ↦ Q.pts (idx k + 1))
        (fun k hk ↦ ?_) (fun k₁ hk₁ k₂ hk₂ heq ↦ ?_)
      · obtain ⟨hk_range, hk_ge2⟩ := Finset.mem_filter.1 hk
        have hk' : k < R.n := Finset.mem_range.1 hk_range
        have h1_lt : idx k + 1 < idx (k + 1) := by omega
        have h1_leQ : idx k + 1 ≤ Q.n := h1_lt.le.trans (hidx_le (k + 1))
        have hgt_left : R.pts k < Q.pts (idx k + 1) := by
          rw [← hidx_eq k hk'.le]
          exact hQ_strict (idx k) (idx k + 1) (Nat.lt_succ_self _) h1_leQ
        have hlt_right : Q.pts (idx k + 1) < R.pts (k + 1) := by
          rw [← hidx_eq (k + 1) (Nat.succ_le_of_lt hk')]
          exact hQ_strict (idx k + 1) (idx (k + 1)) h1_lt (hidx_le (k + 1))
        have hmemS : Q.pts (idx k + 1) ∈ S := by
          have hjS : idx k + 1 < S.card := by
            change idx k + 1 ≤ S.card - 1 at h1_leQ
            have hpos : 0 < S.card :=
          Finset.card_pos.2 ⟨a, Finset.mem_union_left _ P.left_mem_pointFinset⟩
            omega
          change (if h : idx k + 1 < S.card then S.orderEmbOfFin rfl ⟨idx k + 1, h⟩ else b) ∈ S
          simp only [hjS, ↓reduceDIte, Finset.orderEmbOfFin_mem]
        rcases Finset.mem_union.1 hmemS with hmemP | hmemR
        · exact hmemP
        · exfalso
          rcases Finset.mem_image.1 hmemR with ⟨l, hl_range, hl_eq⟩
          have hl_le : l ≤ R.n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl_range)
          rcases le_or_gt l k with hlk | hkl
          · linarith [R.pts_le_pts hlk hk'.le]
          · linarith [R.pts_le_pts (Nat.succ_le_of_lt hkl) hl_le]
      · obtain ⟨hk₁_r, hk₁_ge2⟩ := Finset.mem_filter.1 hk₁
        obtain ⟨hk₂_r, hk₂_ge2⟩ := Finset.mem_filter.1 hk₂
        have h1_leQ₁ : idx k₁ + 1 ≤ Q.n :=
          (by omega : idx k₁ + 1 ≤ idx (k₁ + 1)).trans (hidx_le (k₁ + 1))
        have h1_leQ₂ : idx k₂ + 1 ≤ Q.n :=
          (by omega : idx k₂ + 1 ≤ idx (k₂ + 1)).trans (hidx_le (k₂ + 1))
        rcases lt_trichotomy k₁ k₂ with hlt12 | rfl | hgt12
        · exfalso
          have hmono_k : idx (k₁ + 1) ≤ idx k₂ := by
            clear heq
            have hstep : ∀ d, idx (k₁ + 1) ≤ idx (k₁ + 1 + d) := by
              intro d; induction d with
              | zero => simp
              | succ d ih => exact ih.trans (hidx_mono _)
            have heqk : k₂ = k₁ + 1 + (k₂ - (k₁ + 1)) := by omega
            rw [heqk]; exact hstep _
          have hlt_idx : idx k₁ + 1 < idx k₂ + 1 := by omega
          exact (hQ_strict _ _ hlt_idx h1_leQ₂).ne heq
        · rfl
        · exfalso
          have hmono_k : idx (k₂ + 1) ≤ idx k₁ := by
            clear heq
            have hstep : ∀ d, idx (k₂ + 1) ≤ idx (k₂ + 1 + d) := by
              intro d; induction d with
              | zero => simp
              | succ d ih => exact ih.trans (hidx_mono _)
            have heqk : k₁ = k₂ + 1 + (k₁ - (k₂ + 1)) := by omega
            rw [heqk]; exact hstep _
          have hlt_idx : idx k₂ + 1 < idx k₁ + 1 := by omega
          exact (hQ_strict _ _ hlt_idx h1_leQ₁).ne heq.symm
    have hdiff_le : (upperDarbouxSum f R - lowerDarbouxSum f R) -
        (upperDarbouxSum f Q - lowerDarbouxSum f Q) ≤
        (P.pointFinset.card : ℝ) * (M - m) * dx := by
      rw [hUR_LR, hUQ_LQ, ← Finset.sum_sub_distrib,
          ← Finset.sum_filter_add_sum_filter_not (Finset.range R.n)
            (fun k ↦ idx k + 2 ≤ idx (k + 1))]
      have hzero : ∑ k ∈ (Finset.range R.n).filter (fun k ↦ ¬ idx k + 2 ≤ idx (k + 1)),
          (oscR k - ∑ j ∈ Finset.Ico (idx k) (idx (k + 1)), oscQ j) = 0 := by
        refine Finset.sum_eq_zero fun k hk ↦ ?_
        obtain ⟨hkr, hkn⟩ := Finset.mem_filter.1 hk
        exact hgood_eq k hkr (by simp [bad, hkr, hkn])
      rw [hzero, add_zero]
      calc ∑ k ∈ bad, (oscR k - ∑ j ∈ Finset.Ico (idx k) (idx (k + 1)), oscQ j)
          ≤ ∑ _k ∈ bad, (M - m) * dx := Finset.sum_le_sum hbad_bound
        _ = (bad.card : ℝ) * ((M - m) * dx) := by simp
        _ ≤ (P.pointFinset.card : ℝ) * ((M - m) * dx) := by
            gcongr
        _ = (P.pointFinset.card : ℝ) * (M - m) * dx := by ring
    linarith

/-- **Goldblatt §9.2 (pp. 109–110)**: Full nonstandard characterization of Riemann/Darboux
integrability for bounded functions `f` on `[a, b]` (`a ≤ b`):
`f` is Darboux integrable on `[a, b]` iff `L_a^b(f, Δx) ≈ₕ U_a^b(f, Δx)` for every positive
infinitesimal `Δx`! -/
theorem exists_isDarbouxIntegrableOn_iff_infClose {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hbdd_below : BddBelow (f '' Set.Icc a b)) (hbdd_above : BddAbove (f '' Set.Icc a b)) :
    (∃ I : ℝ, IsDarbouxIntegrableOn f a b I) ↔
      ∀ dx : ℝ*, IsPosInfinitesimal dx →
        hyperStepLowerSum f a b dx ≈ₕ hyperStepUpperSum f a b dx := by
  constructor
  · rintro ⟨I, hI⟩ dx hdx
    rw [isDarbouxIntegrableOn_iff_eps] at hI
    rcases hbdd_below with ⟨m, hm⟩
    rcases hbdd_above with ⟨M, hM⟩
    have hlow : ∀ x ∈ Set.Icc a b, m ≤ f x := fun x hx ↦ hm ⟨x, hx, rfl⟩
    have hhigh : ∀ x ∈ Set.Icc a b, f x ≤ M := fun x hx ↦ hM ⟨x, hx, rfl⟩
    have hdx_inf : IsInfinitesimal dx := isInfinitesimal_iff_trichotomy.2 (Or.inl hdx)
    have hb_hyper := hyperStepSum_bounds hab hlow hhigh hdx.1
    have hnn : 0 ≤ hyperStepUpperSum f a b dx - hyperStepLowerSum f a b dx := by
      linarith [hb_hyper.2.1, hb_hyper.2.2.1]
    symm
    intro r hr
    obtain ⟨P, hP⟩ := hI.2.2.2.2 (r / 2) (half_pos hr)
    rcases ofSeq_surjective dx with ⟨s, rfl⟩
    have hs : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < s j := ofSeq_lt_ofSeq.1 hdx.1
    have hle_hyper : hyperStepUpperSum f a b (ofSeq s) - hyperStepLowerSum f a b (ofSeq s) ≤
        ((upperDarbouxSum f P - lowerDarbouxSum f P : ℝ) : ℝ*) +
        (((P.pointFinset.card : ℝ) * (M - m) : ℝ) : ℝ*) * ofSeq s := by
      refine ofSeq_le_ofSeq.2 (hs.mono fun j hj ↦ ?_)
      simpa [mul_assoc] using stepUpperSum_sub_stepLowerSum_le_partition hab hlow hhigh P hj
    have hrem_inf : IsInfinitesimal
        ((((P.pointFinset.card : ℝ) * (M - m) : ℝ) : ℝ*) * ofSeq s) :=
      (isLimited_coe _).mul_isInfinitesimal hdx_inf
    have hrem_lt : ((((P.pointFinset.card : ℝ) * (M - m) : ℝ) : ℝ*) * ofSeq s) <
        ((r / 2 : ℝ) : ℝ*) :=
      (le_abs_self _).trans_lt (hrem_inf (r / 2) (half_pos hr))
    have hP_lt : ((upperDarbouxSum f P - lowerDarbouxSum f P : ℝ) : ℝ*) < ((r / 2 : ℝ) : ℝ*) :=
      Hyperreal.coe_lt_coe.2 hP
    have hsum : ((r / 2 : ℝ) : ℝ*) + ((r / 2 : ℝ) : ℝ*) = (r : ℝ*) := by
      rw [← Hyperreal.coe_add, add_halves]
    rw [abs_of_nonneg hnn]
    linarith
  · intro hOsc
    exact ⟨hyperIntegral f a b, isDarbouxIntegrableOn_hyperIntegral hab hbdd_below hbdd_above hOsc⟩

/-- **Goldblatt §9.2 (p. 109)**: Standard right-hand limit characterization
`lim_{Δx → 0⁺} S_a^b(f, Δx) = I` whenever `IsDarbouxIntegrableOn f a b I`. -/
theorem tendsto_stepRiemannSum_nhdsWithin_Ioi {a b I : ℝ} {f : ℝ → ℝ}
    (hI : IsDarbouxIntegrableOn f a b I) :
    Tendsto (stepRiemannSum f a b) (𝓝[>] 0) (𝓝 I) := by
  obtain ⟨hab, hbel, habv, hbounds, heps⟩ := isDarbouxIntegrableOn_iff_eps.1 hI
  rcases hbel with ⟨m, hm⟩
  rcases habv with ⟨M, hM⟩
  have hlow : ∀ x ∈ Set.Icc a b, m ≤ f x := fun x hx ↦ hm ⟨x, hx, rfl⟩
  have hhigh : ∀ x ∈ Set.Icc a b, f x ≤ M := fun x hx ↦ hM ⟨x, hx, rfl⟩
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨P, hP⟩ := heps (ε / 2) (half_pos hε)
  set C : ℝ := (P.pointFinset.card : ℝ) * (M - m) + 1
  have hC_pos : 0 < C := by
    have : 0 ≤ M - m := sub_nonneg.2 ((hlow a ⟨le_rfl, hab⟩).trans (hhigh a ⟨le_rfl, hab⟩))
    positivity
  refine ⟨(ε / 2) / C, div_pos (half_pos hε) hC_pos, fun dx hdx_mem hdx_dist ↦ ?_⟩
  have hdx : 0 < dx := hdx_mem
  have hdx_lt : dx < (ε / 2) / C := by
    have : |dx| < (ε / 2) / C := by simpa [Real.dist_eq] using hdx_dist
    rwa [abs_of_pos hdx] at this
  have hstep_le := stepUpperSum_sub_stepLowerSum_le_partition hab hlow hhigh P hdx
  have hrem_lt : (P.pointFinset.card : ℝ) * (M - m) * dx < ε / 2 := by
    have hleC : (P.pointFinset.card : ℝ) * (M - m) ≤ C := by linarith
    have h1 : (P.pointFinset.card : ℝ) * (M - m) * dx ≤ C * dx :=
      mul_le_mul_of_nonneg_right hleC hdx.le
    have h2 : C * dx < ε / 2 := by
      have := (lt_div_iff₀' hC_pos).1 hdx_lt
      linarith
    exact h1.trans_lt h2
  let R := stepPartition a b hab dx hdx
  have hI_R := hbounds R
  have hS_R := darboux_sum_bounds R hlow hhigh
  rw [stepUpperSum_of_pos f hab hdx, stepLowerSum_of_pos f hab hdx] at hstep_le
  rw [Real.dist_eq, stepRiemannSum_of_pos f hab hdx, abs_lt]
  exact ⟨by linarith [hS_R.2.1, hI_R.2], by linarith [hS_R.2.2.1, hI_R.1]⟩

/-! ### Exercise 9.2.1: Equal-Subdivision Sums & `intervalIntegral` -/

/-- Equal-subdivision left-endpoint Riemann sum on `[a, b]` with `n` subintervals of width
`(b - a) / n`: `S_a^b(f, n) = ∑_{k=0}^{n-1} f(a + k(b - a)/n) · (b - a)/n`. -/
def riemannSumEq (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, f (a + (k : ℝ) * (b - a) / (n : ℝ)) * ((b - a) / (n : ℝ))

/-- Equal-subdivision upper Darboux sum `U_a^b(f, n)` for `Δx = (b - a)/n`
(Exercise 9.2.1, p. 110). -/
def upperSumEq (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    sSup (f '' Set.Icc (a + (k : ℝ) * (b - a) / (n : ℝ))
      (a + ((k + 1 : ℕ) : ℝ) * (b - a) / (n : ℝ))) * ((b - a) / (n : ℝ))

/-- Equal-subdivision lower Darboux sum `L_a^b(f, n)` for `Δx = (b - a)/n`
(Exercise 9.2.1, p. 110). -/
def lowerSumEq (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    sInf (f '' Set.Icc (a + (k : ℝ) * (b - a) / (n : ℝ))
      (a + ((k + 1 : ℕ) : ℝ) * (b - a) / (n : ℝ))) * ((b - a) / (n : ℝ))

/-- Hyperfinite equal-subdivision Riemann sum `S_a^b(f, N)` for `N ∈ ℕ*` via `starSeq`. -/
def hyperRiemannSum (f : ℝ → ℝ) (a b : ℝ) (N : ℕ*) : ℝ* :=
  starSeq (riemannSumEq f a b) N

/-- Hyperfinite equal-subdivision upper sum `U_a^b(f, N)` for `N ∈ ℕ*` via `starSeq`. -/
def hyperUpperSumEq (f : ℝ → ℝ) (a b : ℝ) (N : ℕ*) : ℝ* :=
  starSeq (upperSumEq f a b) N

/-- Hyperfinite equal-subdivision lower sum `L_a^b(f, N)` for `N ∈ ℕ*` via `starSeq`. -/
def hyperLowerSumEq (f : ℝ → ℝ) (a b : ℝ) (N : ℕ*) : ℝ* :=
  starSeq (lowerSumEq f a b) N

/-- Degenerate-interval equal-subdivision sums vanish identically on `[a, a]`. -/
@[simp]
theorem eqSums_self (f : ℝ → ℝ) (a : ℝ) (n : ℕ) :
    riemannSumEq f a a n = 0 ∧ upperSumEq f a a n = 0 ∧ lowerSumEq f a a n = 0 := by
  simp [riemannSumEq, upperSumEq, lowerSumEq]

/-- Degenerate-interval hyperfinite equal-subdivision sums vanish identically on `[a, a]`. -/
@[simp]
theorem hyperEqSums_self (f : ℝ → ℝ) (a : ℝ) (N : ℕ*) :
    hyperRiemannSum f a a N = 0 ∧ hyperUpperSumEq f a a N = 0 ∧ hyperLowerSumEq f a a N = 0 := by
  induction N using Germ.inductionOn with | _ s =>
  exact ⟨Germ.coe_eq.2 (Eventually.of_forall fun j ↦ (eqSums_self f a (s j)).1),
         Germ.coe_eq.2 (Eventually.of_forall fun j ↦ (eqSums_self f a (s j)).2.1),
         Germ.coe_eq.2 (Eventually.of_forall fun j ↦ (eqSums_self f a (s j)).2.2)⟩

/-- Exact agreement of equal-subdivision sums with step-size sums at `Δx = (b - a)/n` for `a < b`
and `0 < n`. -/
theorem eqSums_eq_stepSums_div {a b : ℝ} (f : ℝ → ℝ) (hab : a < b) {n : ℕ} (hn : 0 < n) :
    riemannSumEq f a b n = stepRiemannSum f a b ((b - a) / (n : ℝ)) ∧
    upperSumEq f a b n = stepUpperSum f a b ((b - a) / (n : ℝ)) ∧
    lowerSumEq f a b n = stepLowerSum f a b ((b - a) / (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hba_pos : 0 < b - a := sub_pos.2 hab
  have hdx : 0 < (b - a) / (n : ℝ) := div_pos hba_pos hn_pos
  let P := stepPartition a b hab.le ((b - a) / (n : ℝ)) hdx
  have hPn : P.n = n := by
    change ⌈(b - a) / ((b - a) / (n : ℝ))⌉₊ = n
    rw [div_div_cancel₀ hba_pos.ne', Nat.ceil_natCast]
  have hPpts : ∀ k ≤ n, P.pts k = a + (k : ℝ) * (b - a) / (n : ℝ) := by
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · have hlast := P.pts_last
      rw [hPn] at hlast
      rw [hlast, mul_div_cancel_left₀ (b - a) hn_pos.ne', add_sub_cancel]
    · have hkP : k < P.n := hPn ▸ hlt
      rw [stepPartition_pts_of_lt hab.le hdx hkP, mul_div_assoc]
  have hPwidth : ∀ k < n, P.pts (k + 1) - P.pts k = (b - a) / (n : ℝ) := by
    intro k hk
    rw [hPpts (k + 1) (Nat.succ_le_of_lt hk), hPpts k hk.le]
    push_cast
    ring
  rw [stepRiemannSum_of_pos f hab.le hdx, stepUpperSum_of_pos f hab.le hdx,
      stepLowerSum_of_pos f hab.le hdx]
  change (riemannSumEq f a b n = partitionRiemannSum f P) ∧
         (upperSumEq f a b n = upperDarbouxSum f P) ∧
         (lowerSumEq f a b n = lowerDarbouxSum f P)
  unfold riemannSumEq partitionRiemannSum upperSumEq upperDarbouxSum lowerSumEq lowerDarbouxSum
  rw [hPn]
  refine ⟨Finset.sum_congr rfl fun k hk ↦ ?_, Finset.sum_congr rfl fun k hk ↦ ?_,
          Finset.sum_congr rfl fun k hk ↦ ?_⟩
  · have hk' := Finset.mem_range.1 hk
    rw [hPwidth k hk', hPpts k hk'.le]
  · have hk' := Finset.mem_range.1 hk
    rw [hPwidth k hk', hPpts k hk'.le, hPpts (k + 1) (Nat.succ_le_of_lt hk')]
  · have hk' := Finset.mem_range.1 hk
    rw [hPwidth k hk', hPpts k hk'.le, hPpts (k + 1) (Nat.succ_le_of_lt hk')]

/-- If `a < b` and `N ∈ ℕ*` is unlimited, then `(b - a) / N` is a positive infinitesimal in `ℝ*`. -/
theorem isPosInfinitesimal_sub_div_hypernat {a b : ℝ} (hab : a < b) {N : ℕ*}
    (hN : IsUnlimitedNat N) :
    IsPosInfinitesimal (((b - a : ℝ) : ℝ*) / Hypernat.toHyperreal N) := by
  have hpos_unl : IsPosUnlimited (Hypernat.toHyperreal N) :=
    isUnlimitedNat_iff_isPosUnlimited.1 hN
  have hN_pos : (0 : ℝ*) < Hypernat.toHyperreal N := by simpa using hpos_unl 0
  have hba_pos : (0 : ℝ*) < ((b - a : ℝ) : ℝ*) := Hyperreal.coe_pos.2 (sub_pos.2 hab)
  have hunl : IsUnlimited (Hypernat.toHyperreal N) :=
    isUnlimited_iff_pos_or_neg.2 (Or.inl hpos_unl)
  have hinf_inv : IsInfinitesimal (Hypernat.toHyperreal N)⁻¹ := hunl.inv_isInfinitesimal
  have hinf : IsInfinitesimal (((b - a : ℝ) : ℝ*) / Hypernat.toHyperreal N) := by
    rw [div_eq_mul_inv]
    exact (isLimited_coe (b - a)).mul_isInfinitesimal hinf_inv
  refine ⟨div_pos hba_pos hN_pos, fun r hr ↦ ?_⟩
  exact (le_abs_self _).trans_lt (hinf r hr)

/-- Exact identification of `hyperRiemannSum`, `hyperUpperSumEq`, and `hyperLowerSumEq` with
`hyperStepSum`, `hyperStepUpperSum`, and `hyperStepLowerSum` at `dx = (b - a) / N` when `a < b`
and `N > 0` in `ℕ*`. -/
theorem hyperEqSums_eq_hyperStepSums_div {a b : ℝ} (f : ℝ → ℝ) (hab : a < b) {N : ℕ*}
    (hN : (0 : ℕ*) < N) :
    hyperRiemannSum f a b N =
      hyperStepSum f a b (((b - a : ℝ) : ℝ*) / Hypernat.toHyperreal N) ∧
    hyperUpperSumEq f a b N =
      hyperStepUpperSum f a b (((b - a : ℝ) : ℝ*) / Hypernat.toHyperreal N) ∧
    hyperLowerSumEq f a b N =
      hyperStepLowerSum f a b (((b - a : ℝ) : ℝ*) / Hypernat.toHyperreal N) := by
  induction N using Germ.inductionOn with | _ u =>
  have hu : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < u j := Germ.coe_lt.1 hN
  refine ⟨Germ.coe_eq.2 (hu.mono fun j hj ↦ (eqSums_eq_stepSums_div f hab hj).1),
          Germ.coe_eq.2 (hu.mono fun j hj ↦ (eqSums_eq_stepSums_div f hab hj).2.1),
          Germ.coe_eq.2 (hu.mono fun j hj ↦ (eqSums_eq_stepSums_div f hab hj).2.2)⟩

/-- **Goldblatt Exercise 9.2.1 (p. 110)**: For `a ≤ b`, continuous (or monotonic, or any Darboux
integrable) `f` on `[a, b]`, and unlimited `N ∈ ℕ*`,
`L_a^b(f, N) ≈ₕ S_a^b(f, N) ≈ₕ U_a^b(f, N) ≈ₕ hyperIntegral f a b` and all three are limited! -/
theorem hyperRiemannSum_infClose_hyperIntegral_of_isDarbouxIntegrableOn {a b I : ℝ} {f : ℝ → ℝ}
    (hI : IsDarbouxIntegrableOn f a b I) {N : ℕ*} (hN : IsUnlimitedNat N) :
    IsLimited (hyperRiemannSum f a b N) ∧
    hyperLowerSumEq f a b N ≈ₕ hyperRiemannSum f a b N ∧
    hyperRiemannSum f a b N ≈ₕ hyperUpperSumEq f a b N ∧
    hyperRiemannSum f a b N ≈ₕ (hyperIntegral f a b : ℝ*) ∧
    shadow (hyperRiemannSum f a b N) = hyperIntegral f a b := by
  have hOsc := (exists_isDarbouxIntegrableOn_iff_infClose hI.1 hI.2.1 hI.2.2.1).1 ⟨I, hI⟩
  obtain ⟨hab, hbel, habv, _, _⟩ := hI
  rcases eq_or_lt_of_le hab with rfl | hlt
  · have h0 := hyperEqSums_self f a N
    have hint0 : hyperIntegral f a a = 0 := by
      unfold hyperIntegral hyperStepSum
      rcases ofSeq_surjective Hyperreal.epsilon with ⟨s, hs_eq⟩
      rw [← hs_eq]
      have : starFun (stepRiemannSum f a a) (ofSeq s) = 0 :=
        Germ.coe_eq.2 (Eventually.of_forall fun j ↦ (stepSums_self f a (s j)).2.2)
      rw [this, shadow_zero]
    rw [h0.1, h0.2.1, h0.2.2, hint0]
    exact ⟨isLimited_coe 0, InfClose.refl 0, InfClose.refl 0, InfClose.refl 0, shadow_zero⟩
  · have heq := hyperEqSums_eq_hyperStepSums_div f hlt (hN 0)
    have hdx := isPosInfinitesimal_sub_div_hypernat hlt hN
    have hlim := (hyperStepSums_isLimited hab hbel habv hdx.1).2.1
    have hcl := hyperStepSums_infClose_hyperIntegral hab hbel habv hOsc hdx
    rw [heq.1, heq.2.1, heq.2.2]
    exact ⟨hlim, hcl.1.trans hcl.2.1.symm, hcl.2.1.trans hcl.2.2.1.symm, hcl.2.1, hcl.2.2.2⟩

/-- **Goldblatt Exercise 9.2.1 (Continuous Case, p. 110)**: If `a ≤ b`, `f` is continuous on
`[a, b]`, and `N ∈ ℕ*` is unlimited, then `hyperRiemannSum f a b N` is limited and
`L_a^b(f, N) ≈ₕ S_a^b(f, N) ≈ₕ U_a^b(f, N) ≈ₕ hyperIntegral f a b`. -/
theorem hyperRiemannSum_isLimited_and_infClose_of_continuousOn {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) {N : ℕ*} (hN : IsUnlimitedNat N) :
    IsLimited (hyperRiemannSum f a b N) ∧
    hyperLowerSumEq f a b N ≈ₕ hyperRiemannSum f a b N ∧
    hyperRiemannSum f a b N ≈ₕ hyperUpperSumEq f a b N ∧
    hyperRiemannSum f a b N ≈ₕ (hyperIntegral f a b : ℝ*) := by
  have h := hyperRiemannSum_infClose_hyperIntegral_of_isDarbouxIntegrableOn
    (isDarbouxIntegrableOn_of_continuousOn hab hf) hN
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Every standard partition `P` of `[a, b]` (`a ≤ b`) sandwiches Mathlib's `∫ x in a..b, f x`
between `L_a^b(f, P)` and `U_a^b(f, P)`. -/
theorem darboux_bounds_intervalIntegral {a b : ℝ} {f : ℝ → ℝ}
    (hbdd_below : BddBelow (f '' Set.Icc a b)) (hbdd_above : BddAbove (f '' Set.Icc a b))
    (hint : IntervalIntegrable f MeasureTheory.volume a b) (P : IntervalPartition a b) :
    lowerDarbouxSum f P ≤ ∫ x in a..b, f x ∧ ∫ x in a..b, f x ≤ upperDarbouxSum f P := by
  have hsub_int : ∀ k < P.n,
      IntervalIntegrable f MeasureTheory.volume (P.pts k) (P.pts (k + 1)) := by
    intro k hk
    exact hint.mono_set (by
      rw [Set.uIcc_of_le (P.mono k hk), Set.uIcc_of_le P.le_endpoints]
      exact P.subinterval_subset_Icc hk)
  have hsum_eq : ∑ k ∈ Finset.range P.n, ∫ x in P.pts k..P.pts (k + 1), f x = ∫ x in a..b, f x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals hsub_int
    rwa [P.pts_zero, P.pts_last] at h
  rw [← hsum_eq]
  refine ⟨?_, ?_⟩
  · refine Finset.sum_le_sum fun k hk ↦ ?_
    have hk' := Finset.mem_range.1 hk
    have hbel_k : BddBelow (f '' Set.Icc (P.pts k) (P.pts (k + 1))) :=
      hbdd_below.mono (Set.image_mono (P.subinterval_subset_Icc hk'))
    set mk := sInf (f '' Set.Icc (P.pts k) (P.pts (k + 1)))
    have hconst : mk * (P.pts (k + 1) - P.pts k) = ∫ _ in P.pts k..P.pts (k + 1), mk := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    rw [hconst]
    exact intervalIntegral.integral_mono_on (P.mono k hk')
      (intervalIntegrable_const) (hsub_int k hk') fun x hx ↦ csInf_le hbel_k ⟨x, hx, rfl⟩
  · refine Finset.sum_le_sum fun k hk ↦ ?_
    have hk' := Finset.mem_range.1 hk
    have habv_k : BddAbove (f '' Set.Icc (P.pts k) (P.pts (k + 1))) :=
      hbdd_above.mono (Set.image_mono (P.subinterval_subset_Icc hk'))
    set Mk := sSup (f '' Set.Icc (P.pts k) (P.pts (k + 1)))
    have hconst : Mk * (P.pts (k + 1) - P.pts k) = ∫ _ in P.pts k..P.pts (k + 1), Mk := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    rw [hconst]
    exact intervalIntegral.integral_mono_on (P.mono k hk')
      (hsub_int k hk') (intervalIntegrable_const) fun x hx ↦ le_csSup habv_k ⟨x, hx, rfl⟩

/-- Whenever `f` is Darboux integrable on `[a, b]` with Darboux integral `I` and
`IntervalIntegrable` in Mathlib, Mathlib's `∫ x in a..b, f x` equals `I`! -/
theorem intervalIntegral_eq_of_isDarbouxIntegrableOn {a b I : ℝ} {f : ℝ → ℝ}
    (hI : IsDarbouxIntegrableOn f a b I)
    (hint : IntervalIntegrable f MeasureTheory.volume a b) :
    ∫ x in a..b, f x = I := by
  obtain ⟨hab, hbel, habv, hbounds, heps⟩ := isDarbouxIntegrableOn_iff_eps.1 hI
  by_contra hne
  have hpos : 0 < |(∫ x in a..b, f x) - I| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨P, hP⟩ := heps |(∫ x in a..b, f x) - I| hpos
  have h1 := hbounds P
  have h2 := darboux_bounds_intervalIntegral hbel habv hint P
  have habs_le : |(∫ x in a..b, f x) - I| ≤ upperDarbouxSum f P - lowerDarbouxSum f P := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  linarith

/-- **Theorem 9.2.1 / 9.2.2 (Connection to Mathlib `intervalIntegral`)**:
For `a ≤ b` and continuous `f` on `[a, b]`,
`∫ x in a..b, f x = hyperIntegral f a b = shadow (hyperRiemannSum f a b omegaNat)`! -/
theorem intervalIntegral_eq_shadow_hyperRiemannSum {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∫ x in a..b, f x = shadow (hyperRiemannSum f a b omegaNat) := by
  have hDarboux := isDarbouxIntegrableOn_of_continuousOn hab hf
  have hint : IntervalIntegrable f MeasureTheory.volume a b :=
    hf.intervalIntegrable_of_Icc hab
  have heq1 : ∫ x in a..b, f x = hyperIntegral f a b :=
    intervalIntegral_eq_of_isDarbouxIntegrableOn hDarboux hint
  have heq2 : shadow (hyperRiemannSum f a b omegaNat) = hyperIntegral f a b :=
    (hyperRiemannSum_infClose_hyperIntegral_of_isDarbouxIntegrableOn
      hDarboux isUnlimitedNat_omegaNat).2.2.2.2
  exact heq1.trans heq2.symm

/-- **Theorem 9.2.1 / 9.2.2**: For `a ≤ b`, continuous `f` on `[a, b]`, and EVERY unlimited
`N ∈ ℕ*`, `hyperRiemannSum f a b N ≈ₕ (∫ x in a..b, f x : ℝ*)` and
`shadow (hyperRiemannSum f a b N) = ∫ x in a..b, f x`. -/
theorem hyperRiemannSum_infClose_intervalIntegral {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) {N : ℕ*} (hN : IsUnlimitedNat N) :
    hyperRiemannSum f a b N ≈ₕ ((∫ x in a..b, f x : ℝ) : ℝ*) ∧
    shadow (hyperRiemannSum f a b N) = ∫ x in a..b, f x := by
  have hDarboux := isDarbouxIntegrableOn_of_continuousOn hab hf
  have hint : IntervalIntegrable f MeasureTheory.volume a b :=
    hf.intervalIntegrable_of_Icc hab
  have heq : ∫ x in a..b, f x = hyperIntegral f a b :=
    intervalIntegral_eq_of_isDarbouxIntegrableOn hDarboux hint
  have h := hyperRiemannSum_infClose_hyperIntegral_of_isDarbouxIntegrableOn hDarboux hN
  rw [heq]
  exact ⟨h.2.2.2.1, h.2.2.2.2⟩

/-- **Theorem 9.2.1 / 9.2.2**: For `a ≤ b`, continuous `f` on `[a, b]`, and EVERY positive
infinitesimal `Δx ∈ ℝ*`, `hyperStepSum f a b Δx ≈ₕ (∫ x in a..b, f x : ℝ*)` and
`shadow (hyperStepSum f a b Δx) = ∫ x in a..b, f x`. -/
theorem hyperStepSum_infClose_intervalIntegral {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) {dx : ℝ*} (hdx : IsPosInfinitesimal dx) :
    hyperStepSum f a b dx ≈ₕ ((∫ x in a..b, f x : ℝ) : ℝ*) ∧
    shadow (hyperStepSum f a b dx) = ∫ x in a..b, f x := by
  have hDarboux := isDarbouxIntegrableOn_of_continuousOn hab hf
  have hint : IntervalIntegrable f MeasureTheory.volume a b :=
    hf.intervalIntegrable_of_Icc hab
  have heq : ∫ x in a..b, f x = hyperIntegral f a b :=
    intervalIntegral_eq_of_isDarbouxIntegrableOn hDarboux hint
  obtain ⟨hbel, habv⟩ := bddBelow_bddAbove_of_continuousOn hf
  have h := hyperStepSums_infClose_hyperIntegral hab hbel habv
    (fun _ hdx' ↦ hyperStepLowerSum_infClose_hyperStepUpperSum hab hf hdx') hdx
  rw [heq]
  exact ⟨h.2.1, h.2.2.2⟩

/-- Monotonic version of Theorem 9.2.1 / 9.2.2: for `a ≤ b`, monotonic `f` on `[a, b]`, and any
positive infinitesimal `Δx`, `shadow (hyperStepSum f a b Δx) = ∫ x in a..b, f x`. -/
theorem hyperStepSum_shadow_eq_intervalIntegral_of_monotonic {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf : IsMonotonicOn f a b) {dx : ℝ*} (hdx : IsPosInfinitesimal dx) :
    shadow (hyperStepSum f a b dx) = ∫ x in a..b, f x := by
  have hDarboux := isDarbouxIntegrableOn_of_isMonotonicOn hab hf
  have hint : IntervalIntegrable f MeasureTheory.volume a b := by
    rcases hf with hmono | hanti
    · exact MonotoneOn.intervalIntegrable (by rwa [Set.uIcc_of_le hab])
    · exact AntitoneOn.intervalIntegrable (by rwa [Set.uIcc_of_le hab])
  have heq : ∫ x in a..b, f x = hyperIntegral f a b :=
    intervalIntegral_eq_of_isDarbouxIntegrableOn hDarboux hint
  obtain ⟨hbel, habv⟩ := bddBelow_bddAbove_of_isMonotonicOn hab hf
  have h := hyperStepSums_infClose_hyperIntegral hab hbel habv
    (fun _ hdx' ↦ hyperStepLowerSum_infClose_hyperStepUpperSum_of_monotonic hab hf hdx') hdx
  exact h.2.2.2.trans heq.symm

/-! ### Explicit Concrete Integrals via Hyperfinite Power Sums and `shadow` -/

/-- Classical sum of first `n` integers in `ℝ`: `2 * ∑_{k < n} k = n * (n - 1)`. -/
theorem two_mul_sum_range_cast (n : ℕ) :
    2 * ∑ k ∈ Finset.range n, (k : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- Classical sum of first `n` squares in `ℝ`:
`6 * ∑_{k < n} k^2 = n * (n - 1) * (2n - 1)`. -/
theorem six_mul_sum_range_sq_cast (n : ℕ) :
    6 * ∑ k ∈ Finset.range n, (k : ℝ) ^ 2 =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- Explicit closed form of `riemannSumEq (fun x ↦ x) 0 b n` for `n ≥ 1`:
`(b^2 / 2) * (1 - 1 / n)`. -/
theorem riemannSumEq_id_zero {b : ℝ} {n : ℕ} (hn : 0 < n) :
    riemannSumEq (fun x ↦ x) 0 b n = (b ^ 2 / 2) * (1 - 1 / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  unfold riemannSumEq
  have hterm : ∀ k ∈ Finset.range n,
      (0 + (k : ℝ) * (b - 0) / (n : ℝ)) * ((b - 0) / (n : ℝ)) =
        (b ^ 2 / (n : ℝ) ^ 2) * (k : ℝ) := fun k _ ↦ by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsum := two_mul_sum_range_cast n
  have hsum' : ∑ k ∈ Finset.range n, (k : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by linarith
  rw [hsum']
  field_simp [hn0]

/-- Explicit closed form of `riemannSumEq (fun x ↦ x^2) 0 b n` for `n ≥ 1`:
`(b^3 / 6) * (1 - 1 / n) * (2 - 1 / n)`. -/
theorem riemannSumEq_sq_zero {b : ℝ} {n : ℕ} (hn : 0 < n) :
    riemannSumEq (fun x ↦ x ^ 2) 0 b n =
      (b ^ 3 / 6) * (1 - 1 / (n : ℝ)) * (2 - 1 / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  unfold riemannSumEq
  have hterm : ∀ k ∈ Finset.range n,
      (0 + (k : ℝ) * (b - 0) / (n : ℝ)) ^ 2 * ((b - 0) / (n : ℝ)) =
        (b ^ 3 / (n : ℝ) ^ 3) * (k : ℝ) ^ 2 := fun k _ ↦ by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsum := six_mul_sum_range_sq_cast n
  have hsum' : ∑ k ∈ Finset.range n, (k : ℝ) ^ 2 =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by linarith
  rw [hsum']
  field_simp [hn0]

/-- Direct hyperfinite-sum evaluation of `hyperRiemannSum (fun x ↦ x) 0 b N ≈ₕ b^2 / 2` and
`∫ x in 0..b, x = b^2 / 2` (for `0 ≤ b`) without using FTC! -/
theorem integral_id_zero_via_hyperRiemannSum {b : ℝ} (hb : 0 ≤ b) :
    hyperRiemannSum (fun x ↦ x) 0 b omegaNat ≈ₕ ((b ^ 2 / 2 : ℝ) : ℝ*) ∧
    shadow (hyperRiemannSum (fun x ↦ x) 0 b omegaNat) = b ^ 2 / 2 ∧
    ∫ x in (0 : ℝ)..b, x = b ^ 2 / 2 := by
  have hpos : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < j :=
    Germ.coe_lt.1 (isUnlimitedNat_omegaNat 0)
  have heq : hyperRiemannSum (fun x ↦ x) 0 b omegaNat =
      ((b ^ 2 / 2 : ℝ) : ℝ*) * (1 - Hyperreal.epsilon) := by
    refine Germ.coe_eq.2 (hpos.mono fun j hj ↦ ?_)
    change riemannSumEq (fun x ↦ x) 0 b j = (b ^ 2 / 2) * (1 - (j : ℝ)⁻¹)
    rw [riemannSumEq_id_zero hj, one_div]
  have h1 : (1 : ℝ*) - Hyperreal.epsilon ≈ₕ (1 : ℝ*) := by
    unfold InfClose
    simpa using isInfinitesimal_epsilon.neg
  have hclose : hyperRiemannSum (fun x ↦ x) 0 b omegaNat ≈ₕ ((b ^ 2 / 2 : ℝ) : ℝ*) := by
    rw [heq]
    have hmul := InfClose.mul_left_of_isLimited (isLimited_coe (b ^ 2 / 2)) h1
    rwa [mul_one] at hmul
  have hsh : shadow (hyperRiemannSum (fun x ↦ x) 0 b omegaNat) = b ^ 2 / 2 :=
    shadow_eq_of_infClose hclose
  have hint : ∫ x in (0 : ℝ)..b, x = b ^ 2 / 2 := by
    rw [intervalIntegral_eq_shadow_hyperRiemannSum (f := fun x ↦ x) hb continuousOn_id, hsh]
  exact ⟨hclose, hsh, hint⟩

/-- Direct hyperfinite-sum evaluation of `hyperRiemannSum (fun x ↦ x^2) 0 b N ≈ₕ b^3 / 3` and
`∫ x in 0..b, x^2 = b^3 / 3` (for `0 ≤ b`) without using FTC! -/
theorem integral_sq_zero_via_hyperRiemannSum {b : ℝ} (hb : 0 ≤ b) :
    hyperRiemannSum (fun x ↦ x ^ 2) 0 b omegaNat ≈ₕ ((b ^ 3 / 3 : ℝ) : ℝ*) ∧
    shadow (hyperRiemannSum (fun x ↦ x ^ 2) 0 b omegaNat) = b ^ 3 / 3 ∧
    ∫ x in (0 : ℝ)..b, x ^ 2 = b ^ 3 / 3 := by
  have hpos : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < j :=
    Germ.coe_lt.1 (isUnlimitedNat_omegaNat 0)
  have heq : hyperRiemannSum (fun x ↦ x ^ 2) 0 b omegaNat =
      ((b ^ 3 / 6 : ℝ) : ℝ*) * ((1 - Hyperreal.epsilon) * (2 - Hyperreal.epsilon)) := by
    refine Germ.coe_eq.2 (hpos.mono fun j hj ↦ ?_)
    change riemannSumEq (fun x ↦ x ^ 2) 0 b j =
      (b ^ 3 / 6) * ((1 - (j : ℝ)⁻¹) * (2 - (j : ℝ)⁻¹))
    rw [riemannSumEq_sq_zero hj, one_div, mul_assoc]
  have h1 : (1 : ℝ*) - Hyperreal.epsilon ≈ₕ (1 : ℝ*) := by
    unfold InfClose; simpa using isInfinitesimal_epsilon.neg
  have h2 : (2 : ℝ*) - Hyperreal.epsilon ≈ₕ (2 : ℝ*) := by
    unfold InfClose; simpa using isInfinitesimal_epsilon.neg
  have hlim1 : IsLimited ((1 : ℝ*) - Hyperreal.epsilon) :=
    (isLimited_coe 1).sub isInfinitesimal_epsilon.isLimited
  have hlim2 : IsLimited ((2 : ℝ*) - Hyperreal.epsilon) :=
    (isLimited_coe 2).sub isInfinitesimal_epsilon.isLimited
  have hprod : (1 - Hyperreal.epsilon) * (2 - Hyperreal.epsilon) ≈ₕ (2 : ℝ*) := by
    simpa using InfClose.mul hlim1 hlim2 h1 h2
  have hclose : hyperRiemannSum (fun x ↦ x ^ 2) 0 b omegaNat ≈ₕ ((b ^ 3 / 3 : ℝ) : ℝ*) := by
    rw [heq]
    have hmul := InfClose.mul_left_of_isLimited (isLimited_coe (b ^ 3 / 6)) hprod
    have hval : ((b ^ 3 / 6 : ℝ) : ℝ*) * (2 : ℝ*) = ((b ^ 3 / 3 : ℝ) : ℝ*) := by
      have : (b ^ 3 / 6) * 2 = b ^ 3 / 3 := by ring
      exact_mod_cast this
    rwa [hval] at hmul
  have hsh : shadow (hyperRiemannSum (fun x ↦ x ^ 2) 0 b omegaNat) = b ^ 3 / 3 :=
    shadow_eq_of_infClose hclose
  have hint : ∫ x in (0 : ℝ)..b, x ^ 2 = b ^ 3 / 3 := by
    rw [intervalIntegral_eq_shadow_hyperRiemannSum hb (continuousOn_pow 2), hsh]
  exact ⟨hclose, hsh, hint⟩

/-! ## §9.3 Standard Properties of the Integral via Hyperfinite Sums -/

/-- Degenerate interval `[a, a]`: `hyperIntegral f a a = 0`. -/
@[simp]
theorem hyperIntegral_self (f : ℝ → ℝ) (a : ℝ) : hyperIntegral f a a = 0 := by
  unfold hyperIntegral hyperStepSum
  rcases ofSeq_surjective Hyperreal.epsilon with ⟨s, hs_eq⟩
  rw [← hs_eq]
  have h0 : starFun (stepRiemannSum f a a) (ofSeq s) = 0 :=
    Germ.coe_eq.2 (Eventually.of_forall fun j ↦ (stepSums_self f a (s j)).2.2)
  rw [h0, shadow_zero]

/-- Constant step-size Riemann sum: `S_a^b(c, Δx) = c(b - a)` for `a ≤ b` and `Δx > 0`. -/
theorem stepRiemannSum_const (c : ℝ) {a b dx : ℝ} (hab : a ≤ b) (hdx : 0 < dx) :
    stepRiemannSum (fun _ ↦ c) a b dx = c * (b - a) := by
  rw [stepRiemannSum_of_pos _ hab hdx]
  unfold partitionRiemannSum
  rw [← Finset.mul_sum, (stepPartition a b hab dx hdx).sum_widths]

/-- Constant hyperreal step-size Riemann sum: `hyperStepSum (fun _ ↦ c) a b dx = c(b - a)`
for `a ≤ b` and `dx > 0` in `ℝ*`. -/
theorem hyperStepSum_const (c : ℝ) {a b : ℝ} (hab : a ≤ b) {dx : ℝ*} (hdx : 0 < dx) :
    hyperStepSum (fun _ ↦ c) a b dx = ((c * (b - a) : ℝ) : ℝ*) := by
  rcases ofSeq_surjective dx with ⟨s, rfl⟩
  have hs : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < s j := ofSeq_lt_ofSeq.1 hdx
  exact Germ.coe_eq.2 (hs.mono fun j hj ↦ stepRiemannSum_const c hab hj)

/-- **Goldblatt §9.3 / Exercise 9.3.1 (Constant Rule, p. 110)**:
`hyperIntegral (fun _ ↦ c) a b = c * (b - a)` for `a ≤ b`, proved via `shadow`. -/
theorem hyperIntegral_const (c : ℝ) {a b : ℝ} (hab : a ≤ b) :
    hyperIntegral (fun _ ↦ c) a b = c * (b - a) := by
  unfold hyperIntegral
  rw [hyperStepSum_const c hab Hyperreal.epsilon_pos, shadow_coe]

/-- Constant rule for `∫ x in a..b, c` proved directly via `hyperIntegral_const`. -/
theorem integral_const_via_shadow (c : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ _ in a..b, c = c * (b - a) := by
  have hDarboux := isDarbouxIntegrableOn_of_continuousOn hab
    (continuousOn_const : ContinuousOn (fun _ ↦ c) _)
  rw [intervalIntegral_eq_of_isDarbouxIntegrableOn hDarboux intervalIntegrable_const,
      hyperIntegral_const c hab]

/-- Scalar homogeneity of `stepRiemannSum`: `S_a^b(c · f, Δx) = c · S_a^b(f, Δx)`. -/
theorem stepRiemannSum_const_mul (c : ℝ) (f : ℝ → ℝ) (a b dx : ℝ) :
    stepRiemannSum (fun x ↦ c * f x) a b dx = c * stepRiemannSum f a b dx := by
  by_cases h : a ≤ b ∧ 0 < dx
  · rw [stepRiemannSum_of_pos _ h.1 h.2, stepRiemannSum_of_pos _ h.1 h.2]
    unfold partitionRiemannSum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_assoc _ _ _
  · simp [stepRiemannSum, h]

/-- Scalar homogeneity of `hyperStepSum`. -/
theorem hyperStepSum_const_mul (c : ℝ) (f : ℝ → ℝ) (a b : ℝ) (dx : ℝ*) :
    hyperStepSum (fun x ↦ c * f x) a b dx = (c : ℝ*) * hyperStepSum f a b dx := by
  rcases ofSeq_surjective dx with ⟨s, rfl⟩
  exact Germ.coe_eq.2 (Eventually.of_forall fun j ↦ stepRiemannSum_const_mul c f a b (s j))

/-- **Goldblatt §9.3 / Exercise 9.3.1 (Scalar Linearity, p. 110)**:
`hyperIntegral (fun x ↦ c * f x) a b = c * hyperIntegral f a b` via `shadow_mul`. -/
theorem hyperIntegral_const_mul (c : ℝ) {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hbdd_below : BddBelow (f '' Set.Icc a b)) (hbdd_above : BddAbove (f '' Set.Icc a b)) :
    hyperIntegral (fun x ↦ c * f x) a b = c * hyperIntegral f a b := by
  have hlim := (hyperStepSums_isLimited hab hbdd_below hbdd_above Hyperreal.epsilon_pos).2.1
  unfold hyperIntegral
  rw [hyperStepSum_const_mul, shadow_mul (isLimited_coe c) hlim, shadow_coe]

/-- Scalar linearity for `∫ x in a..b, c * f x` proved directly via `hyperIntegral_const_mul`. -/
theorem integral_const_mul_via_shadow (c : ℝ) {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∫ x in a..b, c * f x = c * ∫ x in a..b, f x := by
  have hcf : ContinuousOn (fun x ↦ c * f x) (Set.Icc a b) := continuousOn_const.mul hf
  obtain ⟨hbel, habv⟩ := bddBelow_bddAbove_of_continuousOn hf
  rw [intervalIntegral_eq_of_isDarbouxIntegrableOn
        (isDarbouxIntegrableOn_of_continuousOn hab hcf) (hcf.intervalIntegrable_of_Icc hab),
      intervalIntegral_eq_of_isDarbouxIntegrableOn
        (isDarbouxIntegrableOn_of_continuousOn hab hf) (hf.intervalIntegrable_of_Icc hab),
      hyperIntegral_const_mul c hab hbel habv]

/-- Scalar-action (`•`) version of linearity via `shadow`. -/
theorem integral_smul_via_shadow (c : ℝ) {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∫ x in a..b, (c • f) x = c * ∫ x in a..b, f x :=
  integral_const_mul_via_shadow c hab hf

/-- Additivity of `stepRiemannSum`: `S_a^b(f + g, Δx) = S_a^b(f, Δx) + S_a^b(g, Δx)`. -/
theorem stepRiemannSum_add (f g : ℝ → ℝ) (a b dx : ℝ) :
    stepRiemannSum (fun x ↦ f x + g x) a b dx =
      stepRiemannSum f a b dx + stepRiemannSum g a b dx := by
  by_cases h : a ≤ b ∧ 0 < dx
  · rw [stepRiemannSum_of_pos _ h.1 h.2, stepRiemannSum_of_pos _ h.1 h.2,
        stepRiemannSum_of_pos _ h.1 h.2]
    unfold partitionRiemannSum
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ add_mul _ _ _
  · simp [stepRiemannSum, h]

/-- Additivity of `hyperStepSum`. -/
theorem hyperStepSum_add (f g : ℝ → ℝ) (a b : ℝ) (dx : ℝ*) :
    hyperStepSum (fun x ↦ f x + g x) a b dx =
      hyperStepSum f a b dx + hyperStepSum g a b dx := by
  rcases ofSeq_surjective dx with ⟨s, rfl⟩
  exact Germ.coe_eq.2 (Eventually.of_forall fun j ↦ stepRiemannSum_add f g a b (s j))

/-- **Goldblatt §9.3 / Exercise 9.3.1 (Additivity, p. 110)**:
`hyperIntegral (f + g) a b = hyperIntegral f a b + hyperIntegral g a b` via `shadow_add`. -/
theorem hyperIntegral_add {a b : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
    (hf_bel : BddBelow (f '' Set.Icc a b)) (hf_abv : BddAbove (f '' Set.Icc a b))
    (hg_bel : BddBelow (g '' Set.Icc a b)) (hg_abv : BddAbove (g '' Set.Icc a b)) :
    hyperIntegral (fun x ↦ f x + g x) a b = hyperIntegral f a b + hyperIntegral g a b := by
  have hlim_f := (hyperStepSums_isLimited hab hf_bel hf_abv Hyperreal.epsilon_pos).2.1
  have hlim_g := (hyperStepSums_isLimited hab hg_bel hg_abv Hyperreal.epsilon_pos).2.1
  unfold hyperIntegral
  rw [hyperStepSum_add, shadow_add hlim_f hlim_g]

/-- Subtraction rule for `hyperIntegral` via `hyperIntegral_add` and `hyperIntegral_const_mul`. -/
theorem hyperIntegral_sub {a b : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
    (hf_bel : BddBelow (f '' Set.Icc a b)) (hf_abv : BddAbove (f '' Set.Icc a b))
    (hg_bel : BddBelow (g '' Set.Icc a b)) (hg_abv : BddAbove (g '' Set.Icc a b)) :
    hyperIntegral (fun x ↦ f x - g x) a b = hyperIntegral f a b - hyperIntegral g a b := by
  have hneg_bel : BddBelow ((fun x ↦ (-1 : ℝ) * g x) '' Set.Icc a b) := by
    rcases hg_abv with ⟨M, hM⟩
    exact ⟨-M, fun _ ⟨x, hx, hgx⟩ ↦ hgx ▸ by linarith [hM ⟨x, hx, rfl⟩]⟩
  have hneg_abv : BddAbove ((fun x ↦ (-1 : ℝ) * g x) '' Set.Icc a b) := by
    rcases hg_bel with ⟨m, hm⟩
    exact ⟨-m, fun _ ⟨x, hx, hgx⟩ ↦ hgx ▸ by linarith [hm ⟨x, hx, rfl⟩]⟩
  have hfg : (fun x ↦ f x - g x) = (fun x ↦ f x + (-1 : ℝ) * g x) := by ext x; ring
  rw [hfg, hyperIntegral_add hab hf_bel hf_abv hneg_bel hneg_abv,
      hyperIntegral_const_mul (-1) hab hg_bel hg_abv]
  ring

/-- Additivity for `∫ x in a..b, (f x + g x)` proved directly via `hyperIntegral_add`. -/
theorem integral_add_via_shadow {a b : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b)) :
    ∫ x in a..b, (f x + g x) = (∫ x in a..b, f x) + ∫ x in a..b, g x := by
  have hfg : ContinuousOn (fun x ↦ f x + g x) (Set.Icc a b) := hf.add hg
  obtain ⟨hf_bel, hf_abv⟩ := bddBelow_bddAbove_of_continuousOn hf
  obtain ⟨hg_bel, hg_abv⟩ := bddBelow_bddAbove_of_continuousOn hg
  rw [intervalIntegral_eq_of_isDarbouxIntegrableOn
        (isDarbouxIntegrableOn_of_continuousOn hab hfg) (hfg.intervalIntegrable_of_Icc hab),
      intervalIntegral_eq_of_isDarbouxIntegrableOn
        (isDarbouxIntegrableOn_of_continuousOn hab hf) (hf.intervalIntegrable_of_Icc hab),
      intervalIntegral_eq_of_isDarbouxIntegrableOn
        (isDarbouxIntegrableOn_of_continuousOn hab hg) (hg.intervalIntegrable_of_Icc hab),
      hyperIntegral_add hab hf_bel hf_abv hg_bel hg_abv]

/-- Monotonicity of `stepRiemannSum`: `f ≤ g` on `[a, b]` implies `S_a^b(f, Δx) ≤ S_a^b(g, Δx)`. -/
theorem stepRiemannSum_mono {a b : ℝ} {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) (dx : ℝ) :
    stepRiemannSum f a b dx ≤ stepRiemannSum g a b dx := by
  by_cases h : a ≤ b ∧ 0 < dx
  · rw [stepRiemannSum_of_pos f h.1 h.2, stepRiemannSum_of_pos g h.1 h.2]
    let P := stepPartition a b h.1 dx h.2
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hk' := Finset.mem_range.1 hk
    exact mul_le_mul_of_nonneg_right (hfg (P.pts k) (P.pts_mem_Icc hk'.le)) (P.width_nonneg hk')
  · simp [stepRiemannSum, h]

/-- Monotonicity of `hyperStepSum`. -/
theorem hyperStepSum_mono {a b : ℝ} {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) (dx : ℝ*) :
    hyperStepSum f a b dx ≤ hyperStepSum g a b dx := by
  rcases ofSeq_surjective dx with ⟨s, rfl⟩
  exact ofSeq_le_ofSeq.2 (Eventually.of_forall fun j ↦ stepRiemannSum_mono hfg (s j))

/-- **Goldblatt §9.3 / Exercise 9.3.1 (Monotonicity, p. 110)**:
`f ≤ g` on `[a, b]` implies `hyperIntegral f a b ≤ hyperIntegral g a b` via `shadow_le_of_le`. -/
theorem hyperIntegral_mono {a b : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
    (hf_bel : BddBelow (f '' Set.Icc a b)) (hf_abv : BddAbove (f '' Set.Icc a b))
    (hg_bel : BddBelow (g '' Set.Icc a b)) (hg_abv : BddAbove (g '' Set.Icc a b))
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    hyperIntegral f a b ≤ hyperIntegral g a b := by
  have hlim_f := (hyperStepSums_isLimited hab hf_bel hf_abv Hyperreal.epsilon_pos).2.1
  have hlim_g := (hyperStepSums_isLimited hab hg_bel hg_abv Hyperreal.epsilon_pos).2.1
  exact shadow_le_of_le hlim_f hlim_g (hyperStepSum_mono hfg Hyperreal.epsilon)

/-- Monotonicity for `∫ x in a..b` proved directly via `hyperIntegral_mono`. -/
theorem integral_mono_via_shadow {a b : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    ∫ x in a..b, f x ≤ ∫ x in a..b, g x := by
  obtain ⟨hf_bel, hf_abv⟩ := bddBelow_bddAbove_of_continuousOn hf
  obtain ⟨hg_bel, hg_abv⟩ := bddBelow_bddAbove_of_continuousOn hg
  rw [intervalIntegral_eq_of_isDarbouxIntegrableOn
        (isDarbouxIntegrableOn_of_continuousOn hab hf) (hf.intervalIntegrable_of_Icc hab),
      intervalIntegral_eq_of_isDarbouxIntegrableOn
        (isDarbouxIntegrableOn_of_continuousOn hab hg) (hg.intervalIntegrable_of_Icc hab)]
  exact hyperIntegral_mono hab hf_bel hf_abv hg_bel hg_abv hfg

/-- **Goldblatt §9.3 / Exercise 9.3.1 (Boundedness, p. 110)**:
If `m ≤ f(x) ≤ M` on `[a, b]` (`a ≤ b`), then
`m(b - a) ≤ hyperIntegral f a b ≤ M(b - a)`. -/
theorem hyperIntegral_bounds {a b m M : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hlow : ∀ x ∈ Set.Icc a b, m ≤ f x) (hhigh : ∀ x ∈ Set.Icc a b, f x ≤ M) :
    m * (b - a) ≤ hyperIntegral f a b ∧ hyperIntegral f a b ≤ M * (b - a) := by
  have hf_bel : BddBelow (f '' Set.Icc a b) := ⟨m, fun _ ⟨x, hx, hfx⟩ ↦ hfx ▸ hlow x hx⟩
  have hf_abv : BddAbove (f '' Set.Icc a b) := ⟨M, fun _ ⟨x, hx, hfx⟩ ↦ hfx ▸ hhigh x hx⟩
  have hm_bel : BddBelow ((fun _ ↦ m) '' Set.Icc a b) := ⟨m, fun _ ⟨_, _, h⟩ ↦ h ▸ le_rfl⟩
  have hm_abv : BddAbove ((fun _ ↦ m) '' Set.Icc a b) := ⟨m, fun _ ⟨_, _, h⟩ ↦ h ▸ le_rfl⟩
  have hM_bel : BddBelow ((fun _ ↦ M) '' Set.Icc a b) := ⟨M, fun _ ⟨_, _, h⟩ ↦ h ▸ le_rfl⟩
  have hM_abv : BddAbove ((fun _ ↦ M) '' Set.Icc a b) := ⟨M, fun _ ⟨_, _, h⟩ ↦ h ▸ le_rfl⟩
  refine ⟨?_, ?_⟩
  · rw [← hyperIntegral_const m hab]
    exact hyperIntegral_mono hab hm_bel hm_abv hf_bel hf_abv hlow
  · rw [← hyperIntegral_const M hab]
    exact hyperIntegral_mono hab hf_bel hf_abv hM_bel hM_abv hhigh

/-- Boundedness for `∫ x in a..b, f x` proved directly via `hyperIntegral_bounds`. -/
theorem integral_bounds_via_shadow {a b m M : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hlow : ∀ x ∈ Set.Icc a b, m ≤ f x) (hhigh : ∀ x ∈ Set.Icc a b, f x ≤ M) :
    m * (b - a) ≤ ∫ x in a..b, f x ∧ ∫ x in a..b, f x ≤ M * (b - a) := by
  rw [intervalIntegral_eq_of_isDarbouxIntegrableOn
        (isDarbouxIntegrableOn_of_continuousOn hab hf) (hf.intervalIntegrable_of_Icc hab)]
  exact hyperIntegral_bounds hab hlow hhigh

/-- Pointwise triangle inequality for `stepRiemannSum`:
`|S_a^b(f, Δx)| ≤ S_a^b(|f|, Δx)`. -/
theorem abs_stepRiemannSum_le (f : ℝ → ℝ) (a b dx : ℝ) :
    |stepRiemannSum f a b dx| ≤ stepRiemannSum (fun x ↦ |f x|) a b dx := by
  by_cases h : a ≤ b ∧ 0 < dx
  · rw [stepRiemannSum_of_pos f h.1 h.2, stepRiemannSum_of_pos (fun x ↦ |f x|) h.1 h.2]
    let P := stepPartition a b h.1 dx h.2
    unfold partitionRiemannSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
    have hk' := Finset.mem_range.1 hk
    rw [abs_mul, abs_of_nonneg (P.width_nonneg hk')]
  · simp [stepRiemannSum, h]

/-- Hyperreal triangle inequality for `hyperStepSum`:
`|hyperStepSum f a b dx| ≤ hyperStepSum |f| a b dx`. -/
theorem abs_hyperStepSum_le (f : ℝ → ℝ) (a b : ℝ) (dx : ℝ*) :
    |hyperStepSum f a b dx| ≤ hyperStepSum (fun x ↦ |f x|) a b dx := by
  rcases ofSeq_surjective dx with ⟨s, rfl⟩
  exact ofSeq_le_ofSeq.2 (Eventually.of_forall fun j ↦ abs_stepRiemannSum_le f a b (s j))

/-- Triangle inequality for `hyperIntegral`: `|hyperIntegral f a b| ≤ hyperIntegral |f| a b`. -/
theorem abs_hyperIntegral_le {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf_bel : BddBelow (f '' Set.Icc a b)) (hf_abv : BddAbove (f '' Set.Icc a b)) :
    |hyperIntegral f a b| ≤ hyperIntegral (fun x ↦ |f x|) a b := by
  rcases hf_bel with ⟨m, hm⟩
  rcases hf_abv with ⟨M, hM⟩
  have habs_bel : BddBelow ((fun x ↦ |f x|) '' Set.Icc a b) :=
    ⟨0, fun _ ⟨x, _, hfx⟩ ↦ hfx ▸ abs_nonneg (f x)⟩
  have habs_abv : BddAbove ((fun x ↦ |f x|) '' Set.Icc a b) := by
    refine ⟨max |m| |M|, fun _ ⟨x, hx, hfx⟩ ↦ hfx ▸ ?_⟩
    dsimp only
    have hlow : m ≤ f x := hm ⟨x, hx, rfl⟩
    have hhigh : f x ≤ M := hM ⟨x, hx, rfl⟩
    rcases le_or_gt 0 (f x) with hnn | hneg
    · rw [abs_of_nonneg hnn]
      exact hhigh.trans ((le_abs_self M).trans (le_max_right |m| |M|))
    · rw [abs_of_neg hneg]
      have : -f x ≤ -m := by linarith
      exact this.trans ((neg_le_abs m).trans (le_max_left |m| |M|))
  have hlim_f := (hyperStepSums_isLimited hab ⟨m, hm⟩ ⟨M, hM⟩ Hyperreal.epsilon_pos).2.1
  have hlim_abs := (hyperStepSums_isLimited hab habs_bel habs_abv Hyperreal.epsilon_pos).2.1
  unfold hyperIntegral
  rw [← shadow_abs]
  exact shadow_le_of_le hlim_f.abs hlim_abs (abs_hyperStepSum_le f a b Hyperreal.epsilon)

/-- Triangle inequality `|∫ x in a..b, f x| ≤ ∫ x in a..b, |f x|` proved via `shadow`. -/
theorem abs_integral_le_via_shadow {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    |∫ x in a..b, f x| ≤ ∫ x in a..b, |f x| := by
  have habs : ContinuousOn (fun x ↦ |f x|) (Set.Icc a b) := hf.abs
  obtain ⟨hf_bel, hf_abv⟩ := bddBelow_bddAbove_of_continuousOn hf
  rw [intervalIntegral_eq_of_isDarbouxIntegrableOn
        (isDarbouxIntegrableOn_of_continuousOn hab hf) (hf.intervalIntegrable_of_Icc hab),
      intervalIntegral_eq_of_isDarbouxIntegrableOn
        (isDarbouxIntegrableOn_of_continuousOn hab habs) (habs.intervalIntegrable_of_Icc hab)]
  exact abs_hyperIntegral_le hab hf_bel hf_abv

/-- Ceiling shift helper: `⌈(n : ℝ) + x⌉₊ = n + ⌈x⌉₊` for `n : ℕ` and `0 ≤ x`. -/
private theorem nat_ceil_natCast_add {n : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    ⌈(n : ℝ) + x⌉₊ = n + ⌈x⌉₊ := by
  apply le_antisymm
  · refine Nat.ceil_le.2 ?_
    rw [Nat.cast_add]
    linarith [Nat.le_ceil x]
  · rcases eq_or_lt_of_le (Nat.zero_le ⌈x⌉₊) with hm0 | hm_pos
    · have hx0 : x ≤ 0 := by
        have := Nat.le_ceil x
        rw [← hm0] at this
        simpa using this
      have hxeq : x = 0 := le_antisymm hx0 hx
      simp [hxeq]
    · have hlt : ((⌈x⌉₊ - 1 : ℕ) : ℝ) < x := Nat.lt_ceil.1 (Nat.sub_lt hm_pos Nat.zero_lt_one)
      have hlt_sum : ((n + (⌈x⌉₊ - 1) : ℕ) : ℝ) < (n : ℝ) + x := by
        rw [Nat.cast_add]; linarith
      have hlt_ceil : n + (⌈x⌉₊ - 1) < ⌈(n : ℝ) + x⌉₊ := Nat.lt_ceil.2 hlt_sum
      omega

/-- **Goldblatt §9.3 (eq. (iv), p. 110)**: Exact aligned-step juxtaposition for `stepRiemannSum`,
`stepUpperSum`, and `stepLowerSum` when `Δx = (c - a) / n` (`a < c ≤ b`, `n > 0`)! -/
theorem stepSums_juxtaposition_div {a c b : ℝ} (f : ℝ → ℝ) (hac : a < c) (hcb : c ≤ b)
    {n : ℕ} (hn : 0 < n) :
    stepRiemannSum f a b ((c - a) / (n : ℝ)) =
      stepRiemannSum f a c ((c - a) / (n : ℝ)) + stepRiemannSum f c b ((c - a) / (n : ℝ)) ∧
    stepUpperSum f a b ((c - a) / (n : ℝ)) =
      stepUpperSum f a c ((c - a) / (n : ℝ)) + stepUpperSum f c b ((c - a) / (n : ℝ)) ∧
    stepLowerSum f a b ((c - a) / (n : ℝ)) =
      stepLowerSum f a c ((c - a) / (n : ℝ)) + stepLowerSum f c b ((c - a) / (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hca_pos : 0 < c - a := sub_pos.2 hac
  set dx : ℝ := (c - a) / (n : ℝ)
  have hdx : 0 < dx := div_pos hca_pos hn_pos
  have hab : a ≤ b := hac.le.trans hcb
  let Pab := stepPartition a b hab dx hdx
  let Pac := stepPartition a c hac.le dx hdx
  let Pcb := stepPartition c b hcb dx hdx
  have hPac_n : Pac.n = n := by
    change ⌈(c - a) / ((c - a) / (n : ℝ))⌉₊ = n
    rw [div_div_cancel₀ hca_pos.ne', Nat.ceil_natCast]
  have hPab_n : Pab.n = n + Pcb.n := by
    change ⌈(b - a) / dx⌉₊ = n + ⌈(b - c) / dx⌉₊
    have hsplit : (b - a) / dx = (n : ℝ) + (b - c) / dx := by
      have h1 : (c - a) / dx = (n : ℝ) := div_div_cancel₀ hca_pos.ne'
      have h2 : (b - a) / dx = (c - a) / dx + (b - c) / dx := by ring
      rw [h2, h1]
    rw [hsplit]
    exact nat_ceil_natCast_add (div_nonneg (sub_nonneg.2 hcb) hdx.le)
  have hndxc : a + (n : ℝ) * dx = c := by
    change a + (n : ℝ) * ((c - a) / (n : ℝ)) = c
    rw [mul_div_cancel₀ _ hn_pos.ne']
    ring
  have hleft_pts : ∀ k ≤ n, Pab.pts k = Pac.pts k := by
    intro k hk
    change min (a + (k : ℝ) * dx) b = min (a + (k : ℝ) * dx) c
    have hle_c : a + (k : ℝ) * dx ≤ c := by
      have hk_le : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hk
      nlinarith [hdx.le]
    rw [min_eq_left (hle_c.trans hcb), min_eq_left hle_c]
  have hright_pts : ∀ j : ℕ, Pab.pts (n + j) = Pcb.pts j := by
    intro j
    change min (a + ((n + j : ℕ) : ℝ) * dx) b = min (c + (j : ℝ) * dx) b
    congr 1
    push_cast
    linarith [hndxc]
  rw [stepRiemannSum_of_pos f hab hdx, stepRiemannSum_of_pos f hac.le hdx,
      stepRiemannSum_of_pos f hcb hdx,
      stepUpperSum_of_pos f hab hdx, stepUpperSum_of_pos f hac.le hdx,
      stepUpperSum_of_pos f hcb hdx,
      stepLowerSum_of_pos f hab hdx, stepLowerSum_of_pos f hac.le hdx,
      stepLowerSum_of_pos f hcb hdx]
  change (partitionRiemannSum f Pab = partitionRiemannSum f Pac + partitionRiemannSum f Pcb) ∧
         (upperDarbouxSum f Pab = upperDarbouxSum f Pac + upperDarbouxSum f Pcb) ∧
         (lowerDarbouxSum f Pab = lowerDarbouxSum f Pac + lowerDarbouxSum f Pcb)
  unfold partitionRiemannSum upperDarbouxSum lowerDarbouxSum
  rw [hPab_n, hPac_n, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
  refine ⟨congrArg₂ (· + ·) ?_ ?_, congrArg₂ (· + ·) ?_ ?_, congrArg₂ (· + ·) ?_ ?_⟩
  · refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' := Finset.mem_range.1 hk
    rw [hleft_pts k hk'.le, hleft_pts (k + 1) (Nat.succ_le_of_lt hk')]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hright_pts j, show n + j + 1 = n + (j + 1) by omega, hright_pts (j + 1)]
  · refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' := Finset.mem_range.1 hk
    rw [hleft_pts k hk'.le, hleft_pts (k + 1) (Nat.succ_le_of_lt hk')]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hright_pts j, show n + j + 1 = n + (j + 1) by omega, hright_pts (j + 1)]
  · refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' := Finset.mem_range.1 hk
    rw [hleft_pts k hk'.le, hleft_pts (k + 1) (Nat.succ_le_of_lt hk')]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hright_pts j, show n + j + 1 = n + (j + 1) by omega, hright_pts (j + 1)]

/-- Transfer of Goldblatt's equation (iv) (p. 110) to `Δx = (c - a) / N` for any `N > 0` in `ℕ*`. -/
theorem hyperStepSums_juxtaposition_div {a c b : ℝ} (f : ℝ → ℝ) (hac : a < c) (hcb : c ≤ b)
    {N : ℕ*} (hN : (0 : ℕ*) < N) :
    let dx := ((c - a : ℝ) : ℝ*) / Hypernat.toHyperreal N
    hyperStepSum f a b dx = hyperStepSum f a c dx + hyperStepSum f c b dx ∧
    hyperStepUpperSum f a b dx = hyperStepUpperSum f a c dx + hyperStepUpperSum f c b dx ∧
    hyperStepLowerSum f a b dx = hyperStepLowerSum f a c dx + hyperStepLowerSum f c b dx := by
  induction N using Germ.inductionOn with | _ u =>
  have hu : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < u j := Germ.coe_lt.1 hN
  exact ⟨Germ.coe_eq.2 (hu.mono fun j hj ↦ (stepSums_juxtaposition_div f hac hcb hj).1),
         Germ.coe_eq.2 (hu.mono fun j hj ↦ (stepSums_juxtaposition_div f hac hcb hj).2.1),
         Germ.coe_eq.2 (hu.mono fun j hj ↦ (stepSums_juxtaposition_div f hac hcb hj).2.2)⟩

/-- Nonstandard subinterval Darboux integrability and **Goldblatt §9.3 Juxtaposition / Chasles'
Relation** (p. 110): if `f` is Darboux integrable on `[a, b]` and `a ≤ c ≤ b`, then `f` is Darboux
integrable on `[a, c]` and `[c, b]`, and
`hyperIntegral f a b = hyperIntegral f a c + hyperIntegral f c b`! -/
theorem hyperIntegral_juxtaposition {a c b I : ℝ} {f : ℝ → ℝ}
    (hI : IsDarbouxIntegrableOn f a b I) (hac : a ≤ c) (hcb : c ≤ b) :
    IsDarbouxIntegrableOn f a c (hyperIntegral f a c) ∧
    IsDarbouxIntegrableOn f c b (hyperIntegral f c b) ∧
    hyperIntegral f a b = hyperIntegral f a c + hyperIntegral f c b := by
  have hab : a ≤ b := hac.trans hcb
  have hbel_ab := hI.2.1
  have habv_ab := hI.2.2.1
  have hbel_ac : BddBelow (f '' Set.Icc a c) :=
    hbel_ab.mono (Set.image_mono (Set.Icc_subset_Icc_right hcb))
  have habv_ac : BddAbove (f '' Set.Icc a c) :=
    habv_ab.mono (Set.image_mono (Set.Icc_subset_Icc_right hcb))
  have hbel_cb : BddBelow (f '' Set.Icc c b) :=
    hbel_ab.mono (Set.image_mono (Set.Icc_subset_Icc_left hac))
  have habv_cb : BddAbove (f '' Set.Icc c b) :=
    habv_ab.mono (Set.image_mono (Set.Icc_subset_Icc_left hac))
  have hOsc_ab := (exists_isDarbouxIntegrableOn_iff_infClose hab hbel_ab habv_ab).1 ⟨I, hI⟩
  rcases eq_or_lt_of_le hac with rfl | hlt_ac
  · have hD_aa : IsDarbouxIntegrableOn f a a (hyperIntegral f a a) :=
      isDarbouxIntegrableOn_hyperIntegral le_rfl hbel_ac habv_ac fun dx _ ↦ by
        rcases ofSeq_surjective dx with ⟨s, rfl⟩
        have h1 : hyperStepLowerSum f a a (ofSeq s) = 0 :=
          Germ.coe_eq.2 (Eventually.of_forall fun j ↦ (stepSums_self f a (s j)).2.1)
        have h2 : hyperStepUpperSum f a a (ofSeq s) = 0 :=
          Germ.coe_eq.2 (Eventually.of_forall fun j ↦ (stepSums_self f a (s j)).1)
        rw [h1, h2]
    have hD_ab : IsDarbouxIntegrableOn f a b (hyperIntegral f a b) :=
      isDarbouxIntegrableOn_hyperIntegral hab hbel_ab habv_ab hOsc_ab
    refine ⟨hD_aa, hD_ab, ?_⟩
    rw [hyperIntegral_self, zero_add]
  · -- Use Goldblatt's aligned infinitesimal `dx₀ = (c - a) / ω_ℕ`!
    let dx₀ : ℝ* := ((c - a : ℝ) : ℝ*) / Hypernat.toHyperreal omegaNat
    have hdx₀ : IsPosInfinitesimal dx₀ :=
      isPosInfinitesimal_sub_div_hypernat hlt_ac isUnlimitedNat_omegaNat
    have hjux := hyperStepSums_juxtaposition_div f hlt_ac hcb (isUnlimitedNat_omegaNat 0)
    rcases hbel_ab with ⟨m, hm⟩
    rcases habv_ab with ⟨M, hM⟩
    have hlow_ac : ∀ x ∈ Set.Icc a c, m ≤ f x :=
      fun x hx ↦ hm ⟨x, Set.Icc_subset_Icc_right hcb hx, rfl⟩
    have hhigh_ac : ∀ x ∈ Set.Icc a c, f x ≤ M :=
      fun x hx ↦ hM ⟨x, Set.Icc_subset_Icc_right hcb hx, rfl⟩
    have hlow_cb : ∀ x ∈ Set.Icc c b, m ≤ f x :=
      fun x hx ↦ hm ⟨x, Set.Icc_subset_Icc_left hac hx, rfl⟩
    have hhigh_cb : ∀ x ∈ Set.Icc c b, f x ≤ M :=
      fun x hx ↦ hM ⟨x, Set.Icc_subset_Icc_left hac hx, rfl⟩
    have hb_ac := hyperStepSum_bounds hac hlow_ac hhigh_ac hdx₀.1
    have hb_cb := hyperStepSum_bounds hcb hlow_cb hhigh_cb hdx₀.1
    have hnn_ac : 0 ≤ hyperStepUpperSum f a c dx₀ - hyperStepLowerSum f a c dx₀ := by
      linarith [hb_ac.2.1, hb_ac.2.2.1]
    have hnn_cb : 0 ≤ hyperStepUpperSum f c b dx₀ - hyperStepLowerSum f c b dx₀ := by
      linarith [hb_cb.2.1, hb_cb.2.2.1]
    have hsum_osc : (hyperStepUpperSum f a c dx₀ - hyperStepLowerSum f a c dx₀) +
        (hyperStepUpperSum f c b dx₀ - hyperStepLowerSum f c b dx₀) =
        hyperStepUpperSum f a b dx₀ - hyperStepLowerSum f a b dx₀ := by
      linarith [hjux.2.1, hjux.2.2]
    have hinf_ab : IsInfinitesimal
        (hyperStepUpperSum f a b dx₀ - hyperStepLowerSum f a b dx₀) :=
      (hOsc_ab dx₀ hdx₀).symm
    have hinf_ac : IsInfinitesimal
        (hyperStepUpperSum f a c dx₀ - hyperStepLowerSum f a c dx₀) := by
      refine isInfinitesimal_of_abs_le hinf_ab ?_
      have hnn_ab : 0 ≤ hyperStepUpperSum f a b dx₀ - hyperStepLowerSum f a b dx₀ := by linarith
      rw [abs_of_nonneg hnn_ac, abs_of_nonneg hnn_ab]
      linarith
    have hinf_cb : IsInfinitesimal
        (hyperStepUpperSum f c b dx₀ - hyperStepLowerSum f c b dx₀) := by
      refine isInfinitesimal_of_abs_le hinf_ab ?_
      have hnn_ab : 0 ≤ hyperStepUpperSum f a b dx₀ - hyperStepLowerSum f a b dx₀ := by linarith
      rw [abs_of_nonneg hnn_cb, abs_of_nonneg hnn_ab]
      linarith
    -- Deduce Darboux integrability on `[a, c]` and `[c, b]` by existential transfer from `dx₀`!
    have hex_ac : ∃ I₁ : ℝ, IsDarbouxIntegrableOn f a c I₁ := by
      set I₁ := sSup {L : ℝ | ∃ P : IntervalPartition a c, L = lowerDarbouxSum f P}
      refine ⟨I₁, isDarbouxIntegrableOn_iff_eps.2 ⟨hac, hbel_ac, habv_ac, ?_, ?_⟩⟩
      · have hneL : ({L : ℝ | ∃ P : IntervalPartition a c, L = lowerDarbouxSum f P}).Nonempty :=
          ⟨_, IntervalPartition.single a c hac, rfl⟩
        have hbddL : BddAbove {L : ℝ | ∃ P : IntervalPartition a c, L = lowerDarbouxSum f P} :=
          ⟨upperDarbouxSum f (IntervalPartition.single a c hac),
           fun _ ⟨P, hP⟩ ↦ hP ▸ lowerDarbouxSum_le_upperDarbouxSum hbel_ac habv_ac P _⟩
        exact fun P ↦ ⟨le_csSup hbddL ⟨P, rfl⟩,
          csSup_le hneL fun _ ⟨Q, hQ⟩ ↦ hQ ▸ lowerDarbouxSum_le_upperDarbouxSum hbel_ac habv_ac Q P⟩
      · intro ε hε
        have hlt : hyperStepUpperSum f a c dx₀ - hyperStepLowerSum f a c dx₀ < (ε : ℝ*) :=
          (le_abs_self _).trans_lt (hinf_ac ε hε)
        rcases ofSeq_surjective dx₀ with ⟨s, hs_eq⟩
        have hs_pos : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < s j :=
          ofSeq_lt_ofSeq.1 (hs_eq ▸ hdx₀.1)
        rw [← hs_eq] at hlt
        have hs_lt : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ),
            stepUpperSum f a c (s j) - stepLowerSum f a c (s j) < ε :=
          ofSeq_lt_ofSeq.1 hlt
        obtain ⟨j, hj_pos, hj_lt⟩ := (hs_pos.and hs_lt).exists
        rw [stepUpperSum_of_pos f hac hj_pos, stepLowerSum_of_pos f hac hj_pos] at hj_lt
        exact ⟨stepPartition a c hac (s j) hj_pos, hj_lt⟩
    have hex_cb : ∃ I₂ : ℝ, IsDarbouxIntegrableOn f c b I₂ := by
      set I₂ := sSup {L : ℝ | ∃ P : IntervalPartition c b, L = lowerDarbouxSum f P}
      refine ⟨I₂, isDarbouxIntegrableOn_iff_eps.2 ⟨hcb, hbel_cb, habv_cb, ?_, ?_⟩⟩
      · have hneL : ({L : ℝ | ∃ P : IntervalPartition c b, L = lowerDarbouxSum f P}).Nonempty :=
          ⟨_, IntervalPartition.single c b hcb, rfl⟩
        have hbddL : BddAbove {L : ℝ | ∃ P : IntervalPartition c b, L = lowerDarbouxSum f P} :=
          ⟨upperDarbouxSum f (IntervalPartition.single c b hcb),
           fun _ ⟨P, hP⟩ ↦ hP ▸ lowerDarbouxSum_le_upperDarbouxSum hbel_cb habv_cb P _⟩
        exact fun P ↦ ⟨le_csSup hbddL ⟨P, rfl⟩,
          csSup_le hneL fun _ ⟨Q, hQ⟩ ↦ hQ ▸ lowerDarbouxSum_le_upperDarbouxSum hbel_cb habv_cb Q P⟩
      · intro ε hε
        have hlt : hyperStepUpperSum f c b dx₀ - hyperStepLowerSum f c b dx₀ < (ε : ℝ*) :=
          (le_abs_self _).trans_lt (hinf_cb ε hε)
        rcases ofSeq_surjective dx₀ with ⟨s, hs_eq⟩
        have hs_pos : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < s j :=
          ofSeq_lt_ofSeq.1 (hs_eq ▸ hdx₀.1)
        rw [← hs_eq] at hlt
        have hs_lt : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ),
            stepUpperSum f c b (s j) - stepLowerSum f c b (s j) < ε :=
          ofSeq_lt_ofSeq.1 hlt
        obtain ⟨j, hj_pos, hj_lt⟩ := (hs_pos.and hs_lt).exists
        rw [stepUpperSum_of_pos f hcb hj_pos, stepLowerSum_of_pos f hcb hj_pos] at hj_lt
        exact ⟨stepPartition c b hcb (s j) hj_pos, hj_lt⟩
    have hOsc_ac := (exists_isDarbouxIntegrableOn_iff_infClose hac hbel_ac habv_ac).1 hex_ac
    have hOsc_cb := (exists_isDarbouxIntegrableOn_iff_infClose hcb hbel_cb habv_cb).1 hex_cb
    have hD_ac := isDarbouxIntegrableOn_hyperIntegral hac hbel_ac habv_ac hOsc_ac
    have hD_cb := isDarbouxIntegrableOn_hyperIntegral hcb hbel_cb habv_cb hOsc_cb
    have hsh_ab := (hyperStepSums_infClose_hyperIntegral hab ⟨m, hm⟩ ⟨M, hM⟩ hOsc_ab hdx₀).2.2.2
    have hsh_ac := (hyperStepSums_infClose_hyperIntegral hac hbel_ac habv_ac hOsc_ac hdx₀).2.2.2
    have hsh_cb := (hyperStepSums_infClose_hyperIntegral hcb hbel_cb habv_cb hOsc_cb hdx₀).2.2.2
    have hlim_ac := (hyperStepSums_isLimited hac hbel_ac habv_ac hdx₀.1).2.1
    have hlim_cb := (hyperStepSums_isLimited hcb hbel_cb habv_cb hdx₀.1).2.1
    have heq_int : hyperIntegral f a b = hyperIntegral f a c + hyperIntegral f c b := by
      rw [← hsh_ab, ← hsh_ac, ← hsh_cb, hjux.1, shadow_add hlim_ac hlim_cb]
    exact ⟨hD_ac, hD_cb, heq_int⟩

/-- For EVERY positive infinitesimal `Δx`, `hyperStepSum f a b Δx ≈ₕ hyperStepSum f a c Δx +
hyperStepSum f c b Δx` when `f` is continuous on `[a, b]` and `a ≤ c ≤ b`. -/
theorem hyperStepSum_juxtaposition_infClose {a c b : ℝ} {f : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    {dx : ℝ*} (hdx : IsPosInfinitesimal dx) :
    hyperStepSum f a b dx ≈ₕ hyperStepSum f a c dx + hyperStepSum f c b dx := by
  have hab : a ≤ b := hac.trans hcb
  have hD_ab := isDarbouxIntegrableOn_of_continuousOn hab hf
  obtain ⟨_, _, hjux⟩ := hyperIntegral_juxtaposition hD_ab hac hcb
  obtain ⟨hbel_ab, habv_ab⟩ := bddBelow_bddAbove_of_continuousOn hf
  have hfac : ContinuousOn f (Set.Icc a c) := hf.mono (Set.Icc_subset_Icc_right hcb)
  have hfcb : ContinuousOn f (Set.Icc c b) := hf.mono (Set.Icc_subset_Icc_left hac)
  obtain ⟨hbel_ac, habv_ac⟩ := bddBelow_bddAbove_of_continuousOn hfac
  obtain ⟨hbel_cb, habv_cb⟩ := bddBelow_bddAbove_of_continuousOn hfcb
  have h1 := (hyperStepSums_infClose_hyperIntegral hab hbel_ab habv_ab
    (fun _ h ↦ hyperStepLowerSum_infClose_hyperStepUpperSum hab hf h) hdx).2.1
  have h2 := (hyperStepSums_infClose_hyperIntegral hac hbel_ac habv_ac
    (fun _ h ↦ hyperStepLowerSum_infClose_hyperStepUpperSum hac hfac h) hdx).2.1
  have h3 := (hyperStepSums_infClose_hyperIntegral hcb hbel_cb habv_cb
    (fun _ h ↦ hyperStepLowerSum_infClose_hyperStepUpperSum hcb hfcb h) hdx).2.1
  have hsum : hyperStepSum f a c dx + hyperStepSum f c b dx ≈ₕ (hyperIntegral f a b : ℝ*) := by
    rw [hjux, Hyperreal.coe_add]
    exact h2.add h3
  exact h1.trans hsum.symm

/-- Interval additivity (Chasles' relation) `∫_a^b f = ∫_a^c f + ∫_c^b f` for `a ≤ c ≤ b` and
continuous `f`, proved directly via Goldblatt's nonstandard `hyperIntegral_juxtaposition`! -/
theorem integral_juxtaposition_via_shadow {a c b : ℝ} {f : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (hf : ContinuousOn f (Set.Icc a b)) :
    ∫ x in a..b, f x = (∫ x in a..c, f x) + ∫ x in c..b, f x := by
  have hab : a ≤ b := hac.trans hcb
  have hfac : ContinuousOn f (Set.Icc a c) := hf.mono (Set.Icc_subset_Icc_right hcb)
  have hfcb : ContinuousOn f (Set.Icc c b) := hf.mono (Set.Icc_subset_Icc_left hac)
  have hD_ab := isDarbouxIntegrableOn_of_continuousOn hab hf
  obtain ⟨hD_ac, hD_cb, hjux⟩ := hyperIntegral_juxtaposition hD_ab hac hcb
  rw [intervalIntegral_eq_of_isDarbouxIntegrableOn hD_ab (hf.intervalIntegrable_of_Icc hab),
      intervalIntegral_eq_of_isDarbouxIntegrableOn hD_ac (hfac.intervalIntegrable_of_Icc hac),
      intervalIntegral_eq_of_isDarbouxIntegrableOn hD_cb (hfcb.intervalIntegrable_of_Icc hcb),
      hjux]

/-! ## §9.4 Differentiating the Area Function & Fundamental Theorem of Calculus -/

/-- Goldblatt §9.4 (p. 111): The area function `F(x) = ∫_a^x f(t) dt`, defined nonstandardly as
`shadow (hyperRiemannSum f a x omegaNat)`. -/
def areaFun (f : ℝ → ℝ) (a : ℝ) (x : ℝ) : ℝ :=
  shadow (hyperRiemannSum f a x omegaNat)

/-- At the lower endpoint `a`, `areaFun f a a = 0`. -/
@[simp]
theorem areaFun_self (f : ℝ → ℝ) (a : ℝ) : areaFun f a a = 0 := by
  simp [areaFun]

/-- On `[a, b]`, `areaFun f a x` agrees with `hyperIntegral f a x` and `∫ t in a..x, f t` when `f`
is continuous on `[a, b]`. -/
theorem areaFun_eq_hyperIntegral_and_intervalIntegral {a b x : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hx : x ∈ Set.Icc a b) :
    areaFun f a x = hyperIntegral f a x ∧ areaFun f a x = ∫ t in a..x, f t := by
  have hfax : ContinuousOn f (Set.Icc a x) := hf.mono (Set.Icc_subset_Icc_right hx.2)
  have hD := isDarbouxIntegrableOn_of_continuousOn hx.1 hfax
  have h1 : areaFun f a x = hyperIntegral f a x :=
    (hyperRiemannSum_infClose_hyperIntegral_of_isDarbouxIntegrableOn
      hD isUnlimitedNat_omegaNat).2.2.2.2
  have h2 : ∫ t in a..x, f t = areaFun f a x :=
    intervalIntegral_eq_shadow_hyperRiemannSum hx.1 hfax
  exact ⟨h1, h2.symm⟩

/-- Nonstandard juxtaposition of `areaFun`: for `x, y ∈ [a, b]` with `x ≤ y`,
`areaFun f a y - areaFun f a x = hyperIntegral f x y`. -/
theorem areaFun_sub_eq_hyperIntegral {a b x y : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (hxy : x ≤ y) :
    areaFun f a y - areaFun f a x = hyperIntegral f x y := by
  have hfay : ContinuousOn f (Set.Icc a y) := hf.mono (Set.Icc_subset_Icc_right hy.2)
  have hD_ay := isDarbouxIntegrableOn_of_continuousOn hy.1 hfay
  obtain ⟨_, _, hjux⟩ := hyperIntegral_juxtaposition hD_ay hx.1 hxy
  rw [(areaFun_eq_hyperIntegral_and_intervalIntegral hf hy).1,
      (areaFun_eq_hyperIntegral_and_intervalIntegral hf hx).1, hjux]
  ring

/-- **Goldblatt §9.4 (eq. (v), pp. 111–112)**: Real extreme-value sandwich before transfer.
For `c ∈ [a, b]` and continuous `f` on `[a, b]`, there exist functions `xMin, xMax : ℝ → ℝ`
such that for every nonzero `t` with `c + t ∈ [a, b]`:
`xMin t, xMax t ∈ [a, b]`, `|xMin t - c| ≤ |t|`, `|xMax t - c| ≤ |t|`, and
`f (xMin t) ≤ (areaFun f a (c + t) - areaFun f a c) / t ≤ f (xMax t)`. -/
theorem exists_areaFun_slope_witness {a b c : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hc : c ∈ Set.Icc a b) :
    ∃ xMin xMax : ℝ → ℝ, ∀ t : ℝ, t ≠ 0 → c + t ∈ Set.Icc a b →
      xMin t ∈ Set.Icc a b ∧ xMax t ∈ Set.Icc a b ∧
      |xMin t - c| ≤ |t| ∧ |xMax t - c| ≤ |t| ∧
      f (xMin t) ≤ (areaFun f a (c + t) - areaFun f a c) / t ∧
      (areaFun f a (c + t) - areaFun f a c) / t ≤ f (xMax t) := by
  have hex : ∀ t : ℝ, ∃ xm xM : ℝ,
      (t ≠ 0 → c + t ∈ Set.Icc a b →
        xm ∈ Set.Icc a b ∧ xM ∈ Set.Icc a b ∧
        |xm - c| ≤ |t| ∧ |xM - c| ≤ |t| ∧
        f xm ≤ (areaFun f a (c + t) - areaFun f a c) / t ∧
        (areaFun f a (c + t) - areaFun f a c) / t ≤ f xM) := by
    intro t
    by_cases ht : t ≠ 0 ∧ c + t ∈ Set.Icc a b
    · obtain ⟨ht_ne, hct_mem⟩ := ht
      rcases lt_or_gt_of_ne ht_ne with ht_neg | ht_pos
      · -- Negative increment `t < 0`: work on `[c + t, c] ⊆ [a, b]`
        have hle : c + t ≤ c := by linarith
        have hsub : Set.Icc (c + t) c ⊆ Set.Icc a b := Set.Icc_subset_Icc hct_mem.1 hc.2
        have hne : (Set.Icc (c + t) c).Nonempty := ⟨c + t, le_rfl, hle⟩
        obtain ⟨xm, hxm_mem, hxm_min⟩ := isCompact_Icc.exists_isMinOn hne (hf.mono hsub)
        obtain ⟨xM, hxM_mem, hxM_max⟩ := isCompact_Icc.exists_isMaxOn hne (hf.mono hsub)
        have hdiff := areaFun_sub_eq_hyperIntegral hf hct_mem hc hle
        have hb := hyperIntegral_bounds hle hxm_min hxM_max
        have hneg_pos : 0 < -t := neg_pos.2 ht_neg
        have hlen : c - (c + t) = -t := by ring
        rw [hlen] at hb
        have hquot : (areaFun f a (c + t) - areaFun f a c) / t =
            hyperIntegral f (c + t) c / (-t) := by
          rw [← hdiff]
          ring
        refine ⟨xm, xM, fun _ _ ↦ ⟨hsub hxm_mem, hsub hxM_mem, ?_, ?_, ?_, ?_⟩⟩
        · rw [abs_of_neg ht_neg, abs_le]
          exact ⟨by linarith [hxm_mem.1, hxm_mem.2], by linarith [hxm_mem.1, hxm_mem.2]⟩
        · rw [abs_of_neg ht_neg, abs_le]
          exact ⟨by linarith [hxM_mem.1, hxM_mem.2], by linarith [hxM_mem.1, hxM_mem.2]⟩
        · rw [hquot, le_div_iff₀ hneg_pos]
          exact hb.1
        · rw [hquot, div_le_iff₀ hneg_pos]
          exact hb.2
      · -- Positive increment `t > 0`: work on `[c, c + t] ⊆ [a, b]`
        have hle : c ≤ c + t := by linarith
        have hsub : Set.Icc c (c + t) ⊆ Set.Icc a b := Set.Icc_subset_Icc hc.1 hct_mem.2
        have hne : (Set.Icc c (c + t)).Nonempty := ⟨c, le_rfl, hle⟩
        obtain ⟨xm, hxm_mem, hxm_min⟩ := isCompact_Icc.exists_isMinOn hne (hf.mono hsub)
        obtain ⟨xM, hxM_mem, hxM_max⟩ := isCompact_Icc.exists_isMaxOn hne (hf.mono hsub)
        have hdiff := areaFun_sub_eq_hyperIntegral hf hc hct_mem hle
        have hb := hyperIntegral_bounds hle hxm_min hxM_max
        have hlen : c + t - c = t := by ring
        rw [hlen] at hb
        refine ⟨xm, xM, fun _ _ ↦ ⟨hsub hxm_mem, hsub hxM_mem, ?_, ?_, ?_, ?_⟩⟩
        · rw [abs_of_pos ht_pos, abs_le]
          exact ⟨by linarith [hxm_mem.1, hxm_mem.2], by linarith [hxm_mem.1, hxm_mem.2]⟩
        · rw [abs_of_pos ht_pos, abs_le]
          exact ⟨by linarith [hxM_mem.1, hxM_mem.2], by linarith [hxM_mem.1, hxM_mem.2]⟩
        · rw [hdiff, le_div_iff₀ ht_pos]
          exact hb.1
        · rw [hdiff, div_le_iff₀ ht_pos]
          exact hb.2
    · exact ⟨c, c, fun h1 h2 ↦ (ht ⟨h1, h2⟩).elim⟩
  choose xMin xMax hx using hex
  exact ⟨xMin, xMax, hx⟩

/-- **Goldblatt Theorem 9.4.1 (Nonstandard Slope Within `*[a, b]`, pp. 111–112)**:
For `c ∈ [a, b]`, continuous `f` on `[a, b]`, and any nonzero infinitesimal `Δx` such that
`c + Δx ∈ *[a, b]`,
`(starFun (areaFun f a) (c + Δx) - areaFun f a c) / Δx ≈ₕ f(c)`! -/
theorem areaFun_infClose_slope_within_Icc {a b c : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hc : c ∈ Set.Icc a b)
    {dx : ℝ*} (hdx_inf : IsInfinitesimal dx) (hdx_ne : dx ≠ 0)
    (hmem : (c : ℝ*) + dx ∈ Set.Icc (a : ℝ*) (b : ℝ*)) :
    (starFun (areaFun f a) ((c : ℝ*) + dx) - (areaFun f a c : ℝ*)) / dx ≈ₕ (f c : ℝ*) := by
  obtain ⟨xMin, xMax, hw⟩ := exists_areaFun_slope_witness hf hc
  rcases ofSeq_surjective dx with ⟨s, rfl⟩
  have hs_ne : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), s j ≠ 0 :=
    Ultrafilter.eventually_not.2 fun h0 ↦ hdx_ne (Germ.coe_eq.2 h0)
  have hs_mem : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), c + s j ∈ Set.Icc a b := by
    have hstar : (c : ℝ*) + ofSeq s ∈ starSet (Set.Icc a b) := by rwa [starSet_Icc]
    exact ofSeq_mem_starSet.1 hstar
  have hev := hs_ne.and hs_mem
  let Xm : ℝ* := starFun xMin (ofSeq s)
  let XM : ℝ* := starFun xMax (ofSeq s)
  have hXm_star : Xm ∈ starSet (Set.Icc a b) :=
    ofSeq_mem_starSet.2 (hev.mono fun j ⟨hjne, hjmem⟩ ↦ (hw (s j) hjne hjmem).1)
  have hXM_star : XM ∈ starSet (Set.Icc a b) :=
    ofSeq_mem_starSet.2 (hev.mono fun j ⟨hjne, hjmem⟩ ↦ (hw (s j) hjne hjmem).2.1)
  have hXm_close : Xm ≈ₕ (c : ℝ*) := by
    refine isInfinitesimal_of_abs_le hdx_inf ?_
    exact ofSeq_le_ofSeq.2 (hev.mono fun j ⟨hjne, hjmem⟩ ↦ (hw (s j) hjne hjmem).2.2.1)
  have hXM_close : XM ≈ₕ (c : ℝ*) := by
    refine isInfinitesimal_of_abs_le hdx_inf ?_
    exact ofSeq_le_ofSeq.2 (hev.mono fun j ⟨hjne, hjmem⟩ ↦ (hw (s j) hjne hjmem).2.2.2.1)
  have hfXm : starFun f Xm ≈ₕ (f c : ℝ*) :=
    infClose_starFun_of_continuousWithinAt (hf c hc) hXm_star hXm_close
  have hfXM : starFun f XM ≈ₕ (f c : ℝ*) :=
    infClose_starFun_of_continuousWithinAt (hf c hc) hXM_star hXM_close
  have hlow_slope : starFun f Xm ≤
      (starFun (areaFun f a) ((c : ℝ*) + ofSeq s) - (areaFun f a c : ℝ*)) / ofSeq s :=
    ofSeq_le_ofSeq.2 (hev.mono fun j ⟨hjne, hjmem⟩ ↦ (hw (s j) hjne hjmem).2.2.2.2.1)
  have hhigh_slope :
      (starFun (areaFun f a) ((c : ℝ*) + ofSeq s) - (areaFun f a c : ℝ*)) / ofSeq s ≤
        starFun f XM :=
    ofSeq_le_ofSeq.2 (hev.mono fun j ⟨hjne, hjmem⟩ ↦ (hw (s j) hjne hjmem).2.2.2.2.2)
  exact infClose_of_le_of_le hlow_slope hhigh_slope hfXm hfXM

/-- **Goldblatt Theorem 9.4.1 (Interior Nonstandard Slope, pp. 111–112)**:
For `c ∈ (a, b)`, continuous `f` on `[a, b]`, and ANY nonzero infinitesimal `Δx`,
`(starFun (areaFun f a) (c + Δx) - areaFun f a c) / Δx ≈ₕ f(c)`! -/
theorem areaFun_infClose_slope {a b c : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hc : c ∈ Set.Ioo a b)
    {dx : ℝ*} (hdx_inf : IsInfinitesimal dx) (hdx_ne : dx ≠ 0) :
    (starFun (areaFun f a) ((c : ℝ*) + dx) - (areaFun f a c : ℝ*)) / dx ≈ₕ (f c : ℝ*) := by
  set δ : ℝ := min (c - a) (b - c)
  have hδ : 0 < δ := lt_min (sub_pos.2 hc.1) (sub_pos.2 hc.2)
  have hlt : |dx| < (δ : ℝ*) := hdx_inf δ hδ
  have h1 : (δ : ℝ*) ≤ ((c - a : ℝ) : ℝ*) := Hyperreal.coe_le_coe.2 (min_le_left _ _)
  have h2 : (δ : ℝ*) ≤ ((b - c : ℝ) : ℝ*) := Hyperreal.coe_le_coe.2 (min_le_right _ _)
  rw [Hyperreal.coe_sub] at h1 h2
  rw [abs_lt] at hlt
  have hmem : (c : ℝ*) + dx ∈ Set.Icc (a : ℝ*) (b : ℝ*) := ⟨by linarith, by linarith⟩
  exact areaFun_infClose_slope_within_Icc hf ⟨hc.1.le, hc.2.le⟩ hdx_inf hdx_ne hmem

/-- **Goldblatt Theorem 9.4.1 (`intervalIntegral` Nonstandard Slope, pp. 111–112)**:
For `c ∈ (a, b)`, continuous `f` on `[a, b]`, and ANY nonzero infinitesimal `Δx`,
`(starFun (fun x ↦ ∫ t in a..x, f t) (c + Δx) - ∫ t in a..c, f t) / Δx ≈ₕ f(c)`. -/
theorem intervalIntegral_infClose_slope {a b c : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hc : c ∈ Set.Ioo a b)
    {dx : ℝ*} (hdx_inf : IsInfinitesimal dx) (hdx_ne : dx ≠ 0) :
    (starFun (fun x ↦ ∫ t in a..x, f t) ((c : ℝ*) + dx) - ((∫ t in a..c, f t : ℝ) : ℝ*)) / dx ≈ₕ
      (f c : ℝ*) := by
  set δ : ℝ := min (c - a) (b - c)
  have hδ : 0 < δ := lt_min (sub_pos.2 hc.1) (sub_pos.2 hc.2)
  have hlt : |dx| < (δ : ℝ*) := hdx_inf δ hδ
  have h1 : (δ : ℝ*) ≤ ((c - a : ℝ) : ℝ*) := Hyperreal.coe_le_coe.2 (min_le_left _ _)
  have h2 : (δ : ℝ*) ≤ ((b - c : ℝ) : ℝ*) := Hyperreal.coe_le_coe.2 (min_le_right _ _)
  rw [Hyperreal.coe_sub] at h1 h2
  have hlt' := abs_lt.1 hlt
  have hmem : (c : ℝ*) + dx ∈ starSet (Set.Icc a b) := by
    rw [starSet_Icc]
    exact ⟨by linarith, by linarith⟩
  rcases ofSeq_surjective dx with ⟨s, rfl⟩
  have hs_mem : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), c + s j ∈ Set.Icc a b :=
    ofSeq_mem_starSet.1 hmem
  have heq_star : starFun (fun x ↦ ∫ t in a..x, f t) ((c : ℝ*) + ofSeq s) =
      starFun (areaFun f a) ((c : ℝ*) + ofSeq s) :=
    Germ.coe_eq.2 (hs_mem.mono fun j hj ↦
      (areaFun_eq_hyperIntegral_and_intervalIntegral hf hj).2.symm)
  have heq_c : ∫ t in a..c, f t = areaFun f a c :=
    (areaFun_eq_hyperIntegral_and_intervalIntegral hf ⟨hc.1.le, hc.2.le⟩).2.symm
  rw [heq_star, heq_c]
  exact areaFun_infClose_slope hf hc hdx_inf hdx_ne

/-- **Goldblatt Theorem 9.4.1 (FTC Part 1 on `[a, b]` Including Endpoints, p. 111)**:
If `f` is continuous on `[a, b]`, then `areaFun f a` is differentiable within `[a, b]` at every
`c ∈ [a, b]` (including the right-hand derivative at `a` and left-hand derivative at `b`) with
derivative `f c`! -/
theorem hasDerivWithinAt_areaFun_Icc {a b c : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hc : c ∈ Set.Icc a b) :
    HasDerivWithinAt (areaFun f a) (f c) (Set.Icc a b) c := by
  refine hasDerivWithinAt_of_infClose_slope fun dx hinf hne hmem ↦ ?_
  rw [starSet_Icc] at hmem
  exact areaFun_infClose_slope_within_Icc hf hc hinf hne hmem

/-- `HasDerivWithinAt` on `[a, b]` for `x ↦ ∫ t in a..x, f t` proved via Theorem 9.4.1! -/
theorem hasDerivWithinAt_intervalIntegral_Icc_via_nsa {a b c : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hc : c ∈ Set.Icc a b) :
    HasDerivWithinAt (fun x ↦ ∫ t in a..x, f t) (f c) (Set.Icc a b) c := by
  exact (hasDerivWithinAt_areaFun_Icc hf hc).congr
    (fun x hx ↦ (areaFun_eq_hyperIntegral_and_intervalIntegral hf hx).2.symm)
    (areaFun_eq_hyperIntegral_and_intervalIntegral hf hc).2.symm

/-- **Goldblatt Theorem 9.4.1 (FTC Part 1 on `(a, b)`, p. 111)**:
For `c ∈ (a, b)` and continuous `f` on `[a, b]`, `HasDerivAt (areaFun f a) (f c) c` and
`HasDerivAt (fun x ↦ ∫ t in a..x, f t) (f c) c`! -/
theorem hasDerivAt_areaFun_and_intervalIntegral {a b c : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hc : c ∈ Set.Ioo a b) :
    HasDerivAt (areaFun f a) (f c) c ∧
    HasDerivAt (fun x ↦ ∫ t in a..x, f t) (f c) c := by
  exact ⟨hasDerivAt_of_infClose_slope fun _ hinf hne ↦ areaFun_infClose_slope hf hc hinf hne,
         hasDerivAt_of_infClose_slope fun _ hinf hne ↦
           intervalIntegral_infClose_slope hf hc hinf hne⟩

/-- **Goldblatt Theorem 9.4.2 (FTC Part 2 via `(G - F)' = 0`, p. 112)**:
If `G` is continuous on `[a, b]` (`a ≤ b`) and has derivative `f` on `(a, b)` with `f` continuous
on `[a, b]`, then `hyperIntegral f a b = G b - G a` and `∫ x in a..b, f x = G b - G a`. -/
theorem ftc_part2_via_areaFun {a b : ℝ} {G f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hG_deriv : ∀ x ∈ Set.Ioo a b, HasDerivAt G (f x) x) :
    hyperIntegral f a b = G b - G a ∧ ∫ x in a..b, f x = G b - G a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp [hyperIntegral_self]
  · have hF_cont : ContinuousOn (areaFun f a) (Set.Icc a b) :=
      fun x hx ↦ (hasDerivWithinAt_areaFun_Icc hf hx).continuousWithinAt
    have hdiff_cont : ContinuousOn (fun x ↦ G x - areaFun f a x) (Set.Icc a b) :=
      hG_cont.sub hF_cont
    have hdiff_deriv : ∀ x ∈ Set.Ioo a b,
        HasDerivAt (fun x ↦ G x - areaFun f a x) 0 x := by
      intro x hx
      rw [← sub_self (f x)]
      exact (hG_deriv x hx).sub (hasDerivAt_areaFun_and_intervalIntegral hf hx).1
    obtain ⟨ξ, _, hξ⟩ := exists_hasDerivAt_eq_slope (fun x ↦ G x - areaFun f a x)
      (fun _ ↦ 0) hlt hdiff_cont hdiff_deriv
    have hslope_zero : ((G b - areaFun f a b) - (G a - areaFun f a a)) = 0 :=
      (div_eq_zero_iff.1 hξ.symm).resolve_right (sub_ne_zero.2 hlt.ne')
    have hFb := areaFun_eq_hyperIntegral_and_intervalIntegral hf ⟨hab, le_rfl⟩
    have hFa : areaFun f a a = 0 := areaFun_self f a
    refine ⟨?_, ?_⟩
    · linarith [hFb.1]
    · linarith [hFb.2]

/-- Endpoint-derivative version of **Goldblatt Theorem 9.4.2 (p. 112)**: if `G` has derivative `f`
within `[a, b]` at every point of `[a, b]` (`a ≤ b`) and `f` is continuous on `[a, b]`, then
`∫ x in a..b, f x = G b - G a`. -/
theorem ftc_part2_of_hasDerivWithinAt_Icc {a b : ℝ} {G f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hG : ∀ x ∈ Set.Icc a b, HasDerivWithinAt G (f x) (Set.Icc a b) x) :
    ∫ x in a..b, f x = G b - G a := by
  have hG_cont : ContinuousOn G (Set.Icc a b) := fun x hx ↦ (hG x hx).continuousWithinAt
  have hG_oo : ∀ x ∈ Set.Ioo a b, HasDerivAt G (f x) x := fun x hx ↦
    (hG x ⟨hx.1.le, hx.2.le⟩).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  exact (ftc_part2_via_areaFun hab hf hG_cont hG_oo).2

/-- **Nonstandard Proof 2 of FTC Part 2 (Direct Hyperfinite Telescoping)**:
Writing `G(b) - G(a) = ∑_{k < n} (G(x_{k+1}) - G(x_k)) = ∑_{k < n} (f(x_k) Δx + η_k Δx)` via MVT
and lifting to any unlimited `N ∈ ℕ*`, microcontinuity of `f` directly yields
`hyperRiemannSum f a b N ≈ₕ G(b) - G(a)` and `∫ x in a..b, f x = G(b) - G(a)` (without using
FTC Part 1)! -/
theorem ftc_part2_via_hyperfinite_telescoping {a b : ℝ} {G f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hG_deriv : ∀ x ∈ Set.Ioo a b, HasDerivAt G (f x) x)
    {N : ℕ*} (hN : IsUnlimitedNat N) :
    hyperRiemannSum f a b N ≈ₕ ((G b - G a : ℝ) : ℝ*) ∧
    ∫ x in a..b, f x = G b - G a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · rw [(hyperEqSums_self f a N).1]
    simp [InfClose.refl]
  · -- Real telescoping error bound before transfer: for each `n ≥ 1`, pick worst-case `ξ(n), x(n)`
    have hex : ∀ n : ℕ, ∃ ξn xn : ℝ,
        (0 < n → ξn ∈ Set.Icc a b ∧ xn ∈ Set.Icc a b ∧
          |ξn - xn| ≤ (b - a) / (n : ℝ) ∧
          |(G b - G a) - riemannSumEq f a b n| ≤ |f ξn - f xn| * (b - a)) := by
      intro n
      by_cases hn : 0 < n
      · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
        have hdx_pos : 0 < (b - a) / (n : ℝ) := div_pos (sub_pos.2 hlt) hn_pos
        let xPt : ℕ → ℝ := fun k ↦ a + (k : ℝ) * (b - a) / (n : ℝ)
        have hxPt_zero : xPt 0 = a := by simp [xPt]
        have hxPt_last : xPt n = b := by
          simp only [xPt]
          rw [mul_div_cancel_left₀ (b - a) hn_pos.ne', add_sub_cancel]
        have hxPt_step : ∀ k, xPt (k + 1) - xPt k = (b - a) / (n : ℝ) := fun k ↦ by
          simp only [xPt]
          push_cast
          ring
        have hxPt_lt : ∀ k < n, xPt k < xPt (k + 1) := fun k _ ↦ by linarith [hxPt_step k]
        have hxPt_sub : ∀ k < n, Set.Icc (xPt k) (xPt (k + 1)) ⊆ Set.Icc a b := by
          intro k hk
          refine Set.Icc_subset_Icc ?_ ?_
          · simp only [xPt]
            have : 0 ≤ (k : ℝ) * (b - a) / (n : ℝ) :=
              div_nonneg (mul_nonneg (Nat.cast_nonneg k) (sub_pos.2 hlt).le) hn_pos.le
            linarith
          · simp only [xPt]
            have hk1 : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 (Nat.succ_le_of_lt hk)
            have hle : ((k + 1 : ℕ) : ℝ) * (b - a) / (n : ℝ) ≤ b - a := by
              rw [div_le_iff₀ hn_pos, mul_comm (b - a)]
              exact mul_le_mul_of_nonneg_right hk1 (sub_pos.2 hlt).le
            linarith
        have hmvt : ∀ k < n, ∃ ξ : ℝ, ξ ∈ Set.Ioo (xPt k) (xPt (k + 1)) ∧
            G (xPt (k + 1)) - G (xPt k) = f ξ * ((b - a) / (n : ℝ)) := by
          intro k hk
          have hsub_oo : Set.Ioo (xPt k) (xPt (k + 1)) ⊆ Set.Ioo a b := by
            intro z hz
            have hIcc := hxPt_sub k hk ⟨hz.1.le, hz.2.le⟩
            exact ⟨lt_of_le_of_lt (hxPt_sub k hk ⟨le_rfl, (hxPt_lt k hk).le⟩).1 hz.1,
                   lt_of_lt_of_le hz.2 (hxPt_sub k hk ⟨(hxPt_lt k hk).le, le_rfl⟩).2⟩
          obtain ⟨ξ, hξ_mem, hξ_eq⟩ := exists_hasDerivAt_eq_slope G f (hxPt_lt k hk)
            (hG_cont.mono (hxPt_sub k hk)) (fun z hz ↦ hG_deriv z (hsub_oo hz))
          rw [hxPt_step k, eq_div_iff hdx_pos.ne'] at hξ_eq
          exact ⟨ξ, hξ_mem, hξ_eq.symm⟩
        let ξSub : ℕ → ℝ := fun k ↦ if hk : k < n then (hmvt k hk).choose else a
        have hξSub_spec : ∀ k (hk : k < n), ξSub k ∈ Set.Ioo (xPt k) (xPt (k + 1)) ∧
            G (xPt (k + 1)) - G (xPt k) = f (ξSub k) * ((b - a) / (n : ℝ)) := by
          intro k hk
          simp only [ξSub, hk, ↓reduceDIte]
          exact (hmvt k hk).choose_spec
        obtain ⟨k₀, hk₀_mem, hk₀_max⟩ :=
          Finset.exists_max_image (Finset.range n) (fun k ↦ |f (ξSub k) - f (xPt k)|)
            (Finset.nonempty_range_iff.2 hn.ne')
        have hk₀ : k₀ < n := Finset.mem_range.1 hk₀_mem
        obtain ⟨hξk₀, _⟩ := hξSub_spec k₀ hk₀
        refine ⟨ξSub k₀, xPt k₀, fun _ ↦
          ⟨hxPt_sub k₀ hk₀ ⟨hξk₀.1.le, hξk₀.2.le⟩,
           hxPt_sub k₀ hk₀ ⟨le_rfl, (hxPt_lt k₀ hk₀).le⟩, ?_, ?_⟩⟩
        · rw [abs_le]
          have hst := hxPt_step k₀
          exact ⟨by linarith [hξk₀.1, hdx_pos], by linarith [hξk₀.2]⟩
        · have htele : G b - G a = ∑ k ∈ Finset.range n, (G (xPt (k + 1)) - G (xPt k)) := by
            rw [Finset.sum_range_sub (fun k ↦ G (xPt k)), hxPt_last, hxPt_zero]
          rw [htele]
          unfold riemannSumEq
          rw [← Finset.sum_sub_distrib]
          calc |∑ k ∈ Finset.range n,
                ((G (xPt (k + 1)) - G (xPt k)) - f (xPt k) * ((b - a) / (n : ℝ)))|
              ≤ ∑ k ∈ Finset.range n,
                |(G (xPt (k + 1)) - G (xPt k)) - f (xPt k) * ((b - a) / (n : ℝ))| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = ∑ k ∈ Finset.range n,
                |f (ξSub k) - f (xPt k)| * ((b - a) / (n : ℝ)) := by
                refine Finset.sum_congr rfl fun k hk ↦ ?_
                rw [(hξSub_spec k (Finset.mem_range.1 hk)).2, ← sub_mul,
                    abs_mul, abs_of_pos hdx_pos]
            _ ≤ ∑ _k ∈ Finset.range n,
                |f (ξSub k₀) - f (xPt k₀)| * ((b - a) / (n : ℝ)) :=
                Finset.sum_le_sum fun k hk ↦
                  mul_le_mul_of_nonneg_right (hk₀_max k hk) hdx_pos.le
            _ = |f (ξSub k₀) - f (xPt k₀)| * (b - a) := by
                simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                field_simp [hn_pos.ne']
      · exact ⟨a, a, fun h ↦ (hn h).elim⟩
    choose ξSeq xSeq hSeq using hex
    induction N using Germ.inductionOn with | _ u =>
    have hu_pos : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < u j := Germ.coe_lt.1 (hN 0)
    let Ξ : ℝ* := starSeq ξSeq (u : ℕ*)
    let X : ℝ* := starSeq xSeq (u : ℕ*)
    have hΞ_mem : Ξ ∈ Set.Icc (a : ℝ*) (b : ℝ*) := by
      rw [← starSet_Icc]
      exact ofSeq_mem_starSet.2 (hu_pos.mono fun j hj ↦ (hSeq (u j) hj).1)
    have hX_mem : X ∈ Set.Icc (a : ℝ*) (b : ℝ*) := by
      rw [← starSet_Icc]
      exact ofSeq_mem_starSet.2 (hu_pos.mono fun j hj ↦ (hSeq (u j) hj).2.1)
    have hdx_inf : IsPosInfinitesimal (((b - a : ℝ) : ℝ*) / Hypernat.toHyperreal (u : ℕ*)) :=
      isPosInfinitesimal_sub_div_hypernat hlt hN
    have hΞX_le : |Ξ - X| ≤ ((b - a : ℝ) : ℝ*) / Hypernat.toHyperreal (u : ℕ*) :=
      ofSeq_le_ofSeq.2 (hu_pos.mono fun j hj ↦ (hSeq (u j) hj).2.2.1)
    have hΞX_close : Ξ ≈ₕ X :=
      isInfinitesimal_of_abs_le (isInfinitesimal_iff_trichotomy.2 (Or.inl hdx_inf))
        (hΞX_le.trans (le_abs_self _))
    have hfΞX_close : starFun f Ξ ≈ₕ starFun f X :=
      infClose_starFun_of_continuousOn_Icc hf hΞ_mem hX_mem hΞX_close
    have herr_inf : IsInfinitesimal (|starFun f Ξ - starFun f X| * ((b - a : ℝ) : ℝ*)) :=
      hfΞX_close.abs.mul_isLimited (isLimited_coe (b - a))
    have hbound : |((G b - G a : ℝ) : ℝ*) - hyperRiemannSum f a b (u : ℕ*)| ≤
        |starFun f Ξ - starFun f X| * ((b - a : ℝ) : ℝ*) :=
      ofSeq_le_ofSeq.2 (hu_pos.mono fun j hj ↦ (hSeq (u j) hj).2.2.2)
    have hclose : hyperRiemannSum f a b (u : ℕ*) ≈ₕ ((G b - G a : ℝ) : ℝ*) :=
      InfClose.symm (isInfinitesimal_of_abs_le herr_inf (hbound.trans (le_abs_self _)))
    have hint : ∫ x in a..b, f x = G b - G a := by
      have hint_cl := (hyperRiemannSum_infClose_intervalIntegral hab hf hN).1
      exact coe_eq_of_infClose (hint_cl.symm.trans hclose)
    exact ⟨hclose, hint⟩

/-! ## §9.5 Exercise on Average Function Values & Mean Value Theorems for Integrals -/

/-- Goldblatt §9.5 (p. 112): Sample average `Av(n) = (f(x_0) + ... + f(x_{n-1})) / n`
where `x_i = a + i(b - a)/n`. -/
def sampleAverage (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range n, f (a + (k : ℝ) * (b - a) / (n : ℝ))) / (n : ℝ)

/-- Goldblatt §9.5 (p. 112): Hypersequence extension `Av(N)` for `N ∈ ℕ*` via `starSeq`. -/
def hyperSampleAverage (f : ℝ → ℝ) (a b : ℝ) (N : ℕ*) : ℝ* :=
  starSeq (sampleAverage f a b) N

/-- Algebraic identity relating `riemannSumEq` and `sampleAverage`:
`riemannSumEq f a b n = sampleAverage f a b n * (b - a)`. -/
theorem riemannSumEq_eq_sampleAverage_mul (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    riemannSumEq f a b n = sampleAverage f a b n * (b - a) := by
  unfold riemannSumEq sampleAverage
  rw [← Finset.sum_mul]
  ring

/-- Degenerate interval sample average: for unlimited `N ∈ ℕ*`, `Av(N) = f(a)` on `[a, a]`. -/
theorem hyperSampleAverage_self (f : ℝ → ℝ) (a : ℝ) {N : ℕ*} (hN : IsUnlimitedNat N) :
    hyperSampleAverage f a a N = (f a : ℝ*) := by
  induction N using Germ.inductionOn with | _ u =>
  have hu : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < u j := Germ.coe_lt.1 (hN 0)
  refine Germ.coe_eq.2 (hu.mono fun j hj ↦ ?_)
  change sampleAverage f a a (u j) = f a
  unfold sampleAverage
  have hj0 : ((u j : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hj.ne'
  simp [hj0]

/-- **Goldblatt §9.5 Exercise on Average Function Values (p. 112)**:
If `f` is continuous on `[a, b]` (`a < b`) and `N ∈ ℕ*` is unlimited, then
`Av(N) ≈ₕ (1 / (b - a)) * ∫_a^b f(x) dx` and `sh(Av(N)) = (1 / (b - a)) * ∫_a^b f(x) dx`! -/
theorem hyperSampleAverage_infClose_average_integral {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b)) {N : ℕ*} (hN : IsUnlimitedNat N) :
    hyperSampleAverage f a b N ≈ₕ (((1 / (b - a)) * ∫ x in a..b, f x : ℝ) : ℝ*) ∧
    shadow (hyperSampleAverage f a b N) = (1 / (b - a)) * ∫ x in a..b, f x := by
  have hba_ne : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
  have heq : hyperSampleAverage f a b N =
      (((1 / (b - a) : ℝ)) : ℝ*) * hyperRiemannSum f a b N := by
    induction N using Germ.inductionOn with | _ u =>
    refine Germ.coe_eq.2 (Eventually.of_forall fun j ↦ ?_)
    change sampleAverage f a b (u j) = (1 / (b - a)) * riemannSumEq f a b (u j)
    rw [riemannSumEq_eq_sampleAverage_mul]
    field_simp [hba_ne]
  have hcl_sum := (hyperRiemannSum_infClose_intervalIntegral hab.le hf hN).1
  have hclose : hyperSampleAverage f a b N ≈ₕ (((1 / (b - a)) * ∫ x in a..b, f x : ℝ) : ℝ*) := by
    rw [heq, Hyperreal.coe_mul]
    exact InfClose.mul_left_of_isLimited (isLimited_coe (1 / (b - a))) hcl_sum
  exact ⟨hclose, shadow_eq_of_infClose hclose⟩

/-- **First Mean Value Theorem for Integrals** (proved via `hyperSampleAverage` / `hyperIntegral`,
EVT, and IVT): for `a ≤ b` and continuous `f` on `[a, b]`, there exists `c ∈ [a, b]` such that
`hyperIntegral f a b = f c * (b - a)` and `∫ x in a..b, f x = f c * (b - a)`. -/
theorem exists_eq_integral_mul_sub {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ c ∈ Set.Icc a b,
      hyperIntegral f a b = f c * (b - a) ∧ ∫ x in a..b, f x = f c * (b - a) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact ⟨a, ⟨le_rfl, le_rfl⟩, by simp, by simp⟩
  · have hne : (Set.Icc a b).Nonempty := ⟨a, le_rfl, hab⟩
    obtain ⟨xm, hxm_mem, hxm_min⟩ := isCompact_Icc.exists_isMinOn hne hf
    obtain ⟨xM, hxM_mem, hxM_max⟩ := isCompact_Icc.exists_isMaxOn hne hf
    have hb := hyperIntegral_bounds hab hxm_min hxM_max
    have hba_pos : 0 < b - a := sub_pos.2 hlt
    set avg : ℝ := hyperIntegral f a b / (b - a)
    have havg_low : f xm ≤ avg := (le_div_iff₀ hba_pos).2 hb.1
    have havg_high : avg ≤ f xM := (div_le_iff₀ hba_pos).2 hb.2
    have hmem_img : avg ∈ f '' Set.Icc a b :=
      isPreconnected_Icc.intermediate_value hxm_mem hxM_mem hf ⟨havg_low, havg_high⟩
    rcases hmem_img with ⟨c, hc_mem, hfc⟩
    have h1 : hyperIntegral f a b = f c * (b - a) := by
      rw [hfc]
      exact (div_mul_cancel₀ _ hba_pos.ne').symm
    have h2 : ∫ x in a..b, f x = hyperIntegral f a b :=
      intervalIntegral_eq_of_isDarbouxIntegrableOn
        (isDarbouxIntegrableOn_of_continuousOn hab hf) (hf.intervalIntegrable_of_Icc hab)
    exact ⟨c, hc_mem, h1, h2.trans h1⟩

/-- **Weighted Mean Value Theorem for Integrals (Nonnegative Weight)**, proved directly via
`hyperRiemannSum`, `shadow_mul`, `shadow_le_of_le`, EVT, and IVT:
if `a ≤ b`, `f` and `g` are continuous on `[a, b]`, and `0 ≤ g(x)` on `[a, b]`, then there exists
`c ∈ [a, b]` such that `∫ x in a..b, f x * g x = f c * ∫ x in a..b, g x`! -/
theorem exists_eq_weighted_integral_of_nonneg {a b : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hg0 : ∀ x ∈ Set.Icc a b, 0 ≤ g x) :
    ∃ c ∈ Set.Icc a b, ∫ x in a..b, f x * g x = f c * ∫ x in a..b, g x := by
  have hne : (Set.Icc a b).Nonempty := ⟨a, le_rfl, hab⟩
  obtain ⟨xm, hxm_mem, hxm_min⟩ := isCompact_Icc.exists_isMinOn hne hf
  obtain ⟨xM, hxM_mem, hxM_max⟩ := isCompact_Icc.exists_isMaxOn hne hf
  have hfg_cont : ContinuousOn (fun x ↦ f x * g x) (Set.Icc a b) := hf.mul hg
  -- Pointwise inequality on equal-subdivision Riemann sums!
  have hsum_bounds : ∀ n : ℕ,
      f xm * riemannSumEq g a b n ≤ riemannSumEq (fun x ↦ f x * g x) a b n ∧
      riemannSumEq (fun x ↦ f x * g x) a b n ≤ f xM * riemannSumEq g a b n := by
    intro n
    rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn_pos
    · simp [riemannSumEq]
    · have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn_pos
      have hw_nn : 0 ≤ (b - a) / (n : ℝ) := div_nonneg (sub_nonneg.2 hab) hn_r.le
      have hx_mem : ∀ k ∈ Finset.range n, a + (k : ℝ) * (b - a) / (n : ℝ) ∈ Set.Icc a b := by
        intro k hk
        have hk_le : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 (Finset.mem_range.1 hk).le
        refine ⟨by linarith [mul_nonneg (Nat.cast_nonneg k) hw_nn,
          mul_div_assoc (k : ℝ) (b - a) (n : ℝ)], ?_⟩
        have hle : (k : ℝ) * (b - a) / (n : ℝ) ≤ b - a := by
          rw [div_le_iff₀ hn_r, mul_comm (b - a)]
          exact mul_le_mul_of_nonneg_right hk_le (sub_nonneg.2 hab)
        linarith
      unfold riemannSumEq
      rw [Finset.mul_sum, Finset.mul_sum]
      refine ⟨Finset.sum_le_sum fun k hk ↦ ?_, Finset.sum_le_sum fun k hk ↦ ?_⟩
      · rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hxm_min (hx_mem k hk)) (hg0 _ (hx_mem k hk))) hw_nn
      · rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hxM_max (hx_mem k hk)) (hg0 _ (hx_mem k hk))) hw_nn
  -- Lift to `omegaNat` and apply `shadow`!
  have hhyper_low : (f xm : ℝ*) * hyperRiemannSum g a b omegaNat ≤
      hyperRiemannSum (fun x ↦ f x * g x) a b omegaNat :=
    ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (hsum_bounds n).1)
  have hhyper_high : hyperRiemannSum (fun x ↦ f x * g x) a b omegaNat ≤
      (f xM : ℝ*) * hyperRiemannSum g a b omegaNat :=
    ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (hsum_bounds n).2)
  have hlim_g := (hyperRiemannSum_isLimited_and_infClose_of_continuousOn
    hab hg isUnlimitedNat_omegaNat).1
  have hlim_fg := (hyperRiemannSum_isLimited_and_infClose_of_continuousOn
    hab hfg_cont isUnlimitedNat_omegaNat).1
  have hsh_g : ∫ x in a..b, g x = shadow (hyperRiemannSum g a b omegaNat) :=
    intervalIntegral_eq_shadow_hyperRiemannSum hab hg
  have hsh_fg : ∫ x in a..b, f x * g x =
      shadow (hyperRiemannSum (fun x ↦ f x * g x) a b omegaNat) :=
    intervalIntegral_eq_shadow_hyperRiemannSum hab hfg_cont
  have hlow_int : f xm * ∫ x in a..b, g x ≤ ∫ x in a..b, f x * g x := by
    have h := shadow_le_of_le ((isLimited_coe (f xm)).mul hlim_g) hlim_fg hhyper_low
    rwa [shadow_mul (isLimited_coe (f xm)) hlim_g, shadow_coe, ← hsh_g, ← hsh_fg] at h
  have hhigh_int : ∫ x in a..b, f x * g x ≤ f xM * ∫ x in a..b, g x := by
    have h := shadow_le_of_le hlim_fg ((isLimited_coe (f xM)).mul hlim_g) hhyper_high
    rwa [shadow_mul (isLimited_coe (f xM)) hlim_g, shadow_coe, ← hsh_g, ← hsh_fg] at h
  have hg_int_nn : 0 ≤ ∫ x in a..b, g x := by
    have h0 := integral_mono_via_shadow hab continuousOn_const hg hg0
    rwa [integral_const_via_shadow 0 hab, zero_mul] at h0
  rcases eq_or_lt_of_le hg_int_nn with hg_zero | hg_pos
  · refine ⟨a, ⟨le_rfl, hab⟩, ?_⟩
    rw [← hg_zero] at hlow_int hhigh_int ⊢
    linarith
  · set q : ℝ := (∫ x in a..b, f x * g x) / (∫ x in a..b, g x)
    have hq_low : f xm ≤ q := (le_div_iff₀ hg_pos).2 hlow_int
    have hq_high : q ≤ f xM := (div_le_iff₀ hg_pos).2 hhigh_int
    obtain ⟨c, hc_mem, hfc⟩ :=
      isPreconnected_Icc.intermediate_value hxm_mem hxM_mem hf ⟨hq_low, hq_high⟩
    refine ⟨c, hc_mem, ?_⟩
    rw [hfc]
    exact (div_mul_cancel₀ _ hg_pos.ne').symm

/-- **Weighted Mean Value Theorem for Integrals (Nonpositive Weight)**:
if `a ≤ b`, `f` and `g` are continuous on `[a, b]`, and `g(x) ≤ 0` on `[a, b]`, then there exists
`c ∈ [a, b]` such that `∫ x in a..b, f x * g x = f c * ∫ x in a..b, g x`. -/
theorem exists_eq_weighted_integral_of_nonpos {a b : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hg0 : ∀ x ∈ Set.Icc a b, g x ≤ 0) :
    ∃ c ∈ Set.Icc a b, ∫ x in a..b, f x * g x = f c * ∫ x in a..b, g x := by
  obtain ⟨c, hc_mem, hc_eq⟩ :=
    exists_eq_weighted_integral_of_nonneg (g := fun x ↦ -g x) hab hf hg.neg
      fun x hx ↦ neg_nonneg.2 (hg0 x hx)
  refine ⟨c, hc_mem, ?_⟩
  have h1 : (fun x ↦ f x * -g x) = (fun x ↦ (-1 : ℝ) * (f x * g x)) := by ext x; ring
  have h2 : (fun x ↦ -g x) = (fun x ↦ (-1 : ℝ) * g x) := by ext x; ring
  rw [h1, h2,
      integral_const_mul_via_shadow (f := fun x ↦ f x * g x) (-1) hab (hf.mul hg),
      integral_const_mul_via_shadow (-1) hab hg] at hc_eq
  linarith

end Goldblatt.Ch09
end

