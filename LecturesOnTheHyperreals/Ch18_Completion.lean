import LecturesOnTheHyperreals.Ch12_InternalFunctions
import Mathlib.Algebra.Order.CompleteField
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Topology.MetricSpace.Completion

/-!
# Chapter 18: Completion by Enlargement

Complete formalization of Robert Goldblatt, *Lectures on the Hyperreals: An Introduction to
Nonstandard Analysis* (GTM 188), Chapter 18 (pp. 231–258):

* **§18.1 Completing the Rationals** (pp. 231–233):
  Intrinsic definitions of limited hyperrationals `ℚ_𝕃 = {q : ℚ* | ∃ m : ℕ, |q| ≤ m}`
  (`HyperratLimited`) and infinitesimal hyperrationals `ℚ_𝕀 = {q : ℚ* | ∀ n > 0, |q| < 1 / n}`
  (`HyperratInfinitesimal`) directly on `ℚ* = Germ (hyperfilter ℕ) ℚ` without presupposing `ℝ`;
  proofs that `ℚ_𝕃` is a commutative subring, `ℚ_𝕀` is a maximal ideal of `ℚ_𝕃`, `ℚ_𝕃 ⧸ ℚ_𝕀` is
  an Archimedean Dedekind-complete linearly ordered field, and explicit `OrderRingIso`
  `(ℚ_𝕃 ⧸ ℚ_𝕀) ≃+*o ℝ` (`hyperratQuotientOrderRingIsoReal`).
* **§18.2–18.3 Metric Space Completion and Nonstandard Hulls** (pp. 233–237):
  Ultrapower `StarMetric M = Germ (hyperfilter ℕ) M`, hyperreal distance `starDist`, infinitesimal
  proximity `MetricInfClose` (`≈ₘ`), limited proximity `MetricLimDist`, basepoint independence of
  `LimitedMetric M p` (`*M_lim`), the **Nonstandard Metric Hull** `MetricHull M p`, isometric
  embedding `hullEmbed`, **Theorem 18.3.1** (`CompleteSpace (MetricHull M p)` via internal
  hypersequences, Overflow, and Countable Saturation), approachable / pre-nearstandard points
  `PreNearstandard M` (`*M_ap`), **Theorem 18.3.2** (`MetricCompletion M` as a metric completion
  with isometric bijection `MetricCompletion M ≃ᵢ UniformSpace.Completion M`), **Corollary 18.3.3**
  and **Exercise 18.3.4** (`CompleteSpace M ↔ PreNearstandard M = Nearstandard M`), and total
  boundedness (`TotallyBounded (Set.univ : Set M) ↔ PreNearstandard M = Set.univ`).
* **§18.3 Nonstandard Hulls of Normed Vector Spaces** (pp. 235–237, Banach space hull):
  Ultrapower `StarVec E`, `ℝ`-submodules `LimitedVec E`, `InfinitesimalVec E`, and
  `PreNearstandardVec E`, the **Banach Nonstandard Hull** `NormedHull E = LimitedVec E ⧸ InfinitesimalVec E`
  with `‖[v]‖ = shadow (starNorm v)`, linear isometric embedding `normedHullEmbed : E →ₗᵢ[ℝ] NormedHull E`,
  Banach completeness `CompleteSpace (NormedHull E)`, and Banach completion
  `BanachCompletion E ≃ₗᵢ[ℝ] UniformSpace.Completion E`.
* **§18.4 $p$-adic Integers** (pp. 237–245):
  Nonstandard $p$-adic valuation `starPadicOrderZ` and norm `starPadicNormZ` on `ℤ*`,
  **Theorem 18.4.1** (4-way equivalence characterizing $p$-adic infinitesimals `I_p`), lifted
  residue homomorphisms `hyperZModHom : ℤ* →+* ZMod m`, homomorphism `thetaP : ℤ* →+* ℤ_[p]`,
  ring isomorphism `(ℤ* ⧸ I_p) ≃+* ℤ_[p]` (`hyperintQuotientEquivPadicInt`), norm preservation
  `shadow (starPadicNormZ p x) = ‖thetaP p x‖`, isometric hull equivalence, approachability of all
  `ℤ*` from `ℤ`, and characterization of $p$-adically nearstandard hyperintegers.
* **§18.5 $p$-adic Numbers** (pp. 245–249):
  Nonstandard $p$-adic valuation and norm on `ℚ*`, **Theorem 18.5.1** and **Theorem 18.5.2**
  (denominator characterization of $p$-adic limitedness), subring `PadicLimitedSubringQ p` and
  maximal ideal `PadicInfinitesimalIdealQ p`, homomorphism `thetaPQ : PadicLimitedSubringQ p →+* ℚ_[p]`,
  ring isomorphism `(PadicLimitedSubringQ p ⧸ PadicInfinitesimalIdealQ p) ≃+* ℚ_[p]`, metric
  preservation, and approachability of `PadicLimitedSubringQ p` from `ℚ`.
* **§18.6 Formal Power Series** (pp. 249–254):
  $X$-adic order and norm on `Polynomial R` and `PowerSeries R`, hyperpolynomials `HyperPoly R`,
  **Theorem 18.6.1** (approachability iff standard coefficients of standard degree, plus non-approachable
  limited hyperpolynomials when `Infinite R`), **Theorem 18.6.2** and **Corollary 18.6.3**,
  isomorphisms `(HyperPoly R ⧸ XAdicIdeal R) ≃+* (StarRing R)⟦X⟧`,
  `(ApproachableHyperPoly R ⧸ ApproachableInfinitesimalIdeal R) ≃+* R⟦X⟧`, and
  `(LimitedCoeffHyperPoly ⧸ InfinitesimalCoeffHyperPoly) ≃+* ℝ⟦X⟧`, plus **Exercise 18.6.4** and
  isometric equivalence `MetricCompletion (AdicPoly R) ≃ᵢ AdicPowerSeries R`.
* **§18.7–18.8 Hyperfinite Expansions in Base $p$ & Exercises** (pp. 255–257):
  Base-$p$ digit sequences `SeqP p ≃ ℕ` lifted to `*Seq(p) ≃ ℕ*`, **Exercise 18.8(1)** (internal
  hyperfinite digit sequences), congruence truncation law `(v)`, **Theorem 18.7.1** and
  **Exercise 18.8(2)** ($p$-adic infinite closeness of positive hyperintegers iff identical base-$p$
  digits at all standard degrees), and hyperfinite base-$p$ representation of $p$-adic integers.
-/

noncomputable section

namespace Goldblatt.Ch18

open Filter Goldblatt
open Hyperreal (ofSeq ofSeq_lt_ofSeq ofSeq_le_ofSeq ofSeq_surjective)
open scoped Topology Classical BigOperators

/-! ## §18.1 Completing the Rationals (`ℚ_𝕃 ⧸ ℚ_𝕀 ≃+*o ℝ`) -/

/-- Goldblatt §18.1 (p. 232): Intrinsic predicate that a hyperrational `q ∈ ℚ*` is limited
(`∃ m : ℕ, |q| ≤ m`), formulated directly in `ℚ*` without mentioning `ℝ`. -/
def IsLimitedHyperrat (q : ℚ*) : Prop :=
  ∃ m : ℕ, |q| ≤ (m : ℚ*)

/-- Goldblatt §18.1 (p. 232): Intrinsic predicate that a hyperrational `q ∈ ℚ*` is infinitesimal
(`∀ n > 0, |q| < 1 / n`), formulated directly in `ℚ*` without mentioning `ℝ`. -/
def IsInfinitesimalHyperrat (q : ℚ*) : Prop :=
  ∀ n : ℕ, 0 < n → |q| < (1 : ℚ*) / (n : ℚ*)

/-- Intrinsic limitedness of `0` in `ℚ*` (Goldblatt §18.1, p. 232). -/
theorem isLimitedHyperrat_zero : IsLimitedHyperrat 0 :=
  ⟨0, by simp⟩

/-- Intrinsic limitedness of `1` in `ℚ*` (Goldblatt §18.1, p. 232). -/
theorem isLimitedHyperrat_one : IsLimitedHyperrat 1 :=
  ⟨1, by simp⟩

/-- Intrinsic closure of `IsLimitedHyperrat` under negation (Goldblatt §18.1, p. 232). -/
theorem IsLimitedHyperrat.neg {q : ℚ*} (hq : IsLimitedHyperrat q) : IsLimitedHyperrat (-q) := by
  rcases hq with ⟨m, hm⟩
  exact ⟨m, by simpa using hm⟩

/-- Intrinsic closure of `IsLimitedHyperrat` under addition (Goldblatt §18.1, p. 232). -/
theorem IsLimitedHyperrat.add {p q : ℚ*} (hp : IsLimitedHyperrat p) (hq : IsLimitedHyperrat q) :
    IsLimitedHyperrat (p + q) := by
  rcases hp with ⟨m, hm⟩
  rcases hq with ⟨n, hn⟩
  refine ⟨m + n, ?_⟩
  push_cast
  exact (abs_add_le p q).trans (add_le_add hm hn)

/-- Intrinsic closure of `IsLimitedHyperrat` under multiplication (Goldblatt §18.1, p. 232). -/
theorem IsLimitedHyperrat.mul {p q : ℚ*} (hp : IsLimitedHyperrat p) (hq : IsLimitedHyperrat q) :
    IsLimitedHyperrat (p * q) := by
  rcases hp with ⟨m, hm⟩
  rcases hq with ⟨n, hn⟩
  refine ⟨m * n, ?_⟩
  rw [abs_mul]
  push_cast
  exact mul_le_mul hm hn (abs_nonneg q) (Nat.cast_nonneg m)

/-- Every infinitesimal hyperrational is limited, proved intrinsically in `ℚ*` (Goldblatt §18.1, p. 232). -/
theorem IsInfinitesimalHyperrat.isLimited {q : ℚ*} (hq : IsInfinitesimalHyperrat q) :
    IsLimitedHyperrat q :=
  ⟨1, (hq 1 Nat.one_pos).le.trans (by simp)⟩

/-- `0` is an infinitesimal hyperrational (Goldblatt §18.1, p. 232). -/
theorem isInfinitesimalHyperrat_zero : IsInfinitesimalHyperrat 0 := by
  intro n hn
  have hn' : (0 : ℚ*) < (n : ℚ*) := Nat.cast_pos.2 hn
  simpa using div_pos zero_lt_one hn'

/-- Intrinsic closure of `IsInfinitesimalHyperrat` under negation (Goldblatt §18.1, p. 232). -/
theorem IsInfinitesimalHyperrat.neg {q : ℚ*} (hq : IsInfinitesimalHyperrat q) :
    IsInfinitesimalHyperrat (-q) := by
  intro n hn
  simpa using hq n hn

/-- Intrinsic closure of `IsInfinitesimalHyperrat` under addition (Goldblatt §18.1, p. 232). -/
theorem IsInfinitesimalHyperrat.add {p q : ℚ*}
    (hp : IsInfinitesimalHyperrat p) (hq : IsInfinitesimalHyperrat q) :
    IsInfinitesimalHyperrat (p + q) := by
  intro n hn
  have h2n : 0 < 2 * n := Nat.mul_pos (by decide) hn
  have h1 := hp (2 * n) h2n
  have h2 := hq (2 * n) h2n
  have hn0 : (n : ℚ*) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hsum : (1 : ℚ*) / ((2 * n : ℕ) : ℚ*) + (1 : ℚ*) / ((2 * n : ℕ) : ℚ*) =
      (1 : ℚ*) / (n : ℚ*) := by
    push_cast
    field_simp [hn0]
    ring
  exact (abs_add_le p q).trans_lt ((add_lt_add h1 h2).trans_eq hsum)

/-- Intrinsic absorption of `IsInfinitesimalHyperrat` under multiplication by `IsLimitedHyperrat`
(Goldblatt §18.1, p. 232). -/
theorem IsLimitedHyperrat.mul_isInfinitesimal {p q : ℚ*}
    (hp : IsLimitedHyperrat p) (hq : IsInfinitesimalHyperrat q) :
    IsInfinitesimalHyperrat (p * q) := by
  rcases hp with ⟨m, hm⟩
  intro n hn
  have hm1_pos : 0 < (m + 1) * n := Nat.mul_pos (Nat.succ_pos m) hn
  have hq' := hq ((m + 1) * n) hm1_pos
  have hp' : |p| < ((m + 1 : ℕ) : ℚ*) := hm.trans_lt (by exact_mod_cast Nat.lt_succ_self m)
  rw [abs_mul]
  have hm1_ne : ((m + 1 : ℕ) : ℚ*) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)
  have hn_ne : (n : ℚ*) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  calc |p| * |q|
      < ((m + 1 : ℕ) : ℚ*) * ((1 : ℚ*) / (((m + 1) * n : ℕ) : ℚ*)) :=
        mul_lt_mul'' hp' hq' (abs_nonneg p) (abs_nonneg q)
    _ = (1 : ℚ*) / (n : ℚ*) := by
        push_cast
        field_simp [hm1_ne, hn_ne]

/-- Goldblatt §18.1 (p. 232): The commutative subring `ℚ_𝕃` (`*ℚ_lim`) of limited hyperrationals,
defined intrinsically inside `ℚ* = Germ (hyperfilter ℕ) ℚ`. -/
def HyperratLimited : Subring ℚ* where
  carrier := {q : ℚ* | IsLimitedHyperrat q}
  mul_mem' ha hb := ha.mul hb
  one_mem' := isLimitedHyperrat_one
  add_mem' ha hb := ha.add hb
  zero_mem' := isLimitedHyperrat_zero
  neg_mem' ha := ha.neg

/-- Goldblatt §18.1 (p. 232): The ideal `ℚ_𝕀` (`*ℚ_inf`) of infinitesimal hyperrationals inside
`HyperratLimited`. -/
def HyperratInfinitesimal : Ideal HyperratLimited where
  carrier := {q : HyperratLimited | IsInfinitesimalHyperrat q.1}
  add_mem' ha hb := ha.add hb
  zero_mem' := isInfinitesimalHyperrat_zero
  smul_mem' c _ hx := c.2.mul_isInfinitesimal hx

/-- Intrinsic proof that any non-infinitesimal element of `HyperratLimited` has a limited inverse
in `ℚ*` (Goldblatt §18.1, p. 233). -/
theorem inv_isLimitedHyperrat_of_not_isInfinitesimal {q : ℚ*}
    (hnot : ¬ IsInfinitesimalHyperrat q) :
    q ≠ 0 ∧ IsLimitedHyperrat q⁻¹ := by
  unfold IsInfinitesimalHyperrat at hnot
  push Not at hnot
  obtain ⟨n, hn, hle⟩ := hnot
  have hn_pos : (0 : ℚ*) < (n : ℚ*) := Nat.cast_pos.2 hn
  have h1n_pos : (0 : ℚ*) < (1 : ℚ*) / (n : ℚ*) := div_pos zero_lt_one hn_pos
  have hq_pos : 0 < |q| := h1n_pos.trans_le hle
  refine ⟨abs_pos.1 hq_pos, n, ?_⟩
  rw [abs_inv]
  have hmul : (1 : ℚ*) ≤ |q| * (n : ℚ*) := (div_le_iff₀ hn_pos).1 hle
  exact (inv_le_iff_one_le_mul₀ hq_pos).2 (by rwa [mul_comm])

/-- Intrinsic proof (without mentioning `ℝ`) that `HyperratLimited ⧸ HyperratInfinitesimal` is a
field (`IsField`), since every nonzero coset has an explicit inverse `[q⁻¹]` (Goldblatt §18.1, p. 233). -/
theorem hyperratQuotient_isField :
    IsField (HyperratLimited ⧸ HyperratInfinitesimal) := by
  refine ⟨⟨0, 1, ?_⟩, mul_comm, ?_⟩
  · intro h01
    have hmem : (1 : HyperratLimited) ∈ HyperratInfinitesimal := by
      have hsub : (1 : HyperratLimited) - 0 ∈ HyperratInfinitesimal :=
        (Ideal.Quotient.eq.1 h01.symm)
      simpa using hsub
    have hlt := hmem 2 (by decide)
    norm_num at hlt
  · intro x hx
    induction x using Quotient.inductionOn with | _ a =>
    have ha_not : ¬ IsInfinitesimalHyperrat a.1 := by
      intro hinf
      exact hx (Ideal.Quotient.eq_zero_iff_mem.2 hinf)
    obtain ⟨hne, hinv_lim⟩ := inv_isLimitedHyperrat_of_not_isInfinitesimal ha_not
    let b : HyperratLimited := ⟨a.1⁻¹, hinv_lim⟩
    refine ⟨Ideal.Quotient.mk HyperratInfinitesimal b, ?_⟩
    change Ideal.Quotient.mk HyperratInfinitesimal a *
        Ideal.Quotient.mk HyperratInfinitesimal b = 1
    rw [← map_mul]
    apply Ideal.Quotient.eq.2
    change IsInfinitesimalHyperrat (a.1 * a.1⁻¹ - 1)
    rw [mul_inv_cancel₀ hne, sub_self]
    exact isInfinitesimalHyperrat_zero

/-- Goldblatt §18.1 (p. 232): `HyperratInfinitesimal` is a maximal ideal of `HyperratLimited`. -/
instance instIsMaximalHyperratInfinitesimal : HyperratInfinitesimal.IsMaximal :=
  Ideal.Quotient.maximal_of_isField HyperratInfinitesimal hyperratQuotient_isField

/-- Field structure on `HyperratLimited ⧸ HyperratInfinitesimal` (Goldblatt §18.1, p. 233). -/
instance instFieldHyperratQuotient : Field (HyperratLimited ⧸ HyperratInfinitesimal) :=
  Ideal.Quotient.field HyperratInfinitesimal

/-- Embedding `Hyperrat.toHyperreal` preserves order and ring operations on `ℚ*`. -/
theorem toHyperreal_le_iff {p q : ℚ*} :
    Hyperrat.toHyperreal p ≤ Hyperrat.toHyperreal q ↔ p ≤ q :=
  Germ.inductionOn₂ p q fun u v ↦ by
    change ofSeq (fun n ↦ (u n : ℝ)) ≤ ofSeq (fun n ↦ (v n : ℝ)) ↔ (u : ℚ*) ≤ (v : ℚ*)
    rw [ofSeq_le_ofSeq, Germ.coe_le]
    simp only [EventuallyLE, Rat.cast_le]

/-- Strict order preservation of `Hyperrat.toHyperreal`. -/
theorem toHyperreal_lt_iff {p q : ℚ*} :
    Hyperrat.toHyperreal p < Hyperrat.toHyperreal q ↔ p < q :=
  Germ.inductionOn₂ p q fun u v ↦ by
    change ofSeq (fun n ↦ (u n : ℝ)) < ofSeq (fun n ↦ (v n : ℝ)) ↔ (u : ℚ*) < (v : ℚ*)
    rw [ofSeq_lt_ofSeq, Germ.coe_lt]
    simp only [Rat.cast_lt]

/-- `Hyperrat.toHyperreal` commutes with absolute value. -/
theorem toHyperreal_abs (q : ℚ*) :
    Hyperrat.toHyperreal |q| = |Hyperrat.toHyperreal q| :=
  Germ.inductionOn q fun u ↦ Germ.coe_eq.2 <| Eventually.of_forall fun n ↦ Rat.cast_abs (u n)

/-- Equivalence between intrinsic `IsLimitedHyperrat` on `ℚ*` and `IsLimited` in `ℝ*`
(Goldblatt §18.1, p. 232). -/
theorem isLimitedHyperrat_iff_isLimited {q : ℚ*} :
    IsLimitedHyperrat q ↔ IsLimited (Hyperrat.toHyperreal q) := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m + 1, ?_⟩
    have hlt : |q| < ((m + 1 : ℕ) : ℚ*) := hm.trans_lt (by exact_mod_cast Nat.lt_succ_self m)
    have hreal : Hyperrat.toHyperreal |q| < Hyperrat.toHyperreal ((m + 1 : ℕ) : ℚ*) :=
      toHyperreal_lt_iff.2 hlt
    rwa [toHyperreal_abs, show Hyperrat.toHyperreal ((m + 1 : ℕ) : ℚ*) = ((m + 1 : ℕ) : ℝ*) by
      change Hyperrat.toHyperrealRingHom ((m + 1 : ℕ) : ℚ*) = _; simp] at hreal
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hreal : Hyperrat.toHyperreal |q| ≤ Hyperrat.toHyperreal (m : ℚ*) := by
      rw [toHyperreal_abs, show Hyperrat.toHyperreal (m : ℚ*) = (m : ℝ*) by
        change Hyperrat.toHyperrealRingHom (m : ℚ*) = _; simp]
      exact hm.le
    exact toHyperreal_le_iff.1 hreal

/-- `Hyperrat.toHyperreal` commutes with subtraction. -/
@[simp]
theorem toHyperreal_sub (p q : ℚ*) :
    Hyperrat.toHyperreal (p - q) = Hyperrat.toHyperreal p - Hyperrat.toHyperreal q :=
  Hyperrat.toHyperrealRingHom.map_sub p q

/-- Equivalence between intrinsic `IsInfinitesimalHyperrat` on `ℚ*` and `IsInfinitesimal` in `ℝ*`
(Goldblatt §18.1, p. 232). -/
theorem isInfinitesimalHyperrat_iff_isInfinitesimal {q : ℚ*} :
    IsInfinitesimalHyperrat q ↔ IsInfinitesimal (Hyperrat.toHyperreal q) := by
  rw [isInfinitesimal_iff_nat]
  refine forall_congr' fun n ↦ imp_congr_right fun _ ↦ ?_
  have hcast : Hyperrat.toHyperreal ((1 : ℚ*) / (n : ℚ*)) = (((n : ℝ)⁻¹ : ℝ) : ℝ*) := by
    change Hyperrat.toHyperreal (Germ.const ((1 : ℚ) / (n : ℚ))) = _
    have hq : (((1 : ℚ) / (n : ℚ) : ℚ) : ℝ) = (n : ℝ)⁻¹ := by push_cast; simp
    exact Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ hq)
  rw [← toHyperreal_abs, ← hcast, toHyperreal_lt_iff]

/-- Intrinsic preorder relation on `HyperratLimited` inducing the order on `ℚ_𝕃 ⧸ ℚ_𝕀`:
`[a] ≤ [b]` iff `a - b < 1 / n` in `ℚ*` for every standard `n > 0` (Goldblatt §18.1, p. 233). -/
def HyperratQuotLeRel (a b : HyperratLimited) : Prop :=
  ∀ n : ℕ, 0 < n → a.1 - b.1 < (1 : ℚ*) / (n : ℚ*)

/-- Well-definedness of `HyperratQuotLeRel` modulo `HyperratInfinitesimal`. -/
theorem hyperratQuotLeRel_congr {a a' b b' : HyperratLimited}
    (ha : a - a' ∈ HyperratInfinitesimal) (hb : b - b' ∈ HyperratInfinitesimal) :
    HyperratQuotLeRel a b ↔ HyperratQuotLeRel a' b' := by
  have step : ∀ {u u' v v' : HyperratLimited},
      u - u' ∈ HyperratInfinitesimal → v - v' ∈ HyperratInfinitesimal →
      HyperratQuotLeRel u v → HyperratQuotLeRel u' v' := by
    intro u u' v v' hu hv huv n hn
    have h3n : 0 < 3 * n := Nat.mul_pos (by decide) hn
    have h1 := huv (3 * n) h3n
    have h2 : -(u.1 - u'.1) ≤ |u.1 - u'.1| := neg_le_abs _
    have h2' := h2.trans_lt (hu (3 * n) h3n)
    have h3 := (le_abs_self (v.1 - v'.1)).trans_lt (hv (3 * n) h3n)
    have hn0 : (n : ℚ*) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hsum : (1 : ℚ*) / ((3 * n : ℕ) : ℚ*) + (1 : ℚ*) / ((3 * n : ℕ) : ℚ*) +
        (1 : ℚ*) / ((3 * n : ℕ) : ℚ*) = (1 : ℚ*) / (n : ℚ*) := by
      push_cast; field_simp [hn0]; ring
    have hdecomp : u'.1 - v'.1 = (u.1 - v.1) + -(u.1 - u'.1) + (v.1 - v'.1) := by ring
    rw [hdecomp]
    exact (add_lt_add (add_lt_add h1 h2') h3).trans_eq hsum
  refine ⟨step ha hb, step ?_ ?_⟩
  · have : a' - a = -(a - a') := by ring
    rw [this]; exact HyperratInfinitesimal.neg_mem ha
  · have : b' - b = -(b - b') := by ring
    rw [this]; exact HyperratInfinitesimal.neg_mem hb

/-- Intrinsic `LE` instance on `HyperratLimited ⧸ HyperratInfinitesimal` (Goldblatt §18.1, p. 233). -/
instance instLEHyperratQuotient : LE (HyperratLimited ⧸ HyperratInfinitesimal) where
  le := Quotient.lift₂ HyperratQuotLeRel fun _ _ _ _ ha hb ↦
    propext (hyperratQuotLeRel_congr
      (Ideal.Quotient.eq.1 (Quotient.sound ha))
      (Ideal.Quotient.eq.1 (Quotient.sound hb)))

/-- Unfolding `[a] ≤ [b]` in `HyperratLimited ⧸ HyperratInfinitesimal`. -/
@[simp]
theorem mk_le_mk_hyperratQuotient {a b : HyperratLimited} :
    Ideal.Quotient.mk HyperratInfinitesimal a ≤ Ideal.Quotient.mk HyperratInfinitesimal b ↔
      HyperratQuotLeRel a b :=
  Iff.rfl

/-- Intrinsic `LinearOrder` on `HyperratLimited ⧸ HyperratInfinitesimal` (Goldblatt §18.1, p. 233). -/
instance instLinearOrderHyperratQuotient :
    LinearOrder (HyperratLimited ⧸ HyperratInfinitesimal) where
  le := (· ≤ ·)
  le_refl x := Quotient.inductionOn x fun a n hn ↦ by
    rw [sub_self]
    exact div_pos zero_lt_one (Nat.cast_pos.2 hn)
  le_trans x y z := Quotient.inductionOn₃ x y z fun a b c hab hbc n hn ↦ by
    have h2n : 0 < 2 * n := Nat.mul_pos (by decide) hn
    have h1 := hab (2 * n) h2n
    have h2 := hbc (2 * n) h2n
    have hn0 : (n : ℚ*) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hsum : (1 : ℚ*) / ((2 * n : ℕ) : ℚ*) + (1 : ℚ*) / ((2 * n : ℕ) : ℚ*) =
        (1 : ℚ*) / (n : ℚ*) := by
      push_cast; field_simp [hn0]; ring
    have hdecomp : a.1 - c.1 = (a.1 - b.1) + (b.1 - c.1) := by ring
    rw [hdecomp]
    exact (add_lt_add h1 h2).trans_eq hsum
  le_antisymm x y := Quotient.inductionOn₂ x y fun a b hab hba ↦ by
    apply Ideal.Quotient.eq.2
    intro n hn
    rw [abs_lt]
    refine ⟨?_, hab n hn⟩
    have h := hba n hn
    have hneg : b.1 - a.1 = -(a.1 - b.1) := by ring
    rw [hneg] at h
    exact neg_lt.1 h
  le_total x y := Quotient.inductionOn₂ x y fun a b ↦ by
    by_cases h : HyperratQuotLeRel a b
    · exact Or.inl h
    · right
      unfold HyperratQuotLeRel at h
      push Not at h
      obtain ⟨n, hn, hle⟩ := h
      intro m hm
      have hpos1 : (0 : ℚ*) < (1 : ℚ*) / (n : ℚ*) := div_pos zero_lt_one (Nat.cast_pos.2 hn)
      have hpos2 : (0 : ℚ*) < (1 : ℚ*) / (m : ℚ*) := div_pos zero_lt_one (Nat.cast_pos.2 hm)
      linarith
  toDecidableLE := Classical.decRel _

/-- Shadow homomorphism `ℚ_𝕃 →+* ℝ` on intrinsically limited hyperrationals (Goldblatt §18.1, p. 232). -/
def hyperratShadowRingHom : HyperratLimited →+* ℝ where
  toFun q := shadow (Hyperrat.toHyperreal q.1)
  map_one' := by
    change shadow (Hyperrat.toHyperrealRingHom 1) = 1
    rw [map_one, shadow_one]
  map_mul' a b := by
    change shadow (Hyperrat.toHyperrealRingHom (a.1 * b.1)) = _
    rw [map_mul]
    exact shadow_mul (isLimitedHyperrat_iff_isLimited.1 a.2) (isLimitedHyperrat_iff_isLimited.1 b.2)
  map_zero' := by
    change shadow (Hyperrat.toHyperrealRingHom 0) = 0
    rw [map_zero, shadow_zero]
  map_add' a b := by
    change shadow (Hyperrat.toHyperrealRingHom (a.1 + b.1)) = _
    rw [map_add]
    exact shadow_add (isLimitedHyperrat_iff_isLimited.1 a.2) (isLimitedHyperrat_iff_isLimited.1 b.2)

/-- Surjectivity of `hyperratShadowRingHom : ℚ_𝕃 →+* ℝ` (Goldblatt §18.1, p. 232). -/
theorem hyperratShadowRingHom_surjective : Function.Surjective hyperratShadowRingHom := by
  intro r
  obtain ⟨q, hq⟩ := exists_hyperrat_infClose (r : ℝ*)
  have hlim : IsLimited (Hyperrat.toHyperreal q) := by
    have : Hyperrat.toHyperreal q = (r : ℝ*) + (Hyperrat.toHyperreal q - (r : ℝ*)) := by ring
    rw [this]
    exact (isLimited_coe r).add hq.symm.isLimited
  exact ⟨⟨q, isLimitedHyperrat_iff_isLimited.2 hlim⟩, shadow_eq_of_infClose hq.symm⟩

/-- Kernel of `hyperratShadowRingHom` is `HyperratInfinitesimal` (`ℚ_𝕀`, Goldblatt §18.1, p. 232). -/
theorem ker_hyperratShadowRingHom :
    RingHom.ker hyperratShadowRingHom = HyperratInfinitesimal := by
  ext q
  change shadow (Hyperrat.toHyperreal q.1) = 0 ↔ IsInfinitesimalHyperrat q.1
  rw [shadow_eq_zero_iff_isInfinitesimal (isLimitedHyperrat_iff_isLimited.1 q.2),
    isInfinitesimalHyperrat_iff_isInfinitesimal]

/-- Ring isomorphism `(ℚ_𝕃 ⧸ ℚ_𝕀) ≃+* ℝ` (Goldblatt §18.1, p. 232). -/
def hyperratQuotientRingEquivReal :
    (HyperratLimited ⧸ HyperratInfinitesimal) ≃+* ℝ :=
  (Ideal.quotEquivOfEq ker_hyperratShadowRingHom.symm).trans
    (RingHom.quotientKerEquivOfSurjective hyperratShadowRingHom_surjective)

/-- Explicit evaluation of `hyperratQuotientRingEquivReal` on a coset `[q]`. -/
@[simp]
theorem hyperratQuotientRingEquivReal_mk (q : HyperratLimited) :
    hyperratQuotientRingEquivReal (Ideal.Quotient.mk HyperratInfinitesimal q) =
      shadow (Hyperrat.toHyperreal q.1) :=
  rfl

/-- Goldblatt §18.1 (pp. 232–233): Characterization of the coset `ℚ_𝕀 + x` via infinite closeness
and shadows (`x ≈ y ↔ sh(x) = sh(y) ↔ x - y ∈ ℚ_𝕀 ↔ [x] = [y]`). -/
theorem hyperratCoset_tfae (x y : HyperratLimited) :
    (IsInfinitesimalHyperrat (x.1 - y.1) ↔
      shadow (Hyperrat.toHyperreal x.1) = shadow (Hyperrat.toHyperreal y.1)) ∧
    (shadow (Hyperrat.toHyperreal x.1) = shadow (Hyperrat.toHyperreal y.1) ↔
      Ideal.Quotient.mk HyperratInfinitesimal x = Ideal.Quotient.mk HyperratInfinitesimal y) := by
  have hx := isLimitedHyperrat_iff_isLimited.1 x.2
  have hy := isLimitedHyperrat_iff_isLimited.1 y.2
  refine ⟨?_, ?_⟩
  · rw [isInfinitesimalHyperrat_iff_isInfinitesimal]
    have hsub : Hyperrat.toHyperreal (x.1 - y.1) =
        Hyperrat.toHyperreal x.1 - Hyperrat.toHyperreal y.1 :=
      Hyperrat.toHyperrealRingHom.map_sub x.1 y.1
    rw [hsub, ← shadow_eq_zero_iff_isInfinitesimal (hx.sub hy), shadow_sub hx hy, sub_eq_zero]
  · rw [← hyperratQuotientRingEquivReal_mk, ← hyperratQuotientRingEquivReal_mk]
    exact hyperratQuotientRingEquivReal.injective.eq_iff

/-- Order compatibility between `HyperratQuotLeRel` and `shadow` in `ℝ`. -/
theorem hyperratQuotLeRel_iff_shadow_le (a b : HyperratLimited) :
    HyperratQuotLeRel a b ↔
      shadow (Hyperrat.toHyperreal a.1) ≤ shadow (Hyperrat.toHyperreal b.1) := by
  have ha := isLimitedHyperrat_iff_isLimited.1 a.2
  have hb := isLimitedHyperrat_iff_isLimited.1 b.2
  constructor
  · intro hab
    by_contra hgt
    push Not at hgt
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hgt)
    have hn1_pos : 0 < n + 1 := Nat.succ_pos n
    have hlt_q := hab (n + 1) hn1_pos
    have hlt_r : Hyperrat.toHyperreal (a.1 - b.1) <
        Hyperrat.toHyperreal ((1 : ℚ*) / ((n + 1 : ℕ) : ℚ*)) :=
      toHyperreal_lt_iff.2 hlt_q
    have hsh_le : shadow (Hyperrat.toHyperreal (a.1 - b.1)) ≤
        shadow (Hyperrat.toHyperreal ((1 : ℚ*) / ((n + 1 : ℕ) : ℚ*))) := by
      apply shadow_le_of_le
      · rw [show Hyperrat.toHyperreal (a.1 - b.1) =
            Hyperrat.toHyperreal a.1 - Hyperrat.toHyperreal b.1 from
            Hyperrat.toHyperrealRingHom.map_sub a.1 b.1]
        exact ha.sub hb
      · exact isLimitedHyperrat_iff_isLimited.1 ⟨1, by
          rw [abs_of_pos (div_pos zero_lt_one (Nat.cast_pos.2 hn1_pos))]
          exact div_le_one_of_le₀ (by exact_mod_cast hn1_pos) (by positivity)⟩
      · exact hlt_r.le
    have hcast : Hyperrat.toHyperreal ((1 : ℚ*) / ((n + 1 : ℕ) : ℚ*)) =
        ((1 / ((n + 1 : ℕ) : ℝ) : ℝ) : ℝ*) := by
      change Hyperrat.toHyperreal (Germ.const ((1 : ℚ) / ((n + 1 : ℕ) : ℚ))) = _
      have : (((1 : ℚ) / ((n + 1 : ℕ) : ℚ) : ℚ) : ℝ) = 1 / ((n + 1 : ℕ) : ℝ) := by push_cast; rfl
      exact Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ this)
    rw [toHyperreal_sub, shadow_sub ha hb, hcast, shadow_coe] at hsh_le
    push_cast at hsh_le
    linarith
  · intro hle n hn
    have hsub_le : shadow (Hyperrat.toHyperreal (a.1 - b.1)) ≤ 0 := by
      rw [toHyperreal_sub, shadow_sub ha hb]
      linarith
    have hlim : IsLimited (Hyperrat.toHyperreal (a.1 - b.1)) := by
      rw [toHyperreal_sub]
      exact ha.sub hb
    set s := shadow (Hyperrat.toHyperreal (a.1 - b.1))
    have hclose := infClose_shadow hlim (1 / (2 * (n : ℝ)))
      (div_pos one_pos (mul_pos two_pos (Nat.cast_pos.2 hn)))
    have hlt_real : Hyperrat.toHyperreal (a.1 - b.1) < ((1 / (n : ℝ) : ℝ) : ℝ*) := by
      have h1 : Hyperrat.toHyperreal (a.1 - b.1) < (s : ℝ*) + ((1 / (2 * (n : ℝ)) : ℝ) : ℝ*) := by
        linarith [(abs_lt.1 hclose).2]
      have h2 : s + 1 / (2 * (n : ℝ)) < 1 / (n : ℝ) := by
        have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
        have : 1 / (2 * (n : ℝ)) < 1 / (n : ℝ) :=
          one_div_lt_one_div_of_lt hn_pos (by linarith)
        linarith
      exact h1.trans (by rw [← Hyperreal.coe_add]; exact Hyperreal.coe_lt_coe.2 h2)
    have hcast : Hyperrat.toHyperreal ((1 : ℚ*) / (n : ℚ*)) = ((1 / (n : ℝ) : ℝ) : ℝ*) := by
      change Hyperrat.toHyperreal (Germ.const ((1 : ℚ) / (n : ℚ))) = _
      have : (((1 : ℚ) / (n : ℚ) : ℚ) : ℝ) = 1 / (n : ℝ) := by push_cast; rfl
      exact Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ this)
    exact toHyperreal_lt_iff.1 (by rwa [hcast])

/-- Goldblatt §18.1 (pp. 232–233): Explicit **order-ring isomorphism** `(ℚ_𝕃 ⧸ ℚ_𝕀) ≃+*o ℝ`
preserving ring operations as well as `≤` and `<`. -/
def hyperratQuotientOrderRingIsoReal :
    (HyperratLimited ⧸ HyperratInfinitesimal) ≃+*o ℝ where
  toRingEquiv := hyperratQuotientRingEquivReal
  map_le_map_iff' {x y} := Quotient.inductionOn₂ x y fun a b ↦
    (hyperratQuotLeRel_iff_shadow_le a b).symm

/-- `hyperratQuotientOrderRingIsoReal` preserves and reflects `≤`. -/
theorem hyperratQuotientOrderRingIsoReal_le_iff {x y : HyperratLimited ⧸ HyperratInfinitesimal} :
    hyperratQuotientOrderRingIsoReal x ≤ hyperratQuotientOrderRingIsoReal y ↔ x ≤ y :=
  hyperratQuotientOrderRingIsoReal.map_le_map_iff'

/-- `hyperratQuotientOrderRingIsoReal` preserves and reflects `<`. -/
theorem hyperratQuotientOrderRingIsoReal_lt_iff {x y : HyperratLimited ⧸ HyperratInfinitesimal} :
    hyperratQuotientOrderRingIsoReal x < hyperratQuotientOrderRingIsoReal y ↔ x < y :=
  hyperratQuotientOrderRingIsoReal.toOrderIso.lt_iff_lt

/-- `ℚ_𝕃 ⧸ ℚ_𝕀` is an ordered additive commutative group. -/
instance instIsOrderedAddMonoidHyperratQuotient :
    IsOrderedAddMonoid (HyperratLimited ⧸ HyperratInfinitesimal) where
  add_le_add_left a b hab c := by
    rw [← hyperratQuotientOrderRingIsoReal_le_iff] at hab ⊢
    simpa [map_add] using add_le_add_right hab (hyperratQuotientOrderRingIsoReal c)

/-- `0 ≤ 1` in `ℚ_𝕃 ⧸ ℚ_𝕀`. -/
instance instZeroLEOneClassHyperratQuotient :
    ZeroLEOneClass (HyperratLimited ⧸ HyperratInfinitesimal) where
  zero_le_one := by
    rw [← hyperratQuotientOrderRingIsoReal_le_iff, map_zero, map_one]
    exact zero_le_one

/-- `ℚ_𝕃 ⧸ ℚ_𝕀` is a strict ordered ring (`IsStrictOrderedRing`, Goldblatt §18.1, p. 233). -/
instance instIsStrictOrderedRingHyperratQuotient :
    IsStrictOrderedRing (HyperratLimited ⧸ HyperratInfinitesimal) := by
  refine IsStrictOrderedRing.of_mul_pos fun a b ha hb ↦ ?_
  rw [← hyperratQuotientOrderRingIsoReal_lt_iff, map_zero, map_mul]
  exact mul_pos
    (by simpa using hyperratQuotientOrderRingIsoReal_lt_iff.2 ha)
    (by simpa using hyperratQuotientOrderRingIsoReal_lt_iff.2 hb)

/-- `ℚ_𝕃 ⧸ ℚ_𝕀` is Archimedean (`Archimedean`, Goldblatt §18.1, p. 233). -/
instance instArchimedeanHyperratQuotient :
    Archimedean (HyperratLimited ⧸ HyperratInfinitesimal) := by
  refine ⟨fun x y hy ↦ ?_⟩
  have hy' : 0 < hyperratQuotientOrderRingIsoReal y := by
    simpa using hyperratQuotientOrderRingIsoReal_lt_iff.2 hy
  obtain ⟨n, hn⟩ := Archimedean.arch (hyperratQuotientOrderRingIsoReal x) hy'
  refine ⟨n, hyperratQuotientOrderRingIsoReal_le_iff.1 ?_⟩
  simpa [map_nsmul] using hn

/-- Uniqueness of the order-ring isomorphism `(ℚ_𝕃 ⧸ ℚ_𝕀) ≃+*o ℝ` (Goldblatt §18.1, p. 233:
"all complete ordered fields are isomorphic, showing independence of the framework"). -/
theorem hyperratQuotientOrderRingIsoReal_unique
    (f : (HyperratLimited ⧸ HyperratInfinitesimal) ≃+*o ℝ) :
    f = hyperratQuotientOrderRingIsoReal :=
  Subsingleton.elim f hyperratQuotientOrderRingIsoReal

/-! ## §18.2–18.3 Metric Space Completion via Nonstandard Hulls -/

/-- Goldblatt §18.3 (p. 234): The ultrapower `*M = Germ (hyperfilter ℕ) M` of a metric space `M`. -/
abbrev StarMetric (M : Type*) : Type _ :=
  Germ (hyperfilter ℕ : Filter ℕ) M

/-- Goldblatt §18.3 (p. 234): Extended hyperreal-valued distance `*d : *M → *M → ℝ*` lifted from
`dist : M → M → ℝ`. -/
def starDist {M : Type*} [Dist M] (x y : StarMetric M) : ℝ* :=
  Germ.map₂ dist x y

/-- Standard elements embed with preserved distance: `*d(a, b) = d(a, b)` (Goldblatt §18.3, p. 235). -/
@[simp]
theorem starDist_const {M : Type*} [Dist M] (a b : M) :
    starDist (Germ.const a : StarMetric M) (Germ.const b) = (dist a b : ℝ*) :=
  rfl

/-- Coordinatewise formula for `starDist`. -/
@[simp]
theorem starDist_coe {M : Type*} [Dist M] (u v : ℕ → M) :
    starDist (u : StarMetric M) (v : StarMetric M) = ofSeq (fun i ↦ dist (u i) (v i)) :=
  rfl

/-- Nonnegativity of `starDist` by transfer (Goldblatt §18.3, p. 234). -/
theorem starDist_nonneg {M : Type*} [PseudoMetricSpace M] (x y : StarMetric M) :
    0 ≤ starDist x y :=
  Germ.inductionOn₂ x y fun _ _ ↦
    ofSeq_le_ofSeq.2 <| Eventually.of_forall fun _ ↦ dist_nonneg

/-- Reflexivity `*d(x, x) = 0` by transfer (Goldblatt §18.3, p. 234). -/
@[simp]
theorem starDist_self {M : Type*} [PseudoMetricSpace M] (x : StarMetric M) :
    starDist x x = 0 :=
  Germ.inductionOn x fun u ↦ Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ dist_self (u i)

/-- Identity of indiscernibles `*d(x, y) = 0 ↔ x = y` by transfer (Goldblatt §18.3, p. 234). -/
theorem starDist_eq_zero_iff {M : Type*} [MetricSpace M] {x y : StarMetric M} :
    starDist x y = 0 ↔ x = y :=
  Germ.inductionOn₂ x y fun u v ↦ by
    have h1 : starDist (u : StarMetric M) (v : StarMetric M) = 0 ↔
        ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), dist (u i) (v i) = 0 :=
      Germ.coe_eq
    rw [h1, Germ.coe_eq]
    exact eventually_congr (Eventually.of_forall fun _ ↦ dist_eq_zero)

/-- Symmetry `*d(x, y) = *d(y, x)` by transfer (Goldblatt §18.3, p. 234). -/
theorem starDist_comm {M : Type*} [PseudoMetricSpace M] (x y : StarMetric M) :
    starDist x y = starDist y x :=
  Germ.inductionOn₂ x y fun u v ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ dist_comm (u i) (v i)

/-- Triangle inequality `*d(x, z) ≤ *d(x, y) + *d(y, z)` by transfer (Goldblatt §18.3, p. 234). -/
theorem starDist_triangle {M : Type*} [PseudoMetricSpace M] (x y z : StarMetric M) :
    starDist x z ≤ starDist x y + starDist y z :=
  Germ.inductionOn₃ x y z fun u v w ↦
    ofSeq_le_ofSeq.2 <| Eventually.of_forall fun i ↦ dist_triangle (u i) (v i) (w i)

/-- Absolute difference bound `|*d(x, y) - *d(x', y')| ≤ *d(x, x') + *d(y, y')` on `StarMetric M`. -/
theorem abs_starDist_sub_le {M : Type*} [PseudoMetricSpace M] (x y x' y' : StarMetric M) :
    |starDist x y - starDist x' y'| ≤ starDist x x' + starDist y y' := by
  rw [abs_sub_le_iff]
  constructor
  · have h1 := starDist_triangle x x' y'
    have h2 := starDist_triangle x y' y
    have hc : starDist y' y = starDist y y' := starDist_comm y' y
    linarith
  · have h1 := starDist_triangle x' x y
    have h2 := starDist_triangle x' y y'
    have hc : starDist x' x = starDist x x' := starDist_comm x' x
    linarith

/-- Goldblatt §18.3 (p. 234): Infinitesimal proximity `x ≈ₘ y` (`*d(x, y) ≈ 0`) in `*M`. -/
def MetricInfClose {M : Type*} [Dist M] (x y : StarMetric M) : Prop :=
  IsInfinitesimal (starDist x y)

/-- Goldblatt §18.3 (p. 234): Limited proximity `x ∼ₘ y` (`*d(x, y)` is limited) in `*M`. -/
def MetricLimDist {M : Type*} [Dist M] (x y : StarMetric M) : Prop :=
  IsLimited (starDist x y)

/-- Reflexivity of `MetricInfClose`. -/
@[refl]
theorem MetricInfClose.refl {M : Type*} [PseudoMetricSpace M] (x : StarMetric M) :
    MetricInfClose x x := by
  simpa [MetricInfClose] using isInfinitesimal_zero

/-- Symmetry of `MetricInfClose`. -/
@[symm]
theorem MetricInfClose.symm {M : Type*} [PseudoMetricSpace M] {x y : StarMetric M}
    (h : MetricInfClose x y) : MetricInfClose y x := by
  unfold MetricInfClose at *
  rwa [starDist_comm]

/-- Transitivity of `MetricInfClose`. -/
@[trans]
theorem MetricInfClose.trans {M : Type*} [PseudoMetricSpace M] {x y z : StarMetric M}
    (hxy : MetricInfClose x y) (hyz : MetricInfClose y z) : MetricInfClose x z := by
  refine isInfinitesimal_of_abs_le (hxy.add hyz) ?_
  rw [abs_of_nonneg (starDist_nonneg x z),
      abs_of_nonneg (add_nonneg (starDist_nonneg x y) (starDist_nonneg y z))]
  exact starDist_triangle x y z

/-- `MetricInfClose` is an equivalence relation on `StarMetric M` (Goldblatt §18.3, p. 234). -/
theorem metricInfClose_equivalence (M : Type*) [PseudoMetricSpace M] :
    Equivalence (MetricInfClose (M := M)) :=
  ⟨MetricInfClose.refl, MetricInfClose.symm, MetricInfClose.trans⟩

/-- `MetricLimDist` is an equivalence relation on `StarMetric M` (Goldblatt §18.3, p. 234). -/
theorem metricLimDist_equivalence (M : Type*) [PseudoMetricSpace M] :
    Equivalence (MetricLimDist (M := M)) where
  refl x := by simpa [MetricLimDist] using isLimited_coe 0
  symm h := by unfold MetricLimDist at *; rwa [starDist_comm]
  trans {x y z} hxy hyz := by
    refine isLimited_of_abs_le (hxy.add hyz) ?_
    rw [abs_of_nonneg (starDist_nonneg x z),
        abs_of_nonneg (add_nonneg (starDist_nonneg x y) (starDist_nonneg y z))]
    exact starDist_triangle x y z

/-- Goldblatt §18.3 (p. 234): Metric halo `hal(x) = {y ∈ *M | x ≈ₘ y}`. -/
def metricHalo {M : Type*} [Dist M] (x : StarMetric M) : Set (StarMetric M) :=
  {y : StarMetric M | MetricInfClose x y}

/-- Goldblatt §18.3 (p. 234): Metric galaxy `gal(x) = {y ∈ *M | x ∼ₘ y}`. -/
def metricGalaxy {M : Type*} [Dist M] (x : StarMetric M) : Set (StarMetric M) :=
  {y : StarMetric M | MetricLimDist x y}

/-- Goldblatt §18.3 (p. 235): The set of limited points `LimitedMetric M p` (`gal(p) = *M_lim`),
consisting of points at limited hyperreal distance from basepoint `p ∈ M`. -/
def LimitedMetric (M : Type*) [MetricSpace M] (p : M) : Set (StarMetric M) :=
  {x : StarMetric M | IsLimited (starDist x (Germ.const p))}

/-- Goldblatt §18.3 (p. 235): Basepoint-free definition `*M_lim = {x ∈ *M | ∃ y ∈ M, *d(x, y) ∈ 𝕃}`. -/
def IsLimitedMetric {M : Type*} [MetricSpace M] (x : StarMetric M) : Prop :=
  ∃ y : M, IsLimited (starDist x (Germ.const y))

/-- Basepoint independence of `LimitedMetric M p` (`LimitedMetric M p = LimitedMetric M q`,
Goldblatt §18.3, p. 235). -/
theorem limitedMetric_eq_of_basepoint {M : Type*} [MetricSpace M] (p q : M) :
    LimitedMetric M p = LimitedMetric M q := by
  have sub : ∀ a b : M, LimitedMetric M a ⊆ LimitedMetric M b := by
    intro a b x hx
    refine isLimited_of_abs_le (hx.add (isLimited_coe (dist a b))) ?_
    rw [← starDist_const a b,
        abs_of_nonneg (starDist_nonneg x (Germ.const b)),
        abs_of_nonneg (add_nonneg (starDist_nonneg x (Germ.const a))
          (starDist_nonneg (Germ.const a) (Germ.const b)))]
    exact starDist_triangle x (Germ.const a) (Germ.const b)
  exact Set.Subset.antisymm (sub p q) (sub q p)

/-- `LimitedMetric M p` equals the principal galaxy `{x ∈ *M | IsLimitedMetric x}`
(Goldblatt §18.3, p. 235). -/
theorem limitedMetric_eq_principalGalaxy {M : Type*} [MetricSpace M] (p : M) :
    LimitedMetric M p = {x : StarMetric M | IsLimitedMetric x} := by
  ext x
  constructor
  · exact fun hx ↦ ⟨p, hx⟩
  · rintro ⟨q, hq⟩
    rw [limitedMetric_eq_of_basepoint p q]
    exact hq

/-- Halo invariance of `LimitedMetric M p`: if `x ∈ LimitedMetric M p` and `x ≈ₘ y`, then
`y ∈ LimitedMetric M p` (Goldblatt §18.3, p. 235). -/
theorem mem_limitedMetric_of_infClose {M : Type*} [MetricSpace M] {p : M} {x y : StarMetric M}
    (hx : x ∈ LimitedMetric M p) (hxy : MetricInfClose x y) :
    y ∈ LimitedMetric M p := by
  refine isLimited_of_abs_le (hxy.symm.isLimited.add hx) ?_
  rw [abs_of_nonneg (starDist_nonneg y (Germ.const p)),
      abs_of_nonneg (add_nonneg (starDist_nonneg y x) (starDist_nonneg x (Germ.const p)))]
  exact starDist_triangle y x (Germ.const p)

/-- Distance between any two points of `LimitedMetric M p` is limited. -/
theorem starDist_isLimited_of_mem_limitedMetric {M : Type*} [MetricSpace M] {p : M}
    {x y : StarMetric M} (hx : x ∈ LimitedMetric M p) (hy : y ∈ LimitedMetric M p) :
    IsLimited (starDist x y) := by
  refine isLimited_of_abs_le (hx.add hy) ?_
  rw [abs_of_nonneg (starDist_nonneg x y),
      abs_of_nonneg (add_nonneg (starDist_nonneg x (Germ.const p))
        (starDist_nonneg y (Germ.const p))),
      starDist_comm y (Germ.const p)]
  exact starDist_triangle x (Germ.const p) y

/-- Setoid of infinitesimal proximity `≈ₘ` on `LimitedMetric M p` (Goldblatt §18.3, p. 235). -/
def limitedMetricSetoid (M : Type*) [MetricSpace M] (p : M) : Setoid (LimitedMetric M p) where
  r x y := MetricInfClose x.1 y.1
  iseqv := ⟨fun x ↦ MetricInfClose.refl x.1,
            fun h ↦ h.symm,
            fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Goldblatt §18.3 (p. 235): The **Nonstandard Metric Hull** `MetricHull M p = *M_lim / ≈ₘ`. -/
abbrev MetricHull (M : Type*) [MetricSpace M] (p : M) : Type _ :=
  Quotient (limitedMetricSetoid M p)

/-- Well-definedness of `shadow (starDist x y)` under `MetricInfClose` (Goldblatt §18.3, p. 235). -/
theorem shadow_starDist_congr {M : Type*} [MetricSpace M] {x x' y y' : StarMetric M}
    (hlim : IsLimited (starDist x y))
    (hxx' : MetricInfClose x x') (hyy' : MetricInfClose y y') :
    shadow (starDist x y) = shadow (starDist x' y') := by
  apply shadow_eq_of_infClose
  have hlim' : IsLimited (starDist x' y') := by
    refine isLimited_of_abs_le (hlim.add (hxx'.add hyy').isLimited) ?_
    have hbound := abs_starDist_sub_le x' y' x y
    rw [starDist_comm x' x, starDist_comm y' y] at hbound
    rw [abs_of_nonneg (starDist_nonneg x' y'),
        abs_of_nonneg (add_nonneg (starDist_nonneg x y)
          (add_nonneg (starDist_nonneg x x') (starDist_nonneg y y')))]
    linarith [(abs_le.1 hbound).2]
  have hclose : starDist x y ≈ₕ starDist x' y' :=
    isInfinitesimal_of_abs_le (hxx'.add hyy')
      ((abs_starDist_sub_le x y x' y').trans_eq
        (abs_of_nonneg (add_nonneg (starDist_nonneg x x') (starDist_nonneg y y'))).symm)
  exact hclose.trans (infClose_shadow hlim')

/-- Distance function `d(hal(x), hal(y)) = sh(*d(x, y))` on `MetricHull M p`
(Goldblatt §18.3, p. 235). -/
def hullDist {M : Type*} [MetricSpace M] {p : M} (x y : MetricHull M p) : ℝ :=
  Quotient.lift₂ (fun a b : LimitedMetric M p ↦ shadow (starDist a.1 b.1))
    (fun a b _ _ ha hb ↦
      shadow_starDist_congr (starDist_isLimited_of_mem_limitedMetric a.2 b.2) ha hb) x y

/-- Unfolding `hullDist` on representatives. -/
@[simp]
theorem hullDist_mk {M : Type*} [MetricSpace M] {p : M} (a b : LimitedMetric M p) :
    hullDist (Quotient.mk (limitedMetricSetoid M p) a)
      (Quotient.mk (limitedMetricSetoid M p) b) = shadow (starDist a.1 b.1) :=
  rfl

/-- Goldblatt §18.3 (p. 235): `MetricHull M p` is a genuine `MetricSpace` under `hullDist`. -/
instance instMetricSpaceMetricHull (M : Type*) [MetricSpace M] (p : M) :
    MetricSpace (MetricHull M p) where
  dist := hullDist
  dist_self x := Quotient.inductionOn x fun a ↦ by simp [hullDist_mk]
  dist_comm x y := Quotient.inductionOn₂ x y fun a b ↦ by
    simp only [hullDist_mk, starDist_comm]
  dist_triangle x y z := Quotient.inductionOn₃ x y z fun a b c ↦ by
    simp only [hullDist_mk]
    have hab := starDist_isLimited_of_mem_limitedMetric a.2 b.2
    have hbc := starDist_isLimited_of_mem_limitedMetric b.2 c.2
    have hac := starDist_isLimited_of_mem_limitedMetric a.2 c.2
    rw [← shadow_add hab hbc]
    exact shadow_le_of_le hac (hab.add hbc) (starDist_triangle a.1 b.1 c.1)
  eq_of_dist_eq_zero {x y} := Quotient.inductionOn₂ x y fun a b h ↦ by
    apply Quotient.sound
    exact (shadow_eq_zero_iff_isInfinitesimal
      (starDist_isLimited_of_mem_limitedMetric a.2 b.2)).1 h

/-- Unfolding `dist` on `MetricHull M p`. -/
@[simp]
theorem dist_metricHull_mk {M : Type*} [MetricSpace M] {p : M} (a b : LimitedMetric M p) :
    dist (Quotient.mk (limitedMetricSetoid M p) a)
      (Quotient.mk (limitedMetricSetoid M p) b) = shadow (starDist a.1 b.1) :=
  rfl

/-- Goldblatt §18.3 (p. 235): Canonical embedding `a ↦ hal(a)` of `M` into `MetricHull M p`. -/
def hullEmbed (M : Type*) [MetricSpace M] (p : M) (a : M) : MetricHull M p :=
  Quotient.mk (limitedMetricSetoid M p)
    ⟨Germ.const a, isLimited_coe (dist a p)⟩

/-- `hullEmbed M p` preserves distances (`dist (hullEmbed M p a) (hullEmbed M p b) = dist a b`,
Goldblatt §18.3, p. 235). -/
@[simp]
theorem dist_hullEmbed {M : Type*} [MetricSpace M] (p : M) (a b : M) :
    dist (hullEmbed M p a) (hullEmbed M p b) = dist a b := by
  simp [hullEmbed]

/-- `hullEmbed M p : M → MetricHull M p` is an `Isometry` (Goldblatt §18.3, p. 235). -/
theorem hullEmbed_isometry (M : Type*) [MetricSpace M] (p : M) :
    Isometry (hullEmbed M p) :=
  Isometry.of_dist_eq (dist_hullEmbed p)

/-- Canonical basepoint-change isometric equivalence `MetricHull M p ≃ᵢ MetricHull M q`
(Goldblatt §18.3, p. 235). -/
def metricHullBasepointEquiv {M : Type*} [MetricSpace M] (p q : M) :
    MetricHull M p ≃ᵢ MetricHull M q where
  toFun := Quotient.lift
    (fun a : LimitedMetric M p ↦ Quotient.mk (limitedMetricSetoid M q)
      ⟨a.1, (limitedMetric_eq_of_basepoint p q) ▸ a.2⟩)
    (fun _ _ h ↦ Quotient.sound h)
  invFun := Quotient.lift
    (fun a : LimitedMetric M q ↦ Quotient.mk (limitedMetricSetoid M p)
      ⟨a.1, (limitedMetric_eq_of_basepoint q p) ▸ a.2⟩)
    (fun _ _ h ↦ Quotient.sound h)
  left_inv x := Quotient.inductionOn x fun _ ↦ rfl
  right_inv x := Quotient.inductionOn x fun _ ↦ rfl
  isometry_toFun := Isometry.of_dist_eq fun x y ↦ Quotient.inductionOn₂ x y fun _ _ ↦ rfl

/-- Internal hypersequence extension `ℕ* → StarMetric M` of a family of sequence representatives
`s : ℕ → ℕ → M`, realizing sequential comprehensiveness in `StarMetric M`
(Goldblatt §18.3, Theorem 18.3.1 proof, p. 235). -/
def internalMetricSeq {M : Type*} (s : ℕ → ℕ → M) (N : ℕ*) : StarMetric M :=
  Germ.map₂ (fun (f : ℕ → M) (m : ℕ) ↦ f m)
    ((fun i m ↦ s m i) : Germ (hyperfilter ℕ : Filter ℕ) (ℕ → M)) N

/-- Evaluating `internalMetricSeq s` at a standard index `(n : ℕ*)` recovers `(s n : StarMetric M)`. -/
@[simp]
theorem internalMetricSeq_natCast {M : Type*} (s : ℕ → ℕ → M) (n : ℕ) :
    internalMetricSeq s (n : ℕ*) = (s n : StarMetric M) :=
  rfl

/-- Internal set property for hypersequence distance balls in `ℕ*`:
`{N ∈ ℕ* | *d(x_N, y) < r}` is an internal subset of `ℕ*` (Goldblatt §18.3, p. 236). -/
theorem isInternalNat_starDist_lt {M : Type*} [Dist M] (s : ℕ → ℕ → M) (v : ℕ → M) (r : ℝ) :
    IsInternalNat {N : ℕ* | starDist (internalMetricSeq s N) (v : StarMetric M) < (r : ℝ*)} := by
  refine ⟨fun i ↦ {m : ℕ | dist (s m i) (v i) < r}, ?_⟩
  ext N
  induction N using Germ.inductionOn with | _ a =>
  rw [Set.mem_ofPred_eq, coe_mem_internalNatSet]
  change ofSeq (fun i ↦ dist (s (a i) i) (v i)) < ofSeq (fun _ ↦ r) ↔ _
  exact ofSeq_lt_ofSeq

/-- Core convergence lemma for **Theorem 18.3.1** & **Theorem 18.3.2** (Goldblatt pp. 235–236):
Given representatives `x : ℕ → StarMetric M` whose shadows form a Cauchy sequence (in the sense that
`∀ n, ∃ k_n, ∀ m ≥ k_n, sh(*d(x_m, x_{k_n})) < 1 / (4(n+1))`), Overflow and Countable Saturation
produce an unlimited `K ∈ ℕ*` such that `*d(x_m, x_K) < 1 / (n + 1)` for all `m ≥ k_n`. -/
theorem exists_unlimited_limit_of_cauchy_starMetric {M : Type*} [MetricSpace M]
    (s : ℕ → ℕ → M) {p : M}
    (hlim : ∀ n : ℕ, (s n : StarMetric M) ∈ LimitedMetric M p)
    (hcauchy : ∀ n : ℕ, ∃ kn : ℕ, ∀ m : ℕ, kn ≤ m →
      shadow (starDist (s m : StarMetric M) (s kn : StarMetric M)) <
        1 / (4 * ((n + 1 : ℕ) : ℝ))) :
    ∃ K : ℕ*, IsUnlimitedNat K ∧
      internalMetricSeq s K ∈ LimitedMetric M p ∧
      ∀ n : ℕ, ∃ kn : ℕ, ∀ m : ℕ, kn ≤ m →
        starDist (s m : StarMetric M) (internalMetricSeq s K) <
          ((1 / ((n + 1 : ℕ) : ℝ) : ℝ) : ℝ*) := by
  choose kn hkn using hcauchy
  -- Step 1: For each `n`, `*d(x_m, x_{kn n}) < 1 / (2(n+1))` for all standard `m ≥ kn n`.
  have hstd : ∀ n m : ℕ, kn n ≤ m →
      starDist (internalMetricSeq s (m : ℕ*)) (s (kn n) : StarMetric M) <
        ((1 / (2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : ℝ*) := by
    intro n m hm
    rw [internalMetricSeq_natCast]
    have hd_lim := starDist_isLimited_of_mem_limitedMetric (hlim m) (hlim (kn n))
    set sh := shadow (starDist (s m : StarMetric M) (s (kn n) : StarMetric M))
    have hsh_lt := hkn n m hm
    have hclose := infClose_shadow hd_lim (1 / (4 * ((n + 1 : ℕ) : ℝ))) (by positivity)
    have h1 : starDist (s m : StarMetric M) (s (kn n) : StarMetric M) <
        (sh : ℝ*) + ((1 / (4 * ((n + 1 : ℕ) : ℝ)) : ℝ) : ℝ*) := by
      linarith [(abs_lt.1 hclose).2]
    have h2 : sh + 1 / (4 * ((n + 1 : ℕ) : ℝ)) < 1 / (2 * ((n + 1 : ℕ) : ℝ)) := by
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hquarter : 1 / (4 * ((n + 1 : ℕ) : ℝ)) + 1 / (4 * ((n + 1 : ℕ) : ℝ)) =
          1 / (2 * ((n + 1 : ℕ) : ℝ)) := by field_simp [hpos.ne']; ring
      linarith
    exact h1.trans (by rw [← Hyperreal.coe_add]; exact Hyperreal.coe_lt_coe.2 h2)
  -- Step 2: Apply Overflow to each internal set `A n = {N ∈ ℕ* | *d(x_N, x_{kn n}) < 1/(2(n+1))}`.
  have hover : ∀ n : ℕ, ∃ Kn : ℕ*, IsUnlimitedNat Kn ∧
      ∀ N : ℕ*, (kn n : ℕ*) ≤ N → N ≤ Kn →
        starDist (internalMetricSeq s N) (s (kn n) : StarMetric M) <
          ((1 / (2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : ℝ*) := by
    intro n
    exact overflow_nat (isInternalNat_starDist_lt s (s (kn n)) _) (hstd n)
  choose Kn hKn_unl hKn_seg using hover
  -- Step 3: Countable saturation gives an unlimited `K ≤ Kn n` for all `n`.
  obtain ⟨K, hK_unl, hK_le⟩ := exists_unlimitedNat_lower_bound Kn hKn_unl
  have hK_in : ∀ n : ℕ, starDist (internalMetricSeq s K) (s (kn n) : StarMetric M) <
      ((1 / (2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : ℝ*) :=
    fun n ↦ hKn_seg n K (hK_unl (kn n)).le (hK_le n)
  have hK_lim : internalMetricSeq s K ∈ LimitedMetric M p := by
    refine isLimited_of_abs_le ((isLimited_coe (1 / 2)).add (hlim (kn 0))) ?_
    rw [abs_of_nonneg (starDist_nonneg _ _),
        abs_of_nonneg (add_nonneg (Hyperreal.coe_nonneg.2 (by positivity)) (starDist_nonneg _ _))]
    have h0 : starDist (internalMetricSeq s K) (s (kn 0) : StarMetric M) ≤ ((1 / 2 : ℝ) : ℝ*) := by
      simpa using (hK_in 0).le
    exact (starDist_triangle _ (s (kn 0) : StarMetric M) _).trans
      (add_le_add h0 le_rfl)
  refine ⟨K, hK_unl, hK_lim, fun n ↦ ⟨kn n, fun m hm ↦ ?_⟩⟩
  have hm_in := hstd n m hm
  rw [internalMetricSeq_natCast] at hm_in
  have hsum : ((1 / (2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : ℝ*) +
      ((1 / (2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : ℝ*) =
      ((1 / ((n + 1 : ℕ) : ℝ) : ℝ) : ℝ*) := by
    rw [← Hyperreal.coe_add]
    congr 1
    have hpos : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hpos]
    ring
  calc starDist (s m : StarMetric M) (internalMetricSeq s K)
      ≤ starDist (s m : StarMetric M) (s (kn n) : StarMetric M) +
          starDist (s (kn n) : StarMetric M) (internalMetricSeq s K) :=
        starDist_triangle _ _ _
    _ < ((1 / (2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : ℝ*) +
          ((1 / (2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : ℝ*) := by
        rw [starDist_comm (s (kn n) : StarMetric M)]
        exact add_lt_add hm_in (hK_in n)
    _ = ((1 / ((n + 1 : ℕ) : ℝ) : ℝ) : ℝ*) := hsum

/-- Goldblatt Theorem 18.3.1 (pp. 235–236): **The nonstandard hull `(MetricHull M p, d)` is a
complete metric space!** -/
instance instCompleteSpaceMetricHull (M : Type*) [MetricSpace M] (p : M) :
    CompleteSpace (MetricHull M p) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  choose x hx using fun n ↦ Quotient.exists_rep (u n)
  have hrep : ∀ n : ℕ, ∃ f : ℕ → M, (f : StarMetric M) = (x n).1 := fun n ↦ by
    induction (x n).1 using Germ.inductionOn with | _ f => exact ⟨f, rfl⟩
  choose s hs using hrep
  have hlim : ∀ n : ℕ, (s n : StarMetric M) ∈ LimitedMetric M p := fun n ↦ by
    rw [hs n]; exact (x n).2
  have hcauchy : ∀ n : ℕ, ∃ kn : ℕ, ∀ m : ℕ, kn ≤ m →
      shadow (starDist (s m : StarMetric M) (s kn : StarMetric M)) <
        1 / (4 * ((n + 1 : ℕ) : ℝ)) := by
    intro n
    obtain ⟨kn, hkn⟩ := Metric.cauchySeq_iff'.1 hu (1 / (4 * ((n + 1 : ℕ) : ℝ))) (by positivity)
    refine ⟨kn, fun m hm ↦ ?_⟩
    have hd := hkn m hm
    rw [← hx m, ← hx kn, dist_metricHull_mk] at hd
    simpa [hs m, hs kn] using hd
  obtain ⟨K, _, hK_lim, hconv⟩ := exists_unlimited_limit_of_cauchy_starMetric s hlim hcauchy
  let L : MetricHull M p := Quotient.mk (limitedMetricSetoid M p) ⟨internalMetricSeq s K, hK_lim⟩
  refine ⟨L, Metric.tendsto_atTop.2 fun ε hε ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨kn, hkn⟩ := hconv n
  refine ⟨kn, fun m hm ↦ ?_⟩
  have hlt := hkn m hm
  have hd_eq : dist (u m) L = shadow (starDist (s m : StarMetric M) (internalMetricSeq s K)) := by
    rw [← hx m, dist_metricHull_mk]
    simp [hs m]
  rw [hd_eq]
  have hle : shadow (starDist (s m : StarMetric M) (internalMetricSeq s K)) ≤
      1 / ((n + 1 : ℕ) : ℝ) := by
    have h := shadow_le_of_le
      (starDist_isLimited_of_mem_limitedMetric (hlim m) hK_lim)
      (isLimited_coe (1 / ((n + 1 : ℕ) : ℝ))) hlt.le
    rwa [shadow_coe] at h
  exact hle.trans_lt (by push_cast; exact hn)

/-- Goldblatt §18.3 (p. 236): `x ∈ *M` is **approachable from `M`** (or **pre-nearstandard**) if
for every standard `ε > 0`, there is a standard `a ∈ M` with `*d(x, a) < ε`. -/
def IsPreNearstandard {M : Type*} [MetricSpace M] (x : StarMetric M) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : M, starDist x (Germ.const a) < (ε : ℝ*)

/-- Goldblatt §18.3 (p. 236): The set `*M_ap` (`PreNearstandard M`) of approachable points in `*M`. -/
def PreNearstandard (M : Type*) [MetricSpace M] : Set (StarMetric M) :=
  {x : StarMetric M | IsPreNearstandard x}

/-- Every standard point `Germ.const a` is pre-nearstandard. -/
theorem const_mem_preNearstandard {M : Type*} [MetricSpace M] (a : M) :
    (Germ.const a : StarMetric M) ∈ PreNearstandard M :=
  fun ε hε ↦ ⟨a, by simpa using Hyperreal.coe_pos.2 hε⟩

/-- `*M_ap ⊆ *M_lim` (`PreNearstandard M ⊆ LimitedMetric M p`, Goldblatt §18.3, p. 236). -/
theorem preNearstandard_subset_limitedMetric {M : Type*} [MetricSpace M] (p : M) :
    PreNearstandard M ⊆ LimitedMetric M p := by
  intro x hx
  obtain ⟨a, ha⟩ := hx 1 one_pos
  have ha_lim : x ∈ LimitedMetric M a :=
    isLimited_of_abs_le (isLimited_coe 1)
      (by rw [abs_of_nonneg (starDist_nonneg _ _)]; simpa using ha.le)
  rwa [limitedMetric_eq_of_basepoint p a]

/-- Halo invariance of `PreNearstandard M` (`hal(x) ⊆ *M_ap`, Goldblatt §18.3, p. 236). -/
theorem mem_preNearstandard_of_infClose {M : Type*} [MetricSpace M] {x y : StarMetric M}
    (hx : x ∈ PreNearstandard M) (hxy : MetricInfClose x y) :
    y ∈ PreNearstandard M := by
  intro ε hε
  obtain ⟨a, ha⟩ := hx (ε / 2) (half_pos hε)
  have h1 := hxy.symm (ε / 2) (half_pos hε)
  rw [abs_of_nonneg (starDist_nonneg y x)] at h1
  refine ⟨a, ?_⟩
  have hsum : ((ε / 2 : ℝ) : ℝ*) + ((ε / 2 : ℝ) : ℝ*) = (ε : ℝ*) := by
    rw [← Hyperreal.coe_add, add_halves]
  exact (starDist_triangle y x (Germ.const a)).trans_lt ((add_lt_add h1 ha).trans_eq hsum)

/-- Distance between any two pre-nearstandard points is limited (even without picking a basepoint). -/
theorem starDist_isLimited_of_preNearstandard {M : Type*} [MetricSpace M]
    {x y : StarMetric M} (hx : x ∈ PreNearstandard M) (hy : y ∈ PreNearstandard M) :
    IsLimited (starDist x y) := by
  obtain ⟨a, _⟩ := hx 1 one_pos
  exact starDist_isLimited_of_mem_limitedMetric
    (preNearstandard_subset_limitedMetric a hx)
    (preNearstandard_subset_limitedMetric a hy)

/-- Setoid of infinitesimal proximity `≈ₘ` on `PreNearstandard M` (Goldblatt §18.3, p. 236). -/
def preNearstandardSetoid (M : Type*) [MetricSpace M] : Setoid (PreNearstandard M) where
  r x y := MetricInfClose x.1 y.1
  iseqv := ⟨fun x ↦ MetricInfClose.refl x.1, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Goldblatt §18.3, Theorem 18.3.2 (p. 236): The nonstandard **Metric Completion**
`MetricCompletion M = *M_ap / ≈ₘ`. -/
abbrev MetricCompletion (M : Type*) [MetricSpace M] : Type _ :=
  Quotient (preNearstandardSetoid M)

/-- Metric space structure on `MetricCompletion M` via `d([x], [y]) = sh(*d(x, y))`
(Goldblatt §18.3, p. 236). -/
instance instMetricSpaceMetricCompletion (M : Type*) [MetricSpace M] :
    MetricSpace (MetricCompletion M) where
  dist := Quotient.lift₂ (fun a b : PreNearstandard M ↦ shadow (starDist a.1 b.1))
    (fun a b a' b' ha hb ↦
      shadow_starDist_congr (starDist_isLimited_of_preNearstandard a.2 b.2) ha hb)
  dist_self x := Quotient.inductionOn x fun a ↦ by simp
  dist_comm x y := Quotient.inductionOn₂ x y fun a b ↦ by
    change shadow (starDist a.1 b.1) = shadow (starDist b.1 a.1)
    rw [starDist_comm]
  dist_triangle x y z := Quotient.inductionOn₃ x y z fun a b c ↦ by
    change shadow (starDist a.1 c.1) ≤ shadow (starDist a.1 b.1) + shadow (starDist b.1 c.1)
    have hab := starDist_isLimited_of_preNearstandard a.2 b.2
    have hbc := starDist_isLimited_of_preNearstandard b.2 c.2
    have hac := starDist_isLimited_of_preNearstandard a.2 c.2
    rw [← shadow_add hab hbc]
    exact shadow_le_of_le hac (hab.add hbc) (starDist_triangle a.1 b.1 c.1)
  eq_of_dist_eq_zero {x y} := Quotient.inductionOn₂ x y fun a b h ↦ by
    apply Quotient.sound
    exact (shadow_eq_zero_iff_isInfinitesimal
      (starDist_isLimited_of_preNearstandard a.2 b.2)).1 h

/-- Unfolding `dist` on `MetricCompletion M`. -/
@[simp]
theorem dist_metricCompletion_mk {M : Type*} [MetricSpace M] (a b : PreNearstandard M) :
    dist (Quotient.mk (preNearstandardSetoid M) a)
      (Quotient.mk (preNearstandardSetoid M) b) = shadow (starDist a.1 b.1) :=
  rfl

/-- Canonical embedding `completionEmbed M : M → MetricCompletion M` (`a ↦ hal(a)`). -/
def completionEmbed (M : Type*) [MetricSpace M] (a : M) : MetricCompletion M :=
  Quotient.mk (preNearstandardSetoid M) ⟨Germ.const a, const_mem_preNearstandard a⟩

/-- `completionEmbed M` preserves distances. -/
@[simp]
theorem dist_completionEmbed {M : Type*} [MetricSpace M] (a b : M) :
    dist (completionEmbed M a) (completionEmbed M b) = dist a b := by
  simp [completionEmbed]

/-- `completionEmbed M` is an `Isometry` (Goldblatt Theorem 18.3.2, p. 236). -/
theorem completionEmbed_isometry (M : Type*) [MetricSpace M] :
    Isometry (completionEmbed M) :=
  Isometry.of_dist_eq dist_completionEmbed

/-- `completionEmbed M` has dense range in `MetricCompletion M` (Goldblatt Theorem 18.3.2, p. 236). -/
theorem completionEmbed_denseRange (M : Type*) [MetricSpace M] :
    DenseRange (completionEmbed M) := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  induction x using Quotient.inductionOn with | _ y =>
  obtain ⟨a, ha⟩ := y.2 (ε / 2) (half_pos hε)
  refine ⟨a, ?_⟩
  rw [completionEmbed, dist_metricCompletion_mk]
  have hle := shadow_le_of_le
    (starDist_isLimited_of_preNearstandard y.2 (const_mem_preNearstandard a))
    (isLimited_coe (ε / 2)) ha.le
  rw [shadow_coe] at hle
  exact hle.trans_lt (half_lt_self hε)

/-- Goldblatt Theorem 18.3.2 (p. 236): **`MetricCompletion M` is a complete metric space**, hence a
genuine completion of `(M, d)`! -/
instance instCompleteSpaceMetricCompletion (M : Type*) [MetricSpace M] :
    CompleteSpace (MetricCompletion M) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  -- Extract a basepoint from `u 0`
  obtain ⟨y₀, _⟩ := Quotient.exists_rep (u 0)
  obtain ⟨p, _⟩ := y₀.2 1 one_pos
  choose x hx using fun n ↦ Quotient.exists_rep (u n)
  have hrep : ∀ n : ℕ, ∃ f : ℕ → M, (f : StarMetric M) = (x n).1 := fun n ↦ by
    induction (x n).1 using Germ.inductionOn with | _ f => exact ⟨f, rfl⟩
  choose s hs using hrep
  have hpre : ∀ n : ℕ, (s n : StarMetric M) ∈ PreNearstandard M := fun n ↦ by
    rw [hs n]; exact (x n).2
  have hlim : ∀ n : ℕ, (s n : StarMetric M) ∈ LimitedMetric M p :=
    fun n ↦ preNearstandard_subset_limitedMetric p (hpre n)
  have hcauchy : ∀ n : ℕ, ∃ kn : ℕ, ∀ m : ℕ, kn ≤ m →
      shadow (starDist (s m : StarMetric M) (s kn : StarMetric M)) <
        1 / (4 * ((n + 1 : ℕ) : ℝ)) := by
    intro n
    obtain ⟨kn, hkn⟩ := Metric.cauchySeq_iff'.1 hu (1 / (4 * ((n + 1 : ℕ) : ℝ))) (by positivity)
    refine ⟨kn, fun m hm ↦ ?_⟩
    have hd := hkn m hm
    rw [← hx m, ← hx kn, dist_metricCompletion_mk] at hd
    simpa [hs m, hs kn] using hd
  obtain ⟨K, _, _, hconv⟩ := exists_unlimited_limit_of_cauchy_starMetric s hlim hcauchy
  -- Show `internalMetricSeq s K` is approachable from `M` (Goldblatt p. 236)!
  have hK_pre : internalMetricSeq s K ∈ PreNearstandard M := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨kn, hkn⟩ := hconv n
    have h1 : starDist (internalMetricSeq s K) (s kn : StarMetric M) < ((ε / 2 : ℝ) : ℝ*) := by
      rw [starDist_comm]
      exact (hkn kn le_rfl).trans (Hyperreal.coe_lt_coe.2 (by push_cast; exact hn))
    obtain ⟨a, ha⟩ := hpre kn (ε / 2) (half_pos hε)
    refine ⟨a, ?_⟩
    have hsum : ((ε / 2 : ℝ) : ℝ*) + ((ε / 2 : ℝ) : ℝ*) = (ε : ℝ*) := by
      rw [← Hyperreal.coe_add, add_halves]
    exact (starDist_triangle _ (s kn : StarMetric M) _).trans_lt ((add_lt_add h1 ha).trans_eq hsum)
  let L : MetricCompletion M := Quotient.mk (preNearstandardSetoid M) ⟨internalMetricSeq s K, hK_pre⟩
  refine ⟨L, Metric.tendsto_atTop.2 fun ε hε ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨kn, hkn⟩ := hconv n
  refine ⟨kn, fun m hm ↦ ?_⟩
  have hlt := hkn m hm
  have hd_eq : dist (u m) L = shadow (starDist (s m : StarMetric M) (internalMetricSeq s K)) := by
    rw [← hx m, dist_metricCompletion_mk]
    simp [hs m]
  rw [hd_eq]
  have hle : shadow (starDist (s m : StarMetric M) (internalMetricSeq s K)) ≤
      1 / ((n + 1 : ℕ) : ℝ) := by
    have h := shadow_le_of_le
      (starDist_isLimited_of_preNearstandard (hpre m) hK_pre)
      (isLimited_coe (1 / ((n + 1 : ℕ) : ℝ))) hlt.le
    rwa [shadow_coe] at h
  exact hle.trans_lt (by push_cast; exact hn)

/-- Isometric embedding of `MetricCompletion M` into `MetricHull M p` whose range is the topological
closure of `hullEmbed M p` (Goldblatt §18.3, p. 236). -/
def completionToHull {M : Type*} [MetricSpace M] (p : M) :
    MetricCompletion M → MetricHull M p :=
  Quotient.lift
    (fun a : PreNearstandard M ↦ Quotient.mk (limitedMetricSetoid M p)
      ⟨a.1, preNearstandard_subset_limitedMetric p a.2⟩)
    (fun _ _ h ↦ Quotient.sound h)

/-- `completionToHull p` is an `Isometry` and maps `MetricCompletion M` onto `closure (range (hullEmbed M p))`. -/
theorem completionToHull_isometry_and_range {M : Type*} [MetricSpace M] (p : M) :
    Isometry (completionToHull p) ∧
    Set.range (completionToHull p) = closure (Set.range (hullEmbed M p)) := by
  have hiso : Isometry (completionToHull (M := M) p) :=
    Isometry.of_dist_eq fun x y ↦ Quotient.inductionOn₂ x y fun _ _ ↦ rfl
  refine ⟨hiso, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.1 (completionEmbed_denseRange M x) ε hε
    induction x using Quotient.inductionOn with | _ y =>
    exact ⟨hullEmbed M p a, ⟨a, rfl⟩, ha⟩
  · have hclosed : IsClosed (Set.range (completionToHull p)) :=
      hiso.isUniformInducing.isComplete_range.isClosed
    refine closure_minimal ?_ hclosed
    rintro _ ⟨a, rfl⟩
    exact ⟨completionEmbed M a, rfl⟩

/-- Goldblatt §18.2–18.3 (pp. 234, 236): Isometric bijection between the nonstandard completion
`MetricCompletion M` (`*M_ap / ≈ₘ`) and Mathlib's `UniformSpace.Completion M`, fixing `M`. -/
def metricCompletionEquiv (M : Type*) [MetricSpace M] :
    MetricCompletion M ≃ᵢ UniformSpace.Completion M := by
  let φ : UniformSpace.Completion M → MetricCompletion M :=
    UniformSpace.Completion.extension (completionEmbed M)
  have hφ_iso : Isometry φ := (completionEmbed_isometry M).completion_extension
  have hφ_surj : Function.Surjective φ := by
    rw [← Set.range_eq_univ, ← Set.univ_subset_iff, ← (completionEmbed_denseRange M).closure_eq]
    have hclosed : IsClosed (Set.range φ) := hφ_iso.isUniformInducing.isComplete_range.isClosed
    refine closure_minimal ?_ hclosed
    rintro _ ⟨a, rfl⟩
    exact ⟨(a : UniformSpace.Completion M),
      UniformSpace.Completion.extension_coe (completionEmbed_isometry M).uniformContinuous a⟩
  exact ({ toEquiv := Equiv.ofBijective φ ⟨hφ_iso.injective, hφ_surj⟩
           isometry_toFun := hφ_iso } : UniformSpace.Completion M ≃ᵢ MetricCompletion M).symm

/-- `metricCompletionEquiv M` maps `completionEmbed M a` to `(a : UniformSpace.Completion M)`. -/
@[simp]
theorem metricCompletionEquiv_embed {M : Type*} [MetricSpace M] (a : M) :
    metricCompletionEquiv M (completionEmbed M a) = (a : UniformSpace.Completion M) := by
  apply (metricCompletionEquiv M).symm.injective
  rw [IsometryEquiv.symm_apply_apply]
  exact (UniformSpace.Completion.extension_coe
    (completionEmbed_isometry M).uniformContinuous a).symm

/-- Goldblatt §18.3 (p. 236): A point `x ∈ *M` is **near to `M`** (**nearstandard**) if it is
infinitely close to some standard point `a ∈ M` (`∃ a : M, x ≈ₘ Germ.const a`). -/
def IsNearstandard {M : Type*} [MetricSpace M] (x : StarMetric M) : Prop :=
  ∃ a : M, MetricInfClose x (Germ.const a)

/-- Goldblatt §18.3 (p. 236): Set of nearstandard points in `*M`. -/
def Nearstandard (M : Type*) [MetricSpace M] : Set (StarMetric M) :=
  {x : StarMetric M | IsNearstandard x}

/-- Every nearstandard point is approachable (`Nearstandard M ⊆ PreNearstandard M`,
Goldblatt §18.3, p. 236). -/
theorem nearstandard_subset_preNearstandard (M : Type*) [MetricSpace M] :
    Nearstandard M ⊆ PreNearstandard M := by
  rintro x ⟨a, ha⟩
  exact mem_preNearstandard_of_infClose (const_mem_preNearstandard a) ha.symm

/-- Goldblatt Corollary 18.3.3 (p. 237): If every point in `*M` approachable from `M` is near to
`M`, then `(M, d)` is a complete metric space. -/
theorem completeSpace_of_preNearstandard_subset_nearstandard {M : Type*} [MetricSpace M]
    (h : PreNearstandard M ⊆ Nearstandard M) :
    CompleteSpace M := by
  have hsurj : Function.Surjective (completionEmbed M) := by
    intro y
    induction y using Quotient.inductionOn with | _ x =>
    obtain ⟨a, ha⟩ := h x.2
    exact ⟨a, Quotient.sound ha.symm⟩
  let e : M ≃ᵢ MetricCompletion M :=
    { toEquiv := Equiv.ofBijective (completionEmbed M)
        ⟨(completionEmbed_isometry M).injective, hsurj⟩
      isometry_toFun := completionEmbed_isometry M }
  exact e.completeSpace_iff.2 inferInstance

/-- Goldblatt Exercise 18.3.4 (p. 237): Conversely to Corollary 18.3.3, if `(M, d)` is a complete
metric space, then every point in `*M` approachable from `M` is near to `M`. -/
theorem preNearstandard_subset_nearstandard_of_completeSpace {M : Type*} [MetricSpace M]
    [CompleteSpace M] :
    PreNearstandard M ⊆ Nearstandard M := by
  intro x hx
  choose a ha using fun n : ℕ ↦ hx (1 / ((n + 1 : ℕ) : ℝ)) (by positivity)
  have hcauchy : CauchySeq a := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hε)
    refine ⟨N, fun m hm k hk ↦ ?_⟩
    have hm_lt : starDist x (Germ.const (a m)) < ((ε / 2 : ℝ) : ℝ*) := by
      refine (ha m).trans_le (Hyperreal.coe_le_coe.2 ?_)
      have hle1 : 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 / ((N + 1 : ℕ) : ℝ) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hm)
      exact hle1.trans (by push_cast; exact hN.le)
    have hk_lt : starDist x (Germ.const (a k)) < ((ε / 2 : ℝ) : ℝ*) := by
      refine (ha k).trans_le (Hyperreal.coe_le_coe.2 ?_)
      have hle1 : 1 / ((k + 1 : ℕ) : ℝ) ≤ 1 / ((N + 1 : ℕ) : ℝ) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hk)
      exact hle1.trans (by push_cast; exact hN.le)
    have htri : ((dist (a m) (a k) : ℝ) : ℝ*) < (ε : ℝ*) := by
      rw [← starDist_const, starDist_comm (Germ.const (a m))]
      have hsum : ((ε / 2 : ℝ) : ℝ*) + ((ε / 2 : ℝ) : ℝ*) = (ε : ℝ*) := by
        rw [← Hyperreal.coe_add, add_halves]
      calc starDist (Germ.const (a k)) (Germ.const (a m))
          ≤ starDist (Germ.const (a k)) x + starDist x (Germ.const (a m)) :=
            starDist_triangle _ _ _
        _ < ((ε / 2 : ℝ) : ℝ*) + ((ε / 2 : ℝ) : ℝ*) := by
            rw [starDist_comm (Germ.const (a k))]
            exact add_lt_add hk_lt hm_lt
        _ = (ε : ℝ*) := hsum
    exact Hyperreal.coe_lt_coe.1 htri
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, fun ε hε ↦ ?_⟩
  rw [abs_of_nonneg (starDist_nonneg x (Germ.const L))]
  obtain ⟨N₁, hN₁⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hL (ε / 2) (half_pos hε)
  let n := max N₁ N₂
  have h1 : starDist x (Germ.const (a n)) < ((ε / 2 : ℝ) : ℝ*) := by
    refine (ha n).trans (Hyperreal.coe_lt_coe.2 ?_)
    have hle : 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 / ((N₁ + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ (le_max_left _ _))
    exact hle.trans_lt (by simpa [one_div] using hN₁)
  have h2 : starDist (Germ.const (a n)) (Germ.const L) < ((ε / 2 : ℝ) : ℝ*) :=
    Hyperreal.coe_lt_coe.2 (hN₂ n (le_max_right _ _))
  have hsum : ((ε / 2 : ℝ) : ℝ*) + ((ε / 2 : ℝ) : ℝ*) = (ε : ℝ*) := by
    rw [← Hyperreal.coe_add, add_halves]
  exact (starDist_triangle x (Germ.const (a n)) (Germ.const L)).trans_lt
    ((add_lt_add h1 h2).trans_eq hsum)

/-- Full nonstandard characterization of metric completeness combining Corollary 18.3.3 and
Exercise 18.3.4 (Goldblatt p. 237): `(M, d)` is complete iff `PreNearstandard M = Nearstandard M`. -/
theorem completeSpace_iff_preNearstandard_eq_nearstandard (M : Type*) [MetricSpace M] :
    CompleteSpace M ↔ PreNearstandard M = Nearstandard M :=
  ⟨fun _ ↦ Set.Subset.antisymm preNearstandard_subset_nearstandard_of_completeSpace
      (nearstandard_subset_preNearstandard M),
   fun h ↦ completeSpace_of_preNearstandard_subset_nearstandard h.subset⟩

/-- Nonstandard characterization of total boundedness: `(M, d)` is totally bounded iff every point
of `StarMetric M` is pre-nearstandard (`PreNearstandard M = Set.univ`). -/
theorem totallyBounded_univ_iff_preNearstandard_eq_univ (M : Type*) [MetricSpace M] :
    TotallyBounded (Set.univ : Set M) ↔ PreNearstandard M = Set.univ := by
  constructor
  · intro htb
    ext x
    simp only [Set.mem_univ, iff_true]
    induction x using Germ.inductionOn with | _ s =>
    intro ε hε
    obtain ⟨t, ht_fin, ht_cov⟩ := Metric.totallyBounded_iff.1 htb ε hε
    have huniv : (⋃ a ∈ t, {i : ℕ | dist (s i) a < ε}) ∈ (hyperfilter ℕ : Filter ℕ) := by
      refine mem_of_superset univ_mem fun i _ ↦ ?_
      obtain ⟨a, hat, hai⟩ := Set.mem_iUnion₂.1 (ht_cov (Set.mem_univ (s i)))
      exact Set.mem_biUnion hat (by simpa [Metric.mem_ball] using hai)
    rw [Ultrafilter.mem_coe, Ultrafilter.finite_biUnion_mem_iff ht_fin] at huniv
    obtain ⟨a, _, ha_ev⟩ := huniv
    exact ⟨a, ofSeq_lt_ofSeq.2 ha_ev⟩
  · intro hall
    by_cases hne : Nonempty M
    · obtain ⟨m₀⟩ := hne
      rw [Metric.totallyBounded_iff]
      intro ε hε
      by_contra hno
      push Not at hno
      have hstep : ∀ (t : Finset M), ∃ y : M, ∀ a ∈ t, ε ≤ dist y a := by
        intro t
        by_contra hall_lt
        push Not at hall_lt
        refine hno (t : Set M) t.finite_toSet (fun y _ ↦ ?_)
        obtain ⟨a, hat, hay⟩ := hall_lt y
        exact Set.mem_biUnion hat (by simpa [Metric.mem_ball] using hay)
      -- Construct an `ε`-separated sequence `s : ℕ → M` by strong recursion
      let s : ℕ → M := WellFounded.fix wellFounded_lt fun n rec ↦
        (hstep ((Finset.range n).attach.image fun k ↦ rec k.1 (Finset.mem_range.1 k.2))).choose
      have hs_sep : ∀ n k : ℕ, k < n → ε ≤ dist (s n) (s k) := by
        intro n k hkn
        have hfix : s n = (hstep ((Finset.range n).attach.image
            fun j ↦ s j.1)).choose := by
          dsimp only [s]
          rw [WellFounded.fix_eq]
        have hspec := (hstep ((Finset.range n).attach.image fun j ↦ s j.1)).choose_spec
        rw [hfix]
        exact hspec (s k) (Finset.mem_image.2
          ⟨⟨k, Finset.mem_range.2 hkn⟩, Finset.mem_attach _ _, rfl⟩)
      have hs_pre : (s : StarMetric M) ∈ PreNearstandard M := hall ▸ Set.mem_univ _
      obtain ⟨a, ha⟩ := hs_pre (ε / 2) (half_pos hε)
      have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), dist (s i) a < ε / 2 :=
        ofSeq_lt_ofSeq.1 ha
      have hsub : {i : ℕ | dist (s i) a < ε / 2}.Subsingleton := by
        intro i hi j hj
        by_contra hij
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · have hsep := hs_sep j i hlt
          have htri := dist_triangle (s j) a (s i)
          rw [dist_comm a (s i)] at htri
          change dist (s i) a < ε / 2 at hi
          change dist (s j) a < ε / 2 at hj
          linarith
        · have hsep := hs_sep i j hgt
          have htri := dist_triangle (s i) a (s j)
          rw [dist_comm a (s j)] at htri
          change dist (s i) a < ε / 2 at hi
          change dist (s j) a < ε / 2 at hj
          linarith
      have hcof : {i : ℕ | dist (s i) a < ε / 2}ᶜ ∈ (hyperfilter ℕ : Filter ℕ) :=
        Filter.hyperfilter_le_cofinite hsub.finite.compl_mem_cofinite
      have hemp : (∅ : Set ℕ) ∈ (hyperfilter ℕ : Filter ℕ) := by
        simpa using inter_mem hev hcof
      exact (Ultrafilter.neBot (hyperfilter ℕ)).ne (empty_mem_iff_bot.1 hemp)
    · rw [not_nonempty_iff] at hne
      have : (Set.univ : Set M) = ∅ := Set.eq_empty_of_isEmpty _
      rw [this]
      exact totallyBounded_empty

/-- Goldblatt §18.3 (p. 237): For `(ℚ, dist)`, every limited point of `*ℚ` is approachable from `ℚ`
(`LimitedMetric ℚ 0 = PreNearstandard ℚ`), so the full nonstandard hull of `ℚ` equals its
completion `ℝ`! -/
theorem limitedMetric_rat_eq_preNearstandard :
    LimitedMetric ℚ 0 = PreNearstandard ℚ := by
  refine Set.Subset.antisymm ?_ (preNearstandard_subset_limitedMetric 0)
  intro q hq ε hε
  have hq_lim : IsLimited (Hyperrat.toHyperreal q) := by
    induction q using Germ.inductionOn with | _ u =>
    have hdist : starDist (u : StarMetric ℚ) (Germ.const (0 : ℚ)) =
        |Hyperrat.toHyperreal (u : ℚ*)| := by
      refine Germ.coe_eq.2 (Eventually.of_forall fun i ↦ ?_)
      change dist (u i) 0 = max (u i : ℝ) (-(u i : ℝ))
      rw [Rat.dist_eq, Rat.cast_zero, sub_zero, abs_eq_max_neg]
    exact isLimited_of_abs_le hq (by rw [hdist, abs_of_nonneg (abs_nonneg _)])
  set r := shadow (Hyperrat.toHyperreal q)
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (sub_lt_self r (half_pos hε))
  have hclose := infClose_shadow hq_lim (ε / 2) (half_pos hε)
  refine ⟨a, ?_⟩
  have hdist_eq : starDist q (Germ.const a) = |Hyperrat.toHyperreal q - ((a : ℝ) : ℝ*)| := by
    induction q using Germ.inductionOn with | _ u =>
    refine Germ.coe_eq.2 (Eventually.of_forall fun i ↦ ?_)
    change dist (u i) a = max ((u i : ℝ) - (a : ℝ)) (-((u i : ℝ) - (a : ℝ)))
    rw [Rat.dist_eq, abs_eq_max_neg]
  rw [hdist_eq]
  have hra : |(r : ℝ*) - ((a : ℝ) : ℝ*)| < ((ε / 2 : ℝ) : ℝ*) := by
    rw [← Hyperreal.coe_sub, ← Hyperreal.coe_abs, Hyperreal.coe_lt_coe, abs_lt]
    exact ⟨by linarith, by linarith⟩
  have hsum : ((ε / 2 : ℝ) : ℝ*) + ((ε / 2 : ℝ) : ℝ*) = (ε : ℝ*) := by
    rw [← Hyperreal.coe_add, add_halves]
  have htri : |Hyperrat.toHyperreal q - ((a : ℝ) : ℝ*)| ≤
      |Hyperrat.toHyperreal q - (r : ℝ*)| + |(r : ℝ*) - ((a : ℝ) : ℝ*)| := by
    have : Hyperrat.toHyperreal q - ((a : ℝ) : ℝ*) =
        (Hyperrat.toHyperreal q - (r : ℝ*)) + ((r : ℝ*) - ((a : ℝ) : ℝ*)) := by ring
    rw [this]
    exact abs_add_le _ _
  exact htri.trans_lt ((add_lt_add hclose hra).trans_eq hsum)

/-! ## §18.3 (Part 2) Nonstandard Hulls of Normed Vector Spaces -/

/-- Ultrapower `*E = Germ (hyperfilter ℕ) E` of a normed vector space `E` (Goldblatt §18.3). -/
abbrev StarVec (E : Type*) : Type _ :=
  Germ (hyperfilter ℕ : Filter ℕ) E

/-- Scalar multiplication of `ℝ` on `StarVec E` (`c • [v_n] = [c • v_n]`). -/
instance instSMulRealStarVec (E : Type*) [SMul ℝ E] : SMul ℝ (StarVec E) where
  smul c v := Germ.map (c • ·) v

/-- `Module ℝ (StarVec E)` structure lifted componentwise from `Module ℝ E`. -/
instance instModuleRealStarVec (E : Type*) [AddCommGroup E] [Module ℝ E] :
    Module ℝ (StarVec E) where
  one_smul v := Germ.inductionOn v fun u ↦ Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ one_smul ℝ (u i)
  mul_smul a b v := Germ.inductionOn v fun u ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ mul_smul a b (u i)
  smul_zero a := Germ.coe_eq.2 <| Eventually.of_forall fun _ ↦ smul_zero a
  smul_add a v w := Germ.inductionOn₂ v w fun u₁ u₂ ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ smul_add a (u₁ i) (u₂ i)
  add_smul a b v := Germ.inductionOn v fun u ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ add_smul a b (u i)
  zero_smul v := Germ.inductionOn v fun u ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ zero_smul ℝ (u i)

/-- Hyperreal-valued norm `starNorm : *E → ℝ*` lifted from `‖·‖ : E → ℝ` (Goldblatt §18.2–18.3). -/
def starNorm {E : Type*} [Norm E] (v : StarVec E) : ℝ* :=
  Germ.map norm v

/-- Standard norm preservation: `starNorm (const e) = (‖e‖ : ℝ*)`. -/
@[simp]
theorem starNorm_const {E : Type*} [Norm E] (e : E) :
    starNorm (Germ.const e : StarVec E) = (‖e‖ : ℝ*) :=
  rfl

/-- `starNorm 0 = 0`. -/
@[simp]
theorem starNorm_zero {E : Type*} [SeminormedAddCommGroup E] :
    starNorm (0 : StarVec E) = 0 :=
  Germ.coe_eq.2 <| Eventually.of_forall fun _ ↦ norm_zero

/-- Nonnegativity `0 ≤ starNorm v`. -/
theorem starNorm_nonneg {E : Type*} [SeminormedAddCommGroup E] (v : StarVec E) :
    0 ≤ starNorm v :=
  Germ.inductionOn v fun u ↦ ofSeq_le_ofSeq.2 <| Eventually.of_forall fun i ↦ norm_nonneg (u i)

/-- Symmetry `starNorm (-v) = starNorm v`. -/
@[simp]
theorem starNorm_neg {E : Type*} [SeminormedAddCommGroup E] (v : StarVec E) :
    starNorm (-v) = starNorm v :=
  Germ.inductionOn v fun u ↦ Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ norm_neg (u i)

/-- Subadditivity `starNorm (v + w) ≤ starNorm v + starNorm w`. -/
theorem starNorm_add_le {E : Type*} [SeminormedAddCommGroup E] (v w : StarVec E) :
    starNorm (v + w) ≤ starNorm v + starNorm w :=
  Germ.inductionOn₂ v w fun u₁ u₂ ↦
    ofSeq_le_ofSeq.2 <| Eventually.of_forall fun i ↦ norm_add_le (u₁ i) (u₂ i)

/-- Homogeneity `starNorm (c • v) = ((|c| : ℝ) : ℝ*) * starNorm v` for `c ∈ ℝ`. -/
theorem starNorm_smul {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (v : StarVec E) :
    starNorm (c • v) = ((|c| : ℝ) : ℝ*) * starNorm v :=
  Germ.inductionOn v fun u ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ by
      change ‖c • u i‖ = |c| * ‖u i‖
      rw [norm_smul, Real.norm_eq_abs]

/-- Identification `starDist v w = starNorm (v - w)` on `StarVec E`. -/
theorem starDist_eq_starNorm_sub {E : Type*} [SeminormedAddCommGroup E] (v w : StarVec E) :
    starDist v w = starNorm (v - w) :=
  Germ.inductionOn₂ v w fun u₁ u₂ ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ dist_eq_norm (u₁ i) (u₂ i)

/-- Distance to `0` equals `starNorm` on `StarVec E`. -/
theorem starDist_zero_right {E : Type*} [SeminormedAddCommGroup E] (v : StarVec E) :
    starDist v (Germ.const (0 : E)) = starNorm v := by
  rw [starDist_eq_starNorm_sub]
  have h0 : (Germ.const (0 : E) : StarVec E) = 0 := rfl
  rw [h0, sub_zero]

/-- `ℝ`-submodule `LimitedVec E` of limited vectors `{v ∈ *E | IsLimited (starNorm v)}`
(Goldblatt §18.3). -/
def LimitedVec (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Submodule ℝ (StarVec E) where
  carrier := {v : StarVec E | IsLimited (starNorm v)}
  add_mem' {v w} hv hw :=
    isLimited_of_abs_le (hv.add hw)
      (by rw [abs_of_nonneg (starNorm_nonneg _),
              abs_of_nonneg (add_nonneg (starNorm_nonneg _) (starNorm_nonneg _))]
          exact starNorm_add_le v w)
  zero_mem' := by simpa using isLimited_coe 0
  smul_mem' c v hv := by
    change IsLimited (starNorm (c • v))
    rw [starNorm_smul]
    exact (isLimited_coe |c|).mul hv

/-- Membership in `LimitedVec E`. -/
@[simp]
theorem mem_limitedVec_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : StarVec E} :
    v ∈ LimitedVec E ↔ IsLimited (starNorm v) :=
  Iff.rfl

/-- `ℝ`-submodule `InfinitesimalVec E` of infinitesimal vectors `{v ∈ LimitedVec E | starNorm v ≈ 0}`
inside `LimitedVec E` (Goldblatt §18.3). -/
def InfinitesimalVec (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Submodule ℝ (LimitedVec E) where
  carrier := {v : LimitedVec E | IsInfinitesimal (starNorm v.1)}
  add_mem' {v w} hv hw :=
    isInfinitesimal_of_abs_le (hv.add hw)
      (by rw [abs_of_nonneg (starNorm_nonneg _),
              abs_of_nonneg (add_nonneg (starNorm_nonneg _) (starNorm_nonneg _))]
          exact starNorm_add_le v.1 w.1)
  zero_mem' := by simpa using isInfinitesimal_zero
  smul_mem' c v hv := by
    change IsInfinitesimal (starNorm (c • v.1))
    rw [starNorm_smul]
    exact (isLimited_coe |c|).mul_isInfinitesimal hv

/-- Membership in `InfinitesimalVec E`. -/
@[simp]
theorem mem_infinitesimalVec_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : LimitedVec E} :
    v ∈ InfinitesimalVec E ↔ IsInfinitesimal (starNorm v.1) :=
  Iff.rfl

/-- The **Banach Nonstandard Hull** `NormedHull E = LimitedVec E ⧸ InfinitesimalVec E`
(Goldblatt §18.3). -/
abbrev NormedHull (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Type _ :=
  LimitedVec E ⧸ InfinitesimalVec E

/-- Norm `‖[v]‖ = shadow (starNorm v)` on `NormedHull E`. -/
instance instNormNormedHull (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Norm (NormedHull E) where
  norm := Quotient.lift (fun v : LimitedVec E ↦ shadow (starNorm v.1)) fun a b hab ↦ by
    have hsub : IsInfinitesimal (starNorm (a.1 - b.1)) :=
      mem_infinitesimalVec_iff.1 ((Submodule.quotientRel_def _).1 hab)
    have hclose : MetricInfClose a.1 b.1 := by
      unfold MetricInfClose
      rwa [starDist_eq_starNorm_sub]
    rw [← starDist_zero_right a.1, ← starDist_zero_right b.1]
    exact shadow_starDist_congr ((starDist_zero_right a.1).symm ▸ a.2) hclose (MetricInfClose.refl _)

/-- Unfolding `‖[v]‖ = shadow (starNorm v.1)` on `NormedHull E`. -/
@[simp]
theorem norm_normedHull_mk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : LimitedVec E) :
    ‖(Submodule.Quotient.mk v : NormedHull E)‖ = shadow (starNorm v.1) :=
  rfl

/-- `NormedSpace.Core ℝ (NormedHull E)` verifying all Banach norm axioms on `NormedHull E`. -/
theorem normedHullCore (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace.Core ℝ (NormedHull E) where
  norm_nonneg x := Quotient.inductionOn x fun v ↦
    coe_le_of_infClose_le (InfClose.refl 0) (starNorm_nonneg v.1) (infClose_shadow v.2)
  norm_smul c x := Quotient.inductionOn x fun v ↦ by
    change shadow (starNorm (c • v.1)) = ‖c‖ * shadow (starNorm v.1)
    rw [starNorm_smul, shadow_mul (isLimited_coe |c|) v.2, shadow_coe, Real.norm_eq_abs]
  norm_triangle x y := Quotient.inductionOn₂ x y fun v w ↦ by
    change shadow (starNorm (v.1 + w.1)) ≤ shadow (starNorm v.1) + shadow (starNorm w.1)
    rw [← shadow_add v.2 w.2]
    exact shadow_le_of_le (v + w).2 (v.2.add w.2) (starNorm_add_le v.1 w.1)
  norm_eq_zero_iff x := Quotient.inductionOn x fun v ↦ by
    change shadow (starNorm v.1) = 0 ↔
      (Submodule.Quotient.mk v : NormedHull E) = 0
    rw [shadow_eq_zero_iff_isInfinitesimal v.2, Submodule.Quotient.mk_eq_zero,
      mem_infinitesimalVec_iff]

/-- `NormedAddCommGroup` structure on `NormedHull E`. -/
instance instNormedAddCommGroupNormedHull (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (NormedHull E) :=
  NormedAddCommGroup.ofCore (normedHullCore E)

/-- `NormedSpace ℝ` structure on `NormedHull E`. -/
instance instNormedSpaceNormedHull (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (NormedHull E) :=
  NormedSpace.ofCore (normedHullCore E)

/-- Canonical linear isometric embedding `normedHullEmbed E : E →ₗᵢ[ℝ] NormedHull E`. -/
def normedHullEmbed (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    E →ₗᵢ[ℝ] NormedHull E where
  toFun e := Submodule.Quotient.mk ⟨Germ.const e, isLimited_coe ‖e‖⟩
  map_add' a b := by
    apply (Submodule.Quotient.eq (InfinitesimalVec E)).2
    rw [mem_infinitesimalVec_iff]
    have h0 : (Germ.const a : StarVec E) + Germ.const b - Germ.const (a + b) = 0 :=
      Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ sub_self (a + b))
    change IsInfinitesimal (starNorm ((Germ.const a : StarVec E) + Germ.const b - Germ.const (a + b)))
    rw [h0, starNorm_zero]
    exact isInfinitesimal_zero
  map_smul' c a := by
    apply (Submodule.Quotient.eq (InfinitesimalVec E)).2
    rw [mem_infinitesimalVec_iff]
    have h0 : c • (Germ.const a : StarVec E) - Germ.const (c • a) = 0 :=
      Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ sub_self (c • a))
    change IsInfinitesimal (starNorm (c • (Germ.const a : StarVec E) - Germ.const (c • a)))
    rw [h0, starNorm_zero]
    exact isInfinitesimal_zero
  norm_map' a := by
    change shadow (starNorm (Germ.const a : StarVec E)) = ‖a‖
    simp

/-- Canonical isometric equivalence `NormedHull E ≃ᵢ MetricHull E 0` identifying the Banach
nonstandard hull with the metric nonstandard hull at `0`. -/
def normedHullEquivMetricHull (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedHull E ≃ᵢ MetricHull E (0 : E) where
  toFun := Quotient.lift
    (fun v : LimitedVec E ↦ Quotient.mk (limitedMetricSetoid E 0)
      ⟨v.1, by
        change IsLimited (starDist v.1 (Germ.const 0))
        rw [starDist_zero_right]
        exact mem_limitedVec_iff.1 v.2⟩)
    (fun a b hab ↦ by
      apply Quotient.sound
      have hm : IsInfinitesimal (starNorm (a.1 - b.1)) :=
        mem_infinitesimalVec_iff.1 ((Submodule.quotientRel_def _).1 hab)
      change IsInfinitesimal (starDist a.1 b.1)
      rwa [starDist_eq_starNorm_sub])
  invFun := Quotient.lift
    (fun x : LimitedMetric E 0 ↦
      (Submodule.Quotient.mk ⟨x.1, by
        have hx : IsLimited (starDist x.1 (Germ.const 0)) := x.2
        rw [starDist_zero_right] at hx
        exact mem_limitedVec_iff.2 hx⟩ : NormedHull E))
    (fun a b hab ↦ by
      apply (Submodule.Quotient.eq (InfinitesimalVec E)).2
      rw [mem_infinitesimalVec_iff]
      have h : IsInfinitesimal (starDist a.1 b.1) := hab
      rwa [starDist_eq_starNorm_sub] at h)
  left_inv x := Quotient.inductionOn x fun _ ↦ rfl
  right_inv x := Quotient.inductionOn x fun _ ↦ rfl
  isometry_toFun := Isometry.of_dist_eq fun x y ↦ Quotient.inductionOn₂ x y fun a b ↦ by
    change shadow (starDist a.1 b.1) =
      dist (Submodule.Quotient.mk a : NormedHull E) (Submodule.Quotient.mk b : NormedHull E)
    rw [dist_eq_norm, starDist_eq_starNorm_sub]
    rfl

/-- **Banach Completeness of `NormedHull E`**: `NormedHull E` is a complete normed space (Banach
space) for every real normed space `E` (Goldblatt §18.3, Theorem 18.3.1). -/
instance instCompleteSpaceNormedHull (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    CompleteSpace (NormedHull E) :=
  (normedHullEquivMetricHull E).completeSpace_iff.2 inferInstance

/-- `ℝ`-submodule `PreNearstandardVec E` of pre-nearstandard (approachable) vectors inside
`LimitedVec E` (Goldblatt §18.3). -/
def PreNearstandardVec (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Submodule ℝ (LimitedVec E) where
  carrier := {v : LimitedVec E | v.1 ∈ PreNearstandard E}
  add_mem' {v w} hv hw ε hε := by
    obtain ⟨a, ha⟩ := hv (ε / 2) (half_pos hε)
    obtain ⟨b, hb⟩ := hw (ε / 2) (half_pos hε)
    refine ⟨a + b, ?_⟩
    rw [starDist_eq_starNorm_sub] at ha hb ⊢
    change starNorm ((v.1 + w.1) - Germ.const (a + b)) < (ε : ℝ*)
    have hconst : (Germ.const (a + b) : StarVec E) = Germ.const a + Germ.const b := rfl
    have hsum_vec : (v.1 + w.1) - (Germ.const (a + b) : StarVec E) =
        (v.1 - Germ.const a) + (w.1 - Germ.const b) := by
      rw [hconst, add_sub_add_comm]
    rw [hsum_vec]
    have hsum_eps : ((ε / 2 : ℝ) : ℝ*) + ((ε / 2 : ℝ) : ℝ*) = (ε : ℝ*) := by
      rw [← Hyperreal.coe_add, add_halves]
    exact (starNorm_add_le _ _).trans_lt ((add_lt_add ha hb).trans_eq hsum_eps)
  zero_mem' := const_mem_preNearstandard 0
  smul_mem' c v hv ε hε := by
    by_cases hc : c = 0
    · subst hc
      refine ⟨0, ?_⟩
      change starDist ((0 : ℝ) • v.1) (Germ.const (0 : E)) < (ε : ℝ*)
      rw [zero_smul, starDist_zero_right, starNorm_zero]
      exact Hyperreal.coe_pos.2 hε
    · have hc_pos : 0 < |c| := abs_pos.2 hc
      obtain ⟨a, ha⟩ := hv (ε / |c|) (div_pos hε hc_pos)
      refine ⟨c • a, ?_⟩
      rw [starDist_eq_starNorm_sub] at ha ⊢
      change starNorm (c • v.1 - Germ.const (c • a)) < (ε : ℝ*)
      have hsmul_vec : c • v.1 - (Germ.const (c • a) : StarVec E) =
          c • (v.1 - Germ.const a) :=
        Germ.inductionOn v.1 fun u ↦
          Germ.coe_eq.2 (Eventually.of_forall fun i ↦ (smul_sub c (u i) a).symm)
      rw [hsmul_vec, starNorm_smul]
      have hprod : ((|c| : ℝ) : ℝ*) * ((ε / |c| : ℝ) : ℝ*) = (ε : ℝ*) := by
        rw [← Hyperreal.coe_mul, mul_div_cancel₀ ε hc_pos.ne']
      exact (mul_lt_mul_of_pos_left ha (Hyperreal.coe_pos.2 hc_pos)).trans_eq hprod

/-- The **Banach Completion** of `E` constructed as the topological closure of `normedHullEmbed E`
inside `NormedHull E` (whose underlying cosets are precisely `PreNearstandardVec E ⧸ InfinitesimalVec E`). -/
def BanachCompletion (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Type _ :=
  (LinearMap.range (normedHullEmbed E).toLinearMap).topologicalClosure

/-- Characterization of `BanachCompletion E` inside `NormedHull E`: a coset `[v] ∈ NormedHull E`
belongs to the closure of `E` iff `v ∈ PreNearstandardVec E`. -/
theorem mem_banachCompletion_iff_preNearstandardVec {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : LimitedVec E) :
    (Submodule.Quotient.mk v : NormedHull E) ∈
      (LinearMap.range (normedHullEmbed E).toLinearMap).topologicalClosure ↔
      v ∈ PreNearstandardVec E := by
  change (Submodule.Quotient.mk v : NormedHull E) ∈
      closure (Set.range (normedHullEmbed E)) ↔ v.1 ∈ PreNearstandard E
  rw [Metric.mem_closure_iff]
  constructor
  · intro hcl ε hε
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hcl (ε / 2) (half_pos hε)
    refine ⟨a, ?_⟩
    rw [dist_eq_norm] at ha
    change shadow (starNorm (v.1 - Germ.const a)) < ε / 2 at ha
    have hlim : IsLimited (starNorm (v.1 - Germ.const a)) :=
      mem_limitedVec_iff.1 ((LimitedVec E).sub_mem v.2 (isLimited_coe ‖a‖))
    have hclose := infClose_shadow hlim (ε / 2) (half_pos hε)
    rw [starDist_eq_starNorm_sub]
    have hlt : starNorm (v.1 - Germ.const a) <
        (shadow (starNorm (v.1 - Germ.const a)) : ℝ*) + ((ε / 2 : ℝ) : ℝ*) := by
      linarith [(abs_lt.1 hclose).2]
    have h2 : shadow (starNorm (v.1 - Germ.const a)) + ε / 2 < ε := by linarith
    exact hlt.trans (by rw [← Hyperreal.coe_add]; exact Hyperreal.coe_lt_coe.2 h2)
  · intro hv ε hε
    obtain ⟨a, ha⟩ := hv (ε / 2) (half_pos hε)
    refine ⟨normedHullEmbed E a, ⟨a, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    change shadow (starNorm (v.1 - Germ.const a)) < ε
    rw [starDist_eq_starNorm_sub] at ha
    have hlim : IsLimited (starNorm (v.1 - Germ.const a)) :=
      mem_limitedVec_iff.1 ((LimitedVec E).sub_mem v.2 (isLimited_coe ‖a‖))
    have hle := shadow_le_of_le hlim (isLimited_coe (ε / 2)) ha.le
    rw [shadow_coe] at hle
    exact hle.trans_lt (half_lt_self hε)

/-- `NormedAddCommGroup` structure on `BanachCompletion E`. -/
instance instNormedAddCommGroupBanachCompletion (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (BanachCompletion E) :=
  inferInstanceAs (NormedAddCommGroup (LinearMap.range (normedHullEmbed E).toLinearMap).topologicalClosure)

/-- `NormedSpace ℝ` structure on `BanachCompletion E`. -/
instance instNormedSpaceBanachCompletion (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (BanachCompletion E) :=
  inferInstanceAs (NormedSpace ℝ (LinearMap.range (normedHullEmbed E).toLinearMap).topologicalClosure)

/-- `BanachCompletion E` is a Banach space (`CompleteSpace`, as a closed subspace of `NormedHull E`). -/
instance instCompleteSpaceBanachCompletion (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    CompleteSpace (BanachCompletion E) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- Linear isometric embedding `banachCompletionEmbed E : E →ₗᵢ[ℝ] BanachCompletion E`. -/
def banachCompletionEmbed (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    E →ₗᵢ[ℝ] BanachCompletion E where
  toFun e := ⟨normedHullEmbed E e, Submodule.le_topologicalClosure _ ⟨e, rfl⟩⟩
  map_add' a b := Subtype.ext ((normedHullEmbed E).map_add a b)
  map_smul' c a := Subtype.ext ((normedHullEmbed E).map_smul c a)
  norm_map' a := (normedHullEmbed E).norm_map a

/-- `banachCompletionEmbed E` has dense range in `BanachCompletion E`. -/
theorem banachCompletionEmbed_denseRange (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    DenseRange (banachCompletionEmbed E) := by
  rw [Metric.denseRange_iff]
  intro ⟨y, hy⟩ ε hε
  obtain ⟨z, ⟨e, rfl⟩, hzy⟩ := Metric.mem_closure_iff.1 hy ε hε
  exact ⟨e, hzy⟩

/-- Linear isometric isomorphism `BanachCompletion E ≃ₗᵢ[ℝ] UniformSpace.Completion E` between the
nonstandard Banach completion inside `NormedHull E` and Mathlib's `UniformSpace.Completion E`. -/
def banachCompletionEquiv (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    BanachCompletion E ≃ₗᵢ[ℝ] UniformSpace.Completion E := by
  let f : E →L[ℝ] BanachCompletion E := (banachCompletionEmbed E).toContinuousLinearMap
  let L : UniformSpace.Completion E →L[ℝ] BanachCompletion E := f.fromCompletion
  have hL_coe : ⇑L = UniformSpace.Completion.extension (banachCompletionEmbed E) :=
    ContinuousLinearMap.coe_fromCompletion f
  have hL_iso : Isometry L := by
    rw [hL_coe]
    exact (banachCompletionEmbed E).isometry.completion_extension
  have hL_surj : Function.Surjective L := by
    rw [← Set.range_eq_univ, ← Set.univ_subset_iff, ← (banachCompletionEmbed_denseRange E).closure_eq]
    have hclosed : IsClosed (Set.range L) := hL_iso.isUniformInducing.isComplete_range.isClosed
    refine closure_minimal ?_ hclosed
    rintro _ ⟨e, rfl⟩
    exact ⟨(e : UniformSpace.Completion E), f.fromCompletion_apply_coe e⟩
  let eqv : UniformSpace.Completion E ≃ₗ[ℝ] BanachCompletion E :=
    LinearEquiv.ofBijective L.toLinearMap ⟨hL_iso.injective, hL_surj⟩
  exact ({ toLinearEquiv := eqv
           norm_map' := fun x ↦ by
             change ‖L x‖ = ‖x‖
             simpa using hL_iso.dist_eq x 0 } :
         UniformSpace.Completion E ≃ₗᵢ[ℝ] BanachCompletion E).symm

/-! ## §18.4 $p$-adic Integers via Hyperintegers -/

/-- Constant embedding `R →+* Germ (hyperfilter ℕ) R` as a ring homomorphism. -/
def germConstRingHom (R : Type*) [Semiring R] :
    R →+* Germ (hyperfilter ℕ : Filter ℕ) R where
  toFun := Germ.const
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Lifted ring homomorphism `Germ (hyperfilter ℕ) R →+* Germ (hyperfilter ℕ) S` induced by
`f : R →+* S` (by transfer). -/
def germMapRingHom {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) :
    Germ (hyperfilter ℕ : Filter ℕ) R →+* Germ (hyperfilter ℕ : Filter ℕ) S where
  toFun := Germ.map f
  map_one' := Germ.coe_eq.2 <| Eventually.of_forall fun _ ↦ f.map_one
  map_mul' a b := Germ.inductionOn₂ a b fun u v ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ f.map_mul (u i) (v i)
  map_zero' := Germ.coe_eq.2 <| Eventually.of_forall fun _ ↦ f.map_zero
  map_add' a b := Germ.inductionOn₂ a b fun u v ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ f.map_add (u i) (v i)

/-- Goldblatt §18.4 (p. 240): For any finite type `R`, `Germ.const : R → Germ (hyperfilter ℕ) R` is
bijective (`*R = R` for finite sets, e.g. `*(ℤ/p^kℤ) ≅ ℤ/p^kℤ`). -/
theorem germConst_bijective_of_finite (R : Type*) [Finite R] :
    Function.Bijective (Germ.const : R → Germ (hyperfilter ℕ : Filter ℕ) R) := by
  refine ⟨fun a b h ↦ ?_, fun x ↦ ?_⟩
  · exact (Germ.coe_eq.1 h).exists.choose_spec
  · induction x using Germ.inductionOn with | _ u =>
    have huniv : (⋃ r ∈ (Set.univ : Set R), {i : ℕ | u i = r}) ∈ (hyperfilter ℕ : Filter ℕ) :=
      mem_of_superset univ_mem fun i _ ↦ Set.mem_biUnion (Set.mem_univ (u i)) rfl
    rw [Ultrafilter.mem_coe, Ultrafilter.finite_biUnion_mem_iff Set.finite_univ] at huniv
    obtain ⟨r, _, hr⟩ := huniv
    exact ⟨r, (Germ.coe_eq.2 hr).symm⟩

/-- Ring isomorphism `Germ (hyperfilter ℕ) R ≃+* R` for any finite commutative ring `R`
(Goldblatt §18.4, p. 240). -/
noncomputable def germFiniteRingEquiv (R : Type*) [CommRing R] [Finite R] :
    Germ (hyperfilter ℕ : Filter ℕ) R ≃+* R :=
  (RingEquiv.ofBijective (germConstRingHom R) (germConst_bijective_of_finite R)).symm

/-- `germFiniteRingEquiv R` maps `Germ.const r` to `r`. -/
@[simp]
theorem germFiniteRingEquiv_const {R : Type*} [CommRing R] [Finite R] (r : R) :
    germFiniteRingEquiv R (Germ.const r) = r :=
  (RingEquiv.ofBijective (germConstRingHom R) (germConst_bijective_of_finite R)).symm_apply_apply r

/-- Inverse of `germFiniteRingEquiv R` is `Germ.const`. -/
@[simp]
theorem germFiniteRingEquiv_symm_apply {R : Type*} [CommRing R] [Finite R] (r : R) :
    (germFiniteRingEquiv R).symm r = Germ.const r :=
  rfl

/-- Goldblatt §18.4 (p. 240): Lifted residue ring homomorphism `ℤ* →+* ZMod m` for positive `m`
(`*(ℤ → ℤ/mℤ) : *ℤ → ℤ/mℤ`). -/
noncomputable def hyperZModHom (m : ℕ) [NeZero m] : ℤ* →+* ZMod m :=
  (germFiniteRingEquiv (ZMod m)).toRingHom.comp (germMapRingHom (Int.castRingHom (ZMod m)))

/-- Coordinatewise characterization of `hyperZModHom m`. -/
theorem hyperZModHom_coe_eq_iff (m : ℕ) [NeZero m] (u : ℕ → ℤ) (r : ZMod m) :
    hyperZModHom m (u : ℤ*) = r ↔
      ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (u i : ZMod m) = r := by
  change germFiniteRingEquiv (ZMod m)
    (((fun i ↦ (u i : ZMod m)) : ℕ → ZMod m) : Germ (hyperfilter ℕ : Filter ℕ) (ZMod m)) = r ↔ _
  rw [← (germFiniteRingEquiv (ZMod m)).symm.injective.eq_iff,
      RingEquiv.symm_apply_apply, germFiniteRingEquiv_symm_apply]
  exact Germ.coe_eq

/-- `hyperZModHom m` agrees with standard reduction modulo `m` on `(z : ℤ*)`. -/
@[simp]
theorem hyperZModHom_intCast (m : ℕ) [NeZero m] (z : ℤ) :
    hyperZModHom m (z : ℤ*) = (z : ZMod m) :=
  (hyperZModHom_coe_eq_iff m (fun _ ↦ z) (z : ZMod m)).2 (Eventually.of_forall fun _ ↦ rfl)

/-- Divisibility of a hyperinteger `[u_i]` by a standard integer `d` is coordinatewise eventual
divisibility. -/
theorem intCast_dvd_hyperint_iff (d : ℤ) (u : ℕ → ℤ) :
    (d : ℤ*) ∣ (u : ℤ*) ↔ ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), d ∣ u i := by
  constructor
  · rintro ⟨q, hq⟩
    induction q using Germ.inductionOn with | _ v =>
    have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), u i = d * v i := Germ.coe_eq.1 hq
    exact hev.mono fun i hi ↦ ⟨v i, hi⟩
  · intro hev
    refine ⟨((fun i ↦ u i / d) : ℤ*), Germ.coe_eq.2 ?_⟩
    exact hev.mono fun i hi ↦ (Int.mul_ediv_cancel' hi).symm

/-- Kernel characterization of `hyperZModHom m`: `hyperZModHom m x = 0 ↔ (m : ℤ*) ∣ x`. -/
theorem hyperZModHom_eq_zero_iff_dvd (m : ℕ) [NeZero m] (x : ℤ*) :
    hyperZModHom m x = 0 ↔ (m : ℤ*) ∣ x := by
  induction x using Germ.inductionOn with | _ u =>
  rw [hyperZModHom_coe_eq_iff]
  have hcast : ((m : ℤ) : ℤ*) = (m : ℤ*) := by push_cast; rfl
  rw [← hcast, intCast_dvd_hyperint_iff]
  exact eventually_congr (Eventually.of_forall fun i ↦ ZMod.intCast_zmod_eq_zero_iff_dvd (u i) m)

/-- Embedding `ℕ* → ℤ*` lifting `Int.ofNat : ℕ → ℤ`. -/
def natToHyperint (n : ℕ*) : ℤ* :=
  Germ.map Int.ofNat n

/-- `natToHyperint` on standard naturals. -/
@[simp]
theorem natToHyperint_natCast (n : ℕ) :
    natToHyperint (n : ℕ*) = (n : ℤ*) :=
  rfl

/-- `natToHyperint` preserves addition. -/
theorem natToHyperint_add (a b : ℕ*) :
    natToHyperint (a + b) = natToHyperint a + natToHyperint b :=
  Germ.inductionOn₂ a b fun _ _ ↦ rfl

/-- `natToHyperint` preserves multiplication. -/
theorem natToHyperint_mul (a b : ℕ*) :
    natToHyperint (a * b) = natToHyperint a * natToHyperint b :=
  Germ.inductionOn₂ a b fun _ _ ↦ rfl

/-- `natToHyperint` preserves strict positivity. -/
theorem natToHyperint_pos {n : ℕ*} (hn : 0 < n) :
    0 < natToHyperint n := by
  induction n using Germ.inductionOn with | _ u =>
  have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 0 < u i := Germ.coe_lt.1 hn
  exact Germ.coe_lt.2 (hev.mono fun i hi ↦ Int.natCast_pos.2 hi)

/-- Hyperfinite power `p ^ N ∈ ℤ*` for `p : ℕ` and `N : ℕ*` (Goldblatt §18.4, p. 239). -/
def hyperintPow (p : ℕ) (N : ℕ*) : ℤ* :=
  Germ.map (fun k : ℕ ↦ (p : ℤ) ^ k) N

/-- Standard power recovery `hyperintPow p (k : ℕ*) = (p : ℤ*) ^ k`. -/
@[simp]
theorem hyperintPow_natCast (p k : ℕ) :
    hyperintPow p (k : ℕ*) = (p : ℤ*) ^ k :=
  Germ.coe_eq.2 <| Eventually.of_forall fun _ ↦ rfl

/-- Monotonicity of divisibility for `hyperintPow`: if `M ≤ N` in `ℕ*`, then
`hyperintPow p M ∣ hyperintPow p N` in `ℤ*`. -/
theorem hyperintPow_dvd_of_le (p : ℕ) {M N : ℕ*} (hMN : M ≤ N) :
    hyperintPow p M ∣ hyperintPow p N := by
  induction M using Germ.inductionOn with | _ u =>
  induction N using Germ.inductionOn with | _ v =>
  have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), u i ≤ v i := Germ.coe_le.1 hMN
  refine ⟨((fun i ↦ (p : ℤ) ^ (v i - u i)) : ℤ*), Germ.coe_eq.2 ?_⟩
  exact hev.mono fun i hi ↦ by
    change (p : ℤ) ^ v i = (p : ℤ) ^ u i * (p : ℤ) ^ (v i - u i)
    rw [← pow_add, Nat.add_sub_of_le hi]

/-- Goldblatt §18.4 (p. 237): Standard $p$-adic order `ord_p : ℤ → WithTop ℕ` mapping `0 ↦ ⊤`
and nonzero `z ↦ padicValInt p z`. -/
def padicOrderZ (p : ℕ) (z : ℤ) : WithTop ℕ :=
  if z = 0 then ⊤ else (padicValInt p z : WithTop ℕ)

/-- Divisibility characterization of `padicOrderZ`: `(k : WithTop ℕ) ≤ padicOrderZ p z ↔ (p : ℤ) ^ k ∣ z`. -/
theorem le_padicOrderZ_iff_dvd (p : ℕ) [Fact p.Prime] (k : ℕ) (z : ℤ) :
    (k : WithTop ℕ) ≤ padicOrderZ p z ↔ (p : ℤ) ^ k ∣ z := by
  unfold padicOrderZ
  by_cases hz : z = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte, Nat.cast_le]
    rw [padicValInt_dvd_iff (p := p) k z]
    simp [hz]

/-- Goldblatt §18.4 (p. 238): Nonstandard $p$-adic order `ord_p : ℤ* → *(ℕ ∪ {∞})` lifted to `ℤ*`. -/
def starPadicOrderZ (p : ℕ) (x : ℤ*) : Germ (hyperfilter ℕ : Filter ℕ) (WithTop ℕ) :=
  Germ.map (padicOrderZ p) x

/-- Goldblatt §18.4 (p. 239): `x ∈ ℤ*` has unlimited $p$-adic order if `n < ord_p(x)` for every
standard `n : ℕ` (either `ord_p(x) ∈ *ℕ_∞` or `ord_p(x) = ∞`, i.e. `x = 0`). -/
def HasUnlimitedPadicOrderZ (p : ℕ) (x : ℤ*) : Prop :=
  ∀ n : ℕ, Germ.const (n : WithTop ℕ) < starPadicOrderZ p x

/-- Goldblatt §18.4 (p. 238): Nonstandard $p$-adic absolute value `|x|_p ∈ ℝ*` on `ℤ*`. -/
noncomputable def starPadicNormZ (p : ℕ) [Fact p.Prime] (x : ℤ*) : ℝ* :=
  Germ.map (fun z : ℤ ↦ ‖(z : ℤ_[p])‖) x

/-- Nonnegativity `0 ≤ starPadicNormZ p x`. -/
theorem starPadicNormZ_nonneg (p : ℕ) [Fact p.Prime] (x : ℤ*) :
    0 ≤ starPadicNormZ p x :=
  Germ.inductionOn x fun u ↦
    ofSeq_le_ofSeq.2 <| Eventually.of_forall fun i ↦ norm_nonneg ((u i : ℤ) : ℤ_[p])

/-- Boundedness `starPadicNormZ p x ≤ 1` for every `x ∈ ℤ*` (Goldblatt §18.4, p. 239:
every hyperinteger is $p$-adically limited!). -/
theorem starPadicNormZ_le_one (p : ℕ) [Fact p.Prime] (x : ℤ*) :
    starPadicNormZ p x ≤ 1 :=
  Germ.inductionOn x fun u ↦
    ofSeq_le_ofSeq.2 <| Eventually.of_forall fun i ↦ PadicInt.norm_le_one ((u i : ℤ) : ℤ_[p])

/-- Every `x ∈ ℤ*` has limited $p$-adic norm (`IsLimited (starPadicNormZ p x)`). -/
theorem starPadicNormZ_isLimited (p : ℕ) [Fact p.Prime] (x : ℤ*) :
    IsLimited (starPadicNormZ p x) :=
  isLimited_of_abs_le (isLimited_coe 1)
    (by rw [abs_of_nonneg (starPadicNormZ_nonneg p x),
            abs_of_pos (Hyperreal.coe_pos.2 one_pos)]
        exact starPadicNormZ_le_one p x)

/-- Strong (ultrametric) triangle inequality on `ℤ*`:
`starPadicNormZ p (x + y) ≤ max (starPadicNormZ p x) (starPadicNormZ p y)`. -/
theorem starPadicNormZ_add_le_max (p : ℕ) [Fact p.Prime] (x y : ℤ*) :
    starPadicNormZ p (x + y) ≤ max (starPadicNormZ p x) (starPadicNormZ p y) :=
  Germ.inductionOn₂ x y fun u v ↦
    ofSeq_le_ofSeq.2 <| Eventually.of_forall fun i ↦ by
      change ‖((u i + v i : ℤ) : ℤ_[p])‖ ≤ max ‖(u i : ℤ_[p])‖ ‖(v i : ℤ_[p])‖
      rw [Int.cast_add]
      exact PadicInt.nonarchimedean (u i : ℤ_[p]) (v i : ℤ_[p])

/-- Multiplicativity `starPadicNormZ p (x * y) = starPadicNormZ p x * starPadicNormZ p y`. -/
theorem starPadicNormZ_mul (p : ℕ) [Fact p.Prime] (x y : ℤ*) :
    starPadicNormZ p (x * y) = starPadicNormZ p x * starPadicNormZ p y :=
  Germ.inductionOn₂ x y fun u v ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ by
      change ‖((u i * v i : ℤ) : ℤ_[p])‖ = ‖(u i : ℤ_[p])‖ * ‖(v i : ℤ_[p])‖
      rw [Int.cast_mul, norm_mul]

/-- Symmetry `starPadicNormZ p (-x) = starPadicNormZ p x`. -/
@[simp]
theorem starPadicNormZ_neg (p : ℕ) [Fact p.Prime] (x : ℤ*) :
    starPadicNormZ p (-x) = starPadicNormZ p x :=
  Germ.inductionOn x fun u ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ by
      change ‖((-u i : ℤ) : ℤ_[p])‖ = ‖(u i : ℤ_[p])‖
      rw [Int.cast_neg, norm_neg]

/-- `starPadicNormZ p 0 = 0`. -/
@[simp]
theorem starPadicNormZ_zero (p : ℕ) [Fact p.Prime] :
    starPadicNormZ p 0 = 0 :=
  Germ.coe_eq.2 <| Eventually.of_forall fun _ ↦ by simp

/-- Divisibility equivalence for `starPadicNormZ p`:
`starPadicNormZ p x ≤ ((p : ℝ) ^ (-k : ℤ) : ℝ*) ↔ (p : ℤ*) ^ k ∣ x`. -/
theorem starPadicNormZ_le_pow_iff_dvd (p : ℕ) [Fact p.Prime] (x : ℤ*) (k : ℕ) :
    starPadicNormZ p x ≤ (((p : ℝ) ^ (-k : ℤ) : ℝ) : ℝ*) ↔ (p : ℤ*) ^ k ∣ x := by
  induction x using Germ.inductionOn with | _ u =>
  have hcast : (((p : ℤ) ^ k : ℤ) : ℤ*) = (p : ℤ*) ^ k := by push_cast; rfl
  rw [← hcast, intCast_dvd_hyperint_iff]
  change ofSeq (fun i ↦ ‖(u i : ℤ_[p])‖) ≤ ofSeq (fun _ ↦ (p : ℝ) ^ (-k : ℤ)) ↔ _
  rw [ofSeq_le_ofSeq]
  exact eventually_congr (Eventually.of_forall fun i ↦ by
    simpa using (PadicInt.norm_int_le_pow_iff_dvd (p := p) (k := u i) (n := k)))

/-- Goldblatt §18.4 (p. 239): `x ∈ ℤ*` is a **$p$-adic infinitesimal** (`x ∈ I_p`) if
`starPadicNormZ p x ≈ 0`. -/
def IsPadicInfinitesimalZ (p : ℕ) [Fact p.Prime] (x : ℤ*) : Prop :=
  IsInfinitesimal (starPadicNormZ p x)

/-- Goldblatt **Theorem 18.4.1** (p. 239): Four-way characterization of $p$-adic infinitesimals
`x ∈ I_p` in `ℤ*`:
1. `IsPadicInfinitesimalZ p x` (`|x|_p ≈ 0`),
2. `HasUnlimitedPadicOrderZ p x` (`ord_p(x)` is unlimited or `∞`),
3. `∀ k : ℕ, (p : ℤ*) ^ k ∣ x` (`p^k` divides `x` in `ℤ*` for every standard `k ∈ ℕ`),
4. `∃ N : ℕ*, IsUnlimitedNat N ∧ hyperintPow p N ∣ x` (`p^N` divides `x` for some unlimited `N ∈ *ℕ_∞`). -/
theorem isPadicInfinitesimalZ_tfae (p : ℕ) [Fact p.Prime] (x : ℤ*) :
    (IsPadicInfinitesimalZ p x ↔ HasUnlimitedPadicOrderZ p x) ∧
    (HasUnlimitedPadicOrderZ p x ↔ ∀ k : ℕ, (p : ℤ*) ^ k ∣ x) ∧
    ((∀ k : ℕ, (p : ℤ*) ^ k ∣ x) ↔ ∃ N : ℕ*, IsUnlimitedNat N ∧ hyperintPow p N ∣ x) := by
  have h13 : IsPadicInfinitesimalZ p x ↔ ∀ k : ℕ, (p : ℤ*) ^ k ∣ x := by
    constructor
    · intro hinf k
      rw [← starPadicNormZ_le_pow_iff_dvd]
      have hpos : (0 : ℝ) < (p : ℝ) ^ (-k : ℤ) :=
        zpow_pos (Nat.cast_pos.2 (Fact.out : p.Prime).pos) _
      have hlt := hinf ((p : ℝ) ^ (-k : ℤ)) hpos
      rw [abs_of_nonneg (starPadicNormZ_nonneg p x)] at hlt
      exact hlt.le
    · intro hdvd ε hε
      rw [abs_of_nonneg (starPadicNormZ_nonneg p x)]
      obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
      exact (starPadicNormZ_le_pow_iff_dvd p x k |>.2 (hdvd k)).trans_lt
        (Hyperreal.coe_lt_coe.2 hk)
  have h23 : HasUnlimitedPadicOrderZ p x ↔ ∀ k : ℕ, (p : ℤ*) ^ k ∣ x := by
    induction x using Germ.inductionOn with | _ u =>
    constructor
    · intro hunl k
      cases k with
      | zero => simp
      | succ n =>
        have hlt : Germ.const (n : WithTop ℕ) < starPadicOrderZ p (u : ℤ*) := hunl n
        have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (n : WithTop ℕ) < padicOrderZ p (u i) :=
          Germ.coe_lt.1 hlt
        have hdvd_ev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (p : ℤ) ^ (n + 1) ∣ u i :=
          hev.mono fun i hi ↦ by
            rw [← le_padicOrderZ_iff_dvd]
            cases hord : padicOrderZ p (u i) with
            | top => exact le_top
            | coe m =>
              rw [hord] at hi
              have hnm : n < m := WithTop.coe_lt_coe.1 hi
              exact WithTop.coe_le_coe.2 (Nat.succ_le_of_lt hnm)
        have hcast : (((p : ℤ) ^ (n + 1) : ℤ) : ℤ*) = (p : ℤ*) ^ (n + 1) := by push_cast; rfl
        rw [← hcast, intCast_dvd_hyperint_iff]
        exact hdvd_ev
    · intro hdvd n
      have hcast : (((p : ℤ) ^ (n + 1) : ℤ) : ℤ*) = (p : ℤ*) ^ (n + 1) := by push_cast; rfl
      have hev := (intCast_dvd_hyperint_iff ((p : ℤ) ^ (n + 1)) u).1 (hcast.symm ▸ hdvd (n + 1))
      refine Germ.coe_lt.2 (hev.mono fun i hi ↦ ?_)
      have hle := (le_padicOrderZ_iff_dvd p (n + 1) (u i)).2 hi
      exact (WithTop.coe_lt_coe.2 (Nat.lt_succ_self n)).trans_le hle
  have h34 : (∀ k : ℕ, (p : ℤ*) ^ k ∣ x) ↔
      ∃ N : ℕ*, IsUnlimitedNat N ∧ hyperintPow p N ∣ x := by
    constructor
    · intro hdvd
      induction x using Germ.inductionOn with | _ u =>
      let Nseq : ℕ → ℕ := fun i ↦ if u i = 0 then i else padicValInt p (u i)
      refine ⟨(Nseq : ℕ*), ?_, ?_⟩
      · intro k
        have hcast : (((p : ℤ) ^ (k + 1) : ℤ) : ℤ*) = (p : ℤ*) ^ (k + 1) := by push_cast; rfl
        have hev_dvd := (intCast_dvd_hyperint_iff ((p : ℤ) ^ (k + 1)) u).1
          (hcast.symm ▸ hdvd (k + 1))
        have hcof_mem : (Set.Iio (k + 1))ᶜ ∈ (hyperfilter ℕ : Filter ℕ) :=
          Filter.hyperfilter_le_cofinite (Set.finite_Iio (k + 1)).compl_mem_cofinite
        have hev_cof : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), k + 1 ≤ i :=
          Filter.Eventually.mono hcof_mem fun _ hi ↦ not_lt.1 hi
        refine Germ.coe_lt.2 ((hev_dvd.and hev_cof).mono fun i ⟨hi_dvd, hi_ge⟩ ↦ ?_)
        change k < Nseq i
        dsimp only [Nseq]
        split_ifs with hz
        · omega
        · have hle : k + 1 ≤ padicValInt p (u i) := by
            rcases (padicValInt_dvd_iff (p := p) (k + 1) (u i)).1 hi_dvd with h0 | hle
            · exact absurd h0 hz
            · exact hle
          omega
      · have hev_all : ∀ i : ℕ, (p : ℤ) ^ Nseq i ∣ u i := fun i ↦ by
          dsimp only [Nseq]
          split_ifs with hz
          · rw [hz]; exact dvd_zero _
          · exact padicValInt_dvd (u i)
        refine ⟨((fun i ↦ u i / (p : ℤ) ^ Nseq i) : ℤ*), Germ.coe_eq.2 ?_⟩
        exact Eventually.of_forall fun i ↦ (Int.mul_ediv_cancel' (hev_all i)).symm
    · rintro ⟨N, hN_unl, hN_dvd⟩ k
      rw [← hyperintPow_natCast]
      exact (hyperintPow_dvd_of_le p (hN_unl k).le).trans hN_dvd
  exact ⟨h13.trans h23.symm, h23, h34⟩

/-- Ideal `padicInfinitesimalIdealZ p` (`I_p`) of $p$-adic infinitesimals in `ℤ*`
(Goldblatt §18.4, pp. 239–240). -/
noncomputable def padicInfinitesimalIdealZ (p : ℕ) [Fact p.Prime] : Ideal ℤ* where
  carrier := {x : ℤ* | IsPadicInfinitesimalZ p x}
  add_mem' {x y} hx hy := by
    change IsPadicInfinitesimalZ p x at hx
    change IsPadicInfinitesimalZ p y at hy
    change IsPadicInfinitesimalZ p (x + y)
    rw [(isPadicInfinitesimalZ_tfae p _).1, (isPadicInfinitesimalZ_tfae p _).2.1] at hx hy ⊢
    exact fun k ↦ dvd_add (hx k) (hy k)
  zero_mem' := by simp [IsPadicInfinitesimalZ, isInfinitesimal_zero]
  smul_mem' c x hx := by
    change IsPadicInfinitesimalZ p x at hx
    change IsPadicInfinitesimalZ p (c * x)
    rw [(isPadicInfinitesimalZ_tfae p _).1, (isPadicInfinitesimalZ_tfae p _).2.1] at hx ⊢
    exact fun k ↦ dvd_mul_of_dvd_right (hx k) c

/-- Membership in `padicInfinitesimalIdealZ p`. -/
@[simp]
theorem mem_padicInfinitesimalIdealZ_iff (p : ℕ) [Fact p.Prime] {x : ℤ*} :
    x ∈ padicInfinitesimalIdealZ p ↔ IsPadicInfinitesimalZ p x :=
  Iff.rfl

/-- `NeZero (p ^ k)` instance helper for prime `p`. -/
theorem neZero_pow_of_prime (p : ℕ) [Fact p.Prime] (k : ℕ) : NeZero (p ^ k) :=
  ⟨pow_ne_zero k (Fact.out : p.Prime).ne_zero⟩

/-- Compatibility of the projective family `k ↦ hyperZModHom (p ^ k) : ℤ* →+* ZMod (p ^ k)`
for `PadicInt.lift` (Goldblatt §18.4, p. 240). -/
theorem hyperZModPow_compat (p : ℕ) [Fact p.Prime] :
    ∀ (k1 k2 : ℕ) (hk : k1 ≤ k2),
      haveI := neZero_pow_of_prime p k1
      haveI := neZero_pow_of_prime p k2
      (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k1))).comp (hyperZModHom (p ^ k2)) =
        hyperZModHom (p ^ k1) := by
  intro k1 k2 hk
  have := neZero_pow_of_prime p k1
  have := neZero_pow_of_prime p k2
  ext x
  induction x using Germ.inductionOn with | _ u =>
  let r : ZMod (p ^ k2) := hyperZModHom (p ^ k2) (u : ℤ*)
  have hr : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (u i : ZMod (p ^ k2)) = r :=
    (hyperZModHom_coe_eq_iff (p ^ k2) u r).1 rfl
  symm
  rw [RingHom.comp_apply, hyperZModHom_coe_eq_iff]
  exact hr.mono fun i hi ↦ by
    change (u i : ZMod (p ^ k1)) = (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k1))) r
    rw [← hi, map_intCast]

/-- Goldblatt §18.4 (p. 240): The canonical surjective ring homomorphism `θ_p : ℤ* →+* ℤ_[p]`
lifting the compatible residue maps `ℤ* →+* ZMod (p ^ k)`. -/
noncomputable def thetaP (p : ℕ) [Fact p.Prime] : ℤ* →+* ℤ_[p] :=
  haveI : ∀ k : ℕ, NeZero (p ^ k) := neZero_pow_of_prime p
  PadicInt.lift (hyperZModPow_compat p)

/-- Projective specification of `thetaP`: `toZModPow k (thetaP p x) = hyperZModHom (p ^ k) x`
(Goldblatt §18.4, p. 240). -/
theorem toZModPow_thetaP (p : ℕ) [Fact p.Prime] (k : ℕ) (x : ℤ*) :
    haveI := neZero_pow_of_prime p k
    PadicInt.toZModPow k (thetaP p x) = hyperZModHom (p ^ k) x := by
  have : ∀ n : ℕ, NeZero (p ^ n) := neZero_pow_of_prime p
  exact RingHom.congr_fun (PadicInt.lift_spec (hyperZModPow_compat p) k) x

/-- `thetaP p` fixes standard integers (`thetaP p (z : ℤ*) = (z : ℤ_[p])`, Goldblatt §18.4, p. 240). -/
@[simp]
theorem thetaP_intCast (p : ℕ) [Fact p.Prime] (z : ℤ) :
    thetaP p (z : ℤ*) = (z : ℤ_[p]) := by
  have : ∀ n : ℕ, NeZero (p ^ n) := neZero_pow_of_prime p
  apply PadicInt.ext_of_toZModPow.1
  intro k
  rw [toZModPow_thetaP, hyperZModHom_intCast, map_intCast]

/-- `thetaP p` fixes standard naturals (`thetaP p (n : ℤ*) = (n : ℤ_[p])`). -/
@[simp]
theorem thetaP_natCast (p : ℕ) [Fact p.Prime] (n : ℕ) :
    thetaP p (n : ℤ*) = (n : ℤ_[p]) := by
  rw [← Int.cast_natCast (R := ℤ*) n, thetaP_intCast, Int.cast_natCast]

/-- Goldblatt §18.4 (p. 240): The kernel of `thetaP p : ℤ* →+* ℤ_[p]` is precisely the ideal `I_p`
of $p$-adic infinitesimals (`RingHom.ker (thetaP p) = padicInfinitesimalIdealZ p`). -/
theorem ker_thetaP (p : ℕ) [Fact p.Prime] :
    RingHom.ker (thetaP p) = padicInfinitesimalIdealZ p := by
  have : ∀ n : ℕ, NeZero (p ^ n) := neZero_pow_of_prime p
  ext x
  rw [RingHom.mem_ker, mem_padicInfinitesimalIdealZ_iff,
      (isPadicInfinitesimalZ_tfae p x).1, (isPadicInfinitesimalZ_tfae p x).2.1,
      ← PadicInt.ext_of_toZModPow]
  refine forall_congr' fun k ↦ ?_
  rw [map_zero, toZModPow_thetaP, hyperZModHom_eq_zero_iff_dvd]
  push_cast
  rfl

/-- Goldblatt §18.4 (p. 240) & §18.7 (p. 253): Every $p$-adic integer `a ∈ ℤ_[p]` is the image
under `thetaP p` of a **strictly positive** hypernatural `z ∈ ℕ*` (`0 < z`). -/
theorem exists_pos_hypernat_thetaP_eq (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) :
    ∃ z : ℕ*, 0 < z ∧ thetaP p (natToHyperint z) = a := by
  have : ∀ n : ℕ, NeZero (p ^ n) := neZero_pow_of_prime p
  let u : ℕ → ℕ := fun k ↦ if a.appr k = 0 then p ^ k else a.appr k
  refine ⟨(u : ℕ*), ?_, ?_⟩
  · refine Germ.coe_lt.2 (Eventually.of_forall fun k ↦ ?_)
    dsimp only [u]
    split_ifs with h0
    · exact pow_pos (Fact.out : p.Prime).pos k
    · exact Nat.pos_of_ne_zero h0
  · apply PadicInt.ext_of_toZModPow.1
    intro n
    rw [toZModPow_thetaP]
    change hyperZModHom (p ^ n) (((fun k ↦ (u k : ℤ)) : ℕ → ℤ) : ℤ*) = PadicInt.toZModPow n a
    rw [hyperZModHom_coe_eq_iff]
    have hcof_mem : (Set.Iio n)ᶜ ∈ (hyperfilter ℕ : Filter ℕ) :=
      Filter.hyperfilter_le_cofinite (Set.finite_Iio n).compl_mem_cofinite
    have hcof : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), n ≤ k :=
      Filter.Eventually.mono hcof_mem fun _ hk ↦ not_lt.1 hk
    refine hcof.mono fun k hnk ↦ ?_
    have happr_span : a - (a.appr k : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
      refine Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (p : ℤ_[p]) hnk) ?_
      exact PadicInt.appr_spec k a
    have happr_mod : PadicInt.toZModPow n (a.appr k : ℤ_[p]) = PadicInt.toZModPow n a := by
      have hker : a - (a.appr k : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow n) := by
        rwa [PadicInt.ker_toZModPow]
      rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hker
      exact hker.symm
    rw [← happr_mod, map_natCast]
    dsimp only [u]
    split_ifs with h0
    · rw [h0, Nat.cast_zero, Int.cast_natCast]
      rw [ZMod.natCast_eq_zero_iff]
      exact pow_dvd_pow p hnk
    · simp

/-- Surjectivity of `thetaP p : ℤ* →+* ℤ_[p]` (Goldblatt §18.4, p. 240). -/
theorem thetaP_surjective (p : ℕ) [Fact p.Prime] :
    Function.Surjective (thetaP p) :=
  fun a ↦ let ⟨z, _, hz⟩ := exists_pos_hypernat_thetaP_eq p a; ⟨natToHyperint z, hz⟩

/-- Goldblatt §18.4 (p. 240): **Fundamental Ring Isomorphism `(ℤ* ⧸ I_p) ≃+* ℤ_[p]`** realizing
the ring of $p$-adic integers as a quotient of the hyperintegers `ℤ*`! -/
noncomputable def hyperintQuotientEquivPadicInt (p : ℕ) [Fact p.Prime] :
    (ℤ* ⧸ padicInfinitesimalIdealZ p) ≃+* ℤ_[p] :=
  (Ideal.quotEquivOfEq (ker_thetaP p).symm).trans
    (RingHom.quotientKerEquivOfSurjective (thetaP_surjective p))

/-- Explicit evaluation of `hyperintQuotientEquivPadicInt p` on a coset `[x]`. -/
@[simp]
theorem hyperintQuotientEquivPadicInt_mk (p : ℕ) [Fact p.Prime] (x : ℤ*) :
    hyperintQuotientEquivPadicInt p (Ideal.Quotient.mk (padicInfinitesimalIdealZ p) x) =
      thetaP p x :=
  rfl

/-- Goldblatt §18.4 (p. 240): `I_p` is a prime ideal of `ℤ*` (since `ℤ* ⧸ I_p ≅ ℤ_[p]` is an
integral domain). -/
instance instIsPrimePadicInfinitesimalIdealZ (p : ℕ) [Fact p.Prime] :
    (padicInfinitesimalIdealZ p).IsPrime := by
  rw [← ker_thetaP]
  exact RingHom.ker_isPrime (thetaP p)

/-- Goldblatt §18.4 (p. 240): `I_p` is **not** a maximal ideal of `ℤ*` (for instance `p ∉ I_p` lies
in the proper ideal `ker(ℤ* → ℤ/pℤ)` strictly containing `I_p`, as `ℤ_[p]` is not a field). -/
theorem not_isMaximal_padicInfinitesimalIdealZ (p : ℕ) [Fact p.Prime] :
    ¬ (padicInfinitesimalIdealZ p).IsMaximal := by
  intro hmax
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let J : Ideal ℤ* := RingHom.ker (hyperZModHom p)
  have hJ_ne_top : J ≠ ⊤ := by
    intro htop
    have h1 : (1 : ℤ*) ∈ J := htop ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hle : padicInfinitesimalIdealZ p ≤ J := fun x hx ↦ by
    have hdvd : (p : ℤ*) ^ 1 ∣ x := by
      rw [mem_padicInfinitesimalIdealZ_iff, (isPadicInfinitesimalZ_tfae p x).1,
          (isPadicInfinitesimalZ_tfae p x).2.1] at hx
      exact hx 1
    rw [pow_one] at hdvd
    exact (hyperZModHom_eq_zero_iff_dvd p x).2 hdvd
  have heq : padicInfinitesimalIdealZ p = J := hmax.eq_of_le hJ_ne_top hle
  have hp_mem : (p : ℤ*) ∈ J := by
    change hyperZModHom p (p : ℤ*) = 0
    rw [← Int.cast_natCast (R := ℤ*) p, hyperZModHom_intCast]
    simp
  have hp_not_mem : (p : ℤ*) ∉ padicInfinitesimalIdealZ p := by
    rw [← ker_thetaP, RingHom.mem_ker, thetaP_natCast]
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  exact hp_not_mem (heq ▸ hp_mem)

/-- Exact discrete-valuation constancy of `starPadicNormZ`: when `thetaP p x ≠ 0`,
`starPadicNormZ p x` is equal in `ℝ*` to the standard constant `(‖thetaP p x‖ : ℝ*)`! -/
theorem starPadicNormZ_eq_coe_norm_of_thetaP_ne_zero (p : ℕ) [Fact p.Prime] {x : ℤ*}
    (hx : thetaP p x ≠ 0) :
    starPadicNormZ p x = (‖thetaP p x‖ : ℝ*) := by
  have : ∀ n : ℕ, NeZero (p ^ n) := neZero_pow_of_prime p
  set k := (thetaP p x).valuation
  have hnorm : ‖thetaP p x‖ = (p : ℝ) ^ (-k : ℤ) :=
    PadicInt.norm_eq_zpow_neg_valuation hx
  have hmem_k : thetaP p x ∈ Ideal.span {(p : ℤ_[p]) ^ k} :=
    (PadicInt.mem_span_pow_iff_le_valuation (thetaP p x) hx k).2 le_rfl
  have hnot_mem_succ : thetaP p x ∉ Ideal.span {(p : ℤ_[p]) ^ (k + 1)} := by
    rw [PadicInt.mem_span_pow_iff_le_valuation (thetaP p x) hx (k + 1)]
    omega
  have hdvd_k : (p : ℤ*) ^ k ∣ x := by
    have h0 : hyperZModHom (p ^ k) x = 0 := by
      rw [← toZModPow_thetaP, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
      exact hmem_k
    simpa using (hyperZModHom_eq_zero_iff_dvd (p ^ k) x).1 h0
  have hndvd_succ : ¬ ((p : ℤ*) ^ (k + 1) ∣ x) := by
    intro hd
    apply hnot_mem_succ
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, toZModPow_thetaP,
        hyperZModHom_eq_zero_iff_dvd]
    simpa using hd
  induction x using Germ.inductionOn with | _ u =>
  have hcast_k : (((p : ℤ) ^ k : ℤ) : ℤ*) = (p : ℤ*) ^ k := by push_cast; rfl
  have hcast_s : (((p : ℤ) ^ (k + 1) : ℤ) : ℤ*) = (p : ℤ*) ^ (k + 1) := by push_cast; rfl
  have hev_k := (intCast_dvd_hyperint_iff ((p : ℤ) ^ k) u).1 (hcast_k.symm ▸ hdvd_k)
  have hnot_ev_s : ¬ (∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (p : ℤ) ^ (k + 1) ∣ u i) :=
    fun h ↦ hndvd_succ (hcast_s ▸ (intCast_dvd_hyperint_iff _ u).2 h)
  have hev_ns : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), ¬ ((p : ℤ) ^ (k + 1) ∣ u i) :=
    Ultrafilter.eventually_not.2 hnot_ev_s
  rw [hnorm]
  refine Germ.coe_eq.2 ((hev_k.and hev_ns).mono fun i ⟨hik, hins⟩ ↦ ?_)
  have hle : ‖(u i : ℤ_[p])‖ ≤ (p : ℝ) ^ (-k : ℤ) :=
    (PadicInt.norm_int_le_pow_iff_dvd (p := p) (k := u i) (n := k)).2 (by simpa using hik)
  have hnle : ¬ (‖(u i : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(k + 1 : ℕ) : ℤ)) := fun h ↦
    hins (by simpa using (PadicInt.norm_int_le_pow_iff_dvd (p := p) (k := u i) (n := k + 1)).1 h)
  have hnlt : ¬ (‖(u i : ℤ_[p])‖ < (p : ℝ) ^ (-k : ℤ)) := by
    rw [PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one]
    have hexp : (-k : ℤ) - 1 = -(k + 1 : ℕ) := by push_cast; ring
    rwa [hexp]
  exact le_antisymm hle (not_lt.1 hnlt)

/-- Goldblatt §18.4 (p. 240): **Norm preservation of `thetaP p`**:
`shadow (starPadicNormZ p x) = ‖thetaP p x‖` for every `x ∈ ℤ*`! -/
@[simp]
theorem shadow_starPadicNormZ (p : ℕ) [Fact p.Prime] (x : ℤ*) :
    shadow (starPadicNormZ p x) = ‖thetaP p x‖ := by
  by_cases hx : thetaP p x = 0
  · have hinf : IsInfinitesimal (starPadicNormZ p x) := by
      have hmem : x ∈ RingHom.ker (thetaP p) := hx
      rwa [ker_thetaP, mem_padicInfinitesimalIdealZ_iff] at hmem
    rw [hx, norm_zero]
    exact (shadow_eq_zero_iff_isInfinitesimal (starPadicNormZ_isLimited p x)).2 hinf
  · rw [starPadicNormZ_eq_coe_norm_of_thetaP_ne_zero p hx, shadow_coe]

/-- Type wrapper `PadicZ p` equipping `ℤ` with the $p$-adic metric `d_p(a, b) = ‖(a - b : ℤ_[p])‖`
(Goldblatt §18.4, p. 238). -/
structure PadicZ (p : ℕ) where
  /-- Underlying integer. -/
  val : ℤ

/-- $p$-adic `MetricSpace` structure on `PadicZ p`. -/
noncomputable instance instMetricSpacePadicZ (p : ℕ) [Fact p.Prime] :
    MetricSpace (PadicZ p) where
  dist a b := ‖((a.val - b.val : ℤ) : ℤ_[p])‖
  dist_self a := by simp
  dist_comm a b := by
    have : ((a.val - b.val : ℤ) : ℤ_[p]) = -((b.val - a.val : ℤ) : ℤ_[p]) := by push_cast; ring
    rw [this, norm_neg]
  dist_triangle a b c := by
    have : ((a.val - c.val : ℤ) : ℤ_[p]) =
        ((a.val - b.val : ℤ) : ℤ_[p]) + ((b.val - c.val : ℤ) : ℤ_[p]) := by push_cast; ring
    rw [this]
    exact norm_add_le _ _
  eq_of_dist_eq_zero {a b} h := by
    have h0 : ((a.val - b.val : ℤ) : ℤ_[p]) = 0 := norm_eq_zero.1 h
    have hab : a.val - b.val = 0 := Int.cast_injective h0
    cases a; cases b
    congr
    exact sub_eq_zero.1 hab

/-- Equivalence `StarMetric (PadicZ p) ≃ ℤ*`. -/
def starPadicZEquiv (p : ℕ) : StarMetric (PadicZ p) ≃ ℤ* where
  toFun := Germ.map PadicZ.val
  invFun := Germ.map PadicZ.mk
  left_inv x := Germ.inductionOn x fun _ ↦ rfl
  right_inv x := Germ.inductionOn x fun _ ↦ rfl

/-- Compatibility of `starDist` on `PadicZ p` with `starPadicNormZ`. -/
theorem starDist_padicZ_eq (p : ℕ) [Fact p.Prime] (x y : StarMetric (PadicZ p)) :
    starDist x y = starPadicNormZ p (starPadicZEquiv p x - starPadicZEquiv p y) :=
  Germ.inductionOn₂ x y fun _ _ ↦ rfl

/-- Goldblatt §18.4 (pp. 239–240): **Every** hyperinteger in `StarMetric (PadicZ p)` is limited and
approachable from `ℤ` (`PreNearstandard (PadicZ p) = Set.univ` and
`LimitedMetric (PadicZ p) ⟨0⟩ = Set.univ`), reflecting total boundedness of `(ℤ, d_p)`. -/
theorem preNearstandard_padicZ_eq_univ (p : ℕ) [Fact p.Prime] :
    PreNearstandard (PadicZ p) = Set.univ ∧ LimitedMetric (PadicZ p) ⟨0⟩ = Set.univ := by
  refine ⟨?_, ?_⟩
  · ext x
    simp only [Set.mem_univ, iff_true]
    intro ε hε
    have : ∀ n : ℕ, NeZero (p ^ n) := neZero_pow_of_prime p
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
    let z : ℤ := ((thetaP p (starPadicZEquiv p x)).appr k : ℤ)
    refine ⟨⟨z⟩, ?_⟩
    rw [starDist_padicZ_eq]
    have hconst : starPadicZEquiv p (Germ.const ⟨z⟩) = (z : ℤ*) := rfl
    rw [hconst]
    have hdvd : (p : ℤ*) ^ k ∣ (starPadicZEquiv p x - (z : ℤ*)) := by
      have hspan : thetaP p (starPadicZEquiv p x - (z : ℤ*)) ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
        rw [map_sub, thetaP_intCast]
        simpa [z] using PadicInt.appr_spec k (thetaP p (starPadicZEquiv p x))
      have h0 : hyperZModHom (p ^ k) (starPadicZEquiv p x - (z : ℤ*)) = 0 := by
        rw [← toZModPow_thetaP, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
        exact hspan
      simpa using (hyperZModHom_eq_zero_iff_dvd (p ^ k) _).1 h0
    exact (starPadicNormZ_le_pow_iff_dvd p _ k |>.2 hdvd).trans_lt (Hyperreal.coe_lt_coe.2 hk)
  · ext x
    simp only [Set.mem_univ, iff_true]
    change IsLimited (starDist x (Germ.const ⟨0⟩))
    rw [starDist_padicZ_eq]
    exact starPadicNormZ_isLimited p _

/-- Goldblatt §18.4 (p. 240): **Isometric Equivalence `MetricHull (PadicZ p) ⟨0⟩ ≃ᵢ ℤ_[p]`**
identifying the nonstandard metric hull (and metric completion) of `(ℤ, d_p)` with `ℤ_[p]`. -/
noncomputable def padicZMetricHullEquiv (p : ℕ) [Fact p.Prime] :
    MetricHull (PadicZ p) ⟨0⟩ ≃ᵢ ℤ_[p] := by
  let φ : MetricHull (PadicZ p) ⟨0⟩ → ℤ_[p] :=
    Quotient.lift (fun a : LimitedMetric (PadicZ p) ⟨0⟩ ↦ thetaP p (starPadicZEquiv p a.1))
      fun a b hab ↦ by
        have hinf : IsPadicInfinitesimalZ p (starPadicZEquiv p a.1 - starPadicZEquiv p b.1) := by
          unfold IsPadicInfinitesimalZ
          rw [← starDist_padicZ_eq]
          exact hab
        have hker : starPadicZEquiv p a.1 - starPadicZEquiv p b.1 ∈ RingHom.ker (thetaP p) := by
          rwa [ker_thetaP, mem_padicInfinitesimalIdealZ_iff]
        rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hker
        exact hker
  have hφ_iso : Isometry φ := Isometry.of_dist_eq fun x y ↦
    Quotient.inductionOn₂ x y fun a b ↦ by
      change ‖thetaP p (starPadicZEquiv p a.1) - thetaP p (starPadicZEquiv p b.1)‖ =
        shadow (starDist a.1 b.1)
      rw [← map_sub, ← shadow_starPadicNormZ p, starDist_padicZ_eq]
  have hφ_surj : Function.Surjective φ := fun w ↦ by
    obtain ⟨z, hz⟩ := thetaP_surjective p w
    have hlim : (starPadicZEquiv p).symm z ∈ LimitedMetric (PadicZ p) ⟨0⟩ :=
      (preNearstandard_padicZ_eq_univ p).2 ▸ Set.mem_univ _
    exact ⟨Quotient.mk (limitedMetricSetoid (PadicZ p) ⟨0⟩) ⟨(starPadicZEquiv p).symm z, hlim⟩,
      by simpa [φ] using hz⟩
  exact { toEquiv := Equiv.ofBijective φ ⟨hφ_iso.injective, hφ_surj⟩
          isometry_toFun := hφ_iso }

/-- Goldblatt §18.4 (p. 240): Characterization of $p$-adically **nearstandard** hyperintegers:
`thetaP p x` is a standard integer `(z : ℤ_[p])` iff `x = p^N * y + z` for some unlimited
`N ∈ *ℕ_∞`, `y ∈ ℤ*`, and standard `z ∈ ℤ`. -/
theorem thetaP_mem_range_intCast_iff (p : ℕ) [Fact p.Prime] (x : ℤ*) :
    thetaP p x ∈ Set.range (Int.cast : ℤ → ℤ_[p]) ↔
      ∃ (N : ℕ*) (y : ℤ*) (z : ℤ), IsUnlimitedNat N ∧ x = hyperintPow p N * y + (z : ℤ*) := by
  constructor
  · rintro ⟨z, hz⟩
    have hker : x - (z : ℤ*) ∈ RingHom.ker (thetaP p) := by
      rw [RingHom.mem_ker, map_sub, thetaP_intCast, ← hz, sub_self]
    rw [ker_thetaP, mem_padicInfinitesimalIdealZ_iff,
        (isPadicInfinitesimalZ_tfae p _).1, (isPadicInfinitesimalZ_tfae p _).2.1,
        (isPadicInfinitesimalZ_tfae p _).2.2] at hker
    obtain ⟨N, hN_unl, y, hy⟩ := hker
    exact ⟨N, y, z, hN_unl, by linear_combination hy⟩
  · rintro ⟨N, y, z, hN_unl, rfl⟩
    refine ⟨z, ?_⟩
    have hinf : IsPadicInfinitesimalZ p (hyperintPow p N * y) := by
      rw [(isPadicInfinitesimalZ_tfae p _).1, (isPadicInfinitesimalZ_tfae p _).2.1,
          (isPadicInfinitesimalZ_tfae p _).2.2]
      exact ⟨N, hN_unl, y, rfl⟩
    have h0 : thetaP p (hyperintPow p N * y) = 0 := by
      rw [← RingHom.mem_ker, ker_thetaP, mem_padicInfinitesimalIdealZ_iff]
      exact hinf
    rw [map_add, h0, thetaP_intCast, zero_add]

/-! ## §18.5 $p$-adic Numbers via Hyperrationals -/

/-- Goldblatt §18.5 (p. 241): Standard $p$-adic order `ord_p : ℚ → WithTop ℤ` mapping `0 ↦ ⊤`
and nonzero `q ↦ padicValRat p q`. -/
def padicOrderQ (p : ℕ) (q : ℚ) : WithTop ℤ :=
  if q = 0 then ⊤ else (padicValRat p q : WithTop ℤ)

/-- Exact relation between `‖(q : ℚ_[p])‖` and `padicOrderQ p q` for all `q ∈ ℚ` and `m ∈ ℤ`. -/
theorem norm_padic_le_zpow_iff_le_padicOrderQ (p : ℕ) [Fact p.Prime] (q : ℚ) (m : ℤ) :
    ‖(q : ℚ_[p])‖ ≤ (p : ℝ) ^ (-m) ↔ (m : WithTop ℤ) ≤ padicOrderQ p q := by
  unfold padicOrderQ
  by_cases hq : q = 0
  · subst hq
    simp only [Rat.cast_zero, norm_zero, ↓reduceIte, le_top, iff_true]
    exact zpow_nonneg (Nat.cast_nonneg p) _
  · simp only [hq, ↓reduceIte, WithTop.coe_le_coe]
    have hnorm : ‖(q : ℚ_[p])‖ = (p : ℝ) ^ (-padicValRat p q) := by
      rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hq]
      push_cast
      rfl
    rw [hnorm, zpow_le_zpow_iff_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt),
        neg_le_neg_iff]

/-- Nonstandard $p$-adic order `starPadicOrderQ : ℚ* → *(ℤ ∪ {∞})` lifted to `ℚ*`
(Goldblatt §18.5, p. 242). -/
def starPadicOrderQ (p : ℕ) (x : ℚ*) : Germ (hyperfilter ℕ : Filter ℕ) (WithTop ℤ) :=
  Germ.map (padicOrderQ p) x

/-- Nonstandard $p$-adic norm `starPadicNormQ : ℚ* → ℝ*` lifted from `q ↦ ‖(q : ℚ_[p])‖`
(Goldblatt §18.5, p. 242). -/
noncomputable def starPadicNormQ (p : ℕ) [Fact p.Prime] (x : ℚ*) : ℝ* :=
  Germ.map (fun q : ℚ ↦ ‖(q : ℚ_[p])‖) x

/-- Nonnegativity `0 ≤ starPadicNormQ p x`. -/
theorem starPadicNormQ_nonneg (p : ℕ) [Fact p.Prime] (x : ℚ*) :
    0 ≤ starPadicNormQ p x :=
  Germ.inductionOn x fun u ↦
    ofSeq_le_ofSeq.2 <| Eventually.of_forall fun i ↦ norm_nonneg (u i : ℚ_[p])

/-- Ultrametric inequality `starPadicNormQ p (x + y) ≤ max (starPadicNormQ p x) (starPadicNormQ p y)`. -/
theorem starPadicNormQ_add_le_max (p : ℕ) [Fact p.Prime] (x y : ℚ*) :
    starPadicNormQ p (x + y) ≤ max (starPadicNormQ p x) (starPadicNormQ p y) :=
  Germ.inductionOn₂ x y fun u v ↦
    ofSeq_le_ofSeq.2 <| Eventually.of_forall fun i ↦ by
      change ‖((u i + v i : ℚ) : ℚ_[p])‖ ≤ max ‖(u i : ℚ_[p])‖ ‖(v i : ℚ_[p])‖
      rw [Rat.cast_add]
      exact Padic.nonarchimedean (u i : ℚ_[p]) (v i : ℚ_[p])

/-- Multiplicativity `starPadicNormQ p (x * y) = starPadicNormQ p x * starPadicNormQ p y`. -/
theorem starPadicNormQ_mul (p : ℕ) [Fact p.Prime] (x y : ℚ*) :
    starPadicNormQ p (x * y) = starPadicNormQ p x * starPadicNormQ p y :=
  Germ.inductionOn₂ x y fun u v ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ by
      change ‖((u i * v i : ℚ) : ℚ_[p])‖ = ‖(u i : ℚ_[p])‖ * ‖(v i : ℚ_[p])‖
      rw [Rat.cast_mul, norm_mul]

/-- Symmetry `starPadicNormQ p (-x) = starPadicNormQ p x`. -/
@[simp]
theorem starPadicNormQ_neg (p : ℕ) [Fact p.Prime] (x : ℚ*) :
    starPadicNormQ p (-x) = starPadicNormQ p x :=
  Germ.inductionOn x fun u ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ by
      change ‖((-u i : ℚ) : ℚ_[p])‖ = ‖(u i : ℚ_[p])‖
      rw [Rat.cast_neg, norm_neg]

/-- `starPadicNormQ p 0 = 0`. -/
@[simp]
theorem starPadicNormQ_zero (p : ℕ) [Fact p.Prime] :
    starPadicNormQ p 0 = 0 :=
  Germ.coe_eq.2 <| Eventually.of_forall fun _ ↦ by simp

/-- `starPadicNormQ p 1 = 1`. -/
@[simp]
theorem starPadicNormQ_one (p : ℕ) [Fact p.Prime] :
    starPadicNormQ p 1 = 1 :=
  Germ.coe_eq.2 <| Eventually.of_forall fun _ ↦ by simp

/-- Coordinatewise bound equivalence on `ℚ*`:
`starPadicNormQ p x ≤ ((p : ℝ) ^ (-m) : ℝ*) ↔ Germ.const (m : WithTop ℤ) ≤ starPadicOrderQ p x`. -/
theorem starPadicNormQ_le_zpow_iff (p : ℕ) [Fact p.Prime] (x : ℚ*) (m : ℤ) :
    starPadicNormQ p x ≤ (((p : ℝ) ^ (-m) : ℝ) : ℝ*) ↔
      Germ.const (m : WithTop ℤ) ≤ starPadicOrderQ p x := by
  induction x using Germ.inductionOn with | _ u =>
  change ofSeq (fun i ↦ ‖(u i : ℚ_[p])‖) ≤ ofSeq (fun _ ↦ (p : ℝ) ^ (-m)) ↔
    ((fun _ : ℕ ↦ (m : WithTop ℤ)) : Germ (hyperfilter ℕ : Filter ℕ) (WithTop ℤ)) ≤
      ((fun i ↦ padicOrderQ p (u i)) : Germ (hyperfilter ℕ : Filter ℕ) (WithTop ℤ))
  rw [ofSeq_le_ofSeq, Germ.coe_le]
  exact eventually_congr (Eventually.of_forall fun i ↦
    norm_padic_le_zpow_iff_le_padicOrderQ p (u i) m)

/-- Goldblatt §18.5 (p. 242): `x ∈ ℚ*` is **$p$-adically limited** (`x ∈ ℚ_{p,𝕃}`) if
`starPadicNormQ p x` is limited in `ℝ*`. -/
def IsPadicLimitedQ (p : ℕ) [Fact p.Prime] (x : ℚ*) : Prop :=
  IsLimited (starPadicNormQ p x)

/-- Goldblatt §18.5 (p. 242): `x ∈ ℚ*` is **$p$-adically infinitesimal** (`x ∈ ℚ_{p,𝕀}`) if
`starPadicNormQ p x ≈ 0` in `ℝ*`. -/
def IsPadicInfinitesimalQ (p : ℕ) [Fact p.Prime] (x : ℚ*) : Prop :=
  IsInfinitesimal (starPadicNormQ p x)

/-- Goldblatt **Theorem 18.5.1** (p. 242): Valuation characterizations of `ℚ_{p,𝕃}` and `ℚ_{p,𝕀}`:
1. `x ∈ ℚ_{p,𝕃}` iff `ord_p(x)` is bounded below by a standard integer `m ∈ ℤ`
   (i.e. not a negative unlimited hyperinteger);
2. `x ∈ ℚ_{p,𝕀}` iff `ord_p(x) > n` for every standard natural `n ∈ ℕ`
   (i.e. `ord_p(x)` is a positive unlimited hyperinteger or `∞`). -/
theorem padicLimitedQ_and_infinitesimalQ_order_iff (p : ℕ) [Fact p.Prime] (x : ℚ*) :
    (IsPadicLimitedQ p x ↔ ∃ m : ℤ, Germ.const (m : WithTop ℤ) ≤ starPadicOrderQ p x) ∧
    (IsPadicInfinitesimalQ p x ↔ ∀ n : ℕ, Germ.const ((n : ℤ) : WithTop ℤ) < starPadicOrderQ p x) := by
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨n, hn⟩
      rw [abs_of_nonneg (starPadicNormQ_nonneg p x)] at hn
      refine ⟨-(n : ℤ), (starPadicNormQ_le_zpow_iff p x (-(n : ℤ))).1 ?_⟩
      rw [neg_neg, zpow_natCast]
      have hnp : (n : ℝ) ≤ (p : ℝ) ^ n := by
        exact_mod_cast (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
      exact hn.le.trans (by exact_mod_cast Hyperreal.coe_le_coe.2 hnp)
    · rintro ⟨m, hm⟩
      have hle := (starPadicNormQ_le_zpow_iff p x m).2 hm
      exact isLimited_of_abs_le (isLimited_coe ((p : ℝ) ^ (-m)))
        (by rwa [abs_of_nonneg (starPadicNormQ_nonneg p x),
                 abs_of_pos (Hyperreal.coe_pos.2 (zpow_pos (Nat.cast_pos.2 (Fact.out : p.Prime).pos) _))])
  · constructor
    · intro hinf n
      have hpos : (0 : ℝ) < (p : ℝ) ^ (-(n + 1 : ℤ)) :=
        zpow_pos (Nat.cast_pos.2 (Fact.out : p.Prime).pos) _
      have hlt := hinf _ hpos
      rw [abs_of_nonneg (starPadicNormQ_nonneg p x)] at hlt
      have hle := (starPadicNormQ_le_zpow_iff p x (n + 1 : ℤ)).1 hlt.le
      exact (Germ.coe_lt.2 (Eventually.of_forall fun _ ↦
        WithTop.coe_lt_coe.2 (Int.lt_succ (n : ℤ)))).trans_le hle
    · intro hord ε hε
      rw [abs_of_nonneg (starPadicNormQ_nonneg p x)]
      obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
      have hle : Germ.const ((k : ℤ) : WithTop ℤ) ≤ starPadicOrderQ p x := by
        cases k with
        | zero =>
          have h0 : Germ.const ((0 : ℤ) : WithTop ℤ) < starPadicOrderQ p x := hord 0
          exact h0.le
        | succ m =>
          have hm : Germ.const ((m : ℤ) : WithTop ℤ) < starPadicOrderQ p x := hord m
          induction x using Germ.inductionOn with | _ u =>
          refine Germ.coe_le.2 ((Germ.coe_lt.1 hm).mono fun i hi ↦ ?_)
          by_cases h0 : u i = 0
          · simp [padicOrderQ, h0]
          · simp only [Function.comp_apply, padicOrderQ, h0, ↓reduceIte] at hi ⊢
            have hlt_z : (m : ℤ) < padicValRat p (u i) := WithTop.coe_lt_coe.1 hi
            exact WithTop.coe_le_coe.2 (by omega)
      exact ((starPadicNormQ_le_zpow_iff p x (k : ℤ)).2 hle).trans_lt (Hyperreal.coe_lt_coe.2 hk)

/-- Ring homomorphism `intToHyperrat : ℤ* →+* ℚ*` embedding hyperintegers into hyperrationals. -/
def intToHyperrat : ℤ* →+* ℚ* :=
  germMapRingHom (Int.castRingHom ℚ)

/-- Injectivity of `intToHyperrat : ℤ* →+* ℚ*`. -/
theorem intToHyperrat_injective : Function.Injective intToHyperrat := by
  intro x y h
  induction x using Germ.inductionOn with | _ u =>
  induction y using Germ.inductionOn with | _ v =>
  have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (u i : ℚ) = (v i : ℚ) := Germ.coe_eq.1 h
  exact Germ.coe_eq.2 (hev.mono fun i hi ↦ Int.cast_injective hi)

/-- Compatibility `starPadicNormQ p (intToHyperrat z) = starPadicNormZ p z`. -/
@[simp]
theorem starPadicNormQ_intToHyperrat (p : ℕ) [Fact p.Prime] (z : ℤ*) :
    starPadicNormQ p (intToHyperrat z) = starPadicNormZ p z :=
  Germ.inductionOn z fun u ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ by
      change ‖((u i : ℚ) : ℚ_[p])‖ = ‖(u i : ℤ_[p])‖
      rw [Rat.cast_intCast, PadicInt.norm_intCast_eq_padic_norm]

/-- Reduced hyperinteger numerator `hyperratNum : ℚ* → ℤ*` lifted from `Rat.num`. -/
def hyperratNum (q : ℚ*) : ℤ* :=
  Germ.map Rat.num q

/-- Reduced positive hyperinteger denominator `hyperratDen : ℚ* → ℤ*` lifted from `r ↦ (r.den : ℤ)`. -/
def hyperratDen (q : ℚ*) : ℤ* :=
  Germ.map (fun r : ℚ ↦ (r.den : ℤ)) q

/-- Canonical reduced fraction identity `intToHyperrat (hyperratNum q) / intToHyperrat (hyperratDen q) = q`. -/
theorem intToHyperrat_num_div_den (q : ℚ*) :
    intToHyperrat (hyperratNum q) / intToHyperrat (hyperratDen q) = q :=
  Germ.inductionOn q fun u ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ (u i).num_div_den

/-- Key arithmetic lemma on reduced rationals `r = a / b` (`gcd(a, b) = 1`): for every `k ≥ 1`,
`‖(r.den : ℤ_[p])‖ ≤ p ^ (-k)` iff `p ^ k ≤ ‖(r : ℚ_[p])‖`. -/
theorem norm_den_le_pow_iff_pow_le_norm_rat (p : ℕ) [Fact p.Prime] (r : ℚ) {k : ℕ} (hk : 1 ≤ k) :
    ‖((r.den : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-k : ℤ) ↔ (p : ℝ) ^ (k : ℤ) ≤ ‖(r : ℚ_[p])‖ := by
  have hden_eq : ‖((r.den : ℚ) : ℚ_[p])‖ = ‖((r.den : ℤ) : ℤ_[p])‖ := by
    rw [PadicInt.norm_intCast_eq_padic_norm, Int.cast_natCast, Rat.cast_natCast]
  have hden_ne : ((r.den : ℚ) : ℚ_[p]) ≠ 0 := by exact_mod_cast r.den_nz
  have hden_norm_pos : 0 < ‖((r.den : ℤ) : ℤ_[p])‖ := by
    rw [← hden_eq]
    exact norm_pos_iff.2 hden_ne
  have hr_eq : (r : ℚ_[p]) = ((r.num : ℚ) : ℚ_[p]) / ((r.den : ℚ) : ℚ_[p]) := by
    calc (r : ℚ_[p]) = (((r.num : ℚ) / (r.den : ℚ) : ℚ) : ℚ_[p]) :=
          congrArg Rat.cast r.num_div_den.symm
      _ = ((r.num : ℚ) : ℚ_[p]) / ((r.den : ℚ) : ℚ_[p]) := Rat.cast_div _ _
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.2 (Fact.out : p.Prime).pos
  constructor
  · intro hle
    have hdvd_k : ((p : ℤ) ^ k) ∣ (r.den : ℤ) :=
      (PadicInt.norm_int_le_pow_iff_dvd (p := p) (k := (r.den : ℤ)) (n := k)).1 (by simpa using hle)
    have hdvd_p : (p : ℤ) ∣ (r.den : ℤ) :=
      (dvd_pow_self (p : ℤ) (by omega)).trans hdvd_k
    have hndvd_num : ¬ ((p : ℤ) ∣ r.num) := by
      intro hpn
      have hp_nat_den : p ∣ r.den := Int.natCast_dvd_natCast.1 hdvd_p
      have hp_nat_num : p ∣ r.num.natAbs := Int.natCast_dvd.1 hpn
      have h1 : p ∣ 1 := r.reduced.gcd_eq_one ▸ Nat.dvd_gcd hp_nat_num hp_nat_den
      exact (Fact.out : p.Prime).not_dvd_one h1
    have hnum_norm : ‖((r.num : ℚ) : ℚ_[p])‖ = 1 := by
      rw [Rat.cast_intCast, ← PadicInt.norm_intCast_eq_padic_norm]
      exact le_antisymm (PadicInt.norm_le_one _)
        (not_lt.1 (mt (PadicInt.norm_int_lt_one_iff_dvd r.num).1 hndvd_num))
    have hnorm_r : ‖(r : ℚ_[p])‖ = ‖((r.den : ℤ) : ℤ_[p])‖⁻¹ := by
      rw [hr_eq, norm_div, hnum_norm, hden_eq, one_div]
    have hle' : ‖((r.den : ℤ) : ℤ_[p])‖ ≤ ((p : ℝ) ^ (k : ℤ))⁻¹ := by
      simpa [zpow_neg] using hle
    rw [hnorm_r]
    simpa only [inv_inv] using inv_anti₀ hden_norm_pos hle'
  · intro hge
    have hnorm_le_inv : ‖(r : ℚ_[p])‖ ≤ ‖((r.den : ℤ) : ℤ_[p])‖⁻¹ := by
      rw [hr_eq, norm_div, hden_eq]
      have hnum_le : ‖((r.num : ℚ) : ℚ_[p])‖ ≤ 1 := by
        rw [Rat.cast_intCast, ← PadicInt.norm_intCast_eq_padic_norm]
        exact PadicInt.norm_le_one _
      exact (div_le_div_of_nonneg_right hnum_le hden_norm_pos.le).trans_eq (one_div _)
    have hinv_ge : (p : ℝ) ^ (k : ℤ) ≤ ‖((r.den : ℤ) : ℤ_[p])‖⁻¹ := hge.trans hnorm_le_inv
    simpa only [inv_inv, zpow_neg] using inv_anti₀ (zpow_pos hp_pos (k : ℤ)) hinv_ge

/-- If `y ∈ ℤ*` is not a $p$-adic infinitesimal, then `y` is eventually nonzero and
`intToHyperrat y` is invertible in `ℚ*` with limited $p$-adic norm of `intToHyperrat x / intToHyperrat y`. -/
theorem eventually_ne_zero_and_limited_div_of_not_padicInfinitesimalZ
    (p : ℕ) [Fact p.Prime] (x : ℤ*) {y : ℤ*} (hy : ¬ IsPadicInfinitesimalZ p y) :
    (∀ u : ℕ → ℤ, (u : ℤ*) = y → ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), u i ≠ 0) ∧
    intToHyperrat y * (intToHyperrat y)⁻¹ = 1 ∧
    IsPadicLimitedQ p (intToHyperrat x / intToHyperrat y) := by
  have hnot_all : ¬ ∀ k : ℕ, (p : ℤ*) ^ k ∣ y :=
    mt ((isPadicInfinitesimalZ_tfae p y).1.trans (isPadicInfinitesimalZ_tfae p y).2.1).2 hy
  push Not at hnot_all
  obtain ⟨k, hndvd⟩ := hnot_all
  induction y using Germ.inductionOn with | _ v =>
  induction x using Germ.inductionOn with | _ u =>
  have hcast_k : (((p : ℤ) ^ k : ℤ) : ℤ*) = (p : ℤ*) ^ k := by push_cast; rfl
  have hnot_ev : ¬ (∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (p : ℤ) ^ k ∣ v i) :=
    fun h ↦ hndvd (hcast_k ▸ (intCast_dvd_hyperint_iff _ v).2 h)
  have hev_ndvd : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), ¬ ((p : ℤ) ^ k ∣ v i) :=
    Ultrafilter.eventually_not.2 hnot_ev
  have hev_nz : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), v i ≠ 0 :=
    hev_ndvd.mono fun i hi h0 ↦ hi (h0 ▸ dvd_zero _)
  refine ⟨fun u' hu' ↦ ?_, ?_, ?_⟩
  · have heq : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), u' i = v i := Germ.coe_eq.1 hu'
    exact (heq.and hev_nz).mono fun i ⟨h1, h2⟩ ↦ h1.symm ▸ h2
  · refine Germ.coe_eq.2 (hev_nz.mono fun i hi ↦ ?_)
    have hq_nz : (v i : ℚ) ≠ 0 := Int.cast_ne_zero.2 hi
    exact mul_inv_cancel₀ hq_nz
  · refine isLimited_of_abs_le (isLimited_coe ((p : ℝ) ^ (k : ℤ))) ?_
    rw [abs_of_nonneg (starPadicNormQ_nonneg p _),
        abs_of_pos (Hyperreal.coe_pos.2 (zpow_pos (Nat.cast_pos.2 (Fact.out : p.Prime).pos) _))]
    refine ofSeq_le_ofSeq.2 (hev_ndvd.mono fun i hi ↦ ?_)
    have hv_gt : (p : ℝ) ^ (-k : ℤ) < ‖(v i : ℤ_[p])‖ := not_le.1 fun hle ↦
      hi (by simpa using (PadicInt.norm_int_le_pow_iff_dvd (p := p) (k := v i) (n := k)).1 hle)
    have hpos_zpow : 0 < (p : ℝ) ^ (-k : ℤ) :=
      zpow_pos (Nat.cast_pos.2 (Fact.out : p.Prime).pos) _
    have hu_le : ‖(u i : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one (u i)
    have hv_eq : ‖(v i : ℚ_[p])‖ = ‖(v i : ℤ_[p])‖ :=
      (PadicInt.norm_intCast_eq_padic_norm (p := p) (v i)).symm
    change ‖(((u i : ℚ) / (v i : ℚ) : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (k : ℤ)
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, norm_div, hv_eq]
    calc ‖(u i : ℚ_[p])‖ / ‖(v i : ℤ_[p])‖
        ≤ 1 / (p : ℝ) ^ (-k : ℤ) :=
          div_le_div₀ zero_le_one hu_le hpos_zpow hv_gt.le
      _ = (p : ℝ) ^ (k : ℤ) := by rw [one_div, zpow_neg, inv_inv]

/-- Goldblatt **Theorem 18.5.2** (p. 243): Denominator characterization of $p$-adically limited
hyperrationals `q ∈ ℚ_{p,𝕃}`:
1. A hyperrational `q ∈ ℚ*` is $p$-adically limited iff its reduced denominator `hyperratDen q` is
   **not** a $p$-adic infinitesimal (`hyperratDen q ∉ I_p`);
2. Equivalently, `q ∈ ℚ_{p,𝕃}` iff `q = intToHyperrat x / intToHyperrat y` for some `x, y ∈ ℤ*`
   with `y ∉ I_p`! -/
theorem isPadicLimitedQ_iff_not_infinitesimal_den (p : ℕ) [Fact p.Prime] (q : ℚ*) :
    (IsPadicLimitedQ p q ↔ ¬ IsPadicInfinitesimalZ p (hyperratDen q)) ∧
    (IsPadicLimitedQ p q ↔
      ∃ x y : ℤ*, ¬ IsPadicInfinitesimalZ p y ∧ q = intToHyperrat x / intToHyperrat y) := by
  have h1 : IsPadicLimitedQ p q ↔ ¬ IsPadicInfinitesimalZ p (hyperratDen q) := by
    induction q using Germ.inductionOn with | _ u =>
    constructor
    · intro hlim hinf_den
      obtain ⟨n, hn⟩ := hlim
      rw [abs_of_nonneg (starPadicNormQ_nonneg p _)] at hn
      let k : ℕ := n + 1
      have hk1 : 1 ≤ k := Nat.succ_le_succ (Nat.zero_le n)
      have hdvd_k : (p : ℤ*) ^ k ∣ hyperratDen (u : ℚ*) :=
        ((isPadicInfinitesimalZ_tfae p _).1.trans (isPadicInfinitesimalZ_tfae p _).2.1).1 hinf_den k
      have hden_le : starPadicNormZ p (hyperratDen (u : ℚ*)) ≤ (((p : ℝ) ^ (-k : ℤ) : ℝ) : ℝ*) :=
        (starPadicNormZ_le_pow_iff_dvd p _ k).2 hdvd_k
      have hev_den : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
          ‖(((u i).den : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-k : ℤ) :=
        ofSeq_le_ofSeq.1 hden_le
      have hev_rat : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (p : ℝ) ^ (k : ℤ) ≤ ‖(u i : ℚ_[p])‖ :=
        hev_den.mono fun i hi ↦ (norm_den_le_pow_iff_pow_le_norm_rat p (u i) hk1).1 hi
      have hge : (((p : ℝ) ^ (k : ℤ) : ℝ) : ℝ*) ≤ starPadicNormQ p (u : ℚ*) :=
        ofSeq_le_ofSeq.2 hev_rat
      have hgt_n : (n : ℝ) < (p : ℝ) ^ (k : ℤ) := by
        rw [zpow_natCast]
        exact_mod_cast (Nat.lt_succ_self n).trans_le
          (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
      have hcontr : (n : ℝ*) < (n : ℝ*) := calc
        (n : ℝ*) = ((n : ℝ) : ℝ*) := (coe_natCast_hyperreal n).symm
        _ < (((p : ℝ) ^ (k : ℤ) : ℝ) : ℝ*) := Hyperreal.coe_lt_coe.2 hgt_n
        _ ≤ starPadicNormQ p (u : ℚ*) := hge
        _ < (n : ℝ*) := hn
      exact lt_irrefl _ hcontr
    · intro hnot_inf
      rw [← intToHyperrat_num_div_den (u : ℚ*)]
      exact (eventually_ne_zero_and_limited_div_of_not_padicInfinitesimalZ p
        (hyperratNum (u : ℚ*)) hnot_inf).2.2
  refine ⟨h1, ?_⟩
  constructor
  · intro hlim
    exact ⟨hyperratNum q, hyperratDen q, h1.1 hlim, (intToHyperrat_num_div_den q).symm⟩
  · rintro ⟨x, y, hy, rfl⟩
    exact (eventually_ne_zero_and_limited_div_of_not_padicInfinitesimalZ p x hy).2.2

/-- Goldblatt §18.5 (p. 243): Commutative subring `PadicLimitedSubringQ p` (`ℚ_{p,𝕃}`) of
$p$-adically limited hyperrationals in `ℚ*`. -/
noncomputable def PadicLimitedSubringQ (p : ℕ) [Fact p.Prime] : Subring ℚ* where
  carrier := {x : ℚ* | IsPadicLimitedQ p x}
  mul_mem' {x y} hx hy := by
    change IsLimited (starPadicNormQ p (x * y))
    rw [starPadicNormQ_mul]
    exact hx.mul hy
  one_mem' := by simpa [IsPadicLimitedQ] using isLimited_coe 1
  add_mem' {x y} hx hy :=
    isLimited_of_abs_le (hx.add hy)
      (by rw [abs_of_nonneg (starPadicNormQ_nonneg p _),
              abs_of_nonneg (add_nonneg (starPadicNormQ_nonneg p x) (starPadicNormQ_nonneg p y))]
          exact (starPadicNormQ_add_le_max p x y).trans
            (max_le_add_of_nonneg (starPadicNormQ_nonneg p x) (starPadicNormQ_nonneg p y)))
  zero_mem' := by simpa [IsPadicLimitedQ] using isLimited_coe 0
  neg_mem' {x} hx := by
    change IsLimited (starPadicNormQ p (-x))
    rwa [starPadicNormQ_neg]

/-- Membership in `PadicLimitedSubringQ p`. -/
@[simp]
theorem mem_padicLimitedSubringQ_iff (p : ℕ) [Fact p.Prime] {x : ℚ*} :
    x ∈ PadicLimitedSubringQ p ↔ IsPadicLimitedQ p x :=
  Iff.rfl

/-- Goldblatt §18.5 (p. 243): Ideal `PadicInfinitesimalIdealQ p` (`ℚ_{p,𝕀}`) of $p$-adic
infinitesimals inside `PadicLimitedSubringQ p`. -/
noncomputable def PadicInfinitesimalIdealQ (p : ℕ) [Fact p.Prime] :
    Ideal (PadicLimitedSubringQ p) where
  carrier := {x : PadicLimitedSubringQ p | IsPadicInfinitesimalQ p x.1}
  add_mem' {x y} hx hy :=
    isInfinitesimal_of_abs_le (hx.add hy)
      (by rw [abs_of_nonneg (starPadicNormQ_nonneg p _),
              abs_of_nonneg (add_nonneg (starPadicNormQ_nonneg p x.1) (starPadicNormQ_nonneg p y.1))]
          exact (starPadicNormQ_add_le_max p x.1 y.1).trans
            (max_le_add_of_nonneg (starPadicNormQ_nonneg p x.1) (starPadicNormQ_nonneg p y.1)))
  zero_mem' := by simpa [IsPadicInfinitesimalQ] using isInfinitesimal_zero
  smul_mem' c x hx := by
    change IsInfinitesimal (starPadicNormQ p (c.1 * x.1))
    rw [starPadicNormQ_mul]
    exact c.2.mul_isInfinitesimal hx

/-- Membership in `PadicInfinitesimalIdealQ p`. -/
@[simp]
theorem mem_padicInfinitesimalIdealQ_iff (p : ℕ) [Fact p.Prime] {x : PadicLimitedSubringQ p} :
    x ∈ PadicInfinitesimalIdealQ p ↔ IsPadicInfinitesimalQ p x.1 :=
  Iff.rfl

/-- Underlying map `algebraMap ℤ_[p] ℚ_[p] (thetaP p (num v)) / algebraMap ℤ_[p] ℚ_[p] (thetaP p (den v))`
for `thetaPQ p`. -/
noncomputable def thetaPQFun (p : ℕ) [Fact p.Prime] (v : PadicLimitedSubringQ p) : ℚ_[p] :=
  algebraMap ℤ_[p] ℚ_[p] (thetaP p (hyperratNum v.1)) /
    algebraMap ℤ_[p] ℚ_[p] (thetaP p (hyperratDen v.1))

/-- Nonvanishing of `algebraMap ℤ_[p] ℚ_[p] (thetaP p y)` whenever `¬ IsPadicInfinitesimalZ p y`. -/
theorem coe_thetaP_ne_zero_of_not_infinitesimal (p : ℕ) [Fact p.Prime] {y : ℤ*}
    (hy : ¬ IsPadicInfinitesimalZ p y) :
    algebraMap ℤ_[p] ℚ_[p] (thetaP p y) ≠ 0 := by
  intro h0
  have hz : thetaP p y = 0 := (IsFractionRing.injective ℤ_[p] ℚ_[p]) (by simpa using h0)
  apply hy
  have hmem : y ∈ RingHom.ker (thetaP p) := hz
  rwa [ker_thetaP, mem_padicInfinitesimalIdealZ_iff] at hmem

/-- Representation independence of `thetaPQFun`: for any `x, y ∈ ℤ*` with `¬ IsPadicInfinitesimalZ p y`
and `v.1 = intToHyperrat x / intToHyperrat y`, `thetaPQFun p v = algebraMap _ _ (thetaP p x) / algebraMap _ _ (thetaP p y)`
(Goldblatt §18.5, p. 243). -/
theorem thetaPQFun_eq_div (p : ℕ) [Fact p.Prime] (v : PadicLimitedSubringQ p)
    {x y : ℤ*} (hy : ¬ IsPadicInfinitesimalZ p y)
    (hv : v.1 = intToHyperrat x / intToHyperrat y) :
    thetaPQFun p v =
      algebraMap ℤ_[p] ℚ_[p] (thetaP p x) / algebraMap ℤ_[p] ℚ_[p] (thetaP p y) := by
  have hden_not_inf : ¬ IsPadicInfinitesimalZ p (hyperratDen v.1) :=
    (isPadicLimitedQ_iff_not_infinitesimal_den p v.1).1.1
      ((mem_padicLimitedSubringQ_iff p).1 v.2)
  have hcross : hyperratNum v.1 * y = x * hyperratDen v.1 := by
    obtain ⟨r, hr⟩ : ∃ r : ℕ → ℚ, (r : ℚ*) = v.1 := by
      induction v.1 using Germ.inductionOn with | _ r => exact ⟨r, rfl⟩
    induction x using Germ.inductionOn with | _ a =>
    induction y using Germ.inductionOn with | _ b =>
    rw [← hr] at hv ⊢
    have hev_b : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), b i ≠ 0 :=
      (eventually_ne_zero_and_limited_div_of_not_padicInfinitesimalZ p (a : ℤ*) hy).1 b rfl
    have hev_eq : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), r i = (a i : ℚ) / (b i : ℚ) :=
      Germ.coe_eq.1 hv
    refine Germ.coe_eq.2 ((hev_b.and hev_eq).mono fun i ⟨hbi, hri⟩ ↦ ?_)
    have hdiv_q : ((r i).num : ℚ) / (((r i).den : ℤ) : ℚ) = (a i : ℚ) / (b i : ℚ) := by
      rw [← hri, Int.cast_natCast, (r i).num_div_den]
    have hd_nz : (((r i).den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (r i).den_nz
    have hb_nz : (b i : ℚ) ≠ 0 := Int.cast_ne_zero.2 hbi
    have hmul_q := (div_eq_div_iff hd_nz hb_nz).1 hdiv_q
    dsimp only [Function.comp_apply]
    have hmul_q' : (((r i).num * b i : ℤ) : ℚ) = ((a i * (r i).den : ℤ) : ℚ) := by
      push_cast; exact hmul_q
    exact Int.cast_injective hmul_q'
  unfold thetaPQFun
  rw [div_eq_div_iff
      (coe_thetaP_ne_zero_of_not_infinitesimal p hden_not_inf)
      (coe_thetaP_ne_zero_of_not_infinitesimal p hy)]
  have htheta :
      ((algebraMap ℤ_[p] ℚ_[p]).comp (thetaP p)) (hyperratNum v.1 * y) =
      ((algebraMap ℤ_[p] ℚ_[p]).comp (thetaP p)) (x * hyperratDen v.1) :=
    congrArg _ hcross
  simpa only [RingHom.comp_apply, map_mul] using htheta

/-- Goldblatt §18.5 (p. 243): Canonical surjective ring homomorphism
`thetaPQ p : PadicLimitedSubringQ p →+* ℚ_[p]` extending `thetaP p : ℤ* →+* ℤ_[p]`. -/
noncomputable def thetaPQ (p : ℕ) [Fact p.Prime] :
    PadicLimitedSubringQ p →+* ℚ_[p] where
  toFun := thetaPQFun p
  map_one' := by
    have h1 : ¬ IsPadicInfinitesimalZ p (1 : ℤ*) := by
      intro h
      have h0 : thetaP p (1 : ℤ*) = 0 := by
        rw [← RingHom.mem_ker, ker_thetaP, mem_padicInfinitesimalIdealZ_iff]
        exact h
      rw [map_one] at h0
      exact one_ne_zero h0
    have heq : (1 : PadicLimitedSubringQ p).1 = intToHyperrat 1 / intToHyperrat 1 := by simp
    rw [thetaPQFun_eq_div p 1 h1 heq, map_one, map_one, div_one]
  map_zero' := by
    have h1 : ¬ IsPadicInfinitesimalZ p (1 : ℤ*) := by
      intro h
      have h0 : thetaP p (1 : ℤ*) = 0 := by
        rw [← RingHom.mem_ker, ker_thetaP, mem_padicInfinitesimalIdealZ_iff]
        exact h
      rw [map_one] at h0
      exact one_ne_zero h0
    have heq : (0 : PadicLimitedSubringQ p).1 = intToHyperrat 0 / intToHyperrat 1 := by simp
    rw [thetaPQFun_eq_div p 0 h1 heq, map_zero, map_one, map_zero, map_one, zero_div]
  map_mul' u v := by
    have hdu : ¬ IsPadicInfinitesimalZ p (hyperratDen u.1) :=
      (isPadicLimitedQ_iff_not_infinitesimal_den p u.1).1.1 ((mem_padicLimitedSubringQ_iff p).1 u.2)
    have hdv : ¬ IsPadicInfinitesimalZ p (hyperratDen v.1) :=
      (isPadicLimitedQ_iff_not_infinitesimal_den p v.1).1.1 ((mem_padicLimitedSubringQ_iff p).1 v.2)
    have hduv : ¬ IsPadicInfinitesimalZ p (hyperratDen u.1 * hyperratDen v.1) := by
      intro hinf
      have hm : hyperratDen u.1 * hyperratDen v.1 ∈ RingHom.ker (thetaP p) := by
        rwa [ker_thetaP, mem_padicInfinitesimalIdealZ_iff]
      have h0 : algebraMap ℤ_[p] ℚ_[p] (thetaP p (hyperratDen u.1)) *
          algebraMap ℤ_[p] ℚ_[p] (thetaP p (hyperratDen v.1)) = 0 := by
        rw [← map_mul, ← map_mul, RingHom.mem_ker.1 hm, map_zero]
      exact mul_ne_zero
        (coe_thetaP_ne_zero_of_not_infinitesimal p hdu)
        (coe_thetaP_ne_zero_of_not_infinitesimal p hdv) h0
    have hprod : (u * v).1 =
        intToHyperrat (hyperratNum u.1 * hyperratNum v.1) /
          intToHyperrat (hyperratDen u.1 * hyperratDen v.1) := by
      change u.1 * v.1 = _
      rw [map_mul, map_mul]
      calc u.1 * v.1
          = (intToHyperrat (hyperratNum u.1) / intToHyperrat (hyperratDen u.1)) *
              (intToHyperrat (hyperratNum v.1) / intToHyperrat (hyperratDen v.1)) := by
            rw [intToHyperrat_num_div_den, intToHyperrat_num_div_den]
        _ = (intToHyperrat (hyperratNum u.1) * intToHyperrat (hyperratNum v.1)) /
              (intToHyperrat (hyperratDen u.1) * intToHyperrat (hyperratDen v.1)) := by
            obtain ⟨ru, hru⟩ : ∃ ru : ℕ → ℚ, (ru : ℚ*) = u.1 := by
              induction u.1 using Germ.inductionOn with | _ ru => exact ⟨ru, rfl⟩
            obtain ⟨rv, hrv⟩ : ∃ rv : ℕ → ℚ, (rv : ℚ*) = v.1 := by
              induction v.1 using Germ.inductionOn with | _ rv => exact ⟨rv, rfl⟩
            rw [← hru, ← hrv]
            exact Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ div_mul_div_comm _ _ _ _)
    rw [thetaPQFun_eq_div p (u * v) hduv hprod, map_mul, map_mul, map_mul, map_mul,
        ← div_mul_div_comm]
    rfl
  map_add' u v := by
    have hdu : ¬ IsPadicInfinitesimalZ p (hyperratDen u.1) :=
      (isPadicLimitedQ_iff_not_infinitesimal_den p u.1).1.1 ((mem_padicLimitedSubringQ_iff p).1 u.2)
    have hdv : ¬ IsPadicInfinitesimalZ p (hyperratDen v.1) :=
      (isPadicLimitedQ_iff_not_infinitesimal_den p v.1).1.1 ((mem_padicLimitedSubringQ_iff p).1 v.2)
    have hduv : ¬ IsPadicInfinitesimalZ p (hyperratDen u.1 * hyperratDen v.1) := by
      intro hinf
      have hm : hyperratDen u.1 * hyperratDen v.1 ∈ RingHom.ker (thetaP p) := by
        rwa [ker_thetaP, mem_padicInfinitesimalIdealZ_iff]
      have h0 : algebraMap ℤ_[p] ℚ_[p] (thetaP p (hyperratDen u.1)) *
          algebraMap ℤ_[p] ℚ_[p] (thetaP p (hyperratDen v.1)) = 0 := by
        rw [← map_mul, ← map_mul, RingHom.mem_ker.1 hm, map_zero]
      exact mul_ne_zero
        (coe_thetaP_ne_zero_of_not_infinitesimal p hdu)
        (coe_thetaP_ne_zero_of_not_infinitesimal p hdv) h0
    have hsum : (u + v).1 =
        intToHyperrat (hyperratNum u.1 * hyperratDen v.1 + hyperratDen u.1 * hyperratNum v.1) /
          intToHyperrat (hyperratDen u.1 * hyperratDen v.1) := by
      change u.1 + v.1 = _
      obtain ⟨ru, hru⟩ : ∃ ru : ℕ → ℚ, (ru : ℚ*) = u.1 := by
        induction u.1 using Germ.inductionOn with | _ ru => exact ⟨ru, rfl⟩
      obtain ⟨rv, hrv⟩ : ∃ rv : ℕ → ℚ, (rv : ℚ*) = v.1 := by
        induction v.1 using Germ.inductionOn with | _ rv => exact ⟨rv, rfl⟩
      rw [← hru, ← hrv]
      refine Germ.coe_eq.2 (Eventually.of_forall fun i ↦ ?_)
      have h1 := (ru i).num_div_den.symm
      have h2 := (rv i).num_div_den.symm
      have hdu_nz : ((ru i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (ru i).den_nz
      have hdv_nz : ((rv i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (rv i).den_nz
      change ru i + rv i =
        (((ru i).num * ((rv i).den : ℤ) + ((ru i).den : ℤ) * (rv i).num : ℤ) : ℚ) /
          ((((ru i).den : ℤ) * ((rv i).den : ℤ) : ℤ) : ℚ)
      push_cast
      rw [← div_add_div ((ru i).num : ℚ) ((rv i).num : ℚ) hdu_nz hdv_nz, ← h1, ← h2]
    rw [thetaPQFun_eq_div p (u + v) hduv hsum]
    change _ = thetaPQFun p u + thetaPQFun p v
    unfold thetaPQFun
    rw [div_add_div _ _
        (coe_thetaP_ne_zero_of_not_infinitesimal p hdu)
        (coe_thetaP_ne_zero_of_not_infinitesimal p hdv)]
    congr 1 <;> simp [map_add, map_mul]

/-- `thetaPQ p` fixes standard rationals (`thetaPQ p ⟨r, _⟩ = (r : ℚ_[p])`). -/
@[simp]
theorem thetaPQ_ratCast (p : ℕ) [Fact p.Prime] (r : ℚ) :
    thetaPQ p ⟨Germ.const r, isLimited_coe ‖(r : ℚ_[p])‖⟩ = (r : ℚ_[p]) := by
  change thetaPQFun p ⟨Germ.const r, _⟩ = (r : ℚ_[p])
  unfold thetaPQFun
  have hnum : hyperratNum (Germ.const r : ℚ*) = (r.num : ℤ*) := rfl
  have hden : hyperratDen (Germ.const r : ℚ*) = ((r.den : ℤ) : ℤ*) := rfl
  rw [hnum, hden, thetaP_intCast, thetaP_intCast, map_intCast, map_intCast, Int.cast_natCast]
  symm
  simpa using congrArg (Rat.cast : ℚ → ℚ_[p]) r.num_div_den.symm

/-- Surjectivity of `thetaPQ p : PadicLimitedSubringQ p →+* ℚ_[p]` (Goldblatt §18.5, p. 243). -/
theorem thetaPQ_surjective (p : ℕ) [Fact p.Prime] :
    Function.Surjective (thetaPQ p) := by
  intro q
  obtain ⟨a, b, hb_mem, hab⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) q
  have hb_ne : b ≠ 0 := nonZeroDivisors.ne_zero hb_mem
  obtain ⟨x, hx⟩ := thetaP_surjective p a
  obtain ⟨y, hy⟩ := thetaP_surjective p b
  have hy_not_inf : ¬ IsPadicInfinitesimalZ p y := by
    intro hinf
    have hm : y ∈ RingHom.ker (thetaP p) := by
      rwa [ker_thetaP, mem_padicInfinitesimalIdealZ_iff]
    exact hb_ne (hy ▸ RingHom.mem_ker.1 hm)
  have hlim : IsPadicLimitedQ p (intToHyperrat x / intToHyperrat y) :=
    (eventually_ne_zero_and_limited_div_of_not_padicInfinitesimalZ p x hy_not_inf).2.2
  refine ⟨⟨intToHyperrat x / intToHyperrat y, hlim⟩, ?_⟩
  change thetaPQFun p _ = q
  rw [thetaPQFun_eq_div p _ hy_not_inf rfl, hx, hy, hab]

/-- Norm preservation `shadow (starPadicNormQ p v.1) = ‖thetaPQ p v‖` for all
`v ∈ PadicLimitedSubringQ p` (Goldblatt §18.5, p. 244). -/
@[simp]
theorem shadow_starPadicNormQ (p : ℕ) [Fact p.Prime] (v : PadicLimitedSubringQ p) :
    shadow (starPadicNormQ p v.1) = ‖thetaPQ p v‖ := by
  have hden_not_inf : ¬ IsPadicInfinitesimalZ p (hyperratDen v.1) :=
    (isPadicLimitedQ_iff_not_infinitesimal_den p v.1).1.1 ((mem_padicLimitedSubringQ_iff p).1 v.2)
  have hden_sh_ne : shadow (starPadicNormZ p (hyperratDen v.1)) ≠ 0 := by
    rw [shadow_starPadicNormZ, norm_ne_zero_iff]
    intro h0
    exact coe_thetaP_ne_zero_of_not_infinitesimal p hden_not_inf (by simp [h0])
  have hmul_norm : starPadicNormQ p v.1 * starPadicNormZ p (hyperratDen v.1) =
      starPadicNormZ p (hyperratNum v.1) := by
    rw [← starPadicNormQ_intToHyperrat p (hyperratDen v.1),
        ← starPadicNormQ_intToHyperrat p (hyperratNum v.1),
        ← starPadicNormQ_mul]
    congr 1
    calc v.1 * intToHyperrat (hyperratDen v.1)
        = (intToHyperrat (hyperratNum v.1) / intToHyperrat (hyperratDen v.1)) *
            intToHyperrat (hyperratDen v.1) := by rw [intToHyperrat_num_div_den]
      _ = intToHyperrat (hyperratNum v.1) := by
          obtain ⟨r, hr⟩ : ∃ r : ℕ → ℚ, (r : ℚ*) = v.1 := by
            induction v.1 using Germ.inductionOn with | _ r => exact ⟨r, rfl⟩
          rw [← hr]
          exact Germ.coe_eq.2 (Eventually.of_forall fun i ↦
            div_mul_cancel₀ _ (Nat.cast_ne_zero.2 (r i).den_nz))
  have hsh_mul : shadow (starPadicNormQ p v.1) =
      shadow (starPadicNormZ p (hyperratNum v.1)) /
        shadow (starPadicNormZ p (hyperratDen v.1)) := by
    rw [eq_div_iff hden_sh_ne,
        ← shadow_mul ((mem_padicLimitedSubringQ_iff p).1 v.2)
          (starPadicNormZ_isLimited p (hyperratDen v.1)),
        hmul_norm]
  rw [hsh_mul, shadow_starPadicNormZ, shadow_starPadicNormZ]
  change _ = ‖algebraMap ℤ_[p] ℚ_[p] (thetaP p (hyperratNum v.1)) /
    algebraMap ℤ_[p] ℚ_[p] (thetaP p (hyperratDen v.1))‖
  rw [norm_div]
  rfl

/-- Kernel of `thetaPQ p` is `PadicInfinitesimalIdealQ p` (`ℚ_{p,𝕀}`, Goldblatt §18.5, p. 243). -/
theorem ker_thetaPQ (p : ℕ) [Fact p.Prime] :
    RingHom.ker (thetaPQ p) = PadicInfinitesimalIdealQ p := by
  ext v
  rw [RingHom.mem_ker, mem_padicInfinitesimalIdealQ_iff, IsPadicInfinitesimalQ,
      ← shadow_eq_zero_iff_isInfinitesimal ((mem_padicLimitedSubringQ_iff p).1 v.2),
      shadow_starPadicNormQ, norm_eq_zero]

/-- Goldblatt §18.5 (p. 243): **Fundamental Ring Isomorphism
`(PadicLimitedSubringQ p ⧸ PadicInfinitesimalIdealQ p) ≃+* ℚ_[p]`** (`ℚ_{p,𝕃} ⧸ ℚ_{p,𝕀} ≅ ℚ_[p]`). -/
noncomputable def hyperratQuotientEquivPadic (p : ℕ) [Fact p.Prime] :
    (PadicLimitedSubringQ p ⧸ PadicInfinitesimalIdealQ p) ≃+* ℚ_[p] :=
  (Ideal.quotEquivOfEq (ker_thetaPQ p).symm).trans
    (RingHom.quotientKerEquivOfSurjective (thetaPQ_surjective p))

/-- Goldblatt §18.5 (p. 243): `PadicInfinitesimalIdealQ p` (`ℚ_{p,𝕀}`) is a **maximal ideal** of
`PadicLimitedSubringQ p` (`ℚ_{p,𝕃}`), since `ℚ_[p]` is a field! -/
instance instIsMaximalPadicInfinitesimalIdealQ (p : ℕ) [Fact p.Prime] :
    (PadicInfinitesimalIdealQ p).IsMaximal := by
  refine Ideal.Quotient.maximal_of_isField _ ⟨⟨0, 1, ?_⟩, mul_comm, ?_⟩
  · intro h01
    have := congrArg (hyperratQuotientEquivPadic p) h01
    simp at this
  · intro x hx
    let e := hyperratQuotientEquivPadic p
    have hex : e x ≠ 0 := (map_ne_zero_iff e e.injective).2 hx
    refine ⟨e.symm (e x)⁻¹, e.injective ?_⟩
    simp [map_mul, mul_inv_cancel₀ hex]

/-- Type wrapper `PadicQ p` equipping `ℚ` with the $p$-adic metric `d_p(q, r) = ‖(q - r : ℚ_[p])‖`
(Goldblatt §18.5, p. 242). -/
structure PadicQ (p : ℕ) where
  /-- Underlying rational number. -/
  val : ℚ

/-- $p$-adic `MetricSpace` structure on `PadicQ p`. -/
noncomputable instance instMetricSpacePadicQ (p : ℕ) [Fact p.Prime] :
    MetricSpace (PadicQ p) where
  dist a b := ‖((a.val - b.val : ℚ) : ℚ_[p])‖
  dist_self a := by simp
  dist_comm a b := by
    have hneg : ((a.val - b.val : ℚ) : ℚ_[p]) = -((b.val - a.val : ℚ) : ℚ_[p]) := by
      push_cast; ring
    rw [hneg, norm_neg]
  dist_triangle a b c := by
    have hadd : ((a.val - c.val : ℚ) : ℚ_[p]) =
        ((a.val - b.val : ℚ) : ℚ_[p]) + ((b.val - c.val : ℚ) : ℚ_[p]) := by
      push_cast; ring
    rw [hadd]
    exact norm_add_le _ _
  eq_of_dist_eq_zero {a b} h := by
    have h0 : ((a.val - b.val : ℚ) : ℚ_[p]) = 0 := norm_eq_zero.1 h
    have hab : a.val - b.val = 0 := Rat.cast_injective h0
    cases a; cases b
    congr
    exact sub_eq_zero.1 hab

/-- Equivalence `StarMetric (PadicQ p) ≃ ℚ*`. -/
def starPadicQEquiv (p : ℕ) : StarMetric (PadicQ p) ≃ ℚ* where
  toFun := Germ.map PadicQ.val
  invFun := Germ.map PadicQ.mk
  left_inv x := Germ.inductionOn x fun _ ↦ rfl
  right_inv x := Germ.inductionOn x fun _ ↦ rfl

/-- Compatibility of `starDist` on `PadicQ p` with `starPadicNormQ`. -/
theorem starDist_padicQ_eq (p : ℕ) [Fact p.Prime] (x y : StarMetric (PadicQ p)) :
    starDist x y = starPadicNormQ p (starPadicQEquiv p x - starPadicQEquiv p y) :=
  Germ.inductionOn₂ x y fun _ _ ↦ rfl

/-- Identification `x ∈ LimitedMetric (PadicQ p) ⟨0⟩ ↔ starPadicQEquiv p x ∈ PadicLimitedSubringQ p`. -/
theorem mem_limitedMetric_padicQ_iff (p : ℕ) [Fact p.Prime] (x : StarMetric (PadicQ p)) :
    x ∈ LimitedMetric (PadicQ p) ⟨0⟩ ↔ starPadicQEquiv p x ∈ PadicLimitedSubringQ p := by
  change IsLimited (starDist x (Germ.const ⟨0⟩)) ↔ IsLimited (starPadicNormQ p (starPadicQEquiv p x))
  rw [starDist_padicQ_eq]
  have h0 : starPadicQEquiv p (Germ.const ⟨0⟩) = 0 := rfl
  rw [h0, sub_zero]

/-- Goldblatt §18.5 (p. 244): **Every $p$-adically limited hyperrational is approachable from `ℚ`**
(`LimitedMetric (PadicQ p) ⟨0⟩ = PreNearstandard (PadicQ p)`), so the nonstandard hull of `(ℚ, d_p)`
coincides with its completion `ℚ_[p]`! -/
theorem limitedMetric_padicQ_eq_preNearstandard (p : ℕ) [Fact p.Prime] :
    LimitedMetric (PadicQ p) ⟨0⟩ = PreNearstandard (PadicQ p) := by
  ext x
  refine ⟨fun hx ε hε ↦ ?_,
    fun hx ↦ preNearstandard_subset_limitedMetric (M := PadicQ p) ⟨0⟩ hx⟩
  let v : PadicLimitedSubringQ p := ⟨starPadicQEquiv p x, (mem_limitedMetric_padicQ_iff p x).1 hx⟩
  obtain ⟨r, hr⟩ := Padic.rat_dense p (thetaPQ p v) (half_pos hε)
  refine ⟨⟨r⟩, ?_⟩
  rw [starDist_padicQ_eq]
  have hconst : starPadicQEquiv p (Germ.const ⟨r⟩) = Germ.const r := rfl
  rw [hconst]
  let r_sub : PadicLimitedSubringQ p := ⟨Germ.const r, isLimited_coe ‖(r : ℚ_[p])‖⟩
  have hw_lim : IsLimited (starPadicNormQ p (v - r_sub).1) :=
    (mem_padicLimitedSubringQ_iff p).1 (v - r_sub).2
  have hsh : shadow (starPadicNormQ p (v - r_sub).1) < ε / 2 := by
    rw [shadow_starPadicNormQ, map_sub, thetaPQ_ratCast]
    exact hr
  have hclose := infClose_shadow hw_lim (ε / 2) (half_pos hε)
  change starPadicNormQ p (v - r_sub).1 < (ε : ℝ*)
  set d : ℝ* := starPadicNormQ p (v - r_sub).1
  set s : ℝ := shadow d
  have hlt1 : d < (s : ℝ*) + ((ε / 2 : ℝ) : ℝ*) := by
    have hupper : d - (s : ℝ*) < ((ε / 2 : ℝ) : ℝ*) := (abs_lt.1 hclose).2
    simpa [add_comm] using sub_lt_iff_lt_add.1 hupper
  have hlt2 : s + ε / 2 < ε := by linarith
  exact hlt1.trans (by rw [← Hyperreal.coe_add]; exact Hyperreal.coe_lt_coe.2 hlt2)

/-- Goldblatt §18.5 (p. 244): **Isometric Equivalence `MetricHull (PadicQ p) ⟨0⟩ ≃ᵢ ℚ_[p]`**
identifying the nonstandard metric hull of `(ℚ, d_p)` with `ℚ_[p]`. -/
noncomputable def padicQMetricHullEquiv (p : ℕ) [Fact p.Prime] :
    MetricHull (PadicQ p) ⟨0⟩ ≃ᵢ ℚ_[p] := by
  let φ : MetricHull (PadicQ p) ⟨0⟩ → ℚ_[p] :=
    Quotient.lift
      (fun a : LimitedMetric (PadicQ p) ⟨0⟩ ↦
        thetaPQ p ⟨starPadicQEquiv p a.1, (mem_limitedMetric_padicQ_iff p a.1).1 a.2⟩)
      fun a b hab ↦ by
        let va : PadicLimitedSubringQ p :=
          ⟨starPadicQEquiv p a.1, (mem_limitedMetric_padicQ_iff p a.1).1 a.2⟩
        let vb : PadicLimitedSubringQ p :=
          ⟨starPadicQEquiv p b.1, (mem_limitedMetric_padicQ_iff p b.1).1 b.2⟩
        have hinf : IsPadicInfinitesimalQ p (va - vb).1 := by
          unfold IsPadicInfinitesimalQ
          change IsInfinitesimal (starPadicNormQ p (starPadicQEquiv p a.1 - starPadicQEquiv p b.1))
          rw [← starDist_padicQ_eq]
          exact hab
        have hker : va - vb ∈ RingHom.ker (thetaPQ p) := by
          rwa [ker_thetaPQ, mem_padicInfinitesimalIdealQ_iff]
        rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hker
        exact hker
  have hφ_iso : Isometry φ := Isometry.of_dist_eq fun x y ↦
    Quotient.inductionOn₂ x y fun a b ↦ by
      let va : PadicLimitedSubringQ p :=
        ⟨starPadicQEquiv p a.1, (mem_limitedMetric_padicQ_iff p a.1).1 a.2⟩
      let vb : PadicLimitedSubringQ p :=
        ⟨starPadicQEquiv p b.1, (mem_limitedMetric_padicQ_iff p b.1).1 b.2⟩
      change ‖thetaPQ p va - thetaPQ p vb‖ = shadow (starDist a.1 b.1)
      rw [← map_sub, ← shadow_starPadicNormQ, starDist_padicQ_eq]
      rfl
  have hφ_surj : Function.Surjective φ := fun q ↦ by
    obtain ⟨v, hv⟩ := thetaPQ_surjective p q
    have hlim : (starPadicQEquiv p).symm v.1 ∈ LimitedMetric (PadicQ p) ⟨0⟩ := by
      rw [mem_limitedMetric_padicQ_iff, Equiv.apply_symm_apply]
      exact v.2
    exact ⟨Quotient.mk (limitedMetricSetoid (PadicQ p) ⟨0⟩) ⟨(starPadicQEquiv p).symm v.1, hlim⟩,
      by simpa [φ] using hv⟩
  exact { toEquiv := Equiv.ofBijective φ ⟨hφ_iso.injective, hφ_surj⟩
          isometry_toFun := hφ_iso }

/-!
## §18.6 Formal Power Series via Hyperpolynomials (Goldblatt pp. 249–254)

Given any commutative ring `R`, we equip `Polynomial R` (`R[X]`) and `PowerSeries R` (`R⟦X⟧`) with
the $X$-adic order `ord_X(a) ∈ ℕ∞` and ultrametric norm `|a|_X = 2^{-ord_X(a)}` (`0` when `a = 0`).
In the ultrapower `HyperPoly R = Germ (hyperfilter ℕ) (Polynomial R)` (`*R[X]`):

1. Every hyperpolynomial has internal hyperdegree `N ∈ ℕ*` beyond which all internal coefficients
   vanish (`exists_bound_internalCoeff_eq_zero`), and `(StarRing R)[X]` embeds injectively into
   `HyperPoly R` (`polyStarRingToHyperPoly_injective`) — strictly when `Nontrivial R`
   (`not_surjective_polyStarRingToHyperPoly`, witnessed by `[n ↦ X^n]`).
2. **Theorem 18.6.1** (`mem_preNearstandard_adicPoly_iff`): `P ∈ *R[X]` is approachable from `R[X]`
   if and only if every standard-degree coefficient `hyperCoeff n P` belongs to `R` (the range of
   `Germ.const`); when `Infinite R`, there exist limited hyperpolynomials that are **not**
   approachable (`exists_limited_not_preNearstandard_adicPoly_of_infinite`), whereas when `Finite R`
   all hyperpolynomials are approachable (`preNearstandard_adicPoly_eq_univ_of_finite`).
3. **Theorem 18.6.2** (`isXAdicInfinitesimal_tfae`) and **Corollary 18.6.3**
   (`starPolyXNorm_sub_infinitesimal_iff`): 4-way equivalence characterizing $X$-adic infinitesimals
   `I_X` (`|P|_X ≈ 0` ↔ unlimited order ↔ `∀ k : ℕ, X^k ∣ P` ↔ `∀ n : ℕ, hyperCoeff n P = 0`).
4. **Quotient Isomorphisms & Completion**:
   - `(HyperPoly R ⧸ XAdicIdeal R) ≃+* PowerSeries (StarRing R)`
     (`hyperPolyQuotientEquivPowerSeriesStar`),
   - `(ApproachableHyperPoly R ⧸ ApproachableInfinitesimalIdeal R) ≃+* PowerSeries R`
     (`approachableHyperPolyQuotientEquivPowerSeries`, with hyperfinite truncations `truncHyperPoly`),
   - `(LimitedCoeffHyperPoly ⧸ InfinitesimalCoeffHyperPoly) ≃+* PowerSeries ℝ`
     (`limitedCoeffHyperPolyQuotientEquivRealPowerSeries`),
   - **Exercise 18.6.4** (`exercise_18_6_4` and subring/ideal strict inclusions), and
   - Isometric completion equivalence `MetricCompletion (AdicPoly R) ≃ᵢ AdicPowerSeries R`
     (`adicPolyCompletionEquivPowerSeries`), establishing `CompleteSpace (AdicPowerSeries R)`.
-/

/-- $X$-adic valuation-to-norm conversion `ℕ∞ → ℝ` sending `⊤ ↦ 0` and `(n : ℕ) ↦ 2 ^ (-n)`
(Goldblatt §18.6, p. 251). -/
noncomputable def xAdicValNorm (e : ℕ∞) : ℝ :=
  if e = ⊤ then 0 else (2 : ℝ) ^ (-(e.toNat : ℤ))

/-- `xAdicValNorm ⊤ = 0`. -/
@[simp]
theorem xAdicValNorm_top : xAdicValNorm ⊤ = 0 :=
  rfl

/-- `xAdicValNorm (n : ℕ∞) = 2 ^ (-n)` for finite `n : ℕ`. -/
@[simp]
theorem xAdicValNorm_nat (n : ℕ) : xAdicValNorm (n : ℕ∞) = (2 : ℝ) ^ (-(n : ℤ)) := by
  simp [xAdicValNorm]

/-- `xAdicValNorm e ≥ 0` for all `e : ℕ∞`. -/
theorem xAdicValNorm_nonneg (e : ℕ∞) : 0 ≤ xAdicValNorm e := by
  unfold xAdicValNorm
  split_ifs
  · exact le_rfl
  · exact zpow_nonneg (by norm_num) _

/-- `xAdicValNorm e ≤ 1` for all `e : ℕ∞` (Goldblatt §18.6, p. 252). -/
theorem xAdicValNorm_le_one (e : ℕ∞) : xAdicValNorm e ≤ 1 := by
  unfold xAdicValNorm
  split_ifs
  · norm_num
  · exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)

/-- `xAdicValNorm e = 0 ↔ e = ⊤`. -/
@[simp]
theorem xAdicValNorm_eq_zero_iff (e : ℕ∞) : xAdicValNorm e = 0 ↔ e = ⊤ := by
  unfold xAdicValNorm
  split_ifs with h
  · simp [h]
  · simp [h]

/-- `xAdicValNorm` is strictly antitone on `ℕ∞`. -/
theorem xAdicValNorm_strictAnti : StrictAnti xAdicValNorm := by
  intro a b hab
  induction a using ENat.recTopCoe with
  | top => exact absurd hab (not_lt_of_ge le_top)
  | coe m =>
    induction b using ENat.recTopCoe with
    | top =>
      rw [xAdicValNorm_top, xAdicValNorm_nat]
      exact zpow_pos (by norm_num) _
    | coe n =>
      rw [xAdicValNorm_nat, xAdicValNorm_nat]
      have hmn : m < n := Nat.cast_lt.1 hab
      exact zpow_lt_zpow_right₀ (by norm_num) (by omega)

/-- Exact threshold characterization `xAdicValNorm e ≤ 2 ^ (-n) ↔ (n : ℕ∞) ≤ e`. -/
theorem xAdicValNorm_le_zpow_iff (e : ℕ∞) (n : ℕ) :
    xAdicValNorm e ≤ (2 : ℝ) ^ (-(n : ℤ)) ↔ (n : ℕ∞) ≤ e := by
  rw [← xAdicValNorm_nat n]
  exact xAdicValNorm_strictAnti.le_iff_ge

/-- Strict threshold characterization `xAdicValNorm e < 2 ^ (-n) ↔ (n : ℕ∞) < e`. -/
theorem xAdicValNorm_lt_zpow_iff (e : ℕ∞) (n : ℕ) :
    xAdicValNorm e < (2 : ℝ) ^ (-(n : ℤ)) ↔ (n : ℕ∞) < e := by
  rw [← xAdicValNorm_nat n]
  exact xAdicValNorm_strictAnti.lt_iff_gt

/-- Helper lemma: for any `ε > 0` in `ℝ`, there exists `n : ℕ` with `2 ^ (-n) < ε`. -/
theorem exists_two_zpow_neg_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, (2 : ℝ) ^ (-(n : ℤ)) < ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2⁻¹ : ℝ) < 1)
  refine ⟨n, ?_⟩
  simpa [zpow_neg, zpow_natCast, inv_pow] using hn

/-- $X$-adic norm `|φ|_X = 2 ^ (-ord_X(φ))` on `PowerSeries R` (Goldblatt §18.6, p. 251). -/
noncomputable def powerSeriesXNorm (R : Type*) [CommRing R] (φ : PowerSeries R) : ℝ :=
  xAdicValNorm φ.order

/-- Negation preserves `PowerSeries.order`. -/
@[simp]
theorem powerSeries_order_neg {R : Type*} [CommRing R] (φ : PowerSeries R) :
    (-φ).order = φ.order := by
  have hle : ∀ ψ : PowerSeries R, ψ.order ≤ (-ψ).order := fun ψ ↦
    PowerSeries.le_order (-ψ) ψ.order fun i hi ↦ by simp [PowerSeries.coeff_of_lt_order i hi]
  have h1 := hle (-φ)
  rw [neg_neg] at h1
  exact le_antisymm h1 (hle φ)

/-- Negation preserves `powerSeriesXNorm`. -/
@[simp]
theorem powerSeriesXNorm_neg {R : Type*} [CommRing R] (φ : PowerSeries R) :
    powerSeriesXNorm R (-φ) = powerSeriesXNorm R φ := by
  simp [powerSeriesXNorm]

/-- `powerSeriesXNorm R φ = 0 ↔ φ = 0`. -/
@[simp]
theorem powerSeriesXNorm_eq_zero_iff {R : Type*} [CommRing R] (φ : PowerSeries R) :
    powerSeriesXNorm R φ = 0 ↔ φ = 0 := by
  rw [powerSeriesXNorm, xAdicValNorm_eq_zero_iff, PowerSeries.order_eq_top]

/-- Strong ultrametric inequality `|φ + ψ|_X ≤ max (|φ|_X) (|ψ|_X)` on `PowerSeries R`
(Goldblatt §18.6, p. 251). -/
theorem powerSeriesXNorm_add_le_max {R : Type*} [CommRing R] (φ ψ : PowerSeries R) :
    powerSeriesXNorm R (φ + ψ) ≤ max (powerSeriesXNorm R φ) (powerSeriesXNorm R ψ) := by
  have hanti := xAdicValNorm_strictAnti.antitone (PowerSeries.min_order_le_order_add φ ψ)
  rcases le_total φ.order ψ.order with h | h
  · rw [min_eq_left h] at hanti
    exact hanti.trans (le_max_left _ _)
  · rw [min_eq_right h] at hanti
    exact hanti.trans (le_max_right _ _)

/-- $X$-adic order `ord_X(f) ∈ ℕ∞` of a polynomial `f : Polynomial R` (Goldblatt §18.6, p. 250). -/
noncomputable def polyXOrder (R : Type*) [CommRing R] (f : Polynomial R) : ℕ∞ :=
  (f : PowerSeries R).order

/-- $X$-adic norm `|f|_X = 2 ^ (-ord_X(f))` of a polynomial `f : Polynomial R`
(Goldblatt §18.6, p. 251). -/
noncomputable def polyXNorm (R : Type*) [CommRing R] (f : Polynomial R) : ℝ :=
  xAdicValNorm (polyXOrder R f)

/-- Compatibility `polyXNorm R f = powerSeriesXNorm R (f : PowerSeries R)`. -/
@[simp]
theorem polyXNorm_eq_powerSeriesXNorm {R : Type*} [CommRing R] (f : Polynomial R) :
    polyXNorm R f = powerSeriesXNorm R (f : PowerSeries R) :=
  rfl

/-- `(n : ℕ∞) ≤ polyXOrder R f ↔ ∀ d < n, f.coeff d = 0` ↔ `X ^ n ∣ f` (Goldblatt §18.6, p. 250). -/
theorem nat_le_polyXOrder_iff {R : Type*} [CommRing R] (f : Polynomial R) (n : ℕ) :
    ((n : ℕ∞) ≤ polyXOrder R f ↔ ∀ d < n, f.coeff d = 0) ∧
    ((n : ℕ∞) ≤ polyXOrder R f ↔ (Polynomial.X : Polynomial R) ^ n ∣ f) := by
  have h1 : (n : ℕ∞) ≤ polyXOrder R f ↔ ∀ d < n, f.coeff d = 0 := by
    rw [polyXOrder, PowerSeries.nat_le_order_iff]
    simp [Polynomial.coeff_coe]
  exact ⟨h1, h1.trans Polynomial.X_pow_dvd_iff.symm⟩

/-- `polyXNorm R f ≤ 2 ^ (-n) ↔ X ^ n ∣ f`. -/
theorem polyXNorm_le_zpow_iff_X_pow_dvd {R : Type*} [CommRing R] (f : Polynomial R) (n : ℕ) :
    polyXNorm R f ≤ (2 : ℝ) ^ (-(n : ℤ)) ↔ (Polynomial.X : Polynomial R) ^ n ∣ f :=
  (xAdicValNorm_le_zpow_iff (polyXOrder R f) n).trans (nat_le_polyXOrder_iff f n).2

/-- Type wrapper `AdicPowerSeries R` equipping `PowerSeries R` (`R⟦X⟧`) with the $X$-adic metric
`d(φ, ψ) = |φ - ψ|_X` (Goldblatt §18.6, p. 251). -/
structure AdicPowerSeries (R : Type*) [CommRing R] where
  /-- Underlying formal power series. -/
  val : PowerSeries R

/-- $X$-adic `MetricSpace` structure on `AdicPowerSeries R`. -/
noncomputable instance instMetricSpaceAdicPowerSeries (R : Type*) [CommRing R] :
    MetricSpace (AdicPowerSeries R) where
  dist a b := powerSeriesXNorm R (a.val - b.val)
  dist_self a := by simp
  dist_comm a b := by
    rw [← neg_sub b.val a.val, powerSeriesXNorm_neg]
  dist_triangle a b c := by
    have hadd : a.val - c.val = (a.val - b.val) + (b.val - c.val) := by ring
    rw [hadd]
    refine (powerSeriesXNorm_add_le_max _ _).trans ?_
    exact max_le (le_add_of_nonneg_right (xAdicValNorm_nonneg _))
      (le_add_of_nonneg_left (xAdicValNorm_nonneg _))
  eq_of_dist_eq_zero {a b} h := by
    have h0 : a.val - b.val = 0 := (powerSeriesXNorm_eq_zero_iff _).1 h
    cases a; cases b
    congr
    exact sub_eq_zero.1 h0

/-- Type wrapper `AdicPoly R` equipping `Polynomial R` (`R[X]`) with the $X$-adic metric
`d(f, g) = |f - g|_X` (Goldblatt §18.6, p. 251). -/
structure AdicPoly (R : Type*) [CommRing R] where
  /-- Underlying polynomial. -/
  val : Polynomial R

/-- $X$-adic `MetricSpace` structure on `AdicPoly R`. -/
noncomputable instance instMetricSpaceAdicPoly (R : Type*) [CommRing R] :
    MetricSpace (AdicPoly R) where
  dist a b := polyXNorm R (a.val - b.val)
  dist_self a := by
    change powerSeriesXNorm R ((a.val - a.val : Polynomial R) : PowerSeries R) = 0
    simp
  dist_comm a b := by
    change powerSeriesXNorm R ((a.val - b.val : Polynomial R) : PowerSeries R) =
      powerSeriesXNorm R ((b.val - a.val : Polynomial R) : PowerSeries R)
    have hsub : ((a.val - b.val : Polynomial R) : PowerSeries R) =
        -((b.val - a.val : Polynomial R) : PowerSeries R) := by
      rw [← Polynomial.coeToPowerSeries.ringHom_apply,
          ← Polynomial.coeToPowerSeries.ringHom_apply]
      rw [← map_neg, neg_sub]
    rw [hsub, powerSeriesXNorm_neg]
  dist_triangle a b c := by
    change powerSeriesXNorm R ((a.val - c.val : Polynomial R) : PowerSeries R) ≤
      powerSeriesXNorm R ((a.val - b.val : Polynomial R) : PowerSeries R) +
      powerSeriesXNorm R ((b.val - c.val : Polynomial R) : PowerSeries R)
    have hadd : ((a.val - c.val : Polynomial R) : PowerSeries R) =
        ((a.val - b.val : Polynomial R) : PowerSeries R) +
        ((b.val - c.val : Polynomial R) : PowerSeries R) := by
      rw [← Polynomial.coeToPowerSeries.ringHom_apply,
          ← Polynomial.coeToPowerSeries.ringHom_apply,
          ← Polynomial.coeToPowerSeries.ringHom_apply, ← map_add]
      congr 1; ring
    rw [hadd]
    refine (powerSeriesXNorm_add_le_max _ _).trans ?_
    exact max_le (le_add_of_nonneg_right (xAdicValNorm_nonneg _))
      (le_add_of_nonneg_left (xAdicValNorm_nonneg _))
  eq_of_dist_eq_zero {a b} h := by
    have h0 : ((a.val - b.val : Polynomial R) : PowerSeries R) = 0 :=
      (powerSeriesXNorm_eq_zero_iff _).1 h
    have hab : a.val - b.val = 0 := Polynomial.coe_eq_zero_iff.1 h0
    cases a; cases b
    congr
    exact sub_eq_zero.1 hab

/-- Canonical isometric embedding `adicPolyToPowerSeries R : AdicPoly R → AdicPowerSeries R`
with dense range (`PowerSeries.trunc n φ → φ` in the $X$-adic metric, Goldblatt §18.6, p. 251). -/
def adicPolyToPowerSeries (R : Type*) [CommRing R] (f : AdicPoly R) : AdicPowerSeries R :=
  ⟨(f.val : PowerSeries R)⟩

/-- `adicPolyToPowerSeries R` is an isometry with dense range in `AdicPowerSeries R`. -/
theorem isometry_and_denseRange_adicPolyToPowerSeries (R : Type*) [CommRing R] :
    Isometry (adicPolyToPowerSeries R) ∧ DenseRange (adicPolyToPowerSeries R) := by
  refine ⟨Isometry.of_dist_eq fun a b ↦ ?_, ?_⟩
  · change powerSeriesXNorm R ((a.val : PowerSeries R) - (b.val : PowerSeries R)) =
      powerSeriesXNorm R ((a.val - b.val : Polynomial R) : PowerSeries R)
    rw [← Polynomial.coeToPowerSeries.ringHom_apply (φ := a.val),
        ← Polynomial.coeToPowerSeries.ringHom_apply (φ := b.val),
        ← Polynomial.coeToPowerSeries.ringHom_apply (φ := a.val - b.val), map_sub]
  · rw [Metric.denseRange_iff]
    intro φ ε hε
    obtain ⟨n, hn⟩ := exists_two_zpow_neg_lt hε
    refine ⟨⟨PowerSeries.trunc n φ.val⟩, ?_⟩
    change powerSeriesXNorm R (φ.val - (PowerSeries.trunc n φ.val : PowerSeries R)) < ε
    have hord : (n : ℕ∞) ≤ (φ.val - (PowerSeries.trunc n φ.val : PowerSeries R)).order := by
      rw [PowerSeries.nat_le_order_iff]
      intro d hd
      simp [Polynomial.coeff_coe, PowerSeries.coeff_trunc, hd]
    exact ((xAdicValNorm_le_zpow_iff _ n).2 hord).trans_lt hn

/-- Ultrapower ring `StarRing R = Germ (hyperfilter ℕ) R` (`*R`, Goldblatt §18.6, p. 251). -/
abbrev StarRing (R : Type*) :=
  Germ (hyperfilter ℕ : Filter ℕ) R

/-- Ultrapower ring of hyperpolynomials `HyperPoly R = Germ (hyperfilter ℕ) (Polynomial R)` (`*R[X]`,
Goldblatt §18.6, p. 251). -/
abbrev HyperPoly (R : Type*) [CommRing R] :=
  Germ (hyperfilter ℕ : Filter ℕ) (Polynomial R)

/-- Helper lemma: finite sums in `StarRing R` commute with sequence representatives. -/
theorem starRing_finset_sum {R α : Type*} [CommRing R] (s : Finset α) (F : α → ℕ → R) :
    (∑ a ∈ s, (F a : StarRing R)) = (((fun i ↦ ∑ a ∈ s, F a i) : ℕ → R) : StarRing R) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha, ih]
    rfl

/-- Additive homomorphism `hyperCoeff n : HyperPoly R →+ StarRing R` extracting the `n`-th
coefficient of standard degree `n : ℕ` (Goldblatt §18.6, p. 251). -/
def hyperCoeff {R : Type*} [CommRing R] (n : ℕ) : HyperPoly R →+ StarRing R where
  toFun := Germ.map (fun f : Polynomial R ↦ f.coeff n)
  map_zero' := Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ Polynomial.coeff_zero n)
  map_add' P Q := Germ.inductionOn₂ P Q fun u v ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun i ↦ Polynomial.coeff_add (u i) (v i) n

/-- Evaluation of `hyperCoeff n` on a sequence representative `(u : HyperPoly R)`. -/
@[simp]
theorem hyperCoeff_coe {R : Type*} [CommRing R] (n : ℕ) (u : ℕ → Polynomial R) :
    hyperCoeff n (u : HyperPoly R) = (((fun i ↦ (u i).coeff n) : ℕ → R) : StarRing R) :=
  rfl

/-- Evaluation of `hyperCoeff n` on a standard polynomial `Germ.const f`. -/
@[simp]
theorem hyperCoeff_const {R : Type*} [CommRing R] (n : ℕ) (f : Polynomial R) :
    hyperCoeff n (Germ.const f : HyperPoly R) = (Germ.const (f.coeff n) : StarRing R) :=
  rfl

/-- Cauchy product formula for hyperpolynomial coefficients of standard degree `n : ℕ`
(Goldblatt §18.6, p. 254). -/
theorem hyperCoeff_mul {R : Type*} [CommRing R] (n : ℕ) (P Q : HyperPoly R) :
    hyperCoeff n (P * Q) =
      ∑ ij ∈ Finset.antidiagonal n, hyperCoeff ij.1 P * hyperCoeff ij.2 Q := by
  induction P using Germ.inductionOn with | _ u =>
  induction Q using Germ.inductionOn with | _ v =>
  have hmul : ∀ ij : ℕ × ℕ,
      hyperCoeff ij.1 (u : HyperPoly R) * hyperCoeff ij.2 (v : HyperPoly R) =
        (((fun i ↦ (u i).coeff ij.1 * (v i).coeff ij.2) : ℕ → R) : StarRing R) :=
    fun _ ↦ rfl
  simp only [hmul, starRing_finset_sum]
  exact Germ.coe_eq.2 (Eventually.of_forall fun i ↦ Polynomial.coeff_mul (u i) (v i) n)

/-- Internal coefficient extraction `internalCoeff P k : StarRing R` at any hypernatural index
`k : ℕ*` (Goldblatt §18.6, p. 251). -/
def internalCoeff {R : Type*} [CommRing R] (P : HyperPoly R) (k : ℕ*) : StarRing R :=
  Germ.map₂ (fun (f : Polynomial R) (m : ℕ) ↦ f.coeff m) P k

/-- `internalCoeff P (n : ℕ*)` agrees with `hyperCoeff n P` for every standard `n : ℕ`. -/
@[simp]
theorem internalCoeff_natCast {R : Type*} [CommRing R] (P : HyperPoly R) (n : ℕ) :
    internalCoeff P (n : ℕ*) = hyperCoeff n P :=
  Germ.inductionOn P fun _ ↦ rfl

/-- Internal hyperdegree `hyperNatDegree P : ℕ*` lifted from `Polynomial.natDegree`
(Goldblatt §18.6, p. 251). -/
def hyperNatDegree {R : Type*} [CommRing R] (P : HyperPoly R) : ℕ* :=
  Germ.map (fun f : Polynomial R ↦ f.natDegree) P

/-- Goldblatt §18.6 (p. 251): **Transfer of Eventual Vanishing** — every hyperpolynomial
`P ∈ HyperPoly R` has an internal bound `N ∈ ℕ*` (`hyperNatDegree P`) beyond which all internal
coefficients vanish (`∀ k : ℕ*, N < k → internalCoeff P k = 0`). -/
theorem exists_bound_internalCoeff_eq_zero {R : Type*} [CommRing R] (P : HyperPoly R) :
    ∃ N : ℕ*, ∀ k : ℕ*, N < k → internalCoeff P k = 0 := by
  refine ⟨hyperNatDegree P, fun k hk ↦ ?_⟩
  induction P using Germ.inductionOn with | _ u =>
  induction k using Germ.inductionOn with | _ m =>
  exact Germ.coe_eq.2 ((Germ.coe_lt.1 hk).mono fun i hi ↦
    Polynomial.coeff_eq_zero_of_natDegree_lt hi)

/-- Canonical ring homomorphism `polyStarRingToHyperPoly R : Polynomial (StarRing R) →+* HyperPoly R`
sending `∑_{k=0}^m a_k X^k ∈ (*R)[X]` to the corresponding hyperpolynomial in `*R[X]`
(Goldblatt §18.6, pp. 251–252). -/
noncomputable def polyStarRingToHyperPoly (R : Type*) [CommRing R] :
    Polynomial (StarRing R) →+* HyperPoly R :=
  Polynomial.eval₂RingHom (germMapRingHom Polynomial.C) (Germ.const Polynomial.X)

/-- `polyStarRingToHyperPoly R` preserves every standard-degree coefficient:
`hyperCoeff n (polyStarRingToHyperPoly R Q) = Q.coeff n`. -/
@[simp]
theorem hyperCoeff_polyStarRingToHyperPoly {R : Type*} [CommRing R]
    (Q : Polynomial (StarRing R)) (n : ℕ) :
    hyperCoeff n (polyStarRingToHyperPoly R Q) = Q.coeff n := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, Polynomial.coeff_add, hp, hq]
  | monomial k a =>
    unfold polyStarRingToHyperPoly
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
    induction a using Germ.inductionOn with | _ c =>
    have hpow : (Germ.const (Polynomial.X : Polynomial R) : HyperPoly R) ^ k =
        (Germ.const ((Polynomial.X : Polynomial R) ^ k) : HyperPoly R) := by
      induction k with
      | zero => rfl
      | succ m ihm => rw [pow_succ, pow_succ, ihm]; rfl
    rw [hpow]
    change (((fun i ↦ (Polynomial.C (c i) * Polynomial.X ^ k).coeff n) : ℕ → R) : StarRing R) =
      (Polynomial.monomial k (c : StarRing R)).coeff n
    rw [Polynomial.coeff_monomial]
    split_ifs with hkn
    · subst hkn
      exact Germ.coe_eq.2 (Eventually.of_forall fun i ↦ by simp)
    · exact Germ.coe_eq.2 (Eventually.of_forall fun i ↦ by
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hkn])

/-- Goldblatt §18.6 (p. 251): `polyStarRingToHyperPoly R : (StarRing R)[X] →+* HyperPoly R` is
**injective**. -/
theorem polyStarRingToHyperPoly_injective (R : Type*) [CommRing R] :
    Function.Injective (polyStarRingToHyperPoly R) := by
  intro P Q h
  ext n
  rw [← hyperCoeff_polyStarRingToHyperPoly P n, ← hyperCoeff_polyStarRingToHyperPoly Q n, h]

/-- Goldblatt §18.6 (p. 251): When `Nontrivial R`, `polyStarRingToHyperPoly R` is **not** surjective
(witnessed by `X ^ ω = [i ↦ X ^ i] ∈ *R[X]`, which has Unlimited hyperdegree and zero standard
coefficients yet is nonzero!). -/
theorem not_surjective_polyStarRingToHyperPoly (R : Type*) [CommRing R] [Nontrivial R] :
    ¬ Function.Surjective (polyStarRingToHyperPoly R) := by
  intro hsurj
  let P : HyperPoly R := (((fun i : ℕ ↦ (Polynomial.X : Polynomial R) ^ i) : ℕ → Polynomial R) :
    HyperPoly R)
  obtain ⟨Q, hQ⟩ := hsurj P
  have hQ_zero : Q = 0 := by
    ext n
    rw [Polynomial.coeff_zero, ← hyperCoeff_polyStarRingToHyperPoly Q n, hQ]
    change (((fun i : ℕ ↦ ((Polynomial.X : Polynomial R) ^ i).coeff n) : ℕ → R) : StarRing R) = 0
    have hcof_mem : (Set.Iio (n + 1))ᶜ ∈ (hyperfilter ℕ : Filter ℕ) :=
      Filter.hyperfilter_le_cofinite (Set.finite_Iio (n + 1)).compl_mem_cofinite
    refine Germ.coe_eq.2 (Filter.Eventually.mono hcof_mem fun i hi ↦ ?_)
    rw [Set.mem_Iio, not_lt] at hi
    have hne : n ≠ i := by omega
    simp [Polynomial.coeff_X_pow, hne]
  have hP_zero : P = 0 := by rw [← hQ, hQ_zero, map_zero]
  have hev_zero : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (Polynomial.X : Polynomial R) ^ i = 0 :=
    Germ.coe_eq.1 hP_zero
  obtain ⟨i, hi⟩ := hev_zero.exists
  have h10 : (1 : R) = 0 := by
    have := congrArg (fun f : Polynomial R ↦ f.coeff i) hi
    simp [Polynomial.coeff_X_pow] at this
  exact one_ne_zero h10

/-- Nonstandard $X$-adic order `starPolyXOrder P : Germ (hyperfilter ℕ) ℕ∞` on `HyperPoly R`
(Goldblatt §18.6, p. 252). -/
noncomputable def starPolyXOrder {R : Type*} [CommRing R] (P : HyperPoly R) :
    Germ (hyperfilter ℕ : Filter ℕ) ℕ∞ :=
  Germ.map (polyXOrder R) P

/-- Nonstandard $X$-adic norm `starPolyXNorm P : ℝ*` on `HyperPoly R` (Goldblatt §18.6, p. 252). -/
noncomputable def starPolyXNorm {R : Type*} [CommRing R] (P : HyperPoly R) : ℝ* :=
  Germ.map (polyXNorm R) P

/-- `0 ≤ starPolyXNorm P` and `starPolyXNorm P ≤ 1`, hence every hyperpolynomial is $X$-adically
limited (`IsLimited (starPolyXNorm P)`, Goldblatt §18.6, p. 252). -/
theorem starPolyXNorm_nonneg_and_le_one {R : Type*} [CommRing R] (P : HyperPoly R) :
    0 ≤ starPolyXNorm P ∧ starPolyXNorm P ≤ 1 ∧ IsLimited (starPolyXNorm P) := by
  have h0 : 0 ≤ starPolyXNorm P :=
    Germ.inductionOn P fun u ↦ Germ.coe_le.2 (Eventually.of_forall fun i ↦ xAdicValNorm_nonneg _)
  have h1 : starPolyXNorm P ≤ 1 :=
    Germ.inductionOn P fun u ↦ Germ.coe_le.2 (Eventually.of_forall fun i ↦ xAdicValNorm_le_one _)
  exact ⟨h0, h1, ⟨2, by rw [abs_of_nonneg h0]; exact h1.trans_lt (by norm_cast)⟩⟩

/-- Threshold characterization `starPolyXNorm P ≤ 2 ^ (-n) ↔ Germ.const (n : ℕ∞) ≤ starPolyXOrder P`. -/
theorem starPolyXNorm_le_zpow_iff {R : Type*} [CommRing R] (P : HyperPoly R) (n : ℕ) :
    starPolyXNorm P ≤ (((2 : ℝ) ^ (-(n : ℤ)) : ℝ) : ℝ*) ↔
      Germ.const (n : ℕ∞) ≤ starPolyXOrder P := by
  induction P using Germ.inductionOn with | _ u =>
  exact Germ.coe_le.trans <|
    (eventually_congr (Eventually.of_forall fun i ↦ xAdicValNorm_le_zpow_iff _ n)).trans
      Germ.coe_le.symm

/-- Strict threshold characterization `starPolyXNorm P < 2 ^ (-n) ↔ Germ.const (n : ℕ∞) < starPolyXOrder P`. -/
theorem starPolyXNorm_lt_zpow_iff {R : Type*} [CommRing R] (P : HyperPoly R) (n : ℕ) :
    starPolyXNorm P < (((2 : ℝ) ^ (-(n : ℤ)) : ℝ) : ℝ*) ↔
      Germ.const (n : ℕ∞) < starPolyXOrder P := by
  induction P using Germ.inductionOn with | _ u =>
  exact Germ.coe_lt.trans <|
    (eventually_congr (Eventually.of_forall fun i ↦ xAdicValNorm_lt_zpow_iff _ n)).trans
      Germ.coe_lt.symm

/-- Equivalence `StarMetric (AdicPoly R) ≃ HyperPoly R`. -/
def starAdicPolyEquiv (R : Type*) [CommRing R] : StarMetric (AdicPoly R) ≃ HyperPoly R where
  toFun := Germ.map AdicPoly.val
  invFun := Germ.map AdicPoly.mk
  left_inv x := Germ.inductionOn x fun _ ↦ rfl
  right_inv x := Germ.inductionOn x fun _ ↦ rfl

/-- Compatibility of `starDist` on `AdicPoly R` with `starPolyXNorm`. -/
theorem starDist_adicPoly_eq (R : Type*) [CommRing R] (x y : StarMetric (AdicPoly R)) :
    starDist x y = starPolyXNorm (starAdicPolyEquiv R x - starAdicPolyEquiv R y) :=
  Germ.inductionOn₂ x y fun _ _ ↦ rfl

/-- Every point of `StarMetric (AdicPoly R)` is limited (`LimitedMetric (AdicPoly R) ⟨0⟩ = Set.univ`,
Goldblatt §18.6, p. 252). -/
theorem limitedMetric_adicPoly_eq_univ (R : Type*) [CommRing R] :
    LimitedMetric (AdicPoly R) ⟨0⟩ = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  change IsLimited (starDist x (Germ.const ⟨0⟩))
  rw [starDist_adicPoly_eq]
  exact (starPolyXNorm_nonneg_and_le_one _).2.2

/-- Goldblatt §18.6, **Theorem 18.6.1** (p. 252): A hyperpolynomial `x ∈ StarMetric (AdicPoly R)`
is **approachable from `R[X]`** (`x ∈ PreNearstandard (AdicPoly R)`) if and only if for every
standard degree `n : ℕ`, the coefficient `hyperCoeff n (starAdicPolyEquiv R x)` belongs to `R`
(`Set.range Germ.const`). -/
theorem mem_preNearstandard_adicPoly_iff (R : Type*) [CommRing R] (x : StarMetric (AdicPoly R)) :
    x ∈ PreNearstandard (AdicPoly R) ↔
      ∀ n : ℕ, hyperCoeff n (starAdicPolyEquiv R x) ∈ Set.range Germ.const := by
  constructor
  · intro hap n
    have hε : (0 : ℝ) < (2 : ℝ) ^ (-(n : ℤ)) := zpow_pos (by norm_num) _
    obtain ⟨b, hb⟩ := hap ((2 : ℝ) ^ (-(n : ℤ))) hε
    rw [starDist_adicPoly_eq] at hb
    have hconst : starAdicPolyEquiv R (Germ.const b) = Germ.const b.val := rfl
    rw [hconst] at hb
    have hord : Germ.const (n : ℕ∞) <
        starPolyXOrder (starAdicPolyEquiv R x - Germ.const b.val) :=
      (starPolyXNorm_lt_zpow_iff _ n).1 hb
    refine ⟨b.val.coeff n, ?_⟩
    generalize starAdicPolyEquiv R x = P at hord ⊢
    induction P using Germ.inductionOn with | _ u =>
    have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
        (n : ℕ∞) < polyXOrder R (u i - b.val) := Germ.coe_lt.1 hord
    refine (Germ.coe_eq.2 (hev.mono fun i hi ↦ ?_)).symm
    have hzero : (u i - b.val).coeff n = 0 := by
      have := PowerSeries.coeff_of_lt_order n (φ := ((u i - b.val : Polynomial R) : PowerSeries R)) hi
      rwa [Polynomial.coeff_coe] at this
    rw [Polynomial.coeff_sub, sub_eq_zero] at hzero
    exact hzero
  · intro hstd ε hε
    obtain ⟨k, hk⟩ := exists_two_zpow_neg_lt hε
    let c : ℕ → R := fun d ↦ (hstd d).choose
    have hc : ∀ d : ℕ, Germ.const (c d) = hyperCoeff d (starAdicPolyEquiv R x) :=
      fun d ↦ (hstd d).choose_spec
    let f : Polynomial R := ∑ d ∈ Finset.range (k + 1), Polynomial.monomial d (c d)
    refine ⟨⟨f⟩, ?_⟩
    rw [starDist_adicPoly_eq]
    have hconst : starAdicPolyEquiv R (Germ.const ⟨f⟩) = Germ.const f := rfl
    rw [hconst]
    have hle : Germ.const ((k + 1 : ℕ) : ℕ∞) ≤
        starPolyXOrder (starAdicPolyEquiv R x - Germ.const f) := by
      generalize starAdicPolyEquiv R x = P at hc ⊢
      induction P using Germ.inductionOn with | _ u =>
      have hall : ∀ d ∈ Finset.range (k + 1),
          ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (u i - f).coeff d = 0 := by
        intro d hd
        have hd_lt : d < k + 1 := Finset.mem_range.1 hd
        have hf_d : f.coeff d = c d := by
          simp [f, Polynomial.coeff_monomial, hd_lt]
        have heq_d : (((fun i ↦ (u i).coeff d) : ℕ → R) : StarRing R) = Germ.const (c d) :=
          (hc d).symm
        exact (Germ.coe_eq.1 heq_d).mono fun i hi ↦ by
          dsimp only at hi
          rw [Polynomial.coeff_sub, hi, hf_d, sub_self]
      have hev_fin : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
          ∀ d ∈ Finset.range (k + 1), (u i - f).coeff d = 0 :=
        (Filter.eventually_all_finset (Finset.range (k + 1))).2 hall
      refine Germ.coe_le.2 (hev_fin.mono fun i hi ↦ ?_)
      exact (nat_le_polyXOrder_iff (u i - f) (k + 1)).1.2 fun d hd ↦ hi d (Finset.mem_range.2 hd)
    have hnorm_le : starPolyXNorm (starAdicPolyEquiv R x - Germ.const f) ≤
        (((2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) : ℝ) : ℝ*) :=
      (starPolyXNorm_le_zpow_iff _ (k + 1)).2 hle
    have hlt_real : (2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) < ε :=
      (zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega)).trans hk
    exact hnorm_le.trans_lt (Hyperreal.coe_lt_coe.2 hlt_real)

/-- Goldblatt §18.6 (p. 252): When `Infinite R`, there exist **limited** points in
`StarMetric (AdicPoly R)` that are **not approachable** from `R[X]`
(`PreNearstandard (AdicPoly R) ≠ LimitedMetric (AdicPoly R) ⟨0⟩`), fulfilling the promise from
§18.3! -/
theorem exists_limited_not_preNearstandard_adicPoly_of_infinite (R : Type*) [CommRing R]
    [Infinite R] :
    (∃ x ∈ LimitedMetric (AdicPoly R) ⟨0⟩, x ∉ PreNearstandard (AdicPoly R)) ∧
    PreNearstandard (AdicPoly R) ≠ LimitedMetric (AdicPoly R) ⟨0⟩ := by
  let c : ℕ ↪ R := Infinite.natEmbedding R
  let x : StarMetric (AdicPoly R) :=
    (((fun i : ℕ ↦ (⟨Polynomial.C (c i)⟩ : AdicPoly R)) : ℕ → AdicPoly R) :
      StarMetric (AdicPoly R))
  have hx_lim : x ∈ LimitedMetric (AdicPoly R) ⟨0⟩ := by
    rw [limitedMetric_adicPoly_eq_univ]; trivial
  have hx_not_ap : x ∉ PreNearstandard (AdicPoly R) := by
    rw [mem_preNearstandard_adicPoly_iff]
    intro hall
    obtain ⟨r, hr⟩ := hall 0
    have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
        (Polynomial.C (c i)).coeff 0 = r :=
      Germ.coe_eq.1 hr.symm
    have hfin : {i : ℕ | c i = r}.Finite := by
      refine Set.Subsingleton.finite fun i hi j hj ↦ c.injective ?_
      exact hi.trans hj.symm
    have hcof : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), c i ≠ r :=
      Filter.hyperfilter_le_cofinite hfin.compl_mem_cofinite
    have hev' : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), c i = r :=
      hev.mono fun i hi ↦ by simpa using hi
    obtain ⟨i, hi1, hi2⟩ := (hev'.and hcof).exists
    exact hi2 hi1
  refine ⟨⟨x, hx_lim, hx_not_ap⟩, fun heq ↦ hx_not_ap (heq ▸ hx_lim)⟩

/-- Goldblatt §18.6 (p. 252): Conversely, when `Finite R`, `*R = R`, so **every** hyperpolynomial is
approachable (`PreNearstandard (AdicPoly R) = Set.univ`). -/
theorem preNearstandard_adicPoly_eq_univ_of_finite (R : Type*) [CommRing R] [Finite R] :
    PreNearstandard (AdicPoly R) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true, mem_preNearstandard_adicPoly_iff]
  intro n
  exact (germConst_bijective_of_finite R).2 (hyperCoeff n (starAdicPolyEquiv R x))

/-- Predicate `IsXAdicInfinitesimal P`: `starPolyXNorm P` is infinitesimal (`|P|_X ≈ 0`,
Goldblatt §18.6, p. 253). -/
def IsXAdicInfinitesimal {R : Type*} [CommRing R] (P : HyperPoly R) : Prop :=
  IsInfinitesimal (starPolyXNorm P)

/-- Goldblatt §18.6, **Theorem 18.6.2** (p. 253): Four-way equivalence characterizing $X$-adic
infinitesimals in `HyperPoly R`:
1. `IsXAdicInfinitesimal P` (`|P|_X ≈ 0`)
2. `∀ n : ℕ, Germ.const (n : ℕ∞) < starPolyXOrder P` (unlimited $X$-adic order)
3. `∀ k : ℕ, (Germ.const Polynomial.X) ^ k ∣ P` (`X^k ∣ P` in `*R[X]` for every `k ∈ ℕ`)
4. `∀ n : ℕ, hyperCoeff n P = 0` (all coefficients of standard degree vanish).
Plus internal hypernatural witnessing: `∃ N : ℕ*, IsUnlimitedNat N ∧ ∀ k : ℕ*, k < N → internalCoeff P k = 0`! -/
theorem isXAdicInfinitesimal_tfae (R : Type*) [CommRing R] (P : HyperPoly R) :
    (IsXAdicInfinitesimal P ↔ ∀ n : ℕ, Germ.const (n : ℕ∞) < starPolyXOrder P) ∧
    ((∀ n : ℕ, Germ.const (n : ℕ∞) < starPolyXOrder P) ↔
      ∀ k : ℕ, (Germ.const (Polynomial.X : Polynomial R)) ^ k ∣ P) ∧
    ((∀ k : ℕ, (Germ.const (Polynomial.X : Polynomial R)) ^ k ∣ P) ↔
      ∀ n : ℕ, hyperCoeff n P = 0) ∧
    ((∀ n : ℕ, hyperCoeff n P = 0) ↔
      ∃ N : ℕ*, IsUnlimitedNat N ∧ ∀ k : ℕ*, k < N → internalCoeff P k = 0) := by
  have h12 : IsXAdicInfinitesimal P ↔ ∀ n : ℕ, Germ.const (n : ℕ∞) < starPolyXOrder P := by
    constructor
    · intro hinf n
      have hlt := hinf ((2 : ℝ) ^ (-(n : ℤ))) (zpow_pos (by norm_num) _)
      rw [abs_of_nonneg (starPolyXNorm_nonneg_and_le_one P).1] at hlt
      exact (starPolyXNorm_lt_zpow_iff P n).1 hlt
    · intro hord ε hε
      rw [abs_of_nonneg (starPolyXNorm_nonneg_and_le_one P).1]
      obtain ⟨n, hn⟩ := exists_two_zpow_neg_lt hε
      exact ((starPolyXNorm_lt_zpow_iff P n).2 (hord n)).trans (Hyperreal.coe_lt_coe.2 hn)
  have h24 : (∀ n : ℕ, Germ.const (n : ℕ∞) < starPolyXOrder P) ↔
      ∀ n : ℕ, hyperCoeff n P = 0 := by
    induction P using Germ.inductionOn with | _ u =>
    constructor
    · intro hord n
      refine Germ.coe_eq.2 ((Germ.coe_lt.1 (hord n)).mono fun i hi ↦ ?_)
      have h0 := PowerSeries.coeff_of_lt_order n (φ := (u i : PowerSeries R)) hi
      rwa [Polynomial.coeff_coe] at h0
    · intro hcoeff n
      have hall : ∀ d ∈ Finset.range (n + 1),
          ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (u i).coeff d = 0 :=
        fun d _ ↦ Germ.coe_eq.1 (hcoeff d)
      have hev := (Filter.eventually_all_finset (Finset.range (n + 1))).2 hall
      refine Germ.coe_lt.2 (hev.mono fun i hi ↦ ?_)
      have hle : ((n + 1 : ℕ) : ℕ∞) ≤ polyXOrder R (u i) :=
        (nat_le_polyXOrder_iff (u i) (n + 1)).1.2 fun d hd ↦ hi d (Finset.mem_range.2 hd)
      exact (Nat.cast_lt.2 (Nat.lt_succ_self n)).trans_le hle
  have h34 : (∀ k : ℕ, (Germ.const (Polynomial.X : Polynomial R)) ^ k ∣ P) ↔
      ∀ n : ℕ, hyperCoeff n P = 0 := by
    induction P using Germ.inductionOn with | _ u =>
    constructor
    · intro hdvd n
      obtain ⟨Q, hQ⟩ := hdvd (n + 1)
      induction Q using Germ.inductionOn with | _ v =>
      have hpow : (Germ.const (Polynomial.X : Polynomial R) : HyperPoly R) ^ (n + 1) =
          (Germ.const ((Polynomial.X : Polynomial R) ^ (n + 1)) : HyperPoly R) := by
        induction n + 1 with
        | zero => rfl
        | succ m ihm => rw [pow_succ, pow_succ, ihm]; rfl
      rw [hpow] at hQ
      have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
          u i = (Polynomial.X : Polynomial R) ^ (n + 1) * v i := Germ.coe_eq.1 hQ
      refine Germ.coe_eq.2 (hev.mono fun i hi ↦ ?_)
      have hdvd_i : (Polynomial.X : Polynomial R) ^ (n + 1) ∣ u i := ⟨v i, hi⟩
      exact Polynomial.X_pow_dvd_iff.1 hdvd_i n (Nat.lt_succ_self n)
    · intro hcoeff k
      have hall : ∀ d ∈ Finset.range k,
          ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (u i).coeff d = 0 :=
        fun d _ ↦ Germ.coe_eq.1 (hcoeff d)
      have hev := (Filter.eventually_all_finset (Finset.range k)).2 hall
      classical
      let qseq : ℕ → Polynomial R := fun i ↦
        if h : ∀ d < k, (u i).coeff d = 0 then
          Classical.choose (Polynomial.X_pow_dvd_iff.2 h)
        else 0
      have hpow : (Germ.const (Polynomial.X : Polynomial R) : HyperPoly R) ^ k =
          (Germ.const ((Polynomial.X : Polynomial R) ^ k) : HyperPoly R) :=
        ((germConstRingHom (Polynomial R)).map_pow Polynomial.X k).symm
      rw [hpow]
      refine ⟨(qseq : HyperPoly R), Germ.coe_eq.2 (hev.mono fun i hi ↦ ?_)⟩
      have hd : ∀ d < k, (u i).coeff d = 0 := fun d hd ↦ hi d (Finset.mem_range.2 hd)
      change u i = Polynomial.X ^ k * qseq i
      dsimp only [qseq]
      split_ifs
      exact Classical.choose_spec (Polynomial.X_pow_dvd_iff.2 hd)
  have h45 : (∀ n : ℕ, hyperCoeff n P = 0) ↔
      ∃ N : ℕ*, IsUnlimitedNat N ∧ ∀ k : ℕ*, k < N → internalCoeff P k = 0 := by
    constructor
    · intro hcoeff
      induction P using Germ.inductionOn with | _ u =>
      classical
      let Nseq : ℕ → ℕ := fun i ↦
        if h : u i = 0 then i else (u i : PowerSeries R).order.toNat
      refine ⟨(Nseq : ℕ*), ?_, ?_⟩
      · intro m
        have hord_m := (h24.2 hcoeff) (m + 1)
        have hcof_mem : (Set.Iio (m + 1))ᶜ ∈ (hyperfilter ℕ : Filter ℕ) :=
          Filter.hyperfilter_le_cofinite (Set.finite_Iio (m + 1)).compl_mem_cofinite
        have hcof : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), m + 1 ≤ i :=
          Filter.Eventually.mono hcof_mem fun i hi ↦ by
            rwa [Set.mem_Iio, not_lt] at hi
        refine Germ.coe_lt.2 (((Germ.coe_lt.1 hord_m).and hcof).mono fun i ⟨hi_ord, hi_ge⟩ ↦ ?_)
        change m < Nseq i
        dsimp only [Nseq]
        split_ifs with hz
        · omega
        · have hz_ps : (u i : PowerSeries R) ≠ 0 := Polynomial.coe_eq_zero_iff.not.2 hz
          have hcoe := PowerSeries.coe_toNat_order hz_ps
          change ((m + 1 : ℕ) : ℕ∞) < (u i : PowerSeries R).order at hi_ord
          rw [← hcoe] at hi_ord
          have hlt_nat : m + 1 < (u i : PowerSeries R).order.toNat := Nat.cast_lt.1 hi_ord
          omega
      · intro k hk
        induction k using Germ.inductionOn with | _ m =>
        refine Germ.coe_eq.2 ((Germ.coe_lt.1 hk).mono fun i hi ↦ ?_)
        change m i < Nseq i at hi
        dsimp only [Nseq] at hi
        split_ifs at hi with hz
        · simp [hz]
        · have h0 := PowerSeries.coeff_of_lt_order_toNat (m i) hi
          rwa [Polynomial.coeff_coe] at h0
    · rintro ⟨N, hN_unl, hvan⟩ n
      rw [← internalCoeff_natCast]
      exact hvan (n : ℕ*) (hN_unl n)
  exact ⟨h12, h24.trans h34.symm, h34, h45⟩

/-- Goldblatt §18.6, **Corollary 18.6.3** (p. 253): Two hyperpolynomials `P, Q ∈ HyperPoly R` are
infinitely close in the $X$-adic metric (`|P - Q|_X ≈ 0`) if and only if they have identical
coefficients of every standard degree `n : ℕ`. -/
theorem starPolyXNorm_sub_infinitesimal_iff {R : Type*} [CommRing R] (P Q : HyperPoly R) :
    IsInfinitesimal (starPolyXNorm (P - Q)) ↔ ∀ n : ℕ, hyperCoeff n P = hyperCoeff n Q := by
  have htfae := isXAdicInfinitesimal_tfae R (P - Q)
  have hiff : IsXAdicInfinitesimal (P - Q) ↔ ∀ n : ℕ, hyperCoeff n (P - Q) = 0 :=
    htfae.1.trans (htfae.2.1.trans htfae.2.2.1)
  unfold IsXAdicInfinitesimal at hiff
  rw [hiff]
  exact forall_congr' fun n ↦ by rw [map_sub, sub_eq_zero]

/-- Ideal `XAdicIdeal R` (`I_X`) of $X$-adic infinitesimals in `HyperPoly R`
(Goldblatt §18.6, p. 254). -/
noncomputable def XAdicIdeal (R : Type*) [CommRing R] : Ideal (HyperPoly R) where
  carrier := {P : HyperPoly R | ∀ n : ℕ, hyperCoeff n P = 0}
  add_mem' {P Q} hP hQ n := by rw [map_add, hP n, hQ n, add_zero]
  zero_mem' n := map_zero _
  smul_mem' C P hP n := by
    change hyperCoeff n (C * P) = 0
    rw [hyperCoeff_mul]
    exact Finset.sum_eq_zero fun ij _ ↦ by rw [hP ij.2, mul_zero]

/-- Membership in `XAdicIdeal R` is equivalent to `IsXAdicInfinitesimal P`. -/
@[simp]
theorem mem_xAdicIdeal_iff {R : Type*} [CommRing R] {P : HyperPoly R} :
    P ∈ XAdicIdeal R ↔ IsXAdicInfinitesimal P := by
  have htfae := isXAdicInfinitesimal_tfae R P
  exact (htfae.1.trans (htfae.2.1.trans htfae.2.2.1)).symm

/-- Canonical surjective ring homomorphism `thetaXStar R : HyperPoly R →+* PowerSeries (StarRing R)`
sending `P ↦ ∑_{n=0}^∞ (hyperCoeff n P) X^n` (`*R[X] → (*R)⟦X⟧`, Goldblatt §18.6, pp. 253–254). -/
noncomputable def thetaXStar (R : Type*) [CommRing R] :
    HyperPoly R →+* PowerSeries (StarRing R) where
  toFun P := PowerSeries.mk fun n ↦ hyperCoeff n P
  map_one' := PowerSeries.ext fun n ↦ by
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    change (((fun _ ↦ (1 : Polynomial R).coeff n) : ℕ → R) : StarRing R) = _
    split_ifs with hn
    · subst hn
      exact Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ by simp)
    · exact Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ by simp [Polynomial.coeff_one, hn])
  map_mul' P Q := PowerSeries.ext fun n ↦ by
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, hyperCoeff_mul]
    exact Finset.sum_congr rfl fun ij _ ↦ by simp [PowerSeries.coeff_mk]
  map_zero' := PowerSeries.ext fun n ↦ by simp [PowerSeries.coeff_mk]
  map_add' P Q := PowerSeries.ext fun n ↦ by simp [PowerSeries.coeff_mk, map_add]

/-- Surjectivity of `thetaXStar R : HyperPoly R →+* PowerSeries (StarRing R)`. -/
theorem thetaXStar_surjective (R : Type*) [CommRing R] :
    Function.Surjective (thetaXStar R) := by
  intro Φ
  have hex : ∀ n : ℕ, ∃ fn : ℕ → R, (fn : StarRing R) = PowerSeries.coeff n Φ :=
    fun n ↦ Germ.inductionOn (PowerSeries.coeff n Φ) fun fn ↦ ⟨fn, rfl⟩
  let c : ℕ → ℕ → R := fun n ↦ (hex n).choose
  have hc : ∀ n : ℕ, ((c n : ℕ → R) : StarRing R) = PowerSeries.coeff n Φ :=
    fun n ↦ (hex n).choose_spec
  let Pseq : ℕ → Polynomial R := fun i ↦
    ∑ m ∈ Finset.range (i + 1), Polynomial.monomial m (c m i)
  refine ⟨(Pseq : HyperPoly R), PowerSeries.ext fun n ↦ ?_⟩
  rw [thetaXStar, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, PowerSeries.coeff_mk, ← hc n]
  have hcof_mem : (Set.Iio n)ᶜ ∈ (hyperfilter ℕ : Filter ℕ) :=
    Filter.hyperfilter_le_cofinite (Set.finite_Iio n).compl_mem_cofinite
  refine Germ.coe_eq.2 (Filter.Eventually.mono hcof_mem fun i hi ↦ ?_)
  rw [Set.mem_Iio, not_lt] at hi
  have hn_lt : n < i + 1 := by omega
  simp [Pseq, Polynomial.coeff_monomial, hn_lt]

/-- Kernel of `thetaXStar R` is `XAdicIdeal R`. -/
theorem ker_thetaXStar (R : Type*) [CommRing R] :
    RingHom.ker (thetaXStar R) = XAdicIdeal R := by
  ext P
  rw [RingHom.mem_ker, PowerSeries.ext_iff]
  exact forall_congr' fun n ↦ by simp [thetaXStar, PowerSeries.coeff_mk]

/-- Goldblatt §18.6 (p. 254): **First Quotient Isomorphism
`(HyperPoly R ⧸ XAdicIdeal R) ≃+* PowerSeries (StarRing R)`** (`*R[X] / I_X ≅ (*R)⟦X⟧`, the full
nonstandard metric hull of `R[X]`). -/
noncomputable def hyperPolyQuotientEquivPowerSeriesStar (R : Type*) [CommRing R] :
    (HyperPoly R ⧸ XAdicIdeal R) ≃+* PowerSeries (StarRing R) :=
  (Ideal.quotEquivOfEq (ker_thetaXStar R).symm).trans
    (RingHom.quotientKerEquivOfSurjective (thetaXStar_surjective R))

/-- Subring `ApproachableHyperPoly R` (`*R[X]_ap`) of approachable hyperpolynomials — those whose
standard-degree coefficients all belong to `R` (Goldblatt §18.6, Theorem 18.6.1, p. 252). -/
def ApproachableHyperPoly (R : Type*) [CommRing R] : Subring (HyperPoly R) where
  carrier := {P : HyperPoly R | ∀ n : ℕ, hyperCoeff n P ∈ Set.range Germ.const}
  mul_mem' {P Q} hP hQ n := by
    change hyperCoeff n (P * Q) ∈ (germConstRingHom R).range
    rw [hyperCoeff_mul]
    refine Subring.sum_mem (germConstRingHom R).range fun ij _ ↦
      Subring.mul_mem _ (hP ij.1) (hQ ij.2)
  one_mem' n := ⟨(1 : Polynomial R).coeff n, rfl⟩
  add_mem' {P Q} hP hQ n := by
    change hyperCoeff n (P + Q) ∈ (germConstRingHom R).range
    rw [map_add]
    exact Subring.add_mem _ (hP n) (hQ n)
  zero_mem' n := ⟨0, rfl⟩
  neg_mem' {P} hP n := by
    change hyperCoeff n (-P) ∈ (germConstRingHom R).range
    rw [map_neg]
    exact Subring.neg_mem _ (hP n)

/-- Ideal `ApproachableInfinitesimalIdeal R = (XAdicIdeal R).comap (ApproachableHyperPoly R).subtype`
of $X$-adic infinitesimals inside `ApproachableHyperPoly R` (Goldblatt §18.6, p. 254). -/
noncomputable def ApproachableInfinitesimalIdeal (R : Type*) [CommRing R] :
    Ideal (ApproachableHyperPoly R) :=
  (XAdicIdeal R).comap (ApproachableHyperPoly R).subtype

/-- Goldblatt §18.6 (p. 254): **Hyperfinite Polynomial Truncation** `truncHyperPoly φ N : HyperPoly R`
of a formal power series `φ = ∑_{n=0}^∞ r_n X^n ∈ R⟦X⟧` up to hyperdegree `N ∈ ℕ*`
(`∑_{n=0}^N r_n X^n`). -/
noncomputable def truncHyperPoly {R : Type*} [CommRing R] (φ : PowerSeries R) (N : ℕ*) :
    HyperPoly R :=
  Germ.map (fun m : ℕ ↦ PowerSeries.trunc (m + 1) φ) N

/-- When `IsUnlimitedNat N`, `truncHyperPoly φ N` belongs to `ApproachableHyperPoly R` and its
`n`-th coefficient is `Germ.const (PowerSeries.coeff n φ)` for every `n : ℕ`
(Goldblatt §18.6, p. 254). -/
theorem hyperCoeff_truncHyperPoly_of_unlimited {R : Type*} [CommRing R]
    (φ : PowerSeries R) {N : ℕ*} (hN : IsUnlimitedNat N) :
    (∀ n : ℕ, hyperCoeff n (truncHyperPoly φ N) = Germ.const (PowerSeries.coeff n φ)) ∧
    truncHyperPoly φ N ∈ ApproachableHyperPoly R := by
  have hcoeff : ∀ n : ℕ, hyperCoeff n (truncHyperPoly φ N) =
      Germ.const (PowerSeries.coeff n φ) := by
    intro n
    have hlt : (n : ℕ*) < N := hN n
    induction N using Germ.inductionOn with | _ m =>
    refine Germ.coe_eq.2 ((Germ.coe_lt.1 hlt).mono fun i hi ↦ ?_)
    change (PowerSeries.trunc (m i + 1) φ).coeff n = PowerSeries.coeff n φ
    have hn_lt : n < m i + 1 := by change n < m i at hi; omega
    simp [PowerSeries.coeff_trunc, hn_lt]
  exact ⟨hcoeff, fun n ↦ ⟨PowerSeries.coeff n φ, (hcoeff n).symm⟩⟩

/-- Canonical restriction homomorphism `thetaXApproachable R : ApproachableHyperPoly R →+* PowerSeries R`
sending `P ↦ ∑_{n=0}^∞ r_n X^n` where `Germ.const r_n = hyperCoeff n P`
(`θ : *R[X]_ap → R⟦X⟧`, Goldblatt §18.6, p. 253). -/
noncomputable def thetaXApproachable (R : Type*) [CommRing R] :
    ApproachableHyperPoly R →+* PowerSeries R where
  toFun P := PowerSeries.mk fun n ↦ (P.2 n).choose
  map_one' := PowerSeries.ext fun n ↦ by
    rw [PowerSeries.coeff_mk]
    apply (Germ.const_inj (l := (hyperfilter ℕ : Filter ℕ))).1
    rw [((1 : ApproachableHyperPoly R).2 n).choose_spec]
    change hyperCoeff n (Germ.const (1 : Polynomial R) : HyperPoly R) =
      (Germ.const ((1 : PowerSeries R).coeff n) : StarRing R)
    rw [hyperCoeff_const, ← Polynomial.coe_one, Polynomial.coeff_coe]
  map_mul' P Q := PowerSeries.ext fun n ↦ by
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
    apply (Germ.const_inj (l := (hyperfilter ℕ : Filter ℕ))).1
    rw [((P * Q).2 n).choose_spec]
    change hyperCoeff n (P.1 * Q.1) =
      germConstRingHom R (∑ ij ∈ Finset.antidiagonal n, (P.2 ij.1).choose * (Q.2 ij.2).choose)
    rw [hyperCoeff_mul, map_sum]
    refine Finset.sum_congr rfl fun ij _ ↦ ?_
    rw [map_mul]
    change _ = (Germ.const (P.2 ij.1).choose : StarRing R) *
      (Germ.const (Q.2 ij.2).choose : StarRing R)
    rw [(P.2 ij.1).choose_spec, (Q.2 ij.2).choose_spec]
  map_zero' := PowerSeries.ext fun n ↦ by
    rw [PowerSeries.coeff_mk, map_zero]
    apply (Germ.const_inj (l := (hyperfilter ℕ : Filter ℕ))).1
    exact ((0 : ApproachableHyperPoly R).2 n).choose_spec.trans (map_zero (hyperCoeff n))
  map_add' P Q := PowerSeries.ext fun n ↦ by
    simp only [map_add, PowerSeries.coeff_mk]
    apply (Germ.const_inj (l := (hyperfilter ℕ : Filter ℕ))).1
    rw [((P + Q).2 n).choose_spec]
    change hyperCoeff n (P.1 + Q.1) =
      (Germ.const (P.2 n).choose : StarRing R) + (Germ.const (Q.2 n).choose : StarRing R)
    rw [map_add, (P.2 n).choose_spec, (Q.2 n).choose_spec]

/-- Specification of `thetaXApproachable R`:
`Germ.const (PowerSeries.coeff n (thetaXApproachable R P)) = hyperCoeff n P.1`. -/
@[simp]
theorem const_coeff_thetaXApproachable {R : Type*} [CommRing R]
    (P : ApproachableHyperPoly R) (n : ℕ) :
    (Germ.const (PowerSeries.coeff n (thetaXApproachable R P)) : StarRing R) = hyperCoeff n P.1 := by
  change (Germ.const (PowerSeries.coeff n (PowerSeries.mk fun m ↦ (P.2 m).choose)) : StarRing R) = _
  rw [PowerSeries.coeff_mk]
  exact (P.2 n).choose_spec

/-- Surjectivity of `thetaXApproachable R` witnessed by hyperfinite truncations up to `omegaNat`
(Goldblatt §18.6, p. 254). -/
theorem thetaXApproachable_surjective (R : Type*) [CommRing R] :
    Function.Surjective (thetaXApproachable R) := by
  intro φ
  have htrunc := hyperCoeff_truncHyperPoly_of_unlimited φ isUnlimitedNat_omegaNat
  refine ⟨⟨truncHyperPoly φ omegaNat, htrunc.2⟩, PowerSeries.ext fun n ↦ ?_⟩
  exact (Germ.const_inj (l := (hyperfilter ℕ : Filter ℕ))).1
    ((const_coeff_thetaXApproachable _ n).trans (htrunc.1 n))

/-- Kernel of `thetaXApproachable R` is `ApproachableInfinitesimalIdeal R`
(Goldblatt §18.6, p. 254). -/
theorem ker_thetaXApproachable (R : Type*) [CommRing R] :
    RingHom.ker (thetaXApproachable R) = ApproachableInfinitesimalIdeal R := by
  ext P
  rw [RingHom.mem_ker, PowerSeries.ext_iff]
  change (∀ n : ℕ, PowerSeries.coeff n (thetaXApproachable R P) = (PowerSeries.coeff n 0)) ↔
    ∀ n : ℕ, hyperCoeff n P.1 = 0
  refine forall_congr' fun n ↦ ?_
  rw [map_zero,
      ← Germ.const_inj (l := (hyperfilter ℕ : Filter ℕ))
        (a := PowerSeries.coeff n (thetaXApproachable R P)) (b := 0),
      const_coeff_thetaXApproachable]
  rfl

/-- Goldblatt §18.6 (p. 254): **Second Quotient Isomorphism
`(ApproachableHyperPoly R ⧸ ApproachableInfinitesimalIdeal R) ≃+* PowerSeries R`**
(`*R[X]_ap / (*R[X]_ap ∩ I_X) ≅ R⟦X⟧`). -/
noncomputable def approachableHyperPolyQuotientEquivPowerSeries (R : Type*) [CommRing R] :
    (ApproachableHyperPoly R ⧸ ApproachableInfinitesimalIdeal R) ≃+* PowerSeries R :=
  (Ideal.quotEquivOfEq (ker_thetaXApproachable R).symm).trans
    (RingHom.quotientKerEquivOfSurjective (thetaXApproachable_surjective R))

/-- Goldblatt §18.6, **Exercise 18.6.4** (p. 254): For any `P ∈ ApproachableHyperPoly R`:
1. If `starPolyXOrder P.1` is limited (`∃ m : ℕ, starPolyXOrder P.1 ≤ m`, so `thetaXApproachable R P ≠ 0`),
   then `starPolyXNorm P.1 = (powerSeriesXNorm R (thetaXApproachable R P) : ℝ*)` **exactly**;
2. If `starPolyXOrder P.1` is unlimited (`∀ m : ℕ, m < starPolyXOrder P.1`), then
   `thetaXApproachable R P = 0` and `IsInfinitesimal (starPolyXNorm P.1 - (powerSeriesXNorm R (thetaXApproachable R P) : ℝ*))`;
3. Consequently, in **all** cases `shadow (starPolyXNorm P.1) = powerSeriesXNorm R (thetaXApproachable R P)`! -/
theorem exercise_18_6_4 (R : Type*) [CommRing R] (P : ApproachableHyperPoly R) :
    ((∃ m : ℕ, starPolyXOrder P.1 ≤ Germ.const (m : ℕ∞)) →
      starPolyXNorm P.1 = (powerSeriesXNorm R (thetaXApproachable R P) : ℝ*)) ∧
    ((∀ m : ℕ, Germ.const (m : ℕ∞) < starPolyXOrder P.1) →
      IsInfinitesimal (starPolyXNorm P.1 - (powerSeriesXNorm R (thetaXApproachable R P) : ℝ*))) ∧
    shadow (starPolyXNorm P.1) = powerSeriesXNorm R (thetaXApproachable R P) := by
  set φ : PowerSeries R := thetaXApproachable R P
  have hexact_of_ne : φ ≠ 0 → starPolyXNorm P.1 = (powerSeriesXNorm R φ : ℝ*) := by
    intro hφ
    set k : ℕ := φ.order.toNat
    have hk_ord : (k : ℕ∞) = φ.order := PowerSeries.coe_toNat_order hφ
    have hk_ne : PowerSeries.coeff k φ ≠ 0 := PowerSeries.coeff_order hφ
    have hk_lt : ∀ d < k, PowerSeries.coeff d φ = 0 :=
      fun d hd ↦ PowerSeries.coeff_of_lt_order_toNat d hd
    have hnorm_φ : powerSeriesXNorm R φ = (2 : ℝ) ^ (-(k : ℤ)) := by
      rw [powerSeriesXNorm, ← hk_ord, xAdicValNorm_nat]
    rcases P with ⟨Pval, hP⟩
    induction Pval using Germ.inductionOn with | _ u =>
    have hev_ne : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (u i).coeff k ≠ 0 := by
      have heq_k : (((fun i ↦ (u i).coeff k) : ℕ → R) : StarRing R) =
          (Germ.const (PowerSeries.coeff k φ) : StarRing R) :=
        (const_coeff_thetaXApproachable ⟨(u : HyperPoly R), hP⟩ k).symm
      refine (Germ.coe_eq.1 heq_k).mono fun i hi ↦ ?_
      dsimp only at hi
      rwa [hi]
    have hall_lt : ∀ d ∈ Finset.range k,
        ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (u i).coeff d = 0 := by
      intro d hd
      have heq_d : hyperCoeff d (u : HyperPoly R) = 0 := by
        change hyperCoeff d (⟨(u : HyperPoly R), hP⟩ : ApproachableHyperPoly R).1 = 0
        rw [← const_coeff_thetaXApproachable ⟨(u : HyperPoly R), hP⟩ d,
            hk_lt d (Finset.mem_range.1 hd)]
        rfl
      exact Germ.coe_eq.1 heq_d
    have hev_lt := (Filter.eventually_all_finset (Finset.range k)).2 hall_lt
    rw [hnorm_φ]
    refine Germ.coe_eq.2 ((hev_ne.and hev_lt).mono fun i ⟨hi_ne, hi_lt⟩ ↦ ?_)
    have hord_i : (u i : PowerSeries R).order = (k : ℕ∞) := by
      rw [PowerSeries.order_eq_nat]
      refine ⟨by simpa [Polynomial.coeff_coe] using hi_ne, fun d hd ↦ ?_⟩
      rw [Polynomial.coeff_coe]
      exact hi_lt d (Finset.mem_range.2 hd)
    change xAdicValNorm (u i : PowerSeries R).order = (2 : ℝ) ^ (-(k : ℤ))
    rw [hord_i, xAdicValNorm_nat]
  have hpart1 : (∃ m : ℕ, starPolyXOrder P.1 ≤ Germ.const (m : ℕ∞)) →
      starPolyXNorm P.1 = (powerSeriesXNorm R φ : ℝ*) := by
    rintro ⟨m, hm⟩
    have hφ_ne : φ ≠ 0 := by
      intro hφ0
      have hker : P ∈ RingHom.ker (thetaXApproachable R) := hφ0
      rw [ker_thetaXApproachable] at hker
      have hinf : IsXAdicInfinitesimal P.1 := mem_xAdicIdeal_iff.1 hker
      have hgt := (isXAdicInfinitesimal_tfae R P.1).1.1 hinf m
      exact not_lt_of_ge hm hgt
    exact hexact_of_ne hφ_ne
  have hpart2 : (∀ m : ℕ, Germ.const (m : ℕ∞) < starPolyXOrder P.1) →
      IsInfinitesimal (starPolyXNorm P.1 - (powerSeriesXNorm R φ : ℝ*)) := by
    intro hunl
    have hinf : IsXAdicInfinitesimal P.1 := (isXAdicInfinitesimal_tfae R P.1).1.2 hunl
    have hker : P ∈ RingHom.ker (thetaXApproachable R) := by
      rw [ker_thetaXApproachable]
      exact mem_xAdicIdeal_iff.2 hinf
    have hφ0 : φ = 0 := hker
    rw [hφ0, (powerSeriesXNorm_eq_zero_iff (R := R) 0).2 rfl, Hyperreal.coe_zero, sub_zero]
    exact hinf
  have hpart3 : shadow (starPolyXNorm P.1) = powerSeriesXNorm R φ := by
    by_cases hφ : φ = 0
    · have hker : P ∈ ApproachableInfinitesimalIdeal R := by
        rw [← ker_thetaXApproachable]; exact hφ
      have hinf : IsXAdicInfinitesimal P.1 := mem_xAdicIdeal_iff.1 hker
      rw [hφ, (powerSeriesXNorm_eq_zero_iff (R := R) 0).2 rfl]
      exact (shadow_eq_zero_iff_isInfinitesimal
        (starPolyXNorm_nonneg_and_le_one P.1).2.2).2 hinf
    · rw [hexact_of_ne hφ, shadow_coe]
  exact ⟨hpart1, hpart2, hpart3⟩

/-- Goldblatt §18.6 (p. 254): **Isometric Equivalence `MetricCompletion (AdicPoly R) ≃ᵢ AdicPowerSeries R`**
identifying the nonstandard metric completion of `(R[X], d_X)` with `(R⟦X⟧, d_X)`! -/
noncomputable def adicPolyCompletionEquivPowerSeries (R : Type*) [CommRing R] :
    MetricCompletion (AdicPoly R) ≃ᵢ AdicPowerSeries R := by
  let φ : MetricCompletion (AdicPoly R) → AdicPowerSeries R :=
    Quotient.lift
      (fun a : PreNearstandard (AdicPoly R) ↦
        ⟨thetaXApproachable R ⟨starAdicPolyEquiv R a.1,
          (mem_preNearstandard_adicPoly_iff R a.1).1 a.2⟩⟩)
      fun a b hab ↦ by
        let va : ApproachableHyperPoly R :=
          ⟨starAdicPolyEquiv R a.1, (mem_preNearstandard_adicPoly_iff R a.1).1 a.2⟩
        let vb : ApproachableHyperPoly R :=
          ⟨starAdicPolyEquiv R b.1, (mem_preNearstandard_adicPoly_iff R b.1).1 b.2⟩
        have hinf : IsXAdicInfinitesimal (va - vb).1 := by
          unfold IsXAdicInfinitesimal
          change IsInfinitesimal
            (starPolyXNorm (starAdicPolyEquiv R a.1 - starAdicPolyEquiv R b.1))
          rw [← starDist_adicPoly_eq]
          exact hab
        have hker : va - vb ∈ RingHom.ker (thetaXApproachable R) := by
          rw [ker_thetaXApproachable]
          exact mem_xAdicIdeal_iff.2 hinf
        rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hker
        exact congrArg AdicPowerSeries.mk hker
  have hφ_iso : Isometry φ := Isometry.of_dist_eq fun x y ↦
    Quotient.inductionOn₂ x y fun a b ↦ by
      let va : ApproachableHyperPoly R :=
        ⟨starAdicPolyEquiv R a.1, (mem_preNearstandard_adicPoly_iff R a.1).1 a.2⟩
      let vb : ApproachableHyperPoly R :=
        ⟨starAdicPolyEquiv R b.1, (mem_preNearstandard_adicPoly_iff R b.1).1 b.2⟩
      change powerSeriesXNorm R (thetaXApproachable R va - thetaXApproachable R vb) =
        shadow (starDist a.1 b.1)
      rw [← map_sub, ← (exercise_18_6_4 R (va - vb)).2.2, starDist_adicPoly_eq]
      rfl
  have hφ_surj : Function.Surjective φ := fun ψ ↦ by
    obtain ⟨v, hv⟩ := thetaXApproachable_surjective R ψ.val
    have hap : (starAdicPolyEquiv R).symm v.1 ∈ PreNearstandard (AdicPoly R) := by
      rw [mem_preNearstandard_adicPoly_iff, Equiv.apply_symm_apply]
      exact v.2
    refine ⟨Quotient.mk (preNearstandardSetoid (AdicPoly R)) ⟨(starAdicPolyEquiv R).symm v.1, hap⟩, ?_⟩
    cases ψ
    simpa [φ] using congrArg AdicPowerSeries.mk hv
  exact { toEquiv := Equiv.ofBijective φ ⟨hφ_iso.injective, hφ_surj⟩
          isometry_toFun := hφ_iso }

/-- Goldblatt §18.6 (p. 251): `AdicPowerSeries R` (`(R⟦X⟧, d_X)`) is a **complete metric space**,
obtained directly by transporting `CompleteSpace (MetricCompletion (AdicPoly R))` along
`adicPolyCompletionEquivPowerSeries R`! -/
instance instCompleteSpaceAdicPowerSeries (R : Type*) [CommRing R] :
    CompleteSpace (AdicPowerSeries R) :=
  (adicPolyCompletionEquivPowerSeries R).completeSpace_iff.1 inferInstance

/-- Real-specialized coefficient map `hyperCoeffR n : HyperPoly ℝ →+ ℝ*` with syntactic codomain `ℝ*`
(so `IsLimited`, `IsInfinitesimal`, and `shadow` elaborate at `implicit` transparency). -/
def hyperCoeffR (n : ℕ) : HyperPoly ℝ →+ ℝ* :=
  hyperCoeff n

/-- Cauchy product formula for `hyperCoeffR`. -/
theorem hyperCoeffR_mul (n : ℕ) (P Q : HyperPoly ℝ) :
    hyperCoeffR n (P * Q) =
      ∑ ij ∈ Finset.antidiagonal n, hyperCoeffR ij.1 P * hyperCoeffR ij.2 Q :=
  hyperCoeff_mul n P Q

/-- Subring `LimitedCoeffHyperPoly` (`ℝ[X]^b`) of real hyperpolynomials in `HyperPoly ℝ` whose
coefficients of every standard degree are limited hyperreals (`IsLimited (hyperCoeffR n P)`). -/
def LimitedCoeffHyperPoly : Subring (HyperPoly ℝ) where
  carrier := {P : HyperPoly ℝ | ∀ n : ℕ, IsLimited (hyperCoeffR n P)}
  mul_mem' {P Q} hP hQ n := by
    change IsLimited (hyperCoeffR n (P * Q))
    rw [hyperCoeffR_mul]
    have hsum : ∀ s : Finset (ℕ × ℕ),
        IsLimited (∑ ij ∈ s, hyperCoeffR ij.1 P * hyperCoeffR ij.2 Q) := by
      intro s
      classical
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty]
        exact isInfinitesimal_zero.isLimited
      | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact ((hP a.1).mul (hQ a.2)).add ih
    exact hsum (Finset.antidiagonal n)
  one_mem' n := by
    have : hyperCoeffR n (1 : HyperPoly ℝ) = (((1 : Polynomial ℝ).coeff n : ℝ) : ℝ*) := rfl
    rw [this]
    exact isLimited_coe _
  add_mem' {P Q} hP hQ n := by
    change IsLimited (hyperCoeffR n (P + Q))
    rw [map_add]
    exact (hP n).add (hQ n)
  zero_mem' n := by
    change IsLimited (hyperCoeffR n (0 : HyperPoly ℝ))
    rw [map_zero]
    exact isInfinitesimal_zero.isLimited
  neg_mem' {P} hP n := by
    change IsLimited (hyperCoeffR n (-P))
    rw [map_neg]
    exact (hP n).neg

/-- Ideal `InfinitesimalCoeffHyperPoly` of `LimitedCoeffHyperPoly` consisting of hyperpolynomials
all of whose standard-degree coefficients are infinitesimal (`IsInfinitesimal (hyperCoeffR n P)`). -/
noncomputable def InfinitesimalCoeffHyperPoly : Ideal LimitedCoeffHyperPoly where
  carrier := {P : LimitedCoeffHyperPoly | ∀ n : ℕ, IsInfinitesimal (hyperCoeffR n P.1)}
  add_mem' {P Q} hP hQ n := by
    change IsInfinitesimal (hyperCoeffR n (P.1 + Q.1))
    rw [map_add]
    exact (hP n).add (hQ n)
  zero_mem' n := by
    change IsInfinitesimal (hyperCoeffR n (0 : HyperPoly ℝ))
    rw [map_zero]
    exact isInfinitesimal_zero
  smul_mem' C P hP n := by
    change IsInfinitesimal (hyperCoeffR n (C.1 * P.1))
    rw [hyperCoeffR_mul]
    have hsum : ∀ s : Finset (ℕ × ℕ),
        IsInfinitesimal (∑ ij ∈ s, hyperCoeffR ij.1 C.1 * hyperCoeffR ij.2 P.1) := by
      intro s
      classical
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty]
        exact isInfinitesimal_zero
      | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact ((C.2 a.1).mul_isInfinitesimal (hP a.2)).add ih
    exact hsum (Finset.antidiagonal n)

/-- Helper lemma: `shadow` commutes with finite sums of limited hyperreals. -/
theorem shadow_finset_sum {α : Type*} (s : Finset α) (f : α → ℝ*)
    (hf : ∀ a ∈ s, IsLimited (f a)) :
    (IsLimited (∑ a ∈ s, f a)) ∧ shadow (∑ a ∈ s, f a) = ∑ a ∈ s, shadow (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [isInfinitesimal_zero.isLimited, shadow_zero]
  | insert a s ha ih =>
    have ha_lim : IsLimited (f a) := hf a (Finset.mem_insert_self a s)
    have hs_lim := ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb)
    simp only [Finset.sum_insert ha]
    exact ⟨ha_lim.add hs_lim.1,
      (shadow_add ha_lim hs_lim.1).trans (congrArg (shadow (f a) + ·) hs_lim.2)⟩

/-- Canonical shadow-coefficient ring homomorphism
`thetaXRealLimited : LimitedCoeffHyperPoly →+* PowerSeries ℝ` sending
`P ↦ ∑_{n=0}^∞ shadow(hyperCoeffR n P) X^n`. -/
noncomputable def thetaXRealLimited : LimitedCoeffHyperPoly →+* PowerSeries ℝ where
  toFun P := PowerSeries.mk fun n ↦ shadow (hyperCoeffR n P.1)
  map_one' := PowerSeries.ext fun n ↦ by
    rw [PowerSeries.coeff_mk, Subring.coe_one]
    have : hyperCoeffR n (1 : HyperPoly ℝ) = (((1 : Polynomial ℝ).coeff n : ℝ) : ℝ*) := rfl
    rw [this, shadow_coe, ← Polynomial.coe_one, Polynomial.coeff_coe]
  map_mul' P Q := PowerSeries.ext fun n ↦ by
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
    change shadow (hyperCoeffR n (P.1 * Q.1)) = _
    rw [hyperCoeffR_mul, (shadow_finset_sum (Finset.antidiagonal n) _
      (fun ij _ ↦ (P.2 ij.1).mul (Q.2 ij.2))).2]
    refine Finset.sum_congr rfl fun ij _ ↦ ?_
    rw [shadow_mul (P.2 ij.1) (Q.2 ij.2)]
    simp [PowerSeries.coeff_mk]
  map_zero' := PowerSeries.ext fun n ↦ by
    simp only [PowerSeries.coeff_mk, map_zero]
    change shadow (hyperCoeffR n (0 : HyperPoly ℝ)) = 0
    rw [map_zero, shadow_zero]
  map_add' P Q := PowerSeries.ext fun n ↦ by
    simp only [PowerSeries.coeff_mk, map_add]
    change shadow (hyperCoeffR n (P.1 + Q.1)) = _
    rw [map_add, shadow_add (P.2 n) (Q.2 n)]

/-- Surjectivity of `thetaXRealLimited : LimitedCoeffHyperPoly →+* PowerSeries ℝ`. -/
theorem thetaXRealLimited_surjective : Function.Surjective thetaXRealLimited := by
  intro φ
  have htrunc := hyperCoeff_truncHyperPoly_of_unlimited φ isUnlimitedNat_omegaNat
  have hlim : truncHyperPoly φ omegaNat ∈ LimitedCoeffHyperPoly := fun n ↦ by
    have h1 : hyperCoeffR n (truncHyperPoly φ omegaNat) = ((PowerSeries.coeff n φ : ℝ) : ℝ*) :=
      htrunc.1 n
    rw [h1]
    exact isLimited_coe (PowerSeries.coeff n φ)
  refine ⟨⟨truncHyperPoly φ omegaNat, hlim⟩, PowerSeries.ext fun n ↦ ?_⟩
  simp only [thetaXRealLimited, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    PowerSeries.coeff_mk]
  have h1 : hyperCoeffR n (truncHyperPoly φ omegaNat) = ((PowerSeries.coeff n φ : ℝ) : ℝ*) :=
    htrunc.1 n
  rw [h1]
  exact shadow_coe (PowerSeries.coeff n φ)

/-- Kernel of `thetaXRealLimited` is `InfinitesimalCoeffHyperPoly`. -/
theorem ker_thetaXRealLimited :
    RingHom.ker thetaXRealLimited = InfinitesimalCoeffHyperPoly := by
  ext P
  rw [RingHom.mem_ker, PowerSeries.ext_iff]
  change (∀ n : ℕ, PowerSeries.coeff n (thetaXRealLimited P) = PowerSeries.coeff n 0) ↔
    ∀ n : ℕ, IsInfinitesimal (hyperCoeffR n P.1)
  refine forall_congr' fun n ↦ ?_
  simp only [thetaXRealLimited, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    PowerSeries.coeff_mk, map_zero]
  exact shadow_eq_zero_iff_isInfinitesimal (P.2 n)

/-- **Third Quotient Isomorphism `(LimitedCoeffHyperPoly ⧸ InfinitesimalCoeffHyperPoly) ≃+* PowerSeries ℝ`**
realizing real formal power series `ℝ⟦X⟧` by taking shadows of limited standard-degree coefficients! -/
noncomputable def limitedCoeffHyperPolyQuotientEquivRealPowerSeries :
    (LimitedCoeffHyperPoly ⧸ InfinitesimalCoeffHyperPoly) ≃+* PowerSeries ℝ :=
  (Ideal.quotEquivOfEq ker_thetaXRealLimited.symm).trans
    (RingHom.quotientKerEquivOfSurjective thetaXRealLimited_surjective)

/-- Strict subring & ideal inclusions comparing `ApproachableHyperPoly ℝ` vs `LimitedCoeffHyperPoly`
and `(XAdicIdeal ℝ).comap LimitedCoeffHyperPoly.subtype` vs `InfinitesimalCoeffHyperPoly`
(witnessed by `C(ε)` for `ε = Hyperreal.epsilon`, which has limited & infinitesimal coefficients yet
is neither approachable nor $X$-adically infinitesimal since `|C(ε)|_X = 1`!). -/
theorem approachable_strict_lt_limitedCoeffHyperPoly :
    ApproachableHyperPoly ℝ < LimitedCoeffHyperPoly ∧
    (XAdicIdeal ℝ).comap LimitedCoeffHyperPoly.subtype < InfinitesimalCoeffHyperPoly := by
  have hC_eq0 : ∀ a : StarRing ℝ, hyperCoeffR 0 (germMapRingHom Polynomial.C a) = a :=
    fun a ↦ Germ.inductionOn a fun _ ↦
      Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ Polynomial.coeff_C_zero)
  have hC_succ : ∀ (m : ℕ) (a : StarRing ℝ),
      hyperCoeffR (m + 1) (germMapRingHom Polynomial.C a) = 0 :=
    fun m a ↦ Germ.inductionOn a fun _ ↦
      Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ by simp)
  let Pε : HyperPoly ℝ := germMapRingHom Polynomial.C (Hyperreal.epsilon : StarRing ℝ)
  have hPε_eq0 : hyperCoeffR 0 Pε = Hyperreal.epsilon :=
    hC_eq0 (Hyperreal.epsilon : StarRing ℝ)
  have hPε_inf0 : IsInfinitesimal (hyperCoeffR 0 Pε) := by
    rw [hPε_eq0]
    exact isInfinitesimal_epsilon
  have hPε_inf_all : ∀ n : ℕ, IsInfinitesimal (hyperCoeffR n Pε) := by
    intro n
    cases n with
    | zero => exact hPε_inf0
    | succ m =>
      have h0 : hyperCoeffR (m + 1) Pε = 0 := hC_succ m (Hyperreal.epsilon : StarRing ℝ)
      rw [h0]
      exact isInfinitesimal_zero
  have hPε_lim : Pε ∈ LimitedCoeffHyperPoly := fun n ↦ (hPε_inf_all n).isLimited
  have hPε_ne0 : hyperCoeffR 0 Pε ≠ 0 := by
    rw [hPε_eq0]
    exact Hyperreal.epsilon_ne_zero
  have hPε_not_ap : Pε ∉ ApproachableHyperPoly ℝ := by
    intro hap
    obtain ⟨c, hc⟩ := hap 0
    have hc_inf : IsInfinitesimal (c : ℝ*) := by
      have : (c : ℝ*) = hyperCoeffR 0 Pε := hc
      rw [this]
      exact hPε_inf0
    have hc0 : c = 0 := by
      rw [← shadow_coe c]
      exact (shadow_eq_zero_iff_isInfinitesimal (isLimited_coe c)).2 hc_inf
    apply hPε_ne0
    have : hyperCoeffR 0 Pε = (c : ℝ*) := hc.symm
    rw [this, hc0]
    rfl
  refine ⟨lt_of_le_not_ge (fun P hP n ↦ ?_) (fun hle ↦ hPε_not_ap (hle hPε_lim)),
    lt_of_le_not_ge (fun P hP n ↦ ?_) (fun hle ↦ ?_)⟩
  · obtain ⟨c, hc⟩ := hP n
    have : hyperCoeffR n P = (c : ℝ*) := hc.symm
    rw [this]
    exact isLimited_coe c
  · have h0 : hyperCoeffR n P.1 = 0 := hP n
    rw [h0]
    exact isInfinitesimal_zero
  · have hmem_inf : (⟨Pε, hPε_lim⟩ : LimitedCoeffHyperPoly) ∈ InfinitesimalCoeffHyperPoly :=
      hPε_inf_all
    have hmem_xadic := hle hmem_inf
    exact hPε_ne0 (hmem_xadic 0)

/-!
## §18.7–18.8 Hyperfinite Expansions in Base $p$ & Exercises 18.8(1)–(2) (Goldblatt pp. 255–257)

Every natural number `z ∈ ℕ` has a unique canonical finite base-$p$ digit sequence in `SeqP p`
(digits in `{0, …, p - 1}` with no trailing zero, empty for `0` and non-empty for positive integers),
yielding the bijection `seqPEquivNat p : SeqP p ≃ ℕ` (`posSeqPEquivPosNat p` on positive integers)
and its ultrapower lift `starSeqPEquivHypernat p : StarSeqP p ≃ ℕ*` (`*∑ : *Seq(p) → *ℕ`).

* **Exercise 18.8(1)** (`exercise_18_8_1`): Full nonstandard characterization of `StarSeqP p` as
  internal hyperfinite sequences of standard residues in `{0, …, p - 1}` (`*(ℤ/p) = ℤ/p`),
  including internal reconstruction from any hypernatural length `N ∈ ℕ*` and internal sequence `F`.
* **Result `(v)`** (`hyperBasePPartialSum_mod_pow_and_sub_dvd`,
  Goldblatt p. 255): Congruence of hyperfinite base-$p$ expansions and their truncations modulo
  `p^{n+1}`.
* **Theorem 18.7.1 & Exercise 18.8(2)** (`padicInfClose_hypernat_iff_eq_basePDigits` and
  `theorem_18_7_1_and_exercise_18_8_2`, Goldblatt pp. 256–257): Two (positive) hyperintegers are
  $p$-adically infinitely close if and only if their hyperfinite base-$p$ expansions have identical
  coefficients of every standard degree `n ∈ ℕ`.
* **Hyperfinite Base-$p$ Representation of `ℤ_[p]`** (`exists_pos_hypernat_baseP_expansion_of_padicInt`,
  Goldblatt pp. 256–257): Every $p$-adic integer `a ∈ ℤ_[p]` is represented via `thetaP p` by a
  strictly positive hypernatural `x ∈ ℕ*` (`0 < x`) whose standard-degree base-$p$ digits match the
  Hensel digits of `a`, unique up to agreeing on all standard-degree digits.
-/

/-- Canonical finite base-$p$ digit sequences `SeqP p` (elements in `{0, …, p - 1}` with nonzero
top digit when non-empty, Goldblatt §18.7, p. 255). -/
def SeqP (p : ℕ) : Type :=
  {L : List ℕ // (∀ d ∈ L, d < p) ∧ (∀ h : L ≠ [], L.getLast h ≠ 0)}

/-- Canonical base-$p$ digit sequence `natToSeqP p n : SeqP p` of `n : ℕ` via `Nat.digits p n`. -/
def natToSeqP (p : ℕ) [Fact p.Prime] (n : ℕ) : SeqP p :=
  ⟨Nat.digits p n,
    ⟨fun _ hd ↦ Nat.digits_lt_base (Fact.out : p.Prime).one_lt hd,
     fun h ↦ Nat.getLast_digit_ne_zero p (Nat.digits_ne_nil_iff_ne_zero.1 h)⟩⟩

/-- Goldblatt §18.7 (p. 255): Bijection `seqPEquivNat p : SeqP p ≃ ℕ` given by the base-$p$
evaluation operator `∑ : Seq(p) → ℕ` (`Nat.ofDigits p`). -/
def seqPEquivNat (p : ℕ) [Fact p.Prime] : SeqP p ≃ ℕ where
  toFun s := Nat.ofDigits p s.1
  invFun := natToSeqP p
  left_inv s := Subtype.ext (Nat.digits_ofDigits p (Fact.out : p.Prime).one_lt s.1 s.2.1 s.2.2)
  right_inv n := Nat.ofDigits_digits p n

/-- Positive-integer restriction `posSeqPEquivPosNat p : {s : SeqP p // s.1 ≠ []} ≃ {z : ℕ // 0 < z}`
matching Goldblatt's `ℕ = {1, 2, 3, …}` convention (Goldblatt §18.7, p. 255). -/
def posSeqPEquivPosNat (p : ℕ) [Fact p.Prime] :
    {s : SeqP p // s.1 ≠ []} ≃ {z : ℕ // 0 < z} where
  toFun s := ⟨seqPEquivNat p s.1, Nat.pos_of_ne_zero fun h0 ↦ by
    have hnil : s.1.1 = [] := by
      have h1 : s.1 = natToSeqP p 0 := ((seqPEquivNat p).symm_apply_eq.2 h0.symm).symm
      exact (congrArg Subtype.val h1).trans (Nat.digits_zero p)
    exact s.2 hnil⟩
  invFun z := ⟨(seqPEquivNat p).symm z.1,
    Nat.digits_ne_nil_iff_ne_zero.2 z.2.ne'⟩
  left_inv s := Subtype.ext ((seqPEquivNat p).symm_apply_apply s.1)
  right_inv z := Subtype.ext ((seqPEquivNat p).apply_symm_apply z.1)

/-- Ultrapower `StarSeqP p = Germ (hyperfilter ℕ) (SeqP p)` (`*Seq(p)`, Goldblatt §18.7, p. 255). -/
abbrev StarSeqP (p : ℕ) :=
  Germ (hyperfilter ℕ : Filter ℕ) (SeqP p)

/-- Lifted hyperfinite evaluation operator `starOfDigits p : StarSeqP p → ℕ*`
(`*∑ : *Seq(p) → *ℕ`, Goldblatt §18.7, p. 255). -/
def starOfDigits (p : ℕ) (S : StarSeqP p) : ℕ* :=
  Germ.map (fun s : SeqP p ↦ Nat.ofDigits p s.1) S

/-- Goldblatt §18.7 (p. 255): Lifted bijection `starSeqPEquivHypernat p : StarSeqP p ≃ ℕ*`
between `*Seq(p)` and `*ℕ` (`toFun = starOfDigits p`). -/
def starSeqPEquivHypernat (p : ℕ) [Fact p.Prime] : StarSeqP p ≃ ℕ* where
  toFun := starOfDigits p
  invFun := Germ.map (natToSeqP p)
  left_inv S := Germ.inductionOn S fun s ↦
    Germ.coe_eq.2 (Eventually.of_forall fun j ↦ (seqPEquivNat p).left_inv (s j))
  right_inv z := Germ.inductionOn z fun u ↦
    Germ.coe_eq.2 (Eventually.of_forall fun j ↦ (seqPEquivNat p).right_inv (u j))

/-- Internal hyperfinite length `starSeqPLength S : ℕ*` of `S ∈ StarSeqP p`. -/
def starSeqPLength {p : ℕ} (S : StarSeqP p) : ℕ* :=
  Germ.map (fun s : SeqP p ↦ s.1.length) S

/-- Internal digit lookup `starSeqPDigit S i : ℕ*` at hypernatural index `i : ℕ*` (`0` for
`i ≥ starSeqPLength S`). -/
def starSeqPDigit {p : ℕ} (S : StarSeqP p) (i : ℕ*) : ℕ* :=
  Germ.map₂ (fun (s : SeqP p) (k : ℕ) ↦ s.1.getD k 0) S i

/-- Base-$p$ `i`-th digit `(z / p ^ i) % p` of a natural number `z : ℕ` (Goldblatt §18.7, p. 255). -/
def basePDigit (p z i : ℕ) : ℕ :=
  (z / p ^ i) % p

/-- Compatibility `(Nat.digits p z).getD i 0 = basePDigit p z i` for prime `p`. -/
theorem getD_digits_eq_basePDigit (p : ℕ) [Fact p.Prime] (z i : ℕ) :
    (Nat.digits p z).getD i 0 = basePDigit p z i :=
  Nat.getD_digits z i (Fact.out : p.Prime).two_le

/-- Base-$p$ partial sum `∑_{i < k} basePDigit p z i * p ^ i` on `ℕ`. -/
def basePPartialSum (p z k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, basePDigit p z i * p ^ i

/-- Fundamental Euclidean identity `basePPartialSum p z k = z % p ^ k` for all `z k : ℕ`. -/
theorem basePPartialSum_eq_mod (p : ℕ) [Fact p.Prime] (z k : ℕ) :
    basePPartialSum p z k = z % p ^ k := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  induction k with
  | zero => simp [basePPartialSum, Nat.mod_one]
  | succ m ih =>
    rw [basePPartialSum, Finset.sum_range_succ, ← basePPartialSum, ih]
    unfold basePDigit
    have hz2 : z = (z % p ^ m + ((z / p ^ m) % p) * p ^ m) + p ^ (m + 1) * ((z / p ^ m) / p) := by
      have hz1 : z = p ^ m * (z / p ^ m) + z % p ^ m := (Nat.div_add_mod z (p ^ m)).symm
      have hq1 : z / p ^ m = p * ((z / p ^ m) / p) + (z / p ^ m) % p :=
        (Nat.div_add_mod (z / p ^ m) p).symm
      calc z = p ^ m * (z / p ^ m) + z % p ^ m := hz1
        _ = p ^ m * (p * ((z / p ^ m) / p) + (z / p ^ m) % p) + z % p ^ m := by
          conv_lhs => rw [hq1]
        _ = (z % p ^ m + ((z / p ^ m) % p) * p ^ m) + p ^ (m + 1) * ((z / p ^ m) / p) := by
          rw [pow_succ]; ring
    have hr_lt : z % p ^ m < p ^ m := Nat.mod_lt z (pow_pos hp_pos m)
    have hqp_lt : (z / p ^ m) % p < p := Nat.mod_lt (z / p ^ m) hp_pos
    have hsum_lt : z % p ^ m + ((z / p ^ m) % p) * p ^ m < p ^ (m + 1) := by
      have hle1 : (z / p ^ m) % p + 1 ≤ p := hqp_lt
      have hle2 : ((z / p ^ m) % p + 1) * p ^ m ≤ p * p ^ m := Nat.mul_le_mul_right (p ^ m) hle1
      have hpow : p * p ^ m = p ^ (m + 1) := by rw [pow_succ]; ring
      nlinarith
    conv_rhs => rw [hz2]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsum_lt]

/-- Digit-sum reconstruction lemma on `ℕ`: if `∀ k < n, f k < p` and `0 < n → f (n - 1) ≠ 0`, then
`z = ∑ k ∈ range n, f k * p ^ k` has `(Nat.digits p z).length = n` and
`∀ k < n, basePDigit p z k = f k`. -/
theorem digits_sum_range_length_and_digit (p : ℕ) [Fact p.Prime] (n : ℕ) (f : ℕ → ℕ)
    (hf_lt : ∀ k < n, f k < p) :
    (∑ k ∈ Finset.range n, f k * p ^ k) < p ^ n ∧
    (∀ k < n, basePDigit p (∑ i ∈ Finset.range n, f i * p ^ i) k = f k) ∧
    ((0 < n → f (n - 1) ≠ 0) →
      (Nat.digits p (∑ i ∈ Finset.range n, f i * p ^ i)).length = n) := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hp_gt1 : 1 < p := (Fact.out : p.Prime).one_lt
  have h12 : (∑ k ∈ Finset.range n, f k * p ^ k) < p ^ n ∧
      ∀ k < n, basePDigit p (∑ i ∈ Finset.range n, f i * p ^ i) k = f k := by
    induction n with
    | zero => simp
    | succ m ih =>
      have ihm := ih fun k hk ↦ hf_lt k (Nat.lt_succ_of_lt hk)
      set zm := ∑ i ∈ Finset.range m, f i * p ^ i
      have hfm_lt : f m < p := hf_lt m (Nat.lt_succ_self m)
      have hsum_lt : zm + f m * p ^ m < p ^ (m + 1) := by
        have hle1 : f m + 1 ≤ p := hfm_lt
        have hle2 : (f m + 1) * p ^ m ≤ p * p ^ m := Nat.mul_le_mul_right (p ^ m) hle1
        have hpow : p * p ^ m = p ^ (m + 1) := by rw [pow_succ]; ring
        have hzm := ihm.1
        nlinarith
      refine ⟨by simpa [Finset.sum_range_succ, zm] using hsum_lt, fun k hk ↦ ?_⟩
      rw [Finset.sum_range_succ]
      change basePDigit p (zm + f m * p ^ m) k = f k
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hkm | hkeq
      · have hexp : m = (k + 1) + (m - (k + 1)) := by omega
        have hpow_split : p ^ m = p ^ (k + 1) * p ^ (m - (k + 1)) := by
          rw [← pow_add, ← hexp]
        have hmul_pow : f m * p ^ m = p ^ (k + 1) * (f m * p ^ (m - (k + 1))) := by
          rw [hpow_split]
          ring
        have hmod : (zm + f m * p ^ m) % p ^ (k + 1) = zm % p ^ (k + 1) := by
          rw [hmul_pow, Nat.add_mul_mod_self_left]
        have hdig_mod : ∀ x : ℕ, basePDigit p x k = (x % p ^ (k + 1)) / p ^ k := fun x ↦ by
          unfold basePDigit
          rw [pow_succ, Nat.mod_mul_right_div_self]
        rw [hdig_mod, hmod, ← hdig_mod]
        exact ihm.2 k hkm
      · rw [hkeq]
        unfold basePDigit
        rw [Nat.add_mul_div_right _ _ (pow_pos hp_pos m), Nat.div_eq_of_lt ihm.1, zero_add,
            Nat.mod_eq_of_lt hfm_lt]
  refine ⟨h12.1, h12.2, fun htop ↦ ?_⟩
  cases n with
  | zero => simp
  | succ m =>
    have hfm_ne : f m ≠ 0 := by simpa using htop (Nat.succ_pos m)
    have hfm_ge : 1 ≤ f m := Nat.pos_of_ne_zero hfm_ne
    have hge_pow : p ^ m ≤ ∑ i ∈ Finset.range (m + 1), f i * p ^ i := by
      rw [Finset.sum_range_succ]
      have : p ^ m ≤ f m * p ^ m := by simpa using Nat.mul_le_mul_right (p ^ m) hfm_ge
      omega
    have hle_len : (Nat.digits p (∑ i ∈ Finset.range (m + 1), f i * p ^ i)).length ≤ m + 1 :=
      (Nat.digits_length_le_iff hp_gt1 _).2 h12.1
    have hgt_len : m < (Nat.digits p (∑ i ∈ Finset.range (m + 1), f i * p ^ i)).length :=
      (Nat.lt_digits_length_iff hp_gt1 _).2 hge_pow
    omega

/-- Nonstandard base-$p$ digit `hyperBasePDigit p z i : ℕ*` of `z : ℕ*` at hypernatural index
`i : ℕ*` (Goldblatt §18.7, p. 255). -/
def hyperBasePDigit (p : ℕ) (z i : ℕ*) : ℕ* :=
  Germ.map₂ (basePDigit p) z i

/-- Nonstandard base-$p$ partial sum `hyperBasePPartialSum p z k : ℕ*` (`∑_{i < k} z_i p^i`,
Goldblatt §18.7, p. 255). -/
def hyperBasePPartialSum (p : ℕ) (z k : ℕ*) : ℕ* :=
  Germ.map₂ (basePPartialSum p) z k

/-- Exact compatibility between `starSeqPDigit` on `*Seq(p)` and `hyperBasePDigit p`:
`starSeqPDigit ((starSeqPEquivHypernat p).symm z) i = hyperBasePDigit p z i`. -/
@[simp]
theorem starSeqPDigit_symm_eq_hyperBasePDigit (p : ℕ) [Fact p.Prime] (z i : ℕ*) :
    starSeqPDigit ((starSeqPEquivHypernat p).symm z) i = hyperBasePDigit p z i :=
  Germ.inductionOn₂ z i fun u m ↦
    Germ.coe_eq.2 (Eventually.of_forall fun j ↦ getD_digits_eq_basePDigit p (u j) (m j))

/-- Every hypernatural base-$p$ digit `hyperBasePDigit p z i` belongs to `{0, …, p - 1}` and is
therefore equal to a **unique standard** residue `d : Fin p` (`*(ℤ/p) = ℤ/p`, Goldblatt §18.7,
p. 255). -/
theorem existsUnique_fin_hyperBasePDigit (p : ℕ) [Fact p.Prime] (z i : ℕ*) :
    hyperBasePDigit p z i < (p : ℕ*) ∧
    ∃! d : Fin p, hyperBasePDigit p z i = (d.1 : ℕ*) := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hlt : hyperBasePDigit p z i < (p : ℕ*) :=
    Germ.inductionOn₂ z i fun u m ↦
      Germ.coe_lt.2 (Eventually.of_forall fun j ↦ Nat.mod_lt _ hp_pos)
  refine ⟨hlt, ?_⟩
  induction z using Germ.inductionOn with | _ u =>
  induction i using Germ.inductionOn with | _ m =>
  let f : ℕ → Fin p := fun j ↦ ⟨basePDigit p (u j) (m j), Nat.mod_lt _ hp_pos⟩
  obtain ⟨d, hd⟩ := (germConst_bijective_of_finite (Fin p)).2
    (f : Germ (hyperfilter ℕ : Filter ℕ) (Fin p))
  refine ⟨d, ?_, fun d' hd' ↦ ?_⟩
  · have hev : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), d = f j := Germ.coe_eq.1 hd
    exact Germ.coe_eq.2 (hev.mono fun j hj ↦ (congrArg Fin.val hj).symm)
  · have hev1 : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), basePDigit p (u j) (m j) = d'.1 :=
      Germ.coe_eq.1 hd'
    have hev2 : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), d = f j := Germ.coe_eq.1 hd
    obtain ⟨j, hj1, hj2⟩ := (hev1.and hev2).exists
    ext
    exact hj1.symm.trans (congrArg Fin.val hj2).symm

/-- Goldblatt §18.8, **Exercise 18.8(1)** (p. 257): Full internal characterization of `*Seq(p)`:
1. Every `S ∈ StarSeqP p` has digits `< p`, vanishes at indices `≥ starSeqPLength S`, and when
   `0 < starSeqPLength S` has nonzero leading digit `starSeqPDigit S (starSeqPLength S - 1) ≠ 0`;
2. Conversely, for any hypernatural length `N : ℕ*` and any internal sequence
   `F : Germ (hyperfilter ℕ) (ℕ → ℕ)` satisfying `∀ i < N, F(i) < p` and
   `(0 < N → F(N - 1) ≠ 0)`, there exists a **unique** `S ∈ StarSeqP p` with
   `starSeqPLength S = N` and `∀ i < N, starSeqPDigit S i = F(i)`. -/
theorem exercise_18_8_1 (p : ℕ) [Fact p.Prime] :
    (∀ S : StarSeqP p,
      (∀ i : ℕ*, starSeqPDigit S i < (p : ℕ*)) ∧
      (∀ i : ℕ*, starSeqPLength S ≤ i → starSeqPDigit S i = 0) ∧
      (0 < starSeqPLength S → starSeqPDigit S (starSeqPLength S - 1) ≠ 0)) ∧
    (∀ (N : ℕ*) (F : Germ (hyperfilter ℕ : Filter ℕ) (ℕ → ℕ)),
      (∀ i : ℕ*, i < N → Germ.map₂ (fun (f : ℕ → ℕ) (k : ℕ) ↦ f k) F i < (p : ℕ*)) →
      (0 < N → Germ.map₂ (fun (f : ℕ → ℕ) (k : ℕ) ↦ f k) F (N - 1) ≠ 0) →
      ∃! S : StarSeqP p,
        starSeqPLength S = N ∧
        ∀ i : ℕ*, i < N →
          starSeqPDigit S i = Germ.map₂ (fun (f : ℕ → ℕ) (k : ℕ) ↦ f k) F i) := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨fun S ↦ ⟨fun i ↦ ?_, fun i hle ↦ ?_, fun hpos ↦ ?_⟩,
    fun N F hF_lt hF_top ↦ ?_⟩
  · induction S using Germ.inductionOn with | _ s =>
    induction i using Germ.inductionOn with | _ m =>
    refine Germ.coe_lt.2 (Eventually.of_forall fun j ↦ ?_)
    change (s j).1.getD (m j) 0 < p
    rw [← (seqPEquivNat p).left_inv (s j)]
    change (Nat.digits p (Nat.ofDigits p (s j).1)).getD (m j) 0 < p
    rw [getD_digits_eq_basePDigit]
    exact Nat.mod_lt _ hp_pos
  · induction S using Germ.inductionOn with | _ s =>
    induction i using Germ.inductionOn with | _ m =>
    refine Germ.coe_eq.2 ((Germ.coe_le.1 hle).mono fun j hj ↦ ?_)
    change (s j).1.getD (m j) 0 = 0
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj, Option.getD_none]
  · induction S using Germ.inductionOn with | _ s =>
    intro hzero
    have hev_pos : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), 0 < (s j).1.length :=
      Germ.coe_lt.1 hpos
    have hev_z : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ),
        (s j).1.getD ((s j).1.length - 1) 0 = 0 :=
      Germ.coe_eq.1 hzero
    obtain ⟨j, hj_pos, hj_z⟩ := (hev_pos.and hev_z).exists
    have hne_nil : (s j).1 ≠ [] := List.ne_nil_of_length_pos hj_pos
    have hlt_len : (s j).1.length - 1 < (s j).1.length := Nat.sub_lt hj_pos Nat.one_pos
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_len, Option.getD_some,
        ← List.getLast_eq_getElem hne_nil] at hj_z
    exact (s j).2.2 hne_nil hj_z
  · induction N using Germ.inductionOn with | _ nseq =>
    induction F using Germ.inductionOn with | _ fseq =>
    have hev_lt : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), ∀ k < nseq j, fseq j k < p := by
      by_contra hnot
      have hev_bad : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), ∃ k < nseq j, ¬ fseq j k < p := by
        have hnot' : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), ¬ ∀ k < nseq j, fseq j k < p :=
          Ultrafilter.eventually_not.2 hnot
        exact hnot'.mono fun j hj ↦ by
          push Not at hj; obtain ⟨k, hk1, hk2⟩ := hj; exact ⟨k, hk1, not_lt_of_ge hk2⟩
      classical
      let kseq : ℕ → ℕ := fun j ↦
        if h : ∃ k < nseq j, ¬ fseq j k < p then Classical.choose h else 0
      have hk_lt : (kseq : ℕ*) < (nseq : ℕ*) :=
        Germ.coe_lt.2 (hev_bad.mono fun j hj ↦ by
          change kseq j < nseq j
          dsimp only [kseq]
          split_ifs
          exact (Classical.choose_spec hj).1)
      have hfk_lt := hF_lt (kseq : ℕ*) hk_lt
      have hev_fk : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), fseq j (kseq j) < p :=
        Germ.coe_lt.1 hfk_lt
      obtain ⟨j, hj_bad, hj_ok⟩ := (hev_bad.and hev_fk).exists
      have hspec : kseq j < nseq j ∧ ¬ fseq j (kseq j) < p := by
        dsimp only [kseq] at hj_ok ⊢
        split_ifs
        exact Classical.choose_spec hj_bad
      exact hspec.2 hj_ok
    have hev_top : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ),
        0 < nseq j → fseq j (nseq j - 1) ≠ 0 := by
      rcases Ultrafilter.eventually_or.1
          (Eventually.of_forall fun j ↦ eq_zero_or_pos (nseq j)) with hz | hpos
      · exact hz.mono fun j hj hgt ↦ absurd hj hgt.ne'
      · have hN_pos : (0 : ℕ*) < (nseq : ℕ*) := Germ.coe_lt.2 hpos
        have htop_ne := hF_top hN_pos
        have hev_ne : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), fseq j (nseq j - 1) ≠ 0 := by
          by_contra hnot_ne
          apply htop_ne
          exact Germ.coe_eq.2 (Ultrafilter.eventually_not.2 hnot_ne |>.mono fun j hj ↦ not_not.1 hj)
        exact hev_ne.mono fun j hj _ ↦ hj
    classical
    let zseq : ℕ → ℕ := fun j ↦
      if (∀ k < nseq j, fseq j k < p) ∧ (0 < nseq j → fseq j (nseq j - 1) ≠ 0) then
        ∑ k ∈ Finset.range (nseq j), fseq j k * p ^ k
      else 0
    let S : StarSeqP p := ((fun j ↦ natToSeqP p (zseq j)) : ℕ → SeqP p)
    have hS_len : starSeqPLength S = (nseq : ℕ*) := by
      refine Germ.coe_eq.2 ((hev_lt.and hev_top).mono fun j ⟨hj_lt, hj_top⟩ ↦ ?_)
      change (Nat.digits p (zseq j)).length = nseq j
      have hz_eq : zseq j = ∑ k ∈ Finset.range (nseq j), fseq j k * p ^ k := by
        dsimp only [zseq]
        split_ifs
        rfl
      rw [hz_eq]
      exact (digits_sum_range_length_and_digit p (nseq j) (fseq j) hj_lt).2.2 hj_top
    have hS_dig : ∀ i : ℕ*, i < (nseq : ℕ*) →
        starSeqPDigit S i =
          Germ.map₂ (fun (f : ℕ → ℕ) (k : ℕ) ↦ f k)
            (fseq : Germ (hyperfilter ℕ : Filter ℕ) (ℕ → ℕ)) i := by
      intro i hi
      induction i using Germ.inductionOn with | _ m =>
      refine Germ.coe_eq.2
        (((hev_lt.and hev_top).and (Germ.coe_lt.1 hi)).mono fun j ⟨⟨hj_lt, hj_top⟩, hj_m⟩ ↦ ?_)
      change (Nat.digits p (zseq j)).getD (m j) 0 = fseq j (m j)
      rw [getD_digits_eq_basePDigit]
      have hcond : (∀ k < nseq j, fseq j k < p) ∧ (0 < nseq j → fseq j (nseq j - 1) ≠ 0) :=
        ⟨hj_lt, hj_top⟩
      have hz_eq : zseq j = ∑ k ∈ Finset.range (nseq j), fseq j k * p ^ k := by
        dsimp only [zseq]
        split_ifs
        rfl
      rw [hz_eq]
      exact (digits_sum_range_length_and_digit p (nseq j) (fseq j) hj_lt).2.1 (m j) hj_m
    refine ⟨S, ⟨hS_len, hS_dig⟩, fun S' ⟨hS'_len, hS'_dig⟩ ↦ ?_⟩
    induction S' using Germ.inductionOn with | _ s' =>
    by_contra hne
    have hev_neq : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), s' j ≠ natToSeqP p (zseq j) := by
      have hnot_eq : ¬ ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), s' j = natToSeqP p (zseq j) :=
        fun h ↦ hne (Germ.coe_eq.2 h)
      exact Ultrafilter.eventually_not.2 hnot_eq
    have hev_len_eq : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), (s' j).1.length = nseq j :=
      Germ.coe_eq.1 hS'_len
    have hev_len_S : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), (natToSeqP p (zseq j)).1.length = nseq j :=
      Germ.coe_eq.1 hS_len
    have hev_diff : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ),
        ∃ k < nseq j, (s' j).1.getD k 0 ≠ (natToSeqP p (zseq j)).1.getD k 0 := by
      refine ((hev_neq.and hev_len_eq).and hev_len_S).mono fun j ⟨⟨hj_ne, hj_l1⟩, hj_l2⟩ ↦ ?_
      by_contra hall_eq
      push Not at hall_eq
      apply hj_ne
      apply Subtype.ext
      refine List.ext_getElem (hj_l1.trans hj_l2.symm) fun k hk1 hk2 ↦ ?_
      have hget := hall_eq k (hj_l1 ▸ hk1)
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1, Option.getD_some,
           List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2, Option.getD_some] at hget
    let dseq : ℕ → ℕ := fun j ↦
      if h : ∃ k < nseq j, (s' j).1.getD k 0 ≠ (natToSeqP p (zseq j)).1.getD k 0 then
        Classical.choose h
      else 0
    have hd_lt : (dseq : ℕ*) < (nseq : ℕ*) :=
      Germ.coe_lt.2 (hev_diff.mono fun j hj ↦ by
        change dseq j < nseq j
        dsimp only [dseq]
        split_ifs
        exact (Classical.choose_spec hj).1)
    have heq_d : starSeqPDigit (s' : StarSeqP p) (dseq : ℕ*) = starSeqPDigit S (dseq : ℕ*) :=
      (hS'_dig (dseq : ℕ*) hd_lt).trans (hS_dig (dseq : ℕ*) hd_lt).symm
    obtain ⟨j, hj_diff, hj_eq⟩ := (hev_diff.and (Germ.coe_eq.1 heq_d)).exists
    have hspec : dseq j < nseq j ∧
        (s' j).1.getD (dseq j) 0 ≠ (natToSeqP p (zseq j)).1.getD (dseq j) 0 := by
      dsimp only [dseq]
      split_ifs
      exact Classical.choose_spec hj_diff
    exact hspec.2 hj_eq

/-- Goldblatt §18.7, **Result `(v)`** (p. 255):
1. Every hypernatural `z ∈ ℕ*` is congruent modulo `hyperintPow p k` (`p ^ k`) to its base-$p$
   partial sum `hyperBasePPartialSum p z k`;
2. Whenever `n < m` in `ℕ*`, `∑_{i=0}^m z_i p^i ≡ ∑_{i=0}^n z_i p^i (mod p^{n+1})`, i.e.,
   `hyperintPow p (n + 1) ∣ (natToHyperint (hyperBasePPartialSum p z (m + 1)) - natToHyperint (hyperBasePPartialSum p z (n + 1)))`! -/
theorem hyperBasePPartialSum_mod_pow_and_sub_dvd (p : ℕ) [Fact p.Prime] :
    (∀ z k : ℕ*,
      hyperintPow p k ∣ (natToHyperint z - natToHyperint (hyperBasePPartialSum p z k))) ∧
    (∀ z n m : ℕ*, n < m →
      hyperintPow p (n + 1) ∣
        (natToHyperint (hyperBasePPartialSum p z (m + 1)) -
         natToHyperint (hyperBasePPartialSum p z (n + 1)))) := by
  have h1 : ∀ z k : ℕ*,
      hyperintPow p k ∣ (natToHyperint z - natToHyperint (hyperBasePPartialSum p z k)) := by
    intro z k
    induction z using Germ.inductionOn with | _ u =>
    induction k using Germ.inductionOn with | _ m =>
    refine ⟨(((fun j ↦ ((u j / p ^ m j : ℕ) : ℤ)) : ℕ → ℤ) : ℤ*), Germ.coe_eq.2 ?_⟩
    refine Eventually.of_forall fun j ↦ ?_
    change ((u j : ℤ) - ((basePPartialSum p (u j) (m j) : ℕ) : ℤ)) =
      (p : ℤ) ^ (m j) * ((u j / p ^ m j : ℕ) : ℤ)
    rw [basePPartialSum_eq_mod]
    have hdiv := (Nat.div_add_mod (u j) (p ^ m j)).symm
    calc ((u j : ℤ) - ((u j % p ^ m j : ℕ) : ℤ))
        = (((p ^ m j * (u j / p ^ m j) + u j % p ^ m j : ℕ) : ℤ) - ((u j % p ^ m j : ℕ) : ℤ)) := by
          rw [← hdiv]
      _ = (p : ℤ) ^ (m j) * ((u j / p ^ m j : ℕ) : ℤ) := by
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]; ring
  refine ⟨h1, fun z n m hnm ↦ ?_⟩
  have hn_dvd : hyperintPow p (n + 1) ∣
      (natToHyperint z - natToHyperint (hyperBasePPartialSum p z (n + 1))) := h1 z (n + 1)
  have hm_dvd : hyperintPow p (m + 1) ∣
      (natToHyperint z - natToHyperint (hyperBasePPartialSum p z (m + 1))) := h1 z (m + 1)
  have hle : n + 1 ≤ m + 1 := by simpa [add_comm] using add_le_add_right hnm.le 1
  have hm_dvd' : hyperintPow p (n + 1) ∣
      (natToHyperint z - natToHyperint (hyperBasePPartialSum p z (m + 1))) :=
    (hyperintPow_dvd_of_le p hle).trans hm_dvd
  have hsub := dvd_sub hn_dvd hm_dvd'
  have heq : (natToHyperint z - natToHyperint (hyperBasePPartialSum p z (n + 1))) -
      (natToHyperint z - natToHyperint (hyperBasePPartialSum p z (m + 1))) =
      natToHyperint (hyperBasePPartialSum p z (m + 1)) -
        natToHyperint (hyperBasePPartialSum p z (n + 1)) := by ring
  rwa [heq] at hsub

/-- Goldblatt §18.7, **Theorem 18.7.1** & §18.8, **Exercise 18.8(2)** (pp. 256–257):
Two hypernaturals `z, w ∈ ℕ*` are **$p$-adically infinitely close**
(`IsPadicInfinitesimalZ p (natToHyperint z - natToHyperint w)`) if and only if their hyperfinite
base-$p$ expansions have identical digits at every standard degree `n : ℕ`:
`∀ n : ℕ, hyperBasePDigit p z (n : ℕ*) = hyperBasePDigit p w (n : ℕ*)`! -/
theorem padicInfClose_hypernat_iff_eq_basePDigits (p : ℕ) [Fact p.Prime] (z w : ℕ*) :
    IsPadicInfinitesimalZ p (natToHyperint z - natToHyperint w) ↔
      ∀ n : ℕ, hyperBasePDigit p z (n : ℕ*) = hyperBasePDigit p w (n : ℕ*) := by
  rw [(isPadicInfinitesimalZ_tfae p (natToHyperint z - natToHyperint w)).1,
      (isPadicInfinitesimalZ_tfae p (natToHyperint z - natToHyperint w)).2.1]
  induction z using Germ.inductionOn with | _ u =>
  induction w using Germ.inductionOn with | _ v =>
  constructor
  · intro hdvd n
    have hcast : (((p : ℤ) ^ (n + 1) : ℤ) : ℤ*) = (p : ℤ*) ^ (n + 1) := by push_cast; rfl
    have hev_dvd : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ),
        ((p : ℤ) ^ (n + 1)) ∣ ((u j : ℤ) - (v j : ℤ)) :=
      (intCast_dvd_hyperint_iff ((p : ℤ) ^ (n + 1)) (fun j ↦ (u j : ℤ) - (v j : ℤ))).1
        (hcast.symm ▸ hdvd (n + 1))
    refine Germ.coe_eq.2 (hev_dvd.mono fun j hj ↦ ?_)
    have hj_neg : (((p ^ (n + 1) : ℕ) : ℤ)) ∣ ((v j : ℤ) - (u j : ℤ)) := by
      have := dvd_neg.2 hj
      simpa [neg_sub] using this
    have hmod_z : ((u j : ℤ) % ((p ^ (n + 1) : ℕ) : ℤ)) =
        ((v j : ℤ) % ((p ^ (n + 1) : ℕ) : ℤ)) :=
      Int.modEq_iff_dvd.2 hj_neg
    rw [← Int.natCast_emod, ← Int.natCast_emod] at hmod_z
    have hmod_nat : u j % p ^ (n + 1) = v j % p ^ (n + 1) := Int.ofNat.inj hmod_z
    change basePDigit p (u j) n = basePDigit p (v j) n
    have hdig : ∀ x : ℕ, basePDigit p x n = (x % p ^ (n + 1)) / p ^ n := fun x ↦ by
      unfold basePDigit
      rw [pow_succ, Nat.mod_mul_right_div_self]
    rw [hdig, hmod_nat, ← hdig]
  · intro hdig k
    have hall : ∀ d ∈ Finset.range k,
        ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), basePDigit p (u j) d = basePDigit p (v j) d :=
      fun d _ ↦ Germ.coe_eq.1 (hdig d)
    have hev := (Filter.eventually_all_finset (Finset.range k)).2 hall
    have hcast : (((p : ℤ) ^ k : ℤ) : ℤ*) = (p : ℤ*) ^ k := by push_cast; rfl
    rw [← hcast]
    refine (intCast_dvd_hyperint_iff ((p : ℤ) ^ k) (fun j ↦ (u j : ℤ) - (v j : ℤ))).2 ?_
    refine hev.mono fun j hj ↦ ?_
    have hsum_eq : basePPartialSum p (u j) k = basePPartialSum p (v j) k :=
      Finset.sum_congr rfl fun d hd ↦ by rw [hj d hd]
    rw [basePPartialSum_eq_mod, basePPartialSum_eq_mod] at hsum_eq
    have hmod_z : ((v j : ℤ) % ((p ^ k : ℕ) : ℤ)) = ((u j : ℤ) % ((p ^ k : ℕ) : ℤ)) := by
      rw [← Int.natCast_emod, ← Int.natCast_emod, hsum_eq]
    have hdvd_vu : (((p ^ k : ℕ) : ℤ)) ∣ ((u j : ℤ) - (v j : ℤ)) :=
      Int.modEq_iff_dvd.1 hmod_z
    simpa using hdvd_vu

/-- Explicit positive-hyperinteger specialization of **Theorem 18.7.1 & Exercise 18.8(2)**
(Goldblatt pp. 256–257). -/
theorem theorem_18_7_1_and_exercise_18_8_2 (p : ℕ) [Fact p.Prime] {z w : ℕ*}
    (_hz : 0 < z) (_hw : 0 < w) :
    IsPadicInfinitesimalZ p (natToHyperint z - natToHyperint w) ↔
      ∀ n : ℕ, hyperBasePDigit p z (n : ℕ*) = hyperBasePDigit p w (n : ℕ*) :=
  padicInfClose_hypernat_iff_eq_basePDigits p z w

/-- Goldblatt §18.7 (pp. 256–257): **Hyperfinite Base-$p$ Representation of Every $p$-adic Integer**
— for every `a ∈ ℤ_[p]`, there exists a strictly positive hypernatural `x ∈ ℕ*` (`0 < x`) such that:
1. `thetaP p (natToHyperint x) = a`,
2. For every standard degree `n : ℕ`, `hyperBasePDigit p x (n : ℕ*)` equals the standard $n$-th
   base-$p$ Hensel digit `basePDigit p (a.appr (n + 1)) n` of `a`, and
3. Any `y ∈ ℕ*` represents `a` (`thetaP p (natToHyperint y) = a`) if and only if `y` and `x` have
   identical base-$p$ digits at every standard degree `n : ℕ`! -/
theorem exists_pos_hypernat_baseP_expansion_of_padicInt (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) :
    ∃ x : ℕ*, 0 < x ∧ thetaP p (natToHyperint x) = a ∧
      (∀ n : ℕ, hyperBasePDigit p x (n : ℕ*) = ((basePDigit p (a.appr (n + 1)) n : ℕ) : ℕ*)) ∧
      (∀ y : ℕ*, thetaP p (natToHyperint y) = a ↔
        ∀ n : ℕ, hyperBasePDigit p y (n : ℕ*) = hyperBasePDigit p x (n : ℕ*)) := by
  have : ∀ n : ℕ, NeZero (p ^ n) := neZero_pow_of_prime p
  obtain ⟨x, hx_pos, hx_theta⟩ := exists_pos_hypernat_thetaP_eq p a
  refine ⟨x, hx_pos, hx_theta, fun n ↦ ?_, fun y ↦ ?_⟩
  · set m := a.appr (n + 1)
    have happr_span : a - (m : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ (n + 1)} :=
      PadicInt.appr_spec (n + 1) a
    have hker : a - (m : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (n + 1)) := by
      rwa [PadicInt.ker_toZModPow]
    have htheta_diff : thetaP p (natToHyperint x - natToHyperint (m : ℕ*)) = a - (m : ℤ_[p]) := by
      have hm : natToHyperint (m : ℕ*) = (m : ℤ*) := rfl
      rw [map_sub, hx_theta, hm, thetaP_natCast]
    have hzmod_zero : hyperZModHom (p ^ (n + 1))
        (natToHyperint x - natToHyperint (m : ℕ*)) = 0 := by
      rw [← toZModPow_thetaP, htheta_diff]
      exact hker
    have hdvd : ((p ^ (n + 1) : ℕ) : ℤ*) ∣ (natToHyperint x - natToHyperint (m : ℕ*)) :=
      (hyperZModHom_eq_zero_iff_dvd (p ^ (n + 1)) _).1 hzmod_zero
    induction x using Germ.inductionOn with | _ u =>
    have hev_dvd : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ),
        (((p ^ (n + 1) : ℕ) : ℤ)) ∣ ((u j : ℤ) - (m : ℤ)) :=
      (intCast_dvd_hyperint_iff ((p ^ (n + 1) : ℕ) : ℤ) (fun j ↦ (u j : ℤ) - (m : ℤ))).1 hdvd
    refine Germ.coe_eq.2 (hev_dvd.mono fun j hj ↦ ?_)
    have hj_neg : (((p ^ (n + 1) : ℕ) : ℤ)) ∣ ((m : ℤ) - (u j : ℤ)) := by
      have := dvd_neg.2 hj
      simpa [neg_sub] using this
    have hmod_z : ((u j : ℤ) % ((p ^ (n + 1) : ℕ) : ℤ)) =
        ((m : ℤ) % ((p ^ (n + 1) : ℕ) : ℤ)) :=
      Int.modEq_iff_dvd.2 hj_neg
    rw [← Int.natCast_emod, ← Int.natCast_emod] at hmod_z
    have hmod_nat : u j % p ^ (n + 1) = m % p ^ (n + 1) := Int.ofNat.inj hmod_z
    change basePDigit p (u j) n = basePDigit p m n
    have hdig : ∀ q : ℕ, basePDigit p q n = (q % p ^ (n + 1)) / p ^ n := fun q ↦ by
      unfold basePDigit
      rw [pow_succ, Nat.mod_mul_right_div_self]
    rw [hdig, hmod_nat, ← hdig]
  · rw [← hx_theta, ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, ker_thetaP,
        mem_padicInfinitesimalIdealZ_iff]
    exact padicInfClose_hypernat_iff_eq_basePDigits p y x


end Goldblatt.Ch18
