import LecturesOnTheHyperreals.Ch03_UltrapowerConstruction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Chapter 5: Hyperreals Great and Small

Formalization of Robert Goldblatt, *Lectures on the Hyperreals*, Chapter 5 (pp. 49–60):

* **§5.1** Limited (`IsLimited`), unlimited (`IsUnlimited`, `IsPosUnlimited`, `IsNegUnlimited`),
  infinitesimal (`IsInfinitesimal`, `IsPosInfinitesimal`, `IsNegInfinitesimal`), and appreciable
  (`IsAppreciable`) hyperreals, plus `IsUnlimitedNat` on `ℕ*`.
* **§5.2** Complete arithmetic rules for sums, opposites, products, reciprocals, quotients, and
  square roots; the subring `LimitedSubring` (`𝕃`) and ideal `InfinitesimalIdeal` (`𝕀`).
* **§5.4–5.5** Infinite closeness (`InfClose`, `≈ₕ`), limited distance (`LimDist`, `∼ₗ`), halos,
  galaxies, Real Comparison Principles, and Exercises 5.5(1)–(6).
* **§5.6–5.7** Existence and uniqueness of shadows (`shadow`, Theorem 5.6.1), homomorphism laws
  (Theorem 5.6.2), the quotient isomorphism `𝕃 ⧸ 𝕀 ≃+* ℝ` and maximality of `𝕀` (Theorem 5.6.3),
  and Exercises 5.7(1)–(4) (including trigonometric infinitesimals and `*ℚ` quotient).
* **§5.8–5.9** Cauchy completeness and Dedekind LUB from existence of shadows (Theorem 5.8.1 &
  Exercise 5.9).
* **§5.10–5.12** Structure of `ℕ*` and `*ℕ`-galaxies (copies of `ℤ`, dense with no endpoints),
  hyperfactorials, hyperprimes `*Π`, Exercises 5.11(2)–(3), and the nonstandard proof of Euclid's
  theorem on infinitely many primes (§5.12).
-/

noncomputable section

namespace Goldblatt

open Filter
open Hyperreal (ofSeq ofSeq_lt_ofSeq ofSeq_le_ofSeq ofSeq_surjective)
open scoped Topology Classical

@[simp, norm_cast]
theorem coe_natCast_hyperreal (n : ℕ) : ((n : ℝ) : ℝ*) = (n : ℝ*) := rfl

@[simp, norm_cast]
theorem coe_intCast_hyperreal (z : ℤ) : ((z : ℝ) : ℝ*) = (z : ℝ*) := rfl

@[simp, norm_cast]
theorem coe_ratCast_hyperreal (q : ℚ) : ((q : ℝ) : ℝ*) = (q : ℝ*) := by
  rw [Rat.cast_def, Hyperreal.coe_div, coe_intCast_hyperreal, coe_natCast_hyperreal, ← Rat.cast_def]

/-! ## §5.1 Limited, Unlimited, Infinitesimal, and Appreciable Hyperreals -/

/-- Goldblatt §5.1 (p. 49): `b ∈ ℝ*` is limited (`b ∈ 𝕃`) if `|b| < n` for some `n ∈ ℕ`. -/
def IsLimited (b : ℝ*) : Prop := ∃ n : ℕ, |b| < (n : ℝ*)

/-- Goldblatt §5.1 (p. 49): `b ∈ ℝ*` is positive unlimited if `r < b` for all `r ∈ ℝ`. -/
def IsPosUnlimited (b : ℝ*) : Prop := ∀ r : ℝ, (r : ℝ*) < b

/-- Goldblatt §5.1 (p. 49): `b ∈ ℝ*` is negative unlimited if `b < r` for all `r ∈ ℝ`. -/
def IsNegUnlimited (b : ℝ*) : Prop := ∀ r : ℝ, b < (r : ℝ*)

/-- Goldblatt §5.1 (p. 50): `b ∈ ℝ*` is unlimited if `|b| > n` for all `n ∈ ℕ`. -/
def IsUnlimited (b : ℝ*) : Prop := ∀ n : ℕ, (n : ℝ*) < |b|

/-- Goldblatt §5.1 (p. 49): `b ∈ ℝ*` is positive infinitesimal if `0 < b < r` for all `r > 0` in `ℝ`. -/
def IsPosInfinitesimal (b : ℝ*) : Prop := 0 < b ∧ ∀ r : ℝ, 0 < r → b < (r : ℝ*)

/-- Goldblatt §5.1 (p. 49): `b ∈ ℝ*` is negative infinitesimal if `r < b < 0` for all `r < 0` in `ℝ`. -/
def IsNegInfinitesimal (b : ℝ*) : Prop := b < 0 ∧ ∀ r : ℝ, r < 0 → (r : ℝ*) < b

/-- Goldblatt §5.1 (p. 50): `b ∈ ℝ*` is infinitesimal (`b ∈ 𝕀`) if `|b| < r` for every positive real `r`. -/
def IsInfinitesimal (b : ℝ*) : Prop := ∀ r : ℝ, 0 < r → |b| < (r : ℝ*)

/-- Goldblatt §5.1 (p. 50): `b ∈ ℝ*` is appreciable if it is limited and not infinitesimal. -/
def IsAppreciable (b : ℝ*) : Prop := IsLimited b ∧ ¬ IsInfinitesimal b

/-- Goldblatt §5.1 (p. 50): `N ∈ ℕ*` is unlimited (`N ∈ *ℕ_∞`) if `n < N` for every standard `n ∈ ℕ`. -/
def IsUnlimitedNat (N : ℕ*) : Prop := ∀ n : ℕ, (n : ℕ*) < N

theorem isLimited_iff_exists_real {b : ℝ*} :
    IsLimited b ↔ ∃ r s : ℝ, (r : ℝ*) < b ∧ b < (s : ℝ*) := by
  constructor
  · rintro ⟨n, hn⟩
    rcases abs_lt.1 hn with ⟨hl, hr⟩
    exact ⟨-(n : ℝ), (n : ℝ), by simpa using hl, by simpa using hr⟩
  · rintro ⟨r, s, hr, hs⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (max |r| |s|)
    refine ⟨n, abs_lt.2 ⟨?_, ?_⟩⟩
    · have h1 : -(n : ℝ) < r := by
        have : |r| < (n : ℝ) := (le_max_left |r| |s|).trans_lt hn
        exact (neg_lt_of_abs_lt this)
      exact (Hyperreal.coe_lt_coe.2 h1).trans hr
    · have h2 : s < (n : ℝ) := (le_abs_self s).trans_lt ((le_max_right |r| |s|).trans_lt hn)
      exact hs.trans (Hyperreal.coe_lt_coe.2 h2)

theorem isLimited_iff_abs_le_real {b : ℝ*} :
    IsLimited b ↔ ∃ B : ℝ, 0 ≤ B ∧ |b| ≤ (B : ℝ*) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, Nat.cast_nonneg n, hn.le⟩
  · rintro ⟨B, _, hB⟩
    obtain ⟨n, hn⟩ := exists_nat_gt B
    exact ⟨n, hB.trans_lt (by exact_mod_cast hn)⟩

theorem isUnlimited_iff_not_isLimited {b : ℝ*} :
    IsUnlimited b ↔ ¬ IsLimited b := by
  unfold IsUnlimited IsLimited
  push Not
  constructor
  · intro h n
    exact (h n).le
  · intro h n
    exact (h (n + 1)).trans_lt' (by exact_mod_cast Nat.lt_succ_self n)

theorem isUnlimited_iff_pos_or_neg {b : ℝ*} :
    IsUnlimited b ↔ IsPosUnlimited b ∨ IsNegUnlimited b := by
  constructor
  · intro hb
    rcases le_or_gt 0 b with hpos | hneg
    · left
      intro r
      obtain ⟨n, hn⟩ := exists_nat_gt r
      have hbn : (n : ℝ*) < b := by simpa [abs_of_nonneg hpos] using hb n
      exact (Hyperreal.coe_lt_coe.2 hn).trans (by simpa using hbn)
    · right
      intro r
      obtain ⟨n, hn⟩ := exists_nat_gt (-r)
      have hbn : (n : ℝ*) < -b := by simpa [abs_of_neg hneg] using hb n
      have h1 : b < -(n : ℝ*) := lt_neg.1 hbn
      have h2 : -(n : ℝ*) < (r : ℝ*) := by
        have : -(n : ℝ) < r := neg_lt.1 hn
        simpa using Hyperreal.coe_lt_coe.2 this
      exact h1.trans h2
  · rintro (hpos | hneg) n
    · have h1 : (n : ℝ*) < b := by simpa using hpos n
      exact h1.trans_le (le_abs_self b)
    · have h1 : b < -(n : ℝ*) := by simpa using hneg (-(n : ℝ))
      have h2 : (n : ℝ*) < -b := lt_neg.2 h1
      exact h2.trans_le (neg_le_abs b)

theorem isInfinitesimal_iff_nat {b : ℝ*} :
    IsInfinitesimal b ↔ ∀ n : ℕ, 0 < n → |b| < (((n : ℝ)⁻¹ : ℝ) : ℝ*) := by
  constructor
  · intro hb n hn
    exact hb (n : ℝ)⁻¹ (inv_pos.2 (Nat.cast_pos.2 hn))
  · intro hb r hr
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
    have hn_pos : 0 < n + 1 := Nat.succ_pos n
    have h1 := hb (n + 1) hn_pos
    have h2 : (((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) < r := by simpa [one_div] using hn
    exact h1.trans (by exact_mod_cast h2)

theorem isInfinitesimal_iff_trichotomy {b : ℝ*} :
    IsInfinitesimal b ↔ IsPosInfinitesimal b ∨ IsNegInfinitesimal b ∨ b = 0 := by
  constructor
  · intro hb
    rcases lt_trichotomy 0 b with hpos | rfl | hneg
    · exact Or.inl ⟨hpos, fun r hr ↦ (le_abs_self b).trans_lt (hb r hr)⟩
    · exact Or.inr (Or.inr rfl)
    · refine Or.inr (Or.inl ⟨hneg, fun r hr ↦ ?_⟩)
      have h1 : -b < (-r : ℝ*) := by
        simpa [abs_of_neg hneg] using hb (-r) (neg_pos.2 hr)
      linarith
  · rintro (⟨hpos, h⟩ | ⟨hneg, h⟩ | rfl)
    · intro r hr
      rw [abs_of_pos hpos]
      exact h r hr
    · intro r hr
      rw [abs_of_neg hneg]
      have hlt : -(r : ℝ*) < b := by simpa using h (-r) (neg_lt_zero.2 hr)
      exact neg_lt.1 hlt
    · intro r hr
      simpa using Hyperreal.coe_pos.2 hr

theorem isInfinitesimal_zero : IsInfinitesimal 0 :=
  isInfinitesimal_iff_trichotomy.2 (Or.inr (Or.inr rfl))

theorem isInfinitesimal_epsilon : IsInfinitesimal Hyperreal.epsilon :=
  isInfinitesimal_iff_trichotomy.2 (Or.inl ⟨Hyperreal.epsilon_pos, fun _ hr ↦ Hyperreal.epsilon_lt_of_pos hr⟩)

theorem isUnlimited_omega : IsUnlimited Hyperreal.omega :=
  isUnlimited_iff_pos_or_neg.2 (Or.inl Hyperreal.coe_lt_omega)

theorem IsInfinitesimal.isLimited {b : ℝ*} (hb : IsInfinitesimal b) : IsLimited b :=
  ⟨1, by simpa using hb 1 one_pos⟩

@[simp]
theorem isLimited_coe (r : ℝ) : IsLimited (r : ℝ*) := by
  obtain ⟨n, hn⟩ := exists_nat_gt |r|
  refine ⟨n, ?_⟩
  rw [← Hyperreal.coe_abs]
  exact_mod_cast hn

@[simp]
theorem isInfinitesimal_coe_iff {r : ℝ} : IsInfinitesimal (r : ℝ*) ↔ r = 0 := by
  constructor
  · intro hr
    by_contra hne
    have hpos : 0 < |r| := abs_pos.2 hne
    have hlt : |(r : ℝ*)| < ((|r| / 2 : ℝ) : ℝ*) := hr (|r| / 2) (half_pos hpos)
    rw [← Hyperreal.coe_abs, Hyperreal.coe_lt_coe] at hlt
    linarith
  · rintro rfl
    exact isInfinitesimal_zero

theorem isAppreciable_coe_iff {r : ℝ} : IsAppreciable (r : ℝ*) ↔ r ≠ 0 := by
  simp [IsAppreciable, isLimited_coe, isInfinitesimal_coe_iff]

theorem isAppreciable_iff_pos_real_bounds {b : ℝ*} :
    IsAppreciable b ↔ ∃ r s : ℝ, 0 < r ∧ (r : ℝ*) < |b| ∧ |b| < (s : ℝ*) := by
  constructor
  · rintro ⟨⟨n, hn⟩, hnot⟩
    unfold IsInfinitesimal at hnot
    push Not at hnot
    obtain ⟨r, hr, hrb⟩ := hnot
    exact ⟨r / 2, n, half_pos hr, (Hyperreal.coe_lt_coe.2 (half_lt_self hr)).trans_le hrb,
      by simpa using hn⟩
  · rintro ⟨r, s, hr, hrb, hbs⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨n, hn⟩ := exists_nat_gt s
      exact ⟨n, hbs.trans (by simpa using Hyperreal.coe_lt_coe.2 hn)⟩
    · intro hinf
      exact lt_irrefl |b| ((hinf r hr).trans hrb)

/-! ## §5.2 Arithmetic of Hyperreals, `LimitedSubring`, and `InfinitesimalIdeal` -/

theorem IsInfinitesimal.neg {ε : ℝ*} (hε : IsInfinitesimal ε) : IsInfinitesimal (-ε) := by
  intro r hr
  simpa using hε r hr

theorem IsInfinitesimal.abs {ε : ℝ*} (hε : IsInfinitesimal ε) : IsInfinitesimal |ε| := by
  intro r hr
  simpa using hε r hr

theorem IsInfinitesimal.add {ε δ : ℝ*} (hε : IsInfinitesimal ε) (hδ : IsInfinitesimal δ) :
    IsInfinitesimal (ε + δ) := by
  intro r hr
  have h1 := hε (r / 2) (half_pos hr)
  have h2 := hδ (r / 2) (half_pos hr)
  have hsum : ((r / 2 : ℝ) : ℝ*) + ((r / 2 : ℝ) : ℝ*) = (r : ℝ*) := by
    rw [← Hyperreal.coe_add, add_halves]
  exact (abs_add_le ε δ).trans_lt (by linarith)

theorem IsInfinitesimal.sub {ε δ : ℝ*} (hε : IsInfinitesimal ε) (hδ : IsInfinitesimal δ) :
    IsInfinitesimal (ε - δ) := by
  rw [sub_eq_add_neg]
  exact hε.add hδ.neg

theorem isInfinitesimal_of_abs_le {x ε : ℝ*} (hε : IsInfinitesimal ε) (hle : |x| ≤ |ε|) :
    IsInfinitesimal x :=
  fun r hr ↦ hle.trans_lt (hε r hr)

theorem IsLimited.neg {b : ℝ*} (hb : IsLimited b) : IsLimited (-b) := by
  rcases hb with ⟨n, hn⟩
  exact ⟨n, by simpa using hn⟩

theorem IsLimited.abs {b : ℝ*} (hb : IsLimited b) : IsLimited |b| := by
  rcases hb with ⟨n, hn⟩
  exact ⟨n, by simpa using hn⟩

theorem isLimited_of_abs_le {x b : ℝ*} (hb : IsLimited b) (hle : |x| ≤ |b|) : IsLimited x := by
  rcases hb with ⟨n, hn⟩
  exact ⟨n, hle.trans_lt hn⟩

theorem IsLimited.add {b c : ℝ*} (hb : IsLimited b) (hc : IsLimited c) : IsLimited (b + c) := by
  rcases hb with ⟨m, hm⟩
  rcases hc with ⟨n, hn⟩
  refine ⟨m + n, ?_⟩
  have hmn : ((m + n : ℕ) : ℝ*) = (m : ℝ*) + (n : ℝ*) := by push_cast; rfl
  rw [hmn]
  exact (abs_add_le b c).trans_lt (add_lt_add hm hn)

theorem IsLimited.sub {b c : ℝ*} (hb : IsLimited b) (hc : IsLimited c) : IsLimited (b - c) := by
  rw [sub_eq_add_neg]
  exact hb.add hc.neg

theorem IsLimited.mul {b c : ℝ*} (hb : IsLimited b) (hc : IsLimited c) : IsLimited (b * c) := by
  rcases hb with ⟨m, hm⟩
  rcases hc with ⟨n, hn⟩
  refine ⟨m * n, ?_⟩
  rw [abs_mul]
  have hmn : ((m * n : ℕ) : ℝ*) = (m : ℝ*) * (n : ℝ*) := by push_cast; rfl
  rw [hmn]
  exact mul_lt_mul'' hm hn (abs_nonneg b) (abs_nonneg c)

theorem IsInfinitesimal.mul_isLimited {ε b : ℝ*} (hε : IsInfinitesimal ε) (hb : IsLimited b) :
    IsInfinitesimal (ε * b) := by
  rcases hb with ⟨n, hn⟩
  intro r hr
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hb' : |b| < (((n : ℝ) + 1 : ℝ) : ℝ*) := by
    have : (n : ℝ*) < (((n : ℝ) + 1 : ℝ) : ℝ*) := by exact_mod_cast lt_add_one (n : ℝ)
    exact hn.trans this
  have hε' := hε (r / ((n : ℝ) + 1)) (div_pos hr hn1)
  rw [abs_mul]
  calc |ε| * |b|
      < ((r / ((n : ℝ) + 1) : ℝ) : ℝ*) * (((n : ℝ) + 1 : ℝ) : ℝ*) :=
        mul_lt_mul'' hε' hb' (abs_nonneg ε) (abs_nonneg b)
    _ = (r : ℝ*) := by
        rw [← Hyperreal.coe_mul, div_mul_cancel₀ r hn1.ne']

theorem IsLimited.mul_isInfinitesimal {b ε : ℝ*} (hb : IsLimited b) (hε : IsInfinitesimal ε) :
    IsInfinitesimal (b * ε) := by
  rw [mul_comm]
  exact hε.mul_isLimited hb

theorem IsInfinitesimal.mul {ε δ : ℝ*} (hε : IsInfinitesimal ε) (hδ : IsInfinitesimal δ) :
    IsInfinitesimal (ε * δ) :=
  hε.mul_isLimited hδ.isLimited

theorem IsAppreciable.add_isInfinitesimal {b ε : ℝ*} (hb : IsAppreciable b)
    (hε : IsInfinitesimal ε) : IsAppreciable (b + ε) := by
  refine ⟨hb.1.add hε.isLimited, fun hsum ↦ hb.2 ?_⟩
  have hbeq : b = (b + ε) - ε := by ring
  rw [hbeq]
  exact hsum.sub hε

theorem IsUnlimited.neg {H : ℝ*} (hH : IsUnlimited H) : IsUnlimited (-H) := by
  intro n
  simpa using hH n

theorem IsUnlimited.add_isLimited {H b : ℝ*} (hH : IsUnlimited H) (hb : IsLimited b) :
    IsUnlimited (H + b) := by
  rw [isUnlimited_iff_not_isLimited] at hH ⊢
  intro hsum
  apply hH
  have : H = (H + b) - b := by ring
  rw [this]
  exact hsum.sub hb

/-- Goldblatt §5.2 (p. 51): Reciprocal of a nonzero infinitesimal is unlimited, and conversely. -/
theorem isUnlimited_inv_iff_isInfinitesimal {ε : ℝ*} (hε : ε ≠ 0) :
    IsUnlimited ε⁻¹ ↔ IsInfinitesimal ε := by
  have habs_pos : 0 < |ε| := abs_pos.2 hε
  constructor
  · intro hinv
    rw [isInfinitesimal_iff_nat]
    intro n hn
    have hn_pos : (0 : ℝ*) < (n : ℝ*) := by exact_mod_cast hn
    have hlt : (n : ℝ*) < 1 / |ε| := by simpa [abs_inv, one_div] using hinv n
    have hmul : (n : ℝ*) * |ε| < 1 := (lt_div_iff₀ habs_pos).1 hlt
    have hdiv : |ε| < 1 / (n : ℝ*) := (lt_div_iff₀' hn_pos).2 hmul
    simpa [one_div] using hdiv
  · intro hinf n
    rcases eq_or_ne n 0 with rfl | hn0
    · simpa [abs_inv] using inv_pos.2 habs_pos
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hlt : |ε| < (((n : ℝ)⁻¹ : ℝ) : ℝ*) := (isInfinitesimal_iff_nat.1 hinf) n hn_pos
      have hn_rpos : (0 : ℝ*) < (n : ℝ*) := by exact_mod_cast hn_pos
      have hmul : |ε| * (n : ℝ*) < 1 := by
        have hlt' : |ε| < 1 / (n : ℝ*) := by simpa [one_div] using hlt
        exact (lt_div_iff₀ hn_rpos).1 hlt'
      rw [abs_inv, ← one_div]
      exact (lt_div_iff₀ habs_pos).2 (by rwa [mul_comm])

theorem IsUnlimited.inv_isInfinitesimal {H : ℝ*} (hH : IsUnlimited H) : IsInfinitesimal H⁻¹ := by
  have hne : H ≠ 0 := by
    intro h0
    have := hH 0
    simp [h0] at this
  exact (isUnlimited_inv_iff_isInfinitesimal (inv_ne_zero hne)).1 (by simpa using hH)

theorem IsAppreciable.ne_zero {b : ℝ*} (hb : IsAppreciable b) : b ≠ 0 := by
  intro h0
  subst h0
  exact hb.2 isInfinitesimal_zero

theorem IsAppreciable.inv {b : ℝ*} (hb : IsAppreciable b) : IsAppreciable b⁻¹ := by
  have hne := hb.ne_zero
  refine ⟨?_, ?_⟩
  · by_contra hnot
    have hunl : IsUnlimited b⁻¹ := isUnlimited_iff_not_isLimited.2 hnot
    exact hb.2 ((isUnlimited_inv_iff_isInfinitesimal hne).1 hunl)
  · intro hinf
    have hunl : IsUnlimited b⁻¹⁻¹ := (isUnlimited_inv_iff_isInfinitesimal (inv_ne_zero hne)).2 hinf
    rw [inv_inv] at hunl
    exact (isUnlimited_iff_not_isLimited.1 hunl) hb.1

theorem IsAppreciable.mul {b c : ℝ*} (hb : IsAppreciable b) (hc : IsAppreciable c) :
    IsAppreciable (b * c) := by
  refine ⟨hb.1.mul hc.1, fun hinf ↦ hc.2 ?_⟩
  have hceq : c = b⁻¹ * (b * c) := by field_simp [hb.ne_zero]
  rw [hceq]
  exact hb.inv.1.mul_isInfinitesimal hinf

/-- Goldblatt §5.2 (p. 51): Square root of a positive infinitesimal is infinitesimal. -/
theorem isInfinitesimal_starFun_sqrt {ε : ℝ*} (hpos : 0 ≤ ε) (hε : IsInfinitesimal ε) :
    IsInfinitesimal (starFun Real.sqrt ε) := by
  intro r hr
  have hsq : ε < ((r ^ 2 : ℝ) : ℝ*) := by
    have := hε (r ^ 2) (sq_pos_of_pos hr)
    rwa [abs_of_nonneg hpos] at this
  rcases ofSeq_surjective ε with ⟨s, rfl⟩
  have hs0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 ≤ s n := ofSeq_le_ofSeq.1 hpos
  have hsr : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), s n < r ^ 2 := ofSeq_lt_ofSeq.1 hsq
  have hsqrt_nn : 0 ≤ starFun Real.sqrt (ofSeq s) :=
    ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ Real.sqrt_nonneg (s n))
  rw [abs_of_nonneg hsqrt_nn]
  refine ofSeq_lt_ofSeq.2 ((hs0.and hsr).mono fun n ⟨hn0, hnr⟩ ↦ ?_)
  exact (Real.sqrt_lt' hr).2 hnr

/-- Goldblatt §5.2 (p. 51): The ring `𝕃` of limited hyperreals. -/
def LimitedSubring : Subring ℝ* where
  carrier := {b : ℝ* | IsLimited b}
  mul_mem' ha hb := ha.mul hb
  one_mem' := by simpa using isLimited_coe 1
  add_mem' ha hb := ha.add hb
  zero_mem' := by simpa using isLimited_coe 0
  neg_mem' ha := ha.neg

/-- Goldblatt §5.2 (p. 51): The ideal `𝕀` of infinitesimals inside the ring `𝕃` of limited numbers. -/
def InfinitesimalIdeal : Ideal LimitedSubring where
  carrier := {x : LimitedSubring | IsInfinitesimal x.1}
  add_mem' ha hb := ha.add hb
  zero_mem' := isInfinitesimal_zero
  smul_mem' c _ hx := c.2.mul_isInfinitesimal hx

/-! ## §5.4–5.5 Halos, Galaxies, Infinite Closeness, and Real Comparisons -/

/-- Goldblatt §5.4 (p. 52): `b` is infinitely close to `c` (`b ≈ₕ c`) if `b - c` is infinitesimal. -/
def InfClose (b c : ℝ*) : Prop := IsInfinitesimal (b - c)

/-- Goldblatt §5.4 (p. 52): `b` and `c` are of limited distance apart (`b ∼ₗ c`) if `b - c` is limited. -/
def LimDist (b c : ℝ*) : Prop := IsLimited (b - c)

@[inherit_doc] infix:50 " ≈ₕ " => InfClose
@[inherit_doc] infix:50 " ∼ₗ " => LimDist

/-- Goldblatt §5.4 (p. 52): The halo (monad) `hal(b) = {c ∈ ℝ* | b ≈ₕ c}`. -/
def halo (b : ℝ*) : Set ℝ* := {c : ℝ* | b ≈ₕ c}

/-- Goldblatt §5.4 (p. 52): The galaxy `gal(b) = {c ∈ ℝ* | b ∼ₗ c}`. -/
def galaxy (b : ℝ*) : Set ℝ* := {c : ℝ* | b ∼ₗ c}

@[refl]
theorem InfClose.refl (b : ℝ*) : b ≈ₕ b := by
  simpa [InfClose] using isInfinitesimal_zero

@[symm]
theorem InfClose.symm {b c : ℝ*} (h : b ≈ₕ c) : c ≈ₕ b := by
  have : c - b = -(b - c) := by ring
  unfold InfClose
  rw [this]
  exact h.neg

@[trans]
theorem InfClose.trans {a b c : ℝ*} (h₁ : a ≈ₕ b) (h₂ : b ≈ₕ c) : a ≈ₕ c := by
  have : a - c = (a - b) + (b - c) := by ring
  unfold InfClose
  rw [this]
  exact h₁.add h₂

/-- Goldblatt Exercise 5.5(1a) (p. 52): `≈ₕ` is an equivalence relation on `ℝ*`. -/
theorem infClose_equivalence : Equivalence InfClose :=
  ⟨InfClose.refl, InfClose.symm, InfClose.trans⟩

@[refl]
theorem LimDist.refl (b : ℝ*) : b ∼ₗ b := by
  simpa [LimDist] using isLimited_coe 0

@[symm]
theorem LimDist.symm {b c : ℝ*} (h : b ∼ₗ c) : c ∼ₗ b := by
  have : c - b = -(b - c) := by ring
  unfold LimDist
  rw [this]
  exact h.neg

@[trans]
theorem LimDist.trans {a b c : ℝ*} (h₁ : a ∼ₗ b) (h₂ : b ∼ₗ c) : a ∼ₗ c := by
  have : a - c = (a - b) + (b - c) := by ring
  unfold LimDist
  rw [this]
  exact h₁.add h₂

/-- Goldblatt Exercise 5.5(1b) (p. 52): `∼ₗ` is an equivalence relation on `ℝ*`. -/
theorem limDist_equivalence : Equivalence LimDist :=
  ⟨LimDist.refl, LimDist.symm, LimDist.trans⟩

theorem infClose_zero_iff {b : ℝ*} : b ≈ₕ 0 ↔ IsInfinitesimal b := by
  simp [InfClose]

theorem limDist_zero_iff {b : ℝ*} : b ∼ₗ 0 ↔ IsLimited b := by
  simp [LimDist]

theorem halo_zero : halo 0 = {c : ℝ* | IsInfinitesimal c} := by
  ext c
  change (0 : ℝ*) ≈ₕ c ↔ IsInfinitesimal c
  exact ⟨fun h ↦ by simpa [InfClose] using h.symm, fun h ↦ (infClose_zero_iff.2 h).symm⟩

theorem galaxy_zero : galaxy 0 = {c : ℝ* | IsLimited c} := by
  ext c
  change (0 : ℝ*) ∼ₗ c ↔ IsLimited c
  exact ⟨fun h ↦ by simpa [LimDist] using h.symm, fun h ↦ (limDist_zero_iff.2 h).symm⟩

/-- Goldblatt Exercise 5.5(3) (p. 52): `hal(b) = {b + ε | ε ∈ hal(0)}`. -/
theorem halo_eq_add_halo_zero (b : ℝ*) :
    halo b = {x : ℝ* | ∃ ε ∈ halo 0, x = b + ε} := by
  ext x
  rw [halo_zero]
  constructor
  · intro hx
    refine ⟨x - b, ?_, by ring⟩
    exact hx.symm
  · rintro ⟨ε, hε, rfl⟩
    change IsInfinitesimal (b - (b + ε))
    simpa using hε.neg

/-- Goldblatt Exercise 5.5(4) (p. 53): `gal(b) = {b + c | c ∈ gal(0)}`. -/
theorem galaxy_eq_add_galaxy_zero (b : ℝ*) :
    galaxy b = {x : ℝ* | ∃ c ∈ galaxy 0, x = b + c} := by
  ext x
  rw [galaxy_zero]
  constructor
  · intro hx
    refine ⟨x - b, hx.symm, by ring⟩
  · rintro ⟨c, hc, rfl⟩
    change IsLimited (b - (b + c))
    simpa using hc.neg

/-- Goldblatt Exercise 5.5(2) & Real Comparisons (pp. 52–53):
If `(b : ℝ*) ≈ₕ x`, `x ≤ y`, and `y ≈ₕ (c : ℝ*)` with `b, c : ℝ`, then `b ≤ c`. -/
theorem coe_le_of_infClose_le {b c : ℝ} {x y : ℝ*}
    (hbx : (b : ℝ*) ≈ₕ x) (hxy : x ≤ y) (hyc : y ≈ₕ (c : ℝ*)) : b ≤ c := by
  by_contra hlt
  push Not at hlt
  set δ : ℝ := (b - c) / 3
  have hδ : 0 < δ := by positivity
  have h1 : |(b : ℝ*) - x| < (δ : ℝ*) := hbx δ hδ
  have h2 : |y - (c : ℝ*)| < (δ : ℝ*) := hyc δ hδ
  have hbx' : (b : ℝ*) - (δ : ℝ*) < x := by linarith [(abs_lt.1 h1).2]
  have hyc' : y < (c : ℝ*) + (δ : ℝ*) := by linarith [(abs_lt.1 h2).2]
  have hbc : (b : ℝ*) - (δ : ℝ*) < (c : ℝ*) + (δ : ℝ*) := (hbx'.trans_le hxy).trans hyc'
  have hreal : b - δ < c + δ := by
    have : ((b - δ : ℝ) : ℝ*) < ((c + δ : ℝ) : ℝ*) := by simpa using hbc
    exact Hyperreal.coe_lt_coe.1 this
  linarith [show δ = (b - c) / 3 from rfl]

theorem coe_eq_of_infClose {b c : ℝ} (h : (b : ℝ*) ≈ₕ (c : ℝ*)) : b = c :=
  le_antisymm (coe_le_of_infClose_le h le_rfl (InfClose.refl _))
              (coe_le_of_infClose_le h.symm le_rfl (InfClose.refl _))

theorem InfClose.add {a a' b b' : ℝ*} (ha : a ≈ₕ a') (hb : b ≈ₕ b') : (a + b) ≈ₕ (a' + b') := by
  have : (a + b) - (a' + b') = (a - a') + (b - b') := by ring
  unfold InfClose
  rw [this]
  exact IsInfinitesimal.add ha hb

theorem InfClose.sub {a a' b b' : ℝ*} (ha : a ≈ₕ a') (hb : b ≈ₕ b') : (a - b) ≈ₕ (a' - b') := by
  have : (a - b) - (a' - b') = (a - a') - (b - b') := by ring
  unfold InfClose
  rw [this]
  exact IsInfinitesimal.sub ha hb

theorem InfClose.neg {a a' : ℝ*} (ha : a ≈ₕ a') : (-a) ≈ₕ (-a') := by
  have : -a - (-a') = -(a - a') := by ring
  unfold InfClose
  rw [this]
  exact IsInfinitesimal.neg ha

/-- Goldblatt Exercise 5.5(5a) (p. 53): Multiplication by a limited `b` preserves `≈ₕ`. -/
theorem InfClose.mul_left_of_isLimited {b x y : ℝ*} (hb : IsLimited b) (hxy : x ≈ₕ y) :
    (b * x) ≈ₕ (b * y) := by
  unfold InfClose
  rw [← mul_sub]
  exact hb.mul_isInfinitesimal hxy

/-- Goldblatt Exercise 5.5(5b) (p. 53): Multiplication by an unlimited `b` need NOT preserve `≈ₕ`
(`0 ≈ₕ ε`, yet `ω * 0 = 0` is NOT infinitely close to `ω * ε = 1`). -/
theorem exists_unlimited_not_infClose_mul :
    ∃ b x y : ℝ*, IsUnlimited b ∧ x ≈ₕ y ∧ ¬ ((b * x) ≈ₕ (b * y)) := by
  refine ⟨Hyperreal.omega, 0, Hyperreal.epsilon, isUnlimited_omega,
    (infClose_zero_iff.2 isInfinitesimal_epsilon).symm, ?_⟩
  rw [mul_zero, mul_comm Hyperreal.omega, Hyperreal.epsilon_mul_omega]
  intro h
  have := coe_eq_of_infClose (b := 0) (c := 1) (by simpa using h)
  norm_num at this

/-- Goldblatt Exercise 5.7(1a) (p. 54): Product of infinitely close limited numbers is infinitely close. -/
theorem InfClose.mul {b b' c c' : ℝ*} (hb : IsLimited b) (hc : IsLimited c)
    (hbb : b ≈ₕ b') (hcc : c ≈ₕ c') : (b * c) ≈ₕ (b' * c') := by
  have hb' : IsLimited b' := by
    have : b' = b - (b - b') := by ring
    rw [this]
    exact hb.sub hbb.isLimited
  have : b * c - b' * c' = (b - b') * c + b' * (c - c') := by ring
  unfold InfClose
  rw [this]
  exact (hbb.mul_isLimited hc).add (hb'.mul_isInfinitesimal hcc)

/-- Goldblatt Exercise 5.7(1b) (p. 54): Quotient of infinitely close limited numbers with
appreciable denominator is infinitely close. -/
theorem InfClose.div {b b' c c' : ℝ*} (hb : IsLimited b) (hc : IsAppreciable c)
    (hbb : b ≈ₕ b') (hcc : c ≈ₕ c') : (b / c) ≈ₕ (b' / c') := by
  have hc' : IsAppreciable c' := by
    have : c' = c + (c' - c) := by ring
    rw [this]
    exact hc.add_isInfinitesimal hcc.symm
  have hc0 : c ≠ 0 := hc.ne_zero
  have hc'0 : c' ≠ 0 := hc'.ne_zero
  have hdiff : b / c - b' / c' = ((b - b') * c + b * (c' - c)) * (c⁻¹ * c'⁻¹) := by
    field_simp [hc0, hc'0]
    ring
  unfold InfClose
  rw [hdiff]
  have hnum : IsInfinitesimal ((b - b') * c + b * (c' - c)) :=
    (hbb.mul_isLimited hc.1).add (hb.mul_isInfinitesimal hcc.symm)
  exact hnum.mul_isLimited (hc.inv.1.mul hc'.inv.1)

/-- Hyperreal floor map `⌊x⌋ ∈ ℤ*` lifted from `Int.floor : ℝ → ℤ`. -/
def hyperFloor (x : ℝ*) : ℤ* := Germ.map Int.floor x

theorem hyperFloor_le (x : ℝ*) : Hyperint.toHyperreal (hyperFloor x) ≤ x :=
  Germ.inductionOn x fun r ↦ ofSeq_le_ofSeq.2 <| Eventually.of_forall fun n ↦ Int.floor_le (r n)

theorem lt_hyperFloor_add_one (x : ℝ*) : x < Hyperint.toHyperreal (hyperFloor x) + 1 :=
  Germ.inductionOn x fun r ↦ ofSeq_lt_ofSeq.2 <| Eventually.of_forall fun n ↦ Int.lt_floor_add_one (r n)

/-- Goldblatt Exercise 5.5(6) (p. 53): Every galaxy `gal(b)` contains elements of `*ℤ`,
elements of `*ℚ \ *ℤ`, and elements of `ℝ* \ *ℚ`! -/
theorem galaxy_contains_int_rat_irrat (b : ℝ*) :
    (∃ z ∈ starSet (Set.range (Int.cast : ℤ → ℝ)), z ∈ galaxy b) ∧
    (∃ q ∈ starSet (Set.range (Rat.cast : ℚ → ℝ)) \ starSet (Set.range (Int.cast : ℤ → ℝ)),
      q ∈ galaxy b) ∧
    (∃ α ∉ starSet (Set.range (Rat.cast : ℚ → ℝ)), α ∈ galaxy b) := by
  rcases ofSeq_surjective b with ⟨r, rfl⟩
  let z : ℝ* := Hyperint.toHyperreal (hyperFloor (ofSeq r))
  have hle : z ≤ ofSeq r := hyperFloor_le (ofSeq r)
  have hlt : ofSeq r < z + 1 := lt_hyperFloor_add_one (ofSeq r)
  have hz_mem : z ∈ starSet (Set.range (Int.cast : ℤ → ℝ)) := by
    rw [← range_hyperint_toHyperreal]
    exact ⟨hyperFloor (ofSeq r), rfl⟩
  have hz_gal : z ∈ galaxy (ofSeq r) := by
    refine ⟨1, ?_⟩
    push_cast
    rw [abs_lt]
    constructor <;> linarith
  refine ⟨⟨z, hz_mem, hz_gal⟩, ?_, ?_⟩
  · refine ⟨z + (1 / 2 : ℝ*), ⟨?_, ?_⟩, ?_⟩
    · rw [← range_hyperrat_toHyperreal]
      refine ⟨(((fun n ↦ (⌊r n⌋ : ℚ) + (1 / 2 : ℚ)) : ℕ → ℚ) : ℚ*), ?_⟩
      exact Germ.coe_eq.2 <| Eventually.of_forall fun n ↦ by
        change (((⌊r n⌋ : ℚ) + (1 / 2 : ℚ) : ℚ) : ℝ) = (⌊r n⌋ : ℝ) + 1 / 2
        push_cast
        ring
    · intro hint
      rw [← range_hyperint_toHyperreal] at hint
      rcases hint with ⟨k, hk⟩
      induction k using Germ.inductionOn with | _ l =>
      have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (l n : ℝ) = (⌊r n⌋ : ℝ) + 1 / 2 :=
        Germ.coe_eq.1 hk
      obtain ⟨n, hn⟩ := hev.exists
      have h2 : ((2 * l n : ℤ) : ℝ) = ((2 * ⌊r n⌋ + 1 : ℤ) : ℝ) := by push_cast; linarith
      have : 2 * l n = 2 * ⌊r n⌋ + 1 := Int.cast_injective h2
      omega
    · change IsLimited (ofSeq r - (z + (1 / 2 : ℝ*)))
      have : ofSeq r - (z + (1 / 2 : ℝ*)) = (ofSeq r - z) - (1 / 2 : ℝ*) := by ring
      rw [this]
      exact hz_gal.sub (isLimited_coe (1 / 2))
  · refine ⟨z + (Real.sqrt 2 : ℝ*), ?_, ?_⟩
    · intro hrat
      rw [← range_hyperrat_toHyperreal] at hrat
      rcases hrat with ⟨q, hq⟩
      induction q using Germ.inductionOn with | _ u =>
      have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (u n : ℝ) = (⌊r n⌋ : ℝ) + Real.sqrt 2 :=
        Germ.coe_eq.1 hq
      obtain ⟨n, hn⟩ := hev.exists
      have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
      exact hirr ⟨u n - ⌊r n⌋, by push_cast; linarith⟩
    · change IsLimited (ofSeq r - (z + (Real.sqrt 2 : ℝ*)))
      have : ofSeq r - (z + (Real.sqrt 2 : ℝ*)) = (ofSeq r - z) - (Real.sqrt 2 : ℝ*) := by ring
      rw [this]
      exact hz_gal.sub (isLimited_coe (Real.sqrt 2))

/-! ## §5.6–5.7 Shadows (`shadow`), Homomorphism Laws, and `𝕃 ⧸ 𝕀 ≃+* ℝ` -/

/-- Goldblatt Theorem 5.6.1 (p. 53): The shadow (standard part) `sh(b) ∈ ℝ` of a hyperreal `b`,
constructed directly as `sSup {r : ℝ | (r : ℝ*) < b}` for limited `b` (and `0` otherwise). -/
def shadow (b : ℝ*) : ℝ :=
  if IsLimited b then sSup {r : ℝ | (r : ℝ*) < b} else 0

/-- Goldblatt Theorem 5.6.1 (p. 53): Every limited hyperreal `b` is infinitely close to `shadow b`. -/
theorem infClose_shadow {b : ℝ*} (hb : IsLimited b) : b ≈ₕ (shadow b : ℝ*) := by
  have hsh : shadow b = sSup {r : ℝ | (r : ℝ*) < b} := by simp [shadow, hb]
  obtain ⟨r₀, s₀, hr₀, hs₀⟩ := isLimited_iff_exists_real.1 hb
  have hne : ({r : ℝ | (r : ℝ*) < b}).Nonempty := ⟨r₀, hr₀⟩
  have hbdd : BddAbove {r : ℝ | (r : ℝ*) < b} := by
    refine ⟨s₀, fun r hr ↦ ?_⟩
    exact (Hyperreal.coe_lt_coe.1 (hr.trans hs₀)).le
  intro ε hε
  rw [hsh]
  set c := sSup {r : ℝ | (r : ℝ*) < b}
  have hupper : b ≤ ((c + ε / 2 : ℝ) : ℝ*) := by
    by_contra hgt
    push Not at hgt
    have hmem : c + ε / 2 ∈ {r : ℝ | (r : ℝ*) < b} := hgt
    have hle : c + ε / 2 ≤ c := le_csSup hbdd hmem
    linarith
  have hlower : ((c - ε / 2 : ℝ) : ℝ*) < b := by
    by_contra hle
    push Not at hle
    have hub : ∀ r ∈ {r : ℝ | (r : ℝ*) < b}, r ≤ c - ε / 2 := by
      intro r hr
      exact (Hyperreal.coe_lt_coe.1 (hr.trans_le hle)).le
    have hcle : c ≤ c - ε / 2 := csSup_le hne hub
    linarith
  rw [abs_lt]
  constructor
  · have : - (ε : ℝ*) < - ((ε / 2 : ℝ) : ℝ*) := by
      exact_mod_cast neg_lt_neg (half_lt_self hε)
    have hsub : - ((ε / 2 : ℝ) : ℝ*) < b - (c : ℝ*) := by
      have hlower' : (c : ℝ*) - ((ε / 2 : ℝ) : ℝ*) < b := by simpa using hlower
      linarith
    exact this.trans hsub
  · have hsub : b - (c : ℝ*) ≤ ((ε / 2 : ℝ) : ℝ*) := by
      have hupper' : b ≤ (c : ℝ*) + ((ε / 2 : ℝ) : ℝ*) := by simpa using hupper
      linarith
    have : ((ε / 2 : ℝ) : ℝ*) < (ε : ℝ*) := by exact_mod_cast half_lt_self hε
    exact hsub.trans_lt this

/-- Goldblatt Theorem 5.6.1 (Uniqueness, p. 53): If `b ≈ₕ c` with `c ∈ ℝ`, then `b` is limited and
`shadow b = c`. -/
theorem shadow_eq_of_infClose {b : ℝ*} {c : ℝ} (hbc : b ≈ₕ (c : ℝ*)) : shadow b = c := by
  have hb : IsLimited b := by
    have : b = (c : ℝ*) + (b - (c : ℝ*)) := by ring
    rw [this]
    exact (isLimited_coe c).add hbc.isLimited
  exact coe_eq_of_infClose ((infClose_shadow hb).symm.trans hbc)

theorem existsUnique_real_infClose {b : ℝ*} (hb : IsLimited b) :
    ∃! c : ℝ, b ≈ₕ (c : ℝ*) :=
  ⟨shadow b, infClose_shadow hb, fun _ hc ↦ (shadow_eq_of_infClose hc).symm⟩

@[simp]
theorem shadow_coe (r : ℝ) : shadow (r : ℝ*) = r :=
  shadow_eq_of_infClose (InfClose.refl _)

@[simp]
theorem shadow_zero : shadow 0 = 0 := by
  simpa using shadow_coe 0

@[simp]
theorem shadow_one : shadow 1 = 1 := by
  simpa using shadow_coe 1

theorem shadow_eq_zero_iff_isInfinitesimal {b : ℝ*} (hb : IsLimited b) :
    shadow b = 0 ↔ IsInfinitesimal b := by
  constructor
  · intro h0
    have := infClose_shadow hb
    rw [h0] at this
    simpa [InfClose] using this
  · intro hinf
    exact shadow_eq_of_infClose (by simpa [InfClose] using hinf)

/-- Goldblatt Theorem 5.6.2(1a) (p. 53): `sh(b + c) = sh(b) + sh(c)` for limited `b, c`. -/
theorem shadow_add {b c : ℝ*} (hb : IsLimited b) (hc : IsLimited c) :
    shadow (b + c) = shadow b + shadow c := by
  apply shadow_eq_of_infClose
  rw [Hyperreal.coe_add]
  exact (infClose_shadow hb).add (infClose_shadow hc)

theorem shadow_neg (b : ℝ*) : shadow (-b) = -shadow b := by
  by_cases hb : IsLimited b
  · apply shadow_eq_of_infClose
    rw [Hyperreal.coe_neg]
    exact (infClose_shadow hb).neg
  · have hnb : ¬ IsLimited (-b) := fun h ↦ hb (by simpa using h.neg)
    simp [shadow, hb, hnb]

/-- Goldblatt Theorem 5.6.2(1b) (p. 53): `sh(b - c) = sh(b) - sh(c)` for limited `b, c`. -/
theorem shadow_sub {b c : ℝ*} (hb : IsLimited b) (hc : IsLimited c) :
    shadow (b - c) = shadow b - shadow c := by
  rw [sub_eq_add_neg, shadow_add hb hc.neg, shadow_neg, sub_eq_add_neg]

/-- Goldblatt Theorem 5.6.2(2) (p. 53): `sh(b * c) = sh(b) * sh(c)` for limited `b, c`. -/
theorem shadow_mul {b c : ℝ*} (hb : IsLimited b) (hc : IsLimited c) :
    shadow (b * c) = shadow b * shadow c := by
  apply shadow_eq_of_infClose
  rw [Hyperreal.coe_mul]
  exact InfClose.mul hb hc (infClose_shadow hb) (infClose_shadow hc)

/-- Goldblatt Theorem 5.6.2(3) (p. 53): `sh(b / c) = sh(b) / sh(c)` when `b` is limited and `c` is
appreciable (`sh(c) ≠ 0`). -/
theorem shadow_div {b c : ℝ*} (hb : IsLimited b) (hc : IsAppreciable c) :
    shadow (b / c) = shadow b / shadow c := by
  have hshc : shadow c ≠ 0 := fun h0 ↦ hc.2 ((shadow_eq_zero_iff_isInfinitesimal hc.1).1 h0)
  have hshc_app : IsAppreciable (shadow c : ℝ*) := isAppreciable_coe_iff.2 hshc
  apply shadow_eq_of_infClose
  rw [Hyperreal.coe_div]
  exact InfClose.div hb hc (infClose_shadow hb) (infClose_shadow hc.1)

/-- Goldblatt Theorem 5.6.2(4) (p. 53): `sh(b^n) = sh(b)^n` for limited `b` and `n ∈ ℕ`. -/
theorem shadow_pow {b : ℝ*} (hb : IsLimited b) (n : ℕ) :
    shadow (b ^ n) = (shadow b) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hbk : IsLimited (b ^ k) := by
        clear ih
        induction k with
        | zero => simpa using isLimited_coe 1
        | succ m ihm => rw [pow_succ]; exact ihm.mul hb
      rw [pow_succ, shadow_mul hbk hb, ih, pow_succ]

/-- Goldblatt Theorem 5.6.2(5) (p. 53): `sh(|b|) = |sh(b)|`. -/
theorem shadow_abs (b : ℝ*) : shadow |b| = |shadow b| := by
  by_cases hb : IsLimited b
  · apply shadow_eq_of_infClose
    rw [Hyperreal.coe_abs]
    intro r hr
    have h := infClose_shadow hb r hr
    exact (abs_abs_sub_abs_le b (shadow b : ℝ*)).trans_lt h
  · have habs : ¬ IsLimited |b| := fun h ↦ hb ⟨h.choose, by simpa using h.choose_spec⟩
    simp [shadow, hb, habs]

/-- Goldblatt Theorem 5.6.2(6) (p. 53): `sh(√b) = √(sh(b))` for limited `b ≥ 0`. -/
theorem shadow_sqrt {b : ℝ*} (hb : IsLimited b) (hnn : 0 ≤ b) :
    shadow (starFun Real.sqrt b) = Real.sqrt (shadow b) := by
  have hsh_nn : 0 ≤ shadow b :=
    coe_le_of_infClose_le (InfClose.refl (0 : ℝ*)) hnn (infClose_shadow hb)
  rcases eq_or_lt_of_le hsh_nn with hzero | hpos
  · have hinf : IsInfinitesimal b := (shadow_eq_zero_iff_isInfinitesimal hb).1 hzero.symm
    have hsq_inf : IsInfinitesimal (starFun Real.sqrt b) := isInfinitesimal_starFun_sqrt hnn hinf
    rw [← hzero, Real.sqrt_zero]
    exact (shadow_eq_zero_iff_isInfinitesimal hsq_inf.isLimited).2 hsq_inf
  · apply shadow_eq_of_infClose
    have hdiff : starFun Real.sqrt b - (Real.sqrt (shadow b) : ℝ*) =
        (b - (shadow b : ℝ*)) / (starFun Real.sqrt b + (Real.sqrt (shadow b) : ℝ*)) := by
      rcases ofSeq_surjective b with ⟨r, rfl⟩
      have hr0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 ≤ r n := ofSeq_le_ofSeq.1 hnn
      have hden_ne : starFun Real.sqrt (ofSeq r) + (Real.sqrt (shadow (ofSeq r)) : ℝ*) ≠ 0 := by
        have h1 : 0 ≤ starFun Real.sqrt (ofSeq r) :=
          ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ Real.sqrt_nonneg (r n))
        have h2 : (0 : ℝ*) < (Real.sqrt (shadow (ofSeq r)) : ℝ*) :=
          Hyperreal.coe_pos.2 (Real.sqrt_pos.2 hpos)
        linarith
      rw [eq_div_iff hden_ne]
      refine Germ.coe_eq.2 (hr0.mono fun n hn ↦ ?_)
      change (Real.sqrt (r n) - Real.sqrt (shadow (ofSeq r))) *
        (Real.sqrt (r n) + Real.sqrt (shadow (ofSeq r))) = r n - shadow (ofSeq r)
      have hmul : (Real.sqrt (r n) - Real.sqrt (shadow (ofSeq r))) *
          (Real.sqrt (r n) + Real.sqrt (shadow (ofSeq r))) =
          (Real.sqrt (r n)) ^ 2 - (Real.sqrt (shadow (ofSeq r))) ^ 2 := by ring
      rw [hmul, Real.sq_sqrt hn, Real.sq_sqrt hpos.le]
    unfold InfClose
    rw [hdiff, div_eq_mul_inv]
    have hinv_lim : IsLimited (starFun Real.sqrt b + (Real.sqrt (shadow b) : ℝ*))⁻¹ := by
      have hsq_pos : 0 < Real.sqrt (shadow b) := Real.sqrt_pos.2 hpos
      have hsum_ge : (Real.sqrt (shadow b) : ℝ*) ≤ starFun Real.sqrt b + (Real.sqrt (shadow b) : ℝ*) := by
        have h1 : 0 ≤ starFun Real.sqrt b := by
          rcases ofSeq_surjective b with ⟨r, rfl⟩
          exact ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ Real.sqrt_nonneg (r n))
        linarith
      have hsum_pos : (0 : ℝ*) < (Real.sqrt (shadow b) : ℝ*) := Hyperreal.coe_pos.2 hsq_pos
      refine isLimited_iff_abs_le_real.2 ⟨(Real.sqrt (shadow b))⁻¹, by positivity, ?_⟩
      rw [abs_of_pos (inv_pos.2 (hsum_pos.trans_le hsum_ge)), Hyperreal.coe_inv]
      exact inv_anti₀ hsum_pos hsum_ge
    exact (infClose_shadow hb).mul_isLimited hinv_lim

/-- Goldblatt Theorem 5.6.2(7) (p. 54): `b ≤ c → sh(b) ≤ sh(c)` for limited `b, c`. -/
theorem shadow_le_of_le {b c : ℝ*} (hb : IsLimited b) (hc : IsLimited c) (hbc : b ≤ c) :
    shadow b ≤ shadow c :=
  coe_le_of_infClose_le (infClose_shadow hb).symm hbc (infClose_shadow hc)

/-- Ring homomorphism `sh : 𝕃 →+* ℝ` (Goldblatt §5.6, p. 54). -/
def shadowRingHom : LimitedSubring →+* ℝ where
  toFun x := shadow x.1
  map_one' := shadow_one
  map_mul' x y := shadow_mul x.2 y.2
  map_zero' := shadow_zero
  map_add' x y := shadow_add x.2 y.2

theorem shadowRingHom_surjective : Function.Surjective shadowRingHom :=
  fun r ↦ ⟨⟨(r : ℝ*), isLimited_coe r⟩, shadow_coe r⟩

theorem ker_shadowRingHom : RingHom.ker shadowRingHom = InfinitesimalIdeal := by
  ext x
  exact shadow_eq_zero_iff_isInfinitesimal x.2

/-- Goldblatt Theorem 5.6.3 (p. 54): `𝕃 ⧸ 𝕀 ≃+* ℝ` via the shadow map. -/
def quotientInfinitesimalEquivReal : (LimitedSubring ⧸ InfinitesimalIdeal) ≃+* ℝ :=
  (Ideal.quotEquivOfEq ker_shadowRingHom.symm).trans
    (RingHom.quotientKerEquivOfSurjective shadowRingHom_surjective)

/-- Goldblatt Theorem 5.6.3 (p. 54): `𝕀` is a maximal ideal of the ring `𝕃` of limited numbers. -/
theorem infinitesimalIdeal_isMaximal : InfinitesimalIdeal.IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ (quotientInfinitesimalEquivReal.toMulEquiv.isField (Field.toIsField ℝ))

/-! ## §5.7 Exercises on Infinite Closeness: Trigonometric Infinitesimals & `*ℚ` -/

/-- Goldblatt Exercise 5.7(2a) (p. 54): If `ε` is infinitesimal, `sin ε ≈ₕ 0`. -/
theorem starFun_sin_infClose_zero {ε : ℝ*} (hε : IsInfinitesimal ε) :
    starFun Real.sin ε ≈ₕ 0 := by
  rw [infClose_zero_iff]
  refine isInfinitesimal_of_abs_le hε ?_
  rcases ofSeq_surjective ε with ⟨r, rfl⟩
  exact ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ Real.abs_sin_le_abs)

/-- Goldblatt Exercise 5.7(2b) (p. 54): If `ε` is infinitesimal, `cos ε ≈ₕ 1`. -/
theorem starFun_cos_infClose_one {ε : ℝ*} (hε : IsInfinitesimal ε) :
    starFun Real.cos ε ≈ₕ 1 := by
  have hle : |starFun Real.cos ε - 1| ≤ |ε| := by
    rcases ofSeq_surjective ε with ⟨r, rfl⟩
    refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
    have h1 : |Real.cos (r n) - 1| = |2 * Real.sin (r n / 2) ^ 2| := by
      have hcos := Real.cos_two_mul' (r n / 2)
      rw [show 2 * (r n / 2) = r n by ring] at hcos
      have hsq := Real.cos_sq_add_sin_sq (r n / 2)
      have : Real.cos (r n) - 1 = -(2 * Real.sin (r n / 2) ^ 2) := by linarith
      rw [this, abs_neg]
    have hsin : |Real.sin (r n / 2)| ≤ |r n / 2| := Real.abs_sin_le_abs
    have hsin1 : |Real.sin (r n / 2)| ≤ 1 := Real.abs_sin_le_one _
    calc |Real.cos (r n) - 1|
        = 2 * |Real.sin (r n / 2)| * |Real.sin (r n / 2)| := by
          rw [h1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), sq, abs_mul]
          ring
      _ ≤ 2 * |r n / 2| * 1 := by gcongr
      _ = |r n| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
  exact isInfinitesimal_of_abs_le hε hle

/-- Goldblatt Exercise 5.7(2c) (p. 54): If `ε` is infinitesimal, `tan ε ≈ₕ 0`. -/
theorem starFun_tan_infClose_zero {ε : ℝ*} (hε : IsInfinitesimal ε) :
    starFun Real.tan ε ≈ₕ 0 := by
  have heq : starFun Real.tan ε = starFun Real.sin ε / starFun Real.cos ε := by
    rcases ofSeq_surjective ε with ⟨r, rfl⟩
    exact Germ.coe_eq.2 (Eventually.of_forall fun n ↦ Real.tan_eq_sin_div_cos (r n))
  have hcos_app : IsAppreciable (starFun Real.cos ε) := by
    have : starFun Real.cos ε = 1 + (starFun Real.cos ε - 1) := by ring
    rw [this]
    exact (isAppreciable_coe_iff.2 one_ne_zero).add_isInfinitesimal (starFun_cos_infClose_one hε)
  have h0 : (0 : ℝ*) = 0 / 1 := by simp
  rw [heq, h0]
  exact InfClose.div (infClose_zero_iff.1 (starFun_sin_infClose_zero hε)).isLimited hcos_app
    (starFun_sin_infClose_zero hε) (starFun_cos_infClose_one hε)

/-- Goldblatt Exercise 5.7(2d) (p. 54): If `ε ≠ 0` is infinitesimal, `sin ε / ε ≈ₕ 1`. -/
theorem starFun_sin_div_infClose_one {ε : ℝ*} (hε : IsInfinitesimal ε) (hne : ε ≠ 0) :
    starFun Real.sin ε / ε ≈ₕ 1 := by
  -- Use the classical inequality `|sin x / x - 1| ≤ |x|` for `0 < |x| < 1 / 2`.
  have hlt_half : |ε| < ((1 / 2 : ℝ) : ℝ*) := hε (1 / 2) (by norm_num)
  rcases ofSeq_surjective ε with ⟨r, rfl⟩
  have hr_ne : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ≠ 0 :=
    Ultrafilter.eventually_not.2 (fun h0 ↦ hne (Germ.coe_eq.2 h0))
  have hr_lt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |r n| < 1 / 2 := ofSeq_lt_ofSeq.1 hlt_half
  refine isInfinitesimal_of_abs_le hε ?_
  refine ofSeq_le_ofSeq.2 ((hr_ne.and hr_lt).mono fun n ⟨hn0, hn1⟩ ↦ ?_)
  change |Real.sin (r n) / r n - 1| ≤ |r n|
  have hpos : 0 < |r n| := abs_pos.2 hn0
  have hpi : |r n| < Real.pi / 2 := hn1.trans_le (by linarith [Real.two_le_pi])
  have hcos_le : Real.cos (|r n|) ≤ Real.sin (|r n|) / |r n| := by
    have htan := Real.lt_tan hpos hpi
    have hcos_pos : 0 < Real.cos |r n| := Real.cos_pos_of_mem_Ioo ⟨by linarith, hpi⟩
    rw [Real.tan_eq_sin_div_cos] at htan
    have hmul : |r n| * Real.cos |r n| ≤ Real.sin |r n| := (le_div_iff₀ hcos_pos).1 htan.le
    exact (le_div_iff₀ hpos).2 (by linarith)
  have hquot_eq : Real.sin (r n) / r n = Real.sin |r n| / |r n| := by
    rcases lt_or_gt_of_ne hn0 with hneg | hgt
    · rw [abs_of_neg hneg, Real.sin_neg]
      ring
    · rw [abs_of_pos hgt]
  have hupper : Real.sin |r n| / |r n| ≤ 1 :=
    (div_le_one hpos).2 (Real.sin_le hpos.le)
  have hcos_ge : 1 - |r n| ≤ Real.cos |r n| := by
    have hcos := Real.cos_two_mul' (|r n| / 2)
    rw [show 2 * (|r n| / 2) = |r n| by ring] at hcos
    have hsq0 := Real.cos_sq_add_sin_sq (|r n| / 2)
    have h1 : 1 - Real.cos |r n| = 2 * Real.sin (|r n| / 2) ^ 2 := by linarith
    have hs1 : |Real.sin (|r n| / 2)| ≤ |r n| / 2 := by
      simpa [abs_of_pos (half_pos hpos)] using Real.abs_sin_le_abs (x := |r n| / 2)
    have hs2 : |Real.sin (|r n| / 2)| ≤ 1 := by
      calc |Real.sin (|r n| / 2)| ≤ |r n| / 2 := hs1
      _ ≤ 1 := by linarith
    have hsq : 2 * Real.sin (|r n| / 2) ^ 2 ≤ |r n| := by
      calc 2 * Real.sin (|r n| / 2) ^ 2
          = 2 * |Real.sin (|r n| / 2)| * |Real.sin (|r n| / 2)| := by
            rw [← sq_abs]; ring
        _ ≤ 2 * (|r n| / 2) * 1 := by gcongr
        _ = |r n| := by ring
    linarith
  rw [hquot_eq, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Goldblatt Exercise 5.7(2e) (p. 54): If `ε ≠ 0` is infinitesimal, `(cos ε - 1) / ε ≈ₕ 0`. -/
theorem starFun_cos_sub_one_div_infClose_zero {ε : ℝ*} (hε : IsInfinitesimal ε) (hne : ε ≠ 0) :
    (starFun Real.cos ε - 1) / ε ≈ₕ 0 := by
  rw [infClose_zero_iff]
  rcases ofSeq_surjective ε with ⟨r, rfl⟩
  have hr_ne : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ≠ 0 :=
    Ultrafilter.eventually_not.2 (fun h0 ↦ hne (Germ.coe_eq.2 h0))
  refine isInfinitesimal_of_abs_le hε ?_
  refine ofSeq_le_ofSeq.2 (hr_ne.mono fun n hn0 ↦ ?_)
  change |(Real.cos (r n) - 1) / r n| ≤ |r n|
  have hcos := Real.cos_two_mul' (r n / 2)
  rw [show 2 * (r n / 2) = r n by ring] at hcos
  have hsq0 := Real.cos_sq_add_sin_sq (r n / 2)
  have h1 : Real.cos (r n) - 1 = -(2 * Real.sin (r n / 2) ^ 2) := by linarith
  have hpos : 0 < |r n| := abs_pos.2 hn0
  have hs : |Real.sin (r n / 2)| ≤ |r n| / 2 := by
    simpa [abs_div] using Real.abs_sin_le_abs (x := r n / 2)
  rw [h1, neg_div, abs_neg, abs_div, div_le_iff₀ hpos]
  calc |2 * Real.sin (r n / 2) ^ 2|
      = 2 * |Real.sin (r n / 2)| ^ 2 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_pow]
    _ ≤ 2 * (|r n| / 2) ^ 2 := by gcongr
    _ = |r n| ^ 2 / 2 := by ring
    _ ≤ |r n| * |r n| := by nlinarith

/-- Goldblatt Exercise 5.7(3) (p. 54): Every hyperreal `x ∈ ℝ*` is infinitely close to some
hyperrational `q ∈ *ℚ`. -/
theorem exists_hyperrat_infClose (x : ℝ*) :
    ∃ q : ℚ*, x ≈ₕ Hyperrat.toHyperreal q := by
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  choose q hq using fun n : ℕ ↦
    exists_rat_btwn (lt_add_of_pos_right (r n) (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹))
  refine ⟨(q : ℚ*), ?_⟩
  refine isInfinitesimal_of_abs_le isInfinitesimal_epsilon ?_
  rw [abs_of_pos Hyperreal.epsilon_pos]
  have hne0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), n ≠ 0 :=
    Filter.hyperfilter_le_cofinite (Set.finite_singleton 0).compl_mem_cofinite
  refine ofSeq_le_ofSeq.2 (hne0.mono fun n hn0 ↦ ?_)
  change |r n - (q n : ℝ)| ≤ (n : ℝ)⁻¹
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
  have hdiff : |r n - (q n : ℝ)| ≤ ((n : ℝ) + 1)⁻¹ := by
    have hpos_inv : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    rw [abs_le]
    exact ⟨by linarith [(hq n).2], by linarith [(hq n).1]⟩
  exact hdiff.trans (inv_anti₀ hn_pos (by linarith))

/-- Ring homomorphism embedding `ℚ* →+* ℝ*`. -/
def Hyperrat.toHyperrealRingHom : ℚ* →+* ℝ* where
  toFun := Hyperrat.toHyperreal
  map_one' := Germ.coe_eq.2 <| Eventually.of_forall fun _ ↦ Rat.cast_one
  map_mul' a b := Germ.inductionOn₂ a b fun u v ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun n ↦ Rat.cast_mul (u n) (v n)
  map_zero' := Germ.coe_eq.2 <| Eventually.of_forall fun _ ↦ Rat.cast_zero
  map_add' a b := Germ.inductionOn₂ a b fun u v ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun n ↦ Rat.cast_add (u n) (v n)

/-- Subring of limited hyperrationals `*ℚ ∩ 𝕃` (Goldblatt Exercise 5.7(4), p. 54). -/
def LimitedHyperratSubring : Subring ℚ* :=
  LimitedSubring.comap Hyperrat.toHyperrealRingHom

/-- Ideal of hyperrational infinitesimals `*ℚ ∩ 𝕀` in `LimitedHyperratSubring`. -/
def InfinitesimalHyperratIdeal : Ideal LimitedHyperratSubring where
  carrier := {q : LimitedHyperratSubring | IsInfinitesimal (Hyperrat.toHyperreal q.1)}
  add_mem' {a b} ha hb := by
    change IsInfinitesimal (Hyperrat.toHyperrealRingHom (a.1 + b.1))
    rw [map_add]
    exact ha.add hb
  zero_mem' := by
    change IsInfinitesimal (Hyperrat.toHyperrealRingHom 0)
    rw [map_zero]
    exact isInfinitesimal_zero
  smul_mem' c x hx := by
    change IsInfinitesimal (Hyperrat.toHyperrealRingHom (c.1 * x.1))
    rw [map_mul]
    exact c.2.mul_isInfinitesimal hx

/-- Shadow homomorphism restricted to limited hyperrationals. -/
def shadowHyperratRingHom : LimitedHyperratSubring →+* ℝ where
  toFun q := shadow (Hyperrat.toHyperreal q.1)
  map_one' := by
    change shadow (Hyperrat.toHyperrealRingHom 1) = 1
    rw [map_one]
    exact shadow_one
  map_mul' a b := by
    change shadow (Hyperrat.toHyperrealRingHom (a.1 * b.1)) = _
    rw [map_mul]
    exact shadow_mul a.2 b.2
  map_zero' := by
    change shadow (Hyperrat.toHyperrealRingHom 0) = 0
    rw [map_zero]
    exact shadow_zero
  map_add' a b := by
    change shadow (Hyperrat.toHyperrealRingHom (a.1 + b.1)) = _
    rw [map_add]
    exact shadow_add a.2 b.2

theorem shadowHyperratRingHom_surjective : Function.Surjective shadowHyperratRingHom := by
  intro r
  obtain ⟨q, hq⟩ := exists_hyperrat_infClose (r : ℝ*)
  have hqlim : IsLimited (Hyperrat.toHyperreal q) := by
    have : Hyperrat.toHyperreal q = (r : ℝ*) + (Hyperrat.toHyperreal q - (r : ℝ*)) := by ring
    rw [this]
    exact (isLimited_coe r).add hq.symm.isLimited
  exact ⟨⟨q, hqlim⟩, shadow_eq_of_infClose hq.symm⟩

theorem ker_shadowHyperratRingHom :
    RingHom.ker shadowHyperratRingHom = InfinitesimalHyperratIdeal := by
  ext q
  exact shadow_eq_zero_iff_isInfinitesimal q.2

/-- Goldblatt Exercise 5.7(4) (p. 54): `(*ℚ ∩ 𝕃) ⧸ (*ℚ ∩ 𝕀) ≃+* ℝ`! -/
def quotientHyperratInfinitesimalEquivReal :
    (LimitedHyperratSubring ⧸ InfinitesimalHyperratIdeal) ≃+* ℝ :=
  (Ideal.quotEquivOfEq ker_shadowHyperratRingHom.symm).trans
    (RingHom.quotientKerEquivOfSurjective shadowHyperratRingHom_surjective)

/-! ## §5.8–5.9 Shadows and Completeness (Cauchy & Dedekind) -/

/-- Standard `ε`-`N` Cauchy property of a sequence `s : ℕ → ℝ`. -/
def IsRealCauchy (s : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m n : ℕ, k ≤ m → k ≤ n → |s m - s n| < ε

/-- Goldblatt Theorem 5.8.1 (p. 55): Using ONLY the shadow hypothesis ("every limited hyperreal is
infinitely close to a real number") and hypersequence transfer, every real Cauchy sequence converges
in `ℝ`! -/
theorem cauchy_converges_via_shadow
    (hShadow : ∀ b : ℝ*, IsLimited b → ∃ L : ℝ, b ≈ₕ (L : ℝ*))
    {s : ℕ → ℝ} (hs : IsRealCauchy s) :
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ j : ℕ, ∀ m : ℕ, j ≤ m → |s m - L| ≤ ε := by
  obtain ⟨k, hk⟩ := hs 1 one_pos
  have hN_ge : ∀ j : ℕ, (j : ℕ*) ≤ omegaNat := fun j ↦
    Germ.coe_le.2 (Nat.hyperfilter_le_atTop (eventually_ge_atTop j))
  have hsN_bound : |(s k : ℝ*) - starSeq s omegaNat| < 1 := by
    have hk_ev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |s k - s n| < 1 := by
      have : ∀ᶠ n in atTop, |s k - s n| < 1 :=
        eventually_atTop.2 ⟨k, fun n hn ↦ hk k n le_rfl hn⟩
      exact this.filter_mono Nat.hyperfilter_le_atTop
    change ofSeq (fun n ↦ |s k - s n|) < ofSeq (fun _ ↦ 1)
    exact ofSeq_lt_ofSeq.2 hk_ev
  have hsN_lim : IsLimited (starSeq s omegaNat) := by
    have : starSeq s omegaNat = (s k : ℝ*) - ((s k : ℝ*) - starSeq s omegaNat) := by ring
    rw [this]
    exact (isLimited_coe (s k)).sub ⟨1, by simpa using hsN_bound⟩
  obtain ⟨L, hL⟩ := hShadow (starSeq s omegaNat) hsN_lim
  refine ⟨L, fun ε hε ↦ ?_⟩
  obtain ⟨j, hj⟩ := hs ε hε
  refine ⟨j, fun m hm ↦ ?_⟩
  have hmN : |(s m : ℝ*) - starSeq s omegaNat| < (ε : ℝ*) := by
    have hj_ev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |s m - s n| < ε := by
      have : ∀ᶠ n in atTop, |s m - s n| < ε :=
        eventually_atTop.2 ⟨j, fun n hn ↦ hj m n hm hn⟩
      exact this.filter_mono Nat.hyperfilter_le_atTop
    change ofSeq (fun n ↦ |s m - s n|) < ofSeq (fun _ ↦ ε)
    exact ofSeq_lt_ofSeq.2 hj_ev
  have htri : ((|s m - L| : ℝ) : ℝ*) ≤ |(s m : ℝ*) - starSeq s omegaNat| + |starSeq s omegaNat - (L : ℝ*)| := by
    rw [Hyperreal.coe_abs, Hyperreal.coe_sub]
    have : (s m : ℝ*) - (L : ℝ*) = ((s m : ℝ*) - starSeq s omegaNat) + (starSeq s omegaNat - (L : ℝ*)) := by ring
    rw [this]
    exact abs_add_le _ _
  have hlt_eps : |(s m : ℝ*) - starSeq s omegaNat| + |starSeq s omegaNat - (L : ℝ*)| <
      (ε : ℝ*) + |starSeq s omegaNat - (L : ℝ*)| := by
    gcongr
  have hclose : (ε : ℝ*) + |starSeq s omegaNat - (L : ℝ*)| ≈ₕ (ε : ℝ*) := by
    unfold InfClose
    simpa using hL.abs
  exact coe_le_of_infClose_le (InfClose.refl _) (htri.trans hlt_eps.le) hclose

/-- Goldblatt Exercise 5.9 (pp. 55–56): Direct nonstandard proof of Dedekind least-upper-bound
completeness of `ℝ` from the shadow property via `(s_N) / N`! -/
theorem dedekind_lub_via_shadow
    (hShadow : ∀ b : ℝ*, IsLimited b → ∃ L : ℝ, b ≈ₕ (L : ℝ*))
    {A : Set ℝ} (hAne : A.Nonempty) (hBdd : BddAbove A) :
    ∃ L : ℝ, IsLUB A L := by
  obtain ⟨a₀, ha₀⟩ := hAne
  obtain ⟨B, hB⟩ := hBdd
  -- Part (a): For each `n ≥ 1` (shifted to `n + 1`), there is a least `k : ℤ` such that
  -- `(k : ℝ) / (n + 1)` is an upper bound of `A`.
  have hexists_ub : ∀ n : ℕ, ∃ k : ℤ,
      (∀ a ∈ A, a ≤ (k : ℝ) / ((n : ℝ) + 1)) ∧
      ∀ k' : ℤ, k' < k → ∃ a ∈ A, (k' : ℝ) / ((n : ℝ) + 1) < a := by
    intro n
    set d : ℝ := (n : ℝ) + 1
    have hd : 0 < d := by positivity
    let P : ℤ → Prop := fun k ↦ ∀ a ∈ A, a ≤ (k : ℝ) / d
    have hP_top : P (⌈B * d⌉₊ : ℤ) := by
      intro a ha
      have haB : a ≤ B := hB ha
      have hceil : B * d ≤ ((⌈B * d⌉₊ : ℤ) : ℝ) := by
        exact_mod_cast Nat.le_ceil (B * d)
      exact (le_div_iff₀ hd).2 (by nlinarith)
    have hP_bdd : ∀ k : ℤ, P k → ⌊a₀ * d⌋ - 1 < k := by
      intro k hk
      have ha₀k : a₀ * d ≤ (k : ℝ) := (le_div_iff₀ hd).1 (hk a₀ ha₀)
      have hfl : (⌊a₀ * d⌋ : ℝ) ≤ a₀ * d := Int.floor_le (a₀ * d)
      have hlt : ((⌊a₀ * d⌋ - 1 : ℤ) : ℝ) < (k : ℝ) := by push_cast; linarith
      exact Int.cast_lt.1 hlt
    -- Shift to `ℕ` to pick the least witness by `Nat.find`
    let k₀ : ℤ := ⌊a₀ * d⌋
    have hex_nat : ∃ m : ℕ, P (k₀ + m) := by
      refine ⟨Int.toNat ((⌈B * d⌉₊ : ℤ) - k₀), ?_⟩
      have hle : k₀ ≤ (⌈B * d⌉₊ : ℤ) := by
        have := hP_bdd (⌈B * d⌉₊ : ℤ) hP_top
        omega
      have heq : k₀ + (Int.toNat ((⌈B * d⌉₊ : ℤ) - k₀) : ℤ) = (⌈B * d⌉₊ : ℤ) := by omega
      rwa [heq]
    let m₀ : ℕ := Nat.find hex_nat
    refine ⟨k₀ + m₀, Nat.find_spec hex_nat, fun k' hk' ↦ ?_⟩
    by_contra hno
    push Not at hno
    have hk'P : P k' := hno
    have hk'_ge : k₀ ≤ k' := by
      have := hP_bdd k' hk'P
      omega
    have hm_lt : Int.toNat (k' - k₀) < m₀ := by omega
    have hk'_eq : k₀ + (Int.toNat (k' - k₀) : ℤ) = k' := by omega
    exact Nat.find_min hex_nat hm_lt (by rwa [hk'_eq])
  choose kSeq hkSeq using hexists_ub
  -- Part (b): Consider `q = ofSeq (fun n ↦ kSeq n / (n + 1))`; show `q` is limited.
  let q : ℝ* := ofSeq (fun n ↦ (kSeq n : ℝ) / ((n : ℝ) + 1))
  have hq_ge : (a₀ : ℝ*) ≤ q :=
    ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (hkSeq n).1 a₀ ha₀)
  have hq_le : q ≤ ((B + 1 : ℝ) : ℝ*) := by
    refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
    have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    by_contra hgt
    push Not at hgt
    obtain ⟨a, haA, ha_gt⟩ := (hkSeq n).2 (kSeq n - 1) (by omega)
    have haB : a ≤ B := hB haA
    have h1 : (kSeq n : ℝ) / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1) < B := by
      have : ((kSeq n - 1 : ℤ) : ℝ) / ((n : ℝ) + 1) =
          (kSeq n : ℝ) / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1) := by push_cast; ring
      linarith
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) hd.le
    linarith
  have hq_lim : IsLimited q :=
    isLimited_iff_exists_real.2 ⟨a₀ - 1, B + 2,
      (Hyperreal.coe_lt_coe.2 (by linarith)).trans_le hq_ge,
      hq_le.trans_lt (Hyperreal.coe_lt_coe.2 (by linarith))⟩
  -- Part (c): Let `L ≈ₕ q`; prove `IsLUB A L`.
  obtain ⟨L, hL⟩ := hShadow q hq_lim
  refine ⟨L, ⟨fun a ha ↦ ?_, fun M hM ↦ ?_⟩⟩
  · have haq : (a : ℝ*) ≤ q :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (hkSeq n).1 a ha)
    exact coe_le_of_infClose_le (InfClose.refl _) haq hL
  · let qMinus : ℝ* := ofSeq (fun n ↦ ((kSeq n - 1 : ℤ) : ℝ) / ((n : ℝ) + 1))
    have hqMinus_le : qMinus ≤ (M : ℝ*) := by
      refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
      obtain ⟨a, haA, ha_gt⟩ := (hkSeq n).2 (kSeq n - 1) (by omega)
      exact ha_gt.le.trans (hM haA)
    have hdiff_inf : q ≈ₕ qMinus := by
      refine isInfinitesimal_of_abs_le isInfinitesimal_epsilon ?_
      rw [abs_of_pos Hyperreal.epsilon_pos]
      have hne0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), n ≠ 0 :=
        Filter.hyperfilter_le_cofinite (Set.finite_singleton 0).compl_mem_cofinite
      refine ofSeq_le_ofSeq.2 (hne0.mono fun n hn0 ↦ ?_)
      change |(kSeq n : ℝ) / ((n : ℝ) + 1) - ((kSeq n - 1 : ℤ) : ℝ) / ((n : ℝ) + 1)| ≤ (n : ℝ)⁻¹
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
      have hsimpl : (kSeq n : ℝ) / ((n : ℝ) + 1) - ((kSeq n - 1 : ℤ) : ℝ) / ((n : ℝ) + 1) =
          ((n : ℝ) + 1)⁻¹ := by
        push_cast
        field_simp
        ring
      rw [hsimpl, abs_of_pos (by positivity)]
      exact inv_anti₀ hn_pos (by linarith)
    exact coe_le_of_infClose_le (hL.symm.trans hdiff_inf) hqMinus_le (InfClose.refl _)

/-! ## §5.10–5.12 Hypernaturals, `*ℕ`-Galaxies, Hyperprimes, and Infinitely Many Primes -/

theorem isUnlimitedNat_omegaNat : IsUnlimitedNat omegaNat := fun n ↦ by
  rw [← Hypernat.toHyperreal_lt_iff, Hypernat.toHyperreal_natCast, Hypernat.toHyperreal_omegaNat]
  exact Hyperreal.coe_lt_omega n

theorem isUnlimitedNat_iff_isPosUnlimited {N : ℕ*} :
    IsUnlimitedNat N ↔ IsPosUnlimited (Hypernat.toHyperreal N) := by
  constructor
  · intro hN r
    obtain ⟨n, hn⟩ := exists_nat_gt r
    have hlt : (n : ℝ*) < Hypernat.toHyperreal N := by
      simpa using Hypernat.toHyperreal_lt_iff.2 (hN n)
    exact (Hyperreal.coe_lt_coe.2 hn).trans hlt
  · intro hN n
    exact Hypernat.toHyperreal_lt_iff.1 (by simpa using hN n)

/-- Goldblatt §5.10 (p. 56): Every limited hypernatural is standard (`N = n` for some `n ∈ ℕ`). -/
theorem not_isUnlimitedNat_iff_exists_nat {N : ℕ*} :
    ¬ IsUnlimitedNat N ↔ ∃ n : ℕ, N = (n : ℕ*) := by
  constructor
  · intro hnot
    unfold IsUnlimitedNat at hnot
    push Not at hnot
    obtain ⟨n, hn⟩ := hnot
    induction N using Germ.inductionOn with | _ a =>
    have hev : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), a k ≤ n := Germ.coe_le.1 hn
    have huniv : (⋃ m ∈ Finset.range (n + 1), {k : ℕ | a k = m}) ∈ hyperfilter ℕ := by
      refine mem_of_superset hev fun k hk ↦ ?_
      exact Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) rfl
    obtain ⟨m, _, hm_ev⟩ :=
      (Ultrafilter.finite_biUnion_mem_iff (Finset.finite_toSet (Finset.range (n + 1)))).1 huniv
    exact ⟨m, Germ.coe_eq.2 hm_ev⟩
  · rintro ⟨n, rfl⟩ hN
    exact lt_irrefl (n : ℕ*) (hN n)

/-- Goldblatt §5.10 (p. 56): The `*ℕ`-galaxy `γ(K)` of an unlimited hypernatural `K` consists
precisely of `{K + n | n ∈ ℕ} ∪ {K - n | n ∈ ℕ}` (a copy of `ℤ`). -/
def natGalaxy (K : ℕ*) : Set ℕ* :=
  {H : ℕ* | Hypernat.toHyperreal K ∼ₗ Hypernat.toHyperreal H}

theorem hypernat_nonneg (D : ℕ*) : (0 : ℝ*) ≤ Hypernat.toHyperreal D :=
  Germ.inductionOn D fun d ↦ ofSeq_le_ofSeq.2 (Eventually.of_forall fun i ↦ Nat.cast_nonneg (d i))

theorem mem_natGalaxy_iff {K H : ℕ*} :
    H ∈ natGalaxy K ↔ ∃ n : ℕ, H = K + (n : ℕ*) ∨ K = H + (n : ℕ*) := by
  constructor
  · intro hKH
    rcases le_total K H with hle | hle
    · induction K using Germ.inductionOn with | _ a =>
      induction H using Germ.inductionOn with | _ b =>
      have hab : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), a i ≤ b i := Germ.coe_le.1 hle
      let D : ℕ* := ((fun i ↦ b i - a i) : ℕ*)
      have hKDH : (a : ℕ*) + D = (b : ℕ*) :=
        Germ.coe_eq.2 (hab.mono fun i hi ↦ Nat.add_sub_of_le hi)
      have hD_lim : ¬ IsUnlimitedNat D := by
        intro hD_unl
        rcases hKH with ⟨m, hm⟩
        have hDm := hD_unl m
        have heq_sub : |Hypernat.toHyperreal (a : ℕ*) - Hypernat.toHyperreal (b : ℕ*)| =
            Hypernat.toHyperreal D := by
          have : Hypernat.toHyperreal (b : ℕ*) = Hypernat.toHyperreal (a : ℕ*) + Hypernat.toHyperreal D := by
            rw [← hKDH, Hypernat.toHyperreal_add]
          have hnn : 0 ≤ Hypernat.toHyperreal D := hypernat_nonneg D
          rw [this]
          have hsub : Hypernat.toHyperreal (a : ℕ*) - (Hypernat.toHyperreal (a : ℕ*) + Hypernat.toHyperreal D) =
              -Hypernat.toHyperreal D := by ring
          rw [hsub, abs_neg, abs_of_nonneg hnn]
        rw [heq_sub] at hm
        exact lt_asymm hm (by simpa using Hypernat.toHyperreal_lt_iff.2 hDm)
      obtain ⟨n, hn⟩ := not_isUnlimitedNat_iff_exists_nat.1 hD_lim
      exact ⟨n, Or.inl (by rw [← hKDH, hn])⟩
    · induction K using Germ.inductionOn with | _ a =>
      induction H using Germ.inductionOn with | _ b =>
      have hba : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), b i ≤ a i := Germ.coe_le.1 hle
      let D : ℕ* := ((fun i ↦ a i - b i) : ℕ*)
      have hHDK : (b : ℕ*) + D = (a : ℕ*) :=
        Germ.coe_eq.2 (hba.mono fun i hi ↦ Nat.add_sub_of_le hi)
      have hD_lim : ¬ IsUnlimitedNat D := by
        intro hD_unl
        rcases hKH with ⟨m, hm⟩
        have hDm := hD_unl m
        have heq_sub : |Hypernat.toHyperreal (a : ℕ*) - Hypernat.toHyperreal (b : ℕ*)| =
            Hypernat.toHyperreal D := by
          have : Hypernat.toHyperreal (a : ℕ*) = Hypernat.toHyperreal (b : ℕ*) + Hypernat.toHyperreal D := by
            rw [← hHDK, Hypernat.toHyperreal_add]
          have hnn : 0 ≤ Hypernat.toHyperreal D := hypernat_nonneg D
          rw [this]
          have hsub : (Hypernat.toHyperreal (b : ℕ*) + Hypernat.toHyperreal D) - Hypernat.toHyperreal (b : ℕ*) =
              Hypernat.toHyperreal D := by ring
          rw [hsub, abs_of_nonneg hnn]
        rw [heq_sub] at hm
        exact lt_asymm hm (by simpa using Hypernat.toHyperreal_lt_iff.2 hDm)
      obtain ⟨n, hn⟩ := not_isUnlimitedNat_iff_exists_nat.1 hD_lim
      exact ⟨n, Or.inr (by rw [← hHDK, hn])⟩
  · rintro ⟨n, rfl | hK⟩
    · change IsLimited (Hypernat.toHyperreal K - Hypernat.toHyperreal (K + (n : ℕ*)))
      rw [Hypernat.toHyperreal_add, Hypernat.toHyperreal_natCast]
      have : Hypernat.toHyperreal K - (Hypernat.toHyperreal K + (n : ℝ*)) = -(n : ℝ*) := by ring
      rw [this]
      exact (isLimited_coe n).neg
    · change IsLimited (Hypernat.toHyperreal K - Hypernat.toHyperreal H)
      rw [hK, Hypernat.toHyperreal_add, Hypernat.toHyperreal_natCast]
      have : (Hypernat.toHyperreal H + (n : ℝ*)) - Hypernat.toHyperreal H = (n : ℝ*) := by ring
      rw [this]
      exact isLimited_coe n

/-- Goldblatt §5.10 (p. 56): There is no greatest `*ℕ`-galaxy (`γ(K) < γ(2K)`). -/
theorem natGalaxy_no_greatest {K : ℕ*} (hK : IsUnlimitedNat K) :
    K < 2 * K ∧ 2 * K ∉ natGalaxy K := by
  have hpos : (0 : ℕ*) < K := hK 0
  induction K using Germ.inductionOn with | _ a =>
  refine ⟨?_, ?_⟩
  · have ha : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 0 < a i := Germ.coe_lt.1 hpos
    exact Germ.coe_lt.2 (ha.mono fun i hi ↦ by change a i < 2 * a i; omega)
  · intro hmem
    rcases mem_natGalaxy_iff.1 hmem with ⟨n, h1 | h2⟩
    · have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 2 * a i = a i + n := Germ.coe_eq.1 h1
      have hgt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), n < a i := Germ.coe_lt.1 (hK n)
      obtain ⟨i, hi1, hi2⟩ := (hev.and hgt).exists
      omega
    · have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), a i = 2 * a i + n := Germ.coe_eq.1 h2
      have hgt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 0 < a i := Germ.coe_lt.1 hpos
      obtain ⟨i, hi1, hi2⟩ := (hev.and hgt).exists
      omega

/-- Goldblatt §5.10 (pp. 56–57): There is no smallest unlimited `*ℕ`-galaxy (`⌊K/2⌋` is unlimited
and strictly below `γ(K)`). -/
theorem natGalaxy_no_smallest_unlimited {K : ℕ*} (hK : IsUnlimitedNat K) :
    ∃ M : ℕ*, IsUnlimitedNat M ∧ M < K ∧ M ∉ natGalaxy K := by
  induction K using Germ.inductionOn with | _ a =>
  let M : ℕ* := ((fun i ↦ a i / 2) : ℕ*)
  refine ⟨M, ?_, ?_, ?_⟩
  · intro n
    have hgt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 2 * n + 1 < a i := Germ.coe_lt.1 (hK (2 * n + 1))
    exact Germ.coe_lt.2 (hgt.mono fun i hi ↦ by change n < a i / 2; omega)
  · have hgt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 1 < a i := Germ.coe_lt.1 (hK 1)
    exact Germ.coe_lt.2 (hgt.mono fun i hi ↦ by change a i / 2 < a i; omega)
  · intro hmem
    rcases mem_natGalaxy_iff.1 hmem with ⟨n, h1 | h2⟩
    · have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), a i / 2 = a i + n := Germ.coe_eq.1 h1
      have hgt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 1 < a i := Germ.coe_lt.1 (hK 1)
      obtain ⟨i, hi1, hi2⟩ := (hev.and hgt).exists
      omega
    · have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), a i = a i / 2 + n := Germ.coe_eq.1 h2
      have hgt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 2 * n + 2 < a i := Germ.coe_lt.1 (hK (2 * n + 2))
      obtain ⟨i, hi1, hi2⟩ := (hev.and hgt).exists
      omega

/-- Goldblatt §5.10 (p. 57): Between any two distinct `*ℕ`-galaxies `γ(K) < γ(H)` lies a third
`γ(⌊(K + H)/2⌋)`! -/
theorem natGalaxy_dense {K H : ℕ*} (hKH : K < H) (hnot : H ∉ natGalaxy K) :
    ∃ M : ℕ*, K < M ∧ M < H ∧ M ∉ natGalaxy K ∧ M ∉ natGalaxy H := by
  induction K using Germ.inductionOn with | _ a =>
  induction H using Germ.inductionOn with | _ b =>
  let M : ℕ* := ((fun i ↦ (a i + b i) / 2) : ℕ*)
  have hdiff : ∀ n : ℕ, ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), a i + n < b i := by
    intro n
    have hle_or_gt := le_or_gt ((b : ℕ*)) ((a : ℕ*) + (n : ℕ*))
    rcases hle_or_gt with hle | hgt
    · exfalso
      have hmem : (b : ℕ*) ∈ natGalaxy (a : ℕ*) := by
        refine ⟨n + 1, ?_⟩
        have h1 : Hypernat.toHyperreal (a : ℕ*) ≤ Hypernat.toHyperreal (b : ℕ*) :=
          Hypernat.toHyperreal_le_iff.2 hKH.le
        have h2 : Hypernat.toHyperreal (b : ℕ*) ≤ Hypernat.toHyperreal (a : ℕ*) + (n : ℝ*) := by
          simpa using Hypernat.toHyperreal_le_iff.2 hle
        push_cast
        rw [abs_lt]
        constructor <;> linarith
      exact hnot hmem
    · exact Germ.coe_lt.1 hgt
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · exact Germ.coe_lt.2 ((hdiff 2).mono fun i hi ↦ by change a i < (a i + b i) / 2; omega)
  · exact Germ.coe_lt.2 ((hdiff 2).mono fun i hi ↦ by change (a i + b i) / 2 < b i; omega)
  · intro hMK
    rcases mem_natGalaxy_iff.1 hMK with ⟨n, h1 | h2⟩
    · have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (a i + b i) / 2 = a i + n := Germ.coe_eq.1 h1
      obtain ⟨i, hi1, hi2⟩ := (hev.and (hdiff (2 * n + 2))).exists
      omega
    · have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), a i = (a i + b i) / 2 + n := Germ.coe_eq.1 h2
      obtain ⟨i, hi1, hi2⟩ := (hev.and (hdiff 2)).exists
      omega
  · intro hMH
    rcases mem_natGalaxy_iff.1 hMH with ⟨n, h1 | h2⟩
    · have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (a i + b i) / 2 = b i + n := Germ.coe_eq.1 h1
      obtain ⟨i, hi1, hi2⟩ := (hev.and (hdiff 2)).exists
      omega
    · have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), b i = (a i + b i) / 2 + n := Germ.coe_eq.1 h2
      obtain ⟨i, hi1, hi2⟩ := (hev.and (hdiff (2 * n + 2))).exists
      omega

/-- Hypernatural factorial `M! ∈ ℕ*` lifted from `Nat.factorial`. -/
def hyperFactorial (M : ℕ*) : ℕ* := Germ.map Nat.factorial M

/-- Goldblatt Exercise 5.11(2a) (p. 57): For every `M ∈ ℕ*`, `hyperFactorial M` is divisible in `ℕ*`
by every `k ∈ ℕ*` with `1 ≤ k ≤ M`. -/
theorem dvd_hyperFactorial {k M : ℕ*} (hk1 : (1 : ℕ*) ≤ k) (hkM : k ≤ M) :
    k ∣ hyperFactorial M := by
  induction k using Germ.inductionOn with | _ a =>
  induction M using Germ.inductionOn with | _ b =>
  have ha1 : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 1 ≤ a i := Germ.coe_le.1 hk1
  have hab : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), a i ≤ b i := Germ.coe_le.1 hkM
  refine ⟨((fun i ↦ (b i).factorial / a i) : ℕ*), Germ.coe_eq.2 ?_⟩
  refine (ha1.and hab).mono fun i ⟨hi1, hib⟩ ↦ ?_
  have hdvd : a i ∣ (b i).factorial := Nat.dvd_factorial (by omega) hib
  exact (Nat.mul_div_cancel' hdvd).symm

/-- Goldblatt Exercise 5.11(2b) (p. 57): There exists a hypernatural `N = ω!` divisible by every
standard positive integer `n ≥ 1`. -/
theorem exists_hypernat_dvd_all_pos_nat :
    ∃ N : ℕ*, ∀ n : ℕ, 1 ≤ n → (n : ℕ*) ∣ N := by
  refine ⟨hyperFactorial omegaNat, fun n hn ↦ ?_⟩
  exact dvd_hyperFactorial (by exact_mod_cast hn) (isUnlimitedNat_omegaNat n).le

/-- Goldblatt Exercise 5.11(3) (p. 57): Enlarged prime predicate `*Π` on `ℕ*`, together with the
intrinsic primality predicate on `ℕ*`. -/
def IsStarPrime (p : ℕ*) : Prop := Germ.LiftPred Nat.Prime p

def IsHyperprime (p : ℕ*) : Prop :=
  (1 : ℕ*) < p ∧ ∀ d : ℕ*, d ∣ p → d = 1 ∨ d = p

/-- Goldblatt Exercise 5.11(3a) (p. 57): `*Π` consists precisely of those hypernaturals `> 1`
having no nontrivial factors in `ℕ*`. -/
theorem isStarPrime_iff_isHyperprime {p : ℕ*} :
    IsStarPrime p ↔ IsHyperprime p := by
  induction p using Germ.inductionOn with | _ a =>
  constructor
  · intro hp
    refine ⟨Germ.coe_lt.2 (hp.mono fun i hi ↦ hi.one_lt), fun d hd ↦ ?_⟩
    induction d using Germ.inductionOn with | _ b =>
    rcases hd with ⟨q, hq⟩
    induction q using Germ.inductionOn with | _ c =>
    have hmul : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), a i = b i * c i := Germ.coe_eq.1 hq
    have hor : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), b i = 1 ∨ b i = a i :=
      (hp.and hmul).mono fun i ⟨hip, him⟩ ↦ hip.eq_one_or_self_of_dvd (b i) ⟨c i, him⟩
    rcases Ultrafilter.eventually_or.1 hor with h1 | hself
    · exact Or.inl (Germ.coe_eq.2 h1)
    · exact Or.inr (Germ.coe_eq.2 hself)
  · rintro ⟨h1, hdiv⟩
    by_contra hnot
    have hnot_ev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), ¬ (a i).Prime :=
      Ultrafilter.eventually_not.2 hnot
    have hgt1 : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 1 < a i := Germ.coe_lt.1 h1
    let b : ℕ → ℕ := fun i ↦ (a i).minFac
    let c : ℕ → ℕ := fun i ↦ a i / (a i).minFac
    have hdvd : (b : ℕ*) ∣ (a : ℕ*) := by
      refine ⟨(c : ℕ*), Germ.coe_eq.2 (Eventually.of_forall fun i ↦ ?_)⟩
      exact (Nat.mul_div_cancel' (Nat.minFac_dvd (a i))).symm
    rcases hdiv (b : ℕ*) hdvd with hb1 | hba
    · have hb1_ev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), b i = 1 := Germ.coe_eq.1 hb1
      obtain ⟨i, ⟨hi_gt, hi_b1⟩⟩ := (hgt1.and hb1_ev).exists
      have hpos : 1 < (a i).minFac := (Nat.minFac_prime (by omega)).one_lt
      change (a i).minFac = 1 at hi_b1
      omega
    · have hba_ev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), b i = a i := Germ.coe_eq.1 hba
      obtain ⟨i, ⟨⟨hi_np, hi_gt⟩, hi_ba⟩⟩ := ((hnot_ev.and hgt1).and hba_ev).exists
      have hp_min : (a i).minFac.Prime := Nat.minFac_prime (by omega)
      rw [show (a i).minFac = a i from hi_ba] at hp_min
      exact hi_np hp_min

/-- Goldblatt Exercise 5.11(3b) (p. 57): Every hypernatural `M > 1` is divisible by some
hyperprime `q ∈ *Π`. -/
theorem exists_starPrime_dvd {M : ℕ*} (hM : (1 : ℕ*) < M) :
    ∃ q : ℕ*, IsStarPrime q ∧ q ∣ M := by
  induction M using Germ.inductionOn with | _ a =>
  have hgt1 : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 1 < a i := Germ.coe_lt.1 hM
  refine ⟨((fun i ↦ (a i).minFac) : ℕ*), ?_, ?_⟩
  · exact hgt1.mono fun i hi ↦ Nat.minFac_prime (by omega)
  · refine ⟨((fun i ↦ a i / (a i).minFac) : ℕ*), Germ.coe_eq.2 (Eventually.of_forall fun i ↦ ?_)⟩
    exact (Nat.mul_div_cancel' (Nat.minFac_dvd (a i))).symm

/-- Goldblatt §5.12 (pp. 57–58): **Nonstandard Proof of Euclid's Theorem on Infinitely Many Primes!**
Take `N = ω!` divisible by every standard `n ≥ 1`, and let `q ∈ *Π` divide `N + 1`. Then `q` cannot
be any standard prime `p ∈ Π` (since `p ∣ N` and `p ∣ N + 1` would force `p ∣ 1`), so `*Π` has a
nonstandard member, proving `Π = {p ∈ ℕ | Prime p}` is infinite! -/
theorem nonstandard_exists_unlimited_prime :
    ∃ q : ℕ*, IsStarPrime q ∧ IsUnlimitedNat q := by
  let N : ℕ* := hyperFactorial omegaNat
  have hN_gt1 : (1 : ℕ*) < N + 1 :=
    Germ.coe_lt.2 (Eventually.of_forall fun i ↦ Nat.succ_lt_succ (Nat.factorial_pos i))
  obtain ⟨q, hq_prime, hq_dvd_succ⟩ := exists_starPrime_dvd hN_gt1
  refine ⟨q, hq_prime, ?_⟩
  by_contra hlim
  obtain ⟨p, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 hlim
  have hp_prime : p.Prime := Germ.liftPred_const_iff.1 hq_prime
  have hp_dvd_N : (p : ℕ*) ∣ N :=
    dvd_hyperFactorial (by exact_mod_cast hp_prime.pos) (isUnlimitedNat_omegaNat p).le
  rcases hp_dvd_N with ⟨u, hu⟩
  rcases hq_dvd_succ with ⟨v, hv⟩
  induction u using Germ.inductionOn with | _ b =>
  induction v using Germ.inductionOn with | _ c =>
  have hu_ev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), i.factorial = p * b i := Germ.coe_eq.1 hu
  have hv_ev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), i.factorial + 1 = p * c i := Germ.coe_eq.1 hv
  obtain ⟨i, hi_u, hi_v⟩ := (hu_ev.and hv_ev).exists
  have hdvd1 : p ∣ 1 := ⟨c i - b i, by
    have hcb : b i < c i := by nlinarith [hp_prime.one_lt]
    rw [Nat.mul_sub_left_distrib]
    omega⟩
  exact hp_prime.not_dvd_one hdvd1

/-- Goldblatt §5.12 (p. 57): Nonstandard proof of Euclid's theorem (`{p : ℕ | p.Prime}.Infinite`)
deduced from `nonstandard_exists_unlimited_prime` and Exercise 3.10(1)! -/
theorem nonstandard_euclid_infinite_primes :
    ({p : ℝ | ∃ k : ℕ, k.Prime ∧ (k : ℝ) = p}).Infinite := by
  rw [infinite_iff_exists_nonstandard_mem_starSet]
  obtain ⟨q, hq_prime, hq_unl⟩ := nonstandard_exists_unlimited_prime
  refine ⟨Hypernat.toHyperreal q, ?_, ?_⟩
  · induction q using Germ.inductionOn with | _ a =>
    exact ofSeq_mem_starSet.2 (hq_prime.mono fun i hi ↦ ⟨a i, hi, rfl⟩)
  · rintro ⟨r, ⟨k, _, rfl⟩, hreq⟩
    have hqk : q = (k : ℕ*) := Hypernat.toHyperreal_injective (by simpa using hreq.symm)
    exact lt_irrefl (k : ℕ*) (hqk ▸ hq_unl k)

end Goldblatt
end
