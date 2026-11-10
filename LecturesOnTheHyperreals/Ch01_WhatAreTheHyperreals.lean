import Mathlib.Algebra.Order.CompleteField
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# Chapter 1: What Are the Hyperreals?

Formalization of Chapter 1 ("What Are the Hyperreals?", pp. 3–14) of Robert Goldblatt,
*Lectures on the Hyperreals: An Introduction to Nonstandard Analysis*, Graduate Texts in
Mathematics, Vol. 188, Springer-Verlag, 1998.

## Overview of Contents

* **§1.1 Infinitely Small and Large (pp. 3, 10)**
  * Definitions of infinitesimal (`IsInfinitesimalIn`), nonzero infinitesimal
    (`IsNonzeroInfinitesimalIn`), positive infinitesimal (`IsPositiveInfinitesimalIn`), and
    infinitely large element (`IsInfiniteIn`) in a general linearly ordered field `F`.
  * Algebraic closure properties of infinitesimals (zero, negation, addition, bounded products,
    products of infinitesimals).
  * Reciprocal duality (`isNonzeroInfinitesimalIn_iff_inv_isInfiniteIn`,
    `isInfiniteIn_iff_inv_isNonzeroInfinitesimalIn`): `ε` is a nonzero infinitesimal if and only
    if `ε⁻¹` is infinite (Goldblatt §1.1, p. 3).
  * Absence of nonzero infinitesimals and infinite numbers in Archimedean fields and in `ℝ`
    (`real_isInfinitesimalIn_iff_eq_zero`, `not_real_isNonzeroInfinitesimalIn`,
    `not_real_isInfiniteIn`), and exact equivalence between the Archimedean property and the
    nonexistence of infinite / nonzero infinitesimal elements.

* **§1.2 Historical Background (pp. 4–11)**
  * *Archimedes (pp. 4–5)*: Regular polygon / triangle decomposition identity `A = (1/2) * r * P`,
    the circle area-circumference relation `π r² = (1/2) * r * (2 π r)`, the double-approximation
    *reductio ad absurdum* principle of exhaustion, and the quadrature of the parabola `y = x²` on
    `[0, 1]` via exact finite Riemann sums `∑ k < n, (k / n)² * (1 / n) → 1 / 3` (Footnote 1,
    pp. 4–5).
  * *Leibniz & Newton (pp. 5–8)*: Exact algebraic product increment
    `(x + dx)(y + dy) - xy = x dy + y dx + dx dy`, proof that `(dx * dy) / dx` is infinitesimal
    for nonzero infinitesimal `dx` and infinitesimal `dy` ("`dx dy` is infinitely small in
    comparison with `dx`"), and Newton's method of moments for `x²`.
  * *Euler (pp. 8–9)*: Proof that for infinite `j` in any ordered field `F` and `k : ℕ`, the
    Euler ratio error `(j - k) / j - 1` is infinitesimal, inductive extension to the full binomial
    product `(∏ k ∈ range n, (j - k) / j) - 1`, higher-power ratio `(dx)^k / dx` (`k ≥ 2`) being
    infinitesimal, and the standard limit `(1 + z / n)^n → exp z` (in particular
    `(1 + 1 / n)^n → exp 1`).
  * *Weierstrass & Robinson (pp. 10–11)*: Purely arithmetical `ε`-`δ` definition of
    `lim_{x → a} f(x) = L` (`WeierstrassLimit`), its equivalence with Mathlib's
    punctured-neighborhood filter limit `Filter.Tendsto f (nhdsWithin a {a}ᶜ) (nhds L)`, and
    finite-subset satisfiability in `ℝ` (`robinson_finite_satisfiability_in_real`) motivating
    Robinson's compactness construction of `*ℝ`.

* **§1.3 What Is a Real Number? (pp. 11–14)**
  * *(1) Infinite Decimal Expansions (p. 12)*: Truncated base-10 rational approximations
    `decimalTrunc x n = ⌊x · 10ⁿ⌋ / 10ⁿ`, convergence to `x`, Cauchy property, and explicit
    verification of Goldblatt's `√2` sequence `1, 1.4, 1.41, 1.414, ...`.
  * *(2) Dedekind Completeness & Eudoxus–Archimedes (pp. 11–13)*: `IsDedekindComplete`, proof for
    `ℝ` (`real_isDedekindComplete`), categorical uniqueness of Dedekind-complete ordered fields up
    to unique ordered-ring isomorphism (`orderRingIsoRealOfIsDedekindComplete`,
    `existsUnique_orderRingIso_of_isDedekindComplete`), derivation of the Eudoxus–Archimedes
    property from Dedekind completeness (`archimedean_of_isDedekindComplete`,
    `eudoxus_archimedes_of_isDedekindComplete`), and Goldblatt's key observation (p. 11) that no
    ordered field containing a nonzero infinitesimal (or an infinite element) can be Dedekind
    complete (`not_isDedekindComplete_of_exists_nonzeroInfinitesimal`).
  * *(3) Dedekind Cuts of `ℚ` (p. 12)*: `DedekindCutQ`, canonical map `DedekindCutQ.ofReal`,
    supremum reconstruction `DedekindCutQ.toReal` (`x = sSup ((↑) '' L)`), full order isomorphism
    `DedekindCutQ ≃o ℝ`, irrational cut symmetry, and the explicit cut `sqrtTwoCut` for `√2`.
  * *(4) Cantor's Cauchy Sequences of `ℚ` (p. 12)*: `IsRatCauchySeq`, `RatCauchyEquiv`
    (`lim_{n → ∞} |rₙ - sₙ| = 0`), proof that `RatCauchyEquiv` is an equivalence relation,
    compatibility with `CauSeq ℚ abs` and `Real.mk`, and ring equivalence with
    `CauSeq.Completion.Cauchy (abs : ℚ → ℚ)`.
-/

set_option autoImplicit false

namespace Goldblatt.Ch01

open scoped BigOperators Topology

/-! ### §1.1 Infinitely Small and Large (Goldblatt pp. 3, 10) -/

section InfinitelySmallAndLarge

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- An element `ε` of a linearly ordered field `F` is *infinitesimal* (or *infinitely small*,
allowing `0`) if `|ε| < 1 / n` for every positive natural number `n = 1, 2, 3, ...`
(Goldblatt §1.1, p. 3). -/
def IsInfinitesimalIn (ε : F) : Prop :=
  ∀ n : ℕ, 0 < n → |ε| < (n : F)⁻¹

/-- A *nonzero infinitesimal* in a linearly ordered field `F` is a nonzero element `ε ≠ 0`
satisfying `|ε| < 1 / n` for all `n = 1, 2, 3, ...` (Goldblatt §1.1, p. 3). -/
def IsNonzeroInfinitesimalIn (ε : F) : Prop :=
  ε ≠ 0 ∧ IsInfinitesimalIn ε

/-- A *positive infinitesimal* in a linearly ordered field `F` satisfies `0 < ε` and `ε < 1 / n`
for all `n = 1, 2, 3, ...`, matching Robinson's compactness schema `0 < ε, ε < 1, ε < 1/2, ...`
(Goldblatt §1.2, p. 10). -/
def IsPositiveInfinitesimalIn (ε : F) : Prop :=
  0 < ε ∧ ∀ n : ℕ, 0 < n → ε < (n : F)⁻¹

/-- An element `ω` of a linearly ordered field `F` is *infinitely large* (or *infinite*) if
`|ω| > n` for every positive natural number `n = 1, 2, 3, ...` (Goldblatt §1.1, p. 3). -/
def IsInfiniteIn (ω : F) : Prop :=
  ∀ n : ℕ, 0 < n → (n : F) < |ω|

/-- Zero is trivially an infinitesimal in every linearly ordered field. -/
theorem zero_isInfinitesimalIn : IsInfinitesimalIn (0 : F) := by
  intro n hn
  rw [abs_zero]
  exact inv_pos.mpr (Nat.cast_pos.mpr hn)

/-- Characterizes positive infinitesimals in terms of `IsInfinitesimalIn`. -/
theorem isPositiveInfinitesimalIn_iff (ε : F) :
    IsPositiveInfinitesimalIn ε ↔ 0 < ε ∧ IsInfinitesimalIn ε := by
  constructor
  · rintro ⟨hpos, hlt⟩
    refine ⟨hpos, fun n hn => ?_⟩
    rw [abs_of_pos hpos]
    exact hlt n hn
  · rintro ⟨hpos, hinf⟩
    refine ⟨hpos, fun n hn => ?_⟩
    simpa [abs_of_pos hpos] using hinf n hn

/-- Every positive infinitesimal is a nonzero infinitesimal (Goldblatt §1.2, pp. 10–11). -/
theorem IsPositiveInfinitesimalIn.isNonzeroInfinitesimalIn {ε : F}
    (hε : IsPositiveInfinitesimalIn ε) : IsNonzeroInfinitesimalIn ε := by
  rw [isPositiveInfinitesimalIn_iff] at hε
  exact ⟨hε.1.ne', hε.2⟩

omit [IsStrictOrderedRing F] in
/-- Negation preserves the infinitesimal property. -/
@[simp]
theorem isInfinitesimalIn_neg_iff (ε : F) :
    IsInfinitesimalIn (-ε) ↔ IsInfinitesimalIn ε := by
  simp [IsInfinitesimalIn]

/-- Taking absolute values preserves the infinitesimal property. -/
@[simp]
theorem isInfinitesimalIn_abs_iff (ε : F) :
    IsInfinitesimalIn |ε| ↔ IsInfinitesimalIn ε := by
  simp [IsInfinitesimalIn]

omit [IsStrictOrderedRing F] in
/-- Negation preserves the infinite-element property. -/
@[simp]
theorem isInfiniteIn_neg_iff (ω : F) :
    IsInfiniteIn (-ω) ↔ IsInfiniteIn ω := by
  simp [IsInfiniteIn]

/-- Every infinite element in a linearly ordered field is nonzero. -/
theorem IsInfiniteIn.ne_zero {ω : F} (hω : IsInfiniteIn ω) : ω ≠ 0 := by
  intro h0
  have h1 : (1 : F) < |ω| := by simpa using hω 1 Nat.one_pos
  rw [h0, abs_zero] at h1
  exact not_lt_of_ge zero_le_one h1

/-- Zero is never an infinite element. -/
theorem not_zero_isInfiniteIn : ¬ IsInfiniteIn (0 : F) :=
  fun h => h.ne_zero rfl

omit [IsStrictOrderedRing F] in
/-- No element can be simultaneously infinitesimal and infinite. -/
theorem not_isInfinitesimalIn_and_isInfiniteIn (x : F) :
    ¬ (IsInfinitesimalIn x ∧ IsInfiniteIn x) := by
  rintro ⟨hsmall, hlarge⟩
  have h1 : |x| < 1 := by simpa using hsmall 1 Nat.one_pos
  have h2 : (1 : F) < |x| := by simpa using hlarge 1 Nat.one_pos
  exact lt_asymm h1 h2

/-- **Reciprocal Duality (Goldblatt §1.1, p. 3)**: An element `ε` of a linearly ordered field is a
nonzero infinitesimal if and only if its reciprocal `ε⁻¹` is infinitely large. -/
theorem isNonzeroInfinitesimalIn_iff_inv_isInfiniteIn (ε : F) :
    IsNonzeroInfinitesimalIn ε ↔ IsInfiniteIn ε⁻¹ := by
  constructor
  · rintro ⟨hne, hinf⟩ n hn
    have habs_pos : 0 < |ε| := abs_pos.mpr hne
    have hlt : |ε| < (n : F)⁻¹ := hinf n hn
    have hinv : ((n : F)⁻¹)⁻¹ < |ε|⁻¹ := inv_strictAnti₀ habs_pos hlt
    simpa [abs_inv] using hinv
  · intro hω
    have hinv_ne : ε⁻¹ ≠ 0 := hω.ne_zero
    have hne : ε ≠ 0 := fun h0 => hinv_ne (by simp [h0])
    refine ⟨hne, fun n hn => ?_⟩
    have hn_pos : (0 : F) < (n : F) := Nat.cast_pos.mpr hn
    have hlt : (n : F) < |ε|⁻¹ := by simpa [abs_inv] using hω n hn
    have hinv : (|ε|⁻¹)⁻¹ < (n : F)⁻¹ := inv_strictAnti₀ hn_pos hlt
    simpa using hinv

/-- **Reciprocal Duality (Goldblatt §1.1, p. 3)**: An element `ω` of a linearly ordered field is
infinitely large if and only if its reciprocal `ω⁻¹` is a nonzero infinitesimal. -/
theorem isInfiniteIn_iff_inv_isNonzeroInfinitesimalIn (ω : F) :
    IsInfiniteIn ω ↔ IsNonzeroInfinitesimalIn ω⁻¹ := by
  rw [isNonzeroInfinitesimalIn_iff_inv_isInfiniteIn, inv_inv]

/-- The sum of two infinitesimals in any linearly ordered field is infinitesimal. -/
theorem IsInfinitesimalIn.add {ε δ : F}
    (hε : IsInfinitesimalIn ε) (hδ : IsInfinitesimalIn δ) :
    IsInfinitesimalIn (ε + δ) := by
  intro n hn
  have h2n : 0 < 2 * n := Nat.mul_pos Nat.two_pos hn
  have hε' : |ε| < ((2 * n : ℕ) : F)⁻¹ := hε (2 * n) h2n
  have hδ' : |δ| < ((2 * n : ℕ) : F)⁻¹ := hδ (2 * n) h2n
  have hn_ne : (n : F) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have htwo_ne : (2 : F) ≠ 0 := two_ne_zero
  calc
    |ε + δ| ≤ |ε| + |δ| := abs_add_le ε δ
    _ < ((2 * n : ℕ) : F)⁻¹ + ((2 * n : ℕ) : F)⁻¹ := add_lt_add hε' hδ'
    _ = (n : F)⁻¹ := by
      push_cast
      field_simp
      ring

/-- The difference of two infinitesimals in any linearly ordered field is infinitesimal. -/
theorem IsInfinitesimalIn.sub {ε δ : F}
    (hε : IsInfinitesimalIn ε) (hδ : IsInfinitesimalIn δ) :
    IsInfinitesimalIn (ε - δ) := by
  rw [sub_eq_add_neg]
  exact hε.add ((isInfinitesimalIn_neg_iff δ).mpr hδ)

/-- Multiplying an infinitesimal by any element bounded in absolute value by a natural number
produces an infinitesimal. -/
theorem IsInfinitesimalIn.mul_of_abs_le_nat {ε x : F}
    (hε : IsInfinitesimalIn ε) {m : ℕ} (hx : |x| ≤ (m : F)) :
    IsInfinitesimalIn (ε * x) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hx0 : x = 0 := abs_nonpos_iff.mp (by simpa using hx)
    rw [hx0, mul_zero]
    exact zero_isInfinitesimalIn
  · intro n hn
    by_cases hε0 : ε = 0
    · rw [hε0, zero_mul, abs_zero]
      exact inv_pos.mpr (Nat.cast_pos.mpr hn)
    · have habs_pos : 0 < |ε| := abs_pos.mpr hε0
      have hmn : 0 < m * n := Nat.mul_pos hm hn
      have hm_pos : (0 : F) < (m : F) := Nat.cast_pos.mpr hm
      have hn_ne : (n : F) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
      have hm_ne : (m : F) ≠ 0 := hm_pos.ne'
      calc
        |ε * x| = |ε| * |x| := abs_mul ε x
        _ ≤ |ε| * (m : F) := mul_le_mul_of_nonneg_left hx habs_pos.le
        _ < (((m * n : ℕ) : F)⁻¹) * (m : F) :=
          mul_lt_mul_of_pos_right (hε (m * n) hmn) hm_pos
        _ = (n : F)⁻¹ := by
          push_cast
          field_simp

/-- Multiplying an infinitesimal by a natural number cast `(k : F)` yields an infinitesimal. -/
theorem IsInfinitesimalIn.natCast_mul {ε : F} (hε : IsInfinitesimalIn ε) (k : ℕ) :
    IsInfinitesimalIn ((k : F) * ε) := by
  rw [mul_comm]
  refine hε.mul_of_abs_le_nat (m := k) ?_
  rw [abs_of_nonneg (Nat.cast_nonneg k)]

/-- The product of two infinitesimals in any linearly ordered field is infinitesimal. -/
theorem IsInfinitesimalIn.mul {ε δ : F}
    (hε : IsInfinitesimalIn ε) (hδ : IsInfinitesimalIn δ) :
    IsInfinitesimalIn (ε * δ) := by
  have hδ1 : |δ| ≤ ((1 : ℕ) : F) := by
    have hlt : |δ| < (1 : F)⁻¹ := by simpa using hδ 1 Nat.one_pos
    simpa using hlt.le
  exact hε.mul_of_abs_le_nat hδ1

/-- Any positive natural power `ε ^ k` (`0 < k`) of an infinitesimal is infinitesimal. -/
theorem IsInfinitesimalIn.pow {ε : F} (hε : IsInfinitesimalIn ε) {k : ℕ} (hk : 0 < k) :
    IsInfinitesimalIn (ε ^ k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  induction m with
  | zero => simpa using hε
  | succ m ih =>
    rw [pow_succ]
    exact (ih (Nat.succ_pos m)).mul hε

/-- In any Archimedean linearly ordered field, `0` is the only infinitesimal. -/
theorem archimedean_isInfinitesimalIn_iff_eq_zero [Archimedean F] (ε : F) :
    IsInfinitesimalIn ε ↔ ε = 0 := by
  constructor
  · intro hε
    by_contra hne
    have habs_pos : 0 < |ε| := abs_pos.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_gt |ε|⁻¹
    have hn_cast_pos : (0 : F) < (n : F) := lt_trans (inv_pos.mpr habs_pos) hn
    have hn_pos : 0 < n := Nat.cast_pos.mp hn_cast_pos
    have hlt : |ε| < (n : F)⁻¹ := hε n hn_pos
    have hinv : (n : F) < |ε|⁻¹ := by
      simpa using inv_strictAnti₀ habs_pos hlt
    exact lt_asymm hn hinv
  · rintro rfl
    exact zero_isInfinitesimalIn

/-- An ordered field satisfies `∀ x : F, ∃ n : ℕ, x < n` if and only if it contains no infinite
elements (Goldblatt §1.3, p. 13). -/
theorem forall_exists_nat_gt_iff_not_exists_isInfiniteIn :
    (∀ x : F, ∃ n : ℕ, x < (n : F)) ↔ ¬ ∃ ω : F, IsInfiniteIn ω := by
  constructor
  · intro harch ⟨ω, hω⟩
    obtain ⟨n, hn⟩ := harch |ω|
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · exact not_lt_of_ge (abs_nonneg ω) (by simpa using hn)
    · exact lt_asymm hn (hω n hn_pos)
  · intro hno x
    by_cases hinf : IsInfiniteIn x
    · exact False.elim (hno ⟨x, hinf⟩)
    · unfold IsInfiniteIn at hinf
      push Not at hinf
      obtain ⟨n, _hn_pos, hle⟩ := hinf
      refine ⟨n + 1, ?_⟩
      calc
        x ≤ |x| := le_abs_self x
        _ ≤ (n : F) := hle
        _ < ((n + 1 : ℕ) : F) := by exact_mod_cast Nat.lt_succ_self n

/-- An ordered field satisfies `∀ x : F, ∃ n : ℕ, x < n` if and only if it contains no nonzero
infinitesimals (Goldblatt §1.3, p. 13). -/
theorem forall_exists_nat_gt_iff_not_exists_isNonzeroInfinitesimalIn :
    (∀ x : F, ∃ n : ℕ, x < (n : F)) ↔ ¬ ∃ ε : F, IsNonzeroInfinitesimalIn ε := by
  rw [forall_exists_nat_gt_iff_not_exists_isInfiniteIn]
  constructor
  · rintro hno ⟨ε, hε⟩
    exact hno ⟨ε⁻¹, (isNonzeroInfinitesimalIn_iff_inv_isInfiniteIn ε).mp hε⟩
  · rintro hno ⟨ω, hω⟩
    exact hno ⟨ω⁻¹, (isInfiniteIn_iff_inv_isNonzeroInfinitesimalIn ω).mp hω⟩

/-- **Goldblatt §1.1, p. 3**: In the real number system `ℝ`, the only infinitesimal is `0`. -/
theorem real_isInfinitesimalIn_iff_eq_zero (ε : ℝ) :
    IsInfinitesimalIn ε ↔ ε = 0 :=
  archimedean_isInfinitesimalIn_iff_eq_zero ε

/-- **Goldblatt §1.1, p. 3**: In `ℝ` there are no nonzero infinitesimals. -/
theorem not_real_isNonzeroInfinitesimalIn (ε : ℝ) :
    ¬ IsNonzeroInfinitesimalIn ε := by
  rintro ⟨hne, hinf⟩
  exact hne ((real_isInfinitesimalIn_iff_eq_zero ε).mp hinf)

/-- **Goldblatt §1.1, p. 3**: In `ℝ` there are no infinitely large numbers. -/
theorem not_real_isInfiniteIn (ω : ℝ) :
    ¬ IsInfiniteIn ω := by
  intro hω
  exact not_real_isNonzeroInfinitesimalIn ω⁻¹
    ((isInfiniteIn_iff_inv_isNonzeroInfinitesimalIn ω).mp hω)

end InfinitelySmallAndLarge

/-! ### §1.2 Historical Background (Goldblatt pp. 4–11) -/

section HistoricalBackground

/-! #### Archimedes: Exhaustion of the Circle & Quadrature of the Parabola (pp. 4–5) -/

/-- **Archimedes' Polygon Decomposition (Goldblatt §1.2, p. 4)**: A regular `n`-gon decomposed
into `n` congruent isosceles triangles of height (apothem) `r` and base `b` has total area
`(1 / 2) * r * P`, where `P = n * b` is its perimeter. -/
theorem archimedes_polygon_area_eq_half_apothem_perimeter (n : ℕ) (r b : ℝ) :
    (∑ _k ∈ Finset.range n, (1 / 2 : ℝ) * r * b) = (1 / 2 : ℝ) * r * ((n : ℝ) * b) := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- **Archimedes' Circle Formula `A = (1/2) r C` (Goldblatt §1.2, p. 4)**: A circle of radius `r`,
area `A = π r²`, and circumference `C = 2 π r` satisfies `A = (1 / 2) * r * C`. -/
theorem archimedes_circle_area_eq_half_radius_circumference (r : ℝ) :
    Real.pi * r ^ 2 = (1 / 2 : ℝ) * r * (2 * Real.pi * r) := by
  ring

/-- **Method of Exhaustion via *Reductio ad Absurdum* (Goldblatt §1.2, p. 4)**: Without invoking
infinite limits directly, if a sequence of polygon areas `P : ℕ → ℝ` can be made arbitrarily close
to both `A` and `B`, then `A ≠ B` yields a contradiction, hence `A = B`. -/
theorem archimedes_exhaustion_reductio {A B : ℝ} (P : ℕ → ℝ)
    (hP : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |P n - A| < ε ∧ |P n - B| < ε) :
    A = B := by
  by_contra hne
  have hpos : 0 < |A - B| / 2 := half_pos (abs_sub_pos.mpr hne)
  obtain ⟨N, hN⟩ := hP (|A - B| / 2) hpos
  obtain ⟨hA, hB⟩ := hN N le_rfl
  have htri : |A - B| < |A - B| := by
    calc
      |A - B| = |(A - P N) + (P N - B)| := by ring_nf
      _ ≤ |A - P N| + |P N - B| := abs_add_le _ _
      _ = |P N - A| + |P N - B| := by rw [abs_sub_comm A (P N)]
      _ < |A - B| / 2 + |A - B| / 2 := add_lt_add hA hB
      _ = |A - B| := add_halves |A - B|
  exact lt_irrefl _ htri

/-- Exact finite-sum identity `6 * ∑_{k=0}^{n-1} k² = n (n - 1) (2n - 1)` underlying Archimedes'
quadrature of the parabola `y = x²` on `[0, 1]` (Goldblatt §1.2, Footnote 1, pp. 4–5). -/
theorem sum_range_sq_mul_six (n : ℕ) :
    6 * (∑ k ∈ Finset.range n, (k : ℝ) ^ 2) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- Closed-form identity for the `n`-rectangle Riemann sum of `y = x²` on `[0, 1]`
(Goldblatt §1.2, Footnote 1, pp. 4–5). -/
theorem parabola_quadrature_riemann_sum {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range n, ((k : ℝ) / (n : ℝ)) ^ 2 * (1 / (n : ℝ))) =
      (1 - 1 / (n : ℝ)) * (2 - 1 / (n : ℝ)) / 6 := by
  have hn_ne : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hsum :
      (∑ k ∈ Finset.range n, ((k : ℝ) / (n : ℝ)) ^ 2 * (1 / (n : ℝ))) =
        (∑ k ∈ Finset.range n, (k : ℝ) ^ 2) / (n : ℝ) ^ 3 := by
    calc
      (∑ k ∈ Finset.range n, ((k : ℝ) / (n : ℝ)) ^ 2 * (1 / (n : ℝ))) =
          ∑ k ∈ Finset.range n, (k : ℝ) ^ 2 * ((n : ℝ) ^ 3)⁻¹ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        field_simp
      _ = (∑ k ∈ Finset.range n, (k : ℝ) ^ 2) * ((n : ℝ) ^ 3)⁻¹ := by
        rw [← Finset.sum_mul]
      _ = (∑ k ∈ Finset.range n, (k : ℝ) ^ 2) / (n : ℝ) ^ 3 := by
        rw [div_eq_mul_inv]
  rw [hsum]
  have h6 := sum_range_sq_mul_six n
  field_simp
  linarith

/-- **Quadrature of the Parabola `y = x²` on `[0, 1]` (Goldblatt §1.2, Footnote 1, pp. 4–5)**:
The Riemann sum `∑_{k=0}^{n-1} (k / n)² (1 / n)` converges to `1 / 3` as `n → ∞`. -/
theorem tendsto_parabola_quadrature :
    Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, ((k : ℝ) / (n : ℝ)) ^ 2 * (1 / (n : ℝ)))
      Filter.atTop (𝓝 ((1 : ℝ) / 3)) := by
  have h0 : Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hfun :
      Filter.Tendsto
        (fun n : ℕ => (1 - 1 / (n : ℝ)) * (2 - 1 / (n : ℝ)) / 6)
        Filter.atTop (𝓝 ((1 : ℝ) / 3)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) Filter.atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub h0
    have h2 : Filter.Tendsto (fun n : ℕ => 2 - 1 / (n : ℝ)) Filter.atTop (𝓝 (2 - 0)) :=
      tendsto_const_nhds.sub h0
    have hmul := (h1.mul h2).div_const (6 : ℝ)
    convert hmul using 1
    norm_num
  refine hfun.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  exact (parabola_quadrature_riemann_sum hn).symm

/-! #### Leibniz & Newton: Differential Product Rule and Method of Moments (pp. 5–7) -/

/-- **Leibniz's Product Increment Identity (Goldblatt §1.2, p. 5)**:
`d(xy) = (x + dx)(y + dy) - xy = x dy + y dx + dx dy`. -/
theorem leibniz_product_increment {R : Type*} [CommRing R] (x y dx dy : R) :
    (x + dx) * (y + dy) - x * y = x * dy + y * dx + dx * dy := by
  ring

/-- **Leibniz's Higher-Order Infinitesimal Justification (Goldblatt §1.2, p. 5)**:
In any linearly ordered field `F`, if `dx` is a nonzero infinitesimal and `dy` is an infinitesimal,
then `(dx * dy) / dx` is infinitesimal ("`dx dy` is infinitely small in comparison with `dx`"). -/
theorem leibniz_product_term_div_isInfinitesimalIn
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {dx dy : F} (hdx : IsNonzeroInfinitesimalIn dx) (hdy : IsInfinitesimalIn dy) :
    IsInfinitesimalIn ((dx * dy) / dx) := by
  rw [mul_div_cancel_left₀ dy hdx.1]
  exact hdy

/-- Equivalent explicit-hypothesis form of Leibniz's comparison: whenever `dx ≠ 0` and `dy` is
infinitesimal in `F`, the ratio `(dx * dy) / dx` is infinitesimal, so the error between the exact
product increment `(x + dx)(y + dy) - xy` and `x dy + y dx` is infinitely small relative to `dx`
(Goldblatt §1.2, p. 5). -/
theorem leibniz_product_error_div_isInfinitesimalIn
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (x y : F) {dx dy : F} (hdx : dx ≠ 0) (hdy : IsInfinitesimalIn dy) :
    IsInfinitesimalIn ((((x + dx) * (y + dy) - x * y) - (x * dy + y * dx)) / dx) := by
  have hsub : ((x + dx) * (y + dy) - x * y) - (x * dy + y * dx) = dx * dy := by ring
  rw [hsub, mul_div_cancel_left₀ dy hdx]
  exact hdy

/-- **Newton's Method of Moments for `y = x²` (Goldblatt §1.2, pp. 6–7)**:
Substituting `x + x' * o` for a fluent `x` with fluxion `x'` and nonzero infinitesimal time
increment `o`, dividing the increment by `o` differs from `2 * x * x'` by `x'² * o`, which is
infinitesimal whenever `|x'|` is bounded by a natural number. -/
theorem newton_moment_sq_error_isInfinitesimalIn
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (x x' : F) {o : F} (ho : IsNonzeroInfinitesimalIn o)
    {m : ℕ} (hx' : |x'| ≤ (m : F)) :
    IsInfinitesimalIn (((x + x' * o) ^ 2 - x ^ 2) / o - 2 * x * x') := by
  have hcalc : ((x + x' * o) ^ 2 - x ^ 2) / o - 2 * x * x' = o * (x' ^ 2) := by
    have ho_ne : o ≠ 0 := ho.1
    field_simp
    ring
  rw [hcalc]
  refine ho.2.mul_of_abs_le_nat (m := m ^ 2) ?_
  calc
    |x' ^ 2| = |x'| ^ 2 := abs_pow x' 2
    _ ≤ (m : F) ^ 2 := sq_le_sq' (by linarith [abs_nonneg x']) hx'
    _ = ((m ^ 2 : ℕ) : F) := by push_cast; rfl

/-! #### Euler: Infinitesimal Binomial Ratios and Exponential Limit (pp. 8–9) -/

/-- **Euler's Infinite Ratio Approximation (Goldblatt §1.2, p. 8)**:
In any linearly ordered field `F`, if `j` is infinitely large (`IsInfiniteIn j`) and `k : ℕ`, then
`(j - k) / j - 1` is infinitesimal, rigorously justifying Euler's replacement of `(j - 1) / j`,
`(j - 2) / j`, ... by `1`. -/
theorem euler_ratio_sub_one_isInfinitesimalIn
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {j : F} (hj : IsInfiniteIn j) (k : ℕ) :
    IsInfinitesimalIn (((j - k : F) / j) - 1) := by
  have hj_ne : j ≠ 0 := hj.ne_zero
  have hj_inv : IsInfinitesimalIn j⁻¹ :=
    ((isInfiniteIn_iff_inv_isNonzeroInfinitesimalIn j).mp hj).2
  have hcalc : ((j - k : F) / j) - 1 = -((k : F) * j⁻¹) := by
    field_simp
    ring
  rw [hcalc, isInfinitesimalIn_neg_iff]
  exact hj_inv.natCast_mul k

/-- **Euler's Full Binomial Numerator Ratio (Goldblatt §1.2, p. 8)**:
In any linearly ordered field `F`, for an infinitely large element `j` and any fixed degree
`n : ℕ`, the product `∏_{k=0}^{n-1} ((j - k) / j) = j(j - 1)⋯(j - n + 1) / jⁿ` differs from `1`
by an infinitesimal. -/
theorem euler_binomial_prod_sub_one_isInfinitesimalIn
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {j : F} (hj : IsInfiniteIn j) (n : ℕ) :
    IsInfinitesimalIn ((∏ k ∈ Finset.range n, ((j - k : F) / j)) - 1) := by
  induction n with
  | zero =>
    simp [zero_isInfinitesimalIn]
  | succ n ih =>
    rw [Finset.prod_range_succ]
    set P : F := ∏ k ∈ Finset.range n, ((j - k : F) / j)
    set r : F := (j - n : F) / j
    have hr : IsInfinitesimalIn (r - 1) := euler_ratio_sub_one_isInfinitesimalIn hj n
    have hdecomp : P * r - 1 = (P - 1) + (r - 1) + (P - 1) * (r - 1) := by ring
    rw [hdecomp]
    exact (ih.add hr).add (ih.mul hr)

/-- **Modern Limit Definition of `e` (Goldblatt §1.2, p. 9)**:
`lim_{n → ∞} (1 + 1 / n)ⁿ = exp 1`. -/
theorem tendsto_euler_exp_one :
    Filter.Tendsto (fun n : ℕ => (1 + (1 : ℝ) / n) ^ n) Filter.atTop (𝓝 (Real.exp 1)) :=
  Real.tendsto_one_add_div_pow_exp 1

/-- **Euler's Exponential Limit `eᶻ = lim_{n → ∞} (1 + z / n)ⁿ` (Goldblatt §1.2, p. 9)**. -/
theorem tendsto_euler_exp (z : ℝ) :
    Filter.Tendsto (fun n : ℕ => (1 + z / n) ^ n) Filter.atTop (𝓝 (Real.exp z)) :=
  Real.tendsto_one_add_div_pow_exp z

/-- **Casting Out Higher Powers `(dx)², (dx)³, ...` (Goldblatt §1.2, p. 9)**:
In any linearly ordered field `F`, for a nonzero infinitesimal `dx` and any exponent `k ≥ 2`,
the ratio `dx ^ k / dx` is infinitesimal (justifying Euler's neglect of `(dx)² / 2!`,
`(dx)³ / 3!`, ... in comparison with `dx`). -/
theorem euler_higher_power_div_isInfinitesimalIn
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {dx : F} (hdx : IsNonzeroInfinitesimalIn dx) {k : ℕ} (hk : 2 ≤ k) :
    IsInfinitesimalIn (dx ^ k / dx) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 2 := ⟨k - 2, by omega⟩
  have hdiv : dx ^ (m + 2) / dx = dx ^ (m + 1) := by
    have hdx_ne : dx ≠ 0 := hdx.1
    rw [pow_succ, mul_div_cancel_right₀ _ hdx_ne]
  rw [hdiv]
  exact hdx.2.pow (Nat.succ_pos m)

/-! #### Weierstrass: Arithmetization of Limits (p. 10) -/

/-- **Weierstrass `ε`-`δ` Limit Definition (Goldblatt §1.2, p. 10)**:
`lim_{x → a} f(x) = L` means `(∀ ε > 0) (∃ δ > 0)` such that `0 < |x - a| < δ` implies
`|f(x) - L| < ε`. -/
def WeierstrassLimit (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε

/-- **Equivalence of Weierstrass's `ε`-`δ` Limit and Filter Convergence (Goldblatt §1.2, p. 10)**:
`WeierstrassLimit f a L` holds if and only if `f` tends to `nhds L` along the punctured
neighborhood filter `nhdsWithin a {a}ᶜ`. -/
theorem weierstrassLimit_iff_tendsto_nhdsWithin (f : ℝ → ℝ) (a L : ℝ) :
    WeierstrassLimit f a L ↔ Filter.Tendsto f (nhdsWithin a {a}ᶜ) (𝓝 L) := by
  rw [WeierstrassLimit, Metric.tendsto_nhdsWithin_nhds]
  simp only [Set.mem_compl_singleton_iff, Real.dist_eq, ← abs_sub_pos, and_imp]

/-- **Robinson's Finite-Subset Satisfiability in `ℝ` (Goldblatt §1.2, p. 10)**:
Although `ℝ` has no positive infinitesimal satisfying all of `{0 < ε} ∪ {ε < 1 / n | n ≥ 1}`
simultaneously (`not_real_isNonzeroInfinitesimalIn`), every *finite* subset `S : Finset ℕ` of
these inequalities is satisfiable in `ℝ`. By the Compactness Theorem of first-order logic, the
full infinite system therefore has a model `*ℝ`. -/
theorem robinson_finite_satisfiability_in_real (S : Finset ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n ∈ S, 0 < n → ε < (n : ℝ)⁻¹ := by
  let M : ℕ := S.sup id + 1
  have hM_pos : (0 : ℝ) < (M : ℝ) := by positivity
  refine ⟨(M : ℝ)⁻¹, inv_pos.mpr hM_pos, fun n hnS hn_pos => ?_⟩
  have hn_le : n ≤ S.sup id := Finset.le_sup (f := id) hnS
  have hn_lt : (n : ℝ) < (M : ℝ) := by
    exact_mod_cast Nat.lt_succ_of_le hn_le
  exact inv_strictAnti₀ (Nat.cast_pos.mpr hn_pos) hn_lt

end HistoricalBackground

/-! ### §1.3 What Is a Real Number? (Goldblatt pp. 11–14) -/

section WhatIsARealNumber

/-! #### Characterization (2): Dedekind-Complete Ordered Fields & Eudoxus–Archimedes (pp. 11–13) -/

/-- **Dedekind Completeness (Goldblatt §1.3, Answer (2), p. 12)**:
A linearly ordered field `F` is *Dedekind complete* if every nonempty subset `S : Set F` that is
bounded above possesses a least upper bound in `F`. -/
def IsDedekindComplete (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] : Prop :=
  ∀ S : Set F, S.Nonempty → BddAbove S → ∃ lub : F, IsLUB S lub

/-- **Goldblatt §1.3, Answer (2), p. 12**: The real number field `ℝ` is Dedekind complete. -/
theorem real_isDedekindComplete : IsDedekindComplete ℝ :=
  fun S hne hbdd => ⟨sSup S, isLUB_csSup hne hbdd⟩

/-- Dual form of Dedekind completeness: in any Dedekind-complete ordered field, every nonempty
subset bounded below has a greatest lower bound. -/
theorem exists_isGLB_of_isDedekindComplete
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (hF : IsDedekindComplete F) {S : Set F} (hne : S.Nonempty) (hbdd : BddBelow S) :
    ∃ glb : F, IsGLB S glb := by
  have hneg_ne : (Neg.neg '' S).Nonempty := hne.image Neg.neg
  have hneg_bdd : BddAbove (Neg.neg '' S) := by
    obtain ⟨m, hm⟩ := hbdd
    refine ⟨-m, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact neg_le_neg (hm hx)
  obtain ⟨u, hu⟩ := hF (Neg.neg '' S) hneg_ne hneg_bdd
  refine ⟨-u, ?_⟩
  constructor
  · intro x hx
    have hmem : -x ∈ Neg.neg '' S := ⟨x, hx, rfl⟩
    exact neg_le.mp (hu.1 hmem)
  · intro b hb
    have hub : -b ∈ upperBounds (Neg.neg '' S) := by
      rintro _ ⟨x, hx, rfl⟩
      exact neg_le_neg (hb hx)
    exact le_neg.mp (hu.2 hub)

/-- **Eudoxus–Archimedes Principle from Dedekind Completeness (Goldblatt §1.3, p. 13)**:
Every Dedekind-complete ordered field is Archimedean: for each element `r : F`, there exists a
natural number `n : ℕ` with `r < n`. -/
theorem archimedean_of_isDedekindComplete
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (hF : IsDedekindComplete F) : ∀ r : F, ∃ n : ℕ, r < (n : F) := by
  intro r
  by_contra hno
  push Not at hno
  let S : Set F := Set.range (fun n : ℕ => (n : F))
  have hne : S.Nonempty := ⟨0, 0, Nat.cast_zero⟩
  have hbdd : BddAbove S := by
    refine ⟨r, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hno n
  obtain ⟨lub, hlub⟩ := hF S hne hbdd
  have hsub_lt : lub - 1 < lub := sub_lt_self lub zero_lt_one
  have hnot_ub : lub - 1 ∉ upperBounds S := fun hub => not_le_of_gt hsub_lt (hlub.2 hub)
  rw [mem_upperBounds] at hnot_ub
  push Not at hnot_ub
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hnot_ub
  have hlt : lub < ((n + 1 : ℕ) : F) := by
    push_cast
    linarith
  have hle : ((n + 1 : ℕ) : F) ≤ lub := hlub.1 ⟨n + 1, rfl⟩
  exact not_lt_of_ge hle hlt

/-- **Classical Two-Magnitude Eudoxus–Archimedes Principle (Goldblatt §1.3, p. 13)**:
In any Dedekind-complete ordered field, given any `a > 0` and any `b`, "the less can be multiplied
so as to exceed the other": there exists `n : ℕ` with `b < n * a`. -/
theorem eudoxus_archimedes_of_isDedekindComplete
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (hF : IsDedekindComplete F) {a : F} (ha : 0 < a) (b : F) :
    ∃ n : ℕ, b < (n : F) * a := by
  obtain ⟨n, hn⟩ := archimedean_of_isDedekindComplete hF (b / a)
  exact ⟨n, (div_lt_iff₀ ha).mp hn⟩

/-- **Goldblatt's Key Observation (Goldblatt §1.2, p. 11 & §1.3, p. 13)**:
No linearly ordered field `F` containing a nonzero infinitesimal can be Dedekind complete. In
particular, Dedekind's completeness axiom cannot transfer from `ℝ` to `*ℝ`. -/
theorem not_isDedekindComplete_of_exists_nonzeroInfinitesimal
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (h : ∃ ε : F, IsNonzeroInfinitesimalIn ε) : ¬ IsDedekindComplete F := by
  intro hF
  exact (forall_exists_nat_gt_iff_not_exists_isNonzeroInfinitesimalIn.mp
    (archimedean_of_isDedekindComplete hF)) h

/-- Companion form of Goldblatt's observation: no linearly ordered field containing an infinitely
large element can be Dedekind complete (Goldblatt §1.2, p. 11 & §1.3, p. 13). -/
theorem not_isDedekindComplete_of_exists_infinite
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (h : ∃ ω : F, IsInfiniteIn ω) : ¬ IsDedekindComplete F := by
  obtain ⟨ω, hω⟩ := h
  exact not_isDedekindComplete_of_exists_nonzeroInfinitesimal
    ⟨ω⁻¹, (isInfiniteIn_iff_inv_isNonzeroInfinitesimalIn ω).mp hω⟩

/-- Promotes a linearly ordered field `F` satisfying `IsDedekindComplete F` to Mathlib's
`ConditionallyCompleteLinearOrder F` while preserving its underlying `LinearOrder F`
definitionally. -/
noncomputable abbrev conditionallyCompleteLinearOrderOfIsDedekindComplete
    {F : Type*} [Field F] [iL : LinearOrder F] [IsStrictOrderedRing F]
    (hF : IsDedekindComplete F) : ConditionallyCompleteLinearOrder F where
  __ := iL
  __ := LinearOrder.toLattice
  sSup s := by
    classical
    exact if h : s.Nonempty ∧ BddAbove s then (hF s h.1 h.2).choose else 0
  sInf s := by
    classical
    exact if h : s.Nonempty ∧ BddBelow s then
      (exists_isGLB_of_isDedekindComplete hF h.1 h.2).choose
    else 0
  isLUB_csSup s hne hbdd := by
    have h : s.Nonempty ∧ BddAbove s := ⟨hne, hbdd⟩
    simpa [h] using (hF s hne hbdd).choose_spec
  isGLB_csInf s hne hbdd := by
    have h : s.Nonempty ∧ BddBelow s := ⟨hne, hbdd⟩
    simpa [h] using (exists_isGLB_of_isDedekindComplete hF hne hbdd).choose_spec
  csSup_of_not_bddAbove s hnot := by simp [hnot]
  csInf_of_not_bddBelow s hnot := by simp [hnot]

/-- **Canonical Ordered-Ring Isomorphism `F ≃+*o ℝ` (Goldblatt §1.3, Answer (2), p. 12)**:
Every Dedekind-complete ordered field is canonically isomorphic (as an ordered ring) to `ℝ`. -/
noncomputable def orderRingIsoRealOfIsDedekindComplete
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (hF : IsDedekindComplete F) : F ≃+*o ℝ :=
  letI : ConditionallyCompleteLinearOrder F :=
    conditionallyCompleteLinearOrderOfIsDedekindComplete hF
  ConditionallyCompleteLinearOrderedField.inducedOrderRingIso F ℝ

/-- **Categorical Uniqueness of Dedekind-Complete Ordered Fields (Goldblatt §1.3, p. 12)**:
"Any two complete ordered fields are isomorphic, so this notion uniquely characterises `ℝ`."
Between any two Dedekind-complete ordered fields `F₁` and `F₂`, there exists a *unique* ordered
ring isomorphism `F₁ ≃+*o F₂`. -/
theorem existsUnique_orderRingIso_of_isDedekindComplete
    {F₁ F₂ : Type*}
    [Field F₁] [LinearOrder F₁] [IsStrictOrderedRing F₁]
    [Field F₂] [LinearOrder F₂] [IsStrictOrderedRing F₂]
    (hF₁ : IsDedekindComplete F₁) (hF₂ : IsDedekindComplete F₂) :
    ∃! _e : F₁ ≃+*o F₂, True := by
  let e₁ : F₁ ≃+*o ℝ := orderRingIsoRealOfIsDedekindComplete hF₁
  let e₂ : F₂ ≃+*o ℝ := orderRingIsoRealOfIsDedekindComplete hF₂
  refine ⟨e₁.trans e₂.symm, trivial, fun f _ => ?_⟩
  have hsub : Subsingleton (F₁ ≃+*o F₂) := by
    refine ⟨fun g₁ g₂ => ?_⟩
    have heq : g₁.trans e₂ = g₂.trans e₂ := Subsingleton.elim _ _
    ext x
    exact e₂.injective (DFunLike.congr_fun heq x)
  exact Subsingleton.elim f (e₁.trans e₂.symm)

/-! #### Characterization (3): Dedekind Cuts of `ℚ` (p. 12) -/

/-- **Dedekind Cut in `ℚ` (Goldblatt §1.3, Answer (3), p. 12)**:
A partition of `ℚ` into a pair `(L, U)` of nonempty disjoint subsets such that every element of `L`
is strictly less than every element of `U`, and `L` has no largest member. -/
@[ext]
structure DedekindCutQ where
  /-- The lower class of rationals in the cut. -/
  L : Set ℚ
  /-- The upper class of rationals in the cut. -/
  U : Set ℚ
  /-- The lower class `L` is nonempty. -/
  L_nonempty : L.Nonempty
  /-- The upper class `U` is nonempty. -/
  U_nonempty : U.Nonempty
  /-- `L` and `U` are disjoint. -/
  disjoint : Disjoint L U
  /-- `L` and `U` partition `ℚ`. -/
  union_eq_univ : L ∪ U = Set.univ
  /-- Every member of `L` is strictly less than every member of `U`. -/
  lt_of_mem : ∀ ⦃q : ℚ⦄, q ∈ L → ∀ ⦃r : ℚ⦄, r ∈ U → q < r
  /-- `L` has no greatest element. -/
  no_max : ∀ ⦃q : ℚ⦄, q ∈ L → ∃ q' ∈ L, q < q'

namespace DedekindCutQ

/-- Membership in `U` is the exact negation of membership in `L`. -/
theorem mem_U_iff_not_mem_L (C : DedekindCutQ) (q : ℚ) : q ∈ C.U ↔ q ∉ C.L := by
  constructor
  · intro hU hL
    exact Set.disjoint_left.mp C.disjoint hL hU
  · intro hnotL
    have hmem : q ∈ C.L ∪ C.U := by rw [C.union_eq_univ]; trivial
    exact hmem.resolve_left hnotL

/-- The upper class `U` is uniquely determined as the complement `Lᶜ`. -/
theorem U_eq_compl_L (C : DedekindCutQ) : C.U = C.Lᶜ := by
  ext q
  exact C.mem_U_iff_not_mem_L q

/-- Two Dedekind cuts are equal if and only if their lower classes coincide. -/
theorem ext_L {C₁ C₂ : DedekindCutQ} (hL : C₁.L = C₂.L) : C₁ = C₂ := by
  ext <;> simp [U_eq_compl_L, hL]

/-- The lower class `L` of any Dedekind cut is downward closed. -/
theorem mem_L_of_lt (C : DedekindCutQ) {p q : ℚ} (hpq : p < q) (hq : q ∈ C.L) : p ∈ C.L := by
  by_contra hp
  have hpU : p ∈ C.U := (C.mem_U_iff_not_mem_L p).mpr hp
  exact lt_asymm hpq (C.lt_of_mem hq hpU)

/-- Natural ordering on Dedekind cuts by inclusion of lower classes. -/
instance : PartialOrder DedekindCutQ where
  le C₁ C₂ := C₁.L ⊆ C₂.L
  le_refl C := Set.Subset.rfl
  le_trans _ _ _ h₁ h₂ := Set.Subset.trans h₁ h₂
  le_antisymm _ _ h₁ h₂ := ext_L (Set.Subset.antisymm h₁ h₂)

/-- Every real number `x : ℝ` induces a canonical Dedekind cut on `ℚ` with lower class
`L = {q : ℚ | (q : ℝ) < x}` and upper class `U = {q : ℚ | x ≤ (q : ℝ)}`
(Goldblatt §1.3, Answer (3), p. 12). -/
def ofReal (x : ℝ) : DedekindCutQ where
  L := {q : ℚ | (q : ℝ) < x}
  U := {q : ℚ | x ≤ (q : ℝ)}
  L_nonempty := by
    obtain ⟨q, hq⟩ := exists_rat_lt x
    exact ⟨q, by simpa using hq⟩
  U_nonempty := by
    obtain ⟨r, hr⟩ := exists_rat_gt x
    exact ⟨r, by simpa using hr.le⟩
  disjoint := Set.disjoint_left.mpr fun q hlt hge => by
    simp only [Set.mem_ofPred] at hlt hge
    exact not_lt_of_ge hge hlt
  union_eq_univ := by
    ext q
    simp [lt_or_ge]
  lt_of_mem := fun q hq r hr => by
    simp only [Set.mem_ofPred] at hq hr
    exact Rat.cast_lt.mp (lt_of_lt_of_le hq hr)
  no_max := fun q hq => by
    simp only [Set.mem_ofPred] at hq
    obtain ⟨q', hqq', hq'x⟩ := exists_rat_btwn hq
    exact ⟨q', by simpa using hq'x, Rat.cast_lt.mp hqq'⟩

/-- Membership in the lower class `(ofReal x).L` means `(q : ℝ) < x`. -/
@[simp]
theorem mem_ofReal_L (x : ℝ) (q : ℚ) : q ∈ (ofReal x).L ↔ (q : ℝ) < x := by
  simp [ofReal]

/-- Membership in the upper class `(ofReal x).U` means `x ≤ (q : ℝ)`. -/
@[simp]
theorem mem_ofReal_U (x : ℝ) (q : ℚ) : q ∈ (ofReal x).U ↔ x ≤ (q : ℝ) := by
  simp [ofReal]

/-- When `x : ℝ` is irrational (such as `√2`), the upper class of `ofReal x` is strictly symmetric:
`U = {q : ℚ | x < (q : ℝ)}` (Goldblatt §1.3, p. 12). -/
theorem ofReal_U_eq_of_irrational {x : ℝ} (hx : Irrational x) :
    (ofReal x).U = {q : ℚ | x < (q : ℝ)} := by
  ext q
  simp only [mem_ofReal_U, Set.mem_ofPred]
  constructor
  · intro hle
    exact lt_of_le_of_ne hle (fun h => hx ⟨q, h.symm⟩)
  · exact le_of_lt

/-- The image in `ℝ` of the lower class `C.L` of any Dedekind cut is nonempty and bounded above. -/
theorem cast_L_nonempty_and_bddAbove (C : DedekindCutQ) :
    (((↑) : ℚ → ℝ) '' C.L).Nonempty ∧ BddAbove (((↑) : ℚ → ℝ) '' C.L) := by
  refine ⟨C.L_nonempty.image _, ?_⟩
  obtain ⟨r, hr⟩ := C.U_nonempty
  refine ⟨(r : ℝ), ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact Rat.cast_le.mpr (C.lt_of_mem hq hr).le

/-- **Real Number Reconstructed from a Dedekind Cut (Goldblatt §1.3, p. 12)**:
Maps a Dedekind cut `C` to the supremum `sSup ((↑) '' C.L)` in `ℝ`. -/
noncomputable def toReal (C : DedekindCutQ) : ℝ :=
  sSup (((↑) : ℚ → ℝ) '' C.L)

/-- `C.toReal` is the least upper bound in `ℝ` of the coerced lower class `((↑) : ℚ → ℝ) '' C.L`. -/
theorem isLUB_toReal (C : DedekindCutQ) :
    IsLUB (((↑) : ℚ → ℝ) '' C.L) C.toReal := by
  obtain ⟨hne, hbdd⟩ := C.cast_L_nonempty_and_bddAbove
  exact isLUB_csSup hne hbdd

/-- **Recovering `x = sSup ((↑) '' {q : ℚ | (q : ℝ) < x})` (Goldblatt §1.3, p. 12)**:
Every real number equals the supremum of its Dedekind lower cut. -/
@[simp]
theorem toReal_ofReal (x : ℝ) : (ofReal x).toReal = x := by
  have hne : (((↑) : ℚ → ℝ) '' (ofReal x).L).Nonempty := (ofReal x).L_nonempty.image _
  refine IsLUB.csSup_eq ?_ hne
  constructor
  · rintro _ ⟨q, hq, rfl⟩
    exact le_of_lt (by simpa using hq)
  · intro b hb
    by_contra hnot
    have hbx : b < x := lt_of_not_ge hnot
    obtain ⟨q, hbq, hqx⟩ := exists_rat_btwn hbx
    have hmem : (q : ℝ) ∈ ((↑) : ℚ → ℝ) '' (ofReal x).L := ⟨q, by simpa using hqx, rfl⟩
    exact not_lt_of_ge (hb hmem) hbq

/-- A rational `q` belongs to `C.L` if and only if `(q : ℝ) < C.toReal`. -/
theorem mem_L_iff_lt_toReal (C : DedekindCutQ) (q : ℚ) :
    q ∈ C.L ↔ (q : ℝ) < C.toReal := by
  have hlub := C.isLUB_toReal
  constructor
  · intro hq
    obtain ⟨q', hq'L, hqq'⟩ := C.no_max hq
    have hq'_le : (q' : ℝ) ≤ C.toReal := hlub.1 ⟨q', hq'L, rfl⟩
    exact lt_of_lt_of_le (Rat.cast_lt.mpr hqq') hq'_le
  · intro hlt
    have hnot_ub : (q : ℝ) ∉ upperBounds (((↑) : ℚ → ℝ) '' C.L) :=
      fun hub => not_le_of_gt hlt (hlub.2 hub)
    rw [mem_upperBounds] at hnot_ub
    push Not at hnot_ub
    obtain ⟨_, ⟨q', hq'L, rfl⟩, hqq'⟩ := hnot_ub
    exact C.mem_L_of_lt (Rat.cast_lt.mp hqq') hq'L

/-- **Uniqueness of Cut Representation**: Taking the cut of `C.toReal` recovers `C` identically. -/
@[simp]
theorem ofReal_toReal (C : DedekindCutQ) : ofReal C.toReal = C := by
  apply ext_L
  ext q
  simp [mem_L_iff_lt_toReal]

/-- **Order Isomorphism `DedekindCutQ ≃o ℝ` (Goldblatt §1.3, Answer (3), p. 12)**:
Dedekind cuts of `ℚ` ordered by lower-cut inclusion are order-isomorphic to `ℝ`. -/
noncomputable def orderIsoReal : DedekindCutQ ≃o ℝ where
  toFun := toReal
  invFun := ofReal
  left_inv := ofReal_toReal
  right_inv := toReal_ofReal
  map_rel_iff' := by
    intro C₁ C₂
    constructor
    · intro hle q hq
      rw [mem_L_iff_lt_toReal] at hq ⊢
      exact lt_of_lt_of_le hq hle
    · intro hsub
      have hlub₁ := C₁.isLUB_toReal
      have hlub₂ := C₂.isLUB_toReal
      refine hlub₁.2 ?_
      rintro _ ⟨q, hq, rfl⟩
      exact hlub₂.1 ⟨q, hsub hq, rfl⟩

end DedekindCutQ

/-- **Goldblatt's `√2` Dedekind Cut Example (Goldblatt §1.3, p. 12)**:
The explicit cut on `ℚ` representing `√2`, with `L = {q : ℚ | q ≤ 0 ∨ q² < 2}` and
`U = {q : ℚ | 0 < q ∧ 2 < q²}` (partitioning all of `ℚ` since `q² ≠ 2` for every `q : ℚ`). -/
def sqrtTwoCut : DedekindCutQ where
  L := {q : ℚ | q ≤ 0 ∨ q ^ 2 < 2}
  U := {q : ℚ | 0 < q ∧ 2 < q ^ 2}
  L_nonempty := ⟨1, by norm_num [Set.mem_ofPred]⟩
  U_nonempty := ⟨2, by norm_num [Set.mem_ofPred]⟩
  disjoint := by
    rw [Set.disjoint_left]
    intro q hL hU
    simp only [Set.mem_ofPred] at hL hU
    rcases hL with hq0 | hq2 <;> linarith [hU.1, hU.2]
  union_eq_univ := by
    ext q
    simp only [Set.mem_union, Set.mem_ofPred, Set.mem_univ, iff_true]
    rcases le_or_gt q 0 with hle | hpos
    · exact Or.inl (Or.inl hle)
    · rcases lt_trichotomy (q ^ 2) 2 with hlt | heq | hgt
      · exact Or.inl (Or.inr hlt)
      · exfalso
        have hcast : ((q : ℝ) ^ 2) = 2 := by exact_mod_cast heq
        have hsqrt : Real.sqrt 2 = (q : ℝ) := by
          rw [← hcast, Real.sqrt_sq (Rat.cast_nonneg.mpr hpos.le)]
        exact irrational_sqrt_two ⟨q, hsqrt.symm⟩
      · exact Or.inr ⟨hpos, hgt⟩
  lt_of_mem := by
    intro q hL r hU
    simp only [Set.mem_ofPred] at hL hU
    rcases hL with hq0 | hq2
    · exact lt_of_le_of_lt hq0 hU.1
    · by_contra hge
      push Not at hge
      have hsq : r ^ 2 ≤ q ^ 2 := by nlinarith [hU.1]
      linarith [hU.2]
  no_max := by
    intro q hL
    simp only [Set.mem_ofPred] at hL
    rcases hL with hq0 | hq2
    · exact ⟨1, by simp, lt_of_le_of_lt hq0 zero_lt_one⟩
    · rcases le_or_gt q 0 with hle | hpos
      · exact ⟨1, by simp, lt_of_le_of_lt hle zero_lt_one⟩
      · have hcast : (q : ℝ) < Real.sqrt 2 := by
          have hq2_real : (q : ℝ) ^ 2 < 2 := by exact_mod_cast hq2
          exact (Real.lt_sqrt (Rat.cast_nonneg.mpr hpos.le)).mpr hq2_real
        obtain ⟨q', hqq', hq's⟩ := exists_rat_btwn hcast
        have hq'_pos : 0 < q' := lt_trans hpos (Rat.cast_lt.mp hqq')
        have hq'2_real : (q' : ℝ) ^ 2 < 2 :=
          (Real.lt_sqrt (Rat.cast_nonneg.mpr hq'_pos.le)).mp hq's
        have hq'2 : q' ^ 2 < 2 := by exact_mod_cast hq'2_real
        exact ⟨q', by simp [hq'2], Rat.cast_lt.mp hqq'⟩

/-- `sqrtTwoCut` coincides with `DedekindCutQ.ofReal √2`. -/
theorem sqrtTwoCut_eq_ofReal_sqrt_two :
    sqrtTwoCut = DedekindCutQ.ofReal (Real.sqrt 2) := by
  apply DedekindCutQ.ext_L
  ext q
  simp only [sqrtTwoCut, DedekindCutQ.mem_ofReal_L, Set.mem_ofPred]
  constructor
  · rintro (hq0 | hq2)
    · exact lt_of_le_of_lt (Rat.cast_nonpos.mpr hq0) (Real.sqrt_pos.mpr zero_lt_two)
    · rcases le_or_gt q 0 with hle | hpos
      · exact lt_of_le_of_lt (Rat.cast_nonpos.mpr hle) (Real.sqrt_pos.mpr zero_lt_two)
      · have hq2_real : (q : ℝ) ^ 2 < 2 := by exact_mod_cast hq2
        exact (Real.lt_sqrt (Rat.cast_nonneg.mpr hpos.le)).mpr hq2_real
  · intro hlt
    rcases le_or_gt q 0 with hle | hpos
    · exact Or.inl hle
    · right
      have hq2_real : (q : ℝ) ^ 2 < 2 :=
        (Real.lt_sqrt (Rat.cast_nonneg.mpr hpos.le)).mp hlt
      exact_mod_cast hq2_real

/-- Reconstructing a real number from `sqrtTwoCut` yields `√2` (Goldblatt §1.3, p. 12). -/
theorem sqrtTwoCut_toReal : sqrtTwoCut.toReal = Real.sqrt 2 := by
  rw [sqrtTwoCut_eq_ofReal_sqrt_two, DedekindCutQ.toReal_ofReal]

/-! #### Characterization (4): Cantor's Cauchy Sequences of `ℚ` (p. 12) -/

/-- **Rational Cauchy Sequence (Goldblatt §1.3, Answer (4), p. 12)**:
A sequence `r : ℕ → ℚ` is Cauchy if `lim_{n, m → ∞} |rₙ - rₘ| = 0`. -/
def IsRatCauchySeq (r : ℕ → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |r n - r m| < ε

/-- Two-index `IsRatCauchySeq` is equivalent to Mathlib's `IsCauSeq abs`. -/
theorem isRatCauchySeq_iff_isCauSeq (r : ℕ → ℚ) :
    IsRatCauchySeq r ↔ IsCauSeq abs r := by
  constructor
  · intro hr ε hε
    obtain ⟨N, hN⟩ := hr ε hε
    exact ⟨N, fun n hn => hN N le_rfl n hn⟩
  · intro hr ε hε
    obtain ⟨N, hN⟩ := hr (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    calc
      |r n - r m| = |(r n - r N) + (r N - r m)| := by ring_nf
      _ ≤ |r n - r N| + |r N - r m| := abs_add_le _ _
      _ = |r n - r N| + |r m - r N| := by rw [abs_sub_comm (r N) (r m)]
      _ < ε / 2 + ε / 2 := add_lt_add (hN n hn) (hN m hm)
      _ = ε := add_halves ε

/-- **Cantor's Equivalence Relation on Rational Sequences (Goldblatt §1.3, Answer (4), p. 12)**:
Two sequences `r, s : ℕ → ℚ` are equivalent if `lim_{n → ∞} |rₙ - sₙ| = 0`. -/
def RatCauchyEquiv (r s : ℕ → ℚ) : Prop :=
  Filter.Tendsto (fun n : ℕ => |(r n : ℝ) - (s n : ℝ)|) Filter.atTop (𝓝 0)

/-- **Goldblatt §1.3, p. 12**: `RatCauchyEquiv` (`lim_{n → ∞} |rₙ - sₙ| = 0`) is an equivalence
relation. -/
theorem ratCauchyEquiv_equivalence : Equivalence RatCauchyEquiv where
  refl r := by
    simp [RatCauchyEquiv]
  symm := by
    intro r s hrs
    simpa only [RatCauchyEquiv, abs_sub_comm] using hrs
  trans := by
    intro r s t hrs hst
    rw [RatCauchyEquiv, Metric.tendsto_atTop] at hrs hst ⊢
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := hrs (ε / 2) (half_pos hε)
    obtain ⟨N₂, hN₂⟩ := hst (ε / 2) (half_pos hε)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    rw [Real.dist_0_eq_abs, abs_abs]
    have h₁ : |(r n : ℝ) - (s n : ℝ)| < ε / 2 := by
      simpa [Real.dist_0_eq_abs] using hN₁ n (le_of_max_le_left hn)
    have h₂ : |(s n : ℝ) - (t n : ℝ)| < ε / 2 := by
      simpa [Real.dist_0_eq_abs] using hN₂ n (le_of_max_le_right hn)
    calc
      |(r n : ℝ) - (t n : ℝ)| = |((r n : ℝ) - (s n : ℝ)) + ((s n : ℝ) - (t n : ℝ))| := by ring_nf
      _ ≤ |(r n : ℝ) - (s n : ℝ)| + |(s n : ℝ) - (t n : ℝ)| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add h₁ h₂
      _ = ε := add_halves ε

/-- `Setoid` on rational Cauchy sequences induced by `RatCauchyEquiv` (Goldblatt §1.3, p. 12). -/
def ratCauchySetoid : Setoid {r : ℕ → ℚ // IsRatCauchySeq r} where
  r a b := RatCauchyEquiv a.1 b.1
  iseqv :=
    { refl := fun a => ratCauchyEquiv_equivalence.refl a.1
      symm := fun h => ratCauchyEquiv_equivalence.symm h
      trans := fun h₁ h₂ => ratCauchyEquiv_equivalence.trans h₁ h₂ }

/-- Every rational Cauchy sequence `f : CauSeq ℚ abs` converges in `ℝ` to `Real.mk f`. -/
theorem tendsto_real_mk (f : CauSeq ℚ abs) :
    Filter.Tendsto (fun n : ℕ => (f n : ℝ)) Filter.atTop (𝓝 (Real.mk f)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨q, hq_pos, hq_lt⟩ := exists_pos_rat_lt (half_pos hε)
  have hq_pos_rat : (0 : ℚ) < q := Rat.cast_pos.mp hq_pos
  obtain ⟨N, hN⟩ := ((isRatCauchySeq_iff_isCauSeq f).mpr f.2) q hq_pos_rat
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  have hnear : |Real.mk f - (f n : ℝ)| ≤ (q : ℝ) := by
    refine Real.mk_near_of_forall_near ⟨N, fun j hj => ?_⟩
    have hjn : |f j - f n| < q := hN n hn j hj
    exact_mod_cast hjn.le
  exact lt_of_le_of_lt hnear (lt_trans hq_lt (half_lt_self hε))

/-- **Goldblatt §1.3, Answer (4), p. 12**: Two rational Cauchy sequences `f, g : CauSeq ℚ abs`
represent the same real number (`Real.mk f = Real.mk g`, i.e., `f ≈ g`) if and only if they are
equivalent in Goldblatt's sense (`RatCauchyEquiv f g`, i.e., `lim_{n → ∞} |fₙ - gₙ| = 0`). -/
theorem real_mk_eq_iff_ratCauchyEquiv (f g : CauSeq ℚ abs) :
    Real.mk f = Real.mk g ↔ RatCauchyEquiv f g := by
  constructor
  · intro heq
    have hf := tendsto_real_mk f
    have hg := tendsto_real_mk g
    rw [heq] at hf
    have hsub : Filter.Tendsto (fun n : ℕ => (f n : ℝ) - (g n : ℝ)) Filter.atTop (𝓝 0) := by
      simpa using hf.sub hg
    simpa [RatCauchyEquiv] using hsub.abs
  · intro hequiv
    have hzero : Filter.Tendsto (fun n : ℕ => (f n : ℝ) - (g n : ℝ)) Filter.atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr hequiv
    have hdiff := (tendsto_real_mk f).sub (tendsto_real_mk g)
    have heq0 : Real.mk f - Real.mk g = 0 := tendsto_nhds_unique hdiff hzero
    exact sub_eq_zero.mp heq0

/-- **Ring Isomorphism `ℝ ≃+* CauSeq.Completion.Cauchy (abs : ℚ → ℚ)`
(Goldblatt §1.3, Answer (4), p. 12)**: `ℝ` is ring-isomorphic to the Cauchy completion of `ℚ`. -/
def real_ringEquivCauchy : ℝ ≃+* CauSeq.Completion.Cauchy (abs : ℚ → ℚ) :=
  Real.ringEquivCauchy

/-! #### Characterization (1): Infinite Decimal Truncations & `√2` Approximations (p. 12) -/

/-- **Truncated Base-10 Decimal Approximation (Goldblatt §1.3, Answer (1), p. 12)**:
For `x : ℝ` and `n : ℕ`, `decimalTrunc x n = ⌊x · 10ⁿ⌋ / 10ⁿ ∈ ℚ` gives the `n`-decimal-place
rational lower approximation of `x`. -/
noncomputable def decimalTrunc (x : ℝ) (n : ℕ) : ℚ :=
  (⌊x * (10 : ℝ) ^ n⌋ : ℚ) / (10 : ℚ) ^ n

/-- `decimalTrunc x n` approximates `x` from below within `1 / 10ⁿ`. -/
theorem decimalTrunc_le_and_lt (x : ℝ) (n : ℕ) :
    (decimalTrunc x n : ℝ) ≤ x ∧ x < (decimalTrunc x n : ℝ) + 1 / (10 : ℝ) ^ n := by
  have h10_pos : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
  have hcast : (decimalTrunc x n : ℝ) = (⌊x * (10 : ℝ) ^ n⌋ : ℝ) / (10 : ℝ) ^ n := by
    simp [decimalTrunc]
  rw [hcast]
  constructor
  · exact (div_le_iff₀ h10_pos).mpr (Int.floor_le _)
  · rw [ ← add_div]
    exact (lt_div_iff₀ h10_pos).mpr (Int.lt_floor_add_one _)

/-- **Convergence of Decimal Truncations (Goldblatt §1.3, Answer (1), p. 12)**:
For every real number `x`, its sequence of base-10 decimal truncations converges to `x`. -/
theorem tendsto_decimalTrunc (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => (decimalTrunc x n : ℝ)) Filter.atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h10 : Filter.Tendsto (fun n : ℕ => ((1 / 10 : ℝ) ^ n)) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  rw [Metric.tendsto_atTop] at h10
  obtain ⟨N, hN⟩ := h10 ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hle, hlt⟩ := decimalTrunc_le_and_lt x n
  have hpow : (1 : ℝ) / (10 : ℝ) ^ n < ε := by
    have h := hN n hn
    rw [Real.dist_0_eq_abs, abs_of_pos (by positivity)] at h
    simpa [one_div_pow] using h
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
  linarith

/-- Every real number `x` is the limit of a rational Cauchy sequence (specifically its base-10
decimal truncations, uniting Answers (1) and (4) of Goldblatt §1.3, p. 12). -/
theorem isRatCauchySeq_decimalTrunc (x : ℝ) : IsRatCauchySeq (decimalTrunc x) := by
  intro ε hε
  have hε_real : (0 : ℝ) < (ε : ℝ) := Rat.cast_pos.mpr hε
  have htend := tendsto_decimalTrunc x
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend ((ε : ℝ) / 2) (half_pos hε_real)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hm' : |(decimalTrunc x m : ℝ) - x| < (ε : ℝ) / 2 := by
    simpa [Real.dist_eq] using hN m hm
  have hn' : |(decimalTrunc x n : ℝ) - x| < (ε : ℝ) / 2 := by
    simpa [Real.dist_eq] using hN n hn
  have hreal : |(decimalTrunc x n : ℝ) - (decimalTrunc x m : ℝ)| < (ε : ℝ) := by
    calc
      |(decimalTrunc x n : ℝ) - (decimalTrunc x m : ℝ)| =
          |((decimalTrunc x n : ℝ) - x) + (x - (decimalTrunc x m : ℝ))| := by ring_nf
      _ ≤ |(decimalTrunc x n : ℝ) - x| + |x - (decimalTrunc x m : ℝ)| := abs_add_le _ _
      _ = |(decimalTrunc x n : ℝ) - x| + |(decimalTrunc x m : ℝ) - x| := by
        rw [abs_sub_comm x (decimalTrunc x m : ℝ)]
      _ < (ε : ℝ) / 2 + (ε : ℝ) / 2 := add_lt_add hn' hm'
      _ = (ε : ℝ) := add_halves _
  exact_mod_cast hreal

/-- Every real number `x : ℝ` is the limit of a rational-valued Cauchy sequence
(Goldblatt §1.3, Answer (4), p. 12). -/
theorem exists_rat_cauchy_tendsto (x : ℝ) :
    ∃ r : ℕ → ℚ, IsRatCauchySeq r ∧
      Filter.Tendsto (fun n : ℕ => (r n : ℝ)) Filter.atTop (𝓝 x) :=
  ⟨decimalTrunc x, isRatCauchySeq_decimalTrunc x, tendsto_decimalTrunc x⟩

/-- **Goldblatt's `√2` Decimal Sequence `1, 1.4, 1.41, 1.414` (Goldblatt §1.3, p. 12)**:
Verifies the initial rational decimal truncations of `√2` cited in Answers (1) and (4). -/
theorem decimalTrunc_sqrt_two_initial :
    decimalTrunc (Real.sqrt 2) 0 = 1 ∧
    decimalTrunc (Real.sqrt 2) 1 = 14 / 10 ∧
    decimalTrunc (Real.sqrt 2) 2 = 141 / 100 ∧
    decimalTrunc (Real.sqrt 2) 3 = 1414 / 1000 := by
  have hsqrt_pos : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hfloor_eq : ∀ (n k : ℕ),
      (k : ℝ) ^ 2 ≤ 2 * ((10 : ℝ) ^ n) ^ 2 →
      2 * ((10 : ℝ) ^ n) ^ 2 < ((k : ℝ) + 1) ^ 2 →
      ⌊Real.sqrt 2 * (10 : ℝ) ^ n⌋ = (k : ℤ) := by
    intro n k hlo hhi
    rw [Int.floor_eq_iff]
    push_cast
    have hprod_nonneg : 0 ≤ Real.sqrt 2 * (10 : ℝ) ^ n := by positivity
    have hsq_eq : (Real.sqrt 2 * (10 : ℝ) ^ n) ^ 2 = 2 * ((10 : ℝ) ^ n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
    constructor
    · nlinarith [sq_nonneg ((k : ℝ) - Real.sqrt 2 * (10 : ℝ) ^ n)]
    · nlinarith [sq_nonneg ((k : ℝ) + 1 - Real.sqrt 2 * (10 : ℝ) ^ n)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [decimalTrunc, pow_zero, div_one]
    have h := hfloor_eq 0 1 (by norm_num) (by norm_num)
    simp_all
  · simp only [decimalTrunc, pow_one]
    have h := hfloor_eq 1 14 (by norm_num) (by norm_num)
    rw [pow_one] at h
    rw [h]
    norm_num
  · simp only [decimalTrunc]
    have h := hfloor_eq 2 141 (by norm_num) (by norm_num)
    rw [h]
    norm_num
  · simp only [decimalTrunc]
    have h := hfloor_eq 3 1414 (by norm_num) (by norm_num)
    rw [h]
    norm_num

end WhatIsARealNumber

end Goldblatt.Ch01
