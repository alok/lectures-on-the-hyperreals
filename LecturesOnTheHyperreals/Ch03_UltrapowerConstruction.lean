import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.Ultrafilter.Cardinality

/-!
# Chapter 3: Ultrapower Construction of the Hyperreals

Formalization of Robert Goldblatt, *Lectures on the Hyperreals*, Chapter 3 (pp. 23–34):

* **§3.1** The commutative ring `ℕ → ℝ` of real-valued sequences, zero divisors, and characterization
  of units (`seq_has_zero_divisors`, `isUnit_seq_iff_forall_ne_zero`).
* **§3.2–3.5** Equivalence modulo an ultrafilter, congruence laws (Exercises 3.3(1)–(3)),
  statement-value sets `⟦r = s⟧`, `⟦r < s⟧`, `⟦r ≤ s⟧`, and Exercises 3.5(1)–(4).
* **§3.6** The ultrapower `Ultrapower U` as a linearly ordered field (Theorem 3.6.1), specialized to
  canonical `ℝ*` (`Hyperreal`), plus collapse of principal ultrapowers `Ultrapower (pure k) ≃+*o ℝ`.
* **§3.7** Canonical order-preserving field embedding `ℝ →+*o ℝ*` (Theorem 3.7.1).
* **§3.8** Positive infinitesimals `ε`, unlimited hyperreals `ω`, sequences tending to `0` or `+∞`,
  and Exercise 3.8.1.
* **§3.9–3.10** Set enlargement `starSet` (`⋆A`), characterization of infinite sets via nonstandard
  members (Theorem 3.9.1 & Exercise 3.10(1)), Boolean/interval preservation, failure on countable
  unions, and `*ℤ` as a subring (Exercises 3.10(1)–(8)).
* **§3.11–3.12** Function extensions `starFun`, `starFun₂`, `starFunN`, injectivity/surjectivity,
  absolute value, and indicator/characteristic functions (Exercises 3.12(1)–(5)).
* **§3.13** Partial functions (`starPartialFun`), hypernaturals `ℕ*`, hyperintegers `ℤ*`,
  hyperrationals `ℚ*`, and hypersequences (`starSeq`).
* **§3.14–3.15** Enlarging `k`-ary relations (`starRel`), graphs of functions, finite products,
  and domains of relations/partial functions (Exercises 3.15(1)–(3)).
* **§3.16** Cardinality of ultrafilters on `ℕ` (`#(Ultrafilter ℕ) = 2 ^ 2 ^ ℵ₀`).
-/

noncomputable section

namespace Goldblatt

open Filter Hyperreal
open scoped Topology Cardinal Classical

/-! ## §3.1 The Ring of Real-Valued Sequences -/

/-- Alternating sequence `(1, 0, 1, 0, …)` used in Goldblatt §3.1 (p. 23). -/
def seqEvenOne : ℕ → ℝ := fun n ↦ if Even n then 1 else 0

/-- Alternating sequence `(0, 1, 0, 1, …)` used in Goldblatt §3.1 (p. 23). -/
def seqOddOne : ℕ → ℝ := fun n ↦ if Even n then 0 else 1

/-- `seqEvenOne ≠ 0` in `ℕ → ℝ`. -/
theorem seqEvenOne_ne_zero : seqEvenOne ≠ 0 := by
  intro h
  have h0 : seqEvenOne 0 = 0 := congrFun h 0
  simp [seqEvenOne] at h0

/-- `seqOddOne ≠ 0` in `ℕ → ℝ`. -/
theorem seqOddOne_ne_zero : seqOddOne ≠ 0 := by
  intro h
  have h1 : seqOddOne 1 = 0 := congrFun h 1
  simp [seqOddOne] at h1

/-- Goldblatt §3.1 (p. 23): `(1, 0, 1, 0, …) ⊗ (0, 1, 0, 1, …) = 0`, exhibiting zero divisors. -/
theorem seqEvenOne_mul_seqOddOne : seqEvenOne * seqOddOne = 0 := by
  ext n
  by_cases hn : Even n <;> simp [seqEvenOne, seqOddOne, hn]

/-- Goldblatt §3.1 (p. 23): `ℕ → ℝ` has nonzero zero divisors and so is not a field/domain. -/
theorem seq_has_zero_divisors :
    ∃ r s : ℕ → ℝ, r ≠ 0 ∧ s ≠ 0 ∧ r * s = 0 :=
  ⟨seqEvenOne, seqOddOne, seqEvenOne_ne_zero, seqOddOne_ne_zero, seqEvenOne_mul_seqOddOne⟩

/-- Goldblatt §3.1 (p. 23): A real sequence `r : ℕ → ℝ` has a multiplicative inverse in `ℕ → ℝ`
if and only if no term `r n` is zero. -/
theorem isUnit_seq_iff_forall_ne_zero (r : ℕ → ℝ) :
    IsUnit r ↔ ∀ n : ℕ, r n ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ n hn
    have hmul : (u.val * u.inv) n = 1 := congrFun u.val_inv n
    simp [Pi.mul_apply, hn] at hmul
  · intro h
    refine ⟨⟨r, fun n ↦ (r n)⁻¹, ?_, ?_⟩, rfl⟩ <;>
    · ext n
      simp [h n]

/-! ## §3.2–3.5 Equivalence Modulo an Ultrafilter and Statement Values -/

/-- Goldblatt §3.4 (p. 24): Statement value `⟦r = s⟧ = {n ∈ ℕ | r n = s n}`. -/
def stmtEq {α : Type*} (r s : ℕ → α) : Set ℕ := {n : ℕ | r n = s n}

/-- Goldblatt §3.4 (p. 24): Statement value `⟦r < s⟧ = {n ∈ ℕ | r n < s n}`. -/
def stmtLt {α : Type*} [LT α] (r s : ℕ → α) : Set ℕ := {n : ℕ | r n < s n}

/-- Goldblatt §3.4 (p. 24): Statement value `⟦r ≤ s⟧ = {n ∈ ℕ | r n ≤ s n}`. -/
def stmtLe {α : Type*} [LE α] (r s : ℕ → α) : Set ℕ := {n : ℕ | r n ≤ s n}

/-- Goldblatt §3.2 (p. 24): Almost-everywhere agreement modulo a filter `F`. -/
def SeqEquiv (F : Filter ℕ) (r s : ℕ → ℝ) : Prop := stmtEq r s ∈ F

/-- Goldblatt Exercise 3.5(1) (p. 25): `⟦r = s⟧ ∩ ⟦s = t⟧ ⊆ ⟦r = t⟧`. -/
theorem stmtEq_inter_subset {α : Type*} (r s t : ℕ → α) :
    stmtEq r s ∩ stmtEq s t ⊆ stmtEq r t :=
  fun _ ⟨hrs, hst⟩ ↦ hrs.trans hst

/-- Goldblatt Exercise 3.5(2) (p. 25):
`⟦r = r'⟧ ∩ ⟦s = s'⟧ ⊆ ⟦r + s = r' + s'⟧ ∩ ⟦r * s = r' * s'⟧`. -/
theorem stmtEq_add_mul_subset (r r' s s' : ℕ → ℝ) :
    stmtEq r r' ∩ stmtEq s s' ⊆ stmtEq (r + s) (r' + s') ∩ stmtEq (r * s) (r' * s') := by
  rintro n ⟨hr, hs⟩
  have hr' : r n = r' n := hr
  have hs' : s n = s' n := hs
  exact ⟨show r n + s n = r' n + s' n by rw [hr', hs'],
         show r n * s n = r' n * s' n by rw [hr', hs']⟩

/-- Goldblatt Exercise 3.5(3) (p. 25): `⟦r = r'⟧ ∩ ⟦s = s'⟧ ∩ ⟦r < s⟧ ⊆ ⟦r' < s'⟧`. -/
theorem stmtLt_congr_subset (r r' s s' : ℕ → ℝ) :
    stmtEq r r' ∩ stmtEq s s' ∩ stmtLt r s ⊆ stmtLt r' s' := by
  rintro n ⟨⟨hr, hs⟩, hlt⟩
  change r' n < s' n
  have hr' : r n = r' n := hr
  have hs' : s n = s' n := hs
  linarith [show r n < s n from hlt]

/-- Goldblatt Exercise 3.3(1) (p. 24): `SeqEquiv F` is an equivalence relation on `ℕ → ℝ`. -/
theorem seqEquiv_equivalence (F : Filter ℕ) : Equivalence (SeqEquiv F) where
  refl _ := univ_mem' fun _ ↦ rfl
  symm h := mem_of_superset h fun _ hn ↦ hn.symm
  trans h₁ h₂ := mem_of_superset (inter_mem h₁ h₂) (stmtEq_inter_subset _ _ _)

/-- Goldblatt Exercise 3.3(2) (p. 24): `SeqEquiv F` is a ring congruence on `ℕ → ℝ`. -/
theorem seqEquiv_add_mul {F : Filter ℕ} {r r' s s' : ℕ → ℝ}
    (hr : SeqEquiv F r r') (hs : SeqEquiv F s s') :
    SeqEquiv F (r + s) (r' + s') ∧ SeqEquiv F (r * s) (r' * s') := by
  have h := mem_of_superset (inter_mem hr hs) (stmtEq_add_mul_subset r r' s s')
  exact ⟨mem_of_superset h Set.inter_subset_left, mem_of_superset h Set.inter_subset_right⟩

/-- Goldblatt Exercise 3.3(3) (p. 24): `(1/(n+1))` is not equivalent to `0` modulo any ultrafilter `U`. -/
theorem harmonicSeq_not_seqEquiv_zero (U : Ultrafilter ℕ) :
    ¬ SeqEquiv (U : Filter ℕ) (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) 0 := by
  intro h
  unfold SeqEquiv at h
  have hemp : stmtEq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) 0 = ∅ := by
    ext n
    change ((n : ℝ) + 1)⁻¹ = 0 ↔ False
    simp only [iff_false]
    positivity
  rw [hemp] at h
  exact (Ultrafilter.neBot U).ne (empty_mem_iff_bot.1 h)

/-- Goldblatt Exercise 3.5(4) (p. 25): `⟦r < s⟧ ∈ F ↔ ⟦r' < s'⟧ ∈ F` under `SeqEquiv F`. -/
theorem stmtLt_mem_iff {F : Filter ℕ} {r r' s s' : ℕ → ℝ}
    (hr : SeqEquiv F r r') (hs : SeqEquiv F s s') :
    stmtLt r s ∈ F ↔ stmtLt r' s' ∈ F := by
  constructor
  · intro h
    exact mem_of_superset (inter_mem (inter_mem hr hs) h) (stmtLt_congr_subset r r' s s')
  · intro h
    have hr' : SeqEquiv F r' r := (seqEquiv_equivalence F).symm hr
    have hs' : SeqEquiv F s' s := (seqEquiv_equivalence F).symm hs
    exact mem_of_superset (inter_mem (inter_mem hr' hs') h) (stmtLt_congr_subset r' r s' s)

/-! ## §3.6–3.8 The Ultrapower, Principal Collapse, Infinitesimals, and Unlimited Numbers -/

/-- Goldblatt §3.6 (p. 25): Parametric ultrapower of `ℝ` modulo an arbitrary ultrafilter `U` on `ℕ`. -/
abbrev Ultrapower (U : Ultrafilter ℕ) : Type := Germ (U : Filter ℕ) ℝ

/-- Goldblatt Theorem 3.6.1 (p. 25): For any ultrafilter `U` on `ℕ`, `Ultrapower U` is a
linearly ordered field. -/
instance instFieldUltrapower (U : Ultrafilter ℕ) : Field (Ultrapower U) := inferInstance
instance instLinearOrderUltrapower (U : Ultrafilter ℕ) : LinearOrder (Ultrapower U) := inferInstance
instance instIsStrictOrderedRingUltrapower (U : Ultrafilter ℕ) :
    IsStrictOrderedRing (Ultrapower U) := inferInstance

/-- Goldblatt §3.8 (p. 28): If `U = pure k` is a principal ultrafilter on `ℕ`, then the ultrapower
`Ultrapower (pure k)` collapses via an order-ring isomorphism to `ℝ` (`[s] ↦ s k`). -/
def principalUltrapowerOrderRingIso (k : ℕ) : Ultrapower (pure k : Ultrafilter ℕ) ≃+*o ℝ where
  toFun x := Germ.liftOn x (fun s ↦ s k) (fun _ _ h ↦ h)
  invFun r := (r : Ultrapower (pure k : Ultrafilter ℕ))
  left_inv x := Germ.inductionOn x fun s ↦ Germ.coe_eq.2 (show s k = s k from rfl)
  right_inv _ := rfl
  map_mul' x y := Germ.inductionOn₂ x y fun _ _ ↦ rfl
  map_add' x y := Germ.inductionOn₂ x y fun _ _ ↦ rfl
  map_le_map_iff' {x y} := Germ.inductionOn₂ x y fun r s ↦ by
    change r k ≤ s k ↔ (r : Ultrapower (pure k : Ultrafilter ℕ)) ≤ (s : Ultrapower (pure k : Ultrafilter ℕ))
    exact (Germ.coe_le (l := ((pure k : Ultrafilter ℕ) : Filter ℕ)) (f := r) (g := s)).symm

/-- Goldblatt Theorem 3.7.1 (p. 27): `r ↦ (r : ℝ*)` is a strictly order-preserving ring embedding
of `ℝ` into `ℝ*`. -/
def realToHyperrealHom : ℝ →+*o ℝ* := Hyperreal.coeRingHom

theorem realToHyperreal_injective : Function.Injective realToHyperrealHom :=
  fun _ _ h ↦ Hyperreal.coe_eq_coe.1 h

/-- Goldblatt §3.8 (p. 27): `ε` is strictly between `0` and every positive real number `r`. -/
theorem epsilon_pos_infinitesimal :
    (0 : ℝ*) < Hyperreal.epsilon ∧ ∀ r : ℝ, 0 < r → Hyperreal.epsilon < (r : ℝ*) :=
  ⟨Hyperreal.epsilon_pos, fun _ hr ↦ Hyperreal.epsilon_lt_of_pos hr⟩

/-- Goldblatt §3.8 (p. 27): `ω` exceeds every standard real number `r`, hence `ω ∉ range ofReal`. -/
theorem omega_unlimited_and_nonstandard :
    (∀ r : ℝ, (r : ℝ*) < Hyperreal.omega) ∧ ∀ r : ℝ, (r : ℝ*) ≠ Hyperreal.omega :=
  ⟨Hyperreal.coe_lt_omega, fun r h ↦ (Hyperreal.coe_lt_omega r).ne h⟩

/-- Goldblatt §3.8 (p. 28): Any sequence `r : ℕ → ℝ` converging to `0` defines an element `[r]`
whose absolute value is smaller than every positive real. -/
theorem ofSeq_infinitesimal_of_tendsto_zero {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    ∀ c : ℝ, 0 < c → |ofSeq r| < (c : ℝ*) := by
  intro c hc
  have habs : Tendsto (fun n ↦ |r n|) atTop (𝓝 0) := by
    simpa using hr.abs
  have hev : ∀ᶠ n in atTop, |r n| < c := habs.eventually (Iio_mem_nhds hc)
  have hev' : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |r n| < c :=
    hev.filter_mono Nat.hyperfilter_le_atTop
  have h1 : ofSeq (fun n ↦ |r n|) < (c : ℝ*) := ofSeq_lt_ofSeq.2 hev'
  have h2 : |ofSeq r| = ofSeq (fun n ↦ |r n|) := rfl
  rwa [h2]

/-- Goldblatt §3.8 (p. 28): Any sequence `r : ℕ → ℝ` diverging to `+∞` defines an element `[r]`
greater than every real number. -/
theorem ofSeq_unlimited_of_tendsto_atTop {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    ∀ c : ℝ, (c : ℝ*) < ofSeq r := by
  intro c
  exact lt_of_tendsto_atTop c (hr.mono_left Nat.hyperfilter_le_atTop)

/-- Goldblatt Exercise 3.8.1 (p. 28): Using ONLY ordered-field axioms, if `e > 0` in an ordered
field `F` satisfies `e < r` for the image of every positive `r : ℝ`, then `e⁻¹` exceeds the image
of every `r : ℝ`. -/
theorem inv_gt_all_reals_of_pos_infinitesimal {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (ι : ℝ →+*o F) {e : F}
    (he_pos : 0 < e) (he_inf : ∀ r : ℝ, 0 < r → e < ι r) (r : ℝ) :
    ι r < e⁻¹ := by
  rcases le_or_gt r 0 with hr | hr
  · have h1 : ι r ≤ 0 := by
      have := OrderHomClass.mono ι hr
      rwa [map_zero] at this
    exact h1.trans_lt (inv_pos.2 he_pos)
  · have hpos : (0 : ℝ) < r⁻¹ := inv_pos.2 hr
    have hlt : e < ι r⁻¹ := he_inf r⁻¹ hpos
    have hinv_pos : 0 < ι r := by
      have hle : (0 : F) ≤ ι r := by
        have := OrderHomClass.mono ι hr.le
        rwa [map_zero] at this
      have hne : ι r ≠ 0 := by
        intro h0
        have h1 : (1 : F) = 0 := by
          calc (1 : F) = ι (r * r⁻¹) := by rw [mul_inv_cancel₀ hr.ne', map_one]
          _ = ι r * ι r⁻¹ := map_mul ι r r⁻¹
          _ = 0 := by rw [h0, zero_mul]
        exact one_ne_zero h1
      exact hle.lt_of_ne' hne
    have hmul : ι r * e < 1 := by
      calc ι r * e < ι r * ι r⁻¹ := mul_lt_mul_of_pos_left hlt hinv_pos
      _ = ι (r * r⁻¹) := (map_mul ι r r⁻¹).symm
      _ = 1 := by rw [mul_inv_cancel₀ hr.ne', map_one]
    exact (lt_div_iff₀ he_pos).2 hmul |>.trans_eq (one_div e)

/-! ## §3.9–3.10 Enlarging Sets (`starSet`) and Exercises 3.10(1)–(8) -/

/-- Goldblatt §3.9 (p. 28): Enlargement `*A ⊆ ℝ*` of a subset `A ⊆ ℝ`. -/
def starSet (A : Set ℝ) : Set ℝ* := {x : ℝ* | Germ.LiftPred (· ∈ A) x}

@[simp]
theorem ofSeq_mem_starSet {r : ℕ → ℝ} {A : Set ℝ} :
    ofSeq r ∈ starSet A ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ A :=
  Iff.rfl

@[simp]
theorem coe_mem_starSet {r : ℝ} {A : Set ℝ} :
    (r : ℝ*) ∈ starSet A ↔ r ∈ A :=
  Germ.liftPred_const_iff

/-- Goldblatt §3.9 (p. 29): Standard elements of `A` belong to `*A`. -/
theorem image_coe_subset_starSet (A : Set ℝ) :
    ((↑) : ℝ → ℝ*) '' A ⊆ starSet A := by
  rintro _ ⟨a, ha, rfl⟩
  exact coe_mem_starSet.2 ha

/-- Goldblatt Exercise 3.10(5) (p. 29): `*A ∩ ℝ = A`, expressed via preimage under `ℝ ↪ ℝ*`. -/
@[simp]
theorem preimage_coe_starSet (A : Set ℝ) :
    ((↑) : ℝ → ℝ*) ⁻¹' starSet A = A := by
  ext r
  exact coe_mem_starSet

/-- Goldblatt Theorem 3.9.1 (p. 29): Every infinite subset `A ⊆ ℝ` has a nonstandard member in `*A`. -/
theorem exists_nonstandard_mem_starSet_of_infinite {A : Set ℝ} (hA : A.Infinite) :
    ∃ x ∈ starSet A, x ∉ ((↑) : ℝ → ℝ*) '' A := by
  obtain ⟨f, hf_inj⟩ := hA.natEmbedding
  refine ⟨ofSeq (fun n ↦ (f n : ℝ)), ?_, ?_⟩
  · exact ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (f n).2)
  · rintro ⟨r, _, hr_eq⟩
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (f n : ℝ) = r :=
      Germ.coe_eq.1 hr_eq.symm
    have hfin : {n : ℕ | (f n : ℝ) = r}.Finite := by
      apply Set.Subsingleton.finite
      intro m hm k hk
      have hmk : (f m : ℝ) = (f k : ℝ) := hm.trans hk.symm
      exact hf_inj (Subtype.ext hmk)
    have hnot : {n : ℕ | (f n : ℝ) = r}ᶜ ∈ (hyperfilter ℕ : Filter ℕ) :=
      Filter.hyperfilter_le_cofinite hfin.compl_mem_cofinite
    have hemp : (∅ : Set ℕ) ∈ (hyperfilter ℕ : Filter ℕ) := by
      simpa using inter_mem hev hnot
    exact (Ultrafilter.neBot (hyperfilter ℕ)).ne (empty_mem_iff_bot.1 hemp)

/-- Goldblatt Exercise 3.10(1) (p. 29): If `A ⊆ ℝ` is finite, then `*A = image of A`, so `A` has no
nonstandard members. -/
theorem starSet_eq_image_of_finite {A : Set ℝ} (hA : A.Finite) :
    starSet A = ((↑) : ℝ → ℝ*) '' A := by
  apply Set.Subset.antisymm _ (image_coe_subset_starSet A)
  intro x hx
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  rw [ofSeq_mem_starSet] at hx
  have huniv : (⋃ a ∈ A, {n : ℕ | r n = a}) ∈ (hyperfilter ℕ : Filter ℕ) := by
    refine mem_of_superset hx fun n hn ↦ ?_
    exact Set.mem_biUnion hn rfl
  rw [Ultrafilter.mem_coe, (Ultrafilter.finite_biUnion_mem_iff hA)] at huniv
  obtain ⟨a, ha_mem, ha_ev⟩ := huniv
  exact ⟨a, ha_mem, (Germ.coe_eq.2 ha_ev).symm⟩

/-- Complete characterization combining Theorem 3.9.1 and Exercise 3.10(1):
`A ⊆ ℝ` is infinite iff `*A` strictly extends the standard copy of `A`. -/
theorem infinite_iff_exists_nonstandard_mem_starSet (A : Set ℝ) :
    A.Infinite ↔ ∃ x ∈ starSet A, x ∉ ((↑) : ℝ → ℝ*) '' A := by
  constructor
  · exact exists_nonstandard_mem_starSet_of_infinite
  · rintro ⟨x, hx, hnot⟩ hfin
    rw [starSet_eq_image_of_finite hfin] at hx
    exact hnot hx

/-- Goldblatt Exercise 3.10(2a) (p. 29): `A ⊆ B ↔ *A ⊆ *B`. -/
@[simp]
theorem starSet_subset_starSet_iff {A B : Set ℝ} :
    starSet A ⊆ starSet B ↔ A ⊆ B := by
  constructor
  · intro h r hr
    exact coe_mem_starSet.1 (h (coe_mem_starSet.2 hr))
  · intro h x
    refine Germ.inductionOn x fun r hr ↦ ?_
    exact hr.mono fun _ hn ↦ h hn

/-- Goldblatt Exercise 3.10(2b) (p. 29): `A = B ↔ *A = *B`. -/
@[simp]
theorem starSet_eq_starSet_iff {A B : Set ℝ} :
    starSet A = starSet B ↔ A = B := by
  rw [Set.Subset.antisymm_iff, Set.Subset.antisymm_iff,
      starSet_subset_starSet_iff, starSet_subset_starSet_iff]

/-- Goldblatt Exercise 3.10(3) (p. 29): Boolean algebra preservation of `starSet`. -/
@[simp]
theorem starSet_empty : starSet ∅ = ∅ := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp only [ofSeq_mem_starSet, Set.mem_empty_iff_false, eventually_false_iff_eq_bot]
  exact ⟨fun h ↦ (Ultrafilter.neBot (hyperfilter ℕ)).ne h, False.elim⟩

@[simp]
theorem starSet_univ : starSet Set.univ = Set.univ := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp only [ofSeq_mem_starSet, Set.mem_univ, eventually_true]

@[simp]
theorem starSet_inter (A B : Set ℝ) : starSet (A ∩ B) = starSet A ∩ starSet B := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  exact eventually_and

@[simp]
theorem starSet_union (A B : Set ℝ) : starSet (A ∪ B) = starSet A ∪ starSet B := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  exact Ultrafilter.eventually_or

@[simp]
theorem starSet_compl (A : Set ℝ) : starSet Aᶜ = (starSet A)ᶜ := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  exact Ultrafilter.eventually_not

@[simp]
theorem starSet_diff (A B : Set ℝ) : starSet (A \ B) = starSet A \ starSet B := by
  rw [Set.sdiff_eq, starSet_inter, starSet_compl, Set.sdiff_eq]

/-- Goldblatt Exercise 3.10(4) (p. 29): `*(⋃ n, A_n)` need NOT equal `⋃ n, *A_n`!
Explicit counterexample: `A_n = {n}`, where `ω ∈ *(⋃ n, {n})` yet `ω ∉ ⋃ n, *{n}`. -/
theorem starSet_iUnion_ne_iUnion_starSet :
    starSet (⋃ n : ℕ, ({(n : ℝ)} : Set ℝ)) ≠ ⋃ n : ℕ, starSet ({(n : ℝ)} : Set ℝ) := by
  intro h
  have hmem : Hyperreal.omega ∈ starSet (⋃ n : ℕ, ({(n : ℝ)} : Set ℝ)) := by
    rw [Hyperreal.omega, ofSeq_mem_starSet]
    exact Eventually.of_forall fun n ↦ Set.mem_iUnion.2 ⟨n, rfl⟩
  rw [h, Set.mem_iUnion] at hmem
  rcases hmem with ⟨n, hn⟩
  rw [starSet_eq_image_of_finite (Set.finite_singleton _)] at hn
  rcases hn with ⟨r, hr, hreq⟩
  rw [Set.mem_singleton_iff] at hr
  subst hr
  exact omega_unlimited_and_nonstandard.2 n hreq

/-- Goldblatt Exercise 3.10(6) (p. 29): `*[a, b] = {x ∈ ℝ* | a ≤ x ≤ b}`. -/
@[simp]
theorem starSet_Icc (a b : ℝ) :
    starSet (Set.Icc a b) = Set.Icc (a : ℝ*) (b : ℝ*) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp only [ofSeq_mem_starSet, Set.mem_Icc, eventually_and]
  exact ⟨fun ⟨ha, hb⟩ ↦ ⟨ofSeq_le_ofSeq.2 ha, ofSeq_le_ofSeq.2 hb⟩,
         fun ⟨ha, hb⟩ ↦ ⟨ofSeq_le_ofSeq.1 ha, ofSeq_le_ofSeq.1 hb⟩⟩

@[simp]
theorem starSet_Ioo (a b : ℝ) :
    starSet (Set.Ioo a b) = Set.Ioo (a : ℝ*) (b : ℝ*) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp only [ofSeq_mem_starSet, Set.mem_Ioo, eventually_and]
  exact ⟨fun ⟨ha, hb⟩ ↦ ⟨ofSeq_lt_ofSeq.2 ha, ofSeq_lt_ofSeq.2 hb⟩,
         fun ⟨ha, hb⟩ ↦ ⟨ofSeq_lt_ofSeq.1 ha, ofSeq_lt_ofSeq.1 hb⟩⟩

@[simp]
theorem starSet_Ici (a : ℝ) :
    starSet (Set.Ici a) = Set.Ici (a : ℝ*) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp only [ofSeq_mem_starSet, Set.mem_Ici]
  exact ⟨ofSeq_le_ofSeq.2, ofSeq_le_ofSeq.1⟩

@[simp]
theorem starSet_Ioi (a : ℝ) :
    starSet (Set.Ioi a) = Set.Ioi (a : ℝ*) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp only [ofSeq_mem_starSet, Set.mem_Ioi]
  exact ⟨ofSeq_lt_ofSeq.2, ofSeq_lt_ofSeq.1⟩

/-- Goldblatt Exercise 3.10(8) (p. 30): `*(ℝ⁺) = (ℝ*)⁺`. -/
theorem starSet_pos : starSet {x : ℝ | 0 < x} = {x : ℝ* | 0 < x} :=
  starSet_Ioi 0

/-- Goldblatt Exercise 3.10(7) (p. 29): `*ℤ` is a subring of `ℝ*`. -/
def starIntSubring : Subring ℝ* where
  carrier := starSet (Set.range (Int.cast : ℤ → ℝ))
  mul_mem' {x y} := Germ.inductionOn₂ x y fun r s hr hs ↦
    (hr.and hs).mono fun _ ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ ⟨a * b, by simp [← ha, ← hb]⟩
  one_mem' := coe_mem_starSet.2 ⟨1, Int.cast_one⟩
  add_mem' {x y} := Germ.inductionOn₂ x y fun r s hr hs ↦
    (hr.and hs).mono fun _ ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ ⟨a + b, by simp [← ha, ← hb]⟩
  zero_mem' := coe_mem_starSet.2 ⟨0, Int.cast_zero⟩
  neg_mem' {x} := Germ.inductionOn x fun r hr ↦
    hr.mono fun _ ⟨a, ha⟩ ↦ ⟨-a, by simp [← ha]⟩

/-! ## §3.11–3.13 Extending Functions, Partial Functions, `ℕ*`, `ℤ*`, `ℚ*`, and Hypersequences -/

/-- Goldblatt §3.11 (p. 30): Extension `*f : ℝ* → ℝ*` of `f : ℝ → ℝ`. -/
def starFun (f : ℝ → ℝ) : ℝ* → ℝ* := Germ.map f

/-- Goldblatt §3.12(5) (p. 31): Extension `*f : ℝ* → ℝ* → ℝ*` of a binary function `f : ℝ → ℝ → ℝ`. -/
def starFun₂ (f : ℝ → ℝ → ℝ) : ℝ* → ℝ* → ℝ* := Germ.map₂ f

@[simp]
theorem starFun_ofSeq (f : ℝ → ℝ) (r : ℕ → ℝ) :
    starFun f (ofSeq r) = ofSeq (f ∘ r) := rfl

/-- Goldblatt Exercise 3.12(1) (p. 30): `*f` agrees with `f` on standard reals. -/
@[simp]
theorem starFun_coe (f : ℝ → ℝ) (r : ℝ) :
    starFun f (r : ℝ*) = (f r : ℝ*) := rfl

@[simp]
theorem starFun₂_ofSeq (f : ℝ → ℝ → ℝ) (r s : ℕ → ℝ) :
    starFun₂ f (ofSeq r) (ofSeq s) = ofSeq (fun n ↦ f (r n) (s n)) := rfl

@[simp]
theorem starFun₂_coe (f : ℝ → ℝ → ℝ) (r s : ℝ) :
    starFun₂ f (r : ℝ*) (s : ℝ*) = (f r s : ℝ*) := rfl

@[simp]
theorem starFun_id : starFun id = id := Germ.map_id

theorem starFun_comp (g f : ℝ → ℝ) : starFun (g ∘ f) = starFun g ∘ starFun f := by
  ext x
  exact (Germ.map_map g f x).symm

/-- Goldblatt Exercise 3.12(2a) (p. 30): `f` is injective iff `*f` is injective. -/
theorem starFun_injective_iff {f : ℝ → ℝ} :
    Function.Injective (starFun f) ↔ Function.Injective f := by
  constructor
  · intro hf a b hab
    have : starFun f (a : ℝ*) = starFun f (b : ℝ*) := by simp [hab]
    exact Hyperreal.coe_eq_coe.1 (hf this)
  · intro hf x y hxy
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    rcases ofSeq_surjective y with ⟨s, rfl⟩
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f (r n) = f (s n) := Germ.coe_eq.1 hxy
    exact Germ.coe_eq.2 (hev.mono fun _ hn ↦ hf hn)

/-- Goldblatt Exercise 3.12(2b) (p. 30): `f` is surjective iff `*f` is surjective. -/
theorem starFun_surjective_iff {f : ℝ → ℝ} :
    Function.Surjective (starFun f) ↔ Function.Surjective f := by
  constructor
  · intro hf y
    obtain ⟨x, hx⟩ := hf (y : ℝ*)
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f (r n) = y := Germ.coe_eq.1 hx
    obtain ⟨n, hn⟩ := hev.exists
    exact ⟨r n, hn⟩
  · intro hf y
    rcases ofSeq_surjective y with ⟨s, rfl⟩
    choose g hg using hf
    refine ⟨ofSeq (fun n ↦ g (s n)), ?_⟩
    exact Germ.coe_eq.2 (Eventually.of_forall fun n ↦ hg (s n))

/-- Goldblatt Exercise 3.12(3) (p. 30): `*abs` equals the ordered-field absolute value on `ℝ*`. -/
@[simp]
theorem starFun_abs (x : ℝ*) : starFun abs x = |x| :=
  (Germ.abs_def x).symm

/-- Goldblatt Exercise 3.12(4) (p. 31): Characteristic function extension `*(χ_A) = χ_{*A}`. -/
theorem starFun_indicator_one (A : Set ℝ) :
    starFun (A.indicator (1 : ℝ → ℝ)) = (starSet A).indicator (1 : ℝ* → ℝ*) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  by_cases hx : ofSeq r ∈ starSet A
  · rw [Set.indicator_of_mem hx, Pi.one_apply]
    exact Germ.coe_eq.2 (hx.mono fun n hn ↦ Set.indicator_of_mem hn _)
  · rw [Set.indicator_of_notMem hx]
    have hnot : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∉ A :=
      Ultrafilter.eventually_not.2 hx
    exact Germ.coe_eq.2 (hnot.mono fun n hn ↦ Set.indicator_of_notMem hn _)

/-- Constructive lifting `(Fin k → Germ l α) → Germ l (Fin k → α)`. -/
def piToGerm {α : Type*} {l : Filter ℕ} : {k : ℕ} → (Fin k → Germ l α) → Germ l (Fin k → α)
  | 0, _ => Germ.const Fin.elim0
  | _ + 1, v => Germ.map₂ Fin.cons (v 0) (piToGerm (Fin.tail v))

@[simp]
theorem piToGerm_coe {α : Type*} {l : Filter ℕ} :
    ∀ {k : ℕ} (r : Fin k → ℕ → α),
      piToGerm (l := l) (fun i ↦ (r i : Germ l α)) = ((fun n i ↦ r i n) : Germ l (Fin k → α))
  | 0, _ => Germ.coe_eq.2 <| Eventually.of_forall fun _ ↦ funext fun i ↦ Fin.elim0 i
  | _ + 1, r => by
      unfold piToGerm
      have htail : (Fin.tail fun i ↦ (r i : Germ l α)) = fun j ↦ (r j.succ : Germ l α) := rfl
      rw [htail, piToGerm_coe (fun j ↦ r j.succ), Germ.map₂_coe]
      exact Germ.coe_eq.2 <| Eventually.of_forall fun n ↦ funext fun i ↦
        Fin.cases rfl (fun _ ↦ rfl) i

/-- Canonical bijection between germs of `k`-tuples and `k`-tuples of germs. -/
def germPiEquiv {α : Type*} (l : Filter ℕ) (k : ℕ) :
    Germ l (Fin k → α) ≃ (Fin k → Germ l α) where
  toFun g i := g.map (fun t ↦ t i)
  invFun := piToGerm
  left_inv g := Germ.inductionOn g fun t ↦ by
    simp [Germ.map_coe]
  right_inv v := by
    choose r hr using fun i ↦ Quot.exists_rep (v i)
    have hv : v = fun i ↦ (r i : Germ l α) := funext fun i ↦ (hr i).symm
    rw [hv, piToGerm_coe]
    ext i
    rfl

/-- Specialization of `piToGerm` to `ℝ*`. -/
def hyperrealTupleToGerm {k : ℕ} (v : Fin k → ℝ*) : Germ (hyperfilter ℕ : Filter ℕ) (Fin k → ℝ) :=
  piToGerm (α := ℝ) (l := (hyperfilter ℕ : Filter ℕ)) v

@[simp]
theorem hyperrealTupleToGerm_ofSeq {k : ℕ} (r : Fin k → ℕ → ℝ) :
    hyperrealTupleToGerm (fun i ↦ ofSeq (r i)) = ((fun n i ↦ r i n) : Germ (hyperfilter ℕ : Filter ℕ) (Fin k → ℝ)) :=
  piToGerm_coe r

/-- Goldblatt Exercise 3.12(5) (p. 31): Extension `*f : (Fin m → ℝ*) → ℝ*` of an `m`-ary function. -/
def starFunN {m : ℕ} (f : (Fin m → ℝ) → ℝ) (v : Fin m → ℝ*) : ℝ* :=
  (hyperrealTupleToGerm v).map f

@[simp]
theorem starFunN_ofSeq {m : ℕ} (f : (Fin m → ℝ) → ℝ) (r : Fin m → ℕ → ℝ) :
    starFunN f (fun i ↦ ofSeq (r i)) = ofSeq (fun n ↦ f (fun i ↦ r i n)) := by
  unfold starFunN
  rw [hyperrealTupleToGerm_ofSeq]
  rfl

@[simp]
theorem starFunN_coe {m : ℕ} (f : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) :
    starFunN f (fun i ↦ (x i : ℝ*)) = (f x : ℝ*) :=
  starFunN_ofSeq f (fun i _ ↦ x i)

/-- Goldblatt §3.13 (p. 31): Extension `*f : starSet A → ℝ*` of a partial function `f : A → ℝ`. -/
def starPartialFun {A : Set ℝ} (f : A → ℝ) (x : starSet A) : ℝ* :=
  starFun (fun r ↦ if hr : r ∈ A then f ⟨r, hr⟩ else 0) x.1

theorem starPartialFun_coe {A : Set ℝ} (f : A → ℝ) (a : A) :
    starPartialFun f ⟨(a.1 : ℝ*), coe_mem_starSet.2 a.2⟩ = (f a : ℝ*) := by
  unfold starPartialFun
  rw [starFun_coe, dite_eq_left_of_eq_true (eq_true a.2)]

theorem starPartialFun_ofSeq {A : Set ℝ} (f : A → ℝ) (r : ℕ → ℝ)
    (hr : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ A) :
    starPartialFun f ⟨ofSeq r, hr⟩ =
      ofSeq (fun n ↦ if h : r n ∈ A then f ⟨r n, h⟩ else 0) := rfl

/-- Goldblatt §3.9, §3.13, §5.10: The hypernaturals `ℕ*` as the ultrapower of `ℕ`. -/
abbrev Hypernat : Type := Germ (hyperfilter ℕ : Filter ℕ) ℕ
@[inherit_doc] notation "ℕ*" => Hypernat

/-- Goldblatt §3.10(7), §5.11: The hyperintegers `ℤ*` as the ultrapower of `ℤ`. -/
abbrev Hyperint : Type := Germ (hyperfilter ℕ : Filter ℕ) ℤ
@[inherit_doc] notation "ℤ*" => Hyperint

/-- Goldblatt §5.1, §18.1: The hyperrationals `ℚ*` as the ultrapower of `ℚ`. -/
abbrev Hyperrat : Type := Germ (hyperfilter ℕ : Filter ℕ) ℚ
@[inherit_doc] notation "ℚ*" => Hyperrat

/-- Canonical unlimited hypernatural `ω_ℕ = [(0, 1, 2, …)] ∈ ℕ*`. -/
def omegaNat : ℕ* := ((id : ℕ → ℕ) : ℕ*)

/-- Order-preserving semiring embedding `ℕ* ↪ ℝ*`. -/
def Hypernat.toHyperreal : ℕ* → ℝ* := Germ.map (Nat.cast : ℕ → ℝ)

/-- Order-preserving ring embedding `ℤ* ↪ ℝ*`. -/
def Hyperint.toHyperreal : ℤ* → ℝ* := Germ.map (Int.cast : ℤ → ℝ)

/-- Order-preserving field embedding `ℚ* ↪ ℝ*`. -/
def Hyperrat.toHyperreal : ℚ* → ℝ* := Germ.map (Rat.cast : ℚ → ℝ)

theorem Hypernat.toHyperreal_injective : Function.Injective Hypernat.toHyperreal := by
  intro x y h
  refine Germ.inductionOn₂ x y (fun a b hab ↦ ?_) h
  exact Germ.coe_eq.2 ((Germ.coe_eq.1 hab).mono fun _ hn ↦ Nat.cast_injective hn)

theorem Hyperint.toHyperreal_injective : Function.Injective Hyperint.toHyperreal := by
  intro x y h
  refine Germ.inductionOn₂ x y (fun a b hab ↦ ?_) h
  exact Germ.coe_eq.2 ((Germ.coe_eq.1 hab).mono fun _ hn ↦ Int.cast_injective hn)

theorem Hyperrat.toHyperreal_injective : Function.Injective Hyperrat.toHyperreal := by
  intro x y h
  refine Germ.inductionOn₂ x y (fun a b hab ↦ ?_) h
  exact Germ.coe_eq.2 ((Germ.coe_eq.1 hab).mono fun _ hn ↦ Rat.cast_injective hn)

@[simp]
theorem Hypernat.toHyperreal_natCast (n : ℕ) :
    Hypernat.toHyperreal (n : ℕ*) = (n : ℝ*) := rfl

@[simp]
theorem Hypernat.toHyperreal_omegaNat :
    Hypernat.toHyperreal omegaNat = Hyperreal.omega := rfl

@[simp]
theorem Hypernat.toHyperreal_add (x y : ℕ*) :
    Hypernat.toHyperreal (x + y) = Hypernat.toHyperreal x + Hypernat.toHyperreal y :=
  Germ.inductionOn₂ x y fun a b ↦ Germ.coe_eq.2 <| Eventually.of_forall fun n ↦ Nat.cast_add (a n) (b n)

@[simp]
theorem Hypernat.toHyperreal_mul (x y : ℕ*) :
    Hypernat.toHyperreal (x * y) = Hypernat.toHyperreal x * Hypernat.toHyperreal y :=
  Germ.inductionOn₂ x y fun a b ↦ Germ.coe_eq.2 <| Eventually.of_forall fun n ↦ Nat.cast_mul (a n) (b n)

@[simp]
theorem Hypernat.toHyperreal_le_iff {x y : ℕ*} :
    Hypernat.toHyperreal x ≤ Hypernat.toHyperreal y ↔ x ≤ y :=
  Germ.inductionOn₂ x y fun a b ↦ by
    change ofSeq (fun n ↦ (a n : ℝ)) ≤ ofSeq (fun n ↦ (b n : ℝ)) ↔ (a : ℕ*) ≤ (b : ℕ*)
    rw [ofSeq_le_ofSeq, Germ.coe_le]
    simp only [EventuallyLE, Nat.cast_le]

@[simp]
theorem Hypernat.toHyperreal_lt_iff {x y : ℕ*} :
    Hypernat.toHyperreal x < Hypernat.toHyperreal y ↔ x < y :=
  Germ.inductionOn₂ x y fun a b ↦ by
    change ofSeq (fun n ↦ (a n : ℝ)) < ofSeq (fun n ↦ (b n : ℝ)) ↔ (a : ℕ*) < (b : ℕ*)
    rw [ofSeq_lt_ofSeq, Germ.coe_lt]
    simp only [Nat.cast_lt]

/-- Exact identification of `ℕ*` inside `ℝ*` with `*ℕ = starSet (range Nat.cast)`. -/
theorem range_hypernat_toHyperreal :
    Set.range Hypernat.toHyperreal = starSet (Set.range (Nat.cast : ℕ → ℝ)) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  constructor
  · rintro ⟨N, hN⟩
    refine Germ.inductionOn N (fun a ha ↦ ?_) hN
    exact (Germ.coe_eq.1 ha).mono fun n hn ↦ ⟨a n, hn⟩
  · intro hr
    let a : ℕ → ℕ := fun n ↦ if h : r n ∈ Set.range (Nat.cast : ℕ → ℝ) then h.choose else 0
    refine ⟨(a : ℕ*), Germ.coe_eq.2 ?_⟩
    refine hr.mono fun n hn ↦ ?_
    change ((if h : r n ∈ Set.range (Nat.cast : ℕ → ℝ) then h.choose else 0 : ℕ) : ℝ) = r n
    rw [dite_eq_left_of_eq_true (eq_true hn)]
    exact hn.choose_spec

/-- Exact identification of `ℤ*` inside `ℝ*` with `*ℤ = starSet (range Int.cast)`. -/
theorem range_hyperint_toHyperreal :
    Set.range Hyperint.toHyperreal = starSet (Set.range (Int.cast : ℤ → ℝ)) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  constructor
  · rintro ⟨N, hN⟩
    refine Germ.inductionOn N (fun a ha ↦ ?_) hN
    exact (Germ.coe_eq.1 ha).mono fun n hn ↦ ⟨a n, hn⟩
  · intro hr
    let a : ℕ → ℤ := fun n ↦ if h : r n ∈ Set.range (Int.cast : ℤ → ℝ) then h.choose else 0
    refine ⟨(a : ℤ*), Germ.coe_eq.2 ?_⟩
    refine hr.mono fun n hn ↦ ?_
    change ((if h : r n ∈ Set.range (Int.cast : ℤ → ℝ) then h.choose else 0 : ℤ) : ℝ) = r n
    rw [dite_eq_left_of_eq_true (eq_true hn)]
    exact hn.choose_spec

/-- Exact identification of `ℚ*` inside `ℝ*` with `*ℚ = starSet (range Rat.cast)`. -/
theorem range_hyperrat_toHyperreal :
    Set.range Hyperrat.toHyperreal = starSet (Set.range (Rat.cast : ℚ → ℝ)) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  constructor
  · rintro ⟨N, hN⟩
    refine Germ.inductionOn N (fun a ha ↦ ?_) hN
    exact (Germ.coe_eq.1 ha).mono fun n hn ↦ ⟨a n, hn⟩
  · intro hr
    let a : ℕ → ℚ := fun n ↦ if h : r n ∈ Set.range (Rat.cast : ℚ → ℝ) then h.choose else 0
    refine ⟨(a : ℚ*), Germ.coe_eq.2 ?_⟩
    refine hr.mono fun n hn ↦ ?_
    change ((if h : r n ∈ Set.range (Rat.cast : ℚ → ℝ) then h.choose else 0 : ℚ) : ℝ) = r n
    rw [dite_eq_left_of_eq_true (eq_true hn)]
    exact hn.choose_spec

/-- Goldblatt §3.13 (p. 31): Extension of a sequence `s : ℕ → ℝ` to a hypersequence
`starSeq s : ℕ* → ℝ*`. -/
def starSeq (s : ℕ → ℝ) : ℕ* → ℝ* := Germ.map s

@[simp]
theorem starSeq_coe (s : ℕ → ℝ) (a : ℕ → ℕ) :
    starSeq s (a : ℕ*) = ofSeq (fun k ↦ s (a k)) := rfl

@[simp]
theorem starSeq_natCast (s : ℕ → ℝ) (n : ℕ) :
    starSeq s (n : ℕ*) = (s n : ℝ*) := rfl

@[simp]
theorem starSeq_omegaNat (s : ℕ → ℝ) :
    starSeq s omegaNat = ofSeq s := rfl

theorem starSeq_add (s t : ℕ → ℝ) (N : ℕ*) :
    starSeq (fun n ↦ s n + t n) N = starSeq s N + starSeq t N :=
  Germ.inductionOn N fun _ ↦ rfl

theorem starSeq_sub (s t : ℕ → ℝ) (N : ℕ*) :
    starSeq (fun n ↦ s n - t n) N = starSeq s N - starSeq t N :=
  Germ.inductionOn N fun _ ↦ rfl

theorem starSeq_mul (s t : ℕ → ℝ) (N : ℕ*) :
    starSeq (fun n ↦ s n * t n) N = starSeq s N * starSeq t N :=
  Germ.inductionOn N fun _ ↦ rfl

theorem starSeq_abs (s : ℕ → ℝ) (N : ℕ*) :
    starSeq (fun n ↦ |s n|) N = |starSeq s N| :=
  Germ.inductionOn N fun _ ↦ rfl

/-! ## §3.14–3.15 Enlarging `k`-ary Relations (`starRel`) and Exercises 3.15(1)–(3) -/

/-- Goldblatt §3.14 (p. 31): Enlargement `*P ⊆ (Fin k → ℝ*)` of a `k`-ary relation `P ⊆ ℝ^k`. -/
def starRel {k : ℕ} (P : Set (Fin k → ℝ)) : Set (Fin k → ℝ*) :=
  {v : Fin k → ℝ* | (hyperrealTupleToGerm v).LiftPred (· ∈ P)}

@[simp]
theorem starRel_ofSeq {k : ℕ} (P : Set (Fin k → ℝ)) (r : Fin k → ℕ → ℝ) :
    (fun i ↦ ofSeq (r i)) ∈ starRel P ↔
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (fun i ↦ r i n) ∈ P := by
  change (hyperrealTupleToGerm (fun i ↦ ofSeq (r i))).LiftPred (· ∈ P) ↔ _
  rw [hyperrealTupleToGerm_ofSeq, Germ.liftPred_coe]

@[simp]
theorem starRel_coe {k : ℕ} (P : Set (Fin k → ℝ)) (x : Fin k → ℝ) :
    (fun i ↦ (x i : ℝ*)) ∈ starRel P ↔ x ∈ P := by
  change (fun i ↦ ofSeq (fun _ ↦ x i)) ∈ starRel P ↔ x ∈ P
  rw [starRel_ofSeq, eventually_const]

/-- Goldblatt §3.14 (p. 32): `*(Graph f) = Graph (*f)` for any `m`-ary function `f : ℝ^m → ℝ`. -/
theorem starRel_graph {m : ℕ} (f : (Fin m → ℝ) → ℝ) :
    starRel {p : Fin (m + 1) → ℝ | f (Fin.init p) = p (Fin.last m)} =
      {p : Fin (m + 1) → ℝ* | starFunN f (Fin.init p) = p (Fin.last m)} := by
  ext p
  choose r hr using fun i ↦ ofSeq_surjective (p i)
  have hp : p = fun i ↦ ofSeq (r i) := funext fun i ↦ (hr i).symm
  rw [hp, starRel_ofSeq]
  change (∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f (Fin.init fun i ↦ r i n) = r (Fin.last m) n) ↔
    starFunN f (fun i ↦ ofSeq (r i.castSucc)) = ofSeq (r (Fin.last m))
  rw [starFunN_ofSeq]
  exact Germ.coe_eq.symm

/-- Goldblatt Exercise 3.15(1) (p. 32): `*(A_1 × … × A_k) = *A_1 × … × *A_k`. -/
theorem starRel_pi {k : ℕ} (A : Fin k → Set ℝ) :
    starRel (Set.univ.pi A) = Set.univ.pi (fun i ↦ starSet (A i)) := by
  ext v
  choose r hr using fun i ↦ ofSeq_surjective (v i)
  have hv : v = fun i ↦ ofSeq (r i) := funext fun i ↦ (hr i).symm
  rw [hv, starRel_ofSeq]
  simp only [Set.mem_univ_pi, ofSeq_mem_starSet, eventually_all]

/-- Binary relation enlargement `starRel₂` for convenience in Goldblatt Exercise 3.15(2). -/
def starRel₂ (P : Set (ℝ × ℝ)) : Set (ℝ* × ℝ*) :=
  {p : ℝ* × ℝ* | Germ.LiftRel (fun a b ↦ (a, b) ∈ P) p.1 p.2}

/-- Goldblatt Exercise 3.15(2) (p. 33): `*(dom P) = dom (*P)` for any binary relation `P ⊆ ℝ × ℝ`. -/
theorem starSet_dom_eq_dom_starRel₂ (P : Set (ℝ × ℝ)) :
    starSet (Prod.fst '' P) = Prod.fst '' starRel₂ P := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  constructor
  · intro hx
    rw [ofSeq_mem_starSet] at hx
    let s : ℕ → ℝ := fun n ↦ if h : r n ∈ Prod.fst '' P then h.choose.2 else 0
    have hs : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (r n, s n) ∈ P := by
      refine hx.mono fun n hn ↦ ?_
      have hspec := hn.choose_spec
      have hsn : s n = hn.choose.2 := dite_eq_left_of_eq_true (eq_true hn)
      have hp : (r n, s n) = hn.choose := Prod.ext hspec.2.symm hsn
      rw [hp]
      exact hspec.1
    exact ⟨(ofSeq r, ofSeq s), hs, rfl⟩
  · rintro ⟨⟨_, y⟩, hy, rfl⟩
    rcases ofSeq_surjective y with ⟨s, rfl⟩
    exact hy.mono fun n hn ↦ ⟨(r n, s n), hn, rfl⟩

/-- Goldblatt Exercise 3.15(3) (p. 33): Generalization to `(m + 1)`-ary relations — projecting out
the last coordinate commutes with enlargement `*(dom P) = dom (*P)`. -/
theorem starRel_dom {m : ℕ} (P : Set (Fin (m + 1) → ℝ)) :
    starRel (Fin.init '' P) = Fin.init '' starRel P := by
  ext v
  choose r hr using fun i ↦ ofSeq_surjective (v i)
  have hv : v = fun i ↦ ofSeq (r i) := funext fun i ↦ (hr i).symm
  rw [hv, starRel_ofSeq]
  constructor
  · intro hv_mem
    let lastSeq : ℕ → ℝ := fun n ↦
      if h : (fun i ↦ r i n) ∈ Fin.init '' P then h.choose (Fin.last m) else 0
    let full : Fin (m + 1) → ℕ → ℝ := Fin.snoc r lastSeq
    refine ⟨fun i ↦ ofSeq (full i), ?_, ?_⟩
    · rw [starRel_ofSeq]
      refine hv_mem.mono fun n hn ↦ ?_
      have hspec := hn.choose_spec
      have heq : (fun i : Fin (m + 1) ↦ full i n) = hn.choose := by
        ext j
        refine Fin.lastCases ?_ (fun i ↦ ?_) j
        · simp only [full, Fin.snoc_last]
          exact dite_eq_left_of_eq_true (eq_true hn)
        · have hi := congrFun hspec.2 i
          simpa [full, Fin.init] using hi.symm
      rw [heq]
      exact hspec.1
    · ext i
      simp [Fin.init, full]
  · rintro ⟨w, hw, hw_eq⟩
    choose s hs using fun i ↦ ofSeq_surjective (w i)
    have hw' : w = fun i ↦ ofSeq (s i) := funext fun i ↦ (hs i).symm
    rw [hw', starRel_ofSeq] at hw
    have heq_all : ∀ i : Fin m, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), s i.castSucc n = r i n := by
      intro i
      have hi : ofSeq (s i.castSucc) = ofSeq (r i) := by
        have := congrFun hw_eq i
        simpa [hw', Fin.init] using this
      exact Germ.coe_eq.1 hi
    rw [← eventually_all] at heq_all
    refine (hw.and heq_all).mono fun n ⟨hnP, hnsr⟩ ↦ ?_
    refine ⟨fun j ↦ s j n, hnP, ?_⟩
    ext i
    exact hnsr i

/-! ## §3.16 Cardinality of Ultrafilters on `ℕ` -/

/-- Goldblatt §3.16 (p. 33): There are `2 ^ (2 ^ ℵ₀)` ultrafilters on `ℕ`, matching `#(Set (Set ℕ))`. -/
theorem cardinal_ultrafilter_nat : #(Ultrafilter ℕ) = 2 ^ (2 ^ (ℵ₀ : Cardinal) : Cardinal) := by
  simpa [Cardinal.mk_nat] using (Cardinal.mk_ultrafilter_of_infinite (α := ℕ))

end Goldblatt
end
