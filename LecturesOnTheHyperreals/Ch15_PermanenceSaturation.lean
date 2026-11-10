import LecturesOnTheHyperreals.Ch12_InternalFunctions
import Mathlib.Analysis.Real.Cardinality
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Chapter 15: Permanence, Comprehensiveness, and Saturation

Complete formalization of Robert Goldblatt, *Lectures on the Hyperreals: An Introduction to
Nonstandard Analysis* (GTM 188), Chapter 15 (pp. 191–202):

* **§15.1 Permanence Principles** (pp. 191–192):
  - **Theorem 15.1.1(1)** (`permanence_overflow_nat`, `permanence_overflow_arbitrarily_large_nat`):
    Overflow on `ℕ*` for internal formulas/sets.
  - **Theorem 15.1.1(2)** (`permanence_underflow_nat`, `permanence_underflow_all_unlimited`):
    Underflow on `ℕ*` from an unlimited upper bound and from all unlimited hypernaturals.
  - **Theorem 15.1.1(3)** (`permanence_halo`, `permanence_posInfinitesimal_underflow`,
    `permanence_posInfinitesimal_overflow`): Halo permanence, positive-infinitesimal underflow to a
    standard interval `(0, r)`, and positive-infinitesimal overflow from standard `r > 0`.
  - **Theorem 15.1.1(4)** (`permanence_posUnlimited_of_arbitrarily_large_real`,
    `permanence_negUnlimited_of_arbitrarily_small_real`): Spillover from arbitrarily large (resp.
    small) standard reals to positive (resp. negative) unlimited hyperreals via internal
    order-completeness.
  - **Theorem 15.1.1(5)** (`permanence_ray_overflow_limited`, `permanence_ray_overflow_starSet`,
    `counterexample_ray_overflow_standard_only`): Ray overflow `[r, b]` up to a positive unlimited
    `b ∈ ℝ*` via internal order-completeness.
  - **Exercise 15.1.2** (`exists_nat_bound_of_limited_on_internal`,
    `exists_nat_bound_of_limited_internalGermFun`): Any internal `*ℝ`-valued function taking only
    limited values on an internal subset `A ⊆ dom f` is uniformly bounded by a standard `n ∈ ℕ`.
* **§15.2 Robinson's Sequential Lemma** (p. 193):
  - Internal hypersequences `internalSeq`, `IsInternalSeq`, correspondence with `InternalPartialFun`
    (`isInternalSeq_iff_exists_internalFun`), and externality of `{N ∈ ℕ* | s N ≈ₕ 0}`
    (`isExternalNat_infinitesimal_locus`).
  - **Lemma 15.2.1** (`robinson_sequential_lemma`, `robinson_sequential_lemma_forall_le_trick`,
    `robinson_sequential_lemma_bounded`, `robinson_sequential_lemma_internalFun`): Robinson's
    Sequential Lemma for internal sequences on `ℕ*` and `{n ∈ ℕ* | n ≤ M}`.
  - **Exercise 15.2.2** (`robinson_sequential_infClose`, `robinson_sequential_infClose_lt`,
    `robinson_sequential_infClose_bounded`): Persistence of `s_n ≈ₕ c` up to an unlimited index, plus
    double-limit diagonalization (`robinson_double_limit_diagonal`).
  - **Theorem 15.2.3** (`robinson_limited_to_unlimited_interval`,
    `robinson_limited_infClose_to_unlimited_interval`): An internal function infinitesimal (or `≈ₕ c`)
    on all limited hyperreals remains so on `[-b, b]` for some positive unlimited `b ∈ ℝ*`.
* **§15.3 Uniformly Converging Sequences of Functions** (pp. 193–194):
  - Internal hypersequence of functions `starFunSeq`, nonstandard characterization of continuity on
    subsets (`continuousOn_iff_infClose_starSet`), and infinitesimal closeness at unlimited indices
    (`infClose_starFunSeq_of_tendstoUniformlyOn`).
  - Alternative proof via Robinson's Sequential Lemma that a uniform limit of continuous functions
    on `[a, b]` is continuous (`continuousOn_of_tendstoUniformlyOn_via_robinson`).
  - **Exercise 15.3.1** (`tendstoUniformlyOn_of_infClose_unlimited`,
    `tendstoUniformlyOn_iff_infClose_unlimited`): Equivalence of uniform convergence on `[a, b]` with
    `starFunSeq f N x ≈ₕ starFun g x` for all unlimited `N ∈ ℕ*` and `x ∈ *[a, b]`.
* **§15.4 Comprehensiveness & Countable Comprehensiveness** (pp. 195–198):
  - Full comprehensiveness of ultrapowers `Germ (U : Filter ι) α → Germ (U : Filter ι) β`
    (`ultrapowerExtWithRep`, `ultrapower_comprehensive`) and **Exercise 15.4.1(1)–(2)**
    (`ultrapowerExtWithRep_eq_on_nonstandard_of_cofinite`,
    `ultrapowerExtWithRep_canonicalRep_eq_map`, `ultrapowerExtWithRep_canonicalRep_eq_starFun`).
  - Explicit comprehensiveness and countable/sequential comprehensiveness of `ℝ*` via diagonalization
    (`countable_comprehensiveness_seq`, `countable_comprehensiveness_internalFun`,
    `full_comprehensiveness_internalFun`), plus nonprincipal / countably incomplete ultrafilters on `ℕ`.
  - Alternative proof via countable comprehensiveness + overflow that no infinite internal set is
    countable (`not_countable_infinite_of_isInternal_via_comprehensiveness`), and domain/range
    obstructions for external sets.
  - **Theorem 15.4.3** (`exists_unlimited_lt_countable_via_comprehensiveness`): Robinson's proof via
    sequential comprehensiveness + overflow that every countable set of unlimited hypernaturals has
    a strict unlimited lower bound.
  - **Exercise 15.4.4** (`cumMin`, `IsInternalSeq.cumMin`,
    `exists_unlimited_lt_countable_via_robinson_lemma`): Internality of `s̲_n = min_{m ≤ n} s_m` and
    proof of Theorem 15.4.3 via Robinson's Sequential Lemma on `(s̲_n)⁻¹`.
* **§15.5 Universe Embeddings & Equivalence of Countable Saturation and Comprehensiveness**
  (pp. 196–198):
  - Axiom-free `UniverseEmbedding` framework and **Theorem 15.4.2**
    (`UniverseEmbedding.countableComprehensiveness_iff_countableSaturation`,
    `UniverseEmbedding.sequentialComprehensiveness_iff_countableSaturation`): equivalence of
    countable comprehensiveness (`*ℕ \ ℕ ≠ ∅`), sequential comprehensiveness (`*ℕ \ ℕ ≠ ∅`), and
    countable saturation, plus concrete `ℝ*` / `ℕ*` / `InternalPartialFun` saturation and both
    concrete directions on `ℝ*`.
* **§15.6 `κ`-Saturation, `ℵ₁`-Saturation, Concurrent Relations, and Cardinality Bounds**
  (pp. 198–199):
  - Equivalence of countable saturation with `ℵ₁`-saturation, proof that `ℝ*` is `ℵ₁`-saturated
    (`aleph_one_saturated_hyperreal`), **Exercise 15.5.1** characterizing `κ`-saturation via
    concurrent internal relations (`UniverseEmbedding.isKappaSaturated_iff_concurrent`,
    `countable_saturation_hyperreal_iff_concurrent_internalRel₂`), internal cardinality lower bound
    `#Y ≥ κ` (`UniverseEmbedding.card_infinite_internal_ge_of_kappaSaturated`), exact cardinality
    `#(ℝ*) = 2 ^ ℵ₀` (`card_hyperreal_eq_continuum`), and failure of `(2 ^ ℵ₀)⁺`-saturation
    (`not_succ_continuum_saturated_hyperreal`).
-/

noncomputable section

namespace Goldblatt.Ch15

open Filter
open Hyperreal (ofSeq ofSeq_lt_ofSeq ofSeq_le_ofSeq ofSeq_surjective)
open scoped Topology Cardinal Classical BigOperators

/-! ## §15.1 Permanence Principles -/

/-- Goldblatt §15.1, Theorem 15.1.1(1) (pp. 191–192, **Overflow**):
If an internal subset `X ⊆ ℕ*` contains `(n : ℕ*)` for every standard `n ≥ k` (`k ∈ ℕ`), then there
exists an unlimited `K ∈ ℕ*` such that `N ∈ X` for all `N ∈ ℕ*` with `k ≤ N ≤ K`. -/
theorem permanence_overflow_nat {X : Set ℕ*} (hX : IsInternalNat X) {k : ℕ}
    (hfin : ∀ n : ℕ, k ≤ n → (n : ℕ*) ∈ X) :
    ∃ K : ℕ*, IsUnlimitedNat K ∧ ∀ N : ℕ*, (k : ℕ*) ≤ N → N ≤ K → N ∈ X :=
  overflow_nat hX hfin

/-- Goldblatt §15.1 (p. 191): If an internal subset `X ⊆ ℕ*` contains arbitrarily large finite
`n : ℕ`, then `X` contains an unlimited hypernatural `ω ∈ ℕ*`. -/
theorem permanence_overflow_arbitrarily_large_nat {X : Set ℕ*} (hX : IsInternalNat X)
    (hlarge : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ (n : ℕ*) ∈ X) :
    ∃ ω ∈ X, IsUnlimitedNat ω := by
  obtain ⟨ω, hωX, hω_unl, _⟩ :=
    arbitrarily_small_unlimited_of_arbitrarily_large_nat hX hlarge omegaNat isUnlimitedNat_omegaNat
  exact ⟨ω, hωX, hω_unl⟩

/-- Goldblatt §15.1, Theorem 15.1.1(2) (p. 192, **Underflow**):
If an internal subset `X ⊆ ℕ*` and an unlimited `K ∈ ℕ*` satisfy `N ∈ X` for every unlimited
`N ≤ K`, then there exists `k ∈ ℕ` such that `(n : ℕ*) ∈ X` for all `n ≥ k` in `ℕ` (and indeed
`N ∈ X` for all `N ∈ ℕ*` with `k ≤ N ≤ K`). -/
theorem permanence_underflow_nat {X : Set ℕ*} (hX : IsInternalNat X) {K : ℕ*}
    (hK : IsUnlimitedNat K) (hunl : ∀ N : ℕ*, IsUnlimitedNat N → N ≤ K → N ∈ X) :
    ∃ k : ℕ, (∀ N : ℕ*, (k : ℕ*) ≤ N → N ≤ K → N ∈ X) ∧
      (∀ n : ℕ, k ≤ n → (n : ℕ*) ∈ X) := by
  obtain ⟨k, hk⟩ := underflow_nat hX hK hunl
  exact ⟨k, hk, fun n hkn ↦ hk (n : ℕ*) (by exact_mod_cast hkn) (hK n).le⟩

/-- Goldblatt §15.1 (p. 192, **Unbounded Underflow**):
If an internal subset `X ⊆ ℕ*` contains every unlimited `ω ∈ ℕ*`, then `X` contains the entire tail
`{N ∈ ℕ* | N₀ ≤ N}` for some standard `N₀ ∈ ℕ`. -/
theorem permanence_underflow_all_unlimited {X : Set ℕ*} (hX : IsInternalNat X)
    (hunl : ∀ ω : ℕ*, IsUnlimitedNat ω → ω ∈ X) :
    ∃ N₀ : ℕ, Set.Ici (N₀ : ℕ*) ⊆ X := by
  obtain ⟨N₀, hseg⟩ := underflow_nat hX isUnlimitedNat_omegaNat (fun H hH _ ↦ hunl H hH)
  refine ⟨N₀, fun N hN ↦ ?_⟩
  by_cases hN_unl : IsUnlimitedNat N
  · exact hunl N hN_unl
  · obtain ⟨n, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 hN_unl
    exact hseg (n : ℕ*) hN (isUnlimitedNat_omegaNat n).le

/-- Goldblatt §15.1, Theorem 15.1.1(3) (p. 192, **Halo Permanence**):
If an internal subset `X ⊆ ℝ*` contains every hyperreal infinitely close to `b ∈ ℝ*`, then `X`
contains every hyperreal within some positive standard distance `δ > 0` of `b`. -/
theorem permanence_halo {X : Set ℝ*} (hX : IsInternal X) {b : ℝ*}
    (hclose : ∀ a : ℝ*, a ≈ₕ b → a ∈ X) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ*, |a - b| < (δ : ℝ*) → a ∈ X := by
  have hhalo : halo b ⊆ X := fun a ha ↦ hclose a ha.symm
  obtain ⟨δ, hδ, hball⟩ := hX.exists_real_ball_subset_of_halo_subset hhalo
  exact ⟨δ, hδ, fun a ha ↦ hball ha⟩

/-- Goldblatt §15.1 (p. 192, **Positive Infinitesimal Underflow**):
If an internal subset `A ⊆ ℝ*` contains all positive infinitesimals, then `A` contains `Set.Ioo 0 r`
for some positive standard real `r > 0`. -/
theorem permanence_posInfinitesimal_underflow {A : Set ℝ*} (hA : IsInternal A)
    (hinf : ∀ ε : ℝ*, IsPosInfinitesimal ε → ε ∈ A) :
    ∃ r : ℝ, 0 < r ∧ Set.Ioo (0 : ℝ*) (r : ℝ*) ⊆ A := by
  let C : Set ℝ* := A ∪ Set.Iic 0
  have hC_int : IsInternal C := hA.union (isInternal_Iic 0)
  have hhalo : halo 0 ⊆ C := by
    intro x hx
    rw [halo_zero] at hx
    rcases isInfinitesimal_iff_trichotomy.1 hx with hpos | ⟨hneg, _⟩ | rfl
    · exact Or.inl (hinf x hpos)
    · exact Or.inr (Set.mem_Iic.2 hneg.le)
    · exact Or.inr (Set.mem_Iic.2 le_rfl)
  obtain ⟨r, hr_pos, hball⟩ := hC_int.exists_real_ball_subset_of_halo_subset hhalo
  refine ⟨r, hr_pos, fun x ⟨hx0, hxr⟩ ↦ ?_⟩
  have hx_ball : |x - 0| < (r : ℝ*) := by rwa [sub_zero, abs_of_pos hx0]
  rcases hball hx_ball with hxA | hxle0
  · exact hxA
  · exact (not_lt_of_ge hxle0 hx0).elim

/-- Goldblatt §15.1 (p. 192, **Positive Infinitesimal Overflow**):
If an internal subset `A ⊆ ℝ*` contains `(r : ℝ*)` for arbitrarily small positive standard reals
`r > 0` (in particular, if `(r : ℝ*) ∈ A` for every standard `r > 0`), then `A` contains a positive
infinitesimal! -/
theorem permanence_posInfinitesimal_overflow_of_arbitrarily_small {A : Set ℝ*} (hA : IsInternal A)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < δ ∧ (r : ℝ*) ∈ A) :
    ∃ ε ∈ A, IsPosInfinitesimal ε := by
  by_contra hno
  push Not at hno
  have hcompl : ∀ ε : ℝ*, IsPosInfinitesimal ε → ε ∈ Aᶜ := fun ε hε hεA ↦ hno ε hεA hε
  obtain ⟨δ, hδ_pos, hsub⟩ := permanence_posInfinitesimal_underflow hA.compl hcompl
  obtain ⟨r, hr0, hrδ, hrA⟩ := hsmall δ hδ_pos
  exact hsub ⟨Hyperreal.coe_pos.2 hr0, Hyperreal.coe_lt_coe.2 hrδ⟩ hrA

/-- Specialization of `permanence_posInfinitesimal_overflow_of_arbitrarily_small`: an internal set
`A ⊆ ℝ*` containing `(r : ℝ*)` for every standard real `r > 0` contains a positive infinitesimal. -/
theorem permanence_posInfinitesimal_overflow {A : Set ℝ*} (hA : IsInternal A)
    (hpos : ∀ r : ℝ, 0 < r → (r : ℝ*) ∈ A) :
    ∃ ε ∈ A, IsPosInfinitesimal ε :=
  permanence_posInfinitesimal_overflow_of_arbitrarily_small hA fun δ hδ ↦
    ⟨δ / 2, half_pos hδ, half_lt_self hδ, hpos (δ / 2) (half_pos hδ)⟩

/-- Goldblatt §15.1, Theorem 15.1.1(4a) (p. 192):
If an internal subset `X ⊆ ℝ*` contains arbitrarily large standard reals `a ∈ ℝ`, then `X` contains
some positive unlimited hyperreal `b ∈ ℝ*` (proved via internal order-completeness). -/
theorem permanence_posUnlimited_of_arbitrarily_large_real {X : Set ℝ*} (hX : IsInternal X)
    (hlarge : ∀ r : ℝ, ∃ a : ℝ, r ≤ a ∧ (a : ℝ*) ∈ X) :
    ∃ b ∈ X, IsPosUnlimited b := by
  refine hX.exists_posUnlimited_of_arbitrarily_large_limited fun n ↦ ?_
  obtain ⟨a, hna, haX⟩ := hlarge ((n : ℝ) + 1)
  have hlt : (n : ℝ*) < (a : ℝ*) := by
    have : (n : ℝ) < a := by linarith
    exact_mod_cast this
  exact ⟨(a : ℝ*), haX, isLimited_coe a, hlt⟩

/-- Goldblatt §15.1, Theorem 15.1.1(4b) (p. 192):
If an internal subset `X ⊆ ℝ*` contains arbitrarily small (negative) standard reals `a ∈ ℝ`, then
`X` contains some negative unlimited hyperreal `b ∈ ℝ*` (proved via internal order-completeness). -/
theorem permanence_negUnlimited_of_arbitrarily_small_real {X : Set ℝ*} (hX : IsInternal X)
    (hsmall : ∀ r : ℝ, ∃ a : ℝ, a ≤ r ∧ (a : ℝ*) ∈ X) :
    ∃ b ∈ X, IsNegUnlimited b := by
  rcases hX with ⟨A, rfl⟩
  let negX : Set ℝ* := internalSet (fun n ↦ (- ·) ⁻¹' (A n))
  have hneg_int : IsInternal negX := ⟨_, rfl⟩
  have hmem_neg : ∀ y : ℝ*, y ∈ negX ↔ -y ∈ internalSet A := by
    intro y; rcases ofSeq_surjective y with ⟨r, rfl⟩; exact Iff.rfl
  have hlarge : ∀ r : ℝ, ∃ a : ℝ, r ≤ a ∧ (a : ℝ*) ∈ negX := by
    intro r
    obtain ⟨a, har, haX⟩ := hsmall (-r)
    refine ⟨-a, by linarith, (hmem_neg _).2 ?_⟩
    simpa [Hyperreal.coe_neg] using haX
  obtain ⟨c, hc_mem, hc_pos⟩ := permanence_posUnlimited_of_arbitrarily_large_real hneg_int hlarge
  refine ⟨-c, (hmem_neg c).1 hc_mem, fun s ↦ ?_⟩
  have hs := hc_pos (-s)
  rw [Hyperreal.coe_neg] at hs
  linarith

/-- Goldblatt §15.1, Theorem 15.1.1(5) (p. 192, **Ray Overflow via Internal Order-Completeness**):
If `X ⊆ ℝ*` is internal and `r ∈ ℝ` is such that `a ∈ X` for all limited `a ∈ ℝ*` with `r ≤ a`
(equivalently `Set.Icc (r : ℝ*) (s : ℝ*) ⊆ X` for every `s ≥ r` in `ℝ`), then there exists a
positive unlimited `b ∈ ℝ*` such that `a ∈ X` for all `a ∈ ℝ*` with `r ≤ a ≤ b`. -/
theorem permanence_ray_overflow_limited {X : Set ℝ*} (hX : IsInternal X) {r : ℝ}
    (hlim : ∀ a : ℝ*, IsLimited a → (r : ℝ*) ≤ a → a ∈ X) :
    ∃ b : ℝ*, IsPosUnlimited b ∧ ∀ a : ℝ*, (r : ℝ*) ≤ a → a ≤ b → a ∈ X := by
  let Y : Set ℝ* := Set.Ici (r : ℝ*) \ X
  rcases Y.eq_empty_or_nonempty with hemp | hne
  · refine ⟨Hyperreal.omega, Hyperreal.coe_lt_omega, fun a hra _ ↦ ?_⟩
    by_contra haX
    have : a ∈ Y := ⟨hra, haX⟩
    exact (hemp ▸ this).elim
  · have hY_int : IsInternal Y := (isInternal_Ici _).sdiff hX
    have hY_bdd : BddBelow Y := ⟨(r : ℝ*), fun y hy ↦ hy.1⟩
    obtain ⟨c, hc⟩ := hY_int.exists_isGLB hne hY_bdd
    have hc_not_lim : ¬ IsLimited c := by
      intro hc_lim
      have hnot_lb : c + 1 ∉ lowerBounds Y := fun hlb ↦ by linarith [hc.2 hlb]
      obtain ⟨y, hyY, hy_lt⟩ : ∃ y ∈ Y, y < c + 1 := by
        unfold lowerBounds at hnot_lb
        rw [Set.mem_ofPred_eq] at hnot_lb
        push Not at hnot_lb
        exact hnot_lb
      have hy_lim : IsLimited y := by
        obtain ⟨B₁, _, hB₁⟩ := isLimited_iff_abs_le_real.1 (isLimited_coe r)
        obtain ⟨B₂, _, hB₂⟩ := isLimited_iff_abs_le_real.1 (hc_lim.add (isLimited_coe 1))
        refine isLimited_iff_abs_le_real.2 ⟨max B₁ B₂, le_trans (by positivity) (le_max_left _ _), ?_⟩
        rw [abs_le]
        constructor
        · have h1 : -((B₁ : ℝ*)) ≤ (r : ℝ*) := (abs_le.1 hB₁).1
          have h2 : -((max B₁ B₂ : ℝ) : ℝ*) ≤ -(B₁ : ℝ*) := by simp
          exact h2.trans (h1.trans hyY.1)
        · have h1 : c + 1 ≤ (B₂ : ℝ*) := (abs_le.1 hB₂).2
          have h2 : (B₂ : ℝ*) ≤ ((max B₁ B₂ : ℝ) : ℝ*) := by simp
          exact hy_lt.le.trans (h1.trans h2)
      exact hyY.2 (hlim y hy_lim hyY.1)
    have hc_pos : IsPosUnlimited c := by
      rcases isUnlimited_iff_pos_or_neg.1 (isUnlimited_iff_not_isLimited.2 hc_not_lim) with hp | hn
      · exact hp
      · exfalso
        have hrc : (r : ℝ*) ≤ c := hc.2 fun y hy ↦ hy.1
        exact not_lt_of_ge hrc (hn r)
    refine ⟨c - 1, fun s ↦ ?_, fun a hra hab ↦ ?_⟩
    · have hs := hc_pos (s + 1)
      rw [Hyperreal.coe_add, Hyperreal.coe_one] at hs
      linarith
    · by_contra haX
      have hca : c ≤ a := hc.1 ⟨hra, haX⟩
      linarith

/-- Goldblatt §15.1, Theorem 15.1.1(5) for standard formulas `P : Set ℝ`:
If `a ∈ P` for all standard `a ∈ ℝ` with `r ≤ a`, then `a ∈ starSet P` for all `a ∈ ℝ*` with
`r ≤ a ≤ b` for an unlimited `b ∈ ℝ*` (indeed for all `a ≥ r`). -/
theorem permanence_ray_overflow_starSet {P : Set ℝ} {r : ℝ}
    (hP : ∀ a : ℝ, r ≤ a → a ∈ P) :
    ∃ b : ℝ*, IsPosUnlimited b ∧ ∀ a : ℝ*, (r : ℝ*) ≤ a → a ≤ b → a ∈ starSet P := by
  refine ⟨Hyperreal.omega, Hyperreal.coe_lt_omega, fun a hra _ ↦ ?_⟩
  rcases ofSeq_surjective a with ⟨sa, rfl⟩
  exact ofSeq_mem_starSet.2 ((ofSeq_le_ofSeq.1 hra).mono fun n hn ↦ hP (sa n) hn)

/-- Explicit counterexample showing why internal formulas with nonstandard parameters in
Theorem 15.1.1(5) require `IsLimited a`: `X = ({Hyperreal.epsilon})ᶜ` is internal and contains
`(a : ℝ*)` for every standard `a ≥ 0`, yet `0 ≤ ε ≤ b` and `ε ∉ X` for every positive unlimited `b`. -/
theorem counterexample_ray_overflow_standard_only :
    ∃ X : Set ℝ*, IsInternal X ∧ (∀ a : ℝ, 0 ≤ a → (a : ℝ*) ∈ X) ∧
      ¬ ∃ b : ℝ*, IsPosUnlimited b ∧ ∀ a : ℝ*, (0 : ℝ*) ≤ a → a ≤ b → a ∈ X := by
  refine ⟨({Hyperreal.epsilon} : Set ℝ*)ᶜ, (isInternal_singleton _).compl, ?_, ?_⟩
  · intro a _ ha
    rw [Set.mem_singleton_iff] at ha
    have hne : a ≠ 0 := by
      intro h0; subst h0
      exact Hyperreal.epsilon_pos.ne ha
    exact (isInfinitesimal_coe_iff.not.2 hne) (ha ▸ isInfinitesimal_epsilon)
  · rintro ⟨b, hb_pos, hseg⟩
    have hεb : Hyperreal.epsilon ≤ b :=
      (Hyperreal.epsilon_lt_of_pos one_pos).le.trans (hb_pos 1).le
    have hmem := hseg Hyperreal.epsilon Hyperreal.epsilon_pos.le hεb
    exact hmem rfl

/-- Goldblatt §15.1, Exercise 15.1.2 (p. 192, `InternalPartialFun` formulation on `ℝ*`):
Let `F` be an internal `*ℝ`-valued function such that `F(x)` is limited for all `x` in an internal
set `A ⊆ F.dom`. Then there exists a standard `n ∈ ℕ` such that `|F(x)| < n` for all `x ∈ A`. -/
theorem exists_nat_bound_of_limited_on_internal {F : InternalPartialFun} (hF : IsInternalFun F)
    {A : Set ℝ*} (hA : IsInternal A) (hlim : ∀ x ∈ A, IsLimited (F.apply x)) :
    ∃ n : ℕ, ∀ x ∈ A, |F.apply x| < (n : ℝ*) := by
  have himg_int : IsInternal (F.apply '' A) := hF.image hA
  have himg_lim : ∀ y ∈ F.apply '' A, IsLimited y := by
    rintro _ ⟨x, hxA, rfl⟩
    exact hlim x hxA
  obtain ⟨r, _, hsub⟩ := himg_int.subset_Icc_real_of_forall_isLimited himg_lim
  obtain ⟨n, hn⟩ := exists_nat_gt r
  refine ⟨n, fun x hxA ↦ ?_⟩
  obtain ⟨hl, hu⟩ := hsub ⟨x, hxA, rfl⟩
  have hle : |F.apply x| ≤ (r : ℝ*) := abs_le.2 ⟨hl, hu⟩
  exact hle.trans_lt (by exact_mod_cast hn)

/-- Internal subset `[A_i] ⊆ Germ (U : Filter ι) α` of a general ultrapower over an ultrafilter `U`. -/
def internalGermSet {ι α : Type*} (U : Ultrafilter ι) (A : ι → Set α) :
    Set (Germ (U : Filter ι) α) :=
  {x : Germ (U : Filter ι) α | Germ.LiftRel (· ∈ ·) x (A : Germ (U : Filter ι) (Set α))}

/-- Predicate asserting that `X ⊆ Germ (U : Filter ι) α` is internal. -/
def IsInternalGermSet {ι α : Type*} (U : Ultrafilter ι) (X : Set (Germ (U : Filter ι) α)) : Prop :=
  ∃ A : ι → Set α, X = internalGermSet U A

/-- Membership characterization for `internalGermSet`. -/
@[simp]
theorem coe_mem_internalGermSet {ι α : Type*} {U : Ultrafilter ι} {a : ι → α} {A : ι → Set α} :
    (a : Germ (U : Filter ι) α) ∈ internalGermSet U A ↔ ∀ᶠ i in (U : Filter ι), a i ∈ A i :=
  Germ.liftRel_coe

/-- Internal function `Germ (U : Filter ι) α → Germ (U : Filter ι) β` lifted from `f : ι → α → β`. -/
def internalGermFun {ι α β : Type*} (U : Ultrafilter ι) (f : ι → α → β)
    (x : Germ (U : Filter ι) α) : Germ (U : Filter ι) β :=
  Germ.map₂ (fun g a ↦ g a) (f : Germ (U : Filter ι) (α → β)) x

/-- Evaluation of `internalGermFun` on a representative `a : ι → α`. -/
@[simp]
theorem internalGermFun_coe {ι α β : Type*} (U : Ultrafilter ι) (f : ι → α → β) (a : ι → α) :
    internalGermFun U f (a : Germ (U : Filter ι) α) = ((fun i ↦ f i (a i)) : Germ (U : Filter ι) β) :=
  rfl

/-- Goldblatt §15.1, Exercise 15.1.2 (p. 192, general internal entity domain `Germ (hyperfilter ℕ) α`):
If `f` is an internal `*ℝ`-valued function on an arbitrary ultrapower sort `Germ (hyperfilter ℕ) α`
and `f(x)` is limited for every `x` in an internal set `A`, then there exists a standard `n ∈ ℕ`
such that `|f(x)| < n` for all `x ∈ A`. -/
theorem exists_nat_bound_of_limited_internalGermFun {α : Type*}
    (f : ℕ → α → ℝ) {A : Set (Germ (hyperfilter ℕ : Filter ℕ) α)}
    (hA : IsInternalGermSet (hyperfilter ℕ) A)
    (hlim : ∀ x ∈ A, IsLimited (internalGermFun (hyperfilter ℕ) f x)) :
    ∃ n : ℕ, ∀ x ∈ A, |internalGermFun (hyperfilter ℕ) f x| < (n : ℝ*) := by
  rcases hA with ⟨B, rfl⟩
  let Y : Set ℝ* := internalSet (fun i ↦ f i '' B i)
  have hY_int : IsInternal Y := ⟨_, rfl⟩
  have hY_lim : ∀ y ∈ Y, IsLimited y := by
    intro y hy
    rcases ofSeq_surjective y with ⟨r, rfl⟩
    have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), ∃ a ∈ B i, f i a = r i :=
      ofSeq_mem_internalSet.1 hy
    rcases Classical.em (Nonempty α) with hNe | hEmpty
    · obtain ⟨a₀⟩ := hNe
      let aSeq : ℕ → α := fun i ↦
        if h : ∃ a ∈ B i, f i a = r i then h.choose else a₀
      have ha_mem : (aSeq : Germ (hyperfilter ℕ : Filter ℕ) α) ∈ internalGermSet (hyperfilter ℕ) B := by
        refine coe_mem_internalGermSet.2 (hev.mono fun i hi ↦ ?_)
        simpa only [aSeq, hi, ↓reduceDIte] using hi.choose_spec.1
      have hfa_eq : internalGermFun (hyperfilter ℕ) f (aSeq : Germ (hyperfilter ℕ : Filter ℕ) α) =
          ofSeq r := by
        refine Germ.coe_eq.2 (hev.mono fun i hi ↦ ?_)
        simpa only [aSeq, hi, ↓reduceDIte] using hi.choose_spec.2
      exact hfa_eq ▸ hlim _ ha_mem
    · exfalso
      obtain ⟨i, a, _, _⟩ := hev.exists
      exact hEmpty ⟨a⟩
  obtain ⟨c, _, hsub⟩ := hY_int.subset_Icc_real_of_forall_isLimited hY_lim
  obtain ⟨n, hn⟩ := exists_nat_gt c
  refine ⟨n, fun x hx ↦ ?_⟩
  induction x using Germ.inductionOn with | _ a =>
  have haB : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), a i ∈ B i := coe_mem_internalGermSet.1 hx
  have hfxY : internalGermFun (hyperfilter ℕ) f (a : Germ (hyperfilter ℕ : Filter ℕ) α) ∈ Y :=
    ofSeq_mem_internalSet.2 (haB.mono fun i hi ↦ ⟨a i, hi, rfl⟩)
  obtain ⟨hl, hu⟩ := hsub hfxY
  exact (abs_le.2 ⟨hl, hu⟩).trans_lt (by exact_mod_cast hn)

/-! ## §15.2 Robinson's Sequential Lemma -/

/-- Goldblatt §15.2 (p. 193): An internal hypersequence `s : ℕ* → ℝ*` represented by a sequence of
real sequences `σ : ℕ → ℕ → ℝ` via `s([a_i]) = [σ_i(a_i)]`. -/
def internalSeq (σ : ℕ → ℕ → ℝ) : ℕ* → ℝ* :=
  internalGermFun (hyperfilter ℕ) σ

/-- Evaluation of `internalSeq σ` on `(a : ℕ*)`. -/
@[simp]
theorem internalSeq_coe (σ : ℕ → ℕ → ℝ) (a : ℕ → ℕ) :
    internalSeq σ (a : ℕ*) = ofSeq (fun i ↦ σ i (a i)) := rfl

/-- Evaluation of `internalSeq σ` on a standard `(n : ℕ*)`. -/
@[simp]
theorem internalSeq_natCast (σ : ℕ → ℕ → ℝ) (n : ℕ) :
    internalSeq σ (n : ℕ*) = ofSeq (fun i ↦ σ i n) := rfl

/-- Predicate asserting that `s : ℕ* → ℝ*` is an internal hypersequence. -/
def IsInternalSeq (s : ℕ* → ℝ*) : Prop :=
  ∃ σ : ℕ → ℕ → ℝ, s = internalSeq σ

/-- Every standard sequence `u : ℕ → ℝ` extends to an internal hypersequence `starSeq u`. -/
theorem isInternalSeq_starSeq (u : ℕ → ℝ) : IsInternalSeq (starSeq u) :=
  ⟨fun _ ↦ u, rfl⟩

/-- Constant hypersequences `fun _ ↦ c` (`c ∈ ℝ*`) are internal. -/
theorem isInternalSeq_const (c : ℝ*) : IsInternalSeq (fun _ : ℕ* ↦ c) := by
  rcases ofSeq_surjective c with ⟨sc, rfl⟩
  refine ⟨fun i _ ↦ sc i, ?_⟩
  ext N; induction N using Germ.inductionOn with | _ _ => rfl

/-- Pointwise sum of internal hypersequences is internal. -/
theorem IsInternalSeq.add {s t : ℕ* → ℝ*} (hs : IsInternalSeq s) (ht : IsInternalSeq t) :
    IsInternalSeq (fun N ↦ s N + t N) := by
  rcases hs with ⟨σ, rfl⟩; rcases ht with ⟨τ, rfl⟩
  refine ⟨fun i m ↦ σ i m + τ i m, ?_⟩
  ext N; induction N using Germ.inductionOn with | _ _ => rfl

/-- Pointwise difference of internal hypersequences is internal. -/
theorem IsInternalSeq.sub {s t : ℕ* → ℝ*} (hs : IsInternalSeq s) (ht : IsInternalSeq t) :
    IsInternalSeq (fun N ↦ s N - t N) := by
  rcases hs with ⟨σ, rfl⟩; rcases ht with ⟨τ, rfl⟩
  refine ⟨fun i m ↦ σ i m - τ i m, ?_⟩
  ext N; induction N using Germ.inductionOn with | _ _ => rfl

/-- Pointwise product of internal hypersequences is internal. -/
theorem IsInternalSeq.mul {s t : ℕ* → ℝ*} (hs : IsInternalSeq s) (ht : IsInternalSeq t) :
    IsInternalSeq (fun N ↦ s N * t N) := by
  rcases hs with ⟨σ, rfl⟩; rcases ht with ⟨τ, rfl⟩
  refine ⟨fun i m ↦ σ i m * τ i m, ?_⟩
  ext N; induction N using Germ.inductionOn with | _ _ => rfl

/-- Pointwise absolute value of an internal hypersequence is internal. -/
theorem IsInternalSeq.abs {s : ℕ* → ℝ*} (hs : IsInternalSeq s) :
    IsInternalSeq (fun N ↦ |s N|) := by
  rcases hs with ⟨σ, rfl⟩
  refine ⟨fun i m ↦ |σ i m|, ?_⟩
  ext N; induction N using Germ.inductionOn with | _ _ => rfl

/-- Pointwise reciprocal of an internal hypersequence is internal. -/
theorem IsInternalSeq.inv {s : ℕ* → ℝ*} (hs : IsInternalSeq s) :
    IsInternalSeq (fun N ↦ (s N)⁻¹) := by
  rcases hs with ⟨σ, rfl⟩
  refine ⟨fun i m ↦ (σ i m)⁻¹, ?_⟩
  ext N; induction N using Germ.inductionOn with | _ _ => rfl

/-- Exact correspondence between `IsInternalSeq s` and `InternalPartialFun` with domain `*ℕ`. -/
theorem isInternalSeq_iff_exists_internalFun {s : ℕ* → ℝ*} :
    IsInternalSeq s ↔
      ∃ F : InternalPartialFun, IsInternalFun F ∧
        F.dom = Set.range Hypernat.toHyperreal ∧
        ∀ N : ℕ*, F.apply (Hypernat.toHyperreal N) = s N := by
  constructor
  · rintro ⟨σ, rfl⟩
    let p : ℕ → RealPartialFun := fun i ↦
      RealPartialFun.mkPartial (Set.range (Nat.cast : ℕ → ℝ))
        (fun r ↦ if h : ∃ m : ℕ, (m : ℝ) = r then σ i h.choose else 0)
    refine ⟨internalFun p, isInternalFun_internalFun p, ?_, fun N ↦ ?_⟩
    · rw [internalFun_dom]
      dsimp only [p, RealPartialFun.mkPartial_dom]
      rw [internalSet_const, range_hypernat_toHyperreal]
    · induction N using Germ.inductionOn with | _ a =>
      refine Germ.coe_eq.2 (Eventually.of_forall fun i ↦ ?_)
      have hmem : ((a i : ℕ) : ℝ) ∈ Set.range (Nat.cast : ℕ → ℝ) := ⟨a i, rfl⟩
      dsimp only [p, Function.comp_apply]
      rw [RealPartialFun.mkPartial_apply_of_mem hmem]
      have hex : ∃ m : ℕ, (m : ℝ) = (a i : ℝ) := ⟨a i, rfl⟩
      have hcho : hex.choose = a i := Nat.cast_injective hex.choose_spec
      simp only [hex, ↓reduceDIte, hcho]
  · rintro ⟨F, ⟨p, rfl⟩, _, hval⟩
    refine ⟨fun i m ↦ (p i).apply (m : ℝ), ?_⟩
    ext N
    rw [← hval N]
    induction N using Germ.inductionOn with | _ a => rfl

/-- Goldblatt §15.2 (p. 193, Externality Remark):
For the internal hypersequence `s(N) = N / ω`, `s(n) ≈ₕ 0` for all `n ∈ ℕ`, yet the set
`{N ∈ ℕ* | s(N) ≈ₕ 0}` is **external**, explaining why Overflow cannot be applied directly to
`{N ∈ ℕ* | s(N) ≈ₕ 0}`! -/
theorem isExternalNat_infinitesimal_locus :
    let s : ℕ* → ℝ* := fun N ↦ Hypernat.toHyperreal N / Hyperreal.omega
    IsInternalSeq s ∧
      (∀ n : ℕ, s (n : ℕ*) ≈ₕ 0) ∧
      IsExternalNat {N : ℕ* | s N ≈ₕ 0} := by
  intro s
  have hs_int : IsInternalSeq s := by
    refine ⟨fun i m ↦ (m : ℝ) / (i : ℝ), ?_⟩
    ext N; induction N using Germ.inductionOn with | _ _ => rfl
  have hs_std : ∀ n : ℕ, s (n : ℕ*) ≈ₕ 0 := by
    intro n
    rw [infClose_zero_iff]
    have heq : s (n : ℕ*) = (n : ℝ*) * (Hyperreal.omega)⁻¹ := div_eq_mul_inv _ _
    rw [heq]
    exact (isLimited_coe n).mul_isInfinitesimal isUnlimited_omega.inv_isInfinitesimal
  refine ⟨hs_int, hs_std, fun hInt ↦ ?_⟩
  have hω_not : omegaNat ∉ {N : ℕ* | s N ≈ₕ 0} := by
    intro hmem
    have hsω : s omegaNat = 1 := by
      dsimp [s]
      have hpos : (0 : ℝ*) < Hyperreal.omega := Hyperreal.coe_lt_omega 0
      exact div_self hpos.ne'
    have h10 : (1 : ℝ*) ≈ₕ (0 : ℝ*) := hsω ▸ hmem
    have := coe_eq_of_infClose (b := 1) (c := 0) (by simpa using h10)
    norm_num at this
  obtain ⟨M, hM_not, hM_min⟩ := hInt.compl.exists_least ⟨omegaNat, hω_not⟩
  have hM_unl : IsUnlimitedNat M := by
    by_contra hlim
    obtain ⟨n, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 hlim
    exact hM_not (hs_std n)
  induction M using Germ.inductionOn with | _ a =>
  let K : ℕ* := ((fun i ↦ a i / 2) : ℕ*)
  have hKM : K < (a : ℕ*) := by
    have hgt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 1 < a i := Germ.coe_lt.1 (hM_unl 1)
    exact Germ.coe_lt.2 (hgt.mono fun i hi ↦ by change a i / 2 < a i; omega)
  have hK_in : s K ≈ₕ 0 := by
    by_contra hKnot
    exact not_le_of_gt hKM (hM_min K hKnot)
  have hM_le_2K1 : (a : ℕ*) ≤ 2 * K + 1 :=
    Germ.coe_le.2 (Eventually.of_forall fun i ↦ by change a i ≤ 2 * (a i / 2) + 1; omega)
  have hsM_le : s (a : ℕ*) ≤ 2 * s K + (Hyperreal.omega)⁻¹ := by
    have hω_pos : (0 : ℝ*) < Hyperreal.omega := Hyperreal.coe_lt_omega 0
    have hle_real : Hypernat.toHyperreal (a : ℕ*) ≤ 2 * Hypernat.toHyperreal K + 1 := by
      have := Hypernat.toHyperreal_le_iff.2 hM_le_2K1
      rw [Hypernat.toHyperreal_add, Hypernat.toHyperreal_mul] at this
      have h2 : Hypernat.toHyperreal 2 = 2 :=
        Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ by norm_num)
      have h1 : Hypernat.toHyperreal 1 = 1 :=
        Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ by norm_num)
      rwa [h2, h1] at this
    dsimp [s]
    calc Hypernat.toHyperreal (a : ℕ*) / Hyperreal.omega
        ≤ (2 * Hypernat.toHyperreal K + 1) / Hyperreal.omega :=
          div_le_div_of_nonneg_right hle_real hω_pos.le
      _ = 2 * (Hypernat.toHyperreal K / Hyperreal.omega) + (Hyperreal.omega)⁻¹ := by
          rw [add_div, mul_div_assoc, one_div]
  have hsM_nn : 0 ≤ s (a : ℕ*) := by
    dsimp [s]
    exact div_nonneg (hypernat_nonneg _) (Hyperreal.coe_lt_omega 0).le
  have hrhs_inf : IsInfinitesimal (2 * s K + (Hyperreal.omega)⁻¹) :=
    ((isLimited_coe 2).mul_isInfinitesimal (infClose_zero_iff.1 hK_in)).add
      isUnlimited_omega.inv_isInfinitesimal
  have hsM_inf : IsInfinitesimal (s (a : ℕ*)) := by
    refine isInfinitesimal_of_abs_le hrhs_inf ?_
    rw [abs_of_nonneg hsM_nn]
    exact hsM_le.trans (le_abs_self _)
  exact hM_not (infClose_zero_iff.2 hsM_inf)

/-- Goldblatt §15.2 (p. 193): Internality of `{N ∈ ℕ* | ∀ k ≤ N, |s k| < 1 / (k + 1)}`, demonstrating
the bounded-quantifier internal replacement for `{N ∈ ℕ* | s N ≈ₕ 0}`. -/
theorem isInternalNat_forall_le_bound {s : ℕ* → ℝ*} (hs : IsInternalSeq s) :
    IsInternalNat {N : ℕ* | ∀ k : ℕ*, k ≤ N →
      |s k| < (Hypernat.toHyperreal k + 1)⁻¹} := by
  rcases hs with ⟨σ, rfl⟩
  refine ⟨fun i ↦ {m : ℕ | ∀ k ≤ m, |σ i k| < ((k : ℝ) + 1)⁻¹}, ?_⟩
  ext N
  induction N using Germ.inductionOn with | _ a =>
  rw [Set.mem_ofPred_eq, coe_mem_internalNatSet]
  constructor
  · intro h
    by_contra hnot
    have hbad : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
        ∃ k ≤ a i, ((k : ℝ) + 1)⁻¹ ≤ |σ i k| := by
      refine (Ultrafilter.eventually_not.2 hnot).mono fun i hi ↦ ?_
      change ¬ ∀ k ≤ a i, |σ i k| < ((k : ℝ) + 1)⁻¹ at hi
      push Not at hi
      exact hi
    let kSeq : ℕ → ℕ := fun i ↦
      if h : ∃ k ≤ a i, ((k : ℝ) + 1)⁻¹ ≤ |σ i k| then h.choose else 0
    have hk_le : (kSeq : ℕ*) ≤ (a : ℕ*) :=
      Germ.coe_le.2 (hbad.mono fun i hi ↦ by simpa only [kSeq, hi, ↓reduceDIte] using hi.choose_spec.1)
    have hlt := ofSeq_lt_ofSeq.1 (h (kSeq : ℕ*) hk_le)
    obtain ⟨i, hi1, hi2⟩ := (hbad.and hlt).exists
    have hge : (((kSeq i : ℝ) + 1))⁻¹ ≤ |σ i (kSeq i)| := by
      simpa only [kSeq, hi1, ↓reduceDIte] using hi1.choose_spec.2
    exact not_lt_of_ge hge hi2
  · intro hev k hk
    induction k using Germ.inductionOn with | _ b =>
    have hba := Germ.coe_le.1 hk
    exact ofSeq_lt_ofSeq.2 ((hev.and hba).mono fun i ⟨hi, hle⟩ ↦ hi (b i) hle)

/-- Goldblatt §15.2, Lemma 15.2.1 (p. 193, **Robinson's Sequential Lemma**):
If `s : ℕ* → ℝ*` is an internal hypersequence such that `s(n)` is infinitesimal for every standard
`n ∈ ℕ`, then there exists an unlimited `K ∈ ℕ*` such that `s(N)` is infinitesimal for all
hypernatural `N ≤ K`. -/
theorem robinson_sequential_lemma {s : ℕ* → ℝ*} (hs : IsInternalSeq s)
    (hstd : ∀ n : ℕ, IsInfinitesimal (s (n : ℕ*))) :
    ∃ K : ℕ*, IsUnlimitedNat K ∧ ∀ N : ℕ*, N ≤ K → IsInfinitesimal (s N) := by
  -- Following Goldblatt p. 193: apply Overflow to `{N ∈ ℕ* | |N * s(N)| < 1}`!
  rcases hs with ⟨σ, rfl⟩
  let X : Set ℕ* := internalNatSet (fun i ↦ {m : ℕ | |(m : ℝ) * σ i m| < 1})
  have hX_int : IsInternalNat X := ⟨_, rfl⟩
  have hX_mem_iff : ∀ N : ℕ*, N ∈ X ↔ |Hypernat.toHyperreal N * internalSeq σ N| < 1 := by
    intro N; induction N using Germ.inductionOn with | _ a =>
    rw [coe_mem_internalNatSet]
    exact ofSeq_lt_ofSeq.symm
  have hX_fin : ∀ n : ℕ, 0 ≤ n → (n : ℕ*) ∈ X := by
    intro n _
    rw [hX_mem_iff, Hypernat.toHyperreal_natCast]
    have hinf : IsInfinitesimal ((n : ℝ*) * internalSeq σ (n : ℕ*)) :=
      (isLimited_coe n).mul_isInfinitesimal (hstd n)
    simpa using hinf 1 one_pos
  obtain ⟨K, hK_unl, hseg⟩ := overflow_nat hX_int hX_fin
  refine ⟨K, hK_unl, fun N hNK ↦ ?_⟩
  by_cases hN_unl : IsUnlimitedNat N
  · have hN_in : |Hypernat.toHyperreal N * internalSeq σ N| < 1 :=
      (hX_mem_iff N).1 (hseg N (Germ.inductionOn N fun _ ↦ Germ.coe_le.2 (Eventually.of_forall fun _ ↦ Nat.zero_le _)) hNK)
    have hN_pos_unl : IsPosUnlimited (Hypernat.toHyperreal N) :=
      isUnlimitedNat_iff_isPosUnlimited.1 hN_unl
    have hN_pos : (0 : ℝ*) < Hypernat.toHyperreal N := by simpa using hN_pos_unl 0
    have hlt_inv : |internalSeq σ N| < (Hypernat.toHyperreal N)⁻¹ := by
      rw [abs_mul, abs_of_pos hN_pos] at hN_in
      rw [← one_div]
      exact (lt_div_iff₀' hN_pos).2 hN_in
    have hinv_inf : IsInfinitesimal (Hypernat.toHyperreal N)⁻¹ :=
      (isUnlimited_iff_pos_or_neg.2 (Or.inl hN_pos_unl)).inv_isInfinitesimal
    exact isInfinitesimal_of_abs_le hinv_inf (hlt_inv.le.trans (le_abs_self _))
  · obtain ⟨n, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 hN_unl
    exact hstd n

/-- Alternative proof of Robinson's Sequential Lemma via `{N ∈ ℕ* | ∀ k ≤ N, |s k| < 1 / (k + 1)}`,
yielding an unlimited `ω ∈ ℕ*` such that `∀ N ≤ ω, |s N| < (N + 1)⁻¹` and hence `s N ≈ₕ 0`. -/
theorem robinson_sequential_lemma_forall_le_trick {s : ℕ* → ℝ*} (hs : IsInternalSeq s)
    (hstd : ∀ n : ℕ, s (n : ℕ*) ≈ₕ 0) :
    ∃ ω : ℕ*, IsUnlimitedNat ω ∧
      (∀ N : ℕ*, N ≤ ω → |s N| < (Hypernat.toHyperreal N + 1)⁻¹) ∧
      (∀ N : ℕ*, N ≤ ω → s N ≈ₕ 0) := by
  let X : Set ℕ* := {N : ℕ* | ∀ k : ℕ*, k ≤ N → |s k| < (Hypernat.toHyperreal k + 1)⁻¹}
  have hX_int : IsInternalNat X := isInternalNat_forall_le_bound hs
  have hX_fin : ∀ n : ℕ, 0 ≤ n → (n : ℕ*) ∈ X := by
    intro n _ k hk
    have hk_std : ¬ IsUnlimitedNat k := fun hku ↦ not_lt_of_ge hk (hku n)
    obtain ⟨m, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 hk_std
    have hm_inf : IsInfinitesimal (s (m : ℕ*)) := infClose_zero_iff.1 (hstd m)
    have hpos : (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := by positivity
    have hlt := hm_inf (((m : ℝ) + 1)⁻¹) hpos
    simpa [Hypernat.toHyperreal_natCast] using hlt
  obtain ⟨ω, hω_unl, hseg⟩ := overflow_nat hX_int hX_fin
  have hωX : ω ∈ X := hseg ω (Germ.inductionOn ω fun _ ↦ Germ.coe_le.2 (Eventually.of_forall fun _ ↦ Nat.zero_le _)) le_rfl
  refine ⟨ω, hω_unl, hωX, fun N hNω ↦ infClose_zero_iff.2 ?_⟩
  by_cases hN_unl : IsUnlimitedNat N
  · have hbd := hωX N hNω
    have hNp1_pos_unl : IsPosUnlimited (Hypernat.toHyperreal N + 1) := by
      intro r
      have := (isUnlimitedNat_iff_isPosUnlimited.1 hN_unl) r
      linarith
    have hinv_inf : IsInfinitesimal (Hypernat.toHyperreal N + 1)⁻¹ :=
      (isUnlimited_iff_pos_or_neg.2 (Or.inl hNp1_pos_unl)).inv_isInfinitesimal
    exact isInfinitesimal_of_abs_le hinv_inf (hbd.le.trans (le_abs_self _))
  · obtain ⟨n, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 hN_unl
    exact infClose_zero_iff.1 (hstd n)

/-- Goldblatt §15.2, Exercise 15.2.2 (p. 193):
If `c ∈ ℝ*` and `s : ℕ* → ℝ*` is an internal hypersequence such that `s(n) ≈ₕ c` for all standard
`n ∈ ℕ`, then there exists an unlimited `K ∈ ℕ*` such that `s(N) ≈ₕ c` for all hypernatural `N ≤ K`. -/
theorem robinson_sequential_infClose {s : ℕ* → ℝ*} (hs : IsInternalSeq s) {c : ℝ*}
    (hstd : ∀ n : ℕ, s (n : ℕ*) ≈ₕ c) :
    ∃ K : ℕ*, IsUnlimitedNat K ∧ ∀ N : ℕ*, N ≤ K → s N ≈ₕ c := by
  obtain ⟨K, hK_unl, hK⟩ := robinson_sequential_lemma (hs.sub (isInternalSeq_const c))
    (fun n ↦ hstd n)
  exact ⟨K, hK_unl, hK⟩

/-- Strict `< ω` variant of Exercise 15.2.2: if `s` is internal and `∀ n : ℕ, s(n) ≈ₕ c`, then there
exists an unlimited `ω ∈ ℕ*` such that `∀ N < ω, s(N) ≈ₕ c`. -/
theorem robinson_sequential_infClose_lt {s : ℕ* → ℝ*} (hs : IsInternalSeq s) {c : ℝ*}
    (hstd : ∀ n : ℕ, s (n : ℕ*) ≈ₕ c) :
    ∃ ω : ℕ*, IsUnlimitedNat ω ∧ ∀ N : ℕ*, N < ω → s N ≈ₕ c := by
  obtain ⟨K, hK_unl, hK⟩ := robinson_sequential_infClose hs hstd
  exact ⟨K, hK_unl, fun N hN ↦ hK N hN.le⟩

/-- Goldblatt §15.2 & Exercise 15.2.2 (p. 193, bounded hypersequence `{n ∈ ℕ* | n ≤ M} → ℝ*`):
Let `M ∈ ℕ*` be unlimited, and let `F : InternalPartialFun` be an internal function whose domain
includes `Hypernat.toHyperreal '' Set.Iic M` such that `F(n) ≈ₕ c` for every standard `n ∈ ℕ`.
Then there exists an unlimited `K ≤ M` in `ℕ*` such that `F(N) ≈ₕ c` for all `N ≤ K`. -/
theorem robinson_sequential_infClose_bounded {F : InternalPartialFun} (hF : IsInternalFun F)
    {M : ℕ*} (hM : IsUnlimitedNat M) {c : ℝ*}
    (hdom : Hypernat.toHyperreal '' Set.Iic M ⊆ F.dom)
    (hstd : ∀ n : ℕ, F.apply (n : ℝ*) ≈ₕ c) :
    ∃ K : ℕ*, IsUnlimitedNat K ∧ K ≤ M ∧
      ∀ N : ℕ*, N ≤ K → F.apply (Hypernat.toHyperreal N) ≈ₕ c := by
  rcases hF with ⟨p, rfl⟩
  let s : ℕ* → ℝ* := internalSeq (fun i m ↦ (p i).apply (m : ℝ))
  have hs_int : IsInternalSeq s := ⟨_, rfl⟩
  have hs_std : ∀ n : ℕ, s (n : ℕ*) ≈ₕ c := fun n ↦ hstd n
  obtain ⟨K₀, hK₀_unl, hK₀⟩ := robinson_sequential_infClose hs_int hs_std
  refine ⟨min K₀ M, fun n ↦ lt_min (hK₀_unl n) (hM n), min_le_right K₀ M, fun N hN ↦ ?_⟩
  have hNK₀ : N ≤ K₀ := hN.trans (min_le_left K₀ M)
  have heq : (internalFun p).apply (Hypernat.toHyperreal N) = s N := by
    induction N using Germ.inductionOn with | _ _ => rfl
  rw [heq]
  exact hK₀ N hNK₀

/-- `InternalPartialFun` formulation of Robinson's Sequential Lemma on `*ℕ`: if `F` is internal with
`*ℕ ⊆ F.dom` and `∀ n : ℕ, F(n) ≈ₕ c`, then `∃ K : ℕ*, IsUnlimitedNat K ∧ ∀ N ≤ K, F(N) ≈ₕ c`. -/
theorem robinson_sequential_lemma_internalFun {F : InternalPartialFun} (hF : IsInternalFun F)
    {c : ℝ*} (hdom : Set.range Hypernat.toHyperreal ⊆ F.dom)
    (hstd : ∀ n : ℕ, F.apply (n : ℝ*) ≈ₕ c) :
    ∃ K : ℕ*, IsUnlimitedNat K ∧ ∀ N : ℕ*, N ≤ K → F.apply (Hypernat.toHyperreal N) ≈ₕ c := by
  obtain ⟨K, hK_unl, _, hK⟩ := robinson_sequential_infClose_bounded hF isUnlimitedNat_omegaNat
    (fun _ ⟨N, _, hNx⟩ ↦ hdom ⟨N, hNx⟩) hstd
  exact ⟨K, hK_unl, hK⟩

/-- Application of Robinson's Sequential Lemma to Double Sequences (Diagonal Extraction):
If `a : ℕ → ℕ → ℝ` satisfies `lim_{n → ∞} a m n = b m` for each `m : ℕ` and `lim_{m → ∞} b m = L`,
then for any unlimited `H ∈ ℕ*`, Robinson's Sequential Lemma yields an unlimited `K ∈ ℕ*` such that
`([i ↦ a (m_i) (H_i)]) ≈ₕ (L : ℝ*)` for every unlimited `M ≤ K`; and in `ℝ`, there is a strictly
increasing index sequence `n_seq : ℕ → ℕ` such that `lim_{m → ∞} a m (n_seq m) = L`. -/
theorem robinson_double_limit_diagonal {a : ℕ → ℕ → ℝ} {b : ℕ → ℝ} {L : ℝ}
    (ha : ∀ m : ℕ, Tendsto (a m) atTop (𝓝 (b m)))
    (hb : Tendsto b atTop (𝓝 L)) :
    (∀ H : ℕ*, IsUnlimitedNat H →
      ∃ K : ℕ*, IsUnlimitedNat K ∧
        ∀ M : ℕ*, IsUnlimitedNat M → M ≤ K →
          Germ.map₂ (fun m n ↦ a m n) M H ≈ₕ (L : ℝ*)) ∧
    (∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ Tendsto (fun m ↦ a m (nSeq m)) atTop (𝓝 L)) := by
  constructor
  · intro H hH
    induction H using Germ.inductionOn with | _ hSeq =>
    -- Define the internal hypersequence `s(M) = (*a)(M, H) - (*b)(M)`.
    let s : ℕ* → ℝ* := internalSeq (fun i m ↦ a m (hSeq i) - b m)
    have hs_int : IsInternalSeq s := ⟨_, rfl⟩
    have hs_std : ∀ m : ℕ, IsInfinitesimal (s (m : ℕ*)) := by
      intro m r hr
      have hev_top : ∀ᶠ n in atTop, |a m n - b m| < r := by
        have ht := (ha m).sub_const (b m)
        rw [sub_self] at ht
        exact ht.abs.eventually (Iio_mem_nhds (by simpa using hr))
      obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev_top
      have hH_gt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), N₀ < hSeq i := Germ.coe_lt.1 (hH N₀)
      exact ofSeq_lt_ofSeq.2 (hH_gt.mono fun i hi ↦ hN₀ (hSeq i) hi.le)
    obtain ⟨K, hK_unl, hK_inf⟩ := robinson_sequential_lemma hs_int hs_std
    refine ⟨K, hK_unl, fun M hM_unl hMK ↦ ?_⟩
    have hsM : Germ.map₂ (fun m n ↦ a m n) M (hSeq : ℕ*) ≈ₕ starSeq b M := by
      induction M using Germ.inductionOn with | _ mSeq =>
      exact hK_inf (mSeq : ℕ*) hMK
    have hbM : starSeq b M ≈ₕ (L : ℝ*) := by
      induction M using Germ.inductionOn with | _ mSeq =>
      intro r hr
      have hev_top : ∀ᶠ m in atTop, |b m - L| < r := by
        have ht := hb.sub_const L
        rw [sub_self] at ht
        exact ht.abs.eventually (Iio_mem_nhds (by simpa using hr))
      obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hev_top
      have hM_gt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), M₀ < mSeq i := Germ.coe_lt.1 (hM_unl M₀)
      exact ofSeq_lt_ofSeq.2 (hM_gt.mono fun i hi ↦ hM₀ (mSeq i) hi.le)
    exact hsM.trans hbM
  · -- Standard diagonal extraction: choose `nSeq m` inductively so `|a m (nSeq m) - b m| < 1/(m+1)`.
    have hex_step : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, |a m n - b m| < ((m : ℝ) + 1)⁻¹ := by
      intro m
      have hpos : (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := by positivity
      have ht := (ha m).sub_const (b m)
      rw [sub_self] at ht
      exact eventually_atTop.1 (ht.abs.eventually (Iio_mem_nhds (by simpa using hpos)))
    choose Nbound hNbound using hex_step
    let nSeq : ℕ → ℕ := fun m ↦ Nat.recOn m (Nbound 0) (fun k prev ↦ max (prev + 1) (Nbound (k + 1)))
    have hmono : StrictMono nSeq := strictMono_nat_of_lt_succ fun m ↦
      Nat.lt_of_lt_of_le (Nat.lt_succ_self (nSeq m)) (le_max_left _ _)
    have hbd : ∀ m : ℕ, Nbound m ≤ nSeq m := fun m ↦ by
      cases m with
      | zero => exact le_rfl
      | succ k => exact le_max_right _ _
    refine ⟨nSeq, hmono, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M₁, hM₁⟩ := (Metric.tendsto_atTop.1 hb) (ε / 2) (half_pos hε)
    obtain ⟨M₂, hM₂⟩ := exists_nat_one_div_lt (half_pos hε)
    refine ⟨max M₁ M₂, fun m hm ↦ ?_⟩
    rw [Real.dist_eq]
    have h1 : |a m (nSeq m) - b m| < ((m : ℝ) + 1)⁻¹ := hNbound m (nSeq m) (hbd m)
    have hm2 : M₂ ≤ m := (le_max_right M₁ M₂).trans hm
    have h2 : ((m : ℝ) + 1)⁻¹ ≤ ((M₂ : ℝ) + 1)⁻¹ :=
      inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hm2 1)
    have h3 : ((M₂ : ℝ) + 1)⁻¹ < ε / 2 := by simpa [one_div] using hM₂
    have h4 : |b m - L| < ε / 2 := by
      simpa [Real.dist_eq] using hM₁ m ((le_max_left M₁ M₂).trans hm)
    have htri : |a m (nSeq m) - L| ≤ |a m (nSeq m) - b m| + |b m - L| := by
      have : a m (nSeq m) - L = (a m (nSeq m) - b m) + (b m - L) := by ring
      rw [this]; exact abs_add_le _ _
    linarith

/-- Goldblatt §15.2, Theorem 15.2.3 (p. 193):
If `F` is an internal `*ℝ`-valued function (`IsInternalFun F`) whose domain includes `𝕃` and
`F(x)` is infinitesimal for every limited hyperreal `x`, then there exists a positive unlimited
`b ∈ ℝ*` such that `[-b, b] ⊆ F.dom` and `F(x)` is infinitesimal for all `x ∈ [-b, b]`. -/
theorem robinson_limited_to_unlimited_interval {F : InternalPartialFun} (hF : IsInternalFun F)
    (hdom : {x : ℝ* | IsLimited x} ⊆ F.dom)
    (hinf : ∀ x : ℝ*, IsLimited x → IsInfinitesimal (F.apply x)) :
    ∃ b : ℝ*, IsPosUnlimited b ∧ Set.Icc (-b) b ⊆ F.dom ∧
      ∀ x ∈ Set.Icc (-b) b, IsInfinitesimal (F.apply x) := by
  -- Following Goldblatt p. 193: consider `X = {x ∈ F.dom | |x * F(x)| < 1}`.
  let IdFun : InternalPartialFun := starInternalFun Set.univ id
  have hId : IsInternalFun IdFun := isInternalFun_starInternalFun Set.univ id
  let G : InternalPartialFun := IdFun.mul F
  have hG : IsInternalFun G := hId.mul hF
  have hId_dom : IdFun.dom = Set.univ := by simp [IdFun]
  have hG_dom : G.dom = F.dom := by
    change IdFun.dom ∩ F.dom = F.dom
    rw [hId_dom, Set.univ_inter]
  have hG_app : ∀ x ∈ F.dom, G.apply x = x * F.apply x := by
    intro x hx
    have hxG : x ∈ IdFun.dom ∩ F.dom := ⟨hId_dom.symm ▸ Set.mem_univ x, hx⟩
    have h1 : G.apply x = IdFun.apply x * F.apply x :=
      InternalPartialFun.mkPartial_apply_of_mem hxG
    have h2 : IdFun.apply x = x := by
      rw [starInternalFun_apply_of_mem (by simp), starFun_id]; rfl
    rw [h1, h2]
  let X : Set ℝ* := G.preimage (Set.Ioo (-1 : ℝ*) 1)
  have hX_int : IsInternal X := hG.preimage (isInternal_Ioo _ _)
  have hL_sub : {x : ℝ* | IsLimited x} ⊆ X := by
    intro x hx
    have hxF : x ∈ F.dom := hdom hx
    refine ⟨hG_dom.symm ▸ hxF, ?_⟩
    rw [hG_app x hxF]
    have hmul_inf : IsInfinitesimal (x * F.apply x) := hx.mul_isInfinitesimal (hinf x hx)
    have hlt1 : |x * F.apply x| < 1 := by simpa using hmul_inf 1 one_pos
    exact abs_lt.1 hlt1
  obtain ⟨b, hb_unl, hb_sub⟩ := hX_int.exists_posUnlimited_Icc_subset_of_limited_subset hL_sub
  refine ⟨b, hb_unl, fun x hx ↦ hG_dom ▸ (hb_sub hx).1, fun x hx ↦ ?_⟩
  by_cases hx_lim : IsLimited x
  · exact hinf x hx_lim
  · have hx_unl : IsUnlimited x := isUnlimited_iff_not_isLimited.2 hx_lim
    have hxX : x ∈ X := hb_sub hx
    have hxF : x ∈ F.dom := hG_dom ▸ hxX.1
    have hprod_lt : |x * F.apply x| < 1 := by
      rw [← hG_app x hxF]
      exact abs_lt.2 hxX.2
    have hx_pos : 0 < |x| := (Nat.cast_nonneg 0).trans_lt (hx_unl 0)
    have hlt_inv : |F.apply x| < |x|⁻¹ := by
      rw [abs_mul] at hprod_lt
      rw [← one_div]
      exact (lt_div_iff₀' hx_pos).2 hprod_lt
    have hinv_inf : IsInfinitesimal x⁻¹ := hx_unl.inv_isInfinitesimal
    refine isInfinitesimal_of_abs_le hinv_inf ?_
    rw [abs_inv]
    exact hlt_inv.le

/-- `≈ₕ c` generalization of Theorem 15.2.3: if `F` is internal with `𝕃 ⊆ F.dom` and `F(x) ≈ₕ c` for
every limited `x ∈ ℝ*`, then `F(x) ≈ₕ c` for all `x ∈ [-b, b]` for some positive unlimited `b ∈ ℝ*`. -/
theorem robinson_limited_infClose_to_unlimited_interval {F : InternalPartialFun}
    (hF : IsInternalFun F) {c : ℝ*} (hdom : {x : ℝ* | IsLimited x} ⊆ F.dom)
    (hclose : ∀ x : ℝ*, IsLimited x → F.apply x ≈ₕ c) :
    ∃ b : ℝ*, IsPosUnlimited b ∧ Set.Icc (-b) b ⊆ F.dom ∧
      ∀ x ∈ Set.Icc (-b) b, F.apply x ≈ₕ c := by
  let C : InternalPartialFun := (starInternalFun Set.univ (fun _ ↦ 1)).smul (-c)
  have hC : IsInternalFun C := IsInternalFun.smul (-c) (isInternalFun_starInternalFun _ _)
  have hC_dom : C.dom = Set.univ := by
    dsimp [C, InternalPartialFun.smul]
    simp
  let D : InternalPartialFun := F.add C
  have hD : IsInternalFun D := hF.add hC
  have hD_dom : D.dom = F.dom := by
    change F.dom ∩ C.dom = F.dom
    rw [hC_dom, Set.inter_univ]
  have hD_app : ∀ x ∈ F.dom, D.apply x = F.apply x - c := by
    intro x hx
    have hxD : x ∈ F.dom ∩ C.dom := ⟨hx, hC_dom.symm ▸ Set.mem_univ x⟩
    have h1 : D.apply x = F.apply x + C.apply x := InternalPartialFun.mkPartial_apply_of_mem hxD
    have h2 : C.apply x = -c := by
      have hx1 : x ∈ (starInternalFun Set.univ (fun _ ↦ (1 : ℝ))).dom := by simp
      dsimp only [C, InternalPartialFun.smul]
      rw [InternalPartialFun.mkPartial_apply_of_mem hx1,
          starInternalFun_apply_of_mem (by simp)]
      have hconst : starFun (fun _ : ℝ ↦ (1 : ℝ)) x = 1 :=
        Germ.inductionOn x fun _ ↦ rfl
      rw [hconst, mul_one]
    rw [h1, h2, sub_eq_add_neg]
  obtain ⟨b, hb_unl, hb_dom, hb_inf⟩ := robinson_limited_to_unlimited_interval hD
    (hD_dom.symm ▸ hdom) (fun x hx ↦ by rw [hD_app x (hdom hx)]; exact hclose x hx)
  refine ⟨b, hb_unl, hD_dom ▸ hb_dom, fun x hx ↦ ?_⟩
  have hxF : x ∈ F.dom := hD_dom ▸ hb_dom hx
  have := hb_inf x hx
  rwa [hD_app x hxF] at this

/-! ## §15.3 Uniformly Converging Sequences of Functions -/

/-- Goldblatt §15.3 (p. 194): Extension of a standard sequence of functions `f : ℕ → ℝ → ℝ` to the
internal hypersequence `*f : ℕ* → ℝ* → ℝ*` (`(*f)_N(x) = [f_{N_i}(x_i)]`). -/
def starFunSeq (f : ℕ → ℝ → ℝ) (N : ℕ*) (x : ℝ*) : ℝ* :=
  Germ.map₂ (fun m r ↦ f m r) N x

/-- Evaluation of `starFunSeq` on `(a : ℕ*)` and `ofSeq r`. -/
@[simp]
theorem starFunSeq_coe_ofSeq (f : ℕ → ℝ → ℝ) (a : ℕ → ℕ) (r : ℕ → ℝ) :
    starFunSeq f (a : ℕ*) (ofSeq r) = ofSeq (fun i ↦ f (a i) (r i)) := rfl

/-- On standard index `(n : ℕ*)`, `starFunSeq f (n : ℕ*)` agrees with `starFun (f n)`. -/
@[simp]
theorem starFunSeq_natCast (f : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ*) :
    starFunSeq f (n : ℕ*) x = starFun (f n) x :=
  Germ.inductionOn x fun _ ↦ rfl

/-- On standard index `(n : ℕ*)` and standard real `(c : ℝ*)`, `(*f)_n(c) = f_n(c)`. -/
@[simp]
theorem starFunSeq_natCast_coe (f : ℕ → ℝ → ℝ) (n : ℕ) (c : ℝ) :
    starFunSeq f (n : ℕ*) (c : ℝ*) = (f n c : ℝ*) := rfl

/-- For each hypernatural `N ∈ ℕ*` and standard set `S ⊆ ℝ`, `x ↦ starFunSeq f N x` on `starSet S`
is an internal function (`IsInternalFun`). -/
theorem isInternalFun_starFunSeq (f : ℕ → ℝ → ℝ) (N : ℕ*) (S : Set ℝ) :
    IsInternalFun (InternalPartialFun.mkPartial (starSet S) (starFunSeq f N)) := by
  induction N using Germ.inductionOn with | _ a =>
  refine ⟨fun i ↦ RealPartialFun.mkPartial S (f (a i)), ?_⟩
  rw [InternalPartialFun.eq_iff_dom_and_eqOn]
  refine ⟨(internalSet_const S).symm, fun x hx ↦ ?_⟩
  have hxS : x ∈ starSet S := hx
  rw [InternalPartialFun.mkPartial_apply_of_mem hxS]
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), r i ∈ S := ofSeq_mem_starSet.1 hxS
  exact Germ.coe_eq.2 (hev.mono fun i hi ↦ (RealPartialFun.mkPartial_apply_of_mem hi).symm)

/-- Goldblatt §15.3 (p. 194): For any fixed `x, y ∈ ℝ*`, the hypersequence
`N ↦ |(*f)_N(x) - (*f)_N(y)|` is internal (`IsInternalSeq`). -/
theorem isInternalSeq_abs_sub_starFunSeq (f : ℕ → ℝ → ℝ) (x y : ℝ*) :
    IsInternalSeq (fun N : ℕ* ↦ |starFunSeq f N x - starFunSeq f N y|) := by
  rcases ofSeq_surjective x with ⟨rx, rfl⟩
  rcases ofSeq_surjective y with ⟨ry, rfl⟩
  refine ⟨fun i m ↦ |f m (rx i) - f m (ry i)|, ?_⟩
  ext N; induction N using Germ.inductionOn with | _ _ => rfl

/-- Nonstandard characterization of `ContinuousOn h S` (cf. Goldblatt §7.1): `h` is continuous on
`S ⊆ ℝ` iff for every `c ∈ S` and `x ∈ starSet S` with `x ≈ₕ c`, `*h(x) ≈ₕ h(c)`. -/
theorem continuousOn_iff_infClose_starSet {h : ℝ → ℝ} {S : Set ℝ} :
    ContinuousOn h S ↔
      ∀ c ∈ S, ∀ x ∈ starSet S, x ≈ₕ (c : ℝ*) → starFun h x ≈ₕ (h c : ℝ*) := by
  rw [Metric.continuousOn_iff]
  constructor
  · intro hcont c hc x hxS hxc ε hε
    obtain ⟨δ, hδ, hball⟩ := hcont c hc ε hε
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hrS : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), r i ∈ S := ofSeq_mem_starSet.1 hxS
    have hrδ : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), |r i - c| < δ := by
      have hlt : ofSeq (fun i ↦ |r i - c|) < (δ : ℝ*) := hxc δ hδ
      exact ofSeq_lt_ofSeq.1 hlt
    have habs_eq : |starFun h (ofSeq r) - (h c : ℝ*)| = ofSeq (fun i ↦ |h (r i) - h c|) := rfl
    rw [habs_eq]
    refine ofSeq_lt_ofSeq.2 ((hrS.and hrδ).mono fun i ⟨hi1, hi2⟩ ↦ ?_)
    simpa [Real.dist_eq] using hball (r i) hi1 (by simpa [Real.dist_eq] using hi2)
  · intro hns c hc ε hε
    by_contra hnot
    push Not at hnot
    have hex : ∀ n : ℕ, ∃ r ∈ S, |r - c| < ((n : ℝ) + 1)⁻¹ ∧ ε ≤ |h r - h c| := by
      intro n
      obtain ⟨r, hrS, hdist, hge⟩ := hnot (((n : ℝ) + 1)⁻¹) (by positivity)
      exact ⟨r, hrS, by simpa [Real.dist_eq] using hdist, by simpa [Real.dist_eq] using hge⟩
    choose r hrS hr_lt hr_ge using hex
    have hxS : ofSeq r ∈ starSet S := ofSeq_mem_starSet.2 (Eventually.of_forall hrS)
    have hxc : ofSeq r ≈ₕ (c : ℝ*) := by
      intro η hη
      obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hη
      have hge_top : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), N₀ ≤ i :=
        Nat.hyperfilter_le_atTop (eventually_ge_atTop N₀)
      refine ofSeq_lt_ofSeq.2 (hge_top.mono fun i hi ↦ ?_)
      have h1 : ((i : ℝ) + 1)⁻¹ ≤ ((N₀ : ℝ) + 1)⁻¹ :=
        inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hi 1)
      have h2 : ((N₀ : ℝ) + 1)⁻¹ < η := by simpa [one_div] using hN₀
      exact (hr_lt i).trans (h1.trans_lt h2)
    have hlt : |starFun h (ofSeq r) - (h c : ℝ*)| < (ε : ℝ*) := hns c hc (ofSeq r) hxS hxc ε hε
    have hge : (ε : ℝ*) ≤ |starFun h (ofSeq r) - (h c : ℝ*)| :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall hr_ge)
    exact not_lt_of_ge hge hlt

/-- Goldblatt §15.3(i) (p. 194): If `(f_n : n ∈ ℕ)` converges uniformly to `g` on `S ⊆ ℝ`, then
`(*f)_N(x) ≈ₕ *g(x)` for every unlimited `N ∈ ℕ*` and every `x ∈ starSet S`. -/
theorem infClose_starFunSeq_of_tendstoUniformlyOn {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {S : Set ℝ}
    (hunif : TendstoUniformlyOn f g atTop S) :
    ∀ N : ℕ*, IsUnlimitedNat N → ∀ x ∈ starSet S, starFunSeq f N x ≈ₕ starFun g x := by
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  intro N hN x hxS ε hε
  obtain ⟨k, hk⟩ := eventually_atTop.1 (hunif ε hε)
  induction N using Germ.inductionOn with | _ a =>
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  have ha_gt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), k < a i := Germ.coe_lt.1 (hN k)
  have hrS : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), r i ∈ S := ofSeq_mem_starSet.1 hxS
  refine ofSeq_lt_ofSeq.2 ((ha_gt.and hrS).mono fun i ⟨hi_gt, hi_S⟩ ↦ ?_)
  have hd := hk (a i) hi_gt.le (r i) hi_S
  rw [Real.dist_eq, abs_sub_comm] at hd
  exact hd

/-- Goldblatt §15.3 (p. 194): **Uniform Limit of Continuous Functions via Robinson's Sequential Lemma**!
If a sequence `(f_n : n ∈ ℕ)` of continuous real-valued functions on `[a, b] ⊆ ℝ` converges
uniformly to `g` on `[a, b]`, then `g` is continuous on `[a, b]`. -/
theorem continuousOn_of_tendstoUniformlyOn_via_robinson {a b : ℝ} {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n : ℕ, ContinuousOn (f n) (Set.Icc a b))
    (hunif : TendstoUniformlyOn f g atTop (Set.Icc a b)) :
    ContinuousOn g (Set.Icc a b) := by
  rw [continuousOn_iff_infClose_starSet]
  intro c hc x hx hxc
  have hc_star : (c : ℝ*) ∈ starSet (Set.Icc a b) := coe_mem_starSet.2 hc
  -- Step 1: For each standard `n : ℕ`, `|*f_n(x) - *f_n(c)| ≈ₕ 0` by continuity of `f_n`.
  have hstd_inf : ∀ n : ℕ,
      IsInfinitesimal |starFunSeq f (n : ℕ*) x - starFunSeq f (n : ℕ*) (c : ℝ*)| := by
    intro n
    have hfn := (continuousOn_iff_infClose_starSet.1 (hf n)) c hc x hx hxc
    simpa only [starFunSeq_natCast, starFun_coe] using hfn.abs
  -- Step 2: By Robinson's Sequential Lemma (15.2.1), pick an unlimited `K ∈ ℕ*` with
  -- `*f_K(x) ≈ₕ *f_K(c)`.
  obtain ⟨K, hK_unl, hK_inf⟩ :=
    robinson_sequential_lemma (isInternalSeq_abs_sub_starFunSeq f x (c : ℝ*)) hstd_inf
  have hfK_xc : starFunSeq f K x ≈ₕ starFunSeq f K (c : ℝ*) := by
    have habs := hK_inf K le_rfl
    intro r hr
    simpa using habs r hr
  -- Step 3: By 15.3(i), `*f_K(x) ≈ₕ *g(x)` and `*f_K(c) ≈ₕ *g(c) = g(c)`.
  have hfK_gx : starFunSeq f K x ≈ₕ starFun g x :=
    infClose_starFunSeq_of_tendstoUniformlyOn hunif K hK_unl x hx
  have hfK_gc : starFunSeq f K (c : ℝ*) ≈ₕ (g c : ℝ*) := by
    simpa using infClose_starFunSeq_of_tendstoUniformlyOn hunif K hK_unl (c : ℝ*) hc_star
  exact (hfK_gx.symm.trans hfK_xc).trans hfK_gc

/-- Goldblatt §15.3, Exercise 15.3.1 (p. 194):
Condition 15.3(i) (`(*f)_N(x) ≈ₕ *g(x)` for all unlimited `N ∈ ℕ*` and `x ∈ *[a, b]`) is also
**sufficient** for `(f_n : n ∈ ℕ)` to converge uniformly to `g` on `[a, b]` (proved via Underflow). -/
theorem tendstoUniformlyOn_of_infClose_unlimited {a b : ℝ} {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hclose : ∀ N : ℕ*, IsUnlimitedNat N →
      ∀ x ∈ starSet (Set.Icc a b), starFunSeq f N x ≈ₕ starFun g x) :
    TendstoUniformlyOn f g atTop (Set.Icc a b) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let Sε : Set ℕ := {m : ℕ | ∀ r ∈ Set.Icc a b, |f m r - g r| < ε}
  have hunl_mem : ∀ N : ℕ*, IsUnlimitedNat N → N ∈ starNatSet Sε := by
    intro N hN
    induction N using Germ.inductionOn with | _ mSeq =>
    rw [coe_mem_starNatSet]
    by_contra hnot
    have hbad : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
        ∃ r ∈ Set.Icc a b, ε ≤ |f (mSeq i) r - g r| := by
      refine (Ultrafilter.eventually_not.2 hnot).mono fun i hi ↦ ?_
      change ¬ ∀ r ∈ Set.Icc a b, |f (mSeq i) r - g r| < ε at hi
      push Not at hi
      exact hi
    let rSeq : ℕ → ℝ := fun i ↦
      if h : ∃ r ∈ Set.Icc a b, ε ≤ |f (mSeq i) r - g r| then h.choose else a
    have hx_mem : ofSeq rSeq ∈ starSet (Set.Icc a b) := by
      refine ofSeq_mem_starSet.2 (hbad.mono fun i hi ↦ ?_)
      simpa only [rSeq, hi, ↓reduceDIte] using hi.choose_spec.1
    have hlt : |starFunSeq f (mSeq : ℕ*) (ofSeq rSeq) - starFun g (ofSeq rSeq)| < (ε : ℝ*) :=
      hclose (mSeq : ℕ*) hN (ofSeq rSeq) hx_mem ε hε
    have hge : (ε : ℝ*) ≤ |starFunSeq f (mSeq : ℕ*) (ofSeq rSeq) - starFun g (ofSeq rSeq)| := by
      have habs_eq : |starFunSeq f (mSeq : ℕ*) (ofSeq rSeq) - starFun g (ofSeq rSeq)| =
          ofSeq (fun i ↦ |f (mSeq i) (rSeq i) - g (rSeq i)|) := rfl
      rw [habs_eq]
      refine ofSeq_le_ofSeq.2 (hbad.mono fun i hi ↦ ?_)
      simpa only [rSeq, hi, ↓reduceDIte] using hi.choose_spec.2
    exact not_lt_of_ge hge hlt
  obtain ⟨k, hk⟩ := permanence_underflow_all_unlimited (isInternalNat_starNatSet Sε) hunl_mem
  refine eventually_atTop.2 ⟨k, fun n hkn r hr ↦ ?_⟩
  have hn_mem : n ∈ Sε := natCast_mem_starNatSet.1 (hk (Set.mem_Ici.2 (by exact_mod_cast hkn)))
  rw [Real.dist_eq, abs_sub_comm]
  exact hn_mem r hr

/-- Full nonstandard equivalence for uniform convergence on `[a, b]` combining §15.3(i) and
Exercise 15.3.1. -/
theorem tendstoUniformlyOn_iff_infClose_unlimited {a b : ℝ} {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} :
    TendstoUniformlyOn f g atTop (Set.Icc a b) ↔
      ∀ N : ℕ*, IsUnlimitedNat N →
        ∀ x ∈ starSet (Set.Icc a b), starFunSeq f N x ≈ₕ starFun g x :=
  ⟨infClose_starFunSeq_of_tendstoUniformlyOn, tendstoUniformlyOn_of_infClose_unlimited⟩

/-! ## §15.4 Comprehensiveness, Ultrapower Diagonalization, Theorem 15.4.3, and Exercise 15.4.4 -/

/-- Representative sequence `ι → β` chosen for an arbitrary ultrapower element
`y : Germ (U : Filter ι) β`. -/
def germRep {ι β : Type*} (U : Ultrafilter ι) (y : Germ (U : Filter ι) β) : ι → β :=
  (show ∃ g : ι → β, (Germ.ofFun g : Germ (U : Filter ι) β) = y from by
    induction y using Germ.inductionOn with | _ g => exact ⟨g, rfl⟩).choose

/-- The chosen representative `germRep U y` represents `y` in `Germ (U : Filter ι) β`. -/
@[simp]
theorem germRep_eq {ι β : Type*} (U : Ultrafilter ι) (y : Germ (U : Filter ι) β) :
    (Germ.ofFun (germRep U y) : Germ (U : Filter ι) β) = y :=
  (show ∃ g : ι → β, (Germ.ofFun g : Germ (U : Filter ι) β) = y from by
    induction y using Germ.inductionOn with | _ g => exact ⟨g, rfl⟩).choose_spec

/-- Injectivity of the constant-germ embedding `Germ.const : α → Germ (U : Filter ι) α`
over any ultrafilter `U`. -/
theorem germ_const_injective {ι α : Type*} (U : Ultrafilter ι) :
    Function.Injective (Germ.const (l := (U : Filter ι)) : α → Germ (U : Filter ι) α) := by
  intro a b hab
  have hev : ∀ᶠ _ : ι in (U : Filter ι), a = b := Germ.coe_eq.1 hab
  obtain ⟨_, h⟩ := hev.exists
  exact h

/-- Goldblatt §15.4 (p. 195–196): Ultrapower diagonalization operator extending an arbitrary
standard-domain map `f : α → Germ (U : Filter ι) β` to an internal function
`Germ (U : Filter ι) α → Germ (U : Filter ι) β` using a representative choice `rep`. -/
def ultrapowerExtWithRep {ι α β : Type*} (U : Ultrafilter ι)
    (rep : Germ (U : Filter ι) β → (ι → β))
    (f : α → Germ (U : Filter ι) β) :
    Germ (U : Filter ι) α → Germ (U : Filter ι) β :=
  internalGermFun U (fun i a ↦ rep (f a) i)

/-- Goldblatt §15.4 (p. 195): `ultrapowerExtWithRep U rep f` agrees with `f` on every standard
input `Germ.const a`. -/
theorem ultrapowerExtWithRep_const {ι α β : Type*} (U : Ultrafilter ι)
    (rep : Germ (U : Filter ι) β → (ι → β))
    (hrep : ∀ y, (Germ.ofFun (rep y) : Germ (U : Filter ι) β) = y)
    (f : α → Germ (U : Filter ι) β) (a : α) :
    ultrapowerExtWithRep U rep f (Germ.const a) = f a :=
  hrep (f a)

/-- Goldblatt §15.4 (pp. 195–196, Full Comprehensiveness of Ultrapowers):
Every ultrapower over any ultrafilter `U : Ultrafilter ι` is **comprehensive**: given any standard
type `α`, any internal subset `B = internalGermSet U H ⊆ Germ (U : Filter ι) β`, and *any*
(possibly external) function `f : α → Germ (U : Filter ι) β` with `∀ a, f a ∈ B`, there exists
`F : ι → α → β` such that the internal function `internalGermFun U F` maps all of
`Germ (U : Filter ι) α` into `B` and extends `f` on standard elements `Germ.const a`. -/
theorem ultrapower_comprehensive {ι α β : Type*} (U : Ultrafilter ι)
    (H : ι → Set β) (f : α → Germ (U : Filter ι) β)
    (hf : ∀ a : α, f a ∈ internalGermSet U H) :
    ∃ F : ι → α → β,
      (∀ x : Germ (U : Filter ι) α, internalGermFun U F x ∈ internalGermSet U H) ∧
      (∀ a : α, internalGermFun U F (Germ.const a) = f a) := by
  let F : ι → α → β := fun i a ↦
    if germRep U (f a) i ∈ H i then germRep U (f a) i
    else if hne : (H i).Nonempty then hne.some
    else germRep U (f a) i
  refine ⟨F, fun x ↦ ?_, fun a ↦ ?_⟩
  · induction x using Germ.inductionOn with | _ xSeq =>
    obtain ⟨i₀, _⟩ := (Eventually.of_forall (f := (U : Filter ι)) fun _ ↦ True.intro).exists
    have ha₀ : ∀ᶠ i in (U : Filter ι), germRep U (f (xSeq i₀)) i ∈ H i := by
      have hmem := hf (xSeq i₀)
      rw [← germRep_eq U (f (xSeq i₀))] at hmem
      exact coe_mem_internalGermSet.1 hmem
    refine coe_mem_internalGermSet.2 (ha₀.mono fun i hi ↦ ?_)
    have hne : (H i).Nonempty := ⟨_, hi⟩
    dsimp only [F]
    split_ifs with h1
    · exact h1
    · exact hne.some_mem
  · have ha : ∀ᶠ i in (U : Filter ι), germRep U (f a) i ∈ H i := by
      have hmem := hf a
      rw [← germRep_eq U (f a)] at hmem
      exact coe_mem_internalGermSet.1 hmem
    have heq : (Germ.ofFun (fun i ↦ F i a) : Germ (U : Filter ι) β) =
        Germ.ofFun (germRep U (f a)) := by
      refine Germ.coe_eq.2 (ha.mono fun i hi ↦ ?_)
      simp only [F, hi, ↓reduceIte]
    exact heq.trans (germRep_eq U (f a))

/-- Goldblatt §15.4, Exercise 15.4.1(1) (p. 196):
If `f, g : α → Germ (U : Filter ι) β` agree at all except finitely many elements of `α` (even when
`α` is infinite), then their internal ultrapower extensions `ultrapowerExtWithRep U rep f` and
`ultrapowerExtWithRep U rep g` agree on every nonstandard element
`x ∈ Germ (U : Filter ι) α \ Set.range Germ.const`. -/
theorem ultrapowerExtWithRep_eq_on_nonstandard_of_cofinite {ι α β : Type*} (U : Ultrafilter ι)
    (rep : Germ (U : Filter ι) β → (ι → β))
    {f g : α → Germ (U : Filter ι) β}
    (hfin : {a : α | f a ≠ g a}.Finite)
    {x : Germ (U : Filter ι) α}
    (hx : x ∉ Set.range (Germ.const (l := (U : Filter ι)) : α → Germ (U : Filter ι) α)) :
    ultrapowerExtWithRep U rep f x = ultrapowerExtWithRep U rep g x := by
  induction x using Germ.inductionOn with | _ xSeq =>
  have hnot_mem : {i : ι | xSeq i ∈ {a : α | f a ≠ g a}} ∉ U := by
    intro hmem
    have hsub : {i : ι | xSeq i ∈ {a : α | f a ≠ g a}} =
        ⋃ a ∈ {a : α | f a ≠ g a}, {i : ι | xSeq i = a} := by
      ext i; simp
    rw [hsub, Ultrafilter.finite_biUnion_mem_iff hfin] at hmem
    obtain ⟨a, _, haU⟩ := hmem
    exact hx ⟨a, (Germ.coe_eq.2 haU).symm⟩
  have hev : ∀ᶠ i in (U : Filter ι), xSeq i ∉ {a : α | f a ≠ g a} :=
    Ultrafilter.compl_mem_iff_notMem.2 hnot_mem
  refine Germ.coe_eq.2 (hev.mono fun i hi ↦ ?_)
  have hfg : f (xSeq i) = g (xSeq i) := not_not.1 hi
  dsimp only [Function.comp_apply]
  rw [hfg]

/-- Canonical representative choice on `Germ (U : Filter ι) γ` that selects the constant sequence
`fun _ ↦ c` whenever `y = Germ.const c` is standard, and `germRep U y` otherwise
(Goldblatt §15.4, Exercise 15.4.1(2), p. 196). -/
def canonicalRep {ι γ : Type*} (U : Ultrafilter ι) (y : Germ (U : Filter ι) γ) : ι → γ :=
  if hc : ∃ c : γ, y = Germ.const c then fun _ ↦ hc.choose else germRep U y

/-- `canonicalRep U y` always represents `y`. -/
@[simp]
theorem canonicalRep_eq {ι γ : Type*} (U : Ultrafilter ι) (y : Germ (U : Filter ι) γ) :
    (Germ.ofFun (canonicalRep U y) : Germ (U : Filter ι) γ) = y := by
  dsimp only [canonicalRep]
  split_ifs with hc
  · exact hc.choose_spec.symm
  · exact germRep_eq U y

/-- On any standard element `Germ.const c`, `canonicalRep U` selects the exact constant sequence
`fun _ ↦ c`. -/
@[simp]
theorem canonicalRep_const {ι γ : Type*} (U : Ultrafilter ι) (c : γ) :
    canonicalRep U (Germ.const c) = fun _ ↦ c := by
  have hc : ∃ d : γ, (Germ.const c : Germ (U : Filter ι) γ) = Germ.const d := ⟨c, rfl⟩
  have hd : hc.choose = c := germ_const_injective U hc.choose_spec.symm
  simp only [canonicalRep, hc, ↓reduceDIte, hd]

/-- Goldblatt §15.4, Exercise 15.4.1(2) (p. 196):
When `h : α → γ` is a standard function (viewed as `a ↦ Germ.const (h a)` into `*γ`), the
ultrapower comprehensiveness construction using `canonicalRep U` produces the exact enlargement
`*h = Germ.map h : *α → *γ`. -/
theorem ultrapowerExtWithRep_canonicalRep_eq_map {ι α γ : Type*} (U : Ultrafilter ι)
    (h : α → γ) :
    ultrapowerExtWithRep U (canonicalRep U) (fun a ↦ Germ.const (h a)) = Germ.map h := by
  ext x
  induction x using Germ.inductionOn with | _ xSeq =>
  change Germ.ofFun (fun i ↦ canonicalRep U (Germ.const (h (xSeq i))) i) =
    Germ.ofFun (h ∘ xSeq)
  congr 1
  ext i
  simp [canonicalRep_const]

/-- Specialization of Exercise 15.4.1(2) to `ℝ*`: using `canonicalRep (hyperfilter ℕ)` on a
standard real function `h : ℝ → ℝ` yields `starFun h : ℝ* → ℝ*`. -/
theorem ultrapowerExtWithRep_canonicalRep_eq_starFun (h : ℝ → ℝ) :
    ultrapowerExtWithRep (hyperfilter ℕ) (canonicalRep (hyperfilter ℕ)) (fun r ↦ (h r : ℝ*)) =
      starFun h :=
  ultrapowerExtWithRep_canonicalRep_eq_map (hyperfilter ℕ) h

/-- An ultrafilter `U : Ultrafilter ι` is **countably incomplete** if there is a sequence of sets
`I : ℕ → Set ι` in `U` with empty intersection `⋂ n, I n = ∅`. -/
def IsCountablyIncomplete {ι : Type*} (U : Ultrafilter ι) : Prop :=
  ∃ I : ℕ → Set ι, (∀ n : ℕ, I n ∈ U) ∧ (⋂ n : ℕ, I n) = ∅

/-- Characterization of nonprincipal ultrafilters on `ℕ`: every singleton complement `{n}ᶜ` lies in
`U` iff `(U : Filter ℕ) ≤ Filter.cofinite` iff `U` contains `Set.Ici n` for every `n ∈ ℕ`. -/
theorem ultrafilter_nat_nonprincipal_iff (U : Ultrafilter ℕ) :
    (∀ n : ℕ, ({n}ᶜ : Set ℕ) ∈ U) ↔ (U : Filter ℕ) ≤ Filter.cofinite := by
  constructor
  · intro h
    rcases U.le_cofinite_or_eq_pure with hcof | ⟨n, hn⟩
    · exact hcof
    · exfalso
      have hmem : ({n}ᶜ : Set ℕ) ∈ (U : Filter ℕ) := h n
      rw [hn] at hmem
      exact hmem rfl
  · intro hcof n
    exact hcof (Set.finite_singleton n).compl_mem_cofinite

/-- Every nonprincipal ultrafilter on `ℕ` is countably incomplete (`⋂ n, Set.Ici n = ∅`), and its
diagonal germ `[id]` strictly exceeds every standard `n : ℕ`. -/
theorem isCountablyIncomplete_of_nonprincipal_nat (U : Ultrafilter ℕ)
    (hnp : ∀ n : ℕ, ({n}ᶜ : Set ℕ) ∈ U) :
    IsCountablyIncomplete U ∧
      ∀ n : ℕ, (Germ.const n : Germ (U : Filter ℕ) ℕ) < Germ.ofFun id := by
  have hcof : (U : Filter ℕ) ≤ Filter.cofinite := (ultrafilter_nat_nonprincipal_iff U).1 hnp
  have hIci : ∀ n : ℕ, Set.Ici n ∈ U := by
    intro n
    have hfin : (Set.Iio n).Finite := Set.finite_lt_nat n
    have hmem : (Set.Iio n)ᶜ ∈ (U : Filter ℕ) := hcof hfin.compl_mem_cofinite
    rwa [Set.compl_Iio] at hmem
  refine ⟨⟨Set.Ici, hIci, ?_⟩, fun n ↦ ?_⟩
  · ext k
    simp only [Set.mem_iInter, Set.mem_Ici, Set.mem_empty_iff_false, iff_false, not_forall]
    exact ⟨k + 1, by omega⟩
  · exact Germ.coe_lt.2 (hIci (n + 1))

/-- `hyperfilter ℕ` is countably incomplete. -/
theorem isCountablyIncomplete_hyperfilter_nat : IsCountablyIncomplete (hyperfilter ℕ) := by
  refine (isCountablyIncomplete_of_nonprincipal_nat (hyperfilter ℕ) fun n ↦ ?_).1
  exact mem_hyperfilter_of_finite_compl (by simp)

/-- Over *any* countably incomplete ultrafilter `U : Ultrafilter ι`, the ultrapower
`Germ (U : Filter ι) ℕ` contains an unlimited hypernatural strictly exceeding `Germ.const n`
for every `n : ℕ`. -/
theorem exists_unlimited_germ_of_isCountablyIncomplete {ι : Type*} (U : Ultrafilter ι)
    (hU : IsCountablyIncomplete U) :
    ∃ ω : Germ (U : Filter ι) ℕ, ∀ n : ℕ, Germ.const n < ω := by
  rcases hU with ⟨I, hIU, hEmpty⟩
  let J : ℕ → Set ι := fun n ↦ ⋂ k ∈ Finset.range (n + 1), I k
  have hJU : ∀ n : ℕ, J n ∈ (U : Filter ι) := fun n ↦
    (Filter.biInter_finset_mem (Finset.range (n + 1))).2 fun k _ ↦ hIU k
  have hJ_anti : Antitone J := by
    intro m n hmn i hi
    simp only [J, Set.mem_iInter, Finset.mem_range] at hi ⊢
    intro k hk
    exact hi k (by omega)
  have hex : ∀ i : ι, ∃ n : ℕ, i ∉ J n := by
    intro i
    by_contra hall
    push Not at hall
    have hi_inter : i ∈ ⋂ n : ℕ, I n := by
      refine Set.mem_iInter.2 fun n ↦ ?_
      have hiJ := hall n
      simp only [J, Set.mem_iInter, Finset.mem_range] at hiJ
      exact hiJ n (by omega)
    rw [hEmpty] at hi_inter
    exact hi_inter
  let a : ι → ℕ := fun i ↦ Nat.find (hex i)
  refine ⟨Germ.ofFun a, fun n ↦ Germ.coe_lt.2 ?_⟩
  refine Filter.mem_of_superset (hJU n) fun i hiJ ↦ ?_
  change n < a i
  by_contra hle
  push Not at hle
  have hi_find : i ∉ J (a i) := Nat.find_spec (hex i)
  exact hi_find (hJ_anti hle hiJ)

/-- Goldblatt §15.4 (p. 195–196, Unrestricted Sequential / Countable Comprehensiveness on `ℝ*`):
Every external sequence `x : ℕ → ℝ*` extends via explicit ultrapower diagonalization
`σ k m = germRep (hyperfilter ℕ) (x m) k` to an internal hypersequence `X : ℕ* → ℝ*` satisfying
`X (m : ℕ*) = x m` for all `m ∈ ℕ`. -/
theorem countable_comprehensiveness_seq_unrestricted (x : ℕ → ℝ*) :
    ∃ X : ℕ* → ℝ*, IsInternalSeq X ∧ ∀ m : ℕ, X (m : ℕ*) = x m := by
  refine ⟨internalSeq (fun i m ↦ germRep (hyperfilter ℕ) (x m) i), ⟨_, rfl⟩, fun m ↦ ?_⟩
  rw [internalSeq_natCast]
  exact germRep_eq (hyperfilter ℕ) (x m)

/-- Goldblatt §15.4 (p. 195–196, Sequential Comprehensiveness into an Internal Set `Y ⊆ ℝ*`):
Given any internal set `Y ⊆ ℝ*` and any sequence `x : ℕ → ℝ*` with `∀ m, x m ∈ Y`, there is an
internal hypersequence `X : ℕ* → ℝ*` with `∀ N : ℕ*, X N ∈ Y` and `∀ m : ℕ, X (m : ℕ*) = x m`. -/
theorem countable_comprehensiveness_seq {Y : Set ℝ*} (hY : IsInternal Y)
    (x : ℕ → ℝ*) (hx : ∀ m : ℕ, x m ∈ Y) :
    ∃ X : ℕ* → ℝ*, IsInternalSeq X ∧ (∀ N : ℕ*, X N ∈ Y) ∧ (∀ m : ℕ, X (m : ℕ*) = x m) := by
  rcases hY with ⟨B, rfl⟩
  have hx' : ∀ m : ℕ, x m ∈ internalGermSet (hyperfilter ℕ) B := hx
  obtain ⟨F, hF_mem, hF_ext⟩ := ultrapower_comprehensive (hyperfilter ℕ) B x hx'
  refine ⟨internalSeq F, ⟨F, rfl⟩, hF_mem, fun m ↦ ?_⟩
  exact hF_ext m

/-- Sequential Comprehensiveness for sequences of hypernaturals `x : ℕ → ℕ*` into an internal
set `Y ⊆ ℕ*`. -/
theorem countable_comprehensiveness_nat_seq {Y : Set ℕ*} (hY : IsInternalNat Y)
    (x : ℕ → ℕ*) (hx : ∀ m : ℕ, x m ∈ Y) :
    ∃ τ : ℕ → ℕ → ℕ,
      (∀ N : ℕ*, internalGermFun (hyperfilter ℕ) τ N ∈ Y) ∧
      (∀ m : ℕ, internalGermFun (hyperfilter ℕ) τ (m : ℕ*) = x m) := by
  rcases hY with ⟨B, rfl⟩
  have hx' : ∀ m : ℕ, x m ∈ internalGermSet (hyperfilter ℕ) B := hx
  obtain ⟨τ, hτ_mem, hτ_ext⟩ := ultrapower_comprehensive (hyperfilter ℕ) B x hx'
  exact ⟨τ, hτ_mem, fun m ↦ hτ_ext m⟩

/-- Sequential Comprehensiveness on `ℝ*` formulated directly in terms of `InternalPartialFun`
(Chapter 12): every `x : ℕ → ℝ*` valued in an internal set `Y ⊆ ℝ*` extends to an internal
function `F` with domain `*ℕ = Set.range Hypernat.toHyperreal` and `F.range ⊆ Y`. -/
theorem countable_comprehensiveness_internalFun {Y : Set ℝ*} (hY : IsInternal Y)
    (x : ℕ → ℝ*) (hx : ∀ m : ℕ, x m ∈ Y) :
    ∃ F : InternalPartialFun, IsInternalFun F ∧
      F.dom = Set.range Hypernat.toHyperreal ∧
      F.range ⊆ Y ∧
      ∀ m : ℕ, F.apply (m : ℝ*) = x m := by
  obtain ⟨X, hX_int, hX_mem, hX_ext⟩ := countable_comprehensiveness_seq hY x hx
  obtain ⟨F, hF_int, hF_dom, hF_val⟩ :=
    isInternalSeq_iff_exists_internalFun.1 hX_int
  refine ⟨F, hF_int, hF_dom, ?_, fun m ↦ ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [hF_dom] at hy
    rcases hy with ⟨N, rfl⟩
    rw [hF_val N]
    exact hX_mem N
  · have hm : (m : ℝ*) = Hypernat.toHyperreal (m : ℕ*) := (Hypernat.toHyperreal_natCast m).symm
    rw [hm, hF_val (m : ℕ*), hX_ext m]

/-- Full Comprehensiveness on `ℝ*` in terms of `InternalPartialFun`: for any standard set
`A : Set ℝ`, internal set `Y : Set ℝ*`, and arbitrary map `f : A → ℝ*` with `∀ a, f a ∈ Y`,
there exists an internal function `F` with `F.dom = starSet A`, `F.range ⊆ Y`, and
`F.apply (a : ℝ*) = f a` for all `a ∈ A`. -/
theorem full_comprehensiveness_internalFun (A : Set ℝ) {Y : Set ℝ*} (hY : IsInternal Y)
    (f : A → ℝ*) (hf : ∀ a : A, f a ∈ Y) :
    ∃ F : InternalPartialFun, IsInternalFun F ∧
      F.dom = starSet A ∧
      F.range ⊆ Y ∧
      ∀ a : A, F.apply (a.1 : ℝ*) = f a := by
  rcases hY with ⟨B, rfl⟩
  obtain ⟨G, hG_mem, hG_ext⟩ := ultrapower_comprehensive (hyperfilter ℕ) B f hf
  let p : ℕ → RealPartialFun := fun i ↦
    RealPartialFun.mkPartial A (fun r ↦ if hr : r ∈ A then G i ⟨r, hr⟩ else 0)
  refine ⟨internalFun p, isInternalFun_internalFun p, ?_, ?_, fun a ↦ ?_⟩
  · rw [internalFun_dom]
    rfl
  · rintro _ ⟨x, hx, rfl⟩
    rw [internalFun_dom] at hx
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hrA : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), r i ∈ A := ofSeq_mem_starSet.1 hx
    obtain ⟨i₀, hi₀⟩ := hrA.exists
    let aSeq : ℕ → A := fun i ↦ if hr : r i ∈ A then ⟨r i, hr⟩ else ⟨r i₀, hi₀⟩
    have hmemG : internalGermFun (hyperfilter ℕ) G (Germ.ofFun aSeq) ∈
        internalGermSet (hyperfilter ℕ) B := hG_mem (Germ.ofFun aSeq)
    have heq : (internalFun p).apply (ofSeq r) =
        internalGermFun (hyperfilter ℕ) G (Germ.ofFun aSeq) := by
      refine Germ.coe_eq.2 (hrA.mono fun i hi ↦ ?_)
      dsimp only [p, Function.comp_apply]
      rw [RealPartialFun.mkPartial_apply_of_mem hi]
      simp only [aSeq, hi, ↓reduceDIte]
    rwa [heq]
  · have hmem : a.1 ∈ A := a.2
    have heq : (internalFun p).apply (a.1 : ℝ*) =
        internalGermFun (hyperfilter ℕ) G (Germ.const a) := by
      refine Germ.coe_eq.2 (Eventually.of_forall fun i ↦ ?_)
      dsimp only [p, Function.comp_apply]
      rw [RealPartialFun.mkPartial_apply_of_mem hmem]
      simp only [hmem, ↓reduceDIte]
    exact heq.trans (hG_ext a)

/-- Goldblatt §15.4 (pp. 196–197, Uncountability via Countable Comprehensiveness + Overflow):
Alternative proof — using only Sequential Comprehensiveness and Overflow, *without* invoking
Countable Saturation — that no infinite internal set `Y ⊆ ℝ*` is countable. -/
theorem not_countable_infinite_of_isInternal_via_comprehensiveness {Y : Set ℝ*}
    (hY : IsInternal Y) (hInf : Y.Infinite) : ¬ Y.Countable := by
  intro hCount
  obtain ⟨x, hx_eq⟩ := hCount.exists_eq_range hInf.nonempty
  have hx_mem : ∀ n : ℕ, x n ∈ Y := fun n ↦ hx_eq ▸ ⟨n, rfl⟩
  have hz_ex : ∀ n : ℕ, ∃ y ∈ Y, ∀ k ≤ n, y ≠ x k := by
    intro n
    have hdiff : (Y \ ((Finset.range (n + 1)).image x : Set ℝ*)).Nonempty :=
      (hInf.sdiff (Finset.finite_toSet _)).nonempty
    obtain ⟨y, hyY, hyNot⟩ := hdiff
    refine ⟨y, hyY, fun k hk h_eq ↦ hyNot ?_⟩
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), h_eq.symm⟩)
  let z : ℕ → ℝ* := fun n ↦ (hz_ex n).choose
  have hz_mem : ∀ n : ℕ, z n ∈ Y := fun n ↦ (hz_ex n).choose_spec.1
  have hz_ne : ∀ n : ℕ, ∀ k ≤ n, z n ≠ x k := fun n ↦ (hz_ex n).choose_spec.2
  obtain ⟨X, ⟨σ, rfl⟩, _, hX_ext⟩ := countable_comprehensiveness_seq hY x hx_mem
  obtain ⟨Z, ⟨τ, rfl⟩, hZ_mem, hZ_ext⟩ := countable_comprehensiveness_seq hY z hz_mem
  let W : Set ℕ* := {N : ℕ* | ∀ k ≤ N, internalSeq τ N ≠ internalSeq σ k}
  have hW_int : IsInternalNat W := by
    refine ⟨fun i ↦ {m : ℕ | ∀ k ≤ m, τ i m ≠ σ i k}, ?_⟩
    ext N
    induction N using Germ.inductionOn with | _ a =>
    rw [coe_mem_internalNatSet]
    constructor
    · intro hN
      by_contra hnot
      have hbad : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), ∃ k ≤ a i, τ i (a i) = σ i k := by
        refine (Ultrafilter.eventually_not.2 hnot).mono fun i hi ↦ ?_
        change ¬ ∀ k ≤ a i, τ i (a i) ≠ σ i k at hi
        push Not at hi
        exact hi
      let kSeq : ℕ → ℕ := fun i ↦
        if h : ∃ k ≤ a i, τ i (a i) = σ i k then h.choose else 0
      have hk_le : (kSeq : ℕ*) ≤ (a : ℕ*) := by
        refine Germ.coe_le.2 (hbad.mono fun i hi ↦ ?_)
        simpa only [kSeq, hi, ↓reduceDIte] using hi.choose_spec.1
      have heq_val : internalSeq τ (a : ℕ*) = internalSeq σ (kSeq : ℕ*) := by
        refine Germ.coe_eq.2 (hbad.mono fun i hi ↦ ?_)
        simpa only [kSeq, hi, ↓reduceDIte] using hi.choose_spec.2
      exact hN (kSeq : ℕ*) hk_le heq_val
    · intro hev k hk heq_val
      induction k using Germ.inductionOn with | _ b =>
      have hle : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), b i ≤ a i := Germ.coe_le.1 hk
      have heq' : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), τ i (a i) = σ i (b i) :=
        Germ.coe_eq.1 heq_val
      obtain ⟨i, ⟨hiW, hib⟩, hit⟩ := ((hev.and hle).and heq').exists
      exact hiW (b i) hib hit
  have hW_nat : ∀ n : ℕ, (n : ℕ*) ∈ W := by
    intro n k hk
    obtain ⟨m, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 (fun hunl ↦ not_lt_of_ge hk (hunl n))
    have hmn : m ≤ n := by exact_mod_cast hk
    rw [hZ_ext n, hX_ext m]
    exact hz_ne n m hmn
  obtain ⟨M, hM_W, hM_unl⟩ :=
    permanence_overflow_arbitrarily_large_nat hW_int (fun k ↦ ⟨k, le_rfl, hW_nat k⟩)
  have hZM_Y : internalSeq τ M ∈ Y := hZ_mem M
  rw [hx_eq] at hZM_Y
  rcases hZM_Y with ⟨m, hm⟩
  have hm_le : (m : ℕ*) ≤ M := (hM_unl m).le
  exact hM_W (m : ℕ*) hm_le (hm.symm.trans (hX_ext m).symm)

/-- Goldblatt §15.4 (p. 196): No internal function `F` can have an external domain. -/
theorem no_internalFun_with_external_dom {X : Set ℝ*} (hX : IsExternal X) :
    ¬ ∃ F : InternalPartialFun, IsInternalFun F ∧ F.dom = X := by
  rintro ⟨F, hF, rfl⟩
  exact hX hF.isInternal_dom

/-- Goldblatt §15.4 (p. 196): No internal function `F` can have an external range. -/
theorem no_internalFun_with_external_range {Y : Set ℝ*} (hY : IsExternal Y) :
    ¬ ∃ F : InternalPartialFun, IsInternalFun F ∧ F.range = Y := by
  rintro ⟨F, hF, rfl⟩
  exact hY hF.isInternal_range

/-- Goldblatt §15.4 (p. 196): No internal function on `ℝ*` has exact domain `ℝ` or `ℕ`. -/
theorem no_internalFun_dom_real_or_nat :
    (¬ ∃ F : InternalPartialFun, IsInternalFun F ∧ F.dom = Set.range ((↑) : ℝ → ℝ*)) ∧
    (¬ ∃ F : InternalPartialFun, IsInternalFun F ∧ F.dom = Set.range ((↑) : ℕ → ℝ*)) :=
  ⟨no_internalFun_with_external_dom isExternal_real,
   no_internalFun_with_external_dom isExternal_nat_in_hyperreal⟩

/-- Goldblatt §15.4 (p. 196, "Spilling Out" Phenomenon):
If `x : ℕ → ℝ*` has infinite range, then `{x_n : n ∈ ℕ}` is countably infinite and hence external,
so *every* internal hypersequence `X : ℕ* → ℝ*` extending `x` must take values outside
`Set.range x` at some unlimited hypernatural `N ∈ ℕ* \ ℕ`. -/
theorem internalSeq_spills_outside_infinite_range {x : ℕ → ℝ*} (hInf : (Set.range x).Infinite)
    {X : ℕ* → ℝ*} (hX : IsInternalSeq X) (hext : ∀ n : ℕ, X (n : ℕ*) = x n) :
    ∃ N : ℕ*, IsUnlimitedNat N ∧ X N ∉ Set.range x := by
  rcases hX with ⟨σ, rfl⟩
  have hRange_int : IsInternal (Set.range (internalSeq σ)) := by
    refine ⟨fun i ↦ Set.range (σ i), ?_⟩
    ext y
    rcases ofSeq_surjective y with ⟨r, rfl⟩
    rw [ofSeq_mem_internalSet]
    constructor
    · rintro ⟨N, hN⟩
      induction N using Germ.inductionOn with | _ a =>
      have heq : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), σ i (a i) = r i := Germ.coe_eq.1 hN
      exact heq.mono fun i hi ↦ ⟨a i, hi⟩
    · intro hev
      let a : ℕ → ℕ := fun i ↦ if h : ∃ m : ℕ, σ i m = r i then h.choose else 0
      refine ⟨(a : ℕ*), Germ.coe_eq.2 (hev.mono fun i hi ↦ ?_)⟩
      rw [Set.mem_range] at hi
      have hcho : σ i (hi.choose) = r i := hi.choose_spec
      simp only [a, hi, ↓reduceDIte, hcho]
  by_contra hno
  push Not at hno
  have h_eq : Set.range (internalSeq σ) = Set.range x := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨N, rfl⟩
      rcases Classical.em (IsUnlimitedNat N) with hunl | hlim
      · exact hno N hunl
      · obtain ⟨n, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 hlim
        exact ⟨n, (hext n).symm⟩
    · rintro _ ⟨n, rfl⟩
      exact ⟨(n : ℕ*), hext n⟩
  have hCount : (Set.range (internalSeq σ)).Countable := h_eq ▸ Set.countable_range x
  have hInf' : (Set.range (internalSeq σ)).Infinite := h_eq ▸ hInf
  exact not_countable_infinite_of_isInternal_via_comprehensiveness hRange_int hInf' hCount

/-- Goldblatt §15.4, Theorem 15.4.3 (pp. 197–198, Robinson's Lower Bound for Countably Many
Unlimited Hypernaturals via Comprehensiveness + Overflow):
For any countable set `X ⊆ ℕ*` of unlimited hypernaturals, there exists an unlimited `K ∈ ℕ*`
such that `K < x` for all `x ∈ X`. -/
theorem exists_unlimited_lt_countable_via_comprehensiveness {X : Set ℕ*}
    (hCount : X.Countable) (hunl : ∀ x ∈ X, IsUnlimitedNat x) :
    ∃ K : ℕ*, IsUnlimitedNat K ∧ ∀ x ∈ X, K < x := by
  rcases X.eq_empty_or_nonempty with rfl | hNe
  · exact ⟨omegaNat, isUnlimitedNat_omegaNat, fun _ hx ↦ False.elim hx⟩
  obtain ⟨s, rfl⟩ := hCount.exists_eq_range hNe
  have hs_unl : ∀ n : ℕ, IsUnlimitedNat (s n) := fun n ↦ hunl _ ⟨n, rfl⟩
  have hUniv_int : IsInternalNat (Set.univ : Set ℕ*) := by
    refine ⟨fun _ ↦ Set.univ, ?_⟩
    ext N; induction N using Germ.inductionOn with | _ _ => simp
  obtain ⟨τ, _, hτ_ext⟩ :=
    countable_comprehensiveness_nat_seq hUniv_int s (fun _ ↦ Set.mem_univ _)
  let W : Set ℕ* := {k : ℕ* | ∀ n ≤ k, k < internalGermFun (hyperfilter ℕ) τ n}
  have hW_int : IsInternalNat W := by
    refine ⟨fun i ↦ {m : ℕ | ∀ n ≤ m, m < τ i n}, ?_⟩
    ext k
    induction k using Germ.inductionOn with | _ a =>
    rw [coe_mem_internalNatSet]
    constructor
    · intro hk
      by_contra hnot
      have hbad : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), ∃ n ≤ a i, τ i n ≤ a i := by
        refine (Ultrafilter.eventually_not.2 hnot).mono fun i hi ↦ ?_
        change ¬ ∀ n ≤ a i, a i < τ i n at hi
        push Not at hi
        exact hi
      let nSeq : ℕ → ℕ := fun i ↦
        if h : ∃ n ≤ a i, τ i n ≤ a i then h.choose else 0
      have hn_le : (nSeq : ℕ*) ≤ (a : ℕ*) := by
        refine Germ.coe_le.2 (hbad.mono fun i hi ↦ ?_)
        simpa only [nSeq, hi, ↓reduceDIte] using hi.choose_spec.1
      have hτ_le : internalGermFun (hyperfilter ℕ) τ (nSeq : ℕ*) ≤ (a : ℕ*) := by
        refine Germ.coe_le.2 (hbad.mono fun i hi ↦ ?_)
        simpa only [nSeq, hi, ↓reduceDIte] using hi.choose_spec.2
      exact not_lt_of_ge hτ_le (hk (nSeq : ℕ*) hn_le)
    · intro hev n hn
      induction n using Germ.inductionOn with | _ b =>
      have hle : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), b i ≤ a i := Germ.coe_le.1 hn
      exact Germ.coe_lt.2 ((hev.and hle).mono fun i ⟨hiW, hib⟩ ↦ hiW (b i) hib)
  have hW_nat : ∀ k : ℕ, (k : ℕ*) ∈ W := by
    intro k n hn
    obtain ⟨m, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 (fun h ↦ not_lt_of_ge hn (h k))
    rw [hτ_ext m]
    exact hs_unl m k
  obtain ⟨K, hK_W, hK_unl⟩ :=
    permanence_overflow_arbitrarily_large_nat hW_int (fun k ↦ ⟨k, le_rfl, hW_nat k⟩)
  refine ⟨K, hK_unl, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [← hτ_ext n]
  exact hK_W (n : ℕ*) (hK_unl n).le

/-- Cumulative minimum `cumMin s N = min {s 0, ..., s N}` of a hypersequence `s : ℕ* → ℝ*`
when `s` is internal (and `0` otherwise), used in Exercise 15.4.4. -/
def cumMin (s : ℕ* → ℝ*) : ℕ* → ℝ* :=
  if hs : IsInternalSeq s then
    internalSeq fun i m ↦
      ((Finset.range (m + 1)).image (hs.choose i)).min'
        (Finset.image_nonempty.2 ⟨0, Finset.mem_range.2 (Nat.succ_pos m)⟩)
  else fun _ ↦ 0

/-- If `s : ℕ* → ℝ*` is an internal hypersequence, then its cumulative minimum `cumMin s` is also
an internal hypersequence (`IsInternalSeq (cumMin s)`). -/
theorem IsInternalSeq.cumMin {s : ℕ* → ℝ*} (hs : IsInternalSeq s) :
    IsInternalSeq (Ch15.cumMin s) := by
  dsimp only [Ch15.cumMin]
  rw [dite_eq_left_of_eq_true (eq_true hs)]
  exact ⟨_, rfl⟩

/-- Internal cumulative minimum `T(N) = min {S(0), ..., S(N)}` of an internal sequence of
hypernaturals `S = internalGermFun (hyperfilter ℕ) τ` (Goldblatt §15.4, Exercise 15.4.4, p. 198). -/
def cumMinNat (τ : ℕ → ℕ → ℕ) : ℕ* → ℕ* :=
  internalGermFun (hyperfilter ℕ) fun i m ↦
    ((Finset.range (m + 1)).image (τ i)).min'
      (Finset.image_nonempty.2 ⟨0, Finset.mem_range.2 (Nat.succ_pos m)⟩)

/-- Basic order properties of `cumMinNat τ`:
(1) `cumMinNat τ` is antitone (`M ≤ N → cumMinNat τ N ≤ cumMinNat τ M`),
(2) `k ≤ N → cumMinNat τ N ≤ internalGermFun (hyperfilter ℕ) τ k`,
(3) for each standard `n ∈ ℕ`, `cumMinNat τ (n : ℕ*) = internalGermFun (hyperfilter ℕ) τ (k : ℕ*)`
    for some `k ≤ n`. -/
theorem cumMinNat_properties (τ : ℕ → ℕ → ℕ) :
    Antitone (cumMinNat τ) ∧
    (∀ k N : ℕ*, k ≤ N → cumMinNat τ N ≤ internalGermFun (hyperfilter ℕ) τ k) ∧
    (∀ n : ℕ, ∃ k ≤ n, cumMinNat τ (n : ℕ*) = internalGermFun (hyperfilter ℕ) τ (k : ℕ*)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro M N hMN
    induction M using Germ.inductionOn with | _ a =>
    induction N using Germ.inductionOn with | _ b =>
    refine Germ.coe_le.2 ((Germ.coe_le.1 hMN).mono fun i hle ↦ ?_)
    refine Finset.le_min' _ _ _ fun y hy ↦ ?_
    rcases Finset.mem_image.1 hy with ⟨k, hk, rfl⟩
    refine Finset.min'_le _ _ (Finset.mem_image.2 ⟨k, ?_, rfl⟩)
    rw [Finset.mem_range] at hk ⊢
    omega
  · intro k N hkN
    induction k using Germ.inductionOn with | _ a =>
    induction N using Germ.inductionOn with | _ b =>
    refine Germ.coe_le.2 ((Germ.coe_le.1 hkN).mono fun i hle ↦ ?_)
    refine Finset.min'_le _ _ (Finset.mem_image.2 ⟨a i, ?_, rfl⟩)
    rw [Finset.mem_range]
    omega
  · intro n
    let hne_n : (Finset.range (n + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
    let μ : ℕ → ℕ := fun i ↦
      ((Finset.range (n + 1)).image (τ i)).min' (Finset.image_nonempty.2 hne_n)
    let S_fin : Set ℕ := (Finset.range (n + 1) : Set ℕ)
    have hcov : (⋃ k ∈ S_fin, {i : ℕ | μ i = τ i k}) ∈ hyperfilter ℕ := by
      change (⋃ k ∈ S_fin, {i : ℕ | μ i = τ i k}) ∈ (hyperfilter ℕ : Filter ℕ)
      refine Filter.mem_of_superset Filter.univ_mem fun i _ ↦ ?_
      have hmem := Finset.min'_mem ((Finset.range (n + 1)).image (τ i))
        (Finset.image_nonempty.2 hne_n)
      rcases Finset.mem_image.1 hmem with ⟨k, hk, hk_eq⟩
      exact Set.mem_biUnion (Finset.mem_coe.2 hk) hk_eq.symm
    rw [Ultrafilter.finite_biUnion_mem_iff (Finset.finite_toSet _)] at hcov
    obtain ⟨k, hk, hk_ev⟩ := hcov
    refine ⟨k, Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_coe.1 hk)), Germ.coe_eq.2 hk_ev⟩

/-- Goldblatt §15.4, Exercise 15.4.4 (p. 198):
Alternative proof of Theorem 15.4.3 obtained by applying Robinson's Sequential Lemma 15.2.1
directly to the internal hypersequence `1 / T(N)`, where `T(N) = min {S(0), ..., S(N)}`. -/
theorem exists_unlimited_lt_countable_via_robinson_lemma {X : Set ℕ*}
    (hCount : X.Countable) (hunl : ∀ x ∈ X, IsUnlimitedNat x) :
    ∃ K : ℕ*, IsUnlimitedNat K ∧ ∀ x ∈ X, K < x := by
  rcases X.eq_empty_or_nonempty with rfl | hNe
  · exact ⟨omegaNat, isUnlimitedNat_omegaNat, fun _ hx ↦ False.elim hx⟩
  obtain ⟨s, rfl⟩ := hCount.exists_eq_range hNe
  have hs_unl : ∀ n : ℕ, IsUnlimitedNat (s n) := fun n ↦ hunl _ ⟨n, rfl⟩
  have hUniv_int : IsInternalNat (Set.univ : Set ℕ*) := by
    refine ⟨fun _ ↦ Set.univ, ?_⟩
    ext N; induction N using Germ.inductionOn with | _ _ => simp
  obtain ⟨τ, _, hτ_ext⟩ :=
    countable_comprehensiveness_nat_seq hUniv_int s (fun _ ↦ Set.mem_univ _)
  obtain ⟨hT_anti, hT_le_S, hT_std⟩ := cumMinNat_properties τ
  have hT_std_unl : ∀ n : ℕ, IsUnlimitedNat (cumMinNat τ (n : ℕ*)) := by
    intro n
    obtain ⟨k, _, hk_eq⟩ := hT_std n
    rw [hk_eq, hτ_ext k]
    exact hs_unl k
  -- Ensure `1 ≤ cumMinNat τ N` on an initial unlimited segment so `0⁻¹ = 0` cannot occur:
  let P₁ : Set ℕ* := {N : ℕ* | (1 : ℕ*) ≤ cumMinNat τ N}
  have hP₁_int : IsInternalNat P₁ := by
    refine ⟨fun i ↦ {m : ℕ | 1 ≤ ((Finset.range (m + 1)).image (τ i)).min'
      (Finset.image_nonempty.2 ⟨0, Finset.mem_range.2 (Nat.succ_pos m)⟩)}, ?_⟩
    ext N; induction N using Germ.inductionOn with | _ a =>
    rw [coe_mem_internalNatSet]
    exact ⟨fun h ↦ Germ.coe_le.1 h, fun h ↦ Germ.coe_le.2 h⟩
  have hP₁_nat : ∀ n : ℕ, (n : ℕ*) ∈ P₁ := fun n ↦ (hT_std_unl n 1).le
  obtain ⟨M₀, hM₀_ge1, hM₀_unl⟩ :=
    permanence_overflow_arbitrarily_large_nat hP₁_int (fun k ↦ ⟨k, le_rfl, hP₁_nat k⟩)
  -- Apply Robinson's Sequential Lemma 15.2.1 to `r(N) = (cumMinNat τ N)⁻¹`:
  let r : ℕ* → ℝ* := fun N ↦ (Hypernat.toHyperreal (cumMinNat τ N))⁻¹
  have hr_int : IsInternalSeq r := by
    refine ⟨fun i m ↦
      ((((Finset.range (m + 1)).image (τ i)).min'
        (Finset.image_nonempty.2 ⟨0, Finset.mem_range.2 (Nat.succ_pos m)⟩) : ℕ) : ℝ)⁻¹, ?_⟩
    ext N; induction N using Germ.inductionOn with | _ _ => rfl
  have hr_std : ∀ n : ℕ, IsInfinitesimal (r (n : ℕ*)) := by
    intro n
    have hpos_unl : IsPosUnlimited (Hypernat.toHyperreal (cumMinNat τ (n : ℕ*))) :=
      isUnlimitedNat_iff_isPosUnlimited.1 (hT_std_unl n)
    have hunl_real : IsUnlimited (Hypernat.toHyperreal (cumMinNat τ (n : ℕ*))) := by
      intro m
      exact (hpos_unl m).trans_le (le_abs_self _)
    exact hunl_real.inv_isInfinitesimal
  obtain ⟨M₁, hM₁_unl, hM₁_seg⟩ := robinson_sequential_lemma hr_int hr_std
  let M : ℕ* := min M₀ M₁
  have hM_unl : IsUnlimitedNat M := fun n ↦ lt_min (hM₀_unl n) (hM₁_unl n)
  have hTM_ge1 : (1 : ℕ*) ≤ cumMinNat τ M :=
    hM₀_ge1.trans (hT_anti (min_le_left M₀ M₁))
  have hrM_inf : IsInfinitesimal (r M) := hM₁_seg M (min_le_right M₀ M₁)
  have hTM_pos : (0 : ℝ*) < Hypernat.toHyperreal (cumMinNat τ M) := by
    have h1 : Hypernat.toHyperreal 1 = 1 :=
      Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ by norm_num)
    have hge1 : (1 : ℝ*) ≤ Hypernat.toHyperreal (cumMinNat τ M) := by
      have := Hypernat.toHyperreal_le_iff.2 hTM_ge1
      rwa [h1] at this
    exact lt_of_lt_of_le one_pos hge1
  have hTM_unl : IsUnlimitedNat (cumMinNat τ M) := by
    intro n
    have hε : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := inv_pos.2 (by positivity)
    have hlt_inv := hrM_inf (((n : ℝ) + 1)⁻¹) hε
    have hrM_pos : 0 < r M := inv_pos.2 hTM_pos
    rw [abs_of_pos hrM_pos] at hlt_inv
    have hcast : ((((n : ℝ) + 1)⁻¹ : ℝ) : ℝ*) = ((n : ℝ*) + 1)⁻¹ := by push_cast; rfl
    rw [hcast] at hlt_inv
    have hn1_pos : (0 : ℝ*) < (n : ℝ*) + 1 := by
      have : (0 : ℝ*) ≤ (n : ℝ*) := by exact_mod_cast Nat.zero_le n
      linarith
    have hgt : (n : ℝ*) + 1 < Hypernat.toHyperreal (cumMinNat τ M) :=
      (inv_lt_inv₀ hTM_pos hn1_pos).1 hlt_inv
    have hn_lt : Hypernat.toHyperreal (n : ℕ*) < Hypernat.toHyperreal (cumMinNat τ M) := by
      rw [Hypernat.toHyperreal_natCast]
      linarith
    exact lt_of_not_ge fun hle ↦ not_le_of_gt hn_lt (Hypernat.toHyperreal_le_iff.2 hle)
  -- Take `K = cumMinNat τ M - 1` (predecessor of the unlimited hypernatural `cumMinNat τ M`):
  have hTM_rep : ∃ c : ℕ → ℕ, cumMinNat τ M = (c : ℕ*) := by
    induction (cumMinNat τ M) using Germ.inductionOn with | _ c => exact ⟨c, rfl⟩
  rcases hTM_rep with ⟨c, hc_eq⟩
  rw [hc_eq] at hTM_unl hTM_ge1
  let K : ℕ* := ((fun i ↦ c i - 1) : ℕ*)
  have hK_unl : IsUnlimitedNat K := by
    intro n
    have hgt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), n + 1 < c i :=
      Germ.coe_lt.1 (hTM_unl (n + 1))
    exact Germ.coe_lt.2 (hgt.mono fun i hi ↦ by change n < c i - 1; omega)
  have hK_lt_TM : K < (c : ℕ*) := by
    have hgt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 1 ≤ c i :=
      Germ.coe_le.1 hTM_ge1
    exact Germ.coe_lt.2 (hgt.mono fun i hi ↦ by change c i - 1 < c i; omega)
  refine ⟨K, hK_unl, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hTM_le_sn : (c : ℕ*) ≤ s n := by
    rw [← hc_eq, ← hτ_ext n]
    exact hT_le_S (n : ℕ*) M (hM_unl n).le
  exact lt_of_lt_of_le hK_lt_TM hTM_le_sn

/-! ## §15.5 Universe Embeddings & Equivalence of Countable Saturation and Comprehensiveness -/

/-- Axiom-free formalization of a nonstandard **universe embedding** `*: V(S) ↪ V(*S)`
(Goldblatt §13, §15.4, §15.5, pp. 195–199), bundling the enlargement map `Star`, standard
element embedding `star`, internal set membership `memInt`, internal function application `appInt`,
internal pairing `pairInt`, hypernatural order structure on `Star ℕ`, and the internal set/function
comprehension operations used in Theorems 15.4.2, 15.4.3, and Exercise 15.5.1. -/
structure UniverseEmbedding where
  /-- Enlargement type constructor `T ↦ *T`. -/
  Star : Type → Type
  /-- Standard element embedding `x ↦ *x : T → *T`. -/
  star : {T : Type} → T → Star T
  /-- Injectivity of `star`. -/
  star_injective : ∀ {T : Type}, Function.Injective (@star T)
  /-- Internal membership relation `x ∈_int S` for `x : *T` and `S : *(Set T)`. -/
  memInt : {T : Type} → Star T → Star (Set T) → Prop
  /-- Standard membership transfer `*x ∈_int *A ↔ x ∈ A`. -/
  memInt_star : ∀ {T : Type} (x : T) (A : Set T), memInt (star x) (star A) ↔ x ∈ A
  /-- Nonemptiness transfer `(∃ x : *T, x ∈_int *A) ↔ A.Nonempty`. -/
  extSet_nonempty_star : ∀ {T : Type} (A : Set T), (∃ x : Star T, memInt x (star A)) ↔ A.Nonempty
  /-- Internal function application `g(x)` for `g : *(A → B)` and `x : *A`. -/
  appInt : {A B : Type} → Star (A → B) → Star A → Star B
  /-- Standard application transfer `(*f)(*x) = *(f x)`. -/
  appInt_star : ∀ {A B : Type} (f : A → B) (x : A), appInt (star f) (star x) = star (f x)
  /-- Standard precomposition transfer `(*(· ∘ k) g)(x) = g((*k)(x))`. -/
  appInt_precomp_star : ∀ {A B C : Type} (k : A → B) (g : Star (B → C)) (x : Star A),
    appInt (appInt (star (fun h : B → C ↦ h ∘ k)) g) x = appInt g (appInt (star k) x)
  /-- Linear order on the hypernaturals `Star ℕ`. -/
  instLinearOrderNat : LinearOrder (Star ℕ)
  /-- Order transfer on standard naturals `*m ≤ *n ↔ m ≤ n`. -/
  star_nat_le_iff : ∀ m n : ℕ,
    @LE.le (Star ℕ) instLinearOrderNat.toLE (star m) (star n) ↔ m ≤ n
  /-- End-extension property: every element of `Star ℕ` below `*n` is standard. -/
  end_extension_nat : ∀ (x : Star ℕ) (n : ℕ),
    @LE.le (Star ℕ) instLinearOrderNat.toLE x (star n) → ∃ m : ℕ, m ≤ n ∧ x = star m
  /-- Internal least-number principle on nonempty internal subsets of `Star ℕ`. -/
  least_nat_code : ∀ (S : Star (Set ℕ)), (∃ x : Star ℕ, memInt x S) →
    ∃ m : Star ℕ, memInt m S ∧ ∀ y : Star ℕ, memInt y S →
      @LE.le (Star ℕ) instLinearOrderNat.toLE m y
  /-- Every unlimited hypernatural has a strictly smaller unlimited hypernatural predecessor. -/
  pred_unlimited_nat : ∀ ω : Star ℕ,
    (∀ n : ℕ, @LT.lt (Star ℕ) instLinearOrderNat.toLT (star n) ω) →
    ∃ ω' : Star ℕ,
      (∀ n : ℕ, @LT.lt (Star ℕ) instLinearOrderNat.toLT (star n) ω') ∧
      @LT.lt (Star ℕ) instLinearOrderNat.toLT ω' ω
  /-- Every element of `*T` belongs to `*(Set.univ)`. -/
  memInt_star_univ : ∀ {T : Type} (x : Star T), memInt x (star (Set.univ : Set T))
  /-- Internal complement of an internal set code. -/
  compl_code : {T : Type} → Star (Set T) → Star (Set T)
  /-- Specification of `compl_code`. -/
  memInt_compl : ∀ {T : Type} (x : Star T) (S : Star (Set T)),
    memInt x (compl_code S) ↔ ¬ memInt x S
  /-- Internal binary intersection of internal set codes. -/
  inter_code : {T : Type} → Star (Set T) → Star (Set T) → Star (Set T)
  /-- Specification of `inter_code`. -/
  memInt_inter : ∀ {T : Type} (x : Star T) (S₁ S₂ : Star (Set T)),
    memInt x (inter_code S₁ S₂) ↔ memInt x S₁ ∧ memInt x S₂
  /-- Internal complement of a singleton `{y}ᶜ` in `*T`. -/
  singleton_compl_code : {T : Type} → Star T → Star (Set T)
  /-- Specification of `singleton_compl_code`. -/
  memInt_singleton_compl : ∀ {T : Type} (x y : Star T),
    memInt x (singleton_compl_code y) ↔ x ≠ y
  /-- Internal constant function `x ↦ y` on `*A`. -/
  constFun_code : {A T : Type} → Star T → Star (A → T)
  /-- Specification of `constFun_code`. -/
  appInt_constFun : ∀ {A T : Type} (y : Star T) (x : Star A),
    appInt (constFun_code y) x = y
  /-- Internal point-update of `g : *(A → T)` at `a : *A` with value `y : *T`. -/
  updateFun_code : {A T : Type} → Star (A → T) → Star A → Star T → Star (A → T)
  /-- Point-update value at the updated argument `a`. -/
  appInt_updateFun_eq : ∀ {A T : Type} (g : Star (A → T)) (a : Star A) (y : Star T),
    appInt (updateFun_code g a y) a = y
  /-- Point-update value away from `a`. -/
  appInt_updateFun_ne : ∀ {A T : Type} (g : Star (A → T)) (a : Star A) (y : Star T) (x : Star A),
    x ≠ a → appInt (updateFun_code g a y) x = appInt g x
  /-- Internal comprehension code `{g : *(A → T) | (∀ x, g(x) ∈ Y) ∧ g(*a) = y}`
  (used in Goldblatt Theorem 15.4.2, p. 197). -/
  eval_eq_code : {A T : Type} → Star (Set T) → A → Star T → Star (Set (A → T))
  /-- Specification of `eval_eq_code`. -/
  memInt_eval_eq_code : ∀ {A T : Type} (Y : Star (Set T)) (a : A) (y : Star T)
    (g : Star (A → T)),
    memInt g (eval_eq_code Y a y) ↔
      (∀ x : Star A, memInt (appInt g x) Y) ∧ appInt g (star a) = y
  /-- Internal comprehension code `{N : *ℕ | ∀ k ≤ N, X(N) ∈ 𝒜(k)}`
  (used in Goldblatt Theorem 15.4.2, pp. 197–198). -/
  diag_mem_nat_code : {T : Type} → Star (ℕ → T) → Star (ℕ → Set T) → Star (Set ℕ)
  /-- Specification of `diag_mem_nat_code`. -/
  memInt_diag_mem_nat_code : ∀ {T : Type} (X : Star (ℕ → T)) (𝒜 : Star (ℕ → Set T))
    (N : Star ℕ),
    memInt N (diag_mem_nat_code X 𝒜) ↔
      ∀ k : Star ℕ, @LE.le (Star ℕ) instLinearOrderNat.toLE k N →
        memInt (appInt X N) (appInt 𝒜 k)
  /-- Internal comprehension code `{k : *ℕ | ∀ n ≤ k, k < S(n)}`
  (used in Goldblatt Theorem 15.4.3, p. 197). -/
  diag_lt_nat_code : Star (ℕ → ℕ) → Star (Set ℕ)
  /-- Specification of `diag_lt_nat_code`. -/
  memInt_diag_lt_nat_code : ∀ (S : Star (ℕ → ℕ)) (k : Star ℕ),
    memInt k (diag_lt_nat_code S) ↔
      ∀ n : Star ℕ, @LE.le (Star ℕ) instLinearOrderNat.toLE n k →
        @LT.lt (Star ℕ) instLinearOrderNat.toLT k (appInt S n)
  /-- Internal ordered pair `(a, b) : *(A × B)`. -/
  pairInt : {A B : Type} → Star A → Star B → Star (A × B)
  /-- Internal right-fiber code `{b : *B | (a, b) ∈ R}` of an internal binary relation
  `R : *(Set (A × B))` (used in Exercise 15.5.1, p. 199). -/
  fiber_code : {A B : Type} → Star (Set (A × B)) → Star A → Star (Set B)
  /-- Specification of `fiber_code`. -/
  memInt_fiber_code : ∀ {A B : Type} (R : Star (Set (A × B))) (a : Star A) (b : Star B),
    memInt b (fiber_code R a) ↔ memInt (pairInt a b) R
  /-- Internal reverse-membership binary relation `{(S, x) | x ∈ S}` on `Set T × T`
  (used in Exercise 15.5.1, p. 199). -/
  revMemRel_code : (T : Type) → Star (Set (Set T × T))
  /-- Specification of `revMemRel_code`. -/
  memInt_revMemRel_code : ∀ {T : Type} (S : Star (Set T)) (x : Star T),
    memInt (pairInt S x) (revMemRel_code T) ↔ memInt x S

attribute [instance] UniverseEmbedding.instLinearOrderNat

/-- Finite intersection property on a family of sets `X : I → Set α`: every nonempty finite
subfamily has nonempty intersection (Goldblatt §15.5, p. 198). -/
def HasFIP {I α : Type*} (X : I → Set α) : Prop :=
  ∀ s : Finset I, s.Nonempty → (⋂ i ∈ s, X i).Nonempty

namespace UniverseEmbedding

variable (E : UniverseEmbedding)

/-- External set `{x : *T | x ∈_int S}` corresponding to an internal set code `S : *(Set T)`. -/
def extSet {T : Type} (S : E.Star (Set T)) : Set (E.Star T) :=
  {x : E.Star T | E.memInt x S}

/-- Strict inequality transfer `*m < *n ↔ m < n` on `E.Star ℕ`. -/
theorem star_nat_lt_iff (m n : ℕ) : E.star m < E.star n ↔ m < n := by
  rw [lt_iff_le_not_ge, E.star_nat_le_iff, E.star_nat_le_iff, ← lt_iff_le_not_ge]

/-- Predicate asserting that `ω : E.Star ℕ` is unlimited (`*n < ω` for every `n ∈ ℕ`). -/
def IsUnlimitedStarNat (ω : E.Star ℕ) : Prop :=
  ∀ n : ℕ, E.star n < ω

/-- Goldblatt §15.4 (p. 196): Nontriviality condition `*ℕ ≠ ℕ` (existence of an unlimited
hypernatural in `E.Star ℕ`). -/
def HasNonstandardNat : Prop :=
  ∃ ω : E.Star ℕ, E.IsUnlimitedStarNat ω

/-- If a standard type `T` is empty, then its enlargement `E.Star T` is also empty. -/
theorem isEmpty_star_of_isEmpty {T : Type} [IsEmpty T] : IsEmpty (E.Star T) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨t, _⟩ := (E.extSet_nonempty_star (Set.univ : Set T)).1 ⟨x, E.memInt_star_univ x⟩
  exact isEmptyElim t

/-- **Full Comprehensiveness** (Goldblatt §15.4, p. 195):
For every standard domain `A`, internal set `Y ⊆ *T`, and arbitrary function `f : A → *T` valued
in `Y`, there exists an internal function `g : *(A → T)` mapping `*A` into `Y` such that
`g(*a) = f(a)` for all `a ∈ A`. -/
def IsComprehensive : Prop :=
  ∀ {A T : Type} (Y : E.Star (Set T)) (f : A → E.Star T),
    (∀ a : A, E.memInt (f a) Y) →
    ∃ g : E.Star (A → T),
      (∀ x : E.Star A, E.memInt (E.appInt g x) Y) ∧
      (∀ a : A, E.appInt g (E.star a) = f a)

/-- **Countable Comprehensiveness** (Goldblatt §15.4, p. 196):
Comprehensiveness restricted to countable standard domains `A`. -/
def IsCountablyComprehensive : Prop :=
  ∀ {A T : Type} [Countable A] (Y : E.Star (Set T)) (f : A → E.Star T),
    (∀ a : A, E.memInt (f a) Y) →
    ∃ g : E.Star (A → T),
      (∀ x : E.Star A, E.memInt (E.appInt g x) Y) ∧
      (∀ a : A, E.appInt g (E.star a) = f a)

/-- **Sequential Comprehensiveness** (Goldblatt §15.4, p. 196):
Comprehensiveness for sequences `f : ℕ → *T` (`A = ℕ`). -/
def IsSequentiallyComprehensive : Prop :=
  ∀ {T : Type} (Y : E.Star (Set T)) (f : ℕ → E.Star T),
    (∀ n : ℕ, E.memInt (f n) Y) →
    ∃ g : E.Star (ℕ → T),
      (∀ x : E.Star ℕ, E.memInt (E.appInt g x) Y) ∧
      (∀ n : ℕ, E.appInt g (E.star n) = f n)

/-- **Countable Saturation (Decreasing-Chain Form)** (Goldblatt §11.10 / §15.4, p. 196):
Every decreasing sequence `X_0 ⊇ X_1 ⊇ …` of nonempty internal sets in `*T` has nonempty
intersection `⋂ n, X_n ≠ ∅`. -/
def IsCountablySaturatedDecreasing : Prop :=
  ∀ {T : Type} (X : ℕ → E.Star (Set T)),
    (∀ n : ℕ, (E.extSet (X n)).Nonempty) →
    (∀ n : ℕ, E.extSet (X (n + 1)) ⊆ E.extSet (X n)) →
    (⋂ n : ℕ, E.extSet (X n)).Nonempty

/-- **Countable Saturation (FIP Form)** (Goldblatt §15.5, p. 198):
Every nonempty countable indexed family of internal sets in `*T` with the finite intersection
property has nonempty intersection. -/
def IsCountablySaturated : Prop :=
  ∀ {I T : Type} [Nonempty I] [Countable I] (X : I → E.Star (Set T)),
    HasFIP (fun i ↦ E.extSet (X i)) →
    (⋂ i : I, E.extSet (X i)).Nonempty

/-- Folded internal intersection `S_0 ∩ S_1 ∩ … ∩ S_n` of the first `n + 1` codes of a sequence. -/
def prefixInterCode {T : Type} (X : ℕ → E.Star (Set T)) : ℕ → E.Star (Set T)
  | 0 => X 0
  | n + 1 => E.inter_code (prefixInterCode X n) (X (n + 1))

/-- Membership characterization for `prefixInterCode`. -/
theorem memInt_prefixInterCode {T : Type} (X : ℕ → E.Star (Set T)) (n : ℕ) (x : E.Star T) :
    E.memInt x (E.prefixInterCode X n) ↔ ∀ k ≤ n, E.memInt x (X k) := by
  induction n with
  | zero =>
      simp only [prefixInterCode, Nat.le_zero, forall_eq]
  | succ n ih =>
      rw [prefixInterCode, E.memInt_inter, ih]
      constructor
      · rintro ⟨hprev, hlast⟩ k hk
        rcases Nat.of_le_succ hk with hle | rfl
        · exact hprev k hle
        · exact hlast
      · intro hall
        exact ⟨fun k hk ↦ hall k (Nat.le_succ_of_le hk), hall (n + 1) le_rfl⟩

/-- Equivalence between the FIP form and decreasing-chain form of countable saturation
(Goldblatt §15.5, p. 198). -/
theorem isCountablySaturated_iff_decreasing :
    E.IsCountablySaturated ↔ E.IsCountablySaturatedDecreasing := by
  constructor
  · intro hSat T X hNe hDec
    refine hSat X ?_
    intro s hs
    have hmax_mem : s.max' hs ∈ s := Finset.max'_mem s hs
    obtain ⟨x, hx⟩ := hNe (s.max' hs)
    refine ⟨x, Set.mem_iInter₂.2 fun k hk ↦ ?_⟩
    have hle : k ≤ s.max' hs := Finset.le_max' s k hk
    have hchain : ∀ m d : ℕ, E.extSet (X (m + d)) ⊆ E.extSet (X m) := by
      intro m d
      induction d with
      | zero => simp
      | succ d ih => exact (hDec (m + d)).trans ih
    have heq : s.max' hs = k + (s.max' hs - k) := (Nat.add_sub_of_le hle).symm
    exact hchain k (s.max' hs - k) (heq ▸ hx)
  · intro hDec I T hI hCount X hFIP
    obtain ⟨e, he_surj⟩ := exists_surjective_nat I
    let Y : ℕ → E.Star (Set T) := E.prefixInterCode (fun n ↦ X (e n))
    have hY_ne : ∀ n : ℕ, (E.extSet (Y n)).Nonempty := by
      intro n
      let s : Finset I := (Finset.range (n + 1)).image e
      have hs_ne : s.Nonempty :=
        Finset.image_nonempty.2 ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
      obtain ⟨x, hx⟩ := hFIP s hs_ne
      refine ⟨x, (E.memInt_prefixInterCode _ n x).2 fun k hk ↦ ?_⟩
      have hek_mem : e k ∈ s :=
        Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hk), rfl⟩
      exact (Set.mem_iInter₂.1 hx) (e k) hek_mem
    have hY_dec : ∀ n : ℕ, E.extSet (Y (n + 1)) ⊆ E.extSet (Y n) := by
      intro n x hx
      rw [extSet, Set.mem_ofPred_eq, E.memInt_prefixInterCode] at hx ⊢
      exact fun k hk ↦ hx k (Nat.le_succ_of_le hk)
    obtain ⟨x, hx⟩ := hDec Y hY_ne hY_dec
    refine ⟨x, Set.mem_iInter.2 fun i ↦ ?_⟩
    obtain ⟨n, rfl⟩ := he_surj i
    have hxYn : E.memInt x (Y n) := (Set.mem_iInter.1 hx) n
    exact (E.memInt_prefixInterCode _ n x).1 hxYn n le_rfl

/-- **Overflow** in any `UniverseEmbedding` with `HasNonstandardNat`:
If an internal subset `S : E.Star (Set ℕ)` contains `E.star n` for every `n ∈ ℕ`, then `S`
contains an unlimited hypernatural `ω` (Goldblatt §15.1 / §15.4, p. 191 & p. 197). -/
theorem overflow_nat (hNs : E.HasNonstandardNat) (S : E.Star (Set ℕ))
    (hfin : ∀ n : ℕ, E.memInt (E.star n) S) :
    ∃ ω : E.Star ℕ, E.IsUnlimitedStarNat ω ∧ E.memInt ω S := by
  by_cases hcompl : ∃ x : E.Star ℕ, E.memInt x (E.compl_code S)
  · obtain ⟨m, hm_compl, hm_min⟩ := E.least_nat_code (E.compl_code S) hcompl
    have hm_not : ¬ E.memInt m S := (E.memInt_compl m S).1 hm_compl
    have hm_unl : E.IsUnlimitedStarNat m := by
      intro n
      by_contra hge
      push Not at hge
      obtain ⟨k, _, rfl⟩ := E.end_extension_nat m n hge
      exact hm_not (hfin k)
    obtain ⟨ω', hω'_unl, hω'_lt⟩ := E.pred_unlimited_nat m hm_unl
    have hω'_mem : E.memInt ω' S := by
      by_contra hnot
      exact not_le_of_gt hω'_lt (hm_min ω' ((E.memInt_compl ω' S).2 hnot))
    exact ⟨ω', hω'_unl, hω'_mem⟩
  · obtain ⟨ω₀, hω₀_unl⟩ := hNs
    have hmem : E.memInt ω₀ S := by
      by_contra hnot
      exact hcompl ⟨ω₀, (E.memInt_compl ω₀ S).2 hnot⟩
    exact ⟨ω₀, hω₀_unl, hmem⟩

/-- Full comprehensiveness implies countable comprehensiveness. -/
theorem IsComprehensive.isCountablyComprehensive (h : E.IsComprehensive) :
    E.IsCountablyComprehensive :=
  fun Y f hf ↦ h Y f hf

/-- Goldblatt §15.4 (p. 196): Countable Comprehensiveness and Sequential Comprehensiveness are
equivalent (`A` empty handled via empty-type transfer; `A` nonempty countable reduced to `ℕ` via
surjection/section). -/
theorem isCountablyComprehensive_iff_isSequentiallyComprehensive :
    E.IsCountablyComprehensive ↔ E.IsSequentiallyComprehensive := by
  constructor
  · intro h T Y f hf
    exact h Y f hf
  · intro hSeq A T hCount Y f hf
    rcases isEmpty_or_nonempty A with hEmp | hNe
    · have : IsEmpty (E.Star A) := E.isEmpty_star_of_isEmpty
      refine ⟨E.star isEmptyElim, fun x ↦ isEmptyElim x, fun a ↦ isEmptyElim a⟩
    · obtain ⟨e, he_surj⟩ := exists_surjective_nat A
      let idx : A → ℕ := fun a ↦ (he_surj a).choose
      have hidx_spec : ∀ a : A, e (idx a) = a := fun a ↦ (he_surj a).choose_spec
      obtain ⟨gNat, hgNat_mem, hgNat_ext⟩ :=
        hSeq Y (fun n ↦ f (e n)) (fun n ↦ hf (e n))
      let g : E.Star (A → T) := E.appInt (E.star (fun h : ℕ → T ↦ h ∘ idx)) gNat
      refine ⟨g, fun x ↦ ?_, fun a ↦ ?_⟩
      · dsimp only [g]
        rw [E.appInt_precomp_star]
        exact hgNat_mem (E.appInt (E.star idx) x)
      · dsimp only [g]
        rw [E.appInt_precomp_star, E.appInt_star, hgNat_ext (idx a), hidx_spec a]

/-- Finite-point interpolation in `E.Star (A → T)` (Goldblatt §15.4, Theorem 15.4.2, p. 197):
Given a nonempty countable domain `A` enumerated by `e : ℕ → A` and `f : A → E.Star T` valued in
an internal set `Y`, for every `n ∈ ℕ` there exists `g : E.Star (A → T)` mapping `*A` into `Y`
and agreeing with `f` at `*(e 0), …, *(e n)`. -/
theorem exists_internal_interpolant {A T : Type} (Y : E.Star (Set T))
    (e : ℕ → A) (f : A → E.Star T) (hf : ∀ a : A, E.memInt (f a) Y) (n : ℕ) :
    ∃ g : E.Star (A → T),
      (∀ x : E.Star A, E.memInt (E.appInt g x) Y) ∧
      (∀ k ≤ n, E.appInt g (E.star (e k)) = f (e k)) := by
  induction n with
  | zero =>
      refine ⟨E.updateFun_code (E.constFun_code (f (e 0))) (E.star (e 0)) (f (e 0)),
        fun x ↦ ?_, fun k hk ↦ ?_⟩
      · by_cases hx : x = E.star (e 0)
        · subst hx
          rw [E.appInt_updateFun_eq]
          exact hf (e 0)
        · rw [E.appInt_updateFun_ne _ _ _ _ hx, E.appInt_constFun]
          exact hf (e 0)
      · have hk0 : k = 0 := Nat.le_zero.1 hk
        subst hk0
        exact E.appInt_updateFun_eq _ _ _
  | succ n ih =>
      obtain ⟨g, hg_mem, hg_eq⟩ := ih
      by_cases hseen : ∃ k ≤ n, e (n + 1) = e k
      · obtain ⟨k₀, hk₀_le, hk₀_eq⟩ := hseen
        refine ⟨g, hg_mem, fun k hk ↦ ?_⟩
        rcases Nat.of_le_succ hk with hle | rfl
        · exact hg_eq k hle
        · rw [hk₀_eq, hg_eq k₀ hk₀_le]
      · push Not at hseen
        let g' := E.updateFun_code g (E.star (e (n + 1))) (f (e (n + 1)))
        refine ⟨g', fun x ↦ ?_, fun k hk ↦ ?_⟩
        · by_cases hx : x = E.star (e (n + 1))
          · subst hx
            dsimp only [g']
            rw [E.appInt_updateFun_eq]
            exact hf (e (n + 1))
          · dsimp only [g']
            rw [E.appInt_updateFun_ne _ _ _ _ hx]
            exact hg_mem x
        · rcases Nat.of_le_succ hk with hle | rfl
          · have hne_a : e k ≠ e (n + 1) := (hseen k hle).symm
            have hne_star : E.star (e k) ≠ E.star (e (n + 1)) :=
              fun heq ↦ hne_a (E.star_injective heq)
            dsimp only [g']
            rw [E.appInt_updateFun_ne _ _ _ _ hne_star]
            exact hg_eq k hle
          · exact E.appInt_updateFun_eq _ _ _

/-- Goldblatt §15.4, Theorem 15.4.2 (Direction 1a):
Countable saturation implies `*ℕ \ ℕ ≠ ∅` (`HasNonstandardNat`), by intersecting the decreasing
internal tails `*(Set.Ici (n + 1))`. -/
theorem countableSaturation_implies_hasNonstandardNat
    (hSat : E.IsCountablySaturatedDecreasing) : E.HasNonstandardNat := by
  let U : ℕ → E.Star (Set ℕ) := fun n ↦ E.star (Set.Ici (n + 1))
  let V : ℕ → E.Star (Set ℕ) := E.prefixInterCode U
  have hV_ne : ∀ n : ℕ, (E.extSet (V n)).Nonempty := by
    intro n
    refine ⟨E.star (n + 1), (E.memInt_prefixInterCode U n (E.star (n + 1))).2 fun k hk ↦ ?_⟩
    rw [E.memInt_star]
    exact Set.mem_Ici.2 (by omega)
  have hV_dec : ∀ n : ℕ, E.extSet (V (n + 1)) ⊆ E.extSet (V n) := by
    intro n x hx
    rw [extSet, Set.mem_ofPred_eq, E.memInt_prefixInterCode] at hx ⊢
    exact fun k hk ↦ hx k (Nat.le_succ_of_le hk)
  obtain ⟨ω, hω⟩ := hSat V hV_ne hV_dec
  refine ⟨ω, fun n ↦ ?_⟩
  have hmemVn : E.memInt ω (V n) := (Set.mem_iInter.1 hω) n
  have hmemUn : E.memInt ω (U n) := (E.memInt_prefixInterCode U n ω).1 hmemVn n le_rfl
  by_contra hle
  push Not at hle
  obtain ⟨m, hmn, rfl⟩ := E.end_extension_nat ω n hle
  have hm_ge : n + 1 ≤ m := Set.mem_Ici.1 ((E.memInt_star m (Set.Ici (n + 1))).1 hmemUn)
  omega

/-- Goldblatt §15.4, Theorem 15.4.2 (Direction 1b, p. 197):
Countable saturation implies Countable Comprehensiveness, via intersecting
`E_n = {g : *A → Y | ∀ k ≤ n, g(*a_k) = f(a_k)}`. -/
theorem countableSaturation_implies_countableComprehensiveness
    (hSat : E.IsCountablySaturatedDecreasing) : E.IsCountablyComprehensive := by
  intro A T hCount Y f hf
  rcases isEmpty_or_nonempty A with hEmp | hNe
  · have : IsEmpty (E.Star A) := E.isEmpty_star_of_isEmpty
    exact ⟨E.star isEmptyElim, fun x ↦ isEmptyElim x, fun a ↦ isEmptyElim a⟩
  · obtain ⟨e, he_surj⟩ := exists_surjective_nat A
    let C : ℕ → E.Star (Set (A → T)) := fun k ↦ E.eval_eq_code Y (e k) (f (e k))
    let En : ℕ → E.Star (Set (A → T)) := E.prefixInterCode C
    have hEn_ne : ∀ n : ℕ, (E.extSet (En n)).Nonempty := by
      intro n
      obtain ⟨g, hg_mem, hg_eq⟩ := E.exists_internal_interpolant Y e f hf n
      refine ⟨g, (E.memInt_prefixInterCode C n g).2 fun k hk ↦ ?_⟩
      exact (E.memInt_eval_eq_code Y (e k) (f (e k)) g).2 ⟨hg_mem, hg_eq k hk⟩
    have hEn_dec : ∀ n : ℕ, E.extSet (En (n + 1)) ⊆ E.extSet (En n) := by
      intro n g hg
      rw [extSet, Set.mem_ofPred_eq, E.memInt_prefixInterCode] at hg ⊢
      exact fun k hk ↦ hg k (Nat.le_succ_of_le hk)
    obtain ⟨g, hg⟩ := hSat En hEn_ne hEn_dec
    have hg0 : E.memInt g (C 0) :=
      (E.memInt_prefixInterCode C 0 g).1 ((Set.mem_iInter.1 hg) 0) 0 le_rfl
    have hg_into : ∀ x : E.Star A, E.memInt (E.appInt g x) Y :=
      ((E.memInt_eval_eq_code Y (e 0) (f (e 0)) g).1 hg0).1
    refine ⟨g, hg_into, fun a ↦ ?_⟩
    obtain ⟨n, rfl⟩ := he_surj a
    have hgn : E.memInt g (C n) :=
      (E.memInt_prefixInterCode C n g).1 ((Set.mem_iInter.1 hg) n) n le_rfl
    exact ((E.memInt_eval_eq_code Y (e n) (f (e n)) g).1 hgn).2

/-- Goldblatt §15.4, Theorem 15.4.2 (Direction 2, pp. 197–198):
Sequential Comprehensiveness together with `*ℕ \ ℕ ≠ ∅` (`HasNonstandardNat`) implies Countable
Saturation, by extending a witness sequence `x_n ∈ A_n` and the set sequence `A_n` to internal
`X` and `𝒜` and applying Overflow to `{N ∈ *ℕ | ∀ k ≤ N, X(N) ∈ 𝒜(k)}`. -/
theorem sequentialComprehensiveness_implies_countableSaturation
    (hSeq : E.IsSequentiallyComprehensive) (hNs : E.HasNonstandardNat) :
    E.IsCountablySaturatedDecreasing := by
  intro T A_seq hNe hDec
  have hchain : ∀ m n : ℕ, m ≤ n → E.extSet (A_seq n) ⊆ E.extSet (A_seq m) := by
    intro m n hmn
    have hd : ∃ d : ℕ, n = m + d := ⟨n - m, (Nat.add_sub_of_le hmn).symm⟩
    rcases hd with ⟨d, rfl⟩
    clear hmn
    induction d with
    | zero => simp
    | succ d ih => exact (hDec (m + d)).trans ih
  let x : ℕ → E.Star T := fun n ↦ (hNe n).some
  have hx_mem : ∀ n : ℕ, E.memInt (x n) (A_seq n) := fun n ↦ (hNe n).some_mem
  obtain ⟨X, _, hX_ext⟩ :=
    hSeq (E.star (Set.univ : Set T)) x (fun n ↦ E.memInt_star_univ (x n))
  obtain ⟨𝒜, _, h𝒜_ext⟩ :=
    hSeq (E.star (Set.univ : Set (Set T))) A_seq (fun n ↦ E.memInt_star_univ (A_seq n))
  let W : E.Star (Set ℕ) := E.diag_mem_nat_code X 𝒜
  have hW_fin : ∀ n : ℕ, E.memInt (E.star n) W := by
    intro n
    rw [E.memInt_diag_mem_nat_code]
    intro k hk
    obtain ⟨m, hmn, rfl⟩ := E.end_extension_nat k n hk
    rw [hX_ext n, h𝒜_ext m]
    exact hchain m n hmn (hx_mem n)
  obtain ⟨ω, hω_unl, hω_W⟩ := E.overflow_nat hNs W hW_fin
  refine ⟨E.appInt X ω, Set.mem_iInter.2 fun n ↦ ?_⟩
  have hmem := (E.memInt_diag_mem_nat_code X 𝒜 ω).1 hω_W (E.star n) (hω_unl n).le
  rwa [h𝒜_ext n] at hmem

/-- Goldblatt §15.4, Theorem 15.4.2 (pp. 196–198, **Sequential Comprehensiveness ↔ Countable
Saturation**):
In any nonstandard universe embedding `E`, `(E.IsSequentiallyComprehensive ∧ E.HasNonstandardNat)`
holds if and only if `E.IsCountablySaturated`. -/
theorem sequentialComprehensiveness_iff_countableSaturation :
    (E.IsSequentiallyComprehensive ∧ E.HasNonstandardNat) ↔ E.IsCountablySaturated := by
  rw [E.isCountablySaturated_iff_decreasing]
  constructor
  · rintro ⟨hSeq, hNs⟩
    exact E.sequentialComprehensiveness_implies_countableSaturation hSeq hNs
  · intro hSat
    exact ⟨E.isCountablyComprehensive_iff_isSequentiallyComprehensive.1
      (E.countableSaturation_implies_countableComprehensiveness hSat),
      E.countableSaturation_implies_hasNonstandardNat hSat⟩

/-- Goldblatt §15.4, Theorem 15.4.2 (pp. 196–198, **Countable Comprehensiveness ↔ Countable
Saturation**):
In any nonstandard universe embedding `E`, `(E.IsCountablyComprehensive ∧ E.HasNonstandardNat)`
holds if and only if `E.IsCountablySaturated`. -/
theorem countableComprehensiveness_iff_countableSaturation :
    (E.IsCountablyComprehensive ∧ E.HasNonstandardNat) ↔ E.IsCountablySaturated := by
  rw [E.isCountablyComprehensive_iff_isSequentiallyComprehensive,
    E.sequentialComprehensiveness_iff_countableSaturation]

/-- Goldblatt §15.4, Theorem 15.4.3 (pp. 197–198, Abstract Universe Embedding Form):
In any sequentially comprehensive universe embedding with `*ℕ \ ℕ ≠ ∅`, every countable set
`X ⊆ *ℕ` of unlimited hypernaturals has a strict unlimited lower bound `K < x`. -/
theorem exists_unlimited_lt_countable (hSeq : E.IsSequentiallyComprehensive)
    (hNs : E.HasNonstandardNat) {X : Set (E.Star ℕ)}
    (hCount : X.Countable) (hunl : ∀ x ∈ X, E.IsUnlimitedStarNat x) :
    ∃ K : E.Star ℕ, E.IsUnlimitedStarNat K ∧ ∀ x ∈ X, K < x := by
  rcases X.eq_empty_or_nonempty with rfl | hNe
  · obtain ⟨ω₀, hω₀⟩ := hNs
    exact ⟨ω₀, hω₀, fun _ hx ↦ False.elim hx⟩
  obtain ⟨s, rfl⟩ := hCount.exists_eq_range hNe
  have hs_unl : ∀ n : ℕ, E.IsUnlimitedStarNat (s n) := fun n ↦ hunl _ ⟨n, rfl⟩
  obtain ⟨S, _, hS_ext⟩ :=
    hSeq (E.star (Set.univ : Set ℕ)) s (fun n ↦ E.memInt_star_univ (s n))
  let W : E.Star (Set ℕ) := E.diag_lt_nat_code S
  have hW_fin : ∀ k : ℕ, E.memInt (E.star k) W := by
    intro k
    rw [E.memInt_diag_lt_nat_code]
    intro n hn
    obtain ⟨m, _, rfl⟩ := E.end_extension_nat n k hn
    rw [hS_ext m]
    exact hs_unl m k
  obtain ⟨K, hK_unl, hK_W⟩ := E.overflow_nat hNs W hW_fin
  refine ⟨K, hK_unl, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hlt := (E.memInt_diag_lt_nat_code S K).1 hK_W (E.star n) (hK_unl n).le
  rwa [hS_ext n] at hlt

/-- Goldblatt §15.4 (p. 197, Abstract Uncountability of Infinite Internal Sets):
In any countably saturated universe embedding `E`, no infinite internal set `E.extSet S` is
countable. -/
theorem not_countable_infinite_internal (hSat : E.IsCountablySaturated)
    {T : Type} (S : E.Star (Set T)) (hInf : (E.extSet S).Infinite) :
    ¬ (E.extSet S).Countable := by
  intro hCount
  have hSatDec : E.IsCountablySaturatedDecreasing := E.isCountablySaturated_iff_decreasing.1 hSat
  obtain ⟨x, hx_eq⟩ := hCount.exists_eq_range hInf.nonempty
  let P : ℕ → E.Star (Set T) := fun k ↦ E.inter_code S (E.singleton_compl_code (x k))
  let Q : ℕ → E.Star (Set T) := E.prefixInterCode P
  have hQ_ne : ∀ n : ℕ, (E.extSet (Q n)).Nonempty := by
    intro n
    obtain ⟨y, hyS, hyNot⟩ :=
      (hInf.sdiff (Finset.finite_toSet ((Finset.range (n + 1)).image x))).nonempty
    refine ⟨y, (E.memInt_prefixInterCode P n y).2 fun k hk ↦ ?_⟩
    refine (E.memInt_inter y S (E.singleton_compl_code (x k))).2 ⟨hyS, ?_⟩
    rw [E.memInt_singleton_compl]
    intro heq
    exact hyNot (Finset.mem_coe.2
      (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hk), heq.symm⟩))
  have hQ_dec : ∀ n : ℕ, E.extSet (Q (n + 1)) ⊆ E.extSet (Q n) := by
    intro n y hy
    rw [extSet, Set.mem_ofPred_eq, E.memInt_prefixInterCode] at hy ⊢
    exact fun k hk ↦ hy k (Nat.le_succ_of_le hk)
  obtain ⟨y, hy⟩ := hSatDec Q hQ_ne hQ_dec
  have hyP0 : E.memInt y (P 0) :=
    (E.memInt_prefixInterCode P 0 y).1 ((Set.mem_iInter.1 hy) 0) 0 le_rfl
  have hyS : y ∈ E.extSet S := ((E.memInt_inter y S _).1 hyP0).1
  rw [hx_eq] at hyS
  rcases hyS with ⟨n, rfl⟩
  have hyPn : E.memInt (x n) (P n) :=
    (E.memInt_prefixInterCode P n (x n)).1 ((Set.mem_iInter.1 hy) n) n le_rfl
  have hne : x n ≠ x n :=
    (E.memInt_singleton_compl (x n) (x n)).1 (((E.memInt_inter (x n) S _).1 hyPn).2)
  exact hne rfl

end UniverseEmbedding

/-- Concrete instantiation of `UniverseEmbedding` for the ultrapower `Germ (U : Filter ι)` over
any ultrafilter `U : Ultrafilter ι` (`ι : Type`). -/
def ultrapowerUniverseEmbedding {ι : Type} (U : Ultrafilter ι) : UniverseEmbedding where
  Star T := Germ (U : Filter ι) T
  star x := Germ.const x
  star_injective ha := germ_const_injective U ha
  memInt x S := Germ.LiftRel (· ∈ ·) x S
  memInt_star x A := by
    rw [show (Germ.const x : Germ (U : Filter ι) _) = Germ.ofFun (fun _ ↦ x) from rfl,
      show (Germ.const A : Germ (U : Filter ι) _) = Germ.ofFun (fun _ ↦ A) from rfl,
      Germ.liftRel_coe]
    constructor
    · intro hev
      obtain ⟨_, h⟩ := hev.exists
      exact h
    · intro hx
      exact Eventually.of_forall fun _ ↦ hx
  extSet_nonempty_star A := by
    constructor
    · rintro ⟨x, hx⟩
      induction x using Germ.inductionOn with | _ xSeq =>
      rw [show (Germ.const A : Germ (U : Filter ι) _) = Germ.ofFun (fun _ ↦ A) from rfl,
        Germ.liftRel_coe] at hx
      obtain ⟨i, hi⟩ := hx.exists
      exact ⟨xSeq i, hi⟩
    · rintro ⟨a, ha⟩
      refine ⟨Germ.const a, ?_⟩
      rw [show (Germ.const a : Germ (U : Filter ι) _) = Germ.ofFun (fun _ ↦ a) from rfl,
        show (Germ.const A : Germ (U : Filter ι) _) = Germ.ofFun (fun _ ↦ A) from rfl,
        Germ.liftRel_coe]
      exact Eventually.of_forall fun _ ↦ ha
  appInt g x := Germ.map₂ (fun f a ↦ f a) g x
  appInt_star f x := rfl
  appInt_precomp_star k g x := by
    induction g using Germ.inductionOn with | _ gSeq =>
    induction x using Germ.inductionOn with | _ xSeq =>
    rfl
  instLinearOrderNat := inferInstance
  star_nat_le_iff m n := by
    rw [show (Germ.const m : Germ (U : Filter ι) ℕ) = Germ.ofFun (fun _ ↦ m) from rfl,
      show (Germ.const n : Germ (U : Filter ι) ℕ) = Germ.ofFun (fun _ ↦ n) from rfl,
      Germ.coe_le]
    constructor
    · intro hev
      obtain ⟨_, h⟩ := hev.exists
      exact h
    · intro hle
      exact Eventually.of_forall fun _ ↦ hle
  end_extension_nat x n hle := by
    induction x using Germ.inductionOn with | _ a =>
    rw [show (Germ.const n : Germ (U : Filter ι) ℕ) = Germ.ofFun (fun _ ↦ n) from rfl,
      Germ.coe_le] at hle
    let S_fin : Set ℕ := (Finset.range (n + 1) : Set ℕ)
    have hcov : (⋃ m ∈ S_fin, {i : ι | a i = m}) ∈ U := by
      change (⋃ m ∈ S_fin, {i : ι | a i = m}) ∈ (U : Filter ι)
      refine Filter.mem_of_superset hle fun i hi ↦ ?_
      exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) rfl
    rw [Ultrafilter.finite_biUnion_mem_iff (Finset.finite_toSet _)] at hcov
    obtain ⟨m, hm, hmU⟩ := hcov
    exact ⟨m, Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_coe.1 hm)), Germ.coe_eq.2 hmU⟩
  least_nat_code S hne := by
    induction S using Germ.inductionOn with | _ B =>
    rcases hne with ⟨x₀, hx₀⟩
    induction x₀ using Germ.inductionOn with | _ a₀ =>
    rw [Germ.liftRel_coe] at hx₀
    have hex : ∀ᶠ i in (U : Filter ι), ∃ m : ℕ, m ∈ B i :=
      hx₀.mono fun i hi ↦ ⟨a₀ i, hi⟩
    let mSeq : ι → ℕ := fun i ↦ if h : ∃ m : ℕ, m ∈ B i then Nat.find h else 0
    refine ⟨Germ.ofFun mSeq, ?_, fun y hy ↦ ?_⟩
    · rw [Germ.liftRel_coe]
      refine hex.mono fun i hi ↦ ?_
      have hspec : Nat.find hi ∈ B i := Nat.find_spec hi
      simpa only [mSeq, hi, ↓reduceDIte] using hspec
    · induction y using Germ.inductionOn with | _ b =>
      rw [Germ.liftRel_coe] at hy
      refine Germ.coe_le.2 ((hex.and hy).mono fun i ⟨hi, hbi⟩ ↦ ?_)
      have hmin : Nat.find hi ≤ b i := Nat.find_min' hi hbi
      simpa only [mSeq, hi, ↓reduceDIte] using hmin
  pred_unlimited_nat ω hω := by
    induction ω using Germ.inductionOn with | _ a =>
    refine ⟨Germ.ofFun (fun i ↦ a i - 1), fun n ↦ ?_, ?_⟩
    · have hgt : ∀ᶠ i in (U : Filter ι), n + 1 < a i := Germ.coe_lt.1 (hω (n + 1))
      exact Germ.coe_lt.2 (hgt.mono fun i hi ↦ by change n < a i - 1; omega)
    · have hgt : ∀ᶠ i in (U : Filter ι), 0 < a i := Germ.coe_lt.1 (hω 0)
      exact Germ.coe_lt.2 (hgt.mono fun i hi ↦ by change a i - 1 < a i; omega)
  memInt_star_univ x := by
    induction x using Germ.inductionOn with | _ xSeq =>
    rw [show (Germ.const (Set.univ : Set _) : Germ (U : Filter ι) _) =
      Germ.ofFun (fun _ ↦ Set.univ) from rfl, Germ.liftRel_coe]
    exact Eventually.of_forall fun _ ↦ Set.mem_univ _
  compl_code S := Germ.map compl S
  memInt_compl x S := by
    induction x using Germ.inductionOn with | _ xSeq =>
    induction S using Germ.inductionOn with | _ B =>
    change Germ.LiftRel (· ∈ ·) (Germ.ofFun xSeq) (Germ.ofFun fun i ↦ (B i)ᶜ) ↔
      ¬ Germ.LiftRel (· ∈ ·) (Germ.ofFun xSeq) (Germ.ofFun B)
    rw [Germ.liftRel_coe, Germ.liftRel_coe, ← Ultrafilter.eventually_not]
    rfl
  inter_code S₁ S₂ := Germ.map₂ (· ∩ ·) S₁ S₂
  memInt_inter x S₁ S₂ := by
    induction x using Germ.inductionOn with | _ xSeq =>
    induction S₁ using Germ.inductionOn with | _ B₁ =>
    induction S₂ using Germ.inductionOn with | _ B₂ =>
    change Germ.LiftRel (· ∈ ·) (Germ.ofFun xSeq) (Germ.ofFun fun i ↦ B₁ i ∩ B₂ i) ↔ _
    rw [Germ.liftRel_coe, Germ.liftRel_coe, Germ.liftRel_coe]
    exact Filter.eventually_and
  singleton_compl_code y := Germ.map (fun b ↦ ({b}ᶜ : Set _)) y
  memInt_singleton_compl x y := by
    induction x using Germ.inductionOn with | _ xSeq =>
    induction y using Germ.inductionOn with | _ ySeq =>
    change Germ.LiftRel (· ∈ ·) (Germ.ofFun xSeq) (Germ.ofFun fun i ↦ ({ySeq i}ᶜ : Set _)) ↔ _
    rw [Germ.liftRel_coe, Ne, Germ.coe_eq]
    exact ⟨fun hev heq ↦ by obtain ⟨i, hne, he⟩ := (hev.and heq).exists; exact hne he,
      fun hne ↦ Ultrafilter.eventually_not.2 hne⟩
  constFun_code y := Germ.map (fun b _ ↦ b) y
  appInt_constFun y x := by
    induction y using Germ.inductionOn with | _ _ =>
    induction x using Germ.inductionOn with | _ _ =>
    rfl
  updateFun_code g a y :=
    Germ.map₂ (fun h (p : _ × _) ↦ Function.update h p.1 p.2) g (Germ.map₂ Prod.mk a y)
  appInt_updateFun_eq g a y := by
    induction g using Germ.inductionOn with | _ gSeq =>
    induction a using Germ.inductionOn with | _ aSeq =>
    induction y using Germ.inductionOn with | _ ySeq =>
    refine Germ.coe_eq.2 (Eventually.of_forall fun i ↦ ?_)
    exact Function.update_self (aSeq i) (ySeq i) (gSeq i)
  appInt_updateFun_ne g a y x hne := by
    induction g using Germ.inductionOn with | _ gSeq =>
    induction a using Germ.inductionOn with | _ aSeq =>
    induction y using Germ.inductionOn with | _ ySeq =>
    induction x using Germ.inductionOn with | _ xSeq =>
    have hne_ev : ∀ᶠ i in (U : Filter ι), xSeq i ≠ aSeq i :=
      Ultrafilter.eventually_not.2 fun heq ↦ hne (Germ.coe_eq.2 heq)
    refine Germ.coe_eq.2 (hne_ev.mono fun i hi ↦ ?_)
    exact Function.update_of_ne hi (ySeq i) (gSeq i)
  eval_eq_code Y a y :=
    Germ.map₂ (fun H b ↦ {h | (∀ x, h x ∈ H) ∧ h a = b}) Y y
  memInt_eval_eq_code Y a y g := by
    induction Y using Germ.inductionOn with | _ H =>
    induction y using Germ.inductionOn with | _ ySeq =>
    induction g using Germ.inductionOn with | _ gSeq =>
    change Germ.LiftRel (· ∈ ·) (Germ.ofFun gSeq)
      (Germ.ofFun fun i ↦ {h | (∀ x, h x ∈ H i) ∧ h a = ySeq i}) ↔ _
    rw [Germ.liftRel_coe]
    constructor
    · intro hev
      refine ⟨fun x ↦ ?_, ?_⟩
      · induction x using Germ.inductionOn with | _ xSeq =>
        change Germ.LiftRel (· ∈ ·) (Germ.ofFun fun i ↦ gSeq i (xSeq i)) (Germ.ofFun H)
        rw [Germ.liftRel_coe]
        exact hev.mono fun i hi ↦ hi.1 (xSeq i)
      · exact Germ.coe_eq.2 (hev.mono fun i hi ↦ hi.2)
    · rintro ⟨hall, heq⟩
      have heq' : ∀ᶠ i in (U : Filter ι), gSeq i a = ySeq i := Germ.coe_eq.1 heq
      have hall' : ∀ᶠ i in (U : Filter ι), ∀ x, gSeq i x ∈ H i := by
        by_contra hnot
        have hbad : ∀ᶠ i in (U : Filter ι), ∃ x, gSeq i x ∉ H i := by
          refine (Ultrafilter.eventually_not.2 hnot).mono fun i hi ↦ ?_
          push Not at hi
          exact hi
        obtain ⟨i₀, x₀, _⟩ := hbad.exists
        let xSeq : ι → _ := fun i ↦ if hx : ∃ x, gSeq i x ∉ H i then hx.choose else x₀
        have hx_in : ∀ᶠ i in (U : Filter ι), gSeq i (xSeq i) ∈ H i := by
          have hmem_x : Germ.LiftRel (· ∈ ·) (Germ.ofFun fun i ↦ gSeq i (xSeq i)) (Germ.ofFun H) :=
            hall (Germ.ofFun xSeq)
          exact Germ.liftRel_coe.1 hmem_x
        obtain ⟨i, hi_bad, hi_in⟩ := (hbad.and hx_in).exists
        have hnot_in : gSeq i (hi_bad.choose) ∉ H i := hi_bad.choose_spec
        simp only [xSeq, hi_bad, ↓reduceDIte] at hi_in
        exact hnot_in hi_in
      exact hall'.and heq'
  diag_mem_nat_code X 𝒜 :=
    Germ.map₂ (fun σ B ↦ {m : ℕ | ∀ k ≤ m, σ m ∈ B k}) X 𝒜
  memInt_diag_mem_nat_code X 𝒜 N := by
    induction X using Germ.inductionOn with | _ σ =>
    induction 𝒜 using Germ.inductionOn with | _ B =>
    induction N using Germ.inductionOn with | _ a =>
    change Germ.LiftRel (· ∈ ·) (Germ.ofFun a)
      (Germ.ofFun fun i ↦ {m : ℕ | ∀ k ≤ m, σ i m ∈ B i k}) ↔ _
    rw [Germ.liftRel_coe]
    constructor
    · intro hev k hk
      induction k using Germ.inductionOn with | _ b =>
      change Germ.LiftRel (· ∈ ·) (Germ.ofFun fun i ↦ σ i (a i)) (Germ.ofFun fun i ↦ B i (b i))
      rw [Germ.liftRel_coe]
      exact (hev.and (Germ.coe_le.1 hk)).mono fun i ⟨hi, hba⟩ ↦ hi (b i) hba
    · intro hall
      by_contra hnot
      have hbad : ∀ᶠ i in (U : Filter ι), ∃ k ≤ a i, σ i (a i) ∉ B i k := by
        refine (Ultrafilter.eventually_not.2 hnot).mono fun i hi ↦ ?_
        change ¬ ∀ k ≤ a i, σ i (a i) ∈ B i k at hi
        push Not at hi
        exact hi
      let kSeq : ι → ℕ := fun i ↦
        if h : ∃ k ≤ a i, σ i (a i) ∉ B i k then h.choose else 0
      have hk_le : (Germ.ofFun kSeq : Germ (U : Filter ι) ℕ) ≤ Germ.ofFun a := by
        refine Germ.coe_le.2 (hbad.mono fun i hi ↦ ?_)
        simpa only [kSeq, hi, ↓reduceDIte] using hi.choose_spec.1
      have hmem : ∀ᶠ i in (U : Filter ι), σ i (a i) ∈ B i (kSeq i) := by
        have hmem_k : Germ.LiftRel (· ∈ ·) (Germ.ofFun fun i ↦ σ i (a i))
            (Germ.ofFun fun i ↦ B i (kSeq i)) := hall (Germ.ofFun kSeq) hk_le
        exact Germ.liftRel_coe.1 hmem_k
      obtain ⟨i, hi_bad, hi_in⟩ := (hbad.and hmem).exists
      have hnot_in : σ i (a i) ∉ B i (hi_bad.choose) := hi_bad.choose_spec.2
      simp only [kSeq, hi_bad, ↓reduceDIte] at hi_in
      exact hnot_in hi_in
  diag_lt_nat_code S := Germ.map (fun τ ↦ {m : ℕ | ∀ n ≤ m, m < τ n}) S
  memInt_diag_lt_nat_code S k := by
    induction S using Germ.inductionOn with | _ τ =>
    induction k using Germ.inductionOn with | _ a =>
    change Germ.LiftRel (· ∈ ·) (Germ.ofFun a)
      (Germ.ofFun fun i ↦ {m : ℕ | ∀ n ≤ m, m < τ i n}) ↔ _
    rw [Germ.liftRel_coe]
    constructor
    · intro hev n hn
      induction n using Germ.inductionOn with | _ b =>
      exact Germ.coe_lt.2 ((hev.and (Germ.coe_le.1 hn)).mono fun i ⟨hi, hba⟩ ↦ hi (b i) hba)
    · intro hall
      by_contra hnot
      have hbad : ∀ᶠ i in (U : Filter ι), ∃ n ≤ a i, τ i n ≤ a i := by
        refine (Ultrafilter.eventually_not.2 hnot).mono fun i hi ↦ ?_
        change ¬ ∀ n ≤ a i, a i < τ i n at hi
        push Not at hi
        exact hi
      let nSeq : ι → ℕ := fun i ↦
        if h : ∃ n ≤ a i, τ i n ≤ a i then h.choose else 0
      have hn_le : (Germ.ofFun nSeq : Germ (U : Filter ι) ℕ) ≤ Germ.ofFun a := by
        refine Germ.coe_le.2 (hbad.mono fun i hi ↦ ?_)
        simpa only [nSeq, hi, ↓reduceDIte] using hi.choose_spec.1
      have hlt : ∀ᶠ i in (U : Filter ι), a i < τ i (nSeq i) :=
        Germ.coe_lt.1 (hall (Germ.ofFun nSeq) hn_le)
      obtain ⟨i, hi_bad, hi_lt⟩ := (hbad.and hlt).exists
      have hle : τ i (hi_bad.choose) ≤ a i := hi_bad.choose_spec.2
      simp only [nSeq, hi_bad, ↓reduceDIte] at hi_lt
      exact not_lt_of_ge hle hi_lt
  pairInt a b := Germ.map₂ Prod.mk a b
  fiber_code R a := Germ.map₂ (fun rel x ↦ {b | (x, b) ∈ rel}) R a
  memInt_fiber_code R a b := by
    induction R using Germ.inductionOn with | _ rel =>
    induction a using Germ.inductionOn with | _ aSeq =>
    induction b using Germ.inductionOn with | _ bSeq =>
    change Germ.LiftRel (· ∈ ·) (Germ.ofFun bSeq)
      (Germ.ofFun fun i ↦ {y | (aSeq i, y) ∈ rel i}) ↔
      Germ.LiftRel (· ∈ ·) (Germ.ofFun fun i ↦ (aSeq i, bSeq i)) (Germ.ofFun rel)
    rw [Germ.liftRel_coe, Germ.liftRel_coe]
    rfl
  revMemRel_code T := Germ.const {p : Set T × T | p.2 ∈ p.1}
  memInt_revMemRel_code S x := by
    induction S using Germ.inductionOn with | _ B =>
    induction x using Germ.inductionOn with | _ xSeq =>
    change Germ.LiftRel (· ∈ ·) (Germ.ofFun fun i ↦ (B i, xSeq i))
      (Germ.ofFun fun _ ↦ {p : Set _ × _ | p.2 ∈ p.1}) ↔
      Germ.LiftRel (· ∈ ·) (Germ.ofFun xSeq) (Germ.ofFun B)
    rw [Germ.liftRel_coe, Germ.liftRel_coe]
    rfl

/-- Goldblatt §15.4 (pp. 195–196): For *every* ultrafilter `U : Ultrafilter ι`, the ultrapower
universe embedding `ultrapowerUniverseEmbedding U` is **fully comprehensive** (even without
requiring countable incompleteness!). -/
theorem ultrapowerUniverseEmbedding_isComprehensive {ι : Type} (U : Ultrafilter ι) :
    (ultrapowerUniverseEmbedding U).IsComprehensive := by
  intro A T Y f hf
  change Germ (U : Filter ι) (Set T) at Y
  induction Y using Germ.inductionOn with | _ H =>
  obtain ⟨F, hF_mem, hF_ext⟩ := ultrapower_comprehensive U H f hf
  exact ⟨Germ.ofFun F, hF_mem, hF_ext⟩

/-- For any countably incomplete ultrafilter `U : Ultrafilter ι`, `ultrapowerUniverseEmbedding U`
satisfies `HasNonstandardNat`. -/
theorem ultrapowerUniverseEmbedding_hasNonstandardNat {ι : Type} (U : Ultrafilter ι)
    (hU : IsCountablyIncomplete U) :
    (ultrapowerUniverseEmbedding U).HasNonstandardNat := by
  obtain ⟨ω, hω⟩ := exists_unlimited_germ_of_isCountablyIncomplete U hU
  exact ⟨ω, hω⟩

/-- Goldblatt §15.4, Theorem 15.4.2 + Ultrapower Comprehensiveness:
Every ultrapower over a countably incomplete ultrafilter `U : Ultrafilter ι` is **countably
saturated** (`IsCountablySaturated`). -/
theorem ultrapowerUniverseEmbedding_isCountablySaturated {ι : Type} (U : Ultrafilter ι)
    (hU : IsCountablyIncomplete U) :
    (ultrapowerUniverseEmbedding U).IsCountablySaturated := by
  rw [← (ultrapowerUniverseEmbedding U).countableComprehensiveness_iff_countableSaturation]
  exact ⟨UniverseEmbedding.IsComprehensive.isCountablyComprehensive _
      (ultrapowerUniverseEmbedding_isComprehensive U),
    ultrapowerUniverseEmbedding_hasNonstandardNat U hU⟩

/-- The canonical hyperreal universe embedding over `hyperfilter ℕ`. -/
def hyperrealUniverseEmbedding : UniverseEmbedding :=
  ultrapowerUniverseEmbedding (hyperfilter ℕ)

/-- `hyperrealUniverseEmbedding` is both fully comprehensive and countably saturated. -/
theorem hyperrealUniverseEmbedding_comprehensive_and_saturated :
    hyperrealUniverseEmbedding.IsComprehensive ∧
    hyperrealUniverseEmbedding.IsCountablySaturated :=
  ⟨ultrapowerUniverseEmbedding_isComprehensive (hyperfilter ℕ),
   ultrapowerUniverseEmbedding_isCountablySaturated (hyperfilter ℕ)
     isCountablyIncomplete_hyperfilter_nat⟩

/-- Standalone countable saturation (decreasing-chain form) on `ℕ*`. -/
theorem countable_saturation_nat_decreasing {X : ℕ → Set ℕ*}
    (hInt : ∀ n : ℕ, IsInternalNat (X n))
    (hNe : ∀ n : ℕ, (X n).Nonempty)
    (hDec : ∀ n : ℕ, X (n + 1) ⊆ X n) :
    (⋂ n : ℕ, X n).Nonempty := by
  have hSat : hyperrealUniverseEmbedding.IsCountablySaturatedDecreasing :=
    hyperrealUniverseEmbedding.isCountablySaturated_iff_decreasing.1
      hyperrealUniverseEmbedding_comprehensive_and_saturated.2
  choose B hB using hInt
  let S : ℕ → hyperrealUniverseEmbedding.Star (Set ℕ) := fun n ↦ Germ.ofFun (B n)
  have h_eq : ∀ n : ℕ, hyperrealUniverseEmbedding.extSet (S n) = X n := by
    intro n
    rw [hB n]
    rfl
  have hNe' : ∀ n : ℕ, (hyperrealUniverseEmbedding.extSet (S n)).Nonempty :=
    fun n ↦ (h_eq n).symm ▸ hNe n
  have hDec' : ∀ n : ℕ,
      hyperrealUniverseEmbedding.extSet (S (n + 1)) ⊆ hyperrealUniverseEmbedding.extSet (S n) :=
    fun n ↦ by rw [h_eq (n + 1), h_eq n]; exact hDec n
  obtain ⟨ω, hω⟩ := hSat S hNe' hDec'
  refine ⟨ω, Set.mem_iInter.2 fun n ↦ ?_⟩
  rw [← h_eq n]
  exact (Set.mem_iInter.1 hω) n

/-- Standalone countable saturation (FIP form) on `ℕ*`. -/
theorem countable_saturation_nat_fip {I : Type} [Nonempty I] [Countable I]
    {X : I → Set ℕ*} (hInt : ∀ i : I, IsInternalNat (X i)) (hFIP : HasFIP X) :
    (⋂ i : I, X i).Nonempty := by
  have hSat : hyperrealUniverseEmbedding.IsCountablySaturated :=
    hyperrealUniverseEmbedding_comprehensive_and_saturated.2
  choose B hB using hInt
  let S : I → hyperrealUniverseEmbedding.Star (Set ℕ) := fun i ↦ Germ.ofFun (B i)
  have h_eq : ∀ i : I, hyperrealUniverseEmbedding.extSet (S i) = X i := fun i ↦ by
    rw [hB i]; rfl
  have hFIP' : HasFIP (fun i ↦ hyperrealUniverseEmbedding.extSet (S i)) := by
    intro s hs
    obtain ⟨ω, hω⟩ := hFIP s hs
    refine ⟨ω, Set.mem_iInter₂.2 fun i hi ↦ ?_⟩
    change ω ∈ hyperrealUniverseEmbedding.extSet (S i)
    rw [h_eq i]
    exact (Set.mem_iInter₂.1 hω) i hi
  obtain ⟨ω, hω⟩ := hSat S hFIP'
  refine ⟨ω, Set.mem_iInter.2 fun i ↦ ?_⟩
  rw [← h_eq i]
  exact (Set.mem_iInter.1 hω) i

/-- Standalone countable saturation (FIP form) on `ℝ*` for arbitrary nonempty countable index types
`I` (generalizing `countable_saturation_fip` on `ℕ`). -/
theorem countable_saturation_hyperreal_fip {I : Type} [Nonempty I] [Countable I]
    {X : I → Set ℝ*} (hInt : ∀ i : I, IsInternal (X i)) (hFIP : HasFIP X) :
    (⋂ i : I, X i).Nonempty := by
  have hSat : hyperrealUniverseEmbedding.IsCountablySaturated :=
    hyperrealUniverseEmbedding_comprehensive_and_saturated.2
  choose B hB using hInt
  let S : I → hyperrealUniverseEmbedding.Star (Set ℝ) := fun i ↦ Germ.ofFun (B i)
  have h_eq : ∀ i : I, hyperrealUniverseEmbedding.extSet (S i) = X i := fun i ↦ by
    rw [hB i]; rfl
  have hFIP' : HasFIP (fun i ↦ hyperrealUniverseEmbedding.extSet (S i)) := by
    intro s hs
    obtain ⟨x, hx⟩ := hFIP s hs
    refine ⟨x, Set.mem_iInter₂.2 fun i hi ↦ ?_⟩
    change x ∈ hyperrealUniverseEmbedding.extSet (S i)
    rw [h_eq i]
    exact (Set.mem_iInter₂.1 hx) i hi
  obtain ⟨x, hx⟩ := hSat S hFIP'
  refine ⟨x, Set.mem_iInter.2 fun i ↦ ?_⟩
  rw [← h_eq i]
  exact (Set.mem_iInter.1 hx) i

/-- Concrete Theorem 15.4.2 on `ℝ*` (Countable Saturation ⇒ Sequential Comprehensiveness,
derived directly via `hyperrealUniverseEmbedding` without directly calling
`ultrapower_comprehensive`). -/
theorem countable_comprehensiveness_seq_via_saturation {Y : Set ℝ*} (hY : IsInternal Y)
    (x : ℕ → ℝ*) (hx : ∀ m : ℕ, x m ∈ Y) :
    ∃ X : ℕ* → ℝ*, IsInternalSeq X ∧ (∀ N : ℕ*, X N ∈ Y) ∧ (∀ m : ℕ, X (m : ℕ*) = x m) := by
  rcases hY with ⟨B, rfl⟩
  have hSatDec : hyperrealUniverseEmbedding.IsCountablySaturatedDecreasing :=
    hyperrealUniverseEmbedding.isCountablySaturated_iff_decreasing.1
      hyperrealUniverseEmbedding_comprehensive_and_saturated.2
  have hComp : hyperrealUniverseEmbedding.IsCountablyComprehensive :=
    hyperrealUniverseEmbedding.countableSaturation_implies_countableComprehensiveness hSatDec
  obtain ⟨g, hg_mem, hg_ext⟩ := hComp (Germ.ofFun B) x hx
  change Germ (hyperfilter ℕ : Filter ℕ) (ℕ → ℝ) at g
  induction g using Germ.inductionOn with | _ σ =>
  exact ⟨internalSeq σ, ⟨σ, rfl⟩, hg_mem, hg_ext⟩

/-- Concrete Theorem 15.4.2 on `ℝ*` (Sequential Comprehensiveness + Overflow ⇒ Countable
Saturation of decreasing internal subsets of `ℝ*`). -/
theorem countable_saturation_decreasing_via_comprehensiveness {X : ℕ → Set ℝ*}
    (hInt : ∀ n : ℕ, IsInternal (X n))
    (hNe : ∀ n : ℕ, (X n).Nonempty)
    (hDec : ∀ n : ℕ, X (n + 1) ⊆ X n) :
    (⋂ n : ℕ, X n).Nonempty := by
  have hSeq : hyperrealUniverseEmbedding.IsCountablyComprehensive :=
    UniverseEmbedding.IsComprehensive.isCountablyComprehensive _
      (ultrapowerUniverseEmbedding_isComprehensive (hyperfilter ℕ))
  have hSatDec : hyperrealUniverseEmbedding.IsCountablySaturatedDecreasing :=
    hyperrealUniverseEmbedding.sequentialComprehensiveness_implies_countableSaturation
      (fun Y f hf ↦ hSeq Y f hf)
      (ultrapowerUniverseEmbedding_hasNonstandardNat (hyperfilter ℕ)
        isCountablyIncomplete_hyperfilter_nat)
  choose B hB using hInt
  let S : ℕ → hyperrealUniverseEmbedding.Star (Set ℝ) := fun n ↦ Germ.ofFun (B n)
  have h_eq : ∀ n : ℕ, hyperrealUniverseEmbedding.extSet (S n) = X n := fun n ↦ by
    rw [hB n]; rfl
  obtain ⟨y, hy⟩ := hSatDec S (fun n ↦ (h_eq n).symm ▸ hNe n)
    (fun n ↦ by rw [h_eq (n + 1), h_eq n]; exact hDec n)
  refine ⟨y, Set.mem_iInter.2 fun n ↦ ?_⟩
  rw [← h_eq n]
  exact (Set.mem_iInter.1 hy) n

/-! ## §15.6 `κ`-Saturation, `ℵ₁`-Saturation, Concurrent Relations, and Cardinality Bounds -/

namespace UniverseEmbedding

variable (E : UniverseEmbedding)

/-- Goldblatt §15.5 (p. 198): A universe embedding `E` is **`κ`-saturated** (`κ : Cardinal`) if
every nonempty collection of fewer than `κ` internal sets with the finite intersection property has
nonempty intersection. -/
def IsKappaSaturated (κ : Cardinal) : Prop :=
  ∀ {I T : Type} [Nonempty I], #I < κ → ∀ (X : I → E.Star (Set T)),
    HasFIP (fun i ↦ E.extSet (X i)) →
    (⋂ i : I, E.extSet (X i)).Nonempty

/-- Goldblatt §15.5 (p. 198): "Countably saturated" is equivalent to "`ℵ₁`-saturated", where `ℵ₁`
is the least uncountable cardinal (`#I < ℵ₁ ↔ #I ≤ ℵ₀ ↔ Countable I`). -/
theorem isCountablySaturated_iff_aleph_one_saturated :
    E.IsCountablySaturated ↔ E.IsKappaSaturated ℵ₁ := by
  constructor
  · intro hCountSat I T hI hlt X hFIP
    have hle : #I ≤ ℵ₀ := Cardinal.lt_aleph_one_iff.1 hlt
    have : Countable I := Cardinal.mk_le_aleph0_iff.1 hle
    exact hCountSat X hFIP
  · intro hAleph1 I T hI hCount X hFIP
    have hlt : #I < ℵ₁ := Cardinal.lt_aleph_one_iff.2 (Cardinal.mk_le_aleph0_iff.2 hCount)
    exact hAleph1 hlt X hFIP

/-- Monotonicity of `κ`-saturation: if `κ₁ ≤ κ₂` and `E` is `κ₂`-saturated, then `E` is
`κ₁`-saturated. -/
theorem IsKappaSaturated.mono {κ₁ κ₂ : Cardinal} (hle : κ₁ ≤ κ₂)
    (hSat : E.IsKappaSaturated κ₂) : E.IsKappaSaturated κ₁ :=
  fun hlt X hFIP ↦ hSat (hlt.trans_le hle) X hFIP

/-- External domain `{a : *A | ∃ b : *B, (a, b) ∈_int R}` of an internal binary relation
`R : E.Star (Set (A × B))`. -/
def relDomInt {A B : Type} (R : E.Star (Set (A × B))) : Set (E.Star A) :=
  {a : E.Star A | ∃ b : E.Star B, E.memInt (E.pairInt a b) R}

/-- External range `{b : *B | ∃ a : *A, (a, b) ∈_int R}` of an internal binary relation
`R : E.Star (Set (A × B))`. -/
def relRangeInt {A B : Type} (R : E.Star (Set (A × B))) : Set (E.Star B) :=
  {b : E.Star B | ∃ a : E.Star A, E.memInt (E.pairInt a b) R}

/-- An internal binary relation `R : E.Star (Set (A × B))` is **concurrent on** a subset
`S_dom ⊆ E.Star A` (`S_dom` need not be internal!) if for every nonempty finite subset
`F ⊆ S_dom` there exists `b : E.Star B` such that `(a, b) ∈_int R` for all `a ∈ F`
(Goldblatt §15.5, Exercise 15.5.1, p. 199). -/
def IsConcurrentOnInt {A B : Type} (R : E.Star (Set (A × B))) (S_dom : Set (E.Star A)) : Prop :=
  ∀ F : Finset (E.Star A), F.Nonempty → (F : Set (E.Star A)) ⊆ S_dom →
    ∃ b : E.Star B, ∀ a ∈ F, E.memInt (E.pairInt a b) R

/-- Goldblatt §15.5, Exercise 15.5.1 (p. 199):
A universe embedding `E` is `κ`-saturated **if and only if** for every internal binary relation `R`
and every nonempty subset `S_dom` of `E.relDomInt R` with `#S_dom < κ` (`S_dom` need not be
internal), if `R` is concurrent on `S_dom`, then there exists an entity `b ∈ E.relRangeInt R`
such that `(a, b) ∈_int R` for all `a ∈ S_dom`. -/
theorem isKappaSaturated_iff_concurrent (κ : Cardinal) :
    E.IsKappaSaturated κ ↔
      ∀ {A B : Type} (R : E.Star (Set (A × B))) (S_dom : Set (E.Star A)),
        S_dom.Nonempty → S_dom ⊆ E.relDomInt R → #S_dom < κ →
        E.IsConcurrentOnInt R S_dom →
        ∃ b ∈ E.relRangeInt R, ∀ a ∈ S_dom, E.memInt (E.pairInt a b) R := by
  constructor
  · intro hSat A B R S_dom hNe _ hCard hConc
    have : Nonempty S_dom := hNe.to_subtype
    let X : S_dom → E.Star (Set B) := fun a ↦ E.fiber_code R a.1
    have hFIP : HasFIP (fun a : S_dom ↦ E.extSet (X a)) := by
      intro s hs
      let F : Finset (E.Star A) := s.image Subtype.val
      have hF_ne : F.Nonempty := Finset.image_nonempty.2 hs
      have hF_sub : (F : Set (E.Star A)) ⊆ S_dom := by
        intro x hx
        rcases Finset.mem_image.1 (Finset.mem_coe.1 hx) with ⟨a, _, rfl⟩
        exact a.2
      obtain ⟨b, hb⟩ := hConc F hF_ne hF_sub
      refine ⟨b, Set.mem_iInter₂.2 fun a ha ↦ ?_⟩
      change E.memInt b (E.fiber_code R a.1)
      rw [E.memInt_fiber_code]
      exact hb a.1 (Finset.mem_image.2 ⟨a, ha, rfl⟩)
    obtain ⟨b, hb⟩ := hSat hCard X hFIP
    have hall : ∀ a ∈ S_dom, E.memInt (E.pairInt a b) R := by
      intro a ha
      have hmem : b ∈ E.extSet (X ⟨a, ha⟩) := (Set.mem_iInter.1 hb) ⟨a, ha⟩
      exact (E.memInt_fiber_code R a b).1 hmem
    obtain ⟨a₀, ha₀⟩ := hNe
    exact ⟨b, ⟨a₀, hall a₀ ha₀⟩, hall⟩
  · intro hConcProp I T hI hlt X hFIP
    let R : E.Star (Set (Set T × T)) := E.revMemRel_code T
    let S_dom : Set (E.Star (Set T)) := Set.range X
    obtain ⟨i₀⟩ := hI
    have hNe : S_dom.Nonempty := ⟨X i₀, i₀, rfl⟩
    have hSub : S_dom ⊆ E.relDomInt R := by
      rintro _ ⟨i, rfl⟩
      obtain ⟨x, hx⟩ := hFIP {i} (Finset.singleton_nonempty i)
      have hx_mem : x ∈ E.extSet (X i) := (Set.mem_iInter₂.1 hx) i (Finset.mem_singleton_self i)
      exact ⟨x, (E.memInt_revMemRel_code (X i) x).2 hx_mem⟩
    have hCard : #S_dom < κ := Cardinal.mk_range_le.trans_lt hlt
    have hConc : E.IsConcurrentOnInt R S_dom := by
      intro F hF_ne hF_sub
      let idx : E.Star (Set T) → I := fun S ↦
        if h : ∃ i : I, X i = S then h.choose else i₀
      let s : Finset I := F.image idx
      have hs_ne : s.Nonempty := Finset.image_nonempty.2 hF_ne
      obtain ⟨b, hb⟩ := hFIP s hs_ne
      refine ⟨b, fun S hSF ↦ ?_⟩
      have hS_in : S ∈ S_dom := hF_sub (Finset.mem_coe.2 hSF)
      rw [Set.mem_range] at hS_in
      have hidx_eq : X (idx S) = S := by
        simpa only [idx, hS_in, ↓reduceDIte] using hS_in.choose_spec
      have hidx_mem : idx S ∈ s := Finset.mem_image.2 ⟨S, hSF, rfl⟩
      have hb_mem : E.memInt b (X (idx S)) := (Set.mem_iInter₂.1 hb) (idx S) hidx_mem
      rw [hidx_eq] at hb_mem
      exact (E.memInt_revMemRel_code S b).2 hb_mem
    obtain ⟨b, _, hb_all⟩ := hConcProp R S_dom hNe hSub hCard hConc
    refine ⟨b, Set.mem_iInter.2 fun i ↦ ?_⟩
    exact (E.memInt_revMemRel_code (X i) b).1 (hb_all (X i) ⟨i, rfl⟩)

/-- Goldblatt §15.5 (p. 198, Cardinality Lower Bound for Infinite Internal Sets):
In any `κ`-saturated universe embedding `E`, every infinite internal set `Y = E.extSet S` has
cardinality at least `κ` (`κ ≤ #Y`). -/
theorem card_infinite_internal_ge_of_kappaSaturated {κ : Cardinal}
    (hSat : E.IsKappaSaturated κ) {T : Type} (S : E.Star (Set T))
    (hInf : (E.extSet S).Infinite) :
    κ ≤ #(E.extSet S) := by
  by_contra hlt
  push Not at hlt
  let Y : Set (E.Star T) := E.extSet S
  have : Nonempty Y := hInf.nonempty.to_subtype
  let Z : Y → E.Star (Set T) := fun y ↦ E.inter_code S (E.singleton_compl_code y.1)
  have hFIP : HasFIP (fun y : Y ↦ E.extSet (Z y)) := by
    intro s _
    let F_val : Finset (E.Star T) := s.image Subtype.val
    obtain ⟨x, hxY, hxNot⟩ := (hInf.sdiff (Finset.finite_toSet F_val)).nonempty
    refine ⟨x, Set.mem_iInter₂.2 fun y hy ↦ ?_⟩
    change E.memInt x (E.inter_code S (E.singleton_compl_code y.1))
    rw [E.memInt_inter, E.memInt_singleton_compl]
    refine ⟨hxY, fun heq ↦ hxNot ?_⟩
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨y, hy, heq.symm⟩)
  obtain ⟨x, hx⟩ := hSat hlt Z hFIP
  obtain ⟨y₀, hy₀⟩ := hInf.nonempty
  have hx0 : E.memInt x (Z ⟨y₀, hy₀⟩) := (Set.mem_iInter.1 hx) ⟨y₀, hy₀⟩
  have hxY : x ∈ Y := ((E.memInt_inter x S _).1 hx0).1
  have hxx : E.memInt x (Z ⟨x, hxY⟩) := (Set.mem_iInter.1 hx) ⟨x, hxY⟩
  have hne : x ≠ x := (E.memInt_singleton_compl x x).1 (((E.memInt_inter x S _).1 hxx).2)
  exact hne rfl

end UniverseEmbedding

/-- Goldblatt §15.5 (p. 198): Every ultrapower over a countably incomplete ultrafilter `U` is
`ℵ₁`-saturated. -/
theorem aleph_one_saturated_ultrapower {ι : Type} (U : Ultrafilter ι)
    (hU : IsCountablyIncomplete U) :
    (ultrapowerUniverseEmbedding U).IsKappaSaturated ℵ₁ :=
  (ultrapowerUniverseEmbedding U).isCountablySaturated_iff_aleph_one_saturated.1
    (ultrapowerUniverseEmbedding_isCountablySaturated U hU)

/-- `κ`-saturation predicate for internal subsets of `ℝ*` (`κ : Cardinal`). -/
def IsKappaSaturatedHyperreal (κ : Cardinal) : Prop :=
  ∀ {I : Type} [Nonempty I], #I < κ → ∀ (X : I → Set ℝ*),
    (∀ i : I, IsInternal (X i)) → HasFIP X → (⋂ i : I, X i).Nonempty

/-- Equivalence on `ℝ*` between countable FIP saturation and `ℵ₁`-saturation. -/
theorem countable_saturation_hyperreal_iff_aleph_one_saturated :
    (∀ {I : Type} [Nonempty I] [Countable I] (X : I → Set ℝ*),
      (∀ i : I, IsInternal (X i)) → HasFIP X → (⋂ i : I, X i).Nonempty) ↔
    IsKappaSaturatedHyperreal ℵ₁ := by
  constructor
  · intro hCountSat I hI hlt X hInt hFIP
    have : Countable I := Cardinal.mk_le_aleph0_iff.1 (Cardinal.lt_aleph_one_iff.1 hlt)
    exact hCountSat X hInt hFIP
  · intro hAleph1 I hI hCount X hInt hFIP
    exact hAleph1 (Cardinal.lt_aleph_one_iff.2 (Cardinal.mk_le_aleph0_iff.2 hCount)) X hInt hFIP

/-- Goldblatt §15.5 (p. 198): `ℝ*` (constructed over `hyperfilter ℕ`) is **`ℵ₁`-saturated**. -/
theorem aleph_one_saturated_hyperreal : IsKappaSaturatedHyperreal ℵ₁ :=
  countable_saturation_hyperreal_iff_aleph_one_saturated.1
    fun _ hInt hFIP ↦ countable_saturation_hyperreal_fip hInt hFIP

/-- Internal binary relation `[P_i] ⊆ ℝ* × ℝ*` represented by `P : ℕ → Set (ℝ × ℝ)`. -/
def internalRel₂ (P : ℕ → Set (ℝ × ℝ)) : Set (ℝ* × ℝ*) :=
  {q : ℝ* × ℝ* | Germ.LiftRel (· ∈ ·)
    (Germ.map₂ Prod.mk q.1 q.2) (Germ.ofFun P : Germ (hyperfilter ℕ : Filter ℕ) (Set (ℝ × ℝ)))}

/-- Predicate asserting that `R ⊆ ℝ* × ℝ*` is an internal binary relation on `ℝ*`. -/
def IsInternalRel₂ (R : Set (ℝ* × ℝ*)) : Prop :=
  ∃ P : ℕ → Set (ℝ × ℝ), R = internalRel₂ P

/-- Membership characterization for `internalRel₂` on `(ofSeq r, ofSeq s)`. -/
@[simp]
theorem ofSeq_mem_internalRel₂ {P : ℕ → Set (ℝ × ℝ)} {r s : ℕ → ℝ} :
    (ofSeq r, ofSeq s) ∈ internalRel₂ P ↔
      ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (r i, s i) ∈ P i :=
  Germ.liftRel_coe

/-- Every right fiber `{y : ℝ* | (a, y) ∈ R}` of an internal binary relation `R ⊆ ℝ* × ℝ*` is an
internal subset of `ℝ*`. -/
theorem IsInternalRel₂.fiber_right {R : Set (ℝ* × ℝ*)} (hR : IsInternalRel₂ R) (a : ℝ*) :
    IsInternal {y : ℝ* | (a, y) ∈ R} := by
  rcases hR with ⟨P, rfl⟩
  rcases ofSeq_surjective a with ⟨r, rfl⟩
  refine ⟨fun i ↦ {y : ℝ | (r i, y) ∈ P i}, ?_⟩
  ext y
  rcases ofSeq_surjective y with ⟨s, rfl⟩
  rw [Set.mem_ofPred_eq, ofSeq_mem_internalRel₂, ofSeq_mem_internalSet]
  rfl

/-- Every left fiber `{x : ℝ* | (x, b) ∈ R}` of an internal binary relation `R ⊆ ℝ* × ℝ*` is an
internal subset of `ℝ*`. -/
theorem IsInternalRel₂.fiber_left {R : Set (ℝ* × ℝ*)} (hR : IsInternalRel₂ R) (b : ℝ*) :
    IsInternal {x : ℝ* | (x, b) ∈ R} := by
  rcases hR with ⟨P, rfl⟩
  rcases ofSeq_surjective b with ⟨s, rfl⟩
  refine ⟨fun i ↦ {x : ℝ | (x, s i) ∈ P i}, ?_⟩
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  rw [Set.mem_ofPred_eq, ofSeq_mem_internalRel₂, ofSeq_mem_internalSet]
  rfl

/-- Concurrency of a binary relation `R ⊆ ℝ* × ℝ*` on a subset `A ⊆ ℝ*` (`A` need not be
internal). -/
def IsConcurrentOnRel₂ (R : Set (ℝ* × ℝ*)) (A : Set ℝ*) : Prop :=
  ∀ F : Finset ℝ*, F.Nonempty → (F : Set ℝ*) ⊆ A → ∃ b : ℝ*, ∀ a ∈ F, (a, b) ∈ R

/-- Goldblatt §15.5, Exercise 15.5.1 on `ℝ* × ℝ*` (p. 199):
`ℝ*` is `ℵ₁`-saturated **if and only if** for every internal binary relation `R ⊆ ℝ* × ℝ*`
(`IsInternalRel₂ R`) and every nonempty subset `A ⊆ Prod.fst '' R` with `#A < ℵ₁` (`A` need not
be internal), if `R` is concurrent on `A`, then there exists `b ∈ Prod.snd '' R` such that
`(a, b) ∈ R` for all `a ∈ A`. -/
theorem countable_saturation_hyperreal_iff_concurrent_internalRel₂ :
    IsKappaSaturatedHyperreal ℵ₁ ↔
      ∀ (R : Set (ℝ* × ℝ*)), IsInternalRel₂ R →
        ∀ (A : Set ℝ*), A.Nonempty → A ⊆ Prod.fst '' R → #A < ℵ₁ →
          IsConcurrentOnRel₂ R A →
          ∃ b ∈ Prod.snd '' R, ∀ a ∈ A, (a, b) ∈ R := by
  constructor
  · intro hSat R hR A hNe _ hlt hConc
    have : Nonempty A := hNe.to_subtype
    let X : A → Set ℝ* := fun a ↦ {y : ℝ* | (a.1, y) ∈ R}
    have hInt : ∀ a : A, IsInternal (X a) := fun a ↦ hR.fiber_right a.1
    have hFIP : HasFIP X := by
      intro s hs
      let F : Finset ℝ* := s.image Subtype.val
      have hF_ne : F.Nonempty := Finset.image_nonempty.2 hs
      have hF_sub : (F : Set ℝ*) ⊆ A := by
        intro x hx
        rcases Finset.mem_image.1 (Finset.mem_coe.1 hx) with ⟨a, _, rfl⟩
        exact a.2
      obtain ⟨b, hb⟩ := hConc F hF_ne hF_sub
      refine ⟨b, Set.mem_iInter₂.2 fun a ha ↦ ?_⟩
      exact hb a.1 (Finset.mem_image.2 ⟨a, ha, rfl⟩)
    obtain ⟨b, hb⟩ := hSat hlt X hInt hFIP
    have hall : ∀ a ∈ A, (a, b) ∈ R := fun a ha ↦ (Set.mem_iInter.1 hb) ⟨a, ha⟩
    obtain ⟨a₀, ha₀⟩ := hNe
    exact ⟨b, ⟨(a₀, b), hall a₀ ha₀, rfl⟩, hall⟩
  · intro hConcProp I hI hlt X hInt hFIP
    have : Countable I := Cardinal.mk_le_aleph0_iff.1 (Cardinal.lt_aleph_one_iff.1 hlt)
    obtain ⟨e, he_surj⟩ := exists_surjective_nat I
    choose B hB using hInt
    -- Encode the countable family `(X (e m))_{m ∈ ℕ}` as fibers of an internal relation on `ℝ* × ℝ*`:
    let P : ℕ → Set (ℝ × ℝ) := fun i ↦
      {q : ℝ × ℝ | ∃ m : ℕ, q.1 = (m : ℝ) ∧ q.2 ∈ B (e m) i}
    let R : Set (ℝ* × ℝ*) := internalRel₂ P
    have hR_int : IsInternalRel₂ R := ⟨P, rfl⟩
    have hfiber : ∀ m : ℕ, ∀ y : ℝ*, ((m : ℝ*), y) ∈ R ↔ y ∈ X (e m) := by
      intro m y
      rcases ofSeq_surjective y with ⟨s, rfl⟩
      have hm_eq : (m : ℝ*) = ofSeq (fun _ ↦ (m : ℝ)) := rfl
      rw [hm_eq, ofSeq_mem_internalRel₂, hB (e m), ofSeq_mem_internalSet]
      constructor
      · refine fun hev ↦ hev.mono fun i hi ↦ ?_
        rcases hi with ⟨k, hk_eq, hk_mem⟩
        have hkm : m = k := Nat.cast_injective hk_eq
        rwa [hkm]
      · exact fun hev ↦ hev.mono fun i hi ↦ ⟨m, rfl, hi⟩
    let A : Set ℝ* := Set.range (Nat.cast : ℕ → ℝ*)
    have hA_ne : A.Nonempty := ⟨((0 : ℕ) : ℝ*), 0, rfl⟩
    have hA_sub : A ⊆ Prod.fst '' R := by
      rintro _ ⟨m, rfl⟩
      obtain ⟨y, hy⟩ := hFIP {e m} (Finset.singleton_nonempty (e m))
      have hy_mem : y ∈ X (e m) := (Set.mem_iInter₂.1 hy) (e m) (Finset.mem_singleton_self _)
      exact ⟨((m : ℝ*), y), (hfiber m y).2 hy_mem, rfl⟩
    have hA_lt : #A < ℵ₁ :=
      Cardinal.lt_aleph_one_iff.2 (Cardinal.mk_le_aleph0_iff.2 (Set.countable_range _))
    have hConc : IsConcurrentOnRel₂ R A := by
      intro F hF_ne hF_sub
      let natIdx : ℝ* → ℕ := fun a ↦
        if h : ∃ m : ℕ, (m : ℝ*) = a then h.choose else 0
      let s : Finset I := F.image (fun a ↦ e (natIdx a))
      have hs_ne : s.Nonempty := Finset.image_nonempty.2 hF_ne
      obtain ⟨b, hb⟩ := hFIP s hs_ne
      refine ⟨b, fun a haF ↦ ?_⟩
      have haA : a ∈ A := hF_sub (Finset.mem_coe.2 haF)
      rw [Set.mem_range] at haA
      have hcast : ((natIdx a : ℕ) : ℝ*) = a := by
        simpa only [natIdx, haA, ↓reduceDIte] using haA.choose_spec
      have hmem_s : e (natIdx a) ∈ s := Finset.mem_image.2 ⟨a, haF, rfl⟩
      have hb_mem : b ∈ X (e (natIdx a)) := (Set.mem_iInter₂.1 hb) (e (natIdx a)) hmem_s
      rw [← hcast]
      exact (hfiber (natIdx a) b).2 hb_mem
    obtain ⟨b, _, hb_all⟩ := hConcProp R hR_int A hA_ne hA_sub hA_lt hConc
    refine ⟨b, Set.mem_iInter.2 fun i ↦ ?_⟩
    obtain ⟨m, rfl⟩ := he_surj i
    exact (hfiber m b).1 (hb_all (m : ℝ*) ⟨m, rfl⟩)

/-- Goldblatt §15.5 (p. 198): If `ℝ*` satisfies `IsKappaSaturatedHyperreal κ`, then every infinite
internal set `Y ⊆ ℝ*` has cardinality `κ ≤ #Y`. -/
theorem card_infinite_internal_hyperreal_ge_of_kappaSaturated {κ : Cardinal}
    (hSat : IsKappaSaturatedHyperreal κ) {Y : Set ℝ*} (hY : IsInternal Y) (hInf : Y.Infinite) :
    κ ≤ #Y := by
  by_contra hlt
  push Not at hlt
  have : Nonempty Y := hInf.nonempty.to_subtype
  let Z : Y → Set ℝ* := fun y ↦ Y \ {y.1}
  have hZ_int : ∀ y : Y, IsInternal (Z y) :=
    fun y ↦ hY.sdiff (isInternal_singleton y.1)
  have hFIP : HasFIP Z := by
    intro s _
    let F_val : Finset ℝ* := s.image Subtype.val
    obtain ⟨x, hxY, hxNot⟩ := (hInf.sdiff (Finset.finite_toSet F_val)).nonempty
    refine ⟨x, Set.mem_iInter₂.2 fun y hy ↦ ⟨hxY, fun h_eq ↦ hxNot ?_⟩⟩
    rw [Set.mem_singleton_iff] at h_eq
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨y, hy, h_eq.symm⟩)
  obtain ⟨x, hx⟩ := hSat hlt Z hZ_int hFIP
  obtain ⟨y₀, hy₀⟩ := hInf.nonempty
  have hxY : x ∈ Y := ((Set.mem_iInter.1 hx) ⟨y₀, hy₀⟩).1
  have hxx : x ∈ Z ⟨x, hxY⟩ := (Set.mem_iInter.1 hx) ⟨x, hxY⟩
  exact hxx.2 rfl

/-- Every infinite internal subset `Y ⊆ ℝ*` has cardinality at least `ℵ₁` (and is therefore
uncountable). -/
theorem card_infinite_internal_hyperreal_ge_aleph_one {Y : Set ℝ*}
    (hY : IsInternal Y) (hInf : Y.Infinite) :
    ℵ₁ ≤ #Y :=
  card_infinite_internal_hyperreal_ge_of_kappaSaturated aleph_one_saturated_hyperreal hY hInf

/-- Goldblatt §15.4 (p. 197): Every unlimited hypernatural `K ∈ ℕ*` has uncountably many
hypernaturals strictly greater than it (`{n ∈ ℕ* | K < n}` is uncountable). -/
theorem uncountable_hypernat_gt_of_unlimited (K : ℕ*) :
    ¬ {n : ℕ* | K < n}.Countable := by
  let S : hyperrealUniverseEmbedding.Star (Set ℕ) :=
    Germ.map (fun m ↦ {n : ℕ | m < n}) K
  have h_eq : hyperrealUniverseEmbedding.extSet S = {n : ℕ* | K < n} := by
    ext n
    induction K using Germ.inductionOn with | _ a =>
    induction n using Germ.inductionOn with | _ b =>
    change Germ.LiftRel (· ∈ ·) (Germ.ofFun b) (Germ.ofFun fun i ↦ {m : ℕ | a i < m}) ↔ _
    rw [Germ.liftRel_coe]
    exact ⟨fun h ↦ Germ.coe_lt.2 h, fun h ↦ Germ.coe_lt.1 h⟩
  have hInf : {n : ℕ* | K < n}.Infinite := by
    have hinj : Function.Injective (fun k : ℕ ↦ K + (k + 1 : ℕ*)) := by
      intro k₁ k₂ heq
      induction K using Germ.inductionOn with | _ a =>
      have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), a i + (k₁ + 1) = a i + (k₂ + 1) :=
        Germ.coe_eq.1 heq
      obtain ⟨i, hi⟩ := hev.exists
      omega
    refine Set.infinite_of_injective_forall_mem hinj fun k ↦ ?_
    induction K using Germ.inductionOn with | _ a =>
    exact Germ.coe_lt.2 (Eventually.of_forall fun i ↦ by change a i < a i + (k + 1); omega)
  rw [← h_eq] at hInf ⊢
  exact hyperrealUniverseEmbedding.not_countable_infinite_internal
    hyperrealUniverseEmbedding_comprehensive_and_saturated.2 S hInf

/-- Goldblatt §15.4 (p. 197): Every unlimited hypernatural `K ∈ ℕ*` has uncountably many
**unlimited** hypernaturals strictly less than it (`{n ∈ ℕ* | IsUnlimitedNat n ∧ n < K}` is
uncountable). -/
theorem uncountable_unlimited_hypernat_lt_of_unlimited {K : ℕ*} (hK : IsUnlimitedNat K) :
    ¬ {n : ℕ* | IsUnlimitedNat n ∧ n < K}.Countable := by
  intro hCount
  let S : hyperrealUniverseEmbedding.Star (Set ℕ) :=
    Germ.map (fun m ↦ {n : ℕ | n < m}) K
  have h_eq : hyperrealUniverseEmbedding.extSet S = {n : ℕ* | n < K} := by
    ext n
    induction K using Germ.inductionOn with | _ a =>
    induction n using Germ.inductionOn with | _ b =>
    change Germ.LiftRel (· ∈ ·) (Germ.ofFun b) (Germ.ofFun fun i ↦ {m : ℕ | m < a i}) ↔ _
    rw [Germ.liftRel_coe]
    exact ⟨fun h ↦ Germ.coe_lt.2 h, fun h ↦ Germ.coe_lt.1 h⟩
  have hInf : {n : ℕ* | n < K}.Infinite := by
    refine Set.infinite_of_injective_forall_mem
      (germ_const_injective (hyperfilter ℕ)) fun m ↦ hK m
  have hUncount : ¬ {n : ℕ* | n < K}.Countable := by
    rw [← h_eq] at hInf ⊢
    exact hyperrealUniverseEmbedding.not_countable_infinite_internal
      hyperrealUniverseEmbedding_comprehensive_and_saturated.2 S hInf
  have hDecomp : {n : ℕ* | n < K} =
      Set.range (Nat.cast : ℕ → ℕ*) ∪ {n : ℕ* | IsUnlimitedNat n ∧ n < K} := by
    ext n
    constructor
    · intro hn
      rcases Classical.em (IsUnlimitedNat n) with hunl | hlim
      · exact Or.inr ⟨hunl, hn⟩
      · obtain ⟨m, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 hlim
        exact Or.inl ⟨m, rfl⟩
    · rintro (⟨m, rfl⟩ | ⟨_, hn⟩)
      · exact hK m
      · exact hn
  exact hUncount (hDecomp ▸ (Set.countable_range _).union hCount)

/-- Exact cardinality of the hyperreal line `ℝ*` constructed as `Germ (hyperfilter ℕ) ℝ`:
`#(ℝ*) = 𝔠` (`Cardinal.continuum`). -/
theorem card_hyperreal_eq_continuum : #(ℝ*) = Cardinal.continuum := by
  refine le_antisymm ?_ ?_
  · have hsurj : Function.Surjective (ofSeq : (ℕ → ℝ) → ℝ*) := ofSeq_surjective
    calc #(ℝ*)
        ≤ #(ℕ → ℝ) := Cardinal.mk_le_of_surjective hsurj
      _ = Cardinal.continuum ^ ℵ₀ := by
          rw [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.lift_id,
            Cardinal.mk_real, Cardinal.mk_nat]
      _ = Cardinal.continuum := Cardinal.continuum_power_aleph0
  · have hinj : Function.Injective ((↑) : ℝ → ℝ*) :=
      fun _ _ h ↦ Hyperreal.coe_eq_coe.1 h
    calc Cardinal.continuum
        = #ℝ := Cardinal.mk_real.symm
      _ ≤ #(ℝ*) := Cardinal.mk_le_of_injective hinj

/-- Exact cardinality of `ℝ*` written as `2 ^ ℵ₀`. -/
theorem card_hyperreal_eq_two_power_aleph0 : #(ℝ*) = 2 ^ ℵ₀ := by
  rw [card_hyperreal_eq_continuum, Cardinal.two_power_aleph0]

/-- Goldblatt §15.5 (p. 198, Punctured Hyperreals Example):
The uncountable collection `{ℝ* \ {r} : r ∈ ℝ*}` consists of internal sets, satisfies the finite
intersection property (`HasFIP`), and yet has **empty** intersection `⋂ r : ℝ*, ({r}ᶜ) = ∅`. -/
theorem punctured_hyperreal_fip_empty_iInter :
    (∀ r : ℝ*, IsInternal ({r}ᶜ : Set ℝ*)) ∧
    HasFIP (fun r : ℝ* ↦ ({r}ᶜ : Set ℝ*)) ∧
    (⋂ r : ℝ*, ({r}ᶜ : Set ℝ*)) = ∅ := by
  refine ⟨fun r ↦ (isInternal_singleton r).compl, ?_, ?_⟩
  · intro s _
    have hInf_univ : (Set.univ : Set ℝ*).Infinite := by
      refine Set.infinite_of_injective_forall_mem
        (fun _ _ h ↦ Hyperreal.coe_eq_coe.1 h) fun _ ↦ Set.mem_univ _
    obtain ⟨x, _, hxNot⟩ := (hInf_univ.sdiff (Finset.finite_toSet s)).nonempty
    refine ⟨x, Set.mem_iInter₂.2 fun r hr heq ↦ hxNot ?_⟩
    rw [Set.mem_singleton_iff] at heq
    exact Finset.mem_coe.2 (heq ▸ hr)
  · ext x
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_forall, not_not]
    exact ⟨x, rfl⟩

/-- Goldblatt §15.5 (p. 198, Failure of `(2 ^ ℵ₀)⁺`-Saturation on `ℝ*`):
Because `#(ℝ*) = 2 ^ ℵ₀ < Order.succ (2 ^ ℵ₀)` and `{ℝ* \ {r} : r ∈ ℝ*}` has FIP with empty
intersection, the sequence ultrapower `ℝ*` is **not** `(2 ^ ℵ₀)⁺`-saturated! -/
theorem not_succ_continuum_saturated_hyperreal :
    ¬ IsKappaSaturatedHyperreal (Order.succ (2 ^ ℵ₀)) := by
  intro hSat
  obtain ⟨hInt, hFIP, hEmpty⟩ := punctured_hyperreal_fip_empty_iInter
  have hlt : #(ℝ*) < Order.succ (2 ^ ℵ₀) := by
    rw [card_hyperreal_eq_two_power_aleph0]
    exact Order.lt_succ (2 ^ ℵ₀)
  obtain ⟨x, hx⟩ := hSat hlt (fun r : ℝ* ↦ ({r}ᶜ : Set ℝ*)) hInt hFIP
  rw [hEmpty] at hx
  exact hx

end Goldblatt.Ch15
end
