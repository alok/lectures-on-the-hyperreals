import LecturesOnTheHyperreals.Ch12_InternalFunctions
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Chapter 17: Ramsey Theory (Goldblatt, *Lectures on the Hyperreals*, pp. 221–230)

This module formalizes Chapter 17 of Robert Goldblatt's *Lectures on the Hyperreals:
An Introduction to Nonstandard Analysis* (GTM 188, Springer, 1998), developing Ramsey theory
via the ultrapower construction `ℕ* = Germ (hyperfilter ℕ) ℕ` and nonstandard enlargement.

## Overview of Contents

* **§17.1 Colourings, Monochromatic Sets, and Small Ramsey Examples** (pp. 221–222):
  * `rSubsets r X` (`[X]^r = {s : Finset α | s.card = r ∧ ↑s ⊆ X}`), monotonicity, and agreement
    with `Finset.powersetCard` (`mem_rSubsets_coe_iff_mem_powersetCard`).
  * `IsMonochromatic r c H color` and `IsMonochromaticSet r c H` for `k`-colourings.
  * Infinite pigeonhole principles (`finite_of_subset_iUnion_finite`,
    `infinite_exists_infinite_inter_of_subset_iUnion`,
    `exists_infinite_monochromatic_of_point_colouring`).
  * Finite `r = 1` pigeonhole (`finite_ramsey_r_one`) and the **Party Problem `R(3, 3) = 6`**:
    every `2`-colouring of edges of `Fin 6` has a monochromatic triangle (`ramsey_three_three_six`),
    the pentagon `2`-colouring on `Fin 5` has no monochromatic triangle
    (`pentagonColouring_no_mono_triangle`), and the exact Ramsey threshold characterization
    (`ramsey_number_three_three`).

* **§17.2 A Nonstandard Approach: Cofinality on `ℕ*`, Ultrafilter Colour Selection & Posets**
  (pp. 223–225):
  * Nonstandard cofinality lemma (`unlimited_mem_starNatSet_cofinal`,
    `omegaNat_mem_starNatSet_exists_gt`, `omegaNat_mem_starNatSet_infinite`): if an unlimited
    hypernatural (such as `omegaNat`) belongs to `starNatSet A`, then `A` is unbounded in `ℕ` and
    infinite.
  * Boolean and finite-intersection algebra of `starNatSet` (`starNatSet_biInter_finset`).
  * Canonical collapse `germConstEquiv : β ≃ Germ (hyperfilter ℕ) β` for finite `β` and nonstandard
    evaluation `starNatFinFun c omegaNat` (`*c(omegaNat)`), picking out the unique colour `i : Fin k`
    such that `omegaNat ∈ starNatSet {n | c n = i}` (`existsUnique_colour_omegaNat`).
  * Iterative witness sequence construction (`exists_strictMono_in_set_of_omegaNat_mem`,
    `exists_strictMono_of_finset_omegaNat`).
  * **Theorem 17.1.1 (Direct Nonstandard Proof, §17.2, p. 223)**: Every infinite partially ordered
    set contains an infinite strictly increasing sequence, an infinite strictly decreasing sequence,
    or an infinite antichain (`infinite_poset_chain_or_antichain_nonstandard`), proved by adjoining
    `⊥` and `⊤`, choosing a nonstandard `π ∈ *P`, and analyzing `L = {p < π}`, `U = {p > π}`, and
    `M = {q_l < p < q_u}`.

* **§17.3 Nonstandard Proof of Infinite Ramsey's Theorem & Corollaries** (pp. 224–227):
  * **Exercise 17.3.1** (`rSubsetsOfStar_eq_starRSubsets` & `rSubsetsOfStarNat_eq_starRSubsetsNat`,
    p. 225): `[*A]^r = *([A]^r)` for all `r : ℕ`.
  * Standard colour-reduction lemma from `2`-colourings to `k`-colourings
    (`ramsey_colour_reduction`, p. 224).
  * Induced colouring `inducedColouring c s = *(fun n ↦ c (insert n s))(omegaNat)`,
    `omegaNat`-stabilized sequence construction (`exists_stabilized_seq_omegaNat`, pp. 225–227), and
    **Theorem 17.3.1 (`infinite_ramsey` & `infinite_ramsey_set`)**: Infinite Ramsey's Theorem for
    all `r ≥ 0`, `k ≥ 1`, and infinite sets.
  * Corollaries:
    * **Theorem 17.1.1 (Ramsey Proof, §17.1, p. 222)**:
      `infinite_poset_chain_or_antichain_via_ramsey`.
    * **Erdős–Szekeres Monotone Subsequence Theorem** (`exists_monotone_subseq_linearOrder`,
      `exists_monotone_subseq`).
    * **Bolzano–Weierstrass Theorem** (`exists_convergent_subseq_of_bdd`) deduced from
      `exists_monotone_subseq`.

* **§17.4 Nonstandard Proof of the Finite Ramsey Theorem & Exercise 17.4.1** (pp. 227–228):
  * **Theorem 17.4.1 (`finite_ramsey`, `finite_ramsey_Icc_one`, `finite_ramsey_fin`)**: Finite
    Ramsey's Theorem deduced from Infinite Ramsey's Theorem via ultrapower compactness.
  * **Exercise 17.4.1 (`psiRamsey`, `starPsiRamsey`, `starPsiRamsey_coe_iff`,
    `starPsiRamsey_omegaNat`, `exists_starPsiRamsey_iff_exists_psiRamsey`)**: Explicit internal
    formula `*ψ(N)` on `ℕ*`, proof at `N = omegaNat` via Infinite Ramsey, and existential transfer.

* **§17.5 The Paris–Harrington Version** (pp. 228–229):
  * Relatively large finite sets `IsRelativelyLarge M` (`M.Nonempty` and `M.min' _ ≤ M.card`).
  * Extraction of arbitrarily large subsets with `|B| = min(B) ≥ m` from any infinite `D ⊆ ℕ`
    (`exists_relativelyLarge_subset_of_infinite`, p. 228).
  * **Paris–Harrington Partition Theorem (`paris_harrington_ramsey`,
    `paris_harrington_ramsey_exact`, `starPsiParisHarrington_omegaNat`)**: Nonstandard proof via
    Infinite Ramsey and ultrapower transfer, plus deduction of Finite Ramsey
    (`paris_harrington_implies_finite_ramsey`).
-/

noncomputable section

namespace Goldblatt.Ch17

open Filter
open Hyperreal (ofSeq ofSeq_lt_ofSeq ofSeq_le_ofSeq ofSeq_surjective)
open scoped Topology

/-!
## §17.1 — Colourings, Monochromatic Sets, and Concrete Small Ramsey Examples (pp. 221–222)
-/

/-- Goldblatt §17.1 (p. 222): The collection `[X]^r` of all `r`-element finite subsets of `X ⊆ α`,
represented as `{s : Finset α | s.card = r ∧ (↑s : Set α) ⊆ X}`. -/
def rSubsets {α : Type*} (r : ℕ) (X : Set α) : Set (Finset α) :=
  {s : Finset α | s.card = r ∧ (↑s : Set α) ⊆ X}

/-- Membership characterization for `rSubsets r X` (`[X]^r`, Goldblatt §17.1, p. 222). -/
@[simp]
theorem mem_rSubsets {α : Type*} {r : ℕ} {X : Set α} {s : Finset α} :
    s ∈ rSubsets r X ↔ s.card = r ∧ (↑s : Set α) ⊆ X :=
  Iff.rfl

/-- Goldblatt §17.1 (p. 222): Monotonicity of `r`-subsets (`B ⊆ A → [B]^r ⊆ [A]^r`). -/
theorem rSubsets_mono {α : Type*} (r : ℕ) {X Y : Set α} (hXY : X ⊆ Y) :
    rSubsets r X ⊆ rSubsets r Y :=
  fun _ ⟨hcard, hsub⟩ ↦ ⟨hcard, hsub.trans hXY⟩

/-- On a `Finset` `S`, `rSubsets r (↑S : Set α)` coincides with `S.powersetCard r`
(Goldblatt §17.1, p. 222). -/
theorem mem_rSubsets_coe_iff_mem_powersetCard {α : Type*} [DecidableEq α]
    {r : ℕ} {S s : Finset α} :
    s ∈ rSubsets r (↑S : Set α) ↔ s ∈ S.powersetCard r := by
  rw [mem_rSubsets, Finset.mem_powersetCard, Finset.coe_subset, and_comm]

/-- `[X]^0 = {∅}` for every set `X` (Goldblatt §17.1, p. 222). -/
@[simp]
theorem rSubsets_zero {α : Type*} (X : Set α) :
    rSubsets 0 X = ({∅} : Set (Finset α)) := by
  ext s
  simp only [rSubsets, Set.mem_ofPred_eq, Finset.card_eq_zero, Set.mem_singleton_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, by simp [h]⟩⟩

/-- `s ∈ [X]^1` iff `s = {x}` for some `x ∈ X` (Goldblatt §17.1, p. 224). -/
theorem mem_rSubsets_one_iff {α : Type*} {X : Set α} {s : Finset α} :
    s ∈ rSubsets 1 X ↔ ∃ x ∈ X, s = {x} := by
  constructor
  · rintro ⟨hcard, hsub⟩
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hcard
    exact ⟨x, hsub (Finset.mem_coe.2 (Finset.mem_singleton_self x)), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Finset.card_singleton x, by simpa using hx⟩

/-- Goldblatt §17.1 (p. 222): A subset `H ⊆ α` is **monochromatic of colour `color`** with respect
to `r : ℕ` and a `k`-colouring `c : Finset α → Fin k` if every `r`-element subset `s` of `H` has
`c s = color`. -/
def IsMonochromatic {α : Type*} (r : ℕ) {k : ℕ} (c : Finset α → Fin k)
    (H : Set α) (color : Fin k) : Prop :=
  ∀ s ∈ rSubsets r H, c s = color

/-- Goldblatt §17.1 (p. 222): A subset `H ⊆ α` is **monochromatic** for `r` and `c` if there exists
a single colour `color : Fin k` assigned to all `r`-element subsets of `H`. -/
def IsMonochromaticSet {α : Type*} (r : ℕ) {k : ℕ} (c : Finset α → Fin k)
    (H : Set α) : Prop :=
  ∃ color : Fin k, IsMonochromatic r c H color

/-- Any subset of a monochromatic set of colour `color` is also monochromatic of colour `color`
(Goldblatt §17.1, p. 222). -/
theorem IsMonochromatic.subset {α : Type*} {r k : ℕ} {c : Finset α → Fin k}
    {H H' : Set α} {color : Fin k} (h : IsMonochromatic r c H color) (hsub : H' ⊆ H) :
    IsMonochromatic r c H' color :=
  fun s hs ↦ h s (rSubsets_mono r hsub hs)

/-- Monochromaticity is downward-closed under set inclusion (Goldblatt §17.1, p. 222). -/
theorem IsMonochromaticSet.subset {α : Type*} {r k : ℕ} {c : Finset α → Fin k}
    {H H' : Set α} (h : IsMonochromaticSet r c H) (hsub : H' ⊆ H) :
    IsMonochromaticSet r c H' :=
  h.imp fun _ hc ↦ hc.subset hsub

/-- On a `Finset` `M`, `IsMonochromatic r c (↑M : Set α) color` is equivalent to `c s = color` for
all `s ∈ M.powersetCard r` (Goldblatt §17.1, p. 222). -/
theorem isMonochromatic_coe_iff_powersetCard {α : Type*} [DecidableEq α]
    {r k : ℕ} {c : Finset α → Fin k} {M : Finset α} {color : Fin k} :
    IsMonochromatic r c (↑M : Set α) color ↔ ∀ s ∈ M.powersetCard r, c s = color := by
  simp only [IsMonochromatic, mem_rSubsets_coe_iff_mem_powersetCard]

/-- Restricted `k`-colouring defined only on `[X]^r` (`rSubsets r X → Fin k`), matching Goldblatt's
partition `[A]^r ⊆ C_1 ∪ … ∪ C_k` (§17.1, p. 222). -/
abbrev RestrictedColouring {α : Type*} (r : ℕ) (X : Set α) (k : ℕ) : Type _ :=
  rSubsets r X → Fin k

/-- Extend a restricted colouring `c : rSubsets r X → Fin k` (with `0 < k`) to a total colouring
`Finset α → Fin k` using colour `⟨0, hk⟩` outside `[X]^r` (Goldblatt §17.1, p. 222). -/
noncomputable def RestrictedColouring.extend {α : Type*} {r k : ℕ} {X : Set α}
    (hk : 0 < k) (c : RestrictedColouring r X k) : Finset α → Fin k :=
  letI := Classical.propDecidable
  fun s ↦ if hs : s ∈ rSubsets r X then c ⟨s, hs⟩ else ⟨0, hk⟩

/-- On `[X]^r`, `RestrictedColouring.extend` agrees with `c` (Goldblatt §17.1, p. 222). -/
@[simp]
theorem RestrictedColouring.extend_apply {α : Type*} {r k : ℕ} {X : Set α}
    (hk : 0 < k) (c : RestrictedColouring r X k) {s : Finset α} (hs : s ∈ rSubsets r X) :
    c.extend hk s = c ⟨s, hs⟩ := by
  simp [RestrictedColouring.extend, hs]

/-- Goldblatt §17.1 (p. 221, eq. (i)): If `A ⊆ ⋃ i : Fin k, C i` and each `C i` is finite, then `A`
is finite. -/
theorem finite_of_subset_iUnion_finite {α : Type*} {k : ℕ} {A : Set α} {C : Fin k → Set α}
    (hsub : A ⊆ ⋃ i : Fin k, C i) (hfin : ∀ i : Fin k, (C i).Finite) :
    A.Finite :=
  (Set.finite_iUnion hfin).subset hsub

/-- Goldblatt §17.1 (p. 221): Infinite Pigeonhole Principle for finite covers: if `A` is infinite
and `A ⊆ ⋃ i : Fin k, C i`, then at least one intersection `A ∩ C i` (hence `C i`) is infinite. -/
theorem infinite_exists_infinite_inter_of_subset_iUnion {α : Type*} {k : ℕ}
    {A : Set α} {C : Fin k → Set α} (hA : A.Infinite) (hsub : A ⊆ ⋃ i : Fin k, C i) :
    ∃ i : Fin k, (A ∩ C i).Infinite := by
  by_contra hno
  push Not at hno
  have hcover : A ⊆ ⋃ i : Fin k, A ∩ C i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hsub hx)
    exact Set.mem_iUnion.2 ⟨i, hx, hi⟩
  exact hA (finite_of_subset_iUnion_finite hcover hno)

/-- Goldblatt §17.1 (p. 221): Any finite point-colouring `c : α → Fin k` of an infinite set `A`
admits an infinite monochromatic subset `B ⊆ A`. -/
theorem exists_infinite_monochromatic_of_point_colouring {α : Type*} {k : ℕ}
    {A : Set α} (hA : A.Infinite) (c : α → Fin k) :
    ∃ B : Set α, B ⊆ A ∧ B.Infinite ∧ ∃ i : Fin k, ∀ x ∈ B, c x = i := by
  have hcover : A ⊆ ⋃ i : Fin k, {x : α | c x = i} := fun x _ ↦ Set.mem_iUnion.2 ⟨c x, rfl⟩
  obtain ⟨i, hi⟩ := infinite_exists_infinite_inter_of_subset_iUnion hA hcover
  exact ⟨A ∩ {x : α | c x = i}, Set.inter_subset_left, hi, i, fun _ hx ↦ hx.2⟩

/-- Concrete Finite Ramsey `r = 1` (Finite Pigeonhole Principle, Goldblatt §17.1, p. 221):
For `k ≥ 1` and `m ≥ 1`, any `k`-colouring of `1`-element subsets of `Fin (k * (m - 1) + 1)`
has a monochromatic subset of cardinality at least `m`. -/
theorem finite_ramsey_r_one {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    (c : Finset (Fin (k * (m - 1) + 1)) → Fin k) :
    ∃ M : Finset (Fin (k * (m - 1) + 1)),
      m ≤ M.card ∧ IsMonochromaticSet 1 c (↑M : Set (Fin (k * (m - 1) + 1))) := by
  let _ := hk
  let N := k * (m - 1) + 1
  let f : Fin N → Fin k := fun x ↦ c {x}
  have hex : ∃ i : Fin k, m ≤ (Finset.univ.filter (fun x ↦ f x = i)).card := by
    by_contra hno
    push Not at hno
    have huniv : (Finset.univ : Finset (Fin N)) =
        Finset.univ.biUnion (fun i : Fin k ↦ Finset.univ.filter (fun x ↦ f x = i)) := by
      ext x
      simp
    have hcard_univ : N = (Finset.univ : Finset (Fin N)).card := (Finset.card_fin N).symm
    have hle1 : (Finset.univ : Finset (Fin N)).card ≤
        ∑ i : Fin k, (Finset.univ.filter (fun x ↦ f x = i)).card :=
      calc (Finset.univ : Finset (Fin N)).card
        _ = (Finset.univ.biUnion (fun i : Fin k ↦ Finset.univ.filter (fun x ↦ f x = i))).card :=
            congrArg Finset.card huniv
        _ ≤ ∑ i : Fin k, (Finset.univ.filter (fun x ↦ f x = i)).card :=
            Finset.card_biUnion_le
    have hle2 : ∑ i : Fin k, (Finset.univ.filter (fun x ↦ f x = i)).card ≤
        ∑ _i : Fin k, (m - 1) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hlt := hno i
      omega
    have hsum : (∑ _i : Fin k, (m - 1)) = k * (m - 1) := by
      simp
    omega
  obtain ⟨i, hi⟩ := hex
  refine ⟨Finset.univ.filter (fun x ↦ f x = i), hi, i, ?_⟩
  intro s hs
  obtain ⟨x, hx, rfl⟩ := mem_rSubsets_one_iff.1 hs
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, f] at hx
  exact hx

/-- Helper lemma: if `S` is a `Finset` of cardinality at least `3`, we can extract three pairwise
distinct elements `u, v, w ∈ S`. -/
lemma exists_three_distinct_of_three_le_card {α : Type*} [DecidableEq α] {S : Finset α}
    (hS : 3 ≤ S.card) :
    ∃ u ∈ S, ∃ v ∈ S, ∃ w ∈ S, u ≠ v ∧ u ≠ w ∧ v ≠ w := by
  have h1 : 0 < S.card := by omega
  obtain ⟨u, hu⟩ := Finset.card_pos.1 h1
  have h2 : 0 < (S.erase u).card := by
    rw [Finset.card_erase_of_mem hu]
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.1 h2
  have hvu : v ≠ u := (Finset.mem_erase.1 hv).1
  have hvS : v ∈ S := (Finset.mem_erase.1 hv).2
  have h3 : 0 < ((S.erase u).erase v).card := by
    rw [Finset.card_erase_of_mem hv, Finset.card_erase_of_mem hu]
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.1 h3
  have hwv : w ≠ v := (Finset.mem_erase.1 hw).1
  have hwu : w ≠ u := (Finset.mem_erase.1 (Finset.mem_erase.1 hw).2).1
  have hwS : w ∈ S := (Finset.mem_erase.1 (Finset.mem_erase.1 hw).2).2
  exact ⟨u, hu, v, hvS, w, hwS, hvu.symm, hwu.symm, hwv.symm⟩

/-- Characterization of `2`-element subsets of a `3`-element `Finset` `{a, b, d}`: every `2`-subset
is equal to `{a, b}`, `{a, d}`, or `{b, d}`. -/
lemma mem_rSubsets_two_of_triple {α : Type*} [DecidableEq α] {a b d : α}
    {s : Finset α} (hs : s ∈ rSubsets 2 (↑({a, b, d} : Finset α) : Set α)) :
    s = {a, b} ∨ s = {a, d} ∨ s = {b, d} := by
  rcases hs with ⟨hcard, hsub⟩
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hcard
  have hx : x = a ∨ x = b ∨ x = d := by
    simpa using hsub (Finset.mem_coe.2 (Finset.mem_insert_self x {y}))
  have hy : y = a ∨ y = b ∨ y = d := by
    simpa using hsub (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self y)))
  rcases hx with hxa | hxb | hxd <;> rcases hy with hya | hyb | hyd
  · exact absurd (hxa.trans hya.symm) hxy
  · rw [hxa, hyb]; exact Or.inl rfl
  · rw [hxa, hyd]; exact Or.inr (Or.inl rfl)
  · rw [hxb, hya]; exact Or.inl (Finset.pair_comm b a)
  · exact absurd (hxb.trans hyb.symm) hxy
  · rw [hxb, hyd]; exact Or.inr (Or.inr rfl)
  · rw [hxd, hya]; exact Or.inr (Or.inl (Finset.pair_comm d a))
  · rw [hxd, hyb]; exact Or.inr (Or.inr (Finset.pair_comm d b))
  · exact absurd (hxd.trans hyd.symm) hxy

/-- Helper for the Party Problem: if vertex `x₀` has three neighbours `u, v, w` whose edges to `x₀`
all share colour `i`, then either `{x₀, u, v}`, `{x₀, u, w}`, `{x₀, v, w}` is monochromatic of
colour `i`, or `{u, v, w}` is monochromatic of the opposite colour `1 - i`. -/
lemma triangle_from_three_same_star {α : Type*} [DecidableEq α]
    (c : Finset α → Fin 2) {x₀ u v w : α} (i : Fin 2)
    (hx₀u : x₀ ≠ u) (hx₀v : x₀ ≠ v) (hx₀w : x₀ ≠ w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hcu : c {x₀, u} = i) (hcv : c {x₀, v} = i) (hcw : c {x₀, w} = i) :
    ∃ T : Finset α, T.card = 3 ∧ IsMonochromaticSet 2 c (↑T : Set α) := by
  by_cases hc_uv : c {u, v} = i
  · refine ⟨{x₀, u, v}, ?_, i, ?_⟩
    · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [huv]
      · simp [hx₀u, hx₀v]
    · intro s hs
      rcases mem_rSubsets_two_of_triple hs with rfl | rfl | rfl
      · exact hcu
      · exact hcv
      · exact hc_uv
  · by_cases hc_uw : c {u, w} = i
    · refine ⟨{x₀, u, w}, ?_, i, ?_⟩
      · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [huw]
        · simp [hx₀u, hx₀w]
      · intro s hs
        rcases mem_rSubsets_two_of_triple hs with rfl | rfl | rfl
        · exact hcu
        · exact hcw
        · exact hc_uw
    · by_cases hc_vw : c {v, w} = i
      · refine ⟨{x₀, v, w}, ?_, i, ?_⟩
        · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp [hvw]
          · simp [hx₀v, hx₀w]
        · intro s hs
          rcases mem_rSubsets_two_of_triple hs with rfl | rfl | rfl
          · exact hcv
          · exact hcw
          · exact hc_vw
      · let j : Fin 2 := ⟨1 - i.1, by omega⟩
        have hij : ∀ col : Fin 2, col ≠ i → col = j := by
          intro col hne
          ext
          fin_cases i <;> fin_cases col <;> simp_all [j]
        refine ⟨{u, v, w}, ?_, j, ?_⟩
        · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp [hvw]
          · simp [huv, huw]
        · intro s hs
          rcases mem_rSubsets_two_of_triple hs with rfl | rfl | rfl
          · exact hij _ hc_uv
          · exact hij _ hc_uw
          · exact hij _ hc_vw

/-- **The Party Problem (`R(3, 3) ≤ 6`)** (Goldblatt §17.1, pp. 221–222):
Every `2`-colouring of the `2`-element subsets (edges) of `Fin 6` admits a monochromatic
`3`-element subset (triangle). -/
theorem ramsey_three_three_six (c : Finset (Fin 6) → Fin 2) :
    ∃ T : Finset (Fin 6), T.card = 3 ∧ IsMonochromaticSet 2 c (↑T : Set (Fin 6)) := by
  let S : Finset (Fin 6) := Finset.univ.erase 0
  have hScard : S.card = 5 := by decide
  let S₀ : Finset (Fin 6) := S.filter (fun x ↦ c {0, x} = 0)
  let S₁ : Finset (Fin 6) := S.filter (fun x ↦ c {0, x} = 1)
  have hpart : S₀.card + S₁.card = S.card := by
    have hnot : S₁ = S.filter (fun x ↦ ¬ c {0, x} = 0) := by
      ext x
      simp only [S₁, Finset.mem_filter]
      refine and_congr_right fun _ ↦ ?_
      generalize c {0, x} = col
      fin_cases col <;> simp
    rw [hnot]
    exact Finset.card_filter_add_card_filter_not (fun x ↦ c {0, x} = 0)
  have h3 : 3 ≤ S₀.card ∨ 3 ≤ S₁.card := by omega
  rcases h3 with hS₀ | hS₁
  · obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw⟩ := exists_three_distinct_of_three_le_card hS₀
    simp only [S₀, S, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hu hv hw
    exact triangle_from_three_same_star c 0 hu.1.symm hv.1.symm hw.1.symm huv huw hvw hu.2 hv.2 hw.2
  · obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw⟩ := exists_three_distinct_of_three_le_card hS₁
    simp only [S₁, S, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hu hv hw
    exact triangle_from_three_same_star c 1 hu.1.symm hv.1.symm hw.1.symm huv huw hvw hu.2 hv.2 hw.2

/-- Explicit `5`-cycle (`C_5`) `2`-colouring of pairs in `Fin 5`: colour `0` on pentagon edges
`{x, x + 1}` and colour `1` on diagonals (Goldblatt §17.1). -/
def pentagonColouring (s : Finset (Fin 5)) : Fin 2 :=
  if ∃ x : Fin 5, s = {x, x + 1} then 0 else 1

/-- **Lower bound for the Party Problem (`R(3, 3) > 5`)** (Goldblatt §17.1):
The `pentagonColouring` of `Fin 5` has no monochromatic triangle. -/
theorem pentagonColouring_no_mono_triangle :
    ¬ ∃ T : Finset (Fin 5), T.card = 3 ∧
      IsMonochromaticSet 2 pentagonColouring (↑T : Set (Fin 5)) := by
  rintro ⟨T, hcard, i, hmono⟩
  have hpow : ∀ s ∈ T.powersetCard 2, pentagonColouring s = i :=
    isMonochromatic_coe_iff_powersetCard.1 hmono
  have hmem : T ∈ (Finset.univ : Finset (Fin 5)).powersetCard 3 :=
    Finset.mem_powersetCard.2 ⟨Finset.subset_univ T, hcard⟩
  clear hmono hcard
  revert hpow i hmem T
  decide

/-- **Exact Ramsey Threshold `R(3, 3) = 6`** (Goldblatt §17.1):
For every `n : ℕ`, every `2`-colouring of `[Fin n]^2` contains a monochromatic `3`-subset
**if and only if** `6 ≤ n`. -/
theorem ramsey_number_three_three (n : ℕ) :
    (∀ c : Finset (Fin n) → Fin 2,
      ∃ T : Finset (Fin n), T.card = 3 ∧ IsMonochromaticSet 2 c (↑T : Set (Fin n))) ↔
    6 ≤ n := by
  constructor
  · intro hall
    by_contra hlt
    have hn5 : n ≤ 5 := by omega
    let emb : Fin n ↪ Fin 5 := Fin.castLEEmb hn5
    let c : Finset (Fin n) → Fin 2 := fun s ↦ pentagonColouring (s.map emb)
    obtain ⟨T, hTcard, i, hTmono⟩ := hall c
    refine pentagonColouring_no_mono_triangle ⟨T.map emb, ?_, i, ?_⟩
    · rw [Finset.card_map, hTcard]
    · intro s hs
      rw [mem_rSubsets] at hs
      have hs_sub : s ⊆ T.map emb := Finset.coe_subset.1 hs.2
      obtain ⟨s₀, hs₀_sub, rfl⟩ := Finset.subset_map_iff.1 hs_sub
      have hs₀_card : s₀.card = 2 := by simpa using hs.1
      exact hTmono s₀ ⟨hs₀_card, Finset.coe_subset.2 hs₀_sub⟩
  · intro hn6 c
    let emb : Fin 6 ↪ Fin n := Fin.castLEEmb hn6
    obtain ⟨T₀, hT₀card, i, hT₀mono⟩ := ramsey_three_three_six (fun s ↦ c (s.map emb))
    refine ⟨T₀.map emb, by rw [Finset.card_map, hT₀card], i, ?_⟩
    intro s hs
    rw [mem_rSubsets] at hs
    have hs_sub : s ⊆ T₀.map emb := Finset.coe_subset.1 hs.2
    obtain ⟨s₀, hs₀_sub, rfl⟩ := Finset.subset_map_iff.1 hs_sub
    have hs₀_card : s₀.card = 2 := by simpa using hs.1
    exact hT₀mono s₀ ⟨hs₀_card, Finset.coe_subset.2 hs₀_sub⟩

/-!
## §17.2 — Nonstandard Cofinality on `ℕ*`, Ultrafilter Colour Selection & Nonstandard Posets (pp. 223–225)
-/

open scoped Classical

/-- Membership of `omegaNat` in `starNatSet A` is equivalent to `A ∈ hyperfilter ℕ`
(Goldblatt §17.2–17.3, pp. 223–225). -/
@[simp]
theorem omegaNat_mem_starNatSet_iff {A : Set ℕ} :
    omegaNat ∈ starNatSet A ↔ A ∈ hyperfilter ℕ :=
  Iff.rfl

/-- Boolean algebra preservation for `starNatSet`: `*ℕ = ℕ*`. -/
@[simp]
theorem starNatSet_univ : starNatSet Set.univ = Set.univ :=
  internalNatSet_univ

/-- Boolean algebra preservation for `starNatSet`: `*∅ = ∅`. -/
@[simp]
theorem starNatSet_empty : starNatSet ∅ = ∅ :=
  internalNatSet_empty

/-- Boolean algebra preservation for `starNatSet`: `*(A ∩ B) = *A ∩ *B`. -/
@[simp]
theorem starNatSet_inter (A B : Set ℕ) :
    starNatSet (A ∩ B) = starNatSet A ∩ starNatSet B :=
  (internalNatSet_inter (fun _ ↦ A) (fun _ ↦ B)).symm

/-- Boolean algebra preservation for `starNatSet`: `*(A ∪ B) = *A ∪ *B`. -/
@[simp]
theorem starNatSet_union (A B : Set ℕ) :
    starNatSet (A ∪ B) = starNatSet A ∪ starNatSet B :=
  (internalNatSet_union (fun _ ↦ A) (fun _ ↦ B)).symm

/-- Boolean algebra preservation for `starNatSet`: `*(Aᶜ) = (*A)ᶜ`. -/
@[simp]
theorem starNatSet_compl (A : Set ℕ) :
    starNatSet Aᶜ = (starNatSet A)ᶜ :=
  (internalNatSet_compl (fun _ ↦ A)).symm

/-- Finite intersections commute with `starNatSet` (`*(⋂ i ∈ S, A_i) = ⋂ i ∈ S, *(A_i)`,
Goldblatt §17.3, p. 226). -/
theorem starNatSet_biInter_finset {ι : Type*} (S : Finset ι) (A : ι → Set ℕ) :
    starNatSet (⋂ i ∈ S, A i) = ⋂ i ∈ S, starNatSet (A i) := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a t hat ih =>
      have h1 : (⋂ i ∈ Finset.cons a t hat, A i) = A a ∩ ⋂ i ∈ t, A i := by ext x; simp
      have h2 : (⋂ i ∈ Finset.cons a t hat, starNatSet (A i)) =
          starNatSet (A a) ∩ ⋂ i ∈ t, starNatSet (A i) := by ext x; simp
      rw [h1, h2, starNatSet_inter, ih]

/-- For every standard `m : ℕ`, `omegaNat ∈ starNatSet {n : ℕ | m < n}`
(Goldblatt §17.3, p. 226). -/
theorem omegaNat_mem_starNatSet_Ioi (m : ℕ) :
    omegaNat ∈ starNatSet {n : ℕ | m < n} :=
  Germ.coe_lt.1 (isUnlimitedNat_omegaNat m)

/-- **Nonstandard Cofinality Lemma on `ℕ*` (General Unlimited Witness)** (Goldblatt §17.2–17.3,
pp. 223–226): If an unlimited hypernatural `ω ∈ ℕ*` belongs to `starNatSet A`, then `A` is cofinal
(`∀ m : ℕ, ∃ n ∈ A, m < n`) and therefore infinite. -/
theorem unlimited_mem_starNatSet_cofinal {ω : ℕ*} (hω : IsUnlimitedNat ω) {A : Set ℕ}
    (hA : ω ∈ starNatSet A) :
    (∀ m : ℕ, ∃ n ∈ A, m < n) ∧ A.Infinite := by
  have hcof : ∀ m : ℕ, ∃ n ∈ A, m < n := by
    intro m
    induction ω using Germ.inductionOn with | _ a =>
    have haA : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), a k ∈ A := coe_mem_starNatSet.1 hA
    have ham : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), m < a k := Germ.coe_lt.1 (hω m)
    obtain ⟨k, hkA, hkm⟩ := (haA.and ham).exists
    exact ⟨a k, hkA, hkm⟩
  refine ⟨hcof, fun hfin ↦ ?_⟩
  rcases A.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨n, hn, _⟩ := hcof 0
    exact hn
  · obtain ⟨M, hM⟩ := hfin.bddAbove
    obtain ⟨n, hnA, hMn⟩ := hcof M
    exact not_lt_of_ge (hM hnA) hMn

/-- **Nonstandard Cofinality Lemma for `omegaNat` (Unboundedness)** (Goldblatt §17.2–17.3):
If `omegaNat ∈ starNatSet A`, then for every `m : ℕ` there exists `n ∈ A` with `m < n`. -/
theorem omegaNat_mem_starNatSet_exists_gt {A : Set ℕ} (hA : omegaNat ∈ starNatSet A) (m : ℕ) :
    ∃ n ∈ A, m < n :=
  (unlimited_mem_starNatSet_cofinal isUnlimitedNat_omegaNat hA).1 m

/-- **Nonstandard Cofinality Lemma for `omegaNat` (Infinitude)** (Goldblatt §17.2–17.3):
If `omegaNat ∈ starNatSet A`, then `A` is infinite. -/
theorem omegaNat_mem_starNatSet_infinite {A : Set ℕ} (hA : omegaNat ∈ starNatSet A) :
    A.Infinite :=
  (unlimited_mem_starNatSet_cofinal isUnlimitedNat_omegaNat hA).2

/-- Every finite type `β` is unchanged under ultrapower enlargement:
`β ≃ Germ (hyperfilter ℕ : Filter ℕ) β` via `Germ.const` (Goldblatt §3.10(1), §17.3). -/
def germConstEquiv (β : Type*) [Finite β] : β ≃ Germ (hyperfilter ℕ : Filter ℕ) β :=
  Equiv.ofBijective Germ.const ⟨fun a b hab ↦ (Germ.coe_eq.1 hab).exists.choose_spec, fun g ↦ by
    induction g using Germ.inductionOn with | _ s =>
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ b : β, b = s n :=
      Eventually.of_forall fun n ↦ ⟨s n, rfl⟩
    obtain ⟨b, hb⟩ := (hyperfilter ℕ).eventually_exists_iff.1 hev
    exact ⟨b, Germ.coe_eq.2 hb⟩⟩

/-- `@[simp]` evaluation of `germConstEquiv β` on standard elements. -/
@[simp]
theorem germConstEquiv_apply {β : Type*} [Finite β] (b : β) :
    germConstEquiv β b = (b : Germ (hyperfilter ℕ : Filter ℕ) β) :=
  rfl

/-- `@[simp]` left inverse for `germConstEquiv β` on constant germs. -/
@[simp]
theorem germConstEquiv_symm_const {β : Type*} [Finite β] (b : β) :
    (germConstEquiv β).symm (b : Germ (hyperfilter ℕ : Filter ℕ) β) = b :=
  (germConstEquiv β).symm_apply_apply b

/-- Nonstandard extension `*c : ℕ* → β` of a map `c : ℕ → β` into a finite type `β` (such as
`Fin k`), obtained by composing `Germ.map c` with `(germConstEquiv β).symm`
(Goldblatt §17.2–17.3). -/
def starNatFinFun {β : Type*} [Finite β] (c : ℕ → β) (N : ℕ*) : β :=
  (germConstEquiv β).symm (Germ.map c N)

/-- `*c` agrees with `c` on standard natural numbers `(n : ℕ*)`. -/
@[simp]
theorem starNatFinFun_natCast {β : Type*} [Finite β] (c : ℕ → β) (n : ℕ) :
    starNatFinFun c (n : ℕ*) = c n :=
  germConstEquiv_symm_const (c n)

/-- Fundamental characterization of `*c(N)` for finite codomain `β`:
`N ∈ starNatSet {n : ℕ | c n = i} ↔ starNatFinFun c N = i` (Goldblatt §17.2–17.3). -/
@[simp]
theorem mem_starNatSet_eq_iff_starNatFinFun {β : Type*} [Finite β]
    (c : ℕ → β) (N : ℕ*) (i : β) :
    N ∈ starNatSet {n : ℕ | c n = i} ↔ starNatFinFun c N = i := by
  induction N using Germ.inductionOn with | _ a =>
  rw [coe_mem_starNatSet]
  change (∀ᶠ n in (hyperfilter ℕ : Filter ℕ), c (a n) = i) ↔
    (germConstEquiv β).symm ((fun n ↦ c (a n)) : Germ (hyperfilter ℕ : Filter ℕ) β) = i
  rw [Equiv.symm_apply_eq, germConstEquiv_apply]
  exact Germ.coe_eq.symm

/-- **Ultrafilter Colour Selection Lemma on `ℕ*`** (Goldblatt §17.2–17.3):
For any `k`-colouring `c : ℕ → Fin k`, `*c(omegaNat)` (`starNatFinFun c omegaNat`) is the
**unique** standard colour `i : Fin k` such that `omegaNat ∈ starNatSet {n : ℕ | c n = i}`;
consequently `{n : ℕ | c n = starNatFinFun c omegaNat}` is infinite. -/
theorem existsUnique_colour_omegaNat {k : ℕ} (c : ℕ → Fin k) :
    (∃! i : Fin k, omegaNat ∈ starNatSet {n : ℕ | c n = i}) ∧
      omegaNat ∈ starNatSet {n : ℕ | c n = starNatFinFun c omegaNat} ∧
      {n : ℕ | c n = starNatFinFun c omegaNat}.Infinite := by
  have hmem : omegaNat ∈ starNatSet {n : ℕ | c n = starNatFinFun c omegaNat} :=
    (mem_starNatSet_eq_iff_starNatFinFun c omegaNat _).2 rfl
  refine ⟨⟨starNatFinFun c omegaNat, hmem, fun j hj ↦ ?_⟩,
    hmem, omegaNat_mem_starNatSet_infinite hmem⟩
  exact ((mem_starNatSet_eq_iff_starNatFinFun c omegaNat j).1 hj).symm

/-- **Iterative Witness Construction (Single Set)** (Goldblatt §17.2–17.3):
If `omegaNat ∈ starNatSet B`, then `B` contains a strictly increasing sequence `x : ℕ → ℕ`. -/
theorem exists_strictMono_in_set_of_omegaNat_mem {B : Set ℕ} (hB : omegaNat ∈ starNatSet B) :
    ∃ x : ℕ → ℕ, StrictMono x ∧ ∀ m : ℕ, x m ∈ B := by
  have hgt : ∀ k : ℕ, ∃ n : ℕ, n ∈ B ∧ k < n := fun k ↦ by
    obtain ⟨n, hnB, hkn⟩ := omegaNat_mem_starNatSet_exists_gt hB k
    exact ⟨n, hnB, hkn⟩
  have hne : ∃ n : ℕ, n ∈ B := by
    obtain ⟨n, hnB, _⟩ := hgt 0
    exact ⟨n, hnB⟩
  let x : ℕ → ℕ := Nat.rec hne.choose (fun _ xm ↦ (hgt xm).choose)
  refine ⟨x, strictMono_nat_of_lt_succ fun m ↦ ((hgt (x m)).choose_spec).2, fun m ↦ ?_⟩
  cases m with
  | zero => exact hne.choose_spec
  | succ m => exact ((hgt (x m)).choose_spec).1

/-- **Iterative Witness Construction (History-Dependent `Finset` Family)**
(Goldblatt §17.3, pp. 226–227):
Given a family of sets `B : Finset ℕ → Set ℕ` such that `omegaNat ∈ starNatSet (B S)` for every
finite set `S : Finset ℕ`, there exists a strictly increasing sequence `x : ℕ → ℕ` such that
`x m ∈ B ((Finset.range m).image x)` for every `m : ℕ`. -/
theorem exists_strictMono_of_finset_omegaNat (B : Finset ℕ → Set ℕ)
    (hB : ∀ S : Finset ℕ, omegaNat ∈ starNatSet (B S)) :
    ∃ x : ℕ → ℕ, StrictMono x ∧ ∀ m : ℕ, x m ∈ B ((Finset.range m).image x) := by
  have hgt : ∀ (S : Finset ℕ) (k : ℕ), ∃ n : ℕ, n ∈ B S ∧ k < n := fun S k ↦ by
    obtain ⟨n, hnB, hkn⟩ := omegaNat_mem_starNatSet_exists_gt (hB S) k
    exact ⟨n, hnB, hkn⟩
  have hne₀ : ∃ n : ℕ, n ∈ B ∅ := by
    obtain ⟨n, hnB, _⟩ := hgt ∅ 0
    exact ⟨n, hnB⟩
  -- Primitive recursion tracking `(x m, {x 0, …, x (m - 1)})`.
  let step : ℕ → ℕ × Finset ℕ :=
    Nat.rec (hne₀.choose, ∅) fun _ p ↦
      let S := insert p.1 p.2
      ((hgt S p.1).choose, S)
  let x : ℕ → ℕ := fun m ↦ (step m).1
  have hlt : ∀ m : ℕ, x m < x (m + 1) := fun m ↦
    ((hgt (insert (step m).1 (step m).2) (step m).1).choose_spec).2
  have hsnd : ∀ m : ℕ, (step m).2 = (Finset.range m).image x := by
    intro m
    induction m with
    | zero => simp [step]
    | succ m ih =>
        change insert (x m) (step m).2 = (Finset.range (m + 1)).image x
        rw [ih, Finset.range_add_one, Finset.image_insert]
  refine ⟨x, strictMono_nat_of_lt_succ hlt, fun m ↦ ?_⟩
  rw [← hsnd m]
  cases m with
  | zero => exact hne₀.choose_spec
  | succ m =>
      exact ((hgt (insert (step m).1 (step m).2) (step m).1).choose_spec).1

/-! ### §17.2 Direct Nonstandard Proof of Theorem 17.1.1 (Infinite Posets, Goldblatt p. 223) -/

/-- Goldblatt Theorem 17.1.1(3) (p. 222): A sequence `p : ℕ → P` in a preordered set `(P, ≤)` is an
**antichain sequence** if distinct indices give incomparable elements (`¬ p m ≤ p n ∧ ¬ p n ≤ p m`).
Note that irreflexivity of `¬ (· ≤ ·)` automatically forces `p` to be injective! -/
def IsAntichainSeq {P : Type*} [Preorder P] (p : ℕ → P) : Prop :=
  ∀ m n : ℕ, m ≠ n → ¬ p m ≤ p n ∧ ¬ p n ≤ p m

/-- Every `IsAntichainSeq` is automatically injective (Goldblatt §17.1, p. 222). -/
theorem IsAntichainSeq.injective {P : Type*} [Preorder P] {p : ℕ → P}
    (hp : IsAntichainSeq p) : Function.Injective p := by
  intro m n hmn
  by_contra hne
  exact (hp m n hne).1 (by rw [hmn])

/-- Ultrapower enlargement `*P = Germ (hyperfilter ℕ) P` of a partially ordered set `P`
(Goldblatt §17.2, p. 223). -/
abbrev StarPoset (P : Type*) : Type _ :=
  Germ (hyperfilter ℕ : Filter ℕ) P

/-- In the ultrapower `StarPoset P` of a `PartialOrder P` modulo an ultrafilter, strict inequality
`[f] < [g]` holds if and only if `{n : ℕ | f n < g n} ∈ hyperfilter ℕ` (Goldblatt §17.2, p. 223). -/
theorem coe_lt_starPoset {P : Type*} [PartialOrder P] {f g : ℕ → P} :
    (f : StarPoset P) < (g : StarPoset P) ↔
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n < g n := by
  rw [lt_iff_le_and_ne, Germ.coe_le, Ne, Germ.coe_eq, Filter.EventuallyLE, Filter.EventuallyEq,
      ← Ultrafilter.eventually_not, ← eventually_and]
  exact eventually_congr (Eventually.of_forall fun _ ↦ lt_iff_le_and_ne.symm)

/-- Standard embedding `P ↪ StarPoset P` preserves and reflects strict inequality `<`. -/
@[simp]
theorem const_lt_starPoset {P : Type*} [PartialOrder P] {a b : P} :
    (a : StarPoset P) < (b : StarPoset P) ↔ a < b := by
  change ((fun _ : ℕ ↦ a) : StarPoset P) < ((fun _ : ℕ ↦ b) : StarPoset P) ↔ a < b
  rw [coe_lt_starPoset, eventually_const]

/-- Order-preserving embedding `P ↪ WithBot (WithTop P)` adjoining a least element `⊥` (`0`) and a
greatest element `⊤` (`1`) as in Goldblatt §17.2 (p. 223). -/
def toBoundedPoset {P : Type*} (p : P) : WithBot (WithTop P) :=
  ((p : WithTop P) : WithBot (WithTop P))

/-- `toBoundedPoset` is injective. -/
theorem toBoundedPoset_injective {P : Type*} :
    Function.Injective (toBoundedPoset (P := P)) :=
  fun _ _ h ↦ WithTop.coe_inj.1 (WithBot.coe_inj.1 h)

/-- `toBoundedPoset` reflects and preserves `≤`. -/
@[simp]
theorem toBoundedPoset_le_iff {P : Type*} [Preorder P] {a b : P} :
    toBoundedPoset a ≤ toBoundedPoset b ↔ a ≤ b := by
  simp [toBoundedPoset]

/-- `toBoundedPoset` reflects and preserves `<`. -/
@[simp]
theorem toBoundedPoset_lt_iff {P : Type*} [Preorder P] {a b : P} :
    toBoundedPoset a < toBoundedPoset b ↔ a < b := by
  simp [toBoundedPoset]

/-- Every element of `WithBot (WithTop P)` strictly between `⊥` and `⊤` comes from a unique
standard element of `P` (Goldblatt §17.2, p. 223). -/
lemma exists_eq_toBoundedPoset_of_bot_lt_lt_top {P : Type*} [Preorder P]
    {x : WithBot (WithTop P)} (hbot : ⊥ < x) (htop : x < ⊤) :
    ∃ p : P, x = toBoundedPoset p := by
  cases x with
  | bot => exact absurd hbot (lt_irrefl _)
  | coe y =>
      cases y with
      | top =>
          change ((⊤ : WithTop P) : WithBot (WithTop P)) < ⊤ at htop
          exact absurd htop (lt_irrefl _)
      | coe p => exact ⟨p, rfl⟩

/-- **Theorem 17.1.1 — Direct Nonstandard Proof** (Goldblatt §17.2, p. 223):
Every infinite partially ordered set `(P, ≤)` contains a sequence `p : ℕ → P` that is either:
1. strictly increasing (`StrictMono p`),
2. strictly decreasing (`StrictAnti p`), or
3. an antichain (`IsAntichainSeq p`).

Proved directly without Ramsey's theorem following Goldblatt §17.2: adjoin `⊥` and `⊤`, choose a
nonstandard `π ∈ *P̄`, set `L = {x | x < π}` and `U = {x | π < x}`, extract a monotone chain if `L`
has no maximal element or `U` has no minimal element, and otherwise use `π ∈ *M` for
`M = {x | q_l < x < q_u}` to guide an inductive antichain construction via existential transfer! -/
theorem infinite_poset_chain_or_antichain_nonstandard {P : Type*} [PartialOrder P] [Infinite P] :
    (∃ p : ℕ → P, StrictMono p) ∨
    (∃ p : ℕ → P, StrictAnti p) ∨
    (∃ p : ℕ → P, IsAntichainSeq p) := by
  let Pbar := WithBot (WithTop P)
  let e : ℕ ↪ P := Infinite.natEmbedding P
  let πSeq : ℕ → Pbar := fun n ↦ toBoundedPoset (e n)
  let π : StarPoset Pbar := (πSeq : StarPoset Pbar)
  have hbot_lt_π : (⊥ : StarPoset Pbar) < π := by
    change ((fun _ : ℕ ↦ (⊥ : Pbar)) : StarPoset Pbar) < (πSeq : StarPoset Pbar)
    rw [coe_lt_starPoset]
    exact Eventually.of_forall fun n ↦ WithBot.bot_lt_coe _
  have hπ_lt_top : π < (⊤ : StarPoset Pbar) := by
    change (πSeq : StarPoset Pbar) < ((fun _ : ℕ ↦ (⊤ : Pbar)) : StarPoset Pbar)
    rw [coe_lt_starPoset]
    exact Eventually.of_forall fun n ↦ WithBot.coe_lt_coe.2 (WithTop.coe_lt_top (e n))
  have hπ_nonstd : ∀ x : Pbar, π ≠ (x : StarPoset Pbar) := by
    intro x hx
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), πSeq n = x := Germ.coe_eq.1 hx
    have hfin : {n : ℕ | πSeq n = x}.Finite := by
      apply Set.Subsingleton.finite
      intro m hm k hk
      exact e.injective (toBoundedPoset_injective (hm.trans hk.symm))
    have hcompl : {n : ℕ | πSeq n = x}ᶜ ∈ (hyperfilter ℕ : Filter ℕ) :=
      Filter.hyperfilter_le_cofinite hfin.compl_mem_cofinite
    have hemp : (∅ : Set ℕ) ∈ (hyperfilter ℕ : Filter ℕ) := by
      simpa using inter_mem hev hcompl
    exact (Ultrafilter.neBot (hyperfilter ℕ)).ne (empty_mem_iff_bot.1 hemp)
  let L : Set Pbar := {x : Pbar | (x : StarPoset Pbar) < π}
  let U : Set Pbar := {x : Pbar | π < (x : StarPoset Pbar)}
  have hbotL : (⊥ : Pbar) ∈ L := hbot_lt_π
  have htopU : (⊤ : Pbar) ∈ U := hπ_lt_top
  -- Case 1: `L` has no maximal element (`∀ x ∈ L, ∃ y ∈ L, x < y`).
  by_cases hL_max : ∃ ql ∈ L, ∀ x ∈ L, ¬ ql < x
  · -- Case 2: `U` has no minimal element (`∀ x ∈ U, ∃ y ∈ U, y < x`).
    by_cases hU_min : ∃ qu ∈ U, ∀ x ∈ U, ¬ x < qu
    · -- Case 3: `ql` is maximal in `L` and `qu` is minimal in `U`.
      obtain ⟨ql, hqlL, hql_max⟩ := hL_max
      obtain ⟨qu, hquU, hqu_min⟩ := hU_min
      let M : Set Pbar := {x : Pbar | ql < x ∧ x < qu}
      -- Every element of `M` is strictly between `⊥` and `⊤`, hence comes from `P`.
      have hM_in_P : ∀ x ∈ M, ∃ p : P, x = toBoundedPoset p := by
        rintro x ⟨h1, h2⟩
        exact exists_eq_toBoundedPoset_of_bot_lt_lt_top
          ((bot_le : ⊥ ≤ ql).trans_lt h1) (h2.trans_le (le_top : qu ≤ ⊤))
      -- No member of `M` is comparable with `π`!
      have hM_incomp : ∀ x ∈ M, ¬ (x : StarPoset Pbar) ≤ π ∧ ¬ π ≤ (x : StarPoset Pbar) := by
        rintro x ⟨hqlx, hxqu⟩
        refine ⟨fun hxle ↦ ?_, fun hπle ↦ ?_⟩
        · have hxlt : (x : StarPoset Pbar) < π :=
            lt_of_le_of_ne hxle (Ne.symm (hπ_nonstd x))
          exact hql_max x hxlt hqlx
        · have hπlt : π < (x : StarPoset Pbar) :=
            lt_of_le_of_ne hπle (hπ_nonstd x)
          exact hqu_min x hπlt hxqu
      -- For any finite subset `S : Finset Pbar` of `M`, `π` witnesses that there is an element of
      -- `M` incomparable with every member of `S`!
      have hex_incomp : ∀ S : Finset Pbar, (↑S : Set Pbar) ⊆ M →
          ∃ y ∈ M, ∀ s ∈ S, ¬ s ≤ y ∧ ¬ y ≤ s := by
        intro S hSM
        have hev_ql : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ql < πSeq n :=
          coe_lt_starPoset.1 hqlL
        have hev_qu : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), πSeq n < qu :=
          coe_lt_starPoset.1 hquU
        have hev_S : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
            ∀ s ∈ S, ¬ s ≤ πSeq n ∧ ¬ πSeq n ≤ s := by
          rw [eventually_all_finset]
          intro s hs
          obtain ⟨hns1, hns2⟩ := hM_incomp s (hSM (Finset.mem_coe.2 hs))
          have h1 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ¬ s ≤ πSeq n :=
            Ultrafilter.eventually_not.2 (fun h ↦ hns1 (Germ.coe_le.2 h))
          have h2 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ¬ πSeq n ≤ s :=
            Ultrafilter.eventually_not.2 (fun h ↦ hns2 (Germ.coe_le.2 h))
          exact h1.and h2
        obtain ⟨n, ⟨h1, h2⟩, h3⟩ := ((hev_ql.and hev_qu).and hev_S).exists
        exact ⟨πSeq n, ⟨h1, h2⟩, h3⟩
      -- Inductively build an antichain `(x_m, {x_0, …, x_{m-1}})` in `M`.
      obtain ⟨y₀, hy₀M, _⟩ := hex_incomp ∅ (by simp)
      let step : ℕ → {y : Pbar // y ∈ M} × {S : Finset Pbar // (↑S : Set Pbar) ⊆ M} :=
        Nat.rec (⟨y₀, hy₀M⟩, ⟨∅, by simp⟩) fun _ st ↦
          let S' : Finset Pbar := insert st.1.1 st.2.1
          have hS'M : (↑S' : Set Pbar) ⊆ M := by
            rw [Finset.coe_insert]
            exact Set.insert_subset st.1.2 st.2.2
          let hwit := hex_incomp S' hS'M
          (⟨hwit.choose, hwit.choose_spec.1⟩, ⟨S', hS'M⟩)
      let xBar : ℕ → Pbar := fun m ↦ (step m).1.1
      have hxBar_M : ∀ m : ℕ, xBar m ∈ M := fun m ↦ (step m).1.2
      have hsnd : ∀ m : ℕ, (step m).2.1 = (Finset.range m).image xBar := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
            change insert (xBar m) (step m).2.1 = (Finset.range (m + 1)).image xBar
            rw [ih, Finset.range_add_one, Finset.image_insert]
      have hxBar_incomp_lt : ∀ m k : ℕ, m < k → ¬ xBar m ≤ xBar k ∧ ¬ xBar k ≤ xBar m := by
        intro m k hmk
        cases k with
        | zero => omega
        | succ k =>
            let S' : Finset Pbar := insert (step k).1.1 (step k).2.1
            have hS'M : (↑S' : Set Pbar) ⊆ M := by
              rw [Finset.coe_insert]
              exact Set.insert_subset (step k).1.2 (step k).2.2
            have hspec := (hex_incomp S' hS'M).choose_spec.2
            have hm_mem : xBar m ∈ S' := by
              have hmem_range : xBar m ∈ (Finset.range (k + 1)).image xBar :=
                Finset.mem_image.2 ⟨m, Finset.mem_range.2 hmk, rfl⟩
              have heqS : S' = (Finset.range (k + 1)).image xBar := hsnd (k + 1)
              rwa [heqS]
            exact hspec (xBar m) hm_mem
      let p : ℕ → P := fun m ↦ (hM_in_P (xBar m) (hxBar_M m)).choose
      have hp_eq : ∀ m : ℕ, toBoundedPoset (p m) = xBar m :=
        fun m ↦ ((hM_in_P (xBar m) (hxBar_M m)).choose_spec).symm
      refine Or.inr (Or.inr ⟨p, fun m n hmn ↦ ?_⟩)
      rcases lt_or_gt_of_ne hmn with hlt | hgt
      · obtain ⟨h1, h2⟩ := hxBar_incomp_lt m n hlt
        rw [← hp_eq m, ← hp_eq n, toBoundedPoset_le_iff] at h1 h2
        exact ⟨h1, h2⟩
      · obtain ⟨h1, h2⟩ := hxBar_incomp_lt n m hgt
        rw [← hp_eq m, ← hp_eq n, toBoundedPoset_le_iff] at h1 h2
        exact ⟨h2, h1⟩
    · -- `U` has no minimal element: construct a strictly decreasing sequence in `P`.
      push Not at hU_min
      let f : U → U := fun u ↦
        ⟨(hU_min u.1 u.2).choose, (hU_min u.1 u.2).choose_spec.1⟩
      have hf_lt : ∀ u : U, (f u).1 < u.1 := fun u ↦ (hU_min u.1 u.2).choose_spec.2
      let uSeq : ℕ → U := fun n ↦ f^[n + 1] ⟨⊤, htopU⟩
      have huSeq_anti : StrictAnti (fun n ↦ (uSeq n).1) :=
        strictAnti_nat_of_succ_lt fun n ↦ by
          simp only [uSeq, Function.iterate_succ_apply']
          exact hf_lt _
      have huSeq_in_P : ∀ n : ℕ, ∃ p : P, (uSeq n).1 = toBoundedPoset p := by
        intro n
        have htop_gt : (uSeq n).1 < ⊤ := by
          induction n with
          | zero => exact hf_lt ⟨⊤, htopU⟩
          | succ n ih => exact (huSeq_anti (Nat.lt_succ_self n)).trans ih
        have hbot_lt : ⊥ < (uSeq n).1 := by
          have hπu : π < ((uSeq n).1 : StarPoset Pbar) := (uSeq n).2
          exact const_lt_starPoset.1 (hbot_lt_π.trans hπu)
        exact exists_eq_toBoundedPoset_of_bot_lt_lt_top hbot_lt htop_gt
      let p : ℕ → P := fun n ↦ (huSeq_in_P n).choose
      have hp_eq : ∀ n : ℕ, toBoundedPoset (p n) = (uSeq n).1 :=
        fun n ↦ ((huSeq_in_P n).choose_spec).symm
      refine Or.inr (Or.inl ⟨p, fun m n hmn ↦ ?_⟩)
      rw [← toBoundedPoset_lt_iff, hp_eq m, hp_eq n]
      exact huSeq_anti hmn
  · -- `L` has no maximal element: construct a strictly increasing sequence in `P`.
    push Not at hL_max
    let g : L → L := fun l ↦
      ⟨(hL_max l.1 l.2).choose, (hL_max l.1 l.2).choose_spec.1⟩
    have hg_gt : ∀ l : L, l.1 < (g l).1 := fun l ↦ (hL_max l.1 l.2).choose_spec.2
    let lSeq : ℕ → L := fun n ↦ g^[n + 1] ⟨⊥, hbotL⟩
    have hlSeq_mono : StrictMono (fun n ↦ (lSeq n).1) :=
      strictMono_nat_of_lt_succ fun n ↦ by
        simp only [lSeq, Function.iterate_succ_apply']
        exact hg_gt _
    have hlSeq_in_P : ∀ n : ℕ, ∃ p : P, (lSeq n).1 = toBoundedPoset p := by
      intro n
      have hbot_lt : ⊥ < (lSeq n).1 := by
        induction n with
        | zero => exact hg_gt ⟨⊥, hbotL⟩
        | succ n ih => exact ih.trans (hlSeq_mono (Nat.lt_succ_self n))
      have htop_gt : (lSeq n).1 < ⊤ := by
        have hlπ : ((lSeq n).1 : StarPoset Pbar) < π := (lSeq n).2
        exact const_lt_starPoset.1 (hlπ.trans hπ_lt_top)
      exact exists_eq_toBoundedPoset_of_bot_lt_lt_top hbot_lt htop_gt
    let p : ℕ → P := fun n ↦ (hlSeq_in_P n).choose
    have hp_eq : ∀ n : ℕ, toBoundedPoset (p n) = (lSeq n).1 :=
      fun n ↦ ((hlSeq_in_P n).choose_spec).symm
    refine Or.inl ⟨p, fun m n hmn ↦ ?_⟩
    rw [← toBoundedPoset_lt_iff, hp_eq m, hp_eq n]
    exact hlSeq_mono hmn

/-!
## §17.3 — Nonstandard Proof of Infinite Ramsey's Theorem, Exercise 17.3.1 & Corollaries (pp. 224–227)
-/

/-- General set enlargement `*A ⊆ Germ (hyperfilter ℕ) α` for an arbitrary type `α`
(Goldblatt §3.9, §17.3, p. 224). -/
def starGenSet {α : Type*} (A : Set α) : Set (Germ (hyperfilter ℕ : Filter ℕ) α) :=
  {x | Germ.LiftPred (· ∈ A) x}

/-- Internal subset `[S_n] ⊆ Germ (hyperfilter ℕ) α` generated by a sequence of finite sets
`S : ℕ → Finset α` (Goldblatt §11.1, §17.3, p. 225). -/
def internalGenFinset {α : Type*} (S : ℕ → Finset α) :
    Set (Germ (hyperfilter ℕ : Filter ℕ) α) :=
  {x | Germ.LiftRel (· ∈ ·) x (S : Germ (hyperfilter ℕ : Filter ℕ) (Finset α))}

/-- `[*A]^r` realized as subsets of `Germ (hyperfilter ℕ) α` of the form `(↑F : Set _)` with
`F.card = r` and `↑F ⊆ *A` (Goldblatt §17.3, pp. 224–225). -/
def rSubsetsOfStar {α : Type*} (r : ℕ) (A : Set α) :
    Set (Set (Germ (hyperfilter ℕ : Filter ℕ) α)) :=
  {X | ∃ F ∈ rSubsets r (starGenSet A), X = (↑F : Set (Germ (hyperfilter ℕ : Filter ℕ) α))}

/-- `*([A]^r)` realized as internal subsets `[S_n]` of `Germ (hyperfilter ℕ) α` with
`{n : ℕ | S_n ∈ [A]^r} ∈ hyperfilter ℕ` (Goldblatt §17.3, pp. 224–225). -/
def starRSubsets {α : Type*} (r : ℕ) (A : Set α) :
    Set (Set (Germ (hyperfilter ℕ : Filter ℕ) α)) :=
  {X | ∃ S : ℕ → Finset α, X = internalGenFinset S ∧
    ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), S n ∈ rSubsets r A}

/-- **Goldblatt §17.3 Transfer Inclusion (pp. 224–225)**: `[*A]^r ⊆ *([A]^r)` for every `r : ℕ`
and `A : Set α`. -/
theorem rSubsetsOfStar_subset_starRSubsets {α : Type*} (r : ℕ) (A : Set α) :
    rSubsetsOfStar r A ⊆ starRSubsets r A := by
  rintro _ ⟨F, ⟨hcard, hFsub⟩, rfl⟩
  let eqv : Fin r ≃ F := (Equiv.cast (congrArg Fin hcard.symm)).trans F.equivFin.symm
  have hrep : ∀ i : Fin r, ∃ f : ℕ → α,
      (f : Germ (hyperfilter ℕ : Filter ℕ) α) = (eqv i).1 :=
    fun i ↦ Germ.inductionOn (eqv i).1 fun f ↦ ⟨f, rfl⟩
  choose seq hseq using hrep
  have hev_mem : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∀ i : Fin r, seq i n ∈ A := by
    rw [eventually_all]
    intro i
    have hi : ((seq i : ℕ → α) : Germ (hyperfilter ℕ : Filter ℕ) α) ∈ starGenSet A := by
      rw [hseq i]
      exact hFsub (eqv i).2
    exact hi
  have hev_dist : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
      ∀ i : Fin r, ∀ j : Fin r, i ≠ j → seq i n ≠ seq j n := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ hne ↦ absurd hij hne
    · have hne_germ : ((seq i : ℕ → α) : Germ (hyperfilter ℕ : Filter ℕ) α) ≠
          ((seq j : ℕ → α) : Germ (hyperfilter ℕ : Filter ℕ) α) := by
        rw [hseq i, hseq j]
        intro heq
        exact hij (eqv.injective (Subtype.ext heq))
      have hev_ne : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), seq i n ≠ seq j n :=
        Ultrafilter.eventually_not.2 (fun h ↦ hne_germ (Germ.coe_eq.2 h))
      exact hev_ne.mono fun _ hne _ ↦ hne
  let S : ℕ → Finset α := fun n ↦ Finset.univ.image (fun i : Fin r ↦ seq i n)
  refine ⟨S, ?_, ?_⟩
  · ext x
    induction x using Germ.inductionOn with | _ u =>
    constructor
    · intro huF
      have hu_mem : ((u : ℕ → α) : Germ (hyperfilter ℕ : Filter ℕ) α) ∈ F := huF
      obtain ⟨i, hi⟩ : ∃ i : Fin r, (eqv i).1 = (u : Germ (hyperfilter ℕ : Filter ℕ) α) :=
        ⟨eqv.symm ⟨_, hu_mem⟩, by simp⟩
      have hev_eq : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), seq i n = u n := by
        apply Germ.coe_eq.1
        rw [hseq i, hi]
      exact Germ.liftRel_coe.2 (hev_eq.mono fun n hn ↦
        Finset.mem_image.2 ⟨i, Finset.mem_univ i, hn⟩)
    · intro huS
      have hev_ex : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ i : Fin r, seq i n = u n := by
        refine (Germ.liftRel_coe.1 huS).mono fun n hn ↦ ?_
        obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hn
        exact ⟨i, hi⟩
      obtain ⟨i, hi⟩ := (hyperfilter ℕ).eventually_exists_iff.1 hev_ex
      have heq_germ : (u : Germ (hyperfilter ℕ : Filter ℕ) α) = (eqv i).1 := by
        rw [← hseq i]
        exact (Germ.coe_eq.2 hi).symm
      rw [heq_germ]
      exact (eqv i).2
  · refine (hev_mem.and hev_dist).mono fun n ⟨hmem, hdist⟩ ↦ ⟨?_, ?_⟩
    · rw [Finset.card_image_of_injOn]
      · simp
      · intro i _ j _ hij_eq
        by_contra hij
        exact hdist i j hij hij_eq
    · intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
      exact hmem i

/-- **Exercise 17.3.1 (p. 225)**: `[*A]^r = *([A]^r)` for every `r : ℕ` and every `A : Set α`
(and in particular `[*A]^{k+1} = *([A]^{k+1})`). -/
theorem rSubsetsOfStar_eq_starRSubsets {α : Type*} (r : ℕ) (A : Set α) :
    rSubsetsOfStar r A = starRSubsets r A := by
  apply Set.Subset.antisymm (rSubsetsOfStar_subset_starRSubsets r A)
  rintro _ ⟨S, rfl, hev⟩
  -- On indices where `(S n).card = r`, pick a bijection `Fin r ≃ S n`.
  by_cases hr : r = 0
  · subst hr
    refine ⟨∅, ⟨rfl, by simp⟩, ?_⟩
    ext x
    induction x using Germ.inductionOn with | _ u =>
    simp only [internalGenFinset, Set.mem_ofPred_eq, Germ.liftRel_coe,
      Finset.coe_empty, Set.mem_empty_iff_false, iff_false]
    intro hu
    obtain ⟨n, hn1, hn2⟩ := (hu.and hev).exists
    rw [Finset.card_eq_zero.1 hn2.1] at hn1
    exact Finset.notMem_empty _ hn1
  · have hne_α : Nonempty α := by
      obtain ⟨n, hncard, _⟩ := hev.exists
      have hpos : 0 < (S n).card := by omega
      obtain ⟨a, _⟩ := Finset.card_pos.1 hpos
      exact ⟨a⟩
    let a₀ : α := Classical.arbitrary α
    let pick : ∀ (n : ℕ) (i : Fin r), α := fun n i ↦
      if h : (S n).card = r then
        ((S n).equivFin.symm (Fin.cast h.symm i)).1
      else a₀
    let v : Fin r → Germ (hyperfilter ℕ : Filter ℕ) α := fun i ↦ (fun n ↦ pick n i)
    have hv_inj : Function.Injective v := by
      intro i j hij
      have hev_eq : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), pick n i = pick n j :=
        Germ.coe_eq.1 hij
      obtain ⟨n, ⟨hcard, _⟩, heq⟩ := (hev.and hev_eq).exists
      simp only [pick, hcard, ↓reduceDIte] at heq
      have hsub := ((S n).equivFin.symm).injective (Subtype.ext heq)
      exact Fin.ext (by simpa using congrArg Fin.val hsub)
    let F : Finset (Germ (hyperfilter ℕ : Filter ℕ) α) := Finset.univ.image v
    have hF_card : F.card = r := by
      rw [Finset.card_image_of_injective _ hv_inj, Finset.card_fin]
    have hF_sub : (↑F : Set (Germ (hyperfilter ℕ : Filter ℕ) α)) ⊆ starGenSet A := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      refine hev.mono fun n ⟨hcard, hSA⟩ ↦ ?_
      simp only [pick, hcard, ↓reduceDIte]
      exact hSA (Finset.mem_coe.2 (((S n).equivFin.symm (Fin.cast hcard.symm i)).2))
    refine ⟨F, ⟨hF_card, hF_sub⟩, ?_⟩
    ext x
    induction x using Germ.inductionOn with | _ u =>
    constructor
    · intro huS
      have hev_u : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), u n ∈ S n := Germ.liftRel_coe.1 huS
      have hev_ex : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ i : Fin r, pick n i = u n := by
        refine (hev.and hev_u).mono fun n ⟨⟨hcard, _⟩, hun⟩ ↦ ?_
        let j : Fin (S n).card := (S n).equivFin ⟨u n, hun⟩
        refine ⟨Fin.cast hcard j, ?_⟩
        have hcast : Fin.cast hcard.symm (Fin.cast hcard j) = j := by ext; rfl
        simp only [pick, hcard, ↓reduceDIte, hcast, j, Equiv.symm_apply_apply]
      obtain ⟨i, hi⟩ := (hyperfilter ℕ).eventually_exists_iff.1 hev_ex
      have heq_v : (u : Germ (hyperfilter ℕ : Filter ℕ) α) = v i := (Germ.coe_eq.2 hi).symm
      rw [heq_v]
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem v (Finset.mem_univ i))
    · intro huF
      obtain ⟨i, _, hi⟩ := Finset.mem_image.1 (Finset.mem_coe.1 huF)
      have hev_eq : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), pick n i = u n := Germ.coe_eq.1 hi
      refine Germ.liftRel_coe.2 ((hev.and hev_eq).mono fun n ⟨⟨hcard, _⟩, heq⟩ ↦ ?_)
      rw [← heq]
      simp only [pick, hcard, ↓reduceDIte]
      exact ((S n).equivFin.symm (Fin.cast hcard.symm i)).2

/-- **Exercise 17.3.1 Specialized to `ℕ*` and `k + 1` (Goldblatt p. 225)**:
`[*A]^{k+1} = *([A]^{k+1})` for every `A : Set ℕ` and `k : ℕ`. -/
theorem rSubsetsOfStarNat_eq_starRSubsetsNat (k : ℕ) (A : Set ℕ) :
    rSubsetsOfStar (k + 1) A = starRSubsets (k + 1) A :=
  rSubsetsOfStar_eq_starRSubsets (k + 1) A

/-- **Goldblatt §17.3 Colour-Reduction Lemma (p. 224)**:
If Infinite Ramsey's Theorem holds at exponent `r` for all `2`-colourings of all infinite sets of
type `α`, then by standard induction on the number of colours `k` (`k ≥ 1`), it holds for all
`k`-colourings! -/
theorem ramsey_colour_reduction {α : Type*} {r : ℕ}
    (hTwo : ∀ (B : Set α), B.Infinite → ∀ (c₂ : Finset α → Fin 2),
      ∃ H : Set α, H ⊆ B ∧ H.Infinite ∧ IsMonochromaticSet r c₂ H) :
    ∀ {k : ℕ}, 0 < k → ∀ (A : Set α), A.Infinite → ∀ (c : Finset α → Fin k),
      ∃ H : Set α, H ⊆ A ∧ H.Infinite ∧ IsMonochromaticSet r c H := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
      intro A hA c
      rcases Nat.eq_zero_or_pos k with rfl | hk_pos
      · refine ⟨A, Set.Subset.rfl, hA, ⟨0, Nat.one_pos⟩, fun s _ ↦ ?_⟩
        exact Fin.ext (by omega)
      · -- Group `{0, …, k - 1}` as black (`0`) and `{k}` (`Fin.last k`) as white (`1`).
        let c₂ : Finset α → Fin 2 := fun s ↦ if c s = Fin.last k then 1 else 0
        obtain ⟨B, hBA, hB_inf, col₂, hB_mono⟩ := hTwo A hA c₂
        fin_cases col₂
        · -- `B` gets colour `0` (`c s ≠ Fin.last k`), so `c` induces a `k`-colouring on `[B]^r`.
          let c' : Finset α → Fin k := fun s ↦
            if hlt : (c s).1 < k then ⟨(c s).1, hlt⟩ else ⟨0, hk_pos⟩
          obtain ⟨H, hHB, hH_inf, i', hH_mono⟩ := ih hk_pos B hB_inf c'
          refine ⟨H, hHB.trans hBA, hH_inf, i'.castSucc, fun s hs ↦ ?_⟩
          have hsB : s ∈ rSubsets r B := rSubsets_mono r hHB hs
          have hnot_last : c s ≠ Fin.last k := by
            have hc₂ := hB_mono s hsB
            intro hlast
            simp [c₂, hlast] at hc₂
          have hlt : (c s).1 < k := by
            have hle : (c s).1 ≤ k := Nat.le_of_lt_succ (c s).2
            exact lt_of_le_of_ne hle (fun heq ↦ hnot_last (Fin.ext heq))
          have hc'_eq : c' s = i' := hH_mono s hs
          simp only [c', hlt, ↓reduceDIte] at hc'_eq
          exact Fin.ext (by simpa using congrArg Fin.val hc'_eq)
        · -- `B` gets colour `1`, so every `s ∈ [B]^r` already has `c s = Fin.last k`!
          refine ⟨B, hBA, hB_inf, Fin.last k, fun s hs ↦ ?_⟩
          have hc₂ := hB_mono s hs
          by_contra hne
          simp [c₂, hne] at hc₂

/-- **Induced `r`-Subset Colouring via `omegaNat`** (Goldblatt §17.3, eq. (v), p. 225):
Given a colouring `c : Finset ℕ → Fin k` of `(r + 1)`-subsets, lift `n ↦ c (insert n s)` to `ℕ*`
and evaluate at the unlimited hypernatural `omegaNat` (`*(fun n ↦ c (insert n s))(omegaNat)`). -/
def inducedColouring {k : ℕ} (c : Finset ℕ → Fin k) (s : Finset ℕ) : Fin k :=
  starNatFinFun (fun n ↦ c (insert n s)) omegaNat

/-- For every `s : Finset ℕ`, `omegaNat ∈ starNatSet {n : ℕ | c (insert n s) = inducedColouring c s}`
(Goldblatt §17.3, pp. 225–226). -/
@[simp]
theorem omegaNat_mem_starNatSet_inducedColouring {k : ℕ} (c : Finset ℕ → Fin k) (s : Finset ℕ) :
    omegaNat ∈ starNatSet {n : ℕ | c (insert n s) = inducedColouring c s} :=
  (mem_starNatSet_eq_iff_starNatFinFun (fun n ↦ c (insert n s)) omegaNat _).2 rfl

/-- **Nonstandard Pre-Stabilized Sequence Lemma** (Goldblatt §17.3, eq. (iii), pp. 225–227):
Using `omegaNat ∈ ℕ*` and closure of `starNatSet` under finite intersections, for any `r : ℕ` and
`c : Finset ℕ → Fin k` (`0 < k`), there exists a strictly increasing sequence `x : ℕ → ℕ` such that
for every `m : ℕ` and every `r`-element subset `s ⊆ {x 0, …, x (m - 1)}`,
`c (insert (x m) s) = inducedColouring c s` (each `x m` behaves toward its predecessors like
`omegaNat`!). -/
theorem exists_stabilized_seq_omegaNat (r : ℕ) {k : ℕ} (c : Finset ℕ → Fin k) :
    ∃ x : ℕ → ℕ, StrictMono x ∧
      ∀ m : ℕ, ∀ s ∈ ((Finset.range m).image x).powersetCard r,
        c (insert (x m) s) = inducedColouring c s := by
  let B : Finset ℕ → Set ℕ := fun S ↦
    ⋂ s ∈ S.powersetCard r, {n : ℕ | c (insert n s) = inducedColouring c s}
  have hB : ∀ S : Finset ℕ, omegaNat ∈ starNatSet (B S) := by
    intro S
    dsimp only [B]
    rw [starNatSet_biInter_finset]
    exact Set.mem_iInter₂.2 fun s _ ↦ omegaNat_mem_starNatSet_inducedColouring c s
  obtain ⟨x, hx_mono, hx_mem⟩ := exists_strictMono_of_finset_omegaNat B hB
  refine ⟨x, hx_mono, fun m s hs ↦ ?_⟩
  exact Set.mem_iInter₂.1 (hx_mem m) s hs

/-- Nonstandard base case `r = 1` of Infinite Ramsey's Theorem on `ℕ` directly via `*c(omegaNat)`:
`H = {n : ℕ | c {n} = *(fun n ↦ c {n})(omegaNat)}` contains `omegaNat` in `*H`, hence is infinite
and `1`-monochromatic (Goldblatt §17.2–17.3). -/
theorem infinite_ramsey_r_one_omegaNat {k : ℕ} (c : Finset ℕ → Fin k) :
    ∃ H : Set ℕ, ∃ i₀ : Fin k,
      omegaNat ∈ starNatSet H ∧ H.Infinite ∧ IsMonochromatic 1 c H i₀ := by
  let i₀ : Fin k := starNatFinFun (fun n ↦ c {n}) omegaNat
  let H : Set ℕ := {n : ℕ | c {n} = i₀}
  have hω : omegaNat ∈ starNatSet H :=
    (mem_starNatSet_eq_iff_starNatFinFun (fun n ↦ c {n}) omegaNat i₀).2 rfl
  refine ⟨H, i₀, hω, omegaNat_mem_starNatSet_infinite hω, ?_⟩
  intro s hs
  obtain ⟨n, hn, rfl⟩ := mem_rSubsets_one_iff.1 hs
  exact hn

/-- **Infinite Ramsey's Theorem on `ℕ` (`Set.univ`)** (Goldblatt §17.3, pp. 224–227):
Proved by induction on `r` using `omegaNat ∈ ℕ*` and `inducedColouring`. -/
theorem infinite_ramsey_nat_univ (r : ℕ) {k : ℕ} (hk : 0 < k) (c : Finset ℕ → Fin k) :
    ∃ H : Set ℕ, ∃ i₀ : Fin k, H.Infinite ∧ IsMonochromatic r c H i₀ := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk) with ⟨k', rfl⟩
  induction r generalizing c with
  | zero =>
      refine ⟨Set.univ, c ∅, Set.infinite_univ, fun s hs ↦ ?_⟩
      rw [rSubsets_zero, Set.mem_singleton_iff] at hs
      rw [hs]
  | succ r ih =>
      -- Step `r → r + 1` via `omegaNat`: build `x_0 < x_1 < …` stabilized for `inducedColouring c`.
      obtain ⟨x, hx_mono, hx_stab⟩ := exists_stabilized_seq_omegaNat r c
      let cPull : Finset ℕ → Fin (k' + 1) := fun u ↦ inducedColouring c (u.image x)
      obtain ⟨M, i₀, hM_inf, hM_mono⟩ := ih cPull
      refine ⟨x '' M, i₀, hM_inf.image hx_mono.injective.injOn, ?_⟩
      intro t ⟨ht_card, ht_sub⟩
      -- Pull `t ⊆ x '' M` back along the strictly increasing sequence `x`.
      -- Every element `y ∈ t` has a unique preimage `m ∈ M` with `x m = y`.
      have ht_in_range : ∀ y ∈ t, ∃ m ∈ M, x m = y := fun y hy ↦ ht_sub (Finset.mem_coe.2 hy)
      let pre : ℕ → ℕ := fun y ↦ if h : ∃ m ∈ M, x m = y then h.choose else 0
      have hpre_spec : ∀ y ∈ t, pre y ∈ M ∧ x (pre y) = y := by
        intro y hy
        have hex := ht_in_range y hy
        simpa only [pre, hex, ↓reduceDIte] using hex.choose_spec
      let u : Finset ℕ := t.image pre
      have hu_image : u.image x = t := by
        ext y
        simp only [u, Finset.mem_image]
        constructor
        · rintro ⟨m, ⟨z, hz, rfl⟩, rfl⟩
          rw [(hpre_spec z hz).2]
          exact hz
        · intro hy
          exact ⟨pre y, ⟨y, hy, rfl⟩, (hpre_spec y hy).2⟩
      have hu_card : u.card = r + 1 := by
        have hcard_eq : (u.image x).card = u.card :=
          Finset.card_image_of_injective u hx_mono.injective
        rw [← hcard_eq, hu_image, ht_card]
      have hu_ne : u.Nonempty := Finset.card_pos.1 (by omega)
      let mMax : ℕ := u.max' hu_ne
      have hmMax_mem : mMax ∈ u := Finset.max'_mem u hu_ne
      let uInit : Finset ℕ := u.erase mMax
      have huInit_card : uInit.card = r := by
        rw [Finset.card_erase_of_mem hmMax_mem, hu_card]
        omega
      have huInit_sub_M : (↑uInit : Set ℕ) ⊆ M := by
        intro m hm
        have hmu : m ∈ u := Finset.mem_of_mem_erase (Finset.mem_coe.1 hm)
        obtain ⟨y, hyt, rfl⟩ := Finset.mem_image.1 hmu
        exact (hpre_spec y hyt).1
      have huInit_lt : ∀ m ∈ uInit, m < mMax := by
        intro m hm
        have hne : m ≠ mMax := (Finset.mem_erase.1 hm).1
        have hle : m ≤ mMax := Finset.le_max' u m (Finset.mem_erase.1 hm).2
        exact lt_of_le_of_ne hle hne
      let s : Finset ℕ := uInit.image x
      have hs_mem_pow : s ∈ ((Finset.range mMax).image x).powersetCard r := by
        rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro y hy
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hy
          exact Finset.mem_image.2 ⟨m, Finset.mem_range.2 (huInit_lt m hm), rfl⟩
        · exact Finset.card_image_of_injective uInit hx_mono.injective |>.trans huInit_card
      have ht_eq_insert : t = insert (x mMax) s := by
        rw [← hu_image, ← Finset.insert_erase hmMax_mem, Finset.image_insert]
      rw [ht_eq_insert, hx_stab mMax s hs_mem_pow]
      exact hM_mono uInit ⟨huInit_card, huInit_sub_M⟩

/-- **Infinite Ramsey's Theorem for Arbitrary Infinite Sets** (Goldblatt §17.1 & §17.3,
pp. 222, 224–227):
For any infinite subset `X ⊆ α`, any `r : ℕ`, any `k : ℕ` (`0 < k`), and any `k`-colouring
`c : Finset α → Fin k` of `r`-subsets, there exists an infinite subset `H ⊆ X` and a colour
`i₀ : Fin k` such that `IsMonochromatic r c H i₀`. -/
theorem infinite_ramsey_set {α : Type*} (r : ℕ) {k : ℕ} (hk : 0 < k)
    {X : Set α} (hX : X.Infinite) (c : Finset α → Fin k) :
    ∃ H : Set α, ∃ i₀ : Fin k, H ⊆ X ∧ H.Infinite ∧ IsMonochromatic r c H i₀ := by
  classical
  let e : ℕ ↪ X := hX.natEmbedding
  let f : ℕ ↪ α := e.trans (Function.Embedding.subtype _)
  obtain ⟨M, i₀, hM_inf, hM_mono⟩ := infinite_ramsey_nat_univ r hk (fun u ↦ c (u.map f))
  refine ⟨f '' M, i₀, ?_, hM_inf.image f.injective.injOn, ?_⟩
  · rintro _ ⟨n, _, rfl⟩
    exact (e n).2
  · intro s ⟨hs_card, hs_sub⟩
    -- Pull `s ⊆ f '' M` back along `f : ℕ ↪ α`.
    have hs_ex : ∀ y ∈ s, ∃ n ∈ M, f n = y := fun y hy ↦ hs_sub (Finset.mem_coe.2 hy)
    let inv : α → ℕ := fun y ↦ if h : ∃ n ∈ M, f n = y then h.choose else 0
    have hinv_spec : ∀ y ∈ s, inv y ∈ M ∧ f (inv y) = y := by
      intro y hy
      have hex := hs_ex y hy
      simpa only [inv, hex, ↓reduceDIte] using hex.choose_spec
    let u : Finset ℕ := s.image inv
    have hu_map : u.map f = s := by
      ext y
      simp only [u, Finset.mem_map, Finset.mem_image]
      constructor
      · rintro ⟨n, ⟨z, hz, rfl⟩, rfl⟩
        rw [(hinv_spec z hz).2]
        exact hz
      · intro hy
        exact ⟨inv y, ⟨y, hy, rfl⟩, (hinv_spec y hy).2⟩
    have hu_card : u.card = r := by
      rw [← Finset.card_map f, hu_map, hs_card]
    have hu_sub : (↑u : Set ℕ) ⊆ M := by
      intro n hn
      obtain ⟨y, hys, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hn)
      exact (hinv_spec y hys).1
    rw [← hu_map]
    exact hM_mono u ⟨hu_card, hu_sub⟩

/-- **Infinite Ramsey's Theorem (`infinite_ramsey`, `Set ℕ` Specialization)**
(Goldblatt Theorem 17.3.1, pp. 224–227):
For all `r k : ℕ` (`0 < k`), every infinite subset `X ⊆ ℕ`, and every `k`-colouring
`c : Finset ℕ → Fin k`, there exists an infinite subset `H ⊆ X` and a colour `i₀ : Fin k` such
that every `r`-element subset `s` of `H` has `c s = i₀`. -/
theorem infinite_ramsey (r : ℕ) {k : ℕ} (hk : 0 < k)
    {X : Set ℕ} (hX : X.Infinite) (c : Finset ℕ → Fin k) :
    ∃ H : Set ℕ, ∃ i₀ : Fin k, H ⊆ X ∧ H.Infinite ∧ IsMonochromatic r c H i₀ :=
  infinite_ramsey_set r hk hX c

/-- **Infinite Ramsey's Theorem (Cover / Partition Form)** (Goldblatt §17.1, p. 222):
If `A : Set α` is infinite and `[A]^r ⊆ ⋃ i : Fin k, C i` (`0 < k`), then there exists an infinite
subset `B ⊆ A` and an index `i : Fin k` such that `[B]^r ⊆ C i`. -/
theorem infinite_ramsey_cover {α : Type*} (r : ℕ) {k : ℕ} (hk : 0 < k)
    {A : Set α} (hA : A.Infinite) {C : Fin k → Set (Finset α)}
    (hcover : rSubsets r A ⊆ ⋃ i : Fin k, C i) :
    ∃ B : Set α, ∃ i : Fin k, B ⊆ A ∧ B.Infinite ∧ rSubsets r B ⊆ C i := by
  let c : Finset α → Fin k := fun s ↦
    if hs : s ∈ rSubsets r A then (Set.mem_iUnion.1 (hcover hs)).choose else ⟨0, hk⟩
  obtain ⟨B, i, hBA, hB_inf, hB_mono⟩ := infinite_ramsey_set r hk hA c
  refine ⟨B, i, hBA, hB_inf, fun s hs ↦ ?_⟩
  have hsA : s ∈ rSubsets r A := rSubsets_mono r hBA hs
  have hci : c s = i := hB_mono s hs
  simp only [c, hsA, ↓reduceDIte] at hci
  rw [← hci]
  exact (Set.mem_iUnion.1 (hcover hsA)).choose_spec

/-! ### Corollaries of Infinite Ramsey's Theorem (§17.1 & §17.3) -/

/-- Helper lemma: every infinite subset `H : Set ℕ` can be enumerated by a strictly increasing
sequence `φ : ℕ → ℕ` with `∀ n, φ n ∈ H`. -/
lemma exists_strictMono_mem_of_infinite {H : Set ℕ} (hH : H.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n : ℕ, φ n ∈ H := by
  have hgt : ∀ b : ℕ, ∃ x : ℕ, x ∈ H ∧ b < x := by
    intro b
    by_contra hno
    push Not at hno
    have hsub : H ⊆ Set.Iic b := fun x hx ↦ hno x hx
    exact hH ((Set.finite_Iic b).subset hsub)
  have hne : ∃ x : ℕ, x ∈ H := by
    obtain ⟨x, hx, _⟩ := hgt 0
    exact ⟨x, hx⟩
  let φ : ℕ → ℕ := Nat.rec hne.choose (fun _ prev ↦ (hgt prev).choose)
  refine ⟨φ, strictMono_nat_of_lt_succ fun n ↦ ((hgt (φ n)).choose_spec).2, fun n ↦ ?_⟩
  cases n with
  | zero => exact hne.choose_spec
  | succ n => exact ((hgt (φ n)).choose_spec).1

/-- **Theorem 17.1.1 — Proof from Infinite Ramsey's Theorem** (Goldblatt §17.1, p. 222):
Every infinite partially ordered set `(P, ≤)` contains an infinite strictly increasing sequence,
an infinite strictly decreasing sequence, or an infinite antichain, obtained by `2`-colouring
`[P]^2` into comparable pairs (`0`) and incomparable pairs (`1`). -/
theorem infinite_poset_chain_or_antichain_via_ramsey {P : Type*} [PartialOrder P] [Infinite P] :
    (∃ p : ℕ → P, StrictMono p) ∨
    (∃ p : ℕ → P, StrictAnti p) ∨
    (∃ p : ℕ → P, IsAntichainSeq p) := by
  classical
  let c : Finset P → Fin 2 := fun s ↦
    if ∀ x ∈ s, ∀ y ∈ s, x ≤ y ∨ y ≤ x then 0 else 1
  obtain ⟨Q, col, _, hQ_inf, hQ_mono⟩ :=
    infinite_ramsey_set 2 (by decide : 0 < 2) (Set.infinite_univ : (Set.univ : Set P).Infinite) c
  fin_cases col
  · -- `Q` is an infinite chain (`∀ x ∈ Q, ∀ y ∈ Q, x ≤ y ∨ y ≤ x`).
    have hChain : ∀ x ∈ Q, ∀ y ∈ Q, x ≤ y ∨ y ≤ x := by
      intro x hx y hy
      by_cases hxy : x = y
      · subst hxy
        exact Or.inl le_rfl
      · have hs : ({x, y} : Finset P) ∈ rSubsets 2 Q := by
          refine ⟨Finset.card_pair hxy, ?_⟩
          intro z hz
          rcases Finset.mem_insert.1 (Finset.mem_coe.1 hz) with rfl | hzy
          · exact hx
          · rw [Finset.mem_singleton.1 hzy]
            exact hy
        have hc0 := hQ_mono {x, y} hs
        dsimp only [c] at hc0
        split_ifs at hc0 with hall
        · exact hall x (by simp) y (by simp)
        · nomatch hc0
    -- Either every nonempty `S ⊆ Q` has a least element, or some nonempty `S ⊆ Q` has no least.
    by_cases hWF : ∀ S : Set P, S ⊆ Q → S.Nonempty → ∃ m ∈ S, ∀ y ∈ S, m ≤ y
    · -- Well-ordered chain: remove minimal elements one by one to get `p 0 < p 1 < …`.
      have hex_min : ∀ V : Finset P, ∃ m ∈ Q \ (↑V : Set P), ∀ y ∈ Q \ (↑V : Set P), m ≤ y := by
        intro V
        have hdiff_inf : (Q \ (↑V : Set P)).Infinite := fun hfin ↦
          hQ_inf ((hfin.union V.finite_toSet).subset fun x hx ↦ by
            by_cases hxV : x ∈ (↑V : Set P)
            · exact Or.inr hxV
            · exact Or.inl ⟨hx, hxV⟩)
        exact hWF (Q \ (↑V : Set P)) Set.sdiff_subset hdiff_inf.nonempty
      let step : ℕ → P × Finset P :=
        Nat.rec ((hex_min ∅).choose, ∅) fun _ st ↦
          let V' := insert st.1 st.2
          ((hex_min V').choose, V')
      let p : ℕ → P := fun n ↦ (step n).1
      have hp_spec : ∀ n : ℕ, p n ∈ Q \ (↑(step n).2 : Set P) ∧
          ∀ y ∈ Q \ (↑(step n).2 : Set P), p n ≤ y := by
        intro n
        cases n with
        | zero => exact (hex_min ∅).choose_spec
        | succ n => exact (hex_min (insert (step n).1 (step n).2)).choose_spec
      refine Or.inl ⟨p, strictMono_nat_of_lt_succ fun n ↦ ?_⟩
      have hmem_succ : p (n + 1) ∈ Q \ (↑(insert (p n) (step n).2) : Set P) := (hp_spec (n + 1)).1
      have hmem_prev : p (n + 1) ∈ Q \ (↑(step n).2 : Set P) := by
        rw [Finset.coe_insert] at hmem_succ
        exact ⟨hmem_succ.1, fun h ↦ hmem_succ.2 (Set.mem_insert_of_mem _ h)⟩
      have hle : p n ≤ p (n + 1) := (hp_spec n).2 (p (n + 1)) hmem_prev
      have hne : p n ≠ p (n + 1) := by
        intro heq
        rw [Finset.coe_insert] at hmem_succ
        exact hmem_succ.2 (heq ▸ Set.mem_insert (p n) _)
      exact lt_of_le_of_ne hle hne
    · -- Non-well-ordered chain: some nonempty `S ⊆ Q` satisfies `∀ x ∈ S, ∃ y ∈ S, y < x`.
      push Not at hWF
      obtain ⟨S, hSQ, ⟨x₀, hx₀⟩, hno_min⟩ := hWF
      have hex_lt : ∀ x : S, ∃ y : S, y.1 < x.1 := by
        intro x
        obtain ⟨y, hyS, hnle⟩ := hno_min x.1 x.2
        rcases hChain x.1 (hSQ x.2) y (hSQ hyS) with hxy | hyx
        · exact absurd hxy hnle
        · exact ⟨⟨y, hyS⟩, lt_of_le_of_ne hyx fun heq ↦ hnle (heq ▸ le_rfl)⟩
      let f : S → S := fun x ↦ (hex_lt x).choose
      let sSeq : ℕ → S := fun n ↦ f^[n] ⟨x₀, hx₀⟩
      refine Or.inr (Or.inl ⟨fun n ↦ (sSeq n).1, strictAnti_nat_of_succ_lt fun n ↦ ?_⟩)
      simp only [sSeq, Function.iterate_succ_apply']
      exact (hex_lt (sSeq n)).choose_spec
  · -- `Q` is pairwise incomparable: any injection `ℕ ↪ Q` is an antichain!
    let e : ℕ ↪ Q := hQ_inf.natEmbedding
    refine Or.inr (Or.inr ⟨fun n ↦ (e n).1, fun m n hmn ↦ ?_⟩)
    have hne : (e m).1 ≠ (e n).1 := fun h ↦ hmn (e.injective (Subtype.ext h))
    have hs : ({(e m).1, (e n).1} : Finset P) ∈ rSubsets 2 Q := by
      refine ⟨Finset.card_pair hne, ?_⟩
      intro z hz
      rcases Finset.mem_insert.1 (Finset.mem_coe.1 hz) with rfl | hzn
      · exact (e m).2
      · rw [Finset.mem_singleton.1 hzn]
        exact (e n).2
    have hc1 := hQ_mono {(e m).1, (e n).1} hs
    have hnot_comp : ¬ ((e m).1 ≤ (e n).1 ∨ (e n).1 ≤ (e m).1) := by
      intro hcomp
      have hall : ∀ a ∈ ({(e m).1, (e n).1} : Finset P),
          ∀ b ∈ ({(e m).1, (e n).1} : Finset P), a ≤ b ∨ b ≤ a := by
        intro a ha b hb
        rcases Finset.mem_insert.1 ha with rfl | ha' <;>
          rcases Finset.mem_insert.1 hb with rfl | hb'
        · exact Or.inl le_rfl
        · rw [Finset.mem_singleton.1 hb']
          exact hcomp
        · rw [Finset.mem_singleton.1 ha']
          exact hcomp.symm
        · rw [Finset.mem_singleton.1 ha', Finset.mem_singleton.1 hb']
          exact Or.inl le_rfl
      dsimp only [c] at hc1
      split_ifs at hc1
      nomatch hc1
    exact ⟨fun h ↦ hnot_comp (Or.inl h), fun h ↦ hnot_comp (Or.inr h)⟩

/-- **Erdős–Szekeres Infinite Monotone Subsequence Theorem (General Linear Order)**
(Goldblatt §17.3 Corollary):
Every sequence `a : ℕ → α` in a linearly ordered type `α` admits a strictly increasing index
sequence `φ : ℕ → ℕ` such that `a ∘ φ` is either monotone nondecreasing (`Monotone (a ∘ φ)`) or
strictly decreasing (`StrictAnti (a ∘ φ)`). -/
theorem exists_monotone_subseq_linearOrder {α : Type*} [LinearOrder α] (a : ℕ → α) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (Monotone (a ∘ φ) ∨ StrictAnti (a ∘ φ)) := by
  -- `2`-colour `[ℕ]^2` by comparing `a (min s)` and `a (max s)`.
  let c : Finset ℕ → Fin 2 := fun s ↦
    if hs : s.Nonempty then
      if a (s.min' hs) ≤ a (s.max' hs) then 0 else 1
    else 0
  obtain ⟨H, col, _, hH_inf, hH_mono⟩ :=
    infinite_ramsey 2 (by decide : 0 < 2) Set.infinite_univ c
  obtain ⟨φ, hφ_mono, hφ_mem⟩ := exists_strictMono_mem_of_infinite hH_inf
  refine ⟨φ, hφ_mono, ?_⟩
  fin_cases col
  · left
    intro m n hmn
    rcases eq_or_lt_of_le hmn with rfl | hlt
    · exact le_rfl
    · have hφlt : φ m < φ n := hφ_mono hlt
      let s : Finset ℕ := {φ m, φ n}
      have hs : s ∈ rSubsets 2 H := by
        refine ⟨Finset.card_pair hφlt.ne, ?_⟩
        intro z hz
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hz) with rfl | hzn
        · exact hφ_mem m
        · rw [Finset.mem_singleton.1 hzn]
          exact hφ_mem n
      have hne : s.Nonempty := ⟨φ m, Finset.mem_insert_self _ _⟩
      have hmin : s.min' hne = φ m := by
        apply le_antisymm (Finset.min'_le s (φ m) (Finset.mem_insert_self _ _))
        refine Finset.le_min' s hne (φ m) fun z hz ↦ ?_
        rcases Finset.mem_insert.1 hz with rfl | hzn
        · exact le_rfl
        · rw [Finset.mem_singleton.1 hzn]
          exact hφlt.le
      have hmax : s.max' hne = φ n := by
        apply le_antisymm
        · refine Finset.max'_le s hne (φ n) fun z hz ↦ ?_
          rcases Finset.mem_insert.1 hz with rfl | hzn
          · exact hφlt.le
          · rw [Finset.mem_singleton.1 hzn]
        · exact Finset.le_max' s (φ n) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hc0 := hH_mono s hs
      simp only [c, hne, ↓reduceDIte, hmin, hmax] at hc0
      split_ifs at hc0 with hle
      · exact hle
      · nomatch hc0
  · right
    intro m n hlt
    have hφlt : φ m < φ n := hφ_mono hlt
    let s : Finset ℕ := {φ m, φ n}
    have hs : s ∈ rSubsets 2 H := by
      refine ⟨Finset.card_pair hφlt.ne, ?_⟩
      intro z hz
      rcases Finset.mem_insert.1 (Finset.mem_coe.1 hz) with rfl | hzn
      · exact hφ_mem m
      · rw [Finset.mem_singleton.1 hzn]
        exact hφ_mem n
    have hne : s.Nonempty := ⟨φ m, Finset.mem_insert_self _ _⟩
    have hmin : s.min' hne = φ m := by
      apply le_antisymm (Finset.min'_le s (φ m) (Finset.mem_insert_self _ _))
      refine Finset.le_min' s hne (φ m) fun z hz ↦ ?_
      rcases Finset.mem_insert.1 hz with rfl | hzn
      · exact le_rfl
      · rw [Finset.mem_singleton.1 hzn]
        exact hφlt.le
    have hmax : s.max' hne = φ n := by
      apply le_antisymm
      · refine Finset.max'_le s hne (φ n) fun z hz ↦ ?_
        rcases Finset.mem_insert.1 hz with rfl | hzn
        · exact hφlt.le
        · rw [Finset.mem_singleton.1 hzn]
      · exact Finset.le_max' s (φ n) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hc1 := hH_mono s hs
    simp only [c, hne, ↓reduceDIte, hmin, hmax] at hc1
    split_ifs at hc1 with hle
    · nomatch hc1
    · exact lt_of_not_ge hle

/-- **Monotone Subsequence Theorem for Real Sequences** (Goldblatt §17.3 Corollary):
Every real sequence `a : ℕ → ℝ` has a monotone (either nondecreasing or nonincreasing) subsequence. -/
theorem exists_monotone_subseq (a : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (Monotone (a ∘ φ) ∨ Antitone (a ∘ φ)) := by
  obtain ⟨φ, hφ, hmono | hanti⟩ := exists_monotone_subseq_linearOrder a
  · exact ⟨φ, hφ, Or.inl hmono⟩
  · exact ⟨φ, hφ, Or.inr hanti.antitone⟩

/-- **Bolzano–Weierstrass Theorem via Infinite Ramsey** (Goldblatt §17.3 Corollary):
Every bounded sequence `a : ℕ → ℝ` admits a convergent subsequence. -/
theorem exists_convergent_subseq_of_bdd {a : ℕ → ℝ} (hbdd : ∃ M : ℝ, ∀ n : ℕ, |a n| ≤ M) :
    ∃ φ : ℕ → ℕ, ∃ L : ℝ, StrictMono φ ∧ Tendsto (a ∘ φ) atTop (𝓝 L) := by
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨φ, hφ, hmono | hanti⟩ := exists_monotone_subseq a
  · have hup : BddAbove (Set.range (a ∘ φ)) := by
      refine ⟨M, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact (le_abs_self _).trans (hM (φ n))
    exact ⟨φ, ⨆ n, a (φ n), hφ, tendsto_atTop_ciSup hmono hup⟩
  · have hdn : BddBelow (Set.range (a ∘ φ)) := by
      refine ⟨-M, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact (abs_le.1 (hM (φ n))).1
    exact ⟨φ, ⨅ n, a (φ n), hφ, tendsto_atTop_ciInf hanti hdn⟩

/-!
## §17.4 — Nonstandard Proof of the Finite Ramsey Theorem & Exercise 17.4.1 (pp. 227–228)
-/

/-- **Finite Ramsey's Theorem (`0`-Indexed Initial Segments `{0, …, N}`)**
(Goldblatt Theorem 17.4.1, pp. 227–228):
For any `r k m : ℕ` with `0 < k`, there exists `N : ℕ` such that every `k`-colouring
`c : Finset ℕ → Fin k` of `r`-subsets of `{0, …, N}` (`Finset.Iic N`) admits a monochromatic subset
`M ⊆ Finset.Iic N` of cardinality `M.card = m`.

Proved from Infinite Ramsey's Theorem via ultrapower compactness (`hyperfilter ℕ`) following
Goldblatt §17.4! -/
theorem finite_ramsey (r : ℕ) {k : ℕ} (hk : 0 < k) (m : ℕ) :
    ∃ N : ℕ, ∀ c : Finset ℕ → Fin k,
      ∃ M : Finset ℕ, ∃ i₀ : Fin k,
        M ⊆ Finset.Iic N ∧ M.card = m ∧ IsMonochromatic r c (↑M : Set ℕ) i₀ := by
  by_contra hno
  push Not at hno
  choose cSeq hcSeq using hno
  -- Form the standard colouring `c(s) := [n ↦ c_n(s)] ∈ *(Fin k) ≃ Fin k` on all of `ℕ`!
  let c : Finset ℕ → Fin k := fun s ↦ starNatFinFun (fun n ↦ cSeq n s) omegaNat
  obtain ⟨H, i₀, _, hH_inf, hH_mono⟩ := infinite_ramsey r hk Set.infinite_univ c
  obtain ⟨M, hMH, hM_card⟩ := hH_inf.exists_subset_card_eq m
  -- Every `s ∈ M.powersetCard r` has `c s = i₀`, so `cSeq n s = i₀` for `hyperfilter ℕ`-almost all `n`.
  have hev_col : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
      ∀ s ∈ M.powersetCard r, cSeq n s = i₀ := by
    rw [eventually_all_finset]
    intro s hs
    have hcs : c s = i₀ :=
      hH_mono s (rSubsets_mono r hMH (mem_rSubsets_coe_iff_mem_powersetCard.2 hs))
    exact (mem_starNatSet_eq_iff_starNatFinFun (fun n ↦ cSeq n s) omegaNat i₀).2 hcs
  let maxM : ℕ := M.sup id
  have hev_ge : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), maxM ≤ n :=
    Nat.hyperfilter_le_atTop (eventually_ge_atTop maxM)
  obtain ⟨n, hn_col, hn_ge⟩ := (hev_col.and hev_ge).exists
  have hM_sub : M ⊆ Finset.Iic n := fun x hx ↦
    Finset.mem_Iic.2 ((Finset.le_sup (f := id) hx).trans hn_ge)
  have hM_mono : IsMonochromatic r (cSeq n) (↑M : Set ℕ) i₀ :=
    isMonochromatic_coe_iff_powersetCard.2 hn_col
  exact hcSeq n M i₀ hM_sub hM_card hM_mono

/-- **Finite Ramsey's Theorem (`1`-Indexed `{1, …, n}`, Verbatim Goldblatt §17.4, pp. 227–228)**:
For any `r k m : ℕ` with `0 < k`, there exists `n : ℕ` such that for any `k`-colouring
`c : Finset ℕ → Fin k` of `[{1, …, n}]^r` (`Finset.Icc 1 n`), there is a monochromatic subset
`B ⊆ Finset.Icc 1 n` with `m ≤ B.card` (in fact `B.card = m`). -/
theorem finite_ramsey_Icc_one (r : ℕ) {k : ℕ} (hk : 0 < k) (m : ℕ) :
    ∃ n : ℕ, ∀ c : Finset ℕ → Fin k,
      ∃ B : Finset ℕ, ∃ i₀ : Fin k,
        B ⊆ Finset.Icc 1 n ∧ B.card = m ∧ m ≤ B.card ∧ IsMonochromatic r c (↑B : Set ℕ) i₀ := by
  by_contra hno
  push Not at hno
  choose cSeq hcSeq using hno
  let c : Finset ℕ → Fin k := fun s ↦ starNatFinFun (fun n ↦ cSeq n s) omegaNat
  have hIci_inf : (Set.Ici (1 : ℕ)).Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ ↦ j + 1)
      (fun a b hab ↦ by dsimp at hab; omega) fun j ↦ ?_
    exact Nat.succ_pos j
  obtain ⟨D, i₀, hDIci, hD_inf, hD_mono⟩ := infinite_ramsey r hk hIci_inf c
  obtain ⟨B, hBD, hB_card⟩ := hD_inf.exists_subset_card_eq m
  have hev_col : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
      ∀ s ∈ B.powersetCard r, cSeq n s = i₀ := by
    rw [eventually_all_finset]
    intro s hs
    have hcs : c s = i₀ :=
      hD_mono s (rSubsets_mono r hBD (mem_rSubsets_coe_iff_mem_powersetCard.2 hs))
    exact (mem_starNatSet_eq_iff_starNatFinFun (fun n ↦ cSeq n s) omegaNat i₀).2 hcs
  let maxB : ℕ := B.sup id
  have hev_ge : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), maxB ≤ n :=
    Nat.hyperfilter_le_atTop (eventually_ge_atTop maxB)
  obtain ⟨n, hn_col, hn_ge⟩ := (hev_col.and hev_ge).exists
  have hB_sub : B ⊆ Finset.Icc 1 n := fun x hx ↦
    Finset.mem_Icc.2 ⟨hDIci (hBD (Finset.mem_coe.2 hx)), (Finset.le_sup (f := id) hx).trans hn_ge⟩
  have hB_mono : IsMonochromatic r (cSeq n) (↑B : Set ℕ) i₀ :=
    isMonochromatic_coe_iff_powersetCard.2 hn_col
  exact hcSeq n B i₀ hB_sub hB_card hB_card.ge hB_mono

/-- **Finite Ramsey's Theorem on `Fin N`** (Goldblatt Theorem 17.4.1):
For any `r k m : ℕ` (`0 < k`), there exists `N : ℕ` such that every `k`-colouring of `[Fin N]^r`
admits a monochromatic subset `M : Finset (Fin N)` of cardinality `m`. -/
theorem finite_ramsey_fin (r : ℕ) {k : ℕ} (hk : 0 < k) (m : ℕ) :
    ∃ N : ℕ, ∀ c : Finset (Fin N) → Fin k,
      ∃ M : Finset (Fin N), M.card = m ∧ IsMonochromaticSet r c (↑M : Set (Fin N)) := by
  obtain ⟨N₀, hN₀⟩ := finite_ramsey r hk m
  refine ⟨N₀ + 1, fun c ↦ ?_⟩
  let toFin : ℕ → Fin (N₀ + 1) := fun x ↦
    if hx : x < N₀ + 1 then ⟨x, hx⟩ else ⟨0, Nat.succ_pos N₀⟩
  let cNat : Finset ℕ → Fin k := fun s ↦ c (s.image toFin)
  obtain ⟨M₀, i₀, hM₀_sub, hM₀_card, hM₀_mono⟩ := hN₀ cNat
  have hinj : Set.InjOn toFin (↑M₀ : Set ℕ) := by
    intro a ha b hb hab
    have ha_lt : a < N₀ + 1 := Nat.lt_succ_of_le (Finset.mem_Iic.1 (hM₀_sub ha))
    have hb_lt : b < N₀ + 1 := Nat.lt_succ_of_le (Finset.mem_Iic.1 (hM₀_sub hb))
    simp only [toFin, ha_lt, hb_lt, ↓reduceDIte, Fin.mk.injEq] at hab
    exact hab
  refine ⟨M₀.image toFin, Finset.card_image_of_injOn hinj |>.trans hM₀_card, i₀, ?_⟩
  intro s ⟨hs_card, hs_sub⟩
  let sNat : Finset ℕ := s.map ⟨Fin.val, Fin.val_injective⟩
  have hsNat_sub : (↑sNat : Set ℕ) ⊆ (↑M₀ : Set ℕ) := by
    intro x hx
    obtain ⟨y, hys, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hx)
    obtain ⟨z, hzM₀, hzy⟩ := Finset.mem_image.1 (Finset.mem_coe.1 (hs_sub (Finset.mem_coe.2 hys)))
    have hz_lt : z < N₀ + 1 := Nat.lt_succ_of_le (Finset.mem_Iic.1 (hM₀_sub hzM₀))
    have hzy' : z = y.1 := by
      have := congrArg Fin.val hzy
      simpa only [toFin, hz_lt, ↓reduceDIte] using this
    show y.1 ∈ M₀
    rw [← hzy']
    exact hzM₀
  have hsNat_img : sNat.image toFin = s := by
    ext y
    simp only [sNat, Finset.mem_image, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨_, ⟨z, hzs, rfl⟩, rfl⟩
      simpa only [toFin, z.2, ↓reduceDIte] using hzs
    · intro hys
      exact ⟨y.1, ⟨y, hys, rfl⟩, by simp only [toFin, y.2, ↓reduceDIte]⟩
  have hsNat_card : sNat.card = r := by simpa [sNat] using hs_card
  have hval := hM₀_mono sNat ⟨hsNat_card, hsNat_sub⟩
  simpa only [cNat, hsNat_img] using hval

/-! ### Exercise 17.4.1 (p. 228): Explicit Formula `ψ(n)`, `*ψ(N)`, and Ultrapower Transfer -/

/-- Goldblatt §17.4 & Exercise 17.4.1 (pp. 227–228): The standard first-order Ramsey predicate
`ψ(n)` asserting that every `k`-colouring of `[{1, …, n}]^r` has a monochromatic subset of
`{1, …, n}` of cardinality at least `m`. -/
def psiRamsey (r k m n : ℕ) : Prop :=
  ∀ c : Finset ℕ → Fin k,
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 n ∧ m ≤ B.card ∧ IsMonochromaticSet r c (↑B : Set ℕ)

/-- Goldblatt §17.4 & Exercise 17.4.1 (pp. 227–228): The internal / ultrapower transform `*ψ(N)`
on `ℕ*`: for every internal `k`-colouring `[c_idx]` of `r`-subsets, there exists a hyperfinite
subset `[B_idx] ⊆ {1, …, N}` of internal cardinality `|[B_idx]| ≥ m` and an internal colour
`[i_idx]` on which `[c_idx]` is internally monochromatic. -/
def starPsiRamsey (r k m : ℕ) (N : ℕ*) : Prop :=
  ∀ cSeq : ℕ → Finset ℕ → Fin k,
    ∃ B : ℕ → Finset ℕ, ∃ iSeq : ℕ → Fin k,
      internalNatSet (fun idx ↦ (B idx : Set ℕ)) ⊆ Set.Icc (1 : ℕ*) N ∧
      (m : ℕ*) ≤ ((fun idx ↦ (B idx).card) : ℕ*) ∧
      ∀ᶠ idx in (hyperfilter ℕ : Filter ℕ),
        IsMonochromatic r (cSeq idx) (↑(B idx) : Set ℕ) (iSeq idx)

/-- Helper identity: `Set.Icc (1 : ℕ*) (b : ℕ*) = internalNatSet (fun idx ↦ Set.Icc 1 (b idx))`. -/
theorem Icc_one_coe_eq_internalNatSet (b : ℕ → ℕ) :
    Set.Icc (1 : ℕ*) (b : ℕ*) = internalNatSet (fun idx ↦ Set.Icc 1 (b idx)) := by
  ext K
  induction K using Germ.inductionOn with | _ a =>
  rw [Set.mem_Icc, coe_mem_internalNatSet]
  simp only [Set.mem_Icc, eventually_and]
  exact and_congr Germ.coe_le Germ.coe_le

/-- **Exercise 17.4.1 — Łoś / Ultrapower Transfer Equivalence for `ψ`** (Goldblatt p. 228):
For any `b : ℕ → ℕ` and `0 < k`, `*ψ([b])` holds in `ℕ*` **if and only if**
`{idx : ℕ | ψ(b idx)} ∈ hyperfilter ℕ`. -/
theorem starPsiRamsey_coe_iff (r : ℕ) {k : ℕ} (hk : 0 < k) (m : ℕ) (b : ℕ → ℕ) :
    starPsiRamsey r k m (b : ℕ*) ↔
      ∀ᶠ idx in (hyperfilter ℕ : Filter ℕ), psiRamsey r k m (b idx) := by
  constructor
  · intro hstar
    by_contra hnot
    have hev_not : ∀ᶠ idx in (hyperfilter ℕ : Filter ℕ), ¬ psiRamsey r k m (b idx) :=
      Ultrafilter.eventually_not.2 hnot
    let cDefault : Finset ℕ → Fin k := fun _ ↦ ⟨0, hk⟩
    let cSeq : ℕ → Finset ℕ → Fin k := fun idx ↦
      if h : ∃ c : Finset ℕ → Fin k,
          ¬ ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 (b idx) ∧ m ≤ B.card ∧
            IsMonochromaticSet r c (↑B : Set ℕ)
      then h.choose else cDefault
    obtain ⟨B, iSeq, hsub, hcard, hmono⟩ := hstar cSeq
    rw [Icc_one_coe_eq_internalNatSet, internalNatSet_subset_iff] at hsub
    have hcard_ev : ∀ᶠ idx in (hyperfilter ℕ : Filter ℕ), m ≤ (B idx).card :=
      Germ.coe_le.1 hcard
    obtain ⟨idx, ⟨⟨hnot_psi, hBsub⟩, hBm⟩, hBmono⟩ :=
      (((hev_not.and hsub).and hcard_ev).and hmono).exists
    have hex_bad : ∃ c : Finset ℕ → Fin k,
        ¬ ∃ B' : Finset ℕ, B' ⊆ Finset.Icc 1 (b idx) ∧ m ≤ B'.card ∧
          IsMonochromaticSet r c (↑B' : Set ℕ) := by
      unfold psiRamsey at hnot_psi
      push Not at hnot_psi
      obtain ⟨c, hc⟩ := hnot_psi
      exact ⟨c, fun ⟨B', h1, h2, h3⟩ ↦ hc B' h1 h2 h3⟩
    have hcSeq_eq : cSeq idx = hex_bad.choose := by simp only [cSeq, hex_bad, ↓reduceDIte]
    rw [hcSeq_eq] at hBmono
    have hB_finset_sub : B idx ⊆ Finset.Icc 1 (b idx) := fun x hx ↦ by
      simpa using hBsub (Finset.mem_coe.2 hx)
    exact hex_bad.choose_spec ⟨B idx, hB_finset_sub, hBm, iSeq idx, hBmono⟩
  · intro hev cSeq
    let B : ℕ → Finset ℕ := fun idx ↦
      if h : ∃ B' : Finset ℕ, B' ⊆ Finset.Icc 1 (b idx) ∧ m ≤ B'.card ∧
          IsMonochromaticSet r (cSeq idx) (↑B' : Set ℕ)
      then h.choose else ∅
    let iSeq : ℕ → Fin k := fun idx ↦
      if h : IsMonochromaticSet r (cSeq idx) (↑(B idx) : Set ℕ)
      then h.choose else ⟨0, hk⟩
    have hev_ex : ∀ᶠ idx in (hyperfilter ℕ : Filter ℕ),
        ∃ B' : Finset ℕ, B' ⊆ Finset.Icc 1 (b idx) ∧ m ≤ B'.card ∧
          IsMonochromaticSet r (cSeq idx) (↑B' : Set ℕ) :=
      hev.mono fun idx hpsi ↦ hpsi (cSeq idx)
    refine ⟨B, iSeq, ?_, ?_, ?_⟩
    · rw [Icc_one_coe_eq_internalNatSet, internalNatSet_subset_iff]
      refine hev_ex.mono fun idx hidx x hx ↦ ?_
      have hB_eq : B idx = hidx.choose := by simp [B, hidx]
      rw [hB_eq] at hx
      simpa using hidx.choose_spec.1 (Finset.mem_coe.1 hx)
    · refine Germ.coe_le.2 (hev_ex.mono fun idx hidx ↦ ?_)
      have hB_eq : B idx = hidx.choose := by simp [B, hidx]
      change m ≤ (B idx).card
      rw [hB_eq]
      exact hidx.choose_spec.2.1
    · refine hev_ex.mono fun idx hidx ↦ ?_
      have hB_eq : B idx = hidx.choose := by simp [B, hidx]
      have hmono_ex : IsMonochromaticSet r (cSeq idx) (↑(B idx) : Set ℕ) := by
        rw [hB_eq]
        exact hidx.choose_spec.2.2
      have hi_eq : iSeq idx = hmono_ex.choose := by simp [iSeq, hmono_ex]
      rw [hi_eq]
      exact hmono_ex.choose_spec

/-- **Goldblatt §17.4 Key Nonstandard Step (`*ψ(N)` at `N = omegaNat`, p. 228)**:
For the unlimited hypernatural `omegaNat`, `starPsiRamsey r k m omegaNat` holds directly by
Infinite Ramsey's Theorem! -/
theorem starPsiRamsey_omegaNat (r : ℕ) {k : ℕ} (hk : 0 < k) (m : ℕ) :
    starPsiRamsey r k m omegaNat := by
  intro cSeq
  let c : Finset ℕ → Fin k := fun s ↦ starNatFinFun (fun idx ↦ cSeq idx s) omegaNat
  have hIci_inf : (Set.Ici (1 : ℕ)).Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun j : ℕ ↦ j + 1)
      (fun a b hab ↦ by dsimp at hab; omega) fun j ↦ Nat.succ_pos j
  obtain ⟨D, i₀, hDIci, hD_inf, hD_mono⟩ := infinite_ramsey r hk hIci_inf c
  obtain ⟨B₀, hB₀D, hB₀_card⟩ := hD_inf.exists_subset_card_eq m
  refine ⟨fun _ ↦ B₀, fun _ ↦ i₀, ?_, ?_, ?_⟩
  · rw [show omegaNat = ((id : ℕ → ℕ) : ℕ*) from rfl, Icc_one_coe_eq_internalNatSet,
        internalNatSet_subset_iff]
    have hev_ge : ∀ᶠ idx in (hyperfilter ℕ : Filter ℕ), B₀.sup id ≤ idx :=
      Nat.hyperfilter_le_atTop (eventually_ge_atTop (B₀.sup id))
    refine hev_ge.mono fun idx hidx x hx ↦ ?_
    exact ⟨hDIci (hB₀D hx), (Finset.le_sup (f := id) (Finset.mem_coe.1 hx)).trans hidx⟩
  · exact Germ.coe_le.2 (Eventually.of_forall fun _ ↦ hB₀_card.ge)
  · have hev_col : ∀ᶠ idx in (hyperfilter ℕ : Filter ℕ),
        ∀ s ∈ B₀.powersetCard r, cSeq idx s = i₀ := by
      rw [eventually_all_finset]
      intro s hs
      have hcs : c s = i₀ :=
        hD_mono s (rSubsets_mono r hB₀D (mem_rSubsets_coe_iff_mem_powersetCard.2 hs))
      exact (mem_starNatSet_eq_iff_starNatFinFun (fun idx ↦ cSeq idx s) omegaNat i₀).2 hcs
    exact hev_col.mono fun idx hidx ↦ isMonochromatic_coe_iff_powersetCard.2 hidx

/-- **Exercise 17.4.1 — Existential Transfer `(∃ N ∈ *ℕ, *ψ(N)) ↔ (∃ n ∈ ℕ, ψ(n))`**
(Goldblatt §17.4, p. 228). -/
theorem exists_starPsiRamsey_iff_exists_psiRamsey (r : ℕ) {k : ℕ} (hk : 0 < k) (m : ℕ) :
    (∃ N : ℕ*, starPsiRamsey r k m N) ↔ ∃ n : ℕ, psiRamsey r k m n := by
  constructor
  · rintro ⟨N, hN⟩
    induction N using Germ.inductionOn with | _ b =>
    obtain ⟨idx, hidx⟩ := ((starPsiRamsey_coe_iff r hk m b).1 hN).exists
    exact ⟨b idx, hidx⟩
  · rintro ⟨n, hn⟩
    refine ⟨(n : ℕ*), ?_⟩
    exact (starPsiRamsey_coe_iff r hk m (fun _ ↦ n)).2 (Eventually.of_forall fun _ ↦ hn)

/-!
## §17.5 — Relatively Large Finite Sets & The Paris–Harrington Version (pp. 228–229)
-/

/-- Goldblatt §17.5 (p. 228): A finite set `M : Finset ℕ` is **relatively large** if `M` is nonempty
and its cardinality is at least as great as its smallest element (`|M| ≥ min(M)`). -/
def IsRelativelyLarge (M : Finset ℕ) : Prop :=
  ∃ h : M.Nonempty, M.min' h ≤ M.card

/-- The empty `Finset` is not relatively large. -/
@[simp]
theorem not_isRelativelyLarge_empty : ¬ IsRelativelyLarge ∅ := by
  rintro ⟨h, _⟩
  exact Finset.not_nonempty_empty h

/-- Every relatively large `Finset ℕ` is nonempty (Goldblatt §17.5, p. 228). -/
theorem IsRelativelyLarge.nonempty {M : Finset ℕ} (hM : IsRelativelyLarge M) : M.Nonempty :=
  hM.1

/-- For a relatively large `M`, `M.min' hM.nonempty ≤ M.card` (Goldblatt §17.5, p. 228). -/
theorem IsRelativelyLarge.min'_le_card {M : Finset ℕ} (hM : IsRelativelyLarge M) :
    M.min' hM.nonempty ≤ M.card :=
  hM.2

/-- Construct `IsRelativelyLarge M` from any `h : M.Nonempty` and `M.min' h ≤ M.card`. -/
theorem isRelativelyLarge_of_min'_le_card {M : Finset ℕ} (h : M.Nonempty)
    (hle : M.min' h ≤ M.card) : IsRelativelyLarge M :=
  ⟨h, hle⟩

/-- Concrete example: `{2, 5}` is relatively large (`min = 2 ≤ 2 = card`), whereas `{3, 4}` is not
(`min = 3 > 2 = card`) (Goldblatt §17.5, p. 228). -/
theorem isRelativelyLarge_pair_two_five_and_not_three_four :
    IsRelativelyLarge ({2, 5} : Finset ℕ) ∧ ¬ IsRelativelyLarge ({3, 4} : Finset ℕ) := by
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  rintro ⟨h, hle⟩
  have hmin : 3 ≤ ({3, 4} : Finset ℕ).min' h := Finset.le_min' _ h 3 (by decide)
  have hcard : ({3, 4} : Finset ℕ).card = 2 := by decide
  omega

/-- **Goldblatt §17.5 Selection Lemma (p. 228)**:
From any infinite set `D ⊆ ℕ` and any lower bound `m : ℕ`, we can select a finite subset
`B : Finset ℕ` with `(↑B : Set ℕ) ⊆ D` and `B` nonempty (`hne`) such that
`B.card = B.min' hne`, `m ≤ B.card`, `1 ≤ B.min' hne`, and hence `IsRelativelyLarge B`!
Specifically: pick `j ∈ D` with `max m 1 ≤ j`, and adjoin `j - 1` elements of `D` strictly greater
than `j`. -/
theorem exists_relativelyLarge_subset_of_infinite {D : Set ℕ} (hD : D.Infinite) (m : ℕ) :
    ∃ B : Finset ℕ, ∃ hne : B.Nonempty,
      (↑B : Set ℕ) ⊆ D ∧ B.card = B.min' hne ∧ m ≤ B.card ∧ 1 ≤ B.min' hne ∧
      IsRelativelyLarge B := by
  -- Step 1: Choose `j ∈ D` with `max m 1 ≤ j`.
  have hex_j : ∃ j ∈ D, max m 1 ≤ j := by
    by_contra hno
    push Not at hno
    have hsub : D ⊆ Set.Iio (max m 1) := fun x hx ↦ hno x hx
    exact hD ((Set.finite_Iio _).subset hsub)
  obtain ⟨j, hjD, hj_ge⟩ := hex_j
  have hj1 : 1 ≤ j := (le_max_right m 1).trans hj_ge
  have hjm : m ≤ j := (le_max_left m 1).trans hj_ge
  -- Step 2: `{x ∈ D | j < x}` is infinite since `D \ {0, …, j}` is infinite.
  have hgt_inf : (D ∩ Set.Ioi j).Infinite := by
    have hsub : D ⊆ (D ∩ Set.Iic j) ∪ (D ∩ Set.Ioi j) := fun x hx ↦ by
      rcases le_or_gt x j with hle | hgt
      · exact Or.inl ⟨hx, hle⟩
      · exact Or.inr ⟨hx, hgt⟩
    intro hfin
    have hle_fin : (D ∩ Set.Iic j).Finite := (Set.finite_Iic j).subset Set.inter_subset_right
    exact hD ((hle_fin.union hfin).subset hsub)
  -- Step 3: Select `T ⊆ D ∩ Set.Ioi j` of cardinality `j - 1` and put `B = insert j T`.
  obtain ⟨T, hT_sub, hT_card⟩ := hgt_inf.exists_subset_card_eq (j - 1)
  have hj_notMem : j ∉ T := by
    intro hjT
    have hgt : j < j := (hT_sub (Finset.mem_coe.2 hjT)).2
    exact lt_irrefl j hgt
  let B : Finset ℕ := insert j T
  have hne : B.Nonempty := Finset.insert_nonempty j T
  have hB_sub : (↑B : Set ℕ) ⊆ D := by
    rw [Finset.coe_insert]
    exact Set.insert_subset hjD (hT_sub.trans Set.inter_subset_left)
  have hB_card : B.card = j := by
    rw [Finset.card_insert_of_notMem hj_notMem, hT_card]
    omega
  have hB_min : B.min' hne = j := by
    apply le_antisymm (Finset.min'_le B j (Finset.mem_insert_self j T))
    refine Finset.le_min' B hne j fun x hx ↦ ?_
    rcases Finset.mem_insert.1 hx with rfl | hxT
    · exact le_rfl
    · exact ((hT_sub (Finset.mem_coe.2 hxT)).2).le
  refine ⟨B, hne, hB_sub, hB_card.trans hB_min.symm, hB_card ▸ hjm, hB_min ▸ hj1,
    ⟨hne, by rw [hB_min, hB_card]⟩⟩

/-- **The Paris–Harrington Partition Theorem (Strengthened Exact Form)**
(Goldblatt §17.5, pp. 228–229):
For any `r k m : ℕ` with `0 < k`, there exists `N : ℕ` (`1 ≤ N`) such that for every `k`-colouring
`c : Finset ℕ → Fin k` of `[{1, …, N}]^r`, there exists a nonempty subset `M ⊆ Finset.Icc 1 N` and
a colour `i₀ : Fin k` such that `m ≤ M.card`, `M.card = M.min' hne` (so `IsRelativelyLarge M`), and
`IsMonochromatic r c (↑M : Set ℕ) i₀`.

Proved via Infinite Ramsey + Ultrapower Transfer following Goldblatt §17.5! -/
theorem paris_harrington_ramsey_exact (r : ℕ) {k : ℕ} (hk : 0 < k) (m : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ c : Finset ℕ → Fin k,
      ∃ M : Finset ℕ, ∃ hne : M.Nonempty, ∃ i₀ : Fin k,
        M ⊆ Finset.Icc 1 N ∧ m ≤ M.card ∧ M.card = M.min' hne ∧
        IsRelativelyLarge M ∧ IsMonochromatic r c (↑M : Set ℕ) i₀ := by
  by_contra hno
  push Not at hno
  have hbad : ∀ n : ℕ, ∃ c : Finset ℕ → Fin k,
      ∀ M : Finset ℕ, ∀ hne : M.Nonempty, ∀ i₀ : Fin k,
        M ⊆ Finset.Icc 1 (n + 1) → m ≤ M.card → M.card = M.min' hne →
        IsRelativelyLarge M → ¬ IsMonochromatic r c (↑M : Set ℕ) i₀ :=
    fun n ↦ hno (n + 1) (Nat.succ_pos n)
  choose cSeq hcSeq using hbad
  let c : Finset ℕ → Fin k := fun s ↦ starNatFinFun (fun n ↦ cSeq n s) omegaNat
  have hIci_inf : (Set.Ici (1 : ℕ)).Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun j : ℕ ↦ j + 1)
      (fun a b hab ↦ by dsimp at hab; omega) fun j ↦ Nat.succ_pos j
  obtain ⟨D, i₀, hDIci, hD_inf, hD_mono⟩ := infinite_ramsey r hk hIci_inf c
  obtain ⟨M, hne, hMD, hM_eq, hMm, _, hM_rel⟩ := exists_relativelyLarge_subset_of_infinite hD_inf m
  have hev_col : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
      ∀ s ∈ M.powersetCard r, cSeq n s = i₀ := by
    rw [eventually_all_finset]
    intro s hs
    have hcs : c s = i₀ :=
      hD_mono s (rSubsets_mono r hMD (mem_rSubsets_coe_iff_mem_powersetCard.2 hs))
    exact (mem_starNatSet_eq_iff_starNatFinFun (fun n ↦ cSeq n s) omegaNat i₀).2 hcs
  let maxM : ℕ := M.sup id
  have hev_ge : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), maxM ≤ n :=
    Nat.hyperfilter_le_atTop (eventually_ge_atTop maxM)
  obtain ⟨n, hn_col, hn_ge⟩ := (hev_col.and hev_ge).exists
  have hM_sub : M ⊆ Finset.Icc 1 (n + 1) := fun x hx ↦
    Finset.mem_Icc.2 ⟨hDIci (hMD (Finset.mem_coe.2 hx)),
      ((Finset.le_sup (f := id) hx).trans hn_ge).trans (Nat.le_succ n)⟩
  have hM_mono : IsMonochromatic r (cSeq n) (↑M : Set ℕ) i₀ :=
    isMonochromatic_coe_iff_powersetCard.2 hn_col
  exact hcSeq n M hne i₀ hM_sub hMm hM_eq hM_rel hM_mono

/-- **The Paris–Harrington Partition Theorem** (Goldblatt §17.5, p. 228):
For any `r k m : ℕ` with `0 < k`, there exists `N : ℕ` such that for any `k`-colouring
`c : Finset ℕ → Fin k` of `[{1, …, N}]^r`, there exists a subset `M ⊆ Finset.Icc 1 N` and a colour
`i₀ : Fin k` such that `m ≤ M.card`, `IsRelativelyLarge M` (`|M| ≥ min(M)`), and
`IsMonochromatic r c (↑M : Set ℕ) i₀`. -/
theorem paris_harrington_ramsey (r : ℕ) {k : ℕ} (hk : 0 < k) (m : ℕ) :
    ∃ N : ℕ, ∀ c : Finset ℕ → Fin k,
      ∃ M : Finset ℕ, ∃ i₀ : Fin k,
        M ⊆ Finset.Icc 1 N ∧ m ≤ M.card ∧ IsRelativelyLarge M ∧
        IsMonochromatic r c (↑M : Set ℕ) i₀ := by
  obtain ⟨N, _, hN⟩ := paris_harrington_ramsey_exact r hk m
  exact ⟨N, fun c ↦ by
    obtain ⟨M, _, i₀, hsub, hm, _, hrel, hmono⟩ := hN c
    exact ⟨M, i₀, hsub, hm, hrel, hmono⟩⟩

/-- Goldblatt §17.5 (p. 228): Standard first-order Paris–Harrington predicate `ψ_{PH}(n)`. -/
def psiParisHarrington (r k m n : ℕ) : Prop :=
  ∀ c : Finset ℕ → Fin k,
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 n ∧ m ≤ B.card ∧ IsRelativelyLarge B ∧
      IsMonochromaticSet r c (↑B : Set ℕ)

/-- Goldblatt §17.5 (p. 228): Internal / ultrapower Paris–Harrington predicate `*ψ_{PH}(N)` on `ℕ*`. -/
def starPsiParisHarrington (r k m : ℕ) (N : ℕ*) : Prop :=
  ∀ cSeq : ℕ → Finset ℕ → Fin k,
    ∃ B : ℕ → Finset ℕ, ∃ iSeq : ℕ → Fin k,
      internalNatSet (fun idx ↦ (B idx : Set ℕ)) ⊆ Set.Icc (1 : ℕ*) N ∧
      (m : ℕ*) ≤ ((fun idx ↦ (B idx).card) : ℕ*) ∧
      (∀ᶠ idx in (hyperfilter ℕ : Filter ℕ), IsRelativelyLarge (B idx)) ∧
      (∀ᶠ idx in (hyperfilter ℕ : Filter ℕ),
        IsMonochromatic r (cSeq idx) (↑(B idx) : Set ℕ) (iSeq idx))

/-- **Ultrapower Transfer Equivalence for Paris–Harrington** (Goldblatt §17.4–17.5, pp. 227–228):
`starPsiParisHarrington r k m (b : ℕ*) ↔ ∀ᶠ idx in hyperfilter ℕ, psiParisHarrington r k m (b idx)`. -/
theorem starPsiParisHarrington_coe_iff (r : ℕ) {k : ℕ} (hk : 0 < k) (m : ℕ) (b : ℕ → ℕ) :
    starPsiParisHarrington r k m (b : ℕ*) ↔
      ∀ᶠ idx in (hyperfilter ℕ : Filter ℕ), psiParisHarrington r k m (b idx) := by
  constructor
  · intro hstar
    by_contra hnot
    have hev_not : ∀ᶠ idx in (hyperfilter ℕ : Filter ℕ), ¬ psiParisHarrington r k m (b idx) :=
      Ultrafilter.eventually_not.2 hnot
    let cDefault : Finset ℕ → Fin k := fun _ ↦ ⟨0, hk⟩
    let cSeq : ℕ → Finset ℕ → Fin k := fun idx ↦
      if h : ∃ c : Finset ℕ → Fin k,
          ¬ ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 (b idx) ∧ m ≤ B.card ∧ IsRelativelyLarge B ∧
            IsMonochromaticSet r c (↑B : Set ℕ)
      then h.choose else cDefault
    obtain ⟨B, iSeq, hsub, hcard, hrel, hmono⟩ := hstar cSeq
    rw [Icc_one_coe_eq_internalNatSet, internalNatSet_subset_iff] at hsub
    have hcard_ev : ∀ᶠ idx in (hyperfilter ℕ : Filter ℕ), m ≤ (B idx).card :=
      Germ.coe_le.1 hcard
    obtain ⟨idx, ⟨⟨⟨hnot_ph, hBsub⟩, hBm⟩, hBrel⟩, hBmono⟩ :=
      ((((hev_not.and hsub).and hcard_ev).and hrel).and hmono).exists
    have hex_bad : ∃ c : Finset ℕ → Fin k,
        ¬ ∃ B' : Finset ℕ, B' ⊆ Finset.Icc 1 (b idx) ∧ m ≤ B'.card ∧ IsRelativelyLarge B' ∧
          IsMonochromaticSet r c (↑B' : Set ℕ) := by
      unfold psiParisHarrington at hnot_ph
      push Not at hnot_ph
      obtain ⟨c, hc⟩ := hnot_ph
      exact ⟨c, fun ⟨B', h1, h2, h3, h4⟩ ↦ hc B' h1 h2 h3 h4⟩
    have hcSeq_eq : cSeq idx = hex_bad.choose := by simp only [cSeq, hex_bad, ↓reduceDIte]
    rw [hcSeq_eq] at hBmono
    have hB_finset_sub : B idx ⊆ Finset.Icc 1 (b idx) := fun x hx ↦ by
      simpa using hBsub (Finset.mem_coe.2 hx)
    exact hex_bad.choose_spec ⟨B idx, hB_finset_sub, hBm, hBrel, iSeq idx, hBmono⟩
  · intro hev cSeq
    let B : ℕ → Finset ℕ := fun idx ↦
      if h : ∃ B' : Finset ℕ, B' ⊆ Finset.Icc 1 (b idx) ∧ m ≤ B'.card ∧ IsRelativelyLarge B' ∧
          IsMonochromaticSet r (cSeq idx) (↑B' : Set ℕ)
      then h.choose else ∅
    let iSeq : ℕ → Fin k := fun idx ↦
      if h : IsMonochromaticSet r (cSeq idx) (↑(B idx) : Set ℕ)
      then h.choose else ⟨0, hk⟩
    have hev_ex : ∀ᶠ idx in (hyperfilter ℕ : Filter ℕ),
        ∃ B' : Finset ℕ, B' ⊆ Finset.Icc 1 (b idx) ∧ m ≤ B'.card ∧ IsRelativelyLarge B' ∧
          IsMonochromaticSet r (cSeq idx) (↑B' : Set ℕ) :=
      hev.mono fun idx hph ↦ hph (cSeq idx)
    refine ⟨B, iSeq, ?_, ?_, ?_, ?_⟩
    · rw [Icc_one_coe_eq_internalNatSet, internalNatSet_subset_iff]
      refine hev_ex.mono fun idx hidx x hx ↦ ?_
      have hB_eq : B idx = hidx.choose := by simp [B, hidx]
      rw [hB_eq] at hx
      simpa using hidx.choose_spec.1 (Finset.mem_coe.1 hx)
    · refine Germ.coe_le.2 (hev_ex.mono fun idx hidx ↦ ?_)
      have hB_eq : B idx = hidx.choose := by simp [B, hidx]
      change m ≤ (B idx).card
      rw [hB_eq]
      exact hidx.choose_spec.2.1
    · refine hev_ex.mono fun idx hidx ↦ ?_
      have hB_eq : B idx = hidx.choose := by simp [B, hidx]
      rw [hB_eq]
      exact hidx.choose_spec.2.2.1
    · refine hev_ex.mono fun idx hidx ↦ ?_
      have hB_eq : B idx = hidx.choose := by simp [B, hidx]
      have hmono_ex : IsMonochromaticSet r (cSeq idx) (↑(B idx) : Set ℕ) := by
        rw [hB_eq]
        exact hidx.choose_spec.2.2.2
      have hi_eq : iSeq idx = hmono_ex.choose := by simp [iSeq, hmono_ex]
      rw [hi_eq]
      exact hmono_ex.choose_spec

/-- **Goldblatt §17.5 Nonstandard Core (`*ψ_{PH}(omegaNat)`)**:
`starPsiParisHarrington r k m omegaNat` holds by Infinite Ramsey's Theorem and
`exists_relativelyLarge_subset_of_infinite`! -/
theorem starPsiParisHarrington_omegaNat (r : ℕ) {k : ℕ} (hk : 0 < k) (m : ℕ) :
    starPsiParisHarrington r k m omegaNat := by
  intro cSeq
  let c : Finset ℕ → Fin k := fun s ↦ starNatFinFun (fun idx ↦ cSeq idx s) omegaNat
  have hIci_inf : (Set.Ici (1 : ℕ)).Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun j : ℕ ↦ j + 1)
      (fun a b hab ↦ by dsimp at hab; omega) fun j ↦ Nat.succ_pos j
  obtain ⟨D, i₀, hDIci, hD_inf, hD_mono⟩ := infinite_ramsey r hk hIci_inf c
  obtain ⟨B₀, _, hB₀D, _, hB₀m, _, hB₀_rel⟩ := exists_relativelyLarge_subset_of_infinite hD_inf m
  refine ⟨fun _ ↦ B₀, fun _ ↦ i₀, ?_, ?_, Eventually.of_forall fun _ ↦ hB₀_rel, ?_⟩
  · rw [show omegaNat = ((id : ℕ → ℕ) : ℕ*) from rfl, Icc_one_coe_eq_internalNatSet,
        internalNatSet_subset_iff]
    have hev_ge : ∀ᶠ idx in (hyperfilter ℕ : Filter ℕ), B₀.sup id ≤ idx :=
      Nat.hyperfilter_le_atTop (eventually_ge_atTop (B₀.sup id))
    refine hev_ge.mono fun idx hidx x hx ↦ ?_
    exact ⟨hDIci (hB₀D hx), (Finset.le_sup (f := id) (Finset.mem_coe.1 hx)).trans hidx⟩
  · exact Germ.coe_le.2 (Eventually.of_forall fun _ ↦ hB₀m)
  · have hev_col : ∀ᶠ idx in (hyperfilter ℕ : Filter ℕ),
        ∀ s ∈ B₀.powersetCard r, cSeq idx s = i₀ := by
      rw [eventually_all_finset]
      intro s hs
      have hcs : c s = i₀ :=
        hD_mono s (rSubsets_mono r hB₀D (mem_rSubsets_coe_iff_mem_powersetCard.2 hs))
      exact (mem_starNatSet_eq_iff_starNatFinFun (fun idx ↦ cSeq idx s) omegaNat i₀).2 hcs
    exact hev_col.mono fun idx hidx ↦ isMonochromatic_coe_iff_powersetCard.2 hidx

/-- The Paris–Harrington Partition Theorem strengthens and directly implies the Finite Ramsey
Theorem `psiRamsey` (Goldblatt §17.5, p. 228). -/
theorem paris_harrington_implies_finite_ramsey {r k m n : ℕ}
    (hph : psiParisHarrington r k m n) : psiRamsey r k m n :=
  fun c ↦ by
    obtain ⟨B, hsub, hm, _, hmono⟩ := hph c
    exact ⟨B, hsub, hm, hmono⟩

end Goldblatt.Ch17
