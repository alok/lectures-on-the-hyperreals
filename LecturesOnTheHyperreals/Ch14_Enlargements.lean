import LecturesOnTheHyperreals.Ch02_LargeSets
import LecturesOnTheHyperreals.Ch12_InternalFunctions
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.Bases

/-!
# Chapter 14: The Existence of Nonstandard Entities (Enlargements)

Complete formalization of Robert Goldblatt's *Lectures on the Hyperreals: An Introduction to
Nonstandard Analysis* (GTM 188, Springer, 1998), Chapter 14 (pp. 183–190):

* **§14.1 Enlargements and Nonstandard Entities** (pp. 183–185):
  - Concurrent (finitely satisfiable) binary relations `IsConcurrent` on `α → β → Prop` and
    `IsConcurrentSet` on `Set (α × β)`, domain/range/slice operations (`relDom`, `relRan`,
    `relSlice`), and equivalence with the finite intersection property (`Ch02.HasFIP`) of slices.
  - Universe-polymorphic abstract nonstandard extension interface `NonstandardExtension.{u, v}`
    encoding a universe embedding `* : 𝕌 → 𝕌'` with standard element embedding `starElem`, set
    extension `starSet`, binary relation extension `starRel`, hyperfinite subsets
    `hyperfiniteSubsets` (`𝒫_F(A)`), and internal membership `hyperfiniteSet`.
  - The three enlargement principles:
    1. `IsEnlargement`: FIP intersection property `⋂_{B ∈ 𝒜} *B ≠ ∅` (Goldblatt §14.1, p. 184).
    2. `EnlargementCondition`: concurrent relation realization `∃ b, ∀ x ∈ dom R, (*R) (*x) b`
       (Goldblatt §14.2, Theorem 14.2.1(2), p. 186).
    3. `HyperfiniteApproxProperty`: hyperfinite approximation `σ(A) ⊆ B ⊆ *A` with `B ∈ *𝒫_F(A)`
       (Goldblatt §14.2, Theorem 14.2.1(3), p. 186).
  - All concrete motivating examples of concurrent relations and FIP families (§14.1–14.2,
    pp. 184–186):
    1. Nonidentity `x ≠ y` on an infinite type `α` or infinite subset `A ⊆ α` → existence of
       nonstandard elements in `*α \ σ(α)` and `*A \ σ(A)`.
    2. Strict order `n < y` on `ℕ` and `r < y` on `ℝ₊` → existence of unlimited hypernaturals and
       positive unlimited hyperreals.
    3. Infinitesimal bounds `0 < y ∧ y < r` on `ℝ₊` and punctured intervals `(-r, r) \ {0}` →
       existence of positive infinitesimals and nonzero infinitesimals.
    4. Finite membership `x ∈ S` on `α × Finset α` and `A × 𝒫_F(A)` → existence of hyperfinite sets
       containing all standard elements `σ(A) ⊆ E ⊆ *A`.
    5. Open-neighbourhood concurrence on a topological space `X` → existence of monad points in
       `⋂_{U open, x ∈ U} *U` (and nontrivial monad points `y ≠ *x` whenever `x` is non-isolated).
    6. FIP membership relation `R A y ↔ y ∈ A` on `ℱ : Set (Set α)` → equivalence with `HasFIP ℱ`,
       existence of `y ∈ ⋂_{A ∈ ℱ} *A`, and Robinson's general nonstandard compactness theorem
       `IsCompact K ↔ ∀ y ∈ *K, ∃ x ∈ K, y ∈ monad x`!

* **§14.2 Concurrence, Hyperfinite Approximation, and Countable vs. Uncountable Sets** (pp. 185–188):
  - **Theorem 14.2.1** (`enlargement_tfae`): Threefold equivalence
    `IsEnlargement ↔ EnlargementCondition ↔ HyperfiniteApproxProperty`.
  - Parametric `ultrapowerExtension U` over any ultrafilter `U : Ultrafilter J`.
  - Proof that the sequence ultrapower `ℝ* = Germ (hyperfilter ℕ) ℝ` enlarges every concurrent
    relation with **countable** domain (`hyperfilter_enlarges_countable_concurrent`,
    `hyperreal_enlarges_countable_concurrent`).
  - Exact characterization of hyperfinite approximation in `ℝ*`
    (`exists_hyperfinite_approx_hyperreal_iff_countable`): `∃ E, IsHyperfinite E ∧ σ(A) ⊆ E ⊆ *A`
    holds **if and only if** `A` is countable, proving `ultrapowerExtension (hyperfilter ℕ)` is not
    an enlargement (`not_isEnlargement_hyperfilter_nat`, Goldblatt §14.1, p. 185).

* **§14.3–14.4 Enlargements as Ultrapowers & Exercises 14.4(1)–(3)** (pp. 187–190):
  - Fine sets `hatSet i = {s : Finset I | i ∈ s}`, `upperFinsetSet a = {b : Finset I | a ⊆ b}`,
    fine filters `IsFineFilter`, and `fineUltrafilter I = Ultrafilter.of Filter.atTop`.
  - Łoś / transfer properties on `FineUltrapower I α`, bounded-rank stabilization
    (`existsUnique_rank_mem_ultrafilter`, Exercise 14.4(1)), internal function evaluation
    (`ultraFunApply_eq_iff`, Exercise 14.4(2)), and nonprincipality of `fineUltrafilter I` iff
    `Infinite I` (`fine_ultrafilter_le_cofinite_of_infinite`,
    `fineUltrafilter_nonprincipal_iff_infinite`, Exercise 14.4(3)).
  - **Theorem 14.3.1** (pp. 188–189): explicit diagonal constructions over `fineUltrafilter` for
    single concurrent relations, arbitrary indexed families of concurrent relations, FIP families,
    hyperfinite approximations `g(b) = b ∩ A`, and the **Global Enlargement Theorem**
    (`universalUltrapowerEnlargement_isEnlargement`).
-/

noncomputable section

set_option relaxedAutoImplicit false

namespace Goldblatt

namespace Ch14

open Filter
open Hyperreal (ofSeq ofSeq_lt_ofSeq ofSeq_le_ofSeq ofSeq_surjective)
open scoped Topology Classical

universe u v w

/-! ## §14.1 Concurrent Binary Relations and Abstract Enlargements (Goldblatt pp. 183–186) -/

/-- Domain `dom R = {x : α | ∃ y : β, R x y}` of a binary relation `R : α → β → Prop`
(Goldblatt §14.2, p. 185). -/
def relDom {α : Type u} {β : Type v} (R : α → β → Prop) : Set α :=
  {x : α | ∃ y : β, R x y}

/-- Range `ran R = {y : β | ∃ x : α, R x y}` of a binary relation `R : α → β → Prop`
(Goldblatt §14.2, proof of Theorem 14.2.1, p. 186). -/
def relRan {α : Type u} {β : Type v} (R : α → β → Prop) : Set β :=
  {y : β | ∃ x : α, R x y}

/-- Right fibre / section `R[x] = {y : β | R x y}` of a binary relation `R` at `x : α`
(Goldblatt §14.2, proof of Theorem 14.2.1, p. 186). -/
def relSlice {α : Type u} {β : Type v} (R : α → β → Prop) (x : α) : Set β :=
  {y : β | R x y}

/-- Membership in `relDom R` holds iff `∃ y, R x y` (Goldblatt §14.2, p. 185). -/
@[simp]
theorem mem_relDom {α : Type u} {β : Type v} {R : α → β → Prop} {x : α} :
    x ∈ relDom R ↔ ∃ y : β, R x y :=
  Iff.rfl

/-- Membership in `relRan R` holds iff `∃ x, R x y` (Goldblatt §14.2, p. 186). -/
@[simp]
theorem mem_relRan {α : Type u} {β : Type v} {R : α → β → Prop} {y : β} :
    y ∈ relRan R ↔ ∃ x : α, R x y :=
  Iff.rfl

/-- Membership in `relSlice R x` holds iff `R x y` (Goldblatt §14.2, p. 186). -/
@[simp]
theorem mem_relSlice {α : Type u} {β : Type v} {R : α → β → Prop} {x : α} {y : β} :
    y ∈ relSlice R x ↔ R x y :=
  Iff.rfl

/-- A binary relation `R : α → β → Prop` is **concurrent** (or *finitely satisfiable*) if its
domain `relDom R` is nonempty and for every finite subset `F : Finset α` with `↑F ⊆ relDom R`,
there exists `y : β` such that `∀ x ∈ F, R x y` (Goldblatt §14.2, p. 185). -/
def IsConcurrent {α : Type u} {β : Type v} (R : α → β → Prop) : Prop :=
  (relDom R).Nonempty ∧
    ∀ F : Finset α, (↑F : Set α) ⊆ relDom R → ∃ y : β, ∀ x ∈ F, R x y

/-- Domain `dom P = Prod.fst '' P` of a binary relation represented as a set of ordered pairs
`P : Set (α × β)` (Goldblatt §14.2, p. 185). -/
def pairRelDom {α : Type u} {β : Type v} (P : Set (α × β)) : Set α :=
  Prod.fst '' P

/-- Set-of-ordered-pairs formulation of concurrence for `P : Set (α × β)`
(Goldblatt §14.2, pp. 185–186). -/
def IsConcurrentSet {α : Type u} {β : Type v} (P : Set (α × β)) : Prop :=
  IsConcurrent (fun x y ↦ (x, y) ∈ P)

/-- `pairRelDom P` agrees with `relDom (fun x y ↦ (x, y) ∈ P)` (Goldblatt §14.2, p. 185). -/
@[simp]
theorem pairRelDom_eq_relDom {α : Type u} {β : Type v} (P : Set (α × β)) :
    pairRelDom P = relDom (fun x y ↦ (x, y) ∈ P) := by
  ext x
  simp [pairRelDom, relDom]

/-- Explicit characterization of `IsConcurrentSet P` in terms of `pairRelDom P` and ordered pairs
`(x, y) ∈ P` (Goldblatt §14.2, p. 185). -/
theorem isConcurrentSet_iff {α : Type u} {β : Type v} {P : Set (α × β)} :
    IsConcurrentSet P ↔
      (pairRelDom P).Nonempty ∧
        ∀ F : Finset α, (↑F : Set α) ⊆ pairRelDom P → ∃ y : β, ∀ x ∈ F, (x, y) ∈ P := by
  simp [IsConcurrentSet, IsConcurrent, pairRelDom_eq_relDom]

/-- If `R` is concurrent, both `α` and `β` are inhabited/nonempty (Goldblatt §14.2, p. 185). -/
theorem IsConcurrent.nonempty_types {α : Type u} {β : Type v} {R : α → β → Prop}
    (hR : IsConcurrent R) : Nonempty α ∧ Nonempty β := by
  obtain ⟨x, y, _⟩ := hR.1
  exact ⟨⟨x⟩, ⟨y⟩⟩

/-- On a relation with nonempty domain, quantifying over all `F : Finset α` in `IsConcurrent R` is
equivalent to quantifying over *nonempty* `F : Finset α` with `↑F ⊆ relDom R`
(Goldblatt §14.2, p. 185: `{x_1, …, x_n}` for `n ≥ 1`). -/
theorem isConcurrent_iff_nonempty_finset {α : Type u} {β : Type v} {R : α → β → Prop} :
    IsConcurrent R ↔
      (relDom R).Nonempty ∧
        ∀ F : Finset α, F.Nonempty → (↑F : Set α) ⊆ relDom R → ∃ y : β, ∀ x ∈ F, R x y := by
  refine ⟨fun ⟨hne, hF⟩ ↦ ⟨hne, fun F _ hsub ↦ hF F hsub⟩, fun ⟨hne, hF⟩ ↦ ⟨hne, fun F hsub ↦ ?_⟩⟩
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · obtain ⟨_, y₀, _⟩ := hne
    exact ⟨y₀, fun _ hx ↦ (Finset.notMem_empty _ hx).elim⟩
  · exact hF F hFne hsub

/-- Goldblatt §14.2, proof of Theorem 14.2.1 (p. 186): A binary relation `R : α → β → Prop` is
concurrent if and only if `relDom R` is nonempty and the collection `{R[x] | x ∈ dom R}` of right
slices has the finite intersection property (`Ch02.HasFIP`). -/
theorem isConcurrent_iff_hasFIP_slices {α : Type u} {β : Type v} {R : α → β → Prop} :
    IsConcurrent R ↔ (relDom R).Nonempty ∧ Ch02.HasFIP (relSlice R '' relDom R) := by
  constructor
  · rintro ⟨hne, hconc⟩
    refine ⟨hne, fun s hs ↦ ?_⟩
    let idx : {B : Set β // B ∈ s} → α := fun b ↦ (hs b.2).choose
    let F : Finset α := s.attach.image idx
    have hFsub : (↑F : Set α) ⊆ relDom R := by
      intro x hx
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      exact (hs b.2).choose_spec.1
    obtain ⟨y, hy⟩ := hconc F hFsub
    refine ⟨y, Set.mem_biInter fun B hBs ↦ ?_⟩
    have hmemF : idx ⟨B, hBs⟩ ∈ F :=
      Finset.mem_image.2 ⟨⟨B, hBs⟩, Finset.mem_attach _ _, rfl⟩
    have hRxy : R (idx ⟨B, hBs⟩) y := hy _ hmemF
    rw [← (hs hBs).choose_spec.2]
    exact hRxy
  · rintro ⟨hne, hfip⟩
    refine ⟨hne, fun F hFsub ↦ ?_⟩
    let s : Finset (Set β) := F.image (relSlice R)
    have hs : (↑s : Set (Set β)) ⊆ relSlice R '' relDom R := by
      intro B hB
      obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hB)
      exact ⟨x, hFsub hxF, rfl⟩
    obtain ⟨y, hy⟩ := hfip s hs
    refine ⟨y, fun x hxF ↦ ?_⟩
    have hmem : relSlice R x ∈ s := Finset.mem_image.2 ⟨x, hxF, rfl⟩
    exact Set.mem_iInter₂.1 hy (relSlice R x) hmem

/-! ### Abstract Nonstandard Extension / Universe Embedding (`NonstandardExtension`) -/

/-- Abstract universe-polymorphic nonstandard extension modeling a universe embedding `* : 𝕌 → 𝕌'`
(Goldblatt §13.7–13.9 & §14.1–14.2, pp. 183–186).

For every standard type `α : Type u`, `E.Star α : Type v` is the nonstandard transform `*α`,
`E.starElem : α → E.Star α` embeds standard entities `x ↦ *x`, `E.starSet` extends subsets
`A ⊆ α` to `*A ⊆ *α`, and `E.starRel` extends binary relations `R : α → β → Prop` to
`*R : *α → *β → Prop`, preserving Boolean algebra, finite sets, and first-order relational
transfer. -/
structure NonstandardExtension : Type (max (u + 1) (v + 1)) where
  /-- Nonstandard transform `*α` of a type `α`. -/
  Star : Type u → Type v
  /-- Standard embedding `x ↦ *x` of `α` into `*α`. -/
  starElem : {α : Type u} → α → Star α
  /-- Nonstandard extension `*A ⊆ *α` of a subset `A ⊆ α`. -/
  starSet : {α : Type u} → Set α → Set (Star α)
  /-- Nonstandard extension `*R : *α → *β → Prop` of a binary relation `R : α → β → Prop`. -/
  starRel : {α β : Type u} → (α → β → Prop) → Star α → Star β → Prop
  /-- Injectivity of `starElem`: `*x = *y → x = y`. -/
  starElem_injective : ∀ {α : Type u}, Function.Injective (@starElem α)
  /-- Membership transfer on standard elements: `*x ∈ *A ↔ x ∈ A`. -/
  starElem_mem_starSet_iff : ∀ {α : Type u} (x : α) (A : Set α),
    starElem x ∈ starSet A ↔ x ∈ A
  /-- Empty set transfer: `*∅ = ∅`. -/
  starSet_empty : ∀ {α : Type u}, starSet (∅ : Set α) = ∅
  /-- Universal set transfer: `*Set.univ = Set.univ`. -/
  starSet_univ : ∀ {α : Type u}, starSet (Set.univ : Set α) = Set.univ
  /-- Intersection transfer: `*(A ∩ B) = *A ∩ *B`. -/
  starSet_inter : ∀ {α : Type u} (A B : Set α),
    starSet (A ∩ B) = starSet A ∩ starSet B
  /-- Complement transfer: `*(Aᶜ) = (*A)ᶜ`. -/
  starSet_compl : ∀ {α : Type u} (A : Set α),
    starSet Aᶜ = (starSet A)ᶜ
  /-- Singleton transfer: `*{a} = {*a}`. -/
  starSet_singleton : ∀ {α : Type u} (a : α),
    starSet ({a} : Set α) = {starElem a}
  /-- Equality relation transfer: `*(· = ·) x y ↔ x = y`. -/
  starRel_eq : ∀ {α : Type u} (x y : Star α),
    starRel (· = ·) x y ↔ x = y
  /-- Left-standard section transfer: `(*R) (*x) b ↔ b ∈ *(R[x])` (Goldblatt p. 186). -/
  starRel_starElem_left : ∀ {α β : Type u} (R : α → β → Prop) (x : α) (b : Star β),
    starRel R (starElem x) b ↔ b ∈ starSet {y : β | R x y}
  /-- Right-standard section transfer: `(*R) a (*y) ↔ a ∈ *{x | R x y}`. -/
  starRel_starElem_right : ∀ {α β : Type u} (R : α → β → Prop) (a : Star α) (y : β),
    starRel R a (starElem y) ↔ a ∈ starSet {x : α | R x y}
  /-- Negation transfer for binary relations: `*(¬ R) a b ↔ ¬ (*R) a b`. -/
  starRel_not : ∀ {α β : Type u} (R : α → β → Prop) (a : Star α) (b : Star β),
    starRel (fun x y ↦ ¬ R x y) a b ↔ ¬ starRel R a b
  /-- Conjunction transfer for binary relations: `*(R₁ ∧ R₂) a b ↔ (*R₁) a b ∧ (*R₂) a b`. -/
  starRel_and : ∀ {α β : Type u} (R₁ R₂ : α → β → Prop) (a : Star α) (b : Star β),
    starRel (fun x y ↦ R₁ x y ∧ R₂ x y) a b ↔ starRel R₁ a b ∧ starRel R₂ a b
  /-- Converse / transpose transfer for binary relations. -/
  starRel_swap : ∀ {α β : Type u} (R : α → β → Prop) (a : Star α) (b : Star β),
    starRel (fun y x ↦ R x y) b a ↔ starRel R a b
  /-- Universal Horn transfer: `(∀ x ∈ A, ∀ y, R x y → y ∈ B) → ∀ a ∈ *A, ∀ b, (*R) a b → b ∈ *B`. -/
  starRel_imp_mem : ∀ {α β : Type u} {A : Set α} {B : Set β} {R : α → β → Prop},
    (∀ x y, x ∈ A → R x y → y ∈ B) →
    ∀ a b, a ∈ starSet A → starRel R a b → b ∈ starSet B
  /-- Domain transfer: `*(dom R) = dom (*R)` (Goldblatt Exercise 3.15(2), p. 33). -/
  starSet_dom : ∀ {α β : Type u} (R : α → β → Prop),
    starSet (relDom R) = relDom (starRel R)

namespace NonstandardExtension

variable (E : NonstandardExtension.{u, v})

/-- Standard element equality `*x = *y ↔ x = y` (Goldblatt §13.8). -/
@[simp]
theorem starElem_eq_iff {α : Type u} {x y : α} :
    E.starElem x = E.starElem y ↔ x = y :=
  E.starElem_injective.eq_iff

/-- Preimage of `*A` under `starElem` recovers `A`: `*A ∩ σ(α) = σ(A)` (Goldblatt §3.10(5)). -/
@[simp]
theorem preimage_starElem_starSet {α : Type u} (A : Set α) :
    E.starElem ⁻¹' E.starSet A = A := by
  ext x
  exact E.starElem_mem_starSet_iff x A

/-- Image `im A = {*a : a ∈ A}` of standard elements of `A` is always a subset of `*A`
(Goldblatt §14.1, p. 184). -/
theorem image_starElem_subset_starSet {α : Type u} (A : Set α) :
    E.starElem '' A ⊆ E.starSet A := by
  rintro _ ⟨a, ha, rfl⟩
  exact (E.starElem_mem_starSet_iff a A).2 ha

/-- Union transfer: `*(A ∪ B) = *A ∪ *B` (derived via De Morgan's law from `∩` and `ᶜ`). -/
@[simp]
theorem starSet_union {α : Type u} (A B : Set α) :
    E.starSet (A ∪ B) = E.starSet A ∪ E.starSet B := by
  have h : A ∪ B = (Aᶜ ∩ Bᶜ)ᶜ := by ext x; simp; tauto
  rw [h, E.starSet_compl, E.starSet_inter, E.starSet_compl, E.starSet_compl]
  ext x
  simp
  tauto

/-- Set-difference transfer: `*(A \ B) = *A \ *B` (Goldblatt §14.1, p. 184). -/
@[simp]
theorem starSet_sdiff {α : Type u} (A B : Set α) :
    E.starSet (A \ B) = E.starSet A \ E.starSet B := by
  rw [Set.sdiff_eq, E.starSet_inter, E.starSet_compl, Set.sdiff_eq]

/-- Inclusion transfer: `*A ⊆ *B ↔ A ⊆ B` (Goldblatt §3.10(2a)). -/
@[simp]
theorem starSet_subset_iff {α : Type u} {A B : Set α} :
    E.starSet A ⊆ E.starSet B ↔ A ⊆ B := by
  constructor
  · intro h x hx
    exact (E.starElem_mem_starSet_iff x B).1 (h ((E.starElem_mem_starSet_iff x A).2 hx))
  · intro h
    have hinter : A ∩ B = A := Set.inter_eq_left.2 h
    have hstar : E.starSet A ∩ E.starSet B = E.starSet A := by
      rw [← E.starSet_inter, hinter]
    exact Set.inter_eq_left.1 hstar

/-- Monotonicity of `starSet`: `A ⊆ B → *A ⊆ *B`. -/
theorem starSet_mono {α : Type u} {A B : Set α} (h : A ⊆ B) :
    E.starSet A ⊆ E.starSet B :=
  E.starSet_subset_iff.2 h

/-- Equality transfer for sets: `*A = *B ↔ A = B` (Goldblatt §3.10(2b)). -/
@[simp]
theorem starSet_eq_iff {α : Type u} {A B : Set α} :
    E.starSet A = E.starSet B ↔ A = B := by
  rw [Set.Subset.antisymm_iff, Set.Subset.antisymm_iff,
      E.starSet_subset_iff, E.starSet_subset_iff]

/-- Nonemptiness transfer: `(*A).Nonempty ↔ A.Nonempty`! -/
@[simp]
theorem starSet_nonempty_iff {α : Type u} {A : Set α} :
    (E.starSet A).Nonempty ↔ A.Nonempty := by
  rw [Set.nonempty_iff_ne_empty, Set.nonempty_iff_ne_empty, ← E.starSet_empty, Ne, Ne,
      E.starSet_eq_iff]

/-- Finite union transfer: `*(⋃ i ∈ F, A i) = ⋃ i ∈ F, *(A i)` for any `F : Finset ι`. -/
theorem starSet_biUnion_finset {ι : Type w} {α : Type u} (F : Finset ι) (A : ι → Set α) :
    E.starSet (⋃ i ∈ F, A i) = ⋃ i ∈ F, E.starSet (A i) := by
  induction F using Finset.induction_on with
  | empty => simp [E.starSet_empty]
  | @insert i s _ ih =>
    rw [Finset.set_biUnion_insert, Finset.set_biUnion_insert, E.starSet_union, ih]

/-- Finite intersection transfer: `*(⋂ i ∈ F, A i) = ⋂ i ∈ F, *(A i)` for any `F : Finset ι`. -/
theorem starSet_biInter_finset {ι : Type w} {α : Type u} (F : Finset ι) (A : ι → Set α) :
    E.starSet (⋂ i ∈ F, A i) = ⋂ i ∈ F, E.starSet (A i) := by
  induction F using Finset.induction_on with
  | empty => simp [E.starSet_univ]
  | @insert i s _ ih =>
    rw [Finset.set_biInter_insert, Finset.set_biInter_insert, E.starSet_inter, ih]

/-- Finite set transfer on `Finset α`: `*(↑F) = {*a : a ∈ F}` (Goldblatt §3.10(1) & §13.9). -/
theorem starSet_finset {α : Type u} (F : Finset α) :
    E.starSet (↑F : Set α) = E.starElem '' (↑F : Set α) := by
  induction F using Finset.induction_on with
  | empty => simp [E.starSet_empty]
  | @insert a s _ ih =>
    rw [Finset.coe_insert, Set.insert_eq, E.starSet_union, E.starSet_singleton, ih,
        Set.image_union, Set.image_singleton]

/-- Finite set transfer on `Set α`: if `A.Finite`, then `*A = im A = {*a : a ∈ A}`
(Goldblatt §3.10(1) & §14.1, p. 184). -/
theorem starSet_eq_image_of_finite {α : Type u} {A : Set α} (hA : A.Finite) :
    E.starSet A = E.starElem '' A := by
  have h := E.starSet_finset hA.toFinset
  rwa [Set.Finite.coe_toFinset] at h

/-- If a standard entity `*x` belongs to `*A`, then `*x ∈ im A` (Goldblatt §14.1, p. 184:
"`im A` is the set of standard members of `*A`", citing Theorem 13.9.2). -/
theorem starSet_inter_range_starElem {α : Type u} (A : Set α) :
    E.starSet A ∩ Set.range E.starElem = E.starElem '' A := by
  ext y
  constructor
  · rintro ⟨hyA, a, rfl⟩
    exact ⟨a, (E.starElem_mem_starSet_iff a A).1 hyA, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(E.starElem_mem_starSet_iff a A).2 ha, a, rfl⟩

/-- Relational transfer on standard elements: `(*R) (*x) (*y) ↔ R x y`. -/
@[simp]
theorem starRel_starElem_iff {α β : Type u} (R : α → β → Prop) (x : α) (y : β) :
    E.starRel R (E.starElem x) (E.starElem y) ↔ R x y := by
  rw [E.starRel_starElem_left, E.starElem_mem_starSet_iff]
  rfl

/-- Nonidentity relation transfer: `*(· ≠ ·) a b ↔ a ≠ b` (Goldblatt §14.2, p. 186). -/
@[simp]
theorem starRel_ne {α : Type u} (a b : E.Star α) :
    E.starRel (· ≠ ·) a b ↔ a ≠ b := by
  change E.starRel (fun x y ↦ ¬ x = y) a b ↔ ¬ a = b
  rw [E.starRel_not, E.starRel_eq]

/-- Monotonicity of `starRel`: if `∀ x y, R₁ x y → R₂ x y`, then `(*R₁) a b → (*R₂) a b`. -/
theorem starRel_mono {α β : Type u} {R₁ R₂ : α → β → Prop}
    (h : ∀ x y, R₁ x y → R₂ x y) {a : E.Star α} {b : E.Star β}
    (hab : E.starRel R₁ a b) : E.starRel R₂ a b := by
  have heq : (fun x y ↦ R₁ x y ∧ R₂ x y) = R₁ := by
    ext x y
    exact ⟨fun hp ↦ hp.1, fun hp ↦ ⟨hp, h x y hp⟩⟩
  have hand : E.starRel (fun x y ↦ R₁ x y ∧ R₂ x y) a b := by rwa [heq]
  exact ((E.starRel_and R₁ R₂ a b).1 hand).2

/-- Disjunction transfer for binary relations: `*(R₁ ∨ R₂) a b ↔ (*R₁) a b ∨ (*R₂) a b`. -/
theorem starRel_or {α β : Type u} (R₁ R₂ : α → β → Prop) (a : E.Star α) (b : E.Star β) :
    E.starRel (fun x y ↦ R₁ x y ∨ R₂ x y) a b ↔ E.starRel R₁ a b ∨ E.starRel R₂ a b := by
  have heq : (fun x y ↦ R₁ x y ∨ R₂ x y) = fun x y ↦ ¬ (¬ R₁ x y ∧ ¬ R₂ x y) := by
    ext x y
    tauto
  rw [heq, E.starRel_not, E.starRel_and, E.starRel_not, E.starRel_not]
  tauto

/-- Collection `𝒫_F(A) = {Z : Finset α | ↑Z ⊆ A}` of finite subsets of `A`
(Goldblatt §14.1, p. 184). -/
def hyperfiniteSubsets {α : Type u} (A : Set α) : Set (Finset α) :=
  {Z : Finset α | (↑Z : Set α) ⊆ A}

/-- Underlying subset `{x ∈ *α | *(· ∈ ·) x B}` of `*α` represented by an element
`B : E.Star (Finset α)` of `*(Finset α)` (Goldblatt §14.1–14.2, pp. 185–186). -/
def hyperfiniteSet {α : Type u} (B : E.Star (Finset α)) : Set (E.Star α) :=
  {x : E.Star α | E.starRel (· ∈ ·) x B}

/-- Membership in `E.hyperfiniteSet B` is `E.starRel (· ∈ ·) x B`. -/
@[simp]
theorem mem_hyperfiniteSet {α : Type u} {B : E.Star (Finset α)} {x : E.Star α} :
    x ∈ E.hyperfiniteSet B ↔ E.starRel (· ∈ ·) x B :=
  Iff.rfl

/-- For a standard finite set `F : Finset α`, `E.hyperfiniteSet (*F)` is `{*a : a ∈ F}`. -/
@[simp]
theorem hyperfiniteSet_starElem {α : Type u} (F : Finset α) :
    E.hyperfiniteSet (E.starElem F) = E.starElem '' (↑F : Set α) := by
  ext x
  rw [mem_hyperfiniteSet, E.starRel_starElem_right]
  exact Set.ext_iff.1 (E.starSet_finset F) x

/-- Transfer of `B ∈ *𝒫_F(A)`: every element of `E.hyperfiniteSet B` belongs to `*A`
(Goldblatt §14.1, p. 185: `B ⊆ *A`). -/
theorem hyperfiniteSet_subset_starSet {α : Type u} {A : Set α} {B : E.Star (Finset α)}
    (hB : B ∈ E.starSet (hyperfiniteSubsets A)) :
    E.hyperfiniteSet B ⊆ E.starSet A := by
  intro x hx
  have hswap : E.starRel (fun (Z : Finset α) (y : α) ↦ y ∈ Z) B x :=
    (E.starRel_swap (· ∈ ·) x B).2 hx
  exact E.starRel_imp_mem (A := hyperfiniteSubsets A) (B := A)
    (fun Z y hZA hyZ ↦ hZA hyZ) B x hB hswap

/-! ### The Three Formulations of Enlargement (Goldblatt §14.1–14.2, pp. 183–186) -/

/-- **Enlargement via the Finite Intersection Property** (Goldblatt §14.1, p. 184):
`E` is an **enlargement** if for every collection `ℱ : Set (Set β)` with the finite intersection
property (`Ch02.HasFIP ℱ`), the intersection `⋂_{B ∈ ℱ} *B` is nonempty. -/
def IsEnlargement : Prop :=
  ∀ ⦃β : Type u⦄ (ℱ : Set (Set β)), Ch02.HasFIP ℱ → (⋂ B ∈ ℱ, E.starSet B).Nonempty

/-- **Enlargement Condition via Concurrent Binary Relations** (Goldblatt §14.2, Theorem 14.2.1(2),
p. 186): For every concurrent binary relation `R : α → β → Prop`, there exists `b : *β` such that
`(*R) (*x) b` for all `x ∈ dom R`. -/
def EnlargementCondition : Prop :=
  ∀ ⦃α β : Type u⦄ (R : α → β → Prop), IsConcurrent R →
    ∃ b : E.Star β, ∀ x ∈ relDom R, E.starRel R (E.starElem x) b

/-- **Hyperfinite Approximation Property** (Goldblatt §14.2, Theorem 14.2.1(3), p. 186):
For every set `A : Set α`, there exists `B ∈ *𝒫_F(A)` whose induced hyperfinite subset
`E.hyperfiniteSet B` contains all standard members `im A = {*a : a ∈ A}` and is included in `*A`. -/
def HyperfiniteApproxProperty : Prop :=
  ∀ ⦃α : Type u⦄ (A : Set α),
    ∃ B : E.Star (Finset α),
      B ∈ E.starSet (hyperfiniteSubsets A) ∧
      E.starElem '' A ⊆ E.hyperfiniteSet B ∧
      E.hyperfiniteSet B ⊆ E.starSet A

/-- Set-of-ordered-pairs formulation of `EnlargementCondition` for `P : Set (α × β)`
(Goldblatt §14.2, p. 186). -/
theorem EnlargementCondition.realize_set {E : NonstandardExtension.{u, v}}
    (hE : E.EnlargementCondition) {α β : Type u} {P : Set (α × β)} (hP : IsConcurrentSet P) :
    ∃ b : E.Star β, ∀ x ∈ pairRelDom P,
      E.starRel (fun x y ↦ (x, y) ∈ P) (E.starElem x) b := by
  rw [pairRelDom_eq_relDom]
  exact hE _ hP

end NonstandardExtension

/-! ## §14.1 & §14.2 Concrete Motivating Examples of Concurrent Relations (Goldblatt pp. 184–186) -/

/-! ### Example 1: Nonidentity Relation `x ≠ y` and Nonstandard Elements of Infinite Sets -/

/-- Nonidentity binary relation `R x y ↔ x ≠ y` on a type `α` (Goldblatt §14.2, p. 186). -/
def neRel (α : Type u) : α → α → Prop := (· ≠ ·)

/-- Nonidentity binary relation restricted to a subset `A : Set α`:
`R = {(a, y) ∈ A × A : a ≠ y}` (Goldblatt §14.2, p. 186). -/
def neRelOn {α : Type u} (A : Set α) : α → α → Prop :=
  fun x y ↦ x ∈ A ∧ y ∈ A ∧ x ≠ y

/-- Punctured-set family `{A \ {a} : a ∈ A}` used in Goldblatt §14.1 (p. 184) to obtain
nonstandard members of an infinite set `A`. -/
def puncturedSingletonFamily {α : Type u} (A : Set α) : Set (Set α) :=
  (fun a : α ↦ A \ {a}) '' A

/-- Goldblatt §14.2 (p. 186): The nonidentity relation `neRel α` on `α` is concurrent **if and only
if** `α` is infinite! -/
theorem isConcurrent_neRel_iff (α : Type u) :
    IsConcurrent (neRel α) ↔ Infinite α := by
  constructor
  · rintro ⟨hne, hconc⟩
    rw [← not_finite_iff_infinite]
    intro hFin
    have : Fintype α := Fintype.ofFinite α
    obtain ⟨x₀, y₀, hxy₀⟩ := hne
    have hdom_univ : relDom (neRel α) = Set.univ := by
      ext x
      simp only [mem_relDom, neRel, Set.mem_univ, iff_true]
      by_cases hxx₀ : x = x₀
      · exact ⟨y₀, hxx₀ ▸ hxy₀⟩
      · exact ⟨x₀, hxx₀⟩
    have hsub : (↑(Finset.univ : Finset α) : Set α) ⊆ relDom (neRel α) := by
      rw [hdom_univ]
      exact Set.subset_univ _
    obtain ⟨y, hy⟩ := hconc Finset.univ hsub
    exact hy y (Finset.mem_univ y) rfl
  · intro hInf
    have hdom_univ : relDom (neRel α) = Set.univ := by
      ext x
      simp only [mem_relDom, neRel, Set.mem_univ, iff_true]
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset ({x} : Finset α)
      exact ⟨y, fun hxy ↦ hy (Finset.mem_singleton.2 hxy.symm)⟩
    refine ⟨?_, fun F _ ↦ ?_⟩
    · rw [hdom_univ]
      exact Set.univ_nonempty
    · obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset F
      exact ⟨y, fun x hxF hxy ↦ hy (hxy ▸ hxF)⟩

/-- Goldblatt §14.2 (p. 186): For any subset `A : Set α`, `neRelOn A` is concurrent **if and only
if** `A` is infinite! -/
theorem isConcurrent_neRelOn_iff {α : Type u} (A : Set α) :
    IsConcurrent (neRelOn A) ↔ A.Infinite := by
  constructor
  · rintro ⟨hne, hconc⟩ hFin
    obtain ⟨a₀, b₀, ha₀, hb₀, hab₀⟩ := hne
    have hdom_eq : relDom (neRelOn A) = A := by
      ext x
      simp only [mem_relDom, neRelOn]
      refine ⟨fun ⟨_, hx, _, _⟩ ↦ hx, fun hx ↦ ?_⟩
      by_cases hxa₀ : x = a₀
      · exact ⟨b₀, hx, hb₀, hxa₀ ▸ hab₀⟩
      · exact ⟨a₀, hx, ha₀, hxa₀⟩
    obtain ⟨y, hy⟩ := hconc hFin.toFinset (by rw [hFin.coe_toFinset, hdom_eq])
    obtain ⟨_, hyA, _⟩ := hy a₀ (hFin.mem_toFinset.2 ha₀)
    exact (hy y (hFin.mem_toFinset.2 hyA)).2.2 rfl
  · intro hInf
    have hdom_eq : relDom (neRelOn A) = A := by
      ext x
      simp only [mem_relDom, neRelOn]
      refine ⟨fun ⟨_, hx, _, _⟩ ↦ hx, fun hx ↦ ?_⟩
      obtain ⟨y, hyA, hyne⟩ := hInf.exists_notMem_finset ({x} : Finset α)
      exact ⟨y, hx, hyA, fun hxy ↦ hyne (Finset.mem_singleton.2 hxy.symm)⟩
    refine ⟨hdom_eq.symm ▸ hInf.nonempty, fun F hF ↦ ?_⟩
    rw [hdom_eq] at hF
    obtain ⟨y, hyA, hyF⟩ := hInf.exists_notMem_finset F
    exact ⟨y, fun x hxF ↦ ⟨hF hxF, hyA, fun hxy ↦ hyF (hxy ▸ hxF)⟩⟩

/-- Goldblatt §14.1 (p. 184): If `A` is infinite, `{A \ {a} : a ∈ A}` has the finite intersection
property. -/
theorem hasFIP_puncturedSingletonFamily {α : Type u} {A : Set α} (hA : A.Infinite) :
    Ch02.HasFIP (puncturedSingletonFamily A) := by
  intro s hs
  let F : Finset α := s.attach.image (fun B ↦ (hs B.2).choose)
  obtain ⟨y, hyA, hyF⟩ := hA.exists_notMem_finset F
  refine ⟨y, Set.mem_biInter fun B hBs ↦ ?_⟩
  rw [← (hs hBs).choose_spec.2]
  refine ⟨hyA, fun hy_eq ↦ hyF ?_⟩
  rw [Set.mem_singleton_iff.1 hy_eq]
  exact Finset.mem_image.2 ⟨⟨B, hBs⟩, Finset.mem_attach _ _, rfl⟩

/-- Goldblatt §14.1 & §14.2 (pp. 184, 186): Under `E.EnlargementCondition`, every infinite type
`α : Type u` acquires a **nonstandard element** `b ∈ *α \ Set.range E.starElem`! -/
theorem exists_nonstandard_of_infinite {E : NonstandardExtension.{u, v}}
    (hE : E.EnlargementCondition) (α : Type u) [Infinite α] :
    ∃ b : E.Star α, b ∉ Set.range E.starElem := by
  have hconc : IsConcurrent (neRel α) := (isConcurrent_neRel_iff α).2 ‹Infinite α›
  have hdom : relDom (neRel α) = Set.univ := by
    ext x
    simp only [mem_relDom, neRel, Set.mem_univ, iff_true]
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset ({x} : Finset α)
    exact ⟨y, fun hxy ↦ hy (Finset.mem_singleton.2 hxy.symm)⟩
  obtain ⟨b, hb⟩ := hE (neRel α) hconc
  refine ⟨b, ?_⟩
  rintro ⟨a, rfl⟩
  have hne : E.starRel (· ≠ ·) (E.starElem a) (E.starElem a) :=
    hb a (hdom.symm ▸ Set.mem_univ a)
  exact (E.starRel_ne _ _).1 hne rfl

/-- Goldblatt §14.1 & §14.2 (pp. 184, 186): Under `E.EnlargementCondition`, a subset `A : Set α` is
infinite **if and only if** `*A \ im A` is nonempty! -/
theorem infinite_iff_exists_nonstandard_mem_starSet {E : NonstandardExtension.{u, v}}
    (hE : E.EnlargementCondition) {α : Type u} (A : Set α) :
    A.Infinite ↔ ∃ b ∈ E.starSet A, b ∉ E.starElem '' A := by
  constructor
  · intro hInf
    have hconc : IsConcurrent (neRelOn A) := (isConcurrent_neRelOn_iff A).2 hInf
    obtain ⟨b, hb⟩ := hE (neRelOn A) hconc
    obtain ⟨a₀, ha₀⟩ := hconc.1
    have ha₀_rel : E.starRel (neRelOn A) (E.starElem a₀) b := hb a₀ ha₀
    have hbA : b ∈ E.starSet A := by
      have hsub : E.starRel (fun _ y ↦ y ∈ A) (E.starElem a₀) b :=
        E.starRel_mono (fun _ _ h ↦ h.2.1) ha₀_rel
      exact (E.starRel_starElem_left (fun _ y ↦ y ∈ A) a₀ b).1 hsub
    refine ⟨b, hbA, ?_⟩
    rintro ⟨a, haA, rfl⟩
    have ha_dom : a ∈ relDom (neRelOn A) := by
      obtain ⟨y, hyA, hyne⟩ := hInf.exists_notMem_finset ({a} : Finset α)
      exact ⟨y, haA, hyA, fun hay ↦ hyne (Finset.mem_singleton.2 hay.symm)⟩
    have hne : E.starRel (· ≠ ·) (E.starElem a) (E.starElem a) :=
      E.starRel_mono (fun _ _ h ↦ h.2.2) (hb a ha_dom)
    exact (E.starRel_ne _ _).1 hne rfl
  · rintro ⟨b, hbA, hbnot⟩ hFin
    rw [E.starSet_eq_image_of_finite hFin] at hbA
    exact hbnot hbA

/-- Goldblatt §14.1 (p. 184): Under `E.EnlargementCondition`, a subset `A : Set α` is infinite **if
and only if** `im A` is a **proper** subset (`⊂`) of `*A`! -/
theorem infinite_iff_image_starElem_ssubset_starSet {E : NonstandardExtension.{u, v}}
    (hE : E.EnlargementCondition) {α : Type u} (A : Set α) :
    A.Infinite ↔ E.starElem '' A ⊂ E.starSet A := by
  rw [Set.ssubset_iff_of_subset (E.image_starElem_subset_starSet A),
      infinite_iff_exists_nonstandard_mem_starSet hE A]

/-- Goldblatt §14.1 (p. 184): In any enlargement `E`, the standard copies of `ℕ`, `ℤ`, and `ℚ` inside
`ℝ` are **proper** subsets (`⊂`) of `*ℕ`, `*ℤ`, and `*ℚ` inside `*ℝ`! -/
theorem nat_int_rat_ssubset_starSet_in_enlargement {E : NonstandardExtension.{0, v}}
    (hE : E.EnlargementCondition) :
    E.starElem '' Set.range (Nat.cast : ℕ → ℝ) ⊂ E.starSet (Set.range (Nat.cast : ℕ → ℝ)) ∧
    E.starElem '' Set.range (Int.cast : ℤ → ℝ) ⊂ E.starSet (Set.range (Int.cast : ℤ → ℝ)) ∧
    E.starElem '' Set.range (Rat.cast : ℚ → ℝ) ⊂ E.starSet (Set.range (Rat.cast : ℚ → ℝ)) :=
  ⟨(infinite_iff_image_starElem_ssubset_starSet hE _).1
     (Set.infinite_range_of_injective Nat.cast_injective),
   (infinite_iff_image_starElem_ssubset_starSet hE _).1
     (Set.infinite_range_of_injective Int.cast_injective),
   (infinite_iff_image_starElem_ssubset_starSet hE _).1
     (Set.infinite_range_of_injective Rat.cast_injective)⟩

/-! ### Example 2: `n < y` on `ℕ` and `r < y` on `ℝ₊` → Unlimited Nonstandard Numbers -/

/-- Strict less-than relation on `ℕ`: `ltNatRel n y ↔ n < y` (Goldblatt §14.1–14.2, pp. 184–185). -/
def ltNatRel : ℕ → ℕ → Prop := (· < ·)

/-- Strict less-than relation on positive reals: `R = {(r, y) ∈ ℝ₊ × ℝ₊ : r < y}`
(Goldblatt §14.2, p. 185). -/
def ltPosRealRel : ℝ → ℝ → Prop := fun r y ↦ 0 < r ∧ 0 < y ∧ r < y

/-- Upper open rays `{(r, ∞) : r > 0}` on `ℝ` (Goldblatt §14.1, p. 184). -/
def posUnlimitedIntervals : Set (Set ℝ) :=
  (fun r : {r : ℝ // 0 < r} ↦ Set.Ioi r.1) '' Set.univ

/-- `ltNatRel` has full domain `Set.univ` and is concurrent (witness `F.sup id + 1`). -/
theorem isConcurrent_ltNatRel : relDom ltNatRel = Set.univ ∧ IsConcurrent ltNatRel := by
  have hdom : relDom ltNatRel = Set.univ := by
    ext n
    exact ⟨fun _ ↦ Set.mem_univ n, fun _ ↦ ⟨n + 1, Nat.lt_succ_self n⟩⟩
  refine ⟨hdom, hdom.symm ▸ Set.univ_nonempty, fun F _ ↦ ⟨F.sup id + 1, fun n hn ↦ ?_⟩⟩
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)

/-- `ltPosRealRel` has domain `{r : ℝ | 0 < r}` and is concurrent (Goldblatt §14.2, p. 185). -/
theorem isConcurrent_ltPosRealRel :
    relDom ltPosRealRel = {r : ℝ | 0 < r} ∧ IsConcurrent ltPosRealRel := by
  have hdom : relDom ltPosRealRel = {r : ℝ | 0 < r} := by
    ext r
    refine ⟨fun ⟨_, hr, _, _⟩ ↦ hr, fun hr ↦ ?_⟩
    have hr' : 0 < r := hr
    exact ⟨r + 1, hr', by linarith, by linarith⟩
  refine ⟨hdom, ⟨1, by rw [hdom]; exact show (0 : ℝ) < 1 from one_pos⟩, fun F hF ↦ ?_⟩
  rw [hdom] at hF
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · exact ⟨1, fun _ hx ↦ (Finset.notMem_empty _ hx).elim⟩
  · let m : ℝ := F.max' hFne
    have hm_pos : 0 < m := hF (Finset.max'_mem F hFne)
    refine ⟨m + 1, fun r hr ↦ ⟨hF hr, by linarith, ?_⟩⟩
    have hrm : r ≤ m := Finset.le_max' F r hr
    linarith

/-- Goldblatt §14.1 (p. 184): The collection `{(r, ∞) : r ∈ ℝ₊}` has the finite intersection
property. -/
theorem hasFIP_posUnlimitedIntervals : Ch02.HasFIP posUnlimitedIntervals := by
  intro s hs
  let F : Finset ℝ := s.attach.image (fun B ↦ (hs B.2).choose.1)
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · refine ⟨1, Set.mem_biInter fun B hBs ↦ ?_⟩
    have : (hs hBs).choose.1 ∈ F :=
      Finset.mem_image.2 ⟨⟨B, hBs⟩, Finset.mem_attach _ _, rfl⟩
    rw [hFe] at this
    exact (Finset.notMem_empty _ this).elim
  · refine ⟨F.max' hFne + 1, Set.mem_biInter fun B hBs ↦ ?_⟩
    rw [← (hs hBs).choose_spec.2, Set.mem_Ioi]
    have hmem : (hs hBs).choose.1 ∈ F :=
      Finset.mem_image.2 ⟨⟨B, hBs⟩, Finset.mem_attach _ _, rfl⟩
    have hle : (hs hBs).choose.1 ≤ F.max' hFne := Finset.le_max' F _ hmem
    linarith

/-- Under `E.EnlargementCondition`, there exists an **unlimited hypernatural** `N ∈ *ℕ` exceeding
`*n` for every `n : ℕ` (and consequently `N ∉ Set.range E.starElem`)! -/
theorem exists_unlimited_hypernat {E : NonstandardExtension.{0, v}}
    (hE : E.EnlargementCondition) :
    ∃ N : E.Star ℕ, (∀ n : ℕ, E.starRel (· < ·) (E.starElem n) N) ∧
      N ∉ Set.range E.starElem := by
  obtain ⟨hdom, hconc⟩ := isConcurrent_ltNatRel
  obtain ⟨N, hN⟩ := hE ltNatRel hconc
  have hunl : ∀ n : ℕ, E.starRel (· < ·) (E.starElem n) N :=
    fun n ↦ hN n (hdom.symm ▸ Set.mem_univ n)
  refine ⟨N, hunl, ?_⟩
  rintro ⟨m, rfl⟩
  exact Nat.lt_irrefl m ((E.starRel_starElem_iff (· < ·) m m).1 (hunl m))

/-- Goldblatt §14.1 & §14.2 (pp. 184–185): Under `E.EnlargementCondition`, there exists a
**positive unlimited hyperreal** `ω ∈ *ℝ` exceeding `*r` for every standard real `r : ℝ`! -/
theorem exists_pos_unlimited_hyperreal {E : NonstandardExtension.{0, v}}
    (hE : E.EnlargementCondition) :
    ∃ ω : E.Star ℝ, ∀ r : ℝ, E.starRel (· < ·) (E.starElem r) ω := by
  obtain ⟨hdom, hconc⟩ := isConcurrent_ltPosRealRel
  obtain ⟨ω, hω⟩ := hE ltPosRealRel hconc
  refine ⟨ω, fun r ↦ ?_⟩
  let p : ℝ := max r 1
  have hp_pos : 0 < p := lt_of_lt_of_le one_pos (le_max_right r 1)
  have hpω : E.starRel ltPosRealRel (E.starElem p) ω := hω p (hdom.symm ▸ hp_pos)
  have hlt_p : E.starRel (· < ·) (E.starElem p) ω :=
    E.starRel_mono (fun _ _ h ↦ h.2.2) hpω
  have hmem_p : ω ∈ E.starSet {y : ℝ | p < y} :=
    (E.starRel_starElem_left (· < ·) p ω).1 hlt_p
  have hsub : {y : ℝ | p < y} ⊆ {y : ℝ | r < y} := fun y hy ↦ (le_max_left r 1).trans_lt hy
  exact (E.starRel_starElem_left (· < ·) r ω).2 (E.starSet_mono hsub hmem_p)

/-! ### Example 3: `0 < y ∧ y < r` on `ℝ₊` → Positive and Nonzero Infinitesimals -/

/-- Concurrent relation `R r y ↔ 0 < y ∧ y < r` on `{r : ℝ // 0 < r}` (`ℝ₊`)
(Goldblatt §14.2, p. 185). -/
def posInfinitesimalRelOnPos (r : {r : ℝ // 0 < r}) (y : ℝ) : Prop :=
  0 < y ∧ y < r.1

/-- Concurrent relation `R = {(r, y) ∈ ℝ₊ × ℝ₊ : r > y}` on `ℝ × ℝ`
(Goldblatt §14.2, p. 185). -/
def posInfinitesimalRel (r y : ℝ) : Prop :=
  0 < r ∧ 0 < y ∧ y < r

/-- Open intervals `{(0, r) : r ∈ ℝ₊}` whose enlarged intersection is the set of positive
infinitesimals (Goldblatt §14.1, p. 184). -/
def posInfinitesimalIntervals : Set (Set ℝ) :=
  (fun r : {r : ℝ // 0 < r} ↦ Set.Ioo 0 r.1) '' Set.univ

/-- Punctured symmetric intervals `{(-r, r) \ {0} : r ∈ ℝ₊}` whose enlarged intersection is the set
of nonzero infinitesimals (Goldblatt §14.1, p. 184). -/
def nonzeroInfinitesimalIntervals : Set (Set ℝ) :=
  (fun r : {r : ℝ // 0 < r} ↦ Set.Ioo (-r.1) r.1 \ {0}) '' Set.univ

/-- `posInfinitesimalRelOnPos` has full domain `Set.univ` on `{r : ℝ // 0 < r}` and is concurrent
(witness `(min' F) / 2`). -/
theorem isConcurrent_posInfinitesimalRelOnPos :
    relDom posInfinitesimalRelOnPos = Set.univ ∧ IsConcurrent posInfinitesimalRelOnPos := by
  have hdom : relDom posInfinitesimalRelOnPos = Set.univ := by
    ext r
    exact ⟨fun _ ↦ Set.mem_univ r, fun _ ↦ ⟨r.1 / 2, half_pos r.2, half_lt_self r.2⟩⟩
  refine ⟨hdom, ⟨⟨1, one_pos⟩, hdom.symm ▸ Set.mem_univ _⟩, fun F _ ↦ ?_⟩
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · exact ⟨1, fun _ hx ↦ (Finset.notMem_empty _ hx).elim⟩
  · let Fval : Finset ℝ := F.image Subtype.val
    have hFval_ne : Fval.Nonempty := hFne.image Subtype.val
    let m : ℝ := Fval.min' hFval_ne
    obtain ⟨r₀, _, hr₀⟩ := Finset.mem_image.1 (Finset.min'_mem Fval hFval_ne)
    have hm_pos : 0 < m := by dsimp only [m]; rw [← hr₀]; exact r₀.2
    refine ⟨m / 2, fun r hr ↦ ⟨half_pos hm_pos, ?_⟩⟩
    have hmr : m ≤ r.1 := Finset.min'_le Fval r.1 (Finset.mem_image.2 ⟨r, hr, rfl⟩)
    linarith [half_lt_self hm_pos]

/-- `posInfinitesimalRel` has domain `{r : ℝ | 0 < r}` and is concurrent
(Goldblatt §14.2, p. 185). -/
theorem isConcurrent_posInfinitesimalRel :
    relDom posInfinitesimalRel = {r : ℝ | 0 < r} ∧ IsConcurrent posInfinitesimalRel := by
  have hdom : relDom posInfinitesimalRel = {r : ℝ | 0 < r} := by
    ext r
    refine ⟨fun ⟨_, hr, _, _⟩ ↦ hr, fun hr ↦ ?_⟩
    have hr' : 0 < r := hr
    exact ⟨r / 2, hr', half_pos hr', half_lt_self hr'⟩
  refine ⟨hdom, ⟨1, by rw [hdom]; exact show (0 : ℝ) < 1 from one_pos⟩, fun F hF ↦ ?_⟩
  rw [hdom] at hF
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · exact ⟨1, fun _ hx ↦ (Finset.notMem_empty _ hx).elim⟩
  · let m : ℝ := F.min' hFne
    have hm_pos : 0 < m := hF (Finset.min'_mem F hFne)
    refine ⟨m / 2, fun r hr ↦ ⟨hF hr, half_pos hm_pos, ?_⟩⟩
    have hmr : m ≤ r := Finset.min'_le F r hr
    linarith [half_lt_self hm_pos]

/-- Goldblatt §14.1 (p. 184): `posInfinitesimalIntervals = {(0, r) : r > 0}` has the finite
intersection property. -/
theorem hasFIP_posInfinitesimalIntervals : Ch02.HasFIP posInfinitesimalIntervals := by
  intro s hs
  let F : Finset ℝ := s.attach.image (fun B ↦ (hs B.2).choose.1)
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · refine ⟨1, Set.mem_biInter fun B hBs ↦ ?_⟩
    have : (hs hBs).choose.1 ∈ F :=
      Finset.mem_image.2 ⟨⟨B, hBs⟩, Finset.mem_attach _ _, rfl⟩
    rw [hFe] at this
    exact (Finset.notMem_empty _ this).elim
  · let m : ℝ := F.min' hFne
    obtain ⟨B₀, _, hB₀⟩ := Finset.mem_image.1 (Finset.min'_mem F hFne)
    have hm_pos : 0 < m := by dsimp only [m]; rw [← hB₀]; exact (hs B₀.2).choose.2
    refine ⟨m / 2, Set.mem_biInter fun B hBs ↦ ?_⟩
    rw [← (hs hBs).choose_spec.2, Set.mem_Ioo]
    have hmem : (hs hBs).choose.1 ∈ F :=
      Finset.mem_image.2 ⟨⟨B, hBs⟩, Finset.mem_attach _ _, rfl⟩
    exact ⟨half_pos hm_pos, (half_lt_self hm_pos).trans_le (Finset.min'_le F _ hmem)⟩

/-- Goldblatt §14.1 (p. 184): `nonzeroInfinitesimalIntervals = {(-r, r) \ {0} : r > 0}` has the
finite intersection property. -/
theorem hasFIP_nonzeroInfinitesimalIntervals : Ch02.HasFIP nonzeroInfinitesimalIntervals := by
  intro s hs
  let F : Finset ℝ := s.attach.image (fun B ↦ (hs B.2).choose.1)
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · refine ⟨1, Set.mem_biInter fun B hBs ↦ ?_⟩
    have : (hs hBs).choose.1 ∈ F :=
      Finset.mem_image.2 ⟨⟨B, hBs⟩, Finset.mem_attach _ _, rfl⟩
    rw [hFe] at this
    exact (Finset.notMem_empty _ this).elim
  · let m : ℝ := F.min' hFne
    obtain ⟨B₀, _, hB₀⟩ := Finset.mem_image.1 (Finset.min'_mem F hFne)
    have hm_pos : 0 < m := by dsimp only [m]; rw [← hB₀]; exact (hs B₀.2).choose.2
    refine ⟨m / 2, Set.mem_biInter fun B hBs ↦ ?_⟩
    rw [← (hs hBs).choose_spec.2, Set.mem_sdiff, Set.mem_Ioo, Set.mem_singleton_iff]
    have hmem : (hs hBs).choose.1 ∈ F :=
      Finset.mem_image.2 ⟨⟨B, hBs⟩, Finset.mem_attach _ _, rfl⟩
    have hle : m ≤ (hs hBs).choose.1 := Finset.min'_le F _ hmem
    exact ⟨⟨by linarith [half_pos hm_pos], (half_lt_self hm_pos).trans_le hle⟩,
      (half_pos hm_pos).ne'⟩

/-- Goldblatt §14.1 & §14.2 (pp. 184–185): Under `E.EnlargementCondition`, there exists a
**positive infinitesimal** `ε ∈ *ℝ` satisfying `*0 < ε` and `ε < *r` for every standard `r > 0`! -/
theorem exists_pos_infinitesimal {E : NonstandardExtension.{0, v}}
    (hE : E.EnlargementCondition) :
    ∃ ε : E.Star ℝ,
      E.starRel (· < ·) (E.starElem 0) ε ∧
      ∀ r : ℝ, 0 < r → E.starRel (· < ·) ε (E.starElem r) := by
  obtain ⟨hdom, hconc⟩ := isConcurrent_posInfinitesimalRelOnPos
  obtain ⟨ε, hε⟩ := hE posInfinitesimalRelOnPos hconc
  have h1 := hε ⟨1, one_pos⟩ (hdom.symm ▸ Set.mem_univ _)
  have hpos : E.starRel (· < ·) (E.starElem 0) ε := by
    rw [E.starRel_starElem_left]
    have hmem : ε ∈ E.starSet {y : ℝ | 0 < y ∧ y < 1} :=
      (E.starRel_starElem_left posInfinitesimalRelOnPos ⟨1, one_pos⟩ ε).1 h1
    exact E.starSet_mono (fun _ h ↦ h.1) hmem
  refine ⟨ε, hpos, fun r hr ↦ ?_⟩
  have hrε := hε ⟨r, hr⟩ (hdom.symm ▸ Set.mem_univ _)
  have hmem : ε ∈ E.starSet {y : ℝ | 0 < y ∧ y < r} :=
    (E.starRel_starElem_left posInfinitesimalRelOnPos ⟨r, hr⟩ ε).1 hrε
  rw [E.starRel_starElem_right]
  exact E.starSet_mono (fun _ h ↦ h.2) hmem

/-- Goldblatt §14.1 (p. 184): Exact characterization of `⋂ B ∈ posInfinitesimalIntervals, *B` as the
set of positive infinitesimals in `*ℝ`. -/
theorem mem_biInter_posInfinitesimalIntervals_iff (E : NonstandardExtension.{0, v})
    (b : E.Star ℝ) :
    b ∈ (⋂ B ∈ posInfinitesimalIntervals, E.starSet B) ↔
      E.starRel (· < ·) (E.starElem 0) b ∧
      ∀ r : ℝ, 0 < r → E.starRel (· < ·) b (E.starElem r) := by
  constructor
  · intro hb
    have h1 : b ∈ E.starSet (Set.Ioo (0 : ℝ) 1) :=
      Set.mem_iInter₂.1 hb (Set.Ioo 0 1) ⟨⟨1, one_pos⟩, Set.mem_univ _, rfl⟩
    refine ⟨?_, fun r hr ↦ ?_⟩
    · rw [E.starRel_starElem_left]
      exact E.starSet_mono (fun _ h ↦ h.1) h1
    · have hbr : b ∈ E.starSet (Set.Ioo (0 : ℝ) r) :=
        Set.mem_iInter₂.1 hb (Set.Ioo 0 r) ⟨⟨r, hr⟩, Set.mem_univ _, rfl⟩
      rw [E.starRel_starElem_right]
      exact E.starSet_mono (fun _ h ↦ h.2) hbr
  · rintro ⟨hpos, hlt⟩
    refine Set.mem_biInter fun B hB ↦ ?_
    rcases hB with ⟨⟨r, hr⟩, _, rfl⟩
    dsimp only
    have h1 : b ∈ E.starSet {y : ℝ | 0 < y} := (E.starRel_starElem_left (· < ·) 0 b).1 hpos
    have h2 : b ∈ E.starSet {y : ℝ | y < r} := (E.starRel_starElem_right (· < ·) b r).1 (hlt r hr)
    have heq : Set.Ioo (0 : ℝ) r = {y : ℝ | 0 < y} ∩ {y : ℝ | y < r} := rfl
    rw [heq, E.starSet_inter]
    exact ⟨h1, h2⟩

/-- Goldblatt §14.1 (p. 184): Exact characterization of `⋂ B ∈ nonzeroInfinitesimalIntervals, *B`
as the set of nonzero infinitesimals in `*ℝ`. -/
theorem mem_biInter_nonzeroInfinitesimalIntervals_iff (E : NonstandardExtension.{0, v})
    (b : E.Star ℝ) :
    b ∈ (⋂ B ∈ nonzeroInfinitesimalIntervals, E.starSet B) ↔
      b ≠ E.starElem 0 ∧
      ∀ r : ℝ, 0 < r →
        E.starRel (· < ·) (E.starElem (-r)) b ∧ E.starRel (· < ·) b (E.starElem r) := by
  constructor
  · intro hb
    have h1 : b ∈ E.starSet (Set.Ioo (-1 : ℝ) 1 \ {0}) :=
      Set.mem_iInter₂.1 hb _ ⟨⟨1, one_pos⟩, Set.mem_univ _, rfl⟩
    rw [E.starSet_sdiff, E.starSet_singleton, Set.mem_sdiff, Set.mem_singleton_iff] at h1
    refine ⟨h1.2, fun r hr ↦ ?_⟩
    have hbr : b ∈ E.starSet (Set.Ioo (-r) r \ {0}) :=
      Set.mem_iInter₂.1 hb _ ⟨⟨r, hr⟩, Set.mem_univ _, rfl⟩
    rw [E.starSet_sdiff, Set.mem_sdiff] at hbr
    exact ⟨(E.starRel_starElem_left (· < ·) (-r) b).2 (E.starSet_mono (fun _ h ↦ h.1) hbr.1),
           (E.starRel_starElem_right (· < ·) b r).2 (E.starSet_mono (fun _ h ↦ h.2) hbr.1)⟩
  · rintro ⟨hne, hlt⟩
    refine Set.mem_biInter fun B hB ↦ ?_
    rcases hB with ⟨⟨r, hr⟩, _, rfl⟩
    dsimp only
    rw [E.starSet_sdiff, E.starSet_singleton, Set.mem_sdiff, Set.mem_singleton_iff]
    have h1 : b ∈ E.starSet {y : ℝ | -r < y} :=
      (E.starRel_starElem_left (· < ·) (-r) b).1 (hlt r hr).1
    have h2 : b ∈ E.starSet {y : ℝ | y < r} :=
      (E.starRel_starElem_right (· < ·) b r).1 (hlt r hr).2
    have heq : Set.Ioo (-r) r = {y : ℝ | -r < y} ∩ {y : ℝ | y < r} := rfl
    rw [heq, E.starSet_inter]
    exact ⟨⟨h1, h2⟩, hne⟩

/-- Goldblatt §14.1 (p. 184): In any enlargement `E` (`E.IsEnlargement`), the set of **nonzero
infinitesimals** in `*ℝ` is nonempty! -/
theorem exists_nonzero_infinitesimal {E : NonstandardExtension.{0, v}}
    (hE : E.IsEnlargement) :
    ∃ b : E.Star ℝ, b ≠ E.starElem 0 ∧
      ∀ r : ℝ, 0 < r →
        E.starRel (· < ·) (E.starElem (-r)) b ∧ E.starRel (· < ·) b (E.starElem r) := by
  obtain ⟨b, hb⟩ := hE nonzeroInfinitesimalIntervals hasFIP_nonzeroInfinitesimalIntervals
  exact ⟨b, (mem_biInter_nonzeroInfinitesimalIntervals_iff E b).1 hb⟩

/-! ### Example 4: `x ∈ S` on `α × Finset α` → Hyperfinite Sets Containing Standard Entities -/

/-- Membership binary relation `R x S ↔ x ∈ S` between `α` and `Finset α`
(Goldblatt §14.2, p. 186). -/
def memFinsetRel (α : Type u) : α → Finset α → Prop := (· ∈ ·)

/-- Membership binary relation restricted to `A` and `𝒫_F(A)`:
`R = {(a, Z) : a ∈ Z ∈ 𝒫_F(A)}` (Goldblatt §14.2, p. 186). -/
def memFinsetSubsetRel {α : Type u} (A : Set α) : α → Finset α → Prop :=
  fun a Z ↦ a ∈ A ∧ a ∈ Z ∧ (↑Z : Set α) ⊆ A

/-- Family `{A_a : a ∈ A}` where `A_a = {Z ∈ 𝒫_F(A) : a ∈ Z}` (Goldblatt §14.1, p. 184). -/
def finsetContainingFamily {α : Type u} (A : Set α) : Set (Set (Finset α)) :=
  (fun a : α ↦ {Z : Finset α | (↑Z : Set α) ⊆ A ∧ a ∈ Z}) '' A

/-- On any nonempty type `α`, `memFinsetRel α` has full domain `Set.univ` and is concurrent
(witness `S = F` itself!). -/
theorem isConcurrent_memFinsetRel (α : Type u) [Nonempty α] :
    relDom (memFinsetRel α) = Set.univ ∧ IsConcurrent (memFinsetRel α) := by
  have hdom : relDom (memFinsetRel α) = Set.univ := by
    ext x
    exact ⟨fun _ ↦ Set.mem_univ x, fun _ ↦ ⟨{x}, Finset.mem_singleton_self x⟩⟩
  exact ⟨hdom, hdom.symm ▸ Set.univ_nonempty, fun F _ ↦ ⟨F, fun _ hx ↦ hx⟩⟩

/-- Goldblatt §14.2 (p. 186): For any nonempty `A : Set α`, `memFinsetSubsetRel A` has domain `A`
and is concurrent (witness `Z = F`). -/
theorem isConcurrent_memFinsetSubsetRel {α : Type u} {A : Set α} (hA : A.Nonempty) :
    relDom (memFinsetSubsetRel A) = A ∧ IsConcurrent (memFinsetSubsetRel A) := by
  have hdom : relDom (memFinsetSubsetRel A) = A := by
    ext a
    simp only [mem_relDom, memFinsetSubsetRel]
    exact ⟨fun ⟨_, ha, _, _⟩ ↦ ha,
      fun ha ↦ ⟨{a}, ha, Finset.mem_singleton_self a, by simpa using ha⟩⟩
  refine ⟨hdom, hdom.symm ▸ hA, fun F hF ↦ ?_⟩
  rw [hdom] at hF
  exact ⟨F, fun a haF ↦ ⟨hF haF, haF, hF⟩⟩

/-- Goldblatt §14.1 (pp. 184–185): For any `A : Set α`, `finsetContainingFamily A` has the finite
intersection property (witness `Z = {a_1, …, a_n}`). -/
theorem hasFIP_finsetContainingFamily {α : Type u} (A : Set α) :
    Ch02.HasFIP (finsetContainingFamily A) := by
  intro s hs
  let Z : Finset α := s.attach.image (fun B ↦ (hs B.2).choose)
  have hZA : (↑Z : Set α) ⊆ A := by
    intro a ha
    obtain ⟨B, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
    exact (hs B.2).choose_spec.1
  refine ⟨Z, Set.mem_biInter fun B hBs ↦ ?_⟩
  rw [← (hs hBs).choose_spec.2]
  exact ⟨hZA, Finset.mem_image.2 ⟨⟨B, hBs⟩, Finset.mem_attach _ _, rfl⟩⟩

/-- Goldblatt §14.2 (p. 186): Under `E.EnlargementCondition`, for every type `α : Type u` there
exists a hyperfinite entity `B : E.Star (Finset α)` whose induced hyperfinite subset contains all
standard elements `Set.range E.starElem ⊆ E.hyperfiniteSet B`! -/
theorem exists_hyperfinite_containing_all_standard {E : NonstandardExtension.{u, v}}
    (hE : E.EnlargementCondition) (α : Type u) :
    ∃ B : E.Star (Finset α), Set.range E.starElem ⊆ E.hyperfiniteSet B := by
  by_cases hα : Nonempty α
  · obtain ⟨hdom, hconc⟩ := isConcurrent_memFinsetRel α
    obtain ⟨B, hB⟩ := hE (memFinsetRel α) hconc
    refine ⟨B, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hB x (hdom.symm ▸ Set.mem_univ x)
  · refine ⟨E.starElem ∅, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hα ⟨x⟩).elim

/-! ### Example 5: Topological Open-Neighbourhood Concurrence and Infinitesimal Monads -/

/-- The **topological monad** (or halo) of `x : X` in a nonstandard extension `E`:
`monad E x = ⋂_{U open, x ∈ U} *U` (Goldblatt Chapter 10 & §14.1). -/
def monad (E : NonstandardExtension.{u, v}) {X : Type u} [TopologicalSpace X] (x : X) :
    Set (E.Star X) :=
  ⋂ U ∈ {U : Set X | IsOpen U ∧ x ∈ U}, E.starSet U

/-- `monad E x` equivalently equals the intersection `⋂_{N ∈ 𝓝 x} *N` over **all** neighbourhoods
of `x` in the neighbourhood filter `𝓝 x`. -/
theorem monad_eq_biInter_nhds (E : NonstandardExtension.{u, v}) {X : Type u}
    [TopologicalSpace X] (x : X) :
    monad E x = ⋂ N ∈ 𝓝 x, E.starSet N := by
  ext y
  simp only [monad, Set.mem_iInter]
  constructor
  · intro hy N hN
    obtain ⟨U, hUN, hUo, hxU⟩ := mem_nhds_iff.1 hN
    exact E.starSet_mono hUN (hy U ⟨hUo, hxU⟩)
  · intro hy U ⟨hUo, hxU⟩
    exact hy U (hUo.mem_nhds hxU)

/-- Neighbourhood filter membership relation `R N y ↔ N ∈ 𝓝 x ∧ y ∈ N` on `Set X × X`. -/
def nhdsRel {X : Type u} [TopologicalSpace X] (x : X) : Set X → X → Prop :=
  fun N y ↦ N ∈ 𝓝 x ∧ y ∈ N

/-- `nhdsRel x` has domain `{N : Set X | N ∈ 𝓝 x}` and is concurrent (witness `y = x`). -/
theorem isConcurrent_nhdsRel {X : Type u} [TopologicalSpace X] (x : X) :
    relDom (nhdsRel x) = {N : Set X | N ∈ 𝓝 x} ∧ IsConcurrent (nhdsRel x) := by
  have hdom : relDom (nhdsRel x) = {N : Set X | N ∈ 𝓝 x} := by
    ext N
    exact ⟨fun ⟨_, hN, _⟩ ↦ hN, fun hN ↦ ⟨x, hN, mem_of_mem_nhds hN⟩⟩
  refine ⟨hdom, ⟨Set.univ, hdom.symm ▸ Filter.univ_mem⟩, fun F hF ↦ ?_⟩
  rw [hdom] at hF
  exact ⟨x, fun N hNF ↦ ⟨hF hNF, mem_of_mem_nhds (hF hNF)⟩⟩

/-- Open-neighbourhood membership relation `R U y ↔ IsOpen U ∧ x ∈ U ∧ y ∈ U` on `Set X × X`. -/
def openNhdsRel {X : Type u} [TopologicalSpace X] (x : X) : Set X → X → Prop :=
  fun U y ↦ IsOpen U ∧ x ∈ U ∧ y ∈ U

/-- Subtype open-neighbourhood membership relation `R U y ↔ y ∈ U.1` on
`{U : Set X // IsOpen U ∧ x ∈ U} × X`. -/
def openNhdsSubtypeRel {X : Type u} [TopologicalSpace X] (x : X)
    (U : {U : Set X // IsOpen U ∧ x ∈ U}) (y : X) : Prop :=
  y ∈ U.1

/-- Punctured open-neighbourhood relation `R U y ↔ y ∈ U.1 ∧ y ≠ x` on
`{U : Set X // IsOpen U ∧ x ∈ U} × X`, capturing **nontrivial** monad points `y ≠ *x`. -/
def puncturedOpenNhdsRel {X : Type u} [TopologicalSpace X] (x : X)
    (U : {U : Set X // IsOpen U ∧ x ∈ U}) (y : X) : Prop :=
  y ∈ U.1 ∧ y ≠ x

/-- `openNhdsRel x` has domain `{U : Set X | IsOpen U ∧ x ∈ U}` and is concurrent (witness `y = x`). -/
theorem isConcurrent_openNhdsRel {X : Type u} [TopologicalSpace X] (x : X) :
    relDom (openNhdsRel x) = {U : Set X | IsOpen U ∧ x ∈ U} ∧ IsConcurrent (openNhdsRel x) := by
  have hdom : relDom (openNhdsRel x) = {U : Set X | IsOpen U ∧ x ∈ U} := by
    ext U
    exact ⟨fun ⟨_, hU, hxU, _⟩ ↦ ⟨hU, hxU⟩, fun ⟨hU, hxU⟩ ↦ ⟨x, hU, hxU, hxU⟩⟩
  refine ⟨hdom, ⟨Set.univ, hdom.symm ▸ ⟨isOpen_univ, Set.mem_univ x⟩⟩, fun F hF ↦ ?_⟩
  rw [hdom] at hF
  exact ⟨x, fun U hUF ↦ ⟨(hF hUF).1, (hF hUF).2, (hF hUF).2⟩⟩

/-- `openNhdsSubtypeRel x` has full domain `Set.univ` and is concurrent. -/
theorem isConcurrent_openNhdsSubtypeRel {X : Type u} [TopologicalSpace X] (x : X) :
    relDom (openNhdsSubtypeRel x) = Set.univ ∧ IsConcurrent (openNhdsSubtypeRel x) := by
  have hdom : relDom (openNhdsSubtypeRel x) = Set.univ := by
    ext U
    exact ⟨fun _ ↦ Set.mem_univ U, fun _ ↦ ⟨x, U.2.2⟩⟩
  refine ⟨hdom, ⟨⟨Set.univ, isOpen_univ, Set.mem_univ x⟩, hdom.symm ▸ Set.mem_univ _⟩,
    fun F _ ↦ ⟨x, fun U _ ↦ U.2.2⟩⟩

/-- Exact characterization of nontrivial open-neighbourhood concurrence:
`puncturedOpenNhdsRel x` has full domain `Set.univ` and is concurrent **if and only if** `x` is a
non-isolated point (`(𝓝[≠] x).NeBot`)! -/
theorem isConcurrent_puncturedOpenNhdsRel_iff {X : Type u} [TopologicalSpace X] (x : X) :
    (relDom (puncturedOpenNhdsRel x) = Set.univ ∧ IsConcurrent (puncturedOpenNhdsRel x)) ↔
      (𝓝[≠] x).NeBot := by
  constructor
  · rintro ⟨hdom, _⟩
    rw [Filter.neBot_iff]
    intro hbot
    have hemp : (∅ : Set X) ∈ 𝓝[≠] x := empty_mem_iff_bot.2 hbot
    rw [mem_nhdsWithin] at hemp
    obtain ⟨U, hU_open, hxU, hsub⟩ := hemp
    have hmem : (⟨U, hU_open, hxU⟩ : {V : Set X // IsOpen V ∧ x ∈ V}) ∈
        relDom (puncturedOpenNhdsRel x) := hdom.symm ▸ Set.mem_univ _
    obtain ⟨y, hyU, hyx⟩ := hmem
    exact hsub ⟨hyU, hyx⟩
  · intro hneBot
    have hdom : relDom (puncturedOpenNhdsRel x) = Set.univ := by
      ext U
      simp only [mem_relDom, puncturedOpenNhdsRel, Set.mem_univ, iff_true]
      have hmem : U.1 \ {x} ∈ 𝓝[≠] x :=
        mem_nhdsWithin.2 ⟨U.1, U.2.1, U.2.2, fun _ h ↦ h⟩
      obtain ⟨y, hyU, hyx⟩ := hneBot.nonempty_of_mem hmem
      exact ⟨y, hyU, Set.mem_singleton_iff.not.1 hyx⟩
    refine ⟨hdom, ⟨⟨Set.univ, isOpen_univ, Set.mem_univ x⟩, hdom.symm ▸ Set.mem_univ _⟩,
      fun F _ ↦ ?_⟩
    let V : Set X := ⋂ U ∈ F, U.1
    have hV_open : IsOpen V := isOpen_biInter_finset fun U _ ↦ U.2.1
    have hxV : x ∈ V := Set.mem_biInter fun U _ ↦ U.2.2
    have hmem : V \ {x} ∈ 𝓝[≠] x :=
      mem_nhdsWithin.2 ⟨V, hV_open, hxV, fun _ h ↦ h⟩
    obtain ⟨y, hyV, hyx⟩ := hneBot.nonempty_of_mem hmem
    exact ⟨y, fun U hUF ↦ ⟨Set.mem_iInter₂.1 hyV U hUF, Set.mem_singleton_iff.not.1 hyx⟩⟩

/-- Enlargement of `openNhdsRel x` yields a monad point inside `*U` simultaneously for all open
neighbourhoods `U` of `x`. -/
theorem exists_mem_monad_via_concurrence {E : NonstandardExtension.{u, v}}
    (hE : E.EnlargementCondition) {X : Type u} [TopologicalSpace X] (x : X) :
    ∃ y : E.Star X, y ∈ monad E x := by
  obtain ⟨hdom, hconc⟩ := isConcurrent_openNhdsRel x
  obtain ⟨y, hy⟩ := hE (openNhdsRel x) hconc
  refine ⟨y, Set.mem_biInter fun U hU ↦ ?_⟩
  have hUy := hy U (hdom.symm ▸ hU)
  have hmem := (E.starRel_starElem_left (openNhdsRel x) U y).1 hUy
  exact E.starSet_mono (fun _ h ↦ h.2.2) hmem

/-- For any non-isolated point `x : X` (`(𝓝[≠] x).NeBot`), `E.EnlargementCondition` produces a
**nontrivial** monad point `y ∈ monad E x` with `y ≠ *x`! -/
theorem exists_nontrivial_mem_monad_of_nhdsWithin_neBot {E : NonstandardExtension.{u, v}}
    (hE : E.EnlargementCondition) {X : Type u} [TopologicalSpace X] {x : X}
    (hx : (𝓝[≠] x).NeBot) :
    ∃ y : E.Star X, y ∈ monad E x ∧ y ≠ E.starElem x := by
  obtain ⟨hdom, hconc⟩ := (isConcurrent_puncturedOpenNhdsRel_iff x).2 hx
  obtain ⟨y, hy⟩ := hE (puncturedOpenNhdsRel x) hconc
  have huniv := hy ⟨Set.univ, isOpen_univ, Set.mem_univ x⟩ (hdom.symm ▸ Set.mem_univ _)
  have hy_ne : y ≠ E.starElem x := by
    have hmem : y ∈ E.starSet {z : X | z ∈ (Set.univ : Set X) ∧ z ≠ x} :=
      (E.starRel_starElem_left (puncturedOpenNhdsRel x)
        ⟨Set.univ, isOpen_univ, Set.mem_univ x⟩ y).1 huniv
    have hsub : {z : X | z ∈ (Set.univ : Set X) ∧ z ≠ x} ⊆ ({x} : Set X)ᶜ :=
      fun _ h hz ↦ h.2 (Set.mem_singleton_iff.1 hz)
    have hcompl : y ∈ E.starSet ({x} : Set X)ᶜ := E.starSet_mono hsub hmem
    rw [E.starSet_compl, E.starSet_singleton] at hcompl
    exact fun heq ↦ hcompl (Set.mem_singleton_iff.2 heq)
  refine ⟨y, Set.mem_biInter fun U hU ↦ ?_, hy_ne⟩
  have hUy := hy ⟨U, hU⟩ (hdom.symm ▸ Set.mem_univ _)
  have hmem := (E.starRel_starElem_left (puncturedOpenNhdsRel x) ⟨U, hU⟩ y).1 hUy
  exact E.starSet_mono (fun _ h ↦ h.1) hmem

/-! ### Example 6: FIP Membership Relation and Robinson's Nonstandard Compactness -/

/-- Membership relation `R A y ↔ A ∈ ℱ ∧ y ∈ A` on a family `ℱ : Set (Set α)`. -/
def fipMemRel {α : Type u} (ℱ : Set (Set α)) : Set α → α → Prop :=
  fun A y ↦ A ∈ ℱ ∧ y ∈ A

/-- For any nonempty family `ℱ : Set (Set α)`, `ℱ` has the finite intersection property
(`Ch02.HasFIP ℱ`) **if and only if** `relDom (fipMemRel ℱ) = ℱ` and `fipMemRel ℱ` is concurrent! -/
theorem hasFIP_iff_dom_eq_and_isConcurrent {α : Type u} {ℱ : Set (Set α)} (hℱ : ℱ.Nonempty) :
    Ch02.HasFIP ℱ ↔ relDom (fipMemRel ℱ) = ℱ ∧ IsConcurrent (fipMemRel ℱ) := by
  constructor
  · intro hfip
    have hdom : relDom (fipMemRel ℱ) = ℱ := by
      ext A
      simp only [mem_relDom, fipMemRel]
      refine ⟨fun ⟨_, hA, _⟩ ↦ hA, fun hA ↦ ?_⟩
      obtain ⟨y, hy⟩ := hfip {A} (by simpa using hA)
      exact ⟨y, hA, by simpa using hy⟩
    refine ⟨hdom, hdom.symm ▸ hℱ, fun F hF ↦ ?_⟩
    rw [hdom] at hF
    obtain ⟨y, hy⟩ := hfip F hF
    exact ⟨y, fun A hAF ↦ ⟨hF hAF, Set.mem_iInter₂.1 hy A hAF⟩⟩
  · rintro ⟨hdom, _, hconc⟩ s hs
    obtain ⟨y, hy⟩ := hconc s (hdom.symm ▸ hs)
    exact ⟨y, Set.mem_biInter fun A hAs ↦ (hy A hAs).2⟩

/-- Indexed family membership relation `R i y ↔ y ∈ B i` for `B : ι → Set α`. -/
def indexedFIPRel {ι : Type u} {α : Type u} (B : ι → Set α) : ι → α → Prop :=
  fun i y ↦ y ∈ B i

/-- On a nonempty index type `ι`, `indexedFIPRel B` has full domain `Set.univ` and is concurrent
iff every finite sub-intersection `⋂ i ∈ F, B i` is nonempty. -/
theorem isConcurrent_indexedFIPRel_iff {ι : Type u} [Nonempty ι] {α : Type u} (B : ι → Set α) :
    (relDom (indexedFIPRel B) = Set.univ ∧ IsConcurrent (indexedFIPRel B)) ↔
      ∀ F : Finset ι, (⋂ i ∈ F, B i).Nonempty := by
  constructor
  · rintro ⟨hdom, _, hconc⟩ F
    obtain ⟨y, hy⟩ := hconc F (hdom.symm ▸ Set.subset_univ _)
    exact ⟨y, Set.mem_biInter hy⟩
  · intro hFIP
    have hdom : relDom (indexedFIPRel B) = Set.univ := by
      ext i
      simp only [mem_relDom, indexedFIPRel, Set.mem_univ, iff_true]
      obtain ⟨y, hy⟩ := hFIP {i}
      exact ⟨y, by simpa using hy⟩
    refine ⟨hdom, hdom.symm ▸ Set.univ_nonempty, fun F _ ↦ ?_⟩
    obtain ⟨y, hy⟩ := hFIP F
    exact ⟨y, fun i hi ↦ Set.mem_iInter₂.1 hy i hi⟩

/-- **Robinson's Nonstandard Compactness Theorem** (recovering general topological compactness in
any enlargement `E`): For any topological space `X : Type u` and any subset `K : Set X`, `K` is
compact **if and only if** every `y ∈ *K` belongs to `monad E x` for some standard `x ∈ K`! -/
theorem isCompact_iff_forall_mem_starSet_exists_monad {E : NonstandardExtension.{u, v}}
    (hE : E.IsEnlargement) {X : Type u} [TopologicalSpace X] (K : Set X) :
    IsCompact K ↔ ∀ y ∈ E.starSet K, ∃ x ∈ K, y ∈ monad E x := by
  constructor
  · intro hK y hyK
    by_contra hnot
    push Not at hnot
    have hex : ∀ x : K, ∃ U : Set X, IsOpen U ∧ x.1 ∈ U ∧ y ∉ E.starSet U := by
      intro x
      have hx_not := hnot x.1 x.2
      unfold monad at hx_not
      rw [Set.mem_iInter₂] at hx_not
      push Not at hx_not
      obtain ⟨U, ⟨hUo, hxU⟩, hyU⟩ := hx_not
      exact ⟨U, hUo, hxU, hyU⟩
    choose U hU_open hxU hy_notU using hex
    have hcov : K ⊆ ⋃ x : K, U x := fun x hx ↦ Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
    obtain ⟨F, hFcov⟩ := hK.elim_finite_subcover U hU_open hcov
    have hstar_cov : E.starSet K ⊆ ⋃ x ∈ F, E.starSet (U x) := by
      rw [← E.starSet_biUnion_finset]
      exact E.starSet_mono hFcov
    obtain ⟨x, _, hyUx⟩ := Set.mem_iUnion₂.1 (hstar_cov hyK)
    exact hy_notU x hyUx
  · intro hmonad
    rw [isCompact_iff_finite_subcover]
    intro ι U hU_open hcov
    by_contra hno
    push Not at hno
    have hKne : K.Nonempty := by
      rcases K.eq_empty_or_nonempty with rfl | hne
      · exact (hno ∅ (Set.empty_subset _)).elim
      · exact hne
    let ℱ : Set (Set X) := insert K ((fun i : ι ↦ K \ U i) '' Set.univ)
    have hfip : Ch02.HasFIP ℱ := by
      intro s hs
      let s' : Finset (Set X) := s.filter (fun B ↦ B ∈ (fun i : ι ↦ K \ U i) '' Set.univ)
      let F : Finset ι := s'.attach.image (fun B ↦ (Finset.mem_filter.1 B.2).2.choose)
      obtain ⟨x₀, hx₀K, hx₀_not⟩ := Set.not_subset.1 (hno F)
      refine ⟨x₀, Set.mem_biInter fun B hBs ↦ ?_⟩
      rcases hs hBs with rfl | hB_img
      · exact hx₀K
      · have hBs' : B ∈ s' := Finset.mem_filter.2 ⟨hBs, hB_img⟩
        let i₀ : ι := (Finset.mem_filter.1 hBs').2.choose
        have hi₀_eq : K \ U i₀ = B := (Finset.mem_filter.1 hBs').2.choose_spec.2
        have hi₀F : i₀ ∈ F := Finset.mem_image.2 ⟨⟨B, hBs'⟩, Finset.mem_attach _ _, rfl⟩
        rw [← hi₀_eq]
        exact ⟨hx₀K, fun hx₀U ↦ hx₀_not (Set.mem_biUnion hi₀F hx₀U)⟩
    obtain ⟨y, hy⟩ := hE ℱ hfip
    have hyK : y ∈ E.starSet K := Set.mem_iInter₂.1 hy K (Set.mem_insert K _)
    obtain ⟨x, hxK, hy_monad⟩ := hmonad y hyK
    obtain ⟨i₀, hxi₀⟩ := Set.mem_iUnion.1 (hcov hxK)
    have hyUi₀ : y ∈ E.starSet (U i₀) :=
      Set.mem_iInter₂.1 hy_monad (U i₀) ⟨hU_open i₀, hxi₀⟩
    have hy_diff : y ∈ E.starSet (K \ U i₀) :=
      Set.mem_iInter₂.1 hy (K \ U i₀) (Set.mem_insert_of_mem K ⟨i₀, Set.mem_univ i₀, rfl⟩)
    rw [E.starSet_sdiff] at hy_diff
    exact hy_diff.2 hyUi₀

/-! ## §14.2 Equivalence of Concurrence, FIP, and Hyperfinite Approximation (pp. 186–188) -/

/-- **Theorem 14.2.1, `(1) → (2)`** (Goldblatt §14.2, p. 186):
If `E` satisfies the FIP enlargement property (`IsEnlargement`), then `E` satisfies the concurrent
relation realization property (`EnlargementCondition`). -/
theorem isEnlargement_imp_enlargementCondition {E : NonstandardExtension.{u, v}}
    (hE : E.IsEnlargement) : E.EnlargementCondition := by
  intro α β R hR
  obtain ⟨_, hfip⟩ := isConcurrent_iff_hasFIP_slices.1 hR
  obtain ⟨b, hb⟩ := hE (relSlice R '' relDom R) hfip
  refine ⟨b, fun x hx ↦ ?_⟩
  have hb_mem : b ∈ E.starSet (relSlice R x) :=
    Set.mem_iInter₂.1 hb (relSlice R x) ⟨x, hx, rfl⟩
  exact (E.starRel_starElem_left R x b).2 hb_mem

/-- **Theorem 14.2.1, `(2) → (3)`** (Goldblatt §14.2, p. 186):
If `E` satisfies `EnlargementCondition`, then `E` satisfies `HyperfiniteApproxProperty`
(for every set `A : Set α`, there exists `B ∈ *𝒫_F(A)` with `im A ⊆ B ⊆ *A`). -/
theorem enlargementCondition_imp_hyperfiniteApproxProperty {E : NonstandardExtension.{u, v}}
    (hE : E.EnlargementCondition) : E.HyperfiniteApproxProperty := by
  intro α A
  rcases A.eq_empty_or_nonempty with rfl | hA
  · have hmem : E.starElem (∅ : Finset α) ∈
        E.starSet (NonstandardExtension.hyperfiniteSubsets (∅ : Set α)) :=
      (E.starElem_mem_starSet_iff (∅ : Finset α)
        (NonstandardExtension.hyperfiniteSubsets ∅)).2
        (by simp [NonstandardExtension.hyperfiniteSubsets])
    exact ⟨E.starElem ∅, hmem, by simp, E.hyperfiniteSet_subset_starSet hmem⟩
  · obtain ⟨hdom, hconc⟩ := isConcurrent_memFinsetSubsetRel hA
    obtain ⟨B, hB⟩ := hE (memFinsetSubsetRel A) hconc
    obtain ⟨a₀, ha₀⟩ := hA
    have ha₀B : E.starRel (memFinsetSubsetRel A) (E.starElem a₀) B :=
      hB a₀ (hdom.symm ▸ ha₀)
    have hB_sub : B ∈ E.starSet (NonstandardExtension.hyperfiniteSubsets A) := by
      have hrel : E.starRel (fun _ (Z : Finset α) ↦ (↑Z : Set α) ⊆ A) (E.starElem a₀) B :=
        E.starRel_mono (fun _ _ h ↦ h.2.2) ha₀B
      exact (E.starRel_starElem_left _ a₀ B).1 hrel
    refine ⟨B, hB_sub, ?_, E.hyperfiniteSet_subset_starSet hB_sub⟩
    rintro _ ⟨a, haA, rfl⟩
    have haB : E.starRel (memFinsetSubsetRel A) (E.starElem a) B :=
      hB a (hdom.symm ▸ haA)
    exact E.starRel_mono (fun _ _ h ↦ h.2.1) haB

/-- **Theorem 14.2.1, `(3) → (1)`** (Goldblatt §14.2, p. 186):
If `E` satisfies `HyperfiniteApproxProperty`, then `E` satisfies `IsEnlargement`
(every FIP family `ℱ : Set (Set β)` has nonempty enlarged intersection `⋂_{C ∈ ℱ} *C`). -/
theorem hyperfiniteApproxProperty_imp_isEnlargement {E : NonstandardExtension.{u, v}}
    (hApprox : E.HyperfiniteApproxProperty) : E.IsEnlargement := by
  intro β ℱ hfip
  obtain ⟨B, hB_sub, hB_sup, _⟩ := hApprox ℱ
  let InterMem : Finset (Set β) → β → Prop := fun Z y ↦ ∀ z ∈ Z, y ∈ z
  have hdom_sub : NonstandardExtension.hyperfiniteSubsets ℱ ⊆ relDom InterMem := by
    intro Z hZ
    obtain ⟨y, hy⟩ := hfip Z hZ
    exact ⟨y, fun z hz ↦ Set.mem_iInter₂.1 hy z hz⟩
  have hB_dom : B ∈ relDom (E.starRel InterMem) := by
    rw [← E.starSet_dom InterMem]
    exact E.starSet_mono hdom_sub hB_sub
  obtain ⟨b, hb_inter⟩ := hB_dom
  refine ⟨b, Set.mem_biInter fun C hC ↦ ?_⟩
  have hCB : E.starElem C ∈ E.hyperfiniteSet B := hB_sup ⟨C, hC, rfl⟩
  have hB_has_C : B ∈ E.starSet {Z : Finset (Set β) | C ∈ Z} :=
    (E.starRel_starElem_left (· ∈ ·) C B).1 hCB
  exact E.starRel_imp_mem (A := {Z : Finset (Set β) | C ∈ Z}) (B := C) (R := InterMem)
    (fun Z y hCZ hZ ↦ hZ C hCZ) B b hB_has_C hb_inter

/-- **Theorem 14.2.1 (Equivalence `(1) ↔ (2)`)** (Goldblatt §14.2, p. 186):
`E.IsEnlargement ↔ E.EnlargementCondition`. -/
theorem isEnlargement_iff_enlargementCondition (E : NonstandardExtension.{u, v}) :
    E.IsEnlargement ↔ E.EnlargementCondition :=
  ⟨isEnlargement_imp_enlargementCondition,
   fun h ↦ hyperfiniteApproxProperty_imp_isEnlargement
     (enlargementCondition_imp_hyperfiniteApproxProperty h)⟩

/-- **Theorem 14.2.1 (Equivalence `(2) ↔ (3)`)** (Goldblatt §14.2, p. 186):
`E.EnlargementCondition ↔ E.HyperfiniteApproxProperty`. -/
theorem enlargementCondition_iff_hyperfiniteApproxProperty (E : NonstandardExtension.{u, v}) :
    E.EnlargementCondition ↔ E.HyperfiniteApproxProperty :=
  ⟨enlargementCondition_imp_hyperfiniteApproxProperty,
   fun h ↦ isEnlargement_imp_enlargementCondition
     (hyperfiniteApproxProperty_imp_isEnlargement h)⟩

/-- **Theorem 14.2.1 (Equivalence `(1) ↔ (3)`)** (Goldblatt §14.2, p. 186):
`E.IsEnlargement ↔ E.HyperfiniteApproxProperty`. -/
theorem isEnlargement_iff_hyperfiniteApproxProperty (E : NonstandardExtension.{u, v}) :
    E.IsEnlargement ↔ E.HyperfiniteApproxProperty :=
  ⟨fun h ↦ enlargementCondition_imp_hyperfiniteApproxProperty
     (isEnlargement_imp_enlargementCondition h),
   hyperfiniteApproxProperty_imp_isEnlargement⟩

/-- **Theorem 14.2.1 (Threefold Equivalence Theorem)** (Goldblatt §14.2, p. 186):
For any universe embedding `E : NonstandardExtension`, the following are equivalent:
1. `E.IsEnlargement` (FIP intersection property `⋂_{B ∈ 𝒜} *B ≠ ∅`),
2. `E.EnlargementCondition` (concurrent binary relation realization),
3. `E.HyperfiniteApproxProperty` (hyperfinite approximation `im A ⊆ B ∈ *𝒫_F(A)`). -/
theorem enlargement_tfae (E : NonstandardExtension.{u, v}) :
    List.TFAE [E.IsEnlargement, E.EnlargementCondition, E.HyperfiniteApproxProperty] := by
  tfae_have 1 → 2 := isEnlargement_imp_enlargementCondition
  tfae_have 2 → 3 := enlargementCondition_imp_hyperfiniteApproxProperty
  tfae_have 3 → 1 := hyperfiniteApproxProperty_imp_isEnlargement
  tfae_finish

/-! ### Parametric Ultrapower `ultrapowerExtension U` and Countable vs. Uncountable Domains in `ℝ*` -/

/-- Standard constant germ `a_J = [j ↦ a]` in an ultrapower over `U : Ultrafilter J`
(Goldblatt §14.3, p. 187). -/
def ultraElem {J : Type w} (U : Ultrafilter J) {α : Type u} (a : α) :
    Germ (U : Filter J) α :=
  Germ.const a

/-- Lifted subset `*A ⊆ Germ U α` in an ultrapower over `U : Ultrafilter J`
(Goldblatt §14.3, p. 188). -/
def ultraSet {J : Type w} (U : Ultrafilter J) {α : Type u} (A : Set α) :
    Set (Germ (U : Filter J) α) :=
  {x : Germ (U : Filter J) α | Germ.LiftPred (· ∈ A) x}

/-- Lifted binary relation `*R` on `Germ U α × Germ U β` in an ultrapower over `U : Ultrafilter J`
(Goldblatt §14.3, p. 188). -/
def ultraRel₂ {J : Type w} (U : Ultrafilter J) {α : Type u} {β : Type v}
    (R : α → β → Prop) : Germ (U : Filter J) α → Germ (U : Filter J) β → Prop :=
  Germ.LiftRel R

/-- Internal subset `[S_j] ⊆ Germ U α` defined by an indexed family `S : J → Set α`
(Goldblatt §11.1 & §14.3, p. 187). -/
def ultraInternalSet {J : Type w} (U : Ultrafilter J) {α : Type u} (S : J → Set α) :
    Set (Germ (U : Filter J) α) :=
  {x : Germ (U : Filter J) α | Germ.LiftRel (· ∈ ·) x (S : Germ (U : Filter J) (Set α))}

/-- Hyperfinite subset `[S_j] ⊆ Germ U α` defined by an indexed family of finite sets
`S : J → Finset α` (Goldblatt §12.3 & §14.3, p. 189). -/
def ultraHyperfiniteSet {J : Type w} (U : Ultrafilter J) {α : Type u} (S : J → Finset α) :
    Set (Germ (U : Filter J) α) :=
  {x : Germ (U : Filter J) α | Germ.LiftRel (· ∈ ·) x (S : Germ (U : Filter J) (Finset α))}

/-- Łoś membership criterion for `ultraSet`: `[f] ∈ *A ↔ {j ∈ J | f j ∈ A} ∈ U`
(Goldblatt §14.3, p. 188). -/
@[simp]
theorem coe_mem_ultraSet {J : Type w} (U : Ultrafilter J) {α : Type u}
    {f : J → α} {A : Set α} :
    (f : Germ (U : Filter J) α) ∈ ultraSet U A ↔ ∀ᶠ j in (U : Filter J), f j ∈ A :=
  Germ.liftPred_coe

/-- Łoś relational criterion for `ultraRel₂`:
`(*R) [f] [g] ↔ {j ∈ J | R (f j) (g j)} ∈ U` (Goldblatt §14.3, p. 188). -/
@[simp]
theorem coe_ultraRel₂ {J : Type w} (U : Ultrafilter J) {α : Type u} {β : Type v}
    {R : α → β → Prop} {f : J → α} {g : J → β} :
    ultraRel₂ U R (f : Germ (U : Filter J) α) (g : Germ (U : Filter J) β) ↔
      ∀ᶠ j in (U : Filter J), R (f j) (g j) :=
  Germ.liftRel_coe

/-- Łoś membership criterion for `ultraInternalSet`:
`[f] ∈ [S_j] ↔ {j ∈ J | f j ∈ S j} ∈ U` (Goldblatt §14.3, p. 188). -/
@[simp]
theorem coe_mem_ultraInternalSet {J : Type w} (U : Ultrafilter J) {α : Type u}
    {f : J → α} {S : J → Set α} :
    (f : Germ (U : Filter J) α) ∈ ultraInternalSet U S ↔
      ∀ᶠ j in (U : Filter J), f j ∈ S j :=
  Germ.liftRel_coe

/-- Łoś membership criterion for `ultraHyperfiniteSet`:
`[f] ∈ [S_j] ↔ {j ∈ J | f j ∈ S j} ∈ U` (Goldblatt §14.3, p. 189). -/
@[simp]
theorem coe_mem_ultraHyperfiniteSet {J : Type w} (U : Ultrafilter J) {α : Type u}
    {f : J → α} {S : J → Finset α} :
    (f : Germ (U : Filter J) α) ∈ ultraHyperfiniteSet U S ↔
      ∀ᶠ j in (U : Filter J), f j ∈ S j :=
  Germ.liftRel_coe

/-- Canonical `NonstandardExtension.{u, max w u}` induced by any ultrafilter `U : Ultrafilter J`
 via Łoś's Theorem for sets and binary relations (Goldblatt §14.3, pp. 187–188). -/
def ultrapowerExtension {J : Type w} (U : Ultrafilter J) :
    NonstandardExtension.{u, max w u} where
  Star α := Germ (U : Filter J) α
  starElem a := ultraElem U a
  starSet A := ultraSet U A
  starRel R := ultraRel₂ U R
  starElem_injective {α} x y hxy := by
    have hev : ∀ᶠ _ in (U : Filter J), x = y := Germ.coe_eq.1 hxy
    exact hev.exists.choose_spec
  starElem_mem_starSet_iff x A := Germ.liftPred_const_iff
  starSet_empty {α} := by
    ext x
    induction x using Germ.inductionOn with | _ f =>
    simp only [coe_mem_ultraSet, Set.mem_empty_iff_false, eventually_false_iff_eq_bot]
    exact ⟨fun h ↦ (Ultrafilter.neBot U).ne h, False.elim⟩
  starSet_univ {α} := by
    ext x
    induction x using Germ.inductionOn with | _ f =>
    simp only [coe_mem_ultraSet, Set.mem_univ, eventually_true]
  starSet_inter A B := by
    ext x
    induction x using Germ.inductionOn with | _ f =>
    exact eventually_and
  starSet_compl A := by
    ext x
    induction x using Germ.inductionOn with | _ f =>
    exact Ultrafilter.eventually_not
  starSet_singleton a := by
    ext x
    induction x using Germ.inductionOn with | _ f =>
    rw [coe_mem_ultraSet, Set.mem_singleton_iff]
    exact (Germ.coe_eq (f := f) (g := fun _ ↦ a)).symm.trans (by simp [ultraElem, Germ.const])
  starRel_eq x y := by
    induction x using Germ.inductionOn with | _ f =>
    induction y using Germ.inductionOn with | _ g =>
    rw [coe_ultraRel₂]
    exact Germ.coe_eq.symm
  starRel_starElem_left R x b := by
    induction b using Germ.inductionOn with | _ g =>
    exact Iff.rfl
  starRel_starElem_right R a y := by
    induction a using Germ.inductionOn with | _ f =>
    exact Iff.rfl
  starRel_not R a b := by
    induction a using Germ.inductionOn with | _ f =>
    induction b using Germ.inductionOn with | _ g =>
    exact Ultrafilter.eventually_not
  starRel_and R₁ R₂ a b := by
    induction a using Germ.inductionOn with | _ f =>
    induction b using Germ.inductionOn with | _ g =>
    exact eventually_and
  starRel_swap R a b := by
    induction a using Germ.inductionOn with | _ f =>
    induction b using Germ.inductionOn with | _ g =>
    exact Iff.rfl
  starRel_imp_mem h a b ha hab := by
    induction a using Germ.inductionOn with | _ f =>
    induction b using Germ.inductionOn with | _ g =>
    exact ((Germ.liftPred_coe.1 ha).and (Germ.liftRel_coe.1 hab)).mono
      fun j ⟨hjA, hjR⟩ ↦ h (f j) (g j) hjA hjR
  starSet_dom {α β} R := by
    ext a
    induction a using Germ.inductionOn with | _ f =>
    constructor
    · intro ha
      have hev : ∀ᶠ j in (U : Filter J), ∃ y : β, R (f j) y := Germ.liftPred_coe.1 ha
      obtain ⟨_, y₀, _⟩ := hev.exists
      let g : J → β := fun j ↦ if h : ∃ y : β, R (f j) y then h.choose else y₀
      refine ⟨(g : Germ (U : Filter J) β), Germ.liftRel_coe.2 (hev.mono fun j hj ↦ ?_)⟩
      simpa only [g, hj, ↓reduceDIte] using hj.choose_spec
    · rintro ⟨b, hab⟩
      induction b using Germ.inductionOn with | _ g =>
      exact Germ.liftPred_coe.2 ((Germ.liftRel_coe.1 hab).mono fun j hj ↦ ⟨g j, hj⟩)

/-- For any `S : J → Finset α`, `(ultrapowerExtension U).hyperfiniteSet [S]` equals
`ultraHyperfiniteSet U S`. -/
@[simp]
theorem ultrapowerExtension_hyperfiniteSet {J : Type w} (U : Ultrafilter J) {α : Type u}
    (S : J → Finset α) :
    (ultrapowerExtension U).hyperfiniteSet (S : Germ (U : Filter J) (Finset α)) =
      ultraHyperfiniteSet U S :=
  rfl

/-- Countable-domain enlargement property of `hyperfilter ℕ`:
The sequence ultrapower `Germ (hyperfilter ℕ)` enlarges **every** concurrent binary relation
`R : α → β → Prop` whose domain `relDom R` is countable (Goldblatt §11.10, §12.3, §14.1, p. 185)! -/
theorem hyperfilter_enlarges_countable_concurrent {α : Type u} {β : Type v}
    {R : α → β → Prop} (hR : IsConcurrent R) (hCount : (relDom R).Countable) :
    ∃ b : Germ (hyperfilter ℕ : Filter ℕ) β,
      ∀ x ∈ relDom R, ultraRel₂ (hyperfilter ℕ) R (ultraElem (hyperfilter ℕ) x) b := by
  obtain ⟨e, he⟩ := hCount.exists_eq_range hR.1
  let F : ℕ → Finset α := fun n ↦ (Finset.range (n + 1)).image e
  have hF_sub : ∀ n : ℕ, (↑(F n) : Set α) ⊆ relDom R := by
    intro n x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    rw [he]
    exact ⟨k, rfl⟩
  choose g hg using fun n ↦ hR.2 (F n) (hF_sub n)
  refine ⟨(g : Germ (hyperfilter ℕ : Filter ℕ) β), fun x hx ↦ ?_⟩
  rw [he] at hx
  obtain ⟨m, rfl⟩ := hx
  change Germ.LiftRel R ((fun _ ↦ e m : ℕ → α) : Germ (hyperfilter ℕ : Filter ℕ) α)
    (g : Germ (hyperfilter ℕ : Filter ℕ) β)
  rw [Germ.liftRel_coe]
  have hge : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), m ≤ n :=
    Nat.hyperfilter_le_atTop (eventually_ge_atTop m)
  refine hge.mono fun n hmn ↦ hg n (e m) ?_
  exact Finset.mem_image.2 ⟨m, Finset.mem_range.2 (Nat.lt_succ_of_le hmn), rfl⟩

/-- Specialization to `ℝ*`: `ℝ* = Germ (hyperfilter ℕ) ℝ` enlarges every concurrent relation
`P : Set (ℝ × ℝ)` with countable domain `pairRelDom P` (using `Goldblatt.starRel₂` from Chapter 3). -/
theorem hyperreal_enlarges_countable_concurrent {P : Set (ℝ × ℝ)}
    (hP : IsConcurrentSet P) (hCount : (pairRelDom P).Countable) :
    ∃ b : ℝ*, ∀ x ∈ pairRelDom P, ((x : ℝ*), b) ∈ Goldblatt.starRel₂ P := by
  rw [pairRelDom_eq_relDom] at hCount ⊢
  obtain ⟨b, hb⟩ := hyperfilter_enlarges_countable_concurrent hP hCount
  exact ⟨b, fun x hx ↦ hb x hx⟩

/-- Countable FIP intersection property for `Germ (hyperfilter ℕ)`: any countable family
`ℱ : Set (Set α)` with `Ch02.HasFIP ℱ` has nonempty enlarged intersection in
`ultrapowerExtension (hyperfilter ℕ)`. -/
theorem hyperfilter_enlarges_countable_fip {α : Type u} {ℱ : Set (Set α)}
    (hfip : Ch02.HasFIP ℱ) (hCount : ℱ.Countable) :
    (⋂ B ∈ ℱ, (ultrapowerExtension (hyperfilter ℕ)).starSet B).Nonempty := by
  rcases ℱ.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨y₀, _⟩ := hfip ∅ (by simp)
    exact ⟨ultraElem (hyperfilter ℕ) y₀, Set.mem_biInter fun _ h ↦ h.elim⟩
  · obtain ⟨hdom, hconc⟩ := (hasFIP_iff_dom_eq_and_isConcurrent hne).1 hfip
    obtain ⟨b, hb⟩ := hyperfilter_enlarges_countable_concurrent hconc (hdom.symm ▸ hCount)
    refine ⟨b, Set.mem_biInter fun B hB ↦ ?_⟩
    have hrel := hb B (hdom.symm ▸ hB)
    have hmem := ((ultrapowerExtension (hyperfilter ℕ)).starRel_starElem_left
      (fipMemRel ℱ) B b).1 hrel
    exact (ultrapowerExtension (hyperfilter ℕ)).starSet_mono (fun _ h ↦ h.2) hmem

/-- **Exact Characterization of Hyperfinite Approximation in `ℝ*`** (Goldblatt §12.3 Example 2,
p. 149 & §14.1, p. 185):
For a subset `A : Set ℝ`, there exists a hyperfinite subset `E ⊆ ℝ*` (`Goldblatt.IsHyperfinite E`)
containing all standard members `(↑) '' A` (with `E ⊆ Goldblatt.starSet A`) **if and only if** `A`
is countable! -/
theorem exists_hyperfinite_approx_hyperreal_iff_countable (A : Set ℝ) :
    (∃ E : Set ℝ*, Goldblatt.IsHyperfinite E ∧
      ((fun r : ℝ ↦ (r : ℝ*)) '' A) ⊆ E ∧ E ⊆ Goldblatt.starSet A) ↔ A.Countable := by
  constructor
  · rintro ⟨E, hE_fin, hAE, _⟩
    obtain ⟨S, rfl⟩ := Goldblatt.isHyperfinite_iff_exists_finset.1 hE_fin
    have hsub : A ⊆ ⋃ n : ℕ, (S n : Set ℝ) := by
      intro a ha
      have ha_mem : (a : ℝ*) ∈ Goldblatt.internalSet (fun n ↦ (S n : Set ℝ)) :=
        hAE ⟨a, ha, rfl⟩
      have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), a ∈ (S n : Set ℝ) :=
        Goldblatt.ofSeq_mem_internalSet.1 ha_mem
      obtain ⟨n, hn⟩ := hev.exists
      exact Set.mem_iUnion.2 ⟨n, hn⟩
    exact (Set.countable_iUnion fun n ↦ (Finset.finite_toSet (S n)).countable).mono hsub
  · exact Goldblatt.exists_hyperfinite_approx_of_countable

/-- Stronger negative form for uncountable subsets `A ⊆ ℝ` (Goldblatt §14.1, p. 185):
If `A ⊆ ℝ` is uncountable, **no** hyperfinite subset `E ⊆ ℝ*` can even contain all standard
elements `(↑) '' A`! -/
theorem no_hyperfinite_superset_of_uncountable {A : Set ℝ} (hUnc : ¬ A.Countable) :
    ¬ ∃ E : Set ℝ*, Goldblatt.IsHyperfinite E ∧ ((fun r : ℝ ↦ (r : ℝ*)) '' A) ⊆ E := by
  rintro ⟨E, hE_fin, hAE⟩
  obtain ⟨S, rfl⟩ := Goldblatt.isHyperfinite_iff_exists_finset.1 hE_fin
  have hsub : A ⊆ ⋃ n : ℕ, (S n : Set ℝ) := by
    intro a ha
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), a ∈ (S n : Set ℝ) :=
      Goldblatt.ofSeq_mem_internalSet.1 (hAE ⟨a, ha, rfl⟩)
    obtain ⟨n, hn⟩ := hev.exists
    exact Set.mem_iUnion.2 ⟨n, hn⟩
  exact hUnc ((Set.countable_iUnion fun n ↦ (Finset.finite_toSet (S n)).countable).mono hsub)

/-- Goldblatt §14.1 (p. 185): The sequence ultrapower `ultrapowerExtension.{0} (hyperfilter ℕ)`
(whose transform of `ℝ` is `ℝ*`) is **NOT** an enlargement, because `ℝ` (`Set.univ : Set ℝ`) is
uncountable and therefore admits no hyperfinite superset in `ℝ*`! -/
theorem not_isEnlargement_hyperfilter_nat :
    ¬ (ultrapowerExtension.{0} (hyperfilter ℕ)).IsEnlargement := by
  intro hEnl
  have hApprox := (isEnlargement_iff_hyperfiniteApproxProperty _).1 hEnl
  obtain ⟨B, _, hsup, _⟩ := hApprox (Set.univ : Set ℝ)
  induction B using Germ.inductionOn with | _ S =>
  let E : Set ℝ* := Goldblatt.internalSet (fun n ↦ (S n : Set ℝ))
  have hHyp : Goldblatt.IsHyperfinite E :=
    Goldblatt.isHyperfinite_iff_exists_finset.2 ⟨S, rfl⟩
  have hAE : ((fun r : ℝ ↦ (r : ℝ*)) '' (Set.univ : Set ℝ)) ⊆ E := by
    rintro _ ⟨r, hr, rfl⟩
    have hmem := hsup ⟨r, hr, rfl⟩
    exact Goldblatt.ofSeq_mem_internalSet.2 (Germ.liftRel_coe.1 hmem)
  exact no_hyperfinite_superset_of_uncountable Set.not_countable_univ ⟨E, hHyp, hAE⟩

/-! ## §14.3 & §14.4 Existence of Enlargements via Fine Ultrafilters (pp. 187–190) -/

/-! ### Fine Sets, Fine Filters, and `fineUltrafilter I` -/

/-- For `i : I`, `hatSet i = {s : Finset I | i ∈ s}` (`I_{{i}}` in Goldblatt §14.3, p. 189). -/
def hatSet {I : Type u} (i : I) : Set (Finset I) :=
  {s : Finset I | i ∈ s}

/-- For `a : Finset I`, `upperFinsetSet a = {b : Finset I | a ⊆ b}` (`I_a` in Goldblatt §14.3,
p. 188). -/
def upperFinsetSet {I : Type u} (a : Finset I) : Set (Finset I) :=
  {b : Finset I | a ⊆ b}

/-- Membership in `hatSet i` is `i ∈ s`. -/
@[simp]
theorem mem_hatSet {I : Type u} {i : I} {s : Finset I} :
    s ∈ hatSet i ↔ i ∈ s :=
  Iff.rfl

/-- Membership in `upperFinsetSet a` is `a ⊆ b`. -/
@[simp]
theorem mem_upperFinsetSet {I : Type u} {a b : Finset I} :
    b ∈ upperFinsetSet a ↔ a ⊆ b :=
  Iff.rfl

/-- `hatSet i` equals the upper ray `Set.Ici ({i} : Finset I)` in `Finset I` ordered by `⊆`. -/
theorem hatSet_eq_Ici {I : Type u} (i : I) :
    hatSet i = Set.Ici ({i} : Finset I) := by
  ext s
  simp [hatSet, Set.mem_Ici]

/-- `upperFinsetSet a` equals `Set.Ici a` in `Finset I` ordered by `⊆` (Goldblatt §14.3, p. 188). -/
theorem upperFinsetSet_eq_Ici {I : Type u} (a : Finset I) :
    upperFinsetSet a = Set.Ici a :=
  rfl

/-- `upperFinsetSet a` is the finite intersection `⋂ i ∈ a, hatSet i` (Goldblatt §14.3, p. 189). -/
theorem upperFinsetSet_eq_biInter_hatSet {I : Type u} (a : Finset I) :
    upperFinsetSet a = ⋂ i ∈ a, hatSet i := by
  ext s
  simp [upperFinsetSet, hatSet, Finset.subset_iff]

/-- Goldblatt §14.3 (pp. 188–189): The collection `{I_a : a ∈ Finset I}` of upper cones on
`Finset I` has the finite intersection property (`b = a_1 ∪ ⋯ ∪ a_n ∈ I_{a_1} ∩ ⋯ ∩ I_{a_n}`). -/
theorem hasFIP_range_upperFinsetSet (I : Type u) :
    Ch02.HasFIP (Set.range (upperFinsetSet (I := I))) := by
  intro s hs
  let b : Finset I := s.attach.biUnion (fun B ↦ (hs B.2).choose)
  refine ⟨b, Set.mem_biInter fun B hBs ↦ ?_⟩
  rw [← (hs hBs).choose_spec, mem_upperFinsetSet]
  intro i hi
  exact Finset.mem_biUnion.2 ⟨⟨B, hBs⟩, Finset.mem_attach _ _, hi⟩

/-- The collection `{hatSet i : i ∈ I}` has the finite intersection property on `Finset I`. -/
theorem hasFIP_range_hatSet (I : Type u) :
    Ch02.HasFIP (Set.range (hatSet (I := I))) := by
  intro s hs
  let b : Finset I := s.attach.image (fun B ↦ (hs B.2).choose)
  refine ⟨b, Set.mem_biInter fun B hBs ↦ ?_⟩
  rw [← (hs hBs).choose_spec, mem_hatSet]
  exact Finset.mem_image.2 ⟨⟨B, hBs⟩, Finset.mem_attach _ _, rfl⟩

/-- A filter `F` on `Finset I` is **fine** if it is proper (`F.NeBot`) and contains `hatSet i` for
every `i : I` (Goldblatt §14.3, pp. 188–189). -/
def IsFineFilter {I : Type u} (F : Filter (Finset I)) : Prop :=
  F.NeBot ∧ ∀ i : I, hatSet i ∈ F

/-- A filter `F` on `Finset I` is fine if and only if `F.NeBot` and `F ≤ Filter.atTop`! -/
theorem isFineFilter_iff_le_atTop {I : Type u} {F : Filter (Finset I)} :
    IsFineFilter F ↔ F.NeBot ∧ F ≤ Filter.atTop := by
  constructor
  · rintro ⟨hne, hhat⟩
    refine ⟨hne, ?_⟩
    rw [Filter.atTop, le_iInf_iff]
    intro a
    rw [le_principal_iff, ← upperFinsetSet_eq_Ici, upperFinsetSet_eq_biInter_hatSet]
    exact (biInter_finset_mem a).2 fun i _ ↦ hhat i
  · rintro ⟨hne, hle⟩
    refine ⟨hne, fun i ↦ ?_⟩
    rw [hatSet_eq_Ici]
    exact hle (Ici_mem_atTop ({i} : Finset I))

/-- `Filter.atTop : Filter (Finset I)` is itself a fine filter (`NeBot` and contains `hatSet i` for
every `i : I`). -/
theorem isFineFilter_atTop (I : Type u) :
    IsFineFilter (Filter.atTop : Filter (Finset I)) :=
  isFineFilter_iff_le_atTop.2 ⟨Filter.atTop_neBot, le_rfl⟩

/-- The **fine ultrafilter** `fineUltrafilter I` on `Finset I`, obtained by extending the proper
filter `Filter.atTop : Filter (Finset I)` via Zorn's Lemma / `Ultrafilter.of`
(Goldblatt §14.3, p. 189, citing Theorem 2.6.1). -/
def fineUltrafilter (I : Type u) : Ultrafilter (Finset I) :=
  Ultrafilter.of (Filter.atTop : Filter (Finset I))

/-- `(fineUltrafilter I : Filter (Finset I)) ≤ Filter.atTop` (it refines `Filter.atTop`). -/
theorem fineUltrafilter_le_atTop (I : Type u) :
    (fineUltrafilter I : Filter (Finset I)) ≤ Filter.atTop :=
  Ultrafilter.of_le (Filter.atTop : Filter (Finset I))

/-- Every `hatSet i = {s : Finset I | i ∈ s}` belongs to `fineUltrafilter I`
(Goldblatt §14.3, p. 189). -/
@[simp]
theorem hatSet_mem_fineUltrafilter {I : Type u} (i : I) :
    hatSet i ∈ fineUltrafilter I := by
  change hatSet i ∈ (fineUltrafilter I : Filter (Finset I))
  rw [hatSet_eq_Ici]
  exact fineUltrafilter_le_atTop I (Ici_mem_atTop ({i} : Finset I))

/-- Every upper cone `upperFinsetSet a = {b : Finset I | a ⊆ b}` belongs to `fineUltrafilter I`
(Goldblatt §14.3, p. 189). -/
@[simp]
theorem upperFinsetSet_mem_fineUltrafilter {I : Type u} (a : Finset I) :
    upperFinsetSet a ∈ fineUltrafilter I :=
  fineUltrafilter_le_atTop I (Ici_mem_atTop a)

/-- `fineUltrafilter I` is a fine filter on `Finset I`. -/
theorem isFineFilter_fineUltrafilter (I : Type u) :
    IsFineFilter (fineUltrafilter I : Filter (Finset I)) :=
  ⟨Ultrafilter.neBot (fineUltrafilter I), hatSet_mem_fineUltrafilter⟩

/-! ### Ultrapower over `fineUltrafilter I` and Exercises 14.4(1)–(3) (Goldblatt pp. 187–189) -/

/-- Elements `[f] ∈ Germ (fineUltrafilter I) α` of the ultrapower over `fineUltrafilter I`
(Goldblatt §14.3, p. 187). -/
abbrev FineUltrapower (I : Type w) (α : Type u) : Type (max w u) :=
  Germ (fineUltrafilter I : Filter (Finset I)) α

/-- The canonical `NonstandardExtension` over `fineUltrafilter I` (Goldblatt §14.3, pp. 187–189). -/
def fineUltrapowerExtension (I : Type w) : NonstandardExtension.{u, max w u} :=
  ultrapowerExtension (fineUltrafilter I)

/-- **Goldblatt §14.3 & Exercise 14.4(1)** (pp. 187, 189 — **Bounded-Rank Stabilization**):
If every object of `V` has a natural-number rank `rk : V → ℕ`, and `f : J → V` has bounded rank
`≤ n` modulo an ultrafilter `U` (`{j : J | rk (f j) ≤ n} ∈ U`), then there exists a **unique**
`k : ℕ` with `k ≤ n` and `{j : J | rk (f j) = k} ∈ U`! -/
theorem existsUnique_rank_mem_ultrafilter {J : Type w} (U : Ultrafilter J)
    {V : Type u} (rk : V → ℕ) {f : J → V} {n : ℕ}
    (hbdd : ∀ᶠ j in (U : Filter J), rk (f j) ≤ n) :
    ∃! k : ℕ, k ≤ n ∧ ∀ᶠ j in (U : Filter J), rk (f j) = k := by
  have hunion : (⋃ k ∈ {k : ℕ | k ≤ n}, {j : J | rk (f j) = k}) ∈ (U : Filter J) := by
    refine mem_of_superset hbdd fun j hj ↦ ?_
    exact Set.mem_biUnion hj rfl
  rw [Ultrafilter.mem_coe, Ultrafilter.finite_biUnion_mem_iff (Set.finite_le_nat n)] at hunion
  obtain ⟨k, hk_le, hk_ev⟩ := hunion
  have hk_ev' : ∀ᶠ j in (U : Filter J), rk (f j) = k := hk_ev
  refine ⟨k, ⟨hk_le, hk_ev'⟩, fun m ⟨_, hm_ev⟩ ↦ ?_⟩
  obtain ⟨j, hjk, hjm⟩ := (hk_ev'.and hm_ev).exists
  exact hjm.symm.trans hjk

/-- **Goldblatt §14.3 & Exercise 14.4(1)** (p. 187): The ultrafilter rank of any constant function
`fun _ ↦ a` equals the rank `rk a` of `a`. -/
theorem const_rank_mem_ultrafilter {J : Type w} (U : Ultrafilter J)
    {V : Type u} (rk : V → ℕ) (a : V) :
    ∀ᶠ _ in (U : Filter J), rk a = rk a :=
  Eventually.of_forall fun _ ↦ rfl

/-- Constructive lifting `(Fin k → Germ l α) → Germ l (Fin k → α)` over an arbitrary filter
`l : Filter J` (generalizing `piToGerm` from `ℕ` in Chapter 3 to arbitrary index sets `J`,
Goldblatt §14.3, p. 188). -/
def ultraPiToGerm {J : Type w} {α : Type u} {l : Filter J} :
    {k : ℕ} → (Fin k → Germ l α) → Germ l (Fin k → α)
  | 0, _ => Germ.const Fin.elim0
  | _ + 1, v => Germ.map₂ Fin.cons (v 0) (ultraPiToGerm (Fin.tail v))

/-- Componentwise evaluation of `ultraPiToGerm` on quotient representatives `[r_0], …, [r_{k-1}]`. -/
@[simp]
theorem ultraPiToGerm_coe {J : Type w} {α : Type u} {l : Filter J} :
    ∀ {k : ℕ} (r : Fin k → J → α),
      ultraPiToGerm (l := l) (fun i ↦ (r i : Germ l α)) =
        ((fun j i ↦ r i j) : Germ l (Fin k → α))
  | 0, _ => Germ.coe_eq.2 <| Eventually.of_forall fun _ ↦ funext fun i ↦ Fin.elim0 i
  | _ + 1, r => by
      unfold ultraPiToGerm
      have htail : (Fin.tail fun i ↦ (r i : Germ l α)) = fun m ↦ (r m.succ : Germ l α) := rfl
      rw [htail, ultraPiToGerm_coe (fun m ↦ r m.succ), Germ.map₂_coe]
      exact Germ.coe_eq.2 <| Eventually.of_forall fun _ ↦ funext fun i ↦
        Fin.cases rfl (fun _ ↦ rfl) i

/-- `k`-ary relation extension `*P ⊆ (Fin k → Germ U α)` over an arbitrary ultrafilter
`U : Ultrafilter J` (Goldblatt §14.3, p. 188, lines 315–322). -/
def ultraRelN {J : Type w} (U : Ultrafilter J) {α : Type u} {k : ℕ}
    (P : Set (Fin k → α)) : Set (Fin k → Germ (U : Filter J) α) :=
  {v : Fin k → Germ (U : Filter J) α | (ultraPiToGerm v).LiftPred (· ∈ P)}

/-- **General `k`-ary Łoś Theorem** (Goldblatt §14.3, p. 188):
`*P([f_1], …, [f_k])` holds **if and only if** `{j ∈ J | P(f_1(j), …, f_k(j))} ∈ U`! -/
@[simp]
theorem coe_mem_ultraRelN {J : Type w} (U : Ultrafilter J) {α : Type u} {k : ℕ}
    (P : Set (Fin k → α)) (f : Fin k → J → α) :
    (fun i ↦ (f i : Germ (U : Filter J) α)) ∈ ultraRelN U P ↔
      ∀ᶠ j in (U : Filter J), (fun i ↦ f i j) ∈ P := by
  change (ultraPiToGerm (fun i ↦ (f i : Germ (U : Filter J) α))).LiftPred (· ∈ P) ↔ _
  rw [ultraPiToGerm_coe, Germ.liftPred_coe]

/-- Boolean and existential Łoś laws (`∩`, `∪`, `ᶜ`, and `∃`-projection `Fin.init '' P`) for
`ultraRelN U` over any ultrafilter `U : Ultrafilter J` (Goldblatt §14.3, p. 188 & Exercise 14.4(1)). -/
theorem ultraRelN_boolean_and_dom {J : Type w} (U : Ultrafilter J) {α : Type u} :
    (∀ {k : ℕ} (P Q : Set (Fin k → α)),
      ultraRelN U (P ∩ Q) = ultraRelN U P ∩ ultraRelN U Q ∧
      ultraRelN U (P ∪ Q) = ultraRelN U P ∪ ultraRelN U Q ∧
      ultraRelN U Pᶜ = (ultraRelN U P)ᶜ) ∧
    (∀ {m : ℕ} (P : Set (Fin (m + 1) → α)),
      ultraRelN U (Fin.init '' P) = Fin.init '' ultraRelN U P) := by
  refine ⟨fun {k} P Q ↦ ⟨?_, ?_, ?_⟩, fun {m} P ↦ ?_⟩
  · ext v
    choose f hf using fun i ↦ Quot.exists_rep (v i)
    have hv : v = fun i ↦ (f i : Germ (U : Filter J) α) := funext fun i ↦ (hf i).symm
    rw [hv, Set.mem_inter_iff, coe_mem_ultraRelN, coe_mem_ultraRelN, coe_mem_ultraRelN]
    exact eventually_and
  · ext v
    choose f hf using fun i ↦ Quot.exists_rep (v i)
    have hv : v = fun i ↦ (f i : Germ (U : Filter J) α) := funext fun i ↦ (hf i).symm
    rw [hv, Set.mem_union, coe_mem_ultraRelN, coe_mem_ultraRelN, coe_mem_ultraRelN]
    exact Ultrafilter.eventually_or
  · ext v
    choose f hf using fun i ↦ Quot.exists_rep (v i)
    have hv : v = fun i ↦ (f i : Germ (U : Filter J) α) := funext fun i ↦ (hf i).symm
    rw [hv, Set.mem_compl_iff, coe_mem_ultraRelN, coe_mem_ultraRelN]
    exact Ultrafilter.eventually_not
  · ext v
    choose f hf using fun i ↦ Quot.exists_rep (v i)
    have hv : v = fun i ↦ (f i : Germ (U : Filter J) α) := funext fun i ↦ (hf i).symm
    rw [hv, coe_mem_ultraRelN]
    constructor
    · intro hv_mem
      obtain ⟨_, w₀, _, _⟩ := hv_mem.exists
      let lastSeq : J → α := fun j ↦
        if h : (fun i ↦ f i j) ∈ Fin.init '' P then h.choose (Fin.last m) else w₀ (Fin.last m)
      let full : Fin (m + 1) → J → α := Fin.snoc f lastSeq
      refine ⟨fun i ↦ (full i : Germ (U : Filter J) α), ?_, ?_⟩
      · rw [coe_mem_ultraRelN]
        refine hv_mem.mono fun j hj ↦ ?_
        have hspec := hj.choose_spec
        have heq : (fun i : Fin (m + 1) ↦ full i j) = hj.choose := by
          ext idx
          refine Fin.lastCases ?_ (fun i ↦ ?_) idx
          · simp only [full, Fin.snoc_last, lastSeq, hj, ↓reduceDIte]
          · have hi := congrFun hspec.2 i
            simpa [full, Fin.init] using hi.symm
        rw [heq]
        exact hspec.1
      · ext i
        simp [Fin.init, full]
    · rintro ⟨w, hw, hw_eq⟩
      choose g hg using fun i ↦ Quot.exists_rep (w i)
      have hw' : w = fun i ↦ (g i : Germ (U : Filter J) α) := funext fun i ↦ (hg i).symm
      rw [hw', coe_mem_ultraRelN] at hw
      have heq_all : ∀ i : Fin m, ∀ᶠ j in (U : Filter J), g i.castSucc j = f i j := by
        intro i
        have hi : (g i.castSucc : Germ (U : Filter J) α) = (f i : Germ (U : Filter J) α) := by
          have := congrFun hw_eq i
          simpa [hw', Fin.init] using this
        exact Germ.coe_eq.1 hi
      rw [← eventually_all] at heq_all
      refine (hw.and heq_all).mono fun j ⟨hjP, hjgf⟩ ↦ ⟨fun idx ↦ g idx j, hjP, ?_⟩
      ext i
      exact hjgf i

/-- **Goldblatt Exercise 14.4(1)** (pp. 188–189): Equality of internal sets `[S_j] = [T_j]` in an
ultrapower over `U : Ultrafilter J` holds **if and only if** `{j ∈ J | S j = T j} ∈ U`. -/
theorem ultraInternalSet_eq_iff {J : Type w} (U : Ultrafilter J) {α : Type u}
    {S T : J → Set α} :
    ultraInternalSet U S = ultraInternalSet U T ↔ ∀ᶠ j in (U : Filter J), S j = T j := by
  constructor
  · intro heq
    by_contra hnot
    have hne : ∀ᶠ j in (U : Filter J), S j ≠ T j :=
      Ultrafilter.eventually_not.2 hnot
    have hwit : ∀ᶠ j in (U : Filter J), ∃ x : α, (x ∈ S j ∧ x ∉ T j) ∨ (x ∈ T j ∧ x ∉ S j) := by
      refine hne.mono fun j hj ↦ ?_
      by_contra hno
      apply hj
      ext x
      exact ⟨fun hxS ↦ Classical.byContradiction fun hxT ↦ hno ⟨x, Or.inl ⟨hxS, hxT⟩⟩,
             fun hxT ↦ Classical.byContradiction fun hxS ↦ hno ⟨x, Or.inr ⟨hxT, hxS⟩⟩⟩
    obtain ⟨_, x₀, _⟩ := hwit.exists
    let f : J → α := fun j ↦
      if h : ∃ x : α, (x ∈ S j ∧ x ∉ T j) ∨ (x ∈ T j ∧ x ∉ S j) then h.choose else x₀
    have hmem_iff : (f : Germ (U : Filter J) α) ∈ ultraInternalSet U S ↔
        (f : Germ (U : Filter J) α) ∈ ultraInternalSet U T := by
      rw [heq]
    rw [coe_mem_ultraInternalSet, coe_mem_ultraInternalSet] at hmem_iff
    by_cases hfS : ∀ᶠ j in (U : Filter J), f j ∈ S j
    · have hfT : ∀ᶠ j in (U : Filter J), f j ∈ T j := hmem_iff.1 hfS
      obtain ⟨j, ⟨hj_wit, hjS⟩, hjT⟩ := ((hwit.and hfS).and hfT).exists
      have hspec : (f j ∈ S j ∧ f j ∉ T j) ∨ (f j ∈ T j ∧ f j ∉ S j) := by
        simpa only [f, hj_wit, ↓reduceDIte] using hj_wit.choose_spec
      rcases hspec with ⟨_, hnT⟩ | ⟨_, hnS⟩
      · exact hnT hjT
      · exact hnS hjS
    · have hnfS : ∀ᶠ j in (U : Filter J), f j ∉ S j :=
        Ultrafilter.eventually_not.2 hfS
      have hnfT : ∀ᶠ j in (U : Filter J), f j ∉ T j :=
        Ultrafilter.eventually_not.2 (mt hmem_iff.2 hfS)
      obtain ⟨j, ⟨hj_wit, hjS⟩, hjT⟩ := ((hwit.and hnfS).and hnfT).exists
      have hspec : (f j ∈ S j ∧ f j ∉ T j) ∨ (f j ∈ T j ∧ f j ∉ S j) := by
        simpa only [f, hj_wit, ↓reduceDIte] using hj_wit.choose_spec
      rcases hspec with ⟨hS, _⟩ | ⟨hT, _⟩
      · exact hjS hS
      · exact hjT hT
  · intro hev
    ext x
    induction x using Germ.inductionOn with | _ f =>
    simp only [coe_mem_ultraInternalSet]
    exact ⟨fun hfS ↦ (hfS.and hev).mono fun j ⟨h1, h2⟩ ↦ h2 ▸ h1,
           fun hfT ↦ (hfT.and hev).mono fun j ⟨h1, h2⟩ ↦ h2.symm ▸ h1⟩

/-- Internal function application `[F]([h])` for `F : Germ U (α → β)` and `x : Germ U α`
(Goldblatt Exercise 14.4(2), p. 189). -/
def ultraFunApply {J : Type w} (U : Ultrafilter J) {α : Type u} {β : Type v}
    (F : Germ (U : Filter J) (α → β)) (x : Germ (U : Filter J) α) :
    Germ (U : Filter J) β :=
  Germ.map₂ (fun fn a ↦ fn a) F x

/-- **Goldblatt Exercise 14.4(2)** (p. 189):
If `F : J → (α → β)`, `h : J → α`, and `k : J → β`, then `[F]([h]) = [k]` holds **if and only if**
`{j ∈ J | F j (h j) = k j} ∈ U`! -/
theorem ultraFunApply_eq_iff {J : Type w} (U : Ultrafilter J) {α : Type u} {β : Type v}
    (F : J → α → β) (h : J → α) (k : J → β) :
    ultraFunApply U (F : Germ (U : Filter J) (α → β)) (h : Germ (U : Filter J) α) =
      (k : Germ (U : Filter J) β) ↔
      ∀ᶠ j in (U : Filter J), F j (h j) = k j :=
  Germ.coe_eq

/-- Partial-function version of **Goldblatt Exercise 14.4(2)** (p. 189): if for `U`-almost all `j`,
`D j` is the domain of `F j` and `h j ∈ D j`, then `[h] ∈ [D_j]` and
`[F]([h]) = [k] ↔ {j ∈ J | F j (h j) = k j} ∈ U`. -/
theorem ultraPartialFunApply_eq_iff {J : Type w} (U : Ultrafilter J) {α : Type u} {β : Type v}
    (D : J → Set α) (F : J → α → β) (h : J → α) (k : J → β)
    (hdom : ∀ᶠ j in (U : Filter J), h j ∈ D j) :
    (h : Germ (U : Filter J) α) ∈ ultraInternalSet U D ∧
      (ultraFunApply U (F : Germ (U : Filter J) (α → β)) (h : Germ (U : Filter J) α) =
        (k : Germ (U : Filter J) β) ↔
        ∀ᶠ j in (U : Filter J), F j (h j) = k j) :=
  ⟨coe_mem_ultraInternalSet U |>.2 hdom, Germ.coe_eq⟩

/-- **Goldblatt Exercise 14.4(3)** (p. 189):
Whenever `I` is infinite (as `𝕌(X)` always is in Goldblatt §14.3), **every** fine ultrafilter `U`
on `Finset I` (in particular `fineUltrafilter I`) extends `Filter.cofinite` — so it contains no
finite subsets of `Finset I` and is **nonprincipal**! -/
theorem fine_ultrafilter_le_cofinite_of_infinite {I : Type u} [Infinite I]
    {U : Ultrafilter (Finset I)} (hU : ∀ i : I, hatSet i ∈ U) :
    (U : Filter (Finset I)) ≤ Filter.cofinite := by
  intro S hS
  have hFin : Sᶜ.Finite := mem_cofinite.1 hS
  let F_compl : Finset (Finset I) := hFin.toFinset
  let U_all : Finset I := F_compl.biUnion id
  obtain ⟨i₀, hi₀⟩ := Infinite.exists_notMem_finset U_all
  have hsub : hatSet i₀ ⊆ S := by
    intro s hs
    by_contra hs_not
    have hs_mem : s ∈ F_compl := hFin.mem_toFinset.2 hs_not
    have hi₀_mem : i₀ ∈ U_all := Finset.mem_biUnion.2 ⟨s, hs_mem, hs⟩
    exact hi₀ hi₀_mem
  exact mem_of_superset (hU i₀) hsub

/-- **Goldblatt Exercise 14.4(3), Nonprincipality Corollary** (p. 189):
When `I` is infinite, `fineUltrafilter I` contains no finite subsets of `Finset I` and is distinct
from every principal ultrafilter `pure s` (`s : Finset I`). -/
theorem fineUltrafilter_nonprincipal_of_infinite {I : Type u} [Infinite I] :
    (∀ T : Set (Finset I), T.Finite → T ∉ fineUltrafilter I) ∧
    (∀ s : Finset I, (fineUltrafilter I : Filter (Finset I)) ≠ pure s) := by
  have hcof : (fineUltrafilter I : Filter (Finset I)) ≤ Filter.cofinite :=
    fine_ultrafilter_le_cofinite_of_infinite hatSet_mem_fineUltrafilter
  refine ⟨fun T hT hT_mem ↦ ?_, fun s hs_eq ↦ ?_⟩
  · have hcompl : Tᶜ ∈ (fineUltrafilter I : Filter (Finset I)) :=
      hcof (hT.compl_mem_cofinite)
    have hemp : (∅ : Set (Finset I)) ∈ (fineUltrafilter I : Filter (Finset I)) := by
      simpa using inter_mem hT_mem hcompl
    exact (Ultrafilter.neBot (fineUltrafilter I)).ne (empty_mem_iff_bot.1 hemp)
  · have hsing_compl : ({s} : Set (Finset I))ᶜ ∈ (fineUltrafilter I : Filter (Finset I)) :=
      hcof (Set.finite_singleton s).compl_mem_cofinite
    rw [hs_eq, mem_pure] at hsing_compl
    exact hsing_compl (Set.mem_singleton s)

/-- **Goldblatt Exercise 14.4(3), Complete Iff Characterization** (p. 189):
`fineUltrafilter I` is nonprincipal (`∀ s, ↑(fineUltrafilter I) ≠ pure s`) **if and only if** `I`
is infinite! (When `I` is finite, `Finset.univ` is the greatest element of `Finset I`, forcing
`fineUltrafilter I = pure Finset.univ`.) -/
theorem fineUltrafilter_nonprincipal_iff_infinite (I : Type u) :
    (∀ s : Finset I, (fineUltrafilter I : Filter (Finset I)) ≠ pure s) ↔ Infinite I := by
  constructor
  · intro hnp
    rw [← not_finite_iff_infinite]
    intro hFin
    have htop_fin : (Set.univ : Set I).Finite := Set.finite_univ
    let s_top : Finset I := htop_fin.toFinset
    have hIci_eq : Set.Ici s_top = ({s_top} : Set (Finset I)) := by
      ext s
      simp only [Set.mem_Ici, Set.mem_singleton_iff]
      refine ⟨fun hsub ↦ Finset.Subset.antisymm ?_ hsub, fun h ↦ h ▸ Finset.Subset.refl _⟩
      intro x _
      exact htop_fin.mem_toFinset.2 (Set.mem_univ x)
    have hsing_mem : ({s_top} : Set (Finset I)) ∈ (fineUltrafilter I : Filter (Finset I)) := by
      rw [← hIci_eq]
      exact fineUltrafilter_le_atTop I (Ici_mem_atTop s_top)
    apply hnp s_top
    ext A
    simp only [mem_pure]
    constructor
    · intro hA
      obtain ⟨t, htA, hts⟩ :=
        (Ultrafilter.neBot (fineUltrafilter I)).nonempty_of_mem (inter_mem hA hsing_mem)
      rwa [Set.mem_singleton_iff.1 hts] at htA
    · intro hsA
      exact mem_of_superset hsing_mem (Set.singleton_subset_iff.2 hsA)
  · intro _
    exact fineUltrafilter_nonprincipal_of_infinite.2

/-! ### Theorem 14.3.1 & the Global Enlargement Theorem (Goldblatt pp. 185, 188–189) -/

/-- **Theorem 14.3.1 (Single Concurrent Relation & Simultaneous Hyperfinite Set)**
(Goldblatt §14.3, pp. 188–189):
For any concurrent binary relation `R : α → β → Prop`, taking `I = α` and the diagonal witness
`b(s)` chosen for `s ∩ dom R` yields an element `[b] ∈ FineUltrapower α β` satisfying
`∀ x ∈ relDom R, (*R) (*x) [b]` — while `[id] ∈ FineUltrapower α (Finset α)` simultaneously forms a
hyperfinite set containing `*x` for every `x : α`! -/
theorem theorem_14_3_1_single_concurrent {α : Type u} {β : Type v}
    {R : α → β → Prop} (hR : IsConcurrent R) :
    (∃ b : FineUltrapower α β,
      ∀ x ∈ relDom R, ultraRel₂ (fineUltrafilter α) R (ultraElem (fineUltrafilter α) x) b) ∧
    (∀ x : α, ultraElem (fineUltrafilter α) x ∈
      ultraHyperfiniteSet (fineUltrafilter α) (id : Finset α → Finset α)) := by
  have hsub : ∀ s : Finset α, (↑(s.filter (· ∈ relDom R)) : Set α) ⊆ relDom R := by
    intro s x hx
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
  choose b hb using fun s : Finset α ↦ hR.2 (s.filter (· ∈ relDom R)) (hsub s)
  refine ⟨⟨(b : FineUltrapower α β), fun x hx ↦ ?_⟩, fun x ↦ ?_⟩
  · change Germ.LiftRel R ((fun _ ↦ x : Finset α → α) : FineUltrapower α α)
      (b : FineUltrapower α β)
    rw [Germ.liftRel_coe]
    refine mem_of_superset (hatSet_mem_fineUltrafilter x) fun s hs ↦ ?_
    exact hb s x (Finset.mem_filter.2 ⟨hs, hx⟩)
  · change ((fun _ ↦ x : Finset α → α) : FineUltrapower α α) ∈
      ultraHyperfiniteSet (fineUltrafilter α) id
    rw [coe_mem_ultraHyperfiniteSet]
    exact hatSet_mem_fineUltrafilter x

/-- **Theorem 14.3.1 (Arbitrary Indexed Family of Concurrent Relations)**
(Goldblatt §14.3, pp. 188–189):
Given **any** `K`-indexed family of concurrent relations `(R_k : α k → β k → Prop)_{k : K}`, setting
`I = Σ k : K, {x : α k // x ∈ relDom (R k)}` makes the **single** ultrapower over
`fineUltrafilter I` simultaneously enlarge **every** relation `R k` in the family! -/
theorem theorem_14_3_1_family_concurrent {K : Type w}
    {α : K → Type u} {β : K → Type v} (R : ∀ k : K, α k → β k → Prop)
    (hR : ∀ k : K, IsConcurrent (R k)) :
    ∀ k : K,
      ∃ b : FineUltrapower (Σ j : K, {x : α j // x ∈ relDom (R j)}) (β k),
        ∀ x ∈ relDom (R k),
          ultraRel₂ (fineUltrafilter (Σ j : K, {x : α j // x ∈ relDom (R j)})) (R k)
            (ultraElem (fineUltrafilter (Σ j : K, {x : α j // x ∈ relDom (R j)})) x) b := by
  intro k
  let I := Σ j : K, {x : α j // x ∈ relDom (R j)}
  let extract (p : I) : Finset (α k) :=
    if h : p.1 = k then {(h ▸ p.2).1} else ∅
  let fiber (s : Finset I) : Finset (α k) := s.biUnion extract
  have hsub : ∀ s : Finset I, (↑(fiber s) : Set (α k)) ⊆ relDom (R k) := by
    intro s x hx
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hx)
    by_cases hpk : p.1 = k
    · subst hpk
      simp only [extract, ↓reduceDIte, Finset.mem_singleton] at hp
      subst hp
      exact p.2.2
    · simp [extract, hpk] at hp
  choose b hb using fun s : Finset I ↦ (hR k).2 (fiber s) (hsub s)
  refine ⟨(b : FineUltrapower I (β k)), fun x hx ↦ ?_⟩
  change Germ.LiftRel (R k) ((fun _ ↦ x : Finset I → α k) : FineUltrapower I (α k))
    (b : FineUltrapower I (β k))
  rw [Germ.liftRel_coe]
  let idx : I := ⟨k, ⟨x, hx⟩⟩
  refine mem_of_superset (hatSet_mem_fineUltrafilter idx) fun s hs ↦ ?_
  apply hb s x
  refine Finset.mem_biUnion.2 ⟨idx, hs, ?_⟩
  simp [extract, idx]

/-- **Theorem 14.3.1 (Goldblatt's Direct FIP Ultrapower Proof)** (Goldblatt §14.3, p. 189,
lines 346–362):
For any collection `ℱ : Set (Set β)` with `Ch02.HasFIP ℱ`, choosing `f(b) ∈ ⋂ (b ∩ ℱ)` on
`I = Finset (Set β)` yields `[f] ∈ ⋂ B ∈ ℱ, ultraSet (fineUltrafilter (Set β)) B`. -/
theorem theorem_14_3_1_fip {β : Type u} {ℱ : Set (Set β)} (hfip : Ch02.HasFIP ℱ) :
    (⋂ B ∈ ℱ, ultraSet (fineUltrafilter (Set β)) B).Nonempty := by
  have hsub : ∀ s : Finset (Set β), (↑(s.filter (· ∈ ℱ)) : Set (Set β)) ⊆ ℱ := by
    intro s B hB
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hB)).2
  choose f hf using fun s : Finset (Set β) ↦ hfip (s.filter (· ∈ ℱ)) (hsub s)
  refine ⟨(f : FineUltrapower (Set β) β), Set.mem_biInter fun B hB ↦ ?_⟩
  rw [coe_mem_ultraSet]
  refine mem_of_superset (hatSet_mem_fineUltrafilter B) fun s hs ↦ ?_
  exact Set.mem_iInter₂.1 (hf s) B (Finset.mem_filter.2 ⟨hs, hB⟩)

/-- **Theorem 14.3.1 (Goldblatt's Direct Hyperfinite Approximation Proof `g(b) = b ∩ A`)**
(Goldblatt §14.3, p. 189, lines 364–375):
For any subset `A : Set α`, putting `g(b) = b.filter (· ∈ A)` (`b ∩ A`) defines an element
`[g] ∈ FineUltrapower α (Finset α)` satisfying `[g] ∈ *𝒫_F(A)` and
`im A ⊆ ultraHyperfiniteSet (fineUltrafilter α) g ⊆ *A`! -/
theorem theorem_14_3_1_hyperfinite_approx {α : Type u} (A : Set α) :
    let E := fineUltrapowerExtension α
    let g : Finset α → Finset α := fun b ↦ b.filter (· ∈ A)
    let B : E.Star (Finset α) := (g : FineUltrapower α (Finset α))
    B ∈ E.starSet (NonstandardExtension.hyperfiniteSubsets A) ∧
      E.starElem '' A ⊆ E.hyperfiniteSet B ∧
      E.hyperfiniteSet B ⊆ E.starSet A := by
  let E := fineUltrapowerExtension α
  let g : Finset α → Finset α := fun b ↦ b.filter (· ∈ A)
  let B : E.Star (Finset α) := (g : FineUltrapower α (Finset α))
  have hB_sub : B ∈ E.starSet (NonstandardExtension.hyperfiniteSubsets A) := by
    change (g : FineUltrapower α (Finset α)) ∈
      ultraSet (fineUltrafilter α) {Z : Finset α | (↑Z : Set α) ⊆ A}
    rw [coe_mem_ultraSet]
    exact Eventually.of_forall fun b x hx ↦ (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
  refine ⟨hB_sub, ?_, E.hyperfiniteSet_subset_starSet hB_sub⟩
  rintro _ ⟨a, haA, rfl⟩
  change ((fun _ ↦ a : Finset α → α) : FineUltrapower α α) ∈
    ultraHyperfiniteSet (fineUltrafilter α) g
  rw [coe_mem_ultraHyperfiniteSet]
  refine mem_of_superset (hatSet_mem_fineUltrafilter a) fun b hb ↦ ?_
  exact Finset.mem_filter.2 ⟨hb, haA⟩

/-- Universal index type `Σ α : Type u, α` collecting all elements of all types in `Type u`
(type-theoretic counterpart of the superstructure `𝕌(X)` in Goldblatt §14.3, p. 188). -/
abbrev UniverseIndex : Type (u + 1) :=
  Σ α : Type u, α

/-- **The Universal Ultrapower Enlargement** `universalUltrapowerEnlargement.{u}`:
a `NonstandardExtension.{u, u + 1}` constructed as the ultrapower over
`fineUltrafilter UniverseIndex.{u}` (Goldblatt §14.1, Enlargement Theorem, p. 185 & §14.3, p. 189). -/
def universalUltrapowerEnlargement : NonstandardExtension.{u, u + 1} :=
  fineUltrapowerExtension UniverseIndex.{u}

/-- **Hyperfinite Approximation for `universalUltrapowerEnlargement`** (Goldblatt §14.3, p. 189):
`universalUltrapowerEnlargement.{u}` satisfies `HyperfiniteApproxProperty` simultaneously for
**every** type `α : Type u` and **every** subset `A : Set α`! -/
theorem universalUltrapowerEnlargement_hyperfiniteApprox :
    (universalUltrapowerEnlargement.{u}).HyperfiniteApproxProperty := by
  intro α A
  let E := universalUltrapowerEnlargement.{u}
  let extract (p : UniverseIndex.{u}) : Finset α :=
    if h : p.1 = α then {h ▸ p.2} else ∅
  let g (s : Finset UniverseIndex.{u}) : Finset α :=
    (s.biUnion extract).filter (· ∈ A)
  let B : E.Star (Finset α) := (g : FineUltrapower UniverseIndex.{u} (Finset α))
  have hB_sub : B ∈ E.starSet (NonstandardExtension.hyperfiniteSubsets A) := by
    change (g : FineUltrapower UniverseIndex.{u} (Finset α)) ∈
      ultraSet (fineUltrafilter UniverseIndex.{u}) {Z : Finset α | (↑Z : Set α) ⊆ A}
    rw [coe_mem_ultraSet]
    exact Eventually.of_forall fun s x hx ↦ (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
  refine ⟨B, hB_sub, ?_, E.hyperfiniteSet_subset_starSet hB_sub⟩
  rintro _ ⟨a, haA, rfl⟩
  change ((fun _ ↦ a : Finset UniverseIndex.{u} → α) : FineUltrapower UniverseIndex.{u} α) ∈
    ultraHyperfiniteSet (fineUltrafilter UniverseIndex.{u}) g
  rw [coe_mem_ultraHyperfiniteSet]
  let idx : UniverseIndex.{u} := ⟨α, a⟩
  refine mem_of_superset (hatSet_mem_fineUltrafilter idx) fun s hs ↦ ?_
  refine Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨idx, hs, ?_⟩, haA⟩
  simp [extract, idx]

/-- **Enlargement Theorem (Goldblatt §14.1, p. 185 & §14.3, pp. 188–189)**:
`universalUltrapowerEnlargement.{u}` is an **enlargement** (`IsEnlargement`), and hence by
Theorem 14.2.1 satisfies all three equivalent enlargement principles (`IsEnlargement`,
`EnlargementCondition`, and `HyperfiniteApproxProperty`) across the entire universe `Type u`! -/
theorem universalUltrapowerEnlargement_isEnlargement :
    (universalUltrapowerEnlargement.{u}).IsEnlargement ∧
    (universalUltrapowerEnlargement.{u}).EnlargementCondition ∧
    (universalUltrapowerEnlargement.{u}).HyperfiniteApproxProperty := by
  have hApprox := universalUltrapowerEnlargement_hyperfiniteApprox.{u}
  have hEnl := hyperfiniteApproxProperty_imp_isEnlargement hApprox
  have hConc := isEnlargement_imp_enlargementCondition hEnl
  exact ⟨hEnl, hConc, hApprox⟩

/-- Existence form of Goldblatt's **Enlargement Theorem** (p. 185):
For every universe `Type u`, there exists an ultrapower `NonstandardExtension.{u, u + 1}` that is
an enlargement (`IsEnlargement`)! -/
theorem exists_enlargement :
    ∃ E : NonstandardExtension.{u, u + 1}, E.IsEnlargement :=
  ⟨universalUltrapowerEnlargement.{u}, universalUltrapowerEnlargement_isEnlargement.1⟩

end Ch14

end Goldblatt
end

