import LecturesOnTheHyperreals.Ch12_InternalFunctions
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.OuterMeasure.Caratheodory
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Chapter 16: Loeb Measure

Complete formalization of Robert Goldblatt's *Lectures on the Hyperreals: An Introduction to
Nonstandard Analysis* (GTM 188), Chapter 16 (pp. 203–220):

* **§16.1 Rings and Algebras of Sets** (pp. 204–206):
  - `IsSetRing`, `IsSetAlgebra`, `algebraOfRing`, `IsSigmaRing`, `IsSigmaAlgebra`,
    `sigmaAlgebraGenerated`, closure laws (`∅`, `\`, `∪`, `∩`, `symmDiff`, finite unions and
    intersections, countable intersections, `disjointed`), minimal algebra over a ring, and
    equivalence with `MeasurableSpace.generateFrom`.
  - Examples 16.1(1)–(6): power set `𝒫(Ω)`, finite sets, finite-or-cofinite sets, countable sets,
    the ring `𝒞_ℝ` of finite unions of left-open intervals `(a, b]`, Borel `σ`-algebra `ℬ_ℝ`
    generated equivalently by `𝒞_ℝ`, open intervals, and open sets, and internal subset algebras
    `𝒫_I(S)` failing to be `σ`-algebras by Countable Saturation.
* **§16.2 Finitely Additive and Countably Additive Premeasures** (pp. 206–208):
  - `IsFinitelyAdditiveMeasure`, `IsCountablyAdditiveMeasure`, `IsMuFinite`, `IsMuNull`,
    `IsSigmaFiniteOn`.
  - Monotonicity, subtractivity `ν(B \ A) = ν(B) - ν(A)`, finite subadditivity, countable
    subadditivity on rings, continuity from below/above, equivalence of `σ`-additivity with
    continuity from below and (for finite premeasures) continuity from above at `∅`, and the
    counting measure example (`countingPremeasure`, `σ`-finite iff countable).
* **§16.3 Carathéodory / Hopf Outer Measure and Extension Theorem** (pp. 208–209):
  - `caratheodoryOuter` (`ν*(X) = ⨅ { ∑' n, ν(A_n) | A_n ∈ 𝒜, X ⊆ ⋃ n, A_n }`), outer measure
    laws, increasing-cover lemma, agreement `ν*(A) = ν(A)` on `𝒜` for `σ`-additive `ν`,
    Carathéodory measurability of all `A ∈ 𝒜`, completeness and `σ`-additivity of the extended
    measure `caratheodoryExtensionMeasure`, sandwich completeness, uniqueness on `S(𝒜)` under
    `σ`-finiteness, and the `𝒜_σ` / `𝒜_δ` approximation characterization when `ν(Ω) < ∞`.
* **§16.4 Lebesgue Measure Facts** (p. 210):
  - Uniqueness of Borel Lebesgue measure from open intervals (16.4(1)), Borel sandwich
    characterization of `NullMeasurableSet` (16.4(2)), and closed-inner / open-outer approximation
    criterion (16.4(3)).
* **§16.5–16.7 Internal Measure Rings/Algebras, Peter Loeb's Theorem, and Approximability**
  (pp. 207–215):
  - `InternalMeasureRing`, `InternalMeasureAlgebra`, `loebPremeasure` (`st ∘ μ` when limited, `⊤`
    when unlimited), **Peter Loeb's Theorem** (`loebPremeasure_isCountablyAdditive` and complete
    Loeb measure `loebMeasure`), single-set outer/inner formulas (**Lemmas 16.5.1 & 16.5.2**),
    `IsMuApproximable`, **Lemmas 16.6.1–16.6.4**, finite Loeb single-internal-set approximation and
    null-set characterization, **Theorem 16.7.1**, and concrete ultrapower / weighted hyperfinite
    instantiations (`mkInternalMeasureAlgebra`, `hyperfiniteWeightedAlgebra`).
* **§16.8–16.9 Lebesgue Measure on `[0, 1]` and `ℝ` via Hyperfinite Counting Loeb Measure**
  (pp. 215–220):
  - Unit interval hyperfinite grid `Ω = hyperStepPartition 0 (1/(n+1)) (n+1)` with `μ(A) = |A|/N`:
    `μ(Ω) = 1`, interval measures `b - a`, surjectivity of `st : Ω → [0, 1]`, pushforward equality
    with Lebesgue measure on `[0, 1]`, and `E ⊆ [0, 1]` is Lebesgue measurable iff `st⁻¹(E)` is
    Loeb measurable with `μ_L(st⁻¹(E)) = volume E`.
  - Full real line grid `S = {k/N : |k| ≤ N²}`: **Theorem 16.8.1** (interval slices `(a, b)`,
    `(a, b]`, `[a, b)`, `[a, b]` have Loeb measure `b - a`), `*ℚ` counterexample, externality yet
    Loeb measurability of `sh⁻¹(ℝ)`, **Lemma 16.8.3**, and **Theorem 16.8.2** (`B ⊆ ℝ` is Lebesgue
    measurable iff `sh⁻¹(B)` is Loeb measurable, with `volume B = μ_L(sh⁻¹(B))`).
-/

noncomputable section

namespace Goldblatt.Ch16

open Filter Function
open Hyperreal (ofSeq ofSeq_lt_ofSeq ofSeq_le_ofSeq ofSeq_surjective)
open scoped Topology Classical BigOperators ENNReal NNReal symmDiff MeasureTheory

/-! ## §16.1 Rings, Algebras, σ-Rings, and σ-Algebras of Sets -/

/-- Goldblatt §16.1 (p. 204): A **ring of sets** on `Ω` is a nonempty collection `𝒜` of subsets of
`Ω` closed under set differences and binary unions. -/
structure IsSetRing {Ω : Type*} (𝒜 : Set (Set Ω)) : Prop where
  /-- `𝒜` is nonempty. -/
  nonempty : 𝒜.Nonempty
  /-- Closure under set difference `A \ B`. -/
  sdiff_mem : ∀ ⦃A B : Set Ω⦄, A ∈ 𝒜 → B ∈ 𝒜 → A \ B ∈ 𝒜
  /-- Closure under binary union `A ∪ B`. -/
  union_mem : ∀ ⦃A B : Set Ω⦄, A ∈ 𝒜 → B ∈ 𝒜 → A ∪ B ∈ 𝒜

/-- Goldblatt §16.1 (p. 204): Any ring of sets contains `∅` (since `A \ A = ∅`). -/
theorem IsSetRing.empty_mem {Ω : Type*} {𝒜 : Set (Set Ω)} (h𝒜 : IsSetRing 𝒜) :
    (∅ : Set Ω) ∈ 𝒜 := by
  obtain ⟨A, hA⟩ := h𝒜.nonempty
  simpa using h𝒜.sdiff_mem hA hA

/-- Goldblatt §16.1 (p. 204): Any ring of sets is closed under symmetric difference
`A ∆ B = (A \ B) ∪ (B \ A)`. -/
theorem IsSetRing.symmDiff_mem {Ω : Type*} {𝒜 : Set (Set Ω)} (h𝒜 : IsSetRing 𝒜)
    {A B : Set Ω} (hA : A ∈ 𝒜) (hB : B ∈ 𝒜) :
    A ∆ B ∈ 𝒜 := by
  rw [Set.symmDiff_def]
  exact h𝒜.union_mem (h𝒜.sdiff_mem hA hB) (h𝒜.sdiff_mem hB hA)

/-- Goldblatt §16.1 (p. 204): Any ring of sets is closed under binary intersection
`A ∩ B = A \ (A \ B)`. -/
theorem IsSetRing.inter_mem {Ω : Type*} {𝒜 : Set (Set Ω)} (h𝒜 : IsSetRing 𝒜)
    {A B : Set Ω} (hA : A ∈ 𝒜) (hB : B ∈ 𝒜) :
    A ∩ B ∈ 𝒜 := by
  have heq : A ∩ B = A \ (A \ B) := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_sdiff]; tauto
  rw [heq]
  exact h𝒜.sdiff_mem hA (h𝒜.sdiff_mem hA hB)

/-- Goldblatt §16.1 (p. 204): A ring of sets is closed under finite unions indexed by a `Finset`. -/
theorem IsSetRing.biUnion_finset_mem {Ω ι : Type*} {𝒜 : Set (Set Ω)} (h𝒜 : IsSetRing 𝒜)
    (s : Finset ι) {f : ι → Set Ω} (hf : ∀ i ∈ s, f i ∈ 𝒜) :
    (⋃ i ∈ s, f i) ∈ 𝒜 := by
  induction s using Finset.cons_induction with
  | empty => simpa using h𝒜.empty_mem
  | cons a t hat ih =>
      have heq : (⋃ i ∈ Finset.cons a t hat, f i) = f a ∪ ⋃ i ∈ t, f i := by ext x; simp
      rw [heq]
      exact h𝒜.union_mem (hf a (Finset.mem_cons_self a t))
        (ih fun i hi ↦ hf i (Finset.mem_cons_of_mem hi))

/-- Goldblatt §16.1 (p. 204): A ring of sets is closed under nonempty finite intersections. -/
theorem IsSetRing.biInter_finset_mem {Ω ι : Type*} {𝒜 : Set (Set Ω)} (h𝒜 : IsSetRing 𝒜)
    {s : Finset ι} (hs : s.Nonempty) {f : ι → Set Ω} (hf : ∀ i ∈ s, f i ∈ 𝒜) :
    (⋂ i ∈ s, f i) ∈ 𝒜 := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hf a (Finset.mem_singleton_self a)
  | cons a t hat hne ih =>
      have heq : (⋂ i ∈ Finset.cons a t hat, f i) = f a ∩ ⋂ i ∈ t, f i := by ext x; simp
      rw [heq]
      exact h𝒜.inter_mem (hf a (Finset.mem_cons_self a t))
        (ih fun i hi ↦ hf i (Finset.mem_cons_of_mem hi))

/-- Disjointification of a sequence in a ring of sets remains in the ring. -/
theorem IsSetRing.disjointed_mem {Ω : Type*} {𝒜 : Set (Set Ω)} (h𝒜 : IsSetRing 𝒜)
    {A : ℕ → Set Ω} (hA : ∀ n, A n ∈ 𝒜) (n : ℕ) :
    disjointed A n ∈ 𝒜 := by
  rw [disjointed_eq_inter_compl]
  rcases n with _ | m
  · simpa using hA 0
  · have heq : (A (m + 1) ∩ ⋂ j < m + 1, (A j)ᶜ) =
        A (m + 1) \ (⋃ i ∈ Finset.range (m + 1), A i) := by
      ext x
      simp [Set.mem_sdiff, Finset.mem_range]
    rw [heq]
    exact h𝒜.sdiff_mem (hA (m + 1)) (h𝒜.biUnion_finset_mem _ fun i _ ↦ hA i)

/-- Goldblatt §16.1 (p. 204): An **algebra of sets** on `Ω` is a ring of sets containing `Ω`
(`Set.univ`). -/
structure IsSetAlgebra {Ω : Type*} (𝒜 : Set (Set Ω)) : Prop where
  /-- Underlying ring structure. -/
  toIsSetRing : IsSetRing 𝒜
  /-- Whole space belongs to `𝒜`. -/
  univ_mem : (Set.univ : Set Ω) ∈ 𝒜

/-- Goldblatt §16.1 (p. 204): Any algebra of sets is closed under complements `Aᶜ = Ω \ A`. -/
theorem IsSetAlgebra.compl_mem {Ω : Type*} {𝒜 : Set (Set Ω)} (h𝒜 : IsSetAlgebra 𝒜)
    {A : Set Ω} (hA : A ∈ 𝒜) :
    Aᶜ ∈ 𝒜 := by
  have heq : Aᶜ = Set.univ \ A := Set.compl_eq_univ_sdiff A
  rw [heq]
  exact h𝒜.toIsSetRing.sdiff_mem h𝒜.univ_mem hA

/-- Goldblatt §16.1 (p. 204): A ring of sets `𝒜` is an algebra if and only if `𝒜` is closed under
complements. -/
theorem isSetAlgebra_iff_compl {Ω : Type*} {𝒜 : Set (Set Ω)} :
    IsSetAlgebra 𝒜 ↔ IsSetRing 𝒜 ∧ ∀ ⦃A : Set Ω⦄, A ∈ 𝒜 → Aᶜ ∈ 𝒜 := by
  constructor
  · exact fun h ↦ ⟨h.toIsSetRing, fun _ hA ↦ h.compl_mem hA⟩
  · rintro ⟨hRing, hCompl⟩
    refine ⟨hRing, ?_⟩
    have h := hCompl hRing.empty_mem
    simpa using h

/-- Goldblatt §16.1 (p. 204): Given a ring `𝒜`, `𝒜 ∪ {Ω \ A : A ∈ 𝒜}` is the smallest algebra
including `𝒜`. -/
def algebraOfRing {Ω : Type*} (𝒜 : Set (Set Ω)) : Set (Set Ω) :=
  {A : Set Ω | A ∈ 𝒜 ∨ Aᶜ ∈ 𝒜}

/-- Goldblatt §16.1 (p. 204): If `𝒜` is a ring of sets, `algebraOfRing 𝒜` is an algebra of sets
including `𝒜`, and is minimal among all algebras of sets including `𝒜`. -/
theorem isSetAlgebra_algebraOfRing {Ω : Type*} {𝒜 : Set (Set Ω)} (h𝒜 : IsSetRing 𝒜) :
    IsSetAlgebra (algebraOfRing 𝒜) ∧
    𝒜 ⊆ algebraOfRing 𝒜 ∧
    ∀ ⦃ℬ : Set (Set Ω)⦄, IsSetAlgebra ℬ → 𝒜 ⊆ ℬ → algebraOfRing 𝒜 ⊆ ℬ := by
  have hCompl : ∀ ⦃A : Set Ω⦄, A ∈ algebraOfRing 𝒜 → Aᶜ ∈ algebraOfRing 𝒜 := by
    rintro A (hA | hAc)
    · exact Or.inr (by simpa using hA)
    · exact Or.inl hAc
  have hInter : ∀ ⦃A B : Set Ω⦄, A ∈ algebraOfRing 𝒜 → B ∈ algebraOfRing 𝒜 →
      A ∩ B ∈ algebraOfRing 𝒜 := by
    rintro A B (hA | hAc) (hB | hBc)
    · exact Or.inl (h𝒜.inter_mem hA hB)
    · have heq : A ∩ B = A \ Bᶜ := by ext x; simp
      rw [heq]
      exact Or.inl (h𝒜.sdiff_mem hA hBc)
    · have heq : A ∩ B = B \ Aᶜ := by ext x; simp [and_comm]
      rw [heq]
      exact Or.inl (h𝒜.sdiff_mem hB hAc)
    · right
      rw [Set.compl_inter]
      exact h𝒜.union_mem hAc hBc
  have hRing : IsSetRing (algebraOfRing 𝒜) :=
    { nonempty := ⟨∅, Or.inl h𝒜.empty_mem⟩
      sdiff_mem := fun A B hA hB ↦ by
        rw [Set.sdiff_eq]
        exact hInter hA (hCompl hB)
      union_mem := fun A B hA hB ↦ by
        have h := hCompl (hInter (hCompl hA) (hCompl hB))
        simpa [Set.compl_inter] using h }
  refine ⟨isSetAlgebra_iff_compl.2 ⟨hRing, hCompl⟩, fun A hA ↦ Or.inl hA, fun ℬ hℬ hsub A hA ↦ ?_⟩
  rcases hA with hA | hAc
  · exact hsub hA
  · simpa using hℬ.compl_mem (hsub hAc)

/-- Goldblatt §16.1 (p. 204): A **σ-ring of sets** is a ring of sets closed under countable
unions. -/
structure IsSigmaRing {Ω : Type*} (𝒜 : Set (Set Ω)) : Prop where
  /-- Underlying ring structure. -/
  toIsSetRing : IsSetRing 𝒜
  /-- Closure under countable unions. -/
  iUnion_mem : ∀ ⦃f : ℕ → Set Ω⦄, (∀ n, f n ∈ 𝒜) → (⋃ n, f n) ∈ 𝒜

/-- Goldblatt §16.1 (p. 204): Every σ-ring is closed under countable intersections, since
`⋂ n, A_n = A_0 \ ⋃ n, (A_0 \ A_n)`. -/
theorem IsSigmaRing.iInter_mem {Ω : Type*} {𝒜 : Set (Set Ω)} (h𝒜 : IsSigmaRing 𝒜)
    {f : ℕ → Set Ω} (hf : ∀ n, f n ∈ 𝒜) :
    (⋂ n, f n) ∈ 𝒜 := by
  have heq : (⋂ n, f n) = f 0 \ (⋃ n, (f 0 \ f n)) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_sdiff, Set.mem_iUnion, not_exists, not_and, Classical.not_not]
    exact ⟨fun h ↦ ⟨h 0, fun n _ ↦ h n⟩, fun ⟨h0, h⟩ n ↦ h n h0⟩
  rw [heq]
  exact h𝒜.toIsSetRing.sdiff_mem (hf 0) (h𝒜.iUnion_mem fun n ↦ h𝒜.toIsSetRing.sdiff_mem (hf 0) (hf n))

/-- Goldblatt §16.1 (p. 204): A **σ-algebra of sets** is a σ-ring of sets that is also an algebra
(`Set.univ ∈ 𝒜`). -/
structure IsSigmaAlgebra {Ω : Type*} (𝒜 : Set (Set Ω)) : Prop where
  /-- Underlying σ-ring structure. -/
  toIsSigmaRing : IsSigmaRing 𝒜
  /-- Whole space belongs to `𝒜`. -/
  univ_mem : (Set.univ : Set Ω) ∈ 𝒜

/-- Every σ-algebra is an algebra of sets. -/
theorem IsSigmaAlgebra.toIsSetAlgebra {Ω : Type*} {𝒜 : Set (Set Ω)} (h𝒜 : IsSigmaAlgebra 𝒜) :
    IsSetAlgebra 𝒜 :=
  ⟨h𝒜.toIsSigmaRing.toIsSetRing, h𝒜.univ_mem⟩

/-- Goldblatt §16.1 (p. 204): The intersection `⋂₀ ℱ` of any family `ℱ` of σ-algebras on `Ω` is a
σ-algebra on `Ω`. -/
theorem isSigmaAlgebra_sInter {Ω : Type*} {ℱ : Set (Set (Set Ω))}
    (hℱ : ∀ ℬ ∈ ℱ, IsSigmaAlgebra ℬ) :
    IsSigmaAlgebra (⋂₀ ℱ) := by
  refine ⟨⟨⟨⟨∅, fun ℬ hℬ ↦ (hℱ ℬ hℬ).toIsSigmaRing.toIsSetRing.empty_mem⟩,
    fun A B hA hB ℬ hℬ ↦ (hℱ ℬ hℬ).toIsSigmaRing.toIsSetRing.sdiff_mem (hA ℬ hℬ) (hB ℬ hℬ),
    fun A B hA hB ℬ hℬ ↦ (hℱ ℬ hℬ).toIsSigmaRing.toIsSetRing.union_mem (hA ℬ hℬ) (hB ℬ hℬ)⟩,
    fun f hf ℬ hℬ ↦ (hℱ ℬ hℬ).toIsSigmaRing.iUnion_mem fun n ↦ hf n ℬ hℬ⟩,
    fun ℬ hℬ ↦ (hℱ ℬ hℬ).univ_mem⟩

/-- Goldblatt §16.1 Example (1) (p. 204): The power set `𝒫(Ω)` (`Set.univ : Set (Set Ω)`) is a
σ-algebra. -/
theorem isSigmaAlgebra_univ (Ω : Type*) : IsSigmaAlgebra (Set.univ : Set (Set Ω)) :=
  ⟨⟨⟨⟨∅, trivial⟩, fun _ _ _ _ ↦ trivial, fun _ _ _ _ ↦ trivial⟩, fun _ _ ↦ trivial⟩, trivial⟩

/-- Goldblatt §16.1 (p. 204): The **σ-algebra `S(𝒜)` generated by `𝒜`**, defined as the
intersection of all σ-algebras on `Ω` including `𝒜`. -/
def sigmaAlgebraGenerated {Ω : Type*} (𝒜 : Set (Set Ω)) : Set (Set Ω) :=
  ⋂₀ {ℬ : Set (Set Ω) | IsSigmaAlgebra ℬ ∧ 𝒜 ⊆ ℬ}

/-- Goldblatt §16.1 (p. 204): `sigmaAlgebraGenerated 𝒜` is the smallest σ-algebra including `𝒜`,
and coincides exactly with `MeasurableSpace.generateFrom 𝒜`. -/
theorem isSigmaAlgebra_sigmaAlgebraGenerated {Ω : Type*} (𝒜 : Set (Set Ω)) :
    IsSigmaAlgebra (sigmaAlgebraGenerated 𝒜) ∧
    𝒜 ⊆ sigmaAlgebraGenerated 𝒜 ∧
    (∀ ⦃ℬ : Set (Set Ω)⦄, IsSigmaAlgebra ℬ → 𝒜 ⊆ ℬ → sigmaAlgebraGenerated 𝒜 ⊆ ℬ) ∧
    ∀ A : Set Ω, A ∈ sigmaAlgebraGenerated 𝒜 ↔
      @MeasurableSet Ω (MeasurableSpace.generateFrom 𝒜) A := by
  have hSig : IsSigmaAlgebra (sigmaAlgebraGenerated 𝒜) :=
    isSigmaAlgebra_sInter fun _ h ↦ h.1
  have hSub : 𝒜 ⊆ sigmaAlgebraGenerated 𝒜 := fun A hA _ hℬ ↦ hℬ.2 hA
  have hMin : ∀ ⦃ℬ : Set (Set Ω)⦄, IsSigmaAlgebra ℬ → 𝒜 ⊆ ℬ → sigmaAlgebraGenerated 𝒜 ⊆ ℬ :=
    fun ℬ h1 h2 A hA ↦ hA ℬ ⟨h1, h2⟩
  refine ⟨hSig, hSub, hMin, fun A ↦ ⟨?_, ?_⟩⟩
  · let ℬ : Set (Set Ω) := {X : Set Ω | @MeasurableSet Ω (MeasurableSpace.generateFrom 𝒜) X}
    have hℬ_sig : IsSigmaAlgebra ℬ :=
      ⟨⟨⟨⟨∅, @MeasurableSet.empty Ω (MeasurableSpace.generateFrom 𝒜)⟩,
         fun X Y hX hY ↦ @MeasurableSet.diff Ω (MeasurableSpace.generateFrom 𝒜) X Y hX hY,
         fun X Y hX hY ↦ @MeasurableSet.union Ω (MeasurableSpace.generateFrom 𝒜) X Y hX hY⟩,
        fun f hf ↦ @MeasurableSet.iUnion Ω ℕ (MeasurableSpace.generateFrom 𝒜) _ f hf⟩,
       @MeasurableSet.univ Ω (MeasurableSpace.generateFrom 𝒜)⟩
    have h𝒜_ℬ : 𝒜 ⊆ ℬ := fun X hX ↦ MeasurableSpace.measurableSet_generateFrom hX
    exact fun hA ↦ hMin hℬ_sig h𝒜_ℬ hA
  · intro hMeas
    induction hMeas with
    | basic u hu => exact hSub hu
    | empty => exact hSig.toIsSigmaRing.toIsSetRing.empty_mem
    | compl t _ ih => exact hSig.toIsSetAlgebra.compl_mem ih
    | iUnion f _ ih => exact hSig.toIsSigmaRing.iUnion_mem ih

/-- Goldblatt §16.1 Example (2a) (p. 204): On an infinite type `Ω`, `{A : Set Ω | A.Finite}` is a
ring of sets that is not an algebra. -/
theorem isSetRing_and_not_algebra_finite {Ω : Type*} [Infinite Ω] :
    IsSetRing {A : Set Ω | A.Finite} ∧ ¬ IsSetAlgebra {A : Set Ω | A.Finite} := by
  refine ⟨⟨⟨∅, Set.finite_empty⟩,
    fun A B hA _ ↦ hA.subset Set.sdiff_subset,
    fun A B hA hB ↦ hA.union hB⟩, ?_⟩
  intro hAlg
  exact Set.infinite_univ hAlg.univ_mem

/-- Goldblatt §16.1 Example (2b) (p. 204): On an infinite type `Ω`, the collection of finite or
cofinite subsets `{A : Set Ω | A.Finite ∨ Aᶜ.Finite}` is an algebra of sets that is not a
σ-algebra. -/
theorem isSetAlgebra_and_not_sigmaAlgebra_finite_cofinite {Ω : Type*} [Infinite Ω] :
    IsSetAlgebra {A : Set Ω | A.Finite ∨ Aᶜ.Finite} ∧
    ¬ IsSigmaAlgebra {A : Set Ω | A.Finite ∨ Aᶜ.Finite} := by
  have hFinRing : IsSetRing {A : Set Ω | A.Finite} :=
    ⟨⟨∅, Set.finite_empty⟩, fun _ _ hA _ ↦ hA.subset Set.sdiff_subset, fun _ _ hA hB ↦ hA.union hB⟩
  have hAlg : IsSetAlgebra {A : Set Ω | A.Finite ∨ Aᶜ.Finite} :=
    (isSetAlgebra_algebraOfRing hFinRing).1
  refine ⟨hAlg, fun hSig ↦ ?_⟩
  let e : ℕ ↪ Ω := Infinite.natEmbedding Ω
  let f : ℕ → Set Ω := fun n ↦ {e (2 * n)}
  have hf : ∀ n, f n ∈ {A : Set Ω | A.Finite ∨ Aᶜ.Finite} :=
    fun n ↦ Or.inl (Set.finite_singleton _)
  have hU := hSig.toIsSigmaRing.iUnion_mem hf
  rcases hU with hU_fin | hU_cofin
  · have hInf : (⋃ n, f n).Infinite :=
      Set.infinite_of_injective_forall_mem
        (f := fun n : ℕ ↦ e (2 * n))
        (fun m n hmn ↦ by have := e.injective hmn; omega)
        (fun n ↦ Set.mem_iUnion.2 ⟨n, rfl⟩)
    exact hInf hU_fin
  · have hInfCompl : ((⋃ n, f n)ᶜ).Infinite :=
      Set.infinite_of_injective_forall_mem
        (f := fun n : ℕ ↦ e (2 * n + 1))
        (fun m n hmn ↦ by have := e.injective hmn; omega)
        (fun n hmem ↦ by
          obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hmem
          have := e.injective hm.symm
          omega)
    exact hInfCompl hU_cofin

/-- Goldblatt §16.1 Example (2c) (p. 204): The collection `{A : Set Ω | A.Countable}` is a σ-ring,
and is not an algebra when `Ω` is uncountable (`¬ (Set.univ : Set Ω).Countable`). -/
theorem isSigmaRing_countable_and_not_algebra {Ω : Type*}
    (hUnc : ¬ (Set.univ : Set Ω).Countable) :
    IsSigmaRing {A : Set Ω | A.Countable} ∧ ¬ IsSetAlgebra {A : Set Ω | A.Countable} := by
  refine ⟨⟨⟨⟨∅, Set.countable_empty⟩,
    fun _ _ hA _ ↦ hA.mono Set.sdiff_subset,
    fun _ _ hA hB ↦ hA.union hB⟩,
    fun f hf ↦ Set.countable_iUnion hf⟩,
    fun hAlg ↦ hUnc hAlg.univ_mem⟩

/-- Goldblatt §16.1 Example (3) (p. 204): The collection `𝒞_ℝ` of subsets of `ℝ` that are finite
unions of left-open intervals `(a, b] = Set.Ioc a b`. -/
def leftOpenRing : Set (Set ℝ) :=
  {X : Set ℝ | ∃ s : Finset (ℝ × ℝ), X = ⋃ p ∈ s, Set.Ioc p.1 p.2}

/-- Helper: intersection of two left-open intervals is a left-open interval. -/
theorem Ioc_inter_Ioc_eq (a b c d : ℝ) :
    Set.Ioc a b ∩ Set.Ioc c d = Set.Ioc (max a c) (min b d) :=
  Set.Ioc_inter_Ioc

/-- Helper: set difference of two left-open intervals is a union of two left-open intervals. -/
theorem Ioc_sdiff_Ioc_eq (a b c d : ℝ) :
    Set.Ioc a b \ Set.Ioc c d = Set.Ioc a (min b c) ∪ Set.Ioc (max a d) b := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_Ioc, Set.mem_union, le_min_iff, max_lt_iff]
  constructor
  · rintro ⟨⟨hax, hxb⟩, hnot⟩
    by_cases hxc : x ≤ c
    · exact Or.inl ⟨hax, hxb, hxc⟩
    · push Not at hxc
      have hdx : d < x := by
        by_contra hxd
        push Not at hxd
        exact hnot ⟨hxc, hxd⟩
      exact Or.inr ⟨⟨hax, hdx⟩, hxb⟩
  · rintro (⟨hax, hxb, hxc⟩ | ⟨⟨hax, hdx⟩, hxb⟩)
    · exact ⟨⟨hax, hxb⟩, fun ⟨hcx, _⟩ ↦ not_lt_of_ge hxc hcx⟩
    · exact ⟨⟨hax, hxb⟩, fun ⟨_, hxd⟩ ↦ not_lt_of_ge hxd hdx⟩

/-- Goldblatt §16.1 Example (3) (pp. 204–205): `leftOpenRing` (`𝒞_ℝ`) is a ring of sets, is NOT an
algebra, does not contain `(0, 1)` (since every nonempty member of `𝒞_ℝ` has a greatest element),
yet contains `(0, 1] = ⋃ n : ℕ, (1/(n+2), 1/(n+1)]`. -/
theorem leftOpenRing_properties :
    IsSetRing leftOpenRing ∧
    ¬ IsSetAlgebra leftOpenRing ∧
    Set.Ioo (0 : ℝ) 1 ∉ leftOpenRing ∧
    Set.Ioc (0 : ℝ) 1 ∈ leftOpenRing ∧
    Set.Ioc (0 : ℝ) 1 = ⋃ n : ℕ, Set.Ioc (1 / ((n + 2 : ℕ) : ℝ)) (1 / ((n + 1 : ℕ) : ℝ)) := by
  have hUnion : ∀ ⦃A B : Set ℝ⦄, A ∈ leftOpenRing → B ∈ leftOpenRing → A ∪ B ∈ leftOpenRing := by
    rintro A B ⟨s, rfl⟩ ⟨t, rfl⟩
    refine ⟨s ∪ t, ?_⟩
    ext x
    simp only [Set.mem_iUnion₂, Finset.mem_union, Set.mem_union]
    aesop
  have hEmpty : (∅ : Set ℝ) ∈ leftOpenRing := ⟨∅, by simp⟩
  have hSingle : ∀ a b : ℝ, Set.Ioc a b ∈ leftOpenRing :=
    fun a b ↦ ⟨{(a, b)}, by simp⟩
  -- Helper: `A \ Ioc c d ∈ leftOpenRing` for `A ∈ leftOpenRing`.
  have hSdiffSingle : ∀ ⦃A : Set ℝ⦄, A ∈ leftOpenRing → ∀ c d : ℝ,
      A \ Set.Ioc c d ∈ leftOpenRing := by
    rintro A ⟨s, rfl⟩ c d
    induction s using Finset.cons_induction with
    | empty => simpa using hEmpty
    | cons p t hpt ih =>
        have heq : (⋃ q ∈ Finset.cons p t hpt, Set.Ioc q.1 q.2) \ Set.Ioc c d =
            (Set.Ioc p.1 p.2 \ Set.Ioc c d) ∪ ((⋃ q ∈ t, Set.Ioc q.1 q.2) \ Set.Ioc c d) := by
          ext x
          simp only [Finset.mem_cons, Set.mem_sdiff, Set.mem_iUnion₂, Set.mem_union]
          aesop
        rw [heq, Ioc_sdiff_Ioc_eq]
        exact hUnion (hUnion (hSingle _ _) (hSingle _ _)) ih
  have hSdiff : ∀ ⦃A B : Set ℝ⦄, A ∈ leftOpenRing → B ∈ leftOpenRing → A \ B ∈ leftOpenRing := by
    rintro A B hA ⟨t, rfl⟩
    induction t using Finset.cons_induction generalizing A with
    | empty => simpa using hA
    | cons p u hpu ih =>
        have heq : A \ (⋃ q ∈ Finset.cons p u hpu, Set.Ioc q.1 q.2) =
            (A \ Set.Ioc p.1 p.2) \ (⋃ q ∈ u, Set.Ioc q.1 q.2) := by
          ext x
          simp only [Finset.mem_cons, Set.mem_sdiff, Set.mem_iUnion₂]
          aesop
        rw [heq]
        exact ih (hSdiffSingle hA p.1 p.2)
  have hRing : IsSetRing leftOpenRing := ⟨⟨∅, hEmpty⟩, hSdiff, hUnion⟩
  -- Every member of `leftOpenRing` is bounded above; every nonempty member has a greatest element.
  have hMax : ∀ ⦃X : Set ℝ⦄, X ∈ leftOpenRing → X.Nonempty → ∃ m ∈ X, ∀ x ∈ X, x ≤ m := by
    rintro X ⟨s, rfl⟩ hne
    let s' := s.filter (fun p ↦ p.1 < p.2)
    have hs'_ne : s'.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      obtain ⟨p, hp, hpx⟩ := Set.mem_iUnion₂.1 hx
      exact ⟨p, Finset.mem_filter.2 ⟨hp, hpx.1.trans_le hpx.2⟩⟩
    let m : ℝ := (s'.image Prod.snd).max' (hs'_ne.image Prod.snd)
    obtain ⟨p₀, hp₀, hp₀eq⟩ :=
      Finset.mem_image.1 (Finset.max'_mem (s'.image Prod.snd) (hs'_ne.image Prod.snd))
    obtain ⟨hp₀s, hp₀lt⟩ := Finset.mem_filter.1 hp₀
    refine ⟨p₀.2, Set.mem_iUnion₂.2 ⟨p₀, hp₀s, hp₀lt, le_rfl⟩, fun x hx ↦ ?_⟩
    obtain ⟨q, hqs, hqx⟩ := Set.mem_iUnion₂.1 hx
    have hqs' : q ∈ s' := Finset.mem_filter.2 ⟨hqs, hqx.1.trans_le hqx.2⟩
    have hq_le : q.2 ≤ m := Finset.le_max' _ q.2 (Finset.mem_image.2 ⟨q, hqs', rfl⟩)
    exact hqx.2.trans (hp₀eq.symm ▸ hq_le)
  refine ⟨hRing, ?_, ?_, hSingle 0 1, ?_⟩
  · intro hAlg
    obtain ⟨m, _, hm⟩ := hMax hAlg.univ_mem ⟨0, trivial⟩
    linarith [hm (m + 1) trivial]
  · intro hIoo
    obtain ⟨m, hmIoo, hm⟩ := hMax hIoo ⟨1 / 2, by norm_num⟩
    have hmid : (m + 1) / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hmIoo.1], by linarith [hmIoo.2]⟩
    linarith [hm ((m + 1) / 2) hmid, hmIoo.2]
  · ext x
    simp only [Set.mem_Ioc, Set.mem_iUnion]
    constructor
    · rintro ⟨hx0, hx1⟩
      -- Pick `n` such that `1 / (n + 2) < x` and take the least such `n`.
      have hex : ∃ n : ℕ, 1 / ((n + 2 : ℕ) : ℝ) < x := by
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hx0
        refine ⟨k, lt_of_le_of_lt ?_ hk⟩
        exact one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
      let n₀ : ℕ := Nat.find hex
      refine ⟨n₀, Nat.find_spec hex, ?_⟩
      rcases eq_or_lt_of_le (Nat.zero_le n₀) with hn0 | hn_pos
      · rw [← hn0]
        simpa using hx1
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn_pos.ne'
        have hnot := Nat.find_min hex (hk ▸ Nat.lt_succ_self k)
        push Not at hnot
        rw [hk]
        exact hnot
    · rintro ⟨n, h1, h2⟩
      have hpos : (0 : ℝ) < 1 / ((n + 2 : ℕ) : ℝ) := by positivity
      have hle1 : 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]
        push_cast; linarith
      exact ⟨hpos.trans h1, h2.trans hle1⟩

/-- Goldblatt §16.1 Example (4) (p. 205): The σ-algebra generated by `leftOpenRing` (`𝒞_ℝ`), the
σ-algebra generated by open intervals `{Set.Ioo a b | a b : ℝ}`, and the σ-algebra generated by
open subsets of `ℝ` all coincide with the Borel sets `{B : Set ℝ | MeasurableSet B}`. -/
theorem sigmaAlgebraGenerated_leftOpenRing_eq_borel :
    sigmaAlgebraGenerated leftOpenRing = {B : Set ℝ | MeasurableSet B} ∧
    sigmaAlgebraGenerated {U : Set ℝ | ∃ a b : ℝ, U = Set.Ioo a b} =
      {B : Set ℝ | MeasurableSet B} ∧
    sigmaAlgebraGenerated {U : Set ℝ | IsOpen U} = {B : Set ℝ | MeasurableSet B} := by
  let borelSet : Set (Set ℝ) := {B : Set ℝ | MeasurableSet B}
  have hBorelSig : IsSigmaAlgebra borelSet :=
    ⟨⟨⟨⟨∅, (MeasurableSet.empty : MeasurableSet (∅ : Set ℝ))⟩,
       fun A B (hA : MeasurableSet A) (hB : MeasurableSet B) ↦ hA.diff hB,
       fun A B (hA : MeasurableSet A) (hB : MeasurableSet B) ↦ hA.union hB⟩,
      fun f (hf : ∀ n, MeasurableSet (f n)) ↦ MeasurableSet.iUnion hf⟩,
     (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ))⟩
  have hGenOpen : sigmaAlgebraGenerated {U : Set ℝ | IsOpen U} = {B : Set ℝ | MeasurableSet B} := by
    ext B
    rw [(isSigmaAlgebra_sigmaAlgebraGenerated _).2.2.2 B]
    rfl
  -- Open intervals generate all open sets (via rational endpoints), hence Borel sets.
  have hIoo_sub_leftOpen : {U : Set ℝ | ∃ a b : ℝ, U = Set.Ioo a b} ⊆
      sigmaAlgebraGenerated leftOpenRing := by
    rintro _ ⟨a, b, rfl⟩
    have heq : Set.Ioo a b = ⋃ n : ℕ, Set.Ioc a (b - 1 / ((n : ℝ) + 1)) := by
      ext x
      simp only [Set.mem_Ioo, Set.mem_iUnion, Set.mem_Ioc]
      constructor
      · rintro ⟨hax, hxb⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hxb)
        exact ⟨n, hax, by linarith⟩
      · rintro ⟨n, hax, hxn⟩
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        exact ⟨hax, by linarith⟩
    rw [heq]
    exact (isSigmaAlgebra_sigmaAlgebraGenerated leftOpenRing).1.toIsSigmaRing.iUnion_mem fun n ↦
      (isSigmaAlgebra_sigmaAlgebraGenerated leftOpenRing).2.1
        ⟨{(a, b - 1 / ((n : ℝ) + 1))}, by simp⟩
  have hOpen_sub_Ioo : {U : Set ℝ | IsOpen U} ⊆
      sigmaAlgebraGenerated {U : Set ℝ | ∃ a b : ℝ, U = Set.Ioo a b} := by
    intro U (hU : IsOpen U)
    rw [(isSigmaAlgebra_sigmaAlgebraGenerated _).2.2.2 U]
    have hgen : MeasurableSpace.generateFrom {V : Set ℝ | ∃ a b : ℝ, V = Set.Ioo a b} = borel ℝ := by
      apply le_antisymm
      · exact MeasurableSpace.generateFrom_le fun V ⟨a, b, hV⟩ ↦ hV ▸ isOpen_Ioo.measurableSet
      · rw [Real.borel_eq_generateFrom_Ioo_rat]
        refine MeasurableSpace.generateFrom_le fun V hV ↦ ?_
        simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hV
        obtain ⟨p, q, _, rfl⟩ := hV
        exact MeasurableSpace.measurableSet_generateFrom ⟨p, q, rfl⟩
    rw [hgen]
    exact hU.measurableSet
  have hGenIoo : sigmaAlgebraGenerated {U : Set ℝ | ∃ a b : ℝ, U = Set.Ioo a b} =
      {B : Set ℝ | MeasurableSet B} := by
    apply Set.Subset.antisymm
    · exact (isSigmaAlgebra_sigmaAlgebraGenerated _).2.2.1 hBorelSig
        (fun _ ⟨a, b, h⟩ ↦ Set.mem_ofPred_eq.mpr (h ▸ isOpen_Ioo.measurableSet))
    · rw [← hGenOpen]
      exact (isSigmaAlgebra_sigmaAlgebraGenerated _).2.2.1
        (isSigmaAlgebra_sigmaAlgebraGenerated _).1 hOpen_sub_Ioo
  have hLeftOpen_sub_Borel : leftOpenRing ⊆ {B : Set ℝ | MeasurableSet B} := by
    rintro _ ⟨s, rfl⟩
    exact Set.mem_ofPred_eq.mpr (Finset.measurableSet_biUnion s fun p _ ↦ measurableSet_Ioc)
  refine ⟨Set.Subset.antisymm
    ((isSigmaAlgebra_sigmaAlgebraGenerated _).2.2.1 hBorelSig hLeftOpen_sub_Borel)
    (by
      rw [← hGenIoo]
      exact (isSigmaAlgebra_sigmaAlgebraGenerated _).2.2.1
        (isSigmaAlgebra_sigmaAlgebraGenerated _).1 hIoo_sub_leftOpen),
    hGenIoo, hGenOpen⟩

/-- Goldblatt §16.1 Examples (5)–(6) (pp. 205–206): For any internal set `S ⊆ ℝ*`, `𝒫_I(S)` is the
collection of all subsets of `↥S` whose image in `ℝ*` is internal. -/
def internalSubsetAlgebra (S : Set ℝ*) : Set (Set ↥S) :=
  {A : Set ↥S | IsInternal ((Subtype.val : ↥S → ℝ*) '' A)}

/-- Goldblatt §16.1 Examples (5)–(6) (pp. 205–206): Whenever `S ⊆ ℝ*` is internal, `𝒫_I(S)` is an
algebra of subsets of `↥S`, and satisfies **Countable Saturation for unions**: any countable union
of members of `𝒫_I(S)` that belongs to `𝒫_I(S)` equals a finite subunion! -/
theorem isSetAlgebra_internalSubsetAlgebra {S : Set ℝ*} (hS : IsInternal S) :
    IsSetAlgebra (internalSubsetAlgebra S) ∧
    ∀ ⦃A : ℕ → Set ↥S⦄, (∀ n, A n ∈ internalSubsetAlgebra S) →
      (⋃ n, A n) ∈ internalSubsetAlgebra S →
      ∃ k : ℕ, (⋃ n, A n) = ⋃ n ≤ k, A n := by
  have hRing : IsSetRing (internalSubsetAlgebra S) :=
    { nonempty := ⟨∅, by
        change IsInternal ((Subtype.val : ↥S → ℝ*) '' ∅)
        simpa using isInternal_empty⟩
      sdiff_mem := fun A B hA hB ↦ by
        change IsInternal ((Subtype.val : ↥S → ℝ*) '' (A \ B))
        rw [Set.image_sdiff Subtype.val_injective]
        exact hA.sdiff hB
      union_mem := fun A B hA hB ↦ by
        change IsInternal ((Subtype.val : ↥S → ℝ*) '' (A ∪ B))
        rw [Set.image_union]
        exact hA.union hB }
  have hUniv : (Set.univ : Set ↥S) ∈ internalSubsetAlgebra S := by
    change IsInternal ((Subtype.val : ↥S → ℝ*) '' Set.univ)
    simpa [Subtype.range_coe] using hS
  refine ⟨⟨hRing, hUniv⟩, fun A hA hU ↦ ?_⟩
  have hU_img : IsInternal (⋃ n, (Subtype.val : ↥S → ℝ*) '' A n) := by
    rwa [← Set.image_iUnion]
  obtain ⟨k, hk⟩ := isInternal_iUnion_implies_finite hA hU_img
  refine ⟨k, Set.image_injective.2 Subtype.val_injective ?_⟩
  rw [Set.image_iUnion, hk]
  ext x
  simp

/-- Goldblatt §16.1 Example (5) (p. 205): For any unlimited `N ∈ ℕ*`, `S = {1, …, N}`
(`hyperIccOne N`) is hyperfinite, `𝒫_I(S)` is an algebra containing each `{1, …, n}` (`n ∈ ℕ`),
yet `𝒫_I(S)` is NOT a σ-algebra because `⋃ n : ℕ, {1, …, n}` is the external set `ℕ_{≥ 1}`! -/
theorem not_isSigmaAlgebra_internalSubsetAlgebra_hyperIccOne {N : ℕ*} (hN : IsUnlimitedNat N) :
    IsSetAlgebra (internalSubsetAlgebra (hyperIccOne N)) ∧
    ¬ IsSigmaAlgebra (internalSubsetAlgebra (hyperIccOne N)) := by
  let S := hyperIccOne N
  have hS : IsInternal S := (hasHypercard_Icc_one N).isHyperfinite.isInternal
  refine ⟨(isSetAlgebra_internalSubsetAlgebra hS).1, fun hSig ↦ ?_⟩
  let A : ℕ → Set ↥S := fun n ↦ (Subtype.val : ↥S → ℝ*) ⁻¹' hyperIccOne ((n + 1 : ℕ) : ℕ*)
  have hA_sub : ∀ n : ℕ, hyperIccOne ((n + 1 : ℕ) : ℕ*) ⊆ S := by
    rintro n _ ⟨K, ⟨h1K, hKn⟩, rfl⟩
    exact ⟨K, ⟨h1K, hKn.trans (hN (n + 1)).le⟩, rfl⟩
  have hA_mem : ∀ n : ℕ, A n ∈ internalSubsetAlgebra S := by
    intro n
    change IsInternal ((Subtype.val : ↥S → ℝ*) '' A n)
    rw [Subtype.image_preimage_coe, Set.inter_eq_right.2 (hA_sub n)]
    exact (hasHypercard_Icc_one _).isHyperfinite.isInternal
  have hU_mem := hSig.toIsSigmaRing.iUnion_mem hA_mem
  obtain ⟨k, hk⟩ := (isSetAlgebra_internalSubsetAlgebra hS).2 hA_mem hU_mem
  have hm_sub : ((k + 2 : ℕ) : ℝ*) ∈ S :=
    ⟨((k + 2 : ℕ) : ℕ*), ⟨by exact_mod_cast (show 1 ≤ k + 2 by omega), (hN (k + 2)).le⟩,
      Hypernat.toHyperreal_natCast (k + 2)⟩
  let x : ↥S := ⟨((k + 2 : ℕ) : ℝ*), hm_sub⟩
  have hx_in : x ∈ ⋃ n, A n :=
    Set.mem_iUnion.2 ⟨k + 1, ⟨((k + 2 : ℕ) : ℕ*),
      ⟨by exact_mod_cast (show 1 ≤ k + 2 by omega), le_rfl⟩,
      Hypernat.toHyperreal_natCast (k + 2)⟩⟩
  rw [hk] at hx_in
  obtain ⟨n, hnk, hxn⟩ := Set.mem_iUnion₂.1 hx_in
  obtain ⟨K, ⟨_, hKn⟩, hKeq⟩ := hxn
  change K.toHyperreal = ((k + 2 : ℕ) : ℝ*) at hKeq
  rw [← Hypernat.toHyperreal_natCast (k + 2)] at hKeq
  have hK : K = ((k + 2 : ℕ) : ℕ*) := Hypernat.toHyperreal_injective hKeq
  subst hK
  have hle_hr : ((k + 2 : ℕ) : ℝ*) ≤ ((n + 1 : ℕ) : ℝ*) := by
    rw [← Hypernat.toHyperreal_natCast (k + 2), ← Hypernat.toHyperreal_natCast (n + 1)]
    exact Hypernat.toHyperreal_le_iff.2 hKn
  have hle : k + 2 ≤ n + 1 := by exact_mod_cast hle_hr
  omega

/-- Goldblatt §16.1 Example (6) (p. 205): The internal intervals `*(-(n+1), n+1)` belong to `*ℬ_ℝ`
(and are internal), whereas their union `⋃ n : ℕ, *(-(n+1), n+1)` is the external set `𝕃` of all
limited hyperreals. -/
theorem iUnion_starSet_Ioo_eq_limited_and_external :
    (⋃ n : ℕ, starSet (Set.Ioo (-((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ))) =
      {x : ℝ* | IsLimited x} ∧
    IsExternal (⋃ n : ℕ, starSet (Set.Ioo (-((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ))) := by
  have heq : (⋃ n : ℕ, starSet (Set.Ioo (-((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ))) =
      {x : ℝ* | IsLimited x} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hxn⟩
      rcases ofSeq_surjective x with ⟨r, rfl⟩
      rw [ofSeq_mem_starSet] at hxn
      have h1 : -(((n + 1 : ℕ) : ℝ) : ℝ*) < ofSeq r :=
        ofSeq_lt_ofSeq.2 (hxn.mono fun i hi ↦ hi.1)
      have h2 : ofSeq r < (((n + 1 : ℕ) : ℝ) : ℝ*) :=
        ofSeq_lt_ofSeq.2 (hxn.mono fun i hi ↦ hi.2)
      exact ⟨n + 1, abs_lt.2 ⟨by simpa using h1, by simpa using h2⟩⟩
    · rintro ⟨n, hxn⟩
      rcases ofSeq_surjective x with ⟨r, rfl⟩
      refine ⟨n, ?_⟩
      rw [ofSeq_mem_starSet]
      have hlt : |ofSeq r| < (((n + 1 : ℕ) : ℝ) : ℝ*) :=
        hxn.trans (by exact_mod_cast Nat.lt_succ_self n)
      obtain ⟨hl, hr⟩ := abs_lt.1 hlt
      exact ((ofSeq_lt_ofSeq.1 hl).and (ofSeq_lt_ofSeq.1 hr)).mono fun i hi ↦ hi
  refine ⟨heq, fun hInt ↦ ?_⟩
  rw [heq] at hInt
  obtain ⟨B, _, hB⟩ := hInt.subset_Icc_real_of_forall_isLimited fun _ hx ↦ hx
  obtain ⟨m, hm⟩ := exists_nat_gt B
  have hm_lim : IsLimited ((m : ℝ) : ℝ*) := isLimited_coe m
  have hle : ((m : ℝ) : ℝ*) ≤ (B : ℝ*) := (hB hm_lim).2
  exact not_lt_of_ge (Hyperreal.coe_le_coe.1 hle) hm

/-! ## §16.2 Finitely Additive and Countably Additive Premeasures -/

/-- Goldblatt §16.2 (p. 206, condition M2): A **finitely additive measure** (premeasure) `ν` on a
ring of sets `𝒜` is a function `ν : Set Ω → ℝ≥0∞` with `ν ∅ = 0` and `ν (A ∪ B) = ν A + ν B` for
disjoint `A, B ∈ 𝒜`. -/
structure IsFinitelyAdditiveMeasure {Ω : Type*} (𝒜 : Set (Set Ω)) (ν : Set Ω → ℝ≥0∞) : Prop where
  /-- `𝒜` is a ring of sets. -/
  isSetRing : IsSetRing 𝒜
  /-- Measure of empty set is `0`. -/
  map_empty : ν ∅ = 0
  /-- Binary disjoint additivity (condition M2). -/
  map_union_disjoint : ∀ ⦃A B : Set Ω⦄, A ∈ 𝒜 → B ∈ 𝒜 → Disjoint A B → ν (A ∪ B) = ν A + ν B

/-- Goldblatt §16.2 (p. 206): Finite pairwise disjoint additivity on a ring of sets. -/
theorem IsFinitelyAdditiveMeasure.sum_biUnion_finset {Ω ι : Type*} {𝒜 : Set (Set Ω)}
    {ν : Set Ω → ℝ≥0∞} (hν : IsFinitelyAdditiveMeasure 𝒜 ν) (s : Finset ι) {f : ι → Set Ω}
    (hf : ∀ i ∈ s, f i ∈ 𝒜) (hdisj : (s : Set ι).PairwiseDisjoint f) :
    ν (⋃ i ∈ s, f i) = ∑ i ∈ s, ν (f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using hν.map_empty
  | cons a t hat ih =>
      have heq : (⋃ i ∈ Finset.cons a t hat, f i) = f a ∪ ⋃ i ∈ t, f i := by ext x; simp
      have hd_at : Disjoint (f a) (⋃ i ∈ t, f i) := by
        rw [Set.disjoint_iUnion₂_right]
        intro i hi
        exact hdisj (Finset.mem_cons_self a t) (Finset.mem_cons_of_mem hi)
          (fun h ↦ hat (h ▸ hi))
      rw [heq, Finset.sum_cons,
        hν.map_union_disjoint (hf a (Finset.mem_cons_self a t))
          (hν.isSetRing.biUnion_finset_mem t fun i hi ↦ hf i (Finset.mem_cons_of_mem hi)) hd_at,
        ih (fun i hi ↦ hf i (Finset.mem_cons_of_mem hi))
          (hdisj.subset (by intro x hx; exact Finset.mem_cons_of_mem hx))]

/-- Decomposition `ν B = ν A + ν (B \ A)` for `A ⊆ B` in `𝒜`. -/
theorem IsFinitelyAdditiveMeasure.measure_eq_add_sdiff {Ω : Type*} {𝒜 : Set (Set Ω)}
    {ν : Set Ω → ℝ≥0∞} (hν : IsFinitelyAdditiveMeasure 𝒜 ν) {A B : Set Ω}
    (hA : A ∈ 𝒜) (hB : B ∈ 𝒜) (hAB : A ⊆ B) :
    ν B = ν A + ν (B \ A) := by
  have heq : B = A ∪ (B \ A) := (Set.union_sdiff_cancel hAB).symm
  conv_lhs => rw [heq]
  exact hν.map_union_disjoint hA (hν.isSetRing.sdiff_mem hB hA) disjoint_sdiff_self_right

/-- Goldblatt §16.2 (p. 206): **Monotonicity** of a finitely additive measure: `A ⊆ B → ν A ≤ ν B`
for `A, B ∈ 𝒜`. -/
theorem IsFinitelyAdditiveMeasure.mono {Ω : Type*} {𝒜 : Set (Set Ω)} {ν : Set Ω → ℝ≥0∞}
    (hν : IsFinitelyAdditiveMeasure 𝒜 ν) {A B : Set Ω}
    (hA : A ∈ 𝒜) (hB : B ∈ 𝒜) (hAB : A ⊆ B) :
    ν A ≤ ν B := by
  rw [hν.measure_eq_add_sdiff hA hB hAB]
  exact le_self_add

/-- Goldblatt §16.2 (p. 206): **Subtractivity**: if `A, B ∈ 𝒜`, `A ⊆ B`, and `ν A ≠ ⊤` (in
particular if `ν B < ⊤`), then `ν (B \ A) = ν B - ν A`. -/
theorem IsFinitelyAdditiveMeasure.measure_sdiff {Ω : Type*} {𝒜 : Set (Set Ω)} {ν : Set Ω → ℝ≥0∞}
    (hν : IsFinitelyAdditiveMeasure 𝒜 ν) {A B : Set Ω}
    (hA : A ∈ 𝒜) (hB : B ∈ 𝒜) (hAB : A ⊆ B) (hfin : ν A ≠ ⊤) :
    ν (B \ A) = ν B - ν A := by
  rw [hν.measure_eq_add_sdiff hA hB hAB, ENNReal.add_sub_cancel_left hfin]

/-- Inclusion–exclusion `ν (A ∪ B) + ν (A ∩ B) = ν A + ν B` on a ring of sets. -/
theorem IsFinitelyAdditiveMeasure.measure_union_add_inter {Ω : Type*} {𝒜 : Set (Set Ω)}
    {ν : Set Ω → ℝ≥0∞} (hν : IsFinitelyAdditiveMeasure 𝒜 ν) {A B : Set Ω}
    (hA : A ∈ 𝒜) (hB : B ∈ 𝒜) :
    ν (A ∪ B) + ν (A ∩ B) = ν A + ν B := by
  have h1 : A ∪ B = A ∪ (B \ A) := Set.union_sdiff_self.symm
  have h2 : B = (A ∩ B) ∪ (B \ A) := by
    ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]; tauto
  have hd1 : Disjoint A (B \ A) := disjoint_sdiff_self_right
  have hd2 : Disjoint (A ∩ B) (B \ A) :=
    Set.disjoint_left.2 fun x hx1 hx2 ↦ hx2.2 hx1.1
  rw [h1, hν.map_union_disjoint hA (hν.isSetRing.sdiff_mem hB hA) hd1]
  conv_rhs => rw [h2, hν.map_union_disjoint (hν.isSetRing.inter_mem hA hB)
    (hν.isSetRing.sdiff_mem hB hA) hd2]
  ac_rfl

/-- Finite binary subadditivity `ν (A ∪ B) ≤ ν A + ν B` on a ring of sets. -/
theorem IsFinitelyAdditiveMeasure.measure_union_le {Ω : Type*} {𝒜 : Set (Set Ω)}
    {ν : Set Ω → ℝ≥0∞} (hν : IsFinitelyAdditiveMeasure 𝒜 ν) {A B : Set Ω}
    (hA : A ∈ 𝒜) (hB : B ∈ 𝒜) :
    ν (A ∪ B) ≤ ν A + ν B := by
  have h1 : A ∪ B = A ∪ (B \ A) := Set.union_sdiff_self.symm
  rw [h1, hν.map_union_disjoint hA (hν.isSetRing.sdiff_mem hB hA) disjoint_sdiff_self_right]
  gcongr
  exact hν.mono (hν.isSetRing.sdiff_mem hB hA) hB Set.sdiff_subset

/-- Finite subadditivity `ν (⋃ i ∈ s, f i) ≤ ∑ i ∈ s, ν (f i)` on a ring of sets. -/
theorem IsFinitelyAdditiveMeasure.measure_biUnion_finset_le {Ω ι : Type*} {𝒜 : Set (Set Ω)}
    {ν : Set Ω → ℝ≥0∞} (hν : IsFinitelyAdditiveMeasure 𝒜 ν) (s : Finset ι) {f : ι → Set Ω}
    (hf : ∀ i ∈ s, f i ∈ 𝒜) :
    ν (⋃ i ∈ s, f i) ≤ ∑ i ∈ s, ν (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [hν.map_empty]
  | cons a t hat ih =>
      have heq : (⋃ i ∈ Finset.cons a t hat, f i) = f a ∪ ⋃ i ∈ t, f i := by ext x; simp
      rw [heq, Finset.sum_cons]
      refine (hν.measure_union_le (hf a (Finset.mem_cons_self a t))
        (hν.isSetRing.biUnion_finset_mem t fun i hi ↦ hf i (Finset.mem_cons_of_mem hi))).trans ?_
      gcongr
      exact ih fun i hi ↦ hf i (Finset.mem_cons_of_mem hi)

/-- Goldblatt §16.2 (p. 206, condition M1): A **countably additive measure** (`σ`-additive
premeasure) on a ring of sets `𝒜` satisfies `ν ∅ = 0` and `ν (⋃ n, A_n) = ∑' n, ν (A_n)` whenever
`(A_n)` is a pairwise disjoint sequence in `𝒜` whose union belongs to `𝒜`. -/
structure IsCountablyAdditiveMeasure {Ω : Type*} (𝒜 : Set (Set Ω)) (ν : Set Ω → ℝ≥0∞) : Prop where
  /-- `𝒜` is a ring of sets. -/
  isSetRing : IsSetRing 𝒜
  /-- Measure of empty set is `0`. -/
  map_empty : ν ∅ = 0
  /-- Countable disjoint additivity (condition M1). -/
  map_iUnion_disjoint : ∀ ⦃A : ℕ → Set Ω⦄, (∀ n, A n ∈ 𝒜) → Pairwise (Disjoint on A) →
    (⋃ n, A n) ∈ 𝒜 → ν (⋃ n, A n) = ∑' n, ν (A n)

/-- Every countably additive measure on a ring of sets is finitely additive (M1 ⇒ M2). -/
theorem IsCountablyAdditiveMeasure.toIsFinitelyAdditive {Ω : Type*} {𝒜 : Set (Set Ω)}
    {ν : Set Ω → ℝ≥0∞} (hν : IsCountablyAdditiveMeasure 𝒜 ν) :
    IsFinitelyAdditiveMeasure 𝒜 ν where
  isSetRing := hν.isSetRing
  map_empty := hν.map_empty
  map_union_disjoint := fun A B hA hB hdisj ↦ by
    let f : ℕ → Set Ω := fun n ↦ match n with | 0 => A | 1 => B | _ + 2 => ∅
    have hf_mem : ∀ n, f n ∈ 𝒜 := fun n ↦ match n with
      | 0 => hA | 1 => hB | _ + 2 => hν.isSetRing.empty_mem
    have hf_disj : Pairwise (Disjoint on f) := by
      intro i j hij
      match i, j with
      | 0, 0 => exact (hij rfl).elim
      | 0, 1 => exact hdisj
      | 1, 0 => exact hdisj.symm
      | 1, 1 => exact (hij rfl).elim
      | _ + 2, _ => simp [f]
      | _, _ + 2 => simp [f]
    have hU : (⋃ n, f n) = A ∪ B := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨n, hn⟩
        match n with
        | 0 => exact Or.inl hn
        | 1 => exact Or.inr hn
        | _ + 2 => simp [f] at hn
      · rintro (hxA | hxB)
        · exact ⟨0, hxA⟩
        · exact ⟨1, hxB⟩
    have hsum : (∑' n, ν (f n)) = ν A + ν B := by
      rw [tsum_eq_sum (s := {0, 1}) (fun n hn ↦ by
        match n with
        | 0 => exact (hn (by simp)).elim
        | 1 => exact (hn (by simp)).elim
        | _ + 2 => simp [f, hν.map_empty])]
      simp [f]
    rw [← hU, hν.map_iUnion_disjoint hf_mem hf_disj (hU ▸ hν.isSetRing.union_mem hA hB), hsum]

/-- Countable subadditivity on a ring `𝒜`: if `B ∈ 𝒜`, `∀ n, A n ∈ 𝒜`, and `B ⊆ ⋃ n, A n`, then
`ν B ≤ ∑' n, ν (A n)`. -/
theorem IsCountablyAdditiveMeasure.le_tsum_of_subset_iUnion {Ω : Type*} {𝒜 : Set (Set Ω)}
    {ν : Set Ω → ℝ≥0∞} (hν : IsCountablyAdditiveMeasure 𝒜 ν) {B : Set Ω} (hB : B ∈ 𝒜)
    {A : ℕ → Set Ω} (hA : ∀ n, A n ∈ 𝒜) (hsub : B ⊆ ⋃ n, A n) :
    ν B ≤ ∑' n, ν (A n) := by
  let D : ℕ → Set Ω := disjointed (fun n ↦ B ∩ A n)
  have hBA : ∀ n, B ∩ A n ∈ 𝒜 := fun n ↦ hν.isSetRing.inter_mem hB (hA n)
  have hD_mem : ∀ n, D n ∈ 𝒜 := hν.isSetRing.disjointed_mem hBA
  have hD_disj : Pairwise (Disjoint on D) := disjoint_disjointed _
  have hU_eq : (⋃ n, D n) = B := by
    rw [iUnion_disjointed, ← Set.inter_iUnion, Set.inter_eq_self_of_subset_left hsub]
  rw [← hU_eq, hν.map_iUnion_disjoint hD_mem hD_disj (hU_eq ▸ hB)]
  refine ENNReal.tsum_le_tsum fun n ↦ ?_
  exact hν.toIsFinitelyAdditive.mono (hD_mem n) (hA n)
    ((disjointed_subset _ n).trans Set.inter_subset_right)

/-- Goldblatt §16.2 (p. 207): **Continuity from below**: if `(A_n)` is an increasing sequence in
`𝒜` whose union belongs to `𝒜`, then `ν (⋃ n, A_n) = ⨆ n, ν (A_n)` and `ν(A_n) → ν(⋃ n, A_n)`. -/
theorem IsCountablyAdditiveMeasure.measure_iUnion_of_monotone {Ω : Type*} {𝒜 : Set (Set Ω)}
    {ν : Set Ω → ℝ≥0∞} (hν : IsCountablyAdditiveMeasure 𝒜 ν) {A : ℕ → Set Ω}
    (hA : ∀ n, A n ∈ 𝒜) (hMono : Monotone A) (hU : (⋃ n, A n) ∈ 𝒜) :
    ν (⋃ n, A n) = (⨆ n, ν (A n)) ∧
    Tendsto (fun n ↦ ν (A n)) atTop (𝓝 (ν (⋃ n, A n))) := by
  let D : ℕ → Set Ω := disjointed A
  have hD_mem : ∀ n, D n ∈ 𝒜 := hν.isSetRing.disjointed_mem hA
  have hD_disj : Pairwise (Disjoint on D) := disjoint_disjointed A
  have hU_D : (⋃ n, D n) = ⋃ n, A n := iUnion_disjointed
  have hpart : ∀ n : ℕ, (⋃ i ∈ Finset.range (n + 1), D i) = A n := fun n ↦
    (biUnion_range_succ_disjointed A n).trans (congrFun hMono.partialSups_eq n)
  have hsum_part : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), ν (D i) = ν (A n) := by
    intro n
    rw [← hν.toIsFinitelyAdditive.sum_biUnion_finset (Finset.range (n + 1))
      (fun i _ ↦ hD_mem i) (fun i _ j _ hij ↦ hD_disj hij), hpart n]
  have heq_sup : ν (⋃ n, A n) = ⨆ n, ν (A n) := by
    rw [← hU_D, hν.map_iUnion_disjoint hD_mem hD_disj (hU_D ▸ hU), ENNReal.tsum_eq_iSup_nat]
    apply le_antisymm
    · refine iSup_le fun n ↦ ?_
      rcases n with _ | m
      · simp
      · rw [hsum_part m]
        exact le_iSup (fun k ↦ ν (A k)) m
    · refine iSup_le fun m ↦ ?_
      rw [← hsum_part m]
      exact le_iSup (fun k ↦ ∑ i ∈ Finset.range k, ν (D i)) (m + 1)
  have hMonoVal : Monotone (fun n ↦ ν (A n)) :=
    fun i j hij ↦ hν.toIsFinitelyAdditive.mono (hA i) (hA j) (hMono hij)
  exact ⟨heq_sup, heq_sup ▸ tendsto_atTop_iSup hMonoVal⟩

/-- Equivalence of `σ`-additivity and continuity from below for a finitely additive measure on a
ring `𝒜`. -/
theorem isCountablyAdditiveMeasure_iff_monotone_iUnion {Ω : Type*} {𝒜 : Set (Set Ω)}
    {ν : Set Ω → ℝ≥0∞} (hν : IsFinitelyAdditiveMeasure 𝒜 ν) :
    IsCountablyAdditiveMeasure 𝒜 ν ↔
      ∀ ⦃A : ℕ → Set Ω⦄, (∀ n, A n ∈ 𝒜) → Monotone A → (⋃ n, A n) ∈ 𝒜 →
        ν (⋃ n, A n) = ⨆ n, ν (A n) := by
  constructor
  · exact fun hCA A hA hMono hU ↦ (hCA.measure_iUnion_of_monotone hA hMono hU).1
  · intro hCont
    refine ⟨hν.isSetRing, hν.map_empty, fun A hA hDisj hU ↦ ?_⟩
    let P : ℕ → Set Ω := fun n ↦ ⋃ i ∈ Finset.range n, A i
    have hP_mem : ∀ n, P n ∈ 𝒜 :=
      fun n ↦ hν.isSetRing.biUnion_finset_mem _ fun i _ ↦ hA i
    have hP_mono : Monotone P := fun i j hij x hx ↦ by
      obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.1 hx
      exact Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2 ((Finset.mem_range.1 hk).trans_le hij), hxk⟩
    have hUP : (⋃ n, P n) = ⋃ n, A n := by
      ext x
      simp only [P, Set.mem_iUnion, Finset.mem_range]
      exact ⟨fun ⟨_, k, _, hxk⟩ ↦ ⟨k, hxk⟩, fun ⟨k, hxk⟩ ↦ ⟨k + 1, k, Nat.lt_succ_self k, hxk⟩⟩
    rw [← hUP, hCont hP_mem hP_mono (hUP ▸ hU), ENNReal.tsum_eq_iSup_nat]
    congr 1; ext n
    exact hν.sum_biUnion_finset (Finset.range n) (fun i _ ↦ hA i)
      (fun i _ j _ hij ↦ hDisj hij)

/-- **Continuity from above**: if `(A_n)` is a decreasing (`Antitone`) sequence in `𝒜` whose
intersection belongs to `𝒜` and `ν (A 0) < ⊤`, then `ν (⋂ n, A_n) = ⨅ n, ν (A_n)` and
`ν(A_n) → ν(⋂ n, A_n)`. -/
theorem IsCountablyAdditiveMeasure.measure_iInter_of_antitone {Ω : Type*} {𝒜 : Set (Set Ω)}
    {ν : Set Ω → ℝ≥0∞} (hν : IsCountablyAdditiveMeasure 𝒜 ν) {A : ℕ → Set Ω}
    (hA : ∀ n, A n ∈ 𝒜) (hAnti : Antitone A) (hI : (⋂ n, A n) ∈ 𝒜) (hFin : ν (A 0) < ⊤) :
    ν (⋂ n, A n) = (⨅ n, ν (A n)) ∧
    Tendsto (fun n ↦ ν (A n)) atTop (𝓝 (ν (⋂ n, A n))) := by
  let B : ℕ → Set Ω := fun n ↦ A 0 \ A n
  have hB_mem : ∀ n, B n ∈ 𝒜 := fun n ↦ hν.isSetRing.sdiff_mem (hA 0) (hA n)
  have hB_mono : Monotone B := fun i j hij ↦ Set.sdiff_subset_sdiff_right (hAnti hij)
  have hUB : (⋃ n, B n) = A 0 \ ⋂ n, A n := by
    ext x; simp [B, Set.mem_sdiff, not_forall]
  have hUB_mem : (⋃ n, B n) ∈ 𝒜 := hUB ▸ hν.isSetRing.sdiff_mem (hA 0) hI
  have hsup := (hν.measure_iUnion_of_monotone hB_mem hB_mono hUB_mem).1
  rw [hUB] at hsup
  have hFA := hν.toIsFinitelyAdditive
  have hFinI : ν (⋂ n, A n) ≠ ⊤ :=
    ((hFA.mono hI (hA 0) (Set.iInter_subset A 0)).trans_lt hFin).ne
  have hFinN : ∀ n, ν (A n) ≠ ⊤ :=
    fun n ↦ ((hFA.mono (hA n) (hA 0) (hAnti (Nat.zero_le n))).trans_lt hFin).ne
  have heq_inf : ν (⋂ n, A n) = ⨅ n, ν (A n) := by
    have h1 : ν (A 0) - ν (⋂ n, A n) = ⨆ n, (ν (A 0) - ν (A n)) := by
      rw [← hFA.measure_sdiff hI (hA 0) (Set.iInter_subset A 0) hFinI, hsup]
      congr 1; ext n
      exact hFA.measure_sdiff (hA n) (hA 0) (hAnti (Nat.zero_le n)) (hFinN n)
    rw [← ENNReal.sub_iInf] at h1
    have hInf_le : (⨅ n, ν (A n)) ≤ ν (A 0) := iInf_le (fun n ↦ ν (A n)) 0
    have hI_le : ν (⋂ n, A n) ≤ ν (A 0) := hFA.mono hI (hA 0) (Set.iInter_subset A 0)
    have hsub1 : ν (A 0) - (ν (A 0) - ν (⋂ n, A n)) = ν (⋂ n, A n) :=
      ENNReal.sub_sub_cancel hFin.ne hI_le
    have hsub2 : ν (A 0) - (ν (A 0) - ⨅ n, ν (A n)) = ⨅ n, ν (A n) :=
      ENNReal.sub_sub_cancel hFin.ne hInf_le
    calc ν (⋂ n, A n)
        = ν (A 0) - (ν (A 0) - ν (⋂ n, A n)) := hsub1.symm
      _ = ν (A 0) - (ν (A 0) - ⨅ n, ν (A n)) := by rw [h1]
      _ = ⨅ n, ν (A n) := hsub2
  have hAntiVal : Antitone (fun n ↦ ν (A n)) :=
    fun i j hij ↦ hFA.mono (hA j) (hA i) (hAnti hij)
  exact ⟨heq_inf, heq_inf ▸ tendsto_atTop_iInf hAntiVal⟩

/-- Equivalence of `σ`-additivity and continuity at `∅` from above for a finite finitely additive
measure (`ν Set.univ < ⊤`) on an algebra `𝒜`. -/
theorem isCountablyAdditiveMeasure_iff_antitone_empty {Ω : Type*} {𝒜 : Set (Set Ω)}
    {ν : Set Ω → ℝ≥0∞} (hAlg : IsSetAlgebra 𝒜) (hν : IsFinitelyAdditiveMeasure 𝒜 ν)
    (hFin : ν Set.univ < ⊤) :
    IsCountablyAdditiveMeasure 𝒜 ν ↔
      ∀ ⦃D : ℕ → Set Ω⦄, (∀ n, D n ∈ 𝒜) → Antitone D → (⋂ n, D n) = ∅ →
        (⨅ n, ν (D n)) = 0 := by
  constructor
  · intro hCA D hD hAnti hEmpty
    have hFin0 : ν (D 0) < ⊤ :=
      (hν.mono (hD 0) hAlg.univ_mem (Set.subset_univ _)).trans_lt hFin
    have h := (hCA.measure_iInter_of_antitone hD hAnti
      (hEmpty ▸ hAlg.toIsSetRing.empty_mem) hFin0).1
    rw [hEmpty, hν.map_empty] at h
    exact h.symm
  · intro hZero
    rw [isCountablyAdditiveMeasure_iff_monotone_iUnion hν]
    intro A hA hMono hU
    let D : ℕ → Set Ω := fun n ↦ (⋃ k, A k) \ A n
    have hD_mem : ∀ n, D n ∈ 𝒜 := fun n ↦ hν.isSetRing.sdiff_mem hU (hA n)
    have hD_anti : Antitone D := fun i j hij ↦ Set.sdiff_subset_sdiff_right (hMono hij)
    have hD_empty : (⋂ n, D n) = ∅ := by
      ext x
      simp only [D, Set.mem_iInter, Set.mem_sdiff, Set.mem_iUnion, Set.mem_empty_iff_false,
        iff_false]
      intro h
      obtain ⟨k, hxk⟩ := (h 0).1
      exact (h k).2 hxk
    have hInf0 : (⨅ n, ν (D n)) = 0 := hZero hD_mem hD_anti hD_empty
    have hU_fin : ν (⋃ k, A k) < ⊤ :=
      (hν.mono hU hAlg.univ_mem (Set.subset_univ _)).trans_lt hFin
    have hAn_fin : ∀ n, ν (A n) ≠ ⊤ := fun n ↦
      ((hν.mono (hA n) hAlg.univ_mem (Set.subset_univ _)).trans_lt hFin).ne
    have hsub : ∀ n, ν (D n) = ν (⋃ k, A k) - ν (A n) := fun n ↦
      hν.measure_sdiff (hA n) hU (Set.subset_iUnion A n) (hAn_fin n)
    simp_rw [hsub] at hInf0
    rw [← ENNReal.sub_iSup hU_fin.ne] at hInf0
    exact le_antisymm (tsub_eq_zero_iff_le.1 hInf0)
      (iSup_le fun n ↦ hν.mono (hA n) hU (Set.subset_iUnion A n))

/-- Goldblatt §16.2 (p. 207): `A` is `ν`-finite if `ν A < ⊤`. -/
def IsMuFinite {Ω : Type*} (ν : Set Ω → ℝ≥0∞) (A : Set Ω) : Prop := ν A < ⊤

/-- Goldblatt §16.2 (p. 207): `A` is `ν`-null if `ν A = 0`. -/
def IsMuNull {Ω : Type*} (ν : Set Ω → ℝ≥0∞) (A : Set Ω) : Prop := ν A = 0

/-- Goldblatt §16.2 (p. 207): `ν` is **σ-finite** on `𝒜` if `Ω` is a countable union of `ν`-finite
members of `𝒜`. -/
def IsSigmaFiniteOn {Ω : Type*} (𝒜 : Set (Set Ω)) (ν : Set Ω → ℝ≥0∞) : Prop :=
  ∃ A : ℕ → Set Ω, (∀ n, A n ∈ 𝒜 ∧ ν (A n) < ⊤) ∧ (⋃ n, A n) = Set.univ

/-- Goldblatt §16.2 Example (1) (p. 207): Counting measure `μ_c(A) = |A|` (`A.encard`) on `𝒫(Ω)`. -/
def countingPremeasure {Ω : Type*} (A : Set Ω) : ℝ≥0∞ := A.encard

/-- Goldblatt §16.2 Example (1) (p. 207): `countingPremeasure` is a countably additive measure on
`𝒫(Ω)`, and is σ-finite if and only if `Ω` is countable. -/
theorem countingPremeasure_properties (Ω : Type*) :
    IsCountablyAdditiveMeasure (Set.univ : Set (Set Ω)) countingPremeasure ∧
    (IsSigmaFiniteOn (Set.univ : Set (Set Ω)) countingPremeasure ↔ Countable Ω) := by
  let c : @MeasureTheory.Measure Ω ⊤ := @MeasureTheory.Measure.count Ω ⊤
  have hc : ∀ X : Set Ω, c X = countingPremeasure X :=
    fun X ↦ @MeasureTheory.Measure.count_apply Ω ⊤ X trivial
  refine ⟨⟨(isSigmaAlgebra_univ Ω).toIsSigmaRing.toIsSetRing, by simp [countingPremeasure],
    fun A _ hDisj _ ↦ ?_⟩, ?_⟩
  · simp_rw [← hc]
    exact @MeasureTheory.measure_iUnion ℕ Ω ⊤ c _ A hDisj (fun _ ↦ trivial)
  · constructor
    · rintro ⟨A, hA, hU⟩
      have hFin : ∀ n, (A n).Finite := fun n ↦
        (@MeasureTheory.Measure.count_apply_lt_top' Ω ⊤ (A n) trivial).1 (hc (A n) ▸ (hA n).2)
      have hCountUniv : (Set.univ : Set Ω).Countable := by
        rw [← hU]
        exact Set.countable_iUnion fun n ↦ (hFin n).countable
      exact Set.countable_univ_iff.1 hCountUniv
    · intro hCount
      rcases isEmpty_or_nonempty Ω with hEmp | hNe
      · refine ⟨fun _ ↦ ∅, fun _ ↦ ⟨trivial, by simp [countingPremeasure]⟩, ?_⟩
        ext x; exact (IsEmpty.false x).elim
      · obtain ⟨f, hf⟩ := exists_surjective_nat Ω
        refine ⟨fun n ↦ {f n}, fun n ↦ ⟨trivial, by simp [countingPremeasure]⟩, ?_⟩
        ext x
        simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        obtain ⟨n, rfl⟩ := hf x
        exact ⟨n, rfl⟩

/-! ## §16.3 Carathéodory / Hopf Outer Measure and Extension Theorem -/

/-- Extension of `ν : Set Ω → ℝ≥0∞` outside `𝒜` by `⊤` for constructing the Hopf outer measure. -/
def extendOutside {Ω : Type*} (𝒜 : Set (Set Ω)) (ν : Set Ω → ℝ≥0∞) (A : Set Ω) : ℝ≥0∞ :=
  if A ∈ 𝒜 then ν A else ⊤

/-- Goldblatt §16.3 (p. 208): The **Hopf / Carathéodory outer measure** `ν*` generated by a
function `ν : Set Ω → ℝ≥0∞` on a collection `𝒜` with `∅ ∈ 𝒜` and `ν ∅ = 0`. -/
def caratheodoryOuter {Ω : Type*} (𝒜 : Set (Set Ω)) (ν : Set Ω → ℝ≥0∞)
    (hEmpty : (∅ : Set Ω) ∈ 𝒜) (hZero : ν ∅ = 0) : MeasureTheory.OuterMeasure Ω :=
  MeasureTheory.OuterMeasure.ofFunction (extendOutside 𝒜 ν)
    (by simp [extendOutside, hEmpty, hZero])

/-- Goldblatt §16.3 (p. 208): Explicit infimum formula
`ν*(X) = ⨅ (A : ℕ → Set Ω) (_ : ∀ n, A n ∈ 𝒜) (_ : X ⊆ ⋃ n, A n), ∑' n, ν (A n)`. -/
theorem caratheodoryOuter_eq_iInf {Ω : Type*} (𝒜 : Set (Set Ω)) (ν : Set Ω → ℝ≥0∞)
    (hEmpty : (∅ : Set Ω) ∈ 𝒜) (hZero : ν ∅ = 0) (X : Set Ω) :
    caratheodoryOuter 𝒜 ν hEmpty hZero X =
      ⨅ (A : ℕ → Set Ω) (_ : ∀ n, A n ∈ 𝒜) (_ : X ⊆ ⋃ n, A n), ∑' n, ν (A n) := by
  rw [caratheodoryOuter, MeasureTheory.OuterMeasure.ofFunction_eq_iInf_mem _ _
    (P := (· ∈ 𝒜)) (fun s hs ↦ by simp [extendOutside, hs])]
  refine iInf_congr fun A ↦ iInf_congr fun hA ↦ iInf_congr fun _ ↦ ?_
  exact tsum_congr fun n ↦ by simp [extendOutside, hA n]

/-- Upper bound `ν*(A) ≤ ν(A)` for all `A ∈ 𝒜`. -/
theorem caratheodoryOuter_le_of_mem {Ω : Type*} {𝒜 : Set (Set Ω)} {ν : Set Ω → ℝ≥0∞}
    (hEmpty : (∅ : Set Ω) ∈ 𝒜) (hZero : ν ∅ = 0) {A : Set Ω} (hA : A ∈ 𝒜) :
    caratheodoryOuter 𝒜 ν hEmpty hZero A ≤ ν A := by
  refine (MeasureTheory.OuterMeasure.ofFunction_le A).trans ?_
  simp [extendOutside, hA]

/-- Goldblatt §16.3 (p. 209): `ν*` satisfies the three outer measure laws: `ν*(∅) = 0`,
monotonicity, and countable subadditivity. -/
theorem caratheodoryOuter_laws {Ω : Type*} (𝒜 : Set (Set Ω)) (ν : Set Ω → ℝ≥0∞)
    (hEmpty : (∅ : Set Ω) ∈ 𝒜) (hZero : ν ∅ = 0) :
    caratheodoryOuter 𝒜 ν hEmpty hZero ∅ = 0 ∧
    (∀ ⦃X Y : Set Ω⦄, X ⊆ Y →
      caratheodoryOuter 𝒜 ν hEmpty hZero X ≤ caratheodoryOuter 𝒜 ν hEmpty hZero Y) ∧
    (∀ X : ℕ → Set Ω,
      caratheodoryOuter 𝒜 ν hEmpty hZero (⋃ n, X n) ≤
        ∑' n, caratheodoryOuter 𝒜 ν hEmpty hZero (X n)) :=
  ⟨(caratheodoryOuter 𝒜 ν hEmpty hZero).empty,
   fun _ _ h ↦ (caratheodoryOuter 𝒜 ν hEmpty hZero).mono h,
   fun X ↦ MeasureTheory.measure_iUnion_le X⟩

/-- Goldblatt §16.3 bullet 1 (p. 209): When `ν` is countably additive on a ring `𝒜`, `ν*` agrees
with `ν` on `𝒜`: `ν*(B) = ν(B)` for every `B ∈ 𝒜`. -/
theorem caratheodoryOuter_eq_of_mem {Ω : Type*} {𝒜 : Set (Set Ω)} {ν : Set Ω → ℝ≥0∞}
    (hν : IsCountablyAdditiveMeasure 𝒜 ν) {B : Set Ω} (hB : B ∈ 𝒜) :
    caratheodoryOuter 𝒜 ν hν.isSetRing.empty_mem hν.map_empty B = ν B := by
  refine le_antisymm (caratheodoryOuter_le_of_mem _ _ hB) ?_
  rw [caratheodoryOuter_eq_iInf]
  refine le_iInf fun A ↦ le_iInf fun hA ↦ le_iInf fun hsub ↦ ?_
  exact hν.le_tsum_of_subset_iUnion hB hA hsub

/-- Goldblatt §16.3 bullet 4 (p. 209): For any `B : Set Ω` with `ν*(B) < ⊤` and any `ε > 0` in `ℝ`,
there is an increasing sequence `A_0 ⊆ A_1 ⊆ …` in `𝒜` covering `B` such that
`(⨆ n, ν (A_n)) < ν*(B) + ENNReal.ofReal ε` (hence `ν(A_n) < ν*(B) + ENNReal.ofReal ε` for all `n`). -/
theorem caratheodoryOuter_exists_monotone_cover_lt {Ω : Type*} {𝒜 : Set (Set Ω)}
    {ν : Set Ω → ℝ≥0∞} (hν : IsFinitelyAdditiveMeasure 𝒜 ν) {B : Set Ω}
    (hFin : caratheodoryOuter 𝒜 ν hν.isSetRing.empty_mem hν.map_empty B < ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℕ → Set Ω, (∀ n, A n ∈ 𝒜) ∧ Monotone A ∧ B ⊆ (⋃ n, A n) ∧
      (⨆ n, ν (A n)) <
        caratheodoryOuter 𝒜 ν hν.isSetRing.empty_mem hν.map_empty B + ENNReal.ofReal ε := by
  set μ_star := caratheodoryOuter 𝒜 ν hν.isSetRing.empty_mem hν.map_empty
  have hlt : μ_star B < μ_star B + ENNReal.ofReal ε :=
    ENNReal.lt_add_right hFin.ne (ENNReal.ofReal_pos.2 hε).ne'
  conv_lhs at hlt => rw [caratheodoryOuter_eq_iInf]
  simp only [iInf_lt_iff, exists_prop] at hlt
  obtain ⟨C, hC_mem, hC_cov, hC_sum⟩ := hlt
  let A : ℕ → Set Ω := fun n ↦ ⋃ i ∈ Finset.range (n + 1), C i
  have hA_mem : ∀ n, A n ∈ 𝒜 :=
    fun n ↦ hν.isSetRing.biUnion_finset_mem _ fun i _ ↦ hC_mem i
  have hA_mono : Monotone A := fun i j hij x hx ↦ by
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_iUnion₂.2
      ⟨k, Finset.mem_range.2 ((Finset.mem_range.1 hk).trans_le (Nat.succ_le_succ hij)), hxk⟩
  have hA_cov : B ⊆ ⋃ n, A n := by
    refine hC_cov.trans fun x hx ↦ ?_
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_self k), hxk⟩⟩
  refine ⟨A, hA_mem, hA_mono, hA_cov, lt_of_le_of_lt ?_ hC_sum⟩
  refine iSup_le fun n ↦ ?_
  exact (hν.measure_biUnion_finset_le (Finset.range (n + 1)) fun i _ ↦ hC_mem i).trans
    (ENNReal.sum_le_tsum (Finset.range (n + 1)))

/-- Goldblatt §16.3 (p. 209): Carathéodory measurability with respect to an outer measure `m`:
`B` splits every test set `E` additively (`m E = m (E ∩ B) + m (E \ B)`). -/
abbrev IsCaratheodoryMeasurable {Ω : Type*} (m : MeasureTheory.OuterMeasure Ω) (B : Set Ω) : Prop :=
  m.IsCaratheodory B

/-- Goldblatt §16.3 (p. 209): To check Carathéodory measurability of `B`, it suffices that
`m (E ∩ B) + m (E \ B) ≤ m E` whenever `m E < ⊤`. -/
theorem isCaratheodoryMeasurable_iff_le_of_lt_top {Ω : Type*}
    (m : MeasureTheory.OuterMeasure Ω) (B : Set Ω) :
    IsCaratheodoryMeasurable m B ↔ ∀ E : Set Ω, m E < ⊤ → m (E ∩ B) + m (E \ B) ≤ m E := by
  unfold IsCaratheodoryMeasurable
  rw [MeasureTheory.OuterMeasure.isCaratheodory_iff_le']
  constructor
  · exact fun h E _ ↦ h E
  · intro h E
    rcases lt_or_ge (m E) ⊤ with hlt | htop
    · exact h E hlt
    · exact le_top.trans (top_le_iff.1 htop).symm.le

/-- Goldblatt §16.3 (p. 209): For ANY finitely additive measure `ν` on a ring `𝒜`, **every**
`A ∈ 𝒜` is Carathéodory `ν*`-measurable! -/
theorem isCaratheodoryMeasurable_of_mem {Ω : Type*} {𝒜 : Set (Set Ω)} {ν : Set Ω → ℝ≥0∞}
    (hν : IsFinitelyAdditiveMeasure 𝒜 ν) {A : Set Ω} (hA : A ∈ 𝒜) :
    IsCaratheodoryMeasurable (caratheodoryOuter 𝒜 ν hν.isSetRing.empty_mem hν.map_empty) A := by
  apply MeasureTheory.OuterMeasure.ofFunction_caratheodory
  intro T
  by_cases hT : T ∈ 𝒜
  · have hTA : T ∩ A ∈ 𝒜 := hν.isSetRing.inter_mem hT hA
    have hTsA : T \ A ∈ 𝒜 := hν.isSetRing.sdiff_mem hT hA
    simp only [extendOutside, hT, hTA, hTsA, ↓reduceIte]
    have hd : Disjoint (T ∩ A) (T \ A) :=
      Set.disjoint_left.2 fun x hx1 hx2 ↦ hx2.2 hx1.2
    rw [← hν.map_union_disjoint hTA hTsA hd, Set.inter_union_sdiff]
  · simp [extendOutside, hT]

/-- Goldblatt §16.3 (p. 209): The collection `{B : Set Ω | IsCaratheodoryMeasurable m B}` of
Carathéodory measurable sets is a σ-algebra containing all `m`-null sets. -/
theorem isSigmaAlgebra_caratheodory {Ω : Type*} (m : MeasureTheory.OuterMeasure Ω) :
    IsSigmaAlgebra {B : Set Ω | IsCaratheodoryMeasurable m B} ∧
    ∀ ⦃N : Set Ω⦄, m N = 0 → IsCaratheodoryMeasurable m N := by
  refine ⟨⟨⟨⟨⟨∅, m.isCaratheodory_empty⟩,
    fun A B hA hB ↦ m.isCaratheodory_sdiff hA hB,
    fun A B hA hB ↦ m.isCaratheodory_union hA hB⟩,
    fun f hf ↦ m.isCaratheodory_iUnion hf⟩,
    by simpa using m.isCaratheodory_compl m.isCaratheodory_empty⟩,
    fun N hN ↦ m.isCaratheodory_of_measure_eq_zero hN⟩

/-- Goldblatt §16.3 (p. 209): Every set in the σ-algebra `S(𝒜)` generated by `𝒜` is Carathéodory
`ν*`-measurable. -/
theorem sigmaAlgebraGenerated_subset_caratheodory {Ω : Type*} {𝒜 : Set (Set Ω)}
    {ν : Set Ω → ℝ≥0∞} (hν : IsFinitelyAdditiveMeasure 𝒜 ν) :
    sigmaAlgebraGenerated 𝒜 ⊆
      {B : Set Ω |
        IsCaratheodoryMeasurable
          (caratheodoryOuter 𝒜 ν hν.isSetRing.empty_mem hν.map_empty) B} :=
  (isSigmaAlgebra_sigmaAlgebraGenerated 𝒜).2.2.1
    (isSigmaAlgebra_caratheodory _).1
    (fun _ hA ↦ isCaratheodoryMeasurable_of_mem hν hA)

/-- Goldblatt §16.3 (p. 209): The **Carathéodory extension measure** on the Carathéodory
σ-algebra `(ν*).caratheodory`. -/
def caratheodoryExtensionMeasure {Ω : Type*} {𝒜 : Set (Set Ω)} {ν : Set Ω → ℝ≥0∞}
    (hν : IsCountablyAdditiveMeasure 𝒜 ν) :
    @MeasureTheory.Measure Ω
      (caratheodoryOuter 𝒜 ν hν.isSetRing.empty_mem hν.map_empty).caratheodory :=
  let m := caratheodoryOuter 𝒜 ν hν.isSetRing.empty_mem hν.map_empty
  @MeasureTheory.OuterMeasure.toMeasure Ω m.caratheodory m le_rfl

/-- Goldblatt §16.3 (p. 209, **Carathéodory Extension Theorem**):
For a countably additive premeasure `ν` on a ring `𝒜`, `caratheodoryExtensionMeasure hν` is a
**complete** countably additive measure on `(ν*).caratheodory` that agrees with `ν*` on all
Carathéodory measurable sets and extends `ν` on `𝒜`. -/
theorem caratheodoryExtensionMeasure_properties {Ω : Type*} {𝒜 : Set (Set Ω)} {ν : Set Ω → ℝ≥0∞}
    (hν : IsCountablyAdditiveMeasure 𝒜 ν) :
    let m := caratheodoryOuter 𝒜 ν hν.isSetRing.empty_mem hν.map_empty
    @MeasureTheory.Measure.IsComplete Ω m.caratheodory (caratheodoryExtensionMeasure hν) ∧
    (∀ ⦃B : Set Ω⦄, m.IsCaratheodory B → caratheodoryExtensionMeasure hν B = m B) ∧
    (∀ ⦃A : Set Ω⦄, A ∈ 𝒜 → m.IsCaratheodory A ∧ caratheodoryExtensionMeasure hν A = ν A) := by
  intro m
  have hApply : ∀ ⦃B : Set Ω⦄, m.IsCaratheodory B → caratheodoryExtensionMeasure hν B = m B :=
    fun B hB ↦ @MeasureTheory.toMeasure_apply Ω m.caratheodory m le_rfl B hB
  refine ⟨⟨fun Z hZ ↦ ?_⟩, hApply, fun A hA ↦ ?_⟩
  · have hmZ : m Z = 0 := le_antisymm
      ((@MeasureTheory.le_toMeasure_apply Ω m.caratheodory m le_rfl Z).trans hZ.le) zero_le
    exact m.isCaratheodory_of_measure_eq_zero hmZ
  · have hCar : m.IsCaratheodory A := isCaratheodoryMeasurable_of_mem hν.toIsFinitelyAdditive hA
    exact ⟨hCar, (hApply hCar).trans (caratheodoryOuter_eq_of_mem hν hA)⟩

/-- Goldblatt §16.3 completeness sandwich (p. 209): If `A ⊆ C ⊆ B` with `A, B` Carathéodory
`m`-measurable and `m (B \ A) = 0` (which holds automatically whenever `m A = m B < ⊤`), then `C`
is Carathéodory `m`-measurable and `m C = m A = m B`. -/
theorem isCaratheodoryMeasurable_of_sandwich {Ω : Type*} (m : MeasureTheory.OuterMeasure Ω)
    {A B C : Set Ω} (hA : m.IsCaratheodory A) (_hB : m.IsCaratheodory B)
    (hAC : A ⊆ C) (hCB : C ⊆ B) (hNull : m (B \ A) = 0) :
    m.IsCaratheodory C ∧ m C = m A ∧ m C = m B := by
  have hCA_zero : m (C \ A) = 0 :=
    le_antisymm ((m.mono (Set.sdiff_subset_sdiff_left hCB)).trans hNull.le) zero_le
  have hC_eq : C = A ∪ (C \ A) := (Set.union_sdiff_cancel hAC).symm
  have hCarC : m.IsCaratheodory C :=
    hC_eq ▸ m.isCaratheodory_union hA (m.isCaratheodory_of_measure_eq_zero hCA_zero)
  have hmB : m B = m A := by
    have hBA := hA B
    rw [Set.inter_eq_self_of_subset_right (hAC.trans hCB), hNull, add_zero] at hBA
    exact hBA
  have hmC : m C = m A := le_antisymm
    ((m.mono hCB).trans hmB.le) (m.mono hAC)
  exact ⟨hCarC, hmC, hmC.trans hmB.symm⟩

/-- Goldblatt §16.3 bullet 5 (p. 209): **Uniqueness of Carathéodory Extension** when `ν` is
`σ`-finite on an algebra `𝒜`: any two measures on `MeasurableSpace.generateFrom 𝒜` that agree with
`ν` on `𝒜` are equal! -/
theorem caratheodoryExtension_unique_on_generateFrom {Ω : Type*} {𝒜 : Set (Set Ω)}
    {ν : Set Ω → ℝ≥0∞} (hAlg : IsSetAlgebra 𝒜) (hFin : IsSigmaFiniteOn 𝒜 ν)
    (μ₁ μ₂ : @MeasureTheory.Measure Ω (MeasurableSpace.generateFrom 𝒜))
    (h₁ : ∀ A ∈ 𝒜, μ₁ A = ν A) (h₂ : ∀ A ∈ 𝒜, μ₂ A = ν A) :
    μ₁ = μ₂ := by
  obtain ⟨E, hE, hUE⟩ := hFin
  have hPi : IsPiSystem 𝒜 := fun A hA B hB _ ↦ hAlg.toIsSetRing.inter_mem hA hB
  exact @MeasureTheory.Measure.ext_of_generateFrom_of_iUnion Ω (MeasurableSpace.generateFrom 𝒜)
    μ₁ μ₂ 𝒜 E rfl hPi hUE (fun n ↦ (hE n).1)
    (fun n ↦ by rw [h₁ (E n) (hE n).1]; exact (hE n).2.ne)
    (fun A hA ↦ (h₁ A hA).trans (h₂ A hA).symm)

/-- **Finite Carathéodory `𝒜_σ` / `𝒜_δ` Approximation Theorem**:
When `ν` is a countably additive premeasure on an algebra `𝒜` with `ν Set.univ < ⊤`, a set
`X : Set Ω` is Carathéodory `ν*`-measurable **if and only if** for every real `ε > 0`, there exist
sequences `B, C : ℕ → Set Ω` in `𝒜` such that `(⋂ n, C n) ⊆ X ⊆ (⋃ n, B n)` and
`ν* ((⋃ n, B n) \ (⋂ n, C n)) < ENNReal.ofReal ε`. -/
theorem isCaratheodoryMeasurable_iff_sigma_delta_approx {Ω : Type*} {𝒜 : Set (Set Ω)}
    {ν : Set Ω → ℝ≥0∞} (hAlg : IsSetAlgebra 𝒜) (hν : IsCountablyAdditiveMeasure 𝒜 ν)
    (hFin : ν Set.univ < ⊤) (X : Set Ω) :
    let m := caratheodoryOuter 𝒜 ν hν.isSetRing.empty_mem hν.map_empty
    m.IsCaratheodory X ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ B C : ℕ → Set Ω, (∀ n, B n ∈ 𝒜) ∧ (∀ n, C n ∈ 𝒜) ∧
          (⋂ n, C n) ⊆ X ∧ X ⊆ (⋃ n, B n) ∧
          m ((⋃ n, B n) \ (⋂ n, C n)) < ENNReal.ofReal ε := by
  intro m
  have hm_univ : m Set.univ < ⊤ := by
    rw [caratheodoryOuter_eq_of_mem hν hAlg.univ_mem]; exact hFin
  constructor
  · intro hX ε hε
    have hX_lt : m X < ⊤ := (m.mono (Set.subset_univ X)).trans_lt hm_univ
    have hXc_lt : m Xᶜ < ⊤ := (m.mono (Set.subset_univ Xᶜ)).trans_lt hm_univ
    have hpos2 : 0 < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 (half_pos hε)
    -- Outer cover `U = ⋃ n, B n` of `X`
    have hlt1 : m X < m X + ENNReal.ofReal (ε / 2) := ENNReal.lt_add_right hX_lt.ne hpos2.ne'
    conv_lhs at hlt1 => rw [caratheodoryOuter_eq_iInf]
    simp only [iInf_lt_iff, exists_prop] at hlt1
    obtain ⟨B, hB_mem, hXB, hB_sum⟩ := hlt1
    -- Outer cover `V = ⋃ n, D n` of `Xᶜ`, then complement `C n = (D n)ᶜ`
    have hlt2 : m Xᶜ < m Xᶜ + ENNReal.ofReal (ε / 2) := ENNReal.lt_add_right hXc_lt.ne hpos2.ne'
    conv_lhs at hlt2 => rw [caratheodoryOuter_eq_iInf]
    simp only [iInf_lt_iff, exists_prop] at hlt2
    obtain ⟨D, hD_mem, hXcD, hD_sum⟩ := hlt2
    let C : ℕ → Set Ω := fun n ↦ (D n)ᶜ
    have hC_mem : ∀ n, C n ∈ 𝒜 := fun n ↦ hAlg.compl_mem (hD_mem n)
    have hCX : (⋂ n, C n) ⊆ X := by
      intro x hx
      by_contra hxX
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 (hXcD hxX)
      exact Set.mem_iInter.1 hx n hxn
    refine ⟨B, C, hB_mem, hC_mem, hCX, hXB, ?_⟩
    set U := ⋃ n, B n
    set V := ⋃ n, D n
    set K := ⋂ n, C n
    have hK_eq : K = Vᶜ := by ext x; simp [K, V, C]
    -- `m (U \ X) < ofReal (ε / 2)`
    have hUX : m (U \ X) < ENNReal.ofReal (ε / 2) := by
      have hsplit := hX U
      rw [Set.inter_eq_self_of_subset_right hXB] at hsplit
      have hmU : m U < m X + ENNReal.ofReal (ε / 2) :=
        (MeasureTheory.measure_iUnion_le B).trans_lt <|
          lt_of_le_of_lt (ENNReal.tsum_le_tsum fun n ↦ caratheodoryOuter_le_of_mem _ _ (hB_mem n))
            hB_sum
      rw [hsplit] at hmU
      exact (ENNReal.add_lt_add_iff_left hX_lt.ne).1 hmU
    -- `m (X \ K) = m (V \ Xᶜ) < ofReal (ε / 2)`
    have hXK : m (X \ K) < ENNReal.ofReal (ε / 2) := by
      have hXK_eq : X \ K = V \ Xᶜ := by
        rw [hK_eq]; ext x; simp [and_comm]
      rw [hXK_eq]
      have hsplit := (m.isCaratheodory_compl hX) V
      rw [Set.inter_eq_self_of_subset_right hXcD] at hsplit
      have hmV : m V < m Xᶜ + ENNReal.ofReal (ε / 2) :=
        (MeasureTheory.measure_iUnion_le D).trans_lt <|
          lt_of_le_of_lt (ENNReal.tsum_le_tsum fun n ↦ caratheodoryOuter_le_of_mem _ _ (hD_mem n))
            hD_sum
      rw [hsplit] at hmV
      exact (ENNReal.add_lt_add_iff_left hXc_lt.ne).1 hmV
    have hUK_sub : U \ K ⊆ (U \ X) ∪ (X \ K) := by
      intro x ⟨hxU, hxK⟩
      by_cases hxX : x ∈ X
      · exact Or.inr ⟨hxX, hxK⟩
      · exact Or.inl ⟨hxU, hxX⟩
    have hsum_eps : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
    calc m (U \ K)
        ≤ m ((U \ X) ∪ (X \ K)) := m.mono hUK_sub
      _ ≤ m (U \ X) + m (X \ K) := MeasureTheory.measure_union_le _ _
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hUX hXK
      _ = ENNReal.ofReal ε := hsum_eps
  · intro hApprox
    have hSig := (isSigmaAlgebra_caratheodory m).1
    choose B C hB hC hCX hXB hlt using fun k : ℕ ↦
      hApprox (1 / ((k + 1 : ℕ) : ℝ)) (by positivity)
    let U : ℕ → Set Ω := fun k ↦ ⋃ n, B k n
    let K : ℕ → Set Ω := fun k ↦ ⋂ n, C k n
    have hU_car : ∀ k, m.IsCaratheodory (U k) := fun k ↦
      m.isCaratheodory_iUnion fun n ↦ isCaratheodoryMeasurable_of_mem hν.toIsFinitelyAdditive (hB k n)
    have hK_car : ∀ k, m.IsCaratheodory (K k) := fun k ↦
      hSig.toIsSigmaRing.iInter_mem fun n ↦
        isCaratheodoryMeasurable_of_mem hν.toIsFinitelyAdditive (hC k n)
    let U_inf : Set Ω := ⋂ k, U k
    let K_sup : Set Ω := ⋃ k, K k
    have hU_inf_car : m.IsCaratheodory U_inf := hSig.toIsSigmaRing.iInter_mem hU_car
    have hK_sup_car : m.IsCaratheodory K_sup := m.isCaratheodory_iUnion hK_car
    have hKX : K_sup ⊆ X := Set.iUnion_subset hCX
    have hXU : X ⊆ U_inf := Set.subset_iInter hXB
    have hNull : m (U_inf \ K_sup) = 0 := by
      apply le_antisymm _ zero_le
      refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
      rw [zero_add]
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (NNReal.coe_pos.2 hδ)
      have hsub : U_inf \ K_sup ⊆ U k \ K k :=
        Set.sdiff_subset_sdiff (Set.iInter_subset U k) (Set.subset_iUnion K k)
      calc m (U_inf \ K_sup)
          ≤ m (U k \ K k) := m.mono hsub
        _ ≤ ENNReal.ofReal (1 / ((k + 1 : ℕ) : ℝ)) := (hlt k).le
        _ ≤ (δ : ℝ≥0∞) := by
            rw [← ENNReal.ofReal_coe_nnreal]
            exact ENNReal.ofReal_le_ofReal (by push_cast; exact hk.le)
    exact (isCaratheodoryMeasurable_of_sandwich m hK_sup_car hU_inf_car hKX hXU hNull).1

/-! ## §16.4 Lebesgue Measure Facts on `ℝ` -/

/-- Goldblatt §16.4(1) (p. 210): Any Borel measure `μ` on `ℝ` agreeing with Lebesgue measure on all
open intervals `Set.Ioo a b` (or even just rational open intervals `Set.Ioo (p : ℝ) (q : ℝ)`) is
equal to `MeasureTheory.volume`! -/
theorem borel_measure_eq_volume_of_Ioo_rat (μ : MeasureTheory.Measure ℝ)
    (h : ∀ p q : ℚ, μ (Set.Ioo (p : ℝ) (q : ℝ)) = MeasureTheory.volume (Set.Ioo (p : ℝ) (q : ℝ))) :
    μ = MeasureTheory.volume :=
  (Real.measure_ext_Ioo_rat (μ := MeasureTheory.volume) (ν := μ) fun p q ↦ (h p q).symm).symm

/-- Goldblatt §16.4(1) (p. 210): Any Borel measure `μ` on `ℝ` assigning `ENNReal.ofReal (b - a)` to
every open interval `(a, b)` equals `MeasureTheory.volume`. -/
theorem borel_measure_eq_volume_of_Ioo (μ : MeasureTheory.Measure ℝ)
    (h : ∀ a b : ℝ, μ (Set.Ioo a b) = ENNReal.ofReal (b - a)) :
    μ = MeasureTheory.volume :=
  borel_measure_eq_volume_of_Ioo_rat μ fun p q ↦ by
    rw [h, Real.volume_Ioo]

/-- Goldblatt §16.4(2) (p. 210): A subset `B ⊆ ℝ` is **Lebesgue measurable**
(`NullMeasurableSet B volume`) if and only if there exist Borel sets `C, D ⊆ ℝ` such that
`C ⊆ B ⊆ D` and `volume (D \ C) = 0`; moreover `volume B = volume C = volume D`. -/
theorem nullMeasurableSet_volume_iff_borel_sandwich (B : Set ℝ) :
    MeasureTheory.NullMeasurableSet B MeasureTheory.volume ↔
      ∃ C D : Set ℝ, MeasurableSet C ∧ MeasurableSet D ∧ C ⊆ B ∧ B ⊆ D ∧
        MeasureTheory.volume (D \ C) = 0 := by
  constructor
  · intro hB
    obtain ⟨C, hCB, hCm, hCae⟩ := hB.exists_measurable_subset_ae_eq
    obtain ⟨D, hBD, hDm, hDae⟩ := hB.exists_measurable_superset_ae_eq
    have hCD_ae : C =ᵐ[MeasureTheory.volume] D := hCae.trans hDae.symm
    exact ⟨C, D, hCm, hDm, hCB, hBD, (MeasureTheory.ae_eq_set.1 hCD_ae).2⟩
  · rintro ⟨C, D, hCm, _, hCB, hBD, hNull⟩
    have hBC_zero : MeasureTheory.volume (B \ C) = 0 :=
      MeasureTheory.measure_mono_null (Set.sdiff_subset_sdiff_left hBD) hNull
    have hBC_eq : B = C ∪ (B \ C) := (Set.union_sdiff_cancel hCB).symm
    rw [hBC_eq]
    exact hCm.nullMeasurableSet.union (MeasureTheory.NullMeasurableSet.of_null hBC_zero)

/-- Helper for Goldblatt §16.4(3): every Lebesgue measurable set `E ⊆ ℝ` can be approximated from
outside by an open superset `U ⊇ E` with `volume (U \ E) < ENNReal.ofReal δ`. -/
theorem exists_isOpen_superset_sdiff_lt_of_nullMeasurable {E : Set ℝ}
    (hE : MeasureTheory.NullMeasurableSet E MeasureTheory.volume) {δ : ℝ} (hδ : 0 < δ) :
    ∃ U : Set ℝ, E ⊆ U ∧ IsOpen U ∧
      MeasureTheory.volume (U \ E) < ENNReal.ofReal δ := by
  have hδ_pos : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.2 hδ
  obtain ⟨ε, hε_pos, hε_sum⟩ := ENNReal.exists_pos_sum_of_countable' hδ_pos.ne' ℕ
  let I : ℕ → Set ℝ := fun n ↦ Set.Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1)
  let En : ℕ → Set ℝ := fun n ↦ E ∩ I n
  have hEn_nm : ∀ n, MeasureTheory.NullMeasurableSet (En n) MeasureTheory.volume :=
    fun n ↦ hE.inter isOpen_Ioo.measurableSet.nullMeasurableSet
  have hEn_fin : ∀ n, MeasureTheory.volume (En n) ≠ ⊤ := fun n ↦ by
    refine ((MeasureTheory.measure_mono Set.inter_subset_right).trans_lt ?_).ne
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  choose U hEnU hUo hU_lt using fun n ↦
    (En n).exists_isOpen_lt_add (hEn_fin n) (hε_pos n).ne'
  refine ⟨⋃ n, U n, ?_, isOpen_iUnion hUo, ?_⟩
  · intro x hxE
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    obtain ⟨hl, hr⟩ := abs_lt.1 hn
    have hxI : x ∈ I n := ⟨by linarith, by linarith⟩
    exact Set.mem_iUnion.2 ⟨n, hEnU n ⟨hxE, hxI⟩⟩
  · have hsub : (⋃ n, U n) \ E ⊆ ⋃ n, (U n \ En n) := by
      rintro x ⟨hxU, hxE⟩
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hxU
      exact Set.mem_iUnion.2 ⟨n, hxn, fun h ↦ hxE h.1⟩
    calc MeasureTheory.volume ((⋃ n, U n) \ E)
        ≤ MeasureTheory.volume (⋃ n, (U n \ En n)) := MeasureTheory.measure_mono hsub
      _ ≤ ∑' n, MeasureTheory.volume (U n \ En n) := MeasureTheory.measure_iUnion_le _
      _ ≤ ∑' n, ε n := ENNReal.tsum_le_tsum fun n ↦ by
          rw [MeasureTheory.measure_sdiff (hEnU n) (hEn_nm n) (hEn_fin n)]
          exact tsub_le_iff_right.2 ((hU_lt n).le.trans_eq (add_comm _ _))
      _ < ENNReal.ofReal δ := hε_sum

/-- Goldblatt §16.4(3) (p. 210): A subset `B ⊆ ℝ` is **Lebesgue measurable**
(`NullMeasurableSet B volume`) **if and only if** for every real `ε > 0` there exist a closed set
`C` and an open set `D` such that `C ⊆ B ⊆ D` and `volume (D \ C) < ENNReal.ofReal ε`! -/
theorem nullMeasurableSet_volume_iff_closed_open_approx (B : Set ℝ) :
    MeasureTheory.NullMeasurableSet B MeasureTheory.volume ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ C D : Set ℝ, IsClosed C ∧ IsOpen D ∧ C ⊆ B ∧ B ⊆ D ∧
          MeasureTheory.volume (D \ C) < ENNReal.ofReal ε := by
  constructor
  · intro hB ε hε
    obtain ⟨D, hBD, hDo, hDB⟩ :=
      exists_isOpen_superset_sdiff_lt_of_nullMeasurable hB (half_pos hε)
    obtain ⟨V, hBcV, hVo, hVBc⟩ :=
      exists_isOpen_superset_sdiff_lt_of_nullMeasurable hB.compl (half_pos hε)
    refine ⟨Vᶜ, D, hVo.isClosed_compl, hDo, Set.compl_subset_comm.1 hBcV, hBD, ?_⟩
    have hBC_eq : B \ Vᶜ = V \ Bᶜ := by ext x; simp [and_comm]
    have hDC_sub : D \ Vᶜ ⊆ (D \ B) ∪ (B \ Vᶜ) := by
      intro x ⟨hxD, hxVc⟩
      by_cases hxB : x ∈ B
      · exact Or.inr ⟨hxB, hxVc⟩
      · exact Or.inl ⟨hxD, hxB⟩
    have hsum_eps : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
    calc MeasureTheory.volume (D \ Vᶜ)
        ≤ MeasureTheory.volume ((D \ B) ∪ (B \ Vᶜ)) := MeasureTheory.measure_mono hDC_sub
      _ ≤ MeasureTheory.volume (D \ B) + MeasureTheory.volume (B \ Vᶜ) :=
          MeasureTheory.measure_union_le _ _
      _ = MeasureTheory.volume (D \ B) + MeasureTheory.volume (V \ Bᶜ) := by rw [hBC_eq]
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hDB hVBc
      _ = ENNReal.ofReal ε := hsum_eps
  · intro hApprox
    rw [nullMeasurableSet_volume_iff_borel_sandwich]
    choose C D hCc hDo hCB hBD hlt using fun k : ℕ ↦
      hApprox (1 / ((k : ℝ) + 1)) (by positivity)
    let C_sup : Set ℝ := ⋃ k, C k
    let D_inf : Set ℝ := ⋂ k, D k
    have hCm : MeasurableSet C_sup := MeasurableSet.iUnion fun k ↦ (hCc k).measurableSet
    have hDm : MeasurableSet D_inf := MeasurableSet.iInter fun k ↦ (hDo k).measurableSet
    refine ⟨C_sup, D_inf, hCm, hDm, Set.iUnion_subset hCB, Set.subset_iInter hBD, ?_⟩
    apply le_antisymm _ zero_le
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
    rw [zero_add]
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (NNReal.coe_pos.2 hδ)
    have hsub : D_inf \ C_sup ⊆ D k \ C k :=
      Set.sdiff_subset_sdiff (Set.iInter_subset D k) (Set.subset_iUnion C k)
    calc MeasureTheory.volume (D_inf \ C_sup)
        ≤ MeasureTheory.volume (D k \ C k) := MeasureTheory.measure_mono hsub
      _ ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) := (hlt k).le
      _ ≤ (δ : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal hk.le

/-! ## §16.5–16.7 Internal Measure Rings/Algebras, Peter Loeb's Theorem, and Approximability -/

/-- Goldblatt §16.5 (p. 210): Conversion of a (nonnegative) hyperreal `x ∈ ℝ*` to `ℝ≥0∞`:
`ENNReal.ofReal (shadow x)` if `x` is limited, and `⊤` (`+∞`) if `x` is unlimited. -/
def hyperrealToENNReal (x : ℝ*) : ℝ≥0∞ :=
  if IsLimited x then ENNReal.ofReal (shadow x) else ⊤

/-- When `x` is limited, `hyperrealToENNReal x = ENNReal.ofReal (shadow x)`. -/
theorem hyperrealToENNReal_of_isLimited {x : ℝ*} (hx : IsLimited x) :
    hyperrealToENNReal x = ENNReal.ofReal (shadow x) := by
  simp [hyperrealToENNReal, hx]

/-- When `x` is not limited, `hyperrealToENNReal x = ⊤`. -/
theorem hyperrealToENNReal_of_not_isLimited {x : ℝ*} (hx : ¬ IsLimited x) :
    hyperrealToENNReal x = ⊤ := by
  simp [hyperrealToENNReal, hx]

/-- When `x` is positive unlimited, `hyperrealToENNReal x = ⊤`. -/
theorem hyperrealToENNReal_of_isPosUnlimited {x : ℝ*} (hx : IsPosUnlimited x) :
    hyperrealToENNReal x = ⊤ :=
  hyperrealToENNReal_of_not_isLimited
    (isUnlimited_iff_not_isLimited.1 (isUnlimited_iff_pos_or_neg.2 (Or.inl hx)))

/-- `hyperrealToENNReal 0 = 0`. -/
@[simp]
theorem hyperrealToENNReal_zero : hyperrealToENNReal 0 = 0 := by
  have h0 : IsLimited (0 : ℝ*) := by simpa using isLimited_coe 0
  simp [hyperrealToENNReal, h0, shadow_zero]

/-- `hyperrealToENNReal (r : ℝ*) = ENNReal.ofReal r`. -/
@[simp]
theorem hyperrealToENNReal_coe (r : ℝ) :
    hyperrealToENNReal (r : ℝ*) = ENNReal.ofReal r := by
  simp [hyperrealToENNReal, isLimited_coe r, shadow_coe]

/-- `hyperrealToENNReal x < ⊤ ↔ IsLimited x`. -/
theorem hyperrealToENNReal_lt_top_iff {x : ℝ*} :
    hyperrealToENNReal x < ⊤ ↔ IsLimited x := by
  by_cases hx : IsLimited x <;> simp [hyperrealToENNReal, hx]

/-- If `0 ≤ x ≤ y` and `y` is limited, then `x` is limited. -/
theorem isLimited_of_nonneg_le {x y : ℝ*} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy : IsLimited y) :
    IsLimited x :=
  isLimited_of_abs_le hy (by rw [abs_of_nonneg hx0, abs_of_nonneg (hx0.trans hxy)]; exact hxy)

/-- Nonnegative limited hyperreals have nonnegative shadow. -/
theorem shadow_nonneg_of_nonneg {x : ℝ*} (hx : IsLimited x) (hx0 : 0 ≤ x) :
    0 ≤ shadow x := by
  have h0 : IsLimited (0 : ℝ*) := by simpa using isLimited_coe 0
  simpa [shadow_zero] using shadow_le_of_le h0 hx hx0

/-- Additivity of `hyperrealToENNReal` on nonnegative hyperreals:
`hyperrealToENNReal (x + y) = hyperrealToENNReal x + hyperrealToENNReal y`. -/
theorem hyperrealToENNReal_add {x y : ℝ*} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) :
    hyperrealToENNReal (x + y) = hyperrealToENNReal x + hyperrealToENNReal y := by
  by_cases hx : IsLimited x
  · by_cases hy : IsLimited y
    · have hxy : IsLimited (x + y) := hx.add hy
      rw [hyperrealToENNReal_of_isLimited hxy, hyperrealToENNReal_of_isLimited hx,
        hyperrealToENNReal_of_isLimited hy, shadow_add hx hy,
        ENNReal.ofReal_add (shadow_nonneg_of_nonneg hx hx0) (shadow_nonneg_of_nonneg hy hy0)]
    · have hnot : ¬ IsLimited (x + y) :=
        fun hxy ↦ hy (isLimited_of_nonneg_le hy0 (le_add_of_nonneg_left hx0) hxy)
      simp [hyperrealToENNReal_of_not_isLimited hnot, hyperrealToENNReal_of_not_isLimited hy]
  · have hnot : ¬ IsLimited (x + y) :=
      fun hxy ↦ hx (isLimited_of_nonneg_le hx0 (le_add_of_nonneg_right hy0) hxy)
    simp [hyperrealToENNReal_of_not_isLimited hnot, hyperrealToENNReal_of_not_isLimited hx]

/-- Monotonicity of `hyperrealToENNReal` on nonnegative hyperreals. -/
theorem hyperrealToENNReal_mono {x y : ℝ*} (hx0 : 0 ≤ x) (hxy : x ≤ y) :
    hyperrealToENNReal x ≤ hyperrealToENNReal y := by
  by_cases hy : IsLimited y
  · have hx : IsLimited x := isLimited_of_nonneg_le hx0 hxy hy
    rw [hyperrealToENNReal_of_isLimited hx, hyperrealToENNReal_of_isLimited hy]
    exact ENNReal.ofReal_le_ofReal (shadow_le_of_le hx hy hxy)
  · rw [hyperrealToENNReal_of_not_isLimited hy]
    exact le_top

/-- If `0 ≤ x` and `hyperrealToENNReal x < ENNReal.ofReal r`, then `IsLimited x`, `shadow x < r`,
and `x < (r : ℝ*)`. -/
theorem lt_coe_of_hyperrealToENNReal_lt_ofReal {x : ℝ*} {r : ℝ} (_hx0 : 0 ≤ x)
    (hlt : hyperrealToENNReal x < ENNReal.ofReal r) :
    IsLimited x ∧ shadow x < r ∧ x < (r : ℝ*) := by
  have hx : IsLimited x :=
    hyperrealToENNReal_lt_top_iff.1 (hlt.trans_le ENNReal.ofReal_lt_top.le)
  rw [hyperrealToENNReal_of_isLimited hx] at hlt
  have hr_pos : 0 < r := by
    by_contra hr_le
    push Not at hr_le
    simp [ENNReal.ofReal_of_nonpos hr_le] at hlt
  have hsh : shadow x < r := (ENNReal.ofReal_lt_ofReal_iff hr_pos).1 hlt
  refine ⟨hx, hsh, ?_⟩
  have hinf : IsInfinitesimal (x - (shadow x : ℝ*)) := infClose_shadow hx
  have hbd := abs_lt.1 (hinf (r - shadow x) (sub_pos.2 hsh))
  have hcast : (r : ℝ*) = (shadow x : ℝ*) + ((r - shadow x : ℝ) : ℝ*) := by
    exact_mod_cast (add_sub_cancel (shadow x) r).symm
  linarith [hbd.2, hcast]

/-- Goldblatt §16.5 (p. 210): The **Loeb premeasure** `(st ∘ μ)(A)` associated to an internal
measure `μ : Set Ω → ℝ*`. -/
def loebPremeasure {Ω : Type*} (μ : Set Ω → ℝ*) (A : Set Ω) : ℝ≥0∞ :=
  hyperrealToENNReal (μ A)

/-- Goldblatt §16.2 & §16.5 (pp. 207, 210–213): An **internal measure ring** `(𝒜, μ)` on `Ω`:
`𝒜` is a ring of subsets of `Ω`, `μ : Set Ω → ℝ*` is a nonnegative finitely additive hyperreal
measure on `𝒜`, and `(𝒜, μ)` satisfies Countable Saturation for countable unions in `𝒜` together
with the two sequential comprehensiveness / overflow principles used in Goldblatt §§16.5–16.6. -/
structure InternalMeasureRing (Ω : Type*) where
  /-- Ring of internal measurable sets. -/
  𝒜 : Set (Set Ω)
  /-- `𝒜` is a ring of sets. -/
  isSetRing : IsSetRing 𝒜
  /-- Internal hyperreal finitely additive measure `μ : Set Ω → ℝ*`. -/
  μ : Set Ω → ℝ*
  /-- `μ ∅ = 0`. -/
  map_empty : μ ∅ = 0
  /-- Nonnegativity `0 ≤ μ A` on `𝒜`. -/
  nonneg : ∀ ⦃A : Set Ω⦄, A ∈ 𝒜 → 0 ≤ μ A
  /-- Binary disjoint additivity in `ℝ*`. -/
  map_union_disjoint : ∀ ⦃A B : Set Ω⦄, A ∈ 𝒜 → B ∈ 𝒜 → Disjoint A B → μ (A ∪ B) = μ A + μ B
  /-- **Countable Saturation for unions** (Goldblatt §16.5, p. 210): any countable union of sets in
  `𝒜` that belongs to `𝒜` equals a finite subunion. -/
  iUnion_mem_finite : ∀ ⦃A : ℕ → Set Ω⦄, (∀ n, A n ∈ 𝒜) → (⋃ n, A n) ∈ 𝒜 →
    ∃ k : ℕ, (⋃ n, A n) = ⋃ n ≤ k, A n
  /-- **Overflow for increasing sequences** (Goldblatt Lemma 16.5.1, p. 211): any increasing
  sequence in `𝒜` with `μ (A_n) < r` (`r ∈ ℝ`) is contained in a single `B ∈ 𝒜` with `μ B < r`. -/
  overflow_upper : ∀ ⦃A : ℕ → Set Ω⦄ {r : ℝ}, (∀ n, A n ∈ 𝒜) → Monotone A →
    (∀ n, μ (A n) < (r : ℝ*)) → ∃ B ∈ 𝒜, (∀ n, A n ⊆ B) ∧ μ B < (r : ℝ*)
  /-- **Overflow for nested sequences** (Goldblatt Lemma 16.6.2, p. 213): any increasing `C_n ∈ 𝒜`
  and decreasing `D_n ∈ 𝒜` with `C_n ⊆ D_n` have an interpolant `A ∈ 𝒜` with `C_n ⊆ A ⊆ D_n` for
  all `n`. -/
  overflow_nested : ∀ ⦃C D : ℕ → Set Ω⦄, (∀ n, C n ∈ 𝒜) → (∀ n, D n ∈ 𝒜) →
    Monotone C → Antitone D → (∀ n, C n ⊆ D n) → ∃ A ∈ 𝒜, ∀ n, C n ⊆ A ∧ A ⊆ D n

/-- Goldblatt §16.5 (p. 210): An **internal measure algebra** `(𝒜, μ)` on `Ω` is an
`InternalMeasureRing` with `Set.univ ∈ 𝒜` (so `𝒜` is an algebra of sets on `Ω`). -/
structure InternalMeasureAlgebra (Ω : Type*) extends InternalMeasureRing Ω where
  /-- Whole space `Ω` belongs to `𝒜`. -/
  univ_mem : (Set.univ : Set Ω) ∈ 𝒜

/-- `M.𝒜` is an algebra of sets for any `InternalMeasureAlgebra`. -/
theorem InternalMeasureAlgebra.isSetAlgebra {Ω : Type*} (M : InternalMeasureAlgebra Ω) :
    IsSetAlgebra M.𝒜 :=
  ⟨M.isSetRing, M.univ_mem⟩

/-- Monotonicity of the internal measure `M.μ` on `M.𝒜`. -/
theorem InternalMeasureRing.mu_mono {Ω : Type*} (M : InternalMeasureRing Ω)
    {A B : Set Ω} (hA : A ∈ M.𝒜) (hB : B ∈ M.𝒜) (hAB : A ⊆ B) :
    M.μ A ≤ M.μ B := by
  have heq : B = A ∪ (B \ A) := (Set.union_sdiff_cancel hAB).symm
  rw [heq, M.map_union_disjoint hA (M.isSetRing.sdiff_mem hB hA) disjoint_sdiff_self_right]
  linarith [M.nonneg (M.isSetRing.sdiff_mem hB hA)]

/-- Subtractivity `M.μ (B \ A) = M.μ B - M.μ A` for `A ⊆ B` in `M.𝒜`. -/
theorem InternalMeasureRing.mu_sdiff {Ω : Type*} (M : InternalMeasureRing Ω)
    {A B : Set Ω} (hA : A ∈ M.𝒜) (hB : B ∈ M.𝒜) (hAB : A ⊆ B) :
    M.μ (B \ A) = M.μ B - M.μ A := by
  have heq : B = A ∪ (B \ A) := (Set.union_sdiff_cancel hAB).symm
  have h := M.map_union_disjoint hA (M.isSetRing.sdiff_mem hB hA) disjoint_sdiff_self_right
  rw [← heq] at h
  linarith

/-- Finite additivity of `loebPremeasure M.μ` on `M.𝒜`. -/
theorem InternalMeasureRing.loebPremeasure_isFinitelyAdditive {Ω : Type*}
    (M : InternalMeasureRing Ω) :
    IsFinitelyAdditiveMeasure M.𝒜 (loebPremeasure M.μ) where
  isSetRing := M.isSetRing
  map_empty := by simp [loebPremeasure, M.map_empty]
  map_union_disjoint := fun A B hA hB hdisj ↦ by
    simp only [loebPremeasure]
    rw [M.map_union_disjoint hA hB hdisj, hyperrealToENNReal_add (M.nonneg hA) (M.nonneg hB)]

/-- Goldblatt §16.5 (pp. 210–211, **Peter Loeb's Theorem, Part 1**):
On any internal measure ring `M`, the Loeb premeasure `loebPremeasure M.μ` is **countably additive**
on `M.𝒜`! -/
theorem InternalMeasureRing.loebPremeasure_isCountablyAdditive {Ω : Type*}
    (M : InternalMeasureRing Ω) :
    IsCountablyAdditiveMeasure M.𝒜 (loebPremeasure M.μ) where
  isSetRing := M.isSetRing
  map_empty := M.loebPremeasure_isFinitelyAdditive.map_empty
  map_iUnion_disjoint := fun A hA hDisj hU ↦ by
    obtain ⟨k, hk⟩ := M.iUnion_mem_finite hA hU
    -- Every `A m` with `m > k` must be empty because `A m ⊆ ⋃ n ≤ k, A n` and `A` is disjoint!
    have hEmpty_gt : ∀ m : ℕ, k < m → A m = ∅ := by
      intro m hkm
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hxm
      have hxU : x ∈ ⋃ n, A n := Set.mem_iUnion.2 ⟨m, hxm⟩
      rw [hk] at hxU
      obtain ⟨n, hnk, hxn⟩ := Set.mem_iUnion₂.1 hxU
      exact Set.disjoint_left.1 (hDisj (by omega : m ≠ n)) hxm hxn
    have hU_range : (⋃ n, A n) = ⋃ n ∈ Finset.range (k + 1), A n := by
      rw [hk]
      ext x
      simp [Finset.mem_range]
    rw [hU_range, M.loebPremeasure_isFinitelyAdditive.sum_biUnion_finset
      (Finset.range (k + 1)) (fun n _ ↦ hA n) (fun i _ j _ hij ↦ hDisj hij)]
    symm
    refine tsum_eq_sum fun m hm ↦ ?_
    have hkm : k < m := by
      simp only [Finset.mem_range, not_lt] at hm
      omega
    rw [hEmpty_gt m hkm, M.loebPremeasure_isFinitelyAdditive.map_empty]

/-- Goldblatt §16.5 (p. 211): The **Loeb outer measure** `(μ_L)*` on `Ω`. -/
def InternalMeasureRing.loebOuterMeasure {Ω : Type*} (M : InternalMeasureRing Ω) :
    MeasureTheory.OuterMeasure Ω :=
  caratheodoryOuter M.𝒜 (loebPremeasure M.μ)
    M.isSetRing.empty_mem M.loebPremeasure_isFinitelyAdditive.map_empty

/-- Goldblatt §16.5 (p. 211): The **Loeb measurable space** on `Ω` (the Carathéodory σ-algebra of
`M.loebOuterMeasure`). -/
abbrev InternalMeasureRing.loebMeasurableSpace {Ω : Type*} (M : InternalMeasureRing Ω) :
    MeasurableSpace Ω :=
  M.loebOuterMeasure.caratheodory

/-- Goldblatt §16.5 (p. 211): Predicate `M.IsLoebMeasurable B` asserting that `B ⊆ Ω` belongs to
the Loeb σ-algebra `ℒ(𝒜, μ)`. -/
def InternalMeasureRing.IsLoebMeasurable {Ω : Type*} (M : InternalMeasureRing Ω) (B : Set Ω) :
    Prop :=
  M.loebOuterMeasure.IsCaratheodory B

/-- Goldblatt §16.5 (p. 211, **Peter Loeb's Theorem, Part 2**): The **Loeb measure** `μ_L` on the
complete Loeb σ-algebra `M.loebMeasurableSpace`. -/
def InternalMeasureRing.loebMeasure {Ω : Type*} (M : InternalMeasureRing Ω) :
    @MeasureTheory.Measure Ω M.loebMeasurableSpace :=
  caratheodoryExtensionMeasure M.loebPremeasure_isCountablyAdditive

/-- Goldblatt §16.5 (p. 211, **Loeb Measure Properties**):
1. `M.loebMeasure` is a **complete** σ-additive measure on `M.loebMeasurableSpace`;
2. `M.loebMeasure B = M.loebOuterMeasure B` for every Loeb measurable set `B`;
3. Every `A ∈ M.𝒜` is Loeb measurable with `M.loebMeasure A = loebPremeasure M.μ A` (i.e.,
   `ENNReal.ofReal (shadow (M.μ A))` when `M.μ A` is limited, and `⊤` when `M.μ A` is unlimited). -/
theorem InternalMeasureRing.loebMeasure_properties {Ω : Type*} (M : InternalMeasureRing Ω) :
    @MeasureTheory.Measure.IsComplete Ω M.loebMeasurableSpace M.loebMeasure ∧
    (∀ ⦃B : Set Ω⦄, M.IsLoebMeasurable B → M.loebMeasure B = M.loebOuterMeasure B) ∧
    (∀ ⦃A : Set Ω⦄, A ∈ M.𝒜 →
      M.IsLoebMeasurable A ∧ M.loebMeasure A = loebPremeasure M.μ A) :=
  caratheodoryExtensionMeasure_properties M.loebPremeasure_isCountablyAdditive

/-- Agreement of `M.loebOuterMeasure` with `loebPremeasure M.μ` on `M.𝒜`. -/
theorem InternalMeasureRing.loebOuterMeasure_eq_of_mem {Ω : Type*} (M : InternalMeasureRing Ω)
    {A : Set Ω} (hA : A ∈ M.𝒜) :
    M.loebOuterMeasure A = loebPremeasure M.μ A :=
  caratheodoryOuter_eq_of_mem M.loebPremeasure_isCountablyAdditive hA

/-- Goldblatt §16.5, **Lemma 16.5.1** (p. 211):
On any internal measure ring `M`, the Loeb outer measure of **every** subset `X ⊆ Ω` is the infimum
over **single** covering sets `A ∈ M.𝒜` (no countable covers needed!):
`M.loebOuterMeasure X = ⨅ (A ∈ M.𝒜) (_ : X ⊆ A), loebPremeasure M.μ A`. -/
theorem InternalMeasureRing.loebOuterMeasure_eq_iInf {Ω : Type*} (M : InternalMeasureRing Ω)
    (X : Set Ω) :
    M.loebOuterMeasure X = ⨅ (A ∈ M.𝒜) (_ : X ⊆ A), loebPremeasure M.μ A := by
  apply le_antisymm
  · refine le_iInf fun A ↦ le_iInf fun hA ↦ le_iInf fun hXA ↦ ?_
    exact (M.loebOuterMeasure.mono hXA).trans_eq (M.loebOuterMeasure_eq_of_mem hA)
  · rcases eq_or_lt_of_le (le_top : M.loebOuterMeasure X ≤ ⊤) with htop | hlt
    · rw [htop]; exact le_top
    · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
      have hε_real : 0 < (ε : ℝ) := NNReal.coe_pos.2 hε
      obtain ⟨C, hC_mem, hC_mono, hXC, hC_sup⟩ :=
        caratheodoryOuter_exists_monotone_cover_lt M.loebPremeasure_isFinitelyAdditive hlt hε_real
      set s : ℝ := (M.loebOuterMeasure X).toReal
      have hs_eq : ENNReal.ofReal s = M.loebOuterMeasure X :=
        ENNReal.ofReal_toReal hlt.ne
      have hrhs_eq : M.loebOuterMeasure X + ENNReal.ofReal (ε : ℝ) =
          ENNReal.ofReal (s + (ε : ℝ)) := by
        rw [← hs_eq, ENNReal.ofReal_add ENNReal.toReal_nonneg hε_real.le]
      have hC_lt : ∀ n : ℕ, M.μ (C n) < ((s + (ε : ℝ) : ℝ) : ℝ*) := by
        intro n
        have hn_lt : loebPremeasure M.μ (C n) < ENNReal.ofReal (s + (ε : ℝ)) :=
          (le_iSup (fun k ↦ loebPremeasure M.μ (C k)) n).trans_lt (hrhs_eq ▸ hC_sup)
        exact (lt_coe_of_hyperrealToENNReal_lt_ofReal (M.nonneg (hC_mem n)) hn_lt).2.2
      obtain ⟨B, hB_mem, hCB, hB_lt⟩ := M.overflow_upper hC_mem hC_mono hC_lt
      have hXB : X ⊆ B := hXC.trans (Set.iUnion_subset hCB)
      have hB_le : loebPremeasure M.μ B ≤ M.loebOuterMeasure X + (ε : ℝ≥0∞) := by
        calc loebPremeasure M.μ B
            ≤ hyperrealToENNReal ((s + (ε : ℝ) : ℝ) : ℝ*) :=
              hyperrealToENNReal_mono (M.nonneg hB_mem) hB_lt.le
          _ = ENNReal.ofReal (s + (ε : ℝ)) := hyperrealToENNReal_coe _
          _ = M.loebOuterMeasure X + ENNReal.ofReal (ε : ℝ) := hrhs_eq.symm
          _ = M.loebOuterMeasure X + (ε : ℝ≥0∞) := by rw [ENNReal.ofReal_coe_nnreal]
      exact (iInf₂_le B hB_mem).trans ((iInf_le _ hXB).trans hB_le)

/-- Goldblatt §16.5, **Lemma 16.5.1** for Loeb measurable sets (p. 211):
For every Loeb measurable set `B`, `M.loebMeasure B = ⨅ (A ∈ M.𝒜) (_ : B ⊆ A), loebPremeasure M.μ A`. -/
theorem InternalMeasureRing.loebMeasure_eq_iInf {Ω : Type*} (M : InternalMeasureRing Ω)
    {B : Set Ω} (hB : M.IsLoebMeasurable B) :
    M.loebMeasure B = ⨅ (A ∈ M.𝒜) (_ : B ⊆ A), loebPremeasure M.μ A :=
  (M.loebMeasure_properties.2.1 hB).trans (M.loebOuterMeasure_eq_iInf B)

/-- Goldblatt §16.6 (p. 212): A subset `B ⊆ Ω` is **`μ`-approximable** if for every real `ε > 0`
there exist `C, D ∈ M.𝒜` with `C ⊆ B ⊆ D` and `loebPremeasure M.μ (D \ C) < ENNReal.ofReal ε`. -/
def InternalMeasureRing.IsMuApproximable {Ω : Type*} (M : InternalMeasureRing Ω) (B : Set Ω) :
    Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C ∈ M.𝒜, ∃ D ∈ M.𝒜, C ⊆ B ∧ B ⊆ D ∧
      loebPremeasure M.μ (D \ C) < ENNReal.ofReal ε

/-- Equivalence of `M.IsMuApproximable B` with internal hyperreal inequality `M.μ (D \ C) < (ε : ℝ*)`
and with `IsLimited (M.μ (D \ C)) ∧ shadow (M.μ (D \ C)) < ε` (Goldblatt §16.6, p. 212). -/
theorem InternalMeasureRing.isMuApproximable_iff_hyperreal {Ω : Type*} (M : InternalMeasureRing Ω)
    (B : Set Ω) :
    (M.IsMuApproximable B ↔
      ∀ ε : ℝ, 0 < ε → ∃ C ∈ M.𝒜, ∃ D ∈ M.𝒜, C ⊆ B ∧ B ⊆ D ∧ M.μ (D \ C) < (ε : ℝ*)) ∧
    (M.IsMuApproximable B ↔
      ∀ ε : ℝ, 0 < ε → ∃ C ∈ M.𝒜, ∃ D ∈ M.𝒜, C ⊆ B ∧ B ⊆ D ∧
        IsLimited (M.μ (D \ C)) ∧ shadow (M.μ (D \ C)) < ε) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h ε hε
    obtain ⟨C, hC, D, hD, hCB, hBD, hlt⟩ := h ε hε
    exact ⟨C, hC, D, hD, hCB, hBD,
      (lt_coe_of_hyperrealToENNReal_lt_ofReal (M.nonneg (M.isSetRing.sdiff_mem hD hC)) hlt).2.2⟩
  · intro h ε hε
    obtain ⟨C, hC, D, hD, hCB, hBD, hlt⟩ := h (ε / 2) (half_pos hε)
    refine ⟨C, hC, D, hD, hCB, hBD, ?_⟩
    calc loebPremeasure M.μ (D \ C)
        ≤ hyperrealToENNReal ((ε / 2 : ℝ) : ℝ*) :=
          hyperrealToENNReal_mono (M.nonneg (M.isSetRing.sdiff_mem hD hC)) hlt.le
      _ = ENNReal.ofReal (ε / 2) := hyperrealToENNReal_coe _
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (half_lt_self hε)
  · intro h ε hε
    obtain ⟨C, hC, D, hD, hCB, hBD, hlt⟩ := h ε hε
    obtain ⟨hLim, hSh, _⟩ :=
      lt_coe_of_hyperrealToENNReal_lt_ofReal (M.nonneg (M.isSetRing.sdiff_mem hD hC)) hlt
    exact ⟨C, hC, D, hD, hCB, hBD, hLim, hSh⟩
  · intro h ε hε
    obtain ⟨C, hC, D, hD, hCB, hBD, hLim, hSh⟩ := h ε hε
    refine ⟨C, hC, D, hD, hCB, hBD, ?_⟩
    rw [loebPremeasure, hyperrealToENNReal_of_isLimited hLim]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hSh

/-- Goldblatt §16.6, **Lemma 16.6.1** (p. 212):
Every Loeb measurable set `B` of finite Loeb measure (`M.loebOuterMeasure B < ⊤`) is
`μ`-approximable! -/
theorem InternalMeasureRing.isMuApproximable_of_isLoebMeasurable_of_lt_top {Ω : Type*}
    (M : InternalMeasureRing Ω) {B : Set Ω}
    (hB : M.IsLoebMeasurable B) (hFin : M.loebOuterMeasure B < ⊤) :
    M.IsMuApproximable B := by
  intro ε hε
  set m := M.loebOuterMeasure
  have hpos2 : 0 < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 (half_pos hε)
  -- Step 1: Outer single-set approximation `B ⊆ D` with `ν_L D < m B + ofReal (ε / 2)`.
  have hlt1 : m B < m B + ENNReal.ofReal (ε / 2) := ENNReal.lt_add_right hFin.ne hpos2.ne'
  conv_lhs at hlt1 => rw [M.loebOuterMeasure_eq_iInf B]
  simp only [iInf_lt_iff, exists_prop] at hlt1
  obtain ⟨D, hD_mem, hBD, hD_lt⟩ := hlt1
  -- Step 2: Carathéodory splitting of `D` by `B` gives `m (D \ B) < ofReal (ε / 2)`.
  have hDB_lt : m (D \ B) < ENNReal.ofReal (ε / 2) := by
    have hsplit := hB D
    rw [Set.inter_eq_self_of_subset_right hBD, M.loebOuterMeasure_eq_of_mem hD_mem] at hsplit
    rw [hsplit] at hD_lt
    exact (ENNReal.add_lt_add_iff_left hFin.ne).1 hD_lt
  -- Step 3: Outer single-set approximation `D \ B ⊆ E` with `ν_L E < m (D \ B) + ofReal (ε / 2)`.
  have hDB_fin : m (D \ B) < ⊤ := hDB_lt.trans_le ENNReal.ofReal_lt_top.le
  have hlt2 : m (D \ B) < m (D \ B) + ENNReal.ofReal (ε / 2) :=
    ENNReal.lt_add_right hDB_fin.ne hpos2.ne'
  conv_lhs at hlt2 => rw [M.loebOuterMeasure_eq_iInf (D \ B)]
  simp only [iInf_lt_iff, exists_prop] at hlt2
  obtain ⟨E, hE_mem, hDBE, hE_lt⟩ := hlt2
  -- Step 4: Set `C = D \ E ∈ M.𝒜`. Then `C ⊆ B ⊆ D` and `D \ C ⊆ E`.
  let C : Set Ω := D \ E
  have hC_mem : C ∈ M.𝒜 := M.isSetRing.sdiff_mem hD_mem hE_mem
  have hCB : C ⊆ B := by
    intro x ⟨hxD, hxE⟩
    by_contra hxB
    exact hxE (hDBE ⟨hxD, hxB⟩)
  have hDC_sub : D \ C ⊆ E := fun x ⟨_, hxC⟩ ↦ by
    by_contra hxE
    exact hxC ⟨‹x ∈ D›, hxE⟩
  have hsum_eps : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
  refine ⟨C, hC_mem, D, hD_mem, hCB, hBD, ?_⟩
  calc loebPremeasure M.μ (D \ C)
      ≤ loebPremeasure M.μ E :=
        M.loebPremeasure_isFinitelyAdditive.mono
          (M.isSetRing.sdiff_mem hD_mem hC_mem) hE_mem hDC_sub
    _ < m (D \ B) + ENNReal.ofReal (ε / 2) := hE_lt
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hDB_lt
    _ = ENNReal.ofReal ε := hsum_eps

/-- Goldblatt §16.5, **Lemma 16.5.2** (p. 212):
For every Loeb measurable set `B` with `M.loebOuterMeasure B < ⊤`, the Loeb measure of `B` is the
supremum over **single** inner sets `A ∈ M.𝒜` (`A ⊆ B`):
`M.loebMeasure B = ⨆ (A ∈ M.𝒜) (_ : A ⊆ B), loebPremeasure M.μ A`. -/
theorem InternalMeasureRing.loebMeasure_eq_iSup_of_lt_top {Ω : Type*} (M : InternalMeasureRing Ω)
    {B : Set Ω} (hB : M.IsLoebMeasurable B) (hFin : M.loebOuterMeasure B < ⊤) :
    M.loebMeasure B = ⨆ (A ∈ M.𝒜) (_ : A ⊆ B), loebPremeasure M.μ A := by
  rw [M.loebMeasure_properties.2.1 hB]
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    obtain ⟨C, hC_mem, D, hD_mem, hCB, hBD, hDC_lt⟩ :=
      M.isMuApproximable_of_isLoebMeasurable_of_lt_top hB hFin (ε : ℝ) (NNReal.coe_pos.2 hε)
    have hD_eq : loebPremeasure M.μ D = loebPremeasure M.μ C + loebPremeasure M.μ (D \ C) :=
      M.loebPremeasure_isFinitelyAdditive.measure_eq_add_sdiff hC_mem hD_mem (hCB.trans hBD)
    have hC_le : loebPremeasure M.μ C ≤ ⨆ (A ∈ M.𝒜) (_ : A ⊆ B), loebPremeasure M.μ A :=
      le_iSup₂_of_le C hC_mem (le_iSup_of_le hCB le_rfl)
    calc M.loebOuterMeasure B
        ≤ M.loebOuterMeasure D := M.loebOuterMeasure.mono hBD
      _ = loebPremeasure M.μ D := M.loebOuterMeasure_eq_of_mem hD_mem
      _ = loebPremeasure M.μ C + loebPremeasure M.μ (D \ C) := hD_eq
      _ ≤ (⨆ (A ∈ M.𝒜) (_ : A ⊆ B), loebPremeasure M.μ A) + (ε : ℝ≥0∞) := by
          gcongr
          simpa [ENNReal.ofReal_coe_nnreal] using hDC_lt.le
  · refine iSup₂_le fun A hA ↦ iSup_le fun hAB ↦ ?_
    exact (M.loebOuterMeasure_eq_of_mem hA).symm.trans_le (M.loebOuterMeasure.mono hAB)

/-- Goldblatt §16.6, **Lemma 16.6.2** (p. 213):
If `B ⊆ Ω` is `μ`-approximable, then there exists a single internal set `A ∈ M.𝒜` whose symmetric
difference with `B` is Loeb-null: `M.loebOuterMeasure (B ∆ A) = 0`! -/
theorem InternalMeasureRing.exists_mem_loebOuter_symmDiff_zero {Ω : Type*}
    (M : InternalMeasureRing Ω) {B : Set Ω} (hB : M.IsMuApproximable B) :
    ∃ A ∈ M.𝒜, M.loebOuterMeasure (B ∆ A) = 0 := by
  choose C' hC' D' hD' hC'B hBD' hlt using fun n : ℕ ↦
    hB (1 / ((n : ℝ) + 1)) (by positivity)
  let C : ℕ → Set Ω := fun n ↦ ⋃ i ∈ Finset.range (n + 1), C' i
  let D : ℕ → Set Ω := fun n ↦ ⋂ i ∈ Finset.range (n + 1), D' i
  have hC_mem : ∀ n, C n ∈ M.𝒜 :=
    fun n ↦ M.isSetRing.biUnion_finset_mem _ fun i _ ↦ hC' i
  have hD_mem : ∀ n, D n ∈ M.𝒜 :=
    fun n ↦ M.isSetRing.biInter_finset_mem ⟨0, Finset.mem_range.2 (Nat.zero_lt_succ n)⟩
      fun i _ ↦ hD' i
  have hC_mono : Monotone C := fun i j hij x hx ↦ by
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_iUnion₂.2
      ⟨k, Finset.mem_range.2 ((Finset.mem_range.1 hk).trans_le (Nat.succ_le_succ hij)), hxk⟩
  have hD_anti : Antitone D := fun i j hij x hx ↦ by
    refine Set.mem_iInter₂.2 fun k hk ↦ Set.mem_iInter₂.1 hx k ?_
    exact Finset.mem_range.2 ((Finset.mem_range.1 hk).trans_le (Nat.succ_le_succ hij))
  have hCB : ∀ n, C n ⊆ B := fun n ↦ Set.iUnion₂_subset fun i _ ↦ hC'B i
  have hBD : ∀ n, B ⊆ D n := fun n ↦ Set.subset_iInter₂ fun i _ ↦ hBD' i
  obtain ⟨A, hA_mem, hCA_AD⟩ :=
    M.overflow_nested hC_mem hD_mem hC_mono hD_anti fun n ↦ (hCB n).trans (hBD n)
  refine ⟨A, hA_mem, le_antisymm ?_ zero_le⟩
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
  rw [zero_add]
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (NNReal.coe_pos.2 hδ)
  have hsymm_sub : B ∆ A ⊆ D' n \ C' n := by
    have hn_mem : n ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_self n)
    have hC'n_C : C' n ⊆ C n := Set.subset_biUnion_of_mem hn_mem
    have hD_D'n : D n ⊆ D' n := Set.biInter_subset_of_mem hn_mem
    rw [Set.symmDiff_def]
    rintro x (⟨hxB, hxA⟩ | ⟨hxA, hxB⟩)
    · exact ⟨hD_D'n (hBD n hxB), fun h ↦ hxA ((hCA_AD n).1 (hC'n_C h))⟩
    · exact ⟨hD_D'n ((hCA_AD n).2 hxA), fun h ↦ hxB (hC'B n h)⟩
  calc M.loebOuterMeasure (B ∆ A)
      ≤ M.loebOuterMeasure (D' n \ C' n) := M.loebOuterMeasure.mono hsymm_sub
    _ = loebPremeasure M.μ (D' n \ C' n) :=
        M.loebOuterMeasure_eq_of_mem (M.isSetRing.sdiff_mem (hD' n) (hC' n))
    _ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := (hlt n).le
    _ ≤ (δ : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal hn.le

/-- Goldblatt §16.6, **Lemma 16.6.3** (p. 213):
Every `μ`-approximable set `B ⊆ Ω` is Loeb measurable! Moreover, for the `A ∈ M.𝒜` of Lemma 16.6.2
with `M.loebOuterMeasure (B ∆ A) = 0`, we have `M.loebMeasure B = loebPremeasure M.μ A`. -/
theorem InternalMeasureRing.isLoebMeasurable_of_isMuApproximable {Ω : Type*}
    (M : InternalMeasureRing Ω) {B : Set Ω} (hB : M.IsMuApproximable B) :
    M.IsLoebMeasurable B ∧
    ∃ A ∈ M.𝒜, M.loebOuterMeasure (B ∆ A) = 0 ∧ M.loebMeasure B = loebPremeasure M.μ A := by
  obtain ⟨A, hA_mem, hZero⟩ := M.exists_mem_loebOuter_symmDiff_zero hB
  set m := M.loebOuterMeasure
  have hBA_zero : m (B \ A) = 0 :=
    le_antisymm ((m.mono fun _ hx ↦ (Set.symmDiff_def B A).symm ▸ Or.inl hx).trans hZero.le) zero_le
  have hAB_zero : m (A \ B) = 0 :=
    le_antisymm ((m.mono fun _ hx ↦ (Set.symmDiff_def B A).symm ▸ Or.inr hx).trans hZero.le) zero_le
  have hA_car : m.IsCaratheodory A := (M.loebMeasure_properties.2.2 hA_mem).1
  have hBA_car : m.IsCaratheodory (B \ A) := m.isCaratheodory_of_measure_eq_zero hBA_zero
  have hAB_car : m.IsCaratheodory (A \ B) := m.isCaratheodory_of_measure_eq_zero hAB_zero
  have hB_eq : B = (A \ (A \ B)) ∪ (B \ A) := by
    ext x; simp only [Set.mem_union, Set.mem_sdiff]; tauto
  have hB_car : M.IsLoebMeasurable B :=
    hB_eq ▸ m.isCaratheodory_union (m.isCaratheodory_sdiff hA_car hAB_car) hBA_car
  have hm_eq : m B = m A := by
    have h1 : m B ≤ m (A ∪ (B \ A)) := m.mono fun x hx ↦
      if hxA : x ∈ A then Or.inl hxA else Or.inr ⟨hx, hxA⟩
    have h2 : m A ≤ m (B ∪ (A \ B)) := m.mono fun x hx ↦
      if hxB : x ∈ B then Or.inl hxB else Or.inr ⟨hx, hxB⟩
    apply le_antisymm
    · exact h1.trans ((MeasureTheory.measure_union_le A (B \ A)).trans (by simp [hBA_zero]))
    · exact h2.trans ((MeasureTheory.measure_union_le B (A \ B)).trans (by simp [hAB_zero]))
  refine ⟨hB_car, A, hA_mem, hZero, ?_⟩
  rw [M.loebMeasure_properties.2.1 hB_car, hm_eq, M.loebOuterMeasure_eq_of_mem hA_mem]

/-- Goldblatt §16.6, **Lemma 16.6.4** (p. 213):
For any set `B ⊆ Ω` with `M.loebOuterMeasure B < ⊤`, `B` is Loeb measurable **if and only if** `B`
is `μ`-approximable! -/
theorem InternalMeasureRing.isLoebMeasurable_iff_isMuApproximable_of_lt_top {Ω : Type*}
    (M : InternalMeasureRing Ω) {B : Set Ω} (hFin : M.loebOuterMeasure B < ⊤) :
    M.IsLoebMeasurable B ↔ M.IsMuApproximable B :=
  ⟨fun hB ↦ M.isMuApproximable_of_isLoebMeasurable_of_lt_top hB hFin,
   fun hB ↦ (M.isLoebMeasurable_of_isMuApproximable hB).1⟩

/-- **Finite Loeb Measure Single-Internal-Set Approximation Theorem** (Goldblatt §16.6, p. 213):
On an internal measure algebra `M` with `IsLimited (M.μ Set.univ)` (so `M.loebMeasure Set.univ < ⊤`),
a set `X ⊆ Ω` is Loeb measurable **if and only if** for every real `ε > 0`, there exist single
internal sets `B, C ∈ M.𝒜` (not countable unions/intersections!) such that `B ⊆ X ⊆ C` and
`shadow (M.μ (C \ B)) < ε`! -/
theorem InternalMeasureAlgebra.isLoebMeasurable_iff_single_internal_approx {Ω : Type*}
    (M : InternalMeasureAlgebra Ω) (hLimUniv : IsLimited (M.μ Set.univ)) (X : Set Ω) :
    M.IsLoebMeasurable X ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ B ∈ M.𝒜, ∃ C ∈ M.𝒜, B ⊆ X ∧ X ⊆ C ∧ shadow (M.μ (C \ B)) < ε := by
  have hFinUniv : M.loebOuterMeasure Set.univ < ⊤ := by
    rw [M.loebOuterMeasure_eq_of_mem M.univ_mem, loebPremeasure, hyperrealToENNReal_lt_top_iff]
    exact hLimUniv
  have hFinX : M.loebOuterMeasure X < ⊤ :=
    (M.loebOuterMeasure.mono (Set.subset_univ X)).trans_lt hFinUniv
  rw [M.isLoebMeasurable_iff_isMuApproximable_of_lt_top hFinX,
    (M.isMuApproximable_iff_hyperreal X).2]
  constructor
  · intro h ε hε
    obtain ⟨B, hB, C, hC, hBX, hXC, _, hSh⟩ := h ε hε
    exact ⟨B, hB, C, hC, hBX, hXC, hSh⟩
  · intro h ε hε
    obtain ⟨B, hB, C, hC, hBX, hXC, hSh⟩ := h ε hε
    have hCB_mem : C \ B ∈ M.𝒜 := M.isSetRing.sdiff_mem hC hB
    have hLimCB : IsLimited (M.μ (C \ B)) :=
      isLimited_of_nonneg_le (M.nonneg hCB_mem)
        (M.mu_mono hCB_mem M.univ_mem (Set.subset_univ _)) hLimUniv
    exact ⟨B, hB, C, hC, hBX, hXC, hLimCB, hSh⟩

/-- **Loeb Null-Set Characterization**:
On an internal measure ring `M`, `M.loebOuterMeasure X = 0` **if and only if** for every real
`ε > 0`, there exists a single `C ∈ M.𝒜` with `X ⊆ C` and `IsLimited (M.μ C) ∧ shadow (M.μ C) < ε`
(and when `M` is an algebra with `IsLimited (M.μ Set.univ)`, simply `shadow (M.μ C) < ε`)! -/
theorem InternalMeasureRing.loebOuterMeasure_eq_zero_iff {Ω : Type*} (M : InternalMeasureRing Ω)
    (X : Set Ω) :
    M.loebOuterMeasure X = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ C ∈ M.𝒜, X ⊆ C ∧ IsLimited (M.μ C) ∧ shadow (M.μ C) < ε := by
  rw [M.loebOuterMeasure_eq_iInf X]
  constructor
  · intro h0 ε hε
    have hlt : (⨅ (A ∈ M.𝒜) (_ : X ⊆ A), loebPremeasure M.μ A) < ENNReal.ofReal ε := by
      rw [h0]; exact ENNReal.ofReal_pos.2 hε
    simp only [iInf_lt_iff, exists_prop] at hlt
    obtain ⟨C, hC, hXC, hC_lt⟩ := hlt
    obtain ⟨hLim, hSh, _⟩ := lt_coe_of_hyperrealToENNReal_lt_ofReal (M.nonneg hC) hC_lt
    exact ⟨C, hC, hXC, hLim, hSh⟩
  · intro h
    apply le_antisymm _ zero_le
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
    rw [zero_add]
    obtain ⟨C, hC, hXC, hLim, hSh⟩ := h (δ : ℝ) (NNReal.coe_pos.2 hδ)
    refine (iInf₂_le C hC).trans ((iInf_le _ hXC).trans ?_)
    rw [loebPremeasure, hyperrealToENNReal_of_isLimited hLim, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hSh.le

/-- On a finite internal measure algebra (`IsLimited (M.μ Set.univ)`), `X` is Loeb-null
(`M.IsLoebMeasurable X ∧ M.loebMeasure X = 0`, equivalently `M.loebOuterMeasure X = 0`) if and only
if `∀ ε > 0, ∃ C ∈ M.𝒜, X ⊆ C ∧ shadow (M.μ C) < ε`. -/
theorem InternalMeasureAlgebra.loebMeasure_eq_zero_iff {Ω : Type*}
    (M : InternalMeasureAlgebra Ω) (hLimUniv : IsLimited (M.μ Set.univ)) (X : Set Ω) :
    (M.IsLoebMeasurable X ∧ M.loebMeasure X = 0) ↔
      ∀ ε : ℝ, 0 < ε → ∃ C ∈ M.𝒜, X ⊆ C ∧ shadow (M.μ C) < ε := by
  have hiff0 : (M.IsLoebMeasurable X ∧ M.loebMeasure X = 0) ↔ M.loebOuterMeasure X = 0 :=
    ⟨fun ⟨hX, h0⟩ ↦ (M.loebMeasure_properties.2.1 hX).symm.trans h0,
     fun h0 ↦
       have hX : M.IsLoebMeasurable X := M.loebOuterMeasure.isCaratheodory_of_measure_eq_zero h0
       ⟨hX, (M.loebMeasure_properties.2.1 hX).trans h0⟩⟩
  rw [hiff0, M.loebOuterMeasure_eq_zero_iff X]
  exact ⟨fun h ε hε ↦ let ⟨C, hC, hXC, _, hSh⟩ := h ε hε; ⟨C, hC, hXC, hSh⟩,
    fun h ε hε ↦
      let ⟨C, hC, hXC, hSh⟩ := h ε hε
      ⟨C, hC, hXC,
        isLimited_of_nonneg_le (M.nonneg hC)
          (M.mu_mono hC M.univ_mem (Set.subset_univ _)) hLimUniv,
        hSh⟩⟩

/-- Goldblatt §16.7, **Theorem 16.7.1** (pp. 214–215):
On any internal measure ring `M` (even when `M.μ` takes unlimited values, such as on the hyperfinite
real line grid!), a subset `B ⊆ Ω` is **Loeb measurable** **if and only if** `B ∩ A` is
`μ`-approximable for every `A ∈ M.𝒜` with `IsLimited (M.μ A)`! -/
theorem InternalMeasureRing.isLoebMeasurable_iff_inter_approximable {Ω : Type*}
    (M : InternalMeasureRing Ω) (B : Set Ω) :
    M.IsLoebMeasurable B ↔ ∀ A ∈ M.𝒜, IsLimited (M.μ A) → M.IsMuApproximable (B ∩ A) := by
  set m := M.loebOuterMeasure
  constructor
  · intro hB A hA hLim
    have hA_car : M.IsLoebMeasurable A := (M.loebMeasure_properties.2.2 hA).1
    have hBA_car : M.IsLoebMeasurable (B ∩ A) := m.isCaratheodory_inter hB hA_car
    have hBA_fin : m (B ∩ A) < ⊤ :=
      (m.mono Set.inter_subset_right).trans_lt
        ((M.loebOuterMeasure_eq_of_mem hA).trans_lt (hyperrealToENNReal_lt_top_iff.2 hLim))
    exact M.isMuApproximable_of_isLoebMeasurable_of_lt_top hBA_car hBA_fin
  · intro hInter
    rw [IsLoebMeasurable, ← IsCaratheodoryMeasurable, isCaratheodoryMeasurable_iff_le_of_lt_top]
    intro E hE_fin
    have hlt : m E < m E + 1 := ENNReal.lt_add_right hE_fin.ne one_ne_zero
    conv_lhs at hlt => rw [M.loebOuterMeasure_eq_iInf E]
    simp only [iInf_lt_iff, exists_prop] at hlt
    obtain ⟨A, hA_mem, hEA, hA_lt⟩ := hlt
    have hLimA : IsLimited (M.μ A) :=
      hyperrealToENNReal_lt_top_iff.1
        (lt_trans hA_lt (ENNReal.add_lt_top.2 ⟨hE_fin, ENNReal.one_lt_top⟩))
    have hBA_car : m.IsCaratheodory (B ∩ A) :=
      (M.isLoebMeasurable_of_isMuApproximable (hInter A hA_mem hLimA)).1
    have hsplit := hBA_car E
    have h1 : E ∩ (B ∩ A) = E ∩ B := by
      ext x; simp only [Set.mem_inter_iff]; exact ⟨fun ⟨hxE, hxB, _⟩ ↦ ⟨hxE, hxB⟩,
        fun ⟨hxE, hxB⟩ ↦ ⟨hxE, hxB, hEA hxE⟩⟩
    have h2 : E \ (B ∩ A) = E \ B := by
      ext x; simp only [Set.mem_sdiff, Set.mem_inter_iff, not_and]
      exact ⟨fun ⟨hxE, h⟩ ↦ ⟨hxE, fun hxB ↦ h hxB (hEA hxE)⟩,
        fun ⟨hxE, hxB⟩ ↦ ⟨hxE, fun hxB' _ ↦ hxB hxB'⟩⟩
    rw [h1, h2] at hsplit
    exact hsplit.symm.le

/-! ### Concrete Ultrapower & Hyperfinite Instantiations of `InternalMeasureAlgebra` -/

/-- Helper: monotonic transitivity along finite steps `∀ j < k, f j ⊆ f (j + 1)` implies
`f m ⊆ f k` whenever `m ≤ k`. -/
theorem subset_of_step_subset {α : Type*} {f : ℕ → Set α} {m k : ℕ}
    (hstep : ∀ j < k, f j ⊆ f (j + 1)) (hmk : m ≤ k) :
    f m ⊆ f k := by
  induction k with
  | zero =>
      obtain rfl : m = 0 := Nat.eq_zero_of_le_zero hmk
      exact Set.Subset.rfl
  | succ k ih =>
      rcases eq_or_lt_of_le hmk with rfl | hlt
      · exact Set.Subset.rfl
      · exact (ih (fun j hj ↦ hstep j (Nat.lt_succ_of_lt hj)) (Nat.lt_succ_iff.1 hlt)).trans
          (hstep k (Nat.lt_succ_self k))

/-- Helper: antitonic transitivity along finite steps `∀ j < k, g (j + 1) ⊆ g j` implies
`g k ⊆ g m` whenever `m ≤ k`. -/
theorem subset_of_step_superset {α : Type*} {g : ℕ → Set α} {m k : ℕ}
    (hstep : ∀ j < k, g (j + 1) ⊆ g j) (hmk : m ≤ k) :
    g k ⊆ g m := by
  induction k with
  | zero =>
      obtain rfl : m = 0 := Nat.eq_zero_of_le_zero hmk
      exact Set.Subset.rfl
  | succ k ih =>
      rcases eq_or_lt_of_le hmk with rfl | hlt
      · exact Set.Subset.rfl
      · exact (hstep k (Nat.lt_succ_self k)).trans
          (ih (fun j hj ↦ hstep j (Nat.lt_succ_of_lt hj)) (Nat.lt_succ_iff.1 hlt))

/-- **General Ultrapower Construction of an `InternalMeasureAlgebra`** (Goldblatt §16.2 Examples
2–5 & §16.5, pp. 207–213):
Given a sequence of carrier sets `S_seq : ℕ → Set ℝ`, componentwise algebras `𝒜_seq i` of subsets
of `S_seq i`, and componentwise nonnegative finitely additive real premeasures
`μ_seq : ℕ → Set ℝ → ℝ`, their ultrapower on `↥(internalSet S_seq)` forms an `InternalMeasureAlgebra`
satisfying Countable Saturation (`iUnion_mem_finite`) and both Overflow principles
(`overflow_upper` and `overflow_nested`)! -/
def mkInternalMeasureAlgebra
    (S_seq : ℕ → Set ℝ)
    (𝒜_seq : ℕ → Set (Set ℝ))
    (μ_seq : ℕ → Set ℝ → ℝ)
    (hEmpty : ∀ i, ∅ ∈ 𝒜_seq i)
    (hUniv : ∀ i, S_seq i ∈ 𝒜_seq i)
    (hSub : ∀ i ⦃X⦄, X ∈ 𝒜_seq i → X ⊆ S_seq i)
    (hSdiff : ∀ i ⦃X Y⦄, X ∈ 𝒜_seq i → Y ∈ 𝒜_seq i → X \ Y ∈ 𝒜_seq i)
    (hUnion : ∀ i ⦃X Y⦄, X ∈ 𝒜_seq i → Y ∈ 𝒜_seq i → X ∪ Y ∈ 𝒜_seq i)
    (hμ_empty : ∀ i, μ_seq i ∅ = 0)
    (hμ_nonneg : ∀ i ⦃X⦄, X ∈ 𝒜_seq i → 0 ≤ μ_seq i X)
    (hμ_add : ∀ i ⦃X Y⦄, X ∈ 𝒜_seq i → Y ∈ 𝒜_seq i → Disjoint X Y →
      μ_seq i (X ∪ Y) = μ_seq i X + μ_seq i Y) :
    InternalMeasureAlgebra ↥(internalSet S_seq) := by
  let S : Set ℝ* := internalSet S_seq
  let 𝒜 : Set (Set ↥S) :=
    {A : Set ↥S | ∃ X : ℕ → Set ℝ, (∀ i, X i ∈ 𝒜_seq i) ∧
      ((Subtype.val : ↥S → ℝ*) '' A) = internalSet X}
  let μ : Set ↥S → ℝ* := fun A ↦
    if h : A ∈ 𝒜 then ofSeq (fun i ↦ μ_seq i (h.choose i)) else 0
  have hμ_spec : ∀ {A : Set ↥S} {X : ℕ → Set ℝ},
      (∀ i, X i ∈ 𝒜_seq i) → ((Subtype.val : ↥S → ℝ*) '' A) = internalSet X →
      A ∈ 𝒜 ∧ μ A = ofSeq (fun i ↦ μ_seq i (X i)) := by
    intro A X hX hImg
    have hA : A ∈ 𝒜 := ⟨X, hX, hImg⟩
    refine ⟨hA, ?_⟩
    have hμ_unfold : μ A = ofSeq (fun i ↦ μ_seq i (hA.choose i)) := dite_eq_left hA
    rw [hμ_unfold]
    have heq_set : internalSet hA.choose = internalSet X := hA.choose_spec.2.symm.trans hImg
    have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), hA.choose i = X i :=
      internalSet_eq_iff.1 heq_set
    exact Germ.coe_eq.2 (hev.mono fun i hi ↦ by dsimp only; rw [hi])
  have hMkSet : ∀ X : ℕ → Set ℝ, (∀ i, X i ∈ 𝒜_seq i) →
      ∃ A ∈ 𝒜, ((Subtype.val : ↥S → ℝ*) '' A) = internalSet X ∧
        μ A = ofSeq (fun i ↦ μ_seq i (X i)) := by
    intro X hX
    have hXS : internalSet X ⊆ S :=
      internalSet_subset_iff.2 (Eventually.of_forall fun i ↦ hSub i (hX i))
    let A : Set ↥S := (Subtype.val : ↥S → ℝ*) ⁻¹' internalSet X
    have hImg : ((Subtype.val : ↥S → ℝ*) '' A) = internalSet X := by
      rw [Subtype.image_preimage_coe, Set.inter_eq_right.2 hXS]
    obtain ⟨hA, hμA⟩ := hμ_spec hX hImg
    exact ⟨A, hA, hImg, hμA⟩
  have hEmpty_mem : (∅ : Set ↥S) ∈ 𝒜 ∧ μ ∅ = 0 := by
    obtain ⟨h1, h2⟩ := hμ_spec (A := ∅) (X := fun _ ↦ ∅) hEmpty
      (by simp [internalSet_const])
    refine ⟨h1, h2.trans ?_⟩
    simp_rw [hμ_empty]
    rfl
  refine
    { 𝒜 := 𝒜
      isSetRing :=
        { nonempty := ⟨∅, hEmpty_mem.1⟩
          sdiff_mem := fun A B ⟨X, hX, hAX⟩ ⟨Y, hY, hBY⟩ ↦
            ⟨fun i ↦ X i \ Y i, fun i ↦ hSdiff i (hX i) (hY i), by
              rw [Set.image_sdiff Subtype.val_injective, hAX, hBY, internalSet_sdiff]⟩
          union_mem := fun A B ⟨X, hX, hAX⟩ ⟨Y, hY, hBY⟩ ↦
            ⟨fun i ↦ X i ∪ Y i, fun i ↦ hUnion i (hX i) (hY i), by
              rw [Set.image_union, hAX, hBY, internalSet_union]⟩ }
      univ_mem := ⟨S_seq, hUniv, by simp [S]⟩
      μ := μ
      map_empty := hEmpty_mem.2
      nonneg := fun A ⟨X, hX, hAX⟩ ↦ by
        rw [(hμ_spec hX hAX).2]
        exact ofSeq_le_ofSeq.2 (Eventually.of_forall fun i ↦ hμ_nonneg i (hX i))
      map_union_disjoint := fun A B ⟨X, hX, hAX⟩ ⟨Y, hY, hBY⟩ hdisj ↦ by
        have hImgU : ((Subtype.val : ↥S → ℝ*) '' (A ∪ B)) = internalSet (fun i ↦ X i ∪ Y i) := by
          rw [Set.image_union, hAX, hBY, internalSet_union]
        rw [(hμ_spec (fun i ↦ hUnion i (hX i) (hY i)) hImgU).2,
          (hμ_spec hX hAX).2, (hμ_spec hY hBY).2]
        have hDisjImg : internalSet (fun i ↦ X i ∩ Y i) = internalSet (fun _ ↦ (∅ : Set ℝ)) := by
          rw [← internalSet_inter, ← hAX, ← hBY, ← Set.image_inter Subtype.val_injective,
            hdisj.inter_eq, Set.image_empty]
          simp [internalSet_const]
        have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), Disjoint (X i) (Y i) :=
          (internalSet_eq_iff.1 hDisjImg).mono fun i hi ↦ Set.disjoint_iff_inter_eq_empty.2 hi
        exact Germ.coe_eq.2 (hev.mono fun i hi ↦ hμ_add i (hX i) (hY i) hi)
      iUnion_mem_finite := fun A hA hU ↦
        (isSetAlgebra_internalSubsetAlgebra ⟨S_seq, rfl⟩).2
          (fun n ↦ by
            obtain ⟨X, _, hAX⟩ := hA n
            show IsInternal _
            rw [hAX]
            exact ⟨X, rfl⟩)
          (by
            obtain ⟨X, _, hUX⟩ := hU
            show IsInternal _
            rw [hUX]
            exact ⟨X, rfl⟩)
      overflow_upper := fun A r hA hMono hlt ↦ by
        choose X hX hAX using fun n ↦ hA n
        have hμA : ∀ n, μ (A n) = ofSeq (fun i ↦ μ_seq i (X n i)) :=
          fun n ↦ (hμ_spec (hX n) (hAX n)).2
        let Good : ℕ → ℕ → Prop := fun m i ↦
          (∀ j < m, X j i ⊆ X (j + 1) i) ∧ (∀ j ≤ m, μ_seq i (X j i) < r)
        have hGood_down : ∀ {m m' i : ℕ}, m ≤ m' → Good m' i → Good m i :=
          fun hle ⟨h1, h2⟩ ↦ ⟨fun j hj ↦ h1 j (hj.trans_le hle), fun j hj ↦ h2 j (hj.trans hle)⟩
        have hGood_ev : ∀ m : ℕ, ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), Good m i := by
          intro m
          induction m with
          | zero =>
              have h0 : ofSeq (fun i ↦ μ_seq i (X 0 i)) < ofSeq (fun _ ↦ r) := by
                rw [← hμA 0]; exact hlt 0
              exact (ofSeq_lt_ofSeq.1 h0).mono fun i hi ↦
                ⟨fun _ hj ↦ (Nat.not_lt_zero _ hj).elim,
                 fun j hj ↦ by obtain rfl := Nat.eq_zero_of_le_zero hj; exact hi⟩
          | succ m ih =>
              have hsub_m : internalSet (X m) ⊆ internalSet (X (m + 1)) := by
                rw [← hAX m, ← hAX (m + 1)]
                exact Set.image_mono (hMono (Nat.le_succ m))
              have hev_sub := internalSet_subset_iff.1 hsub_m
              have hlt_m1 : ofSeq (fun i ↦ μ_seq i (X (m + 1) i)) < ofSeq (fun _ ↦ r) := by
                rw [← hμA (m + 1)]; exact hlt (m + 1)
              have hev_lt := ofSeq_lt_ofSeq.1 hlt_m1
              refine (ih.and (hev_sub.and hev_lt)).mono fun i ⟨⟨h1, h2⟩, hs, hl⟩ ↦ ⟨?_, ?_⟩
              · intro j hj
                rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hj) with rfl | hj'
                · exact hs
                · exact h1 j hj'
              · intro j hj
                rcases eq_or_lt_of_le hj with rfl | hj'
                · exact hl
                · exact h2 j (Nat.lt_succ_iff.1 hj')
        let S_fin : ℕ → Finset ℕ := fun i ↦ (Finset.Iic i).filter (fun m ↦ Good m i)
        have hS_ne : ∀ i : ℕ, Good 0 i → (S_fin i).Nonempty :=
          fun i hi0 ↦ ⟨0, Finset.mem_filter.2 ⟨Finset.mem_Iic.2 (Nat.zero_le i), hi0⟩⟩
        let k : ∀ i : ℕ, Good 0 i → ℕ := fun i hi0 ↦ (S_fin i).max' (hS_ne i hi0)
        let B_seq : ℕ → Set ℝ := fun i ↦
          if hi0 : Good 0 i then X (k i hi0) i else ∅
        have hB_mem_seq : ∀ i, B_seq i ∈ 𝒜_seq i := fun i ↦ by
          by_cases hi0 : Good 0 i <;> simp [B_seq, hi0, hX, hEmpty]
        obtain ⟨B, hB_mem, hImgB, hμB⟩ := hMkSet B_seq hB_mem_seq
        refine ⟨B, hB_mem, fun n ↦ ?_, ?_⟩
        · have hev_ge : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), n ≤ i :=
            Nat.hyperfilter_le_atTop (eventually_ge_atTop n)
          have hev_sub : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), X n i ⊆ B_seq i := by
            refine (hev_ge.and (hGood_ev n)).mono fun i ⟨hni, hgn⟩ ↦ ?_
            have hi0 : Good 0 i := hGood_down (Nat.zero_le n) hgn
            simp only [B_seq, hi0, ↓reduceDIte]
            have hnk : n ≤ k i hi0 :=
              Finset.le_max' (S_fin i) n (Finset.mem_filter.2 ⟨Finset.mem_Iic.2 hni, hgn⟩)
            have hgk : Good (k i hi0) i :=
              (Finset.mem_filter.1 (Finset.max'_mem (S_fin i) (hS_ne i hi0))).2
            exact subset_of_step_subset hgk.1 hnk
          have hImgSub : ((Subtype.val : ↥S → ℝ*) '' A n) ⊆ ((Subtype.val : ↥S → ℝ*) '' B) := by
            rw [hAX n, hImgB]
            exact internalSet_subset_iff.2 hev_sub
          intro x hx
          obtain ⟨y, hyB, hyx⟩ := hImgSub ⟨x, hx, rfl⟩
          exact Subtype.val_injective hyx ▸ hyB
        · rw [hμB]
          refine ofSeq_lt_ofSeq.2 ((hGood_ev 0).mono fun i hi0 ↦ ?_)
          simp only [B_seq, hi0, ↓reduceDIte]
          have hgk : Good (k i hi0) i :=
            (Finset.mem_filter.1 (Finset.max'_mem (S_fin i) (hS_ne i hi0))).2
          exact hgk.2 (k i hi0) le_rfl
      overflow_nested := fun C D hC hD hMono hAnti hCD ↦ by
        choose X hX hCX using fun n ↦ hC n
        choose Y hY hDY using fun n ↦ hD n
        let Good : ℕ → ℕ → Prop := fun m i ↦
          (∀ j < m, X j i ⊆ X (j + 1) i) ∧
          (∀ j < m, Y (j + 1) i ⊆ Y j i) ∧
          (∀ j ≤ m, X j i ⊆ Y j i)
        have hGood_down : ∀ {m m' i : ℕ}, m ≤ m' → Good m' i → Good m i :=
          fun hle ⟨h1, h2, h3⟩ ↦
            ⟨fun j hj ↦ h1 j (hj.trans_le hle),
             fun j hj ↦ h2 j (hj.trans_le hle),
             fun j hj ↦ h3 j (hj.trans hle)⟩
        have hGood_ev : ∀ m : ℕ, ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), Good m i := by
          intro m
          induction m with
          | zero =>
              have h0 : internalSet (X 0) ⊆ internalSet (Y 0) := by
                rw [← hCX 0, ← hDY 0]; exact Set.image_mono (hCD 0)
              exact (internalSet_subset_iff.1 h0).mono fun i hi ↦
                ⟨fun _ hj ↦ (Nat.not_lt_zero _ hj).elim,
                 fun _ hj ↦ (Nat.not_lt_zero _ hj).elim,
                 fun j hj ↦ by obtain rfl := Nat.eq_zero_of_le_zero hj; exact hi⟩
          | succ m ih =>
              have hsC : internalSet (X m) ⊆ internalSet (X (m + 1)) := by
                rw [← hCX m, ← hCX (m + 1)]; exact Set.image_mono (hMono (Nat.le_succ m))
              have hsD : internalSet (Y (m + 1)) ⊆ internalSet (Y m) := by
                rw [← hDY (m + 1), ← hDY m]; exact Set.image_mono (hAnti (Nat.le_succ m))
              have hsCD : internalSet (X (m + 1)) ⊆ internalSet (Y (m + 1)) := by
                rw [← hCX (m + 1), ← hDY (m + 1)]; exact Set.image_mono (hCD (m + 1))
              refine (ih.and ((internalSet_subset_iff.1 hsC).and
                ((internalSet_subset_iff.1 hsD).and (internalSet_subset_iff.1 hsCD)))).mono
                fun i ⟨⟨h1, h2, h3⟩, hc, hd, hcd⟩ ↦ ⟨?_, ?_, ?_⟩
              · intro j hj
                rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hj) with rfl | hj'
                · exact hc
                · exact h1 j hj'
              · intro j hj
                rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hj) with rfl | hj'
                · exact hd
                · exact h2 j hj'
              · intro j hj
                rcases eq_or_lt_of_le hj with rfl | hj'
                · exact hcd
                · exact h3 j (Nat.lt_succ_iff.1 hj')
        let S_fin : ℕ → Finset ℕ := fun i ↦ (Finset.Iic i).filter (fun m ↦ Good m i)
        have hS_ne : ∀ i : ℕ, Good 0 i → (S_fin i).Nonempty :=
          fun i hi0 ↦ ⟨0, Finset.mem_filter.2 ⟨Finset.mem_Iic.2 (Nat.zero_le i), hi0⟩⟩
        let k : ∀ i : ℕ, Good 0 i → ℕ := fun i hi0 ↦ (S_fin i).max' (hS_ne i hi0)
        let A_seq : ℕ → Set ℝ := fun i ↦
          if hi0 : Good 0 i then X (k i hi0) i else ∅
        have hA_mem_seq : ∀ i, A_seq i ∈ 𝒜_seq i := fun i ↦ by
          by_cases hi0 : Good 0 i <;> simp [A_seq, hi0, hX, hEmpty]
        obtain ⟨A, hA_mem, hImgA, _⟩ := hMkSet A_seq hA_mem_seq
        refine ⟨A, hA_mem, fun n ↦ ?_⟩
        have hev_ge : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), n ≤ i :=
          Nat.hyperfilter_le_atTop (eventually_ge_atTop n)
        have hev_both : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
            X n i ⊆ A_seq i ∧ A_seq i ⊆ Y n i := by
          refine (hev_ge.and (hGood_ev n)).mono fun i ⟨hni, hgn⟩ ↦ ?_
          have hi0 : Good 0 i := hGood_down (Nat.zero_le n) hgn
          simp only [A_seq, hi0, ↓reduceDIte]
          have hnk : n ≤ k i hi0 :=
            Finset.le_max' (S_fin i) n (Finset.mem_filter.2 ⟨Finset.mem_Iic.2 hni, hgn⟩)
          have hgk : Good (k i hi0) i :=
            (Finset.mem_filter.1 (Finset.max'_mem (S_fin i) (hS_ne i hi0))).2
          exact ⟨subset_of_step_subset (f := fun j ↦ X j i) hgk.1 hnk,
            (hgk.2.2 (k i hi0) le_rfl).trans
              (subset_of_step_superset (g := fun j ↦ Y j i) hgk.2.1 hnk)⟩
        have hSub1 : ((Subtype.val : ↥S → ℝ*) '' C n) ⊆ ((Subtype.val : ↥S → ℝ*) '' A) := by
          rw [hCX n, hImgA]
          exact internalSet_subset_iff.2 (hev_both.mono fun _ h ↦ h.1)
        have hSub2 : ((Subtype.val : ↥S → ℝ*) '' A) ⊆ ((Subtype.val : ↥S → ℝ*) '' D n) := by
          rw [hImgA, hDY n]
          exact internalSet_subset_iff.2 (hev_both.mono fun _ h ↦ h.2)
        exact ⟨fun x hx ↦ let ⟨y, hy, hyx⟩ := hSub1 ⟨x, hx, rfl⟩; Subtype.val_injective hyx ▸ hy,
          fun x hx ↦ let ⟨y, hy, hyx⟩ := hSub2 ⟨x, hx, rfl⟩; Subtype.val_injective hyx ▸ hy⟩ }

/-- Goldblatt §16.2 Example (5) (pp. 207–208): **Hyperfinite Weighted Internal Measure Algebra**:
Given `T_seq : ℕ → Finset ℝ` representing `S = internalSet (fun i ↦ (T_seq i : Set ℝ))` and
componentwise nonnegative weight functions `w_seq : ℕ → ℝ → ℝ` (`∀ i x, x ∈ T_seq i → 0 ≤ w_seq i x`),
the hyperfinite sum `μ_w(A) = hypersum W ((↑) '' A)` defines an `InternalMeasureAlgebra` on `↥S`
whose algebra `𝒜` is `internalSubsetAlgebra S` (`𝒫_I(S)`)! -/
def hyperfiniteWeightedAlgebra
    (T_seq : ℕ → Finset ℝ)
    (w_seq : ℕ → ℝ → ℝ)
    (hw_nonneg : ∀ i x, x ∈ T_seq i → 0 ≤ w_seq i x) :
    InternalMeasureAlgebra ↥(internalSet (fun i ↦ (T_seq i : Set ℝ))) :=
  mkInternalMeasureAlgebra
    (fun i ↦ (T_seq i : Set ℝ))
    (fun i ↦ {X : Set ℝ | X ⊆ (T_seq i : Set ℝ)})
    (fun i X ↦ ∑ x ∈ (T_seq i).filter (fun x ↦ x ∈ X), w_seq i x)
    (fun _ ↦ Set.empty_subset _)
    (fun _ ↦ Set.Subset.rfl)
    (fun _ _ hX ↦ hX)
    (fun _ _ _ hX _ ↦ Set.sdiff_subset.trans hX)
    (fun _ _ _ hX hY ↦ Set.union_subset hX hY)
    (fun i ↦ by simp)
    (fun i X _ ↦ Finset.sum_nonneg fun x hx ↦ hw_nonneg i x (Finset.mem_filter.1 hx).1)
    (fun i X Y _ _ hdisj ↦ by
      simp only [Finset.sum_filter]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      by_cases hxX : x ∈ X
      · have hxY : x ∉ Y := Set.disjoint_left.1 hdisj hxX
        simp [hxX, hxY]
      · by_cases hxY : x ∈ Y <;> simp [hxX, hxY])

/-- Characterization of `hyperfiniteWeightedAlgebra`:
1. Its algebra `𝒜` equals `internalSubsetAlgebra S` (`𝒫_I(S)`);
2. For every `A ∈ internalSubsetAlgebra S`, its internal measure equals `hypersum W ((↑) '' A)`
   where `W = internalFun (fun i ↦ ⟨Set.univ, w_seq i, ...⟩)`;
3. When `w_seq i _ = c_seq i` is a constant weight per index `i` (such as `1 / |T_seq i|` or
   `1 / b i`), for every `A` with `HasHypercard ((↑) '' A) K`, `μ A = K.toHyperreal * ofSeq c_seq`! -/
theorem hyperfiniteWeightedAlgebra_spec
    (T_seq : ℕ → Finset ℝ)
    (w_seq : ℕ → ℝ → ℝ)
    (hw_nonneg : ∀ i x, x ∈ T_seq i → 0 ≤ w_seq i x) :
    let S : Set ℝ* := internalSet (fun i ↦ (T_seq i : Set ℝ))
    let M := hyperfiniteWeightedAlgebra T_seq w_seq hw_nonneg
    let W : InternalPartialFun :=
      internalFun (fun i ↦ ⟨Set.univ, w_seq i, fun x hx ↦ (hx (Set.mem_univ x)).elim⟩)
    M.𝒜 = internalSubsetAlgebra S ∧
    (∀ A ∈ internalSubsetAlgebra S,
      M.μ A = hypersum W ((Subtype.val : ↥S → ℝ*) '' A)) ∧
    (∀ (c_seq : ℕ → ℝ), (∀ i x, x ∈ T_seq i → w_seq i x = c_seq i) →
      ∀ (A : Set ↥S) (K : ℕ*),
        HasHypercard ((Subtype.val : ↥S → ℝ*) '' A) K →
        M.μ A = Hypernat.toHyperreal K * ofSeq c_seq) := by
  intro S M W
  have hS_hf : IsHyperfinite S := isHyperfinite_iff_exists_finset.2 ⟨T_seq, rfl⟩
  have h𝒜_eq : M.𝒜 = internalSubsetAlgebra S := by
    ext A
    constructor
    · rintro ⟨X, _, hAX⟩
      change IsInternal ((Subtype.val : ↥S → ℝ*) '' A)
      exact hAX ▸ ⟨X, rfl⟩
    · rintro ⟨Y, hAY⟩
      refine ⟨fun i ↦ Y i ∩ (T_seq i : Set ℝ), fun i ↦ Set.inter_subset_right, ?_⟩
      rw [← internalSet_inter, ← hAY]
      exact (Set.inter_eq_left.2 (Subtype.coe_image_subset S A)).symm
  have hμ_sum : ∀ (A : Set ↥S) (X : ℕ → Set ℝ),
      (∀ i, X i ⊆ (T_seq i : Set ℝ)) →
      ((Subtype.val : ↥S → ℝ*) '' A) = internalSet X →
      M.μ A = ofSeq (fun i ↦ ∑ x ∈ T_seq i, if x ∈ X i then w_seq i x else 0) := by
    intro A X hX hAX
    have hA_mem : A ∈ M.𝒜 := ⟨X, hX, hAX⟩
    have hμ_unfold : M.μ A =
        ofSeq (fun i ↦ ∑ x ∈ (T_seq i).filter (fun x ↦ x ∈ hA_mem.choose i), w_seq i x) :=
      dite_eq_left hA_mem
    rw [hμ_unfold]
    have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), hA_mem.choose i = X i :=
      internalSet_eq_iff.1 (hA_mem.choose_spec.2.symm.trans hAX)
    refine Germ.coe_eq.2 (hev.mono fun i hi ↦ ?_)
    dsimp only
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun x _ ↦ by simp [hi]
  refine ⟨h𝒜_eq, ?_, ?_⟩
  · intro A hA
    have hImg_hf : IsHyperfinite ((Subtype.val : ↥S → ℝ*) '' A) :=
      (hS_hf.of_isInternal_subset hA (Subtype.coe_image_subset S A)).1
    obtain ⟨U, hU⟩ := isHyperfinite_iff_exists_finset.1 hImg_hf
    let X : ℕ → Set ℝ := fun i ↦ (U i : Set ℝ) ∩ (T_seq i : Set ℝ)
    have hImgX : ((Subtype.val : ↥S → ℝ*) '' A) = internalSet X := by
      rw [← internalSet_inter, ← hU]
      exact (Set.inter_eq_left.2 (Subtype.coe_image_subset S A)).symm
    rw [hμ_sum A X (fun _ ↦ Set.inter_subset_right) hImgX, hU,
      hypersum_internalFun (fun i ↦ ⟨Set.univ, w_seq i, fun x hx ↦ (hx (Set.mem_univ x)).elim⟩) U]
    have hev_sub : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (U i : Set ℝ) ⊆ (T_seq i : Set ℝ) :=
      internalSet_subset_iff.1 (hU ▸ Subtype.coe_image_subset S A)
    refine Germ.coe_eq.2 (hev_sub.mono fun i hi ↦ ?_)
    dsimp only
    have hi_fin : U i ⊆ T_seq i := Finset.coe_subset.1 hi
    exact (Finset.sum_subset hi_fin (fun x hxT hxU ↦ by simp [X, hxT, hxU])).symm.trans
      (Finset.sum_congr rfl fun x hxU ↦ by simp [X, hxU, hi_fin hxU])
  · intro c_seq hc A K ⟨U, hU, hK⟩
    subst hK
    let X : ℕ → Set ℝ := fun i ↦ (U i : Set ℝ) ∩ (T_seq i : Set ℝ)
    have hImgX : ((Subtype.val : ↥S → ℝ*) '' A) = internalSet X := by
      rw [← internalSet_inter, ← hU]
      exact (Set.inter_eq_left.2 (Subtype.coe_image_subset S A)).symm
    rw [hμ_sum A X (fun _ ↦ Set.inter_subset_right) hImgX]
    have hev_sub : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (U i : Set ℝ) ⊆ (T_seq i : Set ℝ) :=
      internalSet_subset_iff.1 (hU ▸ Subtype.coe_image_subset S A)
    change ofSeq _ = ofSeq (fun i ↦ ((U i).card : ℝ)) * ofSeq c_seq
    change ofSeq _ = ofSeq (fun i ↦ ((U i).card : ℝ) * c_seq i)
    refine Germ.coe_eq.2 (hev_sub.mono fun i hi ↦ ?_)
    dsimp only
    have hi_fin : U i ⊆ T_seq i := Finset.coe_subset.1 hi
    refine ((Finset.sum_subset hi_fin (fun x hxT hxU ↦ by simp [X, hxT, hxU])).symm.trans
      (Finset.sum_congr rfl (g := fun _ ↦ c_seq i)
        fun x hxU ↦ by simp [X, hxU, hi_fin hxU, hc i x (hi_fin hxU)])).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]

/-! ## §16.8–16.9 Lebesgue Measure on `[0, 1]` and `ℝ` via Hyperfinite Counting Loeb Measure

### Part A: Uniform Hyperfinite Grid on `[0, 1]` -/

/-- Step-count sequence `N_n = n + 1` representing `omegaNat + 1 ∈ ℕ*`. -/
def unitNSeq (n : ℕ) : ℕ := n + 1

/-- Step-size sequence `dx_n = 1 / (n + 1)` representing `1 / N ∈ ℝ*`. -/
def unitDxSeq (n : ℕ) : ℝ := 1 / ((n + 1 : ℕ) : ℝ)

/-- Finite uniform grid `{0, 1/(n+1), …, n/(n+1)}` on `[0, 1]` at index `n`. -/
def unitGridFinset (n : ℕ) : Finset ℝ :=
  realStepPartition 0 (unitDxSeq n) (unitNSeq n)

/-- Hyperfinite uniform grid `Ω = {0, 1/N, 2/N, …, (N-1)/N} ⊆ *[0, 1]` of size `N = (unitNSeq : ℕ*)`. -/
def unitGridSet : Set ℝ* :=
  hyperStepPartition 0 unitDxSeq unitNSeq

/-- Type `UnitGrid` of points of the hyperfinite uniform grid on `[0, 1]`. -/
abbrev UnitGrid : Type := ↥unitGridSet

/-- `unitGridSet` is hyperfinite of unlimited internal cardinality `(unitNSeq : ℕ*) = omegaNat + 1`. -/
theorem hasHypercard_unitGridSet :
    HasHypercard unitGridSet (unitNSeq : ℕ*) ∧ IsUnlimitedNat (unitNSeq : ℕ*) := by
  have hpos : (0 : ℝ*) < ofSeq unitDxSeq :=
    ofSeq_lt_ofSeq.2 (Eventually.of_forall fun n ↦ by simp [unitDxSeq]; positivity)
  have hunlim : IsUnlimitedNat (unitNSeq : ℕ*) := fun m ↦
    Germ.coe_lt.2 ((Germ.coe_lt.1 (isUnlimitedNat_omegaNat m)).mono fun n (hn : m < n) ↦ by
      dsimp [unitNSeq]; omega)
  exact ⟨(hyperStepPartition_eq_and_hypercard 0 hpos unitNSeq).2, hunlim⟩

/-- Goldblatt §16.2 Example (3) & §16.8: The uniform probability internal measure algebra `M_unit`
on `UnitGrid`, assigning `μ(A) = |A| / N` to each internal subset `A ∈ 𝒫_I(unitGridSet)`. -/
def M_unit : InternalMeasureAlgebra UnitGrid :=
  hyperfiniteWeightedAlgebra unitGridFinset (fun n _ ↦ unitDxSeq n)
    (fun n _ _ ↦ by simp [unitDxSeq]; positivity)

/-- Basic algebraic properties of `M_unit`:
1. `M_unit.𝒜 = internalSubsetAlgebra unitGridSet`;
2. For every `A` with `HasHypercard ((↑) '' A) K`,
   `M_unit.μ A = K.toHyperreal / (unitNSeq : ℕ*).toHyperreal`;
3. `M_unit.μ Set.univ = 1`, `IsLimited (M_unit.μ Set.univ)`, `shadow (M_unit.μ Set.univ) = 1`, and
   `M_unit.loebMeasure Set.univ = 1`. -/
theorem M_unit_basic_properties :
    M_unit.𝒜 = internalSubsetAlgebra unitGridSet ∧
    (∀ (A : Set UnitGrid) (K : ℕ*),
      HasHypercard ((Subtype.val : UnitGrid → ℝ*) '' A) K →
      M_unit.μ A = Hypernat.toHyperreal K / Hypernat.toHyperreal (unitNSeq : ℕ*)) ∧
    M_unit.μ Set.univ = 1 ∧
    IsLimited (M_unit.μ Set.univ) ∧
    shadow (M_unit.μ Set.univ) = 1 ∧
    M_unit.loebMeasure Set.univ = 1 := by
  have hspec := hyperfiniteWeightedAlgebra_spec unitGridFinset (fun n _ ↦ unitDxSeq n)
    (fun n _ _ ↦ by simp [unitDxSeq]; positivity)
  have hdiv : ∀ (A : Set UnitGrid) (K : ℕ*),
      HasHypercard ((Subtype.val : UnitGrid → ℝ*) '' A) K →
      M_unit.μ A = Hypernat.toHyperreal K / Hypernat.toHyperreal (unitNSeq : ℕ*) := by
    intro A K hK
    dsimp only [M_unit]
    rw [hspec.2.2 unitDxSeq (fun _ _ _ ↦ rfl) A K hK]
    have hinv : ofSeq unitDxSeq = (Hypernat.toHyperreal (unitNSeq : ℕ*))⁻¹ :=
      Germ.coe_eq.2 (Eventually.of_forall fun n ↦ by simp [unitDxSeq, unitNSeq])
    rw [hinv, div_eq_mul_inv]
  have hUniv_img : ((Subtype.val : UnitGrid → ℝ*) '' Set.univ) = unitGridSet := by simp
  have hUniv_mu : M_unit.μ Set.univ = 1 := by
    rw [hdiv Set.univ (unitNSeq : ℕ*) (hUniv_img.symm ▸ hasHypercard_unitGridSet.1)]
    have hne : Hypernat.toHyperreal (unitNSeq : ℕ*) ≠ 0 := by
      have hlt := Hypernat.toHyperreal_lt_iff.2 (hasHypercard_unitGridSet.2 0)
      rw [Hypernat.toHyperreal_natCast, Nat.cast_zero] at hlt
      exact hlt.ne'
    exact div_self hne
  have hLim : IsLimited (M_unit.μ Set.univ) := hUniv_mu ▸ isLimited_coe 1
  have hSh : shadow (M_unit.μ Set.univ) = 1 := by rw [hUniv_mu, shadow_one]
  have hLoeb : M_unit.loebMeasure Set.univ = 1 := by
    rw [(M_unit.loebMeasure_properties.2.2 M_unit.univ_mem).2, loebPremeasure,
      hyperrealToENNReal_of_isLimited hLim, hSh, ENNReal.ofReal_one]
  exact ⟨hspec.1, hdiv, hUniv_mu, hLim, hSh, hLoeb⟩

/-- Every point `x : UnitGrid` satisfies `0 ≤ x.1 ≤ 1`, is limited, and has `shadow x.1 ∈ [0, 1]`. -/
theorem unitGrid_bounds (x : UnitGrid) :
    (0 : ℝ*) ≤ x.1 ∧ x.1 ≤ (1 : ℝ*) ∧ IsLimited x.1 ∧ shadow x.1 ∈ Set.Icc (0 : ℝ) 1 := by
  rcases ofSeq_surjective x.1 with ⟨r, hr⟩
  have hmem : ofSeq r ∈ unitGridSet := hr ▸ x.2
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 ≤ r n ∧ r n ≤ 1 := by
    refine (ofSeq_mem_internalSet.1 hmem).mono fun n hn ↦ ?_
    obtain ⟨k, hk, hkr⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hn)
    rw [← hkr]
    have hkn : k < n + 1 := Finset.mem_range.1 hk
    simp only [unitDxSeq, zero_add]
    refine ⟨by positivity, ?_⟩
    rw [mul_one_div, div_le_one (by positivity)]
    exact_mod_cast hkn.le
  have h0 : (0 : ℝ*) ≤ x.1 := hr ▸ ofSeq_le_ofSeq.2 (hev.mono fun _ h ↦ h.1)
  have h1 : x.1 ≤ (1 : ℝ*) := hr ▸ ofSeq_le_ofSeq.2 (hev.mono fun _ h ↦ h.2)
  have hLim : IsLimited x.1 := isLimited_of_nonneg_le h0 h1 (isLimited_coe 1)
  have hsh0 : 0 ≤ shadow x.1 := shadow_nonneg_of_nonneg hLim h0
  have hsh1 : shadow x.1 ≤ 1 := by
    simpa [shadow_one] using shadow_le_of_le hLim (isLimited_coe 1) h1
  exact ⟨h0, h1, hLim, hsh0, hsh1⟩

/-- Standard part map `unitShadow : UnitGrid → ℝ` (`x ↦ shadow x.1`). -/
def unitShadow (x : UnitGrid) : ℝ := shadow x.1

/-- Standard part map `unitSt : UnitGrid → unitInterval` (`[0, 1]`). -/
def unitSt (x : UnitGrid) : unitInterval := ⟨shadow x.1, (unitGrid_bounds x).2.2.2⟩

/-- **Surjectivity of `st : UnitGrid → [0, 1]`**: every standard real in `[0, 1]` is the shadow of
a point in the hyperfinite grid `UnitGrid`! -/
theorem unitSt_surjective : Function.Surjective unitSt := by
  rintro ⟨r, hr0, hr1⟩
  let k : ℕ → ℕ := fun n ↦ min ⌊r * ((n + 1 : ℕ) : ℝ)⌋₊ n
  let s : ℕ → ℝ := fun n ↦ 0 + (k n : ℝ) * unitDxSeq n
  have hs_mem : ∀ n : ℕ, s n ∈ (unitGridFinset n : Set ℝ) := fun n ↦ by
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨k n, Finset.mem_range.2 ?_, rfl⟩)
    exact (Nat.min_le_right _ n).trans_lt (Nat.lt_succ_self n)
  let x : UnitGrid := ⟨ofSeq s, ofSeq_mem_internalSet.2 (Eventually.of_forall hs_mem)⟩
  refine ⟨x, Subtype.ext ?_⟩
  change shadow (ofSeq s) = r
  apply shadow_eq_of_infClose
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  have hdiff_le : ∀ n : ℕ, |s n - r| ≤ 1 / ((n + 1 : ℕ) : ℝ) := fun n ↦ by
    set m : ℝ := ((n + 1 : ℕ) : ℝ)
    have hm_pos : 0 < m := by positivity
    have hs_eq : s n = (k n : ℝ) / m := by
      simp [s, unitDxSeq, m, div_eq_mul_inv]
    rw [hs_eq, div_sub' hm_pos.ne', abs_div, abs_of_pos hm_pos]
    refine div_le_div_of_nonneg_right ?_ hm_pos.le
    rcases eq_or_lt_of_le hr1 with rfl | hr_lt1
    · have hfl : ⌊(1 : ℝ) * m⌋₊ = n + 1 := by
        rw [one_mul]; exact Nat.floor_natCast (n + 1)
      have hkn : k n = n := by
        dsimp only [k]; rw [hfl]; exact Nat.min_eq_right (Nat.le_succ n)
      rw [hkn, mul_one]
      have hdiff : (n : ℝ) - m = -1 := by dsimp [m]; push_cast; ring
      rw [hdiff]; norm_num
    · have hrm_lt : r * m < m := mul_lt_of_lt_one_left hm_pos hr_lt1
      have hfl_lt : ⌊r * m⌋₊ < n + 1 :=
        (Nat.floor_lt (by positivity)).2 (by exact_mod_cast hrm_lt)
      have hkn : k n = ⌊r * m⌋₊ := Nat.min_eq_left (Nat.lt_succ_iff.1 hfl_lt)
      rw [hkn]
      have h1 : (⌊r * m⌋₊ : ℝ) ≤ r * m := Nat.floor_le (by positivity)
      have h2 : r * m < (⌊r * m⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (r * m)
      exact abs_le.2 ⟨by linarith, by linarith⟩
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |s n - r| < ε := by
    refine (Germ.coe_lt.1 (isUnlimitedNat_omegaNat N)).mono fun n (hn : N < n) ↦ ?_
    refine (hdiff_le n).trans_lt (lt_of_le_of_lt ?_ hN)
    exact one_div_le_one_div_of_le (by positivity) (by push_cast; gcongr)
  exact ofSeq_lt_ofSeq.2 hev

/-- Elementary integer-lattice counting helper on `ℤ`:
1. `(Finset.Icc ⌈a * m⌉ ⌊c * m⌋).card ≤ (c - a) * m + 1` for `a ≤ c` and `0 ≤ m`;
2. `(c - a) * m - 2 ≤ (Finset.Icc (⌊a * m⌋ + 1) (⌈c * m⌉ - 1)).card` for all `a, c, m : ℝ`. -/
theorem int_Icc_card_bounds {a c m : ℝ} (hac : a ≤ c) (hm : 0 ≤ m) :
    (((Finset.Icc ⌈a * m⌉ ⌊c * m⌋).card : ℕ) : ℝ) ≤ (c - a) * m + 1 ∧
    (c - a) * m - 2 ≤ (((Finset.Icc (⌊a * m⌋ + 1) (⌈c * m⌉ - 1)).card : ℕ) : ℝ) := by
  rw [Int.card_Icc, Int.card_Icc]
  constructor
  · set z : ℤ := ⌊c * m⌋ + 1 - ⌈a * m⌉
    rcases le_or_gt z 0 with hz | hz
    · rw [Int.toNat_of_nonpos hz]
      have hnn : 0 ≤ (c - a) * m := mul_nonneg (sub_nonneg.2 hac) hm
      push_cast; linarith
    · have hz_cast : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hz.le
      rw [hz_cast]
      have hfl : (⌊c * m⌋ : ℝ) ≤ c * m := Int.floor_le (c * m)
      have hce : a * m ≤ (⌈a * m⌉ : ℝ) := Int.le_ceil (a * m)
      simp only [z, Int.cast_sub, Int.cast_add, Int.cast_one]
      linarith
  · set w : ℤ := ⌈c * m⌉ - 1 + 1 - (⌊a * m⌋ + 1)
    have hw_le : (w : ℝ) ≤ ((w.toNat : ℕ) : ℝ) := by
      exact_mod_cast Int.self_le_toNat w
    have hce : c * m ≤ (⌈c * m⌉ : ℝ) := Int.le_ceil (c * m)
    have hfl : (⌊a * m⌋ : ℝ) ≤ a * m := Int.floor_le (a * m)
    have hw_val : (c - a) * m - 2 ≤ (w : ℝ) := by
      simp only [w, sub_add_cancel, Int.cast_sub, Int.cast_add, Int.cast_one]
      linarith
    exact hw_val.trans hw_le

/-- Finite counting bound on `unitGridFinset n` for subintervals of `[0, 1]`:
for `0 ≤ a ≤ c ≤ 1` and any `J : Set ℝ` with `Set.Ioo a c ⊆ J` and `J ⊆ Set.Icc a c`, the fraction
of points of `unitGridFinset n` in `J` lies in `[c - a - 2/(n+1), c - a + 1/(n+1)]`! -/
theorem unitGridFinset_interval_density_bounds {a c : ℝ} (ha0 : 0 ≤ a) (hac : a ≤ c) (hc1 : c ≤ 1)
    {J : Set ℝ} (hJ_open : Set.Ioo a c ⊆ J) (hJ_closed : J ⊆ Set.Icc a c) (n : ℕ) :
    let m : ℝ := ((n + 1 : ℕ) : ℝ)
    (c - a) - 2 / m ≤ ((∑ x ∈ unitGridFinset n, if x ∈ J then unitDxSeq n else 0) : ℝ) ∧
    ((∑ x ∈ unitGridFinset n, if x ∈ J then unitDxSeq n else 0) : ℝ) ≤ (c - a) + 1 / m := by
  intro m
  have hm_pos : 0 < m := by positivity
  -- Rewrite the sum over `unitGridFinset n` as `(card of indices k < n+1 with k/m ∈ J) / m`.
  let g : ℕ → ℝ := fun k ↦ 0 + (k : ℝ) * unitDxSeq n
  have hg_inj : Set.InjOn g (Finset.range (n + 1)) := by
    intro k₁ _ k₂ _ heq
    have hdx_ne : unitDxSeq n ≠ 0 := by simp [unitDxSeq]; positivity
    have hk_eq : (k₁ : ℝ) = (k₂ : ℝ) := mul_right_cancel₀ hdx_ne (by simpa [g] using heq)
    exact_mod_cast hk_eq
  have hsum_eq : (∑ x ∈ unitGridFinset n, if x ∈ J then unitDxSeq n else 0) =
      ((((Finset.range (n + 1)).filter (fun k ↦ g k ∈ J)).card : ℕ) : ℝ) / m := by
    change (∑ x ∈ (Finset.range (n + 1)).image g, if x ∈ J then unitDxSeq n else 0) = _
    rw [Finset.sum_image hg_inj, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    simp [unitDxSeq, m, div_eq_mul_inv]
  rw [hsum_eq]
  set F := (Finset.range (n + 1)).filter (fun k ↦ g k ∈ J)
  obtain ⟨hub_int, hlb_int⟩ := int_Icc_card_bounds hac hm_pos.le
  constructor
  · rcases eq_or_lt_of_le hac with rfl | hlt
    · rw [sub_self, zero_sub]
      linarith [ (by positivity : (0 : ℝ) ≤ 2 / m), (by positivity : (0 : ℝ) ≤ (F.card : ℝ) / m) ]
    · -- Inject `Finset.Icc (⌊a * m⌋ + 1) (⌈c * m⌉ - 1)` into `F` via `z ↦ z.toNat`.
      let Z := Finset.Icc (⌊a * m⌋ + 1) (⌈c * m⌉ - 1)
      have hZ_sub : Z.image Int.toNat ⊆ F := by
        intro k hk
        obtain ⟨z, hzZ, rfl⟩ := Finset.mem_image.1 hk
        obtain ⟨hz1, hz2⟩ := Finset.mem_Icc.1 hzZ
        have hz_gt_am : a * m < (z : ℝ) :=
          (Int.lt_floor_add_one (a * m)).trans_le (by exact_mod_cast hz1)
        have hz_lt_cm : (z : ℝ) < c * m :=
          (by exact_mod_cast hz2 : (z : ℝ) ≤ (⌈c * m⌉ : ℝ) - 1).trans_lt
            (by linarith [Int.ceil_lt_add_one (c * m)])
        have hz_nonneg : 0 ≤ z := by
          have : (0 : ℝ) < (z : ℝ) := (mul_nonneg ha0 hm_pos.le).trans_lt hz_gt_am
          exact_mod_cast this.le
        have hznat_eq : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hz_nonneg
        have hznat_lt : z.toNat < n + 1 := by
          have hlt_m : ((z.toNat : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) :=
            hznat_eq.trans_lt (hz_lt_cm.trans_le (mul_le_of_le_one_left hm_pos.le hc1))
          exact_mod_cast hlt_m
        have hgk : g z.toNat = (z : ℝ) / m := by
          simp [g, unitDxSeq, m, hznat_eq, div_eq_mul_inv]
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hznat_lt, hJ_open ⟨?_, ?_⟩⟩
        · rw [hgk, lt_div_iff₀ hm_pos]; exact hz_gt_am
        · rw [hgk, div_lt_iff₀ hm_pos]; exact hz_lt_cm
      have hZ_inj : Set.InjOn Int.toNat (Z : Set ℤ) := by
        intro z₁ hz₁ z₂ hz₂ heq
        have hnn : ∀ z ∈ (Z : Set ℤ), 0 ≤ z := fun z hz ↦ by
          have hz_gt : a * m < (z : ℝ) :=
            (Int.lt_floor_add_one (a * m)).trans_le (by exact_mod_cast (Finset.mem_Icc.1 hz).1)
          have : (0 : ℝ) < (z : ℝ) := (mul_nonneg ha0 hm_pos.le).trans_lt hz_gt
          exact_mod_cast this.le
        have h1 := Int.toNat_of_nonneg (hnn z₁ hz₁)
        have h2 := Int.toNat_of_nonneg (hnn z₂ hz₂)
        omega
      have hcard_ge : Z.card ≤ F.card := by
        rw [← Finset.card_image_of_injOn hZ_inj]
        exact Finset.card_le_card hZ_sub
      rw [le_div_iff₀ hm_pos]
      have hmul : ((c - a) - 2 / m) * m = (c - a) * m - 2 := by
        rw [sub_mul, div_mul_cancel₀ _ hm_pos.ne']
      rw [hmul]
      exact hlb_int.trans (by exact_mod_cast hcard_ge)
  · -- Inject `F` into `Finset.Icc ⌈a * m⌉ ⌊c * m⌋` via `Nat.cast : ℕ → ℤ`.
    let W := Finset.Icc ⌈a * m⌉ ⌊c * m⌋
    have hF_sub : F.image (Nat.cast : ℕ → ℤ) ⊆ W := by
      intro z hz
      obtain ⟨k, hkF, rfl⟩ := Finset.mem_image.1 hz
      obtain ⟨ha_le, hc_ge⟩ := hJ_closed (Finset.mem_filter.1 hkF).2
      have hgk : g k = (k : ℝ) / m := by simp [g, unitDxSeq, m, div_eq_mul_inv]
      rw [hgk, le_div_iff₀ hm_pos] at ha_le
      rw [hgk, div_le_iff₀ hm_pos] at hc_ge
      exact Finset.mem_Icc.2
        ⟨Int.ceil_le.2 (by exact_mod_cast ha_le), Int.le_floor.2 (by exact_mod_cast hc_ge)⟩
    have hcard_le : F.card ≤ W.card := by
      rw [← Finset.card_image_of_injective F (fun _ _ h ↦ Int.ofNat_inj.1 h)]
      exact Finset.card_le_card hF_sub
    rw [div_le_iff₀ hm_pos]
    have hmul : ((c - a) + 1 / m) * m = (c - a) * m + 1 := by
      rw [add_mul, div_mul_cancel₀ _ hm_pos.ne']
    rw [hmul]
    exact (by exact_mod_cast hcard_le : (F.card : ℝ) ≤ (W.card : ℝ)).trans hub_int

/-- **Internal Interval Measure on `UnitGrid`**:
For any `0 ≤ a ≤ c ≤ 1` and any real interval `J` with `Set.Ioo a c ⊆ J ⊆ Set.Icc a c` (in
particular `Set.Ioo a c`, `Set.Ioc a c`, `Set.Ico a c`, and `Set.Icc a c`), the hyperfinite slice
`A_J = {x : UnitGrid | x.1 ∈ starSet J}` belongs to `M_unit.𝒜`, satisfies
`M_unit.μ A_J ≈ₕ ((c - a : ℝ) : ℝ*)`, `shadow (M_unit.μ A_J) = c - a`, and
`M_unit.loebMeasure A_J = ENNReal.ofReal (c - a)`! -/
theorem M_unit_starInterval_measure {a c : ℝ} (ha0 : 0 ≤ a) (hac : a ≤ c) (hc1 : c ≤ 1)
    {J : Set ℝ} (hJ_open : Set.Ioo a c ⊆ J) (hJ_closed : J ⊆ Set.Icc a c) :
    let A : Set UnitGrid := {x : UnitGrid | x.1 ∈ starSet J}
    A ∈ M_unit.𝒜 ∧
    M_unit.IsLoebMeasurable A ∧
    (M_unit.μ A ≈ₕ ((c - a : ℝ) : ℝ*)) ∧
    shadow (M_unit.μ A) = c - a ∧
    M_unit.loebMeasure A = ENNReal.ofReal (c - a) := by
  intro A
  let X : ℕ → Set ℝ := fun n ↦ (unitGridFinset n : Set ℝ) ∩ J
  have hImg : ((Subtype.val : UnitGrid → ℝ*) '' A) = internalSet X := by
    have hpre : A = (Subtype.val : UnitGrid → ℝ*) ⁻¹' starSet J := rfl
    rw [hpre, Subtype.image_preimage_coe]
    change unitGridSet ∩ starSet J = internalSet X
    rw [← internalSet_const J, unitGridSet, hyperStepPartition, ← internalSet_inter]
    rfl
  have hA_mem : A ∈ M_unit.𝒜 := ⟨X, fun _ ↦ Set.inter_subset_left, hImg⟩
  have hμ_unfold : M_unit.μ A =
      ofSeq (fun n ↦ ∑ x ∈ (unitGridFinset n).filter (fun x ↦ x ∈ hA_mem.choose n), unitDxSeq n) :=
    dite_eq_left hA_mem
  have hμ_eq : M_unit.μ A =
      ofSeq (fun n ↦ ∑ x ∈ (unitGridFinset n).filter (fun x ↦ x ∈ X n), unitDxSeq n) := by
    rw [hμ_unfold]
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), hA_mem.choose n = X n :=
      internalSet_eq_iff.1 (hA_mem.choose_spec.2.symm.trans hImg)
    exact Germ.coe_eq.2 (hev.mono fun n hn ↦ by dsimp only; simp_rw [hn])
  have hμ_if : M_unit.μ A =
      ofSeq (fun n ↦ ∑ x ∈ unitGridFinset n, if x ∈ J then unitDxSeq n else 0) := by
    rw [hμ_eq]
    refine Germ.coe_eq.2 (Eventually.of_forall fun n ↦ ?_)
    dsimp only
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun x hx ↦ by simp [X, Finset.mem_coe.2 hx]
  have hClose : M_unit.μ A ≈ₕ ((c - a : ℝ) : ℝ*) := by
    rw [hμ_if]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hε)
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
        |(∑ x ∈ unitGridFinset n, if x ∈ J then unitDxSeq n else 0) - (c - a)| < ε := by
      refine (Germ.coe_lt.1 (isUnlimitedNat_omegaNat N)).mono fun n (hn : N < n) ↦ ?_
      obtain ⟨hlb, hub⟩ := unitGridFinset_interval_density_bounds ha0 hac hc1 hJ_open hJ_closed n
      have h1 : 1 / ((n + 1 : ℕ) : ℝ) < ε / 2 :=
        lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by push_cast; gcongr)) hN
      have h2 : 2 / ((n + 1 : ℕ) : ℝ) < ε := by
        rw [show (2 : ℝ) / ((n + 1 : ℕ) : ℝ) = 2 * (1 / ((n + 1 : ℕ) : ℝ)) by ring]
        linarith
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    exact ofSeq_lt_ofSeq.2 hev
  have hSh : shadow (M_unit.μ A) = c - a := shadow_eq_of_infClose hClose
  have hLim : IsLimited (M_unit.μ A) :=
    isLimited_of_nonneg_le (M_unit.nonneg hA_mem)
      (M_unit.mu_mono hA_mem M_unit.univ_mem (Set.subset_univ _)) M_unit_basic_properties.2.2.2.1
  obtain ⟨hCar, hLoeb⟩ := M_unit.loebMeasure_properties.2.2 hA_mem
  rw [loebPremeasure, hyperrealToENNReal_of_isLimited hLim, hSh] at hLoeb
  exact ⟨hA_mem, hCar, hClose, hSh, hLoeb⟩

/-- Helper: on `UnitGrid`, `unitShadow ⁻¹' (Set.Ioo a c)` equals the increasing countable union of
internal closed-interval slices `{x | x.1 ∈ starSet (Set.Icc (a + 1/(k+1)) (c - 1/(k+1)))}`, and
`unitShadow ⁻¹' {r}` equals the decreasing countable intersection of
`{x | x.1 ∈ starSet (Set.Icc (r - 1/(k+1)) (r + 1/(k+1)))}`. -/
theorem unitShadow_preimage_Ioo_and_singleton :
    (∀ a c : ℝ,
      unitShadow ⁻¹' Set.Ioo a c =
        ⋃ k : ℕ, {x : UnitGrid |
          x.1 ∈ starSet (Set.Icc (a + 1 / ((k : ℝ) + 1)) (c - 1 / ((k : ℝ) + 1)))}) ∧
    (∀ r : ℝ,
      unitShadow ⁻¹' {r} =
        ⋂ k : ℕ, {x : UnitGrid |
          x.1 ∈ starSet (Set.Icc (r - 1 / ((k : ℝ) + 1)) (r + 1 / ((k : ℝ) + 1)))}) := by
  have hstar_Icc : ∀ (u v : ℝ) (y : ℝ*), y ∈ starSet (Set.Icc u v) ↔ (u : ℝ*) ≤ y ∧ y ≤ (v : ℝ*) := by
    intro u v y
    rcases ofSeq_surjective y with ⟨s, rfl⟩
    rw [ofSeq_mem_starSet]
    exact ⟨fun h ↦ ⟨ofSeq_le_ofSeq.2 (h.mono fun _ hi ↦ hi.1),
                     ofSeq_le_ofSeq.2 (h.mono fun _ hi ↦ hi.2)⟩,
           fun ⟨h1, h2⟩ ↦ ((ofSeq_le_ofSeq.1 h1).and (ofSeq_le_ofSeq.1 h2)).mono fun _ hi ↦ hi⟩
  refine ⟨fun a c ↦ ?_, fun r ↦ ?_⟩
  · ext x
    have hLim := (unitGrid_bounds x).2.2.1
    simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_iUnion, Set.mem_ofPred_eq, hstar_Icc,
      unitShadow]
    constructor
    · rintro ⟨hax, hxc⟩
      have hd_pos : 0 < min (shadow x.1 - a) (c - shadow x.1) / 2 :=
        half_pos (lt_min (sub_pos.2 hax) (sub_pos.2 hxc))
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hd_pos
      refine ⟨k, ?_, ?_⟩
      · have hinf := abs_lt.1 (infClose_shadow hLim (1 / ((k : ℝ) + 1)) (by positivity))
        have h1 : a + 2 * (1 / ((k : ℝ) + 1)) ≤ shadow x.1 := by
          linarith [min_le_left (shadow x.1 - a) (c - shadow x.1)]
        have hcast : ((a + 1 / ((k : ℝ) + 1) : ℝ) : ℝ*) + ((1 / ((k : ℝ) + 1) : ℝ) : ℝ*) ≤
            (shadow x.1 : ℝ*) := by
          exact_mod_cast (by linarith : a + 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) ≤ shadow x.1)
        linarith [hinf.1, hcast]
      · have hinf := abs_lt.1 (infClose_shadow hLim (1 / ((k : ℝ) + 1)) (by positivity))
        have h2 : shadow x.1 + 2 * (1 / ((k : ℝ) + 1)) ≤ c := by
          linarith [min_le_right (shadow x.1 - a) (c - shadow x.1)]
        have hcast : (shadow x.1 : ℝ*) + ((1 / ((k : ℝ) + 1) : ℝ) : ℝ*) ≤
            ((c - 1 / ((k : ℝ) + 1) : ℝ) : ℝ*) := by
          exact_mod_cast (by linarith : shadow x.1 + 1 / ((k : ℝ) + 1) ≤ c - 1 / ((k : ℝ) + 1))
        linarith [hinf.2, hcast]
    · rintro ⟨k, h1, h2⟩
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hs1 : a + 1 / ((k : ℝ) + 1) ≤ shadow x.1 := by
        have h := shadow_le_of_le (isLimited_coe _) hLim h1
        rwa [shadow_coe] at h
      have hs2 : shadow x.1 ≤ c - 1 / ((k : ℝ) + 1) := by
        have h := shadow_le_of_le hLim (isLimited_coe _) h2
        rwa [shadow_coe] at h
      exact ⟨by linarith, by linarith⟩
  · ext x
    have hLim := (unitGrid_bounds x).2.2.1
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq,
      hstar_Icc, unitShadow]
    constructor
    · rintro hsh k
      rw [← hsh]
      have hinf := abs_lt.1 (infClose_shadow hLim (1 / ((k : ℝ) + 1)) (by positivity))
      have hc1 : ((shadow x.1 - 1 / ((k : ℝ) + 1) : ℝ) : ℝ*) =
          (shadow x.1 : ℝ*) - ((1 / ((k : ℝ) + 1) : ℝ) : ℝ*) := by exact_mod_cast rfl
      have hc2 : ((shadow x.1 + 1 / ((k : ℝ) + 1) : ℝ) : ℝ*) =
          (shadow x.1 : ℝ*) + ((1 / ((k : ℝ) + 1) : ℝ) : ℝ*) := by exact_mod_cast rfl
      exact ⟨by linarith [hinf.1, hc1], by linarith [hinf.2, hc2]⟩
    · intro hall
      apply le_antisymm
      · refine le_of_forall_pos_le_add fun ε hε ↦ ?_
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
        have hs2 : shadow x.1 ≤ r + 1 / ((k : ℝ) + 1) := by
          have h := shadow_le_of_le hLim (isLimited_coe _) (hall k).2
          rwa [shadow_coe] at h
        linarith
      · refine le_of_forall_pos_le_add fun ε hε ↦ ?_
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
        have hs1 : r - 1 / ((k : ℝ) + 1) ≤ shadow x.1 := by
          have h := shadow_le_of_le (isLimited_coe _) hLim (hall k).1
          rwa [shadow_coe] at h
        linarith

/-- On `UnitGrid`:
1. Every singleton shadow fiber `unitShadow ⁻¹' {r}` (`r ∈ ℝ`) is Loeb measurable with Loeb measure `0`;
2. Every open-interval shadow fiber `unitShadow ⁻¹' Set.Ioo a c` (`a, c ∈ ℝ`) is Loeb measurable,
   and for `0 ≤ a ≤ c ≤ 1` has Loeb measure `ENNReal.ofReal (c - a)` (as does `unitShadow ⁻¹' Set.Icc a c`). -/
theorem M_unit_invShadow_interval_measure :
    (∀ r : ℝ,
      M_unit.IsLoebMeasurable (unitShadow ⁻¹' {r}) ∧
      M_unit.loebMeasure (unitShadow ⁻¹' {r}) = 0) ∧
    (∀ a c : ℝ, M_unit.IsLoebMeasurable (unitShadow ⁻¹' Set.Ioo a c)) ∧
    (∀ ⦃a c : ℝ⦄, 0 ≤ a → a ≤ c → c ≤ 1 →
      M_unit.loebMeasure (unitShadow ⁻¹' Set.Ioo a c) = ENNReal.ofReal (c - a) ∧
      M_unit.IsLoebMeasurable (unitShadow ⁻¹' Set.Icc a c) ∧
      M_unit.loebMeasure (unitShadow ⁻¹' Set.Icc a c) = ENNReal.ofReal (c - a)) := by
  have hSig := (isSigmaAlgebra_caratheodory M_unit.loebOuterMeasure).1
  have hStarMem : ∀ u v : ℝ,
      {x : UnitGrid | x.1 ∈ starSet (Set.Icc u v)} ∈ M_unit.𝒜 := by
    intro u v
    rw [M_unit_basic_properties.1]
    change IsInternal ((Subtype.val : UnitGrid → ℝ*) ''
      ((Subtype.val : UnitGrid → ℝ*) ⁻¹' starSet (Set.Icc u v)))
    rw [Subtype.image_preimage_coe]
    exact IsInternal.inter ⟨fun n ↦ (unitGridFinset n : Set ℝ), rfl⟩ (isInternal_starSet _)
  -- Part 1: Singletons
  have hSing : ∀ r : ℝ,
      M_unit.IsLoebMeasurable (unitShadow ⁻¹' {r}) ∧
      M_unit.loebMeasure (unitShadow ⁻¹' {r}) = 0 := by
    intro r
    have hCar : M_unit.IsLoebMeasurable (unitShadow ⁻¹' {r}) := by
      rw [unitShadow_preimage_Ioo_and_singleton.2 r]
      exact hSig.toIsSigmaRing.iInter_mem fun k ↦
        (M_unit.loebMeasure_properties.2.2 (hStarMem _ _)).1
    refine ⟨hCar, ?_⟩
    by_cases hr : r ∈ Set.Icc (0 : ℝ) 1
    · apply le_antisymm _ zero_le
      refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
      rw [zero_add]
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos (NNReal.coe_pos.2 hδ))
      let u := max 0 (r - 1 / ((k : ℝ) + 1))
      let v := min 1 (r + 1 / ((k : ℝ) + 1))
      have huv_sub : unitShadow ⁻¹' {r} ⊆ {x : UnitGrid | x.1 ∈ starSet (Set.Icc u v)} := by
        intro x hx
        have hmem_k : x ∈ {y : UnitGrid |
            y.1 ∈ starSet (Set.Icc (r - 1 / ((k : ℝ) + 1)) (r + 1 / ((k : ℝ) + 1)))} := by
          have hI := unitShadow_preimage_Ioo_and_singleton.2 r
          rw [hI] at hx
          exact Set.mem_iInter.1 hx k
        rcases ofSeq_surjective x.1 with ⟨s, hs⟩
        have h01 : ofSeq s ∈ starSet (Set.Icc 0 1) := by
          have hb := unitGrid_bounds x
          rw [← hs] at hb
          rw [ofSeq_mem_starSet]
          exact ((ofSeq_le_ofSeq.1 hb.1).and (ofSeq_le_ofSeq.1 hb.2.1)).mono fun _ h ↦ h
        have hrr : ofSeq s ∈ starSet (Set.Icc (r - 1 / ((k : ℝ) + 1)) (r + 1 / ((k : ℝ) + 1))) :=
          hs ▸ hmem_k
        change x.1 ∈ starSet (Set.Icc u v)
        rw [← hs, ofSeq_mem_starSet]
        exact ((ofSeq_mem_starSet.1 h01).and (ofSeq_mem_starSet.1 hrr)).mono fun _ ⟨h1, h2⟩ ↦
          ⟨max_le h1.1 h2.1, le_min h1.2 h2.2⟩
      have hu0 : 0 ≤ u := le_max_left _ _
      have hv1 : v ≤ 1 := min_le_left _ _
      have huv : u ≤ v := by
        have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        exact max_le (le_min (by norm_num) (by linarith [hr.1]))
          (le_min (by linarith [hr.2]) (by linarith))
      have hm_uv := (M_unit_starInterval_measure hu0 huv hv1
        Set.Ioo_subset_Icc_self Set.Subset.rfl).2.2.2.2
      have hv_sub_u : v - u ≤ 2 * (1 / ((k : ℝ) + 1)) := by
        have : u ≥ r - 1 / ((k : ℝ) + 1) := le_max_right _ _
        have : v ≤ r + 1 / ((k : ℝ) + 1) := min_le_right _ _
        linarith
      calc M_unit.loebMeasure (unitShadow ⁻¹' {r})
          ≤ M_unit.loebMeasure {x : UnitGrid | x.1 ∈ starSet (Set.Icc u v)} :=
            MeasureTheory.measure_mono huv_sub
        _ = ENNReal.ofReal (v - u) := hm_uv
        _ ≤ ENNReal.ofReal (2 * (1 / ((k : ℝ) + 1))) := ENNReal.ofReal_le_ofReal hv_sub_u
        _ ≤ (δ : ℝ≥0∞) := by
            rw [← ENNReal.ofReal_coe_nnreal]
            exact ENNReal.ofReal_le_ofReal (by linarith)
    · have hEmpty : unitShadow ⁻¹' {r} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hr (h ▸ (unitGrid_bounds x).2.2.2)
      simp [hEmpty]
  -- Part 2: Open intervals measurable for all `a, c : ℝ`
  have hIooCar : ∀ a c : ℝ, M_unit.IsLoebMeasurable (unitShadow ⁻¹' Set.Ioo a c) := by
    intro a c
    rw [unitShadow_preimage_Ioo_and_singleton.1 a c]
    exact hSig.toIsSigmaRing.iUnion_mem fun k ↦
      (M_unit.loebMeasure_properties.2.2 (hStarMem _ _)).1
  refine ⟨hSing, hIooCar, fun a c ha0 hac hc1 ↦ ?_⟩
  -- Part 3: Measure of `Ioo a c` and `Icc a c` for `0 ≤ a ≤ c ≤ 1`
  have hSubStar : unitShadow ⁻¹' Set.Ioo a c ⊆ {x : UnitGrid | x.1 ∈ starSet (Set.Icc a c)} := by
    rw [unitShadow_preimage_Ioo_and_singleton.1 a c]
    refine Set.iUnion_subset fun k x hx ↦ ?_
    rcases ofSeq_surjective x.1 with ⟨s, hs⟩
    change x.1 ∈ starSet (Set.Icc a c)
    rw [← hs, ofSeq_mem_starSet]
    have hxk : ofSeq s ∈ starSet (Set.Icc (a + 1 / ((k : ℝ) + 1)) (c - 1 / ((k : ℝ) + 1))) :=
      hs ▸ hx
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    exact (ofSeq_mem_starSet.1 hxk).mono fun _ ⟨h1, h2⟩ ↦ ⟨by linarith, by linarith⟩
  have hIoo_le : M_unit.loebMeasure (unitShadow ⁻¹' Set.Ioo a c) ≤ ENNReal.ofReal (c - a) :=
    (MeasureTheory.measure_mono hSubStar).trans_eq
      (M_unit_starInterval_measure ha0 hac hc1 Set.Ioo_subset_Icc_self Set.Subset.rfl).2.2.2.2
  have hIoo_ge : ENNReal.ofReal (c - a) ≤ M_unit.loebMeasure (unitShadow ⁻¹' Set.Ioo a c) := by
    rcases eq_or_lt_of_le hac with rfl | hlt
    · simp
    · refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
      have hd_pos : 0 < min ((c - a) / 2) ((δ : ℝ) / 2) :=
        lt_min (half_pos (sub_pos.2 hlt)) (half_pos (NNReal.coe_pos.2 hδ))
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hd_pos
      let u := a + 1 / ((k : ℝ) + 1)
      let v := c - 1 / ((k : ℝ) + 1)
      have hu0 : 0 ≤ u := by positivity
      have hv1 : v ≤ 1 := by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      have huv : u ≤ v := by
        have : 1 / ((k : ℝ) + 1) < (c - a) / 2 := hk.trans_le (min_le_left _ _)
        linarith
      have hSub_k : {x : UnitGrid | x.1 ∈ starSet (Set.Icc u v)} ⊆
          unitShadow ⁻¹' Set.Ioo a c := by
        rw [unitShadow_preimage_Ioo_and_singleton.1 a c]
        exact Set.subset_iUnion (fun j : ℕ ↦
          {x : UnitGrid | x.1 ∈ starSet (Set.Icc (a + 1 / ((j : ℝ) + 1))
            (c - 1 / ((j : ℝ) + 1)))}) k
      have hm_uv := (M_unit_starInterval_measure hu0 huv hv1
        Set.Ioo_subset_Icc_self Set.Subset.rfl).2.2.2.2
      have h2k_le : 2 * (1 / ((k : ℝ) + 1)) ≤ (δ : ℝ) := by
        have : 1 / ((k : ℝ) + 1) < (δ : ℝ) / 2 := hk.trans_le (min_le_right _ _)
        linarith
      have hca_le : ENNReal.ofReal (c - a) ≤ ENNReal.ofReal (v - u) + (δ : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_add (sub_nonneg.2 huv) (NNReal.coe_nonneg δ)]
        exact ENNReal.ofReal_le_ofReal (by dsimp [u, v]; linarith)
      exact hca_le.trans
        (add_le_add (hm_uv.symm.trans_le (MeasureTheory.measure_mono hSub_k)) le_rfl)
  have hIoo_eq : M_unit.loebMeasure (unitShadow ⁻¹' Set.Ioo a c) = ENNReal.ofReal (c - a) :=
    le_antisymm hIoo_le hIoo_ge
  have hIcc_decomp : unitShadow ⁻¹' Set.Icc a c =
      unitShadow ⁻¹' Set.Ioo a c ∪ unitShadow ⁻¹' {a} ∪ unitShadow ⁻¹' {c} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h1 with h1eq | h1lt
      · exact Or.inl (Or.inr h1eq.symm)
      · rcases eq_or_lt_of_le h2 with h2eq | h2lt
        · exact Or.inr h2eq
        · exact Or.inl (Or.inl ⟨h1lt, h2lt⟩)
    · rintro ((⟨h1, h2⟩ | rfl) | rfl)
      · exact ⟨h1.le, h2.le⟩
      · exact ⟨le_rfl, hac⟩
      · exact ⟨hac, le_rfl⟩
  have hIcc_car : M_unit.IsLoebMeasurable (unitShadow ⁻¹' Set.Icc a c) := by
    rw [hIcc_decomp]
    exact hSig.toIsSigmaRing.toIsSetRing.union_mem
      (hSig.toIsSigmaRing.toIsSetRing.union_mem (hIooCar a c) (hSing a).1) (hSing c).1
  have hIcc_eq : M_unit.loebMeasure (unitShadow ⁻¹' Set.Icc a c) = ENNReal.ofReal (c - a) := by
    apply le_antisymm
    · rw [hIcc_decomp]
      calc M_unit.loebMeasure (unitShadow ⁻¹' Set.Ioo a c ∪ unitShadow ⁻¹' {a} ∪ unitShadow ⁻¹' {c})
          ≤ M_unit.loebMeasure (unitShadow ⁻¹' Set.Ioo a c ∪ unitShadow ⁻¹' {a}) +
              M_unit.loebMeasure (unitShadow ⁻¹' {c}) :=
            MeasureTheory.measure_union_le _ _
        _ ≤ M_unit.loebMeasure (unitShadow ⁻¹' Set.Ioo a c) +
              M_unit.loebMeasure (unitShadow ⁻¹' {a}) +
              M_unit.loebMeasure (unitShadow ⁻¹' {c}) := by
            gcongr; exact MeasureTheory.measure_union_le _ _
        _ = ENNReal.ofReal (c - a) := by simp [hIoo_eq, (hSing a).2, (hSing c).2]
    · rw [← hIoo_eq]
      exact MeasureTheory.measure_mono (Set.preimage_mono Set.Ioo_subset_Icc_self)
  exact ⟨hIoo_eq, hIcc_car, hIcc_eq⟩

/-- Measurability of `unitShadow : UnitGrid → ℝ` and `unitSt : UnitGrid → unitInterval` with
respect to `M_unit.loebMeasurableSpace`. -/
theorem unitShadow_and_unitSt_measurable :
    @Measurable UnitGrid ℝ M_unit.loebMeasurableSpace _ unitShadow ∧
    @Measurable UnitGrid unitInterval M_unit.loebMeasurableSpace _ unitSt := by
  have hShMeas : @Measurable UnitGrid ℝ M_unit.loebMeasurableSpace _ unitShadow := by
    rw [BorelSpace.measurable_eq (α := ℝ), Real.borel_eq_generateFrom_Ioo_rat]
    refine @measurable_generateFrom UnitGrid ℝ M_unit.loebMeasurableSpace _ _ fun U hU ↦ ?_
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hU
    obtain ⟨p, q, _, rfl⟩ := hU
    exact M_unit_invShadow_interval_measure.2.1 p q
  exact ⟨hShMeas, hShMeas.subtype_mk⟩

/-- **Pushforward Theorem on `[0, 1]`**:
1. Pushing `M_unit.loebMeasure` forward along `unitShadow : UnitGrid → ℝ` yields
   `MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)`;
2. Pushing `M_unit.loebMeasure` forward along `unitSt : UnitGrid → unitInterval` yields Lebesgue
   measure `MeasureTheory.volume` on `unitInterval`! -/
theorem map_unitSt_loebMeasure_eq_volume :
    @MeasureTheory.Measure.map UnitGrid ℝ M_unit.loebMeasurableSpace _
      unitShadow M_unit.loebMeasure = MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1) ∧
    @MeasureTheory.Measure.map UnitGrid unitInterval M_unit.loebMeasurableSpace _
      unitSt M_unit.loebMeasure = MeasureTheory.volume := by
  have hShMeas := unitShadow_and_unitSt_measurable.1
  have hStMeas := unitShadow_and_unitSt_measurable.2
  have hMapReal : @MeasureTheory.Measure.map UnitGrid ℝ M_unit.loebMeasurableSpace _
      unitShadow M_unit.loebMeasure = MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1) := by
    refine (Real.measure_ext_Ioo_rat
      (μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
      (ν := @MeasureTheory.Measure.map UnitGrid ℝ M_unit.loebMeasurableSpace _
        unitShadow M_unit.loebMeasure)
      fun p q ↦ ?_).symm
    rw [@MeasureTheory.Measure.map_apply UnitGrid ℝ M_unit.loebMeasurableSpace _
      M_unit.loebMeasure unitShadow hShMeas _ isOpen_Ioo.measurableSet,
      MeasureTheory.Measure.restrict_apply isOpen_Ioo.measurableSet]
    set u := max (p : ℝ) 0
    set v := min (q : ℝ) 1
    by_cases huv : u < v
    · have hu0 : 0 ≤ u := le_max_right _ _
      have hv1 : v ≤ 1 := min_le_right _ _
      have hIoo_sub : Set.Ioo u v ⊆ Set.Ioo (p : ℝ) (q : ℝ) ∩ Set.Icc 0 1 := fun x ⟨h1, h2⟩ ↦
        ⟨⟨(le_max_left _ _).trans_lt h1, h2.trans_le (min_le_left _ _)⟩,
         ⟨hu0.trans h1.le, h2.le.trans hv1⟩⟩
      have hSub_Icc : Set.Ioo (p : ℝ) (q : ℝ) ∩ Set.Icc 0 1 ⊆ Set.Icc u v := fun x ⟨h1, h2⟩ ↦
        ⟨max_le h1.1.le h2.1, le_min h1.2.le h2.2⟩
      have hVol : MeasureTheory.volume (Set.Ioo (p : ℝ) (q : ℝ) ∩ Set.Icc 0 1) =
          ENNReal.ofReal (v - u) := by
        apply le_antisymm
        · exact (MeasureTheory.measure_mono hSub_Icc).trans_eq Real.volume_Icc
        · exact (Real.volume_Ioo (a := u) (b := v)).symm.trans_le
            (MeasureTheory.measure_mono hIoo_sub)
      have hPre_eq : unitShadow ⁻¹' Set.Ioo (p : ℝ) (q : ℝ) =
          unitShadow ⁻¹' (Set.Ioo (p : ℝ) (q : ℝ) ∩ Set.Icc 0 1) := by
        ext x; simp [unitShadow, (unitGrid_bounds x).2.2.2]
      have hLoeb : M_unit.loebMeasure (unitShadow ⁻¹' Set.Ioo (p : ℝ) (q : ℝ)) =
          ENNReal.ofReal (v - u) := by
        rw [hPre_eq]
        obtain ⟨hm_Ioo, _, hm_Icc⟩ := M_unit_invShadow_interval_measure.2.2 hu0 huv.le hv1
        apply le_antisymm
        · exact (MeasureTheory.measure_mono (Set.preimage_mono hSub_Icc)).trans_eq hm_Icc
        · exact hm_Ioo.symm.trans_le (MeasureTheory.measure_mono (Set.preimage_mono hIoo_sub))
      rw [hVol, hLoeb]
    · push Not at huv
      have hSubSingle : Set.Ioo (p : ℝ) (q : ℝ) ∩ Set.Icc 0 1 = ∅ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨hpx, hxq⟩, ⟨hx0, hx1⟩⟩
        have hux : u ≤ x := max_le hpx.le hx0
        have hxv : x ≤ v := le_min hxq.le hx1
        have hne : u < v := by
          by_cases hp0 : (p : ℝ) ≤ 0
          · have hu_eq : u = 0 := max_eq_right hp0
            have hv_pos : 0 < v := lt_min (hx0.trans_lt hxq) (by norm_num)
            linarith
          · push Not at hp0
            have hu_eq : u = (p : ℝ) := max_eq_left hp0.le
            have hpx_v : (p : ℝ) < v := lt_min (hpx.trans hxq) (hpx.trans_le hx1)
            linarith
        linarith
      have hPre_empty : unitShadow ⁻¹' Set.Ioo (p : ℝ) (q : ℝ) = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        intro hx
        have hmem : unitShadow x ∈ Set.Ioo (p : ℝ) (q : ℝ) ∩ Set.Icc 0 1 :=
          ⟨hx, (unitGrid_bounds x).2.2.2⟩
        rw [hSubSingle] at hmem
        exact hmem
      simp [hSubSingle, hPre_empty]
  refine ⟨hMapReal, ?_⟩
  ext s hs
  rw [@MeasureTheory.Measure.map_apply UnitGrid unitInterval M_unit.loebMeasurableSpace _
    M_unit.loebMeasure unitSt hStMeas s hs, unitInterval.volume_apply]
  have hImgMeas : MeasurableSet ((Subtype.val : unitInterval → ℝ) '' s) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc |>.measurableSet_image.2 hs
  have hPreImg : unitSt ⁻¹' s = unitShadow ⁻¹' ((Subtype.val : unitInterval → ℝ) '' s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    exact ⟨fun hx ↦ ⟨unitSt x, hx, rfl⟩,
      fun ⟨y, hy, hyx⟩ ↦ (Subtype.ext hyx : y = unitSt x) ▸ hy⟩
  have hSubIcc : ((Subtype.val : unitInterval → ℝ) '' s) ⊆ Set.Icc 0 1 :=
    Subtype.coe_image_subset (Set.Icc 0 1) s
  rw [hPreImg, ← @MeasureTheory.Measure.map_apply UnitGrid ℝ M_unit.loebMeasurableSpace _
    M_unit.loebMeasure unitShadow hShMeas _ hImgMeas, hMapReal,
    MeasureTheory.Measure.restrict_apply hImgMeas, Set.inter_eq_left.2 hSubIcc]

/-- **Goldblatt's Theorem on `[0, 1]`** (real subset form):
For **every** subset `E ⊆ Set.Icc (0 : ℝ) 1`:
1. `E` is **Lebesgue measurable** (`NullMeasurableSet E volume`) **if and only if** `unitShadow ⁻¹' E`
   is **Loeb measurable** (`M_unit.IsLoebMeasurable (unitShadow ⁻¹' E)`);
2. Whenever this holds, `M_unit.loebMeasure (unitShadow ⁻¹' E) = MeasureTheory.volume E`! -/
theorem nullMeasurableSet_iff_isLoebMeasurable_unitShadow {E : Set ℝ}
    (hE_sub : E ⊆ Set.Icc (0 : ℝ) 1) :
    (MeasureTheory.NullMeasurableSet E MeasureTheory.volume ↔
      M_unit.IsLoebMeasurable (unitShadow ⁻¹' E)) ∧
    (MeasureTheory.NullMeasurableSet E MeasureTheory.volume →
      M_unit.loebMeasure (unitShadow ⁻¹' E) = MeasureTheory.volume E) := by
  have hBorelEq : ∀ ⦃B : Set ℝ⦄, MeasurableSet B →
      M_unit.IsLoebMeasurable (unitShadow ⁻¹' B) ∧
      M_unit.loebMeasure (unitShadow ⁻¹' B) = MeasureTheory.volume (B ∩ Set.Icc 0 1) := by
    intro B hBm
    have hCar : M_unit.IsLoebMeasurable (unitShadow ⁻¹' B) :=
      unitShadow_and_unitSt_measurable.1 hBm
    have hEq : M_unit.loebMeasure (unitShadow ⁻¹' B) =
        MeasureTheory.volume (B ∩ Set.Icc 0 1) := by
      rw [← @MeasureTheory.Measure.map_apply UnitGrid ℝ M_unit.loebMeasurableSpace _
        M_unit.loebMeasure unitShadow unitShadow_and_unitSt_measurable.1 B hBm,
        map_unitSt_loebMeasure_eq_volume.1, MeasureTheory.Measure.restrict_apply hBm]
    exact ⟨hCar, hEq⟩
  -- Forward helper: Lebesgue measurable `E ⊆ [0, 1]` implies Loeb measurable with equal measure.
  have hFwd : MeasureTheory.NullMeasurableSet E MeasureTheory.volume →
      M_unit.IsLoebMeasurable (unitShadow ⁻¹' E) ∧
      M_unit.loebMeasure (unitShadow ⁻¹' E) = MeasureTheory.volume E := by
    intro hEnm
    obtain ⟨C, D, hCm, hDm, hCE, hED, hNull⟩ :=
      (nullMeasurableSet_volume_iff_borel_sandwich E).1 hEnm
    let C' := C ∩ Set.Icc 0 1
    let D' := D ∩ Set.Icc 0 1
    have hC'm : MeasurableSet C' := hCm.inter measurableSet_Icc
    have hD'm : MeasurableSet D' := hDm.inter measurableSet_Icc
    have hC'E : C' ⊆ E := Set.inter_subset_left.trans hCE
    have hED' : E ⊆ D' := Set.subset_inter hED hE_sub
    have hNull' : MeasureTheory.volume (D' \ C') = 0 :=
      MeasureTheory.measure_mono_null
        (show D' \ C' ⊆ D \ C from fun x ⟨hxD', hxC'⟩ ↦ ⟨hxD'.1, fun hxC ↦ hxC' ⟨hxC, hxD'.2⟩⟩)
        hNull
    have hLoebNull : M_unit.loebOuterMeasure (unitShadow ⁻¹' D' \ unitShadow ⁻¹' C') = 0 := by
      have hpre_diff : unitShadow ⁻¹' D' \ unitShadow ⁻¹' C' = unitShadow ⁻¹' (D' \ C') := rfl
      rw [hpre_diff, ← M_unit.loebMeasure_properties.2.1 (hBorelEq (hD'm.diff hC'm)).1,
        (hBorelEq (hD'm.diff hC'm)).2]
      exact MeasureTheory.measure_mono_null Set.inter_subset_left hNull'
    obtain ⟨hCarE, hmEC', _⟩ := isCaratheodoryMeasurable_of_sandwich M_unit.loebOuterMeasure
      (hBorelEq hC'm).1 (hBorelEq hD'm).1
      (Set.preimage_mono hC'E) (Set.preimage_mono hED') hLoebNull
    refine ⟨hCarE, ?_⟩
    rw [M_unit.loebMeasure_properties.2.1 hCarE, hmEC',
      ← M_unit.loebMeasure_properties.2.1 (hBorelEq hC'm).1, (hBorelEq hC'm).2,
      Set.inter_eq_left.2 (hC'E.trans hE_sub)]
    apply le_antisymm (MeasureTheory.measure_mono hC'E)
    calc MeasureTheory.volume E
        ≤ MeasureTheory.volume D' := MeasureTheory.measure_mono hED'
      _ ≤ MeasureTheory.volume (C' ∪ (D' \ C')) :=
          MeasureTheory.measure_mono fun x hx ↦
            if hxC : x ∈ C' then Or.inl hxC else Or.inr ⟨hx, hxC⟩
      _ ≤ MeasureTheory.volume C' + MeasureTheory.volume (D' \ C') :=
          MeasureTheory.measure_union_le _ _
      _ = MeasureTheory.volume C' := by rw [hNull', add_zero]
  -- Converse helper: closed inner approximation from `IsInternal.isClosed_shadowSet`!
  have hClosedInner : ∀ ⦃G : Set ℝ⦄, G ⊆ Set.Icc (0 : ℝ) 1 →
      M_unit.IsLoebMeasurable (unitShadow ⁻¹' G) →
      ∀ δ : ℝ, 0 < δ →
        ∃ K : Set ℝ, IsClosed K ∧ K ⊆ G ∧
          M_unit.loebOuterMeasure (unitShadow ⁻¹' (G \ K)) < ENNReal.ofReal δ := by
    intro G _ hG_car δ hδ
    have hFinG : M_unit.loebOuterMeasure (unitShadow ⁻¹' G) < ⊤ :=
      (MeasureTheory.measure_mono (Set.subset_univ _)).trans_lt
        ((M_unit.loebOuterMeasure_eq_of_mem M_unit.univ_mem).trans_lt
          (by rw [loebPremeasure, hyperrealToENNReal_of_isLimited M_unit_basic_properties.2.2.2.1,
                  M_unit_basic_properties.2.2.2.2.1]; exact ENNReal.ofReal_lt_top))
    obtain ⟨C, hC_mem, D, hD_mem, hCG, hGD, hDC_lt⟩ :=
      M_unit.isMuApproximable_of_isLoebMeasurable_of_lt_top hG_car hFinG δ hδ
    have hC_int : IsInternal ((Subtype.val : UnitGrid → ℝ*) '' C) := by
      have h𝒜 := M_unit_basic_properties.1
      rw [h𝒜] at hC_mem
      exact hC_mem
    let K : Set ℝ := shadowSet ((Subtype.val : UnitGrid → ℝ*) '' C)
    have hK_closed : IsClosed K := hC_int.isClosed_shadowSet
    have hKG : K ⊆ G := by
      rintro r ⟨y, ⟨x, hxC, rfl⟩, _, rfl⟩
      exact hCG hxC
    have hCK : C ⊆ unitShadow ⁻¹' K := fun x hxC ↦
      ⟨x.1, ⟨x, hxC, rfl⟩, (unitGrid_bounds x).2.2.1, rfl⟩
    have hSubDC : unitShadow ⁻¹' (G \ K) ⊆ D \ C :=
      fun x ⟨hxG, hxK⟩ ↦ ⟨hGD hxG, fun hxC ↦ hxK (hCK hxC)⟩
    refine ⟨K, hK_closed, hKG, ?_⟩
    exact (M_unit.loebOuterMeasure.mono hSubDC).trans_lt
      ((M_unit.loebOuterMeasure_eq_of_mem (M_unit.isSetRing.sdiff_mem hD_mem hC_mem)).trans_lt
        hDC_lt)
  refine ⟨⟨fun h ↦ (hFwd h).1, fun hCarE ↦ ?_⟩, fun h ↦ (hFwd h).2⟩
  -- Prove `NullMeasurableSet E volume` via §16.4(3) (`nullMeasurableSet_volume_iff_closed_open_approx`).
  rw [nullMeasurableSet_volume_iff_closed_open_approx]
  intro ε hε
  let F : Set ℝ := Set.Icc (0 : ℝ) 1 \ E
  have hPreF : unitShadow ⁻¹' F = (unitShadow ⁻¹' E)ᶜ := by
    ext x
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨(unitGrid_bounds x).2.2.2, h⟩⟩
  have hCarF : M_unit.IsLoebMeasurable (unitShadow ⁻¹' F) :=
    hPreF ▸ M_unit.loebOuterMeasure.isCaratheodory_compl hCarE
  obtain ⟨K, hKc, hKE, hEK_lt⟩ := hClosedInner hE_sub hCarE (ε / 4) (by linarith)
  obtain ⟨K', hK'c, hK'F, hFK'_lt⟩ := hClosedInner Set.sdiff_subset hCarF (ε / 4) (by linarith)
  let U : Set ℝ := Set.Ioo (-ε / 8) (1 + ε / 8) \ K'
  have hUo : IsOpen U := isOpen_Ioo.sdiff hK'c
  have hEU : E ⊆ U := fun x hxE ↦
    ⟨⟨by linarith [(hE_sub hxE).1], by linarith [(hE_sub hxE).2]⟩,
     fun hxK' ↦ (hK'F hxK').2 hxE⟩
  refine ⟨K, U, hKc, hUo, hKE, hEU, ?_⟩
  -- Decompose `U \ K ⊆ ((U \ K) ∩ Icc 0 1) ∪ Ioo (-ε/8) 0 ∪ Ioo 1 (1 + ε/8)`
  have hUK_decomp : U \ K ⊆
      ((U \ K) ∩ Set.Icc 0 1) ∪ Set.Ioo (-ε / 8) 0 ∪ Set.Ioo 1 (1 + ε / 8) := by
    rintro x ⟨⟨⟨hx1, hx2⟩, hxK'⟩, hxK⟩
    by_cases hx0 : x < 0
    · exact Or.inl (Or.inr ⟨hx1, hx0⟩)
    · by_cases hx1' : 1 < x
      · exact Or.inr ⟨hx1', hx2⟩
      · push Not at hx0 hx1'
        exact Or.inl (Or.inl ⟨⟨⟨⟨hx1, hx2⟩, hxK'⟩, hxK⟩, ⟨hx0, hx1'⟩⟩)
  have hUK_borel : MeasurableSet ((U \ K) ∩ Set.Icc 0 1) :=
    (hUo.measurableSet.diff hKc.measurableSet).inter measurableSet_Icc
  have hVol_mid : MeasureTheory.volume ((U \ K) ∩ Set.Icc 0 1) <
      ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by
    have hEqLoeb := (hBorelEq hUK_borel).2
    rw [Set.inter_assoc, Set.inter_self] at hEqLoeb
    rw [← hEqLoeb, M_unit.loebMeasure_properties.2.1 (hBorelEq hUK_borel).1]
    have hPreSub : unitShadow ⁻¹' ((U \ K) ∩ Set.Icc 0 1) ⊆
        unitShadow ⁻¹' (E \ K) ∪ unitShadow ⁻¹' (F \ K') := by
      rintro x ⟨⟨⟨_, hxK'⟩, hxK⟩, hxI⟩
      by_cases hxE : unitShadow x ∈ E
      · exact Or.inl ⟨hxE, hxK⟩
      · exact Or.inr ⟨⟨hxI, hxE⟩, hxK'⟩
    exact (M_unit.loebOuterMeasure.mono hPreSub).trans_lt
      ((MeasureTheory.measure_union_le _ _).trans_lt (ENNReal.add_lt_add hEK_lt hFK'_lt))
  have hVol_tails : MeasureTheory.volume (Set.Ioo (-ε / 8) 0) +
      MeasureTheory.volume (Set.Ioo 1 (1 + ε / 8)) = ENNReal.ofReal (ε / 4) := by
    rw [Real.volume_Ioo, Real.volume_Ioo,
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1; ring
  have h34_lt : ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) <
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by linarith) (by linarith),
      ENNReal.ofReal_lt_ofReal_iff hε]
    linarith
  calc MeasureTheory.volume (U \ K)
      ≤ MeasureTheory.volume
          (((U \ K) ∩ Set.Icc 0 1) ∪ Set.Ioo (-ε / 8) 0 ∪ Set.Ioo 1 (1 + ε / 8)) :=
        MeasureTheory.measure_mono hUK_decomp
    _ ≤ MeasureTheory.volume (((U \ K) ∩ Set.Icc 0 1) ∪ Set.Ioo (-ε / 8) 0) +
          MeasureTheory.volume (Set.Ioo 1 (1 + ε / 8)) :=
        MeasureTheory.measure_union_le _ _
    _ ≤ MeasureTheory.volume ((U \ K) ∩ Set.Icc 0 1) +
          MeasureTheory.volume (Set.Ioo (-ε / 8) 0) +
          MeasureTheory.volume (Set.Ioo 1 (1 + ε / 8)) := by
        gcongr; exact MeasureTheory.measure_union_le _ _
    _ = MeasureTheory.volume ((U \ K) ∩ Set.Icc 0 1) +
          (MeasureTheory.volume (Set.Ioo (-ε / 8) 0) +
            MeasureTheory.volume (Set.Ioo 1 (1 + ε / 8))) := add_assoc _ _ _
    _ = MeasureTheory.volume ((U \ K) ∩ Set.Icc 0 1) + ENNReal.ofReal (ε / 4) := by
        rw [hVol_tails]
    _ < (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) + ENNReal.ofReal (ε / 4) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hVol_mid
    _ < ENNReal.ofReal ε := h34_lt

/-- **Goldblatt's Theorem on `unitInterval`** (`[0, 1]` subtype form):
For **every** subset `E' : Set unitInterval`:
1. `NullMeasurableSet E' volume ↔ M_unit.IsLoebMeasurable (unitSt ⁻¹' E')`;
2. When this holds, `M_unit.loebMeasure (unitSt ⁻¹' E') = MeasureTheory.volume E'`! -/
theorem nullMeasurableSet_iff_isLoebMeasurable_unitSt (E' : Set unitInterval) :
    (MeasureTheory.NullMeasurableSet E' MeasureTheory.volume ↔
      M_unit.IsLoebMeasurable (unitSt ⁻¹' E')) ∧
    (MeasureTheory.NullMeasurableSet E' MeasureTheory.volume →
      M_unit.loebMeasure (unitSt ⁻¹' E') = MeasureTheory.volume E') := by
  let E : Set ℝ := (Subtype.val : unitInterval → ℝ) '' E'
  have hE_sub : E ⊆ Set.Icc (0 : ℝ) 1 := Subtype.coe_image_subset (Set.Icc 0 1) E'
  have hPre : unitSt ⁻¹' E' = unitShadow ⁻¹' E := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image, E]
    exact ⟨fun hx ↦ ⟨unitSt x, hx, rfl⟩,
      fun ⟨y, hy, hyx⟩ ↦ (Subtype.ext hyx : y = unitSt x) ▸ hy⟩
  have hNM_iff : MeasureTheory.NullMeasurableSet E' MeasureTheory.volume ↔
      MeasureTheory.NullMeasurableSet E MeasureTheory.volume := by
    constructor
    · intro hE'
      obtain ⟨C', hC'E', hC'm, hC'ae⟩ := hE'.exists_measurable_subset_ae_eq
      obtain ⟨D', hE'D', hD'm, hD'ae⟩ := hE'.exists_measurable_superset_ae_eq
      have hEmb := MeasurableEmbedding.subtype_coe (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc
      have hCm : MeasurableSet ((Subtype.val : unitInterval → ℝ) '' C') :=
        hEmb.measurableSet_image.2 hC'm
      have hDm : MeasurableSet ((Subtype.val : unitInterval → ℝ) '' D') :=
        hEmb.measurableSet_image.2 hD'm
      rw [nullMeasurableSet_volume_iff_borel_sandwich]
      refine ⟨_, _, hCm, hDm, Set.image_mono hC'E', Set.image_mono hE'D', ?_⟩
      rw [← Set.image_sdiff Subtype.val_injective, ← unitInterval.volume_apply]
      exact (MeasureTheory.ae_eq_set.1 (hC'ae.trans hD'ae.symm)).2
    · intro hE
      obtain ⟨C, D, hCm, hDm, hCE, hED, hNull⟩ :=
        (nullMeasurableSet_volume_iff_borel_sandwich E).1 hE
      let C' : Set unitInterval := (Subtype.val : unitInterval → ℝ) ⁻¹' C
      let D' : Set unitInterval := (Subtype.val : unitInterval → ℝ) ⁻¹' D
      have hC'm : MeasurableSet C' := hCm.preimage measurable_subtype_coe
      have hD'm : MeasurableSet D' := hDm.preimage measurable_subtype_coe
      have hC'E' : C' ⊆ E' := by
        intro y hy
        obtain ⟨z, hz, hzy⟩ := hCE hy
        exact Subtype.ext hzy ▸ hz
      have hE'D' : E' ⊆ D' := fun y hy ↦ hED ⟨y, hy, rfl⟩
      have hNull' : MeasureTheory.volume (D' \ C') = 0 := by
        rw [unitInterval.volume_apply]
        refine MeasureTheory.measure_mono_null ?_ hNull
        rintro x ⟨y, ⟨hyD, hyC⟩, rfl⟩
        exact ⟨hyD, hyC⟩
      have hE'C'_zero : MeasureTheory.volume (E' \ C') = 0 :=
        MeasureTheory.measure_mono_null (Set.sdiff_subset_sdiff_left hE'D') hNull'
      have hEq : E' = C' ∪ (E' \ C') := (Set.union_sdiff_cancel hC'E').symm
      rw [hEq]
      exact hC'm.nullMeasurableSet.union (MeasureTheory.NullMeasurableSet.of_null hE'C'_zero)
  have hMain := nullMeasurableSet_iff_isLoebMeasurable_unitShadow hE_sub
  rw [hPre, hNM_iff, unitInterval.volume_apply]
  exact hMain

/-! ### Part B: Full Real Line Hyperfinite Grid `S = {k / N : |k| ≤ N²}` (Goldblatt §16.8) -/

/-- Goldblatt §16.8 (p. 215): Finite rational grid `{k / m : k ∈ ℤ, |k| ≤ m²}` on `[-m, m]` at
positive integer resolution `m`. -/
def realLineGrid (m : ℕ) : Finset ℝ :=
  (Finset.Icc (-((m : ℤ) ^ 2)) ((m : ℤ) ^ 2)).image (fun k : ℤ ↦ (k : ℝ) / (m : ℝ))

/-- For every `m > 0`, `realLineGrid m` has exact cardinality `2 * m ^ 2 + 1` (Goldblatt §16.8,
p. 215). -/
theorem realLineGrid_card {m : ℕ} (hm : 0 < m) :
    (realLineGrid m).card = 2 * m ^ 2 + 1 := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 hm
  have hinj : Set.InjOn (fun k : ℤ ↦ (k : ℝ) / (m : ℝ))
      (Finset.Icc (-((m : ℤ) ^ 2)) ((m : ℤ) ^ 2)) :=
    fun k₁ _ k₂ _ heq ↦ Int.cast_inj.1 ((div_left_inj' hm_pos.ne').1 heq)
  rw [realLineGrid, Finset.card_image_of_injOn hinj, Int.card_Icc]
  have hval : ((m : ℤ) ^ 2) + 1 - -((m : ℤ) ^ 2) = ((2 * m ^ 2 + 1 : ℕ) : ℤ) := by
    push_cast; ring
  rw [hval, Int.toNat_natCast]

/-- Goldblatt §16.8 (p. 215): The hyperfinite real-line grid
`S = {k / N : k ∈ *ℤ, |k| ≤ N²} ⊆ [-N, N]` associated with `N = (b : ℕ*) ∈ ℕ*`. -/
def lineGridSet (b : ℕ → ℕ) : Set ℝ* :=
  internalSet (fun n ↦ (realLineGrid (b n) : Set ℝ))

/-- Type `LineGrid b` of points of Goldblatt's hyperfinite grid `S = lineGridSet b` on `ℝ*`. -/
abbrev LineGrid (b : ℕ → ℕ) : Type := ↥(lineGridSet b)

/-- Step-weight sequence `1 / b_n` representing `1 / N` on `LineGrid b`. -/
def lineDxSeq (b : ℕ → ℕ) (n : ℕ) : ℝ := 1 / (b n : ℝ)

/-- Goldblatt §16.8 (p. 215): For any unlimited hypernatural `N = (b : ℕ*)`, `lineGridSet b` is
hyperfinite of internal cardinality `2 * N ^ 2 + 1`. -/
theorem hasHypercard_lineGridSet {b : ℕ → ℕ} (hb : IsUnlimitedNat (b : ℕ*)) :
    HasHypercard (lineGridSet b) (2 * (b : ℕ*) ^ 2 + 1) := by
  refine ⟨fun n ↦ realLineGrid (b n), rfl, ?_⟩
  have hcard_eq : (2 * (b : ℕ*) ^ 2 + 1 : ℕ*) = ((fun n ↦ 2 * b n ^ 2 + 1) : ℕ*) := by
    rw [sq]
    exact Germ.coe_eq.2 (Eventually.of_forall fun n ↦ by
      change 2 * (b n * b n) + 1 = 2 * b n ^ 2 + 1; ring)
  rw [hcard_eq]
  exact Germ.coe_eq.2 ((Germ.coe_lt.1 (hb 0)).mono fun n (hn : 0 < b n) ↦
    (realLineGrid_card hn).symm)

/-- Goldblatt §16.8 (p. 215): Every standard real `r ∈ ℝ` is approximated infinitely closely on
either side by points of `LineGrid b` (`s ≤ r < s + 1/N`, hence `s ≈ₕ r`, `IsLimited s`, and
`shadow s = r`). -/
theorem lineGrid_approx_real {b : ℕ → ℕ} (hb : IsUnlimitedNat (b : ℕ*)) (r : ℝ) :
    ∃ x : LineGrid b,
      x.1 ≤ (r : ℝ*) ∧
      (r : ℝ*) < x.1 + (Hypernat.toHyperreal (b : ℕ*))⁻¹ ∧
      (x.1 ≈ₕ (r : ℝ*)) ∧
      IsLimited x.1 ∧
      shadow x.1 = r := by
  let k : ℕ → ℤ := fun n ↦
    if 0 < b n ∧ |r| < (b n : ℝ) then ⌊r * (b n : ℝ)⌋ else 0
  let s : ℕ → ℝ := fun n ↦ (k n : ℝ) / (b n : ℝ)
  have hs_mem : ∀ n : ℕ, s n ∈ (realLineGrid (b n) : Set ℝ) := fun n ↦ by
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨k n, Finset.mem_Icc.2 ?_, rfl⟩)
    by_cases h : 0 < b n ∧ |r| < (b n : ℝ)
    · rw [show k n = ⌊r * (b n : ℝ)⌋ from ite_eq_left h]
      obtain ⟨hpos_n, habs⟩ := h
      have hm_ge1 : (1 : ℝ) ≤ (b n : ℝ) := by exact_mod_cast hpos_n
      have hm_pos : (0 : ℝ) < (b n : ℝ) := by positivity
      obtain ⟨hr_lo, hr_hi⟩ := abs_lt.1 habs
      constructor
      · refine Int.le_floor.2 ?_
        have hlo : -((b n : ℝ) ^ 2) < r * (b n : ℝ) := by nlinarith
        exact (by push_cast; exact hlo.le)
      · have hhi : (⌊r * (b n : ℝ)⌋ : ℝ) < ((b n : ℝ) ^ 2) :=
          (Int.floor_le _).trans_lt (by nlinarith)
        have hhi' : (⌊r * (b n : ℝ)⌋ : ℝ) < (((b n : ℤ) ^ 2 : ℤ) : ℝ) := by
          simpa using hhi
        exact (Int.cast_lt.1 hhi').le
    · rw [show k n = 0 from ite_eq_right h]
      exact ⟨neg_nonpos.2 (sq_nonneg _), sq_nonneg _⟩
  let x : LineGrid b := ⟨ofSeq s, ofSeq_mem_internalSet.2 (Eventually.of_forall hs_mem)⟩
  obtain ⟨M, hM⟩ := exists_nat_gt |r|
  have hev_good : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < b n ∧ |r| < (b n : ℝ) := by
    refine (Germ.coe_lt.1 (hb (max 1 M))).mono fun n (hn : max 1 M < b n) ↦ ?_
    have h1 : 1 < b n := (le_max_left 1 M).trans_lt hn
    have h2 : M < b n := (le_max_right 1 M).trans_lt hn
    exact ⟨ by omega, hM.trans (by exact_mod_cast h2) ⟩
  have hx_le : x.1 ≤ (r : ℝ*) := by
    refine ofSeq_le_ofSeq.2 (hev_good.mono fun n hn ↦ ?_)
    have hm_pos : (0 : ℝ) < (b n : ℝ) := Nat.cast_pos.2 hn.1
    dsimp only [s]
    rw [show k n = ⌊r * (b n : ℝ)⌋ from ite_eq_left hn, div_le_iff₀ hm_pos]
    exact Int.floor_le _
  have hr_lt : (r : ℝ*) < x.1 + (Hypernat.toHyperreal (b : ℕ*))⁻¹ := by
    have hinv : (Hypernat.toHyperreal (b : ℕ*))⁻¹ = ofSeq (fun n ↦ (b n : ℝ)⁻¹) :=
      Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ rfl)
    rw [hinv]
    change ofSeq (fun _ ↦ r) < ofSeq (fun n ↦ s n + (b n : ℝ)⁻¹)
    refine ofSeq_lt_ofSeq.2 (hev_good.mono fun n hn ↦ ?_)
    have hm_pos : (0 : ℝ) < (b n : ℝ) := Nat.cast_pos.2 hn.1
    dsimp only [s]
    rw [show k n = ⌊r * (b n : ℝ)⌋ from ite_eq_left hn, ← one_div, ← add_div, lt_div_iff₀ hm_pos]
    exact Int.lt_floor_add_one _
  have hClose : x.1 ≈ₕ (r : ℝ*) := by
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
    have hevK : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), K + 1 < b n :=
      Germ.coe_lt.1 (hb (K + 1))
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |s n - r| < ε := by
      refine (hev_good.and hevK).mono fun n ⟨hn, hnK⟩ ↦ ?_
      have hm_pos : (0 : ℝ) < (b n : ℝ) := Nat.cast_pos.2 hn.1
      dsimp only [s]
      rw [show k n = ⌊r * (b n : ℝ)⌋ from ite_eq_left hn]
      have hlo : (⌊r * (b n : ℝ)⌋ : ℝ) / (b n : ℝ) ≤ r :=
        (div_le_iff₀ hm_pos).2 (Int.floor_le _)
      have hhi : r - (⌊r * (b n : ℝ)⌋ : ℝ) / (b n : ℝ) < 1 / (b n : ℝ) := by
        rw [sub_lt_iff_lt_add', ← add_div, lt_div_iff₀ hm_pos]
        exact Int.lt_floor_add_one _
      have hbn_le : 1 / (b n : ℝ) ≤ 1 / ((K : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hnK.le)
      rw [abs_lt]
      exact ⟨by linarith [hhi.trans_le hbn_le], by linarith⟩
    exact ofSeq_lt_ofSeq.2 hev
  have hLim : IsLimited x.1 := by
    obtain ⟨h1, h2⟩ := abs_lt.1 (hClose 1 one_pos)
    refine isLimited_iff_exists_real.2 ⟨r - 1, r + 1, ?_, ?_⟩
    · simp only [Hyperreal.coe_sub] at *; linarith
    · simp only [Hyperreal.coe_add] at *; linarith
  exact ⟨x, hx_le, hr_lt, hClose, hLim, shadow_eq_of_infClose hClose⟩

/-- Goldblatt §16.8 (p. 215): The weighted hyperfinite internal measure algebra `M_line b` on
`LineGrid b`, assigning `μ(A) = |A| / N` to each internal subset `A ∈ 𝒫_I(lineGridSet b)`. -/
def M_line (b : ℕ → ℕ) : InternalMeasureAlgebra (LineGrid b) :=
  hyperfiniteWeightedAlgebra (fun n ↦ realLineGrid (b n)) (fun n _ ↦ lineDxSeq b n)
    (fun n _ _ ↦ by simp [lineDxSeq])

/-- Basic properties of `M_line b` for an unlimited hypernatural `N = (b : ℕ*)` (Goldblatt §16.8,
p. 215):
1. `(M_line b).𝒜 = internalSubsetAlgebra (lineGridSet b)`;
2. For every `A` with `HasHypercard ((↑) '' A) K`,
   `(M_line b).μ A = K.toHyperreal / (b : ℕ*).toHyperreal`;
3. `(M_line b).μ Set.univ` is positive unlimited (`≈ 2N + 1/N`), and
   `(M_line b).loebMeasure Set.univ = ⊤`. -/
theorem M_line_basic_properties {b : ℕ → ℕ} (hb : IsUnlimitedNat (b : ℕ*)) :
    (M_line b).𝒜 = internalSubsetAlgebra (lineGridSet b) ∧
    (∀ (A : Set (LineGrid b)) (K : ℕ*),
      HasHypercard ((Subtype.val : LineGrid b → ℝ*) '' A) K →
      (M_line b).μ A = Hypernat.toHyperreal K / Hypernat.toHyperreal (b : ℕ*)) ∧
    IsPosUnlimited ((M_line b).μ Set.univ) ∧
    (M_line b).loebMeasure Set.univ = ⊤ := by
  have hspec := hyperfiniteWeightedAlgebra_spec (fun n ↦ realLineGrid (b n))
    (fun n _ ↦ lineDxSeq b n) (fun n _ _ ↦ by simp [lineDxSeq])
  have hdiv : ∀ (A : Set (LineGrid b)) (K : ℕ*),
      HasHypercard ((Subtype.val : LineGrid b → ℝ*) '' A) K →
      (M_line b).μ A = Hypernat.toHyperreal K / Hypernat.toHyperreal (b : ℕ*) := by
    intro A K hK
    dsimp only [M_line]
    rw [hspec.2.2 (lineDxSeq b) (fun _ _ _ ↦ rfl) A K hK]
    have hinv : ofSeq (lineDxSeq b) = (Hypernat.toHyperreal (b : ℕ*))⁻¹ :=
      Germ.coe_eq.2 (Eventually.of_forall fun n ↦ by simp [lineDxSeq])
    rw [hinv, div_eq_mul_inv]
  have hUniv_img : ((Subtype.val : LineGrid b → ℝ*) '' Set.univ) = lineGridSet b := by simp
  have hUniv_ge : Hypernat.toHyperreal (b : ℕ*) ≤ (M_line b).μ Set.univ := by
    rw [hdiv Set.univ (2 * (b : ℕ*) ^ 2 + 1) (hUniv_img.symm ▸ hasHypercard_lineGridSet hb)]
    have hcard_eq : (2 * (b : ℕ*) ^ 2 + 1 : ℕ*) = ((fun n ↦ 2 * b n ^ 2 + 1) : ℕ*) := by
      rw [sq]
      exact Germ.coe_eq.2 (Eventually.of_forall fun n ↦ by
        change 2 * (b n * b n) + 1 = 2 * b n ^ 2 + 1; ring)
    have hnum_eq : Hypernat.toHyperreal (2 * (b : ℕ*) ^ 2 + 1) =
        ofSeq (fun n ↦ ((2 * b n ^ 2 + 1 : ℕ) : ℝ)) := by
      rw [hcard_eq]; rfl
    have hden_eq : Hypernat.toHyperreal (b : ℕ*) = ofSeq (fun n ↦ (b n : ℝ)) := rfl
    rw [hnum_eq, hden_eq]
    change ofSeq (fun n ↦ (b n : ℝ)) ≤
      ofSeq (fun n ↦ ((2 * b n ^ 2 + 1 : ℕ) : ℝ) / (b n : ℝ))
    refine ofSeq_le_ofSeq.2 ((Germ.coe_lt.1 (hb 0)).mono fun n (hn : 0 < b n) ↦ ?_)
    have hm_pos : (0 : ℝ) < (b n : ℝ) := Nat.cast_pos.2 hn
    rw [le_div_iff₀ hm_pos]
    push_cast
    nlinarith
  have hPosUnl : IsPosUnlimited ((M_line b).μ Set.univ) := fun r ↦
    ((isUnlimitedNat_iff_isPosUnlimited.1 hb) r).trans_le hUniv_ge
  have hNotLim : ¬ IsLimited ((M_line b).μ Set.univ) := by
    rintro ⟨n, hn⟩
    exact not_lt_of_ge (abs_lt.1 hn).2.le (hPosUnl (n : ℝ))
  have hLoeb : (M_line b).loebMeasure Set.univ = ⊤ := by
    rw [((M_line b).loebMeasure_properties.2.2 (M_line b).univ_mem).2, loebPremeasure,
      hyperrealToENNReal_of_not_isLimited hNotLim]
  exact ⟨hspec.1, hdiv, hPosUnl, hLoeb⟩

/-- Finite counting bound on `realLineGrid m` (`m > 0`, `max |a| |c| ≤ m`): for any `a ≤ c` and any
`J : Set ℝ` with `Set.Ioo a c ⊆ J ⊆ Set.Icc a c`, the weighted count of `realLineGrid m ∩ J` lies
in `[(c - a) - 2 / m, (c - a) + 1 / m]`. -/
theorem realLineGrid_interval_density_bounds {a c : ℝ} (hac : a ≤ c) {J : Set ℝ}
    (hJ_open : Set.Ioo a c ⊆ J) (hJ_closed : J ⊆ Set.Icc a c) {m : ℕ} (hm : 0 < m)
    (hbd : max |a| |c| ≤ (m : ℝ)) :
    (c - a) - 2 / (m : ℝ) ≤ (∑ x ∈ realLineGrid m, if x ∈ J then lineDxSeq id m else 0) ∧
    (∑ x ∈ realLineGrid m, if x ∈ J then lineDxSeq id m else 0) ≤ (c - a) + 1 / (m : ℝ) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 hm
  let I_m : Finset ℤ := Finset.Icc (-((m : ℤ) ^ 2)) ((m : ℤ) ^ 2)
  let g : ℤ → ℝ := fun k ↦ (k : ℝ) / (m : ℝ)
  have hg_inj : Set.InjOn g I_m := fun k₁ _ k₂ _ heq ↦
    Int.cast_inj.1 ((div_left_inj' hm_pos.ne').1 heq)
  have hsum_eq : (∑ x ∈ realLineGrid m, if x ∈ J then lineDxSeq id m else 0) =
      (((I_m.filter (fun k ↦ g k ∈ J)).card : ℕ) : ℝ) / (m : ℝ) := by
    change (∑ x ∈ I_m.image g, if x ∈ J then lineDxSeq id m else 0) = _
    rw [Finset.sum_image hg_inj, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    simp [lineDxSeq, div_eq_mul_inv]
  rw [hsum_eq]
  set F := I_m.filter (fun k ↦ g k ∈ J)
  obtain ⟨hub_int, hlb_int⟩ := int_Icc_card_bounds hac hm_pos.le
  have ha_abs : |a| ≤ (m : ℝ) := (le_max_left |a| |c|).trans hbd
  have hc_abs : |c| ≤ (m : ℝ) := (le_max_right |a| |c|).trans hbd
  constructor
  · rcases eq_or_lt_of_le hac with rfl | hlt
    · rw [sub_self, zero_sub]
      linarith [(by positivity : (0 : ℝ) ≤ 2 / (m : ℝ)),
                (by positivity : (0 : ℝ) ≤ (F.card : ℝ) / (m : ℝ))]
    · have hZ_sub : Finset.Icc (⌊a * (m : ℝ)⌋ + 1) (⌈c * (m : ℝ)⌉ - 1) ⊆ F := by
        intro z hz
        obtain ⟨hz1, hz2⟩ := Finset.mem_Icc.1 hz
        have hz_gt : a * (m : ℝ) < (z : ℝ) :=
          (Int.lt_floor_add_one (a * (m : ℝ))).trans_le (by exact_mod_cast hz1)
        have hz_lt : (z : ℝ) < c * (m : ℝ) :=
          (by exact_mod_cast hz2 : (z : ℝ) ≤ (⌈c * (m : ℝ)⌉ : ℝ) - 1).trans_lt
            (by linarith [Int.ceil_lt_add_one (c * (m : ℝ))])
        have ham_lo : -((m : ℝ) ^ 2) ≤ a * (m : ℝ) := by
          have : -(m : ℝ) ≤ a := (abs_le.1 ha_abs).1
          nlinarith
        have hcm_hi : c * (m : ℝ) ≤ (m : ℝ) ^ 2 := by
          have : c ≤ (m : ℝ) := (abs_le.1 hc_abs).2
          nlinarith
        have hz_Im : z ∈ I_m := by
          refine Finset.mem_Icc.2 ⟨?_, ?_⟩
          · have hlt' : ((-((m : ℤ) ^ 2) : ℤ) : ℝ) < (z : ℝ) := by
              simpa using ham_lo.trans_lt hz_gt
            exact (Int.cast_lt.1 hlt').le
          · have hlt' : (z : ℝ) < (((m : ℤ) ^ 2 : ℤ) : ℝ) := by
              simpa using hz_lt.trans_le hcm_hi
            exact (Int.cast_lt.1 hlt').le
        refine Finset.mem_filter.2 ⟨hz_Im, hJ_open ⟨?_, ?_⟩⟩
        · exact (lt_div_iff₀ hm_pos).2 hz_gt
        · exact (div_lt_iff₀ hm_pos).2 hz_lt
      have hcard_ge := Finset.card_le_card hZ_sub
      rw [le_div_iff₀ hm_pos]
      have hmul : ((c - a) - 2 / (m : ℝ)) * (m : ℝ) = (c - a) * (m : ℝ) - 2 := by
        rw [sub_mul, div_mul_cancel₀ _ hm_pos.ne']
      rw [hmul]
      exact hlb_int.trans (by exact_mod_cast hcard_ge)
  · have hF_sub : F ⊆ Finset.Icc ⌈a * (m : ℝ)⌉ ⌊c * (m : ℝ)⌋ := by
      intro z hz
      obtain ⟨ha_le, hc_ge⟩ := hJ_closed (Finset.mem_filter.1 hz).2
      rw [le_div_iff₀ hm_pos] at ha_le
      rw [div_le_iff₀ hm_pos] at hc_ge
      exact Finset.mem_Icc.2
        ⟨Int.ceil_le.2 (by exact_mod_cast ha_le), Int.le_floor.2 (by exact_mod_cast hc_ge)⟩
    have hcard_le := Finset.card_le_card hF_sub
    rw [div_le_iff₀ hm_pos]
    have hmul : ((c - a) + 1 / (m : ℝ)) * (m : ℝ) = (c - a) * (m : ℝ) + 1 := by
      rw [add_mul, div_mul_cancel₀ _ hm_pos.ne']
    rw [hmul]
    exact (by exact_mod_cast hcard_le : (F.card : ℝ) ≤ _).trans hub_int

/-- Goldblatt §16.8, **Theorem 16.8.1** & Remark (pp. 215–216):
For any unlimited hypernatural `N = (b : ℕ*)`, any `a ≤ c` in `ℝ`, and any interval `J` with
`Set.Ioo a c ⊆ J ⊆ Set.Icc a c` (hence all four intervals `(a, c)`, `(a, c]`, `[a, c)`, `[a, c]`),
the hyperfinite slice `A_J = {x : LineGrid b | x.1 ∈ starSet J}` belongs to `(M_line b).𝒜`, is Loeb
measurable, satisfies `(M_line b).μ A_J ≈ₕ ((c - a : ℝ) : ℝ*)`, and has Loeb measure
`ENNReal.ofReal (c - a)`! -/
theorem M_line_starInterval_measure {b : ℕ → ℕ} (hb : IsUnlimitedNat (b : ℕ*))
    {a c : ℝ} (hac : a ≤ c) {J : Set ℝ}
    (hJ_open : Set.Ioo a c ⊆ J) (hJ_closed : J ⊆ Set.Icc a c) :
    let A : Set (LineGrid b) := {x : LineGrid b | x.1 ∈ starSet J}
    A ∈ (M_line b).𝒜 ∧
    (M_line b).IsLoebMeasurable A ∧
    ((M_line b).μ A ≈ₕ ((c - a : ℝ) : ℝ*)) ∧
    shadow ((M_line b).μ A) = c - a ∧
    (M_line b).loebMeasure A = ENNReal.ofReal (c - a) := by
  intro A
  let X : ℕ → Set ℝ := fun n ↦ (realLineGrid (b n) : Set ℝ) ∩ J
  have hImg : ((Subtype.val : LineGrid b → ℝ*) '' A) = internalSet X := by
    have hpre : A = (Subtype.val : LineGrid b → ℝ*) ⁻¹' starSet J := rfl
    rw [hpre, Subtype.image_preimage_coe]
    change lineGridSet b ∩ starSet J = internalSet X
    rw [← internalSet_const J, lineGridSet, ← internalSet_inter]
  have hA_mem : A ∈ (M_line b).𝒜 := ⟨X, fun _ ↦ Set.inter_subset_left, hImg⟩
  have hμ_unfold : (M_line b).μ A =
      ofSeq (fun n ↦ ∑ x ∈ (realLineGrid (b n)).filter (fun x ↦ x ∈ hA_mem.choose n),
        lineDxSeq b n) := dite_eq_left hA_mem
  have hμ_if : (M_line b).μ A =
      ofSeq (fun n ↦ ∑ x ∈ realLineGrid (b n), if x ∈ J then lineDxSeq id (b n) else 0) := by
    rw [hμ_unfold]
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), hA_mem.choose n = X n :=
      internalSet_eq_iff.1 (hA_mem.choose_spec.2.symm.trans hImg)
    refine Germ.coe_eq.2 (hev.mono fun n hn ↦ ?_)
    dsimp only
    simp_rw [hn, Finset.sum_filter]
    exact Finset.sum_congr rfl fun x hx ↦ by simp [X, lineDxSeq, Finset.mem_coe.2 hx]
  have hClose : (M_line b).μ A ≈ₕ ((c - a : ℝ) : ℝ*) := by
    rw [hμ_if]
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨M, hM⟩ := exists_nat_gt (max |a| |c|)
    let B : ℕ := max (max 1 M) (K + 1)
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
        |(∑ x ∈ realLineGrid (b n), if x ∈ J then lineDxSeq id (b n) else 0) - (c - a)| < ε := by
      refine (Germ.coe_lt.1 (hb B)).mono fun n (hn : B < b n) ↦ ?_
      have hpos_bn : 0 < b n := by
        have : 1 ≤ B := le_trans (le_max_left 1 M) (le_max_left _ _)
        omega
      have hbd_bn : max |a| |c| ≤ (b n : ℝ) := by
        have hMB : M < b n := lt_of_le_of_lt
          (le_trans (le_max_right 1 M) (le_max_left _ _)) hn
        exact hM.le.trans (by exact_mod_cast hMB.le)
      have hK_bn : K + 1 < b n := lt_of_le_of_lt (le_max_right _ _) hn
      obtain ⟨hlb, hub⟩ := realLineGrid_interval_density_bounds hac hJ_open hJ_closed hpos_bn hbd_bn
      have h1 : 1 / (b n : ℝ) < ε / 2 :=
        lt_of_le_of_lt
          (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hK_bn.le)) hK
      have h2 : 2 / (b n : ℝ) < ε := by
        rw [show (2 : ℝ) / (b n : ℝ) = 2 * (1 / (b n : ℝ)) by ring]; linarith
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    exact ofSeq_lt_ofSeq.2 hev
  have hSh : shadow ((M_line b).μ A) = c - a := shadow_eq_of_infClose hClose
  have hLim : IsLimited ((M_line b).μ A) := by
    obtain ⟨h1, h2⟩ := abs_lt.1 (hClose 1 one_pos)
    refine isLimited_iff_exists_real.2 ⟨(c - a) - 1, (c - a) + 1, ?_, ?_⟩
    · simp only [Hyperreal.coe_sub] at *; linarith
    · simp only [Hyperreal.coe_add] at *; linarith
  obtain ⟨hCar, hLoeb⟩ := (M_line b).loebMeasure_properties.2.2 hA_mem
  rw [loebPremeasure, hyperrealToENNReal_of_isLimited hLim, hSh] at hLoeb
  exact ⟨hA_mem, hCar, hClose, hSh, hLoeb⟩

/-- Goldblatt §16.8, Theorem 16.8.1 & Corollary (p. 216): All four interval slices `S ∩ *(a, c)`,
`S ∩ *(a, c]`, `S ∩ *[a, c)`, and `S ∩ *[a, c]` have Loeb measure `ENNReal.ofReal (c - a)` for
`a ≤ c`. -/
theorem M_line_starInterval_four_forms {b : ℕ → ℕ} (hb : IsUnlimitedNat (b : ℕ*))
    {a c : ℝ} (hac : a ≤ c) :
    (M_line b).loebMeasure {x : LineGrid b | x.1 ∈ starSet (Set.Ioo a c)} =
      ENNReal.ofReal (c - a) ∧
    (M_line b).loebMeasure {x : LineGrid b | x.1 ∈ starSet (Set.Ioc a c)} =
      ENNReal.ofReal (c - a) ∧
    (M_line b).loebMeasure {x : LineGrid b | x.1 ∈ starSet (Set.Ico a c)} =
      ENNReal.ofReal (c - a) ∧
    (M_line b).loebMeasure {x : LineGrid b | x.1 ∈ starSet (Set.Icc a c)} =
      ENNReal.ofReal (c - a) :=
  ⟨(M_line_starInterval_measure hb hac Set.Subset.rfl Set.Ioo_subset_Icc_self).2.2.2.2,
   (M_line_starInterval_measure hb hac Set.Ioo_subset_Ioc_self Set.Ioc_subset_Icc_self).2.2.2.2,
   (M_line_starInterval_measure hb hac Set.Ioo_subset_Ico_self Set.Ico_subset_Icc_self).2.2.2.2,
   (M_line_starInterval_measure hb hac Set.Ioo_subset_Icc_self Set.Subset.rfl).2.2.2.2⟩

/-- Goldblatt §16.8 **`*ℚ` Counterexample** (p. 216): Every grid point in `lineGridSet b` is a
hyperrational (`lineGridSet b ⊆ *ℚ`), so `S ∩ *ℚ = S` has Loeb measure `⊤`, whereas `ℚ ⊆ ℝ` has
Lebesgue measure `0` (`volume ℚ ≠ μ_L(S ∩ *ℚ)`). -/
theorem M_line_starRat_counterexample {b : ℕ → ℕ} (hb : IsUnlimitedNat (b : ℕ*)) :
    let Q : Set ℝ := Set.range (Rat.cast : ℚ → ℝ)
    lineGridSet b ⊆ starSet Q ∧
    {x : LineGrid b | x.1 ∈ starSet Q} = Set.univ ∧
    (M_line b).loebMeasure {x : LineGrid b | x.1 ∈ starSet Q} = ⊤ ∧
    MeasureTheory.volume Q = 0 := by
  intro Q
  have hSub : lineGridSet b ⊆ starSet Q := by
    intro y hy
    rcases ofSeq_surjective y with ⟨s, rfl⟩
    rw [ofSeq_mem_starSet]
    refine (ofSeq_mem_internalSet.1 hy).mono fun n hn ↦ ?_
    obtain ⟨k, _, hks⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hn)
    refine ⟨(k : ℚ) / (b n : ℚ), ?_⟩
    rw [← hks]
    push_cast
    rfl
  have hEqUniv : {x : LineGrid b | x.1 ∈ starSet Q} = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ hSub x.2
  have hLoeb : (M_line b).loebMeasure {x : LineGrid b | x.1 ∈ starSet Q} = ⊤ := by
    rw [hEqUniv, (M_line_basic_properties hb).2.2.2]
  have hVol : MeasureTheory.volume Q = 0 :=
    (Set.countable_range (Rat.cast : ℚ → ℝ)).measure_zero MeasureTheory.volume
  exact ⟨hSub, hEqUniv, hLoeb, hVol⟩

/-- Goldblatt §16.8 (p. 216): The **inverse shadow** `sh⁻¹(E) = {s ∈ S : s ∈ ℝ_L ∧ sh(s) ∈ E}`
of a subset `E ⊆ ℝ` inside `LineGrid b`. -/
def invShadow (b : ℕ → ℕ) (E : Set ℝ) : Set (LineGrid b) :=
  {x : LineGrid b | IsLimited x.1 ∧ shadow x.1 ∈ E}

/-- Goldblatt §16.8 (p. 216): Equivalence of the two definitions of `sh⁻¹(E)`:
`invShadow b E = {x : LineGrid b | ∃ r ∈ E, x.1 ≈ₕ (r : ℝ*)}`. -/
theorem invShadow_eq_infClose (b : ℕ → ℕ) (E : Set ℝ) :
    invShadow b E = {x : LineGrid b | ∃ r ∈ E, x.1 ≈ₕ (r : ℝ*)} := by
  ext x
  simp only [invShadow, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hLim, hshE⟩
    exact ⟨shadow x.1, hshE, infClose_shadow hLim⟩
  · rintro ⟨r, hrE, hClose⟩
    have hLim : IsLimited x.1 := by
      obtain ⟨h1, h2⟩ := abs_lt.1 (hClose 1 one_pos)
      refine isLimited_iff_exists_real.2 ⟨r - 1, r + 1, ?_, ?_⟩
      · simp only [Hyperreal.coe_sub] at *; linarith
      · simp only [Hyperreal.coe_add] at *; linarith
    exact ⟨hLim, (shadow_eq_of_infClose hClose).symm ▸ hrE⟩

/-- Goldblatt §16.8 (p. 216): `sh⁻¹(ℝ) = invShadow b Set.univ` equals the countable union
`⋃ n : ℕ, (S ∩ *(-(n+1), n+1))`, hence is **Loeb measurable** (with Loeb measure `⊤`), yet is
**not internal** (`invShadow b Set.univ ∉ (M_line b).𝒜` and its image in `ℝ*` is **external**)! -/
theorem invShadow_univ_loebMeasurable_and_external {b : ℕ → ℕ} (hb : IsUnlimitedNat (b : ℕ*)) :
    invShadow b Set.univ =
      (⋃ n : ℕ, {x : LineGrid b | x.1 ∈ starSet (Set.Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1))}) ∧
    (M_line b).IsLoebMeasurable (invShadow b Set.univ) ∧
    (M_line b).loebMeasure (invShadow b Set.univ) = ⊤ ∧
    invShadow b Set.univ ∉ (M_line b).𝒜 ∧
    IsExternal ((Subtype.val : LineGrid b → ℝ*) '' invShadow b Set.univ) := by
  let A : ℕ → Set (LineGrid b) :=
    fun n ↦ {x : LineGrid b | x.1 ∈ starSet (Set.Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1))}
  have hstar_Ioo : ∀ (u v : ℝ) (y : ℝ*), y ∈ starSet (Set.Ioo u v) →
      (u : ℝ*) ≤ y ∧ y ≤ (v : ℝ*) := by
    intro u v y hy
    rcases ofSeq_surjective y with ⟨s, rfl⟩
    rw [ofSeq_mem_starSet] at hy
    exact ⟨ofSeq_le_ofSeq.2 (hy.mono fun _ h ↦ h.1.le),
           ofSeq_le_ofSeq.2 (hy.mono fun _ h ↦ h.2.le)⟩
  have hEq : invShadow b Set.univ = ⋃ n : ℕ, A n := by
    ext x
    simp only [invShadow, Set.mem_univ, and_true, Set.mem_ofPred_eq, Set.mem_iUnion, A]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rcases ofSeq_surjective x.1 with ⟨s, hs⟩
      rw [← hs] at hn ⊢
      rw [ofSeq_mem_starSet]
      obtain ⟨h1, h2⟩ := abs_lt.1 hn
      exact ((ofSeq_lt_ofSeq.1 h1).and (ofSeq_lt_ofSeq.1 h2)).mono
        fun i (hni : -(n : ℝ) < s i ∧ s i < (n : ℝ)) ↦ ⟨by linarith [hni.1], by linarith [hni.2]⟩
    · rintro ⟨n, hxn⟩
      obtain ⟨hlo, hhi⟩ := hstar_Ioo _ _ x.1 hxn
      refine ⟨n + 2, abs_lt.2 ⟨?_, ?_⟩⟩
      · have hc : (-(((n + 2 : ℕ) : ℝ) : ℝ*)) < ((-((n : ℝ) + 1) : ℝ) : ℝ*) := by
          exact_mod_cast (by push_cast; linarith : -((n + 2 : ℕ) : ℝ) < -((n : ℝ) + 1))
        exact hc.trans_le hlo
      · have hc : (((n : ℝ) + 1 : ℝ) : ℝ*) < (((n + 2 : ℕ) : ℝ) : ℝ*) := by
          exact_mod_cast (by push_cast; linarith : (n : ℝ) + 1 < ((n + 2 : ℕ) : ℝ))
        exact hhi.trans_lt hc
  have hA_info : ∀ n : ℕ,
      A n ∈ (M_line b).𝒜 ∧
      (M_line b).IsLoebMeasurable (A n) ∧
      (M_line b).loebMeasure (A n) = ENNReal.ofReal (2 * ((n : ℝ) + 1)) := by
    intro n
    have hle : -((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by linarith
    have hm := M_line_starInterval_measure hb hle Set.Subset.rfl Set.Ioo_subset_Icc_self
    have hring : ((n : ℝ) + 1) - (-((n : ℝ) + 1)) = 2 * ((n : ℝ) + 1) := by ring
    rw [hring] at hm
    exact ⟨hm.1, hm.2.1, hm.2.2.2.2⟩
  have hSig := (isSigmaAlgebra_caratheodory (M_line b).loebOuterMeasure).1
  have hCar : (M_line b).IsLoebMeasurable (invShadow b Set.univ) := by
    rw [hEq]
    exact hSig.toIsSigmaRing.iUnion_mem fun n ↦ (hA_info n).2.1
  have hTop : (M_line b).loebMeasure (invShadow b Set.univ) = ⊤ := by
    by_contra hne
    obtain ⟨n, hn⟩ := exists_nat_gt ((M_line b).loebMeasure (invShadow b Set.univ)).toReal
    have hle_m : ENNReal.ofReal (2 * ((n : ℝ) + 1)) ≤
        (M_line b).loebMeasure (invShadow b Set.univ) := by
      rw [← (hA_info n).2.2, hEq]
      exact MeasureTheory.measure_mono (Set.subset_iUnion A n)
    have hle_real : 2 * ((n : ℝ) + 1) ≤
        ((M_line b).loebMeasure (invShadow b Set.univ)).toReal := by
      have := ENNReal.toReal_mono hne hle_m
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    linarith
  have hExt : IsExternal ((Subtype.val : LineGrid b → ℝ*) '' invShadow b Set.univ) := by
    intro hInt
    have hLine_int : IsInternal (lineGridSet b) := ⟨fun n ↦ (realLineGrid (b n) : Set ℝ), rfl⟩
    have hA_alg : ∀ n : ℕ, A n ∈ internalSubsetAlgebra (lineGridSet b) := by
      intro n
      have hm := (hA_info n).1
      rwa [(M_line_basic_properties hb).1] at hm
    obtain ⟨k, hk⟩ := (isSetAlgebra_internalSubsetAlgebra hLine_int).2 hA_alg (hEq ▸ hInt)
    obtain ⟨x, _, _, _, hLim, hsh⟩ := lineGrid_approx_real hb ((k : ℝ) + 2)
    have hx_in : x ∈ ⋃ n : ℕ, A n := hEq ▸ ⟨hLim, trivial⟩
    rw [hk] at hx_in
    obtain ⟨n, hnk, hxn⟩ := Set.mem_iUnion₂.1 hx_in
    have hhi := (hstar_Ioo _ _ x.1 hxn).2
    have hsh_le : shadow x.1 ≤ (n : ℝ) + 1 := by
      have h := shadow_le_of_le hLim (isLimited_coe _) hhi
      rwa [shadow_coe] at h
    have hnk_real : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnk
    linarith
  have hNotMem : invShadow b Set.univ ∉ (M_line b).𝒜 := by
    rw [(M_line_basic_properties hb).1]
    exact hExt
  exact ⟨hEq, hCar, hTop, hNotMem, hExt⟩

/-- Total shadow map `lineSh b : LineGrid b → ℝ` (`x ↦ shadow x.1`, sending unlimited grid points
to `0`). -/
def lineSh (b : ℕ → ℕ) (x : LineGrid b) : ℝ := shadow x.1

/-- Goldblatt §16.8, **Lemma 16.8.3** (p. 217):
For any unlimited hypernatural `N = (b : ℕ*)`:
1. `lineSh b : LineGrid b → ℝ` is measurable with respect to `(M_line b).loebMeasurableSpace`;
2. Pushing `(M_line b).loebMeasure.restrict (invShadow b Set.univ)` forward along `lineSh b` yields
   Lebesgue measure `MeasureTheory.volume` on `ℝ`;
3. For every Borel set `B : Set ℝ` (`MeasurableSet B`), `invShadow b B` is Loeb measurable and
   `(M_line b).loebMeasure (invShadow b B) = MeasureTheory.volume B`! -/
theorem M_line_borel_measure {b : ℕ → ℕ} (hb : IsUnlimitedNat (b : ℕ*)) :
    @Measurable (LineGrid b) ℝ (M_line b).loebMeasurableSpace _ (lineSh b) ∧
    @MeasureTheory.Measure.map (LineGrid b) ℝ (M_line b).loebMeasurableSpace _
      (lineSh b) ((M_line b).loebMeasure.restrict (invShadow b Set.univ)) =
        MeasureTheory.volume ∧
    ∀ ⦃B : Set ℝ⦄, MeasurableSet B →
      (M_line b).IsLoebMeasurable (invShadow b B) ∧
      (M_line b).loebMeasure (invShadow b B) = MeasureTheory.volume B := by
  have hSig := (isSigmaAlgebra_caratheodory (M_line b).loebOuterMeasure).1
  have hUnivCar : (M_line b).IsLoebMeasurable (invShadow b Set.univ) :=
    (invShadow_univ_loebMeasurable_and_external hb).2.1
  have hstar_Icc : ∀ (u v : ℝ) (y : ℝ*),
      y ∈ starSet (Set.Icc u v) ↔ (u : ℝ*) ≤ y ∧ y ≤ (v : ℝ*) := by
    intro u v y
    rcases ofSeq_surjective y with ⟨s, rfl⟩
    rw [ofSeq_mem_starSet]
    exact ⟨fun h ↦ ⟨ofSeq_le_ofSeq.2 (h.mono fun _ hi ↦ hi.1),
                     ofSeq_le_ofSeq.2 (h.mono fun _ hi ↦ hi.2)⟩,
           fun ⟨h1, h2⟩ ↦ ((ofSeq_le_ofSeq.1 h1).and (ofSeq_le_ofSeq.1 h2)).mono fun _ hi ↦ hi⟩
  have hStarMem : ∀ u v : ℝ,
      {x : LineGrid b | x.1 ∈ starSet (Set.Icc u v)} ∈ (M_line b).𝒜 := by
    intro u v
    rw [(M_line_basic_properties hb).1]
    change IsInternal ((Subtype.val : LineGrid b → ℝ*) ''
      ((Subtype.val : LineGrid b → ℝ*) ⁻¹' starSet (Set.Icc u v)))
    rw [Subtype.image_preimage_coe]
    exact IsInternal.inter ⟨fun n ↦ (realLineGrid (b n) : Set ℝ), rfl⟩ (isInternal_starSet _)
  -- Step 1: `invShadow b (Set.Ioo a c)` equals the countable union of internal `Icc` slices
  have hIoo_eq_iUnion : ∀ a c : ℝ,
      invShadow b (Set.Ioo a c) =
        ⋃ k : ℕ, {x : LineGrid b |
          x.1 ∈ starSet (Set.Icc (a + 1 / ((k : ℝ) + 1)) (c - 1 / ((k : ℝ) + 1)))} := by
    intro a c
    ext x
    simp only [invShadow, Set.mem_Ioo, Set.mem_ofPred_eq, Set.mem_iUnion, hstar_Icc]
    constructor
    · rintro ⟨hLim, hax, hxc⟩
      have hd_pos : 0 < min (shadow x.1 - a) (c - shadow x.1) / 2 :=
        half_pos (lt_min (sub_pos.2 hax) (sub_pos.2 hxc))
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hd_pos
      have hinf := abs_lt.1 (infClose_shadow hLim (1 / ((k : ℝ) + 1)) (by positivity))
      refine ⟨k, ?_, ?_⟩
      · have h1 : a + 2 * (1 / ((k : ℝ) + 1)) ≤ shadow x.1 := by
          linarith [min_le_left (shadow x.1 - a) (c - shadow x.1)]
        have hcast : ((a + 1 / ((k : ℝ) + 1) : ℝ) : ℝ*) + ((1 / ((k : ℝ) + 1) : ℝ) : ℝ*) ≤
            (shadow x.1 : ℝ*) := by
          exact_mod_cast (by linarith : a + 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) ≤ shadow x.1)
        linarith [hinf.1, hcast]
      · have h2 : shadow x.1 + 2 * (1 / ((k : ℝ) + 1)) ≤ c := by
          linarith [min_le_right (shadow x.1 - a) (c - shadow x.1)]
        have hcast : (shadow x.1 : ℝ*) + ((1 / ((k : ℝ) + 1) : ℝ) : ℝ*) ≤
            ((c - 1 / ((k : ℝ) + 1) : ℝ) : ℝ*) := by
          exact_mod_cast (by linarith : shadow x.1 + 1 / ((k : ℝ) + 1) ≤ c - 1 / ((k : ℝ) + 1))
        linarith [hinf.2, hcast]
    · rintro ⟨k, h1, h2⟩
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hLim : IsLimited x.1 := by
        refine isLimited_iff_exists_real.2 ⟨a, c, ?_, ?_⟩
        · exact (Hyperreal.coe_lt_coe.2 (by linarith : a < a + 1 / ((k : ℝ) + 1))).trans_le h1
        · exact h2.trans_lt (Hyperreal.coe_lt_coe.2 (by linarith : c - 1 / ((k : ℝ) + 1) < c))
      have hs1 : a + 1 / ((k : ℝ) + 1) ≤ shadow x.1 := by
        have h := shadow_le_of_le (isLimited_coe _) hLim h1
        rwa [shadow_coe] at h
      have hs2 : shadow x.1 ≤ c - 1 / ((k : ℝ) + 1) := by
        have h := shadow_le_of_le hLim (isLimited_coe _) h2
        rwa [shadow_coe] at h
      exact ⟨hLim, by linarith, by linarith⟩
  have hIoo_car : ∀ a c : ℝ, (M_line b).IsLoebMeasurable (invShadow b (Set.Ioo a c)) := by
    intro a c
    rw [hIoo_eq_iUnion a c]
    exact hSig.toIsSigmaRing.iUnion_mem fun k ↦
      ((M_line b).loebMeasure_properties.2.2 (hStarMem _ _)).1
  have hIoo_meas : ∀ a c : ℝ,
      (M_line b).loebMeasure (invShadow b (Set.Ioo a c)) = ENNReal.ofReal (c - a) := by
    intro a c
    rcases le_or_gt c a with hca | hlt
    · have hEmpty : Set.Ioo a c = ∅ := Set.Ioo_eq_empty (not_lt.2 hca)
      have hInvEmpty : invShadow b ∅ = ∅ := by ext x; simp [invShadow]
      rw [hEmpty, hInvEmpty, ENNReal.ofReal_of_nonpos (sub_nonpos.2 hca)]
      simp
    · apply le_antisymm
      · have hSub : invShadow b (Set.Ioo a c) ⊆
            {x : LineGrid b | x.1 ∈ starSet (Set.Icc a c)} := by
          rw [hIoo_eq_iUnion a c]
          refine Set.iUnion_subset fun k x hx ↦ ?_
          rw [Set.mem_ofPred_eq, hstar_Icc] at hx ⊢
          have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
          exact ⟨(Hyperreal.coe_lt_coe.2 (by linarith)).le.trans hx.1,
                 hx.2.trans (Hyperreal.coe_lt_coe.2 (by linarith)).le⟩
        exact (MeasureTheory.measure_mono hSub).trans_eq
          (M_line_starInterval_measure hb hlt.le Set.Ioo_subset_Icc_self Set.Subset.rfl).2.2.2.2
      · refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
        have hd_pos : 0 < min ((c - a) / 2) ((δ : ℝ) / 2) :=
          lt_min (half_pos (sub_pos.2 hlt)) (half_pos (NNReal.coe_pos.2 hδ))
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hd_pos
        let u := a + 1 / ((k : ℝ) + 1)
        let v := c - 1 / ((k : ℝ) + 1)
        have huv : u ≤ v := by
          have : 1 / ((k : ℝ) + 1) < (c - a) / 2 := hk.trans_le (min_le_left _ _)
          linarith
        have hSub_k : {x : LineGrid b | x.1 ∈ starSet (Set.Icc u v)} ⊆
            invShadow b (Set.Ioo a c) := by
          rw [hIoo_eq_iUnion a c]
          exact Set.subset_iUnion (fun j : ℕ ↦
            {x : LineGrid b | x.1 ∈ starSet (Set.Icc (a + 1 / ((j : ℝ) + 1))
              (c - 1 / ((j : ℝ) + 1)))}) k
        have hm_uv := (M_line_starInterval_measure hb huv
          Set.Ioo_subset_Icc_self Set.Subset.rfl).2.2.2.2
        have h2k_le : 2 * (1 / ((k : ℝ) + 1)) ≤ (δ : ℝ) := by
          have : 1 / ((k : ℝ) + 1) < (δ : ℝ) / 2 := hk.trans_le (min_le_right _ _)
          linarith
        have hca_le : ENNReal.ofReal (c - a) ≤ ENNReal.ofReal (v - u) + (δ : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_coe_nnreal,
            ← ENNReal.ofReal_add (sub_nonneg.2 huv) (NNReal.coe_nonneg δ)]
          exact ENNReal.ofReal_le_ofReal (by dsimp [u, v]; linarith)
        exact hca_le.trans
          (add_le_add (hm_uv.symm.trans_le (MeasureTheory.measure_mono hSub_k)) le_rfl)
  -- Step 2: Measurability of `lineSh b`
  have hShMeas : @Measurable (LineGrid b) ℝ (M_line b).loebMeasurableSpace _ (lineSh b) := by
    rw [BorelSpace.measurable_eq (α := ℝ), Real.borel_eq_generateFrom_Ioo_rat]
    refine @measurable_generateFrom (LineGrid b) ℝ (M_line b).loebMeasurableSpace _ _ fun U hU ↦ ?_
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hU
    obtain ⟨p, q, _, rfl⟩ := hU
    have hPreEq : lineSh b ⁻¹' Set.Ioo (p : ℝ) (q : ℝ) =
        invShadow b (Set.Ioo (p : ℝ) (q : ℝ)) ∪
          (if (0 : ℝ) ∈ Set.Ioo (p : ℝ) (q : ℝ) then (invShadow b Set.univ)ᶜ else ∅) := by
      ext x
      by_cases hLim : IsLimited x.1
      · simp [lineSh, invShadow, hLim]
      · have hsh0 : shadow x.1 = 0 := by simp [shadow, hLim]
        by_cases h0 : (0 : ℝ) ∈ Set.Ioo (p : ℝ) (q : ℝ)
        · simp [lineSh, invShadow, hLim, hsh0, h0]
        · simp [lineSh, invShadow, hLim, hsh0, h0]
    rw [hPreEq]
    split_ifs
    · exact hSig.toIsSigmaRing.toIsSetRing.union_mem (hIoo_car _ _)
        (hSig.toIsSetAlgebra.compl_mem hUnivCar)
    · rw [Set.union_empty]
      exact hIoo_car (p : ℝ) (q : ℝ)
  -- Step 3: Pushforward of `loebMeasure.restrict (invShadow b Set.univ)` along `lineSh b` = `volume`
  have hInterEq : ∀ E : Set ℝ,
      lineSh b ⁻¹' E ∩ invShadow b Set.univ = invShadow b E := by
    intro E; ext x; simp [lineSh, invShadow, and_comm]
  let ν : MeasureTheory.Measure ℝ :=
    @MeasureTheory.Measure.map (LineGrid b) ℝ (M_line b).loebMeasurableSpace _
      (lineSh b) ((M_line b).loebMeasure.restrict (invShadow b Set.univ))
  have hMapEq : ν = MeasureTheory.volume := by
    refine borel_measure_eq_volume_of_Ioo_rat ν fun p q ↦ ?_
    rw [@MeasureTheory.Measure.map_apply (LineGrid b) ℝ (M_line b).loebMeasurableSpace _
      ((M_line b).loebMeasure.restrict (invShadow b Set.univ)) (lineSh b) hShMeas _
      isOpen_Ioo.measurableSet,
      @MeasureTheory.Measure.restrict_apply (LineGrid b) (M_line b).loebMeasurableSpace
        (M_line b).loebMeasure (invShadow b Set.univ) _ (hShMeas isOpen_Ioo.measurableSet),
      hInterEq, hIoo_meas, Real.volume_Ioo]
  refine ⟨hShMeas, hMapEq, fun B hBm ↦ ?_⟩
  have hCarB : (M_line b).IsLoebMeasurable (invShadow b B) := by
    rw [← hInterEq B]
    exact hSig.toIsSigmaRing.toIsSetRing.inter_mem (hShMeas hBm) hUnivCar
  have hMeasB : (M_line b).loebMeasure (invShadow b B) = MeasureTheory.volume B := by
    rw [← hMapEq]
    dsimp only [ν]
    rw [@MeasureTheory.Measure.map_apply (LineGrid b) ℝ (M_line b).loebMeasurableSpace _
      ((M_line b).loebMeasure.restrict (invShadow b Set.univ)) (lineSh b) hShMeas B hBm,
      @MeasureTheory.Measure.restrict_apply (LineGrid b) (M_line b).loebMeasurableSpace
        (M_line b).loebMeasure (invShadow b Set.univ) _ (hShMeas hBm),
      hInterEq]
  exact ⟨hCarB, hMeasB⟩

/-- Goldblatt §16.8, **Theorem 16.8.2** (pp. 217–219):
For any unlimited hypernatural `N = (b : ℕ*)` and **every** subset `B : Set ℝ`:
1. `B` is **Lebesgue measurable** (`NullMeasurableSet B volume`) **if and only if** `sh⁻¹(B)`
   (`invShadow b B`) is **Loeb measurable** (`(M_line b).IsLoebMeasurable (invShadow b B)`);
2. Whenever this holds, `MeasureTheory.volume B = (M_line b).loebMeasure (invShadow b B)`! -/
theorem nullMeasurableSet_iff_isLoebMeasurable_invShadow {b : ℕ → ℕ}
    (hb : IsUnlimitedNat (b : ℕ*)) (B : Set ℝ) :
    (MeasureTheory.NullMeasurableSet B MeasureTheory.volume ↔
      (M_line b).IsLoebMeasurable (invShadow b B)) ∧
    (MeasureTheory.NullMeasurableSet B MeasureTheory.volume →
      MeasureTheory.volume B = (M_line b).loebMeasure (invShadow b B)) := by
  have hBorel := (M_line_borel_measure hb).2.2
  have hSig := (isSigmaAlgebra_caratheodory (M_line b).loebOuterMeasure).1
  -- Forward direction + measure equality via Borel sandwich (§16.4(2)) & Loeb completeness
  have hFwd : MeasureTheory.NullMeasurableSet B MeasureTheory.volume →
      (M_line b).IsLoebMeasurable (invShadow b B) ∧
      MeasureTheory.volume B = (M_line b).loebMeasure (invShadow b B) := by
    intro hBnm
    obtain ⟨C, D, hCm, hDm, hCB, hBD, hNull⟩ :=
      (nullMeasurableSet_volume_iff_borel_sandwich B).1 hBnm
    have hInvMono : ∀ ⦃X Y : Set ℝ⦄, X ⊆ Y → invShadow b X ⊆ invShadow b Y :=
      fun _ _ h x hx ↦ ⟨hx.1, h hx.2⟩
    have hInvDiff : invShadow b D \ invShadow b C = invShadow b (D \ C) := by
      ext x
      simp only [invShadow, Set.mem_sdiff, Set.mem_ofPred_eq, not_and]
      exact ⟨fun ⟨⟨hL, hxD⟩, hnot⟩ ↦ ⟨hL, hxD, hnot hL⟩,
             fun ⟨hL, hxD, hxC⟩ ↦ ⟨⟨hL, hxD⟩, fun _ ↦ hxC⟩⟩
    have hLoebNull : (M_line b).loebOuterMeasure (invShadow b D \ invShadow b C) = 0 := by
      rw [hInvDiff, ← (M_line b).loebMeasure_properties.2.1 (hBorel (hDm.diff hCm)).1,
        (hBorel (hDm.diff hCm)).2, hNull]
    obtain ⟨hCarB, hmBC, _⟩ := isCaratheodoryMeasurable_of_sandwich (M_line b).loebOuterMeasure
      (hBorel hCm).1 (hBorel hDm).1 (hInvMono hCB) (hInvMono hBD) hLoebNull
    refine ⟨hCarB, ?_⟩
    rw [(M_line b).loebMeasure_properties.2.1 hCarB, hmBC,
      ← (M_line b).loebMeasure_properties.2.1 (hBorel hCm).1, (hBorel hCm).2]
    apply le_antisymm _ (MeasureTheory.measure_mono hCB)
    calc MeasureTheory.volume B
        ≤ MeasureTheory.volume D := MeasureTheory.measure_mono hBD
      _ ≤ MeasureTheory.volume (C ∪ (D \ C)) :=
          MeasureTheory.measure_mono fun x hx ↦
            if hxC : x ∈ C then Or.inl hxC else Or.inr ⟨hx, hxC⟩
      _ ≤ MeasureTheory.volume C + MeasureTheory.volume (D \ C) :=
          MeasureTheory.measure_union_le _ _
      _ = MeasureTheory.volume C := by rw [hNull, add_zero]
  -- Finite-measure converse helper via Goldblatt's `K = sh(C)` and `U = ℝ \ sh(S \ D)` (p. 218)!
  have hFinCase : ∀ ⦃E : Set ℝ⦄,
      (M_line b).IsLoebMeasurable (invShadow b E) →
      (M_line b).loebOuterMeasure (invShadow b E) < ⊤ →
      MeasureTheory.NullMeasurableSet E MeasureTheory.volume := by
    intro E hCarE hFinE
    rw [nullMeasurableSet_volume_iff_closed_open_approx]
    intro ε hε
    obtain ⟨C, hC_mem, D, hD_mem, hCE, hED, hDC_lt⟩ :=
      (M_line b).isMuApproximable_of_isLoebMeasurable_of_lt_top hCarE hFinE ε hε
    have hDc_mem : Dᶜ ∈ (M_line b).𝒜 := (M_line b).isSetAlgebra.compl_mem hD_mem
    have hC_int : IsInternal ((Subtype.val : LineGrid b → ℝ*) '' C) := by
      rwa [(M_line_basic_properties hb).1] at hC_mem
    have hDc_int : IsInternal ((Subtype.val : LineGrid b → ℝ*) '' Dᶜ) := by
      rwa [(M_line_basic_properties hb).1] at hDc_mem
    let K : Set ℝ := shadowSet ((Subtype.val : LineGrid b → ℝ*) '' C)
    let U : Set ℝ := (shadowSet ((Subtype.val : LineGrid b → ℝ*) '' Dᶜ))ᶜ
    have hKc : IsClosed K := hC_int.isClosed_shadowSet
    have hUo : IsOpen U := hDc_int.isClosed_shadowSet.isOpen_compl
    have hKE : K ⊆ E := by
      rintro r ⟨y, ⟨x, hxC, rfl⟩, _, rfl⟩
      exact (hCE hxC).2
    have hEU : E ⊆ U := by
      rintro r hrE ⟨y, ⟨x, hxDc, rfl⟩, hLim, rfl⟩
      exact hxDc (hED ⟨hLim, hrE⟩)
    have hSubDC : invShadow b (U \ K) ⊆ D \ C := by
      rintro x ⟨hLim, hxU, hxK⟩
      refine ⟨?_, fun hxC ↦ hxK ⟨x.1, ⟨x, hxC, rfl⟩, hLim, rfl⟩⟩
      by_contra hxD
      exact hxU ⟨x.1, ⟨x, hxD, rfl⟩, hLim, rfl⟩
    refine ⟨K, U, hKc, hUo, hKE, hEU, ?_⟩
    have hUKm : MeasurableSet (U \ K) := hUo.measurableSet.diff hKc.measurableSet
    rw [← (hBorel hUKm).2, (M_line b).loebMeasure_properties.2.1 (hBorel hUKm).1]
    exact ((M_line b).loebOuterMeasure.mono hSubDC).trans_lt
      (((M_line b).loebOuterMeasure_eq_of_mem
        ((M_line b).isSetRing.sdiff_mem hD_mem hC_mem)).trans_lt hDC_lt)
  refine ⟨⟨fun h ↦ (hFwd h).1, fun hCarB ↦ ?_⟩, fun h ↦ (hFwd h).2⟩
  -- General case: `B = ⋃ n : ℕ, (B ∩ (-(n+1), n+1))` (Goldblatt p. 218–219)
  have hB_iUnion : B = ⋃ n : ℕ, (B ∩ Set.Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1)) := by
    ext r
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Ioo]
    refine ⟨fun hr ↦ ?_, fun ⟨_, hr, _⟩ ↦ hr⟩
    obtain ⟨n, hn⟩ := exists_nat_gt |r|
    obtain ⟨h1, h2⟩ := abs_lt.1 hn
    exact ⟨n, hr, by linarith, by linarith⟩
  rw [hB_iUnion]
  refine MeasureTheory.NullMeasurableSet.iUnion fun n ↦ ?_
  let Jn : Set ℝ := Set.Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1)
  have hInvInter : invShadow b (B ∩ Jn) = invShadow b B ∩ invShadow b Jn := by
    ext x
    simp only [invShadow, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  have hCarSlice : (M_line b).IsLoebMeasurable (invShadow b (B ∩ Jn)) := by
    rw [hInvInter]
    exact hSig.toIsSigmaRing.toIsSetRing.inter_mem hCarB (hBorel isOpen_Ioo.measurableSet).1
  have hFinSlice : (M_line b).loebOuterMeasure (invShadow b (B ∩ Jn)) < ⊤ := by
    have hSub : invShadow b (B ∩ Jn) ⊆ invShadow b Jn := fun x hx ↦ ⟨hx.1, hx.2.2⟩
    refine (MeasureTheory.measure_mono hSub).trans_lt ?_
    rw [← (M_line b).loebMeasure_properties.2.1 (hBorel isOpen_Ioo.measurableSet).1,
      (hBorel isOpen_Ioo.measurableSet).2, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  exact hFinCase hCarSlice hFinSlice

/-- Specialization of **Theorem 16.8.2** to `N = omegaNat` (`b = id`): a subset `B ⊆ ℝ` is Lebesgue
measurable iff `invShadow id B` is Loeb measurable, with `volume B = (M_line id).loebMeasure (invShadow id B)`. -/
theorem nullMeasurableSet_iff_isLoebMeasurable_invShadow_omega (B : Set ℝ) :
    (MeasureTheory.NullMeasurableSet B MeasureTheory.volume ↔
      (M_line id).IsLoebMeasurable (invShadow id B)) ∧
    (MeasureTheory.NullMeasurableSet B MeasureTheory.volume →
      MeasureTheory.volume B = (M_line id).loebMeasure (invShadow id B)) :=
  nullMeasurableSet_iff_isLoebMeasurable_invShadow isUnlimitedNat_omegaNat B

end Goldblatt.Ch16
