import LecturesOnTheHyperreals.Ch05_HyperrealsGreatAndSmall
import Mathlib.Data.Set.Countable
import Mathlib.Topology.MetricSpace.Basic

/-!
# Chapter 11: Internal and External Sets

Formalization of Robert Goldblatt, *Lectures on the Hyperreals*, Chapter 11 (pp. 125–146):

* **§11.1** Internal subsets `[A_n]` of `ℝ*` (`internalSet`, `IsInternal`) and `ℕ*`
  (`internalNatSet`, `IsInternalNat`), standard enlargements, finite sets, hyperreal intervals,
  and initial hypernatural segments.
* **§11.2** Boolean algebra of internal sets (`∩`, `∪`, `\`, `ᶜ`), ultrafilter characterizations of
  inclusion, equality, and nonemptiness (`11.2(1)–(4)`), and subsets of internal standard sets.
* **§11.3** Internal Least Number Principle (Theorem 11.3.1) and Internal Induction (Theorem 11.3.2).
* **§11.4** The Overflow Principle (Theorem 11.4.1), Exercise 11.4.2, and externality of cofinite
  subsets of `ℕ`.
* **§11.5** Internal Order-Completeness (Theorem 11.5.1: LUB & GLB for internal subsets of `ℝ*`)
  and spillover principles (Exercise 11.5.2(i)–(iv)).
* **§11.6** External sets (`*ℕ_∞`, `ℕ`, `ℝ`, `𝕃`, `𝕀`, halos, and Exercise 11.6.1).
* **§11.7** The Internal Set Definition Principle (11.7.1), proof that every infinite subset of `ℝ`
  is external, and Exercise 11.7.1.
* **§11.8–11.9** The Underflow Principle (Theorem 11.8.1), Exercise 11.8.2, and Halo Permanence
  (Theorem 11.9.1).
* **§11.10–11.11** Countable Saturation (Theorem 11.10.1), Corollary 11.10.2(1)–(5),
  Exercise 11.10.3, and saturation consequences for infinitesimals and unlimited hypernaturals
  (Exercises 11.11.1–11.11.2).
* **§11.12** Cardinality dichotomy: every countable internal set is finite, so every infinite
  internal set is uncountable.
* **§11.13** Topological closure of the shadow `sh(X)` of any internal set `X` (Theorem 11.13.1 via
  saturation and Exercise 11.13.2 via overflow).
* **§11.14** Interval topology, real-open sets, S-topology, and hyper-open sets (Lemma 11.14.1,
  Exercises 11.14.2–11.14.3, and Theorem 11.14.4).
-/

noncomputable section

namespace Goldblatt

open Filter
open Hyperreal (ofSeq ofSeq_lt_ofSeq ofSeq_le_ofSeq ofSeq_surjective)
open scoped Topology Classical

/-! ## §11.1 Internal Sets in `ℝ*` and `ℕ*` -/

/-- Goldblatt §11.1 (p. 125): The internal subset `[A_n] ⊆ ℝ*` determined by a sequence
`A : ℕ → Set ℝ`, defined via `Germ.LiftRel (· ∈ ·)`. -/
def internalSet (A : ℕ → Set ℝ) : Set ℝ* :=
  {x : ℝ* | Germ.LiftRel (· ∈ ·) x (A : Germ (hyperfilter ℕ : Filter ℕ) (Set ℝ))}

/-- A subset `X ⊆ ℝ*` is **internal** if `X = [A_n]` for some sequence `A : ℕ → Set ℝ`. -/
def IsInternal (X : Set ℝ*) : Prop :=
  ∃ A : ℕ → Set ℝ, X = internalSet A

/-- Goldblatt §11.6 (p. 131): A subset `X ⊆ ℝ*` is **external** if it is not internal. -/
def IsExternal (X : Set ℝ*) : Prop := ¬ IsInternal X

/-- Internal subset `[A_n] ⊆ ℕ*` determined by a sequence `A : ℕ → Set ℕ`. -/
def internalNatSet (A : ℕ → Set ℕ) : Set ℕ* :=
  {N : ℕ* | Germ.LiftRel (· ∈ ·) N (A : Germ (hyperfilter ℕ : Filter ℕ) (Set ℕ))}

/-- A subset `X ⊆ ℕ*` is **internal** if `X = [A_n]` for some sequence `A : ℕ → Set ℕ`. -/
def IsInternalNat (X : Set ℕ*) : Prop :=
  ∃ A : ℕ → Set ℕ, X = internalNatSet A

/-- A subset `X ⊆ ℕ*` is **external** if it is not internal. -/
def IsExternalNat (X : Set ℕ*) : Prop := ¬ IsInternalNat X

@[simp]
theorem ofSeq_mem_internalSet {r : ℕ → ℝ} {A : ℕ → Set ℝ} :
    ofSeq r ∈ internalSet A ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ A n :=
  Germ.liftRel_coe

@[simp]
theorem coe_mem_internalNatSet {a : ℕ → ℕ} {A : ℕ → Set ℕ} :
    (a : ℕ*) ∈ internalNatSet A ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), a n ∈ A n :=
  Germ.liftRel_coe

/-- Goldblatt §11.1 (p. 126): A constant sequence `A_n = A` produces the enlargement `*A`. -/
@[simp]
theorem internalSet_const (A : Set ℝ) : internalSet (fun _ ↦ A) = starSet A := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp [ofSeq_mem_starSet]

/-- Enlargement `*A ⊆ ℕ*` of a standard subset `A ⊆ ℕ`. -/
def starNatSet (A : Set ℕ) : Set ℕ* := internalNatSet (fun _ ↦ A)

@[simp]
theorem coe_mem_starNatSet {a : ℕ → ℕ} {A : Set ℕ} :
    (a : ℕ*) ∈ starNatSet A ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), a n ∈ A :=
  Germ.liftRel_coe

@[simp]
theorem natCast_mem_starNatSet {n : ℕ} {A : Set ℕ} :
    (n : ℕ*) ∈ starNatSet A ↔ n ∈ A :=
  Germ.liftRel_const_iff

theorem isInternal_starSet (A : Set ℝ) : IsInternal (starSet A) :=
  ⟨fun _ ↦ A, (internalSet_const A).symm⟩

theorem isInternalNat_starNatSet (A : Set ℕ) : IsInternalNat (starNatSet A) :=
  ⟨fun _ ↦ A, rfl⟩

@[simp]
theorem internalSet_empty : internalSet (fun _ ↦ (∅ : Set ℝ)) = ∅ := by
  rw [internalSet_const, starSet_empty]

@[simp]
theorem internalSet_univ : internalSet (fun _ ↦ (Set.univ : Set ℝ)) = Set.univ := by
  rw [internalSet_const, starSet_univ]

theorem isInternal_empty : IsInternal (∅ : Set ℝ*) :=
  ⟨fun _ ↦ ∅, internalSet_empty.symm⟩

theorem isInternal_univ : IsInternal (Set.univ : Set ℝ*) :=
  ⟨fun _ ↦ Set.univ, internalSet_univ.symm⟩

@[simp]
theorem internalNatSet_empty : internalNatSet (fun _ ↦ (∅ : Set ℕ)) = ∅ := by
  ext N
  induction N using Germ.inductionOn with | _ a =>
  simp only [coe_mem_internalNatSet, Set.mem_empty_iff_false, eventually_const]

@[simp]
theorem internalNatSet_univ : internalNatSet (fun _ ↦ (Set.univ : Set ℕ)) = Set.univ := by
  ext N
  induction N using Germ.inductionOn with | _ a =>
  simp

theorem isInternalNat_empty : IsInternalNat (∅ : Set ℕ*) :=
  ⟨fun _ ↦ ∅, internalNatSet_empty.symm⟩

theorem isInternalNat_univ : IsInternalNat (Set.univ : Set ℕ*) :=
  ⟨fun _ ↦ Set.univ, internalNatSet_univ.symm⟩

/-- Exact correspondence between internal subsets of `ℕ*` and internal subsets of `*ℕ ⊆ ℝ*`. -/
theorem isInternal_image_hypernat_iff {X : Set ℕ*} :
    IsInternal (Hypernat.toHyperreal '' X) ↔ IsInternalNat X := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨fun n ↦ (Nat.cast : ℕ → ℝ) ⁻¹' (B n), ?_⟩
    ext N
    induction N using Germ.inductionOn with | _ a =>
    have hinj : (a : ℕ*) ∈ X ↔ Hypernat.toHyperreal (a : ℕ*) ∈ Hypernat.toHyperreal '' X :=
      ⟨fun h ↦ ⟨(a : ℕ*), h, rfl⟩,
       fun ⟨M, hM, heq⟩ ↦ Hypernat.toHyperreal_injective heq ▸ hM⟩
    rw [hinj, hB]
    exact ofSeq_mem_internalSet
  · rintro ⟨A, rfl⟩
    refine ⟨fun n ↦ (Nat.cast : ℕ → ℝ) '' (A n), ?_⟩
    ext x
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    constructor
    · rintro ⟨N, hN, hNx⟩
      induction N using Germ.inductionOn with | _ a =>
      have haA : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), a n ∈ A n := coe_mem_internalNatSet.1 hN
      have har : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (a n : ℝ) = r n := Germ.coe_eq.1 hNx
      exact ofSeq_mem_internalSet.2 ((haA.and har).mono fun n ⟨h1, h2⟩ ↦ ⟨a n, h1, h2⟩)
    · intro hx
      have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ (Nat.cast : ℕ → ℝ) '' (A n) :=
        ofSeq_mem_internalSet.1 hx
      let a : ℕ → ℕ := fun n ↦
        if h : r n ∈ (Nat.cast : ℕ → ℝ) '' (A n) then h.choose else 0
      refine ⟨(a : ℕ*), coe_mem_internalNatSet.2 ?_, Germ.coe_eq.2 ?_⟩
      · refine hev.mono fun n hn ↦ ?_
        simpa only [a, hn, ↓reduceDIte] using hn.choose_spec.1
      · refine hev.mono fun n hn ↦ ?_
        simpa only [Function.comp_apply, a, hn, ↓reduceDIte] using hn.choose_spec.2

/-- Goldblatt §11.1 (p. 126): Every singleton `{c}` in `ℝ*` is internal. -/
theorem isInternal_singleton (c : ℝ*) : IsInternal ({c} : Set ℝ*) := by
  rcases ofSeq_surjective c with ⟨s, rfl⟩
  refine ⟨fun n ↦ {s n}, ?_⟩
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  rw [Set.mem_singleton_iff, ofSeq_mem_internalSet]
  exact Germ.coe_eq

/-- Goldblatt §11.1 & §11.7 (pp. 126, 136): Hyperreal intervals `(a, b)`, `(a, b]`, `[a, b)`,
`[a, b]`, `(a, ∞)`, `[a, ∞)`, `(-∞, b)`, `(-∞, b]` are all internal! -/
theorem internalSet_Ioo (a b : ℕ → ℝ) :
    internalSet (fun n ↦ Set.Ioo (a n) (b n)) = Set.Ioo (ofSeq a) (ofSeq b) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp [ofSeq_mem_internalSet, Set.mem_Ioo, eventually_and, ← ofSeq_lt_ofSeq]

theorem isInternal_Ioo (a b : ℝ*) : IsInternal (Set.Ioo a b) := by
  rcases ofSeq_surjective a with ⟨sa, rfl⟩
  rcases ofSeq_surjective b with ⟨sb, rfl⟩
  exact ⟨fun n ↦ Set.Ioo (sa n) (sb n), (internalSet_Ioo sa sb).symm⟩

theorem isInternal_Ioc (a b : ℝ*) : IsInternal (Set.Ioc a b) := by
  rcases ofSeq_surjective a with ⟨sa, rfl⟩
  rcases ofSeq_surjective b with ⟨sb, rfl⟩
  refine ⟨fun n ↦ Set.Ioc (sa n) (sb n), ?_⟩
  ext x; rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp [ofSeq_mem_internalSet, Set.mem_Ioc, eventually_and, ← ofSeq_lt_ofSeq, ← ofSeq_le_ofSeq]

theorem isInternal_Ico (a b : ℝ*) : IsInternal (Set.Ico a b) := by
  rcases ofSeq_surjective a with ⟨sa, rfl⟩
  rcases ofSeq_surjective b with ⟨sb, rfl⟩
  refine ⟨fun n ↦ Set.Ico (sa n) (sb n), ?_⟩
  ext x; rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp [ofSeq_mem_internalSet, Set.mem_Ico, eventually_and, ← ofSeq_lt_ofSeq, ← ofSeq_le_ofSeq]

theorem isInternal_Icc (a b : ℝ*) : IsInternal (Set.Icc a b) := by
  rcases ofSeq_surjective a with ⟨sa, rfl⟩
  rcases ofSeq_surjective b with ⟨sb, rfl⟩
  refine ⟨fun n ↦ Set.Icc (sa n) (sb n), ?_⟩
  ext x; rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp [ofSeq_mem_internalSet, Set.mem_Icc, eventually_and, ← ofSeq_le_ofSeq]

theorem isInternal_Ioi (a : ℝ*) : IsInternal (Set.Ioi a) := by
  rcases ofSeq_surjective a with ⟨sa, rfl⟩
  refine ⟨fun n ↦ Set.Ioi (sa n), ?_⟩
  ext x; rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp [ofSeq_mem_internalSet, Set.mem_Ioi, ← ofSeq_lt_ofSeq]

theorem isInternal_Ici (a : ℝ*) : IsInternal (Set.Ici a) := by
  rcases ofSeq_surjective a with ⟨sa, rfl⟩
  refine ⟨fun n ↦ Set.Ici (sa n), ?_⟩
  ext x; rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp [ofSeq_mem_internalSet, Set.mem_Ici, ← ofSeq_le_ofSeq]

theorem isInternal_Iio (b : ℝ*) : IsInternal (Set.Iio b) := by
  rcases ofSeq_surjective b with ⟨sb, rfl⟩
  refine ⟨fun n ↦ Set.Iio (sb n), ?_⟩
  ext x; rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp [ofSeq_mem_internalSet, Set.mem_Iio, ← ofSeq_lt_ofSeq]

theorem isInternal_Iic (b : ℝ*) : IsInternal (Set.Iic b) := by
  rcases ofSeq_surjective b with ⟨sb, rfl⟩
  refine ⟨fun n ↦ Set.Iic (sb n), ?_⟩
  ext x; rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp [ofSeq_mem_internalSet, Set.mem_Iic, ← ofSeq_le_ofSeq]

/-- Goldblatt §11.1 (p. 126): Initial hypernatural segments `{k ∈ ℕ* | M ≤ k ∧ k ≤ N}` are internal. -/
theorem isInternalNat_Icc (M N : ℕ*) : IsInternalNat (Set.Icc M N) := by
  induction M using Germ.inductionOn with | _ a =>
  induction N using Germ.inductionOn with | _ b =>
  refine ⟨fun n ↦ Set.Icc (a n) (b n), ?_⟩
  ext K; induction K using Germ.inductionOn with | _ c =>
  rw [Set.mem_Icc, coe_mem_internalNatSet]
  simp only [Set.mem_Icc, eventually_and]
  exact and_congr Germ.coe_le Germ.coe_le

theorem isInternalNat_Iic (N : ℕ*) : IsInternalNat (Set.Iic N) := by
  induction N using Germ.inductionOn with | _ b =>
  refine ⟨fun n ↦ Set.Iic (b n), ?_⟩
  ext K; induction K using Germ.inductionOn with | _ c =>
  rw [Set.mem_Iic, coe_mem_internalNatSet]
  exact Germ.coe_le

theorem isInternalNat_Ici (M : ℕ*) : IsInternalNat (Set.Ici M) := by
  induction M using Germ.inductionOn with | _ a =>
  refine ⟨fun n ↦ Set.Ici (a n), ?_⟩
  ext K; induction K using Germ.inductionOn with | _ c =>
  rw [Set.mem_Ici, coe_mem_internalNatSet]
  exact Germ.coe_le

theorem isInternalNat_singleton (N : ℕ*) : IsInternalNat ({N} : Set ℕ*) := by
  induction N using Germ.inductionOn with | _ a =>
  refine ⟨fun n ↦ {a n}, ?_⟩
  ext K; induction K using Germ.inductionOn with | _ c =>
  rw [Set.mem_singleton_iff, coe_mem_internalNatSet]
  exact Germ.coe_eq

/-- Goldblatt §11.1 & Exercise 11.7.1 (pp. 126, 136): For any `N ∈ ℕ*`, the grid
`{k / N | k ∈ ℕ*, k ≤ N}` in `ℝ*` is internal. -/
theorem isInternal_uniformGrid (N : ℕ*) :
    IsInternal {x : ℝ* | ∃ k : ℕ*, k ≤ N ∧
      x = Hypernat.toHyperreal k / Hypernat.toHyperreal N} := by
  induction N using Germ.inductionOn with | _ b =>
  refine ⟨fun n ↦ {r : ℝ | ∃ k : ℕ, k ≤ b n ∧ r = (k : ℝ) / (b n : ℝ)}, ?_⟩
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  constructor
  · rintro ⟨k, hk, hxk⟩
    induction k using Germ.inductionOn with | _ a =>
    have hab : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), a n ≤ b n := Germ.coe_le.1 hk
    have hreq : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n = (a n : ℝ) / (b n : ℝ) :=
      Germ.coe_eq.1 hxk
    exact ofSeq_mem_internalSet.2 ((hab.and hreq).mono fun n ⟨h1, h2⟩ ↦ ⟨a n, h1, h2⟩)
  · intro hx
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ k : ℕ, k ≤ b n ∧ r n = (k : ℝ) / (b n : ℝ) :=
      ofSeq_mem_internalSet.1 hx
    let a : ℕ → ℕ := fun n ↦
      if h : ∃ k : ℕ, k ≤ b n ∧ r n = (k : ℝ) / (b n : ℝ) then h.choose else 0
    refine ⟨(a : ℕ*), Germ.coe_le.2 ?_, Germ.coe_eq.2 ?_⟩
    · exact hev.mono fun n hn ↦ by simpa only [a, hn, ↓reduceDIte] using hn.choose_spec.1
    · exact hev.mono fun n hn ↦ by
        simpa only [Function.comp_apply, a, hn, ↓reduceDIte] using hn.choose_spec.2

/-! ## §11.2 Algebra of Internal Sets -/

/-- Goldblatt §11.2(1) (p. 127): `[A_n] ∩ [B_n] = [A_n ∩ B_n]`. -/
theorem internalSet_inter (A B : ℕ → Set ℝ) :
    internalSet A ∩ internalSet B = internalSet (fun n ↦ A n ∩ B n) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp [ofSeq_mem_internalSet, Set.mem_inter_iff, eventually_and]

/-- Goldblatt §11.2(1) (p. 127): `[A_n] ∪ [B_n] = [A_n ∪ B_n]`. -/
theorem internalSet_union (A B : ℕ → Set ℝ) :
    internalSet A ∪ internalSet B = internalSet (fun n ↦ A n ∪ B n) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp [ofSeq_mem_internalSet, Set.mem_union, Ultrafilter.eventually_or]

/-- Goldblatt §11.2(1) (p. 127): `[A_n] \ [B_n] = [A_n \ B_n]`. -/
theorem internalSet_sdiff (A B : ℕ → Set ℝ) :
    internalSet A \ internalSet B = internalSet (fun n ↦ A n \ B n) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  rw [Set.mem_sdiff, ofSeq_mem_internalSet, ofSeq_mem_internalSet, ofSeq_mem_internalSet,
      ← Ultrafilter.eventually_not, ← eventually_and]
  rfl

theorem internalSet_compl (A : ℕ → Set ℝ) :
    (internalSet A)ᶜ = internalSet (fun n ↦ (A n)ᶜ) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  rw [Set.mem_compl_iff, ofSeq_mem_internalSet, ofSeq_mem_internalSet, ← Ultrafilter.eventually_not]
  rfl

theorem IsInternal.inter {X Y : Set ℝ*} (hX : IsInternal X) (hY : IsInternal Y) :
    IsInternal (X ∩ Y) := by
  rcases hX with ⟨A, rfl⟩
  rcases hY with ⟨B, rfl⟩
  exact ⟨fun n ↦ A n ∩ B n, internalSet_inter A B⟩

theorem IsInternal.union {X Y : Set ℝ*} (hX : IsInternal X) (hY : IsInternal Y) :
    IsInternal (X ∪ Y) := by
  rcases hX with ⟨A, rfl⟩
  rcases hY with ⟨B, rfl⟩
  exact ⟨fun n ↦ A n ∪ B n, internalSet_union A B⟩

theorem IsInternal.sdiff {X Y : Set ℝ*} (hX : IsInternal X) (hY : IsInternal Y) :
    IsInternal (X \ Y) := by
  rcases hX with ⟨A, rfl⟩
  rcases hY with ⟨B, rfl⟩
  exact ⟨fun n ↦ A n \ B n, internalSet_sdiff A B⟩

theorem IsInternal.compl {X : Set ℝ*} (hX : IsInternal X) :
    IsInternal Xᶜ := by
  rcases hX with ⟨A, rfl⟩
  exact ⟨fun n ↦ (A n)ᶜ, internalSet_compl A⟩

/-- Any finite subset of `ℝ*` is internal (Goldblatt §11.1, p. 126). -/
theorem isInternal_finset (s : Finset ℝ*) : IsInternal (s : Set ℝ*) := by
  induction s using Finset.cons_induction with
  | empty => simpa using isInternal_empty
  | cons a t _ ih =>
      rw [Finset.cons_eq_insert, Finset.coe_insert, Set.insert_eq]
      exact (isInternal_singleton a).union ih

theorem isInternal_of_finite {X : Set ℝ*} (hX : X.Finite) : IsInternal X := by
  rw [← hX.coe_toFinset]
  exact isInternal_finset hX.toFinset

theorem isInternal_biUnion_finset {ι : Type*} (s : Finset ι) {X : ι → Set ℝ*}
    (hX : ∀ i ∈ s, IsInternal (X i)) :
    IsInternal (⋃ i ∈ s, X i) := by
  induction s using Finset.cons_induction with
  | empty => simp [isInternal_empty]
  | cons a t hat ih =>
      have heq : (⋃ i ∈ Finset.cons a t hat, X i) = X a ∪ ⋃ i ∈ t, X i := by ext x; simp
      rw [heq]
      exact (hX a (Finset.mem_cons_self a t)).union
        (ih fun i hi ↦ hX i (Finset.mem_cons_of_mem hi))

theorem isInternal_biInter_finset {ι : Type*} (s : Finset ι) {X : ι → Set ℝ*}
    (hX : ∀ i ∈ s, IsInternal (X i)) :
    IsInternal (⋂ i ∈ s, X i) := by
  induction s using Finset.cons_induction with
  | empty => simp [isInternal_univ]
  | cons a t hat ih =>
      have heq : (⋂ i ∈ Finset.cons a t hat, X i) = X a ∩ ⋂ i ∈ t, X i := by ext x; simp
      rw [heq]
      exact (hX a (Finset.mem_cons_self a t)).inter
        (ih fun i hi ↦ hX i (Finset.mem_cons_of_mem hi))

-- `ℕ*` Boolean algebra operations
theorem internalNatSet_inter (A B : ℕ → Set ℕ) :
    internalNatSet A ∩ internalNatSet B = internalNatSet (fun n ↦ A n ∩ B n) := by
  ext N; induction N using Germ.inductionOn with | _ a =>
  simp [coe_mem_internalNatSet, Set.mem_inter_iff, eventually_and]

theorem internalNatSet_union (A B : ℕ → Set ℕ) :
    internalNatSet A ∪ internalNatSet B = internalNatSet (fun n ↦ A n ∪ B n) := by
  ext N; induction N using Germ.inductionOn with | _ a =>
  simp [coe_mem_internalNatSet, Set.mem_union, Ultrafilter.eventually_or]

theorem internalNatSet_sdiff (A B : ℕ → Set ℕ) :
    internalNatSet A \ internalNatSet B = internalNatSet (fun n ↦ A n \ B n) := by
  ext N; induction N using Germ.inductionOn with | _ a =>
  rw [Set.mem_sdiff, coe_mem_internalNatSet, coe_mem_internalNatSet, coe_mem_internalNatSet,
      ← Ultrafilter.eventually_not, ← eventually_and]
  rfl

theorem internalNatSet_compl (A : ℕ → Set ℕ) :
    (internalNatSet A)ᶜ = internalNatSet (fun n ↦ (A n)ᶜ) := by
  ext N; induction N using Germ.inductionOn with | _ a =>
  rw [Set.mem_compl_iff, coe_mem_internalNatSet, coe_mem_internalNatSet, ← Ultrafilter.eventually_not]
  rfl

theorem IsInternalNat.inter {X Y : Set ℕ*} (hX : IsInternalNat X) (hY : IsInternalNat Y) :
    IsInternalNat (X ∩ Y) := by
  rcases hX with ⟨A, rfl⟩; rcases hY with ⟨B, rfl⟩
  exact ⟨fun n ↦ A n ∩ B n, internalNatSet_inter A B⟩

theorem IsInternalNat.union {X Y : Set ℕ*} (hX : IsInternalNat X) (hY : IsInternalNat Y) :
    IsInternalNat (X ∪ Y) := by
  rcases hX with ⟨A, rfl⟩; rcases hY with ⟨B, rfl⟩
  exact ⟨fun n ↦ A n ∪ B n, internalNatSet_union A B⟩

theorem IsInternalNat.sdiff {X Y : Set ℕ*} (hX : IsInternalNat X) (hY : IsInternalNat Y) :
    IsInternalNat (X \ Y) := by
  rcases hX with ⟨A, rfl⟩; rcases hY with ⟨B, rfl⟩
  exact ⟨fun n ↦ A n \ B n, internalNatSet_sdiff A B⟩

theorem IsInternalNat.compl {X : Set ℕ*} (hX : IsInternalNat X) :
    IsInternalNat Xᶜ := by
  rcases hX with ⟨A, rfl⟩
  exact ⟨fun n ↦ (A n)ᶜ, internalNatSet_compl A⟩

/-- Goldblatt §11.2(4) (p. 127): `[A_n] ≠ ∅` iff `{n ∈ ℕ | A_n ≠ ∅} ∈ 𝓕`. -/
theorem internalSet_nonempty_iff {A : ℕ → Set ℝ} :
    (internalSet A).Nonempty ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (A n).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    exact (ofSeq_mem_internalSet.1 hx).mono fun n hn ↦ ⟨r n, hn⟩
  · intro hev
    let r : ℕ → ℝ := fun n ↦ if h : (A n).Nonempty then h.some else 0
    refine ⟨ofSeq r, ofSeq_mem_internalSet.2 ?_⟩
    exact hev.mono fun n hn ↦ by simpa [r, hn] using hn.some_mem

theorem internalNatSet_nonempty_iff {A : ℕ → Set ℕ} :
    (internalNatSet A).Nonempty ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (A n).Nonempty := by
  constructor
  · rintro ⟨N, hN⟩
    induction N using Germ.inductionOn with | _ a =>
    exact (coe_mem_internalNatSet.1 hN).mono fun n hn ↦ ⟨a n, hn⟩
  · intro hev
    let a : ℕ → ℕ := fun n ↦ if h : (A n).Nonempty then h.some else 0
    refine ⟨(a : ℕ*), coe_mem_internalNatSet.2 ?_⟩
    exact hev.mono fun n hn ↦ by simpa [a, hn] using hn.some_mem

/-- Goldblatt §11.2(2) (p. 127): `[A_n] ⊆ [B_n]` iff `{n ∈ ℕ | A_n ⊆ B_n} ∈ 𝓕`. -/
theorem internalSet_subset_iff {A B : ℕ → Set ℝ} :
    internalSet A ⊆ internalSet B ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), A n ⊆ B n := by
  rw [← Set.sdiff_eq_empty, internalSet_sdiff, ← Set.not_nonempty_iff_eq_empty,
      internalSet_nonempty_iff, ← Ultrafilter.eventually_not]
  simp [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty]

/-- Goldblatt §11.2(3) (p. 127): `[A_n] = [B_n]` iff `{n ∈ ℕ | A_n = B_n} ∈ 𝓕`. -/
theorem internalSet_eq_iff {A B : ℕ → Set ℝ} :
    internalSet A = internalSet B ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), A n = B n := by
  rw [Set.Subset.antisymm_iff, internalSet_subset_iff, internalSet_subset_iff, ← eventually_and]
  exact eventually_congr (Eventually.of_forall fun n ↦ Set.Subset.antisymm_iff.symm)

theorem internalNatSet_subset_iff {A B : ℕ → Set ℕ} :
    internalNatSet A ⊆ internalNatSet B ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), A n ⊆ B n := by
  rw [← Set.sdiff_eq_empty, internalNatSet_sdiff, ← Set.not_nonempty_iff_eq_empty,
      internalNatSet_nonempty_iff, ← Ultrafilter.eventually_not]
  simp [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty]

theorem internalNatSet_eq_iff {A B : ℕ → Set ℕ} :
    internalNatSet A = internalNatSet B ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), A n = B n := by
  rw [Set.Subset.antisymm_iff, internalNatSet_subset_iff, internalNatSet_subset_iff, ← eventually_and]
  exact eventually_congr (Eventually.of_forall fun n ↦ Set.Subset.antisymm_iff.symm)

/-- Goldblatt §11.2 (p. 128): If a set `A ⊆ ℝ` (viewed inside `ℝ*`) is internal, then every subset
`Y ⊆ A` is also internal (`Y = A ∩ *Y`). -/
theorem isInternal_subset_of_real_internal {A Y : Set ℝ}
    (hA : IsInternal ((fun r : ℝ ↦ (r : ℝ*)) '' A)) (hYA : Y ⊆ A) :
    IsInternal ((fun r : ℝ ↦ (r : ℝ*)) '' Y) := by
  have heq : ((fun r : ℝ ↦ (r : ℝ*)) '' Y) =
      ((fun r : ℝ ↦ (r : ℝ*)) '' A) ∩ starSet Y := by
    ext x
    constructor
    · rintro ⟨r, hrY, rfl⟩
      exact ⟨⟨r, hYA hrY, rfl⟩, coe_mem_starSet.2 hrY⟩
    · rintro ⟨⟨r, _, rfl⟩, hrstar⟩
      exact ⟨r, coe_mem_starSet.1 hrstar, rfl⟩
  rw [heq]
  exact hA.inter (isInternal_starSet Y)

/-! ## §11.3 Internal Least Number Principle and Internal Induction -/

/-- Goldblatt Theorem 11.3.1 (p. 128): Any nonempty internal subset of `ℕ*` has a least element,
given explicitly on a nonempty component sequence by `min [A_n] = [min A_n]`. -/
theorem IsInternalNat.exists_least {X : Set ℕ*} (hX : IsInternalNat X) (hne : X.Nonempty) :
    ∃ m ∈ X, ∀ y ∈ X, m ≤ y := by
  rcases hX with ⟨A, rfl⟩
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (A n).Nonempty :=
    internalNatSet_nonempty_iff.1 hne
  let mSeq : ℕ → ℕ := fun n ↦
    if h : (A n).Nonempty then Nat.find h else 0
  refine ⟨(mSeq : ℕ*), coe_mem_internalNatSet.2 ?_, fun y hy ↦ ?_⟩
  · exact hev.mono fun n hn ↦ by simpa [mSeq, hn] using Nat.find_spec hn
  · induction y using Germ.inductionOn with | _ s =>
    have hs : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), s n ∈ A n := coe_mem_internalNatSet.1 hy
    refine Germ.coe_le.2 ((hev.and hs).mono fun n ⟨hn, hsn⟩ ↦ ?_)
    simpa [mSeq, hn] using Nat.find_min' hn hsn

/-- Goldblatt Theorem 11.3.2 (p. 129, 0-based): Internal induction on `ℕ*`. -/
theorem IsInternalNat.induction_zero {X : Set ℕ*} (hX : IsInternalNat X)
    (h0 : (0 : ℕ*) ∈ X) (hsucc : ∀ n ∈ X, n + 1 ∈ X) :
    X = Set.univ := by
  by_contra hne
  have hYne : (Xᶜ).Nonempty := Set.nonempty_compl.2 hne
  obtain ⟨m, hmY, hm_min⟩ := hX.compl.exists_least hYne
  have hm_ne0 : m ≠ 0 := fun h ↦ hmY (h ▸ h0)
  -- Since `m ≠ 0` in `ℕ*`, `m = p + 1` for some `p ∈ ℕ*` with `p < m`.
  have hex_pred : ∃ p : ℕ*, p < m ∧ p + 1 = m := by
    induction m using Germ.inductionOn with | _ a =>
    have ha0 : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), a i ≠ 0 :=
      Ultrafilter.eventually_not.2 (fun h ↦ hm_ne0 (Germ.coe_eq.2 h))
    refine ⟨((fun i ↦ a i - 1) : ℕ*), Germ.coe_lt.2 ?_, Germ.coe_eq.2 ?_⟩
    · exact ha0.mono fun i hi ↦ by change a i - 1 < a i; omega
    · exact ha0.mono fun i hi ↦ by change (a i - 1) + 1 = a i; omega
  obtain ⟨p, hpm, rfl⟩ := hex_pred
  have hpX : p ∈ X := by
    by_contra hpY
    exact not_le_of_gt hpm (hm_min p hpY)
  exact hmY (hsucc p hpX)

/-- Goldblatt Theorem 11.3.2 (p. 129, 1-based, matching Goldblatt's `ℕ = {1, 2, …}`):
If an internal subset `X ⊆ {n ∈ ℕ* | 1 ≤ n}` contains `1` and is closed under `n ↦ n + 1`,
then `X = {n ∈ ℕ* | 1 ≤ n}`. -/
theorem IsInternalNat.induction_one {X : Set ℕ*} (hX : IsInternalNat X)
    (hsub : X ⊆ Set.Ici (1 : ℕ*)) (h1 : (1 : ℕ*) ∈ X) (hsucc : ∀ n ∈ X, n + 1 ∈ X) :
    X = Set.Ici (1 : ℕ*) := by
  have hU : X ∪ {(0 : ℕ*)} = Set.univ := by
    refine (hX.union (isInternalNat_singleton 0)).induction_zero (Or.inr rfl) ?_
    rintro n (hnX | rfl)
    · exact Or.inl (hsucc n hnX)
    · exact Or.inl (by simpa using h1)
  ext n
  constructor
  · exact fun hn ↦ hsub hn
  · intro hn1
    have hn_ne0 : n ≠ 0 := by
      intro h0; subst h0
      have : 1 ≤ 0 := Germ.coe_le.1 hn1 |>.exists.choose_spec
      omega
    have : n ∈ X ∪ {(0 : ℕ*)} := hU ▸ Set.mem_univ n
    exact this.resolve_right hn_ne0

/-! ## §11.4 The Overflow Principle -/

/-- Helper: If `H ∈ ℕ*` is unlimited, then `H - 1` (i.e. `P` with `P + 1 = H`) is also unlimited. -/
theorem exists_pred_isUnlimitedNat {H : ℕ*} (hH : IsUnlimitedNat H) :
    ∃ K : ℕ*, IsUnlimitedNat K ∧ K + 1 = H := by
  induction H using Germ.inductionOn with | _ a =>
  let K : ℕ* := ((fun i ↦ a i - 1) : ℕ*)
  refine ⟨K, fun n ↦ ?_, ?_⟩
  · have hgt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), n + 1 < a i := Germ.coe_lt.1 (hH (n + 1))
    exact Germ.coe_lt.2 (hgt.mono fun i hi ↦ by change n < a i - 1; omega)
  · have hgt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 0 < a i := Germ.coe_lt.1 (hH 0)
    exact Germ.coe_eq.2 (hgt.mono fun i hi ↦ by change (a i - 1) + 1 = a i; omega)

/-- Goldblatt Theorem 11.4.1 (pp. 129–130, **The Overflow Principle**):
Let `X` be an internal subset of `ℕ*` and `k ∈ ℕ`. If `(n : ℕ*) ∈ X` for all `n ∈ ℕ` with `k ≤ n`,
then there is an unlimited `K ∈ ℕ*` such that `N ∈ X` for all `N ∈ ℕ*` with `k ≤ N ≤ K`. -/
theorem overflow_nat {X : Set ℕ*} (hX : IsInternalNat X) {k : ℕ}
    (hfin : ∀ n : ℕ, k ≤ n → (n : ℕ*) ∈ X) :
    ∃ K : ℕ*, IsUnlimitedNat K ∧ ∀ N : ℕ*, (k : ℕ*) ≤ N → N ≤ K → N ∈ X := by
  by_cases hall : ∀ N : ℕ*, IsUnlimitedNat N → N ∈ X
  · refine ⟨omegaNat, isUnlimitedNat_omegaNat, fun N hkN _ ↦ ?_⟩
    by_cases hN : IsUnlimitedNat N
    · exact hall N hN
    · obtain ⟨n, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 hN
      have hkn : k ≤ n := by
        have := (Germ.coe_le.1 hkN).exists
        exact this.choose_spec
      exact hfin n hkn
  · push Not at hall
    obtain ⟨M₀, hM₀_unl, hM₀_not⟩ := hall
    let Y : Set ℕ* := Set.Ici ((k + 1 : ℕ) : ℕ*) \ X
    have hY_int : IsInternalNat Y := (isInternalNat_Ici _).sdiff hX
    have hY_ne : Y.Nonempty := ⟨M₀, (hM₀_unl (k + 1)).le, hM₀_not⟩
    obtain ⟨H, ⟨hHk, hHnot⟩, hHmin⟩ := hY_int.exists_least hY_ne
    have hH_unl : IsUnlimitedNat H := by
      by_contra hlim
      obtain ⟨n, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 hlim
      have hkn : k + 1 ≤ n := (Germ.coe_le.1 hHk).exists.choose_spec
      exact hHnot (hfin n (by omega))
    obtain ⟨K, hK_unl, hKH⟩ := exists_pred_isUnlimitedNat hH_unl
    refine ⟨K, hK_unl, fun N hkN hNK ↦ ?_⟩
    by_contra hNnot
    rcases eq_or_lt_of_le hkN with rfl | hklt
    · exact hNnot (hfin k le_rfl)
    · have hk1N : ((k + 1 : ℕ) : ℕ*) ≤ N := by
        induction N using Germ.inductionOn with | _ a =>
        have ha : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), k < a i := Germ.coe_lt.1 hklt
        exact Germ.coe_le.2 (ha.mono fun i hi ↦ by change k + 1 ≤ a i; omega)
      have hHN : H ≤ N := hHmin N ⟨hk1N, hNnot⟩
      have hHK : K < H := by
        rw [← hKH]
        induction K using Germ.inductionOn with | _ b =>
        exact Germ.coe_lt.2 (Eventually.of_forall fun i ↦ Nat.lt_succ_self (b i))
      exact not_lt_of_ge (hHN.trans hNK) hHK

/-- Goldblatt Exercise 11.4.2 (p. 130): If an internal subset `X ⊆ ℕ*` contains arbitrarily small
unlimited members, then `X` contains arbitrarily large standard members; and this statement is
equivalent to the Overflow Principle! -/
theorem arbitrarily_large_nat_of_arbitrarily_small_unlimited {X : Set ℕ*} (hX : IsInternalNat X)
    (hsmall : ∀ K : ℕ*, IsUnlimitedNat K → ∃ M ∈ X, IsUnlimitedNat M ∧ M ≤ K) :
    ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ (n : ℕ*) ∈ X := by
  intro k
  by_contra hno
  push Not at hno
  have hcompl : ∀ n : ℕ, k ≤ n → (n : ℕ*) ∈ Xᶜ := hno
  obtain ⟨K, hK_unl, hseg⟩ := overflow_nat hX.compl hcompl
  obtain ⟨M, hMX, hM_unl, hMK⟩ := hsmall K hK_unl
  exact (hseg M (hM_unl k).le hMK) hMX

theorem overflow_iff_small_unlimited_implies_large_standard :
    (∀ (X : Set ℕ*), IsInternalNat X → ∀ (k : ℕ),
      (∀ n : ℕ, k ≤ n → (n : ℕ*) ∈ X) →
      ∃ K : ℕ*, IsUnlimitedNat K ∧ ∀ N : ℕ*, (k : ℕ*) ≤ N → N ≤ K → N ∈ X) ↔
    (∀ (X : Set ℕ*), IsInternalNat X →
      (∀ K : ℕ*, IsUnlimitedNat K → ∃ M ∈ X, IsUnlimitedNat M ∧ M ≤ K) →
      ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ (n : ℕ*) ∈ X) := by
  constructor
  · intro _ X hX hsmall
    exact arbitrarily_large_nat_of_arbitrarily_small_unlimited hX hsmall
  · intro hPrinciple X hX k hfin
    by_contra hno
    push Not at hno
    let Z : Set ℕ* := Set.Ici (k : ℕ*) \ X
    have hZ_int : IsInternalNat Z := (isInternalNat_Ici _).sdiff hX
    have hZ_small : ∀ K : ℕ*, IsUnlimitedNat K → ∃ M ∈ Z, IsUnlimitedNat M ∧ M ≤ K := by
      intro K hK
      obtain ⟨M, hMk, hMK, hMnot⟩ := hno K hK
      refine ⟨M, ⟨hMk, hMnot⟩, ?_, hMK⟩
      by_contra hMlim
      obtain ⟨n, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 hMlim
      have hkn : k ≤ n := (Germ.coe_le.1 hMk).exists.choose_spec
      exact hMnot (hfin n hkn)
    obtain ⟨n, _, hnZ⟩ := hPrinciple Z hZ_int hZ_small k
    have hkn : k ≤ n := (Germ.coe_le.1 hnZ.1).exists.choose_spec
    exact hnZ.2 (hfin n hkn)

/-- Goldblatt §11.4 (p. 130): Every cofinite subset `A ⊆ ℕ` (embedded in `ℕ*`) is external. -/
theorem isExternalNat_of_cofinite {A : Set ℕ} (hcof : Aᶜ.Finite) :
    IsExternalNat ((Nat.cast : ℕ → ℕ*) '' A) := by
  intro hInt
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ n : ℕ, k ≤ n → n ∈ A := by
    by_cases hne : Aᶜ.Nonempty
    · obtain ⟨m, hm⟩ := hcof.bddAbove
      refine ⟨m + 1, fun n hn ↦ ?_⟩
      by_contra hnA
      exact absurd (hm hnA) (by omega)
    · refine ⟨0, fun n _ ↦ ?_⟩
      by_contra hnA
      exact hne ⟨n, hnA⟩
  obtain ⟨K, hK_unl, hseg⟩ := overflow_nat hInt (k := k) (fun n hn ↦ ⟨n, hk n hn, rfl⟩)
  obtain ⟨n, _, hnK⟩ := hseg K (hK_unl k).le le_rfl
  exact lt_irrefl (n : ℕ*) (hnK ▸ hK_unl n)

/-! ## §11.5 Internal Order-Completeness and Spillover -/

/-- Goldblatt Theorem 11.5.1 (pp. 130–131): Every nonempty bounded-above internal subset of `ℝ*`
has a least upper bound in `ℝ*` (`lub [A_n] = [lub A_n]`). -/
theorem IsInternal.exists_isLUB {X : Set ℝ*} (hX : IsInternal X)
    (hne : X.Nonempty) (hbdd : BddAbove X) :
    ∃ s : ℝ*, IsLUB X s := by
  rcases hX with ⟨A, rfl⟩
  obtain ⟨u, hu⟩ := hbdd
  rcases ofSeq_surjective u with ⟨r, rfl⟩
  have hev_ne : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (A n).Nonempty :=
    internalSet_nonempty_iff.1 hne
  have hev_ub : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∀ a ∈ A n, a ≤ r n := by
    by_contra hnot
    have hnot' : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ a ∈ A n, r n < a := by
      have := Ultrafilter.eventually_not.2 hnot
      exact this.mono fun n hn ↦ by push Not at hn; exact hn
    let aSeq : ℕ → ℝ := fun n ↦
      if h : ∃ a ∈ A n, r n < a then h.choose else 0
    have ha_mem : ofSeq aSeq ∈ internalSet A :=
      ofSeq_mem_internalSet.2 (hnot'.mono fun n hn ↦ by simpa [aSeq, hn] using hn.choose_spec.1)
    have ha_gt : ofSeq r < ofSeq aSeq :=
      ofSeq_lt_ofSeq.2 (hnot'.mono fun n hn ↦ by simpa [aSeq, hn] using hn.choose_spec.2)
    exact not_lt_of_ge (hu ha_mem) ha_gt
  let sSeq : ℕ → ℝ := fun n ↦ sSup (A n)
  refine ⟨ofSeq sSeq, ⟨fun b hb ↦ ?_, fun t ht ↦ ?_⟩⟩
  · rcases ofSeq_surjective b with ⟨bSeq, rfl⟩
    have hb_ev := ofSeq_mem_internalSet.1 hb
    refine ofSeq_le_ofSeq.2 ((hb_ev.and hev_ub).mono fun n ⟨hbn, hubn⟩ ↦ ?_)
    exact le_csSup ⟨r n, hubn⟩ hbn
  · rcases ofSeq_surjective t with ⟨tSeq, rfl⟩
    have hev_tub : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∀ a ∈ A n, a ≤ tSeq n := by
      by_contra hnot
      have hnot' : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ a ∈ A n, tSeq n < a :=
        (Ultrafilter.eventually_not.2 hnot).mono fun n hn ↦ by push Not at hn; exact hn
      let aSeq : ℕ → ℝ := fun n ↦
        if h : ∃ a ∈ A n, tSeq n < a then h.choose else 0
      have ha_mem : ofSeq aSeq ∈ internalSet A :=
        ofSeq_mem_internalSet.2 (hnot'.mono fun n hn ↦ by simpa [aSeq, hn] using hn.choose_spec.1)
      have ha_gt : ofSeq tSeq < ofSeq aSeq :=
        ofSeq_lt_ofSeq.2 (hnot'.mono fun n hn ↦ by simpa [aSeq, hn] using hn.choose_spec.2)
      exact not_lt_of_ge (ht ha_mem) ha_gt
    refine ofSeq_le_ofSeq.2 ((hev_ne.and hev_tub).mono fun n ⟨hnen, htubn⟩ ↦ ?_)
    exact csSup_le hnen htubn

/-- Goldblatt Theorem 11.5.1 (GLB dual, p. 130): Every nonempty bounded-below internal subset of
`ℝ*` has a greatest lower bound in `ℝ*`. -/
theorem IsInternal.exists_isGLB {X : Set ℝ*} (hX : IsInternal X)
    (hne : X.Nonempty) (hbdd : BddBelow X) :
    ∃ s : ℝ*, IsGLB X s := by
  rcases hX with ⟨A, rfl⟩
  let negX : Set ℝ* := internalSet (fun n ↦ (- ·) ⁻¹' (A n))
  have hneg_int : IsInternal negX := ⟨_, rfl⟩
  have hmem_neg : ∀ y : ℝ*, y ∈ negX ↔ -y ∈ internalSet A := by
    intro y; rcases ofSeq_surjective y with ⟨r, rfl⟩
    exact Iff.rfl
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨l, hl⟩ := hbdd
  have hneg_ne : negX.Nonempty := ⟨-x₀, (hmem_neg (-x₀)).2 (by simpa using hx₀)⟩
  have hneg_bdd : BddAbove negX := ⟨-l, fun y hy ↦ le_neg.1 (hl ((hmem_neg y).1 hy))⟩
  obtain ⟨s, hs⟩ := hneg_int.exists_isLUB hneg_ne hneg_bdd
  refine ⟨-s, ⟨fun x hx ↦ ?_, fun b hb ↦ ?_⟩⟩
  · exact neg_le.2 (hs.1 ((hmem_neg (-x)).2 (by simpa using hx)))
  · exact le_neg.2 (hs.2 fun y hy ↦ le_neg.1 (hb ((hmem_neg y).1 hy)))

/-- Goldblatt Exercise 11.5.2(ii) (p. 131): If an internal set `X ⊆ ℝ*` has only limited members,
then `X ⊆ [-r, r]` for some standard `r ∈ ℝ`. -/
theorem IsInternal.subset_Icc_real_of_forall_isLimited {X : Set ℝ*} (hX : IsInternal X)
    (hlim : ∀ x ∈ X, IsLimited x) :
    ∃ r : ℝ, 0 ≤ r ∧ X ⊆ Set.Icc (-(r : ℝ*)) (r : ℝ*) := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, le_rfl, Set.empty_subset _⟩
  · have hbdd_up : BddAbove X := ⟨Hyperreal.omega, fun x hx ↦ by
      rcases hlim x hx with ⟨n, hn⟩
      exact (le_abs_self x).trans (hn.le.trans (Hyperreal.coe_lt_omega n).le)⟩
    have hbdd_dn : BddBelow X := ⟨-Hyperreal.omega, fun x hx ↦ by
      rcases hlim x hx with ⟨n, hn⟩
      have h1 : -(n : ℝ*) < x := (abs_lt.1 hn).1
      have h2 : -Hyperreal.omega < -(n : ℝ*) := neg_lt_neg (Hyperreal.coe_lt_omega n)
      exact (h2.trans h1).le⟩
    obtain ⟨u, hu⟩ := hX.exists_isLUB hne hbdd_up
    obtain ⟨l, hl⟩ := hX.exists_isGLB hne hbdd_dn
    have hu_lim : IsLimited u := by
      by_contra hunl
      rcases isUnlimited_iff_pos_or_neg.1 (isUnlimited_iff_not_isLimited.2 hunl) with hpos | hneg
      · have hu2 : IsPosUnlimited (u - 1) := fun r ↦ by
          have := hpos (r + 1)
          rw [Hyperreal.coe_add, Hyperreal.coe_one] at this
          linarith
        have hub : u - 1 ∈ upperBounds X := fun x hx ↦ by
          rcases hlim x hx with ⟨n, hn⟩
          exact ((le_abs_self x).trans hn.le).trans (hu2 n).le
        linarith [hu.2 hub]
      · obtain ⟨x₀, hx₀⟩ := hne
        rcases hlim x₀ hx₀ with ⟨n, hn⟩
        have hlt : u < -(n : ℝ*) := by simpa using hneg (-(n : ℝ))
        have hxgt : -(n : ℝ*) < x₀ := (abs_lt.1 hn).1
        have : u < x₀ := hlt.trans hxgt
        exact not_le_of_gt this (hu.1 hx₀)
    have hl_lim : IsLimited l := by
      by_contra hunl
      rcases isUnlimited_iff_pos_or_neg.1 (isUnlimited_iff_not_isLimited.2 hunl) with hpos | hneg
      · obtain ⟨x₀, hx₀⟩ := hne
        rcases hlim x₀ hx₀ with ⟨n, hn⟩
        have hposn : (n : ℝ*) < l := by simpa using hpos n
        have : x₀ < l := (abs_lt.1 hn).2.trans hposn
        exact not_le_of_gt this (hl.1 hx₀)
      · have hl2 : IsNegUnlimited (l + 1) := fun r ↦ by
          have := hneg (r - 1)
          rw [Hyperreal.coe_sub, Hyperreal.coe_one] at this
          linarith
        have hlb : l + 1 ∈ lowerBounds X := fun x hx ↦ by
          rcases hlim x hx with ⟨n, hn⟩
          have h1 : -(n : ℝ*) < x := (abs_lt.1 hn).1
          have h2 : l + 1 < -(n : ℝ*) := by simpa using hl2 (-(n : ℝ))
          exact (h2.trans h1).le
        linarith [hl.2 hlb]
    rcases hu_lim with ⟨nu, hnu⟩
    rcases hl_lim with ⟨nl, hnl⟩
    refine ⟨max (nu : ℝ) (nl : ℝ), by positivity, fun x hx ↦ ⟨?_, ?_⟩⟩
    · have h1 : -(nl : ℝ*) < l := (abs_lt.1 hnl).1
      have h2 : -((max (nu : ℝ) (nl : ℝ) : ℝ) : ℝ*) ≤ -(nl : ℝ*) := by simp
      exact h2.trans (h1.le.trans (hl.1 hx))
    · have h1 : u < (nu : ℝ*) := (abs_lt.1 hnu).2
      have h2 : (nu : ℝ*) ≤ ((max (nu : ℝ) (nl : ℝ) : ℝ) : ℝ*) := by simp
      exact (hu.1 hx).trans (h1.le.trans h2)

/-- Goldblatt Exercise 11.5.2(i) (p. 131): If an internal set `X ⊆ ℝ*` has arbitrarily large
limited members, then `X` has a positive unlimited member. -/
theorem IsInternal.exists_posUnlimited_of_arbitrarily_large_limited {X : Set ℝ*} (hX : IsInternal X)
    (hlarge : ∀ n : ℕ, ∃ x ∈ X, IsLimited x ∧ (n : ℝ*) < x) :
    ∃ x ∈ X, IsPosUnlimited x := by
  by_contra hno
  push Not at hno
  let Y : Set ℝ* := X ∩ Set.Ici 0
  have hY_int : IsInternal Y := hX.inter (isInternal_Ici 0)
  have hY_lim : ∀ y ∈ Y, IsLimited y := by
    rintro y ⟨hyX, hy0⟩
    by_contra hunl
    rcases isUnlimited_iff_pos_or_neg.1 (isUnlimited_iff_not_isLimited.2 hunl) with hpos | hneg
    · exact hno y hyX hpos
    · exact not_lt_of_ge hy0 (by simpa using hneg 0)
  obtain ⟨r, _, hYr⟩ := hY_int.subset_Icc_real_of_forall_isLimited hY_lim
  obtain ⟨n, hn⟩ := exists_nat_gt r
  obtain ⟨x, hxX, _, hnx⟩ := hlarge n
  have hx0 : 0 ≤ x := (Nat.cast_nonneg n).trans hnx.le
  have hxr : x ≤ (r : ℝ*) := (hYr ⟨hxX, hx0⟩).2
  exact not_lt_of_ge hxr ((Hyperreal.coe_lt_coe.2 hn).trans (by simpa using hnx))

/-- Goldblatt Exercise 11.5.2(iv) (p. 131): If an internal set `X ⊆ ℝ*` has no limited members,
then `X ⊆ (-∞, -b) ∪ (b, ∞)` for some positive unlimited `b`. -/
theorem IsInternal.exists_posUnlimited_gap_of_no_limited {X : Set ℝ*} (hX : IsInternal X)
    (hno_lim : ∀ x ∈ X, IsUnlimited x) :
    ∃ b : ℝ*, IsPosUnlimited b ∧ ∀ x ∈ X, x < -b ∨ b < x := by
  -- Check `X⁺ = X ∩ (0, ∞)` and `X⁻ = (-X) ∩ (0, ∞)` using GLB!
  let Xpos : Set ℝ* := X ∩ Set.Ioi 0
  let Xneg : Set ℝ* := X ∩ Set.Iio 0
  have hpos_bound : ∃ b₁ : ℝ*, IsPosUnlimited b₁ ∧ ∀ x ∈ Xpos, b₁ < x := by
    rcases Xpos.eq_empty_or_nonempty with hemp | hne
    · exact ⟨Hyperreal.omega, Hyperreal.coe_lt_omega, fun x hx ↦ (hemp ▸ hx).elim⟩
    · obtain ⟨l, hl⟩ := (hX.inter (isInternal_Ioi 0)).exists_isGLB hne ⟨0, fun _ hx ↦ hx.2.le⟩
      have hl_unl : IsPosUnlimited l := by
        intro r
        obtain ⟨n, hn⟩ := exists_nat_gt r
        have hnl : (n : ℝ*) ≤ l := hl.2 fun x hx ↦ by
          have hunl := hno_lim x hx.1
          have hxpos : 0 < x := hx.2
          have hnx : (n : ℝ*) < x := by rw [← abs_of_pos hxpos]; exact hunl n
          exact hnx.le
        exact (Hyperreal.coe_lt_coe.2 hn).trans_le (by simpa using hnl)
      refine ⟨l - 1, fun r ↦ ?_, fun x hx ↦ ?_⟩
      · have := hl_unl (r + 1)
        rw [Hyperreal.coe_add, Hyperreal.coe_one] at this
        linarith
      · linarith [hl.1 hx]
  have hneg_bound : ∃ b₂ : ℝ*, IsPosUnlimited b₂ ∧ ∀ x ∈ Xneg, x < -b₂ := by
    rcases Xneg.eq_empty_or_nonempty with hemp | hne
    · exact ⟨Hyperreal.omega, Hyperreal.coe_lt_omega, fun x hx ↦ (hemp ▸ hx).elim⟩
    · obtain ⟨u, hu⟩ := (hX.inter (isInternal_Iio 0)).exists_isLUB hne ⟨0, fun _ hx ↦ hx.2.le⟩
      have hu_unl : IsNegUnlimited u := by
        intro r
        obtain ⟨n, hn⟩ := exists_nat_gt (-r)
        have hun : u ≤ -(n : ℝ*) := hu.2 fun x hx ↦ by
          have hunl := hno_lim x hx.1
          have hxneg : x < 0 := hx.2
          have h1 : (n : ℝ*) < -x := by rw [← abs_of_neg hxneg]; exact hunl n
          exact (lt_neg.1 h1).le
        have hnr : -(n : ℝ*) < (r : ℝ*) := by
          simpa using Hyperreal.coe_lt_coe.2 (neg_lt.1 hn)
        exact hun.trans_lt hnr
      refine ⟨-u - 1, fun r ↦ ?_, fun x hx ↦ ?_⟩
      · have := hu_unl (-r - 1)
        rw [Hyperreal.coe_sub, Hyperreal.coe_neg, Hyperreal.coe_one] at this
        linarith
      · linarith [hu.1 hx]
  obtain ⟨b₁, hb₁, h1⟩ := hpos_bound
  obtain ⟨b₂, hb₂, h2⟩ := hneg_bound
  refine ⟨min b₁ b₂, fun r ↦ lt_min (hb₁ r) (hb₂ r), fun x hx ↦ ?_⟩
  rcases lt_trichotomy x 0 with hlt | rfl | hgt
  · left
    have hxb₂ := h2 x ⟨hx, hlt⟩
    have : -b₂ ≤ -min b₁ b₂ := neg_le_neg (min_le_right b₁ b₂)
    exact hxb₂.trans_le this
  · exfalso
    have := hno_lim 0 hx 0
    simp at this
  · right
    exact (min_le_left b₁ b₂).trans_lt (h1 x ⟨hx, hgt⟩)

/-- Goldblatt Exercise 11.5.2(iii) (p. 131): If an internal set `X ⊆ ℝ*` has arbitrarily small
positive unlimited members, then `X` has a positive limited member. -/
theorem IsInternal.exists_pos_limited_of_arbitrarily_small_posUnlimited {X : Set ℝ*}
    (hX : IsInternal X)
    (hsmall : ∀ H : ℝ*, IsPosUnlimited H → ∃ x ∈ X, IsPosUnlimited x ∧ x < H) :
    ∃ x ∈ X, 0 < x ∧ IsLimited x := by
  by_contra hno
  push Not at hno
  let Y : Set ℝ* := X ∩ Set.Ioi 0
  have hY_int : IsInternal Y := hX.inter (isInternal_Ioi 0)
  have hY_unl : ∀ y ∈ Y, IsUnlimited y := by
    rintro y ⟨hyX, hy0⟩
    exact isUnlimited_iff_not_isLimited.2 (hno y hyX hy0)
  obtain ⟨b, hb_unl, hb_gap⟩ := hY_int.exists_posUnlimited_gap_of_no_limited hY_unl
  obtain ⟨x, hxX, hx_unl, hxb⟩ := hsmall b hb_unl
  have hx0 : 0 < x := by simpa using hx_unl 0
  rcases hb_gap x ⟨hxX, hx0⟩ with hlt | hgt
  · have hb0 : 0 < b := by simpa using hb_unl 0
    linarith
  · exact lt_asymm hxb hgt

/-! ## §11.6 External Sets -/

/-- Goldblatt §11.6 (p. 132): The set `*ℕ \ ℕ` of unlimited hypernaturals is external. -/
theorem isExternalNat_unlimited : IsExternalNat {N : ℕ* | IsUnlimitedNat N} := by
  intro hInt
  obtain ⟨m, hm_unl, hm_min⟩ := hInt.exists_least ⟨omegaNat, isUnlimitedNat_omegaNat⟩
  obtain ⟨K, hK_unl, hKm⟩ := exists_pred_isUnlimitedNat hm_unl
  have hlt : K < m := by
    rw [← hKm]
    induction K using Germ.inductionOn with | _ a =>
    exact Germ.coe_lt.2 (Eventually.of_forall fun i ↦ Nat.lt_succ_self (a i))
  exact not_le_of_gt hlt (hm_min K hK_unl)

/-- Goldblatt §11.6 (p. 132): The set `ℕ` inside `ℕ*` is external. -/
theorem isExternalNat_standard : IsExternalNat (Set.range (Nat.cast : ℕ → ℕ*)) := by
  intro hInt
  have hcompl : (Set.range (Nat.cast : ℕ → ℕ*))ᶜ = {N : ℕ* | IsUnlimitedNat N} := by
    ext N
    rw [Set.mem_compl_iff, Set.mem_range]
    change (¬ ∃ n : ℕ, (n : ℕ*) = N) ↔ IsUnlimitedNat N
    constructor
    · intro hnot
      by_contra hlim
      obtain ⟨n, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 hlim
      exact hnot ⟨n, rfl⟩
    · rintro hunl ⟨n, rfl⟩
      exact lt_irrefl (n : ℕ*) (hunl n)
  exact isExternalNat_unlimited (hcompl ▸ hInt.compl)

/-- Goldblatt §11.6 (p. 132): `ℕ` inside `ℝ*` is external. -/
theorem isExternal_nat_in_hyperreal : IsExternal (Set.range (Nat.cast : ℕ → ℝ*)) := by
  intro hInt
  have heq : Hypernat.toHyperreal '' (Set.range (Nat.cast : ℕ → ℕ*)) =
      Set.range (Nat.cast : ℕ → ℝ*) := by
    ext x
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, Hypernat.toHyperreal_natCast n⟩
    · rintro ⟨n, rfl⟩
      exact ⟨(n : ℕ*), ⟨n, rfl⟩, Hypernat.toHyperreal_natCast n⟩
  exact isExternalNat_standard (isInternal_image_hypernat_iff.1 (heq.symm ▸ hInt))

/-- Goldblatt §11.6 (p. 132): The set `ℝ` of standard real numbers inside `ℝ*` is external. -/
theorem isExternal_real : IsExternal (Set.range (fun r : ℝ ↦ (r : ℝ*))) := by
  intro hInt
  have hinter : Set.range (fun r : ℝ ↦ (r : ℝ*)) ∩ starSet (Set.range (Nat.cast : ℕ → ℝ)) =
      Set.range (Nat.cast : ℕ → ℝ*) := by
    ext x
    constructor
    · rintro ⟨⟨r, rfl⟩, hstar⟩
      rw [coe_mem_starSet] at hstar
      rcases hstar with ⟨n, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨⟨(n : ℝ), rfl⟩, coe_mem_starSet.2 ⟨n, rfl⟩⟩
  exact isExternal_nat_in_hyperreal (hinter ▸ hInt.inter (isInternal_starSet _))

/-- Goldblatt §11.6 (p. 132): The set `𝕃` of limited hyperreals is external. -/
theorem isExternal_limited : IsExternal {x : ℝ* | IsLimited x} := by
  intro hInt
  obtain ⟨r, _, hsub⟩ := hInt.subset_Icc_real_of_forall_isLimited (fun _ hx ↦ hx)
  have hmem : ((r + 1 : ℝ) : ℝ*) ∈ {x : ℝ* | IsLimited x} := isLimited_coe (r + 1)
  have hle : ((r + 1 : ℝ) : ℝ*) ≤ (r : ℝ*) := (hsub hmem).2
  have := Hyperreal.coe_le_coe.1 hle
  linarith

/-- Goldblatt §11.6 (p. 132): If an internal set `X` includes `𝕃`, then `[-b, b] ⊆ X` for some
positive unlimited `b`. -/
theorem IsInternal.exists_posUnlimited_Icc_subset_of_limited_subset {X : Set ℝ*}
    (hX : IsInternal X) (hL : {x : ℝ* | IsLimited x} ⊆ X) :
    ∃ b : ℝ*, IsPosUnlimited b ∧ Set.Icc (-b) b ⊆ X := by
  have hcompl_unl : ∀ x ∈ Xᶜ, IsUnlimited x :=
    fun x hx ↦ isUnlimited_iff_not_isLimited.2 (fun hlim ↦ hx (hL hlim))
  obtain ⟨b, hb_unl, hgap⟩ := hX.compl.exists_posUnlimited_gap_of_no_limited hcompl_unl
  refine ⟨b / 2, fun r ↦ ?_, fun x ⟨h1, h2⟩ ↦ ?_⟩
  · have := hb_unl (2 * r)
    rw [Hyperreal.coe_mul, Hyperreal.coe_ofNat] at this
    linarith
  · by_contra hxnot
    have hb0 : 0 < b := by simpa using hb_unl 0
    rcases hgap x hxnot with hlt | hgt <;> linarith

/-- Goldblatt §11.6 (p. 132): If `X` is a nonempty internal subset of `𝕀 = halo 0`, then
`X ⊆ [-c, c]` for some infinitesimal `c ≥ 0`. -/
theorem IsInternal.subset_Icc_infinitesimal_of_subset_halo_zero {X : Set ℝ*}
    (hX : IsInternal X) (hne : X.Nonempty) (hsub : X ⊆ halo 0) :
    ∃ c : ℝ*, 0 ≤ c ∧ IsInfinitesimal c ∧ X ⊆ Set.Icc (-c) c := by
  have hbdd_up : BddAbove X := ⟨1, fun x hx ↦ by
    rw [halo_zero] at hsub
    have h1 : |x| < 1 := by simpa using hsub hx 1 one_pos
    exact (le_abs_self x).trans h1.le⟩
  have hbdd_dn : BddBelow X := ⟨-1, fun x hx ↦ by
    rw [halo_zero] at hsub
    have h1 : -1 < x := by simpa using (abs_lt.1 (hsub hx 1 one_pos)).1
    exact h1.le⟩
  obtain ⟨u, hu⟩ := hX.exists_isLUB hne hbdd_up
  obtain ⟨l, hl⟩ := hX.exists_isGLB hne hbdd_dn
  have hu_inf : IsInfinitesimal u := by
    intro r hr
    have hr2 : 0 < r / 2 := half_pos hr
    have hub : u ≤ ((r / 2 : ℝ) : ℝ*) := hu.2 fun x hx ↦ by
      rw [halo_zero] at hsub
      exact (le_abs_self x).trans (hsub hx (r / 2) hr2).le
    obtain ⟨x₀, hx₀⟩ := hne
    rw [halo_zero] at hsub
    have hx₀_gt : -((r / 2 : ℝ) : ℝ*) < x₀ := (abs_lt.1 (hsub hx₀ (r / 2) hr2)).1
    have hlb : -((r / 2 : ℝ) : ℝ*) < u := hx₀_gt.trans_le (hu.1 hx₀)
    have hhalf : ((r / 2 : ℝ) : ℝ*) < (r : ℝ*) := Hyperreal.coe_lt_coe.2 (half_lt_self hr)
    rw [abs_lt]
    exact ⟨(neg_lt_neg hhalf).trans hlb, hub.trans_lt hhalf⟩
  have hl_inf : IsInfinitesimal l := by
    intro r hr
    have hr2 : 0 < r / 2 := half_pos hr
    have hlb : -((r / 2 : ℝ) : ℝ*) ≤ l := hl.2 fun x hx ↦ by
      rw [halo_zero] at hsub
      exact (abs_lt.1 (hsub hx (r / 2) hr2)).1.le
    obtain ⟨x₀, hx₀⟩ := hne
    rw [halo_zero] at hsub
    have hx₀_lt : x₀ < ((r / 2 : ℝ) : ℝ*) := (abs_lt.1 (hsub hx₀ (r / 2) hr2)).2
    have hub : l < ((r / 2 : ℝ) : ℝ*) := (hl.1 hx₀).trans_lt hx₀_lt
    have hhalf : ((r / 2 : ℝ) : ℝ*) < (r : ℝ*) := Hyperreal.coe_lt_coe.2 (half_lt_self hr)
    rw [abs_lt]
    exact ⟨(neg_lt_neg hhalf).trans_le hlb, hub.trans hhalf⟩
  let c : ℝ* := |u| + |l|
  refine ⟨c, by positivity, hu_inf.abs.add hl_inf.abs, fun x hx ↦ ⟨?_, ?_⟩⟩
  · have h1 : -|l| ≤ l := neg_abs_le l
    have h2 : -c ≤ -|l| := by dsimp [c]; linarith [abs_nonneg u]
    exact h2.trans (h1.trans (hl.1 hx))
  · have h1 : u ≤ |u| := le_abs_self u
    have h2 : |u| ≤ c := by dsimp [c]; linarith [abs_nonneg l]
    exact (hu.1 hx).trans (h1.trans h2)

/-- Goldblatt §11.6 (p. 132): `𝕀 = halo 0` is external, and in fact every halo `halo b` (as well as
its left and right halves) is external! -/
theorem isExternal_halo_zero : IsExternal (halo 0) := by
  intro hInt
  obtain ⟨c, hc0, hc_inf, hsub⟩ :=
    hInt.subset_Icc_infinitesimal_of_subset_halo_zero ⟨0, InfClose.refl 0⟩ Set.Subset.rfl
  let d : ℝ* := c + Hyperreal.epsilon
  have hd_mem : d ∈ halo 0 := by
    rw [halo_zero]
    exact hc_inf.add isInfinitesimal_epsilon
  have hdc : d ≤ c := (hsub hd_mem).2
  linarith [Hyperreal.epsilon_pos]

theorem isExternal_halo (b : ℝ*) : IsExternal (halo b) := by
  intro hInt
  rcases hInt with ⟨A, hA⟩
  rcases ofSeq_surjective b with ⟨s, rfl⟩
  have h0 : halo 0 = internalSet (fun n ↦ (fun x ↦ x + s n) ⁻¹' (A n)) := by
    ext x
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hmem : ofSeq (fun n ↦ r n + s n) ∈ halo (ofSeq s) ↔ ofSeq r ∈ halo 0 := by
      change (ofSeq s ≈ₕ ofSeq r + ofSeq s) ↔ ((0 : ℝ*) ≈ₕ ofSeq r)
      unfold InfClose
      have : ofSeq s - (ofSeq r + ofSeq s) = 0 - ofSeq r := by ring
      rw [this]
    rw [← hmem, hA]
    exact ofSeq_mem_internalSet
  exact isExternal_halo_zero ⟨_, h0⟩

theorem isExternal_halo_right_half (b : ℝ*) :
    IsExternal {x : ℝ* | b < x ∧ b ≈ₕ x} := by
  intro hInt
  have hpos_zero : IsInternal {x : ℝ* | 0 < x ∧ (0 : ℝ*) ≈ₕ x} := by
    rcases hInt with ⟨A, hA⟩
    rcases ofSeq_surjective b with ⟨s, rfl⟩
    refine ⟨fun n ↦ (fun x ↦ x + s n) ⁻¹' (A n), ?_⟩
    ext x; rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hmem : ofSeq (fun n ↦ r n + s n) ∈ {y : ℝ* | ofSeq s < y ∧ ofSeq s ≈ₕ y} ↔
        ofSeq r ∈ {y : ℝ* | 0 < y ∧ (0 : ℝ*) ≈ₕ y} := by
      change (ofSeq s < ofSeq (fun n ↦ r n + s n) ∧ ofSeq s ≈ₕ ofSeq (fun n ↦ r n + s n)) ↔
        (0 < ofSeq r ∧ (0 : ℝ*) ≈ₕ ofSeq r)
      constructor
      · rintro ⟨hlt, hcl⟩
        have hlt' : (0 : ℝ*) < ofSeq r := by
          have : ofSeq (fun n ↦ r n + s n) = ofSeq r + ofSeq s := rfl
          linarith
        refine ⟨hlt', ?_⟩
        unfold InfClose at hcl ⊢
        have : 0 - ofSeq r = ofSeq s - ofSeq (fun n ↦ r n + s n) := by
          change 0 - ofSeq r = ofSeq s - (ofSeq r + ofSeq s); ring
        rwa [this]
      · rintro ⟨hlt, hcl⟩
        refine ⟨by change ofSeq s < ofSeq r + ofSeq s; linarith, ?_⟩
        change IsInfinitesimal (ofSeq s - (ofSeq r + ofSeq s))
        unfold InfClose at hcl
        have : ofSeq s - (ofSeq r + ofSeq s) = 0 - ofSeq r := by ring
        rwa [this]
    rw [← hmem, hA]
    exact ofSeq_mem_internalSet
  have hneg_zero : IsInternal {x : ℝ* | x < 0 ∧ (0 : ℝ*) ≈ₕ x} := by
    rcases hpos_zero with ⟨B, hB⟩
    refine ⟨fun n ↦ (- ·) ⁻¹' (B n), ?_⟩
    ext x; rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hmem : -ofSeq r ∈ {y : ℝ* | 0 < y ∧ (0 : ℝ*) ≈ₕ y} ↔
        ofSeq r ∈ {y : ℝ* | y < 0 ∧ (0 : ℝ*) ≈ₕ y} := by
      change (0 < -ofSeq r ∧ (0 : ℝ*) ≈ₕ -ofSeq r) ↔ (ofSeq r < 0 ∧ (0 : ℝ*) ≈ₕ ofSeq r)
      rw [Left.neg_pos_iff]
      refine and_congr_right fun _ ↦ ?_
      unfold InfClose
      have : 0 - (-ofSeq r) = -(0 - ofSeq r) := by ring
      rw [this]
      exact ⟨fun h ↦ by simpa using h.neg, fun h ↦ h.neg⟩
    rw [← hmem, hB]
    exact ofSeq_mem_internalSet
  have hhalo : halo 0 = {x : ℝ* | 0 < x ∧ (0 : ℝ*) ≈ₕ x} ∪
      {x : ℝ* | x < 0 ∧ (0 : ℝ*) ≈ₕ x} ∪ {(0 : ℝ*)} := by
    ext x
    simp only [halo, Set.mem_union, Set.mem_singleton_iff]
    change ((0 : ℝ*) ≈ₕ x) ↔
      ((0 < x ∧ (0 : ℝ*) ≈ₕ x) ∨ (x < 0 ∧ (0 : ℝ*) ≈ₕ x)) ∨ x = 0
    rcases lt_trichotomy 0 x with hgt | rfl | hlt
    · simp [hgt, hgt.ne', not_lt_of_gt hgt]
    · simp [InfClose.refl]
    · simp [hlt, hlt.ne, not_lt_of_gt hlt]
  exact isExternal_halo_zero (hhalo ▸ (hpos_zero.union hneg_zero).union (isInternal_singleton 0))

/-- Goldblatt Exercise 11.6.1 (p. 133): `ℝ₊`, `ℤ`, `ℚ`, unlimited hyperreals, positive unlimited
hyperreals, negative unlimited hyperreals, and appreciable hyperreals are all external! -/
theorem isExternal_pos_real : IsExternal ((fun r : ℝ ↦ (r : ℝ*)) '' {r : ℝ | 0 < r}) := by
  intro hInt
  have hneg : IsInternal ((fun r : ℝ ↦ (r : ℝ*)) '' {r : ℝ | r < 0}) := by
    rcases hInt with ⟨A, hA⟩
    refine ⟨fun n ↦ (- ·) ⁻¹' (A n), ?_⟩
    ext x; rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hmem : -ofSeq r ∈ ((fun t : ℝ ↦ (t : ℝ*)) '' {t : ℝ | 0 < t}) ↔
        ofSeq r ∈ ((fun t : ℝ ↦ (t : ℝ*)) '' {t : ℝ | t < 0}) := by
      constructor
      · rintro ⟨t, ht, heq⟩
        refine ⟨-t, show -t < 0 from neg_lt_zero.2 ht, ?_⟩
        dsimp only at heq ⊢
        rw [Hyperreal.coe_neg, heq, neg_neg]
      · rintro ⟨t, ht, heq⟩
        refine ⟨-t, show 0 < -t from neg_pos.2 ht, ?_⟩
        dsimp only at heq ⊢
        rw [Hyperreal.coe_neg, ← heq]
    rw [← hmem, hA]
    exact ofSeq_mem_internalSet
  have hR : Set.range (fun r : ℝ ↦ (r : ℝ*)) =
      ((fun r : ℝ ↦ (r : ℝ*)) '' {r : ℝ | 0 < r}) ∪
      ((fun r : ℝ ↦ (r : ℝ*)) '' {r : ℝ | r < 0}) ∪ {(0 : ℝ*)} := by
    ext x
    constructor
    · rintro ⟨r, rfl⟩
      rcases lt_trichotomy 0 r with hpos | rfl | hneg'
      · exact Or.inl (Or.inl ⟨r, hpos, rfl⟩)
      · exact Or.inr rfl
      · exact Or.inl (Or.inr ⟨r, hneg', rfl⟩)
    · rintro ((⟨r, _, rfl⟩ | ⟨r, _, rfl⟩) | rfl)
      · exact ⟨r, rfl⟩
      · exact ⟨r, rfl⟩
      · exact ⟨0, rfl⟩
  exact isExternal_real (hR ▸ (hInt.union hneg).union (isInternal_singleton 0))

theorem isExternal_int : IsExternal (Set.range (Int.cast : ℤ → ℝ*)) := by
  intro hInt
  have hinter : Set.range (Int.cast : ℤ → ℝ*) ∩ Set.Ici 0 =
      Set.range (Nat.cast : ℕ → ℝ*) := by
    ext x
    constructor
    · rintro ⟨⟨z, rfl⟩, hz0⟩
      have hz_nn : 0 ≤ z := by
        have : (0 : ℝ*) ≤ ((z : ℝ) : ℝ*) := by simpa using hz0
        exact_mod_cast Hyperreal.coe_le_coe.1 this
      exact ⟨z.toNat, by
        rw [← coe_natCast_hyperreal, ← coe_intCast_hyperreal]
        exact_mod_cast Int.toNat_of_nonneg hz_nn⟩
    · rintro ⟨n, rfl⟩
      refine ⟨⟨(n : ℤ), by rw [← coe_intCast_hyperreal, ← coe_natCast_hyperreal]; push_cast; rfl⟩, ?_⟩
      show (0 : ℝ*) ≤ (n : ℝ*)
      exact Nat.cast_nonneg n
  exact isExternal_nat_in_hyperreal (hinter ▸ hInt.inter (isInternal_Ici 0))

theorem isExternal_rat : IsExternal (Set.range (Rat.cast : ℚ → ℝ*)) := by
  intro hInt
  have hinter : Set.range (Rat.cast : ℚ → ℝ*) ∩ starSet (Set.range (Int.cast : ℤ → ℝ)) =
      Set.range (Int.cast : ℤ → ℝ*) := by
    ext x
    constructor
    · rintro ⟨⟨q, rfl⟩, hstar⟩
      rw [← coe_ratCast_hyperreal, coe_mem_starSet] at hstar
      rcases hstar with ⟨z, hz⟩
      exact ⟨z, by rw [← coe_intCast_hyperreal, ← coe_ratCast_hyperreal, hz]⟩
    · rintro ⟨z, rfl⟩
      refine ⟨⟨(z : ℚ), by rw [← coe_ratCast_hyperreal, ← coe_intCast_hyperreal]; push_cast; rfl⟩, ?_⟩
      rw [← coe_intCast_hyperreal, coe_mem_starSet]
      exact ⟨z, rfl⟩
  exact isExternal_int (hinter ▸ hInt.inter (isInternal_starSet _))

theorem isExternal_unlimited : IsExternal {x : ℝ* | IsUnlimited x} := by
  intro hInt
  have heq : ({x : ℝ* | IsUnlimited x})ᶜ = {x : ℝ* | IsLimited x} := by
    ext x; simp [isUnlimited_iff_not_isLimited]
  exact isExternal_limited (heq ▸ hInt.compl)

theorem isExternal_posUnlimited : IsExternal {x : ℝ* | IsPosUnlimited x} := by
  intro hInt
  have hneg : IsInternal {x : ℝ* | IsNegUnlimited x} := by
    rcases hInt with ⟨A, hA⟩
    refine ⟨fun n ↦ (- ·) ⁻¹' (A n), ?_⟩
    ext x; rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hmem : -ofSeq r ∈ {y : ℝ* | IsPosUnlimited y} ↔ ofSeq r ∈ {y : ℝ* | IsNegUnlimited y} := by
      change IsPosUnlimited (-ofSeq r) ↔ IsNegUnlimited (ofSeq r)
      constructor
      · intro h s
        have hs := h (-s)
        rw [Hyperreal.coe_neg] at hs
        linarith
      · intro h s
        have hs := h (-s)
        rw [Hyperreal.coe_neg] at hs
        linarith
    rw [← hmem, hA]
    exact ofSeq_mem_internalSet
  have hunion : {x : ℝ* | IsUnlimited x} =
      {x : ℝ* | IsPosUnlimited x} ∪ {x : ℝ* | IsNegUnlimited x} := by
    ext x; exact isUnlimited_iff_pos_or_neg
  exact isExternal_unlimited (hunion ▸ hInt.union hneg)

theorem isExternal_negUnlimited : IsExternal {x : ℝ* | IsNegUnlimited x} := by
  intro hInt
  have hpos : IsInternal {x : ℝ* | IsPosUnlimited x} := by
    rcases hInt with ⟨A, hA⟩
    refine ⟨fun n ↦ (- ·) ⁻¹' (A n), ?_⟩
    ext x; rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hmem : -ofSeq r ∈ {y : ℝ* | IsNegUnlimited y} ↔ ofSeq r ∈ {y : ℝ* | IsPosUnlimited y} := by
      change IsNegUnlimited (-ofSeq r) ↔ IsPosUnlimited (ofSeq r)
      constructor
      · intro h s
        have hs := h (-s)
        rw [Hyperreal.coe_neg] at hs
        linarith
      · intro h s
        have hs := h (-s)
        rw [Hyperreal.coe_neg] at hs
        linarith
    rw [← hmem, hA]
    exact ofSeq_mem_internalSet
  exact isExternal_posUnlimited hpos

theorem isExternal_appreciable : IsExternal {x : ℝ* | IsAppreciable x} := by
  intro hInt
  obtain ⟨r, hr0, hsub⟩ := hInt.subset_Icc_real_of_forall_isLimited (fun _ hx ↦ hx.1)
  have happ : IsAppreciable ((r + 1 : ℝ) : ℝ*) := isAppreciable_coe_iff.2 (by linarith)
  have hle : ((r + 1 : ℝ) : ℝ*) ≤ (r : ℝ*) := (hsub happ).2
  linarith [Hyperreal.coe_le_coe.1 hle]

/-! ## §11.7 Internal Set Definition Principle & Finite Real Subsets -/

/-- Goldblatt 11.7.1 (**Internal Set Definition Principle**, p. 134):
Given any componentwise family of predicates `P : ℕ → ℝ → Prop` (built from standard formulas with
hyperreal parameters `c_i = [c_{i,n}]` and internal sets `X_j = [A_{j,n}]`), the set
`{x ∈ ℝ* | [P_n(x_n)]}` is internal, namely `internalSet (fun n ↦ {r : ℝ | P n r})`. -/
theorem isInternal_of_componentPred (P : ℕ → ℝ → Prop) :
    IsInternal {x : ℝ* | Germ.LiftPred (fun p : ℝ × (ℝ → Prop) ↦ p.2 p.1)
      (Germ.map₂ Prod.mk x (P : Germ (hyperfilter ℕ : Filter ℕ) (ℝ → Prop)))} := by
  refine ⟨fun n ↦ {r : ℝ | P n r}, ?_⟩
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp [ofSeq_mem_internalSet]
  rfl

/-- Quantifier transfer for Internal Set Definition on `ℕ* × ℕ*`:
If `R : ℕ → ℕ → ℕ → Prop` is a componentwise binary predicate, then
`{k ∈ ℕ* | ∀ z ∈ ℕ*, LiftRel_n (R n k z)}` equals `internalNatSet (fun n ↦ {k | ∀ z, R n k z})`! -/
theorem internalNatSet_forall (R : ℕ → ℕ → ℕ → Prop) :
    {k : ℕ* | ∀ z : ℕ*,
      Germ.LiftPred (fun t : ℕ × ℕ × (ℕ → ℕ → Prop) ↦ t.2.2 t.1 t.2.1)
        (Germ.map₂ Prod.mk k (Germ.map₂ Prod.mk z (R : Germ (hyperfilter ℕ : Filter ℕ) _)))} =
    internalNatSet (fun n ↦ {k : ℕ | ∀ z : ℕ, R n k z}) := by
  ext k
  induction k using Germ.inductionOn with | _ a =>
  rw [Set.mem_ofPred_eq, coe_mem_internalNatSet]
  constructor
  · intro h
    by_contra hnot
    have hnot' : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ z : ℕ, ¬ R n (a n) z :=
      (Ultrafilter.eventually_not.2 hnot).mono fun n hn ↦ not_forall.1 hn
    let zSeq : ℕ → ℕ := fun n ↦ if hz : ∃ z : ℕ, ¬ R n (a n) z then hz.choose else 0
    have hz_true : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), R n (a n) (zSeq n) :=
      Germ.liftPred_coe.1 (h (zSeq : ℕ*))
    obtain ⟨n, hn1, hn2⟩ := (hnot'.and hz_true).exists
    have hspec : ¬ R n (a n) (zSeq n) := by simpa only [zSeq, hn1, ↓reduceDIte] using hn1.choose_spec
    exact hspec hn2
  · intro hev z
    induction z using Germ.inductionOn with | _ b =>
    exact Germ.liftPred_coe.2 (hev.mono fun n hn ↦ hn (b n))

/-- Quantifier transfer for Internal Set Definition on `ℕ* × ℝ*`:
`{k ∈ ℕ* | ∀ z ∈ ℝ*, R_n(k_n, z_n)}` is an internal subset of `ℕ*`! -/
theorem isInternalNat_forall_real (R : ℕ → ℕ → ℝ → Prop) :
    IsInternalNat {k : ℕ* | ∀ z : ℝ*,
      Germ.LiftPred (fun t : ℕ × ℝ × (ℕ → ℝ → Prop) ↦ t.2.2 t.1 t.2.1)
        (Germ.map₂ Prod.mk k (Germ.map₂ Prod.mk z (R : Germ (hyperfilter ℕ : Filter ℕ) _)))} := by
  refine ⟨fun n ↦ {k : ℕ | ∀ z : ℝ, R n k z}, ?_⟩
  ext k
  induction k using Germ.inductionOn with | _ a =>
  rw [Set.mem_ofPred_eq, coe_mem_internalNatSet]
  constructor
  · intro h
    by_contra hnot
    have hnot' : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ z : ℝ, ¬ R n (a n) z :=
      (Ultrafilter.eventually_not.2 hnot).mono fun n hn ↦ not_forall.1 hn
    let zSeq : ℕ → ℝ := fun n ↦ if hz : ∃ z : ℝ, ¬ R n (a n) z then hz.choose else 0
    have hz_true : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), R n (a n) (zSeq n) :=
      Germ.liftPred_coe.1 (h (ofSeq zSeq))
    obtain ⟨n, hn1, hn2⟩ := (hnot'.and hz_true).exists
    have hspec : ¬ R n (a n) (zSeq n) := by simpa only [zSeq, hn1, ↓reduceDIte] using hn1.choose_spec
    exact hspec hn2
  · intro hev z
    rcases ofSeq_surjective z with ⟨b, rfl⟩
    exact Germ.liftPred_coe.2 (hev.mono fun n hn ↦ hn (b n))

/-- Existential quantifier transfer for Internal Set Definition on `ℕ* × ℝ*`:
`{k ∈ ℕ* | ∃ z ∈ ℝ*, R_n(k_n, z_n)}` is an internal subset of `ℕ*`! -/
theorem isInternalNat_exists_real (R : ℕ → ℕ → ℝ → Prop) :
    IsInternalNat {k : ℕ* | ∃ z : ℝ*,
      Germ.LiftPred (fun t : ℕ × ℝ × (ℕ → ℝ → Prop) ↦ t.2.2 t.1 t.2.1)
        (Germ.map₂ Prod.mk k (Germ.map₂ Prod.mk z (R : Germ (hyperfilter ℕ : Filter ℕ) _)))} := by
  refine ⟨fun n ↦ {k : ℕ | ∃ z : ℝ, R n k z}, ?_⟩
  ext k
  induction k using Germ.inductionOn with | _ a =>
  rw [Set.mem_ofPred_eq, coe_mem_internalNatSet]
  constructor
  · rintro ⟨z, hz⟩
    rcases ofSeq_surjective z with ⟨b, rfl⟩
    exact (Germ.liftPred_coe.1 hz).mono fun n hn ↦ ⟨b n, hn⟩
  · intro hev
    let b : ℕ → ℝ := fun n ↦ if h : ∃ z : ℝ, R n (a n) z then h.choose else 0
    refine ⟨ofSeq b, Germ.liftPred_coe.2 ?_⟩
    exact hev.mono fun n hn ↦ by
      change ∃ z : ℝ, R n (a n) z at hn
      simpa only [b, hn, ↓reduceDIte] using hn.choose_spec

/-- Goldblatt §11.7 (p. 135): **Every infinite set of real numbers is external!**
Equivalently, `A ⊆ ℝ` (embedded in `ℝ*`) is internal iff `A` is finite. -/
theorem isInternal_real_set_iff_finite {A : Set ℝ} :
    IsInternal ((fun r : ℝ ↦ (r : ℝ*)) '' A) ↔ A.Finite := by
  constructor
  · intro hA
    by_contra hinf
    have hA_inf : A.Infinite := hinf
    let f : ℕ ↪ A := hA_inf.natEmbedding
    let g : ℕ → ℝ := fun n ↦ (f n).1
    have hg_inj : Function.Injective g := fun m n hmn ↦ f.injective (Subtype.ext hmn)
    let X : Set ℝ := Set.range g
    have hXA : X ⊆ A := by rintro _ ⟨n, rfl⟩; exact (f n).2
    have hX_int : IsInternal ((fun r : ℝ ↦ (r : ℝ*)) '' X) :=
      isInternal_subset_of_real_internal hA hXA
    rcases hX_int with ⟨B, hB⟩
    -- Apply Internal Set Definition to `N_set = {k ∈ ℕ* | *g(k) ∈ X}` = `Set.range Nat.cast`!
    let Nset : Set ℕ* := internalNatSet (fun n ↦ g ⁻¹' (B n))
    have hNset_int : IsInternalNat Nset := ⟨_, rfl⟩
    have hNset_eq : Nset = Set.range (Nat.cast : ℕ → ℕ*) := by
      ext K
      induction K using Germ.inductionOn with | _ a =>
      have hmem : (a : ℕ*) ∈ Nset ↔ starSeq g (a : ℕ*) ∈ ((fun r : ℝ ↦ (r : ℝ*)) '' X) := by
        rw [hB]
        exact Iff.rfl
      rw [hmem]
      constructor
      · rintro ⟨r, ⟨m, rfl⟩, hgeq⟩
        have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), g (a i) = g m :=
          Germ.coe_eq.1 hgeq.symm
        exact ⟨m, Germ.coe_eq.2 (hev.mono fun i hi ↦ hg_inj hi.symm)⟩
      · rintro ⟨m, heq⟩
        refine ⟨g m, ⟨m, rfl⟩, ?_⟩
        have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), a i = m :=
          Germ.coe_eq.1 heq.symm
        exact Germ.coe_eq.2 (hev.mono fun i hi ↦ congrArg g hi.symm)
    exact isExternalNat_standard (hNset_eq ▸ hNset_int)
  · intro hfin
    exact isInternal_of_finite (hfin.image _)

/-! ## §11.8–11.9 The Underflow Principle and Halo Permanence -/

/-- Goldblatt Theorem 11.8.1 (p. 136, **The Underflow Principle**):
Let `X` be an internal subset of `ℕ*`, and let `K ∈ ℕ*` be unlimited. If every unlimited
`H ∈ ℕ*` with `H ≤ K` belongs to `X`, then there is some `k ∈ ℕ` such that every `N ∈ ℕ*` with
`k ≤ N ≤ K` belongs to `X` (and in particular `(n : ℕ*) ∈ X` for all `n ≥ k` in `ℕ`). -/
theorem underflow_nat {X : Set ℕ*} (hX : IsInternalNat X) {K : ℕ*} (hK : IsUnlimitedNat K)
    (hunl : ∀ H : ℕ*, IsUnlimitedNat H → H ≤ K → H ∈ X) :
    ∃ k : ℕ, ∀ N : ℕ*, (k : ℕ*) ≤ N → N ≤ K → N ∈ X := by
  rcases hX with ⟨A, rfl⟩
  induction K using Germ.inductionOn with | _ b =>
  -- By Internal Set Definition (11.7.1), `Y = {m ∈ ℕ* | m ≤ K ∧ ∀ z ∈ ℕ*, m ≤ z ≤ K → z ∈ X}`
  -- is internal!
  let R : ℕ → ℕ → ℕ → Prop := fun n m z ↦ (m ≤ z ∧ z ≤ b n) → z ∈ A n
  let Y : Set ℕ* := Set.Iic (b : ℕ*) ∩ internalNatSet (fun n ↦ {m : ℕ | ∀ z : ℕ, R n m z})
  have hY_int : IsInternalNat Y := (isInternalNat_Iic _).inter ⟨_, rfl⟩
  have hY_iff : ∀ m : ℕ*, m ∈ Y ↔ m ≤ (b : ℕ*) ∧ ∀ z : ℕ*, m ≤ z → z ≤ (b : ℕ*) → z ∈ internalNatSet A := by
    intro m
    dsimp only [Y]
    rw [Set.mem_inter_iff, Set.mem_Iic, ← internalNatSet_forall R]
    induction m using Germ.inductionOn with | _ c =>
    rw [Set.mem_ofPred_eq]
    refine and_congr_right fun _ ↦ forall_congr' fun z ↦ ?_
    induction z using Germ.inductionOn with | _ d =>
    simp only [Germ.map₂_coe, coe_mem_internalNatSet]
    constructor
    · intro h h1 h2
      exact ((h.and (Germ.coe_le.1 h1)).and (Germ.coe_le.1 h2)).mono fun n ⟨⟨hr, hc⟩, hd⟩ ↦ hr ⟨hc, hd⟩
    · intro h
      by_contra hnot
      have hnot' : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (c n ≤ d n ∧ d n ≤ b n) ∧ d n ∉ A n :=
        (Ultrafilter.eventually_not.2 hnot).mono fun n hn ↦ by
          change ¬ ((c n ≤ d n ∧ d n ≤ b n) → d n ∈ A n) at hn
          push Not at hn
          exact hn
      have hc : (c : ℕ*) ≤ (d : ℕ*) := Germ.coe_le.2 (hnot'.mono fun n hn ↦ hn.1.1)
      have hd : (d : ℕ*) ≤ (b : ℕ*) := Germ.coe_le.2 (hnot'.mono fun n hn ↦ hn.1.2)
      obtain ⟨n, hn1, hn2⟩ := (hnot'.and (h hc hd)).exists
      exact hn1.2 hn2
  have hK_mem : (b : ℕ*) ∈ Y := (hY_iff _).2 ⟨le_rfl, fun z h1 h2 ↦ by
    have : z = (b : ℕ*) := le_antisymm h2 h1
    subst this
    exact hunl _ hK le_rfl⟩
  obtain ⟨m, hmY, hm_min⟩ := hY_int.exists_least ⟨(b : ℕ*), hK_mem⟩
  have hm_lim : ¬ IsUnlimitedNat m := by
    intro hm_unl
    obtain ⟨p, hp_unl, hpm⟩ := exists_pred_isUnlimitedNat hm_unl
    have hpK : p ≤ (b : ℕ*) := by
      have hmK := ((hY_iff m).1 hmY).1
      have hpm_le : p ≤ m := by
        rw [← hpm]
        induction p using Germ.inductionOn with | _ q =>
        exact Germ.coe_le.2 (Eventually.of_forall fun i ↦ Nat.le_succ (q i))
      exact hpm_le.trans hmK
    have hpY : p ∈ Y := (hY_iff p).2 ⟨hpK, fun z hpz hzK ↦ by
      have hz_unl : IsUnlimitedNat z := fun n ↦ (hp_unl n).trans_le hpz
      exact hunl z hz_unl hzK⟩
    have hlt : p < m := by
      rw [← hpm]
      induction p using Germ.inductionOn with | _ q =>
      exact Germ.coe_lt.2 (Eventually.of_forall fun i ↦ Nat.lt_succ_self (q i))
    exact not_le_of_gt hlt (hm_min p hpY)
  obtain ⟨k, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 hm_lim
  exact ⟨k, ((hY_iff (k : ℕ*)).1 hmY).2⟩

/-- Goldblatt Exercise 11.8.2 (p. 137): If an internal subset `X ⊆ ℕ*` contains arbitrarily large
standard members, then `X` contains arbitrarily small unlimited members! -/
theorem arbitrarily_small_unlimited_of_arbitrarily_large_nat {X : Set ℕ*} (hX : IsInternalNat X)
    (hlarge : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ (n : ℕ*) ∈ X) :
    ∀ K : ℕ*, IsUnlimitedNat K → ∃ H ∈ X, IsUnlimitedNat H ∧ H ≤ K := by
  intro K hK
  by_contra hno
  push Not at hno
  have hcompl : ∀ H : ℕ*, IsUnlimitedNat H → H ≤ K → H ∈ Xᶜ :=
    fun H hH hHK hHX ↦ not_lt_of_ge hHK (hno H hHX hH)
  obtain ⟨k, hk⟩ := underflow_nat hX.compl hK hcompl
  obtain ⟨n, hkn, hnX⟩ := hlarge k
  exact hk (n : ℕ*) (by exact_mod_cast hkn) (hK n).le hnX

/-- Goldblatt Exercise 11.8.2 corollary (p. 137): If `A ⊆ ℕ` is infinite, then `*A` contains
arbitrarily small unlimited hypernaturals! -/
theorem starNatSet_arbitrarily_small_unlimited_of_infinite {A : Set ℕ} (hA : A.Infinite) :
    ∀ K : ℕ*, IsUnlimitedNat K → ∃ H ∈ starNatSet A, IsUnlimitedNat H ∧ H ≤ K := by
  refine arbitrarily_small_unlimited_of_arbitrarily_large_nat (isInternalNat_starNatSet A) ?_
  intro k
  obtain ⟨n, hnA, hkn⟩ := hA.exists_gt k
  exact ⟨n, hkn.le, natCast_mem_starNatSet.2 hnA⟩

/-- Goldblatt Theorem 11.9.1 (pp. 137–138, **Halo Permanence**):
If an internal subset `X ⊆ ℝ*` contains `halo b`, then there is a standard `e > 0` in `ℝ` such
that `{z ∈ ℝ* | |z - b| < e} ⊆ X`! -/
theorem IsInternal.exists_real_ball_subset_of_halo_subset {X : Set ℝ*} (hX : IsInternal X)
    {b : ℝ*} (hhalo : halo b ⊆ X) :
    ∃ e : ℝ, 0 < e ∧ {z : ℝ* | |z - b| < (e : ℝ*)} ⊆ X := by
  rcases hX with ⟨A, rfl⟩
  rcases ofSeq_surjective b with ⟨s, rfl⟩
  -- Define `Y = {k ∈ ℕ* | 1 ≤ k ∧ ∀ z ∈ ℝ*, |z - b| < 1/k → z ∈ X}` via 11.7.1!
  let R : ℕ → ℕ → ℝ → Prop := fun n k z ↦ |z - s n| < 1 / (k : ℝ) → z ∈ A n
  let Y : Set ℕ* := Set.Ici 1 ∩ internalNatSet (fun n ↦ {k : ℕ | ∀ z : ℝ, R n k z})
  have hY_int : IsInternalNat Y := (isInternalNat_Ici 1).inter ⟨_, rfl⟩
  have hY_mem_of_unl : ∀ H : ℕ*, IsUnlimitedNat H → H ∈ Y := by
    intro H hH
    induction H using Germ.inductionOn with | _ c =>
    refine ⟨Germ.coe_le.2 ((Germ.coe_lt.1 (hH 0)).mono fun i hi ↦ by change 1 ≤ c i; omega), ?_⟩
    rw [coe_mem_internalNatSet]
    by_contra hnot
    have hnot' : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ z : ℝ, |z - s n| < 1 / (c n : ℝ) ∧ z ∉ A n :=
      (Ultrafilter.eventually_not.2 hnot).mono fun n hn ↦ by
        change ¬ ∀ z : ℝ, |z - s n| < 1 / (c n : ℝ) → z ∈ A n at hn
        push Not at hn
        exact hn
    let zSeq : ℕ → ℝ := fun n ↦
      if hz : ∃ z : ℝ, |z - s n| < 1 / (c n : ℝ) ∧ z ∉ A n then hz.choose else 0
    have hz_close : ofSeq zSeq ∈ halo (ofSeq s) := by
      intro r hr
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr
      have hc_gt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), m + 1 < c n := Germ.coe_lt.1 (hH (m + 1))
      have hbd : |ofSeq zSeq - ofSeq s| < ((1 / ((m + 1 : ℕ) : ℝ) : ℝ) : ℝ*) := by
        refine ofSeq_lt_ofSeq.2 ((hnot'.and hc_gt).mono fun n ⟨hn1, hn2⟩ ↦ ?_)
        have h1 : |zSeq n - s n| < 1 / (c n : ℝ) := by
          simpa only [zSeq, hn1, ↓reduceDIte] using hn1.choose_spec.1
        have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
        have h2 : 1 / (c n : ℝ) < 1 / ((m + 1 : ℕ) : ℝ) :=
          one_div_lt_one_div_of_lt hpos (by exact_mod_cast hn2)
        exact h1.trans h2
      have hmr : ((1 / ((m + 1 : ℕ) : ℝ) : ℝ) : ℝ*) < (r : ℝ*) :=
        Hyperreal.coe_lt_coe.2 (by push_cast; exact hm)
      have hlt_all : |ofSeq zSeq - ofSeq s| < (r : ℝ*) := hbd.trans hmr
      simpa only [InfClose, abs_sub_comm] using hlt_all
    have hzA : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), zSeq n ∈ A n :=
      ofSeq_mem_internalSet.1 (hhalo hz_close)
    obtain ⟨n, hn1, hn2⟩ := (hnot'.and hzA).exists
    have hnotA : zSeq n ∉ A n := by simpa only [zSeq, hn1, ↓reduceDIte] using hn1.choose_spec.2
    exact hnotA hn2
  obtain ⟨k, hk⟩ := underflow_nat hY_int isUnlimitedNat_omegaNat
    (fun H hH _ ↦ hY_mem_of_unl H hH)
  let m : ℕ := max k 1
  have hmY : (m : ℕ*) ∈ Y := hk (m : ℕ*) (by exact_mod_cast le_max_left k 1)
    (isUnlimitedNat_omegaNat m).le
  have hm_ev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∀ z : ℝ, |z - s n| < 1 / (m : ℝ) → z ∈ A n :=
    coe_mem_internalNatSet.1 hmY.2
  have hm_pos : (0 : ℝ) < 1 / (m : ℝ) := by
    have : 1 ≤ m := le_max_right k 1
    positivity
  refine ⟨1 / (m : ℝ), hm_pos, fun z hz ↦ ?_⟩
  rcases ofSeq_surjective z with ⟨t, rfl⟩
  have hzt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |t n - s n| < 1 / (m : ℝ) :=
    ofSeq_lt_ofSeq.1 hz
  exact ofSeq_mem_internalSet.2 ((hm_ev.and hzt).mono fun n ⟨h1, h2⟩ ↦ h1 (t n) h2)

/-! ## §11.10–11.11 Countable Saturation and Consequences -/

/-- Goldblatt Theorem 11.10.1 (pp. 138–139, **Countable Saturation**):
The intersection `⋂ k : ℕ, X k` of any decreasing sequence `X 0 ⊇ X 1 ⊇ …` of nonempty internal
subsets of `ℝ*` is nonempty! -/
theorem countable_saturation_decreasing {X : ℕ → Set ℝ*}
    (hInt : ∀ k : ℕ, IsInternal (X k))
    (hNe : ∀ k : ℕ, (X k).Nonempty)
    (hDec : ∀ k : ℕ, X (k + 1) ⊆ X k) :
    (⋂ k : ℕ, X k).Nonempty := by
  choose A hA using hInt
  -- Define `J k = {n ∈ ℕ | (∀ i < k, A (i+1) n ⊆ A i n) ∧ (A k n).Nonempty}`
  let J : ℕ → Set ℕ := fun k ↦
    {n : ℕ | (∀ i < k, A (i + 1) n ⊆ A i n) ∧ (A k n).Nonempty}
  have hJ_mem : ∀ k : ℕ, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), n ∈ J k := by
    intro k
    induction k with
    | zero =>
        have h0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (A 0 n).Nonempty :=
          internalSet_nonempty_iff.1 (hA 0 ▸ hNe 0)
        exact h0.mono fun n hn ↦ ⟨fun _ hi ↦ (Nat.not_lt_zero _ hi).elim, hn⟩
    | succ k ih =>
        have hsub : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), A (k + 1) n ⊆ A k n :=
          internalSet_subset_iff.1 (by rw [← hA (k + 1), ← hA k]; exact hDec k)
        have hne_k1 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (A (k + 1) n).Nonempty :=
          internalSet_nonempty_iff.1 (hA (k + 1) ▸ hNe (k + 1))
        refine ((ih.and hsub).and hne_k1).mono fun n ⟨⟨hJk, hsubn⟩, hnen⟩ ↦ ⟨?_, hnen⟩
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
        · exact hJk.1 i hlt
        · exact hsubn
  -- Helper: if `n ∈ J m` and `k ≤ m`, then `A m n ⊆ A k n`.
  have hJ_chain : ∀ {n k m : ℕ}, n ∈ J m → k ≤ m → A m n ⊆ A k n := by
    intro n k m hnm hkm
    induction m with
    | zero =>
        have : k = 0 := by omega
        subst this; exact Set.Subset.rfl
    | succ m ihm =>
        rcases eq_or_lt_of_le hkm with rfl | hlt
        · exact Set.Subset.rfl
        · have hnm' : n ∈ J m :=
            ⟨fun i hi ↦ hnm.1 i (Nat.lt_succ_of_lt hi),
             hnm.2.mono (hnm.1 m (Nat.lt_succ_self m))⟩
          exact (hnm.1 m (Nat.lt_succ_self m)).trans (ihm hnm' (by omega))
  -- Diagonal selection: for `n ∈ J 0`, let `k_n = max {k ≤ n | n ∈ J k}` and pick `s_n ∈ A k_n n`.
  let s : ℕ → ℝ := fun n ↦
    if hn0 : n ∈ J 0 then
      let S : Finset ℕ := (Finset.range (n + 1)).filter (fun k ↦ n ∈ J k)
      have hSne : S.Nonempty := ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.succ_pos n), hn0⟩⟩
      let kn : ℕ := S.max' hSne
      have hkn_mem : n ∈ J kn := (Finset.mem_filter.1 (Finset.max'_mem S hSne)).2
      hkn_mem.2.some
    else 0
  refine ⟨ofSeq s, Set.mem_iInter.2 fun k ↦ ?_⟩
  rw [hA k, ofSeq_mem_internalSet]
  have hk_atTop : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), k ≤ n :=
    Nat.hyperfilter_le_atTop (eventually_ge_atTop k)
  refine (hk_atTop.and (hJ_mem k)).mono fun n ⟨hkn_le, hnJk⟩ ↦ ?_
  have hnJ0 : n ∈ J 0 := ⟨fun _ hi ↦ (Nat.not_lt_zero _ hi).elim,
    hnJk.2.mono (hJ_chain hnJk (Nat.zero_le k))⟩
  let S : Finset ℕ := (Finset.range (n + 1)).filter (fun m ↦ n ∈ J m)
  have hSne : S.Nonempty := ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.succ_pos n), hnJ0⟩⟩
  let kn : ℕ := S.max' hSne
  have hk_in_S : k ∈ S :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hkn_le), hnJk⟩
  have hk_le_kn : k ≤ kn := Finset.le_max' S k hk_in_S
  have hkn_Jk : n ∈ J kn := (Finset.mem_filter.1 (Finset.max'_mem S hSne)).2
  have hsn_mem : s n ∈ A kn n := by
    simpa only [s, hnJ0, ↓reduceDIte] using hkn_Jk.2.some_mem
  exact hJ_chain hkn_Jk hk_le_kn hsn_mem

/-- Goldblatt Corollary 11.10.2(1) (p. 139): Countable family of internal sets with the finite
intersection property has nonempty intersection! -/
theorem countable_saturation_fip {X : ℕ → Set ℝ*}
    (hInt : ∀ n : ℕ, IsInternal (X n))
    (hFIP : ∀ k : ℕ, (⋂ n ≤ k, X n).Nonempty) :
    (⋂ n : ℕ, X n).Nonempty := by
  let Y : ℕ → Set ℝ* := fun k ↦ ⋂ n ∈ Finset.range (k + 1), X n
  have hY_eq : ∀ k : ℕ, Y k = ⋂ n ≤ k, X n := by
    intro k; ext x
    simp only [Y, Set.mem_iInter, Finset.mem_range, Nat.lt_succ_iff]
  have hY_int : ∀ k : ℕ, IsInternal (Y k) :=
    fun k ↦ isInternal_biInter_finset (Finset.range (k + 1)) (fun n _ ↦ hInt n)
  have hY_ne : ∀ k : ℕ, (Y k).Nonempty := fun k ↦ (hY_eq k).symm ▸ hFIP k
  have hY_dec : ∀ k : ℕ, Y (k + 1) ⊆ Y k := by
    intro k x hx
    rw [hY_eq] at hx ⊢
    exact Set.mem_biInter fun n hn ↦ Set.mem_iInter₂.1 hx n (Nat.le_succ_of_le hn)
  obtain ⟨x, hx⟩ := countable_saturation_decreasing hY_int hY_ne hY_dec
  refine ⟨x, Set.mem_iInter.2 fun n ↦ ?_⟩
  have hxn := Set.mem_iInter.1 hx n
  rw [hY_eq n] at hxn
  exact Set.mem_iInter₂.1 hxn n le_rfl

/-- Goldblatt Corollary 11.10.2(2) (p. 139): If an internal set `X` is covered by `⋃ n : ℕ, X n`
with each `X n` internal, then `X ⊆ ⋃ n ≤ k, X n` for some `k ∈ ℕ`. -/
theorem internal_subset_iUnion_implies_finite {X : Set ℝ*} {Xs : ℕ → Set ℝ*}
    (hX : IsInternal X) (hXs : ∀ n : ℕ, IsInternal (Xs n))
    (hcov : X ⊆ ⋃ n : ℕ, Xs n) :
    ∃ k : ℕ, X ⊆ ⋃ n ≤ k, Xs n := by
  by_contra hno
  push Not at hno
  have hFIP : ∀ k : ℕ, (⋂ n ≤ k, (X \ Xs n)).Nonempty := by
    intro k
    obtain ⟨x, hxX, hxnot⟩ := Set.not_subset.1 (hno k)
    refine ⟨x, Set.mem_biInter fun n hn ↦ ⟨hxX, fun hxn ↦ hxnot ?_⟩⟩
    exact Set.mem_biUnion hn hxn
  obtain ⟨x, hx⟩ := countable_saturation_fip (fun n ↦ hX.sdiff (hXs n)) hFIP
  have hx0 := Set.mem_iInter.1 hx 0
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 (hcov hx0.1)
  exact (Set.mem_iInter.1 hx n).2 hxn

/-- Goldblatt Corollary 11.10.2(3) (p. 139): Dual for countable intersections. -/
theorem iInter_subset_internal_implies_finite {X : Set ℝ*} {Xs : ℕ → Set ℝ*}
    (hX : IsInternal X) (hXs : ∀ n : ℕ, IsInternal (Xs n))
    (hsub : (⋂ n : ℕ, Xs n) ⊆ X) :
    ∃ k : ℕ, (⋂ n ≤ k, Xs n) ⊆ X := by
  have hcov : Xᶜ ⊆ ⋃ n : ℕ, (Xs n)ᶜ := by
    intro x hx
    by_contra hnot
    rw [Set.mem_iUnion, not_exists] at hnot
    exact hx (hsub (Set.mem_iInter.2 fun n ↦ Classical.not_not.1 (hnot n)))
  obtain ⟨k, hk⟩ := internal_subset_iUnion_implies_finite hX.compl (fun n ↦ (hXs n).compl) hcov
  refine ⟨k, fun x hx ↦ ?_⟩
  by_contra hxnot
  obtain ⟨n, hnk, hn_mem⟩ := Set.mem_iUnion₂.1 (hk hxnot)
  exact hn_mem (Set.mem_iInter₂.1 hx n hnk)

/-- Goldblatt Corollary 11.10.2(4) (p. 139, crucial for Loeb Measure in Chapter 16!):
If `⋃ n : ℕ, Xs n` is internal (where each `Xs n` is internal), then it equals `⋃ n ≤ k, Xs n`
for some `k ∈ ℕ`! -/
theorem isInternal_iUnion_implies_finite {Xs : ℕ → Set ℝ*}
    (hXs : ∀ n : ℕ, IsInternal (Xs n)) (hU : IsInternal (⋃ n : ℕ, Xs n)) :
    ∃ k : ℕ, (⋃ n : ℕ, Xs n) = ⋃ n ≤ k, Xs n := by
  obtain ⟨k, hk⟩ := internal_subset_iUnion_implies_finite hU hXs Set.Subset.rfl
  exact ⟨k, Set.Subset.antisymm hk (Set.iUnion₂_subset fun n _ ↦ Set.subset_iUnion Xs n)⟩

/-- Goldblatt Corollary 11.10.2(5) (p. 139): If `⋂ n : ℕ, Xs n` is internal, it equals a finite
sub-intersection. -/
theorem isInternal_iInter_implies_finite {Xs : ℕ → Set ℝ*}
    (hXs : ∀ n : ℕ, IsInternal (Xs n)) (hI : IsInternal (⋂ n : ℕ, Xs n)) :
    ∃ k : ℕ, (⋂ n : ℕ, Xs n) = ⋂ n ≤ k, Xs n := by
  obtain ⟨k, hk⟩ := iInter_subset_internal_implies_finite hI hXs Set.Subset.rfl
  exact ⟨k, Set.Subset.antisymm (Set.subset_iInter₂ fun n _ ↦ Set.iInter_subset Xs n) hk⟩

/-- Goldblatt Exercise 11.10.3 (p. 140): The union of a strictly increasing sequence of internal
sets is external, and the intersection of a strictly decreasing sequence of internal sets is
external! -/
theorem isExternal_iUnion_of_strictMono {Xs : ℕ → Set ℝ*}
    (hXs : ∀ n : ℕ, IsInternal (Xs n)) (hStrict : StrictMono Xs) :
    IsExternal (⋃ n : ℕ, Xs n) := by
  intro hInt
  obtain ⟨k, hk⟩ := isInternal_iUnion_implies_finite hXs hInt
  have hsub : Xs (k + 1) ⊆ Xs k := by
    intro x hx
    have hmem : x ∈ ⋃ n ≤ k, Xs n := hk ▸ Set.mem_iUnion.2 ⟨k + 1, hx⟩
    obtain ⟨n, hnk, hxn⟩ := Set.mem_iUnion₂.1 hmem
    exact (hStrict.monotone hnk) hxn
  exact (hStrict (Nat.lt_succ_self k)).2 hsub

theorem isExternal_iInter_of_strictAnti {Xs : ℕ → Set ℝ*}
    (hXs : ∀ n : ℕ, IsInternal (Xs n)) (hStrict : StrictAnti Xs) :
    IsExternal (⋂ n : ℕ, Xs n) := by
  intro hInt
  obtain ⟨k, hk⟩ := isInternal_iInter_implies_finite hXs hInt
  have hsub : Xs k ⊆ Xs (k + 1) := by
    intro x hx
    have hmem : x ∈ ⋂ n ≤ k, Xs n := Set.mem_biInter fun n hnk ↦ (hStrict.antitone hnk) hx
    exact Set.mem_iInter.1 (hk.symm ▸ hmem) (k + 1)
  exact (hStrict (Nat.lt_succ_self k)).2 hsub

/-- Goldblatt §11.11 & Exercise 11.11.1 (p. 140): Countable saturation directly yields positive
infinitesimals, positive unlimited hyperreals, and negative unlimited hyperreals! -/
theorem exists_posInfinitesimal_via_saturation : ∃ ε : ℝ*, IsPosInfinitesimal ε := by
  let b : ℕ → ℝ := fun n ↦ 1 / ((n + 1 : ℕ) : ℝ)
  let X : ℕ → Set ℝ* := fun n ↦ Set.Ioo 0 (b n : ℝ*)
  have hInt : ∀ n, IsInternal (X n) := fun _ ↦ isInternal_Ioo _ _
  have hNe : ∀ n, (X n).Nonempty := fun n ↦ by
    let m : ℝ := 1 / ((2 * (n + 1) : ℕ) : ℝ)
    have hm0 : 0 < m := by positivity
    have hmb : m < b n := one_div_lt_one_div_of_lt (by positivity) (by push_cast; linarith)
    exact ⟨(m : ℝ*), Hyperreal.coe_pos.2 hm0, Hyperreal.coe_lt_coe.2 hmb⟩
  have hDec : ∀ n, X (n + 1) ⊆ X n := fun n x ⟨hx0, hxn⟩ ↦
    ⟨hx0, hxn.trans (Hyperreal.coe_lt_coe.2 (one_div_lt_one_div_of_lt (by positivity) (by push_cast; linarith)))⟩
  obtain ⟨ε, hε⟩ := countable_saturation_decreasing hInt hNe hDec
  refine ⟨ε, (Set.mem_iInter.1 hε 0).1, fun r hr ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
  exact (Set.mem_iInter.1 hε n).2.trans (Hyperreal.coe_lt_coe.2 (by dsimp [b]; push_cast; exact hn))

theorem exists_pos_and_neg_unlimited_via_saturation :
    (∃ H : ℝ*, IsPosUnlimited H) ∧ (∃ K : ℝ*, IsNegUnlimited K) := by
  have hpos : ∃ H : ℝ*, IsPosUnlimited H := by
    let X : ℕ → Set ℝ* := fun n ↦ Set.Ioi (n : ℝ*)
    obtain ⟨H, hH⟩ := countable_saturation_decreasing
      (fun _ ↦ isInternal_Ioi _)
      (fun n ↦ ⟨((n + 1 : ℕ) : ℝ*), show (n : ℝ*) < ((n + 1 : ℕ) : ℝ*) by exact_mod_cast Nat.lt_succ_self n⟩)
      (fun n x hx ↦ (show (n : ℝ*) < ((n + 1 : ℕ) : ℝ*) by exact_mod_cast Nat.lt_succ_self n).trans hx)
    refine ⟨H, fun r ↦ ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_gt r
    exact (Hyperreal.coe_lt_coe.2 hn).trans (by simpa using Set.mem_iInter.1 hH n)
  obtain ⟨H, hH⟩ := hpos
  refine ⟨⟨H, hH⟩, ⟨-H, fun r ↦ ?_⟩⟩
  have hs := hH (-r)
  rw [Hyperreal.coe_neg] at hs
  linarith

/-- Goldblatt §11.11 (p. 140): Every sequence `(e_n : n ∈ ℕ)` of infinitesimals has an
infinitesimal upper bound! -/
theorem exists_infinitesimal_upper_bound (e : ℕ → ℝ*) (he : ∀ n : ℕ, IsInfinitesimal (e n)) :
    ∃ c : ℝ*, IsInfinitesimal c ∧ ∀ n : ℕ, e n ≤ c := by
  let b : ℕ → ℝ := fun n ↦ 1 / ((n + 1 : ℕ) : ℝ)
  let X : ℕ → Set ℝ* := fun n ↦ Set.Icc (|e n|) (b n : ℝ*)
  have hInt : ∀ n : ℕ, IsInternal (X n) := fun _ ↦ isInternal_Icc _ _
  have hFIP : ∀ k : ℕ, (⋂ n ≤ k, X n).Nonempty := by
    intro k
    let S : Finset ℝ* := (Finset.range (k + 1)).image (fun n ↦ |e n|)
    have hSne : S.Nonempty := ⟨|e 0|, Finset.mem_image.2 ⟨0, Finset.mem_range.2 (Nat.succ_pos k), rfl⟩⟩
    let m : ℝ* := S.max' hSne
    obtain ⟨j, _, hmj⟩ := Finset.mem_image.1 (Finset.max'_mem S hSne)
    have hm_eq : m = |e j| := hmj.symm
    have hm_inf : IsInfinitesimal m := hm_eq ▸ (he j).abs
    have hm_nn : 0 ≤ m := hm_eq ▸ abs_nonneg (e j)
    refine ⟨m, Set.mem_biInter fun n hnk ↦ ⟨?_, ?_⟩⟩
    · exact Finset.le_max' S |e n|
        (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (Nat.lt_succ_of_le hnk), rfl⟩)
    · have hm_lt := hm_inf (b n) (by dsimp [b]; positivity)
      rw [abs_of_nonneg hm_nn] at hm_lt
      exact hm_lt.le
  obtain ⟨c, hc⟩ := countable_saturation_fip hInt hFIP
  have hc0 : 0 ≤ c := (abs_nonneg (e 0)).trans (Set.mem_iInter.1 hc 0).1
  refine ⟨c, isInfinitesimal_iff_nat.2 fun n hn ↦ ?_, fun n ↦ (le_abs_self (e n)).trans (Set.mem_iInter.1 hc n).1⟩
  rcases n with _ | m
  · omega
  · rw [abs_of_nonneg hc0]
    have hle : c ≤ (b (m + 1) : ℝ*) := (Set.mem_iInter.1 hc (m + 1)).2
    have hlt_real : b (m + 1) < ((m + 1 : ℕ) : ℝ)⁻¹ := by
      dsimp [b]
      rw [one_div]
      exact inv_strictAnti₀ (by positivity) (by push_cast; linarith)
    have hlt : (b (m + 1) : ℝ*) < (((m + 1 : ℕ) : ℝ*))⁻¹ := by
      rw [← coe_natCast_hyperreal, ← Hyperreal.coe_inv]
      exact Hyperreal.coe_lt_coe.2 hlt_real
    exact hle.trans_lt hlt

/-- Goldblatt §11.11 (p. 141): Every sequence `(s_n : n ∈ ℕ)` of unlimited hypernaturals has an
unlimited hypernatural lower bound! -/
theorem exists_unlimitedNat_lower_bound (s : ℕ → ℕ*) (hs : ∀ n : ℕ, IsUnlimitedNat (s n)) :
    ∃ M : ℕ*, IsUnlimitedNat M ∧ ∀ n : ℕ, M ≤ s n := by
  let X : ℕ → Set ℝ* := fun n ↦
    Set.Icc ((n + 1 : ℕ) : ℝ*) (Hypernat.toHyperreal (s n)) ∩ starSet (Set.range (Nat.cast : ℕ → ℝ))
  have hInt : ∀ n : ℕ, IsInternal (X n) :=
    fun _ ↦ (isInternal_Icc _ _).inter (isInternal_starSet _)
  have hFIP : ∀ k : ℕ, (⋂ n ≤ k, X n).Nonempty := by
    intro k
    let S : Finset ℕ* := (Finset.range (k + 1)).image s
    have hSne : S.Nonempty := ⟨s 0, Finset.mem_image.2 ⟨0, Finset.mem_range.2 (Nat.succ_pos k), rfl⟩⟩
    let M₀ : ℕ* := S.min' hSne
    obtain ⟨j, _, hMj⟩ := Finset.mem_image.1 (Finset.min'_mem S hSne)
    have hM₀_eq : M₀ = s j := hMj.symm
    have hM₀_unl : IsUnlimitedNat M₀ := hM₀_eq ▸ hs j
    refine ⟨Hypernat.toHyperreal M₀, Set.mem_biInter fun n hnk ↦ ⟨⟨?_, ?_⟩, ?_⟩⟩
    · rw [← Hypernat.toHyperreal_natCast (n + 1)]
      exact Hypernat.toHyperreal_le_iff.2 (hM₀_unl (n + 1)).le
    · refine Hypernat.toHyperreal_le_iff.2 ?_
      exact Finset.min'_le S (s n)
        (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (Nat.lt_succ_of_le hnk), rfl⟩)
    · rw [← range_hypernat_toHyperreal]
      exact ⟨M₀, rfl⟩
  obtain ⟨x, hx⟩ := countable_saturation_fip hInt hFIP
  have hx_nat : x ∈ starSet (Set.range (Nat.cast : ℕ → ℝ)) := (Set.mem_iInter.1 hx 0).2
  rw [← range_hypernat_toHyperreal] at hx_nat
  obtain ⟨M, rfl⟩ := hx_nat
  refine ⟨M, fun n ↦ ?_, fun n ↦ Hypernat.toHyperreal_le_iff.1 (Set.mem_iInter.1 hx n).1.2⟩
  have hle : ((n + 1 : ℕ) : ℝ*) ≤ Hypernat.toHyperreal M := (Set.mem_iInter.1 hx n).1.1
  have hlt : Hypernat.toHyperreal (n : ℕ*) < Hypernat.toHyperreal M := by
    rw [Hypernat.toHyperreal_natCast]
    exact (show (n : ℝ*) < ((n + 1 : ℕ) : ℝ*) by exact_mod_cast Nat.lt_succ_self n).trans_le hle
  exact Hypernat.toHyperreal_lt_iff.1 hlt

/-- Goldblatt Exercise 11.11.2 (p. 141): Without appealing to saturation, the infinitesimal upper
bound property and the unlimited hypernatural lower bound property imply each other directly! -/
theorem infinitesimal_ub_iff_unlimitedNat_lb :
    (∀ e : ℕ → ℝ*, (∀ n, IsInfinitesimal (e n)) → ∃ c : ℝ*, IsInfinitesimal c ∧ ∀ n, e n ≤ c) ↔
    (∀ s : ℕ → ℕ*, (∀ n, IsUnlimitedNat (s n)) → ∃ M : ℕ*, IsUnlimitedNat M ∧ ∀ n, M ≤ s n) := by
  constructor
  · intro hInf s hs
    let e : ℕ → ℝ* := fun n ↦ (Hypernat.toHyperreal (s n))⁻¹
    have he : ∀ n, IsInfinitesimal (e n) := fun n ↦ by
      have hunl : IsUnlimited (Hypernat.toHyperreal (s n)) :=
        isUnlimited_iff_pos_or_neg.2 (Or.inl (isUnlimitedNat_iff_isPosUnlimited.1 (hs n)))
      exact hunl.inv_isInfinitesimal
    obtain ⟨c, hc_inf, hce⟩ := hInf e he
    let c' : ℝ* := c + Hyperreal.epsilon
    have hs0_pos : 0 < Hypernat.toHyperreal (s 0) := by
      simpa using (isUnlimitedNat_iff_isPosUnlimited.1 (hs 0)) 0
    have hc'_pos : 0 < c' := by
      have h0 : 0 < e 0 := inv_pos.2 hs0_pos
      linarith [hce 0, Hyperreal.epsilon_pos]
    have hc'_inf : IsInfinitesimal c' := hc_inf.add isInfinitesimal_epsilon
    have hc'_inv_unl : IsPosUnlimited c'⁻¹ := by
      have hunl := (isUnlimited_inv_iff_isInfinitesimal hc'_pos.ne').2 hc'_inf
      rcases isUnlimited_iff_pos_or_neg.1 hunl with hp | hn
      · exact hp
      · exfalso; exact not_lt_of_ge (inv_pos.2 hc'_pos).le (by simpa using hn 0)
    rcases ofSeq_surjective c'⁻¹ with ⟨r, hr⟩
    let M : ℕ* := ((fun i ↦ ⌊r i⌋₊) : ℕ*)
    have hM_le : Hypernat.toHyperreal M ≤ c'⁻¹ := by
      have hr0 : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 0 ≤ r i :=
        ofSeq_le_ofSeq.1 (hr ▸ (inv_pos.2 hc'_pos).le)
      rw [← hr]
      exact ofSeq_le_ofSeq.2 (hr0.mono fun i hi ↦ Nat.floor_le hi)
    have hlt_M1 : c'⁻¹ - 1 < Hypernat.toHyperreal M := by
      rw [← hr]
      exact ofSeq_lt_ofSeq.2 (Eventually.of_forall fun i ↦ sub_lt_iff_lt_add.2 (Nat.lt_floor_add_one (r i)))
    refine ⟨M, isUnlimitedNat_iff_isPosUnlimited.2 fun q ↦ ?_, fun n ↦ ?_⟩
    · have := hc'_inv_unl (q + 1)
      rw [Hyperreal.coe_add, Hyperreal.coe_one] at this
      linarith
    · have hs_pos : 0 < Hypernat.toHyperreal (s n) := by
        simpa using (isUnlimitedNat_iff_isPosUnlimited.1 (hs n)) 0
      have he_lt : e n < c' := (hce n).trans_lt (by dsimp [c']; linarith [Hyperreal.epsilon_pos])
      have hinv_le : c'⁻¹ ≤ Hypernat.toHyperreal (s n) := by
        have := inv_anti₀ (inv_pos.2 hs_pos) he_lt.le
        simpa [e] using this
      exact Hypernat.toHyperreal_le_iff.1 (hM_le.trans hinv_le)
  · intro hNat e he
    let a : ℕ → ℝ* := fun n ↦ |e n| + Hyperreal.epsilon
    have ha_pos : ∀ n, 0 < a n := fun n ↦ add_pos_of_nonneg_of_pos (abs_nonneg _) Hyperreal.epsilon_pos
    have ha_inf : ∀ n, IsInfinitesimal (a n) := fun n ↦ (he n).abs.add isInfinitesimal_epsilon
    choose rSeq hr using fun n ↦ ofSeq_surjective (a n)⁻¹
    let s : ℕ → ℕ* := fun n ↦ ((fun i ↦ ⌊rSeq n i⌋₊) : ℕ*)
    have hs_unl : ∀ n, IsUnlimitedNat (s n) := fun n ↦ by
      have hunl := (isUnlimited_inv_iff_isInfinitesimal (ha_pos n).ne').2 (ha_inf n)
      have hp : IsPosUnlimited (a n)⁻¹ := by
        rcases isUnlimited_iff_pos_or_neg.1 hunl with hp | hn
        · exact hp
        · exfalso; exact not_lt_of_ge (inv_pos.2 (ha_pos n)).le (by simpa using hn 0)
      refine isUnlimitedNat_iff_isPosUnlimited.2 fun q ↦ ?_
      have hfl : (a n)⁻¹ - 1 < Hypernat.toHyperreal (s n) := by
        rw [← hr n]
        exact ofSeq_lt_ofSeq.2 (Eventually.of_forall fun i ↦ sub_lt_iff_lt_add.2 (Nat.lt_floor_add_one (rSeq n i)))
      have hp1 := hp (q + 1)
      rw [Hyperreal.coe_add, Hyperreal.coe_one] at hp1
      linarith
    obtain ⟨M, hM_unl, hMs⟩ := hNat s hs_unl
    have hM_pos : 0 < Hypernat.toHyperreal M := by
      simpa using (isUnlimitedNat_iff_isPosUnlimited.1 hM_unl) 0
    have hM_inf : IsInfinitesimal (Hypernat.toHyperreal M)⁻¹ :=
      (isUnlimited_iff_pos_or_neg.2 (Or.inl (isUnlimitedNat_iff_isPosUnlimited.1 hM_unl))).inv_isInfinitesimal
    refine ⟨(Hypernat.toHyperreal M)⁻¹, hM_inf, fun n ↦ ?_⟩
    have hs_le : Hypernat.toHyperreal (s n) ≤ (a n)⁻¹ := by
      have hr0 : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 0 ≤ rSeq n i :=
        ofSeq_le_ofSeq.1 (hr n ▸ (inv_pos.2 (ha_pos n)).le)
      rw [← hr n]
      exact ofSeq_le_ofSeq.2 (hr0.mono fun i hi ↦ Nat.floor_le hi)
    have hM_le_inv : Hypernat.toHyperreal M ≤ (a n)⁻¹ :=
      (Hypernat.toHyperreal_le_iff.2 (hMs n)).trans hs_le
    have han_le : a n ≤ (Hypernat.toHyperreal M)⁻¹ := by
      have := inv_anti₀ hM_pos hM_le_inv
      simpa using this
    exact (le_abs_self (e n)).trans ((by dsimp [a]; linarith [Hyperreal.epsilon_pos] : |e n| ≤ a n).trans han_le)

/-! ## §11.12 The Size of an Internal Set -/

/-- Goldblatt §11.12 (p. 141): **Every countable internal set is finite!** -/
theorem IsInternal.finite_of_countable {X : Set ℝ*} (hX : IsInternal X) (hCount : X.Countable) :
    X.Finite := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · exact Set.finite_empty
  · obtain ⟨f, rfl⟩ := hCount.exists_eq_range hne
    let Y : ℕ → Set ℝ* := fun k ↦
      Set.range f \ (Finset.range (k + 1)).image f
    have hY_int : ∀ k : ℕ, IsInternal (Y k) := fun k ↦
      hX.sdiff (isInternal_finset _)
    have hY_dec : ∀ k : ℕ, Y (k + 1) ⊆ Y k := by
      intro k x ⟨hx1, hx2⟩
      refine ⟨hx1, fun hx_mem ↦ hx2 ?_⟩
      exact Finset.mem_image.2 <|
        let ⟨i, hi, hfi⟩ := Finset.mem_image.1 hx_mem
        ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 hi)), hfi⟩
    by_cases hall_ne : ∀ k : ℕ, (Y k).Nonempty
    · exfalso
      obtain ⟨x, hx⟩ := countable_saturation_decreasing hY_int hall_ne hY_dec
      obtain ⟨m, rfl⟩ := (Set.mem_iInter.1 hx 0).1
      exact (Set.mem_iInter.1 hx m).2
        (Finset.mem_image.2 ⟨m, Finset.mem_range.2 (Nat.lt_succ_self m), rfl⟩)
    · push Not at hall_ne
      obtain ⟨k, hk⟩ := hall_ne
      rw [Set.sdiff_eq_empty] at hk
      exact (Finset.finite_toSet _).subset hk

/-- Goldblatt §11.12 (p. 141): **Every infinite internal subset of `ℝ*` is uncountable!** -/
theorem IsInternal.not_countable_of_infinite {X : Set ℝ*} (hX : IsInternal X) (hInf : X.Infinite) :
    ¬ X.Countable :=
  fun hCount ↦ hInf (hX.finite_of_countable hCount)

/-- Goldblatt §11.12 (pp. 141–142): For any unlimited `N ∈ ℕ*`, the initial segment `{K ≤ N}` and
the set of unlimited hypernaturals `≤ N` are uncountable! -/
theorem uncountable_Iic_of_isUnlimitedNat {N : ℕ*} (hN : IsUnlimitedNat N) :
    ¬ (Set.Iic N).Countable ∧ ¬ ({K : ℕ* | IsUnlimitedNat K ∧ K ≤ N}).Countable := by
  have hInt : IsInternal (Hypernat.toHyperreal '' Set.Iic N) :=
    isInternal_image_hypernat_iff.2 (isInternalNat_Iic N)
  have hInf_seg : (Set.Iic N).Infinite := by
    refine Set.infinite_of_injective_forall_mem
      (f := (Nat.cast : ℕ → ℕ*))
      (fun m n hmn ↦ by
        have := congrArg Hypernat.toHyperreal hmn
        rw [Hypernat.toHyperreal_natCast, Hypernat.toHyperreal_natCast,
            ← coe_natCast_hyperreal, ← coe_natCast_hyperreal] at this
        exact Nat.cast_injective (Hyperreal.coe_eq_coe.1 this))
      (fun n ↦ (hN n).le)
  have hInf_img : (Hypernat.toHyperreal '' Set.Iic N).Infinite :=
    hInf_seg.image (fun _ _ _ _ h ↦ Hypernat.toHyperreal_injective h)
  have hUnc_seg : ¬ (Set.Iic N).Countable :=
    fun hC ↦ hInt.not_countable_of_infinite hInf_img (hC.image _)
  refine ⟨hUnc_seg, fun hC_unl ↦ hUnc_seg ?_⟩
  have hdecomp : Set.Iic N ⊆ Set.range (Nat.cast : ℕ → ℕ*) ∪ {K : ℕ* | IsUnlimitedNat K ∧ K ≤ N} := by
    intro K hKN
    by_cases hK : IsUnlimitedNat K
    · exact Or.inr ⟨hK, hKN⟩
    · obtain ⟨n, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 hK
      exact Or.inl ⟨n, rfl⟩
  exact ((Set.countable_range _).union hC_unl).mono hdecomp

/-! ## §11.13 Closure of the Shadow of an Internal Set -/

/-- Goldblatt §11.13 (p. 142): `sh(X) = {sh(x) | x ∈ X, x is limited} ⊆ ℝ`. -/
def shadowSet (X : Set ℝ*) : Set ℝ :=
  {r : ℝ | ∃ x ∈ X, IsLimited x ∧ shadow x = r}

/-- Goldblatt Theorem 11.13.1 (p. 142): **If `X ⊆ ℝ*` is internal, then `sh(X)` is closed in `ℝ`!**
Proved via countable saturation (and played a foundational role in Loeb/Lebesgue measure in Ch 16). -/
theorem IsInternal.isClosed_shadowSet {X : Set ℝ*} (hX : IsInternal X) :
    IsClosed (shadowSet X) := by
  rw [← closure_subset_iff_isClosed]
  intro r hr
  rw [Metric.mem_closure_iff] at hr
  let d : ℕ → ℝ := fun n ↦ 1 / ((n + 1 : ℕ) : ℝ)
  let Y : ℕ → Set ℝ* := fun n ↦
    X ∩ Set.Ioo (((r - d n : ℝ) : ℝ*)) (((r + d n : ℝ) : ℝ*))
  have hY_int : ∀ n : ℕ, IsInternal (Y n) := fun _ ↦ hX.inter (isInternal_Ioo _ _)
  have hY_ne : ∀ n : ℕ, (Y n).Nonempty := by
    intro n
    have hpos : 0 < d n := by dsimp [d]; positivity
    obtain ⟨s, hs_sh, hdist⟩ := hr (d n) hpos
    obtain ⟨x, hxX, hx_lim, hshx⟩ := hs_sh
    refine ⟨x, hxX, ?_, ?_⟩
    · have hsr : r - d n < s := by
        rw [Real.dist_eq, abs_lt] at hdist; linarith
      set δ : ℝ := (s - (r - d n)) / 2
      have hδ : 0 < δ := by positivity
      have hcl := infClose_shadow hx_lim δ hδ
      rw [hshx] at hcl
      have h1 : (s : ℝ*) - (δ : ℝ*) < x := by linarith [(abs_lt.1 hcl).1]
      have h2 : ((r - d n : ℝ) : ℝ*) < (s : ℝ*) - (δ : ℝ*) := by
        rw [← Hyperreal.coe_sub, Hyperreal.coe_lt_coe]
        dsimp [δ]; linarith
      exact h2.trans h1
    · have hsr : s < r + d n := by
        rw [Real.dist_eq, abs_lt] at hdist; linarith
      set δ : ℝ := ((r + d n) - s) / 2
      have hδ : 0 < δ := by positivity
      have hcl := infClose_shadow hx_lim δ hδ
      rw [hshx] at hcl
      have h1 : x < (s : ℝ*) + (δ : ℝ*) := by linarith [(abs_lt.1 hcl).2]
      have h2 : (s : ℝ*) + (δ : ℝ*) < ((r + d n : ℝ) : ℝ*) := by
        rw [← Hyperreal.coe_add, Hyperreal.coe_lt_coe]
        dsimp [δ]; linarith
      exact h1.trans h2
  have hY_dec : ∀ n : ℕ, Y (n + 1) ⊆ Y n := by
    intro n x ⟨hxX, hl, hu⟩
    have hlt : d (n + 1) < d n := by
      dsimp [d]
      exact one_div_lt_one_div_of_lt (by positivity) (by push_cast; linarith)
    refine ⟨hxX, ?_, ?_⟩
    · exact (Hyperreal.coe_lt_coe.2 (by linarith)).trans hl
    · exact hu.trans (Hyperreal.coe_lt_coe.2 (by linarith))
  obtain ⟨y, hy⟩ := countable_saturation_decreasing hY_int hY_ne hY_dec
  have hyX : y ∈ X := (Set.mem_iInter.1 hy 0).1
  have hy_close : y ≈ₕ (r : ℝ*) := by
    refine isInfinitesimal_iff_nat.2 fun n hn ↦ ?_
    rcases n with _ | m
    · omega
    · obtain ⟨_, hl, hu⟩ := Set.mem_iInter.1 hy m
      have hd_real : d m = (((m + 1 : ℕ) : ℝ))⁻¹ := one_div _
      rw [abs_lt]
      constructor
      · rw [Hyperreal.coe_sub, hd_real] at hl; linarith
      · rw [Hyperreal.coe_add, hd_real] at hu; linarith
  have hy_lim : IsLimited y := by
    have : y = (r : ℝ*) + (y - (r : ℝ*)) := by ring
    rw [this]
    exact (isLimited_coe r).add hy_close.isLimited
  exact ⟨y, hyX, hy_lim, shadow_eq_of_infClose hy_close⟩

/-- Goldblatt Exercise 11.13.2 (p. 142): Alternative proof that `sh(X)` is closed using the
Internal Set Definition Principle and Overflow (without appealing to countable saturation)! -/
theorem isInternalNat_ball_inter_nonempty {X : Set ℝ*} (hX : IsInternal X) (b : ℝ*) :
    IsInternalNat {N : ℕ* | (1 : ℕ*) ≤ N ∧
      (X ∩ {y : ℝ* | |y - b| < (Hypernat.toHyperreal N)⁻¹}).Nonempty} := by
  rcases hX with ⟨A, rfl⟩
  rcases ofSeq_surjective b with ⟨s, rfl⟩
  have hball : {N : ℕ* | (internalSet A ∩ {y : ℝ* | |y - ofSeq s| < (Hypernat.toHyperreal N)⁻¹}).Nonempty} =
      internalNatSet (fun n ↦ {k : ℕ | ∃ y : ℝ, y ∈ A n ∧ |y - s n| < ((k : ℝ))⁻¹}) := by
    ext N
    induction N using Germ.inductionOn with | _ c =>
    rw [Set.mem_ofPred_eq, coe_mem_internalNatSet]
    constructor
    · rintro ⟨y, hyA, hyb⟩
      rcases ofSeq_surjective y with ⟨t, rfl⟩
      exact ((ofSeq_mem_internalSet.1 hyA).and (ofSeq_lt_ofSeq.1 hyb)).mono
        fun n ⟨h1, h2⟩ ↦ ⟨t n, h1, h2⟩
    · intro hev
      let t : ℕ → ℝ := fun n ↦
        if h : ∃ y : ℝ, y ∈ A n ∧ |y - s n| < ((c n : ℝ))⁻¹ then h.choose else 0
      refine ⟨ofSeq t, ofSeq_mem_internalSet.2 ?_, ofSeq_lt_ofSeq.2 ?_⟩
      · exact hev.mono fun n hn ↦ by
          change ∃ y : ℝ, y ∈ A n ∧ |y - s n| < ((c n : ℝ))⁻¹ at hn
          simpa only [t, hn, ↓reduceDIte] using hn.choose_spec.1
      · exact hev.mono fun n hn ↦ by
          change ∃ y : ℝ, y ∈ A n ∧ |y - s n| < ((c n : ℝ))⁻¹ at hn
          change |t n - s n| < ((c n : ℝ))⁻¹
          simpa only [t, hn, ↓reduceDIte] using hn.choose_spec.2
  change IsInternalNat (Set.Ici 1 ∩
    {N : ℕ* | (internalSet A ∩ {y : ℝ* | |y - ofSeq s| < (Hypernat.toHyperreal N)⁻¹}).Nonempty})
  exact (isInternalNat_Ici 1).inter ⟨_, hball⟩

theorem isClosed_shadowSet_via_overflow {X : Set ℝ*} (hX : IsInternal X) :
    IsClosed (shadowSet X) := by
  rw [← closure_subset_iff_isClosed]
  intro r hr
  rw [Metric.mem_closure_iff] at hr
  let Z : Set ℕ* := {N : ℕ* | (1 : ℕ*) ≤ N ∧
    (X ∩ {y : ℝ* | |y - (r : ℝ*)| < (Hypernat.toHyperreal N)⁻¹}).Nonempty}
  have hZ_int : IsInternalNat Z := isInternalNat_ball_inter_nonempty hX (r : ℝ*)
  have hZ_fin : ∀ n : ℕ, 1 ≤ n → (n : ℕ*) ∈ Z := by
    intro n hn
    refine ⟨by exact_mod_cast hn, ?_⟩
    let δ : ℝ := 1 / (2 * (n : ℝ))
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (by omega)
    have hpos : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨s, ⟨x, hxX, hx_lim, hshx⟩, hdist⟩ := hr δ hpos
    refine ⟨x, hxX, ?_⟩
    have hcl := infClose_shadow hx_lim δ hpos
    rw [hshx] at hcl
    have hsr : |s - r| < δ := by rw [Real.dist_eq, abs_sub_comm] at hdist; exact hdist
    have htri : |x - (r : ℝ*)| ≤ |x - (s : ℝ*)| + |(s : ℝ*) - (r : ℝ*)| := by
      have : x - (r : ℝ*) = (x - (s : ℝ*)) + ((s : ℝ*) - (r : ℝ*)) := by ring
      rw [this]; exact abs_add_le _ _
    have hs_cast : |(s : ℝ*) - (r : ℝ*)| < (δ : ℝ*) := by
      rw [← Hyperreal.coe_sub, ← Hyperreal.coe_abs]
      exact Hyperreal.coe_lt_coe.2 hsr
    have hlt : |x - (s : ℝ*)| + |(s : ℝ*) - (r : ℝ*)| < (δ : ℝ*) + (δ : ℝ*) :=
      add_lt_add hcl hs_cast
    have hsum_real : δ + δ = ((n : ℝ))⁻¹ := by
      dsimp [δ]
      field_simp [hn_pos.ne']
      ring
    have hsum : (δ : ℝ*) + (δ : ℝ*) = (Hypernat.toHyperreal (n : ℕ*))⁻¹ := by
      rw [← Hyperreal.coe_add, hsum_real, Hyperreal.coe_inv, coe_natCast_hyperreal,
          Hypernat.toHyperreal_natCast]
    exact htri.trans_lt (hlt.trans_eq hsum)
  obtain ⟨K, hK_unl, hseg⟩ := overflow_nat hZ_int hZ_fin
  obtain ⟨_, ⟨y, hyX, hyr⟩⟩ := hseg K (hK_unl 1).le le_rfl
  have hK_inf : IsInfinitesimal (Hypernat.toHyperreal K)⁻¹ :=
    (isUnlimited_iff_pos_or_neg.2 (Or.inl (isUnlimitedNat_iff_isPosUnlimited.1 hK_unl))).inv_isInfinitesimal
  have hK_pos : 0 < (Hypernat.toHyperreal K)⁻¹ :=
    inv_pos.2 (by simpa using (isUnlimitedNat_iff_isPosUnlimited.1 hK_unl) 0)
  have hy_close : y ≈ₕ (r : ℝ*) :=
    isInfinitesimal_of_abs_le hK_inf (by rw [abs_of_pos hK_pos]; exact hyr.le)
  have hy_lim : IsLimited y := by
    have : y = (r : ℝ*) + (y - (r : ℝ*)) := by ring
    rw [this]; exact (isLimited_coe r).add hy_close.isLimited
  exact ⟨y, hyX, hy_lim, shadow_eq_of_infClose hy_close⟩

/-! ## §11.14 Interval Topology, Real-Open, S-Open, and Hyper-Open Sets -/

/-- Goldblatt §11.14 (p. 143): `U ⊆ ℝ*` is **interval-open** if every `x ∈ U` lies in some
hyperreal open interval `(a, b) ⊆ U`. -/
def IsIntervalOpen (U : Set ℝ*) : Prop :=
  ∀ x ∈ U, ∃ a b : ℝ*, x ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ U

/-- Goldblatt §11.14 (p. 143): `U ⊆ ℝ*` is **real-open** if every `x ∈ U` lies in `(r - e, r + e) ⊆ U`
for some `r ∈ ℝ*` and positive standard real `e > 0` (equivalently `(x - e', x + e') ⊆ U`). -/
def IsRealOpen (U : Set ℝ*) : Prop :=
  ∀ x ∈ U, ∃ r : ℝ*, ∃ e : ℝ, 0 < e ∧
    x ∈ Set.Ioo (r - (e : ℝ*)) (r + (e : ℝ*)) ∧
    Set.Ioo (r - (e : ℝ*)) (r + (e : ℝ*)) ⊆ U

/-- Goldblatt §11.14 (p. 143): S-neighbourhood `((r - e, r + e)) = {x ∈ ℝ* | halo x ⊆ (r - e, r + e)}`. -/
def sBall (r : ℝ*) (e : ℝ) : Set ℝ* :=
  {x : ℝ* | halo x ⊆ Set.Ioo (r - (e : ℝ*)) (r + (e : ℝ*))}

/-- Goldblatt §11.14 (p. 143): `U ⊆ ℝ*` is **S-open** if it is a union of S-neighbourhoods of
positive standard radius. -/
def IsSOpen (U : Set ℝ*) : Prop :=
  ∀ x ∈ U, ∃ r : ℝ*, ∃ e : ℝ, 0 < e ∧ x ∈ sBall r e ∧ sBall r e ⊆ U

/-- Goldblatt §11.14 (p. 143): An internal set `X = [A_n]` is **hyper-open** if `A_n` is open in `ℝ`
for `𝓕`-almost all `n`. -/
def IsHyperOpen (X : Set ℝ*) : Prop :=
  ∃ A : ℕ → Set ℝ, X = internalSet A ∧ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), IsOpen (A n)

theorem sBall_subset_Ioo (r : ℝ*) (e : ℝ) :
    sBall r e ⊆ Set.Ioo (r - (e : ℝ*)) (r + (e : ℝ*)) :=
  fun x hx ↦ hx (InfClose.refl x)

theorem mem_sBall_self {r : ℝ*} {e : ℝ} (he : 0 < e) : r ∈ sBall r e := by
  intro y hy
  have hlt := hy (e / 2) (half_pos he)
  have hhalf : ((e / 2 : ℝ) : ℝ*) < (e : ℝ*) := Hyperreal.coe_lt_coe.2 (half_lt_self he)
  rw [Set.mem_Ioo]
  rw [abs_lt] at hlt
  exact ⟨by linarith, by linarith⟩

theorem halo_subset_of_mem_sBall {r x : ℝ*} {e : ℝ} (hx : x ∈ sBall r e) :
    halo x ⊆ sBall r e := by
  intro y hxy z hyz
  exact hx (hxy.trans hyz)

/-- Goldblatt Lemma 11.14.1 (p. 143): Every hyper-open set is interval-open (a union of hyperreal
open intervals). -/
theorem IsHyperOpen.isIntervalOpen {X : Set ℝ*} (hX : IsHyperOpen X) : IsIntervalOpen X := by
  rcases hX with ⟨A, rfl, hOpen⟩
  intro x hx
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  have hrA := ofSeq_mem_internalSet.1 hx
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
      ∃ ε : ℝ, 0 < ε ∧ Set.Ioo (r n - ε) (r n + ε) ⊆ A n := by
    refine (hrA.and hOpen).mono fun n ⟨hrn, hOn⟩ ↦ ?_
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hOn (r n) hrn
    refine ⟨ε, hε, fun y hy ↦ hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  let εSeq : ℕ → ℝ := fun n ↦
    if h : ∃ ε : ℝ, 0 < ε ∧ Set.Ioo (r n - ε) (r n + ε) ⊆ A n then h.choose else 1
  let a : ℝ* := ofSeq (fun n ↦ r n - εSeq n)
  let b : ℝ* := ofSeq (fun n ↦ r n + εSeq n)
  refine ⟨a, b, ?_, ?_⟩
  · refine ⟨ofSeq_lt_ofSeq.2 ?_, ofSeq_lt_ofSeq.2 ?_⟩
    · exact hev.mono fun n hn ↦ by
        have hpos : 0 < εSeq n := by simpa only [εSeq, hn, ↓reduceDIte] using hn.choose_spec.1
        linarith
    · exact hev.mono fun n hn ↦ by
        have hpos : 0 < εSeq n := by simpa only [εSeq, hn, ↓reduceDIte] using hn.choose_spec.1
        linarith
  · intro y ⟨hya, hyb⟩
    rcases ofSeq_surjective y with ⟨s, rfl⟩
    have h1 := ofSeq_lt_ofSeq.1 hya
    have h2 := ofSeq_lt_ofSeq.1 hyb
    refine ofSeq_mem_internalSet.2 (((hev.and h1).and h2).mono fun n ⟨⟨hn, hs1⟩, hs2⟩ ↦ ?_)
    have hsub : Set.Ioo (r n - εSeq n) (r n + εSeq n) ⊆ A n := by
      simpa only [εSeq, hn, ↓reduceDIte] using hn.choose_spec.2
    exact hsub ⟨hs1, hs2⟩

/-- Goldblatt Exercise 11.14.2 (p. 144): Hyper-open sets are closed under finite unions. -/
theorem IsHyperOpen.union {X Y : Set ℝ*} (hX : IsHyperOpen X) (hY : IsHyperOpen Y) :
    IsHyperOpen (X ∪ Y) := by
  rcases hX with ⟨A, rfl, hA⟩
  rcases hY with ⟨B, rfl, hB⟩
  exact ⟨fun n ↦ A n ∪ B n, internalSet_union A B,
    (hA.and hB).mono fun n ⟨h1, h2⟩ ↦ h1.union h2⟩

/-- Goldblatt Exercise 11.14.3 (p. 144): For `A = [A_n]`, `B = [interior (A_n)]` is the interior
of `A` in the interval topology, and consequently an internal set is interval-open iff it is
hyper-open! -/
theorem internalSet_interior_eq_sUnion_intervalOpen (A : ℕ → Set ℝ) :
    internalSet (fun n ↦ interior (A n)) =
      ⋃₀ {U : Set ℝ* | IsIntervalOpen U ∧ U ⊆ internalSet A} := by
  ext x
  constructor
  · intro hx
    have hB : IsHyperOpen (internalSet (fun n ↦ interior (A n))) :=
      ⟨_, rfl, Eventually.of_forall fun n ↦ isOpen_interior⟩
    have hsub : internalSet (fun n ↦ interior (A n)) ⊆ internalSet A :=
      internalSet_subset_iff.2 (Eventually.of_forall fun n ↦ interior_subset)
    exact Set.mem_sUnion.2 ⟨_, ⟨hB.isIntervalOpen, hsub⟩, hx⟩
  · rintro ⟨U, ⟨hU_open, hUA⟩, hxU⟩
    obtain ⟨a, b, hxab, habU⟩ := hU_open x hxU
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    rcases ofSeq_surjective a with ⟨sa, rfl⟩
    rcases ofSeq_surjective b with ⟨sb, rfl⟩
    have habA : internalSet (fun n ↦ Set.Ioo (sa n) (sb n)) ⊆ internalSet A := by
      rw [internalSet_Ioo]
      exact habU.trans hUA
    have hev_sub := internalSet_subset_iff.1 habA
    have hr_in : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ Set.Ioo (sa n) (sb n) := by
      rw [← ofSeq_mem_internalSet, internalSet_Ioo]
      exact hxab
    refine ofSeq_mem_internalSet.2 ((hev_sub.and hr_in).mono fun n ⟨h1, h2⟩ ↦ ?_)
    exact mem_interior.2 ⟨Set.Ioo (sa n) (sb n), h1, isOpen_Ioo, h2⟩

theorem isIntervalOpen_iff_isHyperOpen_of_isInternal {X : Set ℝ*} (hX : IsInternal X) :
    IsIntervalOpen X ↔ IsHyperOpen X := by
  constructor
  · intro hIntOpen
    rcases hX with ⟨A, rfl⟩
    have heq : internalSet (fun n ↦ interior (A n)) = internalSet A := by
      rw [internalSet_interior_eq_sUnion_intervalOpen]
      refine Set.Subset.antisymm (Set.sUnion_subset fun U hU ↦ hU.2) ?_
      exact Set.subset_sUnion_of_mem ⟨hIntOpen, Set.Subset.rfl⟩
    have hev := internalSet_eq_iff.1 heq
    exact ⟨A, rfl, hev.mono fun n hn ↦ hn ▸ isOpen_interior⟩
  · exact IsHyperOpen.isIntervalOpen

/-- Goldblatt Theorem 11.14.4 (pp. 144–145): **An internal set `B ⊆ ℝ*` is S-open if and only if
it contains the halo of each of its points!** -/
theorem isSOpen_iff_forall_halo_subset_of_isInternal {B : Set ℝ*} (hB : IsInternal B) :
    IsSOpen B ↔ ∀ r ∈ B, halo r ⊆ B := by
  constructor
  · intro hS r hrB
    obtain ⟨c, e, _, hrc, hcB⟩ := hS r hrB
    exact (halo_subset_of_mem_sBall hrc).trans hcB
  · intro hhalo r hrB
    obtain ⟨e, he, hball⟩ := hB.exists_real_ball_subset_of_halo_subset (hhalo r hrB)
    refine ⟨r, e, he, mem_sBall_self he, ?_⟩
    refine (sBall_subset_Ioo r e).trans ?_
    intro x ⟨h1, h2⟩
    apply hball
    rw [Set.mem_ofPred_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩

end Goldblatt
end
