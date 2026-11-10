import LecturesOnTheHyperreals.Ch05_HyperrealsGreatAndSmall
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Basic

/-!
# Chapter 10: Topology of the Reals

Formalization of Robert Goldblatt, *Lectures on the Hyperreals*, Chapter 10 (pp. 113–124):

* **§10.1 Interior, Closure, Boundary, and Limit Points** (pp. 113–115):
  - Derived set `derivedSet` (`A'`), isolated points `IsIsolatedPt`, and standard decomposition
    `interior A ⊆ A ⊆ closure A = A ∪ derivedSet A` (`interior_subset_self_subset_closure`).
  - **Theorem 10.1.1(1)** (`mem_interior_iff_halo_subset`): `x ∈ interior A ↔ halo (x : ℝ*) ⊆ starSet A`.
  - **Theorem 10.1.1(2)** (`accPt_principal_iff_exists_starSet`, `mem_derivedSet_iff_halo_inter_diff_nonempty`):
    `AccPt x (𝓟 A) ↔ ∃ y ∈ starSet A, y ≠ (x : ℝ*) ∧ y ≈ₕ (x : ℝ*)`.
  - **Theorem 10.1.1(3)** (`mem_closure_iff_halo_inter_nonempty`, `mem_closure_iff_exists_infClose`):
    `x ∈ closure A ↔ (halo (x : ℝ*) ∩ starSet A).Nonempty`.
  - Frontier (`mem_frontier_iff_halo`), isolated points (`isIsolatedPt_iff_halo_inter_eq_singleton`),
    Kuratowski closure axioms (`closure_empty_via_halo`, `subset_closure_via_halo`,
    `closure_union_via_halo`, `closure_closure_via_halo`), and interior duals proved directly via halos.

* **§10.2 Open and Closed Sets, Continuity, and Relative Openness** (pp. 115–116):
  - Nonstandard characterizations of open sets (`isOpen_iff_halo_subset`) and closed sets
    (`isClosed_iff_forall_infClose`, `isClosed_iff_shadow_mem`, `isClosed_iff_derivedSet_subset`).
  - **Theorem 10.2.1(1)–(3)** (pp. 115–116): Complement duality and closure of open/closed sets under
    finite intersections/unions and arbitrary unions/intersections proved directly via halos.
  - **Theorem 10.2.2** (p. 116): `halo (r : ℝ*) = ⋂ {*A | r ∈ A ∧ IsOpen A}`
    (`halo_coe_eq_biInter_starSet_isOpen`).
  - **Exercise 10.2.3** (p. 116): Failure of the finite-intersection proof for countable intersections
    `⋂ n, *(-1/(n+1), 1/(n+1)) = halo 0 ≠ {0} = *(⋂ n, (-1/(n+1), 1/(n+1)))`.
  - Nonstandard microcontinuity (`continuousAt_iff_infClose`, `continuousOn_iff_infClose`,
    `continuous_iff_infClose`), topological characterizations of continuity via open/closed preimages
    proved through halos (`continuous_iff_isOpen_preimage_via_halo`,
    `continuous_iff_isClosed_preimage_via_halo`), and subspace openness (`isRelOpen_iff_halo_inter_subset`).

* **§10.3 Compactness, Robinson's Criterion, and the Heine–Borel Theorem** (pp. 116–119):
  - Near-standardness `IsNearStandardIn` and its shadow reformulation
    (`isNearStandardIn_iff_isLimited_and_shadow_mem`).
  - **Robinson's Compactness Criterion** (`isCompact_iff_robinson`, pp. 117–118):
    `IsCompact A ↔ ∀ y ∈ starSet A, ∃ c ∈ A, y ≈ₕ (c : ℝ*)`, proved directly from open covers and
    countable rational-endpoint intervals without invoking Heine–Borel.
  - Nonstandard proofs that `(0, 1)` is not compact, `[a, b]` and finite sets are compact, and compact
    sets are bounded and closed (pp. 117–118).
  - **Theorem 10.3.1 (Heine–Borel Theorem)** (`heine_borel_via_robinson`, p. 119) and
    **Exercise 10.3.2** (`isCompact_of_isClosed_subset_via_robinson`, p. 119).

* **§10.4 Compactness, Extreme Values, and Uniform Continuity** (pp. 119–120):
  - **Theorem 10.4.1** (`isCompact_image_of_continuousOn_via_robinson`, p. 119): Continuous image of a
    compact set is compact.
  - **Extreme Value Theorem** (`extreme_value_on_isCompact_via_robinson`) on arbitrary nonempty compact
    subsets of `ℝ`.
  - **Theorem 10.4.2** (`uniformContinuousOn_of_continuousOn_isCompact_via_robinson`, p. 120):
    Heine–Cantor uniform continuity on compact subsets of `ℝ`.

* **§10.5 Topologies on the Hyperreals `ℝ*`** (pp. 120–122):
  - Real-radius neighbourhoods `realRadiusNhds`, real-open sets `IsRealOpen`, Goldblatt's eight
    classes of real-open sets, and failure of finite intersections (`exists_isRealOpen_not_isRealOpen_inter`).
  - S-neighbourhoods `sNhds`, shadow/appreciable characterizations, S-open sets `IsSOpen`, Robinson's
    `sTopology`, and **Exercise 10.5.1(i)–(iii)** (p. 121).
  - Interval-open sets `IsIntervalOpen`, `intervalTopology = Preorder.topology ℝ*`, clopenness of
    halos and galaxies, total disconnectedness of `(ℝ*, intervalTopology)`, disconnectedness of
    `(ℝ*, sTopology)`, intersection of open neighbourhoods of `r ∈ ℝ*`, generation of
    `intervalTopology` from `realRadiusNhds`, and **Exercise 10.5.2(i)–(iii)** (p. 122).
-/

noncomputable section

namespace Goldblatt.Ch10

open Filter
open Hyperreal (ofSeq ofSeq_lt_ofSeq ofSeq_le_ofSeq ofSeq_surjective)
open scoped Topology Classical

/-! ## §10.0 Preliminary Lemmas on Halos, Enlarged Sets, and Enlarged Functions -/

/-- Membership in `halo b` is definitionally `b ≈ₕ x`. -/
@[simp]
theorem mem_halo_iff {b x : ℝ*} : x ∈ halo b ↔ b ≈ₕ x := Iff.rfl

/-- Symmetric form of membership in `halo b`: `x ∈ halo b ↔ x ≈ₕ b`. -/
theorem mem_halo_iff_symm {b x : ℝ*} : x ∈ halo b ↔ x ≈ₕ b :=
  ⟨InfClose.symm, InfClose.symm⟩

/-- Every hyperreal belongs to its own halo. -/
@[simp]
theorem self_mem_halo (b : ℝ*) : b ∈ halo b :=
  InfClose.refl b

/-- Infinitely close hyperreals have identical halos (`a ≈ₕ b ↔ halo a = halo b`). -/
theorem halo_eq_of_infClose {a b : ℝ*} (h : a ≈ₕ b) : halo a = halo b := by
  ext x
  exact ⟨fun hax ↦ h.symm.trans hax, fun hbx ↦ h.trans hbx⟩

/-- Enlargement of a singleton `{r} ⊆ ℝ` is the hyperreal singleton `{(r : ℝ*)}`. -/
@[simp]
theorem starSet_singleton (r : ℝ) : starSet ({r} : Set ℝ) = {(r : ℝ*)} := by
  simpa using starSet_eq_image_of_finite (Set.finite_singleton r)

/-- Set enlargement commutes with finite unions indexed by a `Finset`. -/
theorem starSet_biUnion_finset {ι : Type*} (F : Finset ι) (V : ι → Set ℝ) :
    starSet (⋃ i ∈ F, V i) = ⋃ i ∈ F, starSet (V i) := by
  induction F using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
      have h1 : (⋃ i ∈ insert a s, V i) = V a ∪ ⋃ i ∈ s, V i := by ext; simp
      have h2 : (⋃ i ∈ insert a s, starSet (V i)) = starSet (V a) ∪ ⋃ i ∈ s, starSet (V i) := by
        ext; simp
      rw [h1, h2, starSet_union, ih]

/-- Set enlargement commutes with finite intersections indexed by a `Finset`. -/
theorem starSet_biInter_finset {ι : Type*} (F : Finset ι) (V : ι → Set ℝ) :
    starSet (⋂ i ∈ F, V i) = ⋂ i ∈ F, starSet (V i) := by
  induction F using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
      have h1 : (⋂ i ∈ insert a s, V i) = V a ∩ ⋂ i ∈ s, V i := by ext; simp
      have h2 : (⋂ i ∈ insert a s, starSet (V i)) = starSet (V a) ∩ ⋂ i ∈ s, starSet (V i) := by
        ext; simp
      rw [h1, h2, starSet_inter, ih]

/-- Enlargement of a metric open ball in `ℝ` is the corresponding hyperreal open interval. -/
@[simp]
theorem starSet_ball (r ε : ℝ) :
    starSet (Metric.ball r ε) = Set.Ioo ((r - ε : ℝ) : ℝ*) ((r + ε : ℝ) : ℝ*) := by
  rw [Real.ball_eq_Ioo, starSet_Ioo]

/-- Enlargement of a metric closed ball in `ℝ` is the corresponding hyperreal closed interval. -/
@[simp]
theorem starSet_closedBall (r ε : ℝ) :
    starSet (Metric.closedBall r ε) = Set.Icc ((r - ε : ℝ) : ℝ*) ((r + ε : ℝ) : ℝ*) := by
  rw [Real.closedBall_eq_Icc, starSet_Icc]

/-- Enlargement commutes with preimages: `*(f ⁻¹' U) = (*f) ⁻¹' (*U)`. -/
@[simp]
theorem starSet_preimage (f : ℝ → ℝ) (U : Set ℝ) :
    starSet (f ⁻¹' U) = starFun f ⁻¹' starSet U := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  rfl

/-- Enlargement commutes with images: `*(f '' A) = (*f) '' (*A)` (Goldblatt §10.4, p. 119). -/
@[simp]
theorem starSet_image (f : ℝ → ℝ) (A : Set ℝ) :
    starSet (f '' A) = starFun f '' starSet A := by
  ext y
  rcases ofSeq_surjective y with ⟨s, rfl⟩
  constructor
  · intro hy
    rw [ofSeq_mem_starSet] at hy
    let r : ℕ → ℝ := fun n ↦ if h : s n ∈ f '' A then h.choose else 0
    refine ⟨ofSeq r, ?_, ?_⟩
    · rw [ofSeq_mem_starSet]
      refine hy.mono fun n hn ↦ ?_
      change (if h : s n ∈ f '' A then h.choose else 0) ∈ A
      rw [dite_eq_left_of_eq_true (eq_true hn)]
      exact hn.choose_spec.1
    · refine Germ.coe_eq.2 (hy.mono fun n hn ↦ ?_)
      change f (if h : s n ∈ f '' A then h.choose else 0) = s n
      rw [dite_eq_left_of_eq_true (eq_true hn)]
      exact hn.choose_spec.2
  · rintro ⟨x, hx, hxy⟩
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    rw [ofSeq_mem_starSet] at hx ⊢
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f (r n) = s n := Germ.coe_eq.1 hxy
    exact (hx.and hev).mono fun n ⟨hnA, hnf⟩ ↦ ⟨r n, hnA, hnf⟩

/-! ## §10.1 Interior, Closure, Boundary, and Limit Points -/

/-- Goldblatt §10.1 (p. 113): The *derived set* `A'` of `A ⊆ ℝ`, consisting of all limit
(accumulation) points of `A`. -/
def derivedSet (A : Set ℝ) : Set ℝ := {r : ℝ | AccPt r (𝓟 A)}

/-- Goldblatt §10.1 (p. 113): An *isolated point* of `A ⊆ ℝ` is a point of `A` that is not a
limit point of `A`. -/
def IsIsolatedPt (A : Set ℝ) (r : ℝ) : Prop := r ∈ A ∧ ¬ AccPt r (𝓟 A)

/-- Goldblatt §10.1 (p. 113): `r ∈ derivedSet A` iff for every real `ε > 0`, `(r - ε, r + ε)`
intersects `A` in a point other than `r`. -/
theorem mem_derivedSet_iff_Ioo {A : Set ℝ} {r : ℝ} :
    r ∈ derivedSet A ↔ ∀ ε : ℝ, 0 < ε → ∃ x ∈ A, x ≠ r ∧ x ∈ Set.Ioo (r - ε) (r + ε) := by
  change AccPt r (𝓟 A) ↔ _
  rw [accPt_iff_nhds]
  constructor
  · intro h ε hε
    have hmem : Set.Ioo (r - ε) (r + ε) ∈ 𝓝 r := by
      rw [← Real.ball_eq_Ioo]
      exact Metric.ball_mem_nhds r hε
    obtain ⟨x, ⟨hxI, hxA⟩, hxr⟩ := h _ hmem
    exact ⟨x, hxA, hxr, hxI⟩
  · intro h U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨x, hxA, hxr, hxI⟩ := h ε hε
    rw [Real.ball_eq_Ioo] at hball
    exact ⟨x, ⟨hball hxI, hxA⟩, hxr⟩

/-- Standard equivalence `AccPt r (𝓟 A) ↔ r ∈ closure (A \ {r})`. -/
theorem mem_derivedSet_iff_mem_closure_diff {A : Set ℝ} {r : ℝ} :
    r ∈ derivedSet A ↔ r ∈ closure (A \ {r}) := by
  rw [mem_derivedSet_iff_Ioo, Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨x, hxA, hxr, hxI⟩ := h ε hε
    rw [← Real.ball_eq_Ioo, Metric.mem_ball, dist_comm] at hxI
    exact ⟨x, ⟨hxA, hxr⟩, hxI⟩
  · intro h ε hε
    obtain ⟨x, ⟨hxA, hxr⟩, hdist⟩ := h ε hε
    rw [dist_comm, ← Metric.mem_ball, Real.ball_eq_Ioo] at hdist
    exact ⟨x, hxA, hxr, hdist⟩

/-- Goldblatt §10.1 (p. 113): `A° ⊆ A ⊆ Ā = A ∪ A'`. -/
theorem interior_subset_self_subset_closure (A : Set ℝ) :
    interior A ⊆ A ∧ A ⊆ closure A ∧ closure A = A ∪ derivedSet A := by
  refine ⟨interior_subset, subset_closure, ?_⟩
  ext r
  rw [Set.mem_union, mem_derivedSet_iff_mem_closure_diff]
  constructor
  · intro hr
    by_cases hrA : r ∈ A
    · exact Or.inl hrA
    · right
      rw [Metric.mem_closure_iff] at hr ⊢
      intro ε hε
      obtain ⟨x, hxA, hdist⟩ := hr ε hε
      refine ⟨x, ⟨hxA, ?_⟩, hdist⟩
      rintro rfl
      exact hrA hxA
  · rintro (hrA | hr')
    · exact subset_closure hrA
    · exact closure_mono Set.sdiff_subset hr'

/-- **Goldblatt Theorem 10.1.1(1)** (p. 114): `r ∈ ℝ` is an interior point of `A ⊆ ℝ` if and only
if `halo (r : ℝ*) ⊆ starSet A` (every hyperreal infinitely close to `r` belongs to `*A`). -/
theorem mem_interior_iff_halo_subset {A : Set ℝ} {r : ℝ} :
    r ∈ interior A ↔ halo (r : ℝ*) ⊆ starSet A := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  constructor
  · rintro ⟨ε, hε, hball⟩ x hx
    have hlt : |(r : ℝ*) - x| < (ε : ℝ*) := hx ε hε
    have hx_ball : x ∈ starSet (Metric.ball r ε) := by
      rw [starSet_ball, Hyperreal.coe_sub, Hyperreal.coe_add, Set.mem_Ioo]
      rcases abs_lt.1 hlt with ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    exact (starSet_subset_starSet_iff.2 hball) hx_ball
  · intro hhalo
    by_contra hno
    push Not at hno
    have hex : ∀ n : ℕ, ∃ a : ℝ, a ∈ Metric.ball r (((n : ℝ) + 1)⁻¹) ∧ a ∉ A := by
      intro n
      have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      obtain ⟨a, ha_ball, ha_notA⟩ := Set.not_subset.1 (hno (((n : ℝ) + 1)⁻¹) hpos)
      exact ⟨a, ha_ball, ha_notA⟩
    choose a ha using hex
    have hclose : (r : ℝ*) ≈ₕ ofSeq a := by
      refine isInfinitesimal_of_abs_le isInfinitesimal_epsilon ?_
      rw [abs_of_pos Hyperreal.epsilon_pos]
      have hne0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), n ≠ 0 :=
        Filter.hyperfilter_le_cofinite (Set.finite_singleton 0).compl_mem_cofinite
      refine ofSeq_le_ofSeq.2 (hne0.mono fun n hn0 ↦ ?_)
      change |r - a n| ≤ (n : ℝ)⁻¹
      have hdist : |a n - r| < ((n : ℝ) + 1)⁻¹ := by
        simpa [Real.dist_eq] using (ha n).1
      rw [abs_sub_comm]
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
      exact hdist.le.trans (inv_anti₀ hn_pos (by linarith))
    have hmemA : ofSeq a ∈ starSet A := hhalo hclose
    have hnotA : ofSeq a ∈ (starSet A)ᶜ := by
      rw [← starSet_compl, ofSeq_mem_starSet]
      exact Eventually.of_forall fun n ↦ (ha n).2
    exact hnotA hmemA

/-- Pointwise form of **Goldblatt Theorem 10.1.1(1)** (p. 114):
`r ∈ interior A ↔ ∀ x : ℝ*, (r : ℝ*) ≈ₕ x → x ∈ starSet A`. -/
theorem mem_interior_iff_forall_infClose {A : Set ℝ} {r : ℝ} :
    r ∈ interior A ↔ ∀ x : ℝ*, (r : ℝ*) ≈ₕ x → x ∈ starSet A :=
  mem_interior_iff_halo_subset

/-- **Goldblatt Theorem 10.1.1(2)** (p. 114): `r ∈ ℝ` is a limit (accumulation) point of `A ⊆ ℝ`
if and only if there exists `y ∈ starSet A` with `y ≠ (r : ℝ*)` and `y ≈ₕ (r : ℝ*)`. -/
theorem accPt_principal_iff_exists_starSet {A : Set ℝ} {r : ℝ} :
    AccPt r (𝓟 A) ↔ ∃ y ∈ starSet A, y ≠ (r : ℝ*) ∧ y ≈ₕ (r : ℝ*) := by
  change r ∈ derivedSet A ↔ _
  rw [mem_derivedSet_iff_Ioo]
  constructor
  · intro h
    have hex : ∀ n : ℕ, ∃ a : ℝ, a ∈ A ∧ a ≠ r ∧
        a ∈ Set.Ioo (r - ((n : ℝ) + 1)⁻¹) (r + ((n : ℝ) + 1)⁻¹) :=
      fun n ↦ h (((n : ℝ) + 1)⁻¹) (by positivity)
    choose a ha using hex
    refine ⟨ofSeq a, ?_, ?_, ?_⟩
    · exact ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (ha n).1)
    · intro heq
      have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), a n = r := Germ.coe_eq.1 heq
      obtain ⟨n, hn⟩ := hev.exists
      exact (ha n).2.1 hn
    · refine isInfinitesimal_of_abs_le isInfinitesimal_epsilon ?_
      rw [abs_of_pos Hyperreal.epsilon_pos]
      have hne0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), n ≠ 0 :=
        Filter.hyperfilter_le_cofinite (Set.finite_singleton 0).compl_mem_cofinite
      refine ofSeq_le_ofSeq.2 (hne0.mono fun n hn0 ↦ ?_)
      change |a n - r| ≤ (n : ℝ)⁻¹
      have hI := (ha n).2.2
      have hlt : |a n - r| < ((n : ℝ) + 1)⁻¹ :=
        abs_lt.2 ⟨by linarith [hI.1], by linarith [hI.2]⟩
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
      exact hlt.le.trans (inv_anti₀ hn_pos (by linarith))
  · rintro ⟨y, hyA, hy_ne, hy_close⟩ ε hε
    rcases ofSeq_surjective y with ⟨a, rfl⟩
    have haA : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), a n ∈ A := ofSeq_mem_starSet.1 hyA
    have ha_ne : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), a n ≠ r :=
      Ultrafilter.eventually_not.2 (fun h0 ↦ hy_ne (Germ.coe_eq.2 h0))
    have hlt : |ofSeq a - (r : ℝ*)| < (ε : ℝ*) := hy_close ε hε
    have ha_dist : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |a n - r| < ε := ofSeq_lt_ofSeq.1 hlt
    obtain ⟨n, ⟨hnA, hnr⟩, hndist⟩ := ((haA.and ha_ne).and ha_dist).exists
    rcases abs_lt.1 hndist with ⟨h1, h2⟩
    exact ⟨a n, hnA, hnr, ⟨by linarith, by linarith⟩⟩

/-- Halo formulation of **Goldblatt Theorem 10.1.1(2)** (p. 114):
`r ∈ derivedSet A ↔ ((halo (r : ℝ*) ∩ starSet A) \ {(r : ℝ*)}).Nonempty`. -/
theorem mem_derivedSet_iff_halo_inter_diff_nonempty {A : Set ℝ} {r : ℝ} :
    r ∈ derivedSet A ↔ ((halo (r : ℝ*) ∩ starSet A) \ {(r : ℝ*)}).Nonempty := by
  change AccPt r (𝓟 A) ↔ _
  rw [accPt_principal_iff_exists_starSet]
  constructor
  · rintro ⟨y, hyA, hy_ne, hy_close⟩
    exact ⟨y, ⟨hy_close.symm, hyA⟩, hy_ne⟩
  · rintro ⟨y, ⟨hy_halo, hyA⟩, hy_ne⟩
    exact ⟨y, hyA, hy_ne, hy_halo.symm⟩

/-- Closure-of-punctured-set form of **Goldblatt Theorem 10.1.1(2)** (p. 114):
`r ∈ closure (A \ {r}) ↔ ∃ y ∈ starSet A, y ≠ (r : ℝ*) ∧ y ≈ₕ (r : ℝ*)`. -/
theorem mem_closure_diff_singleton_iff_exists_starSet {A : Set ℝ} {r : ℝ} :
    r ∈ closure (A \ {r}) ↔ ∃ y ∈ starSet A, y ≠ (r : ℝ*) ∧ y ≈ₕ (r : ℝ*) := by
  rw [← mem_derivedSet_iff_mem_closure_diff]
  exact accPt_principal_iff_exists_starSet

/-- **Goldblatt Theorem 10.1.1(3)** (pp. 114–115): `r ∈ closure A` if and only if
`(halo (r : ℝ*) ∩ starSet A).Nonempty` (following Goldblatt's decomposition `Ā = A ∪ A'`). -/
theorem mem_closure_iff_halo_inter_nonempty {A : Set ℝ} {r : ℝ} :
    r ∈ closure A ↔ (halo (r : ℝ*) ∩ starSet A).Nonempty := by
  rw [(interior_subset_self_subset_closure A).2.2, Set.mem_union,
      mem_derivedSet_iff_halo_inter_diff_nonempty]
  constructor
  · rintro (hrA | ⟨y, hy, _⟩)
    · exact ⟨(r : ℝ*), self_mem_halo _, coe_mem_starSet.2 hrA⟩
    · exact ⟨y, hy⟩
  · rintro ⟨y, hy_halo, hyA⟩
    by_cases hyr : y = (r : ℝ*)
    · subst hyr
      exact Or.inl (coe_mem_starSet.1 hyA)
    · exact Or.inr ⟨y, ⟨hy_halo, hyA⟩, hyr⟩

/-- Existential form of **Goldblatt Theorem 10.1.1(3)** (p. 114):
`r ∈ closure A ↔ ∃ y ∈ starSet A, y ≈ₕ (r : ℝ*)`. -/
theorem mem_closure_iff_exists_infClose {A : Set ℝ} {r : ℝ} :
    r ∈ closure A ↔ ∃ y ∈ starSet A, y ≈ₕ (r : ℝ*) := by
  rw [mem_closure_iff_halo_inter_nonempty]
  constructor
  · rintro ⟨y, hy_halo, hyA⟩
    exact ⟨y, hyA, hy_halo.symm⟩
  · rintro ⟨y, hyA, hy_close⟩
    exact ⟨y, hy_close.symm, hyA⟩

/-- Nonstandard characterization of the frontier (boundary) of `A ⊆ ℝ`: `r ∈ frontier A` iff
`halo (r : ℝ*)` meets both `*A` and `(*A)ᶜ`. -/
theorem mem_frontier_iff_halo {A : Set ℝ} {r : ℝ} :
    r ∈ frontier A ↔
      (halo (r : ℝ*) ∩ starSet A).Nonempty ∧ (halo (r : ℝ*) ∩ (starSet A)ᶜ).Nonempty := by
  rw [frontier, Set.mem_sdiff, mem_closure_iff_halo_inter_nonempty, mem_interior_iff_halo_subset]
  refine and_congr_right fun _ ↦ ?_
  rw [Set.not_subset]
  exact ⟨fun ⟨y, hy1, hy2⟩ ↦ ⟨y, hy1, hy2⟩, fun ⟨y, hy1, hy2⟩ ↦ ⟨y, hy1, hy2⟩⟩

/-- Nonstandard characterization of isolated points: `r` is an isolated point of `A ⊆ ℝ` iff
`halo (r : ℝ*) ∩ starSet A = {(r : ℝ*)}`. -/
theorem isIsolatedPt_iff_halo_inter_eq_singleton {A : Set ℝ} {r : ℝ} :
    IsIsolatedPt A r ↔ halo (r : ℝ*) ∩ starSet A = {(r : ℝ*)} := by
  unfold IsIsolatedPt
  rw [accPt_principal_iff_exists_starSet]
  constructor
  · rintro ⟨hrA, hno⟩
    ext y
    simp only [Set.mem_inter_iff, mem_halo_iff_symm, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy_close, hyA⟩
      by_contra hy_ne
      exact hno ⟨y, hyA, hy_ne, hy_close⟩
    · rintro rfl
      exact ⟨InfClose.refl _, coe_mem_starSet.2 hrA⟩
  · intro heq
    have hr_mem : (r : ℝ*) ∈ halo (r : ℝ*) ∩ starSet A := by
      rw [heq]
      exact Set.mem_singleton _
    refine ⟨coe_mem_starSet.1 hr_mem.2, ?_⟩
    rintro ⟨y, hyA, hy_ne, hy_close⟩
    have hy_in : y ∈ ({(r : ℝ*)} : Set ℝ*) := by
      rw [← heq]
      exact ⟨hy_close.symm, hyA⟩
    exact hy_ne hy_in

/-! ### Kuratowski Closure Axioms & Interior Duals Proved Directly via Halos -/

/-- Kuratowski Axiom 1 via halos: `closure ∅ = ∅`. -/
theorem closure_empty_via_halo : closure (∅ : Set ℝ) = ∅ := by
  ext r
  rw [mem_closure_iff_halo_inter_nonempty, starSet_empty, Set.inter_empty]
  simp

/-- Kuratowski Axiom 2 via halos: `A ⊆ closure A`. -/
theorem subset_closure_via_halo (A : Set ℝ) : A ⊆ closure A := by
  intro r hr
  rw [mem_closure_iff_halo_inter_nonempty]
  exact ⟨(r : ℝ*), self_mem_halo _, coe_mem_starSet.2 hr⟩

/-- Kuratowski Axiom 3 via halos: `closure (A ∪ B) = closure A ∪ closure B`. -/
theorem closure_union_via_halo (A B : Set ℝ) : closure (A ∪ B) = closure A ∪ closure B := by
  ext r
  simp only [Set.mem_union, mem_closure_iff_halo_inter_nonempty, starSet_union,
    Set.inter_union_distrib_left, Set.union_nonempty]

/-- Kuratowski Axiom 4 (idempotence) proved genuinely via halos and infinitesimals:
if `x ∈ *(closure A)` with `x ≈ₕ r`, transfer at infinitesimal radius `ε = Hyperreal.epsilon`
produces `y ∈ *A` with `|x - y| < ε`, so `y ≈ₕ x ≈ₕ r` and hence `r ∈ closure A`. -/
theorem closure_closure_via_halo (A : Set ℝ) : closure (closure A) = closure A := by
  apply Set.Subset.antisymm _ (subset_closure_via_halo (closure A))
  intro r hr
  obtain ⟨x, hx_cl, hxr⟩ := mem_closure_iff_exists_infClose.1 hr
  rcases ofSeq_surjective x with ⟨u, rfl⟩
  rw [ofSeq_mem_starSet] at hx_cl
  let v : ℕ → ℝ := fun n ↦
    if h : u n ∈ closure A then
      (Metric.mem_closure_iff.1 h (((n : ℝ) + 1)⁻¹) (by positivity)).choose
    else 0
  have hvA : ofSeq v ∈ starSet A := by
    rw [ofSeq_mem_starSet]
    refine hx_cl.mono fun n hn ↦ ?_
    change (if h : u n ∈ closure A then _ else 0) ∈ A
    rw [dite_eq_left_of_eq_true (eq_true hn)]
    exact (Metric.mem_closure_iff.1 hn (((n : ℝ) + 1)⁻¹) (by positivity)).choose_spec.1
  have huv : ofSeq v ≈ₕ ofSeq u := by
    refine isInfinitesimal_of_abs_le isInfinitesimal_epsilon ?_
    rw [abs_of_pos Hyperreal.epsilon_pos]
    have hne0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), n ≠ 0 :=
      Filter.hyperfilter_le_cofinite (Set.finite_singleton 0).compl_mem_cofinite
    refine ofSeq_le_ofSeq.2 ((hx_cl.and hne0).mono fun n ⟨hn_cl, hn0⟩ ↦ ?_)
    change |v n - u n| ≤ (n : ℝ)⁻¹
    have hv_eq : v n = (Metric.mem_closure_iff.1 hn_cl (((n : ℝ) + 1)⁻¹) (by positivity)).choose :=
      dite_eq_left_of_eq_true (eq_true hn_cl)
    have hdist : dist (u n) (v n) < ((n : ℝ) + 1)⁻¹ := by
      rw [hv_eq]
      exact (Metric.mem_closure_iff.1 hn_cl (((n : ℝ) + 1)⁻¹) (by positivity)).choose_spec.2
    rw [Real.dist_eq, abs_sub_comm] at hdist
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
    exact hdist.le.trans (inv_anti₀ hn_pos (by linarith))
  exact mem_closure_iff_exists_infClose.2 ⟨ofSeq v, hvA, huv.trans hxr⟩

/-- Interior Axiom 1 via halos: `interior Set.univ = Set.univ`. -/
theorem interior_univ_via_halo : interior (Set.univ : Set ℝ) = Set.univ := by
  ext r
  rw [mem_interior_iff_halo_subset, starSet_univ]
  simp

/-- Interior Axiom 2 via halos: `interior A ⊆ A`. -/
theorem interior_subset_via_halo (A : Set ℝ) : interior A ⊆ A := by
  intro r hr
  exact coe_mem_starSet.1 (mem_interior_iff_halo_subset.1 hr (self_mem_halo _))

/-- Interior Axiom 3 via halos: `interior (A ∩ B) = interior A ∩ interior B`. -/
theorem interior_inter_via_halo (A B : Set ℝ) :
    interior (A ∩ B) = interior A ∩ interior B := by
  ext r
  simp only [Set.mem_inter_iff, mem_interior_iff_halo_subset, starSet_inter, Set.subset_inter_iff]

/-- Interior Axiom 4 (idempotence) proved via halos: `interior (interior A) = interior A`. -/
theorem interior_interior_via_halo (A : Set ℝ) :
    interior (interior A) = interior A := by
  have hcompl : ∀ S : Set ℝ, interior S = (closure Sᶜ)ᶜ := by
    intro S
    ext r
    rw [mem_interior_iff_halo_subset, Set.mem_compl_iff, mem_closure_iff_halo_inter_nonempty,
        starSet_compl, Set.not_nonempty_iff_eq_empty, Set.disjoint_compl_right_iff_subset.symm,
        Set.disjoint_iff_inter_eq_empty]
  rw [hcompl (interior A), hcompl A, compl_compl, closure_closure_via_halo]

/-! ## §10.2 Open and Closed Sets, Continuity, and Relative Openness -/

/-- **Goldblatt §10.2** (p. 115): `A ⊆ ℝ` is open if and only if `halo (x : ℝ*) ⊆ starSet A`
for every `x ∈ A`. -/
theorem isOpen_iff_halo_subset {A : Set ℝ} :
    IsOpen A ↔ ∀ x ∈ A, halo (x : ℝ*) ⊆ starSet A := by
  rw [← interior_eq_iff_isOpen]
  constructor
  · intro h x hx
    rw [← h] at hx
    exact mem_interior_iff_halo_subset.1 hx
  · intro h
    apply Set.Subset.antisymm interior_subset
    intro x hx
    exact mem_interior_iff_halo_subset.2 (h x hx)

/-- Pointwise form of `isOpen_iff_halo_subset` (Goldblatt §10.2, p. 115):
`IsOpen A ↔ ∀ r ∈ A, ∀ x : ℝ*, x ≈ₕ (r : ℝ*) → x ∈ starSet A`. -/
theorem isOpen_iff_forall_infClose {A : Set ℝ} :
    IsOpen A ↔ ∀ r ∈ A, ∀ x : ℝ*, x ≈ₕ (r : ℝ*) → x ∈ starSet A := by
  rw [isOpen_iff_halo_subset]
  exact forall₂_congr fun _ _ ↦ forall_congr' fun _ ↦ imp_congr mem_halo_iff_symm Iff.rfl

/-- **Goldblatt §10.2** (p. 115): `A ⊆ ℝ` is closed if and only if every `x ∈ ℝ` infinitely close
to some member of `*A` belongs to `A`. -/
theorem isClosed_iff_forall_infClose {A : Set ℝ} :
    IsClosed A ↔ ∀ x : ℝ, (∃ y ∈ starSet A, y ≈ₕ (x : ℝ*)) → x ∈ A := by
  rw [← closure_eq_iff_isClosed]
  constructor
  · intro h x hx
    rw [← h]
    exact mem_closure_iff_exists_infClose.2 hx
  · intro h
    apply Set.Subset.antisymm _ subset_closure
    intro x hx
    exact h x (mem_closure_iff_exists_infClose.1 hx)

/-- Shadow characterization of closed sets (**Goldblatt §10.2 & §10.3**, pp. 115, 117):
`A ⊆ ℝ` is closed if and only if for every limited `y ∈ starSet A`, `shadow y ∈ A`. -/
theorem isClosed_iff_shadow_mem {A : Set ℝ} :
    IsClosed A ↔ ∀ y ∈ starSet A, IsLimited y → shadow y ∈ A := by
  rw [isClosed_iff_forall_infClose]
  constructor
  · intro h y hy hlim
    exact h (shadow y) ⟨y, hy, infClose_shadow hlim⟩
  · intro h x ⟨y, hy, hyx⟩
    have hlim : IsLimited y := by
      have : y = (x : ℝ*) + (y - (x : ℝ*)) := by ring
      rw [this]
      exact (isLimited_coe x).add hyx.isLimited
    have hsh : shadow y = x := shadow_eq_of_infClose hyx
    rw [← hsh]
    exact h y hy hlim

/-- Goldblatt §10.2 (p. 115): `A ⊆ ℝ` is closed iff `A` contains all its limit points (`A' ⊆ A`). -/
theorem isClosed_iff_derivedSet_subset {A : Set ℝ} :
    IsClosed A ↔ derivedSet A ⊆ A := by
  rw [← closure_eq_iff_isClosed, (interior_subset_self_subset_closure A).2.2]
  exact ⟨fun h x hx ↦ h ▸ Or.inr hx, fun h ↦ Set.union_eq_self_of_subset_right h⟩

/-- **Goldblatt Theorem 10.2.1(1)** (p. 115, including the converse exercise):
`A ⊆ ℝ` is open in `ℝ` if and only if `Aᶜ` is closed in `ℝ`, proved directly via halos and
`*(Aᶜ) = (*A)ᶜ`. -/
theorem isOpen_iff_isClosed_compl_via_halo (A : Set ℝ) :
    IsOpen A ↔ IsClosed Aᶜ := by
  rw [isOpen_iff_forall_infClose, isClosed_iff_forall_infClose]
  constructor
  · intro hopen x ⟨y, hy_compl, hyx⟩ hxA
    have hyA : y ∈ starSet A := hopen x hxA y hyx
    rw [starSet_compl] at hy_compl
    exact hy_compl hyA
  · intro hclosed r hrA x hxr
    by_contra hx_notA
    have hx_compl : x ∈ starSet Aᶜ := by rwa [starSet_compl]
    have hr_compl : r ∈ Aᶜ := hclosed r ⟨x, hx_compl, hxr⟩
    exact hr_compl hrA

/-- Dual form of **Goldblatt Theorem 10.2.1(1)** (p. 115): `IsClosed A ↔ IsOpen Aᶜ` via halos. -/
theorem isClosed_iff_isOpen_compl_via_halo (A : Set ℝ) :
    IsClosed A ↔ IsOpen Aᶜ := by
  rw [isOpen_iff_isClosed_compl_via_halo, compl_compl]

/-- **Goldblatt Theorem 10.2.1(2a)** (p. 116): Binary intersection of open sets is open, proved in
two lines via halos. -/
theorem isOpen_inter_via_halo {A B : Set ℝ} (hA : IsOpen A) (hB : IsOpen B) :
    IsOpen (A ∩ B) := by
  rw [isOpen_iff_halo_subset] at hA hB ⊢
  rintro x ⟨hxA, hxB⟩
  rw [starSet_inter]
  exact Set.subset_inter (hA x hxA) (hB x hxB)

/-- **Goldblatt Theorem 10.2.1(2b)** (p. 116): Finite intersections of open sets are open, proved
directly via halos and `starSet_biInter_finset`. -/
theorem isOpen_biInter_finset_via_halo {ι : Type*} (F : Finset ι) {A : ι → Set ℝ}
    (hA : ∀ i ∈ F, IsOpen (A i)) :
    IsOpen (⋂ i ∈ F, A i) := by
  rw [isOpen_iff_halo_subset]
  intro x hx
  rw [starSet_biInter_finset, Set.subset_iInter₂_iff]
  intro i hi
  exact (isOpen_iff_halo_subset.1 (hA i hi)) x (Set.mem_iInter₂.1 hx i hi)

/-- **Goldblatt Theorem 10.2.1(2c)** (p. 116): Arbitrary `sUnion` of open sets is open, proved in
three lines via halos. -/
theorem isOpen_sUnion_via_halo {S : Set (Set ℝ)} (hS : ∀ A ∈ S, IsOpen A) :
    IsOpen (⋃₀ S) := by
  rw [isOpen_iff_halo_subset]
  rintro x ⟨A, hAS, hxA⟩
  exact ((isOpen_iff_halo_subset.1 (hS A hAS)) x hxA).trans
    (starSet_subset_starSet_iff.2 (Set.subset_sUnion_of_mem hAS))

/-- **Goldblatt Theorem 10.2.1(2d)** (p. 116): Arbitrary indexed union of open sets is open, proved
directly via halos. -/
theorem isOpen_iUnion_via_halo {ι : Type*} {A : ι → Set ℝ} (hA : ∀ i, IsOpen (A i)) :
    IsOpen (⋃ i, A i) := by
  rw [isOpen_iff_halo_subset]
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  exact ((isOpen_iff_halo_subset.1 (hA i)) x hxi).trans
    (starSet_subset_starSet_iff.2 (Set.subset_iUnion A i))

/-- **Goldblatt Theorem 10.2.1(3a)** (Exercise, p. 116): Binary union of closed sets is closed,
proved directly via halos. -/
theorem isClosed_union_via_halo {A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B) :
    IsClosed (A ∪ B) := by
  rw [isClosed_iff_forall_infClose] at hA hB ⊢
  rintro x ⟨y, hy, hyx⟩
  rw [starSet_union] at hy
  exact hy.elim (fun hyA ↦ Or.inl (hA x ⟨y, hyA, hyx⟩))
    (fun hyB ↦ Or.inr (hB x ⟨y, hyB, hyx⟩))

/-- **Goldblatt Theorem 10.2.1(3b)** (Exercise, p. 116): Finite unions of closed sets are closed,
proved directly via halos. -/
theorem isClosed_biUnion_finset_via_halo {ι : Type*} (F : Finset ι) {A : ι → Set ℝ}
    (hA : ∀ i ∈ F, IsClosed (A i)) :
    IsClosed (⋃ i ∈ F, A i) := by
  rw [isClosed_iff_forall_infClose]
  rintro x ⟨y, hy, hyx⟩
  rw [starSet_biUnion_finset, Set.mem_iUnion₂] at hy
  rcases hy with ⟨i, hi, hyi⟩
  exact Set.mem_biUnion hi ((isClosed_iff_forall_infClose.1 (hA i hi)) x ⟨y, hyi, hyx⟩)

/-- **Goldblatt Theorem 10.2.1(3c)** (Exercise, p. 116): Arbitrary `sInter` of closed sets is
closed, proved directly via halos. -/
theorem isClosed_sInter_via_halo {S : Set (Set ℝ)} (hS : ∀ A ∈ S, IsClosed A) :
    IsClosed (⋂₀ S) := by
  rw [isClosed_iff_forall_infClose]
  rintro x ⟨y, hy, hyx⟩ A hAS
  have hyA : y ∈ starSet A :=
    (starSet_subset_starSet_iff.2 (Set.sInter_subset_of_mem hAS)) hy
  exact (isClosed_iff_forall_infClose.1 (hS A hAS)) x ⟨y, hyA, hyx⟩

/-- **Goldblatt Theorem 10.2.1(3d)** (Exercise, p. 116): Arbitrary indexed intersection of closed
sets is closed, proved directly via halos. -/
theorem isClosed_iInter_via_halo {ι : Type*} {A : ι → Set ℝ} (hA : ∀ i, IsClosed (A i)) :
    IsClosed (⋂ i, A i) := by
  rw [isClosed_iff_forall_infClose]
  rintro x ⟨y, hy, hyx⟩
  rw [Set.mem_iInter]
  intro i
  have hyi : y ∈ starSet (A i) :=
    (starSet_subset_starSet_iff.2 (Set.iInter_subset A i)) hy
  exact (isClosed_iff_forall_infClose.1 (hA i)) x ⟨y, hyi, hyx⟩

/-- **Goldblatt Theorem 10.2.2** (p. 116): For any real number `r`,
`hal(r) = ⋂ {*A | r ∈ A and A is open}`. -/
theorem halo_coe_eq_biInter_starSet_isOpen (r : ℝ) :
    halo (r : ℝ*) = ⋂ (A : Set ℝ) (_ : r ∈ A) (_ : IsOpen A), starSet A := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_iInter]
    intro A
    rw [Set.mem_iInter]
    intro hrA
    rw [Set.mem_iInter]
    intro hA
    exact (isOpen_iff_halo_subset.1 hA) r hrA hx
  · intro x hx
    by_contra hnot
    change ¬ IsInfinitesimal ((r : ℝ*) - x) at hnot
    unfold IsInfinitesimal at hnot
    push Not at hnot
    obtain ⟨ε, hε, hge⟩ := hnot
    let A : Set ℝ := Set.Ioo (r - ε) (r + ε)
    have hrA : r ∈ A := ⟨by linarith, by linarith⟩
    have hA_open : IsOpen A := isOpen_Ioo
    have hxA : x ∈ starSet A := by
      have h1 := Set.mem_iInter.1 hx A
      have h2 := Set.mem_iInter.1 h1 hrA
      exact Set.mem_iInter.1 h2 hA_open
    rw [starSet_Ioo, Hyperreal.coe_sub, Hyperreal.coe_add, Set.mem_Ioo] at hxA
    have hlt : |(r : ℝ*) - x| < (ε : ℝ*) := abs_lt.2 ⟨by linarith [hxA.2], by linarith [hxA.1]⟩
    exact lt_irrefl _ (hlt.trans_le hge)

/-- `sInter` formulation of **Goldblatt Theorem 10.2.2** (p. 116). -/
theorem halo_coe_eq_sInter_starSet_isOpen (r : ℝ) :
    halo (r : ℝ*) = ⋂₀ {S : Set ℝ* | ∃ A : Set ℝ, r ∈ A ∧ IsOpen A ∧ S = starSet A} := by
  rw [halo_coe_eq_biInter_starSet_isOpen]
  ext x
  simp only [Set.mem_iInter, Set.mem_sInter]
  constructor
  · rintro h S ⟨A, hrA, hAo, rfl⟩
    exact h A hrA hAo
  · intro h A hrA hAo
    exact h (starSet A) ⟨A, hrA, hAo, rfl⟩

/-! ### Exercise 10.2.3: Countable Intersections of Open Sets vs. Enlargement -/

/-- **Goldblatt Exercise 10.2.3(a)** (p. 116): For `A_n = (-1/(n+1), 1/(n+1))`, the countable
intersection of the enlargements `*A_n` equals `halo 0`. -/
theorem iInter_starSet_symm_Ioo_eq_halo_zero :
    (⋂ n : ℕ, starSet (Set.Ioo (-(((n : ℝ) + 1)⁻¹)) (((n : ℝ) + 1)⁻¹))) = halo 0 := by
  ext x
  rw [Set.mem_iInter, halo_zero]
  change (∀ n : ℕ, x ∈ starSet (Set.Ioo (-(((n : ℝ) + 1)⁻¹)) (((n : ℝ) + 1)⁻¹))) ↔
    IsInfinitesimal x
  rw [isInfinitesimal_iff_nat]
  constructor
  · intro hx n hn
    cases n with
    | zero => exact absurd hn (lt_irrefl 0)
    | succ k =>
        have hxk := hx k
        rw [starSet_Ioo, Set.mem_Ioo] at hxk
        have hcast : (((k + 1 : ℕ) : ℝ)⁻¹ : ℝ) = ((k : ℝ) + 1)⁻¹ := by push_cast; rfl
        rw [hcast]
        rw [Hyperreal.coe_neg] at hxk
        exact abs_lt.2 hxk
  · intro hx k
    have hk1 : 0 < k + 1 := Nat.succ_pos k
    have hlt := hx (k + 1) hk1
    have hcast : (((k + 1 : ℕ) : ℝ)⁻¹ : ℝ) = ((k : ℝ) + 1)⁻¹ := by push_cast; rfl
    rw [hcast] at hlt
    rw [starSet_Ioo, Hyperreal.coe_neg, Set.mem_Ioo]
    exact abs_lt.1 hlt

/-- **Goldblatt Exercise 10.2.3(b)** (p. 116): Meanwhile, the enlargement of the countable
intersection `*(⋂ n, (-1/(n+1), 1/(n+1)))` is just `{0}`. -/
theorem starSet_iInter_symm_Ioo_eq_singleton_zero :
    starSet (⋂ n : ℕ, Set.Ioo (-(((n : ℝ) + 1)⁻¹)) (((n : ℝ) + 1)⁻¹)) = {(0 : ℝ*)} := by
  have hiInter : (⋂ n : ℕ, Set.Ioo (-(((n : ℝ) + 1)⁻¹)) (((n : ℝ) + 1)⁻¹)) = {(0 : ℝ)} := by
    ext r
    simp only [Set.mem_iInter, Set.mem_Ioo, Set.mem_singleton_iff]
    constructor
    · intro hr
      by_contra hne
      have hpos : 0 < |r| := abs_pos.2 hne
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      have hrn := hr n
      have habs : |r| < ((n : ℝ) + 1)⁻¹ := abs_lt.2 hrn
      have hone_div : 1 / ((n : ℝ) + 1) = ((n : ℝ) + 1)⁻¹ := one_div _
      linarith
    · rintro rfl n
      have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      exact ⟨by linarith, this⟩
  rw [hiInter, starSet_singleton, Hyperreal.coe_zero]

/-- **Goldblatt Exercise 10.2.3(c)** (p. 116): Explain why the proof of Theorem 10.2.1(2) fails for
infinite intersections: `⋂ n, *A_n = halo 0 ≠ {0} = *(⋂ n, A_n)` and `⋂ n, A_n` is not open. -/
theorem iInter_starSet_ne_starSet_iInter :
    (⋂ n : ℕ, starSet (Set.Ioo (-(((n : ℝ) + 1)⁻¹)) (((n : ℝ) + 1)⁻¹))) ≠
      starSet (⋂ n : ℕ, Set.Ioo (-(((n : ℝ) + 1)⁻¹)) (((n : ℝ) + 1)⁻¹)) ∧
    ¬ IsOpen (⋂ n : ℕ, Set.Ioo (-(((n : ℝ) + 1)⁻¹)) (((n : ℝ) + 1)⁻¹)) := by
  refine ⟨?_, ?_⟩
  · rw [iInter_starSet_symm_Ioo_eq_halo_zero, starSet_iInter_symm_Ioo_eq_singleton_zero]
    intro heq
    have hmem : Hyperreal.epsilon ∈ halo 0 := by
      rw [halo_zero]
      exact isInfinitesimal_epsilon
    rw [heq, Set.mem_singleton_iff] at hmem
    exact Hyperreal.epsilon_ne_zero hmem
  · intro hopen
    have hsub : halo (0 : ℝ*) ⊆ starSet (⋂ n : ℕ, Set.Ioo (-(((n : ℝ) + 1)⁻¹)) (((n : ℝ) + 1)⁻¹)) := by
      refine (isOpen_iff_halo_subset.1 hopen) 0 ?_
      rw [Set.mem_iInter]
      intro n
      have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      exact ⟨by linarith, this⟩
    rw [starSet_iInter_symm_Ioo_eq_singleton_zero] at hsub
    have heps : Hyperreal.epsilon ∈ halo (0 : ℝ*) := by
      rw [halo_zero]
      exact isInfinitesimal_epsilon
    exact Hyperreal.epsilon_ne_zero (hsub heps)

/-! ### Microcontinuity, Topological Continuity Characterization, and Relative Openness -/

/-- Nonstandard characterization of pointwise continuity (`ContinuousAt f r`, Goldblatt Theorem 7.1.1):
`f` is continuous at `r` iff `x ≈ₕ r` implies `*f(x) ≈ₕ f(r)`. -/
theorem continuousAt_iff_infClose {f : ℝ → ℝ} {r : ℝ} :
    ContinuousAt f r ↔ ∀ x : ℝ*, x ≈ₕ (r : ℝ*) → starFun f x ≈ₕ (f r : ℝ*) := by
  rw [Metric.continuousAt_iff]
  constructor
  · intro hf x hxr ε hε
    obtain ⟨δ, hδ, hdist⟩ := hf ε hε
    rcases ofSeq_surjective x with ⟨u, rfl⟩
    have hu : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |u n - r| < δ :=
      ofSeq_lt_ofSeq.1 (hxr δ hδ)
    refine ofSeq_lt_ofSeq.2 (hu.mono fun n hn ↦ ?_)
    change |f (u n) - f r| < ε
    rw [← Real.dist_eq]
    exact hdist (by rwa [Real.dist_eq])
  · intro hf ε hε
    by_contra hno
    push Not at hno
    have hex : ∀ n : ℕ, ∃ u : ℝ, |u - r| < ((n : ℝ) + 1)⁻¹ ∧ ε ≤ |f u - f r| := by
      intro n
      obtain ⟨u, hu1, hu2⟩ := hno (((n : ℝ) + 1)⁻¹) (by positivity)
      exact ⟨u, by simpa [Real.dist_eq] using hu1, by simpa [Real.dist_eq] using hu2⟩
    choose u hu using hex
    have hclose : ofSeq u ≈ₕ (r : ℝ*) := by
      refine isInfinitesimal_of_abs_le isInfinitesimal_epsilon ?_
      rw [abs_of_pos Hyperreal.epsilon_pos]
      have hne0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), n ≠ 0 :=
        Filter.hyperfilter_le_cofinite (Set.finite_singleton 0).compl_mem_cofinite
      refine ofSeq_le_ofSeq.2 (hne0.mono fun n hn0 ↦ ?_)
      change |u n - r| ≤ (n : ℝ)⁻¹
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
      exact (hu n).1.le.trans (inv_anti₀ hn_pos (by linarith))
    have hlt : |starFun f (ofSeq u) - (f r : ℝ*)| < (ε : ℝ*) := hf (ofSeq u) hclose ε hε
    have hge : (ε : ℝ*) ≤ |starFun f (ofSeq u) - (f r : ℝ*)| :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (hu n).2)
    exact lt_irrefl _ (hlt.trans_le hge)

/-- Nonstandard characterization of `ContinuousOn f A`: `f` is continuous on `A ⊆ ℝ` iff for every
`r ∈ A` and every `x ∈ starSet A` with `x ≈ₕ (r : ℝ*)`, `starFun f x ≈ₕ (f r : ℝ*)`. -/
theorem continuousOn_iff_infClose {f : ℝ → ℝ} {A : Set ℝ} :
    ContinuousOn f A ↔ ∀ r ∈ A, ∀ x ∈ starSet A, x ≈ₕ (r : ℝ*) → starFun f x ≈ₕ (f r : ℝ*) := by
  rw [Metric.continuousOn_iff]
  constructor
  · intro hf r hrA x hxA hxr ε hε
    obtain ⟨δ, hδ, hdist⟩ := hf r hrA ε hε
    rcases ofSeq_surjective x with ⟨u, rfl⟩
    have huA : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), u n ∈ A := ofSeq_mem_starSet.1 hxA
    have hud : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |u n - r| < δ :=
      ofSeq_lt_ofSeq.1 (hxr δ hδ)
    refine ofSeq_lt_ofSeq.2 ((huA.and hud).mono fun n ⟨hnA, hnd⟩ ↦ ?_)
    change |f (u n) - f r| < ε
    rw [← Real.dist_eq]
    exact hdist (u n) hnA (by rwa [Real.dist_eq])
  · intro hf r hrA ε hε
    by_contra hno
    push Not at hno
    have hex : ∀ n : ℕ, ∃ u : ℝ, u ∈ A ∧ |u - r| < ((n : ℝ) + 1)⁻¹ ∧ ε ≤ |f u - f r| := by
      intro n
      obtain ⟨u, huA, hu1, hu2⟩ := hno (((n : ℝ) + 1)⁻¹) (by positivity)
      exact ⟨u, huA, by simpa [Real.dist_eq] using hu1, by simpa [Real.dist_eq] using hu2⟩
    choose u hu using hex
    have hu_mem : ofSeq u ∈ starSet A :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (hu n).1)
    have hclose : ofSeq u ≈ₕ (r : ℝ*) := by
      refine isInfinitesimal_of_abs_le isInfinitesimal_epsilon ?_
      rw [abs_of_pos Hyperreal.epsilon_pos]
      have hne0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), n ≠ 0 :=
        Filter.hyperfilter_le_cofinite (Set.finite_singleton 0).compl_mem_cofinite
      refine ofSeq_le_ofSeq.2 (hne0.mono fun n hn0 ↦ ?_)
      change |u n - r| ≤ (n : ℝ)⁻¹
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
      exact (hu n).2.1.le.trans (inv_anti₀ hn_pos (by linarith))
    have hlt : |starFun f (ofSeq u) - (f r : ℝ*)| < (ε : ℝ*) :=
      hf r hrA (ofSeq u) hu_mem hclose ε hε
    have hge : (ε : ℝ*) ≤ |starFun f (ofSeq u) - (f r : ℝ*)| :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (hu n).2.2)
    exact lt_irrefl _ (hlt.trans_le hge)

/-- Global microcontinuity characterization: `Continuous f ↔ ∀ r : ℝ, ∀ x : ℝ*, x ≈ₕ r → *f(x) ≈ₕ f(r)`. -/
theorem continuous_iff_infClose {f : ℝ → ℝ} :
    Continuous f ↔ ∀ (r : ℝ) (x : ℝ*), x ≈ₕ (r : ℝ*) → starFun f x ≈ₕ (f r : ℝ*) := by
  rw [continuous_iff_continuousAt]
  exact forall_congr' fun _ ↦ continuousAt_iff_infClose

/-- Topological characterization of continuity via open preimages, proved purely nonstandardly via
halos, `starSet_preimage`, microcontinuity, and **Theorem 10.2.2** (`halo_coe_eq_biInter_starSet_isOpen`)! -/
theorem continuous_iff_isOpen_preimage_via_halo {f : ℝ → ℝ} :
    Continuous f ↔ ∀ U : Set ℝ, IsOpen U → IsOpen (f ⁻¹' U) := by
  rw [continuous_iff_infClose]
  constructor
  · intro hf U hU
    rw [isOpen_iff_halo_subset] at hU ⊢
    intro r hr x hx
    rw [starSet_preimage, Set.mem_preimage]
    exact hU (f r) hr (hf r x hx.symm).symm
  · intro hpre r x hxr
    have hmem : starFun f x ∈ halo (f r : ℝ*) := by
      rw [halo_coe_eq_biInter_starSet_isOpen]
      simp only [Set.mem_iInter]
      intro U hfrU hUo
      have hopen_pre := isOpen_iff_halo_subset.1 (hpre U hUo) r hfrU
      have hx_pre : x ∈ starSet (f ⁻¹' U) := hopen_pre hxr.symm
      rwa [starSet_preimage, Set.mem_preimage] at hx_pre
    exact hmem.symm

/-- Topological characterization of continuity via closed preimages, proved directly via halos and
complement duality (`isClosed_iff_isOpen_compl_via_halo`). -/
theorem continuous_iff_isClosed_preimage_via_halo {f : ℝ → ℝ} :
    Continuous f ↔ ∀ F : Set ℝ, IsClosed F → IsClosed (f ⁻¹' F) := by
  rw [continuous_iff_isOpen_preimage_via_halo]
  constructor
  · intro h F hF
    rw [isClosed_iff_isOpen_compl_via_halo] at hF ⊢
    exact h Fᶜ hF
  · intro h U hU
    rw [isOpen_iff_isClosed_compl_via_halo] at hU ⊢
    exact h Uᶜ hU

/-- Relative (subspace) openness of `B ⊆ A` in `A ⊆ ℝ`. -/
def IsRelOpen (A B : Set ℝ) : Prop :=
  B ⊆ A ∧ ∃ U : Set ℝ, IsOpen U ∧ B = A ∩ U

/-- Equivalence of `IsRelOpen A B` with openness in the subtype topology on `A`. -/
theorem isRelOpen_iff_isOpen_subtype {A B : Set ℝ} (hBA : B ⊆ A) :
    IsRelOpen A B ↔ IsOpen ((Subtype.val : A → ℝ) ⁻¹' B) := by
  unfold IsRelOpen
  rw [isOpen_induced_iff]
  constructor
  · rintro ⟨_, U, hUo, rfl⟩
    exact ⟨U, hUo, by ext ⟨x, _⟩; simp⟩
  · rintro ⟨U, hUo, hpre⟩
    refine ⟨hBA, U, hUo, ?_⟩
    ext x
    constructor
    · intro hxB
      have hxA : x ∈ A := hBA hxB
      have hxU : (⟨x, hxA⟩ : A) ∈ (Subtype.val : A → ℝ) ⁻¹' U := by
        rw [hpre]
        exact hxB
      exact ⟨hxA, hxU⟩
    · rintro ⟨hxA, hxU⟩
      have hxB : (⟨x, hxA⟩ : A) ∈ (Subtype.val : A → ℝ) ⁻¹' B := by
        rw [← hpre]
        exact hxU
      exact hxB

/-- Nonstandard halo characterization of subspace openness on `A ⊆ ℝ`: for `B ⊆ A`, `B` is
relatively open in `A` if and only if `halo (x : ℝ*) ∩ starSet A ⊆ starSet B` for all `x ∈ B`. -/
theorem isRelOpen_iff_halo_inter_subset {A B : Set ℝ} (hBA : B ⊆ A) :
    IsRelOpen A B ↔ ∀ x ∈ B, halo (x : ℝ*) ∩ starSet A ⊆ starSet B := by
  constructor
  · rintro ⟨_, U, hUo, rfl⟩ x ⟨hxA, hxU⟩ y ⟨hy_halo, hyA⟩
    rw [starSet_inter]
    exact ⟨hyA, (isOpen_iff_halo_subset.1 hUo) x hxU hy_halo⟩
  · intro hhalo
    have hex_ball : ∀ x ∈ B, ∃ r : ℝ, 0 < r ∧ A ∩ Metric.ball x r ⊆ B := by
      intro x hxB
      by_contra hno
      push Not at hno
      have hex : ∀ n : ℕ, ∃ a : ℝ, a ∈ A ∧ a ∈ Metric.ball x (((n : ℝ) + 1)⁻¹) ∧ a ∉ B := by
        intro n
        obtain ⟨a, ⟨haA, ha_ball⟩, ha_notB⟩ :=
          Set.not_subset.1 (hno (((n : ℝ) + 1)⁻¹) (by positivity))
        exact ⟨a, haA, ha_ball, ha_notB⟩
      choose a ha using hex
      have haA : ofSeq a ∈ starSet A :=
        ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (ha n).1)
      have hclose : (x : ℝ*) ≈ₕ ofSeq a := by
        refine isInfinitesimal_of_abs_le isInfinitesimal_epsilon ?_
        rw [abs_of_pos Hyperreal.epsilon_pos]
        have hne0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), n ≠ 0 :=
          Filter.hyperfilter_le_cofinite (Set.finite_singleton 0).compl_mem_cofinite
        refine ofSeq_le_ofSeq.2 (hne0.mono fun n hn0 ↦ ?_)
        change |x - a n| ≤ (n : ℝ)⁻¹
        have hdist : |a n - x| < ((n : ℝ) + 1)⁻¹ := by simpa [Real.dist_eq] using (ha n).2.1
        rw [abs_sub_comm]
        have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
        exact hdist.le.trans (inv_anti₀ hn_pos (by linarith))
      have haB : ofSeq a ∈ starSet B := hhalo x hxB ⟨hclose, haA⟩
      have ha_notB : ofSeq a ∈ (starSet B)ᶜ := by
        rw [← starSet_compl, ofSeq_mem_starSet]
        exact Eventually.of_forall fun n ↦ (ha n).2.2
      exact ha_notB haB
    let rad : ℝ → ℝ := fun x ↦ if hx : x ∈ B then (hex_ball x hx).choose else 1
    have hrad : ∀ x ∈ B, 0 < rad x ∧ A ∩ Metric.ball x (rad x) ⊆ B := by
      intro x hxB
      have heq : rad x = (hex_ball x hxB).choose := dite_eq_left_of_eq_true (eq_true hxB)
      rw [heq]
      exact (hex_ball x hxB).choose_spec
    refine ⟨hBA, ⋃ x ∈ B, Metric.ball x (rad x), ?_, ?_⟩
    · exact isOpen_biUnion fun x _ ↦ Metric.isOpen_ball
    · ext y
      constructor
      · intro hyB
        exact ⟨hBA hyB, Set.mem_biUnion hyB (Metric.mem_ball_self (hrad y hyB).1)⟩
      · rintro ⟨hyA, hyU⟩
        rcases Set.mem_iUnion₂.1 hyU with ⟨x, hxB, hy_ball⟩
        exact (hrad x hxB).2 ⟨hyA, hy_ball⟩

/-! ## §10.3 Compactness, Robinson's Criterion, and the Heine–Borel Theorem -/

/-- Goldblatt §10.3 (p. 117): A hyperreal `y ∈ ℝ*` is *near-standard* in `A ⊆ ℝ` if `y ≈ₕ c`
for some standard point `c ∈ A`. -/
def IsNearStandardIn (y : ℝ*) (A : Set ℝ) : Prop :=
  ∃ c ∈ A, y ≈ₕ (c : ℝ*)

/-- Goldblatt §10.3 (p. 117): `y ∈ ℝ*` is near-standard in `A ⊆ ℝ` if and only if `y` is limited
and its shadow `sh(y)` belongs to `A`. -/
theorem isNearStandardIn_iff_isLimited_and_shadow_mem {y : ℝ*} {A : Set ℝ} :
    IsNearStandardIn y A ↔ IsLimited y ∧ shadow y ∈ A := by
  constructor
  · rintro ⟨c, hcA, hyc⟩
    have hlim : IsLimited y := by
      have : y = (c : ℝ*) + (y - (c : ℝ*)) := by ring
      rw [this]
      exact (isLimited_coe c).add hyc.isLimited
    exact ⟨hlim, (shadow_eq_of_infClose hyc).symm ▸ hcA⟩
  · rintro ⟨hlim, hsh⟩
    exact ⟨shadow y, hsh, infClose_shadow hlim⟩

/-- Goldblatt §10.3 (p. 117): Every member of `*B` is near-standard in `B` iff
`*B ⊆ ⋃ r ∈ B, hal(r)`. -/
theorem forall_mem_starSet_isNearStandardIn_iff_subset_biUnion_halo {B : Set ℝ} :
    (∀ y ∈ starSet B, IsNearStandardIn y B) ↔ starSet B ⊆ ⋃ r ∈ B, halo (r : ℝ*) := by
  constructor
  · intro h y hy
    obtain ⟨r, hrB, hyr⟩ := h y hy
    exact Set.mem_biUnion hrB hyr.symm
  · intro h y hy
    rcases Set.mem_iUnion₂.1 (h hy) with ⟨r, hrB, hyr⟩
    exact ⟨r, hrB, hyr.symm⟩

/-- **Robinson's Compactness Criterion** (Goldblatt §10.3, pp. 117–118):
A subset `B ⊆ ℝ` is compact if and only if every `y ∈ starSet B` is infinitely close to some
`c ∈ B`.

Proved directly from open covers following Goldblatt's argument on p. 118 (using open covers by
finite subcovers for `(→)` and countable rational-endpoint interval covers for `(←)`), without
invoking the Heine–Borel theorem! -/
theorem isCompact_iff_robinson {B : Set ℝ} :
    IsCompact B ↔ ∀ y ∈ starSet B, ∃ c ∈ B, y ≈ₕ (c : ℝ*) := by
  rw [isCompact_iff_finite_subcover]
  constructor
  · intro hcomp b hb
    by_contra hno
    push Not at hno
    have hex : ∀ r ∈ B, ∃ ε : ℝ, 0 < ε ∧ (ε : ℝ*) ≤ |b - (r : ℝ*)| := by
      intro r hrB
      have hnot : ¬ IsInfinitesimal (b - (r : ℝ*)) := hno r hrB
      unfold IsInfinitesimal at hnot
      push Not at hnot
      exact hnot
    let rad : ℝ → ℝ := fun r ↦ if hr : r ∈ B then (hex r hr).choose else 1
    have hrad : ∀ r ∈ B, 0 < rad r ∧ (rad r : ℝ*) ≤ |b - (r : ℝ*)| := by
      intro r hrB
      have heq : rad r = (hex r hrB).choose := dite_eq_left_of_eq_true (eq_true hrB)
      rw [heq]
      exact (hex r hrB).choose_spec
    let U : B → Set ℝ := fun r ↦ Set.Ioo (r.1 - rad r.1) (r.1 + rad r.1)
    have hUo : ∀ r : B, IsOpen (U r) := fun _ ↦ isOpen_Ioo
    have hcov : B ⊆ ⋃ r : B, U r := by
      intro x hxB
      refine Set.mem_iUnion.2 ⟨⟨x, hxB⟩, ?_⟩
      have hpos := (hrad x hxB).1
      exact ⟨by linarith, by linarith⟩
    obtain ⟨F, hF⟩ := hcomp U hUo hcov
    have hb_union : b ∈ ⋃ r ∈ F, starSet (U r) := by
      rw [← starSet_biUnion_finset]
      exact (starSet_subset_starSet_iff.2 hF) hb
    rcases Set.mem_iUnion₂.1 hb_union with ⟨r, _, hbr⟩
    have hbIoo : b ∈ Set.Ioo ((r.1 - rad r.1 : ℝ) : ℝ*) ((r.1 + rad r.1 : ℝ) : ℝ*) := by
      simpa [U, starSet_Ioo] using hbr
    have hlt : |b - (r.1 : ℝ*)| < (rad r.1 : ℝ*) := by
      rw [Hyperreal.coe_sub, Hyperreal.coe_add, Set.mem_Ioo] at hbIoo
      exact abs_lt.2 ⟨by linarith [hbIoo.1], by linarith [hbIoo.2]⟩
    exact lt_irrefl _ (hlt.trans_le (hrad r.1 r.2).2)
  · intro hRob ι U hUo hcov
    rcases B.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
    · exact ⟨∅, by simp⟩
    obtain ⟨i₀, _⟩ := Set.mem_iUnion.1 (hcov hb₀)
    let P : ℚ × ℚ → Prop := fun pq ↦ ∃ i : ι, Set.Ioo (pq.1 : ℝ) (pq.2 : ℝ) ⊆ U i
    obtain ⟨e, he_surj⟩ := exists_surjective_nat (ℚ × ℚ)
    let V : ℕ → Set ℝ := fun n ↦
      if P (e n) then Set.Ioo ((e n).1 : ℝ) ((e n).2 : ℝ) else ∅
    let idx : ℕ → ι := fun n ↦ if h : P (e n) then h.choose else i₀
    have hVo : ∀ n : ℕ, IsOpen (V n) := by
      intro n
      dsimp [V]
      split_ifs
      · exact isOpen_Ioo
      · exact isOpen_empty
    have hVU : ∀ n : ℕ, V n ⊆ U (idx n) := by
      intro n
      by_cases hP : P (e n)
      · have h1 : V n = Set.Ioo ((e n).1 : ℝ) ((e n).2 : ℝ) := by simp [V, hP]
        have h2 : idx n = hP.choose := dite_eq_left_of_eq_true (eq_true hP)
        rw [h1, h2]
        exact hP.choose_spec
      · have h1 : V n = ∅ := by simp [V, hP]
        rw [h1]
        exact Set.empty_subset _
    have hB_covV : B ⊆ ⋃ n : ℕ, V n := by
      intro r hrB
      obtain ⟨i, hri⟩ := Set.mem_iUnion.1 (hcov hrB)
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hUo i) r hri
      rw [Real.ball_eq_Ioo] at hball
      obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (sub_lt_self r hε)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right r hε)
      have hsub : Set.Ioo (p : ℝ) (q : ℝ) ⊆ U i :=
        fun z hz ↦ hball ⟨hp1.trans hz.1, hz.2.trans hq2⟩
      obtain ⟨n, hn⟩ := he_surj (p, q)
      have hPn : P (e n) := by
        rw [hn]
        exact ⟨i, hsub⟩
      refine Set.mem_iUnion.2 ⟨n, ?_⟩
      have hVn : V n = Set.Ioo ((e n).1 : ℝ) ((e n).2 : ℝ) := by simp [V, hPn]
      rw [hVn, hn]
      exact ⟨hp2, hq1⟩
    by_contra hno_fin
    push Not at hno_fin
    have hex_miss : ∀ k : ℕ, ∃ a ∈ B, ∀ n ≤ k, a ∉ V n := by
      intro k
      have hnot_sub : ¬ (B ⊆ ⋃ n ∈ Finset.range (k + 1), V n) := by
        intro hsub
        apply hno_fin ((Finset.range (k + 1)).image idx)
        intro x hxB
        rcases Set.mem_iUnion₂.1 (hsub hxB) with ⟨n, hn_range, hxn⟩
        exact Set.mem_biUnion (Finset.mem_image_of_mem idx hn_range) (hVU n hxn)
      obtain ⟨a, haB, ha_not⟩ := Set.not_subset.1 hnot_sub
      refine ⟨a, haB, fun n hnk han ↦ ha_not ?_⟩
      exact Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hnk)) han
    choose a ha using hex_miss
    have ha_star : ofSeq a ∈ starSet B :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun k ↦ (ha k).1)
    obtain ⟨c, hcB, hxc⟩ := hRob (ofSeq a) ha_star
    obtain ⟨m, hcm⟩ := Set.mem_iUnion.1 (hB_covV hcB)
    have ha_in_Vm : ofSeq a ∈ starSet (V m) :=
      (isOpen_iff_halo_subset.1 (hVo m)) c hcm hxc.symm
    have hev_in : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), a k ∈ V m :=
      ofSeq_mem_starSet.1 ha_in_Vm
    have hev_out : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), a k ∉ V m :=
      (eventually_atTop.2 ⟨m, fun k hmk ↦ (ha k).2 m hmk⟩).filter_mono Nat.hyperfilter_le_atTop
    obtain ⟨k, hk_in, hk_out⟩ := (hev_in.and hev_out).exists
    exact hk_out hk_in

/-- Near-standard form of **Robinson's Compactness Criterion** (Goldblatt §10.3, p. 117). -/
theorem isCompact_iff_forall_isNearStandardIn {A : Set ℝ} :
    IsCompact A ↔ ∀ y ∈ starSet A, IsNearStandardIn y A :=
  isCompact_iff_robinson

/-- Halo-covering form of **Robinson's Compactness Criterion** (Goldblatt §10.3, p. 117):
`IsCompact A ↔ *A ⊆ ⋃ c ∈ A, hal(c)`. -/
theorem isCompact_iff_starSet_subset_biUnion_halo {A : Set ℝ} :
    IsCompact A ↔ starSet A ⊆ ⋃ c ∈ A, halo (c : ℝ*) :=
  isCompact_iff_forall_isNearStandardIn.trans forall_mem_starSet_isNearStandardIn_iff_subset_biUnion_halo

/-- Shadow form of **Robinson's Compactness Criterion** (Goldblatt §10.3, p. 117):
`IsCompact A ↔ ∀ y ∈ starSet A, IsLimited y ∧ shadow y ∈ A`. -/
theorem isCompact_iff_forall_isLimited_shadow_mem {A : Set ℝ} :
    IsCompact A ↔ ∀ y ∈ starSet A, IsLimited y ∧ shadow y ∈ A := by
  rw [isCompact_iff_forall_isNearStandardIn]
  exact forall₂_congr fun _ _ ↦ isNearStandardIn_iff_isLimited_and_shadow_mem

/-! ### Goldblatt's Consequences, Examples, and the Heine–Borel Theorem -/

/-- Goldblatt §10.3 (p. 117): The open interval `(0, 1) ⊆ ℝ` is NOT compact, since the positive
infinitesimal `ε ∈ *(0, 1)` has shadow `0 ∉ (0, 1)`. -/
theorem not_isCompact_Ioo_zero_one : ¬ IsCompact (Set.Ioo (0 : ℝ) 1) := by
  rw [isCompact_iff_forall_isLimited_shadow_mem]
  intro h
  have heps_mem : Hyperreal.epsilon ∈ starSet (Set.Ioo (0 : ℝ) 1) := by
    rw [starSet_Ioo, Hyperreal.coe_zero, Hyperreal.coe_one]
    exact ⟨Hyperreal.epsilon_pos, Hyperreal.epsilon_lt_of_pos one_pos⟩
  have hsh := (h Hyperreal.epsilon heps_mem).2
  have hzero : shadow Hyperreal.epsilon = 0 :=
    (shadow_eq_zero_iff_isInfinitesimal isInfinitesimal_epsilon.isLimited).2 isInfinitesimal_epsilon
  rw [hzero] at hsh
  exact lt_irrefl (0 : ℝ) hsh.1

/-- Goldblatt §10.3 (p. 117): Every closed interval `[a, b] ⊆ ℝ` is compact, proved in four lines
via Robinson's Compactness Criterion and order preservation of `shadow`! -/
theorem isCompact_Icc_via_robinson (a b : ℝ) : IsCompact (Set.Icc a b) := by
  rw [isCompact_iff_forall_isLimited_shadow_mem]
  intro x hx
  rw [starSet_Icc, Set.mem_Icc] at hx
  have hlim : IsLimited x :=
    isLimited_iff_exists_real.2 ⟨a - 1, b + 1,
      (Hyperreal.coe_lt_coe.2 (by linarith)).trans_le hx.1,
      hx.2.trans_lt (Hyperreal.coe_lt_coe.2 (by linarith))⟩
  refine ⟨hlim, ?_, ?_⟩
  · simpa using shadow_le_of_le (isLimited_coe a) hlim hx.1
  · simpa using shadow_le_of_le hlim (isLimited_coe b) hx.2

/-- Goldblatt §10.3 (p. 117): Every finite subset `B ⊆ ℝ` is compact, since `*B = B`. -/
theorem isCompact_of_finite_via_robinson {B : Set ℝ} (hB : B.Finite) : IsCompact B := by
  rw [isCompact_iff_robinson, starSet_eq_image_of_finite hB]
  rintro _ ⟨c, hcB, rfl⟩
  exact ⟨c, hcB, InfClose.refl _⟩

/-- Goldblatt §10.3 (p. 117): Every compact subset `B ⊆ ℝ` is bounded, proved directly from
Robinson's Compactness Criterion (an unbounded set has an unlimited member in `*B`). -/
theorem isBounded_of_isCompact_via_robinson {B : Set ℝ} (hB : IsCompact B) :
    Bornology.IsBounded B := by
  rw [isBounded_iff_forall_norm_le]
  by_contra hunb
  push Not at hunb
  choose a ha using fun n : ℕ ↦ hunb n
  have ha_star : ofSeq a ∈ starSet B :=
    ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (ha n).1)
  have hunl : IsUnlimited (ofSeq a) := by
    intro n
    have hgt : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), (n : ℝ) < |a k| := by
      refine (eventually_atTop.2 ⟨n, fun k hnk ↦ ?_⟩).filter_mono Nat.hyperfilter_le_atTop
      have hk : (k : ℝ) < |a k| := by simpa [Real.norm_eq_abs] using (ha k).2
      have hnk' : (n : ℝ) ≤ (k : ℝ) := Nat.cast_le.2 hnk
      exact hnk'.trans_lt hk
    exact ofSeq_lt_ofSeq.2 hgt
  obtain ⟨hlim, _⟩ := (isCompact_iff_forall_isLimited_shadow_mem.1 hB) (ofSeq a) ha_star
  exact (isUnlimited_iff_not_isLimited.1 hunl) hlim

/-- Goldblatt §10.3 (pp. 117–118): Every compact subset `B ⊆ ℝ` is closed, proved directly from
Robinson's Compactness Criterion. -/
theorem isClosed_of_isCompact_via_robinson {B : Set ℝ} (hB : IsCompact B) : IsClosed B := by
  rw [isClosed_iff_forall_infClose]
  rintro r ⟨x, hxB, hxr⟩
  obtain ⟨s, hsB, hxs⟩ := (isCompact_iff_robinson.1 hB) x hxB
  have hrs : r = s := coe_eq_of_infClose (hxr.symm.trans hxs)
  exact hrs ▸ hsB

/-- **Goldblatt Theorem 10.3.1 (Heine–Borel Theorem)** (p. 119):
A subset `B ⊆ ℝ` is compact if and only if it is closed and bounded — deduced directly from
Robinson's Compactness Criterion (`isCompact_iff_forall_isLimited_shadow_mem`) and `shadow`! -/
theorem heine_borel_via_robinson (B : Set ℝ) :
    IsCompact B ↔ IsClosed B ∧ Bornology.IsBounded B := by
  constructor
  · intro hB
    exact ⟨isClosed_of_isCompact_via_robinson hB, isBounded_of_isCompact_via_robinson hB⟩
  · rintro ⟨hclosed, hbdd⟩
    rw [isCompact_iff_forall_isLimited_shadow_mem]
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hbdd
    intro x hx
    rcases ofSeq_surjective x with ⟨u, rfl⟩
    have huB : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), u n ∈ B := ofSeq_mem_starSet.1 hx
    have habs : |ofSeq u| ≤ ((max C 0 : ℝ) : ℝ*) := by
      refine ofSeq_le_ofSeq.2 (huB.mono fun n hn ↦ ?_)
      have h1 : |u n| ≤ C := by simpa [Real.norm_eq_abs] using hC (u n) hn
      exact h1.trans (le_max_left C 0)
    have hlim : IsLimited (ofSeq u) :=
      isLimited_iff_abs_le_real.2 ⟨max C 0, le_max_right C 0, habs⟩
    exact ⟨hlim, (isClosed_iff_shadow_mem.1 hclosed) (ofSeq u) hx hlim⟩

/-- **Goldblatt Exercise 10.3.2** (p. 119): In `ℝ`, a closed subset of a compact set is compact,
proved directly from Robinson's Compactness Criterion! -/
theorem isCompact_of_isClosed_subset_via_robinson {K F : Set ℝ}
    (hK : IsCompact K) (hF : IsClosed F) (hFK : F ⊆ K) :
    IsCompact F := by
  rw [isCompact_iff_robinson]
  intro y hyF
  have hyK : y ∈ starSet K := (starSet_subset_starSet_iff.2 hFK) hyF
  obtain ⟨c, _, hyc⟩ := (isCompact_iff_robinson.1 hK) y hyK
  exact ⟨c, (isClosed_iff_forall_infClose.1 hF) c ⟨y, hyF, hyc⟩, hyc⟩

/-! ## §10.4 Compactness, Extreme Values, and Uniform Continuity -/

/-- **Goldblatt Theorem 10.4.1** (p. 119): The continuous image of a compact set is compact,
proved in five lines via Robinson's Compactness Criterion and `starSet_image`! -/
theorem isCompact_image_of_continuousOn_via_robinson {f : ℝ → ℝ} {B : Set ℝ}
    (hf : ContinuousOn f B) (hB : IsCompact B) :
    IsCompact (f '' B) := by
  rw [isCompact_iff_robinson]
  intro y hy
  rw [starSet_image] at hy
  rcases hy with ⟨x, hxB, rfl⟩
  obtain ⟨r, hrB, hxr⟩ := (isCompact_iff_robinson.1 hB) x hxB
  exact ⟨f r, ⟨r, hrB, rfl⟩, (continuousOn_iff_infClose.1 hf) r hrB x hxB hxr⟩

/-- Global `Continuous` specialization of **Goldblatt Theorem 10.4.1** (p. 119). -/
theorem isCompact_image_of_continuous_via_robinson {f : ℝ → ℝ} {B : Set ℝ}
    (hf : Continuous f) (hB : IsCompact B) :
    IsCompact (f '' B) :=
  isCompact_image_of_continuousOn_via_robinson hf.continuousOn hB

/-- Nonstandard proof via Robinson's Compactness Criterion that every nonempty compact subset
`C ⊆ ℝ` contains both its supremum `sSup C` and its infimum `sInf C`. -/
theorem sSup_mem_and_sInf_mem_of_isCompact {C : Set ℝ} (hC : IsCompact C) (hCne : C.Nonempty) :
    sSup C ∈ C ∧ sInf C ∈ C := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (isBounded_of_isCompact_via_robinson hC)
  have hbdd_above : BddAbove C :=
    ⟨M, fun x hx ↦ (le_abs_self x).trans (by simpa [Real.norm_eq_abs] using hM x hx)⟩
  have hbdd_below : BddBelow C :=
    ⟨-M, fun x hx ↦ neg_le_of_abs_le (by simpa [Real.norm_eq_abs] using hM x hx)⟩
  have hne0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), n ≠ 0 :=
    Filter.hyperfilter_le_cofinite (Set.finite_singleton 0).compl_mem_cofinite
  refine ⟨?_, ?_⟩
  · set supC : ℝ := sSup C
    have hex_sup : ∀ n : ℕ, ∃ u ∈ C, supC - ((n : ℝ) + 1)⁻¹ < u := fun n ↦
      exists_lt_of_lt_csSup hCne (sub_lt_self supC (by positivity))
    choose u hu using hex_sup
    have huC : ofSeq u ∈ starSet C :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (hu n).1)
    have hu_close : ofSeq u ≈ₕ (supC : ℝ*) := by
      refine isInfinitesimal_of_abs_le isInfinitesimal_epsilon ?_
      rw [abs_of_pos Hyperreal.epsilon_pos]
      refine ofSeq_le_ofSeq.2 (hne0.mono fun n hn0 ↦ ?_)
      change |u n - supC| ≤ (n : ℝ)⁻¹
      have hle : u n ≤ supC := le_csSup hbdd_above (hu n).1
      have hgt : supC - ((n : ℝ) + 1)⁻¹ < u n := (hu n).2
      have habs : |u n - supC| ≤ ((n : ℝ) + 1)⁻¹ := abs_le.2 ⟨by linarith, by linarith⟩
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
      exact habs.trans (inv_anti₀ hn_pos (by linarith))
    obtain ⟨c, hcC, huc⟩ := (isCompact_iff_robinson.1 hC) (ofSeq u) huC
    have heq : supC = c := coe_eq_of_infClose (hu_close.symm.trans huc)
    exact heq ▸ hcC
  · set infC : ℝ := sInf C
    have hex_inf : ∀ n : ℕ, ∃ v ∈ C, v < infC + ((n : ℝ) + 1)⁻¹ := fun n ↦
      exists_lt_of_csInf_lt hCne (lt_add_of_pos_right infC (by positivity))
    choose v hv using hex_inf
    have hvC : ofSeq v ∈ starSet C :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (hv n).1)
    have hv_close : ofSeq v ≈ₕ (infC : ℝ*) := by
      refine isInfinitesimal_of_abs_le isInfinitesimal_epsilon ?_
      rw [abs_of_pos Hyperreal.epsilon_pos]
      refine ofSeq_le_ofSeq.2 (hne0.mono fun n hn0 ↦ ?_)
      change |v n - infC| ≤ (n : ℝ)⁻¹
      have hge : infC ≤ v n := csInf_le hbdd_below (hv n).1
      have hlt : v n < infC + ((n : ℝ) + 1)⁻¹ := (hv n).2
      have habs : |v n - infC| ≤ ((n : ℝ) + 1)⁻¹ := abs_le.2 ⟨by linarith, by linarith⟩
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
      exact habs.trans (inv_anti₀ hn_pos (by linarith))
    obtain ⟨c, hcC, hvc⟩ := (isCompact_iff_robinson.1 hC) (ofSeq v) hvC
    have heq : infC = c := coe_eq_of_infClose (hv_close.symm.trans hvc)
    exact heq ▸ hcC

/-- **Extreme Value Theorem on Compact Sets** deduced from **Theorem 10.4.1** and Robinson's
Compactness Criterion: every function `f` continuous on a nonempty compact set `B ⊆ ℝ` attains
its maximum and minimum on `B`! -/
theorem extreme_value_on_isCompact_via_robinson {f : ℝ → ℝ} {B : Set ℝ}
    (hB : IsCompact B) (hBne : B.Nonempty) (hf : ContinuousOn f B) :
    (∃ x_max ∈ B, ∀ x ∈ B, f x ≤ f x_max) ∧ (∃ x_min ∈ B, ∀ x ∈ B, f x_min ≤ f x) := by
  have hImg : IsCompact (f '' B) := isCompact_image_of_continuousOn_via_robinson hf hB
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (isBounded_of_isCompact_via_robinson hImg)
  have hbdd_above : BddAbove (f '' B) :=
    ⟨M, fun y hy ↦ (le_abs_self y).trans (by simpa [Real.norm_eq_abs] using hM y hy)⟩
  have hbdd_below : BddBelow (f '' B) :=
    ⟨-M, fun y hy ↦ neg_le_of_abs_le (by simpa [Real.norm_eq_abs] using hM y hy)⟩
  obtain ⟨hsup, hinf⟩ := sSup_mem_and_sInf_mem_of_isCompact hImg (hBne.image f)
  rcases hsup with ⟨x_max, hx_max, hf_max⟩
  rcases hinf with ⟨x_min, hx_min, hf_min⟩
  refine ⟨⟨x_max, hx_max, fun x hx ↦ ?_⟩, ⟨x_min, hx_min, fun x hx ↦ ?_⟩⟩
  · rw [hf_max]
    exact le_csSup hbdd_above ⟨x, hx, rfl⟩
  · rw [hf_min]
    exact csInf_le hbdd_below ⟨x, hx, rfl⟩

/-- Nonstandard characterization of `UniformContinuousOn f B` (Goldblatt Theorem 7.7.1):
`f` is uniformly continuous on `B ⊆ ℝ` iff for all `x, y ∈ starSet B`, `x ≈ₕ y → *f(x) ≈ₕ *f(y)`. -/
theorem uniformContinuousOn_iff_infClose {f : ℝ → ℝ} {B : Set ℝ} :
    UniformContinuousOn f B ↔
      ∀ x ∈ starSet B, ∀ y ∈ starSet B, x ≈ₕ y → starFun f x ≈ₕ starFun f y := by
  rw [Metric.uniformContinuousOn_iff]
  constructor
  · intro hf x hxB y hyB hxy ε hε
    obtain ⟨δ, hδ, hdist⟩ := hf ε hε
    rcases ofSeq_surjective x with ⟨u, rfl⟩
    rcases ofSeq_surjective y with ⟨v, rfl⟩
    have huB : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), u n ∈ B := ofSeq_mem_starSet.1 hxB
    have hvB : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), v n ∈ B := ofSeq_mem_starSet.1 hyB
    have huv : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |u n - v n| < δ :=
      ofSeq_lt_ofSeq.1 (hxy δ hδ)
    refine ofSeq_lt_ofSeq.2 (((huB.and hvB).and huv).mono fun n ⟨⟨hnu, hnv⟩, hnd⟩ ↦ ?_)
    change |f (u n) - f (v n)| < ε
    rw [← Real.dist_eq]
    exact hdist (u n) hnu (v n) hnv (by rwa [Real.dist_eq])
  · intro hf ε hε
    by_contra hno
    push Not at hno
    have hex : ∀ n : ℕ, ∃ u v : ℝ,
        u ∈ B ∧ v ∈ B ∧ |u - v| < ((n : ℝ) + 1)⁻¹ ∧ ε ≤ |f u - f v| := by
      intro n
      obtain ⟨u, huB, v, hvB, h1, h2⟩ := hno (((n : ℝ) + 1)⁻¹) (by positivity)
      exact ⟨u, v, huB, hvB, by simpa [Real.dist_eq] using h1, by simpa [Real.dist_eq] using h2⟩
    choose u v huv using hex
    have hu_star : ofSeq u ∈ starSet B :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (huv n).1)
    have hv_star : ofSeq v ∈ starSet B :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (huv n).2.1)
    have hclose : ofSeq u ≈ₕ ofSeq v := by
      refine isInfinitesimal_of_abs_le isInfinitesimal_epsilon ?_
      rw [abs_of_pos Hyperreal.epsilon_pos]
      have hne0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), n ≠ 0 :=
        Filter.hyperfilter_le_cofinite (Set.finite_singleton 0).compl_mem_cofinite
      refine ofSeq_le_ofSeq.2 (hne0.mono fun n hn0 ↦ ?_)
      change |u n - v n| ≤ (n : ℝ)⁻¹
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
      exact (huv n).2.2.1.le.trans (inv_anti₀ hn_pos (by linarith))
    have hlt : |starFun f (ofSeq u) - starFun f (ofSeq v)| < (ε : ℝ*) :=
      hf (ofSeq u) hu_star (ofSeq v) hv_star hclose ε hε
    have hge : (ε : ℝ*) ≤ |starFun f (ofSeq u) - starFun f (ofSeq v)| :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (huv n).2.2.2)
    exact lt_irrefl _ (hlt.trans_le hge)

/-- **Goldblatt Theorem 10.4.2 (Heine–Cantor Theorem on Compact Sets)** (p. 120):
If `f` is continuous on a compact set `B ⊆ ℝ`, then `f` is uniformly continuous on `B` — proved
in six lines via Robinson's Compactness Criterion! -/
theorem uniformContinuousOn_of_continuousOn_isCompact_via_robinson {f : ℝ → ℝ} {B : Set ℝ}
    (hf : ContinuousOn f B) (hB : IsCompact B) :
    UniformContinuousOn f B := by
  rw [uniformContinuousOn_iff_infClose]
  intro x hxB y hyB hxy
  obtain ⟨r, hrB, hxr⟩ := (isCompact_iff_robinson.1 hB) x hxB
  obtain ⟨s, _, hys⟩ := (isCompact_iff_robinson.1 hB) y hyB
  have hrs : r = s := coe_eq_of_infClose (hxr.symm.trans (hxy.trans hys))
  subst hrs
  exact ((continuousOn_iff_infClose.1 hf) r hrB x hxB hxr).trans
    ((continuousOn_iff_infClose.1 hf) r hrB y hyB hys).symm

/-! ## §10.5 Topologies on the Hyperreals `ℝ*` -/

/-! ### Real-Radius Neighbourhoods and Real-Open Sets -/

/-- Goldblatt §10.5 (p. 120): The *real-radius neighbourhood* `(r - ε, r + ε) ⊆ ℝ*` of `r ∈ ℝ*`
with real radius `ε ∈ ℝ`. -/
def realRadiusNhds (r : ℝ*) (ε : ℝ) : Set ℝ* :=
  Set.Ioo (r - (ε : ℝ*)) (r + (ε : ℝ*))

/-- Membership in `realRadiusNhds r ε` is equivalent to `|x - r| < (ε : ℝ*)`. -/
@[simp]
theorem mem_realRadiusNhds_iff_abs {r x : ℝ*} {ε : ℝ} :
    x ∈ realRadiusNhds r ε ↔ |x - r| < (ε : ℝ*) := by
  unfold realRadiusNhds
  rw [Set.mem_Ioo, abs_lt]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨by linarith, by linarith⟩,
         fun ⟨h1, h2⟩ ↦ ⟨by linarith, by linarith⟩⟩

/-- When `0 < ε`, the center `r` belongs to `realRadiusNhds r ε`. -/
theorem self_mem_realRadiusNhds (r : ℝ*) {ε : ℝ} (hε : 0 < ε) :
    r ∈ realRadiusNhds r ε := by
  rw [mem_realRadiusNhds_iff_abs, sub_self, abs_zero]
  exact Hyperreal.coe_pos.2 hε

/-- Goldblatt §10.5 (p. 120): A subset `A ⊆ ℝ*` is *real-open* if it is a union of real-radius
neighbourhoods `(r - ε, r + ε)` with `ε > 0` in `ℝ`. -/
def IsRealOpen (A : Set ℝ*) : Prop :=
  ∃ S : Set (Set ℝ*), (∀ U ∈ S, ∃ (r : ℝ*) (ε : ℝ), 0 < ε ∧ U = realRadiusNhds r ε) ∧ A = ⋃₀ S

/-- Pointwise characterization of `IsRealOpen`: `A ⊆ ℝ*` is real-open iff every `x ∈ A` belongs to
some real-radius neighbourhood `(r - ε, r + ε) ⊆ A` with real `ε > 0`. -/
theorem isRealOpen_iff {A : Set ℝ*} :
    IsRealOpen A ↔ ∀ x ∈ A, ∃ (r : ℝ*) (ε : ℝ), 0 < ε ∧ x ∈ realRadiusNhds r ε ∧
      realRadiusNhds r ε ⊆ A := by
  constructor
  · rintro ⟨S, hS, rfl⟩ x ⟨U, hUS, hxU⟩
    obtain ⟨r, ε, hε, rfl⟩ := hS U hUS
    exact ⟨r, ε, hε, hxU, Set.subset_sUnion_of_mem hUS⟩
  · intro h
    refine ⟨{U : Set ℝ* | ∃ (r : ℝ*) (ε : ℝ), 0 < ε ∧ U = realRadiusNhds r ε ∧ U ⊆ A}, ?_, ?_⟩
    · rintro U ⟨r, ε, hε, hU, _⟩
      exact ⟨r, ε, hε, hU⟩
    · apply Set.Subset.antisymm
      · intro x hxA
        obtain ⟨r, ε, hε, hxr, hsub⟩ := h x hxA
        exact ⟨realRadiusNhds r ε, ⟨r, ε, hε, rfl, hsub⟩, hxr⟩
      · rintro x ⟨U, ⟨_, _, _, _, hUA⟩, hxU⟩
        exact hUA hxU

/-- Sufficient condition for `IsRealOpen`: if every `x ∈ A` admits a real `ε > 0` such that the
centered neighbourhood `realRadiusNhds x ε ⊆ A`, then `A` is real-open. -/
theorem isRealOpen_of_forall_centered {A : Set ℝ*}
    (h : ∀ x ∈ A, ∃ ε : ℝ, 0 < ε ∧ realRadiusNhds x ε ⊆ A) :
    IsRealOpen A := by
  rw [isRealOpen_iff]
  intro x hxA
  obtain ⟨ε, hε, hsub⟩ := h x hxA
  exact ⟨x, ε, hε, self_mem_realRadiusNhds x hε, hsub⟩

/-- Every positive real-radius neighbourhood is real-open. -/
theorem isRealOpen_realRadiusNhds (r : ℝ*) {ε : ℝ} (hε : 0 < ε) :
    IsRealOpen (realRadiusNhds r ε) :=
  ⟨{realRadiusNhds r ε}, fun _ hU ↦ ⟨r, ε, hε, hU⟩, (Set.sUnion_singleton _).symm⟩

/-- `∅` is real-open. -/
theorem isRealOpen_empty : IsRealOpen ∅ :=
  ⟨∅, by simp, Set.sUnion_empty.symm⟩

/-- `Set.univ` is real-open. -/
theorem isRealOpen_univ : IsRealOpen Set.univ :=
  isRealOpen_of_forall_centered fun _ _ ↦ ⟨1, one_pos, Set.subset_univ _⟩

/-- Goldblatt §10.5 (p. 120): The class of real-open sets is closed under arbitrary unions. -/
theorem isRealOpen_sUnion {F : Set (Set ℝ*)} (hF : ∀ A ∈ F, IsRealOpen A) :
    IsRealOpen (⋃₀ F) := by
  rw [isRealOpen_iff]
  rintro x ⟨A, hAF, hxA⟩
  obtain ⟨r, ε, hε, hxr, hsub⟩ := (isRealOpen_iff.1 (hF A hAF)) x hxA
  exact ⟨r, ε, hε, hxr, hsub.trans (Set.subset_sUnion_of_mem hAF)⟩

/-- Indexed union form of `isRealOpen_sUnion`. -/
theorem isRealOpen_iUnion {ι : Type*} {A : ι → Set ℝ*} (hA : ∀ i, IsRealOpen (A i)) :
    IsRealOpen (⋃ i, A i) := by
  rw [← Set.sUnion_range]
  refine isRealOpen_sUnion ?_
  rintro _ ⟨i, rfl⟩
  exact hA i

/-! ### Goldblatt's Eight Examples of Real-Open Sets (§10.5, p. 120) -/

/-- Goldblatt §10.5 Example 1 (p. 120): The set `𝕃` of limited hyperreals is real-open. -/
theorem isRealOpen_limited : IsRealOpen {x : ℝ* | IsLimited x} := by
  refine isRealOpen_of_forall_centered fun x hx ↦ ⟨1, one_pos, fun y hy ↦ ?_⟩
  rw [mem_realRadiusNhds_iff_abs] at hy
  have hdiff : IsLimited (y - x) := ⟨1, by simpa using hy⟩
  have heq : y = x + (y - x) := by ring
  rw [heq]
  exact hx.add hdiff

/-- Goldblatt §10.5 Example 2 (p. 120): The set of unlimited hyperreals is real-open. -/
theorem isRealOpen_unlimited : IsRealOpen {x : ℝ* | IsUnlimited x} := by
  refine isRealOpen_of_forall_centered fun x hx ↦ ⟨1, one_pos, fun y hy ↦ ?_⟩
  rw [mem_realRadiusNhds_iff_abs] at hy
  have hdiff : IsLimited (y - x) := ⟨1, by simpa using hy⟩
  have heq : y = x + (y - x) := by ring
  change IsUnlimited y
  rw [heq]
  exact hx.add_isLimited hdiff

/-- Goldblatt §10.5 Example 3 (p. 120): The set of positive unlimited hyperreals is real-open. -/
theorem isRealOpen_posUnlimited : IsRealOpen {x : ℝ* | IsPosUnlimited x} := by
  refine isRealOpen_of_forall_centered fun x hx ↦ ⟨1, one_pos, fun y hy c ↦ ?_⟩
  have hxc : ((c + 1 : ℝ) : ℝ*) < x := hx (c + 1)
  have hyx : x - 1 < y := hy.1
  rw [Hyperreal.coe_add, Hyperreal.coe_one] at hxc
  linarith

/-- Goldblatt §10.5 Example 4 (p. 120): The set of negative unlimited hyperreals is real-open. -/
theorem isRealOpen_negUnlimited : IsRealOpen {x : ℝ* | IsNegUnlimited x} := by
  refine isRealOpen_of_forall_centered fun x hx ↦ ⟨1, one_pos, fun y hy c ↦ ?_⟩
  have hxc : x < ((c - 1 : ℝ) : ℝ*) := hx (c - 1)
  have hyx : y < x + 1 := hy.2
  rw [Hyperreal.coe_sub, Hyperreal.coe_one] at hxc
  linarith

/-- Goldblatt §10.5 Example 5 (p. 120): The set of appreciable hyperreals is real-open. -/
theorem isRealOpen_appreciable : IsRealOpen {x : ℝ* | IsAppreciable x} := by
  refine isRealOpen_of_forall_centered fun x hx ↦ ?_
  obtain ⟨c, d, hc_pos, hcx, hxd⟩ := isAppreciable_iff_pos_real_bounds.1 hx
  refine ⟨c / 2, half_pos hc_pos, fun y hy ↦ ?_⟩
  rw [mem_realRadiusNhds_iff_abs] at hy
  refine isAppreciable_iff_pos_real_bounds.2 ⟨c / 4, d + c / 2, by positivity, ?_, ?_⟩
  · have htri : |x| - |y - x| ≤ |y| := by
      have := abs_sub_abs_le_abs_sub x y
      rwa [abs_sub_comm x y, sub_le_iff_le_add, ← sub_le_iff_le_add'] at this
    have hgt : ((c - c / 2 : ℝ) : ℝ*) < |x| - |y - x| := by
      rw [Hyperreal.coe_sub]
      linarith
    have hlt4 : ((c / 4 : ℝ) : ℝ*) < ((c - c / 2 : ℝ) : ℝ*) :=
      Hyperreal.coe_lt_coe.2 (by linarith)
    exact (hlt4.trans hgt).trans_le htri
  · have htri : |y| ≤ |x| + |y - x| := by
      have : y = x + (y - x) := by ring
      conv_lhs => rw [this]
      exact abs_add_le x (y - x)
    have hlt_sum : |x| + |y - x| < ((d + c / 2 : ℝ) : ℝ*) := by
      rw [Hyperreal.coe_add]
      exact add_lt_add hxd hy
    exact htri.trans_lt hlt_sum

/-- Goldblatt §10.5 Example 6 (p. 120): The set of positive appreciable hyperreals is real-open. -/
theorem isRealOpen_posAppreciable : IsRealOpen {x : ℝ* | IsAppreciable x ∧ 0 < x} := by
  refine isRealOpen_of_forall_centered fun x ⟨hx_app, hx_pos⟩ ↦ ?_
  obtain ⟨c, d, hc_pos, hcx, hxd⟩ := isAppreciable_iff_pos_real_bounds.1 hx_app
  rw [abs_of_pos hx_pos] at hcx hxd
  refine ⟨c / 2, half_pos hc_pos, fun y hy ↦ ?_⟩
  have hy_gt : ((c / 2 : ℝ) : ℝ*) < y := by
    have h1 : x - ((c / 2 : ℝ) : ℝ*) < y := hy.1
    have h2 : ((c / 2 : ℝ) : ℝ*) = (c : ℝ*) - ((c / 2 : ℝ) : ℝ*) := by
      rw [← Hyperreal.coe_sub]
      ring_nf
    linarith
  have hy_pos : 0 < y := (Hyperreal.coe_pos.2 (half_pos hc_pos)).trans hy_gt
  have hy_lt : y < ((d + c / 2 : ℝ) : ℝ*) := by
    rw [Hyperreal.coe_add]
    exact hy.2.trans (add_lt_add_left hxd _)
  refine ⟨isAppreciable_iff_pos_real_bounds.2 ⟨c / 4, d + c / 2, by positivity, ?_, ?_⟩, hy_pos⟩
  · rw [abs_of_pos hy_pos]
    exact (Hyperreal.coe_lt_coe.2 (by linarith)).trans hy_gt
  · rwa [abs_of_pos hy_pos]

/-- Goldblatt §10.5 Example 7 (p. 120): The set of negative appreciable hyperreals is real-open. -/
theorem isRealOpen_negAppreciable : IsRealOpen {x : ℝ* | IsAppreciable x ∧ x < 0} := by
  refine isRealOpen_of_forall_centered fun x ⟨hx_app, hx_neg⟩ ↦ ?_
  obtain ⟨c, d, hc_pos, hcx, hxd⟩ := isAppreciable_iff_pos_real_bounds.1 hx_app
  rw [abs_of_neg hx_neg] at hcx hxd
  refine ⟨c / 2, half_pos hc_pos, fun y hy ↦ ?_⟩
  have hy_lt : y < -((c / 2 : ℝ) : ℝ*) := by
    have h1 : y < x + ((c / 2 : ℝ) : ℝ*) := hy.2
    have h2 : (c : ℝ*) - ((c / 2 : ℝ) : ℝ*) = ((c / 2 : ℝ) : ℝ*) := by
      rw [← Hyperreal.coe_sub]
      ring_nf
    linarith
  have hy_neg : y < 0 := hy_lt.trans (neg_lt_zero.2 (Hyperreal.coe_pos.2 (half_pos hc_pos)))
  have hy_gt : -((d + c / 2 : ℝ) : ℝ*) < y := by
    have h1 : x - ((c / 2 : ℝ) : ℝ*) < y := hy.1
    rw [Hyperreal.coe_add]
    linarith
  refine ⟨isAppreciable_iff_pos_real_bounds.2 ⟨c / 4, d + c / 2, by positivity, ?_, ?_⟩, hy_neg⟩
  · rw [abs_of_neg hy_neg]
    have h4 : ((c / 4 : ℝ) : ℝ*) < ((c / 2 : ℝ) : ℝ*) := Hyperreal.coe_lt_coe.2 (by linarith)
    linarith
  · rw [abs_of_neg hy_neg]
    linarith

/-- Goldblatt §10.5 Example 8 (p. 120): Every galaxy `galaxy b` is real-open. -/
theorem isRealOpen_galaxy (b : ℝ*) : IsRealOpen (galaxy b) := by
  refine isRealOpen_of_forall_centered fun x hx ↦ ⟨1, one_pos, fun y hy ↦ ?_⟩
  rw [mem_realRadiusNhds_iff_abs] at hy
  have hxy : x ∼ₗ y := ⟨1, by rw [abs_sub_comm]; simpa using hy⟩
  exact hx.trans hxy

/-! ### Failure of Finite Intersections for Real-Open Sets -/

/-- No nonempty subset of `ℝ*` of infinitesimal diameter can be real-open, since every positive
real-radius neighbourhood has appreciable width. -/
theorem not_isRealOpen_of_infinitesimal_diam {A : Set ℝ*} (hAne : A.Nonempty)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, x ≈ₕ y) :
    ¬ IsRealOpen A := by
  intro hopen
  obtain ⟨x₀, hx₀⟩ := hAne
  obtain ⟨r, ε, hε, _, hsub⟩ := (isRealOpen_iff.1 hopen) x₀ hx₀
  let u : ℝ* := r - ((ε / 2 : ℝ) : ℝ*)
  let v : ℝ* := r + ((ε / 2 : ℝ) : ℝ*)
  have hu : u ∈ A := by
    apply hsub
    rw [mem_realRadiusNhds_iff_abs]
    have h1 : u - r = -((ε / 2 : ℝ) : ℝ*) := by ring
    rw [h1, abs_neg, abs_of_pos (Hyperreal.coe_pos.2 (half_pos hε))]
    exact Hyperreal.coe_lt_coe.2 (half_lt_self hε)
  have hv : v ∈ A := by
    apply hsub
    rw [mem_realRadiusNhds_iff_abs]
    have h1 : v - r = ((ε / 2 : ℝ) : ℝ*) := by ring
    rw [h1, abs_of_pos (Hyperreal.coe_pos.2 (half_pos hε))]
    exact Hyperreal.coe_lt_coe.2 (half_lt_self hε)
  have hclose : v ≈ₕ u := hdiam v hv u hu
  have hdiff : v - u = (ε : ℝ*) := by
    change (r + ((ε / 2 : ℝ) : ℝ*)) - (r - ((ε / 2 : ℝ) : ℝ*)) = (ε : ℝ*)
    have hsum : ((ε / 2 : ℝ) : ℝ*) + ((ε / 2 : ℝ) : ℝ*) = (ε : ℝ*) := by
      rw [← Hyperreal.coe_add, add_halves]
    linarith
  have hinf : IsInfinitesimal (ε : ℝ*) := by
    rw [← hdiff]
    exact hclose
  exact hε.ne' (isInfinitesimal_coe_iff.1 hinf)

/-- Goldblatt §10.5 (p. 121): No halo `halo b` is real-open. -/
theorem not_isRealOpen_halo (b : ℝ*) : ¬ IsRealOpen (halo b) :=
  not_isRealOpen_of_infinitesimal_diam ⟨b, self_mem_halo b⟩ fun _ hx _ hy ↦ hx.symm.trans hy

/-- Goldblatt §10.5 (p. 121): Any nonempty hyperreal open interval `(a, b)` with `a ≈ₕ b` fails
to be real-open. -/
theorem not_isRealOpen_Ioo_of_infClose {a b : ℝ*} (hab : a < b) (hclose : a ≈ₕ b) :
    ¬ IsRealOpen (Set.Ioo a b) := by
  refine not_isRealOpen_of_infinitesimal_diam ⟨(a + b) / 2, by linarith, by linarith⟩ ?_
  intro x hx y hy
  refine isInfinitesimal_of_abs_le hclose.symm ?_
  have hba : 0 < b - a := sub_pos.2 hab
  rw [abs_of_pos hba, abs_le]
  exact ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩

/-- **Goldblatt §10.5** (p. 120): The class of real-open sets is NOT closed under binary
intersections (hence is not a topology on `ℝ*`): `(-1, 1)` and `(1 - ε, 3 - ε)` are both
real-open, yet their intersection `(1 - ε, 1)` has infinitesimal width `ε` and is not real-open! -/
theorem exists_isRealOpen_not_isRealOpen_inter :
    ∃ U V : Set ℝ*, IsRealOpen U ∧ IsRealOpen V ∧ ¬ IsRealOpen (U ∩ V) := by
  refine ⟨realRadiusNhds 0 1, realRadiusNhds (2 - Hyperreal.epsilon) 1,
    isRealOpen_realRadiusNhds 0 one_pos,
    isRealOpen_realRadiusNhds (2 - Hyperreal.epsilon) one_pos, ?_⟩
  have heps_pos : (0 : ℝ*) < Hyperreal.epsilon := Hyperreal.epsilon_pos
  have heps_lt1 : Hyperreal.epsilon < 1 := by
    simpa using Hyperreal.epsilon_lt_of_pos one_pos
  have hinter : realRadiusNhds 0 1 ∩ realRadiusNhds (2 - Hyperreal.epsilon) 1 =
      Set.Ioo (1 - Hyperreal.epsilon) 1 := by
    ext x
    simp only [realRadiusNhds, Hyperreal.coe_one, Set.mem_inter_iff, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨_, hx2⟩, ⟨hx3, _⟩⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  rw [hinter]
  refine not_isRealOpen_Ioo_of_infClose (by linarith) ?_
  change IsInfinitesimal ((1 - Hyperreal.epsilon) - 1)
  simpa using isInfinitesimal_epsilon.neg

/-! ### S-Neighbourhoods, S-Open Sets, Robinson's S-Topology, and Exercise 10.5.1 -/

/-- Goldblatt §10.5 (p. 120): The *S-neighbourhood* `((r - ε, r + ε)) = {x ∈ ℝ* | hal(x) ⊆ (r - ε, r + ε)}`
consisting of points well inside the real-radius neighbourhood `(r - ε, r + ε)`. -/
def sNhds (r : ℝ*) (ε : ℝ) : Set ℝ* :=
  {x : ℝ* | halo x ⊆ realRadiusNhds r ε}

/-- When `ε ≤ 0`, `sNhds r ε` is empty. -/
theorem sNhds_of_nonpos (r : ℝ*) {ε : ℝ} (hε : ε ≤ 0) : sNhds r ε = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hxr : x ∈ realRadiusNhds r ε := hx (self_mem_halo x)
  rw [mem_realRadiusNhds_iff_abs] at hxr
  have hle : (ε : ℝ*) ≤ 0 := Hyperreal.coe_le_coe.2 hε
  exact lt_irrefl (0 : ℝ*) ((abs_nonneg (x - r)).trans_lt (hxr.trans_le hle))

/-- **Goldblatt §10.5** (p. 121): For `ε > 0`, `x ∈ ((r - ε, r + ε))` if and only if `r - x` is
limited and `sh(|r - x|) < ε`. -/
theorem mem_sNhds_iff_shadow {r x : ℝ*} {ε : ℝ} (hε : 0 < ε) :
    x ∈ sNhds r ε ↔ IsLimited (r - x) ∧ shadow |r - x| < ε := by
  constructor
  · intro hx
    have hself : |x - r| < (ε : ℝ*) := mem_realRadiusNhds_iff_abs.1 (hx (self_mem_halo x))
    rw [abs_sub_comm] at hself
    have hlim : IsLimited (r - x) :=
      isLimited_iff_abs_le_real.2 ⟨ε, hε.le, hself.le⟩
    have hsh_le : shadow |r - x| ≤ ε := by
      simpa using shadow_le_of_le hlim.abs (isLimited_coe ε) hself.le
    refine ⟨hlim, hsh_le.lt_of_ne ?_⟩
    intro hsh_eq
    have hclose : |r - x| ≈ₕ (ε : ℝ*) := by
      have := infClose_shadow hlim.abs
      rwa [hsh_eq] at this
    rcases le_or_gt r x with hrx | hxr
    · have habs : |r - x| = x - r := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hrx)]
      rw [habs] at hclose
      let y : ℝ* := r + (ε : ℝ*)
      have hy_halo : y ∈ halo x := by
        change IsInfinitesimal (x - (r + (ε : ℝ*)))
        have : x - (r + (ε : ℝ*)) = (x - r) - (ε : ℝ*) := by ring
        rw [this]
        exact hclose
      have hy_in := mem_realRadiusNhds_iff_abs.1 (hx hy_halo)
      have hy_eq : |y - r| = (ε : ℝ*) := by
        change |(r + (ε : ℝ*)) - r| = (ε : ℝ*)
        rw [add_sub_cancel_left, abs_of_pos (Hyperreal.coe_pos.2 hε)]
      rw [hy_eq] at hy_in
      exact lt_irrefl _ hy_in
    · have habs : |r - x| = r - x := abs_of_pos (sub_pos.2 hxr)
      rw [habs] at hclose
      let y : ℝ* := r - (ε : ℝ*)
      have hy_halo : y ∈ halo x := by
        change IsInfinitesimal (x - (r - (ε : ℝ*)))
        have : x - (r - (ε : ℝ*)) = -((r - x) - (ε : ℝ*)) := by ring
        rw [this]
        exact IsInfinitesimal.neg hclose
      have hy_in := mem_realRadiusNhds_iff_abs.1 (hx hy_halo)
      have hy_eq : |y - r| = (ε : ℝ*) := by
        change |(r - (ε : ℝ*)) - r| = (ε : ℝ*)
        rw [sub_sub_cancel_left, abs_neg, abs_of_pos (Hyperreal.coe_pos.2 hε)]
      rw [hy_eq] at hy_in
      exact lt_irrefl _ hy_in
  · rintro ⟨hlim, hsh_lt⟩ y hy_halo
    rw [mem_realRadiusNhds_iff_abs, abs_sub_comm]
    set η : ℝ := (ε - shadow |r - x|) / 2
    have hη : 0 < η := by positivity
    have h1 : |(|r - x| - (shadow |r - x| : ℝ*))| < (η : ℝ*) :=
      infClose_shadow hlim.abs η hη
    have h2 : |x - y| < (η : ℝ*) := hy_halo η hη
    have hrx_lt : |r - x| < (shadow |r - x| : ℝ*) + (η : ℝ*) := by
      linarith [(abs_lt.1 h1).2]
    have htri : |r - y| ≤ |r - x| + |x - y| := by
      have : r - y = (r - x) + (x - y) := by ring
      rw [this]
      exact abs_add_le (r - x) (x - y)
    have hsum : (shadow |r - x| : ℝ*) + (η : ℝ*) + (η : ℝ*) = (ε : ℝ*) := by
      have : shadow |r - x| + η + η = ε := by linarith [show η = (ε - shadow |r - x|) / 2 from rfl]
      exact_mod_cast this
    calc |r - y|
        ≤ |r - x| + |x - y| := htri
      _ < ((shadow |r - x| : ℝ*) + (η : ℝ*)) + (η : ℝ*) := add_lt_add hrx_lt h2
      _ = (ε : ℝ*) := hsum

/-- **Goldblatt §10.5** (p. 121): Equivalently, `x ∈ ((r - ε, r + ε))` (for `ε > 0`) iff
`|r - x| < ε` and `ε - |r - x|` is appreciable. -/
theorem mem_sNhds_iff_appreciable {r x : ℝ*} {ε : ℝ} (hε : 0 < ε) :
    x ∈ sNhds r ε ↔ |r - x| < (ε : ℝ*) ∧ IsAppreciable ((ε : ℝ*) - |r - x|) := by
  rw [mem_sNhds_iff_shadow hε]
  constructor
  · rintro ⟨hlim, hsh_lt⟩
    have hlt : |r - x| < (ε : ℝ*) := by
      by_contra hge
      push Not at hge
      have hle_sh : ε ≤ shadow |r - x| := by
        simpa using shadow_le_of_le (isLimited_coe ε) hlim.abs hge
      linarith
    refine ⟨hlt, (isLimited_coe ε).sub hlim.abs, ?_⟩
    intro hinf
    have hclose : |r - x| ≈ₕ (ε : ℝ*) := by
      change IsInfinitesimal (|r - x| - (ε : ℝ*))
      have : |r - x| - (ε : ℝ*) = -((ε : ℝ*) - |r - x|) := by ring
      rw [this]
      exact hinf.neg
    have hsh_eq : shadow |r - x| = ε := shadow_eq_of_infClose hclose
    linarith
  · rintro ⟨hlt, happ⟩
    have hlim : IsLimited (r - x) :=
      isLimited_iff_abs_le_real.2 ⟨ε, hε.le, hlt.le⟩
    have hsh_le : shadow |r - x| ≤ ε := by
      simpa using shadow_le_of_le hlim.abs (isLimited_coe ε) hlt.le
    refine ⟨hlim, hsh_le.lt_of_ne ?_⟩
    intro hsh_eq
    apply happ.2
    have hclose : |r - x| ≈ₕ (ε : ℝ*) := by
      have := infClose_shadow hlim.abs
      rwa [hsh_eq] at this
    have : (ε : ℝ*) - |r - x| = -(|r - x| - (ε : ℝ*)) := by ring
    rw [this]
    exact IsInfinitesimal.neg hclose

/-- When `0 < ε`, `r ∈ sNhds r ε`. -/
theorem self_mem_sNhds (r : ℝ*) {ε : ℝ} (hε : 0 < ε) : r ∈ sNhds r ε := by
  rw [mem_sNhds_iff_shadow hε, sub_self, abs_zero, shadow_zero]
  exact ⟨isLimited_coe 0, hε⟩

/-- **Goldblatt §10.5** (p. 121): If `t ∈ ((r - ε, r + ε))` (`ε > 0`) and
`0 < γ ≤ ε - sh(|r - t|)`, then `((t - γ, t + γ)) ⊆ ((r - ε, r + ε))`. -/
theorem sNhds_subset_sNhds {r t : ℝ*} {ε γ : ℝ} (hε : 0 < ε)
    (ht : t ∈ sNhds r ε) (hγ_pos : 0 < γ) (hγ_le : γ ≤ ε - shadow |r - t|) :
    sNhds t γ ⊆ sNhds r ε := by
  obtain ⟨hlim_rt, _⟩ := (mem_sNhds_iff_shadow hε).1 ht
  intro y hy
  obtain ⟨hlim_ty, hsh_ty⟩ := (mem_sNhds_iff_shadow hγ_pos).1 hy
  rw [mem_sNhds_iff_shadow hε]
  have hlim_ry : IsLimited (r - y) := by
    have : r - y = (r - t) + (t - y) := by ring
    rw [this]
    exact hlim_rt.add hlim_ty
  refine ⟨hlim_ry, ?_⟩
  have htri : |r - y| ≤ |r - t| + |t - y| := by
    have : r - y = (r - t) + (t - y) := by ring
    rw [this]
    exact abs_add_le (r - t) (t - y)
  have hsh_tri : shadow |r - y| ≤ shadow |r - t| + shadow |t - y| := by
    calc shadow |r - y|
        ≤ shadow (|r - t| + |t - y|) :=
          shadow_le_of_le hlim_ry.abs (hlim_rt.abs.add hlim_ty.abs) htri
      _ = shadow |r - t| + shadow |t - y| := shadow_add hlim_rt.abs hlim_ty.abs
  linarith

/-- **Goldblatt §10.5** (p. 121): Explicit formula for an S-neighbourhood inside the intersection
of two S-neighbourhoods `((r - ε, r + ε)) ∩ ((s - δ, s + δ))` using
`0 < γ ≤ min (ε - sh(|r - t|)) (δ - sh(|s - t|))`. -/
theorem sNhds_subset_inter_sNhds {r s t : ℝ*} {ε δ γ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (ht : t ∈ sNhds r ε ∩ sNhds s δ)
    (hγ_pos : 0 < γ)
    (hγ_le : γ ≤ min (ε - shadow |r - t|) (δ - shadow |s - t|)) :
    sNhds t γ ⊆ sNhds r ε ∩ sNhds s δ :=
  Set.subset_inter
    (sNhds_subset_sNhds hε ht.1 hγ_pos (hγ_le.trans (min_le_left _ _)))
    (sNhds_subset_sNhds hδ ht.2 hγ_pos (hγ_le.trans (min_le_right _ _)))

/-- Goldblatt §10.5 (p. 120): A subset `A ⊆ ℝ*` is *S-open* if it is a union of S-neighbourhoods. -/
def IsSOpen (A : Set ℝ*) : Prop :=
  ∃ S : Set (Set ℝ*), (∀ U ∈ S, ∃ (r : ℝ*) (ε : ℝ), 0 < ε ∧ U = sNhds r ε) ∧ A = ⋃₀ S

/-- Centered S-neighbourhood characterization of `IsSOpen`: unlike `IsRealOpen`, `A ⊆ ℝ*` is S-open
iff every `x ∈ A` admits a real `γ > 0` with `sNhds x γ ⊆ A`! -/
theorem isSOpen_iff {A : Set ℝ*} :
    IsSOpen A ↔ ∀ x ∈ A, ∃ γ : ℝ, 0 < γ ∧ sNhds x γ ⊆ A := by
  constructor
  · rintro ⟨S, hS, rfl⟩ x ⟨U, hUS, hxU⟩
    obtain ⟨r, ε, hε, rfl⟩ := hS U hUS
    obtain ⟨_, hsh⟩ := (mem_sNhds_iff_shadow hε).1 hxU
    refine ⟨ε - shadow |r - x|, sub_pos.2 hsh, ?_⟩
    exact (sNhds_subset_sNhds hε hxU (sub_pos.2 hsh) le_rfl).trans (Set.subset_sUnion_of_mem hUS)
  · intro h
    refine ⟨{U : Set ℝ* | ∃ (x : ℝ*) (γ : ℝ), 0 < γ ∧ U = sNhds x γ ∧ U ⊆ A}, ?_, ?_⟩
    · rintro U ⟨x, γ, hγ, hU, _⟩
      exact ⟨x, γ, hγ, hU⟩
    · apply Set.Subset.antisymm
      · intro x hxA
        obtain ⟨γ, hγ, hsub⟩ := h x hxA
        exact ⟨sNhds x γ, ⟨x, γ, hγ, rfl, hsub⟩, self_mem_sNhds x hγ⟩
      · rintro x ⟨U, ⟨_, _, _, _, hUA⟩, hxU⟩
        exact hUA hxU

/-- Every S-neighbourhood `sNhds r ε` (for any `ε : ℝ`) is S-open. -/
theorem isSOpen_sNhds (r : ℝ*) (ε : ℝ) : IsSOpen (sNhds r ε) := by
  rcases le_or_gt ε 0 with hle | hgt
  · rw [sNhds_of_nonpos r hle]
    exact ⟨∅, by simp, Set.sUnion_empty.symm⟩
  · exact ⟨{sNhds r ε}, fun _ hU ↦ ⟨r, ε, hgt, hU⟩, (Set.sUnion_singleton _).symm⟩

/-- **Goldblatt §10.5** (p. 121): The intersection of two S-open sets is S-open. -/
theorem isSOpen_inter {A B : Set ℝ*} (hA : IsSOpen A) (hB : IsSOpen B) :
    IsSOpen (A ∩ B) := by
  rw [isSOpen_iff] at hA hB ⊢
  rintro x ⟨hxA, hxB⟩
  obtain ⟨ε, hε, hsubA⟩ := hA x hxA
  obtain ⟨δ, hδ, hsubB⟩ := hB x hxB
  refine ⟨min ε δ, lt_min hε hδ, fun y hy ↦ ⟨hsubA ?_, hsubB ?_⟩⟩
  · exact sNhds_subset_sNhds hε (self_mem_sNhds x hε) (lt_min hε hδ)
      (by simp [sub_self, abs_zero, shadow_zero]) hy
  · exact sNhds_subset_sNhds hδ (self_mem_sNhds x hδ) (lt_min hε hδ)
      (by simp [sub_self, abs_zero, shadow_zero]) hy

/-- **Goldblatt §10.5** (p. 120): Abraham Robinson's *S-topology* on `ℝ*`, whose open sets are
precisely `IsSOpen`. -/
@[instance_reducible]
def sTopology : TopologicalSpace ℝ* where
  IsOpen := IsSOpen
  isOpen_univ := isSOpen_iff.2 fun _ _ ↦ ⟨1, one_pos, Set.subset_univ _⟩
  isOpen_inter _ _ := isSOpen_inter
  isOpen_sUnion F hF := by
    rw [isSOpen_iff]
    rintro x ⟨A, hAF, hxA⟩
    obtain ⟨γ, hγ, hsub⟩ := (isSOpen_iff.1 (hF A hAF)) x hxA
    exact ⟨γ, hγ, hsub.trans (Set.subset_sUnion_of_mem hAF)⟩

/-- Openness in `sTopology` is definitionally `IsSOpen`. -/
@[simp]
theorem isOpen_sTopology_iff {A : Set ℝ*} : IsOpen[sTopology] A ↔ IsSOpen A := Iff.rfl

/-- **Goldblatt Exercise 10.5.1(i)** (p. 121): Every S-open set is real-open. -/
theorem IsSOpen.isRealOpen {A : Set ℝ*} (hA : IsSOpen A) : IsRealOpen A := by
  refine isRealOpen_of_forall_centered fun x hxA ↦ ?_
  obtain ⟨ε, hε, hsub⟩ := (isSOpen_iff.1 hA) x hxA
  refine ⟨ε / 2, half_pos hε, fun y hy ↦ hsub ?_⟩
  rw [mem_realRadiusNhds_iff_abs, abs_sub_comm] at hy
  have hlim : IsLimited (x - y) :=
    isLimited_iff_abs_le_real.2 ⟨ε / 2, (half_pos hε).le, hy.le⟩
  have hsh : shadow |x - y| ≤ ε / 2 := by
    rw [← shadow_coe (ε / 2)]
    exact shadow_le_of_le hlim.abs (isLimited_coe (ε / 2)) hy.le
  exact (mem_sNhds_iff_shadow hε).2 ⟨hlim, hsh.trans_lt (half_lt_self hε)⟩

/-- **Goldblatt Exercise 10.5.1(ii, part 1)** (p. 121): Every S-open set contains the halo of each
of its points, and so is a union of halos (`A = ⋃ x ∈ A, hal(x)`). -/
theorem IsSOpen.halo_subset {A : Set ℝ*} (hA : IsSOpen A) {x : ℝ*} (hxA : x ∈ A) :
    halo x ⊆ A := by
  obtain ⟨ε, hε, hsub⟩ := (isSOpen_iff.1 hA) x hxA
  intro y hy
  apply hsub
  change halo y ⊆ realRadiusNhds x ε
  rw [halo_eq_of_infClose hy.symm]
  exact self_mem_sNhds x hε

/-- Union-of-halos equation for S-open sets (**Goldblatt Exercise 10.5.1(ii)**, p. 121). -/
theorem IsSOpen.eq_biUnion_halo {A : Set ℝ*} (hA : IsSOpen A) :
    A = ⋃ x ∈ A, halo x := by
  apply Set.Subset.antisymm
  · intro x hxA
    exact Set.mem_biUnion hxA (self_mem_halo x)
  · exact Set.iUnion₂_subset fun x hxA ↦ hA.halo_subset hxA

/-- No halo `halo b` is S-open. -/
theorem not_isSOpen_halo (b : ℝ*) : ¬ IsSOpen (halo b) :=
  fun h ↦ not_isRealOpen_halo b h.isRealOpen

/-- **Goldblatt Exercise 10.5.1(ii, part 2)** (p. 121): A union of halos need NOT be S-open
(witnessed by `halo 0`). -/
theorem exists_union_halos_not_isSOpen :
    ∃ A : Set ℝ*, (A = ⋃ x ∈ A, halo x) ∧ ¬ IsSOpen A := by
  refine ⟨halo 0, ?_, not_isSOpen_halo 0⟩
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_biUnion hx (self_mem_halo x)
  · refine Set.iUnion₂_subset fun x hx y hy ↦ ?_
    exact hx.trans hy

/-- **Goldblatt Exercise 10.5.1(iii)** (p. 121): No positive real-radius neighbourhood
`(r - ε, r + ε)` (`ε > 0` in `ℝ`) can be S-open! -/
theorem not_isSOpen_realRadiusNhds (r : ℝ*) {ε : ℝ} (hε : 0 < ε) :
    ¬ IsSOpen (realRadiusNhds r ε) := by
  intro hS
  let x : ℝ* := r + (ε : ℝ*) - Hyperreal.epsilon
  have heps_pos : (0 : ℝ*) < Hyperreal.epsilon := Hyperreal.epsilon_pos
  have heps_lt : Hyperreal.epsilon < (ε : ℝ*) := Hyperreal.epsilon_lt_of_pos hε
  have hx_mem : x ∈ realRadiusNhds r ε := by
    rw [mem_realRadiusNhds_iff_abs]
    have hdiff : x - r = (ε : ℝ*) - Hyperreal.epsilon := by ring
    rw [hdiff, abs_of_pos (sub_pos.2 heps_lt)]
    linarith
  have hy_halo : r + (ε : ℝ*) ∈ halo x := by
    change IsInfinitesimal (x - (r + (ε : ℝ*)))
    have : x - (r + (ε : ℝ*)) = -Hyperreal.epsilon := by ring
    rw [this]
    exact isInfinitesimal_epsilon.neg
  have hy_in : r + (ε : ℝ*) ∈ realRadiusNhds r ε := hS.halo_subset hx_mem hy_halo
  rw [mem_realRadiusNhds_iff_abs, add_sub_cancel_left,
      abs_of_pos (Hyperreal.coe_pos.2 hε)] at hy_in
  exact lt_irrefl _ hy_in

/-! ### Interval-Open Sets, the Interval Topology, Clopen Halos/Galaxies, and Disconnectedness -/

/-- Goldblatt §10.5 (p. 121): A subset `A ⊆ ℝ*` is *interval-open* if it is a union of hyperreal
open intervals `(a, b) ⊆ ℝ*`. -/
def IsIntervalOpen (A : Set ℝ*) : Prop :=
  ∃ S : Set (Set ℝ*), (∀ U ∈ S, ∃ a b : ℝ*, U = Set.Ioo a b) ∧ A = ⋃₀ S

/-- Pointwise interval characterization of `IsIntervalOpen`. -/
theorem isIntervalOpen_iff {A : Set ℝ*} :
    IsIntervalOpen A ↔ ∀ x ∈ A, ∃ a b : ℝ*, x ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ A := by
  constructor
  · rintro ⟨S, hS, rfl⟩ x ⟨U, hUS, hxU⟩
    obtain ⟨a, b, rfl⟩ := hS U hUS
    exact ⟨a, b, hxU, Set.subset_sUnion_of_mem hUS⟩
  · intro h
    refine ⟨{U : Set ℝ* | ∃ a b : ℝ*, U = Set.Ioo a b ∧ U ⊆ A}, ?_, ?_⟩
    · rintro U ⟨a, b, hU, _⟩
      exact ⟨a, b, hU⟩
    · apply Set.Subset.antisymm
      · intro x hxA
        obtain ⟨a, b, hxab, hsub⟩ := h x hxA
        exact ⟨Set.Ioo a b, ⟨a, b, rfl, hsub⟩, hxab⟩
      · rintro x ⟨U, ⟨_, _, _, hUA⟩, hxU⟩
        exact hUA hxU

/-- Symmetric hyperreal-radius characterization of `IsIntervalOpen`: `A` is interval-open iff every
`x ∈ A` admits a positive hyperreal `δ > 0` (possibly infinitesimal!) with `(x - δ, x + δ) ⊆ A`. -/
theorem isIntervalOpen_iff_symm_radius {A : Set ℝ*} :
    IsIntervalOpen A ↔ ∀ x ∈ A, ∃ δ : ℝ*, 0 < δ ∧ Set.Ioo (x - δ) (x + δ) ⊆ A := by
  rw [isIntervalOpen_iff]
  constructor
  · intro h x hxA
    obtain ⟨a, b, ⟨hax, hxb⟩, hsub⟩ := h x hxA
    refine ⟨min (x - a) (b - x), lt_min (sub_pos.2 hax) (sub_pos.2 hxb), fun y hy ↦ hsub ?_⟩
    have h1 : min (x - a) (b - x) ≤ x - a := min_le_left _ _
    have h2 : min (x - a) (b - x) ≤ b - x := min_le_right _ _
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · intro h x hxA
    obtain ⟨δ, hδ, hsub⟩ := h x hxA
    exact ⟨x - δ, x + δ, ⟨by linarith, by linarith⟩, hsub⟩

/-- Every hyperreal open interval `(a, b)` is interval-open. -/
theorem isIntervalOpen_Ioo (a b : ℝ*) : IsIntervalOpen (Set.Ioo a b) :=
  ⟨{Set.Ioo a b}, fun _ hU ↦ ⟨a, b, hU⟩, (Set.sUnion_singleton _).symm⟩

/-- **Goldblatt §10.5** (p. 121): Every real-open set is interval-open. -/
theorem IsRealOpen.isIntervalOpen {A : Set ℝ*} (hA : IsRealOpen A) : IsIntervalOpen A := by
  rw [isIntervalOpen_iff]
  intro x hxA
  obtain ⟨r, ε, _, hxr, hsub⟩ := (isRealOpen_iff.1 hA) x hxA
  exact ⟨r - (ε : ℝ*), r + (ε : ℝ*), hxr, hsub⟩

/-- Binary intersection of interval-open sets is interval-open. -/
theorem isIntervalOpen_inter {A B : Set ℝ*} (hA : IsIntervalOpen A) (hB : IsIntervalOpen B) :
    IsIntervalOpen (A ∩ B) := by
  rw [isIntervalOpen_iff_symm_radius] at hA hB ⊢
  rintro x ⟨hxA, hxB⟩
  obtain ⟨δ₁, hδ₁, hsubA⟩ := hA x hxA
  obtain ⟨δ₂, hδ₂, hsubB⟩ := hB x hxB
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy ↦ ⟨hsubA ?_, hsubB ?_⟩⟩
  · have : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · have : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- **Goldblatt §10.5** (p. 121): The *interval topology* on `ℝ*`, whose open sets are `IsIntervalOpen`. -/
@[instance_reducible]
def intervalTopology : TopologicalSpace ℝ* where
  IsOpen := IsIntervalOpen
  isOpen_univ := isIntervalOpen_iff_symm_radius.2 fun _ _ ↦ ⟨1, one_pos, Set.subset_univ _⟩
  isOpen_inter _ _ := isIntervalOpen_inter
  isOpen_sUnion F hF := by
    rw [isIntervalOpen_iff]
    rintro x ⟨A, hAF, hxA⟩
    obtain ⟨a, b, hxab, hsub⟩ := (isIntervalOpen_iff.1 (hF A hAF)) x hxA
    exact ⟨a, b, hxab, hsub.trans (Set.subset_sUnion_of_mem hAF)⟩

/-- Openness in `intervalTopology` is definitionally `IsIntervalOpen`. -/
@[simp]
theorem isOpen_intervalTopology_iff {A : Set ℝ*} :
    IsOpen[intervalTopology] A ↔ IsIntervalOpen A := Iff.rfl

/-- `intervalTopology` coincides with Mathlib's order topology `Preorder.topology ℝ*` on the
linearly ordered field `ℝ*`. -/
theorem intervalTopology_eq_preorderTopology :
    intervalTopology = Preorder.topology ℝ* := by
  have hIoi : ∀ a : ℝ*, IsIntervalOpen (Set.Ioi a) := by
    intro a
    rw [isIntervalOpen_iff]
    intro x hax
    exact ⟨a, x + 1, ⟨hax, lt_add_one x⟩, fun y hy ↦ hy.1⟩
  have hIio : ∀ b : ℝ*, IsIntervalOpen (Set.Iio b) := by
    intro b
    rw [isIntervalOpen_iff]
    intro x hxb
    exact ⟨x - 1, b, ⟨sub_lt_self x one_pos, hxb⟩, fun y hy ↦ hy.2⟩
  have hgen_le : ∀ s : Set ℝ*,
      TopologicalSpace.GenerateOpen {t : Set ℝ* | ∃ a : ℝ*, t = Set.Ioi a ∨ t = Set.Iio a} s →
        IsIntervalOpen s := by
    intro s hs
    induction hs with
    | basic t ht =>
        rcases ht with ⟨a, rfl | rfl⟩
        · exact hIoi a
        · exact hIio a
    | univ => exact intervalTopology.isOpen_univ
    | inter u v _ _ ihu ihv => exact isIntervalOpen_inter ihu ihv
    | sUnion S _ ihS => exact intervalTopology.isOpen_sUnion S ihS
  have hint_le : ∀ s : Set ℝ*, IsIntervalOpen s →
      TopologicalSpace.GenerateOpen {t : Set ℝ* | ∃ a : ℝ*, t = Set.Ioi a ∨ t = Set.Iio a} s := by
    rintro s ⟨S, hS, rfl⟩
    refine TopologicalSpace.GenerateOpen.sUnion S fun U hUS ↦ ?_
    obtain ⟨a, b, rfl⟩ := hS U hUS
    rw [← Set.Ioi_inter_Iio]
    exact TopologicalSpace.GenerateOpen.inter _ _
      (TopologicalSpace.GenerateOpen.basic _ ⟨a, Or.inl rfl⟩)
      (TopologicalSpace.GenerateOpen.basic _ ⟨b, Or.inr rfl⟩)
  unfold intervalTopology Preorder.topology TopologicalSpace.generateFrom
  have heq : IsIntervalOpen =
      TopologicalSpace.GenerateOpen {t : Set ℝ* | ∃ a : ℝ*, t = Set.Ioi a ∨ t = Set.Iio a} :=
    funext fun s ↦ propext ⟨hint_le s, hgen_le s⟩
  congr!

/-- **Goldblatt §10.5** (p. 121): Every halo `halo b` is open in the interval topology on `ℝ*`! -/
theorem isIntervalOpen_halo (b : ℝ*) : IsIntervalOpen (halo b) := by
  rw [isIntervalOpen_iff_symm_radius]
  intro x hx
  refine ⟨Hyperreal.epsilon, Hyperreal.epsilon_pos, fun y hy ↦ ?_⟩
  have hxy : x ≈ₕ y := by
    refine isInfinitesimal_of_abs_le isInfinitesimal_epsilon ?_
    rw [abs_of_pos Hyperreal.epsilon_pos, abs_le]
    exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
  exact hx.trans hxy

/-- Every halo complement `(halo b)ᶜ` is ALSO open in the interval topology on `ℝ*`! -/
theorem isIntervalOpen_compl_halo (b : ℝ*) : IsIntervalOpen (halo b)ᶜ := by
  rw [isIntervalOpen_iff_symm_radius]
  intro x hx
  change ¬ (b ≈ₕ x) at hx
  unfold InfClose IsInfinitesimal at hx
  push Not at hx
  obtain ⟨r, hr_pos, hge⟩ := hx
  refine ⟨((r / 2 : ℝ) : ℝ*), Hyperreal.coe_pos.2 (half_pos hr_pos), fun y hy hy_halo ↦ ?_⟩
  have hxy : |x - y| < ((r / 2 : ℝ) : ℝ*) :=
    abs_lt.2 ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hby : |b - y| < ((r / 2 : ℝ) : ℝ*) := hy_halo (r / 2) (half_pos hr_pos)
  have htri : |b - x| ≤ |b - y| + |x - y| := by
    have : b - x = (b - y) + (y - x) := by ring
    rw [this, abs_sub_comm x y]
    exact abs_add_le (b - y) (y - x)
  have hsum : ((r / 2 : ℝ) : ℝ*) + ((r / 2 : ℝ) : ℝ*) = (r : ℝ*) := by
    rw [← Hyperreal.coe_add, add_halves]
  have hlt : |b - x| < (r : ℝ*) := htri.trans_lt ((add_lt_add hby hxy).trans_eq hsum)
  exact lt_irrefl _ (hlt.trans_le hge)

/-- Every halo `halo b` is **clopen** (both closed and open) in `intervalTopology`! -/
theorem isClopen_intervalTopology_halo (b : ℝ*) :
    @IsClopen ℝ* intervalTopology (halo b) :=
  ⟨@isClosed_compl_iff ℝ* intervalTopology _ |>.2 (by simp; exact isIntervalOpen_compl_halo b)
    |> fun h ↦ by simpa using h,
   isIntervalOpen_halo b⟩

/-- Every galaxy `galaxy b` is S-open (and its complement is also S-open, being a union of
galaxies), so `galaxy b` is **clopen** in Robinson's `sTopology`! -/
theorem isClopen_sTopology_galaxy (b : ℝ*) :
    @IsClopen ℝ* sTopology (galaxy b) := by
  have hopen_gal : ∀ c : ℝ*, IsSOpen (galaxy c) := by
    intro c
    rw [isSOpen_iff]
    intro x hcx
    refine ⟨1, one_pos, fun y hy ↦ ?_⟩
    obtain ⟨hlim_xy, _⟩ := (mem_sNhds_iff_shadow one_pos).1 hy
    exact hcx.trans hlim_xy
  have hopen_compl : IsSOpen (galaxy b)ᶜ := by
    rw [isSOpen_iff]
    intro x hx
    refine ⟨1, one_pos, fun y hy hy_gal ↦ hx ?_⟩
    obtain ⟨hlim_xy, _⟩ := (mem_sNhds_iff_shadow one_pos).1 hy
    exact hy_gal.trans (LimDist.symm hlim_xy)
  refine ⟨?_, hopen_gal b⟩
  let _ : TopologicalSpace ℝ* := sTopology
  exact isOpen_compl_iff.1 hopen_compl

/-- Every galaxy `galaxy b` is also **clopen** in `intervalTopology`! -/
theorem isClopen_intervalTopology_galaxy (b : ℝ*) :
    @IsClopen ℝ* intervalTopology (galaxy b) := by
  have hcl := isClopen_sTopology_galaxy b
  let _ : TopologicalSpace ℝ* := intervalTopology
  have hopen : IsIntervalOpen (galaxy b) := (isRealOpen_galaxy b).isIntervalOpen
  have hopen_c : IsIntervalOpen (galaxy b)ᶜ := by
    have hSc : IsSOpen (galaxy b)ᶜ := by
      let _ : TopologicalSpace ℝ* := sTopology
      exact hcl.1.isOpen_compl
    exact hSc.isRealOpen.isIntervalOpen
  exact ⟨isOpen_compl_iff.1 hopen_c, hopen⟩

/-- `(ℝ*, intervalTopology)` is **totally disconnected**: any two distinct hyperreals `x ≠ y` are
separated by the clopen scaled halo `{z ∈ ℝ* | ∀ n ≥ 1, |z - x| < |y - x| / n}`! -/
theorem totallyDisconnectedSpace_intervalTopology :
    @TotallyDisconnectedSpace ℝ* intervalTopology := by
  let _ : TopologicalSpace ℝ* := intervalTopology
  refine ⟨fun s _ hs x hx y hy ↦ ?_⟩
  by_contra hxy
  set d : ℝ* := |y - x|
  have hd_pos : 0 < d := abs_pos.2 (sub_ne_zero.2 (Ne.symm hxy))
  let G : Set ℝ* := {z : ℝ* | ∀ n : ℕ, 0 < n → |z - x| < d / (n : ℝ*)}
  have hxG : x ∈ G := by
    intro n hn
    rw [sub_self, abs_zero]
    have hn_pos : (0 : ℝ*) < (n : ℝ*) := by exact_mod_cast hn
    exact div_pos hd_pos hn_pos
  have hyG : y ∉ G := by
    intro hy_in
    have h1 := hy_in 1 one_pos
    rw [Nat.cast_one, div_one] at h1
    exact lt_irrefl d h1
  have hG_open : IsIntervalOpen G := by
    rw [isIntervalOpen_iff_symm_radius]
    intro z hz
    refine ⟨d * Hyperreal.epsilon, mul_pos hd_pos Hyperreal.epsilon_pos, fun w hw n hn ↦ ?_⟩
    have hwz : |w - z| < d * Hyperreal.epsilon :=
      abs_lt.2 ⟨by linarith [hw.1], by linarith [hw.2]⟩
    have h2n : 0 < 2 * n := by omega
    have hzx : |z - x| < d / ((2 * n : ℕ) : ℝ*) := hz (2 * n) h2n
    have hinv_pos : (0 : ℝ) < (((2 * n : ℕ) : ℝ)⁻¹ : ℝ) :=
      inv_pos.2 (Nat.cast_pos.2 h2n)
    have heps_lt : Hyperreal.epsilon < (((2 * n : ℕ) : ℝ)⁻¹ : ℝ*) :=
      Hyperreal.epsilon_lt_of_pos hinv_pos
    have hmul_lt : d * Hyperreal.epsilon < d / ((2 * n : ℕ) : ℝ*) := by
      have hcast : (((2 * n : ℕ) : ℝ)⁻¹ : ℝ*) = ((2 * n : ℕ) : ℝ*)⁻¹ := by push_cast; rfl
      rw [div_eq_mul_inv, ← hcast]
      exact mul_lt_mul_of_pos_left heps_lt hd_pos
    have htri : |w - x| ≤ |w - z| + |z - x| := by
      have : w - x = (w - z) + (z - x) := by ring
      rw [this]
      exact abs_add_le (w - z) (z - x)
    have hhalves : d / ((2 * n : ℕ) : ℝ*) + d / ((2 * n : ℕ) : ℝ*) = d / (n : ℝ*) := by
      have hn_ne : (n : ℝ*) ≠ 0 := by exact_mod_cast hn.ne'
      push_cast
      field_simp [hn_ne]
      ring
    exact htri.trans_lt ((add_lt_add (hwz.trans hmul_lt) hzx).trans_eq hhalves)
  have hGc_open : IsIntervalOpen Gᶜ := by
    rw [isIntervalOpen_iff_symm_radius]
    intro z hz
    change ¬ (∀ n : ℕ, 0 < n → |z - x| < d / (n : ℝ*)) at hz
    push Not at hz
    obtain ⟨n, hn, hge⟩ := hz
    have h2n_pos : (0 : ℝ*) < ((2 * n : ℕ) : ℝ*) := by
      have : 0 < 2 * n := by omega
      exact_mod_cast this
    refine ⟨d / ((2 * n : ℕ) : ℝ*), div_pos hd_pos h2n_pos, fun w hw hwG ↦ ?_⟩
    have hwz : |z - w| < d / ((2 * n : ℕ) : ℝ*) :=
      abs_lt.2 ⟨by linarith [hw.2], by linarith [hw.1]⟩
    have hwx : |w - x| < d / ((2 * n : ℕ) : ℝ*) := hwG (2 * n) (by omega)
    have htri : |z - x| ≤ |z - w| + |w - x| := by
      have : z - x = (z - w) + (w - x) := by ring
      rw [this]
      exact abs_add_le (z - w) (w - x)
    have hhalves : d / ((2 * n : ℕ) : ℝ*) + d / ((2 * n : ℕ) : ℝ*) = d / (n : ℝ*) := by
      have hn_ne : (n : ℝ*) ≠ 0 := by exact_mod_cast hn.ne'
      push_cast
      field_simp [hn_ne]
      ring
    have hlt : |z - x| < d / (n : ℝ*) := htri.trans_lt ((add_lt_add hwz hwx).trans_eq hhalves)
    exact lt_irrefl _ (hlt.trans_le hge)
  have hG_clopen : IsClopen G := ⟨isOpen_compl_iff.1 hGc_open, hG_open⟩
  have hsub : s ⊆ G := hs.subset_isClopen hG_clopen ⟨x, hx, hxG⟩
  exact hyG (hsub hy)

/-- `(ℝ*, intervalTopology)` is NOT preconnected (and hence NOT connected), witnessed by any
clopen halo (e.g. `halo 0`, containing `0` and omitting `1`)! -/
theorem not_connectedSpace_intervalTopology :
    ¬ @PreconnectedSpace ℝ* intervalTopology ∧ ¬ @ConnectedSpace ℝ* intervalTopology := by
  let _ : TopologicalSpace ℝ* := intervalTopology
  have hnot_pre : ¬ PreconnectedSpace ℝ* := by
    intro hpre
    have hcl : IsClopen (halo 0) := isClopen_intervalTopology_halo 0
    rcases isClopen_iff.1 hcl with hemp | huniv
    · have : (0 : ℝ*) ∈ (∅ : Set ℝ*) := hemp ▸ self_mem_halo 0
      exact this
    · have h1 : (1 : ℝ*) ∈ halo 0 := huniv ▸ Set.mem_univ 1
      rw [halo_zero] at h1
      exact one_ne_zero (isInfinitesimal_coe_iff.1 h1)
  exact ⟨hnot_pre, fun hconn ↦ hnot_pre hconn.toPreconnectedSpace⟩

/-- `(ℝ*, sTopology)` is ALSO NOT preconnected (and hence NOT connected), witnessed by the clopen
galaxy `galaxy 0` (containing `0` and omitting `Hyperreal.omega`)! -/
theorem not_connectedSpace_sTopology :
    ¬ @PreconnectedSpace ℝ* sTopology ∧ ¬ @ConnectedSpace ℝ* sTopology := by
  let _ : TopologicalSpace ℝ* := sTopology
  have hnot_pre : ¬ PreconnectedSpace ℝ* := by
    intro hpre
    have hcl : IsClopen (galaxy 0) := isClopen_sTopology_galaxy 0
    rcases isClopen_iff.1 hcl with hemp | huniv
    · have : (0 : ℝ*) ∈ (∅ : Set ℝ*) := hemp ▸ LimDist.refl 0
      exact this
    · have homega : Hyperreal.omega ∈ galaxy 0 := huniv ▸ Set.mem_univ _
      rw [galaxy_zero] at homega
      exact (isUnlimited_iff_not_isLimited.1 isUnlimited_omega) homega
  exact ⟨hnot_pre, fun hconn ↦ hnot_pre hconn.toPreconnectedSpace⟩

/-! ### Intersection of Open Neighbourhoods of `r ∈ ℝ*` (Goldblatt §10.5, p. 121) -/

/-- **Goldblatt §10.5** (p. 121): `⋂ {A | r ∈ A and A is S-open} = hal(r)` for every `r ∈ ℝ*`. -/
theorem biInter_isSOpen_eq_halo (r : ℝ*) :
    (⋂ (A : Set ℝ*) (_ : r ∈ A) (_ : IsSOpen A), A) = halo r := by
  apply Set.Subset.antisymm
  · intro x hx
    change IsInfinitesimal (r - x)
    intro ε hε
    have hr_in : r ∈ sNhds r ε := self_mem_sNhds r hε
    have hS : IsSOpen (sNhds r ε) := isSOpen_sNhds r ε
    have hx_in : x ∈ sNhds r ε := by
      have h1 := Set.mem_iInter.1 hx (sNhds r ε)
      have h2 := Set.mem_iInter.1 h1 hr_in
      exact Set.mem_iInter.1 h2 hS
    have hreal : x ∈ realRadiusNhds r ε := hx_in (self_mem_halo x)
    rw [mem_realRadiusNhds_iff_abs, abs_sub_comm] at hreal
    exact hreal
  · intro x hx
    simp only [Set.mem_iInter]
    intro A hrA hAo
    exact hAo.halo_subset hrA hx

/-- **Goldblatt §10.5** (p. 121): The intersection of all *centered* positive real-radius
neighbourhoods `(r - ε, r + ε)` (`ε > 0` in `ℝ`) of `r ∈ ℝ*` equals `hal(r)`. -/
theorem biInter_realRadiusNhds_eq_halo (r : ℝ*) :
    (⋂ (ε : ℝ) (_ : 0 < ε), realRadiusNhds r ε) = halo r := by
  ext x
  simp only [Set.mem_iInter, mem_realRadiusNhds_iff_abs, abs_sub_comm x r]
  rfl

/-- **Goldblatt §10.5** (p. 121): `⋂ {A | r ∈ A and A is interval-open} = {r}` for every `r ∈ ℝ*`. -/
theorem biInter_isIntervalOpen_eq_singleton (r : ℝ*) :
    (⋂ (A : Set ℝ*) (_ : r ∈ A) (_ : IsIntervalOpen A), A) = {r} := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_singleton_iff]
    by_contra hxr
    set δ : ℝ* := |x - r| / 2
    have hδ : 0 < δ := half_pos (abs_pos.2 (sub_ne_zero.2 hxr))
    let A : Set ℝ* := Set.Ioo (r - δ) (r + δ)
    have hrA : r ∈ A := ⟨by linarith, by linarith⟩
    have hAo : IsIntervalOpen A := isIntervalOpen_Ioo (r - δ) (r + δ)
    have hxA : x ∈ A := by
      have h1 := Set.mem_iInter.1 hx A
      have h2 := Set.mem_iInter.1 h1 hrA
      exact Set.mem_iInter.1 h2 hAo
    have hlt : |x - r| < δ := abs_lt.2 ⟨by linarith [hxA.1], by linarith [hxA.2]⟩
    have hd_pos : 0 < |x - r| := abs_pos.2 (sub_ne_zero.2 hxr)
    linarith [show δ = |x - r| / 2 from rfl]
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simp only [Set.mem_iInter]
    intro A hrA _
    exact hrA

/-- Note on Goldblatt §10.5 (p. 121, lines 473–478): While centered real-radius neighbourhoods
intersect to `hal(r)` (`biInter_realRadiusNhds_eq_halo`) and S-open neighbourhoods intersect to
`hal(r)` (`biInter_isSOpen_eq_halo`), the intersection of ALL (possibly off-center!) `IsRealOpen`
sets containing `r` actually collapses to `{r}`, because `r` and any `x ≠ r` can be separated by
an off-center real-radius neighbourhood `(c - 1, c + 1)` with endpoint between `r` and `x`! -/
theorem biInter_isRealOpen_eq_singleton (r : ℝ*) :
    (⋂ (A : Set ℝ*) (_ : r ∈ A) (_ : IsRealOpen A), A) = {r} := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_singleton_iff]
    by_contra hxr
    rcases lt_or_gt_of_ne hxr with hlt | hgt
    · set η : ℝ* := min ((r - x) / 2) 1
      have hη_pos : 0 < η := lt_min (half_pos (sub_pos.2 hlt)) one_pos
      have hη_le1 : η ≤ 1 := min_le_right _ _
      have hη_lt : x < r - η := by
        have : η ≤ (r - x) / 2 := min_le_left _ _
        linarith
      let c : ℝ* := r - η + 1
      have hrc : r ∈ realRadiusNhds c 1 := by
        rw [realRadiusNhds, Hyperreal.coe_one, Set.mem_Ioo]
        exact ⟨by linarith, by linarith⟩
      have hRo : IsRealOpen (realRadiusNhds c 1) := isRealOpen_realRadiusNhds c one_pos
      have hxc : x ∈ realRadiusNhds c 1 := by
        have h1 := Set.mem_iInter.1 hx (realRadiusNhds c 1)
        have h2 := Set.mem_iInter.1 h1 hrc
        exact Set.mem_iInter.1 h2 hRo
      rw [realRadiusNhds, Hyperreal.coe_one, Set.mem_Ioo] at hxc
      linarith [hxc.1]
    · set η : ℝ* := min ((x - r) / 2) 1
      have hη_pos : 0 < η := lt_min (half_pos (sub_pos.2 hgt)) one_pos
      have hη_le1 : η ≤ 1 := min_le_right _ _
      have hη_gt : r + η < x := by
        have : η ≤ (x - r) / 2 := min_le_left _ _
        linarith
      let c : ℝ* := r + η - 1
      have hrc : r ∈ realRadiusNhds c 1 := by
        rw [realRadiusNhds, Hyperreal.coe_one, Set.mem_Ioo]
        exact ⟨by linarith, by linarith⟩
      have hRo : IsRealOpen (realRadiusNhds c 1) := isRealOpen_realRadiusNhds c one_pos
      have hxc : x ∈ realRadiusNhds c 1 := by
        have h1 := Set.mem_iInter.1 hx (realRadiusNhds c 1)
        have h2 := Set.mem_iInter.1 h1 hrc
        exact Set.mem_iInter.1 h2 hRo
      rw [realRadiusNhds, Hyperreal.coe_one, Set.mem_Ioo] at hxc
      linarith [hxc.2]
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simp only [Set.mem_iInter]
    intro A hrA _
    exact hrA

/-! ### Generating the Interval Topology from Real-Radius Neighbourhoods (pp. 121–122) -/

/-- **Goldblatt §10.5** (p. 121): Every hyperreal open interval `(a, b)` of limited width is the
intersection of two real-radius neighbourhoods! -/
theorem Ioo_eq_inter_realRadiusNhds {a b : ℝ*} (hlim : IsLimited (b - a)) :
    ∃ (r₁ : ℝ*) (ε₁ : ℝ) (r₂ : ℝ*) (ε₂ : ℝ),
      0 < ε₁ ∧ 0 < ε₂ ∧ Set.Ioo a b = realRadiusNhds r₁ ε₁ ∩ realRadiusNhds r₂ ε₂ := by
  rcases le_or_gt b a with hba | hab
  · refine ⟨0, 1, 3, 1, one_pos, one_pos, ?_⟩
    have hemp1 : Set.Ioo a b = ∅ := Set.Ioo_eq_empty (not_lt.2 hba)
    have hemp2 : realRadiusNhds 0 1 ∩ realRadiusNhds 3 1 = ∅ := by
      ext x
      simp only [realRadiusNhds, Hyperreal.coe_one, Set.mem_inter_iff, Set.mem_Ioo,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hx2⟩, ⟨hx3, _⟩⟩
      linarith
    rw [hemp1, hemp2]
  · obtain ⟨n, hn⟩ := hlim
    let R : ℝ := (n : ℝ) + 1
    have hR_pos : 0 < R := by positivity
    have hba_lt : b - a < (R : ℝ*) := by
      rw [abs_of_pos (sub_pos.2 hab)] at hn
      have hnR : (n : ℝ*) < (R : ℝ*) := Hyperreal.coe_lt_coe.2 (lt_add_one (n : ℝ))
      exact hn.trans hnR
    refine ⟨b - (R : ℝ*), R, a + (R : ℝ*), R, hR_pos, hR_pos, ?_⟩
    ext x
    simp only [realRadiusNhds, Set.mem_inter_iff, Set.mem_Ioo]
    have hR_pos' : (0 : ℝ*) < (R : ℝ*) := Hyperreal.coe_pos.2 hR_pos
    constructor
    · rintro ⟨hax, hxb⟩
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · rintro ⟨⟨_, hxb⟩, ⟨hax, _⟩⟩
      exact ⟨by linarith, by linarith⟩

/-- **Goldblatt §10.5** (pp. 121–122): Any topology on `ℝ*` in which every real-radius
neighbourhood is open must contain every hyperreal open interval `(a, b)` and hence every
interval-open set; thus `generateFrom {realRadiusNhds r ε | ε > 0} = intervalTopology`! -/
theorem generateFrom_realRadiusNhds_eq_intervalTopology :
    TopologicalSpace.generateFrom
      {U : Set ℝ* | ∃ (r : ℝ*) (ε : ℝ), 0 < ε ∧ U = realRadiusNhds r ε} = intervalTopology := by
  set G : Set (Set ℝ*) := {U : Set ℝ* | ∃ (r : ℝ*) (ε : ℝ), 0 < ε ∧ U = realRadiusNhds r ε}
  have hgen_to_int : ∀ s : Set ℝ*, TopologicalSpace.GenerateOpen G s → IsIntervalOpen s := by
    intro s hs
    induction hs with
    | basic t ht =>
        rcases ht with ⟨r, ε, _, rfl⟩
        exact isIntervalOpen_Ioo _ _
    | univ => exact intervalTopology.isOpen_univ
    | inter u v _ _ ihu ihv => exact isIntervalOpen_inter ihu ihv
    | sUnion S _ ihS => exact intervalTopology.isOpen_sUnion S ihS
  have hbdd_Ioo : ∀ a b : ℝ*, IsLimited (b - a) → TopologicalSpace.GenerateOpen G (Set.Ioo a b) := by
    intro a b hlim
    obtain ⟨r₁, ε₁, r₂, ε₂, hε₁, hε₂, heq⟩ := Ioo_eq_inter_realRadiusNhds hlim
    rw [heq]
    exact TopologicalSpace.GenerateOpen.inter _ _
      (TopologicalSpace.GenerateOpen.basic _ ⟨r₁, ε₁, hε₁, rfl⟩)
      (TopologicalSpace.GenerateOpen.basic _ ⟨r₂, ε₂, hε₂, rfl⟩)
  have hall_Ioo : ∀ a b : ℝ*, TopologicalSpace.GenerateOpen G (Set.Ioo a b) := by
    intro a b
    let S : Set (Set ℝ*) :=
      {V : Set ℝ* | ∃ (x δ : ℝ*), 0 < δ ∧ δ ≤ 1 ∧ V = Set.Ioo (x - δ) (x + δ) ∧ V ⊆ Set.Ioo a b}
    have hcov : Set.Ioo a b = ⋃₀ S := by
      apply Set.Subset.antisymm
      · intro x ⟨hax, hxb⟩
        set δ : ℝ* := min 1 (min (x - a) (b - x))
        have hδ_pos : 0 < δ := lt_min one_pos (lt_min (sub_pos.2 hax) (sub_pos.2 hxb))
        have hδ_le1 : δ ≤ 1 := min_le_left _ _
        have hsub : Set.Ioo (x - δ) (x + δ) ⊆ Set.Ioo a b := by
          intro y hy
          have h1 : δ ≤ x - a := (min_le_right _ _).trans (min_le_left _ _)
          have h2 : δ ≤ b - x := (min_le_right _ _).trans (min_le_right _ _)
          exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
        exact ⟨Set.Ioo (x - δ) (x + δ), ⟨x, δ, hδ_pos, hδ_le1, rfl, hsub⟩, ⟨by linarith, by linarith⟩⟩
      · rintro x ⟨V, ⟨_, _, _, _, _, hVsub⟩, hxV⟩
        exact hVsub hxV
    rw [hcov]
    refine TopologicalSpace.GenerateOpen.sUnion S fun V hVS ↦ ?_
    rcases hVS with ⟨x, δ, hδ_pos, hδ_le1, rfl, _⟩
    apply hbdd_Ioo
    refine isLimited_iff_abs_le_real.2 ⟨2, by norm_num, ?_⟩
    have hdiff : (x + δ) - (x - δ) = 2 * δ := by ring
    rw [hdiff, abs_of_pos (by linarith)]
    push_cast
    linarith
  have hint_to_gen : ∀ s : Set ℝ*, IsIntervalOpen s → TopologicalSpace.GenerateOpen G s := by
    rintro s ⟨S, hS, rfl⟩
    refine TopologicalSpace.GenerateOpen.sUnion S fun U hUS ↦ ?_
    obtain ⟨a, b, rfl⟩ := hS U hUS
    exact hall_Ioo a b
  unfold intervalTopology TopologicalSpace.generateFrom
  have heq : TopologicalSpace.GenerateOpen G = IsIntervalOpen :=
    funext fun s ↦ propext ⟨hgen_to_int s, hint_to_gen s⟩
  congr!

/-! ### Exercise 10.5.2: Enlargements `*A` of Open Subsets of `ℝ` (p. 122) -/

/-- **Goldblatt Exercise 10.5.2(i)** (p. 122): For every open subset `A ⊆ ℝ`, `*A` (`starSet A`)
is interval-open in `ℝ*`. -/
theorem isIntervalOpen_starSet_of_isOpen {A : Set ℝ} (hA : IsOpen A) :
    IsIntervalOpen (starSet A) := by
  rw [isIntervalOpen_iff_symm_radius]
  have hex_rad : ∀ r ∈ A, ∃ d : ℝ, 0 < d ∧ Set.Ioo (r - d) (r + d) ⊆ A := by
    intro r hrA
    obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.1 hA r hrA
    rw [Real.ball_eq_Ioo] at hball
    exact ⟨d, hd, hball⟩
  let rad : ℝ → ℝ := fun r ↦ if hr : r ∈ A then (hex_rad r hr).choose else 1
  have hrad_pos : ∀ r : ℝ, 0 < rad r := by
    intro r
    by_cases hr : r ∈ A
    · have heq : rad r = (hex_rad r hr).choose := dite_eq_left_of_eq_true (eq_true hr)
      rw [heq]
      exact (hex_rad r hr).choose_spec.1
    · have heq : rad r = 1 := dite_eq_right_iff.2 fun h ↦ absurd h hr
      rw [heq]
      exact one_pos
  have hrad_sub : ∀ r ∈ A, Set.Ioo (r - rad r) (r + rad r) ⊆ A := by
    intro r hr
    have heq : rad r = (hex_rad r hr).choose := dite_eq_left_of_eq_true (eq_true hr)
    rw [heq]
    exact (hex_rad r hr).choose_spec.2
  intro x hxA
  rcases ofSeq_surjective x with ⟨u, rfl⟩
  have huA : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), u n ∈ A := ofSeq_mem_starSet.1 hxA
  let δ : ℝ* := ofSeq (fun n ↦ rad (u n))
  have hδ_pos : 0 < δ := ofSeq_lt_ofSeq.2 (Eventually.of_forall fun n ↦ hrad_pos (u n))
  refine ⟨δ, hδ_pos, fun y hy ↦ ?_⟩
  rcases ofSeq_surjective y with ⟨v, rfl⟩
  have hlow : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), u n - rad (u n) < v n :=
    ofSeq_lt_ofSeq.1 hy.1
  have hhigh : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), v n < u n + rad (u n) :=
    ofSeq_lt_ofSeq.1 hy.2
  rw [ofSeq_mem_starSet]
  refine (huA.and (hlow.and hhigh)).mono fun n ⟨hnuA, hnl, hnh⟩ ↦ ?_
  exact hrad_sub (u n) hnuA ⟨hnl, hnh⟩

/-- Helper for **Exercise 10.5.2(ii)–(iii)**: endpoints `a n` and `b n` of pairwise disjoint
nonempty open intervals `(a n, b n)` cannot belong to `⋃ m, (a m, b m)`. -/
theorem endpoints_notMem_iUnion_of_pairwise_disjoint {a b : ℕ → ℝ}
    (hab : ∀ n : ℕ, a n < b n)
    (hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ ↦ Set.Ioo (a n) (b n))) (n : ℕ) :
    a n ∉ (⋃ m : ℕ, Set.Ioo (a m) (b m)) ∧ b n ∉ (⋃ m : ℕ, Set.Ioo (a m) (b m)) := by
  refine ⟨?_, ?_⟩
  · intro han
    rcases Set.mem_iUnion.1 han with ⟨m, ham, hbm⟩
    have hmn : m ≠ n := fun h ↦ lt_irrefl (a n) (h ▸ ham)
    let z : ℝ := (a n + min (b n) (b m)) / 2
    have hmin : a n < min (b n) (b m) := lt_min (hab n) hbm
    have hzm : z ∈ Set.Ioo (a m) (b m) := by
      have : min (b n) (b m) ≤ b m := min_le_right _ _
      exact ⟨by linarith [show z = (a n + min (b n) (b m)) / 2 from rfl],
             by linarith [show z = (a n + min (b n) (b m)) / 2 from rfl]⟩
    have hzn : z ∈ Set.Ioo (a n) (b n) := by
      have : min (b n) (b m) ≤ b n := min_le_left _ _
      exact ⟨by linarith [show z = (a n + min (b n) (b m)) / 2 from rfl],
             by linarith [show z = (a n + min (b n) (b m)) / 2 from rfl]⟩
    exact Set.disjoint_left.1 (hdisj hmn) hzm hzn
  · intro hbn
    rcases Set.mem_iUnion.1 hbn with ⟨m, ham, hbm⟩
    have hmn : m ≠ n := fun h ↦ lt_irrefl (b n) (h ▸ hbm)
    let z : ℝ := (max (a n) (a m) + b n) / 2
    have hmax : max (a n) (a m) < b n := max_lt (hab n) ham
    have hzm : z ∈ Set.Ioo (a m) (b m) := by
      have : a m ≤ max (a n) (a m) := le_max_right _ _
      exact ⟨by linarith [show z = (max (a n) (a m) + b n) / 2 from rfl],
             by linarith [show z = (max (a n) (a m) + b n) / 2 from rfl]⟩
    have hzn : z ∈ Set.Ioo (a n) (b n) := by
      have : a n ≤ max (a n) (a m) := le_max_left _ _
      exact ⟨by linarith [show z = (max (a n) (a m) + b n) / 2 from rfl],
             by linarith [show z = (max (a n) (a m) + b n) / 2 from rfl]⟩
    exact Set.disjoint_left.1 (hdisj hmn) hzm hzn

/-- **Goldblatt Exercise 10.5.2(ii)** (p. 122): If `A = ⋃ n, (a n, b n)` is the union of pairwise
disjoint nonempty open intervals in `ℝ` of length `b n - a n < 1 / (n + 1)`, then some element of
`*A` is infinitely close to an element outside `*A`, and consequently `*A` is NOT S-open! -/
theorem exists_mem_starSet_infClose_notMem_and_not_isSOpen {a b : ℕ → ℝ}
    (hab : ∀ n : ℕ, a n < b n)
    (hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ ↦ Set.Ioo (a n) (b n)))
    (hlen : ∀ n : ℕ, b n - a n < ((n : ℝ) + 1)⁻¹) :
    let A := ⋃ n : ℕ, Set.Ioo (a n) (b n)
    (∃ x ∈ starSet A, ∃ z ∉ starSet A, x ≈ₕ z) ∧ ¬ IsSOpen (starSet A) := by
  intro A
  let x : ℝ* := ofSeq (fun n ↦ (a n + b n) / 2)
  let z : ℝ* := ofSeq b
  have hxA : x ∈ starSet A := by
    rw [ofSeq_mem_starSet]
    refine Eventually.of_forall fun n ↦ Set.mem_iUnion.2 ⟨n, ?_⟩
    have hn := hab n
    exact ⟨by linarith, by linarith⟩
  have hz_notA : z ∉ starSet A := by
    change z ∈ (starSet A)ᶜ
    rw [← starSet_compl, ofSeq_mem_starSet]
    exact Eventually.of_forall fun n ↦ (endpoints_notMem_iUnion_of_pairwise_disjoint hab hdisj n).2
  have hxz : x ≈ₕ z := by
    refine isInfinitesimal_of_abs_le isInfinitesimal_epsilon ?_
    rw [abs_of_pos Hyperreal.epsilon_pos]
    have hne0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), n ≠ 0 :=
      Filter.hyperfilter_le_cofinite (Set.finite_singleton 0).compl_mem_cofinite
    refine ofSeq_le_ofSeq.2 (hne0.mono fun n hn0 ↦ ?_)
    change |(a n + b n) / 2 - b n| ≤ (n : ℝ)⁻¹
    have h1 : |(a n + b n) / 2 - b n| = (b n - a n) / 2 := by
      have : (a n + b n) / 2 - b n = -((b n - a n) / 2) := by ring
      rw [this, abs_neg, abs_of_pos (half_pos (sub_pos.2 (hab n)))]
    have h2 : (b n - a n) / 2 < ((n : ℝ) + 1)⁻¹ := by
      linarith [hlen n, sub_pos.2 (hab n)]
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
    rw [h1]
    exact h2.le.trans (inv_anti₀ hn_pos (by linarith))
  refine ⟨⟨x, hxA, z, hz_notA, hxz⟩, fun hS ↦ hz_notA (hS.halo_subset hxA hxz)⟩

/-- **Goldblatt Exercise 10.5.2(iii)** (p. 122): Stronger still, for `A = ⋃ n, (a n, b n)` as in
Exercise 10.5.2(ii), `*A` contains a point `x` that belongs to NO real-radius neighbourhood
`(r - ε, r + ε)` included in `*A`, and consequently `*A` is NOT even real-open! -/
theorem exists_mem_starSet_no_realRadiusNhds_and_not_isRealOpen {a b : ℕ → ℝ}
    (hab : ∀ n : ℕ, a n < b n)
    (hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ ↦ Set.Ioo (a n) (b n)))
    (hlen : ∀ n : ℕ, b n - a n < ((n : ℝ) + 1)⁻¹) :
    let A := ⋃ n : ℕ, Set.Ioo (a n) (b n)
    (∃ x ∈ starSet A, ∀ (r : ℝ*) (ε : ℝ), 0 < ε → x ∈ realRadiusNhds r ε →
      ¬ (realRadiusNhds r ε ⊆ starSet A)) ∧ ¬ IsRealOpen (starSet A) := by
  intro A
  let w : ℝ* := ofSeq a
  let x : ℝ* := ofSeq (fun n ↦ (a n + b n) / 2)
  let z : ℝ* := ofSeq b
  have hxA : x ∈ starSet A := by
    rw [ofSeq_mem_starSet]
    refine Eventually.of_forall fun n ↦ Set.mem_iUnion.2 ⟨n, ?_⟩
    have hn := hab n
    exact ⟨by linarith, by linarith⟩
  have hw_notA : w ∉ starSet A := by
    change w ∈ (starSet A)ᶜ
    rw [← starSet_compl, ofSeq_mem_starSet]
    exact Eventually.of_forall fun n ↦ (endpoints_notMem_iUnion_of_pairwise_disjoint hab hdisj n).1
  have hz_notA : z ∉ starSet A := by
    change z ∈ (starSet A)ᶜ
    rw [← starSet_compl, ofSeq_mem_starSet]
    exact Eventually.of_forall fun n ↦ (endpoints_notMem_iUnion_of_pairwise_disjoint hab hdisj n).2
  have hwx : w < x := ofSeq_lt_ofSeq.2 (Eventually.of_forall fun n ↦ by linarith [hab n])
  have hxz : x < z := ofSeq_lt_ofSeq.2 (Eventually.of_forall fun n ↦ by linarith [hab n])
  have hzw_inf : IsInfinitesimal (z - w) := by
    refine isInfinitesimal_of_abs_le isInfinitesimal_epsilon ?_
    rw [abs_of_pos Hyperreal.epsilon_pos]
    have hne0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), n ≠ 0 :=
      Filter.hyperfilter_le_cofinite (Set.finite_singleton 0).compl_mem_cofinite
    refine ofSeq_le_ofSeq.2 (hne0.mono fun n hn0 ↦ ?_)
    change |b n - a n| ≤ (n : ℝ)⁻¹
    rw [abs_of_pos (sub_pos.2 (hab n))]
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
    exact (hlen n).le.trans (inv_anti₀ hn_pos (by linarith))
  have hno_nhds : ∀ (r : ℝ*) (ε : ℝ), 0 < ε → x ∈ realRadiusNhds r ε →
      ¬ (realRadiusNhds r ε ⊆ starSet A) := by
    intro r ε hε hxr hsub
    have hzw_lt : z - w < 2 * (ε : ℝ*) := by
      have h1 := hzw_inf (2 * ε) (by positivity)
      rw [abs_of_pos (sub_pos.2 (hwx.trans hxz)), Hyperreal.coe_mul, Hyperreal.coe_ofNat] at h1
      exact h1
    rcases lt_or_ge (r - (ε : ℝ*)) w with hlt_w | hge_w
    · have hw_in : w ∈ realRadiusNhds r ε := ⟨hlt_w, hwx.trans hxr.2⟩
      exact hw_notA (hsub hw_in)
    · have hz_lt : z < r + (ε : ℝ*) := by linarith
      have hz_in : z ∈ realRadiusNhds r ε := ⟨hxr.1.trans hxz, hz_lt⟩
      exact hz_notA (hsub hz_in)
  refine ⟨⟨x, hxA, hno_nhds⟩, ?_⟩
  intro hR
  obtain ⟨r, ε, hε, hxr, hsub⟩ := (isRealOpen_iff.1 hR) x hxA
  exact hno_nhds r ε hε hxr hsub

/-- Concrete unconditional witness for **Exercise 10.5.2** (p. 122):
`A = ⋃ n : ℕ, (1/(n+2), 1/(n+1))` is an open subset of `ℝ` whose enlargement `*A` is interval-open
yet neither real-open nor S-open! -/
theorem exists_isOpen_not_isRealOpen_starSet :
    ∃ A : Set ℝ, IsOpen A ∧ IsIntervalOpen (starSet A) ∧
      ¬ IsRealOpen (starSet A) ∧ ¬ IsSOpen (starSet A) := by
  let a : ℕ → ℝ := fun n ↦ ((n : ℝ) + 2)⁻¹
  let b : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1)⁻¹
  have hab : ∀ n : ℕ, a n < b n := fun n ↦ by
    dsimp [a, b]
    exact inv_strictAnti₀ (by positivity) (by linarith)
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ ↦ Set.Ioo (a n) (b n)) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_left]
    intro x hxm hxn
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · have hmn1 : (m : ℝ) + 2 ≤ (n : ℝ) + 1 := by
        have : m + 1 ≤ n := hlt
        exact_mod_cast Nat.add_le_add_right this 1
      have hbn_le_am : b n ≤ a m :=
        inv_anti₀ (by positivity) hmn1
      linarith [hxn.2, hxm.1]
    · have hnm1 : (n : ℝ) + 2 ≤ (m : ℝ) + 1 := by
        have : n + 1 ≤ m := hgt
        exact_mod_cast Nat.add_le_add_right this 1
      have hbm_le_an : b m ≤ a n :=
        inv_anti₀ (by positivity) hnm1
      linarith [hxm.2, hxn.1]
  have hlen : ∀ n : ℕ, b n - a n < ((n : ℝ) + 1)⁻¹ := fun n ↦ by
    have : (0 : ℝ) < a n := by dsimp [a]; positivity
    dsimp [b]
    linarith
  let A : Set ℝ := ⋃ n : ℕ, Set.Ioo (a n) (b n)
  have hA_open : IsOpen A := isOpen_iUnion fun _ ↦ isOpen_Ioo
  refine ⟨A, hA_open, isIntervalOpen_starSet_of_isOpen hA_open,
    (exists_mem_starSet_no_realRadiusNhds_and_not_isRealOpen hab hdisj hlen).2,
    (exists_mem_starSet_infClose_notMem_and_not_isSOpen hab hdisj hlen).2⟩

end Goldblatt.Ch10
end
