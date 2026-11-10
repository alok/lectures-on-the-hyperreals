import LecturesOnTheHyperreals.Ch11_InternalSets
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Chapter 12: Internal Functions and Hyperfinite Sets

Complete formalization of Robert Goldblatt's *Lectures on the Hyperreals*, Chapter 12 (pp. 147–155):

* **§12.1 Internal Functions** (pp. 147–148):
  - `RealPartialFun`, `InternalPartialFun`, `internalFun` (`[f_n]`), `IsInternalFun`,
    `dom [f_n] = [dom f_n]`, agreement with `starFun` on constant sequences, and
    **Theorem 12.1.1** (`internalFun_eq_iff`): `[f_n] = [g_n] ↔ {n ∈ ℕ | f_n = g_n} ∈ 𝓕`.
* **§12.2 Exercises on Properties of Internal Functions** (pp. 148–149):
  - (1) Image of an internal set under an internal function is internal (`internalFun_image`,
    `IsInternalFun.image`).
  - (2) Preimage of an internal set under an internal function is internal (`internalFun_preimage`,
    `IsInternalFun.preimage`).
  - (3) Composition of internal functions is internal (`internalFun_comp`, `IsInternalFun.comp`).
  - (4) `[f_n]` is injective iff `{n ∈ ℕ | f_n is injective} ∈ 𝓕` (`internalFun_isInjective_iff`).
  - (5) Inverse of an injective internal function is internal (`internalFun_inv`,
    `IsInternalFun.inv`).
  - (6) `f + g`, `f * g`, and `c • f` (`c ∈ ℝ*`) are internal (`IsInternalFun.add`,
    `IsInternalFun.mul`, `IsInternalFun.smul`).
  - (7) Infinitesimal-valued internal function with nonempty domain has an infinitesimal least upper
    bound (`IsInternalFun.exists_infinitesimal_isLUB_range`).
  - (8) Alternative proof that every infinite subset of `ℝ` is external using Exercise 12.2(1)
    (`isExternal_infinite_real_via_image`).
* **§12.3–12.4 Hyperfinite Sets and Internal Cardinality** (pp. 149–150):
  - `IsHyperfinite`, `HasHypercard`, `IsHyperfinite.hypercard` (`|A| = [|A_n|] ∈ ℕ*`).
  - Examples: `{1, …, ω}` (`hasHypercard_Icc_one_omegaNat`), countable hyperfinite approximation
    `B ⊆ A ⊆ *B` (`exists_hyperfinite_approx_of_countable`), finite sets (`hasHypercard_finset`,
    `IsHyperfinite.of_finite`), `{1, …, N}` (`hasHypercard_Icc_one`), uniform grid `{k/N}` and
    uniform partition `{a + k(b-a)/N}` of internal size `N + 1` (`hasHypercard_uniformPartition`).
  - Exercises 12.4(1)–(3): greatest and least elements (`IsHyperfinite.exists_isGreatest`,
    `IsHyperfinite.exists_isLeast`), closure under `∪`, `∩`, `\` and inclusion–exclusion
    `|X ∪ Y| + |X ∩ Y| = |X| + |Y|` (`hypercard_union_add_hypercard_inter`), internal subsets of
    hyperfinite sets (`IsHyperfinite.of_isInternal_subset`).
* **§12.5 Counting a Hyperfinite Set** (p. 151):
  - **Theorem 12.5.1** (`hasHypercard_iff_exists_internal_bijection`): an internal set `A` is
    hyperfinite of internal cardinality `N` iff there is an internal bijection `{1, …, N} → A`.
* **§12.6 Hyperfinite Pigeonhole Principle** (pp. 151–152):
  - **Theorem 12.6.1** (`isHyperfinite_iff_pigeonhole`): an internal set `A` is hyperfinite iff
    every injective internal function `f` with `A ⊆ dom f` and `f(A) ⊆ A` satisfies `f(A) = A`.
  - Non-internal function example `f(n) = 2n` (`n ∈ ℕ`), `f(n) = n` (`n ∉ ℕ`) proved non-internal
    via Theorem 12.6.1 (`not_isInternalFun_doubleStandard_on_Icc` and
    `not_isInternalFun_doubleStandard_on_starNat`).
* **§12.7 Integrals as Hyperfinite Sums** (pp. 152–154):
  - `hypersum` (`∑_{x ∈ A} f(x) = [∑_{x ∈ A_n} f_n(x)]`) with linearity, disjoint additivity, and
    monotonicity (`hypersum_smul`, `hypersum_add`, `hypersum_union_disjoint`, `hypersum_mono`).
  - **Exercise 12.7.1** (`hyperfinitePartition_eq`) & **Riemann Integral as Shadow of Hyperfinite
    Sum** (`integral_eq_shadow_hypersum`): `∫ x in a..b, f x = shadow (hypersum (*f) P * dx)`.
-/

noncomputable section

namespace Goldblatt

open Filter
open Hyperreal (ofSeq ofSeq_lt_ofSeq ofSeq_le_ofSeq ofSeq_surjective)
open scoped Topology Classical BigOperators

/-! ## §12.1 Internal Functions -/

/-- A partial function from `ℝ` to `ℝ` with explicit domain `dom ⊆ ℝ`, normalized to `0` outside
`dom` so that two partial functions are equal iff they have the same domain and agree on `dom`. -/
@[ext]
structure RealPartialFun where
  /-- Domain of the partial function. -/
  dom : Set ℝ
  /-- Underlying total function, normalized to `0` outside `dom`. -/
  apply : ℝ → ℝ
  /-- Normalization outside `dom`. -/
  default_outside : ∀ x, x ∉ dom → apply x = 0

/-- Construct a `RealPartialFun` from a domain `A ⊆ ℝ` and an arbitrary function `f : ℝ → ℝ`. -/
def RealPartialFun.mkPartial (A : Set ℝ) (f : ℝ → ℝ) : RealPartialFun where
  dom := A
  apply x := if x ∈ A then f x else 0
  default_outside x hx := by simp [hx]

/-- Domain of `RealPartialFun.mkPartial A f` is `A`. -/
@[simp]
theorem RealPartialFun.mkPartial_dom (A : Set ℝ) (f : ℝ → ℝ) :
    (RealPartialFun.mkPartial A f).dom = A := rfl

/-- Evaluation of `RealPartialFun.mkPartial A f` inside `A`. -/
theorem RealPartialFun.mkPartial_apply_of_mem {A : Set ℝ} {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ A) :
    (RealPartialFun.mkPartial A f).apply x = f x := by
  simp [RealPartialFun.mkPartial, hx]

/-- Two `RealPartialFun`s are equal iff they have the same domain and agree on every element of
that domain. -/
theorem RealPartialFun.eq_iff_dom_and_eqOn {f g : RealPartialFun} :
    f = g ↔ f.dom = g.dom ∧ ∀ x ∈ f.dom, f.apply x = g.apply x := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ ↦ rfl⟩
  · rintro ⟨hdom, heq⟩
    ext x
    · rw [hdom]
    · by_cases hx : x ∈ f.dom
      · exact heq x hx
      · have hxg : x ∉ g.dom := hdom ▸ hx
        rw [f.default_outside x hx, g.default_outside x hxg]

/-- Range `f(dom f)` of a `RealPartialFun`. -/
def RealPartialFun.range (f : RealPartialFun) : Set ℝ :=
  f.apply '' f.dom

/-- Injectivity of a `RealPartialFun` on its domain. -/
def RealPartialFun.IsInjective (f : RealPartialFun) : Prop :=
  Set.InjOn f.apply f.dom

/-- A partial function from `ℝ*` to `ℝ*` with explicit domain `dom ⊆ ℝ*`, normalized to `0`
outside `dom`. -/
@[ext]
structure InternalPartialFun where
  /-- Domain of the partial function on `ℝ*`. -/
  dom : Set ℝ*
  /-- Underlying map `ℝ* → ℝ*`, normalized to `0` outside `dom`. -/
  apply : ℝ* → ℝ*
  /-- Normalization outside `dom`. -/
  default_outside : ∀ x, x ∉ dom → apply x = 0

/-- Construct an `InternalPartialFun` from a domain `X ⊆ ℝ*` and a map `F : ℝ* → ℝ*`. -/
def InternalPartialFun.mkPartial (X : Set ℝ*) (F : ℝ* → ℝ*) : InternalPartialFun where
  dom := X
  apply x := if x ∈ X then F x else 0
  default_outside x hx := by simp [hx]

@[simp]
theorem InternalPartialFun.mkPartial_dom (X : Set ℝ*) (F : ℝ* → ℝ*) :
    (InternalPartialFun.mkPartial X F).dom = X := rfl

theorem InternalPartialFun.mkPartial_apply_of_mem {X : Set ℝ*} {F : ℝ* → ℝ*} {x : ℝ*}
    (hx : x ∈ X) :
    (InternalPartialFun.mkPartial X F).apply x = F x := by
  simp [InternalPartialFun.mkPartial, hx]

/-- Two `InternalPartialFun`s are equal iff they have the same domain and agree on that domain. -/
theorem InternalPartialFun.eq_iff_dom_and_eqOn {F G : InternalPartialFun} :
    F = G ↔ F.dom = G.dom ∧ ∀ x ∈ F.dom, F.apply x = G.apply x := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ ↦ rfl⟩
  · rintro ⟨hdom, heq⟩
    ext x
    · rw [hdom]
    · by_cases hx : x ∈ F.dom
      · exact heq x hx
      · have hxG : x ∉ G.dom := hdom ▸ hx
        rw [F.default_outside x hx, G.default_outside x hxG]

/-- Range `F(dom F)` of an `InternalPartialFun`. -/
def InternalPartialFun.range (F : InternalPartialFun) : Set ℝ* :=
  F.apply '' F.dom

/-- Injectivity of an `InternalPartialFun` on its domain. -/
def InternalPartialFun.IsInjective (F : InternalPartialFun) : Prop :=
  Set.InjOn F.apply F.dom

/-- Restriction of an `InternalPartialFun` to a subset `X ⊆ ℝ*` (giving domain `F.dom ∩ X`). -/
def InternalPartialFun.restrict (F : InternalPartialFun) (X : Set ℝ*) : InternalPartialFun :=
  InternalPartialFun.mkPartial (F.dom ∩ X) F.apply

/-- Goldblatt §12.1 (p. 147): The internal function `[f_n]` built from a sequence of real partial
functions `f : ℕ → RealPartialFun`, with domain `[dom f_n]` and `[f_n]([r_n]) = [f_n(r_n)]`. -/
def internalFun (f : ℕ → RealPartialFun) : InternalPartialFun where
  dom := internalSet (fun n ↦ (f n).dom)
  apply x := Germ.map₂ RealPartialFun.apply (f : Germ (hyperfilter ℕ : Filter ℕ) RealPartialFun) x
  default_outside x hx := by
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    rw [ofSeq_mem_internalSet, ← Ultrafilter.eventually_not] at hx
    exact Germ.coe_eq.2 (hx.mono fun n hn ↦ (f n).default_outside (r n) hn)

/-- Goldblatt §12.1 (p. 147): `dom [f_n] = [dom f_n]`. -/
@[simp]
theorem internalFun_dom (f : ℕ → RealPartialFun) :
    (internalFun f).dom = internalSet (fun n ↦ (f n).dom) := rfl

/-- Evaluation of `[f_n]` on `[r_n]` is `[f_n(r_n)]`. -/
@[simp]
theorem internalFun_apply_ofSeq (f : ℕ → RealPartialFun) (r : ℕ → ℝ) :
    (internalFun f).apply (ofSeq r) = ofSeq (fun n ↦ (f n).apply (r n)) := rfl

/-- Goldblatt §12.1 (p. 147): An `InternalPartialFun` is **internal** if it is of the form `[f_n]`
for some sequence `f : ℕ → RealPartialFun`. -/
def IsInternalFun (F : InternalPartialFun) : Prop :=
  ∃ f : ℕ → RealPartialFun, F = internalFun f

/-- `internalFun f` is internal by definition. -/
theorem isInternalFun_internalFun (f : ℕ → RealPartialFun) : IsInternalFun (internalFun f) :=
  ⟨f, rfl⟩

/-- The domain of any internal function is an internal set. -/
theorem IsInternalFun.isInternal_dom {F : InternalPartialFun} (hF : IsInternalFun F) :
    IsInternal F.dom := by
  rcases hF with ⟨f, rfl⟩
  exact ⟨fun n ↦ (f n).dom, rfl⟩

/-- Goldblatt §12.1 (p. 147): For a constant sequence `f_n = mkPartial A f₀`, `[f_n]` has domain
`*A` and agrees with `starFun f₀` on `*A`. -/
def starInternalFun (A : Set ℝ) (f₀ : ℝ → ℝ) : InternalPartialFun :=
  internalFun (fun _ ↦ RealPartialFun.mkPartial A f₀)

/-- `starInternalFun A f₀` is internal. -/
theorem isInternalFun_starInternalFun (A : Set ℝ) (f₀ : ℝ → ℝ) :
    IsInternalFun (starInternalFun A f₀) :=
  ⟨_, rfl⟩

/-- Domain of `starInternalFun A f₀` is `starSet A`. -/
@[simp]
theorem starInternalFun_dom (A : Set ℝ) (f₀ : ℝ → ℝ) :
    (starInternalFun A f₀).dom = starSet A :=
  internalSet_const A

/-- On `starSet A`, `starInternalFun A f₀` evaluates as `starFun f₀`. -/
theorem starInternalFun_apply_of_mem {A : Set ℝ} {f₀ : ℝ → ℝ} {x : ℝ*} (hx : x ∈ starSet A) :
    (starInternalFun A f₀).apply x = starFun f₀ x := by
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ A := by
    rw [← internalSet_const, ofSeq_mem_internalSet] at hx
    exact hx
  exact Germ.coe_eq.2 (hev.mono fun n hn ↦ RealPartialFun.mkPartial_apply_of_mem hn)

/-- Goldblatt Theorem 12.1.1 (pp. 147–148):
Two internal functions `[f_n]` and `[g_n]` are equal **if and only if**
`{n ∈ ℕ | f_n = g_n} ∈ 𝓕`. -/
theorem internalFun_eq_iff {f g : ℕ → RealPartialFun} :
    internalFun f = internalFun g ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n = g n := by
  constructor
  · intro heq
    have hdom_eq : internalSet (fun n ↦ (f n).dom) = internalSet (fun n ↦ (g n).dom) :=
      congrArg InternalPartialFun.dom heq
    have hev_dom : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (f n).dom = (g n).dom :=
      internalSet_eq_iff.1 hdom_eq
    by_contra hnot
    have hev_ne : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n ≠ g n :=
      Ultrafilter.eventually_not.2 hnot
    have hev_wit : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
        ∃ r : ℝ, r ∈ (f n).dom ∧ (f n).apply r ≠ (g n).apply r := by
      refine (hev_dom.and hev_ne).mono fun n ⟨hdn, hnen⟩ ↦ ?_
      rw [Ne, RealPartialFun.eq_iff_dom_and_eqOn] at hnen
      push Not at hnen
      exact hnen hdn
    let rSeq : ℕ → ℝ := fun n ↦
      if h : ∃ r : ℝ, r ∈ (f n).dom ∧ (f n).apply r ≠ (g n).apply r then h.choose else 0
    have happ_eq : (internalFun f).apply (ofSeq rSeq) = (internalFun g).apply (ofSeq rSeq) :=
      congrArg (fun F ↦ F.apply (ofSeq rSeq)) heq
    have hev_val_eq : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
        (f n).apply (rSeq n) = (g n).apply (rSeq n) :=
      Germ.coe_eq.1 happ_eq
    obtain ⟨n, hn1, hn2⟩ := (hev_wit.and hev_val_eq).exists
    have hne_val : (f n).apply (rSeq n) ≠ (g n).apply (rSeq n) := by
      simpa only [rSeq, hn1, ↓reduceDIte] using hn1.choose_spec.2
    exact hne_val hn2
  · intro hev
    rw [InternalPartialFun.eq_iff_dom_and_eqOn]
    refine ⟨internalSet_eq_iff.2 (hev.mono fun n hn ↦ congrArg RealPartialFun.dom hn), ?_⟩
    intro x _
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    exact Germ.coe_eq.2 (hev.mono fun n hn ↦ congrArg (fun p ↦ p.apply (r n)) hn)

/-! ## §12.2 Exercises on Properties of Internal Functions -/

/-- Restriction of an internal function to an internal set is internal. -/
theorem IsInternalFun.restrict {F : InternalPartialFun} (hF : IsInternalFun F)
    {X : Set ℝ*} (hX : IsInternal X) :
    IsInternalFun (F.restrict X) := by
  rcases hF with ⟨f, rfl⟩
  rcases hX with ⟨A, rfl⟩
  refine ⟨fun n ↦ RealPartialFun.mkPartial ((f n).dom ∩ A n) (f n).apply, ?_⟩
  rw [InternalPartialFun.eq_iff_dom_and_eqOn]
  refine ⟨internalSet_inter _ _, fun x hx ↦ ?_⟩
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  have hx_mem : ofSeq r ∈ (internalFun f).dom ∩ internalSet A := hx
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ (f n).dom ∧ r n ∈ A n := by
    rw [internalFun_dom, internalSet_inter, ofSeq_mem_internalSet] at hx_mem
    exact hx_mem
  have h1 : (InternalPartialFun.restrict (internalFun f) (internalSet A)).apply (ofSeq r) =
      (internalFun f).apply (ofSeq r) :=
    InternalPartialFun.mkPartial_apply_of_mem hx_mem
  rw [h1]
  exact Germ.coe_eq.2 (hev.mono fun n hn ↦ by
    dsimp only
    rw [RealPartialFun.mkPartial_apply_of_mem hn])

/-- Goldblatt Exercise 12.2(1) (p. 148): If `f = [f_n]` is an internal function and `A = [A_n]` is
any internal subset of `dom f`, then `f(A) = [f_n(A_n)]`. -/
theorem internalFun_image (f : ℕ → RealPartialFun) (A : ℕ → Set ℝ) :
    (internalFun f).apply '' (internalSet A) =
      internalSet (fun n ↦ (f n).apply '' (A n)) := by
  ext y
  rcases ofSeq_surjective y with ⟨s, rfl⟩
  constructor
  · rintro ⟨x, hxA, hfx⟩
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hrA : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ A n := ofSeq_mem_internalSet.1 hxA
    have hfs : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (f n).apply (r n) = s n := Germ.coe_eq.1 hfx
    exact ofSeq_mem_internalSet.2 ((hrA.and hfs).mono fun n ⟨h1, h2⟩ ↦ ⟨r n, h1, h2⟩)
  · intro hy
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ r ∈ A n, (f n).apply r = s n :=
      ofSeq_mem_internalSet.1 hy
    let rSeq : ℕ → ℝ := fun n ↦
      if h : ∃ r ∈ A n, (f n).apply r = s n then h.choose else 0
    refine ⟨ofSeq rSeq, ofSeq_mem_internalSet.2 ?_, Germ.coe_eq.2 ?_⟩
    · exact hev.mono fun n hn ↦ by simpa only [rSeq, hn, ↓reduceDIte] using hn.choose_spec.1
    · exact hev.mono fun n hn ↦ by simpa only [rSeq, hn, ↓reduceDIte] using hn.choose_spec.2

/-- Goldblatt Exercise 12.2(1) corollary: The image `F(X)` of any internal set `X ⊆ dom F` under an
internal function `F` is internal; in particular `F.range` is internal. -/
theorem IsInternalFun.image {F : InternalPartialFun} (hF : IsInternalFun F)
    {X : Set ℝ*} (hX : IsInternal X) :
    IsInternal (F.apply '' X) := by
  rcases hF with ⟨f, rfl⟩
  rcases hX with ⟨A, rfl⟩
  exact ⟨fun n ↦ (f n).apply '' (A n), internalFun_image f A⟩

/-- Range of an internal function is internal. -/
theorem IsInternalFun.isInternal_range {F : InternalPartialFun} (hF : IsInternalFun F) :
    IsInternal F.range :=
  hF.image hF.isInternal_dom

/-- Preimage of a set `B ⊆ ℝ` inside `dom p` for `p : RealPartialFun`. -/
def RealPartialFun.preimage (p : RealPartialFun) (B : Set ℝ) : Set ℝ :=
  {a ∈ p.dom | p.apply a ∈ B}

/-- Preimage `{a ∈ dom F | F(a) ∈ Y}` of `Y ⊆ ℝ*` under `F : InternalPartialFun`. -/
def InternalPartialFun.preimage (F : InternalPartialFun) (Y : Set ℝ*) : Set ℝ* :=
  {a ∈ F.dom | F.apply a ∈ Y}

/-- Goldblatt Exercise 12.2(2) (p. 148): For `f = [f_n]` and `B = [B_n]`,
`f⁻¹(B) = {a ∈ dom f | f(a) ∈ B} = [f_n⁻¹(B_n)]`. -/
theorem internalFun_preimage (f : ℕ → RealPartialFun) (B : ℕ → Set ℝ) :
    (internalFun f).preimage (internalSet B) =
      internalSet (fun n ↦ (f n).preimage (B n)) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp only [InternalPartialFun.preimage, RealPartialFun.preimage, Set.mem_ofPred_eq,
    internalFun_dom, internalFun_apply_ofSeq, ofSeq_mem_internalSet, eventually_and]

/-- Goldblatt Exercise 12.2(2) corollary: The preimage of an internal set under an internal function
is internal. -/
theorem IsInternalFun.preimage {F : InternalPartialFun} (hF : IsInternalFun F)
    {Y : Set ℝ*} (hY : IsInternal Y) :
    IsInternal (F.preimage Y) := by
  rcases hF with ⟨f, rfl⟩
  rcases hY with ⟨B, rfl⟩
  exact ⟨fun n ↦ (f n).preimage (B n), internalFun_preimage f B⟩

/-- Composition `q ∘ p` of two `RealPartialFun`s on domain `p.preimage q.dom`. -/
def RealPartialFun.comp (q p : RealPartialFun) : RealPartialFun :=
  RealPartialFun.mkPartial (p.preimage q.dom) (fun x ↦ q.apply (p.apply x))

/-- Composition `G ∘ F` of two `InternalPartialFun`s on domain `F.preimage G.dom` (which equals
`F.dom` whenever `F.range ⊆ G.dom`). -/
def InternalPartialFun.comp (G F : InternalPartialFun) : InternalPartialFun :=
  InternalPartialFun.mkPartial (F.preimage G.dom) (fun x ↦ G.apply (F.apply x))

/-- When `F.range ⊆ G.dom`, `(G.comp F).dom = F.dom`. -/
theorem InternalPartialFun.comp_dom_of_range_subset {G F : InternalPartialFun}
    (hsub : F.range ⊆ G.dom) :
    (G.comp F).dom = F.dom := by
  ext x
  exact ⟨fun hx ↦ hx.1, fun hx ↦ ⟨hx, hsub ⟨x, hx, rfl⟩⟩⟩

/-- Goldblatt Exercise 12.2(3) (p. 149): `[g_n] ∘ [f_n] = [g_n ∘ f_n]`, so the composition of
internal functions is internal! -/
theorem internalFun_comp (g f : ℕ → RealPartialFun) :
    (internalFun g).comp (internalFun f) = internalFun (fun n ↦ (g n).comp (f n)) := by
  rw [InternalPartialFun.eq_iff_dom_and_eqOn]
  have hdom : ((internalFun g).comp (internalFun f)).dom =
      internalSet (fun n ↦ ((g n).comp (f n)).dom) :=
    internalFun_preimage f (fun n ↦ (g n).dom)
  refine ⟨hdom, fun x hx ↦ ?_⟩
  have hx' : x ∈ (internalFun f).preimage (internalFun g).dom := hx
  have h1 : ((internalFun g).comp (internalFun f)).apply x =
      (internalFun g).apply ((internalFun f).apply x) :=
    InternalPartialFun.mkPartial_apply_of_mem hx'
  rw [h1]
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ (f n).preimage (g n).dom := by
    rw [internalFun_dom, internalFun_preimage, ofSeq_mem_internalSet] at hx'
    exact hx'
  exact Germ.coe_eq.2 (hev.mono fun n hn ↦ by
    dsimp only [RealPartialFun.comp]
    rw [RealPartialFun.mkPartial_apply_of_mem hn])

/-- Goldblatt Exercise 12.2(3) corollary: Composition of internal functions is internal. -/
theorem IsInternalFun.comp {G F : InternalPartialFun} (hG : IsInternalFun G)
    (hF : IsInternalFun F) :
    IsInternalFun (G.comp F) := by
  rcases hG with ⟨g, rfl⟩
  rcases hF with ⟨f, rfl⟩
  exact ⟨fun n ↦ (g n).comp (f n), internalFun_comp g f⟩

/-- Goldblatt Exercise 12.2(4) (p. 149): An internal function `[f_n]` is injective **if and only if**
`{n ∈ ℕ | f_n is injective} ∈ 𝓕`. -/
theorem internalFun_isInjective_iff {f : ℕ → RealPartialFun} :
    (internalFun f).IsInjective ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (f n).IsInjective := by
  constructor
  · intro hinj
    by_contra hnot
    have hev_not : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
        ∃ a ∈ (f n).dom, ∃ b ∈ (f n).dom, (f n).apply a = (f n).apply b ∧ a ≠ b := by
      refine (Ultrafilter.eventually_not.2 hnot).mono fun n hn ↦ ?_
      unfold RealPartialFun.IsInjective Set.InjOn at hn
      push Not at hn
      exact hn
    let aSeq : ℕ → ℝ := fun n ↦
      if h : ∃ a ∈ (f n).dom, ∃ b ∈ (f n).dom, (f n).apply a = (f n).apply b ∧ a ≠ b
      then h.choose else 0
    let bSeq : ℕ → ℝ := fun n ↦
      if h : ∃ a ∈ (f n).dom, ∃ b ∈ (f n).dom, (f n).apply a = (f n).apply b ∧ a ≠ b
      then h.choose_spec.2.choose else 0
    have ha_dom : ofSeq aSeq ∈ (internalFun f).dom := by
      refine ofSeq_mem_internalSet.2 (hev_not.mono fun n hn ↦ ?_)
      simpa only [aSeq, hn, ↓reduceDIte] using hn.choose_spec.1
    have hb_dom : ofSeq bSeq ∈ (internalFun f).dom := by
      refine ofSeq_mem_internalSet.2 (hev_not.mono fun n hn ↦ ?_)
      simpa only [bSeq, hn, ↓reduceDIte] using hn.choose_spec.2.choose_spec.1
    have hfab : (internalFun f).apply (ofSeq aSeq) = (internalFun f).apply (ofSeq bSeq) := by
      refine Germ.coe_eq.2 (hev_not.mono fun n hn ↦ ?_)
      simpa only [aSeq, bSeq, hn, ↓reduceDIte] using hn.choose_spec.2.choose_spec.2.1
    have hab_eq : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), aSeq n = bSeq n :=
      Germ.coe_eq.1 (hinj ha_dom hb_dom hfab)
    obtain ⟨n, hn1, hn2⟩ := (hev_not.and hab_eq).exists
    have hne : aSeq n ≠ bSeq n := by
      simpa only [aSeq, bSeq, hn1, ↓reduceDIte] using hn1.choose_spec.2.choose_spec.2.2
    exact hne hn2
  · intro hev x hx y hy hxy
    rcases ofSeq_surjective x with ⟨rx, rfl⟩
    rcases ofSeq_surjective y with ⟨ry, rfl⟩
    have hrx : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), rx n ∈ (f n).dom := ofSeq_mem_internalSet.1 hx
    have hry : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ry n ∈ (f n).dom := ofSeq_mem_internalSet.1 hy
    have hfxy : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (f n).apply (rx n) = (f n).apply (ry n) :=
      Germ.coe_eq.1 hxy
    exact Germ.coe_eq.2 ((((hev.and hrx).and hry).and hfxy).mono
      fun n ⟨⟨⟨hinjn, h1⟩, h2⟩, h3⟩ ↦ hinjn h1 h2 h3)

/-- Partial inverse of a `RealPartialFun`, with domain `p.range`. -/
def RealPartialFun.inv (p : RealPartialFun) : RealPartialFun where
  dom := p.range
  apply y := if h : ∃ x ∈ p.dom, p.apply x = y then h.choose else 0
  default_outside y hy := by
    have hnot : ¬ ∃ x ∈ p.dom, p.apply x = y := hy
    simp [hnot]

/-- Partial inverse of an `InternalPartialFun`, with domain `F.range`. -/
def InternalPartialFun.inv (F : InternalPartialFun) : InternalPartialFun where
  dom := F.range
  apply y := if h : ∃ x ∈ F.dom, F.apply x = y then h.choose else 0
  default_outside y hy := by
    have hnot : ¬ ∃ x ∈ F.dom, F.apply x = y := hy
    simp [hnot]

/-- Left-inverse property of `InternalPartialFun.inv` when `F` is injective. -/
theorem InternalPartialFun.inv_apply_apply {F : InternalPartialFun} (hinj : F.IsInjective)
    {x : ℝ*} (hx : x ∈ F.dom) :
    F.inv.apply (F.apply x) = x := by
  have hex : ∃ z ∈ F.dom, F.apply z = F.apply x := ⟨x, hx, rfl⟩
  have hspec := hex.choose_spec
  have heq : hex.choose = x := hinj hspec.1 hx hspec.2
  simpa only [InternalPartialFun.inv, hex, ↓reduceDIte] using heq

/-- Right-inverse property of `InternalPartialFun.inv` on `F.range`. -/
theorem InternalPartialFun.apply_inv_apply (F : InternalPartialFun) {y : ℝ*} (hy : y ∈ F.range) :
    F.apply (F.inv.apply y) = y := by
  have hex : ∃ z ∈ F.dom, F.apply z = y := hy
  have hcho : F.inv.apply y = hex.choose := by
    simp only [InternalPartialFun.inv, hex, ↓reduceDIte]
  rw [hcho]
  exact hex.choose_spec.2

/-- Goldblatt Exercise 12.2(5) (p. 149): If `[f_n]` is injective, then `[f_n]⁻¹ = [f_n⁻¹]`, so the
inverse of an injective internal function is internal! -/
theorem internalFun_inv {f : ℕ → RealPartialFun} (hinj : (internalFun f).IsInjective) :
    (internalFun f).inv = internalFun (fun n ↦ (f n).inv) := by
  have hev_inj : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (f n).IsInjective :=
    internalFun_isInjective_iff.1 hinj
  rw [InternalPartialFun.eq_iff_dom_and_eqOn]
  have hdom : (internalFun f).inv.dom = internalSet (fun n ↦ ((f n).inv).dom) :=
    internalFun_image f (fun n ↦ (f n).dom)
  refine ⟨hdom, fun y hy ↦ ?_⟩
  obtain ⟨x, hx_dom, rfl⟩ := hy
  rw [InternalPartialFun.inv_apply_apply hinj hx_dom]
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  have hr_dom : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ (f n).dom :=
    ofSeq_mem_internalSet.1 hx_dom
  refine (Germ.coe_eq.2 ((hev_inj.and hr_dom).mono fun n ⟨hinjn, hrn⟩ ↦ ?_)).symm
  have hex : ∃ z ∈ (f n).dom, (f n).apply z = (f n).apply (r n) := ⟨r n, hrn, rfl⟩
  have hspec := hex.choose_spec
  have heq : hex.choose = r n := hinjn hspec.1 hrn hspec.2
  simpa only [RealPartialFun.inv, hex, ↓reduceDIte] using heq

/-- Goldblatt Exercise 12.2(5) corollary: The inverse of an injective internal function is
internal. -/
theorem IsInternalFun.inv {F : InternalPartialFun} (hF : IsInternalFun F)
    (hinj : F.IsInjective) :
    IsInternalFun F.inv := by
  rcases hF with ⟨f, rfl⟩
  exact ⟨fun n ↦ (f n).inv, internalFun_inv hinj⟩

/-- Pointwise sum `F + G` of two `InternalPartialFun`s (on `F.dom ∩ G.dom`, which equals `F.dom`
when `F.dom = G.dom`). -/
def InternalPartialFun.add (F G : InternalPartialFun) : InternalPartialFun :=
  InternalPartialFun.mkPartial (F.dom ∩ G.dom) (fun x ↦ F.apply x + G.apply x)

/-- Pointwise product `F * G` of two `InternalPartialFun`s on `F.dom ∩ G.dom`. -/
def InternalPartialFun.mul (F G : InternalPartialFun) : InternalPartialFun :=
  InternalPartialFun.mkPartial (F.dom ∩ G.dom) (fun x ↦ F.apply x * G.apply x)

/-- Scalar multiple `c • F` (`c ∈ ℝ*`) of an `InternalPartialFun` on `F.dom`. -/
def InternalPartialFun.smul (c : ℝ*) (F : InternalPartialFun) : InternalPartialFun :=
  InternalPartialFun.mkPartial F.dom (fun x ↦ c * F.apply x)

/-- Goldblatt Exercise 12.2(6a) (p. 149): If `F` and `G` are internal functions, then `F + G` is
internal. -/
theorem IsInternalFun.add {F G : InternalPartialFun} (hF : IsInternalFun F)
    (hG : IsInternalFun G) :
    IsInternalFun (F.add G) := by
  rcases hF with ⟨f, rfl⟩
  rcases hG with ⟨g, rfl⟩
  refine ⟨fun n ↦ RealPartialFun.mkPartial ((f n).dom ∩ (g n).dom)
    (fun x ↦ (f n).apply x + (g n).apply x), ?_⟩
  rw [InternalPartialFun.eq_iff_dom_and_eqOn]
  refine ⟨internalSet_inter _ _, fun x hx ↦ ?_⟩
  have hx' : x ∈ (internalFun f).dom ∩ (internalFun g).dom := hx
  have h1 : ((internalFun f).add (internalFun g)).apply x =
      (internalFun f).apply x + (internalFun g).apply x :=
    InternalPartialFun.mkPartial_apply_of_mem hx'
  rw [h1]
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ (f n).dom ∩ (g n).dom := by
    rw [internalFun_dom, internalFun_dom, internalSet_inter, ofSeq_mem_internalSet] at hx'
    exact hx'
  exact Germ.coe_eq.2 (hev.mono fun n hn ↦ by
    dsimp only
    rw [RealPartialFun.mkPartial_apply_of_mem hn])

/-- Goldblatt Exercise 12.2(6b) (p. 149): If `F` and `G` are internal functions, then `F * G` is
internal. -/
theorem IsInternalFun.mul {F G : InternalPartialFun} (hF : IsInternalFun F)
    (hG : IsInternalFun G) :
    IsInternalFun (F.mul G) := by
  rcases hF with ⟨f, rfl⟩
  rcases hG with ⟨g, rfl⟩
  refine ⟨fun n ↦ RealPartialFun.mkPartial ((f n).dom ∩ (g n).dom)
    (fun x ↦ (f n).apply x * (g n).apply x), ?_⟩
  rw [InternalPartialFun.eq_iff_dom_and_eqOn]
  refine ⟨internalSet_inter _ _, fun x hx ↦ ?_⟩
  have hx' : x ∈ (internalFun f).dom ∩ (internalFun g).dom := hx
  have h1 : ((internalFun f).mul (internalFun g)).apply x =
      (internalFun f).apply x * (internalFun g).apply x :=
    InternalPartialFun.mkPartial_apply_of_mem hx'
  rw [h1]
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ (f n).dom ∩ (g n).dom := by
    rw [internalFun_dom, internalFun_dom, internalSet_inter, ofSeq_mem_internalSet] at hx'
    exact hx'
  exact Germ.coe_eq.2 (hev.mono fun n hn ↦ by
    dsimp only
    rw [RealPartialFun.mkPartial_apply_of_mem hn])

/-- Goldblatt Exercise 12.2(6c) (p. 149): If `F` is an internal function and `c ∈ ℝ*`, then `c • F`
is internal. -/
theorem IsInternalFun.smul (c : ℝ*) {F : InternalPartialFun} (hF : IsInternalFun F) :
    IsInternalFun (F.smul c) := by
  rcases hF with ⟨f, rfl⟩
  rcases ofSeq_surjective c with ⟨s, rfl⟩
  refine ⟨fun n ↦ RealPartialFun.mkPartial (f n).dom (fun x ↦ s n * (f n).apply x), ?_⟩
  rw [InternalPartialFun.eq_iff_dom_and_eqOn]
  refine ⟨rfl, fun x hx ↦ ?_⟩
  have hx' : x ∈ (internalFun f).dom := hx
  have h1 : ((internalFun f).smul (ofSeq s)).apply x = ofSeq s * (internalFun f).apply x :=
    InternalPartialFun.mkPartial_apply_of_mem hx'
  rw [h1]
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ (f n).dom :=
    ofSeq_mem_internalSet.1 hx'
  exact Germ.coe_eq.2 (hev.mono fun n hn ↦ by
    dsimp only
    rw [RealPartialFun.mkPartial_apply_of_mem hn])

/-- Goldblatt Exercise 12.2(7) (p. 149): Let `F` be an internal function with nonempty domain that
takes only infinitesimal values (`∀ x ∈ F.dom, F.apply x ≈ₕ 0`). Then its range `F.range` has an
infinitesimal least upper bound! -/
theorem IsInternalFun.exists_infinitesimal_isLUB_range {F : InternalPartialFun}
    (hF : IsInternalFun F) (hne : F.dom.Nonempty)
    (hinf : ∀ x ∈ F.dom, F.apply x ≈ₕ (0 : ℝ*)) :
    ∃ u : ℝ*, IsInfinitesimal u ∧ IsLUB F.range u := by
  have hRange_int : IsInternal F.range := hF.isInternal_range
  have hRange_ne : F.range.Nonempty := hne.image F.apply
  have hsub : F.range ⊆ halo 0 := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hinf x hx).symm
  obtain ⟨c, _, hc_inf, hIcc⟩ :=
    hRange_int.subset_Icc_infinitesimal_of_subset_halo_zero hRange_ne hsub
  have hbdd : BddAbove F.range := ⟨c, fun y hy ↦ (hIcc hy).2⟩
  obtain ⟨u, hu⟩ := hRange_int.exists_isLUB hRange_ne hbdd
  obtain ⟨y₀, hy₀⟩ := hRange_ne
  have hc_nn : 0 ≤ c := by linarith [(hIcc hy₀).1, (hIcc hy₀).2]
  have huc : u ≤ |c| := (hu.2 fun y hy ↦ (hIcc hy).2).trans (le_abs_self c)
  have hcu : -|c| ≤ u := by
    rw [abs_of_nonneg hc_nn]
    exact (hIcc hy₀).1.trans (hu.1 hy₀)
  have hu_inf : IsInfinitesimal u :=
    isInfinitesimal_of_abs_le hc_inf (abs_le.2 ⟨hcu, huc⟩)
  exact ⟨u, hu_inf, hu⟩

/-- Goldblatt Exercise 12.2(8) (p. 149): Alternative proof that every infinite subset `B ⊆ ℝ` is
external, using Exercise 12.2(1) (`IsInternalFun.image`) in place of the Internal Set Definition
Principle! -/
theorem isExternal_infinite_real_via_image {B : Set ℝ} (hB : B.Infinite) :
    IsExternal ((fun r : ℝ ↦ (r : ℝ*)) '' B) := by
  intro hInt
  let e : ℕ ↪ B := hB.natEmbedding
  let g : ℝ → ℝ := fun r ↦
    if h : ∃ n : ℕ, (e n : ℝ) = r then (h.choose : ℝ) else 0
  have hg_val : ∀ n : ℕ, g (e n : ℝ) = (n : ℝ) := by
    intro n
    have hex : ∃ m : ℕ, (e m : ℝ) = (e n : ℝ) := ⟨n, rfl⟩
    have hm : hex.choose = n := e.injective (Subtype.ext hex.choose_spec)
    simpa only [g, hex, ↓reduceDIte] using congrArg (Nat.cast : ℕ → ℝ) hm
  let F : InternalPartialFun := starInternalFun Set.univ g
  have hF : IsInternalFun F := isInternalFun_starInternalFun Set.univ g
  have himg_int : IsInternal (F.apply '' ((fun r : ℝ ↦ (r : ℝ*)) '' B)) := hF.image hInt
  have himg_eq : F.apply '' ((fun r : ℝ ↦ (r : ℝ*)) '' B) = Set.range (Nat.cast : ℕ → ℝ*) := by
    ext y
    constructor
    · rintro ⟨_, ⟨r, _, rfl⟩, rfl⟩
      have hmem : (r : ℝ*) ∈ starSet (Set.univ : Set ℝ) := coe_mem_starSet.2 (Set.mem_univ r)
      have hFr : F.apply (r : ℝ*) = ((g r : ℝ) : ℝ*) := by
        rw [starInternalFun_apply_of_mem hmem, starFun_coe]
      rw [hFr]
      by_cases hex : ∃ n : ℕ, (e n : ℝ) = r
      · refine ⟨hex.choose, ?_⟩
        have hg_eq : g r = (hex.choose : ℝ) := by simp only [g, hex, ↓reduceDIte]
        rw [hg_eq, coe_natCast_hyperreal]
      · refine ⟨0, ?_⟩
        have hg_eq : g r = 0 := by simp only [g, hex, ↓reduceDIte]
        simp [hg_eq]
    · rintro ⟨n, rfl⟩
      refine ⟨((e n : ℝ) : ℝ*), ⟨(e n : ℝ), (e n).2, rfl⟩, ?_⟩
      have hmem : ((e n : ℝ) : ℝ*) ∈ starSet (Set.univ : Set ℝ) :=
        coe_mem_starSet.2 (Set.mem_univ _)
      rw [starInternalFun_apply_of_mem hmem, starFun_coe, hg_val n, coe_natCast_hyperreal]
  exact isExternal_nat_in_hyperreal (himg_eq ▸ himg_int)

/-! ## §12.3–12.4 Hyperfinite Sets and Internal Cardinality -/

/-- Goldblatt §12.3 (p. 149): An internal set `X ⊆ ℝ*` is **hyperfinite** if `X = [A_n]` with
`{n ∈ ℕ | A_n is finite} ∈ 𝓕`. -/
def IsHyperfinite (X : Set ℝ*) : Prop :=
  ∃ A : ℕ → Set ℝ, X = internalSet A ∧ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (A n).Finite

/-- Every hyperfinite set is internal. -/
theorem IsHyperfinite.isInternal {X : Set ℝ*} (hX : IsHyperfinite X) : IsInternal X := by
  rcases hX with ⟨A, rfl, _⟩
  exact ⟨A, rfl⟩

/-- `X` is hyperfinite iff `X = [(S_n : Set ℝ)]` for an everywhere-finite sequence `S : ℕ → Finset ℝ`
(Goldblatt §12.3, p. 149: "by 11.2(3) we may as well assume that all `A_n`'s are finite"). -/
theorem isHyperfinite_iff_exists_finset {X : Set ℝ*} :
    IsHyperfinite X ↔ ∃ S : ℕ → Finset ℝ, X = internalSet (fun n ↦ (S n : Set ℝ)) := by
  constructor
  · rintro ⟨A, rfl, hev⟩
    let S : ℕ → Finset ℝ := fun n ↦ if h : (A n).Finite then h.toFinset else ∅
    refine ⟨S, internalSet_eq_iff.2 (hev.mono fun n hn ↦ ?_)⟩
    simpa only [S, hn, ↓reduceDIte] using hn.coe_toFinset.symm
  · rintro ⟨S, rfl⟩
    exact ⟨fun n ↦ (S n : Set ℝ), rfl, Eventually.of_forall fun n ↦ Finset.finite_toSet (S n)⟩

/-- Goldblatt §12.3 (p. 149): Relational predicate `HasHypercard X N` asserting that `X` is a
hyperfinite set of internal cardinality `N = [|S_n|] ∈ ℕ*`. -/
def HasHypercard (X : Set ℝ*) (N : ℕ*) : Prop :=
  ∃ S : ℕ → Finset ℝ, X = internalSet (fun n ↦ (S n : Set ℝ)) ∧
    N = ((fun n ↦ (S n).card) : ℕ*)

/-- `HasHypercard X N` implies `IsHyperfinite X`. -/
theorem HasHypercard.isHyperfinite {X : Set ℝ*} {N : ℕ*} (h : HasHypercard X N) :
    IsHyperfinite X := by
  rcases h with ⟨S, hX, _⟩
  exact isHyperfinite_iff_exists_finset.2 ⟨S, hX⟩

/-- Uniqueness of internal cardinality: if `HasHypercard X N` and `HasHypercard X M`, then `N = M`. -/
theorem HasHypercard.unique {X : Set ℝ*} {N M : ℕ*}
    (hN : HasHypercard X N) (hM : HasHypercard X M) :
    N = M := by
  rcases hN with ⟨S, hXS, rfl⟩
  rcases hM with ⟨T, hXT, rfl⟩
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (S n : Set ℝ) = (T n : Set ℝ) :=
    internalSet_eq_iff.1 (hXS.symm.trans hXT)
  exact Germ.coe_eq.2 (hev.mono fun n hn ↦ congrArg Finset.card (Finset.coe_inj.1 hn))

/-- Goldblatt §12.3 (p. 149): The internal cardinality `|X| ∈ ℕ*` of a hyperfinite set `X`. -/
def IsHyperfinite.hypercard {X : Set ℝ*} (hX : IsHyperfinite X) : ℕ* :=
  ((fun n ↦ ((isHyperfinite_iff_exists_finset.1 hX).choose n).card) : ℕ*)

/-- `hX.hypercard` satisfies `HasHypercard X hX.hypercard`. -/
theorem IsHyperfinite.hasHypercard {X : Set ℝ*} (hX : IsHyperfinite X) :
    HasHypercard X hX.hypercard :=
  ⟨(isHyperfinite_iff_exists_finset.1 hX).choose,
   (isHyperfinite_iff_exists_finset.1 hX).choose_spec, rfl⟩

/-- `HasHypercard X N` characterizes `hX.hypercard = N`. -/
theorem HasHypercard.hypercard_eq {X : Set ℝ*} {N : ℕ*} (h : HasHypercard X N) :
    h.isHyperfinite.hypercard = N :=
  h.isHyperfinite.hasHypercard.unique h

/-- Empty set is hyperfinite of internal cardinality `0`. -/
theorem hasHypercard_empty : HasHypercard (∅ : Set ℝ*) 0 :=
  ⟨fun _ ↦ ∅, by simp, rfl⟩

/-- `∅` is hyperfinite. -/
theorem isHyperfinite_empty : IsHyperfinite (∅ : Set ℝ*) :=
  hasHypercard_empty.isHyperfinite

/-- Initial segment `{1, …, N}` embedded in `ℝ*` (`Hypernat.toHyperreal '' Set.Icc 1 N`). -/
def hyperIccOne (N : ℕ*) : Set ℝ* :=
  Hypernat.toHyperreal '' Set.Icc (1 : ℕ*) N

/-- Componentwise `Finset` representation of `hyperIccOne (b : ℕ*)`. -/
theorem hyperIccOne_eq_internalSet (b : ℕ → ℕ) :
    hyperIccOne (b : ℕ*) =
      internalSet (fun n ↦ (((Finset.Icc 1 (b n)).image (Nat.cast : ℕ → ℝ)) : Set ℝ)) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  constructor
  · rintro ⟨K, ⟨h1K, hKb⟩, hKx⟩
    induction K using Germ.inductionOn with | _ a =>
    have ha1 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 1 ≤ a n := Germ.coe_le.1 h1K
    have hab : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), a n ≤ b n := Germ.coe_le.1 hKb
    have har : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (a n : ℝ) = r n := Germ.coe_eq.1 hKx
    refine ofSeq_mem_internalSet.2 (((ha1.and hab).and har).mono fun n ⟨⟨h1, h2⟩, h3⟩ ↦ ?_)
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨a n, Finset.mem_Icc.2 ⟨h1, h2⟩, h3⟩)
  · intro hx
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
        ∃ k : ℕ, (1 ≤ k ∧ k ≤ b n) ∧ (k : ℝ) = r n := by
      refine (ofSeq_mem_internalSet.1 hx).mono fun n hn ↦ ?_
      obtain ⟨k, hk, hkr⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hn)
      exact ⟨k, Finset.mem_Icc.1 hk, hkr⟩
    let a : ℕ → ℕ := fun n ↦
      if h : ∃ k : ℕ, (1 ≤ k ∧ k ≤ b n) ∧ (k : ℝ) = r n then h.choose else 1
    refine ⟨(a : ℕ*), ⟨Germ.coe_le.2 ?_, Germ.coe_le.2 ?_⟩, Germ.coe_eq.2 ?_⟩
    · exact hev.mono fun n hn ↦ by simpa only [a, hn, ↓reduceDIte] using hn.choose_spec.1.1
    · exact hev.mono fun n hn ↦ by simpa only [a, hn, ↓reduceDIte] using hn.choose_spec.1.2
    · exact hev.mono fun n hn ↦ by
        simpa only [Function.comp_apply, a, hn, ↓reduceDIte] using hn.choose_spec.2

/-- Goldblatt §12.3 Example 4 (p. 150): `{1, 2, …, N}` (`hyperIccOne N`) is hyperfinite of
internal cardinality `N`! -/
theorem hasHypercard_Icc_one (N : ℕ*) : HasHypercard (hyperIccOne N) N := by
  induction N using Germ.inductionOn with | _ b =>
  refine ⟨fun n ↦ (Finset.Icc 1 (b n)).image (Nat.cast : ℕ → ℝ),
    hyperIccOne_eq_internalSet b, Germ.coe_eq.2 (Eventually.of_forall fun n ↦ ?_)⟩
  dsimp only
  rw [Finset.card_image_of_injective _ Nat.cast_injective, Nat.card_Icc]
  omega

/-- Goldblatt §12.3 Example 1 (p. 149): `hyperIccOne omegaNat` (`[ {1, …, n} ]`, where `n + 1` in
0-based indexing or `omegaNat`) has internal cardinality `omegaNat`, contains all standard positive
naturals `(m : ℝ*)` (`m ≥ 1`), and is uncountable! -/
theorem hasHypercard_Icc_one_omegaNat :
    HasHypercard (hyperIccOne omegaNat) omegaNat ∧
    (∀ m : ℕ, 1 ≤ m → (m : ℝ*) ∈ hyperIccOne omegaNat) ∧
    ¬ (hyperIccOne omegaNat).Countable := by
  refine ⟨hasHypercard_Icc_one omegaNat, fun m hm ↦ ?_, ?_⟩
  · refine ⟨(m : ℕ*), ⟨by exact_mod_cast hm, (isUnlimitedNat_omegaNat m).le⟩,
      Hypernat.toHyperreal_natCast m⟩
  · have hInt : IsInternal (hyperIccOne omegaNat) := (hasHypercard_Icc_one omegaNat).isHyperfinite.isInternal
    have hInf : (hyperIccOne omegaNat).Infinite := by
      refine Set.infinite_of_injective_forall_mem
        (f := fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ*))
        (fun m n hmn ↦ by
          dsimp only at hmn
          exact Nat.succ_inj.1 (Nat.cast_injective hmn))
        (fun m ↦ ⟨((m + 1 : ℕ) : ℕ*),
          ⟨by exact_mod_cast Nat.succ_pos m, (isUnlimitedNat_omegaNat (m + 1)).le⟩,
          Hypernat.toHyperreal_natCast (m + 1)⟩)
    exact hInt.not_countable_of_infinite hInf

/-- Goldblatt §12.3 Example 2 (pp. 149–150, **Hyperfinite Approximation of Countable Sets**):
For any countable subset `B ⊆ ℝ`, there exists a hyperfinite set `A ⊆ ℝ*` such that
`((↑) '' B) ⊆ A` and `A ⊆ starSet B`. -/
theorem exists_hyperfinite_approx_of_countable {B : Set ℝ} (hB : B.Countable) :
    ∃ A : Set ℝ*, IsHyperfinite A ∧ ((fun r : ℝ ↦ (r : ℝ*)) '' B) ⊆ A ∧ A ⊆ starSet B := by
  rcases B.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, isHyperfinite_empty, by simp, by simp⟩
  · obtain ⟨x, rfl⟩ := hB.exists_eq_range hne
    let S : ℕ → Finset ℝ := fun n ↦ (Finset.range (n + 1)).image x
    let A : Set ℝ* := internalSet (fun n ↦ (S n : Set ℝ))
    refine ⟨A, isHyperfinite_iff_exists_finset.2 ⟨S, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      dsimp only
      rw [show ((x m : ℝ) : ℝ*) = ofSeq (fun _ ↦ x m) from rfl, ofSeq_mem_internalSet]
      have hge : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), m ≤ n :=
        Nat.hyperfilter_le_atTop (eventually_ge_atTop m)
      exact hge.mono fun n hmn ↦ Finset.mem_coe.2
        (Finset.mem_image.2 ⟨m, Finset.mem_range.2 (Nat.lt_succ_of_le hmn), rfl⟩)
    · rw [← internalSet_const]
      refine internalSet_subset_iff.2 (Eventually.of_forall fun n r hr ↦ ?_)
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hr)
      exact ⟨k, rfl⟩

/-- Singleton `{c}` is hyperfinite of internal cardinality `1`. -/
theorem hasHypercard_singleton (c : ℝ*) : HasHypercard ({c} : Set ℝ*) 1 := by
  rcases ofSeq_surjective c with ⟨s, rfl⟩
  refine ⟨fun n ↦ {s n}, ?_, rfl⟩
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp only [Finset.coe_singleton, Set.mem_singleton_iff, ofSeq_mem_internalSet]
  exact Germ.coe_eq

/-- Goldblatt §12.4 Exercise 2 (p. 150): Union and intersection of two hyperfinite sets `X` and `Y`
are hyperfinite, with `|X ∪ Y| + |X ∩ Y| = |X| + |Y|`! -/
theorem hypercard_union_add_hypercard_inter {X Y : Set ℝ*} {NX NY : ℕ*}
    (hX : HasHypercard X NX) (hY : HasHypercard Y NY) :
    ∃ NU NI : ℕ*, HasHypercard (X ∪ Y) NU ∧ HasHypercard (X ∩ Y) NI ∧ NU + NI = NX + NY := by
  rcases hX with ⟨S, rfl, rfl⟩
  rcases hY with ⟨T, rfl, rfl⟩
  refine ⟨((fun n ↦ (S n ∪ T n).card) : ℕ*), ((fun n ↦ (S n ∩ T n).card) : ℕ*), ?_, ?_, ?_⟩
  · refine ⟨fun n ↦ S n ∪ T n, ?_, rfl⟩
    rw [internalSet_union]
    exact internalSet_eq_iff.2 (Eventually.of_forall fun n ↦ (Finset.coe_union (S n) (T n)).symm)
  · refine ⟨fun n ↦ S n ∩ T n, ?_, rfl⟩
    rw [internalSet_inter]
    exact internalSet_eq_iff.2 (Eventually.of_forall fun n ↦ (Finset.coe_inter (S n) (T n)).symm)
  · exact Germ.coe_eq.2 (Eventually.of_forall fun n ↦ Finset.card_union_add_card_inter (S n) (T n))

/-- Binary union of hyperfinite sets is hyperfinite. -/
theorem IsHyperfinite.union {X Y : Set ℝ*} (hX : IsHyperfinite X) (hY : IsHyperfinite Y) :
    IsHyperfinite (X ∪ Y) := by
  obtain ⟨NU, _, hU, _, _⟩ := hypercard_union_add_hypercard_inter hX.hasHypercard hY.hasHypercard
  exact hU.isHyperfinite

/-- Binary intersection of hyperfinite sets is hyperfinite. -/
theorem IsHyperfinite.inter {X Y : Set ℝ*} (hX : IsHyperfinite X) (hY : IsHyperfinite Y) :
    IsHyperfinite (X ∩ Y) := by
  obtain ⟨_, NI, _, hI, _⟩ := hypercard_union_add_hypercard_inter hX.hasHypercard hY.hasHypercard
  exact hI.isHyperfinite

/-- Disjoint hyperfinite union adds internal cardinalities: `|X ∪ Y| = |X| + |Y|`. -/
theorem HasHypercard.union_disjoint {X Y : Set ℝ*} {NX NY : ℕ*}
    (hX : HasHypercard X NX) (hY : HasHypercard Y NY) (hdisj : Disjoint X Y) :
    HasHypercard (X ∪ Y) (NX + NY) := by
  obtain ⟨NU, NI, hU, hI, hsum⟩ := hypercard_union_add_hypercard_inter hX hY
  have hXY_empty : X ∩ Y = ∅ := Set.disjoint_iff_inter_eq_empty.1 hdisj
  have hNI0 : NI = 0 := hI.unique (hXY_empty ▸ hasHypercard_empty)
  subst hNI0
  rw [add_zero] at hsum
  exact hsum ▸ hU

/-- Goldblatt §12.3 Example 3 (p. 150): Every finite set `s : Finset ℝ*` is hyperfinite with
internal cardinality `(s.card : ℕ*)`! -/
theorem hasHypercard_finset (s : Finset ℝ*) :
    HasHypercard (s : Set ℝ*) (s.card : ℕ*) := by
  induction s using Finset.cons_induction with
  | empty => simpa using hasHypercard_empty
  | cons a t hat ih =>
      rw [Finset.cons_eq_insert, Finset.coe_insert, Set.insert_eq, Finset.card_insert_of_notMem hat]
      have hdisj : Disjoint ({a} : Set ℝ*) (t : Set ℝ*) :=
        Set.disjoint_singleton_left.2 (Finset.mem_coe.not.2 hat)
      have h1 := (hasHypercard_singleton a).union_disjoint ih hdisj
      simpa [add_comm] using h1

/-- Every finite subset of `ℝ*` is hyperfinite. -/
theorem IsHyperfinite.of_finite {X : Set ℝ*} (hX : X.Finite) : IsHyperfinite X := by
  rw [← hX.coe_toFinset]
  exact (hasHypercard_finset hX.toFinset).isHyperfinite

/-- Goldblatt §12.3 Example 5 (p. 150): For any `a, b ∈ ℝ*` with `a ≠ b` and any `N ∈ ℕ*` with
`1 ≤ N`, the uniform partition `{a + k(b - a)/N | k ∈ ℕ*, k ≤ N}` is hyperfinite of internal
cardinality `N + 1`! -/
theorem hasHypercard_uniformPartition {a b : ℝ*} (hab : a ≠ b) {N : ℕ*} (hN : (1 : ℕ*) ≤ N) :
    HasHypercard
      {x : ℝ* | ∃ k : ℕ*, k ≤ N ∧ x = a + Hypernat.toHyperreal k * (b - a) / Hypernat.toHyperreal N}
      (N + 1) := by
  rcases ofSeq_surjective a with ⟨sa, rfl⟩
  rcases ofSeq_surjective b with ⟨sb, rfl⟩
  induction N using Germ.inductionOn with | _ c =>
  have hev_ab : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), sa n ≠ sb n :=
    Ultrafilter.eventually_not.2 (fun h ↦ hab (Germ.coe_eq.2 h))
  have hev_c1 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 1 ≤ c n := Germ.coe_le.1 hN
  let g : ℕ → ℕ → ℝ := fun n k ↦ sa n + (k : ℝ) * (sb n - sa n) / (c n : ℝ)
  let S : ℕ → Finset ℝ := fun n ↦
    if sa n ≠ sb n ∧ 1 ≤ c n then (Finset.range (c n + 1)).image (g n)
    else (Finset.range (c n + 1)).image (Nat.cast : ℕ → ℝ)
  refine ⟨S, ?_, ?_⟩
  · ext x
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    constructor
    · rintro ⟨k, hkc, hrx⟩
      induction k using Germ.inductionOn with | _ d =>
      have hdc : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), d n ≤ c n := Germ.coe_le.1 hkc
      have hrg : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n = g n (d n) := Germ.coe_eq.1 hrx
      refine ofSeq_mem_internalSet.2
        ((((hev_ab.and hev_c1).and hdc).and hrg).mono fun n ⟨⟨hcond, hd⟩, hrn⟩ ↦ ?_)
      have hmem : r n ∈ ((Finset.range (c n + 1)).image (g n) : Set ℝ) :=
        Finset.mem_coe.2 (Finset.mem_image.2 ⟨d n, Finset.mem_range.2 (Nat.lt_succ_of_le hd), hrn.symm⟩)
      dsimp only [S]
      rw [ite_eq_left hcond]
      exact hmem
    · intro hx
      have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ k : ℕ, k ≤ c n ∧ r n = g n k := by
        refine ((hev_ab.and hev_c1).and (ofSeq_mem_internalSet.1 hx)).mono fun n ⟨hcond, hrS⟩ ↦ ?_
        have hr_img : r n ∈ ((Finset.range (c n + 1)).image (g n) : Set ℝ) := by
          dsimp only [S] at hrS
          rwa [ite_eq_left hcond] at hrS
        obtain ⟨k, hk, hgk⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hr_img)
        exact ⟨k, Nat.lt_succ_iff.1 (Finset.mem_range.1 hk), hgk.symm⟩
      let d : ℕ → ℕ := fun n ↦ if h : ∃ k : ℕ, k ≤ c n ∧ r n = g n k then h.choose else 0
      refine ⟨(d : ℕ*), Germ.coe_le.2 ?_, Germ.coe_eq.2 ?_⟩
      · exact hev.mono fun n hn ↦ by simpa only [d, hn, ↓reduceDIte] using hn.choose_spec.1
      · exact hev.mono fun n hn ↦ by
          simpa only [Function.comp_apply, g, d, hn, ↓reduceDIte] using hn.choose_spec.2
  · refine (Germ.coe_eq.2 ((hev_ab.and hev_c1).mono fun n ⟨hne_n, hc1_n⟩ ↦ ?_)).symm
    have hcond : sa n ≠ sb n ∧ 1 ≤ c n := ⟨hne_n, hc1_n⟩
    have hinj : Function.Injective (g n) := by
      intro i j hij
      dsimp only [g] at hij
      have hcn_ne : (c n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have hdiff_ne : sb n - sa n ≠ 0 := sub_ne_zero.2 hne_n.symm
      have hmul : (i : ℝ) * (sb n - sa n) = (j : ℝ) * (sb n - sa n) := by
        have := add_left_cancel hij
        exact (div_left_inj' hcn_ne).1 this
      exact Nat.cast_injective (mul_right_cancel₀ hdiff_ne hmul)
    dsimp only [S]
    rw [ite_eq_left hcond,
      Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- Goldblatt Exercise 12.4(1) (p. 150): Every nonempty hyperfinite set `X` has a greatest element
and a least element! -/
theorem IsHyperfinite.exists_isGreatest_and_isLeast {X : Set ℝ*}
    (hX : IsHyperfinite X) (hne : X.Nonempty) :
    (∃ M ∈ X, ∀ x ∈ X, x ≤ M) ∧ (∃ m ∈ X, ∀ x ∈ X, m ≤ x) := by
  obtain ⟨S, rfl⟩ := isHyperfinite_iff_exists_finset.1 hX
  have hev_ne : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (S n).Nonempty := by
    refine (internalSet_nonempty_iff.1 hne).mono fun n ⟨x, hx⟩ ↦ ⟨x, Finset.mem_coe.1 hx⟩
  let maxSeq : ℕ → ℝ := fun n ↦ if h : (S n).Nonempty then (S n).max' h else 0
  let minSeq : ℕ → ℝ := fun n ↦ if h : (S n).Nonempty then (S n).min' h else 0
  refine ⟨⟨ofSeq maxSeq, ofSeq_mem_internalSet.2 ?_, fun x hx ↦ ?_⟩,
          ⟨ofSeq minSeq, ofSeq_mem_internalSet.2 ?_, fun x hx ↦ ?_⟩⟩
  · exact hev_ne.mono fun n hn ↦ by
      simpa only [maxSeq, hn, ↓reduceDIte, Finset.mem_coe] using Finset.max'_mem (S n) hn
  · rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hr : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ S n :=
      (ofSeq_mem_internalSet.1 hx).mono fun n hn ↦ Finset.mem_coe.1 hn
    refine ofSeq_le_ofSeq.2 ((hev_ne.and hr).mono fun n ⟨hn, hrn⟩ ↦ ?_)
    simpa only [maxSeq, hn, ↓reduceDIte] using Finset.le_max' (S n) (r n) hrn
  · exact hev_ne.mono fun n hn ↦ by
      simpa only [minSeq, hn, ↓reduceDIte, Finset.mem_coe] using Finset.min'_mem (S n) hn
  · rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hr : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ S n :=
      (ofSeq_mem_internalSet.1 hx).mono fun n hn ↦ Finset.mem_coe.1 hn
    refine ofSeq_le_ofSeq.2 ((hev_ne.and hr).mono fun n ⟨hn, hrn⟩ ↦ ?_)
    simpa only [minSeq, hn, ↓reduceDIte] using Finset.min'_le (S n) (r n) hrn

/-- Goldblatt Exercise 12.4(3) (p. 150): Any internal subset `Y` of a hyperfinite set `X` is
hyperfinite (with `|Y| ≤ |X|`). -/
theorem IsHyperfinite.of_isInternal_subset {X Y : Set ℝ*}
    (hX : IsHyperfinite X) (hY : IsInternal Y) (hYX : Y ⊆ X) :
    IsHyperfinite Y ∧ ∃ NY NX : ℕ*, HasHypercard Y NY ∧ HasHypercard X NX ∧ NY ≤ NX := by
  obtain ⟨S, rfl⟩ := isHyperfinite_iff_exists_finset.1 hX
  rcases hY with ⟨B, rfl⟩
  have hev_sub : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), B n ⊆ (S n : Set ℝ) :=
    internalSet_subset_iff.1 hYX
  have hev_fin : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (B n).Finite :=
    hev_sub.mono fun n hn ↦ (Finset.finite_toSet (S n)).subset hn
  have hY_hyp : IsHyperfinite (internalSet B) := ⟨B, rfl, hev_fin⟩
  let T : ℕ → Finset ℝ := fun n ↦ if h : (B n).Finite then h.toFinset else ∅
  have hBT : internalSet B = internalSet (fun n ↦ (T n : Set ℝ)) :=
    internalSet_eq_iff.2 (hev_fin.mono fun n hn ↦ by
      simpa only [T, hn, ↓reduceDIte] using hn.coe_toFinset.symm)
  refine ⟨hY_hyp, ((fun n ↦ (T n).card) : ℕ*), ((fun n ↦ (S n).card) : ℕ*),
    ⟨T, hBT, rfl⟩, ⟨S, rfl, rfl⟩, ?_⟩
  refine Germ.coe_le.2 ((hev_sub.and hev_fin).mono fun n ⟨hsubn, hfinn⟩ ↦ ?_)
  have hT_sub : T n ⊆ S n := by
    intro x hx
    have hxB : x ∈ B n := by simpa only [T, hfinn, ↓reduceDIte, hfinn.mem_toFinset] using hx
    exact Finset.mem_coe.1 (hsubn hxB)
  exact Finset.card_le_card hT_sub

/-- Set difference of hyperfinite sets is hyperfinite. -/
theorem IsHyperfinite.sdiff {X Y : Set ℝ*} (hX : IsHyperfinite X) (hY : IsHyperfinite Y) :
    IsHyperfinite (X \ Y) :=
  (hX.of_isInternal_subset (hX.isInternal.sdiff hY.isInternal) Set.sdiff_subset).1

/-! ## §12.5 Counting a Hyperfinite Set -/

/-- Goldblatt Theorem 12.5.1 (p. 151):
An internal set `A ⊆ ℝ*` is hyperfinite with internal cardinality `N ∈ ℕ*` **if and only if**
there is an internal bijection `f : {1, …, N} → A` (`f.dom = hyperIccOne N`, `f.IsInjective`, and
`f.range = A`). -/
theorem hasHypercard_iff_exists_internal_bijection {A : Set ℝ*} {N : ℕ*} :
    HasHypercard A N ↔
      ∃ f : InternalPartialFun, IsInternalFun f ∧
        f.dom = hyperIccOne N ∧ f.IsInjective ∧ f.range = A := by
  constructor
  · rintro ⟨S, rfl, rfl⟩
    let I : ℕ → Finset ℝ := fun n ↦ (Finset.Icc 1 (S n).card).image (Nat.cast : ℕ → ℝ)
    have hcard_eq : ∀ n : ℕ, Fintype.card (I n) = Fintype.card (S n) := fun n ↦ by
      rw [Fintype.card_coe, Fintype.card_coe]
      dsimp only [I]
      rw [Finset.card_image_of_injective _ Nat.cast_injective, Nat.card_Icc]
      omega
    let e : ∀ n : ℕ, ↥(I n) ≃ ↥(S n) := fun n ↦ Fintype.equivOfCardEq (hcard_eq n)
    let p : ℕ → RealPartialFun := fun n ↦
      { dom := (I n : Set ℝ)
        apply := fun x ↦ if hx : x ∈ (I n : Set ℝ) then (e n ⟨x, hx⟩ : ℝ) else 0
        default_outside := fun x hx ↦ by simp [hx] }
    refine ⟨internalFun p, isInternalFun_internalFun p, ?_, ?_, ?_⟩
    · exact (hyperIccOne_eq_internalSet (fun n ↦ (S n).card)).symm
    · refine internalFun_isInjective_iff.2 (Eventually.of_forall fun n x hx y hy hxy ↦ ?_)
      have hxI : x ∈ I n := Finset.mem_coe.1 hx
      have hyI : y ∈ I n := Finset.mem_coe.1 hy
      have heq_val : (e n ⟨x, hxI⟩ : ℝ) = (e n ⟨y, hyI⟩ : ℝ) := by
        simpa only [p, Finset.mem_coe, hxI, hyI, ↓reduceDIte] using hxy
      have heq_sub : e n ⟨x, hxI⟩ = e n ⟨y, hyI⟩ := Subtype.ext heq_val
      exact congrArg Subtype.val ((e n).injective heq_sub)
    · change (internalFun p).apply '' (internalFun p).dom = internalSet (fun n ↦ (S n : Set ℝ))
      rw [internalFun_dom, internalFun_image]
      refine internalSet_eq_iff.2 (Eventually.of_forall fun n ↦ ?_)
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hxI : x ∈ I n := Finset.mem_coe.1 hx
        simpa only [p, Finset.mem_coe, hxI, ↓reduceDIte] using (e n ⟨x, hxI⟩).2
      · intro hy
        have hyS : y ∈ S n := Finset.mem_coe.1 hy
        let xSub := (e n).symm ⟨y, hyS⟩
        refine ⟨(xSub : ℝ), Finset.mem_coe.2 xSub.2, ?_⟩
        have hxI : (xSub : ℝ) ∈ I n := xSub.2
        have he_apply : e n ⟨(xSub : ℝ), hxI⟩ = ⟨y, hyS⟩ := (e n).apply_symm_apply ⟨y, hyS⟩
        simpa only [p, Finset.mem_coe, hxI, ↓reduceDIte] using congrArg Subtype.val he_apply
  · rintro ⟨f, ⟨p, rfl⟩, hdom, hinj, rfl⟩
    induction N using Germ.inductionOn with | _ b =>
    let I : ℕ → Finset ℝ := fun n ↦ (Finset.Icc 1 (b n)).image (Nat.cast : ℕ → ℝ)
    have hev_dom : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (p n).dom = (I n : Set ℝ) := by
      rw [internalFun_dom, hyperIccOne_eq_internalSet] at hdom
      exact internalSet_eq_iff.1 hdom
    have hev_inj : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (p n).IsInjective :=
      internalFun_isInjective_iff.1 hinj
    let S : ℕ → Finset ℝ := fun n ↦
      if (p n).dom = (I n : Set ℝ) ∧ (p n).IsInjective then (I n).image (p n).apply
      else I n
    refine ⟨S, ?_, ?_⟩
    · change (internalFun p).apply '' (internalFun p).dom = internalSet (fun n ↦ (S n : Set ℝ))
      rw [internalFun_dom, internalFun_image]
      refine internalSet_eq_iff.2 ((hev_dom.and hev_inj).mono fun n ⟨hdn, hinjn⟩ ↦ ?_)
      have hcond : (p n).dom = (I n : Set ℝ) ∧ (p n).IsInjective := ⟨hdn, hinjn⟩
      dsimp only [S]
      rw [ite_eq_left hcond, Finset.coe_image, hdn]
    · refine (Germ.coe_eq.2 ((hev_dom.and hev_inj).mono fun n ⟨hdn, hinjn⟩ ↦ ?_)).symm
      have hcond : (p n).dom = (I n : Set ℝ) ∧ (p n).IsInjective := ⟨hdn, hinjn⟩
      have hinj_I : Set.InjOn (p n).apply (I n : Set ℝ) := hdn ▸ hinjn
      have hcard_I : (I n).card = b n := by
        dsimp only [I]
        rw [Finset.card_image_of_injective _ Nat.cast_injective, Nat.card_Icc]
        omega
      dsimp only [S]
      rw [ite_eq_left hcond, Finset.card_image_of_injOn hinj_I, hcard_I]

/-! ## §12.6 Hyperfinite Pigeonhole Principle -/

/-- Goldblatt Theorem 12.6.1 (pp. 151–152, **Hyperfinite Pigeonhole Principle**):
An internal set `A ⊆ ℝ*` is hyperfinite **if and only if** every injective internal function `f`
whose domain includes `A` and satisfies `f(A) ⊆ A` must satisfy `f(A) = A`! -/
theorem isHyperfinite_iff_pigeonhole {A : Set ℝ*} (hA : IsInternal A) :
    IsHyperfinite A ↔
      ∀ f : InternalPartialFun, IsInternalFun f → f.IsInjective →
        A ⊆ f.dom → f.apply '' A ⊆ A → f.apply '' A = A := by
  constructor
  · intro hHyp f hf hinj hsub_dom hsub_img
    obtain ⟨S, rfl⟩ := isHyperfinite_iff_exists_finset.1 hHyp
    rcases hf with ⟨p, rfl⟩
    have hev_dom : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (S n : Set ℝ) ⊆ (p n).dom :=
      internalSet_subset_iff.1 hsub_dom
    have hev_img : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (p n).apply '' (S n : Set ℝ) ⊆ (S n : Set ℝ) := by
      rw [internalFun_image] at hsub_img
      exact internalSet_subset_iff.1 hsub_img
    have hev_inj : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (p n).IsInjective :=
      internalFun_isInjective_iff.1 hinj
    rw [internalFun_image]
    refine internalSet_eq_iff.2 (((hev_dom.and hev_img).and hev_inj).mono
      fun n ⟨⟨hdomn, himgn⟩, hinjn⟩ ↦ ?_)
    have hinjS : Set.InjOn (p n).apply (S n : Set ℝ) := hinjn.mono hdomn
    let T : Finset ℝ := (S n).image (p n).apply
    have hTS : T ⊆ S n := by
      intro y hy
      have hy_set : y ∈ (p n).apply '' (S n : Set ℝ) := by
        simpa only [T, ← Finset.coe_image, Finset.mem_coe] using hy
      exact Finset.mem_coe.1 (himgn hy_set)
    have hcard : (S n).card ≤ T.card := by
      dsimp only [T]
      rw [Finset.card_image_of_injOn hinjS]
    have hTeq : T = S n := Finset.eq_of_subset_of_card_le hTS hcard
    have hcoe := congrArg (fun U : Finset ℝ ↦ (U : Set ℝ)) hTeq
    simpa only [T, Finset.coe_image] using hcoe
  · intro hpig
    rcases hA with ⟨B, rfl⟩
    by_contra hnot_hyp
    have hnot_ev : ¬ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (B n).Finite :=
      fun hfin ↦ hnot_hyp ⟨B, rfl, hfin⟩
    have hev_inf : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (B n).Infinite :=
      Ultrafilter.eventually_not.2 hnot_ev
    -- On each infinite `B n`, shift along `Set.Infinite.natEmbedding (B n) h` and fix the rest!
    let g : ℕ → ℝ → ℝ := fun n x ↦
      if hinf : (B n).Infinite then
        if hex : ∃ k : ℕ, (Set.Infinite.natEmbedding (B n) hinf k : ℝ) = x then
          (Set.Infinite.natEmbedding (B n) hinf (hex.choose + 1) : ℝ)
        else x
      else x
    let p : ℕ → RealPartialFun := fun n ↦ RealPartialFun.mkPartial (B n) (g n)
    have hp_inj : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (p n).IsInjective := by
      refine hev_inf.mono fun n hn x hx y hy hxy ↦ ?_
      have hpx : (p n).apply x = g n x := RealPartialFun.mkPartial_apply_of_mem hx
      have hpy : (p n).apply y = g n y := RealPartialFun.mkPartial_apply_of_mem hy
      rw [hpx, hpy] at hxy
      by_cases hex_x : ∃ k : ℕ, (Set.Infinite.natEmbedding (B n) hn k : ℝ) = x <;>
        by_cases hex_y : ∃ k : ℕ, (Set.Infinite.natEmbedding (B n) hn k : ℝ) = y
      · have hval : (Set.Infinite.natEmbedding (B n) hn (hex_x.choose + 1) : ℝ) =
            (Set.Infinite.natEmbedding (B n) hn (hex_y.choose + 1) : ℝ) := by
          simpa only [g, hn, hex_x, hex_y, ↓reduceDIte] using hxy
        have hk : hex_x.choose = hex_y.choose :=
          Nat.succ_inj.1 ((Set.Infinite.natEmbedding (B n) hn).injective (Subtype.ext hval))
        rw [← hex_x.choose_spec, ← hex_y.choose_spec, hk]
      · exfalso
        have hval : (Set.Infinite.natEmbedding (B n) hn (hex_x.choose + 1) : ℝ) = y := by
          simpa only [g, hn, hex_x, hex_y, ↓reduceDIte] using hxy
        exact hex_y ⟨hex_x.choose + 1, hval⟩
      · exfalso
        have hval : x = (Set.Infinite.natEmbedding (B n) hn (hex_y.choose + 1) : ℝ) := by
          simpa only [g, hn, hex_x, hex_y, ↓reduceDIte] using hxy
        exact hex_x ⟨hex_y.choose + 1, hval.symm⟩
      · simpa only [g, hn, hex_x, hex_y, ↓reduceDIte] using hxy
    have hp_sub : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (p n).apply '' (B n) ⊆ B n := by
      refine hev_inf.mono fun n hn ↦ ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [RealPartialFun.mkPartial_apply_of_mem hx]
      by_cases hex : ∃ k : ℕ, (Set.Infinite.natEmbedding (B n) hn k : ℝ) = x
      · simpa only [g, hn, hex, ↓reduceDIte] using
          (Set.Infinite.natEmbedding (B n) hn (hex.choose + 1)).2
      · simpa only [g, hn, hex, ↓reduceDIte] using hx
    let f : InternalPartialFun := internalFun p
    have hf_inj : f.IsInjective := internalFun_isInjective_iff.2 hp_inj
    have hf_dom : internalSet B ⊆ f.dom := Set.Subset.rfl
    have hf_img_sub : f.apply '' (internalSet B) ⊆ internalSet B := by
      rw [internalFun_image]
      exact internalSet_subset_iff.2 hp_sub
    have hf_onto : f.apply '' (internalSet B) = internalSet B :=
      hpig f (isInternalFun_internalFun p) hf_inj hf_dom hf_img_sub
    -- Witness `r₀ n = e_n 0 ∈ B n \ (p n).apply '' (B n)`!
    let r₀ : ℕ → ℝ := fun n ↦
      if hn : (B n).Infinite then (Set.Infinite.natEmbedding (B n) hn 0 : ℝ) else 0
    have hr₀_in_B : ofSeq r₀ ∈ internalSet B := by
      refine ofSeq_mem_internalSet.2 (hev_inf.mono fun n hn ↦ ?_)
      simpa only [r₀, hn, ↓reduceDIte] using (Set.Infinite.natEmbedding (B n) hn 0).2
    have hr₀_in_img : ofSeq r₀ ∈ f.apply '' (internalSet B) := hf_onto.symm ▸ hr₀_in_B
    rw [internalFun_image, ofSeq_mem_internalSet] at hr₀_in_img
    obtain ⟨n, hn_inf, ⟨x, hxB, hgx⟩⟩ := (hev_inf.and hr₀_in_img).exists
    rw [RealPartialFun.mkPartial_apply_of_mem hxB] at hgx
    have hr₀_eq : r₀ n = (Set.Infinite.natEmbedding (B n) hn_inf 0 : ℝ) := by
      simp only [r₀, hn_inf, ↓reduceDIte]
    rw [hr₀_eq] at hgx
    by_cases hex : ∃ k : ℕ, (Set.Infinite.natEmbedding (B n) hn_inf k : ℝ) = x
    · have hval : (Set.Infinite.natEmbedding (B n) hn_inf (hex.choose + 1) : ℝ) =
          (Set.Infinite.natEmbedding (B n) hn_inf 0 : ℝ) := by
        simpa only [g, hn_inf, hex, ↓reduceDIte] using hgx
      exact Nat.succ_ne_zero hex.choose
        ((Set.Infinite.natEmbedding (B n) hn_inf).injective (Subtype.ext hval))
    · have hval : x = (Set.Infinite.natEmbedding (B n) hn_inf 0 : ℝ) := by
        simpa only [g, hn_inf, hex, ↓reduceDIte] using hgx
      exact hex ⟨0, hval.symm⟩

/-- Goldblatt §12.6 (p. 152): The map `x ↦ 2x` on standard positive naturals and `x ↦ x`
elsewhere. -/
def doubleStandardMap (x : ℝ*) : ℝ* :=
  if ∃ n : ℕ, 1 ≤ n ∧ x = (n : ℝ*) then 2 * x else x

/-- `doubleStandardMap` is injective on all of `ℝ*`. -/
theorem injective_doubleStandardMap : Function.Injective doubleStandardMap := by
  intro x y hxy
  by_cases hx : ∃ n : ℕ, 1 ≤ n ∧ x = (n : ℝ*) <;>
    by_cases hy : ∃ m : ℕ, 1 ≤ m ∧ y = (m : ℝ*)
  · simp only [doubleStandardMap, hx, hy, ↓reduceIte] at hxy
    linarith
  · exfalso
    simp only [doubleStandardMap, hx, hy, ↓reduceIte] at hxy
    rcases hx with ⟨n, hn1, rfl⟩
    exact hy ⟨2 * n, by omega, by rw [← hxy]; push_cast; ring⟩
  · exfalso
    simp only [doubleStandardMap, hx, hy, ↓reduceIte] at hxy
    rcases hy with ⟨m, hm1, rfl⟩
    exact hx ⟨2 * m, by omega, by rw [hxy]; push_cast; ring⟩
  · simpa only [doubleStandardMap, hx, hy, ↓reduceIte] using hxy

/-- Goldblatt §12.6 (p. 152): On any unlimited hyperfinite initial segment `{1, …, N}` (`N ∈ ℕ*`
unlimited), `doubleStandardMap` maps `{1, …, N}` injectively into itself while missing `1`, so by
the **Hyperfinite Pigeonhole Principle** (Theorem 12.6.1) it cannot be internal! -/
theorem not_isInternalFun_doubleStandard_on_Icc {N : ℕ*} (hN : IsUnlimitedNat N) :
    ¬ IsInternalFun (InternalPartialFun.mkPartial (hyperIccOne N) doubleStandardMap) := by
  intro hInt
  let A : Set ℝ* := hyperIccOne N
  let F : InternalPartialFun := InternalPartialFun.mkPartial A doubleStandardMap
  have hHyp : IsHyperfinite A := (hasHypercard_Icc_one N).isHyperfinite
  have hInj : F.IsInjective := by
    intro x hx y hy hxy
    have hx' : x ∈ A := hx
    have hy' : y ∈ A := hy
    simp only [F, InternalPartialFun.mkPartial, hx', hy', ↓reduceIte] at hxy
    exact injective_doubleStandardMap hxy
  have hImg_sub : F.apply '' A ⊆ A := by
    rintro _ ⟨x, hxA, rfl⟩
    have hFx : F.apply x = doubleStandardMap x := by
      simp [F, InternalPartialFun.mkPartial, hxA]
    rw [hFx]
    by_cases hx_std : ∃ n : ℕ, 1 ≤ n ∧ x = (n : ℝ*)
    · rcases hx_std with ⟨n, hn1, rfl⟩
      have hval : doubleStandardMap (n : ℝ*) = ((2 * n : ℕ) : ℝ*) := by
        have hcond : ∃ k : ℕ, 1 ≤ k ∧ (n : ℝ*) = (k : ℝ*) := ⟨n, hn1, rfl⟩
        simp only [doubleStandardMap, hcond, ↓reduceIte]
        push_cast; ring
      rw [hval]
      exact ⟨((2 * n : ℕ) : ℕ*), ⟨by exact_mod_cast (show 1 ≤ 2 * n by omega), (hN (2 * n)).le⟩,
        Hypernat.toHyperreal_natCast (2 * n)⟩
    · simp only [doubleStandardMap, hx_std, ↓reduceIte]
      exact hxA
  have hOnto : F.apply '' A = A :=
    (isHyperfinite_iff_pigeonhole hHyp.isInternal).1 hHyp F hInt hInj Set.Subset.rfl hImg_sub
  have h1_mem : (1 : ℝ*) ∈ A :=
    ⟨1, ⟨le_rfl, (hN 1).le⟩, by simpa using Hypernat.toHyperreal_natCast 1⟩
  obtain ⟨x, hxA, hFx1⟩ := hOnto.symm ▸ h1_mem
  have hFx_eq : F.apply x = doubleStandardMap x := by
    simp [F, InternalPartialFun.mkPartial, hxA]
  rw [hFx_eq] at hFx1
  by_cases hx_std : ∃ n : ℕ, 1 ≤ n ∧ x = (n : ℝ*)
  · rcases hx_std with ⟨n, hn1, rfl⟩
    have hcond : ∃ k : ℕ, 1 ≤ k ∧ (n : ℝ*) = (k : ℝ*) := ⟨n, hn1, rfl⟩
    simp only [doubleStandardMap, hcond, ↓reduceIte] at hFx1
    have hreal : 2 * (n : ℝ) = 1 := by
      have : ((2 * (n : ℝ) : ℝ) : ℝ*) = ((1 : ℝ) : ℝ*) := by
        push_cast; simpa [← coe_natCast_hyperreal] using hFx1
      exact Hyperreal.coe_eq_coe.1 this
    have hn_ge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  · simp only [doubleStandardMap, hx_std, ↓reduceIte] at hFx1
    exact hx_std ⟨1, le_rfl, by simpa using hFx1⟩

/-- Goldblatt §12.6 (p. 152): Consequently, `doubleStandardMap` defined on all of `*ℕ_{≥ 1}` is
NOT internal either (since restricting it to `{1, …, ω}` would violate Theorem 12.6.1)! -/
theorem not_isInternalFun_doubleStandard_on_starNat :
    ¬ IsInternalFun (InternalPartialFun.mkPartial
      (Hypernat.toHyperreal '' Set.Ici (1 : ℕ*)) doubleStandardMap) := by
  intro hInt
  let X : Set ℝ* := Hypernat.toHyperreal '' Set.Ici (1 : ℕ*)
  let A : Set ℝ* := hyperIccOne omegaNat
  have hA_int : IsInternal A := (hasHypercard_Icc_one omegaNat).isHyperfinite.isInternal
  have hsub : A ⊆ X := by
    rintro _ ⟨K, ⟨h1K, _⟩, rfl⟩
    exact ⟨K, h1K, rfl⟩
  have hRestr : IsInternalFun
      ((InternalPartialFun.mkPartial X doubleStandardMap).restrict A) :=
    hInt.restrict hA_int
  have heq : (InternalPartialFun.mkPartial X doubleStandardMap).restrict A =
      InternalPartialFun.mkPartial A doubleStandardMap := by
    rw [InternalPartialFun.eq_iff_dom_and_eqOn]
    refine ⟨Set.inter_eq_self_of_subset_right hsub, fun x hx ↦ ?_⟩
    have hxA : x ∈ A := hx.2
    have hxX : x ∈ X := hsub hxA
    simp [InternalPartialFun.restrict, InternalPartialFun.mkPartial, hxA, hxX]
  exact not_isInternalFun_doubleStandard_on_Icc isUnlimitedNat_omegaNat (heq ▸ hRestr)

/-! ## §12.7 Integrals as Hyperfinite Sums -/

/-- Goldblatt §12.7 (p. 153): Hyperfinite sum `∑_{x ∈ A} F(x) = [∑_{x ∈ S_n} f_n(x)]` of an
internal function `F = [f_n]` over a hyperfinite set `A = [S_n]` (defaulting to `0` if `F` is not
internal or `A` is not hyperfinite). -/
def hypersum (F : InternalPartialFun) (A : Set ℝ*) : ℝ* :=
  if h : IsInternalFun F ∧ IsHyperfinite A then
    let f := h.1.choose
    let S := (isHyperfinite_iff_exists_finset.1 h.2).choose
    ofSeq (fun n ↦ ∑ x ∈ S n, (f n).apply x)
  else 0

/-- Goldblatt §12.7 (p. 153): `∑_{x ∈ [S_n]} [f_n](x) = [∑_{x ∈ S_n} f_n(x)]` unconditionally! -/
@[simp]
theorem hypersum_internalFun (f : ℕ → RealPartialFun) (S : ℕ → Finset ℝ) :
    hypersum (internalFun f) (internalSet (fun n ↦ (S n : Set ℝ))) =
      ofSeq (fun n ↦ ∑ x ∈ S n, (f n).apply x) := by
  have hcond : IsInternalFun (internalFun f) ∧
      IsHyperfinite (internalSet (fun n ↦ (S n : Set ℝ))) :=
    ⟨isInternalFun_internalFun f, isHyperfinite_iff_exists_finset.2 ⟨S, rfl⟩⟩
  let f' := hcond.1.choose
  let S' := (isHyperfinite_iff_exists_finset.1 hcond.2).choose
  have hf_eq : internalFun f = internalFun f' := hcond.1.choose_spec
  have hS_eq : internalSet (fun n ↦ (S n : Set ℝ)) = internalSet (fun n ↦ (S' n : Set ℝ)) :=
    (isHyperfinite_iff_exists_finset.1 hcond.2).choose_spec
  have hev_f : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n = f' n := internalFun_eq_iff.1 hf_eq
  have hev_S : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), S n = S' n :=
    (internalSet_eq_iff.1 hS_eq).mono fun n hn ↦ Finset.coe_inj.1 hn
  have hval : hypersum (internalFun f) (internalSet (fun n ↦ (S n : Set ℝ))) =
      ofSeq (fun n ↦ ∑ x ∈ S' n, (f' n).apply x) :=
    dite_eq_left hcond
  rw [hval]
  exact Germ.coe_eq.2 ((hev_f.and hev_S).mono fun n ⟨hfn, hSn⟩ ↦ by
    dsimp only
    rw [hfn, hSn])

/-- Goldblatt §12.7 Property 1 (p. 153): `∑_{x ∈ A} (c • F)(x) = c * ∑_{x ∈ A} F(x)`. -/
theorem hypersum_smul (c : ℝ*) {F : InternalPartialFun} (hF : IsInternalFun F)
    {A : Set ℝ*} (hA : IsHyperfinite A) :
    hypersum (F.smul c) A = c * hypersum F A := by
  rcases hF with ⟨f, rfl⟩
  obtain ⟨S, rfl⟩ := isHyperfinite_iff_exists_finset.1 hA
  rcases ofSeq_surjective c with ⟨sc, rfl⟩
  let g : ℕ → RealPartialFun :=
    fun n ↦ RealPartialFun.mkPartial (f n).dom (fun x ↦ sc n * (f n).apply x)
  have hsmul_eq : (internalFun f).smul (ofSeq sc) = internalFun g := by
    rw [InternalPartialFun.eq_iff_dom_and_eqOn]
    refine ⟨rfl, fun x hx ↦ ?_⟩
    have hx' : x ∈ (internalFun f).dom := hx
    have h1 : ((internalFun f).smul (ofSeq sc)).apply x = ofSeq sc * (internalFun f).apply x :=
      InternalPartialFun.mkPartial_apply_of_mem hx'
    rw [h1]
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hev := ofSeq_mem_internalSet.1 hx'
    exact Germ.coe_eq.2 (hev.mono fun n hn ↦ by
      dsimp only [g]
      rw [RealPartialFun.mkPartial_apply_of_mem hn])
  rw [hsmul_eq, hypersum_internalFun, hypersum_internalFun]
  refine Germ.coe_eq.2 (Eventually.of_forall fun n ↦ ?_)
  change (∑ x ∈ S n, (g n).apply x) = sc n * ∑ x ∈ S n, (f n).apply x
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hx : x ∈ (f n).dom
  · exact RealPartialFun.mkPartial_apply_of_mem hx
  · simp [g, RealPartialFun.mkPartial, hx, (f n).default_outside x hx]

/-- Goldblatt §12.7 Property 2 (p. 153): `∑_{x ∈ A} (F + G)(x) = ∑_{x ∈ A} F(x) + ∑_{x ∈ A} G(x)`
whenever `A ⊆ F.dom` and `A ⊆ G.dom`. -/
theorem hypersum_add {F G : InternalPartialFun} (hF : IsInternalFun F) (hG : IsInternalFun G)
    {A : Set ℝ*} (hA : IsHyperfinite A) (hAF : A ⊆ F.dom) (hAG : A ⊆ G.dom) :
    hypersum (F.add G) A = hypersum F A + hypersum G A := by
  rcases hF with ⟨f, rfl⟩
  rcases hG with ⟨g, rfl⟩
  obtain ⟨S, rfl⟩ := isHyperfinite_iff_exists_finset.1 hA
  let fg : ℕ → RealPartialFun :=
    fun n ↦ RealPartialFun.mkPartial ((f n).dom ∩ (g n).dom)
      (fun x ↦ (f n).apply x + (g n).apply x)
  have hadd_eq : (internalFun f).add (internalFun g) = internalFun fg := by
    rw [InternalPartialFun.eq_iff_dom_and_eqOn]
    refine ⟨internalSet_inter _ _, fun x hx ↦ ?_⟩
    have hx' : x ∈ (internalFun f).dom ∩ (internalFun g).dom := hx
    have h1 : ((internalFun f).add (internalFun g)).apply x =
        (internalFun f).apply x + (internalFun g).apply x :=
      InternalPartialFun.mkPartial_apply_of_mem hx'
    rw [h1]
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∈ (f n).dom ∩ (g n).dom := by
      rw [internalFun_dom, internalFun_dom, internalSet_inter, ofSeq_mem_internalSet] at hx'
      exact hx'
    exact Germ.coe_eq.2 (hev.mono fun n hn ↦ by
      dsimp only [fg]
      rw [RealPartialFun.mkPartial_apply_of_mem hn])
  have hevF : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (S n : Set ℝ) ⊆ (f n).dom :=
    internalSet_subset_iff.1 hAF
  have hevG : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (S n : Set ℝ) ⊆ (g n).dom :=
    internalSet_subset_iff.1 hAG
  rw [hadd_eq, hypersum_internalFun, hypersum_internalFun, hypersum_internalFun]
  refine Germ.coe_eq.2 ((hevF.and hevG).mono fun n ⟨hFn, hGn⟩ ↦ ?_)
  change (∑ x ∈ S n, (fg n).apply x) = (∑ x ∈ S n, (f n).apply x) + ∑ x ∈ S n, (g n).apply x
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx_mem : x ∈ (f n).dom ∩ (g n).dom :=
    ⟨hFn (Finset.mem_coe.2 hx), hGn (Finset.mem_coe.2 hx)⟩
  exact RealPartialFun.mkPartial_apply_of_mem hx_mem

/-- Goldblatt §12.7 Property 3 (p. 153): For disjoint hyperfinite sets `A` and `B`,
`∑_{x ∈ A ∪ B} F(x) = ∑_{x ∈ A} F(x) + ∑_{x ∈ B} F(x)`. -/
theorem hypersum_union_disjoint {F : InternalPartialFun} (hF : IsInternalFun F)
    {A B : Set ℝ*} (hA : IsHyperfinite A) (hB : IsHyperfinite B) (hdisj : Disjoint A B) :
    hypersum F (A ∪ B) = hypersum F A + hypersum F B := by
  rcases hF with ⟨f, rfl⟩
  obtain ⟨S, rfl⟩ := isHyperfinite_iff_exists_finset.1 hA
  obtain ⟨T, rfl⟩ := isHyperfinite_iff_exists_finset.1 hB
  have hU_eq : internalSet (fun n ↦ (S n : Set ℝ)) ∪ internalSet (fun n ↦ (T n : Set ℝ)) =
      internalSet (fun n ↦ ((S n ∪ T n : Finset ℝ) : Set ℝ)) := by
    rw [internalSet_union]
    exact internalSet_eq_iff.2 (Eventually.of_forall fun n ↦ (Finset.coe_union (S n) (T n)).symm)
  have hev_disj : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), Disjoint (S n) (T n) := by
    have hempty : internalSet (fun n ↦ ((S n ∩ T n : Finset ℝ) : Set ℝ)) = ∅ := by
      have h1 : internalSet (fun n ↦ (S n : Set ℝ)) ∩ internalSet (fun n ↦ (T n : Set ℝ)) = ∅ :=
        Set.disjoint_iff_inter_eq_empty.1 hdisj
      rw [internalSet_inter] at h1
      have h2 : internalSet (fun n ↦ ((S n ∩ T n : Finset ℝ) : Set ℝ)) =
          internalSet (fun n ↦ (S n : Set ℝ) ∩ (T n : Set ℝ)) :=
        internalSet_eq_iff.2 (Eventually.of_forall fun n ↦ Finset.coe_inter (S n) (T n))
      exact h2.trans h1
    have hev_inter : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ((S n ∩ T n : Finset ℝ) : Set ℝ) = ∅ :=
      internalSet_eq_iff.1 (hempty.trans internalSet_empty.symm)
    exact hev_inter.mono fun n hn ↦
      Finset.disjoint_iff_inter_eq_empty.2 (Finset.coe_eq_empty.1 hn)
  rw [hU_eq, hypersum_internalFun, hypersum_internalFun, hypersum_internalFun]
  exact Germ.coe_eq.2 (hev_disj.mono fun n hn ↦ Finset.sum_union hn)

/-- Goldblatt §12.7 Property 4 (p. 153): Monotonicity of hyperfinite sums: if `F(x) ≤ G(x)` for all
`x ∈ A` (with `A ⊆ F.dom` and `A ⊆ G.dom`), then `∑_{x ∈ A} F(x) ≤ ∑_{x ∈ A} G(x)`. -/
theorem hypersum_mono {F G : InternalPartialFun} (hF : IsInternalFun F) (hG : IsInternalFun G)
    {A : Set ℝ*} (hA : IsHyperfinite A) (hAF : A ⊆ F.dom) (hAG : A ⊆ G.dom)
    (hle : ∀ x ∈ A, F.apply x ≤ G.apply x) :
    hypersum F A ≤ hypersum G A := by
  rcases hF with ⟨f, rfl⟩
  rcases hG with ⟨g, rfl⟩
  obtain ⟨S, rfl⟩ := isHyperfinite_iff_exists_finset.1 hA
  -- Check that `∀ᶠ n, ∀ x ∈ S n, (f n).apply x ≤ (g n).apply x`!
  have hev_le : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
      ∀ x ∈ S n, (f n).apply x ≤ (g n).apply x := by
    by_contra hnot
    have hev_bad : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
        ∃ x ∈ S n, (g n).apply x < (f n).apply x := by
      refine (Ultrafilter.eventually_not.2 hnot).mono fun n hn ↦ ?_
      push Not at hn
      exact hn
    let rSeq : ℕ → ℝ := fun n ↦
      if h : ∃ x ∈ S n, (g n).apply x < (f n).apply x then h.choose else 0
    have hr_mem : ofSeq rSeq ∈ internalSet (fun n ↦ (S n : Set ℝ)) := by
      refine ofSeq_mem_internalSet.2 (hev_bad.mono fun n hn ↦ ?_)
      simpa only [rSeq, hn, ↓reduceDIte, Finset.mem_coe] using hn.choose_spec.1
    have hgt : (internalFun g).apply (ofSeq rSeq) < (internalFun f).apply (ofSeq rSeq) := by
      refine ofSeq_lt_ofSeq.2 (hev_bad.mono fun n hn ↦ ?_)
      simpa only [rSeq, hn, ↓reduceDIte] using hn.choose_spec.2
    exact not_lt_of_ge (hle (ofSeq rSeq) hr_mem) hgt
  rw [hypersum_internalFun, hypersum_internalFun]
  exact ofSeq_le_ofSeq.2 (hev_le.mono fun n hn ↦ Finset.sum_le_sum hn)

/-- Real uniform partition `P_n(a, ε, N) = {a + k * ε | 0 ≤ k < N}` as a `Finset ℝ`. -/
def realStepPartition (a ε : ℝ) (N : ℕ) : Finset ℝ :=
  (Finset.range N).image (fun k : ℕ ↦ a + (k : ℝ) * ε)

/-- Goldblatt §12.7 (p. 153): Hyperfinite partition `P = [P_n]` associated to a real starting point
`a ∈ ℝ`, step sequence `ε : ℕ → ℝ`, and hypernatural step count `NSeq : ℕ → ℕ`. -/
def hyperStepPartition (a : ℝ) (ε : ℕ → ℝ) (NSeq : ℕ → ℕ) : Set ℝ* :=
  internalSet (fun n ↦ (realStepPartition a (ε n) (NSeq n) : Set ℝ))

/-- Goldblatt Exercise 12.7.1 (pp. 153–154):
Every member of the hyperfinite partition `P = hyperStepPartition a ε NSeq` has the form
`a + k * dx` (with `dx = ofSeq ε`) for a hypernatural `k < N` (`N = (NSeq : ℕ*)`), and when
`dx > 0`, `P` is hyperfinite of internal cardinality `N`! -/
theorem hyperStepPartition_eq_and_hypercard (a : ℝ) {ε : ℕ → ℝ} (hε : 0 < ofSeq ε)
    (NSeq : ℕ → ℕ) :
    hyperStepPartition a ε NSeq =
      {y : ℝ* | ∃ k : ℕ*, k < (NSeq : ℕ*) ∧
        y = (a : ℝ*) + Hypernat.toHyperreal k * ofSeq ε} ∧
    HasHypercard (hyperStepPartition a ε NSeq) (NSeq : ℕ*) := by
  have hev_pos : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < ε n := ofSeq_lt_ofSeq.1 hε
  constructor
  · ext y
    rcases ofSeq_surjective y with ⟨r, rfl⟩
    constructor
    · intro hy
      have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
          ∃ k : ℕ, k < NSeq n ∧ r n = a + (k : ℝ) * ε n := by
        refine (ofSeq_mem_internalSet.1 hy).mono fun n hn ↦ ?_
        obtain ⟨k, hk, hkr⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hn)
        exact ⟨k, Finset.mem_range.1 hk, hkr.symm⟩
      let kSeq : ℕ → ℕ := fun n ↦
        if h : ∃ k : ℕ, k < NSeq n ∧ r n = a + (k : ℝ) * ε n then h.choose else 0
      refine ⟨(kSeq : ℕ*), Germ.coe_lt.2 ?_, Germ.coe_eq.2 ?_⟩
      · exact hev.mono fun n hn ↦ by simpa only [kSeq, hn, ↓reduceDIte] using hn.choose_spec.1
      · exact hev.mono fun n hn ↦ by
          simpa only [Function.comp_apply, kSeq, hn, ↓reduceDIte] using hn.choose_spec.2
    · rintro ⟨k, hk, hyk⟩
      induction k using Germ.inductionOn with | _ d =>
      have hd_lt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), d n < NSeq n := Germ.coe_lt.1 hk
      have hrd : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n = a + (d n : ℝ) * ε n :=
        Germ.coe_eq.1 hyk
      refine ofSeq_mem_internalSet.2 ((hd_lt.and hrd).mono fun n ⟨h1, h2⟩ ↦ ?_)
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨d n, Finset.mem_range.2 h1, h2.symm⟩)
  · refine ⟨fun n ↦ realStepPartition a (ε n) (NSeq n), rfl, ?_⟩
    refine (Germ.coe_eq.2 (hev_pos.mono fun n hn ↦ ?_)).symm
    have hinj : Function.Injective (fun k : ℕ ↦ a + (k : ℝ) * ε n) := by
      intro i j hij
      exact Nat.cast_injective (mul_right_cancel₀ hn.ne' (add_left_cancel hij))
    dsimp only [realStepPartition]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- Goldblatt §12.7 (p. 154): Exact algebraic identity between the lifted Riemann sum
`[(∑_{x ∈ P_n} f(x)) * ε_n]` and the hyperfinite sum `hypersum (*f) P * dx`! -/
theorem riemann_sum_eq_hypersum_mul (a : ℝ) (f : ℝ → ℝ) (ε : ℕ → ℝ) (NSeq : ℕ → ℕ) :
    ofSeq (fun n ↦ (∑ x ∈ realStepPartition a (ε n) (NSeq n), f x) * ε n) =
      hypersum (starInternalFun Set.univ f) (hyperStepPartition a ε NSeq) * ofSeq ε := by
  rw [starInternalFun, hyperStepPartition, hypersum_internalFun]
  refine Germ.coe_eq.2 (Eventually.of_forall fun n ↦ ?_)
  change (∑ x ∈ realStepPartition a (ε n) (NSeq n), f x) * ε n =
    (∑ x ∈ realStepPartition a (ε n) (NSeq n), (RealPartialFun.mkPartial Set.univ f).apply x) * ε n
  congr 1
  exact Finset.sum_congr rfl fun x _ ↦
    (RealPartialFun.mkPartial_apply_of_mem (Set.mem_univ x)).symm

/-- Goldblatt §12.7 (p. 154, **Riemann Integral as Shadow of a Hyperfinite Sum**):
Let `f : ℝ → ℝ` be continuous on `[a, b]` (`a < b`), and let `dx = ofSeq ε` be any positive
infinitesimal (`IsPosInfinitesimal (ofSeq ε)`). Setting `N_n = ⌊(b - a) / ε_n⌋₊` and
`P = hyperStepPartition a ε N_n`, the hyperfinite Riemann sum `hypersum (*f) P * dx` is limited
and infinitely close to `∫ x in a..b, f x`, so
`∫ x in a..b, f x = shadow (hypersum (*f) P * dx)`! -/
theorem integral_eq_shadow_hypersum {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) {ε : ℕ → ℝ} (hε : IsPosInfinitesimal (ofSeq ε)) :
    let NSeq : ℕ → ℕ := fun n ↦ ⌊(b - a) / ε n⌋₊
    let P : Set ℝ* := hyperStepPartition a ε NSeq
    let S : ℝ* := hypersum (starInternalFun Set.univ f) P * ofSeq ε
    S ≈ₕ ((∫ x in a..b, f x : ℝ) : ℝ*) ∧
      (∫ x in a..b, f x) = shadow S := by
  intro NSeq P S
  have hba_pos : 0 < b - a := sub_pos.2 hab
  -- Uniform continuity and boundedness of `f` on compact `[a, b]`.
  have huc : UniformContinuousOn f (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf
  obtain ⟨M, hM_bound⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Icc a b, |f x| ≤ M := by
    have hbdd : Bornology.IsBounded (f '' Set.Icc a b) :=
      (isCompact_Icc.image_of_continuousOn hf).isBounded
    obtain ⟨C, hC⟩ := hbdd.subset_closedBall 0
    refine ⟨max C 0, le_max_right C 0, fun x hx ↦ ?_⟩
    have hmem : f x ∈ Metric.closedBall (0 : ℝ) C := hC ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
    exact hmem.trans (le_max_left C 0)
  have hM0 : 0 ≤ M := hM_bound.1
  have hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M := hM_bound.2
  -- Show `S ≈ₕ (∫ x in a..b, f x : ℝ*)` by checking `|S - ∫ f| < η` for every standard `η > 0`.
  have hclose : S ≈ₕ ((∫ x in a..b, f x : ℝ) : ℝ*) := by
    intro η hη
    have hη_mesh : 0 < η / (2 * (b - a)) := div_pos hη (by positivity)
    obtain ⟨δ, hδ_pos, hδ_uc⟩ := Metric.uniformContinuousOn_iff.1 huc (η / (2 * (b - a))) hη_mesh
    let τ : ℝ := min δ (min (b - a) (η / (2 * (M + 1))))
    have hτ_pos : 0 < τ :=
      lt_min hδ_pos (lt_min hba_pos (div_pos hη (by positivity)))
    have hev_pos : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < ε n := ofSeq_lt_ofSeq.1 hε.1
    have hev_lt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ε n < τ := by
      have hlt_hyp : ofSeq ε < (τ : ℝ*) := hε.2 τ hτ_pos
      exact ofSeq_lt_ofSeq.1 hlt_hyp
    have hS_eq : S = ofSeq (fun n ↦ (∑ x ∈ realStepPartition a (ε n) (NSeq n), f x) * ε n) :=
      (riemann_sum_eq_hypersum_mul a f ε NSeq).symm
    rw [hS_eq]
    refine ofSeq_lt_ofSeq.2 ((hev_pos.and hev_lt).mono fun n ⟨hε_pos, hε_τ⟩ ↦ ?_)
    have hε_δ : ε n < δ := hε_τ.trans_le (min_le_left _ _)
    have hε_ba : ε n < b - a := hε_τ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hε_tail : ε n < η / (2 * (M + 1)) :=
      hε_τ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    -- Grid points `pts k = a + k * ε n`
    let pts : ℕ → ℝ := fun k ↦ a + (k : ℝ) * ε n
    have hpts_inj : Function.Injective pts := by
      intro i j hij
      exact Nat.cast_injective (mul_right_cancel₀ hε_pos.ne' (add_left_cancel hij))
    have hsum_pts : (∑ x ∈ realStepPartition a (ε n) (NSeq n), f x) * ε n =
        ∑ k ∈ Finset.range (NSeq n), f (pts k) * ε n := by
      dsimp only [realStepPartition]
      rw [Finset.sum_image (fun i _ j _ h ↦ hpts_inj h), Finset.sum_mul]
    have hN_mul_le : (NSeq n : ℝ) * ε n ≤ b - a := by
      have hdiv_nn : 0 ≤ (b - a) / ε n := div_nonneg hba_pos.le hε_pos.le
      exact (le_div_iff₀ hε_pos).1 (Nat.floor_le hdiv_nn)
    have hba_lt_succ : b - a < ((NSeq n : ℝ) + 1) * ε n :=
      (div_lt_iff₀ hε_pos).1 (Nat.lt_floor_add_one ((b - a) / ε n))
    have hpts_N_le_b : pts (NSeq n) ≤ b := by dsimp [pts]; linarith
    have hb_lt_next : b < pts (NSeq n) + ε n := by dsimp [pts]; linarith
    have ha_le_pts : ∀ k : ℕ, a ≤ pts k := fun k ↦ by
      dsimp [pts]; exact le_add_of_nonneg_right (by positivity)
    have hpts_le_b : ∀ k ≤ NSeq n, pts k ≤ b := fun k hk ↦ by
      have hk_cast : (k : ℝ) ≤ (NSeq n : ℝ) := by exact_mod_cast hk
      have hmul : (k : ℝ) * ε n ≤ (NSeq n : ℝ) * ε n :=
        mul_le_mul_of_nonneg_right hk_cast hε_pos.le
      dsimp [pts]; linarith
    -- Split `∫ x in a..b, f x` into `∑_{k < NSeq n} ∫_{pts k}^{pts (k+1)} f + ∫_{pts (NSeq n)}^b f`
    have hint_full : IntervalIntegrable f MeasureTheory.volume a b :=
      hf.intervalIntegrable_of_Icc hab.le
    have hint_a_ptsN : IntervalIntegrable f MeasureTheory.volume a (pts (NSeq n)) :=
      (hf.mono (Set.Icc_subset_Icc_right hpts_N_le_b)).intervalIntegrable_of_Icc (ha_le_pts _)
    have hint_ptsN_b : IntervalIntegrable f MeasureTheory.volume (pts (NSeq n)) b :=
      (hf.mono (Set.Icc_subset_Icc_left (ha_le_pts _))).intervalIntegrable_of_Icc hpts_N_le_b
    have hint_adj : ∀ k < NSeq n,
        IntervalIntegrable f MeasureTheory.volume (pts k) (pts (k + 1)) := by
      intro k hk
      have hk1 : k + 1 ≤ NSeq n := Nat.succ_le_of_lt hk
      have hle_step : pts k ≤ pts (k + 1) := by dsimp [pts]; push_cast; linarith
      exact (hf.mono (Set.Icc_subset_Icc (ha_le_pts k) (hpts_le_b (k + 1) hk1))).intervalIntegrable_of_Icc hle_step
    have hsplit_main : (∫ x in a..b, f x) =
        (∑ k ∈ Finset.range (NSeq n), ∫ x in (pts k)..(pts (k + 1)), f x) +
          ∫ x in (pts (NSeq n))..b, f x := by
      have h1 : (∑ k ∈ Finset.range (NSeq n), ∫ x in (pts k)..(pts (k + 1)), f x) =
          ∫ x in a..(pts (NSeq n)), f x := by
        have hsum_adj := intervalIntegral.sum_integral_adjacent_intervals hint_adj
        have hpts0 : pts 0 = a := by simp [pts]
        rwa [hpts0] at hsum_adj
      rw [h1, intervalIntegral.integral_add_adjacent_intervals hint_a_ptsN hint_ptsN_b]
    -- Bound each subinterval error `|f (pts k) * ε n - ∫_{pts k}^{pts (k+1)} f|`
    have hstep_err : ∀ k ∈ Finset.range (NSeq n),
        |f (pts k) * ε n - ∫ x in (pts k)..(pts (k + 1)), f x| ≤
          (η / (2 * (b - a))) * ε n := by
      intro k hk
      have hk_lt : k < NSeq n := Finset.mem_range.1 hk
      have hk1 : k + 1 ≤ NSeq n := Nat.succ_le_of_lt hk_lt
      have hstep_len : pts (k + 1) - pts k = ε n := by dsimp [pts]; push_cast; ring
      have hconst_int : f (pts k) * ε n =
          ∫ _ in (pts k)..(pts (k + 1)), f (pts k) := by
        rw [intervalIntegral.integral_const, hstep_len, smul_eq_mul, mul_comm]
      rw [hconst_int, ← intervalIntegral.integral_sub intervalIntegrable_const (hint_adj k hk_lt)]
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := pts k) (b := pts (k + 1)) (C := η / (2 * (b - a)))
        (f := fun x ↦ f (pts k) - f x) ?_
      · rw [Real.norm_eq_abs, hstep_len, abs_of_pos hε_pos] at hnorm
        exact hnorm
      · intro x hx
        have hle_step : pts k ≤ pts (k + 1) := by linarith
        rw [Set.uIoc_of_le hle_step] at hx
        have hx_Icc : x ∈ Set.Icc a b :=
          ⟨(ha_le_pts k).trans hx.1.le, hx.2.trans (hpts_le_b (k + 1) hk1)⟩
        have hpk_Icc : pts k ∈ Set.Icc a b :=
          ⟨ha_le_pts k, hpts_le_b k (Nat.le_of_lt hk_lt)⟩
        have hdist_lt : dist (pts k) x < δ := by
          rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 hx.1)]
          linarith [hx.2, hstep_len]
        have huc_lt := hδ_uc (pts k) hpk_Icc x hx_Icc hdist_lt
        rw [Real.dist_eq] at huc_lt
        rw [Real.norm_eq_abs]
        exact huc_lt.le
    have hsum_err :
        |(∑ k ∈ Finset.range (NSeq n), f (pts k) * ε n) -
          (∑ k ∈ Finset.range (NSeq n), ∫ x in (pts k)..(pts (k + 1)), f x)| ≤ η / 2 := by
      rw [← Finset.sum_sub_distrib]
      calc
        |∑ k ∈ Finset.range (NSeq n), (f (pts k) * ε n - ∫ x in (pts k)..(pts (k + 1)), f x)|
            ≤ ∑ k ∈ Finset.range (NSeq n),
                |f (pts k) * ε n - ∫ x in (pts k)..(pts (k + 1)), f x| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range (NSeq n), (η / (2 * (b - a))) * ε n :=
          Finset.sum_le_sum hstep_err
        _ = (NSeq n : ℝ) * ((η / (2 * (b - a))) * ε n) := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ = (η / (2 * (b - a))) * ((NSeq n : ℝ) * ε n) := by ring
        _ ≤ (η / (2 * (b - a))) * (b - a) :=
          mul_le_mul_of_nonneg_left hN_mul_le hη_mesh.le
        _ = η / 2 := by field_simp [hba_pos.ne']
    -- Bound tail integral `|∫_{pts (NSeq n)}^b f| < η / 2`
    have htail_err : |∫ x in (pts (NSeq n))..b, f x| < η / 2 := by
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := pts (NSeq n)) (b := b) (C := M) (f := f) ?_
      · rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hpts_N_le_b)] at hnorm
        have hlen_lt : b - pts (NSeq n) < ε n := by linarith
        have hM_le : M * (b - pts (NSeq n)) ≤ (M + 1) * ε n := by
          have h1 : M * (b - pts (NSeq n)) ≤ M * ε n :=
            mul_le_mul_of_nonneg_left hlen_lt.le hM0
          linarith [hε_pos]
        have hlt_half : (M + 1) * ε n < η / 2 := by
          have hM1_pos : 0 < M + 1 := by positivity
          have := (lt_div_iff₀' hM1_pos).1
            (show ε n < (η / 2) / (M + 1) by rw [div_div]; ring_nf at hε_tail ⊢; exact hε_tail)
          linarith
        exact (hnorm.trans hM_le).trans_lt hlt_half
      · intro x hx
        rw [Set.uIoc_of_le hpts_N_le_b] at hx
        rw [Real.norm_eq_abs]
        exact hM x ⟨(ha_le_pts _).trans hx.1.le, hx.2⟩
    -- Combine main sum and tail error!
    change |(∑ x ∈ realStepPartition a (ε n) (NSeq n), f x) * ε n - ∫ x in a..b, f x| < η
    rw [hsum_pts, hsplit_main]
    set A₁ : ℝ := ∑ k ∈ Finset.range (NSeq n), f (pts k) * ε n
    set A₂ : ℝ := ∑ k ∈ Finset.range (NSeq n), ∫ x in (pts k)..(pts (k + 1)), f x
    set T : ℝ := ∫ x in (pts (NSeq n))..b, f x
    have htri : |A₁ - (A₂ + T)| ≤ |A₁ - A₂| + |-T| := by
      have : A₁ - (A₂ + T) = (A₁ - A₂) + (-T) := by ring
      rw [this]
      exact abs_add_le _ _
    rw [abs_neg] at htri
    linarith [htri, hsum_err, htail_err]
  exact ⟨hclose, (shadow_eq_of_infClose hclose).symm⟩

end Goldblatt
end
