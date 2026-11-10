import LecturesOnTheHyperreals.Ch05_HyperrealsGreatAndSmall
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Chapter 7: Continuous Functions

Formalization of Robert Goldblatt, *Lectures on the Hyperreals*, Chapter 7 (pp. 75–90):

* **§7.1** Cauchy's account of continuity via microcontinuity (`continuousAt_iff_infClose`,
  `continuousAt_iff_image_halo_subset`, Theorem 7.1.1), infinitesimal-neighborhood continuity
  (Corollary 7.1.2), restricted domain continuity (`continuousWithinAt_iff_infClose`,
  `continuousWithinAt_iff_exists_posInfinitesimal`, `continuousOn_iff_infClose`, Theorem 7.1.3),
  and nonstandard proofs of the algebra and composition of continuous functions.
* **§7.2** Nonstandard proofs of the continuity of `Real.sin` and `Real.cos` on `ℝ` via
  transferred addition identities and trigonometric infinitesimals.
* **§7.3–7.4** Nonstandard characterizations of all seven functional limit types (`x → c⁺`,
  `x → c⁻`, punctured `x → c`, infinite limits `+∞` and `-∞`, and limits as `x → +∞` and
  `x → -∞`), plus Exercises 7.4(1)–(3): two-sided vs one-sided limits, algebra of limits,
  continuity via limits, and complete infinitesimal analysis of `sin(1/x)`, `x sin(1/x)`,
  Dirichlet's indicator `1_ℚ`, `±x` on `ℚ` vs `ℝ \ ℚ`, and Thomae's ruler function `f₅`.
* **§7.5** Nonstandard hyperfinite-partition proof of the Intermediate Value Theorem
  (`intermediate_value_Ioo_nonstandard`, `intermediate_value_Icc_nonstandard`).
* **§7.6** Nonstandard hyperfinite-grid proof of the Extreme Value Theorem
  (`exists_max_on_Icc_nonstandard`, `exists_min_on_Icc_nonstandard`, `extreme_value_Icc_nonstandard`)
  and boundedness of continuous functions on `[a, b]`.
* **§7.7–7.8** Uniform continuity (`uniformContinuousOn_iff_infClose`, Theorem 7.7.1), the
  Heine–Cantor theorem on `[a, b]` (`uniformContinuousOn_Icc_of_continuousOn`, Theorem 7.7.2),
  and Exercises 7.8(1)–(4): failure of the shadow proof on non-closed intervals, non-uniform
  continuity of `x²` on `ℝ` and `1/x` on `(0, 1)`, preservation of Cauchy sequences, and
  continuity of monotone functions with the intermediate value property.
* **§7.9** Lipschitz functions, contraction mappings, concrete iterate analysis of `x/2 + 1/2`,
  and the nonstandard proof of Banach's Contraction Fixed-Point Theorem on `ℝ` and on closed
  subsets `A ⊆ ℝ` (`contraction_existsUnique_fixedPoint`, Theorem 7.9.1), together with
  convergence of Picard iterates.
* **§7.10–7.11** Permanence principles: Cauchy's infinitesimal-to-real neighborhood principle
  (`cauchy_permanence_principle`), Robinson's sequential lemma in the ultrapower
  (`robinson_sequential_lemma`), and Exercises 7.11(1)–(3) (including constancy of continuous
  functions on intervals whose hyperreal extensions take only real values).
* **§7.12–7.15** Hypersequences of functions (`starFunSeq`), pointwise convergence (Theorem 7.12.1),
  Robinson's nonstandard criterion for uniform convergence (Theorem 7.12.2), non-uniform
  convergence of `xⁿ` on `[0, 1]` (both via Robinson's sequential lemma and via explicit Bernoulli
  witnesses), continuity of a uniform limit (Theorem 7.13.1, hybrid and purely nonstandard proofs),
  infinitesimal continuity of extended hypersequence terms (Theorem 7.14.1), and Cauchy's 1821
  sum theorem (§7.15: classical counterexample series and the Robinson–Cleave–Lakatos vindication).
-/

noncomputable section

namespace Goldblatt.Ch07

open Filter
open Hyperreal (ofSeq ofSeq_lt_ofSeq ofSeq_le_ofSeq ofSeq_surjective)
open scoped Topology Classical

/-! ## Algebraic & Transfer Helpers for `starFun`, `halo`, and `starSet` -/

/-- Membership in `halo b` is symmetric: `x ∈ halo b ↔ x ≈ₕ b`. -/
@[simp]
theorem mem_halo_iff {b x : ℝ*} : x ∈ halo b ↔ x ≈ₕ b :=
  ⟨InfClose.symm, InfClose.symm⟩

/-- `starFun` of a constant function is the constant hyperreal. -/
@[simp]
theorem starFun_const (c : ℝ) (x : ℝ*) : starFun (fun _ ↦ c) x = (c : ℝ*) :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` commutes with pointwise addition. -/
theorem starFun_add (f g : ℝ → ℝ) (x : ℝ*) :
    starFun (fun t ↦ f t + g t) x = starFun f x + starFun g x :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` commutes with pointwise subtraction. -/
theorem starFun_sub (f g : ℝ → ℝ) (x : ℝ*) :
    starFun (fun t ↦ f t - g t) x = starFun f x - starFun g x :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` commutes with pointwise negation. -/
theorem starFun_neg (f : ℝ → ℝ) (x : ℝ*) :
    starFun (fun t ↦ -f t) x = -starFun f x :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` commutes with pointwise multiplication. -/
theorem starFun_mul (f g : ℝ → ℝ) (x : ℝ*) :
    starFun (fun t ↦ f t * g t) x = starFun f x * starFun g x :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` commutes with pointwise division. -/
theorem starFun_div (f g : ℝ → ℝ) (x : ℝ*) :
    starFun (fun t ↦ f t / g t) x = starFun f x / starFun g x :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` commutes with pointwise inversion. -/
theorem starFun_inv (f : ℝ → ℝ) (x : ℝ*) :
    starFun (fun t ↦ (f t)⁻¹) x = (starFun f x)⁻¹ :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` of `(fun t ↦ t)` is the identity. -/
@[simp]
theorem starFun_id_apply (x : ℝ*) : starFun (fun t ↦ t) x = x :=
  Germ.inductionOn x fun _ ↦ rfl

/-- `starFun` commutes with natural powers. -/
theorem starFun_pow (f : ℝ → ℝ) (n : ℕ) (x : ℝ*) :
    starFun (fun t ↦ f t ^ n) x = starFun f x ^ n :=
  Germ.inductionOn x fun _ ↦ rfl

/-- Pointwise form of `starFun_comp`: `* (g ∘ f) (x) = *g (*f x)`. -/
@[simp]
theorem starFun_comp_apply (g f : ℝ → ℝ) (x : ℝ*) :
    starFun (g ∘ f) x = starFun g (starFun f x) :=
  congrFun (starFun_comp g f) x

/-- Enlargement of `Set.Iio b` is `Set.Iio (b : ℝ*)`. -/
@[simp]
theorem starSet_Iio (b : ℝ) : starSet (Set.Iio b) = Set.Iio (b : ℝ*) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp only [ofSeq_mem_starSet, Set.mem_Iio]
  exact ⟨ofSeq_lt_ofSeq.2, ofSeq_lt_ofSeq.1⟩

/-- Enlargement of `Set.Iic b` is `Set.Iic (b : ℝ*)`. -/
@[simp]
theorem starSet_Iic (b : ℝ) : starSet (Set.Iic b) = Set.Iic (b : ℝ*) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp only [ofSeq_mem_starSet, Set.mem_Iic]
  exact ⟨ofSeq_le_ofSeq.2, ofSeq_le_ofSeq.1⟩

/-- Enlargement of a singleton `{c}` is `{(c : ℝ*)}`. -/
@[simp]
theorem starSet_singleton (c : ℝ) : starSet ({c} : Set ℝ) = {(c : ℝ*)} := by
  rw [starSet_eq_image_of_finite (Set.finite_singleton c), Set.image_singleton]

/-- If `f` maps `A` into `B`, then `starFun f` maps `starSet A` into `starSet B`. -/
theorem starFun_mapsTo {f : ℝ → ℝ} {A B : Set ℝ} (h : Set.MapsTo f A B) :
    Set.MapsTo (starFun f) (starSet A) (starSet B) := by
  intro x hx
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  exact hx.mono fun n hn ↦ h hn

/-- If `b ≈ₕ (c : ℝ*)` for standard `c : ℝ`, then `b` is limited. -/
theorem isLimited_of_infClose_coe {b : ℝ*} {c : ℝ} (h : b ≈ₕ (c : ℝ*)) : IsLimited b := by
  have : b = (c : ℝ*) + (b - (c : ℝ*)) := by ring
  rw [this]
  exact (isLimited_coe c).add h.isLimited

/-- Canonical harmonic infinitesimal `ofSeq (fun n ↦ ((n : ℝ) + 1)⁻¹)` is positive infinitesimal. -/
theorem isPosInfinitesimal_inv_nat_succ :
    IsPosInfinitesimal (ofSeq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹)) := by
  refine ⟨ofSeq_lt_ofSeq.2 (Eventually.of_forall fun n ↦ by positivity), fun r hr ↦ ?_⟩
  have htend : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hinf := ofSeq_infinitesimal_of_tendsto_zero htend r hr
  have hpos : 0 ≤ ofSeq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) :=
    ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ by positivity)
  rwa [abs_of_nonneg hpos] at hinf

/-- `ofSeq (fun n ↦ ((n : ℝ) + 1)⁻¹)` is infinitesimal. -/
theorem isInfinitesimal_inv_nat_succ :
    IsInfinitesimal (ofSeq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹)) :=
  isInfinitesimal_iff_trichotomy.2 (Or.inl isPosInfinitesimal_inv_nat_succ)

/-! ## §7.1 Cauchy's Account of Continuity and Microcontinuity -/

/-- Goldblatt §7.1, equation `(i)` (p. 76): Standard `ε`-`δ` continuity of `f : ℝ → ℝ` at `c ∈ ℝ`. -/
def EpsDeltaContinuousAt (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x - c| < δ → |f x - f c| < ε

/-- Goldblatt §7.1 (p. 77): Standard `ε`-`δ` continuity of `f : ℝ → ℝ` at `c` relative to `A ⊆ ℝ`. -/
def EpsDeltaContinuousWithinAt (f : ℝ → ℝ) (A : Set ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ A, |x - c| < δ → |f x - f c| < ε

/-- Equivalence of `ContinuousAt` and `EpsDeltaContinuousAt` on `ℝ`. -/
theorem continuousAt_iff_epsDelta {f : ℝ → ℝ} {c : ℝ} :
    ContinuousAt f c ↔ EpsDeltaContinuousAt f c := by
  simp only [Metric.continuousAt_iff, EpsDeltaContinuousAt, Real.dist_eq]

/-- Equivalence of `ContinuousWithinAt` and `EpsDeltaContinuousWithinAt` on `ℝ`. -/
theorem continuousWithinAt_iff_epsDelta {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ} :
    ContinuousWithinAt f A c ↔ EpsDeltaContinuousWithinAt f A c := by
  simp only [Metric.continuousWithinAt_iff, EpsDeltaContinuousWithinAt, Real.dist_eq]

/-- Goldblatt §7.1, Theorem 7.1.3 `(1) ↔ (2) ↔ (3)` core lemma (p. 77):
If there exists a positive hyperreal `d` (e.g. a positive infinitesimal) such that
`starFun f x ≈ₕ (f c : ℝ*)` for all `x ∈ starSet A` with `|x - c| < d`, then `f` is `ε`-`δ`
continuous at `c` within `A`. -/
theorem epsDeltaContinuousWithinAt_of_exists_pos_infClose {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (h : ∃ d : ℝ*, 0 < d ∧ ∀ x ∈ starSet A, |x - (c : ℝ*)| < d → starFun f x ≈ₕ (f c : ℝ*)) :
    EpsDeltaContinuousWithinAt f A c := by
  rcases h with ⟨d, hd_pos, hd⟩
  rcases ofSeq_surjective d with ⟨dSeq, rfl⟩
  have hd_ev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < dSeq n := ofSeq_lt_ofSeq.1 hd_pos
  intro ε hε
  by_contra hnot
  push Not at hnot
  obtain ⟨a₀, ha₀, _, _⟩ := hnot 1 one_pos
  have hex : ∀ n : ℕ, 0 < dSeq n → ∃ x ∈ A, |x - c| < dSeq n / 2 ∧ ε ≤ |f x - f c| :=
    fun n hn ↦ hnot (dSeq n / 2) (half_pos hn)
  let r : ℕ → ℝ := fun n ↦ if hn : 0 < dSeq n then (hex n hn).choose else a₀
  have hrA : ofSeq r ∈ starSet A := by
    refine ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ ?_)
    by_cases hn : 0 < dSeq n
    · simp only [r, hn, ↓reduceDIte]
      exact (hex n hn).choose_spec.1
    · simp only [r, hn, ↓reduceDIte]
      exact ha₀
  have hr_lt : |ofSeq r - (c : ℝ*)| < ofSeq dSeq := by
    refine ofSeq_lt_ofSeq.2 (hd_ev.mono fun n hn ↦ ?_)
    change |r n - c| < dSeq n
    simp only [r, hn, ↓reduceDIte]
    exact ((hex n hn).choose_spec.2.1).trans (half_lt_self hn)
  have hr_ge : (ε : ℝ*) ≤ |starFun f (ofSeq r) - (f c : ℝ*)| := by
    refine ofSeq_le_ofSeq.2 (hd_ev.mono fun n hn ↦ ?_)
    change ε ≤ |f (r n) - f c|
    simp only [r, hn, ↓reduceDIte]
    exact (hex n hn).choose_spec.2.2
  exact not_lt_of_ge hr_ge (hd (ofSeq r) hrA hr_lt ε hε)

/-- Goldblatt §7.1, Theorem 7.1.3 `(1) ↔ (2)` (p. 77):
`f : ℝ → ℝ` is continuous at `c` within `A ⊆ ℝ` if and only if `*f(x) ≈ₕ f(c)` for all `x ∈ *A`
with `x ≈ₕ c`. -/
theorem continuousWithinAt_iff_infClose {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ} :
    ContinuousWithinAt f A c ↔
      ∀ x ∈ starSet A, x ≈ₕ (c : ℝ*) → starFun f x ≈ₕ (f c : ℝ*) := by
  rw [continuousWithinAt_iff_epsDelta]
  constructor
  · intro hf x hx hxc ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := hf ε hε
    have hlt_δ : |x - (c : ℝ*)| < (δ : ℝ*) := hxc δ hδ_pos
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hr_lt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |r n - c| < δ := ofSeq_lt_ofSeq.1 hlt_δ
    exact ofSeq_lt_ofSeq.2 ((hx.and hr_lt).mono fun n ⟨hnA, hnr⟩ ↦ hδ (r n) hnA hnr)
  · intro h
    refine epsDeltaContinuousWithinAt_of_exists_pos_infClose
      ⟨Hyperreal.epsilon, Hyperreal.epsilon_pos, fun x hx hxd ↦ h x hx ?_⟩
    exact isInfinitesimal_of_abs_le isInfinitesimal_epsilon
      (hxd.le.trans (le_abs_self Hyperreal.epsilon))

/-- Explicit `ε`-`δ` form of Goldblatt Theorem 7.1.3 `(1) ↔ (2)` (p. 77). -/
theorem epsDeltaContinuousWithinAt_iff_infClose {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ} :
    EpsDeltaContinuousWithinAt f A c ↔
      ∀ x ∈ starSet A, x ≈ₕ (c : ℝ*) → starFun f x ≈ₕ (f c : ℝ*) := by
  rw [← continuousWithinAt_iff_epsDelta, continuousWithinAt_iff_infClose]

/-- Goldblatt §7.1, Theorem 7.1.3 `(1) ↔ (3)` (p. 77):
`f` is continuous at `c` within `A` iff there is a positive infinitesimal `d` such that
`*f(x) ≈ₕ f(c)` for all `x ∈ *A` with `|x - c| < d`. -/
theorem continuousWithinAt_iff_exists_posInfinitesimal {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ} :
    ContinuousWithinAt f A c ↔
      ∃ d : ℝ*, IsPosInfinitesimal d ∧
        ∀ x ∈ starSet A, |x - (c : ℝ*)| < d → starFun f x ≈ₕ (f c : ℝ*) := by
  constructor
  · intro hf
    refine ⟨Hyperreal.epsilon,
      ⟨Hyperreal.epsilon_pos, fun _ hr ↦ Hyperreal.epsilon_lt_of_pos hr⟩,
      fun x hx hxd ↦ (continuousWithinAt_iff_infClose.1 hf) x hx ?_⟩
    exact isInfinitesimal_of_abs_le isInfinitesimal_epsilon
      (hxd.le.trans (le_abs_self Hyperreal.epsilon))
  · rintro ⟨d, ⟨hd_pos, _⟩, hd⟩
    exact continuousWithinAt_iff_epsDelta.2
      (epsDeltaContinuousWithinAt_of_exists_pos_infClose ⟨d, hd_pos, hd⟩)

/-- Goldblatt §7.1, Theorem 7.1.1 (p. 75):
`f : ℝ → ℝ` is continuous at `c ∈ ℝ` if and only if `*f(x) ≈ₕ f(c)` for all `x ∈ ℝ*` with `x ≈ₕ c`. -/
theorem continuousAt_iff_infClose {f : ℝ → ℝ} {c : ℝ} :
    ContinuousAt f c ↔ ∀ x : ℝ*, x ≈ₕ (c : ℝ*) → starFun f x ≈ₕ (f c : ℝ*) := by
  rw [← continuousWithinAt_univ, continuousWithinAt_iff_infClose]
  simp [starSet_univ]

/-- Explicit `ε`-`δ` form of Goldblatt Theorem 7.1.1 (pp. 75–76). -/
theorem epsDeltaContinuousAt_iff_infClose {f : ℝ → ℝ} {c : ℝ} :
    EpsDeltaContinuousAt f c ↔ ∀ x : ℝ*, x ≈ₕ (c : ℝ*) → starFun f x ≈ₕ (f c : ℝ*) := by
  rw [← continuousAt_iff_epsDelta, continuousAt_iff_infClose]

/-- Goldblatt §7.1, Theorem 7.1.1 halo formulation (p. 75):
`f` is continuous at `c ∈ ℝ` if and only if `*f(hal(c)) ⊆ hal(f(c))`. -/
theorem continuousAt_iff_image_halo_subset {f : ℝ → ℝ} {c : ℝ} :
    ContinuousAt f c ↔ starFun f '' halo (c : ℝ*) ⊆ halo (f c : ℝ*) := by
  rw [continuousAt_iff_infClose]
  constructor
  · rintro h _ ⟨x, hx, rfl⟩
    exact mem_halo_iff.2 (h x (mem_halo_iff.1 hx))
  · intro h x hxc
    exact mem_halo_iff.1 (h ⟨x, mem_halo_iff.2 hxc, rfl⟩)

/-- Goldblatt §7.1, Corollary 7.1.2 (pp. 76–77):
`f` is continuous at `c ∈ ℝ` iff there exists a positive infinitesimal `d` such that
`*f(x) ≈ₕ f(c)` whenever `|x - c| < d`. -/
theorem continuousAt_iff_exists_posInfinitesimal {f : ℝ → ℝ} {c : ℝ} :
    ContinuousAt f c ↔
      ∃ d : ℝ*, IsPosInfinitesimal d ∧ ∀ x : ℝ*, |x - (c : ℝ*)| < d → starFun f x ≈ₕ (f c : ℝ*) := by
  rw [← continuousWithinAt_univ, continuousWithinAt_iff_exists_posInfinitesimal]
  simp [starSet_univ]

/-- Goldblatt §7.1, Theorem 7.1.3 set-level form (p. 77):
`ContinuousOn f A` holds iff microcontinuity holds at every real point `c ∈ A` for points in `*A`. -/
theorem continuousOn_iff_infClose {f : ℝ → ℝ} {A : Set ℝ} :
    ContinuousOn f A ↔
      ∀ c ∈ A, ∀ x ∈ starSet A, x ≈ₕ (c : ℝ*) → starFun f x ≈ₕ (f c : ℝ*) := by
  simp only [ContinuousOn, continuousWithinAt_iff_infClose]

/-- Global microcontinuity characterization of `Continuous f`. -/
theorem continuous_iff_infClose {f : ℝ → ℝ} :
    Continuous f ↔ ∀ c : ℝ, ∀ x : ℝ*, x ≈ₕ (c : ℝ*) → starFun f x ≈ₕ (f c : ℝ*) := by
  simp only [continuous_iff_continuousAt, continuousAt_iff_infClose]

/-! ### Nonstandard Proofs of Algebra & Composition of Continuous Functions -/

/-- Sum of functions continuous within `A` at `c` is continuous within `A` at `c`
(nonstandard proof via `InfClose.add`). -/
theorem continuousWithinAt_add_nonstandard {f g : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (hf : ContinuousWithinAt f A c) (hg : ContinuousWithinAt g A c) :
    ContinuousWithinAt (fun x ↦ f x + g x) A c := by
  rw [continuousWithinAt_iff_infClose] at hf hg ⊢
  intro x hx hxc
  rw [starFun_add, Hyperreal.coe_add]
  exact (hf x hx hxc).add (hg x hx hxc)

/-- Difference of functions continuous within `A` at `c` is continuous within `A` at `c`
(nonstandard proof via `InfClose.sub`). -/
theorem continuousWithinAt_sub_nonstandard {f g : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (hf : ContinuousWithinAt f A c) (hg : ContinuousWithinAt g A c) :
    ContinuousWithinAt (fun x ↦ f x - g x) A c := by
  rw [continuousWithinAt_iff_infClose] at hf hg ⊢
  intro x hx hxc
  rw [starFun_sub, Hyperreal.coe_sub]
  exact (hf x hx hxc).sub (hg x hx hxc)

/-- Negation of a function continuous within `A` at `c` is continuous within `A` at `c`
(nonstandard proof via `InfClose.neg`). -/
theorem continuousWithinAt_neg_nonstandard {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (hf : ContinuousWithinAt f A c) :
    ContinuousWithinAt (fun x ↦ -f x) A c := by
  rw [continuousWithinAt_iff_infClose] at hf ⊢
  intro x hx hxc
  rw [starFun_neg, Hyperreal.coe_neg]
  exact (hf x hx hxc).neg

/-- Product of functions continuous within `A` at `c` is continuous within `A` at `c`
(nonstandard proof via `InfClose.mul`). -/
theorem continuousWithinAt_mul_nonstandard {f g : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (hf : ContinuousWithinAt f A c) (hg : ContinuousWithinAt g A c) :
    ContinuousWithinAt (fun x ↦ f x * g x) A c := by
  rw [continuousWithinAt_iff_infClose] at hf hg ⊢
  intro x hx hxc
  have hfx := hf x hx hxc
  have hgx := hg x hx hxc
  rw [starFun_mul, Hyperreal.coe_mul]
  exact InfClose.mul (isLimited_of_infClose_coe hfx) (isLimited_of_infClose_coe hgx) hfx hgx

/-- Quotient of functions continuous within `A` at `c` (with `g c ≠ 0`) is continuous within `A`
at `c` (nonstandard proof via `InfClose.div`). -/
theorem continuousWithinAt_div_nonstandard {f g : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (hf : ContinuousWithinAt f A c) (hg : ContinuousWithinAt g A c) (hgc : g c ≠ 0) :
    ContinuousWithinAt (fun x ↦ f x / g x) A c := by
  rw [continuousWithinAt_iff_infClose] at hf hg ⊢
  intro x hx hxc
  have hfx := hf x hx hxc
  have hgx := hg x hx hxc
  have hgx_app : IsAppreciable (starFun g x) := by
    have : starFun g x = (g c : ℝ*) + (starFun g x - (g c : ℝ*)) := by ring
    rw [this]
    exact (isAppreciable_coe_iff.2 hgc).add_isInfinitesimal hgx
  rw [starFun_div, Hyperreal.coe_div]
  exact InfClose.div (isLimited_of_infClose_coe hfx) hgx_app hfx hgx

/-- Composition `g ∘ f` of functions continuous within `A` at `c` and within `B` at `f c`
(with `Set.MapsTo f A B`) is continuous within `A` at `c` (nonstandard 2-step `≈ₕ` proof). -/
theorem continuousWithinAt_comp_nonstandard {f g : ℝ → ℝ} {A B : Set ℝ} {c : ℝ}
    (hf : ContinuousWithinAt f A c) (hg : ContinuousWithinAt g B (f c))
    (hAB : Set.MapsTo f A B) :
    ContinuousWithinAt (g ∘ f) A c := by
  rw [continuousWithinAt_iff_infClose] at hf hg ⊢
  intro x hx hxc
  rw [starFun_comp_apply, Function.comp_apply]
  exact hg (starFun f x) (starFun_mapsTo hAB hx) (hf x hx hxc)

/-- Pointwise sum of functions continuous at `c` is continuous at `c` (nonstandard proof). -/
theorem continuousAt_add_nonstandard {f g : ℝ → ℝ} {c : ℝ}
    (hf : ContinuousAt f c) (hg : ContinuousAt g c) :
    ContinuousAt (fun x ↦ f x + g x) c := by
  rw [← continuousWithinAt_univ] at hf hg ⊢
  exact continuousWithinAt_add_nonstandard hf hg

/-- Pointwise difference of functions continuous at `c` is continuous at `c` (nonstandard proof). -/
theorem continuousAt_sub_nonstandard {f g : ℝ → ℝ} {c : ℝ}
    (hf : ContinuousAt f c) (hg : ContinuousAt g c) :
    ContinuousAt (fun x ↦ f x - g x) c := by
  rw [← continuousWithinAt_univ] at hf hg ⊢
  exact continuousWithinAt_sub_nonstandard hf hg

/-- Pointwise product of functions continuous at `c` is continuous at `c` (nonstandard proof). -/
theorem continuousAt_mul_nonstandard {f g : ℝ → ℝ} {c : ℝ}
    (hf : ContinuousAt f c) (hg : ContinuousAt g c) :
    ContinuousAt (fun x ↦ f x * g x) c := by
  rw [← continuousWithinAt_univ] at hf hg ⊢
  exact continuousWithinAt_mul_nonstandard hf hg

/-- Pointwise quotient of functions continuous at `c` (with `g c ≠ 0`) is continuous at `c`
(nonstandard proof). -/
theorem continuousAt_div_nonstandard {f g : ℝ → ℝ} {c : ℝ}
    (hf : ContinuousAt f c) (hg : ContinuousAt g c) (hgc : g c ≠ 0) :
    ContinuousAt (fun x ↦ f x / g x) c := by
  rw [← continuousWithinAt_univ] at hf hg ⊢
  exact continuousWithinAt_div_nonstandard hf hg hgc

/-- Composition `g ∘ f` of functions continuous at `c` and `f c` is continuous at `c`
(nonstandard 1-line microcontinuity proof). -/
theorem continuousAt_comp_nonstandard {f g : ℝ → ℝ} {c : ℝ}
    (hf : ContinuousAt f c) (hg : ContinuousAt g (f c)) :
    ContinuousAt (g ∘ f) c := by
  rw [continuousAt_iff_infClose] at hf hg ⊢
  exact fun x hxc ↦ starFun_comp_apply g f x ▸ hg (starFun f x) (hf x hxc)

/-! ## §7.2 Continuity of the Sine and Cosine Functions -/

/-- Goldblatt §7.2 (p. 78): Hyperreal addition formula for `sin`, transferred from `Real.sin_add`. -/
theorem starFun_sin_add (x y : ℝ*) :
    starFun Real.sin (x + y) =
      starFun Real.sin x * starFun Real.cos y + starFun Real.cos x * starFun Real.sin y :=
  Germ.inductionOn₂ x y fun r s ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun n ↦ Real.sin_add (r n) (s n)

/-- Hyperreal addition formula for `cos`, transferred from `Real.cos_add`. -/
theorem starFun_cos_add (x y : ℝ*) :
    starFun Real.cos (x + y) =
      starFun Real.cos x * starFun Real.cos y - starFun Real.sin x * starFun Real.sin y :=
  Germ.inductionOn₂ x y fun r s ↦
    Germ.coe_eq.2 <| Eventually.of_forall fun n ↦ Real.cos_add (r n) (s n)

/-- Goldblatt §7.2 (pp. 77–78): **Nonstandard proof that `Real.sin` is continuous on `ℝ`**, using
`sin(c + δ) - sin c = sin c (cos δ - 1) + cos c sin δ`, `cos δ ≈ₕ 1`, and `sin δ ≈ₕ 0`. -/
theorem continuous_sin_nonstandard : Continuous Real.sin := by
  rw [continuous_iff_infClose]
  intro c x hxc
  set δ : ℝ* := x - (c : ℝ*)
  have hδ : IsInfinitesimal δ := hxc
  have hx_eq : x = (c : ℝ*) + δ := by simp [δ]
  have hdiff : starFun Real.sin x - (Real.sin c : ℝ*) =
      (Real.sin c : ℝ*) * (starFun Real.cos δ - 1) +
        (Real.cos c : ℝ*) * starFun Real.sin δ := by
    rw [hx_eq, starFun_sin_add, starFun_coe, starFun_coe]
    ring
  unfold InfClose
  rw [hdiff]
  have hterm1 : IsInfinitesimal ((Real.sin c : ℝ*) * (starFun Real.cos δ - 1)) :=
    (isLimited_coe (Real.sin c)).mul_isInfinitesimal (starFun_cos_infClose_one hδ)
  have hterm2 : IsInfinitesimal ((Real.cos c : ℝ*) * starFun Real.sin δ) :=
    (isLimited_coe (Real.cos c)).mul_isInfinitesimal
      (infClose_zero_iff.1 (starFun_sin_infClose_zero hδ))
  exact hterm1.add hterm2

/-- Goldblatt §7.2 (pp. 77–78): **Nonstandard proof that `Real.cos` is continuous on `ℝ`**, using
`cos(c + δ) - cos c = cos c (cos δ - 1) - sin c sin δ`, `cos δ ≈ₕ 1`, and `sin δ ≈ₕ 0`. -/
theorem continuous_cos_nonstandard : Continuous Real.cos := by
  rw [continuous_iff_infClose]
  intro c x hxc
  set δ : ℝ* := x - (c : ℝ*)
  have hδ : IsInfinitesimal δ := hxc
  have hx_eq : x = (c : ℝ*) + δ := by simp [δ]
  have hdiff : starFun Real.cos x - (Real.cos c : ℝ*) =
      (Real.cos c : ℝ*) * (starFun Real.cos δ - 1) -
        (Real.sin c : ℝ*) * starFun Real.sin δ := by
    rw [hx_eq, starFun_cos_add, starFun_coe, starFun_coe]
    ring
  unfold InfClose
  rw [hdiff]
  have hterm1 : IsInfinitesimal ((Real.cos c : ℝ*) * (starFun Real.cos δ - 1)) :=
    (isLimited_coe (Real.cos c)).mul_isInfinitesimal (starFun_cos_infClose_one hδ)
  have hterm2 : IsInfinitesimal ((Real.sin c : ℝ*) * starFun Real.sin δ) :=
    (isLimited_coe (Real.sin c)).mul_isInfinitesimal
      (infClose_zero_iff.1 (starFun_sin_infClose_zero hδ))
  exact hterm1.sub hterm2

/-! ## §7.3–7.4 Limits of Functions and Exercises on Limits -/

/-- Explicit `ε`-`δ` punctured limit of `f` on `A` as `x → c` (`0 < |x - c| < δ → |f x - L| < ε`). -/
def EpsDeltaPuncturedLimitOn (f : ℝ → ℝ) (A : Set ℝ) (c L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ A, 0 < |x - c| → |x - c| < δ → |f x - L| < ε

/-- Equivalence between `Tendsto f (𝓝[A \ {c}] c) (𝓝 L)` and `EpsDeltaPuncturedLimitOn f A c L`. -/
theorem tendsto_nhdsWithin_diff_singleton_iff_epsDelta {f : ℝ → ℝ} {A : Set ℝ} {c L : ℝ} :
    Tendsto f (𝓝[A \ {c}] c) (𝓝 L) ↔ EpsDeltaPuncturedLimitOn f A c L := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [EpsDeltaPuncturedLimitOn, Set.mem_sdiff, Set.mem_singleton_iff, Real.dist_eq]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := h ε hε
    exact ⟨δ, hδ_pos, fun x hxA hpos hlt ↦ hδ ⟨hxA, sub_ne_zero.1 (abs_pos.1 hpos)⟩ hlt⟩
  · intro h ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := h ε hε
    exact ⟨δ, hδ_pos, fun x ⟨hxA, hne⟩ hlt ↦ hδ x hxA (abs_pos.2 (sub_ne_zero.2 hne)) hlt⟩

/-- General characterization of `Tendsto f (𝓝[S] c) (𝓝 L)` via hyperreals in `starSet S`. -/
theorem tendsto_nhdsWithin_nhds_iff_infClose {f : ℝ → ℝ} {S : Set ℝ} {c L : ℝ} :
    Tendsto f (𝓝[S] c) (𝓝 L) ↔
      ∀ x ∈ starSet S, x ≈ₕ (c : ℝ*) → starFun f x ≈ₕ (L : ℝ*) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h x hx hxc ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := h ε hε
    have hlt_δ : |x - (c : ℝ*)| < (δ : ℝ*) := hxc δ hδ_pos
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hr_lt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |r n - c| < δ := ofSeq_lt_ofSeq.1 hlt_δ
    refine ofSeq_lt_ofSeq.2 ((hx.and hr_lt).mono fun n ⟨hnS, hnr⟩ ↦ ?_)
    have h1 := hδ hnS (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at h1
  · intro h ε hε
    by_contra hnot
    push Not at hnot
    choose r hr using fun n : ℕ ↦ hnot ((n : ℝ) + 1)⁻¹ (by positivity)
    have hrS : ofSeq r ∈ starSet S :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (hr n).1)
    have hrc : ofSeq r ≈ₕ (c : ℝ*) := by
      refine isInfinitesimal_of_abs_le isInfinitesimal_inv_nat_succ ?_
      have hpos : 0 ≤ ofSeq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) :=
        ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ by positivity)
      rw [abs_of_nonneg hpos]
      refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
      have hlt := (hr n).2.1
      rw [Real.dist_eq] at hlt
      exact hlt.le
    have hr_ge : (ε : ℝ*) ≤ |starFun f (ofSeq r) - (L : ℝ*)| := by
      refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
      have hge := (hr n).2.2
      rwa [Real.dist_eq] at hge
    exact not_lt_of_ge hr_ge (h (ofSeq r) hrS hrc ε hε)

/-- Goldblatt §7.3, bullet 1 (p. 78): Right-hand limit characterization
`lim_{x → c⁺, x ∈ A} f(x) = L ↔ ∀ x ∈ *A, c < x → x ≈ₕ c → *f(x) ≈ₕ L`. -/
theorem tendsto_right_iff_infClose {f : ℝ → ℝ} {A : Set ℝ} {c L : ℝ} :
    Tendsto f (𝓝[A ∩ Set.Ioi c] c) (𝓝 L) ↔
      ∀ x ∈ starSet A, (c : ℝ*) < x → x ≈ₕ (c : ℝ*) → starFun f x ≈ₕ (L : ℝ*) := by
  rw [tendsto_nhdsWithin_nhds_iff_infClose]
  simp only [starSet_inter, starSet_Ioi, Set.mem_inter_iff, Set.mem_Ioi, and_imp]

/-- Goldblatt §7.3, bullet 2 (p. 78): Left-hand limit characterization
`lim_{x → c⁻, x ∈ A} f(x) = L ↔ ∀ x ∈ *A, x < c → x ≈ₕ c → *f(x) ≈ₕ L`. -/
theorem tendsto_left_iff_infClose {f : ℝ → ℝ} {A : Set ℝ} {c L : ℝ} :
    Tendsto f (𝓝[A ∩ Set.Iio c] c) (𝓝 L) ↔
      ∀ x ∈ starSet A, x < (c : ℝ*) → x ≈ₕ (c : ℝ*) → starFun f x ≈ₕ (L : ℝ*) := by
  rw [tendsto_nhdsWithin_nhds_iff_infClose]
  simp only [starSet_inter, starSet_Iio, Set.mem_inter_iff, Set.mem_Iio, and_imp]

/-- Goldblatt §7.3, bullet 3 (p. 78): Punctured two-sided limit characterization
`lim_{x → c, x ∈ A \ {c}} f(x) = L ↔ ∀ x ∈ *A, x ≠ c → x ≈ₕ c → *f(x) ≈ₕ L`. -/
theorem tendsto_punctured_iff_infClose {f : ℝ → ℝ} {A : Set ℝ} {c L : ℝ} :
    Tendsto f (𝓝[A \ {c}] c) (𝓝 L) ↔
      ∀ x ∈ starSet A, x ≠ (c : ℝ*) → x ≈ₕ (c : ℝ*) → starFun f x ≈ₕ (L : ℝ*) := by
  rw [tendsto_nhdsWithin_nhds_iff_infClose]
  simp only [starSet_diff, starSet_singleton, Set.mem_sdiff, Set.mem_singleton_iff, and_imp]

/-- Explicit `ε`-`δ` punctured limit equivalence with the hyperreal characterization. -/
theorem epsDeltaPuncturedLimitOn_iff_infClose {f : ℝ → ℝ} {A : Set ℝ} {c L : ℝ} :
    EpsDeltaPuncturedLimitOn f A c L ↔
      ∀ x ∈ starSet A, x ≠ (c : ℝ*) → x ≈ₕ (c : ℝ*) → starFun f x ≈ₕ (L : ℝ*) := by
  rw [← tendsto_nhdsWithin_diff_singleton_iff_epsDelta, tendsto_punctured_iff_infClose]

/-- Goldblatt §7.3, bullet 4 (p. 78): Divergence to `+∞` at `c`
`lim_{x → c, x ∈ A \ {c}} f(x) = +∞ ↔ ∀ x ∈ *A, x ≠ c → x ≈ₕ c → IsPosUnlimited (*f x)`. -/
theorem tendsto_punctured_atTop_iff_isPosUnlimited {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ} :
    Tendsto f (𝓝[A \ {c}] c) atTop ↔
      ∀ x ∈ starSet A, x ≠ (c : ℝ*) → x ≈ₕ (c : ℝ*) → IsPosUnlimited (starFun f x) := by
  rw [Filter.tendsto_atTop]
  constructor
  · intro h x hx hne hxc B
    have hev : {t : ℝ | B + 1 ≤ f t} ∈ 𝓝[A \ {c}] c := h (B + 1)
    rw [Metric.mem_nhdsWithin_iff] at hev
    obtain ⟨δ, hδ_pos, hδ⟩ := hev
    have hlt_δ : |x - (c : ℝ*)| < (δ : ℝ*) := hxc δ hδ_pos
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hr_ne : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ≠ c :=
      Ultrafilter.eventually_not.2 fun heq ↦ hne (Germ.coe_eq.2 heq)
    have hr_lt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |r n - c| < δ := ofSeq_lt_ofSeq.1 hlt_δ
    refine ofSeq_lt_ofSeq.2 (((hx.and hr_ne).and hr_lt).mono fun n ⟨⟨hnA, hnc⟩, hnr⟩ ↦ ?_)
    change B < f (r n)
    have hball : r n ∈ Metric.ball c δ ∩ (A \ {c}) :=
      ⟨by simpa [Metric.mem_ball, Real.dist_eq] using hnr, hnA, hnc⟩
    have hge : B + 1 ≤ f (r n) := hδ hball
    linarith
  · intro h B
    change {t : ℝ | B ≤ f t} ∈ 𝓝[A \ {c}] c
    rw [Metric.mem_nhdsWithin_iff]
    by_contra hnot
    push Not at hnot
    have hex : ∀ n : ℕ, ∃ t : ℝ, |t - c| < ((n : ℝ) + 1)⁻¹ ∧ t ∈ A ∧ t ≠ c ∧ f t < B := by
      intro n
      obtain ⟨t, ⟨ht_ball, htA, htc⟩, htB⟩ :=
        Set.not_subset.1 (hnot ((n : ℝ) + 1)⁻¹ (by positivity))
      rw [Metric.mem_ball, Real.dist_eq] at ht_ball
      have htB' : f t < B := not_le.1 htB
      exact ⟨t, ht_ball, htA, htc, htB'⟩
    choose r hr using hex
    have hrA : ofSeq r ∈ starSet A :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (hr n).2.1)
    have hr_ne : ofSeq r ≠ (c : ℝ*) := by
      intro heq
      obtain ⟨n, hn⟩ := (Germ.coe_eq.1 heq).exists
      exact (hr n).2.2.1 hn
    have hrc : ofSeq r ≈ₕ (c : ℝ*) := by
      refine isInfinitesimal_of_abs_le isInfinitesimal_inv_nat_succ ?_
      have hpos : 0 ≤ ofSeq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) :=
        ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ by positivity)
      rw [abs_of_nonneg hpos]
      exact ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (hr n).1.le)
    have hle : starFun f (ofSeq r) ≤ (B : ℝ*) :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (hr n).2.2.2.le)
    exact not_lt_of_ge hle (h (ofSeq r) hrA hr_ne hrc B)

/-- Goldblatt §7.3, bullet 5 (p. 78): Divergence to `-∞` at `c`
`lim_{x → c, x ∈ A \ {c}} f(x) = -∞ ↔ ∀ x ∈ *A, x ≠ c → x ≈ₕ c → IsNegUnlimited (*f x)`. -/
theorem tendsto_punctured_atBot_iff_isNegUnlimited {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ} :
    Tendsto f (𝓝[A \ {c}] c) atBot ↔
      ∀ x ∈ starSet A, x ≠ (c : ℝ*) → x ≈ₕ (c : ℝ*) → IsNegUnlimited (starFun f x) := by
  rw [← tendsto_neg_atTop_iff, tendsto_punctured_atTop_iff_isPosUnlimited]
  constructor
  · intro h x hx hne hxc r
    have hlt := h x hx hne hxc (-r)
    rw [starFun_neg] at hlt
    have : (-r : ℝ*) < -starFun f x := by simpa using hlt
    linarith
  · intro h x hx hne hxc r
    have hlt := h x hx hne hxc (-r)
    rw [starFun_neg]
    have : starFun f x < (-r : ℝ*) := by simpa using hlt
    linarith

/-- Goldblatt §7.3, bullet 6 existence remark (p. 78): `*A` contains positive unlimited elements
if and only if `A` is unbounded above in `ℝ`. -/
theorem exists_isPosUnlimited_mem_starSet_iff {A : Set ℝ} :
    (∃ x ∈ starSet A, IsPosUnlimited x) ↔ ∀ M : ℝ, ∃ t ∈ A, M < t := by
  constructor
  · rintro ⟨x, hxA, hx_unl⟩ M
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hgt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), M < r n := ofSeq_lt_ofSeq.1 (hx_unl M)
    obtain ⟨n, hnA, hnM⟩ := (hxA.and hgt).exists
    exact ⟨r n, hnA, hnM⟩
  · intro h
    choose r hr using fun n : ℕ ↦ h (n : ℝ)
    refine ⟨ofSeq r, ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (hr n).1), fun M ↦ ?_⟩
    obtain ⟨k, hk⟩ := exists_nat_gt M
    have hgt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), M < r n := by
      have hat : ∀ᶠ n in atTop, M < r n :=
        eventually_atTop.2 ⟨k, fun n hn ↦ hk.trans (( Nat.cast_le.2 hn).trans_lt (hr n).2)⟩
      exact hat.filter_mono Nat.hyperfilter_le_atTop
    exact ofSeq_lt_ofSeq.2 hgt

/-- Goldblatt §7.3, bullet 6 (p. 78): Limit as `x → +∞` along `A`
`Tendsto f (atTop ⊓ 𝓟 A) (𝓝 L) ↔ ∀ x ∈ *A, IsPosUnlimited x → *f(x) ≈ₕ L`. -/
theorem tendsto_atTop_principal_nhds_iff_infClose {f : ℝ → ℝ} {A : Set ℝ} {L : ℝ} :
    Tendsto f (atTop ⊓ 𝓟 A) (𝓝 L) ↔
      ∀ x ∈ starSet A, IsPosUnlimited x → starFun f x ≈ₕ (L : ℝ*) := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro h x hxA hx_unl ε hε
    have hev := h ε hε
    rw [Filter.eventually_inf_principal, Filter.eventually_atTop] at hev
    obtain ⟨M, hM⟩ := hev
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hrM : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), M < r n := ofSeq_lt_ofSeq.1 (hx_unl M)
    refine ofSeq_lt_ofSeq.2 ((hxA.and hrM).mono fun n ⟨hnA, hnM⟩ ↦ ?_)
    have h1 := hM (r n) hnM.le hnA
    rwa [Real.dist_eq] at h1
  · intro h ε hε
    rw [Filter.eventually_inf_principal, Filter.eventually_atTop]
    by_contra hnot
    push Not at hnot
    choose r hr using fun n : ℕ ↦ hnot (n : ℝ)
    have hrA : ofSeq r ∈ starSet A :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (hr n).2.1)
    have hr_unl : IsPosUnlimited (ofSeq r) := by
      intro M
      obtain ⟨k, hk⟩ := exists_nat_gt M
      have hat : ∀ᶠ n in atTop, M < r n :=
        eventually_atTop.2 ⟨k, fun n hn ↦ hk.trans_le ((Nat.cast_le.2 hn).trans (hr n).1)⟩
      exact ofSeq_lt_ofSeq.2 (hat.filter_mono Nat.hyperfilter_le_atTop)
    have hr_ge : (ε : ℝ*) ≤ |starFun f (ofSeq r) - (L : ℝ*)| := by
      refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
      have hge := (hr n).2.2
      rwa [Real.dist_eq] at hge
    exact not_lt_of_ge hr_ge (h (ofSeq r) hrA hr_unl ε hε)

/-- Global `x → +∞` specialization of Goldblatt §7.3, bullet 6 (p. 78). -/
theorem tendsto_atTop_nhds_real_iff_infClose {f : ℝ → ℝ} {L : ℝ} :
    Tendsto f atTop (𝓝 L) ↔ ∀ x : ℝ*, IsPosUnlimited x → starFun f x ≈ₕ (L : ℝ*) := by
  have : (atTop : Filter ℝ) = atTop ⊓ 𝓟 Set.univ := by simp
  rw [this, tendsto_atTop_principal_nhds_iff_infClose]
  simp [starSet_univ]

/-- Goldblatt §7.3, bullet 7 existence remark (p. 78): `*A` contains negative unlimited elements
if and only if `A` is unbounded below in `ℝ`. -/
theorem exists_isNegUnlimited_mem_starSet_iff {A : Set ℝ} :
    (∃ x ∈ starSet A, IsNegUnlimited x) ↔ ∀ M : ℝ, ∃ t ∈ A, t < M := by
  constructor
  · rintro ⟨x, hxA, hx_unl⟩ M
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hlt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n < M := ofSeq_lt_ofSeq.1 (hx_unl M)
    obtain ⟨n, hnA, hnM⟩ := (hxA.and hlt).exists
    exact ⟨r n, hnA, hnM⟩
  · intro h
    choose r hr using fun n : ℕ ↦ h (-(n : ℝ))
    refine ⟨ofSeq r, ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (hr n).1), fun M ↦ ?_⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (-M)
    have hlt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n < M := by
      have hat : ∀ᶠ n in atTop, r n < M :=
        eventually_atTop.2 ⟨k, fun n hn ↦ by
          have hkn : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
          linarith [(hr n).2]⟩
      exact hat.filter_mono Nat.hyperfilter_le_atTop
    exact ofSeq_lt_ofSeq.2 hlt

/-- Goldblatt §7.3, bullet 7 (p. 78): Limit as `x → -∞` along `A`
`Tendsto f (atBot ⊓ 𝓟 A) (𝓝 L) ↔ ∀ x ∈ *A, IsNegUnlimited x → *f(x) ≈ₕ L`. -/
theorem tendsto_atBot_principal_nhds_iff_infClose {f : ℝ → ℝ} {A : Set ℝ} {L : ℝ} :
    Tendsto f (atBot ⊓ 𝓟 A) (𝓝 L) ↔
      ∀ x ∈ starSet A, IsNegUnlimited x → starFun f x ≈ₕ (L : ℝ*) := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro h x hxA hx_unl ε hε
    have hev := h ε hε
    rw [Filter.eventually_inf_principal, Filter.eventually_atBot] at hev
    obtain ⟨M, hM⟩ := hev
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hrM : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n < M := ofSeq_lt_ofSeq.1 (hx_unl M)
    refine ofSeq_lt_ofSeq.2 ((hxA.and hrM).mono fun n ⟨hnA, hnM⟩ ↦ ?_)
    have h1 := hM (r n) hnM.le hnA
    rwa [Real.dist_eq] at h1
  · intro h ε hε
    rw [Filter.eventually_inf_principal, Filter.eventually_atBot]
    by_contra hnot
    push Not at hnot
    choose r hr using fun n : ℕ ↦ hnot (-(n : ℝ))
    have hrA : ofSeq r ∈ starSet A :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (hr n).2.1)
    have hr_unl : IsNegUnlimited (ofSeq r) := by
      intro M
      obtain ⟨k, hk⟩ := exists_nat_gt (-M)
      have hat : ∀ᶠ n in atTop, r n < M :=
        eventually_atTop.2 ⟨k, fun n hn ↦ by
          have hkn : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
          linarith [(hr n).1]⟩
      exact ofSeq_lt_ofSeq.2 (hat.filter_mono Nat.hyperfilter_le_atTop)
    have hr_ge : (ε : ℝ*) ≤ |starFun f (ofSeq r) - (L : ℝ*)| := by
      refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
      have hge := (hr n).2.2
      rwa [Real.dist_eq] at hge
    exact not_lt_of_ge hr_ge (h (ofSeq r) hrA hr_unl ε hε)

/-! ### §7.4 Exercises on Limits (pp. 78–79) -/

/-- Goldblatt Exercise 7.4(2a) (p. 78): Two-sided punctured limit equals `L` iff both right-hand
and left-hand limits equal `L` (3-line nonstandard proof via trichotomy `x < c ∨ c < x`). -/
theorem tendsto_punctured_iff_right_and_left {f : ℝ → ℝ} {A : Set ℝ} {c L : ℝ} :
    Tendsto f (𝓝[A \ {c}] c) (𝓝 L) ↔
      Tendsto f (𝓝[A ∩ Set.Ioi c] c) (𝓝 L) ∧ Tendsto f (𝓝[A ∩ Set.Iio c] c) (𝓝 L) := by
  rw [tendsto_punctured_iff_infClose, tendsto_right_iff_infClose, tendsto_left_iff_infClose]
  constructor
  · intro h
    exact ⟨fun x hx hgt hxc ↦ h x hx hgt.ne' hxc, fun x hx hlt hxc ↦ h x hx hlt.ne hxc⟩
  · rintro ⟨hr, hl⟩ x hx hne hxc
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hl x hx hlt hxc
    · exact hr x hx hgt hxc

/-- Goldblatt Exercise 7.4(2b) (p. 78): Sum rule for functional limits via `≈ₕ`. -/
theorem tendsto_punctured_add_nonstandard {f g : ℝ → ℝ} {A : Set ℝ} {c L M : ℝ}
    (hf : Tendsto f (𝓝[A \ {c}] c) (𝓝 L)) (hg : Tendsto g (𝓝[A \ {c}] c) (𝓝 M)) :
    Tendsto (fun x ↦ f x + g x) (𝓝[A \ {c}] c) (𝓝 (L + M)) := by
  rw [tendsto_punctured_iff_infClose] at hf hg ⊢
  intro x hx hne hxc
  rw [starFun_add, Hyperreal.coe_add]
  exact (hf x hx hne hxc).add (hg x hx hne hxc)

/-- Goldblatt Exercise 7.4(2c) (p. 78): Product rule for functional limits via `≈ₕ`. -/
theorem tendsto_punctured_mul_nonstandard {f g : ℝ → ℝ} {A : Set ℝ} {c L M : ℝ}
    (hf : Tendsto f (𝓝[A \ {c}] c) (𝓝 L)) (hg : Tendsto g (𝓝[A \ {c}] c) (𝓝 M)) :
    Tendsto (fun x ↦ f x * g x) (𝓝[A \ {c}] c) (𝓝 (L * M)) := by
  rw [tendsto_punctured_iff_infClose] at hf hg ⊢
  intro x hx hne hxc
  have hfx := hf x hx hne hxc
  have hgx := hg x hx hne hxc
  rw [starFun_mul, Hyperreal.coe_mul]
  exact InfClose.mul (isLimited_of_infClose_coe hfx) (isLimited_of_infClose_coe hgx) hfx hgx

/-- Goldblatt Exercise 7.4(2d) (p. 78): Quotient rule for functional limits when `M ≠ 0` via `≈ₕ`. -/
theorem tendsto_punctured_div_nonstandard {f g : ℝ → ℝ} {A : Set ℝ} {c L M : ℝ}
    (hf : Tendsto f (𝓝[A \ {c}] c) (𝓝 L)) (hg : Tendsto g (𝓝[A \ {c}] c) (𝓝 M)) (hM : M ≠ 0) :
    Tendsto (fun x ↦ f x / g x) (𝓝[A \ {c}] c) (𝓝 (L / M)) := by
  rw [tendsto_punctured_iff_infClose] at hf hg ⊢
  intro x hx hne hxc
  have hfx := hf x hx hne hxc
  have hgx := hg x hx hne hxc
  have hgx_app : IsAppreciable (starFun g x) := by
    have : starFun g x = (M : ℝ*) + (starFun g x - (M : ℝ*)) := by ring
    rw [this]
    exact (isAppreciable_coe_iff.2 hM).add_isInfinitesimal hgx
  rw [starFun_div, Hyperreal.coe_div]
  exact InfClose.div (isLimited_of_infClose_coe hfx) hgx_app hfx hgx

/-- Goldblatt Exercise 7.4(2e) (p. 79): `f` is continuous at `c` within `A` iff
`lim_{x → c, x ∈ A \ {c}} f(x) = f(c)` (4-line nonstandard proof). -/
theorem continuousWithinAt_iff_tendsto_punctured {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ} :
    ContinuousWithinAt f A c ↔ Tendsto f (𝓝[A \ {c}] c) (𝓝 (f c)) := by
  rw [continuousWithinAt_iff_infClose, tendsto_punctured_iff_infClose]
  constructor
  · exact fun h x hx _ hxc ↦ h x hx hxc
  · intro h x hx hxc
    rcases eq_or_ne x (c : ℝ*) with rfl | hne
    · rw [starFun_coe]
    · exact h x hx hne hxc

/-- Global form of Goldblatt Exercise 7.4(2e) (p. 79):
`ContinuousAt f c ↔ Tendsto f (𝓝[≠] c) (𝓝 (f c))`. -/
theorem continuousAt_iff_tendsto_punctured_nonstandard {f : ℝ → ℝ} {c : ℝ} :
    ContinuousAt f c ↔ Tendsto f (𝓝[≠] c) (𝓝 (f c)) := by
  have heq : (Set.univ \ {c} : Set ℝ) = ({c}ᶜ : Set ℝ) := by ext; simp
  rw [← continuousWithinAt_univ, continuousWithinAt_iff_tendsto_punctured, heq]

/-! ### Exercise 7.4(3): Infinitesimal Continuity Analysis of Five Classical Functions (p. 79) -/

/-- Goldblatt Exercise 7.4(3), function `f₁` (p. 79): `sin(1/x)` for `x ≠ 0` and `0` at `0`. -/
def topologistSine (x : ℝ) : ℝ := if x = 0 then 0 else Real.sin (1 / x)

/-- Goldblatt Exercise 7.4(3), function `f₂` (p. 79): `x sin(1/x)` for `x ≠ 0` and `0` at `0`. -/
def dampedTopologistSine (x : ℝ) : ℝ := if x = 0 then 0 else x * Real.sin (1 / x)

/-- Goldblatt Exercise 7.4(3), function `f₃` (p. 79): Dirichlet's rational indicator (`1` on `ℚ`, `0` on `ℝ \ ℚ`). -/
def dirichletIndicator (x : ℝ) : ℝ :=
  if x ∈ Set.range (Rat.cast : ℚ → ℝ) then 1 else 0

/-- Goldblatt Exercise 7.4(3), function `f₄` (p. 79): `x` if `x ∈ ℚ`, `-x` if `x ∉ ℚ`. -/
def signedDirichlet (x : ℝ) : ℝ :=
  if x ∈ Set.range (Rat.cast : ℚ → ℝ) then x else -x

/-- Goldblatt Exercise 7.4(3), function `f₅` (p. 79): Thomae's ruler function (`1/n` if `x = m/n ∈ ℚ`
in lowest terms with `n ≥ 1`, and `0` if `x` is irrational). -/
def thomaeFunction (x : ℝ) : ℝ :=
  if h : x ∈ Set.range (Rat.cast : ℚ → ℝ) then ((h.choose.den : ℝ))⁻¹ else 0

/-- Goldblatt Exercise 7.4(3) `f₁` (p. 79): `topologistSine` is continuous at `c` iff `c ≠ 0`
(infinitesimal witness `x_n = 1 / (2π n + π/2) ≈ₕ 0` has `*f₁(x) = 1 ≉ 0`). -/
theorem continuousAt_topologistSine_iff {c : ℝ} :
    ContinuousAt topologistSine c ↔ c ≠ 0 := by
  rw [continuousAt_iff_infClose]
  constructor
  · intro hc h0
    subst h0
    let r : ℕ → ℝ := fun n ↦ (2 * Real.pi * (n : ℝ) + Real.pi / 2)⁻¹
    have hr_pos : ∀ n : ℕ, 0 < 2 * Real.pi * (n : ℝ) + Real.pi / 2 := fun n ↦ by
      have := Real.pi_pos
      positivity
    have hr_inf : ofSeq r ≈ₕ (0 : ℝ*) := by
      rw [infClose_zero_iff]
      intro ε hε
      have htend : Tendsto r atTop (𝓝 0) := by
        refine tendsto_inv_atTop_zero.comp ?_
        exact (tendsto_natCast_atTop_atTop.const_mul_atTop
          (by positivity : 0 < 2 * Real.pi)).atTop_add tendsto_const_nhds
      exact ofSeq_infinitesimal_of_tendsto_zero htend ε hε
    have hf1_eq : starFun topologistSine (ofSeq r) = 1 := by
      refine Germ.coe_eq.2 (Eventually.of_forall fun n ↦ ?_)
      change topologistSine (r n) = 1
      have hne : r n ≠ 0 := inv_ne_zero (hr_pos n).ne'
      simp only [topologistSine, hne, ↓reduceIte, one_div, r, inv_inv]
      have hper : Real.sin (2 * Real.pi * (n : ℝ) + Real.pi / 2) = Real.sin (Real.pi / 2) := by
        have := Real.sin_add_nat_mul_two_pi (Real.pi / 2) n
        rwa [add_comm, mul_comm (n : ℝ) (2 * Real.pi)] at this
      rw [hper, Real.sin_pi_div_two]
    have hclose := hc (ofSeq r) hr_inf
    have hf0 : topologistSine 0 = 0 := by simp [topologistSine]
    rw [hf1_eq, hf0] at hclose
    have h01 : (1 : ℝ) = 0 := coe_eq_of_infClose (by simpa using hclose)
    norm_num at h01
  · intro hc x hxc
    have hx_app : IsAppreciable x := by
      have : x = (c : ℝ*) + (x - (c : ℝ*)) := by ring
      rw [this]
      exact (isAppreciable_coe_iff.2 hc).add_isInfinitesimal hxc
    have hx_ne : x ≠ 0 := hx_app.ne_zero
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hr_ne : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ≠ 0 :=
      Ultrafilter.eventually_not.2 fun h0 ↦ hx_ne (Germ.coe_eq.2 h0)
    have hf_eq : starFun topologistSine (ofSeq r) = starFun Real.sin (1 / ofSeq r) := by
      refine Germ.coe_eq.2 (hr_ne.mono fun n hn ↦ ?_)
      simp [topologistSine, hn]
    have hinv_close : (1 / ofSeq r) ≈ₕ ((1 / c : ℝ) : ℝ*) := by
      rw [Hyperreal.coe_div, Hyperreal.coe_one]
      exact InfClose.div (isLimited_coe 1) hx_app (InfClose.refl _) hxc
    rw [hf_eq, show topologistSine c = Real.sin (1 / c) by simp [topologistSine, hc]]
    exact (continuousAt_iff_infClose.1 continuous_sin_nonstandard.continuousAt) _ hinv_close

/-- Goldblatt Exercise 7.4(3) `f₂` (p. 79): `dampedTopologistSine` (`x sin(1/x)`) is continuous on
all of `ℝ` (at `0`, `infinitesimal * limited = infinitesimal`). -/
theorem continuous_dampedTopologistSine : Continuous dampedTopologistSine := by
  rw [continuous_iff_infClose]
  intro c x hxc
  by_cases hc : c = 0
  · subst hc
    have hf0 : dampedTopologistSine 0 = 0 := by simp [dampedTopologistSine]
    rw [hf0, Hyperreal.coe_zero, infClose_zero_iff]
    have hε : IsInfinitesimal x := infClose_zero_iff.1 hxc
    refine isInfinitesimal_of_abs_le hε ?_
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
    change |dampedTopologistSine (r n)| ≤ |r n|
    by_cases hn : r n = 0
    · simp [dampedTopologistSine, hn]
    · simp only [dampedTopologistSine, hn, ↓reduceIte, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  · have hx_app : IsAppreciable x := by
      have : x = (c : ℝ*) + (x - (c : ℝ*)) := by ring
      rw [this]
      exact (isAppreciable_coe_iff.2 hc).add_isInfinitesimal hxc
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hr_ne : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ≠ 0 :=
      Ultrafilter.eventually_not.2 fun h0 ↦ hx_app.ne_zero (Germ.coe_eq.2 h0)
    have hf_eq : starFun dampedTopologistSine (ofSeq r) =
        ofSeq r * starFun topologistSine (ofSeq r) :=
      Germ.coe_eq.2 (hr_ne.mono fun n hn ↦ by simp [dampedTopologistSine, topologistSine, hn])
    have hc_eq : dampedTopologistSine c = c * topologistSine c := by
      simp [dampedTopologistSine, topologistSine, hc]
    have hsin_close :=
      (continuousAt_iff_infClose.1 (continuousAt_topologistSine_iff.2 hc)) (ofSeq r) hxc
    rw [hf_eq, hc_eq, Hyperreal.coe_mul]
    exact InfClose.mul hx_app.1 (isLimited_of_infClose_coe hsin_close) hxc hsin_close

/-- Every real halo `hal(c)` contains both a hyperrational `q ∈ *ℚ` and a hyperirrational `α ∉ *ℚ`. -/
theorem exists_hyperrat_and_hyperirrat_infClose (c : ℝ) :
    (∃ q ∈ starSet (Set.range (Rat.cast : ℚ → ℝ)), q ≈ₕ (c : ℝ*)) ∧
    (∃ α ∉ starSet (Set.range (Rat.cast : ℚ → ℝ)), α ≈ₕ (c : ℝ*)) := by
  obtain ⟨q, hq⟩ := exists_hyperrat_infClose (c : ℝ*)
  refine ⟨⟨Hyperrat.toHyperreal q, ?_, hq.symm⟩, ?_⟩
  · rw [← range_hyperrat_toHyperreal]
    exact ⟨q, rfl⟩
  · choose u hu using fun n : ℕ ↦
      exists_rat_btwn (lt_add_of_pos_right c (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹))
    let αSeq : ℕ → ℝ := fun n ↦ (u n : ℝ) + Real.sqrt 2 / ((n : ℝ) + 1)
    refine ⟨ofSeq αSeq, ?_, ?_⟩
    · intro hmem
      obtain ⟨n, qn, hqn⟩ := hmem.exists
      have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hsqrt : Real.sqrt 2 = (((qn - u n) * (n + 1) : ℚ) : ℝ) := by
        push_cast
        have : (u n : ℝ) + Real.sqrt 2 / ((n : ℝ) + 1) = (qn : ℝ) := hqn.symm
        field_simp [hd.ne'] at this
        linarith
      exact irrational_sqrt_two ⟨(qn - u n) * (n + 1), hsqrt.symm⟩
    · have hu_close : ofSeq (fun n ↦ (u n : ℝ)) ≈ₕ (c : ℝ*) := by
        refine isInfinitesimal_of_abs_le isInfinitesimal_inv_nat_succ ?_
        have hpos : 0 ≤ ofSeq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) :=
          ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ by positivity)
        rw [abs_of_nonneg hpos]
        refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
        change |(u n : ℝ) - c| ≤ ((n : ℝ) + 1)⁻¹
        rw [abs_le]
        exact ⟨by linarith [(hu n).1, (show (0 : ℝ) < ((n : ℝ) + 1)⁻¹ by positivity)],
               by linarith [(hu n).2]⟩
      have hrad_inf : IsInfinitesimal (ofSeq (fun n ↦ Real.sqrt 2 / ((n : ℝ) + 1))) := by
        have heq : ofSeq (fun n : ℕ ↦ Real.sqrt 2 / ((n : ℝ) + 1)) =
            (Real.sqrt 2 : ℝ*) * ofSeq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) :=
          Germ.coe_eq.2 (Eventually.of_forall fun n ↦ div_eq_mul_inv _ _)
        rw [heq]
        exact (isLimited_coe (Real.sqrt 2)).mul_isInfinitesimal isInfinitesimal_inv_nat_succ
      have hdecomp : ofSeq αSeq - (c : ℝ*) =
          (ofSeq (fun n ↦ (u n : ℝ)) - (c : ℝ*)) +
            ofSeq (fun n ↦ Real.sqrt 2 / ((n : ℝ) + 1)) :=
        Germ.coe_eq.2 (Eventually.of_forall fun n ↦ by simp [αSeq]; ring)
      unfold InfClose
      rw [hdecomp]
      exact IsInfinitesimal.add hu_close hrad_inf

/-- Goldblatt Exercise 7.4(3) `f₃` (p. 79): Dirichlet's indicator `dirichletIndicator` is
discontinuous at EVERY real point `c ∈ ℝ`. -/
theorem not_continuousAt_dirichletIndicator (c : ℝ) :
    ¬ ContinuousAt dirichletIndicator c := by
  rw [continuousAt_iff_infClose]
  intro hc
  obtain ⟨⟨q, hq_mem, hqc⟩, ⟨α, hα_nmem, hαc⟩⟩ := exists_hyperrat_and_hyperirrat_infClose c
  have hq_val : starFun dirichletIndicator q = 1 := by
    rcases ofSeq_surjective q with ⟨r, rfl⟩
    exact Germ.coe_eq.2 (hq_mem.mono fun n hn ↦ by simp [dirichletIndicator, hn])
  have hα_val : starFun dirichletIndicator α = 0 := by
    rcases ofSeq_surjective α with ⟨s, rfl⟩
    have hs : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), s n ∉ Set.range (Rat.cast : ℚ → ℝ) :=
      Ultrafilter.eventually_not.2 hα_nmem
    exact Germ.coe_eq.2 (hs.mono fun n hn ↦ by simp [dirichletIndicator, hn])
  have h1 := hc q hqc
  have h2 := hc α hαc
  rw [hq_val] at h1
  rw [hα_val] at h2
  have h10 : (1 : ℝ) = 0 := coe_eq_of_infClose (by simpa using h1.trans h2.symm)
  norm_num at h10

/-- Goldblatt Exercise 7.4(3) `f₄` (p. 79): `signedDirichlet` (`x` on `ℚ`, `-x` on `ℝ \ ℚ`) is
continuous at `c` if and only if `c = 0`. -/
theorem continuousAt_signedDirichlet_iff {c : ℝ} :
    ContinuousAt signedDirichlet c ↔ c = 0 := by
  rw [continuousAt_iff_infClose]
  constructor
  · intro hc
    obtain ⟨⟨q, hq_mem, hqc⟩, ⟨α, hα_nmem, hαc⟩⟩ := exists_hyperrat_and_hyperirrat_infClose c
    have hq_val : starFun signedDirichlet q = q := by
      rcases ofSeq_surjective q with ⟨r, rfl⟩
      exact Germ.coe_eq.2 (hq_mem.mono fun n hn ↦ by simp [signedDirichlet, hn])
    have hα_val : starFun signedDirichlet α = -α := by
      rcases ofSeq_surjective α with ⟨s, rfl⟩
      have hs : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), s n ∉ Set.range (Rat.cast : ℚ → ℝ) :=
        Ultrafilter.eventually_not.2 hα_nmem
      exact Germ.coe_eq.2 (hs.mono fun n hn ↦ by simp [signedDirichlet, hn])
    have h1 : (c : ℝ*) ≈ₕ (signedDirichlet c : ℝ*) :=
      hqc.symm.trans (hq_val ▸ hc q hqc)
    have h2 : ((-c : ℝ) : ℝ*) ≈ₕ (signedDirichlet c : ℝ*) := by
      rw [Hyperreal.coe_neg]
      exact hαc.neg.symm.trans (hα_val ▸ hc α hαc)
    have hceq : c = -c := coe_eq_of_infClose (h1.trans h2.symm)
    linarith
  · rintro rfl x hx0
    have hf0 : signedDirichlet 0 = 0 := by
      simp [signedDirichlet]
    rw [hf0, Hyperreal.coe_zero, infClose_zero_iff]
    have hε : IsInfinitesimal x := infClose_zero_iff.1 hx0
    refine isInfinitesimal_of_abs_le hε ?_
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
    change |signedDirichlet (r n)| ≤ |r n|
    by_cases hn : r n ∈ Set.range (Rat.cast : ℚ → ℝ) <;> simp [signedDirichlet, hn]

/-- Every limited hyperinteger `Z ∈ ℤ*` is standard (`Z = (m : ℤ*)` for some `m ∈ ℤ`). -/
theorem exists_int_of_isLimited_hyperint {Z : ℤ*} (hZ : IsLimited (Hyperint.toHyperreal Z)) :
    ∃ m : ℤ, Z = (m : ℤ*) := by
  rcases hZ with ⟨k, hk⟩
  induction Z using Germ.inductionOn with | _ a =>
  have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), |a i| ≤ (k : ℤ) := by
    have hk' : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), |(a i : ℝ)| < (k : ℝ) := ofSeq_lt_ofSeq.1 hk
    refine hk'.mono fun i hi ↦ ?_
    have : ((|a i| : ℤ) : ℝ) < ((k : ℤ) : ℝ) := by simpa using hi
    exact (Int.cast_lt.1 this).le
  let S : Set ℤ := Set.Icc (-(k : ℤ)) (k : ℤ)
  have hfin : S.Finite := Set.finite_Icc _ _
  have huniv : (⋃ m ∈ S, {i : ℕ | a i = m}) ∈ hyperfilter ℕ := by
    refine mem_of_superset hev fun i hi ↦ ?_
    exact Set.mem_biUnion (abs_le.1 hi) rfl
  obtain ⟨m, _, hm_ev⟩ := (Ultrafilter.finite_biUnion_mem_iff hfin).1 huniv
  exact ⟨m, Germ.coe_eq.2 hm_ev⟩

/-- Value of `thomaeFunction` at a rational `(q : ℝ)` is `(q.den : ℝ)⁻¹`. -/
theorem thomaeFunction_ratCast (q : ℚ) : thomaeFunction (q : ℝ) = (q.den : ℝ)⁻¹ := by
  have hmem : (q : ℝ) ∈ Set.range (Rat.cast : ℚ → ℝ) := ⟨q, rfl⟩
  simp only [thomaeFunction, hmem, ↓reduceDIte]
  have hq : hmem.choose = q := Rat.cast_injective hmem.choose_spec
  rw [hq]

/-- Goldblatt Exercise 7.4(3) `f₅` (p. 79): **Thomae's ruler function is continuous at `c` if and
only if `c` is irrational!**
Nonstandard proof: if `c` is irrational and `m/n ≈ₕ c` with `m ∈ ℤ*`, `n ∈ ℕ*`, then `n` cannot be
standard (else `m = (m/n) * n` would be a limited hyperinteger hence standard, making `c = m/n ∈ ℚ`),
so `n` is unlimited and `*f₅(m/n) = 1/n ≈ₕ 0 = f₅(c)`! -/
theorem continuousAt_thomaeFunction_iff {c : ℝ} :
    ContinuousAt thomaeFunction c ↔ Irrational c := by
  rw [continuousAt_iff_infClose]
  constructor
  · intro hc ⟨q, hqc⟩
    subst hqc
    obtain ⟨_, ⟨α, hα_nmem, hαc⟩⟩ := exists_hyperrat_and_hyperirrat_infClose (q : ℝ)
    have hα_val : starFun thomaeFunction α = 0 := by
      rcases ofSeq_surjective α with ⟨s, rfl⟩
      have hs : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), s n ∉ Set.range (Rat.cast : ℚ → ℝ) :=
        Ultrafilter.eventually_not.2 hα_nmem
      exact Germ.coe_eq.2 (hs.mono fun n hn ↦ by simp [thomaeFunction, hn])
    have hclose := hc α hαc
    rw [hα_val, thomaeFunction_ratCast q] at hclose
    have h0 : (0 : ℝ) = (q.den : ℝ)⁻¹ := coe_eq_of_infClose (by simpa using hclose)
    have hpos : (0 : ℝ) < (q.den : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 q.pos)
    linarith
  · intro hirr x hxc
    have hfc : thomaeFunction c = 0 := by
      have hc_nmem : c ∉ Set.range (Rat.cast : ℚ → ℝ) := hirr
      simp [thomaeFunction, hc_nmem]
    rw [hfc, Hyperreal.coe_zero, infClose_zero_iff]
    by_cases hx_rat : x ∈ starSet (Set.range (Rat.cast : ℚ → ℝ))
    · rw [← range_hyperrat_toHyperreal] at hx_rat
      rcases hx_rat with ⟨Q, rfl⟩
      induction Q using Germ.inductionOn with | _ u =>
      let N : ℕ* := ((fun i ↦ (u i).den) : ℕ*)
      let M : ℤ* := ((fun i ↦ (u i).num) : ℤ*)
      have hf_eq : starFun thomaeFunction (Hyperrat.toHyperreal (u : ℚ*)) =
          (Hypernat.toHyperreal N)⁻¹ := by
        refine Germ.coe_eq.2 (Eventually.of_forall fun i ↦ ?_)
        exact thomaeFunction_ratCast (u i)
      have hMN : Hyperint.toHyperreal M =
          Hyperrat.toHyperreal (u : ℚ*) * Hypernat.toHyperreal N := by
        refine Germ.coe_eq.2 (Eventually.of_forall fun i ↦ ?_)
        change ((u i).num : ℝ) = (u i : ℝ) * ((u i).den : ℝ)
        rw [Rat.cast_def, div_mul_cancel₀ _ (Nat.cast_ne_zero.2 (u i).den_nz)]
      have hN_unl : IsUnlimitedNat N := by
        by_contra hN_lim
        obtain ⟨d, hd_eq⟩ := not_isUnlimitedNat_iff_exists_nat.1 hN_lim
        have hd_pos : 0 < d := by
          have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), (u i).den = d := Germ.coe_eq.1 hd_eq
          obtain ⟨i, hi⟩ := hev.exists
          exact hi ▸ (u i).pos
        have hM_lim : IsLimited (Hyperint.toHyperreal M) := by
          rw [hMN, hd_eq, Hypernat.toHyperreal_natCast]
          exact (isLimited_of_infClose_coe hxc).mul (isLimited_coe d)
        obtain ⟨m, hm_eq⟩ := exists_int_of_isLimited_hyperint hM_lim
        have hQ_eq : Hyperrat.toHyperreal (u : ℚ*) = (((m : ℝ) / (d : ℝ) : ℝ) : ℝ*) := by
          have hd_ne : (d : ℝ*) ≠ 0 := by exact_mod_cast hd_pos.ne'
          have hMN' : (m : ℝ*) = Hyperrat.toHyperreal (u : ℚ*) * (d : ℝ*) := by
            have hM_coe : Hyperint.toHyperreal (m : ℤ*) = (m : ℝ*) := rfl
            rw [← hM_coe, ← hm_eq, hMN, hd_eq, Hypernat.toHyperreal_natCast]
          rw [Hyperreal.coe_div, coe_intCast_hyperreal, coe_natCast_hyperreal]
          exact eq_div_of_mul_eq hd_ne hMN'.symm
        rw [hQ_eq] at hxc
        have hc_rat : (m : ℝ) / (d : ℝ) = c := coe_eq_of_infClose hxc
        exact hirr ⟨(m : ℚ) / (d : ℚ), by push_cast; exact hc_rat⟩
      rw [hf_eq]
      exact (isUnlimited_iff_pos_or_neg.2
        (Or.inl (isUnlimitedNat_iff_isPosUnlimited.1 hN_unl))).inv_isInfinitesimal
    · rcases ofSeq_surjective x with ⟨r, rfl⟩
      have hr : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), r i ∉ Set.range (Rat.cast : ℚ → ℝ) :=
        Ultrafilter.eventually_not.2 hx_rat
      have hf0' : starFun thomaeFunction (ofSeq r) = 0 :=
        Germ.coe_eq.2 (hr.mono fun i hi ↦ by simp [thomaeFunction, hi])
      rw [hf0']
      exact isInfinitesimal_zero

/-! ## §7.5 The Intermediate Value Theorem (Hyperfinite Partition Proof) -/

/-- Uniform grid point `p_{n, k} = a + k * (b - a) / (n + 1)` dividing `[a, b]` into `n + 1`
equal subintervals (Goldblatt §7.5–7.6, pp. 79–80). -/
def ivtGridPoint (a b : ℝ) (n k : ℕ) : ℝ :=
  a + (k : ℝ) * (b - a) / ((n : ℝ) + 1)

/-- Initial grid point `p_{n, 0} = a`. -/
theorem ivtGridPoint_zero (a b : ℝ) (n : ℕ) : ivtGridPoint a b n 0 = a := by
  simp [ivtGridPoint]

/-- Final grid point `p_{n, n + 1} = b`. -/
theorem ivtGridPoint_last (a b : ℝ) (n : ℕ) : ivtGridPoint a b n (n + 1) = b := by
  have hd : ((n : ℝ) + 1) ≠ 0 := by positivity
  unfold ivtGridPoint
  push_cast
  field_simp [hd]
  ring

/-- Step size between adjacent grid points `p_{n, k + 1} - p_{n, k} = (b - a) / (n + 1)`. -/
theorem ivtGridPoint_succ (a b : ℝ) (n k : ℕ) :
    ivtGridPoint a b n (k + 1) = ivtGridPoint a b n k + (b - a) / ((n : ℝ) + 1) := by
  unfold ivtGridPoint
  push_cast
  ring

/-- Every grid point `p_{n, k}` with `0 ≤ k ≤ n + 1` belongs to `Set.Icc a b` when `a ≤ b`. -/
theorem ivtGridPoint_mem_Icc {a b : ℝ} (hab : a ≤ b) {n k : ℕ} (hk : k ≤ n + 1) :
    ivtGridPoint a b n k ∈ Set.Icc a b := by
  have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  have hkle : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hk
  constructor
  · unfold ivtGridPoint
    have : 0 ≤ (k : ℝ) * (b - a) / ((n : ℝ) + 1) := div_nonneg (mul_nonneg (Nat.cast_nonneg k) hba) hd.le
    linarith
  · unfold ivtGridPoint
    have hdiv : (k : ℝ) * (b - a) / ((n : ℝ) + 1) ≤ b - a := by
      rw [div_le_iff₀ hd]
      nlinarith
    linarith

/-- Goldblatt §7.5 (pp. 79–80): **Nonstandard Hyperfinite-Partition Proof of the Intermediate Value
Theorem** (`f a < d < f b` case).
Partitions `[a, b]` into `n + 1` subintervals, takes `s_n` to be the greatest grid point with
`f(p_{n,k}) < d`, and lets `c = shadow (ofSeq s_n)`. -/
theorem intermediate_value_lt_nonstandard {f : ℝ → ℝ} {a b d : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) (hfa : f a < d) (hfb : d < f b) :
    ∃ c ∈ Set.Ioo a b, f c = d := by
  let S : ℕ → Finset ℕ := fun n ↦
    (Finset.range (n + 2)).filter (fun k ↦ f (ivtGridPoint a b n k) < d)
  have hS_ne : ∀ n : ℕ, (S n).Nonempty := fun n ↦
    ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by rwa [ivtGridPoint_zero]⟩⟩
  let kSeq : ℕ → ℕ := fun n ↦ (S n).max' (hS_ne n)
  have hk_mem : ∀ n : ℕ, kSeq n ∈ S n := fun n ↦ Finset.max'_mem (S n) (hS_ne n)
  have hk_lt : ∀ n : ℕ, kSeq n < n + 1 := by
    intro n
    have hlt2 : kSeq n < n + 2 := Finset.mem_range.1 (Finset.mem_filter.1 (hk_mem n)).1
    have hne : kSeq n ≠ n + 1 := by
      intro heq
      have hfd : f (ivtGridPoint a b n (kSeq n)) < d := (Finset.mem_filter.1 (hk_mem n)).2
      rw [heq, ivtGridPoint_last] at hfd
      linarith
    omega
  have hk_succ_ge : ∀ n : ℕ, d ≤ f (ivtGridPoint a b n (kSeq n + 1)) := by
    intro n
    by_contra hlt
    push Not at hlt
    have hmem : kSeq n + 1 ∈ S n := Finset.mem_filter.2
      ⟨Finset.mem_range.2 (by have := hk_lt n; omega), hlt⟩
    have hle : kSeq n + 1 ≤ kSeq n := Finset.le_max' (S n) (kSeq n + 1) hmem
    omega
  let s : ℝ* := ofSeq (fun n ↦ ivtGridPoint a b n (kSeq n))
  let s' : ℝ* := ofSeq (fun n ↦ ivtGridPoint a b n (kSeq n + 1))
  have hs_mem : s ∈ starSet (Set.Icc a b) :=
    ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦
      ivtGridPoint_mem_Icc hab (hk_lt n).le)
  have hs'_mem : s' ∈ starSet (Set.Icc a b) :=
    ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦
      ivtGridPoint_mem_Icc hab (hk_lt n))
  have hs_le : (a : ℝ*) ≤ s ∧ s ≤ (b : ℝ*) := by
    simpa [starSet_Icc] using hs_mem
  have hs_lim : IsLimited s :=
    isLimited_iff_exists_real.2 ⟨a - 1, b + 1,
      (Hyperreal.coe_lt_coe.2 (by linarith)).trans_le hs_le.1,
      hs_le.2.trans_lt (Hyperreal.coe_lt_coe.2 (by linarith))⟩
  set c : ℝ := shadow s
  have hsc : s ≈ₕ (c : ℝ*) := infClose_shadow hs_lim
  have hc_mem : c ∈ Set.Icc a b :=
    ⟨coe_le_of_infClose_le (InfClose.refl _) hs_le.1 hsc,
     coe_le_of_infClose_le hsc.symm hs_le.2 (InfClose.refl _)⟩
  have hss' : s' ≈ₕ s := by
    have hdiff : s' - s = (b - a : ℝ*) * ofSeq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) :=
      Germ.coe_eq.2 (Eventually.of_forall fun n ↦ by
        change ivtGridPoint a b n (kSeq n + 1) - ivtGridPoint a b n (kSeq n) =
          (b - a) * ((n : ℝ) + 1)⁻¹
        rw [ivtGridPoint_succ]
        ring)
    unfold InfClose
    rw [hdiff]
    exact (isLimited_coe (b - a)).mul_isInfinitesimal isInfinitesimal_inv_nat_succ
  have hs'c : s' ≈ₕ (c : ℝ*) := hss'.trans hsc
  have hfs_close : starFun f s ≈ₕ (f c : ℝ*) :=
    (continuousOn_iff_infClose.1 hf) c hc_mem s hs_mem hsc
  have hfs'_close : starFun f s' ≈ₕ (f c : ℝ*) :=
    (continuousOn_iff_infClose.1 hf) c hc_mem s' hs'_mem hs'c
  have hfs_le_d : starFun f s ≤ (d : ℝ*) :=
    ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ((Finset.mem_filter.1 (hk_mem n)).2).le)
  have hd_le_fs' : (d : ℝ*) ≤ starFun f s' :=
    ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ hk_succ_ge n)
  have hfc_eq : f c = d := le_antisymm
    (coe_le_of_infClose_le hfs_close.symm hfs_le_d (InfClose.refl _))
    (coe_le_of_infClose_le (InfClose.refl _) hd_le_fs' hfs'_close)
  refine ⟨c, ⟨?_, ?_⟩, hfc_eq⟩
  · refine lt_of_le_of_ne hc_mem.1 ?_
    intro hca
    rw [← hca] at hfc_eq
    linarith
  · refine lt_of_le_of_ne hc_mem.2 ?_
    intro hcb
    rw [hcb] at hfc_eq
    linarith

/-- Goldblatt §7.5 (pp. 79–80): Full strict **Intermediate Value Theorem** (`d` strictly between
`f a` and `f b` in either order). -/
theorem intermediate_value_Ioo_nonstandard {f : ℝ → ℝ} {a b d : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (hd : (f a < d ∧ d < f b) ∨ (f b < d ∧ d < f a)) :
    ∃ c ∈ Set.Ioo a b, f c = d := by
  rcases hd with ⟨hfa, hfb⟩ | ⟨hfb, hfa⟩
  · exact intermediate_value_lt_nonstandard hab hf hfa hfb
  · have hneg : ContinuousOn (fun x ↦ -f x) (Set.Icc a b) :=
      fun x hx ↦ continuousWithinAt_neg_nonstandard (hf x hx)
    obtain ⟨c, hc, hfc⟩ := intermediate_value_lt_nonstandard hab hneg
      (neg_lt_neg hfa) (neg_lt_neg hfb)
    exact ⟨c, hc, by linarith⟩

/-- Closed-interval **Intermediate Value Theorem** (`d` between `f a` and `f b` inclusive). -/
theorem intermediate_value_Icc_nonstandard {f : ℝ → ℝ} {a b d : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (hd : d ∈ Set.Icc (min (f a) (f b)) (max (f a) (f b))) :
    ∃ c ∈ Set.Icc a b, f c = d := by
  rcases eq_or_ne d (f a) with rfl | hda
  · exact ⟨a, Set.left_mem_Icc.2 hab, rfl⟩
  · rcases eq_or_ne d (f b) with rfl | hdb
    · exact ⟨b, Set.right_mem_Icc.2 hab, rfl⟩
    · rcases le_total (f a) (f b) with hle | hle
      · rw [min_eq_left hle, max_eq_right hle] at hd
        obtain ⟨c, hc, hfc⟩ := intermediate_value_lt_nonstandard hab hf
          (lt_of_le_of_ne hd.1 hda.symm) (lt_of_le_of_ne hd.2 hdb)
        exact ⟨c, Set.Ioo_subset_Icc_self hc, hfc⟩
      · rw [min_eq_right hle, max_eq_left hle] at hd
        obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo_nonstandard hab hf
          (Or.inr ⟨lt_of_le_of_ne hd.1 hdb.symm, lt_of_le_of_ne hd.2 hda⟩)
        exact ⟨c, Set.Ioo_subset_Icc_self hc, hfc⟩

/-! ## §7.6 The Extreme Value Theorem (Hyperfinite Grid Proof) -/

/-- Goldblatt §7.6 (pp. 80–81): **Nonstandard Hyperfinite-Grid Proof of the Maximum Value Theorem**.
For each `n`, picks a grid point `s_n` maximizing `f` on `{a + k(b - a)/(n + 1) | 0 ≤ k ≤ n + 1}`,
lets `d = shadow (ofSeq s_n) ∈ [a, b]`, and approximates any `x ∈ [a, b]` by infinitely close
grid points! -/
theorem exists_max_on_Icc_nonstandard {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ d ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f d := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · refine ⟨a, Set.left_mem_Icc.2 le_rfl, fun x hx ↦ ?_⟩
    rw [Set.Icc_self, Set.mem_singleton_iff] at hx
    rw [hx]
  · have hmax_grid : ∀ n : ℕ, ∃ k ∈ Finset.range (n + 2),
        ∀ j ∈ Finset.range (n + 2), f (ivtGridPoint a b n j) ≤ f (ivtGridPoint a b n k) :=
      fun n ↦ Finset.exists_max_image (Finset.range (n + 2))
        (fun k ↦ f (ivtGridPoint a b n k)) ⟨0, Finset.mem_range.2 (by omega)⟩
    choose kSeq hk_mem hk_max using hmax_grid
    let s : ℝ* := ofSeq (fun n ↦ ivtGridPoint a b n (kSeq n))
    have hs_mem : s ∈ starSet (Set.Icc a b) :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦
        ivtGridPoint_mem_Icc hab (Nat.lt_succ_iff.1 (Finset.mem_range.1 (hk_mem n))))
    have hs_le : (a : ℝ*) ≤ s ∧ s ≤ (b : ℝ*) := by simpa [starSet_Icc] using hs_mem
    have hs_lim : IsLimited s :=
      isLimited_iff_exists_real.2 ⟨a - 1, b + 1,
        (Hyperreal.coe_lt_coe.2 (by linarith)).trans_le hs_le.1,
        hs_le.2.trans_lt (Hyperreal.coe_lt_coe.2 (by linarith))⟩
    set d : ℝ := shadow s
    have hsd : s ≈ₕ (d : ℝ*) := infClose_shadow hs_lim
    have hd_mem : d ∈ Set.Icc a b :=
      ⟨coe_le_of_infClose_le (InfClose.refl _) hs_le.1 hsd,
       coe_le_of_infClose_le hsd.symm hs_le.2 (InfClose.refl _)⟩
    -- Equation (iii) in Goldblatt p. 80: `*f(s_N) ≈ₕ f(d)`
    have hfs_d : starFun f s ≈ₕ (f d : ℝ*) :=
      (continuousOn_iff_infClose.1 hf) d hd_mem s hs_mem hsd
    refine ⟨d, hd_mem, fun x hx ↦ ?_⟩
    have hba_pos : 0 < b - a := sub_pos.2 hlt
    set t : ℝ := (x - a) / (b - a)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.2 hx.1) hba_pos.le
    have ht1 : t ≤ 1 := (div_le_one hba_pos).2 (sub_le_sub_right hx.2 a)
    let jSeq : ℕ → ℕ := fun n ↦ ⌊t * ((n : ℝ) + 1)⌋₊
    have hj_le : ∀ n : ℕ, jSeq n ≤ n + 1 := by
      intro n
      have hnn : 0 ≤ t * ((n : ℝ) + 1) := mul_nonneg ht0 (by positivity)
      have hfl : (jSeq n : ℝ) ≤ t * ((n : ℝ) + 1) := Nat.floor_le hnn
      have hub : t * ((n : ℝ) + 1) ≤ ((n + 1 : ℕ) : ℝ) := by
        push_cast
        nlinarith
      exact Nat.cast_le.1 (hfl.trans hub)
    let y : ℝ* := ofSeq (fun n ↦ ivtGridPoint a b n (jSeq n))
    have hy_mem : y ∈ starSet (Set.Icc a b) :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ ivtGridPoint_mem_Icc hab (hj_le n))
    have hyx : y ≈ₕ (x : ℝ*) := by
      refine isInfinitesimal_of_abs_le
        ((isLimited_coe (b - a)).mul_isInfinitesimal isInfinitesimal_inv_nat_succ) ?_
      have hpos : 0 ≤ ((b - a : ℝ) : ℝ*) * ofSeq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) :=
        mul_nonneg (Hyperreal.coe_nonneg.2 hba_pos.le)
          (ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ by positivity))
      rw [abs_of_nonneg hpos]
      refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
      change |ivtGridPoint a b n (jSeq n) - x| ≤ (b - a) * ((n : ℝ) + 1)⁻¹
      have hd_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hnn : 0 ≤ t * ((n : ℝ) + 1) := mul_nonneg ht0 hd_pos.le
      have hfl_le : (jSeq n : ℝ) ≤ t * ((n : ℝ) + 1) := Nat.floor_le hnn
      have hfl_gt : t * ((n : ℝ) + 1) < (jSeq n : ℝ) + 1 := Nat.lt_floor_add_one _
      have hx_eq : x = a + t * ((n : ℝ) + 1) * (b - a) / ((n : ℝ) + 1) := by
        simp only [t]
        field_simp [hba_pos.ne', hd_pos.ne']
        ring
      have hdiff_nn : 0 ≤ x - ivtGridPoint a b n (jSeq n) := by
        rw [hx_eq, ivtGridPoint]
        have : a + t * ((n : ℝ) + 1) * (b - a) / ((n : ℝ) + 1) -
            (a + (jSeq n : ℝ) * (b - a) / ((n : ℝ) + 1)) =
            (t * ((n : ℝ) + 1) - (jSeq n : ℝ)) * ((b - a) / ((n : ℝ) + 1)) := by ring
        rw [this]
        exact mul_nonneg (sub_nonneg.2 hfl_le) (div_nonneg hba_pos.le hd_pos.le)
      have hdiff_le : x - ivtGridPoint a b n (jSeq n) ≤ (b - a) * ((n : ℝ) + 1)⁻¹ := by
        rw [hx_eq, ivtGridPoint]
        have : a + t * ((n : ℝ) + 1) * (b - a) / ((n : ℝ) + 1) -
            (a + (jSeq n : ℝ) * (b - a) / ((n : ℝ) + 1)) =
            (t * ((n : ℝ) + 1) - (jSeq n : ℝ)) * ((b - a) * ((n : ℝ) + 1)⁻¹) := by
          rw [← div_eq_mul_inv]
          ring
        rw [this]
        exact mul_le_of_le_one_left (mul_nonneg hba_pos.le (by positivity)) (by linarith)
      rw [abs_sub_comm, abs_of_nonneg hdiff_nn]
      exact hdiff_le
    -- Equation (iv) in Goldblatt p. 81: `f(x) ≈ₕ *f(y)`
    have hfy_x : (f x : ℝ*) ≈ₕ starFun f y :=
      ((continuousOn_iff_infClose.1 hf) x hx y hy_mem hyx).symm
    -- Equation (v) in Goldblatt p. 81: `*f(y) ≤ *f(s)`
    have hfy_le_fs : starFun f y ≤ starFun f s :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦
        hk_max n (jSeq n) (Finset.mem_range.2 (Nat.lt_succ_of_le (hj_le n))))
    exact coe_le_of_infClose_le hfy_x hfy_le_fs hfs_d

/-- Goldblatt §7.6 (p. 81): **Minimum Value Theorem** on `[a, b]` via `exists_max_on_Icc_nonstandard`
applied to `-f`. -/
theorem exists_min_on_Icc_nonstandard {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ c ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f c ≤ f x := by
  have hneg : ContinuousOn (fun x ↦ -f x) (Set.Icc a b) :=
    fun x hx ↦ continuousWithinAt_neg_nonstandard (hf x hx)
  obtain ⟨c, hc, hmax⟩ := exists_max_on_Icc_nonstandard hab hneg
  exact ⟨c, hc, fun x hx ↦ neg_le_neg_iff.1 (hmax x hx)⟩

/-- Goldblatt §7.6 (p. 80): Full **Extreme Value Theorem** on `[a, b]`: `f` attains both an
absolute minimum `f c` and an absolute maximum `f d` on `[a, b]`. -/
theorem extreme_value_Icc_nonstandard {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ c ∈ Set.Icc a b, ∃ d ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f c ≤ f x ∧ f x ≤ f d := by
  obtain ⟨c, hc, hmin⟩ := exists_min_on_Icc_nonstandard hab hf
  obtain ⟨d, hd, hmax⟩ := exists_max_on_Icc_nonstandard hab hf
  exact ⟨c, hc, d, hd, fun x hx ↦ ⟨hmin x hx, hmax x hx⟩⟩

/-- Every continuous function on `[a, b]` is bounded (`∃ M, ∀ x ∈ [a, b], |f x| ≤ M`), deduced
from the nonstandard Extreme Value Theorem. -/
theorem bounded_on_Icc_of_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M := by
  rcases le_or_gt a b with hab | hgt
  · obtain ⟨c, _, d, _, hcd⟩ := extreme_value_Icc_nonstandard hab hf
    refine ⟨max |f c| |f d|, fun x hx ↦ ?_⟩
    obtain ⟨hc, hd⟩ := hcd x hx
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have : -max |f c| |f d| ≤ -|f c| := neg_le_neg (le_max_left _ _)
      exact this.trans ((neg_abs_le (f c)).trans hc)
    · exact hd.trans ((le_abs_self (f d)).trans (le_max_right _ _))
  · refine ⟨0, fun x hx ↦ ?_⟩
    exfalso
    linarith [hx.1, hx.2]

/-! ## §7.7–7.8 Uniform Continuity, Heine–Cantor, and Exercises on Uniform Continuity -/

/-- Goldblatt §7.7 (p. 81): Standard `ε`-`δ` uniform continuity of `f : ℝ → ℝ` on `A ⊆ ℝ`. -/
def EpsDeltaUniformContinuousOn (f : ℝ → ℝ) (A : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ A, ∀ y ∈ A, |x - y| < δ → |f x - f y| < ε

/-- Equivalence of `UniformContinuousOn` and `EpsDeltaUniformContinuousOn` on `ℝ`. -/
theorem uniformContinuousOn_iff_epsDelta {f : ℝ → ℝ} {A : Set ℝ} :
    UniformContinuousOn f A ↔ EpsDeltaUniformContinuousOn f A := by
  simp only [Metric.uniformContinuousOn_iff, EpsDeltaUniformContinuousOn, Real.dist_eq]

/-- Goldblatt §7.7, Theorem 7.7.1 (p. 81):
`f` is uniformly continuous on `A ⊆ ℝ` if and only if `x ≈ₕ y` implies `*f(x) ≈ₕ *f(y)` for ALL
hyperreal points `x, y ∈ *A`. -/
theorem uniformContinuousOn_iff_infClose {f : ℝ → ℝ} {A : Set ℝ} :
    UniformContinuousOn f A ↔
      ∀ x ∈ starSet A, ∀ y ∈ starSet A, x ≈ₕ y → starFun f x ≈ₕ starFun f y := by
  rw [uniformContinuousOn_iff_epsDelta]
  constructor
  · intro hf x hx y hy hxy ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := hf ε hε
    have hlt_δ : |x - y| < (δ : ℝ*) := hxy δ hδ_pos
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    rcases ofSeq_surjective y with ⟨s, rfl⟩
    have hrs_lt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |r n - s n| < δ := ofSeq_lt_ofSeq.1 hlt_δ
    exact ofSeq_lt_ofSeq.2 (((hx.and hy).and hrs_lt).mono fun n ⟨⟨hnx, hny⟩, hnd⟩ ↦
      hδ (r n) hnx (s n) hny hnd)
  · intro h ε hε
    by_contra hnot
    push Not at hnot
    have hex : ∀ n : ℕ, ∃ u : ℝ × ℝ, u.1 ∈ A ∧ u.2 ∈ A ∧
        |u.1 - u.2| < ((n : ℝ) + 1)⁻¹ ∧ ε ≤ |f u.1 - f u.2| := by
      intro n
      obtain ⟨x, hx, y, hy, hlt, hge⟩ := hnot ((n : ℝ) + 1)⁻¹ (by positivity)
      exact ⟨(x, y), hx, hy, hlt, hge⟩
    choose u hu using hex
    let r : ℕ → ℝ := fun n ↦ (u n).1
    let s : ℕ → ℝ := fun n ↦ (u n).2
    have hrA : ofSeq r ∈ starSet A :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (hu n).1)
    have hsA : ofSeq s ∈ starSet A :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ (hu n).2.1)
    have hrs : ofSeq r ≈ₕ ofSeq s := by
      refine isInfinitesimal_of_abs_le isInfinitesimal_inv_nat_succ ?_
      have hpos : 0 ≤ ofSeq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) :=
        ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ by positivity)
      rw [abs_of_nonneg hpos]
      exact ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (hu n).2.2.1.le)
    have hge : (ε : ℝ*) ≤ |starFun f (ofSeq r) - starFun f (ofSeq s)| :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ (hu n).2.2.2)
    exact not_lt_of_ge hge (h (ofSeq r) hrA (ofSeq s) hsA hrs ε hε)

/-- Explicit `ε`-`δ` form of Goldblatt Theorem 7.7.1 (p. 81). -/
theorem epsDeltaUniformContinuousOn_iff_infClose {f : ℝ → ℝ} {A : Set ℝ} :
    EpsDeltaUniformContinuousOn f A ↔
      ∀ x ∈ starSet A, ∀ y ∈ starSet A, x ≈ₕ y → starFun f x ≈ₕ starFun f y := by
  rw [← uniformContinuousOn_iff_epsDelta, uniformContinuousOn_iff_infClose]

/-- Global form of Goldblatt Theorem 7.7.1 (p. 81):
`UniformContinuous f ↔ ∀ x y : ℝ*, x ≈ₕ y → *f(x) ≈ₕ *f(y)`. -/
theorem uniformContinuous_iff_infClose {f : ℝ → ℝ} :
    UniformContinuous f ↔ ∀ x y : ℝ*, x ≈ₕ y → starFun f x ≈ₕ starFun f y := by
  rw [← uniformContinuousOn_univ, uniformContinuousOn_iff_infClose]
  simp [starSet_univ]

/-- Goldblatt §7.7, Theorem 7.7.2 — **Heine–Cantor Theorem** (pp. 81–82):
Every function continuous on a closed bounded interval `[a, b]` in `ℝ` is uniformly continuous on
`[a, b]`, proved in 8 lines by taking the common shadow `c = shadow x ∈ [a, b]`! -/
theorem uniformContinuousOn_Icc_of_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    UniformContinuousOn f (Set.Icc a b) := by
  rw [uniformContinuousOn_iff_infClose]
  intro x hx y hy hxy
  have hx_le : (a : ℝ*) ≤ x ∧ x ≤ (b : ℝ*) := by simpa [starSet_Icc] using hx
  have hx_lim : IsLimited x :=
    isLimited_iff_exists_real.2 ⟨a - 1, b + 1,
      (Hyperreal.coe_lt_coe.2 (by linarith)).trans_le hx_le.1,
      hx_le.2.trans_lt (Hyperreal.coe_lt_coe.2 (by linarith))⟩
  set c : ℝ := shadow x
  have hxc : x ≈ₕ (c : ℝ*) := infClose_shadow hx_lim
  have hc_mem : c ∈ Set.Icc a b :=
    ⟨coe_le_of_infClose_le (InfClose.refl _) hx_le.1 hxc,
     coe_le_of_infClose_le hxc.symm hx_le.2 (InfClose.refl _)⟩
  have hyc : y ≈ₕ (c : ℝ*) := hxy.symm.trans hxc
  have hfx := (continuousOn_iff_infClose.1 hf) c hc_mem x hx hxc
  have hfy := (continuousOn_iff_infClose.1 hf) c hc_mem y hy hyc
  exact hfx.trans hfy.symm

/-! ### §7.8 Exercises on Uniform Continuity (p. 82) -/

/-- Enlargement of `Set.Ioc a b` is `Set.Ioc (a : ℝ*) (b : ℝ*)`. -/
@[simp]
theorem starSet_Ioc (a b : ℝ) : starSet (Set.Ioc a b) = Set.Ioc (a : ℝ*) (b : ℝ*) := by
  ext x
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  simp only [ofSeq_mem_starSet, Set.mem_Ioc, eventually_and]
  exact ⟨fun ⟨ha, hb⟩ ↦ ⟨ofSeq_lt_ofSeq.2 ha, ofSeq_le_ofSeq.2 hb⟩,
         fun ⟨ha, hb⟩ ↦ ⟨ofSeq_lt_ofSeq.1 ha, ofSeq_le_ofSeq.1 hb⟩⟩

/-- Goldblatt Exercise 7.8(1a) (p. 82): Why the shadow proof of Theorem 7.7.2 fails on open
intervals `(a, b)` (`a < b`): `*(a, b)` contains elements whose shadow `a` escapes `(a, b)`. -/
theorem exists_mem_starSet_Ioo_shadow_notMem {a b : ℝ} (hab : a < b) :
    ∃ x ∈ starSet (Set.Ioo a b), shadow x ∉ Set.Ioo a b := by
  let d : ℝ* := ((b - a) / 2 : ℝ*) * ofSeq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹)
  have hd_pos : 0 < d := by
    refine mul_pos ?_ isPosInfinitesimal_inv_nat_succ.1
    have : (0 : ℝ) < (b - a) / 2 := by linarith
    exact_mod_cast this
  have hd_inf : IsInfinitesimal d := by
    have : (((b - a) / 2 : ℝ) : ℝ*) = ((b - a) / 2 : ℝ*) := by push_cast; rfl
    rw [show d = (((b - a) / 2 : ℝ) : ℝ*) * ofSeq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) by
      simp [d, this]]
    exact (isLimited_coe ((b - a) / 2)).mul_isInfinitesimal isInfinitesimal_inv_nat_succ
  refine ⟨(a : ℝ*) + d, ?_, ?_⟩
  · rw [starSet_Ioo]
    refine ⟨by linarith, ?_⟩
    have hlt_ba : d < ((b - a : ℝ) : ℝ*) := by
      have h1 := hd_inf (b - a) (sub_pos.2 hab)
      rwa [abs_of_pos hd_pos] at h1
    have hba : (a : ℝ*) + ((b - a : ℝ) : ℝ*) = (b : ℝ*) := by
      rw [← Hyperreal.coe_add]
      congr 1
      ring
    linarith
  · have hxa : ((a : ℝ*) + d) ≈ₕ (a : ℝ*) := by
      unfold InfClose
      simpa using hd_inf
    rw [shadow_eq_of_infClose hxa]
    intro hmem
    exact lt_irrefl a hmem.1

/-- Goldblatt Exercise 7.8(1b) (p. 82): On half-open `(a, b]` (`a < b`), `*(a, b]` also contains
elements whose shadow `a` escapes `(a, b]`. -/
theorem exists_mem_starSet_Ioc_shadow_notMem {a b : ℝ} (hab : a < b) :
    ∃ x ∈ starSet (Set.Ioc a b), shadow x ∉ Set.Ioc a b := by
  let d : ℝ* := ((b - a) / 2 : ℝ*) * ofSeq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹)
  have hd_pos : 0 < d := by
    refine mul_pos ?_ isPosInfinitesimal_inv_nat_succ.1
    have : (0 : ℝ) < (b - a) / 2 := by linarith
    exact_mod_cast this
  have hd_inf : IsInfinitesimal d := by
    have : (((b - a) / 2 : ℝ) : ℝ*) = ((b - a) / 2 : ℝ*) := by push_cast; rfl
    rw [show d = (((b - a) / 2 : ℝ) : ℝ*) * ofSeq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) by
      simp [d, this]]
    exact (isLimited_coe ((b - a) / 2)).mul_isInfinitesimal isInfinitesimal_inv_nat_succ
  refine ⟨(a : ℝ*) + d, ?_, ?_⟩
  · rw [starSet_Ioc]
    refine ⟨by linarith, ?_⟩
    have hlt_ba : d < ((b - a : ℝ) : ℝ*) := by
      have h1 := hd_inf (b - a) (sub_pos.2 hab)
      rwa [abs_of_pos hd_pos] at h1
    have hba : (a : ℝ*) + ((b - a : ℝ) : ℝ*) = (b : ℝ*) := by
      rw [← Hyperreal.coe_add]
      congr 1
      ring
    linarith
  · have hxa : ((a : ℝ*) + d) ≈ₕ (a : ℝ*) := by
      unfold InfClose
      simpa using hd_inf
    rw [shadow_eq_of_infClose hxa]
    intro hmem
    exact lt_irrefl a hmem.1

/-- Goldblatt Exercise 7.8(1c) (p. 82): On unbounded `(a, +∞)` and `(-∞, b)`, `*(a, +∞)` and
`*(-∞, b)` contain unlimited hyperreals that have no real shadow at all. -/
theorem exists_mem_starSet_unbounded_not_isLimited (a b : ℝ) :
    (∃ x ∈ starSet (Set.Ioi a), ¬ IsLimited x) ∧
    (∃ y ∈ starSet (Set.Iio b), ¬ IsLimited y) := by
  refine ⟨⟨(a : ℝ*) + Hyperreal.omega, ?_, ?_⟩, ⟨(b : ℝ*) - Hyperreal.omega, ?_, ?_⟩⟩
  · rw [starSet_Ioi, Set.mem_Ioi]
    have hpos : (0 : ℝ*) < Hyperreal.omega := by simpa using Hyperreal.coe_lt_omega 0
    linarith
  · rw [← isUnlimited_iff_not_isLimited, add_comm]
    exact isUnlimited_omega.add_isLimited (isLimited_coe a)
  · rw [starSet_Iio, Set.mem_Iio]
    have hpos : (0 : ℝ*) < Hyperreal.omega := by simpa using Hyperreal.coe_lt_omega 0
    linarith
  · rw [← isUnlimited_iff_not_isLimited, sub_eq_add_neg, add_comm]
    exact isUnlimited_omega.neg.add_isLimited (isLimited_coe b)

/-- Squaring `x ↦ x ^ 2` is continuous on `ℝ` yet NOT uniformly continuous on `ℝ`:
for `ω = Hyperreal.omega` and `e = Hyperreal.epsilon`, `ω + e ≈ₕ ω`, yet
`(ω + e)^2 - ω^2 = 2 + e^2 ≈ₕ 2 ≠ 0`! -/
theorem continuous_sq_and_not_uniformContinuous :
    Continuous (fun x : ℝ ↦ x ^ 2) ∧ ¬ UniformContinuous (fun x : ℝ ↦ x ^ 2) := by
  refine ⟨continuous_pow 2, ?_⟩
  rw [uniformContinuous_iff_infClose]
  intro h
  set ω : ℝ* := Hyperreal.omega
  set e : ℝ* := Hyperreal.epsilon
  have hclose : (ω + e) ≈ₕ ω := by
    unfold InfClose
    simpa using isInfinitesimal_epsilon
  have hsq := h (ω + e) ω hclose
  rw [starFun_pow, starFun_pow, starFun_id_apply, starFun_id_apply] at hsq
  have hdiff : (ω + e) ^ 2 - ω ^ 2 = (2 : ℝ*) + e ^ 2 := by
    have heω : e * ω = 1 := Hyperreal.epsilon_mul_omega
    calc (ω + e) ^ 2 - ω ^ 2
        = 2 * (e * ω) + e ^ 2 := by ring
      _ = (2 : ℝ*) + e ^ 2 := by rw [heω]; ring
  have he2 : IsInfinitesimal (e ^ 2) := by
    rw [sq]
    exact isInfinitesimal_epsilon.mul isInfinitesimal_epsilon
  have h2_inf : IsInfinitesimal (2 : ℝ*) := by
    have hsum : IsInfinitesimal ((2 : ℝ*) + e ^ 2) := by
      unfold InfClose at hsq
      rwa [hdiff] at hsq
    have : (2 : ℝ*) = ((2 : ℝ*) + e ^ 2) - e ^ 2 := by ring
    rw [this]
    exact hsum.sub he2
  have h20 : (2 : ℝ) = 0 := isInfinitesimal_coe_iff.1 (by simpa using h2_inf)
  norm_num at h20

/-- Goldblatt Exercise 7.8(2) (p. 82): `f(x) = 1 / x` is continuous on `(0, 1)`, yet NOT uniformly
continuous on `(0, 1)`: for `e = Hyperreal.epsilon`, `e / 2, e ∈ *(0, 1)` with `e / 2 ≈ₕ e`,
yet `1 / (e / 2) - 1 / e = ω` is unlimited! -/
theorem not_uniformContinuousOn_inv_Ioo :
    ContinuousOn (fun x : ℝ ↦ 1 / x) (Set.Ioo 0 1) ∧
    ¬ UniformContinuousOn (fun x : ℝ ↦ 1 / x) (Set.Ioo 0 1) := by
  refine ⟨?_, ?_⟩
  · intro c hc
    exact continuousWithinAt_div_nonstandard continuousWithinAt_const continuousWithinAt_id hc.1.ne'
  · rw [uniformContinuousOn_iff_infClose]
    intro h
    set e : ℝ* := Hyperreal.epsilon
    have he_pos : 0 < e := Hyperreal.epsilon_pos
    have he_lt1 : e < 1 := by simpa using Hyperreal.epsilon_lt_of_pos one_pos
    have hx_mem : e / 2 ∈ starSet (Set.Ioo 0 1) := by
      rw [starSet_Ioo]
      exact ⟨half_pos he_pos, (half_lt_self he_pos).trans he_lt1⟩
    have hy_mem : e ∈ starSet (Set.Ioo 0 1) := by
      rw [starSet_Ioo]
      exact ⟨he_pos, he_lt1⟩
    have hxy : (e / 2) ≈ₕ e := by
      unfold InfClose
      have : e / 2 - e = -((1 / 2 : ℝ) : ℝ*) * e := by push_cast; ring
      rw [this]
      exact (isLimited_coe (1 / 2)).neg.mul_isInfinitesimal isInfinitesimal_epsilon
    have hinv := h (e / 2) hx_mem e hy_mem hxy
    rw [starFun_div, starFun_div, starFun_const, starFun_const, starFun_id_apply, starFun_id_apply] at hinv
    have hdiff : ((1 : ℝ) : ℝ*) / (e / 2) - ((1 : ℝ) : ℝ*) / e = Hyperreal.omega := by
      have heω : e * Hyperreal.omega = 1 := Hyperreal.epsilon_mul_omega
      have he_ne : e ≠ 0 := he_pos.ne'
      push_cast
      field_simp [he_ne]
      linarith
    unfold InfClose at hinv
    rw [hdiff] at hinv
    exact (isUnlimited_iff_not_isLimited.1 isUnlimited_omega) hinv.isLimited

/-- Nonstandard characterization of real Cauchy sequences (`IsRealCauchy`):
`s : ℕ → ℝ` is Cauchy iff `starSeq s M ≈ₕ starSeq s N` for all unlimited `M, N ∈ ℕ*`. -/
theorem isRealCauchy_iff_starSeq_infClose {s : ℕ → ℝ} :
    IsRealCauchy s ↔ ∀ M N : ℕ*, IsUnlimitedNat M → IsUnlimitedNat N → starSeq s M ≈ₕ starSeq s N := by
  constructor
  · intro hs M N hM hN r hr
    obtain ⟨k, hk⟩ := hs r hr
    induction M using Germ.inductionOn with | _ a =>
    induction N using Germ.inductionOn with | _ b =>
    have ha : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), k < a i := Germ.coe_lt.1 (hM k)
    have hb : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), k < b i := Germ.coe_lt.1 (hN k)
    exact ofSeq_lt_ofSeq.2 ((ha.and hb).mono fun i ⟨hia, hib⟩ ↦ hk (a i) (b i) hia.le hib.le)
  · intro h ε hε
    by_contra hnot
    push Not at hnot
    have hex : ∀ k : ℕ, ∃ p : ℕ × ℕ, k + 1 ≤ p.1 ∧ k + 1 ≤ p.2 ∧ ε ≤ |s p.1 - s p.2| := by
      intro k
      obtain ⟨m, n, hm, hn, hge⟩ := hnot (k + 1)
      exact ⟨(m, n), hm, hn, hge⟩
    choose p hp using hex
    let M : ℕ* := ((fun k ↦ (p k).1) : ℕ*)
    let N : ℕ* := ((fun k ↦ (p k).2) : ℕ*)
    have hM_unl : IsUnlimitedNat M := by
      intro j
      have hat : ∀ᶠ k in atTop, j < (p k).1 :=
        eventually_atTop.2 ⟨j, fun k hk ↦ Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hk) (hp k).1⟩
      exact Germ.coe_lt.2 (hat.filter_mono Nat.hyperfilter_le_atTop)
    have hN_unl : IsUnlimitedNat N := by
      intro j
      have hat : ∀ᶠ k in atTop, j < (p k).2 :=
        eventually_atTop.2 ⟨j, fun k hk ↦ Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hk) (hp k).2.1⟩
      exact Germ.coe_lt.2 (hat.filter_mono Nat.hyperfilter_le_atTop)
    have hge : (ε : ℝ*) ≤ |starSeq s M - starSeq s N| :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun k ↦ (hp k).2.2)
    exact not_lt_of_ge hge (h M N hM_unl hN_unl ε hε)

/-- Composition of `starFun f` with `starSeq s` agrees with `starSeq (f ∘ s)`. -/
@[simp]
theorem starFun_starSeq (f : ℝ → ℝ) (s : ℕ → ℝ) (N : ℕ*) :
    starFun f (starSeq s N) = starSeq (fun n ↦ f (s n)) N :=
  Germ.inductionOn N fun _ ↦ rfl

/-- Goldblatt Exercise 7.8(3) (p. 82): If `f` is uniformly continuous on `A` and `(s_n)` is a
Cauchy sequence in `A`, then `(f(s_n))` is a Cauchy sequence (4-line nonstandard proof!). -/
theorem isRealCauchy_comp_of_uniformContinuousOn {f : ℝ → ℝ} {A : Set ℝ} {s : ℕ → ℝ}
    (hf : UniformContinuousOn f A) (hsA : ∀ n : ℕ, s n ∈ A) (hs : IsRealCauchy s) :
    IsRealCauchy (fun n ↦ f (s n)) := by
  rw [isRealCauchy_iff_starSeq_infClose] at hs ⊢
  rw [uniformContinuousOn_iff_infClose] at hf
  intro M N hM hN
  have hMA : starSeq s M ∈ starSet A := by
    induction M using Germ.inductionOn with | _ a =>
    exact ofSeq_mem_starSet.2 (Eventually.of_forall fun k ↦ hsA (a k))
  have hNA : starSeq s N ∈ starSet A := by
    induction N using Germ.inductionOn with | _ b =>
    exact ofSeq_mem_starSet.2 (Eventually.of_forall fun k ↦ hsA (b k))
  rw [← starFun_starSeq, ← starFun_starSeq]
  exact hf (starSeq s M) hMA (starSeq s N) hNA (hs M N hM hN)

/-- Global form of Goldblatt Exercise 7.8(3) (p. 82): If `f : ℝ → ℝ` is uniformly continuous and
`(s_n)` is Cauchy, then `(f(s_n))` is Cauchy. -/
theorem isRealCauchy_comp_of_uniformContinuous {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hf : UniformContinuous f) (hs : IsRealCauchy s) :
    IsRealCauchy (fun n ↦ f (s n)) :=
  isRealCauchy_comp_of_uniformContinuousOn (uniformContinuousOn_univ.2 hf)
    (fun _ ↦ Set.mem_univ _) hs

/-- Goldblatt Exercise 7.8(4) (p. 82): If `f : ℝ → ℝ` is monotone nondecreasing on `[a, b]` and
attains every intermediate value between `f a` and `f b` on `[a, b]`, then `f` is continuous on
`[a, b]` (nonstandard proof via transferred monotonicity). -/
theorem continuousOn_Icc_of_monotoneOn_ivp {f : ℝ → ℝ} {a b : ℝ}
    (hmono : MonotoneOn f (Set.Icc a b))
    (hivp : ∀ r ∈ Set.Icc (f a) (f b), ∃ d ∈ Set.Icc a b, f d = r) :
    ContinuousOn f (Set.Icc a b) := by
  -- Transferred monotonicity on `starSet (Set.Icc a b)`
  have hstar_mono : ∀ u ∈ starSet (Set.Icc a b), ∀ v ∈ starSet (Set.Icc a b),
      u ≤ v → starFun f u ≤ starFun f v := by
    intro u hu v hv huv
    rcases ofSeq_surjective u with ⟨r, rfl⟩
    rcases ofSeq_surjective v with ⟨s, rfl⟩
    have hrs : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ≤ s n := ofSeq_le_ofSeq.1 huv
    exact ofSeq_le_ofSeq.2 (((hu.and hv).and hrs).mono fun n ⟨⟨hnr, hns⟩, hnle⟩ ↦
      hmono hnr hns hnle)
  rw [continuousOn_iff_infClose]
  intro c hc x hx hxc ε hε
  have hab : a ≤ b := hc.1.trans hc.2
  have ha_star : (a : ℝ*) ∈ starSet (Set.Icc a b) := coe_mem_starSet.2 (Set.left_mem_Icc.2 hab)
  have hb_star : (b : ℝ*) ∈ starSet (Set.Icc a b) := coe_mem_starSet.2 (Set.right_mem_Icc.2 hab)
  have hx_bounds : (a : ℝ*) ≤ x ∧ x ≤ (b : ℝ*) := by simpa [starSet_Icc] using hx
  rw [abs_lt]
  refine ⟨?_, ?_⟩
  · -- Lower bound: `-(ε : ℝ*) < starFun f x - (f c : ℝ*)`
    by_cases hlow : f c - ε / 2 < f a
    · have hfx_ge : (f a : ℝ*) ≤ starFun f x := by
        simpa using hstar_mono (a : ℝ*) ha_star x hx hx_bounds.1
      have hfa_gt : ((f c - ε / 2 : ℝ) : ℝ*) < (f a : ℝ*) := Hyperreal.coe_lt_coe.2 hlow
      have heps : ((f c - ε : ℝ) : ℝ*) < ((f c - ε / 2 : ℝ) : ℝ*) :=
        Hyperreal.coe_lt_coe.2 (by linarith)
      have h1 : (f c : ℝ*) - (ε : ℝ*) < starFun f x := by
        calc (f c : ℝ*) - (ε : ℝ*)
            = ((f c - ε : ℝ) : ℝ*) := by push_cast; ring
          _ < (f a : ℝ*) := heps.trans hfa_gt
          _ ≤ starFun f x := hfx_ge
      linarith
    · push Not at hlow
      have hmem_r : f c - ε / 2 ∈ Set.Icc (f a) (f b) :=
        ⟨hlow, (by linarith : f c - ε / 2 ≤ f c).trans (hmono hc (Set.right_mem_Icc.2 hab) hc.2)⟩
      obtain ⟨d₁, hd₁_mem, hfd₁⟩ := hivp (f c - ε / 2) hmem_r
      have hd₁_lt_c : d₁ < c := by
        by_contra hge
        push Not at hge
        have hle := hmono hc hd₁_mem hge
        linarith
      have hd₁_lt_x : (d₁ : ℝ*) < x := by
        have hclose := hxc (c - d₁) (sub_pos.2 hd₁_lt_c)
        have h1 : -(((c - d₁ : ℝ) : ℝ*)) < x - (c : ℝ*) := (abs_lt.1 hclose).1
        push_cast at h1
        linarith
      have hfx_ge : (f d₁ : ℝ*) ≤ starFun f x := by
        simpa using hstar_mono (d₁ : ℝ*) (coe_mem_starSet.2 hd₁_mem) x hx hd₁_lt_x.le
      rw [hfd₁] at hfx_ge
      have heps : (f c : ℝ*) - (ε : ℝ*) < ((f c - ε / 2 : ℝ) : ℝ*) := by
        have : f c - ε < f c - ε / 2 := by linarith
        simpa [Hyperreal.coe_sub] using Hyperreal.coe_lt_coe.2 this
      linarith
  · -- Upper bound: `starFun f x - (f c : ℝ*) < (ε : ℝ*)`
    by_cases hhigh : f b < f c + ε / 2
    · have hfx_le : starFun f x ≤ (f b : ℝ*) := by
        simpa using hstar_mono x hx (b : ℝ*) hb_star hx_bounds.2
      have hfb_lt : (f b : ℝ*) < ((f c + ε / 2 : ℝ) : ℝ*) := Hyperreal.coe_lt_coe.2 hhigh
      have heps : ((f c + ε / 2 : ℝ) : ℝ*) < (f c : ℝ*) + (ε : ℝ*) := by
        have : f c + ε / 2 < f c + ε := by linarith
        simpa [Hyperreal.coe_add] using Hyperreal.coe_lt_coe.2 this
      linarith
    · push Not at hhigh
      have hmem_r : f c + ε / 2 ∈ Set.Icc (f a) (f b) :=
        ⟨(hmono (Set.left_mem_Icc.2 hab) hc hc.1).trans (by linarith), hhigh⟩
      obtain ⟨d₂, hd₂_mem, hfd₂⟩ := hivp (f c + ε / 2) hmem_r
      have hc_lt_d₂ : c < d₂ := by
        by_contra hle
        push Not at hle
        have hle' := hmono hd₂_mem hc hle
        linarith
      have hx_lt_d₂ : x < (d₂ : ℝ*) := by
        have hclose := hxc (d₂ - c) (sub_pos.2 hc_lt_d₂)
        have h2 : x - (c : ℝ*) < ((d₂ - c : ℝ) : ℝ*) := (abs_lt.1 hclose).2
        push_cast at h2
        linarith
      have hfx_le : starFun f x ≤ (f d₂ : ℝ*) := by
        simpa using hstar_mono x hx (d₂ : ℝ*) (coe_mem_starSet.2 hd₂_mem) hx_lt_d₂.le
      rw [hfd₂] at hfx_le
      have heps : ((f c + ε / 2 : ℝ) : ℝ*) < (f c : ℝ*) + (ε : ℝ*) := by
        have : f c + ε / 2 < f c + ε := by linarith
        simpa [Hyperreal.coe_add] using Hyperreal.coe_lt_coe.2 this
      linarith

/-- Antitone companion to Goldblatt Exercise 7.8(4) (p. 82). -/
theorem continuousOn_Icc_of_antitoneOn_ivp {f : ℝ → ℝ} {a b : ℝ}
    (hanti : AntitoneOn f (Set.Icc a b))
    (hivp : ∀ r ∈ Set.Icc (f b) (f a), ∃ d ∈ Set.Icc a b, f d = r) :
    ContinuousOn f (Set.Icc a b) := by
  have hmono : MonotoneOn (fun x ↦ -f x) (Set.Icc a b) := fun u hu v hv huv ↦
    neg_le_neg (hanti hu hv huv)
  have hivp' : ∀ r ∈ Set.Icc (-f a) (-f b), ∃ d ∈ Set.Icc a b, -f d = r := by
    intro r hr
    obtain ⟨d, hd, hfd⟩ := hivp (-r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
    exact ⟨d, hd, by linarith⟩
  have hneg := continuousOn_Icc_of_monotoneOn_ivp hmono hivp'
  intro x hx
  simpa using continuousWithinAt_neg_nonstandard (hneg x hx)

/-! ## §7.9 Contraction Mappings and Fixed Points -/

/-- Goldblatt §7.9, equation `(vi)` (p. 82): Lipschitz condition on `A ⊆ ℝ` with constant `c ≥ 0`. -/
def IsLipschitzOn (f : ℝ → ℝ) (A : Set ℝ) (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ x ∈ A, ∀ y ∈ A, |f x - f y| ≤ c * |x - y|

/-- Global Lipschitz condition on `ℝ` with constant `c ≥ 0`. -/
def IsLipschitz (f : ℝ → ℝ) (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ x y : ℝ, |f x - f y| ≤ c * |x - y|

/-- Transferred hyperreal Lipschitz inequality on `starSet A` (Goldblatt §7.9, p. 82). -/
theorem starFun_abs_sub_le_of_isLipschitzOn {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (hf : IsLipschitzOn f A c) {x y : ℝ*} (hx : x ∈ starSet A) (hy : y ∈ starSet A) :
    |starFun f x - starFun f y| ≤ (c : ℝ*) * |x - y| := by
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  rcases ofSeq_surjective y with ⟨s, rfl⟩
  exact ofSeq_le_ofSeq.2 ((hx.and hy).mono fun n ⟨hnx, hny⟩ ↦ hf.2 (r n) hnx (s n) hny)

/-- Goldblatt §7.9 (p. 82): **Nonstandard proof that every Lipschitz function on `A` is uniformly
continuous on `A`**: if `x ≈ₕ y`, `c |x - y|` is `limited * infinitesimal = infinitesimal`. -/
theorem uniformContinuousOn_of_isLipschitzOn {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (hf : IsLipschitzOn f A c) : UniformContinuousOn f A := by
  rw [uniformContinuousOn_iff_infClose]
  intro x hx y hy hxy
  have hle := starFun_abs_sub_le_of_isLipschitzOn hf hx hy
  have hinf : IsInfinitesimal ((c : ℝ*) * |x - y|) :=
    (isLimited_coe c).mul_isInfinitesimal hxy.abs
  refine isInfinitesimal_of_abs_le hinf ?_
  have hnn : 0 ≤ (c : ℝ*) * |x - y| :=
    mul_nonneg (Hyperreal.coe_nonneg.2 hf.1) (abs_nonneg _)
  rwa [abs_of_nonneg hnn]

/-- Global form of Goldblatt §7.9 (p. 82): every Lipschitz function `f : ℝ → ℝ` is uniformly
continuous (and hence continuous). -/
theorem uniformContinuous_of_isLipschitz {f : ℝ → ℝ} {c : ℝ} (hf : IsLipschitz f c) :
    UniformContinuous f := by
  rw [← uniformContinuousOn_univ]
  exact uniformContinuousOn_of_isLipschitzOn ⟨hf.1, fun x _ y _ ↦ hf.2 x y⟩

/-- Goldblatt §7.9 (p. 82): A contraction mapping on `ℝ` is a Lipschitz function with `0 ≤ c < 1`. -/
def IsContraction (f : ℝ → ℝ) (c : ℝ) : Prop :=
  0 ≤ c ∧ c < 1 ∧ ∀ x y : ℝ, |f x - f y| ≤ c * |x - y|

/-- Contraction mapping on a subset `A ⊆ ℝ` mapping `A` into itself. -/
def IsContractionOn (f : ℝ → ℝ) (A : Set ℝ) (c : ℝ) : Prop :=
  0 ≤ c ∧ c < 1 ∧ Set.MapsTo f A A ∧ ∀ x ∈ A, ∀ y ∈ A, |f x - f y| ≤ c * |x - y|

/-- Goldblatt §7.9 concrete contraction example `f(x) = x / 2 + 1 / 2` (p. 83). -/
def halfAddHalf (x : ℝ) : ℝ := x / 2 + 1 / 2

/-- Goldblatt §7.9 (p. 83): `halfAddHalf` is a contraction with constant `c = 1 / 2`, its `n`-th
iterate is `x / 2 ^ n + (1 - 1 / 2 ^ n)`, and its unique fixed point is `1`. -/
theorem halfAddHalf_contraction_and_iterates :
    IsContraction halfAddHalf (1 / 2) ∧
    (∀ (n : ℕ) (x : ℝ), halfAddHalf^[n] x = x / (2 : ℝ) ^ n + (1 - 1 / (2 : ℝ) ^ n)) ∧
    (∀ x : ℝ, halfAddHalf x = x ↔ x = 1) := by
  refine ⟨⟨by norm_num, by norm_num, fun x y ↦ ?_⟩, ?_, fun x ↦ ?_⟩
  · have : halfAddHalf x - halfAddHalf y = (1 / 2) * (x - y) := by
      simp only [halfAddHalf]
      ring
    rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  · intro n x
    induction n generalizing x with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply, ih (halfAddHalf x)]
        simp only [halfAddHalf, pow_succ]
        field_simp
        ring
  · simp only [halfAddHalf]
    constructor <;> intro h <;> linarith

/-- Nonstandard characterization of sequential convergence (Goldblatt Theorem 6.1.1, used in
§7.9 p. 84 and §7.12 p. 87): `Tendsto s atTop (𝓝 L) ↔ ∀ N : ℕ*, IsUnlimitedNat N → starSeq s N ≈ₕ L`. -/
theorem tendsto_atTop_nhds_iff_starSeq_infClose {s : ℕ → ℝ} {L : ℝ} :
    Tendsto s atTop (𝓝 L) ↔ ∀ N : ℕ*, IsUnlimitedNat N → starSeq s N ≈ₕ (L : ℝ*) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro hs N hN r hr
    obtain ⟨k, hk⟩ := hs r hr
    induction N using Germ.inductionOn with | _ a =>
    have ha : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), k < a i := Germ.coe_lt.1 (hN k)
    refine ofSeq_lt_ofSeq.2 (ha.mono fun i hi ↦ ?_)
    have h1 := hk (a i) hi.le
    rwa [Real.dist_eq] at h1
  · intro h ε hε
    by_contra hnot
    push Not at hnot
    choose a ha using fun k : ℕ ↦ hnot (k + 1)
    let N : ℕ* := (a : ℕ*)
    have hN_unl : IsUnlimitedNat N := by
      intro j
      have hat : ∀ᶠ k in atTop, j < a k :=
        eventually_atTop.2 ⟨j, fun k hk ↦ Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hk) (ha k).1⟩
      exact Germ.coe_lt.2 (hat.filter_mono Nat.hyperfilter_le_atTop)
    have hge : (ε : ℝ*) ≤ |starSeq s N - (L : ℝ*)| := by
      refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun k ↦ ?_)
      have h1 := (ha k).2
      rwa [Real.dist_eq] at h1
    exact not_lt_of_ge hge (h N hN_unl ε hε)

/-- For `0 ≤ c < 1` and any unlimited `N ∈ ℕ*`, `c ^ N` (`starSeq (c ^ ·) N`) is infinitesimal
(used in Goldblatt §7.9, p. 84). -/
theorem isInfinitesimal_starSeq_pow_of_lt_one {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    {N : ℕ*} (hN : IsUnlimitedNat N) :
    IsInfinitesimal (starSeq (fun n ↦ c ^ n) N) := by
  have htend : Tendsto (fun n : ℕ ↦ c ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1
  exact infClose_zero_iff.1 ((tendsto_atTop_nhds_iff_starSeq_infClose.1 htend) N hN)

/-- Goldblatt §7.9, Theorem 7.9.1 (pp. 83–84): **Contraction Mapping Fixed-Point Theorem on Closed
Subsets of `ℝ`** (nonstandard proof via Picard iterates and shadows).
If `A ⊆ ℝ` is closed and nonempty and `f` is a contraction on `A`, then `f` has a unique fixed
point `L ∈ A`, and for every starting point `x₀ ∈ A`, `f^[n] x₀ → L` as `n → ∞`. -/
theorem contractionOn_isClosed_existsUnique_fixedPoint {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (hclosed : IsClosed A) (hAne : A.Nonempty) (hcon : IsContractionOn f A c) :
    ∃ L : ℝ, (L ∈ A ∧ f L = L) ∧ (∀ y : ℝ, y ∈ A → f y = y → y = L) ∧
      (∀ x₀ ∈ A, Tendsto (fun n ↦ f^[n] x₀) atTop (𝓝 L)) := by
  rcases hcon with ⟨hc0, hc1, hmaps, hlip⟩
  have h1mc : 0 < 1 - c := sub_pos.2 hc1
  -- Continuity of `f` on `A` from Lipschitz condition
  have hcont : ContinuousOn f A :=
    (uniformContinuousOn_of_isLipschitzOn ⟨hc0, hlip⟩).continuousOn
  -- Core step: for ANY `x₀ ∈ A` and ANY unlimited `N : ℕ*`, `shadow (starSeq (f^[·] x₀) N)` is in
  -- `A`, is infinitely close to `starSeq (f^[·] x₀) N`, and is a fixed point of `f`!
  have hshadow_fp : ∀ x₀ ∈ A, ∀ N : ℕ*, IsUnlimitedNat N →
      let s : ℕ → ℝ := fun n ↦ f^[n] x₀
      let L : ℝ := shadow (starSeq s N)
      starSeq s N ≈ₕ (L : ℝ*) ∧ L ∈ A ∧ f L = L := by
    intro x₀ hx₀ N hN
    set s : ℕ → ℝ := fun n ↦ f^[n] x₀
    -- Equation (vii): `s (n + 1) = f (s n)`
    have hs_succ : ∀ n : ℕ, s (n + 1) = f (s n) := fun n ↦ Function.iterate_succ_apply' f n x₀
    have hsA : ∀ n : ℕ, s n ∈ A := by
      intro n
      induction n with
      | zero => exact hx₀
      | succ k ih =>
          rw [hs_succ k]
          exact hmaps ih
    -- Equation (viii): `|s n - s (n + 1)| ≤ c ^ n * |s 0 - s 1|`
    have hviii : ∀ n : ℕ, |s n - s (n + 1)| ≤ c ^ n * |s 0 - s 1| := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
          rw [hs_succ k, hs_succ (k + 1)]
          calc |f (s k) - f (s (k + 1))|
              ≤ c * |s k - s (k + 1)| := hlip _ (hsA k) _ (hsA (k + 1))
            _ ≤ c * (c ^ k * |s 0 - s 1|) := mul_le_mul_of_nonneg_left ih hc0
            _ = c ^ (k + 1) * |s 0 - s 1| := by rw [pow_succ']; ring
    -- Equation (ix): `|s 0 - s n| ≤ ((1 - c ^ n) / (1 - c)) * |s 0 - s 1| ≤ |s 0 - s 1| / (1 - c)`
    have hix_geom : ∀ n : ℕ, |s 0 - s n| ≤ ((1 - c ^ n) / (1 - c)) * |s 0 - s 1| := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
          have htri : |s 0 - s (k + 1)| ≤ |s 0 - s k| + |s k - s (k + 1)| := by
            have : s 0 - s (k + 1) = (s 0 - s k) + (s k - s (k + 1)) := by ring
            rw [this]
            exact abs_add_le _ _
          calc |s 0 - s (k + 1)|
              ≤ ((1 - c ^ k) / (1 - c)) * |s 0 - s 1| + c ^ k * |s 0 - s 1| :=
                htri.trans (add_le_add ih (hviii k))
            _ = ((1 - c ^ (k + 1)) / (1 - c)) * |s 0 - s 1| := by
                have hne : 1 - c ≠ 0 := h1mc.ne'
                field_simp [hne]
                ring
    have hix : ∀ n : ℕ, |s 0 - s n| ≤ |s 0 - s 1| / (1 - c) := by
      intro n
      have hpow_nn : 0 ≤ c ^ n := pow_nonneg hc0 n
      have h1_le : (1 - c ^ n) / (1 - c) ≤ 1 / (1 - c) :=
        div_le_div_of_nonneg_right (by linarith) h1mc.le
      calc |s 0 - s n|
          ≤ ((1 - c ^ n) / (1 - c)) * |s 0 - s 1| := hix_geom n
        _ ≤ (1 / (1 - c)) * |s 0 - s 1| := mul_le_mul_of_nonneg_right h1_le (abs_nonneg _)
        _ = |s 0 - s 1| / (1 - c) := by ring
    -- Transfer (ix) to `N ∈ ℕ*` to see `starSeq s N` is limited
    have hsN_bound : |(s 0 : ℝ*) - starSeq s N| ≤ ((|s 0 - s 1| / (1 - c) : ℝ) : ℝ*) := by
      induction N using Germ.inductionOn with | _ a =>
      exact ofSeq_le_ofSeq.2 (Eventually.of_forall fun i ↦ hix (a i))
    have hsN_lim : IsLimited (starSeq s N) := by
      have : starSeq s N = (s 0 : ℝ*) - ((s 0 : ℝ*) - starSeq s N) := by ring
      rw [this]
      refine (isLimited_coe (s 0)).sub (isLimited_iff_abs_le_real.2 ?_)
      exact ⟨|s 0 - s 1| / (1 - c), div_nonneg (abs_nonneg _) h1mc.le, hsN_bound⟩
    set L : ℝ := shadow (starSeq s N)
    have hsN_close : starSeq s N ≈ₕ (L : ℝ*) := infClose_shadow hsN_lim
    have hsN_mem : starSeq s N ∈ starSet A := by
      induction N using Germ.inductionOn with | _ a =>
      exact ofSeq_mem_starSet.2 (Eventually.of_forall fun i ↦ hsA (a i))
    -- Show `L ∈ A` because `A` is closed and `starSeq s N ∈ starSet A` is infinitely close to `L`
    have hLA : L ∈ A := by
      rw [← hclosed.closure_eq, Metric.mem_closure_iff]
      intro ε hε
      have hlt : |starSeq s N - (L : ℝ*)| < (ε : ℝ*) := hsN_close ε hε
      induction N using Germ.inductionOn with | _ a =>
      have hev_lt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), |s (a i) - L| < ε := ofSeq_lt_ofSeq.1 hlt
      obtain ⟨i, hi_lt⟩ := hev_lt.exists
      exact ⟨s (a i), hsA (a i), by rwa [Real.dist_eq, abs_sub_comm]⟩
    -- Transfer (vii): `starFun f (starSeq s N) = starSeq s (N + 1)`
    have hf_sN : starFun f (starSeq s N) = starSeq s (N + 1) := by
      induction N using Germ.inductionOn with | _ a =>
      exact Germ.coe_eq.2 (Eventually.of_forall fun i ↦ (hs_succ (a i)).symm)
    -- Transfer (viii): `|starSeq s N - starSeq s (N + 1)| ≤ c ^ N * |s 0 - s 1|`
    have hstep_le : |starSeq s N - starSeq s (N + 1)| ≤
        starSeq (fun n ↦ c ^ n) N * |(s 0 : ℝ*) - (s 1 : ℝ*)| := by
      induction N using Germ.inductionOn with | _ a =>
      exact ofSeq_le_ofSeq.2 (Eventually.of_forall fun i ↦ hviii (a i))
    have hstep_inf : starSeq s (N + 1) ≈ₕ starSeq s N := by
      have hclose' : starSeq s N ≈ₕ starSeq s (N + 1) := by
        refine isInfinitesimal_of_abs_le
          ((isInfinitesimal_starSeq_pow_of_lt_one hc0 hc1 hN).mul_isLimited
            (isLimited_coe |s 0 - s 1|)) ?_
        have hnn : 0 ≤ starSeq (fun n ↦ c ^ n) N * |(s 0 : ℝ*) - (s 1 : ℝ*)| := by
          induction N using Germ.inductionOn with | _ a =>
          exact ofSeq_le_ofSeq.2 (Eventually.of_forall fun i ↦
            mul_nonneg (pow_nonneg hc0 (a i)) (abs_nonneg _))
        rw [Hyperreal.coe_abs, Hyperreal.coe_sub, abs_of_nonneg hnn]
        exact hstep_le
      exact hclose'.symm
    -- Goldblatt p. 84 chain: `f(L) ≈ₕ *f(s_N) = s_{N+1} ≈ₕ s_N ≈ₕ L`
    have hfL_close : (f L : ℝ*) ≈ₕ (L : ℝ*) := by
      have hcont_L := ((continuousOn_iff_infClose.1 hcont) L hLA (starSeq s N) hsN_mem hsN_close).symm
      exact hcont_L.trans (hf_sN ▸ hstep_inf.trans hsN_close)
    exact ⟨hsN_close, hLA, coe_eq_of_infClose hfL_close⟩
  -- Uniqueness of fixed point on `A`
  have huniq : ∀ x y : ℝ, x ∈ A → y ∈ A → f x = x → f y = y → x = y := by
    intro x y hx hy hfx hfy
    have hle : |x - y| ≤ c * |x - y| := by
      calc |x - y| = |f x - f y| := by rw [hfx, hfy]
      _ ≤ c * |x - y| := hlip x hx y hy
    have hzero : |x - y| = 0 := by nlinarith [abs_nonneg (x - y)]
    exact sub_eq_zero.1 (abs_eq_zero.1 hzero)
  set L₀ : ℝ := shadow (starSeq (fun n ↦ f^[n] hAne.choose) omegaNat)
  obtain ⟨_, hL₀A, hfL₀⟩ := hshadow_fp hAne.choose hAne.choose_spec omegaNat isUnlimitedNat_omegaNat
  refine ⟨L₀, ⟨hL₀A, hfL₀⟩, fun y hyA hfy ↦ huniq y L₀ hyA hL₀A hfy hfL₀, ?_⟩
  -- Deduce convergence of Picard iterates from uniqueness of shadow (Goldblatt p. 84 remark!)
  intro x₀ hx₀
  rw [tendsto_atTop_nhds_iff_starSeq_infClose]
  intro N hN
  obtain ⟨hsN_close, hLN_A, hfLN⟩ := hshadow_fp x₀ hx₀ N hN
  have hLN_eq : shadow (starSeq (fun n ↦ f^[n] x₀) N) = L₀ :=
    huniq _ L₀ hLN_A hL₀A hfLN hfL₀
  rwa [← hLN_eq]

/-- Goldblatt §7.9, Theorem 7.9.1 (pp. 83–84): **Any contraction mapping `f : ℝ → ℝ` has a unique
fixed point `L`**, and for any starting point `x₀ ∈ ℝ`, `f^[n] x₀ → L`. -/
theorem contraction_existsUnique_fixedPoint {f : ℝ → ℝ} {c : ℝ} (hf : IsContraction f c) :
    (∃! L : ℝ, f L = L) ∧
    ∀ x₀ : ℝ, ∃ L : ℝ, f L = L ∧ Tendsto (fun n ↦ f^[n] x₀) atTop (𝓝 L) := by
  have hcon_univ : IsContractionOn f Set.univ c :=
    ⟨hf.1, hf.2.1, Set.mapsTo_univ f _, fun x _ y _ ↦ hf.2.2 x y⟩
  obtain ⟨L, ⟨_, hfL⟩, huniq, htend⟩ :=
    contractionOn_isClosed_existsUnique_fixedPoint isClosed_univ ⟨0, trivial⟩ hcon_univ
  refine ⟨⟨L, hfL, fun y hfy ↦ huniq y trivial hfy⟩, fun x₀ ↦ ?_⟩
  exact ⟨L, hfL, htend x₀ trivial⟩

/-! ## §7.10–7.11 Permanence Principles for Functions & Robinson's Sequential Lemma -/

/-- Goldblatt §7.10 — **Cauchy's Principle (Infinitesimal-to-Real Neighborhood Permanence)** (p. 85):
If `S ⊆ ℝ`, `c ∈ ℝ`, and there is a positive hyperreal `d > 0` (in particular, any positive
infinitesimal `d ≈ₕ 0`) such that every `x ∈ ℝ*` with `|x - c| < d` belongs to `*S`, then there is
a standard real `ε > 0` such that:
1. every real `x` with `|x - c| < ε` belongs to `S`, AND
2. every hyperreal `x` with `|x - c| < ε` belongs to `*S`! -/
theorem cauchy_permanence_principle {S : Set ℝ} {c : ℝ}
    (h : ∃ d : ℝ*, 0 < d ∧ ∀ x : ℝ*, |x - (c : ℝ*)| < d → x ∈ starSet S) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ x : ℝ, |x - c| < ε → x ∈ S) ∧
      (∀ x : ℝ*, |x - (c : ℝ*)| < (ε : ℝ*) → x ∈ starSet S) := by
  rcases h with ⟨d, hd_pos, hd⟩
  rcases ofSeq_surjective d with ⟨dSeq, rfl⟩
  have hd_ev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < dSeq n := ofSeq_lt_ofSeq.1 hd_pos
  have hex_real : ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x - c| < ε → x ∈ S := by
    by_contra hnot
    push Not at hnot
    have hex : ∀ n : ℕ, 0 < dSeq n → ∃ x : ℝ, |x - c| < dSeq n / 2 ∧ x ∉ S :=
      fun n hn ↦ hnot (dSeq n / 2) (half_pos hn)
    let r : ℕ → ℝ := fun n ↦ if hn : 0 < dSeq n then (hex n hn).choose else c
    have hr_lt : |ofSeq r - (c : ℝ*)| < ofSeq dSeq := by
      refine ofSeq_lt_ofSeq.2 (hd_ev.mono fun n hn ↦ ?_)
      change |r n - c| < dSeq n
      simp only [r, hn, ↓reduceDIte]
      exact ((hex n hn).choose_spec.1).trans (half_lt_self hn)
    have hr_nmem : ofSeq r ∉ starSet S := by
      refine Ultrafilter.eventually_not.1 (hd_ev.mono fun n hn ↦ ?_)
      simp only [r, hn, ↓reduceDIte]
      exact (hex n hn).choose_spec.2
    exact hr_nmem (hd (ofSeq r) hr_lt)
  obtain ⟨ε, hε_pos, hεS⟩ := hex_real
  refine ⟨ε, hε_pos, hεS, fun x hx ↦ ?_⟩
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  have hr_lt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |r n - c| < ε := ofSeq_lt_ofSeq.1 hx
  exact ofSeq_mem_starSet.2 (hr_lt.mono fun n hn ↦ hεS (r n) hn)

/-- **Robinson's Sequential Lemma** in the ultrapower `ℝ*` (referenced in Goldblatt §7.12, p. 87):
Given an internal hypersequence `U : ℕ* → ℝ*` represented by `u : ℕ → ℕ → ℝ` (`U = Germ.map₂ u omegaNat`),
if `U (n : ℕ*) ≈ₕ L` for every standard `n ∈ ℕ`, then there exists an UNLIMITED `N ∈ ℕ*` such that
`U K ≈ₕ L` for ALL `K ∈ ℕ*` with `K ≤ N` (i.e. `{U K : K ≤ N} ⊆ hal(L)`)! -/
theorem robinson_sequential_lemma (u : ℕ → ℕ → ℝ) (L : ℝ*)
    (hstd : ∀ n : ℕ, Germ.map₂ u omegaNat (n : ℕ*) ≈ₕ L) :
    ∃ N : ℕ*, IsUnlimitedNat N ∧ ∀ K : ℕ*, K ≤ N → Germ.map₂ u omegaNat K ≈ₕ L := by
  rcases ofSeq_surjective L with ⟨lSeq, rfl⟩
  -- For each `m : ℕ`, let `E m` be the set of indices `i` where `∀ k ≤ m, |u i k - lSeq i| < (m + 1)⁻¹`
  let P : ℕ → ℕ → Prop := fun i m ↦ ∀ k ≤ m, |u i k - lSeq i| < ((m : ℝ) + 1)⁻¹
  have hE_mem : ∀ m : ℕ, {i : ℕ | P i m} ∈ (hyperfilter ℕ : Filter ℕ) := by
    intro m
    have hall : ∀ k ∈ Finset.range (m + 1),
        {i : ℕ | |u i k - lSeq i| < ((m : ℝ) + 1)⁻¹} ∈ (hyperfilter ℕ : Filter ℕ) := by
      intro k _
      have hclose := hstd k ((m : ℝ) + 1)⁻¹ (by positivity)
      exact ofSeq_lt_ofSeq.1 hclose
    have hbi := (Filter.biInter_finset_mem (Finset.range (m + 1))).2 hall
    refine mem_of_superset hbi fun i hi k hkm ↦ ?_
    exact Set.mem_iInter₂.1 hi k (Finset.mem_range.2 (Nat.lt_succ_of_le hkm))
  -- At each ultrapower coordinate `i`, pick the largest `m ≤ i` satisfying `P i m` (or `0`)
  let S : ℕ → Finset ℕ := fun i ↦ (Finset.range (i + 1)).filter (fun m ↦ P i m)
  let a : ℕ → ℕ := fun i ↦ if hne : (S i).Nonempty then (S i).max' hne else 0
  have ha_ge : ∀ m : ℕ, ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), m ≤ a i ∧ P i (a i) := by
    intro m
    have hi_ge : {i : ℕ | m ≤ i} ∈ (hyperfilter ℕ : Filter ℕ) :=
      Nat.hyperfilter_le_atTop (eventually_ge_atTop m)
    have hboth : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), P i m ∧ m ≤ i :=
      Filter.inter_mem (hE_mem m) hi_ge
    refine hboth.mono fun i ⟨hiP, him⟩ ↦ ?_
    have hm_mem : m ∈ S i :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le him), hiP⟩
    have hne : (S i).Nonempty := ⟨m, hm_mem⟩
    have ha_eq : a i = (S i).max' hne := by simp [a, hne]
    refine ⟨ha_eq ▸ Finset.le_max' (S i) m hm_mem, ?_⟩
    rw [ha_eq]
    exact (Finset.mem_filter.1 (Finset.max'_mem (S i) hne)).2
  refine ⟨(a : ℕ*), ?_, ?_⟩
  · intro m
    exact Germ.coe_lt.2 ((ha_ge (m + 1)).mono fun i hi ↦ Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hi.1)
  · intro K hK r hr
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr
    induction K using Germ.inductionOn with | _ b =>
    have hba : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), b i ≤ a i := Germ.coe_le.1 hK
    refine ofSeq_lt_ofSeq.2 (((ha_ge m).and hba).mono fun i ⟨⟨him, hiP⟩, hiba⟩ ↦ ?_)
    change |u i (b i) - lSeq i| < r
    have h1 : |u i (b i) - lSeq i| < ((a i : ℝ) + 1)⁻¹ := hiP (b i) hiba
    have h2 : ((a i : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1)⁻¹ := by
      have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hm_le : (m : ℝ) + 1 ≤ (a i : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right him 1
      exact inv_anti₀ hm_pos hm_le
    have h3 : ((m : ℝ) + 1)⁻¹ < r := by simpa [one_div] using hm
    exact (h1.trans_le h2).trans h3

/-! ### §7.11 Exercises on Permanence of Functions (pp. 85–86) -/

/-- Goldblatt Exercise 7.11(1) (p. 85): For `A ⊆ ℝ` (representing the domain of a partial real
function `f`) and `c ∈ ℝ`, `*f(x)` is defined for all `x ≈ₕ c` (`halo (c : ℝ*) ⊆ starSet A`)
if and only if `f(x)` is defined throughout some real open interval `(c - ε, c + ε)` with `ε > 0`. -/
theorem halo_subset_starSet_iff_exists_real_Ioo {A : Set ℝ} {c : ℝ} :
    halo (c : ℝ*) ⊆ starSet A ↔ ∃ ε : ℝ, 0 < ε ∧ Set.Ioo (c - ε) (c + ε) ⊆ A := by
  constructor
  · intro h
    have hex : ∃ d : ℝ*, 0 < d ∧ ∀ x : ℝ*, |x - (c : ℝ*)| < d → x ∈ starSet A := by
      refine ⟨Hyperreal.epsilon, Hyperreal.epsilon_pos, fun x hx ↦ h (mem_halo_iff.2 ?_)⟩
      exact isInfinitesimal_of_abs_le isInfinitesimal_epsilon
        (hx.le.trans (le_abs_self Hyperreal.epsilon))
    obtain ⟨ε, hε_pos, hεA, _⟩ := cauchy_permanence_principle hex
    refine ⟨ε, hε_pos, fun x hx ↦ hεA x ?_⟩
    rw [abs_lt]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · rintro ⟨ε, hε_pos, hεA⟩ x hx
    have hxc : x ≈ₕ (c : ℝ*) := mem_halo_iff.1 hx
    have hlt : |x - (c : ℝ*)| < (ε : ℝ*) := hxc ε hε_pos
    have hmem_Ioo : x ∈ starSet (Set.Ioo (c - ε) (c + ε)) := by
      rw [starSet_Ioo]
      rcases abs_lt.1 hlt with ⟨hl, hr⟩
      exact ⟨by push_cast; linarith, by push_cast; linarith⟩
    exact (starSet_subset_starSet_iff.2 hεA) hmem_Ioo

/-- Goldblatt Exercise 7.11(2) (p. 85): If `*f` is constant on `hal(c)` for `c ∈ ℝ`, then `f` is
constant on some real open interval `(c - ε, c + ε)` with `ε > 0`. -/
theorem constant_on_Ioo_of_starFun_constant_on_halo {f : ℝ → ℝ} {c : ℝ}
    (hconst : ∃ k : ℝ*, ∀ x ∈ halo (c : ℝ*), starFun f x = k) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Set.Ioo (c - ε) (c + ε), f x = f c := by
  rcases hconst with ⟨k, hk⟩
  have hkc : k = (f c : ℝ*) := by
    have := hk (c : ℝ*) (mem_halo_iff.2 (InfClose.refl _))
    rwa [starFun_coe, eq_comm] at this
  subst hkc
  let S : Set ℝ := {x : ℝ | f x = f c}
  have hsub : halo (c : ℝ*) ⊆ starSet S := by
    intro x hx
    have hfx := hk x hx
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    exact ofSeq_mem_starSet.2 (Germ.coe_eq.1 hfx)
  exact halo_subset_starSet_iff_exists_real_Ioo.1 hsub

/-- Relative form of Exercise 7.11(2) on a subset `A ⊆ ℝ`: if `*f(x) = f(c)` for all `x ∈ *A`
with `x ≈ₕ c`, then there exists `ε > 0` such that `f x = f c` for all `x ∈ A ∩ (c - ε, c + ε)`. -/
theorem locally_constant_within_of_starFun_constant_on_halo {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (hconst : ∀ x ∈ starSet A, x ≈ₕ (c : ℝ*) → starFun f x = (f c : ℝ*)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ A, |x - c| < ε → f x = f c := by
  let S : Set ℝ := {x : ℝ | x ∈ A → f x = f c}
  have hsub : halo (c : ℝ*) ⊆ starSet S := by
    intro x hx
    have hxc : x ≈ₕ (c : ℝ*) := mem_halo_iff.1 hx
    by_cases hxA : x ∈ starSet A
    · have hfx := hconst x hxA hxc
      rcases ofSeq_surjective x with ⟨r, rfl⟩
      exact ofSeq_mem_starSet.2 ((Germ.coe_eq.1 hfx).mono fun n hn _ ↦ hn)
    · rcases ofSeq_surjective x with ⟨r, rfl⟩
      have hnot : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r n ∉ A :=
        Ultrafilter.eventually_not.2 hxA
      exact ofSeq_mem_starSet.2 (hnot.mono fun n hn hnA ↦ False.elim (hn hnA))
  obtain ⟨ε, hε_pos, hεS⟩ := halo_subset_starSet_iff_exists_real_Ioo.1 hsub
  refine ⟨ε, hε_pos, fun x hxA hlt ↦ ?_⟩
  rcases abs_lt.1 hlt with ⟨hl, hr⟩
  exact hεS ⟨by linarith, by linarith⟩ hxA

/-- Goldblatt Exercise 7.11(3) (p. 86): **If `f : ℝ → ℝ` is continuous on an interval `A ⊆ ℝ`
(`Set.OrdConnected A`) and `*f(x)` is a standard real (`∈ range coe`) for every `x ∈ *A`, then `f`
is constant on `A`!**
Proved using Exercise 7.11(2): at every `c ∈ A`, `*f(x) ≈ₕ f(c)` and `*f(x) ∈ ℝ` force
`*f(x) = f(c)` on `hal(c) ∩ *A`, so `f` is locally constant on `A`, hence globally constant on
every `[a, b] ⊆ A`! -/
theorem constant_on_ordConnected_of_starFun_real {f : ℝ → ℝ} {A : Set ℝ}
    (hA : A.OrdConnected) (hf : ContinuousOn f A)
    (hreal : ∀ x ∈ starSet A, ∃ r : ℝ, starFun f x = (r : ℝ*)) :
    ∀ a ∈ A, ∀ b ∈ A, f a = f b := by
  -- Step 1: By continuity + `hreal` + Exercise 7.11(2), `f` is locally constant on `A`
  have hloc : ∀ c ∈ A, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ A, |x - c| < ε → f x = f c := by
    intro c hc
    refine locally_constant_within_of_starFun_constant_on_halo fun x hxA hxc ↦ ?_
    obtain ⟨r, hr⟩ := hreal x hxA
    have hclose : starFun f x ≈ₕ (f c : ℝ*) :=
      (continuousOn_iff_infClose.1 hf) c hc x hxA hxc
    rw [hr] at hclose ⊢
    exact congrArg _ (coe_eq_of_infClose hclose)
  -- Step 2: Deduce `f a = f b` for `a ≤ b` in `A` via `sSup {t ∈ [a, b] | ∀ u ∈ [a, t], f u = f a}`
  have hle_case : ∀ a ∈ A, ∀ b ∈ A, a ≤ b → f a = f b := by
    intro a ha b hb hab
    rcases eq_or_lt_of_le hab with rfl | hlt
    · rfl
    · have hsub : Set.Icc a b ⊆ A := hA.out ha hb
      let B : Set ℝ := {t : ℝ | t ∈ Set.Icc a b ∧ ∀ u ∈ Set.Icc a t, f u = f a}
      have haB : a ∈ B := ⟨Set.left_mem_Icc.2 hab, fun u hu ↦ by
        have hua : u = a := le_antisymm hu.2 hu.1
        rw [hua]⟩
      have hB_ne : B.Nonempty := ⟨a, haB⟩
      have hB_bdd : BddAbove B := ⟨b, fun t ht ↦ ht.1.2⟩
      set s : ℝ := sSup B
      have hs_mem_Icc : s ∈ Set.Icc a b :=
        ⟨le_csSup hB_bdd haB, csSup_le hB_ne fun t ht ↦ ht.1.2⟩
      obtain ⟨ε, hε_pos, hεs⟩ := hloc s (hsub hs_mem_Icc)
      -- First show `∀ u ∈ Set.Icc a s, f u = f a` (in particular `f s = f a`)
      have hs_const : ∀ u ∈ Set.Icc a s, f u = f a := by
        obtain ⟨t₀, ht₀B, ht₀_gt⟩ := exists_lt_of_lt_csSup hB_ne (by linarith : s - ε / 2 < s)
        have hfs_eq : f s = f a := by
          have ht₀_close : |t₀ - s| < ε := by
            rw [abs_lt]
            exact ⟨by linarith, by linarith [le_csSup hB_bdd ht₀B]⟩
          have hft₀_s : f t₀ = f s := hεs t₀ (hsub ht₀B.1) ht₀_close
          have hft₀_a : f t₀ = f a := ht₀B.2 t₀ ⟨ht₀B.1.1, le_rfl⟩
          exact hft₀_s.symm.trans hft₀_a
        intro u hu
        by_cases hut₀ : u ≤ t₀
        · exact ht₀B.2 u ⟨hu.1, hut₀⟩
        · push Not at hut₀
          have hu_close : |u - s| < ε := by
            rw [abs_lt]
            exact ⟨by linarith, by linarith [hu.2]⟩
          exact (hεs u (hsub ⟨hu.1, hu.2.trans hs_mem_Icc.2⟩) hu_close).trans hfs_eq
      -- Now show `s = b` (otherwise `min b (s + ε / 2) ∈ B` exceeds `s`)
      have hsb : s = b := by
        by_contra hne
        have hs_lt_b : s < b := lt_of_le_of_ne hs_mem_Icc.2 hne
        set s' : ℝ := min b (s + ε / 2)
        have hs'_gt : s < s' := lt_min hs_lt_b (by linarith)
        have hs'_B : s' ∈ B := by
          refine ⟨⟨hs_mem_Icc.1.trans hs'_gt.le, min_le_left _ _⟩, fun u hu ↦ ?_⟩
          by_cases hus : u ≤ s
          · exact hs_const u ⟨hu.1, hus⟩
          · push Not at hus
            have hu_close : |u - s| < ε := by
              have hu_le : u ≤ s + ε / 2 := hu.2.trans (min_le_right _ _)
              rw [abs_lt]
              exact ⟨by linarith, by linarith⟩
            exact (hεs u (hsub ⟨hu.1, hu.2.trans (min_le_left _ _)⟩) hu_close).trans
              (hs_const s ⟨hs_mem_Icc.1, le_rfl⟩)
        exact not_lt_of_ge (le_csSup hB_bdd hs'_B) hs'_gt
      rw [hsb] at hs_const
      exact (hs_const b (Set.right_mem_Icc.2 hab)).symm
  intro a ha b hb
  rcases le_total a b with hab | hba
  · exact hle_case a ha b hb hab
  · exact (hle_case b hb a ha hba).symm

/-! ## §7.12 Sequences of Functions: Pointwise vs Uniform Convergence -/

/-- Goldblatt §7.12 (p. 86): Extension of a sequence of functions `F : ℕ → ℝ → ℝ` to a
hypersequence of functions `starFunSeq F : ℕ* → ℝ* → ℝ*` (`*F(N, x)`). -/
def starFunSeq (F : ℕ → ℝ → ℝ) : ℕ* → ℝ* → ℝ* :=
  Germ.map₂ (fun n x ↦ F n x)

/-- Componentwise evaluation of `starFunSeq` on `[a]` and `ofSeq r`. -/
@[simp]
theorem starFunSeq_coe_ofSeq (F : ℕ → ℝ → ℝ) (a : ℕ → ℕ) (r : ℕ → ℝ) :
    starFunSeq F (a : ℕ*) (ofSeq r) = ofSeq (fun k ↦ F (a k) (r k)) := rfl

/-- Goldblatt §7.12 (p. 86): For any standard `n ∈ ℕ`, `starFunSeq F (n : ℕ*)` reproduces `starFun (F n)`. -/
@[simp]
theorem starFunSeq_natCast (F : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ*) :
    starFunSeq F (n : ℕ*) x = starFun (F n) x := by
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  rfl

/-- Goldblatt §7.12 (p. 86): For any standard `x ∈ ℝ`, `N ↦ starFunSeq F N (x : ℝ*)` reproduces
the hypersequence `starSeq (fun n ↦ F n x)`. -/
@[simp]
theorem starFunSeq_coe_real (F : ℕ → ℝ → ℝ) (N : ℕ*) (x : ℝ) :
    starFunSeq F N (x : ℝ*) = starSeq (fun n ↦ F n x) N := by
  induction N using Germ.inductionOn with | _ a =>
  rfl

/-- Goldblatt §7.12 (p. 86): Standard `ε`-`m` definition of pointwise convergence of `F` to `f` on `A`. -/
def EpsDeltaPointwiseConvergesOn (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (A : Set ℝ) : Prop :=
  ∀ x ∈ A, ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → |F n x - f x| < ε

/-- Goldblatt §7.12 (p. 86): Standard `ε`-`m` definition of uniform convergence of `F` to `f` on `A`. -/
def EpsDeltaUniformConvergesOn (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (A : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → ∀ x ∈ A, |F n x - f x| < ε

/-- Equivalence of `EpsDeltaPointwiseConvergesOn` with `∀ x ∈ A, Tendsto (F · x) atTop (𝓝 (f x))`. -/
theorem pointwise_tendsto_iff_epsDelta {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {A : Set ℝ} :
    (∀ x ∈ A, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x))) ↔
      EpsDeltaPointwiseConvergesOn F f A := by
  simp only [Metric.tendsto_atTop, EpsDeltaPointwiseConvergesOn, Real.dist_eq, ge_iff_le]

/-- Equivalence of `TendstoUniformlyOn F f atTop A` and `EpsDeltaUniformConvergesOn F f A`. -/
theorem tendstoUniformlyOn_iff_epsDelta {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {A : Set ℝ} :
    TendstoUniformlyOn F f atTop A ↔ EpsDeltaUniformConvergesOn F f A := by
  rw [Metric.tendstoUniformlyOn_iff]
  simp only [Filter.eventually_atTop, EpsDeltaUniformConvergesOn, Real.dist_eq]
  constructor
  · intro h ε hε
    obtain ⟨m, hm⟩ := h ε hε
    exact ⟨m, fun n hn x hx ↦ abs_sub_comm (f x) (F n x) ▸ hm n hn x hx⟩
  · intro h ε hε
    obtain ⟨m, hm⟩ := h ε hε
    exact ⟨m, fun n hn x hx ↦ abs_sub_comm (F n x) (f x) ▸ hm n hn x hx⟩

/-- Goldblatt §7.12, Theorem 7.12.1 (p. 87):
`F` converges pointwise on `A` to `f` if and only if for each standard `x ∈ A` and each unlimited
`N ∈ ℕ*`, `starFunSeq F N (x : ℝ*) ≈ₕ (f x : ℝ*)`. -/
theorem pointwise_tendsto_iff_starFunSeq_infClose {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {A : Set ℝ} :
    (∀ x ∈ A, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x))) ↔
      ∀ x ∈ A, ∀ N : ℕ*, IsUnlimitedNat N → starFunSeq F N (x : ℝ*) ≈ₕ (f x : ℝ*) := by
  constructor
  · intro h x hx N hN
    rw [starFunSeq_coe_real]
    exact (tendsto_atTop_nhds_iff_starSeq_infClose.1 (h x hx)) N hN
  · intro h x hx
    refine tendsto_atTop_nhds_iff_starSeq_infClose.2 fun N hN ↦ ?_
    rw [← starFunSeq_coe_real]
    exact h x hx N hN

/-- Explicit `ε`-`m` form of Goldblatt Theorem 7.12.1 (p. 87). -/
theorem epsDeltaPointwiseConvergesOn_iff_starFunSeq_infClose {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {A : Set ℝ} :
    EpsDeltaPointwiseConvergesOn F f A ↔
      ∀ x ∈ A, ∀ N : ℕ*, IsUnlimitedNat N → starFunSeq F N (x : ℝ*) ≈ₕ (f x : ℝ*) := by
  rw [← pointwise_tendsto_iff_epsDelta, pointwise_tendsto_iff_starFunSeq_infClose]

/-- Goldblatt §7.12, Theorem 7.12.2 — **Robinson's Nonstandard Criterion for Uniform Convergence**
(p. 87):
`F` converges uniformly on `A` to `f` (`TendstoUniformlyOn F f atTop A`) if and only if for EVERY
hyperreal `x ∈ *A` and EVERY unlimited `N ∈ ℕ*`, `starFunSeq F N x ≈ₕ starFun f x`! -/
theorem tendstoUniformlyOn_iff_starFunSeq_infClose {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {A : Set ℝ} :
    TendstoUniformlyOn F f atTop A ↔
      ∀ N : ℕ*, IsUnlimitedNat N → ∀ x ∈ starSet A, starFunSeq F N x ≈ₕ starFun f x := by
  rw [tendstoUniformlyOn_iff_epsDelta]
  constructor
  · intro h N hN x hx r hr
    obtain ⟨m, hm⟩ := h r hr
    induction N using Germ.inductionOn with | _ a =>
    rcases ofSeq_surjective x with ⟨s, rfl⟩
    have ha : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), m < a k := Germ.coe_lt.1 (hN m)
    exact ofSeq_lt_ofSeq.2 ((ha.and hx).mono fun k ⟨hka, hkx⟩ ↦ hm (a k) hka.le (s k) hkx)
  · intro h ε hε
    by_contra hnot
    push Not at hnot
    have hex : ∀ k : ℕ, ∃ p : ℕ × ℝ, k + 1 ≤ p.1 ∧ p.2 ∈ A ∧ ε ≤ |F p.1 p.2 - f p.2| := by
      intro k
      obtain ⟨n, hn, x, hx, hge⟩ := hnot (k + 1)
      exact ⟨(n, x), hn, hx, hge⟩
    choose p hp using hex
    let N : ℕ* := ((fun k ↦ (p k).1) : ℕ*)
    let x : ℝ* := ofSeq (fun k ↦ (p k).2)
    have hN_unl : IsUnlimitedNat N := by
      intro j
      have hat : ∀ᶠ k in atTop, j < (p k).1 :=
        eventually_atTop.2 ⟨j, fun k hk ↦ Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hk) (hp k).1⟩
      exact Germ.coe_lt.2 (hat.filter_mono Nat.hyperfilter_le_atTop)
    have hxA : x ∈ starSet A :=
      ofSeq_mem_starSet.2 (Eventually.of_forall fun k ↦ (hp k).2.1)
    have hge : (ε : ℝ*) ≤ |starFunSeq F N x - starFun f x| :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun k ↦ (hp k).2.2)
    exact not_lt_of_ge hge (h N hN_unl x hxA ε hε)

/-- Explicit `ε`-`m` form of Goldblatt Theorem 7.12.2 (p. 87). -/
theorem epsDeltaUniformConvergesOn_iff_starFunSeq_infClose {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {A : Set ℝ} :
    EpsDeltaUniformConvergesOn F f A ↔
      ∀ N : ℕ*, IsUnlimitedNat N → ∀ x ∈ starSet A, starFunSeq F N x ≈ₕ starFun f x := by
  rw [← tendstoUniformlyOn_iff_epsDelta, tendstoUniformlyOn_iff_starFunSeq_infClose]

/-! ### Goldblatt §7.12 Counterexample: `f_n(x) = x^n` on `[0, 1]` (p. 87) -/

/-- Sequence of power functions `powFunSeq n x = x ^ n` (Goldblatt §7.12, p. 87). -/
def powFunSeq (n : ℕ) (x : ℝ) : ℝ := x ^ n

/-- Pointwise limit of `x ^ n` on `[0, 1]`: `0` for `x ≠ 1` and `1` at `x = 1`. -/
def powLimitFun (x : ℝ) : ℝ := if x = 1 then 1 else 0

/-- Elementary Bernoulli inequality `1 + n * t ≤ (1 + t) ^ n` for `-1 ≤ t` on `ℝ`. -/
theorem bernoulli_ineq_real {t : ℝ} (ht : -1 ≤ t) (n : ℕ) :
    1 + (n : ℝ) * t ≤ (1 + t) ^ n := by
  have h1t : 0 ≤ 1 + t := by linarith
  induction n with
  | zero => simp
  | succ k ih =>
      push_cast
      rw [pow_succ]
      have hmul : (1 + (k : ℝ) * t) * (1 + t) ≤ (1 + t) ^ k * (1 + t) :=
        mul_le_mul_of_nonneg_right ih h1t
      have hsq : 0 ≤ (k : ℝ) * t ^ 2 := mul_nonneg (Nat.cast_nonneg k) (sq_nonneg t)
      nlinarith

/-- Goldblatt §7.12 (p. 87): Each `powFunSeq n` is continuous on `[0, 1]` and `powFunSeq` converges
pointwise on `[0, 1]` to `powLimitFun`, yet `powLimitFun` is discontinuous at `1`! -/
theorem powFunSeq_continuous_pointwise_and_limit_discontinuous :
    (∀ n : ℕ, ContinuousOn (powFunSeq n) (Set.Icc 0 1)) ∧
    (∀ x ∈ Set.Icc 0 1, Tendsto (fun n ↦ powFunSeq n x) atTop (𝓝 (powLimitFun x))) ∧
    ¬ ContinuousWithinAt powLimitFun (Set.Icc 0 1) 1 := by
  refine ⟨fun n ↦ (continuous_pow n).continuousOn, ?_, ?_⟩
  · intro x hx
    rcases eq_or_lt_of_le hx.2 with rfl | hlt1
    · simp [powFunSeq, powLimitFun]
    · have hfx : powLimitFun x = 0 := by simp [powLimitFun, hlt1.ne]
      rw [hfx]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one hx.1 hlt1
  · rw [continuousWithinAt_iff_infClose]
    intro hcont
    let x : ℝ* := 1 - Hyperreal.epsilon / 2
    have he_pos : (0 : ℝ*) < Hyperreal.epsilon := Hyperreal.epsilon_pos
    have he_lt1 : Hyperreal.epsilon < 1 := by simpa using Hyperreal.epsilon_lt_of_pos one_pos
    have hx_mem : x ∈ starSet (Set.Icc 0 1) := by
      rw [starSet_Icc, Set.mem_Icc]
      push_cast
      simp only [x]
      exact ⟨by linarith, by linarith⟩
    have hx_close : x ≈ₕ (1 : ℝ*) := by
      unfold InfClose
      have : x - 1 = -((1 / 2 : ℝ) : ℝ*) * Hyperreal.epsilon := by
        simp only [x]
        push_cast
        ring
      rw [this]
      exact (isLimited_coe (1 / 2)).neg.mul_isInfinitesimal isInfinitesimal_epsilon
    have hfx_eq : starFun powLimitFun x = 0 := by
      have hx_lt1 : x < 1 := by simp only [x]; linarith
      rcases ofSeq_surjective x with ⟨r, hrx⟩
      rw [← hrx] at hx_lt1 ⊢
      have hr_lt1 : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), r k < 1 := ofSeq_lt_ofSeq.1 hx_lt1
      exact Germ.coe_eq.2 (hr_lt1.mono fun k hk ↦ by simp [powLimitFun, hk.ne])
    have hclose := hcont x hx_mem hx_close
    rw [hfx_eq, show powLimitFun 1 = 1 by simp [powLimitFun]] at hclose
    have h01 : (0 : ℝ) = 1 := coe_eq_of_infClose (by simpa using hclose)
    norm_num at h01

/-- Goldblatt §7.12 (p. 87): **Non-uniform convergence of `x ^ n` on `[0, 1]` via Robinson's
Sequential Lemma** (exact formalization of Goldblatt's paragraph on p. 87!):
For `x = 1 - ε/2 ∈ *[0, 1]` (`x ≈ₕ 1`, `x < 1`), `{x ^ n : n ∈ ℕ} ⊆ hal(1)`, so Robinson's
sequential lemma produces an unlimited `N ∈ ℕ*` with `{x ^ K : K ≤ N} ⊆ hal(1)`; in particular
`*F_N(x) ≈ₕ 1 ≉ 0 = *f(x)`, violating Theorem 7.12.2! -/
theorem powFunSeq_not_uniform_via_robinson_lemma :
    (∃ x ∈ starSet (Set.Icc 0 1), x < 1 ∧ x ≈ₕ 1 ∧
      ∃ N : ℕ*, IsUnlimitedNat N ∧
        (∀ K : ℕ*, K ≤ N → starFunSeq powFunSeq K x ≈ₕ 1) ∧
        ¬ (starFunSeq powFunSeq N x ≈ₕ starFun powLimitFun x)) ∧
    ¬ TendstoUniformlyOn powFunSeq powLimitFun atTop (Set.Icc 0 1) := by
  let rSeq : ℕ → ℝ := fun i ↦ 1 - ((i : ℝ) + 2)⁻¹
  let x : ℝ* := ofSeq rSeq
  have hx_mem : x ∈ starSet (Set.Icc 0 1) := by
    refine ofSeq_mem_starSet.2 (Eventually.of_forall fun i ↦ ?_)
    have hd : (1 : ℝ) < (i : ℝ) + 2 := by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    have hinv_lt1 : ((i : ℝ) + 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hd
    have hinv_pos : (0 : ℝ) < ((i : ℝ) + 2)⁻¹ := by positivity
    exact ⟨by linarith, by linarith⟩
  have hx_lt1 : x < 1 := by
    refine ofSeq_lt_ofSeq.2 (Eventually.of_forall fun i ↦ ?_)
    have hinv_pos : (0 : ℝ) < ((i : ℝ) + 2)⁻¹ := by positivity
    change 1 - ((i : ℝ) + 2)⁻¹ < 1
    linarith
  have hx_close1 : x ≈ₕ 1 := by
    refine isInfinitesimal_of_abs_le isInfinitesimal_inv_nat_succ ?_
    have hpos : 0 ≤ ofSeq (fun i : ℕ ↦ ((i : ℝ) + 1)⁻¹) :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun i ↦ by positivity)
    rw [abs_of_nonneg hpos]
    refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun i ↦ ?_)
    change |(1 - ((i : ℝ) + 2)⁻¹) - 1| ≤ ((i : ℝ) + 1)⁻¹
    have h1 : (1 - ((i : ℝ) + 2)⁻¹) - 1 = -((i : ℝ) + 2)⁻¹ := by ring
    rw [h1, abs_neg, abs_of_pos (by positivity)]
    exact inv_anti₀ (by positivity) (by linarith)
  -- For every standard `n : ℕ`, `x ^ n ≈ₕ 1`
  have hx_pow : ∀ n : ℕ, x ^ n ≈ₕ ((1 : ℝ) : ℝ*) := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, Hyperreal.coe_one]
    | succ k ih =>
        have hx1 : x ≈ₕ ((1 : ℝ) : ℝ*) := by simpa using hx_close1
        rw [pow_succ, show ((1 : ℝ) : ℝ*) = ((1 : ℝ) : ℝ*) * ((1 : ℝ) : ℝ*) by push_cast; ring]
        exact InfClose.mul (isLimited_of_infClose_coe ih) (isLimited_of_infClose_coe hx1) ih hx1
  have hstd_pow : ∀ n : ℕ, Germ.map₂ (fun i k ↦ powFunSeq k (rSeq i)) omegaNat (n : ℕ*) ≈ₕ 1 := by
    intro n
    have heq : Germ.map₂ (fun i k ↦ powFunSeq k (rSeq i)) omegaNat (n : ℕ*) = x ^ n :=
      Germ.coe_eq.2 (Eventually.of_forall fun _ ↦ rfl)
    rw [heq]
    simpa using hx_pow n
  obtain ⟨N, hN_unl, hN_halo⟩ :=
    robinson_sequential_lemma (fun i k ↦ powFunSeq k (rSeq i)) 1 hstd_pow
  have hmap_eq : ∀ K : ℕ*,
      Germ.map₂ (fun i k ↦ powFunSeq k (rSeq i)) omegaNat K = starFunSeq powFunSeq K x := by
    intro K
    induction K using Germ.inductionOn with | _ b =>
    rfl
  have hfx0 : starFun powLimitFun x = 0 :=
    Germ.coe_eq.2 ((ofSeq_lt_ofSeq.1 hx_lt1).mono fun i hi ↦ by simp [powLimitFun, hi.ne])
  have hnot_close : ¬ (starFunSeq powFunSeq N x ≈ₕ starFun powLimitFun x) := by
    intro hbad
    have h1 := (hmap_eq N) ▸ hN_halo N le_rfl
    rw [hfx0] at hbad
    have h10 : (1 : ℝ) = 0 := coe_eq_of_infClose (by simpa using h1.symm.trans hbad)
    norm_num at h10
  refine ⟨⟨x, hx_mem, hx_lt1, hx_close1, N, hN_unl, fun K hK ↦ hmap_eq K ▸ hN_halo K hK,
    hnot_close⟩, ?_⟩
  rw [tendstoUniformlyOn_iff_starFunSeq_infClose]
  intro hunif
  exact hnot_close (hunif N hN_unl x hx_mem)

/-- Explicit constructive non-uniform witness for `x ^ n` at `N = omegaNat`:
at `x = ofSeq (fun n ↦ 1 - 1 / (2 * (n + 1))) ∈ *[0, 1]` (`x ≈ₕ 1`, `x < 1`), Bernoulli's
inequality gives `*F_ω(x) ≥ 1 / 2`, whereas `*f(x) = 0`! -/
theorem powFunSeq_omegaNat_explicit_witness :
    ∃ x ∈ starSet (Set.Icc 0 1), x < 1 ∧ x ≈ₕ 1 ∧
      ((1 / 2 : ℝ) : ℝ*) ≤ starFunSeq powFunSeq omegaNat x ∧
      starFun powLimitFun x = 0 := by
  let rSeq : ℕ → ℝ := fun n ↦ 1 - 1 / (2 * ((n : ℝ) + 1))
  let x : ℝ* := ofSeq rSeq
  have hx_mem : x ∈ starSet (Set.Icc 0 1) := by
    refine ofSeq_mem_starSet.2 (Eventually.of_forall fun n ↦ ?_)
    have hd : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hdiv_le : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hd
    have hdiv_pos : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    exact ⟨by linarith, by linarith⟩
  have hx_lt1 : x < 1 := by
    refine ofSeq_lt_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
    have hdiv_pos : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    change 1 - 1 / (2 * ((n : ℝ) + 1)) < 1
    linarith
  have hx_close1 : x ≈ₕ 1 := by
    refine isInfinitesimal_of_abs_le isInfinitesimal_inv_nat_succ ?_
    have hpos : 0 ≤ ofSeq (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ by positivity)
    rw [abs_of_nonneg hpos]
    refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
    change |(1 - 1 / (2 * ((n : ℝ) + 1))) - 1| ≤ ((n : ℝ) + 1)⁻¹
    have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : (1 - 1 / (2 * ((n : ℝ) + 1))) - 1 = -(1 / (2 * ((n : ℝ) + 1))) := by ring
    rw [h1, abs_neg, abs_of_pos (by positivity), ← one_div]
    exact one_div_le_one_div_of_le hd (by linarith)
  have hpow_ge : ((1 / 2 : ℝ) : ℝ*) ≤ starFunSeq powFunSeq omegaNat x := by
    refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun n ↦ ?_)
    change (1 / 2 : ℝ) ≤ (1 - 1 / (2 * ((n : ℝ) + 1))) ^ n
    set t : ℝ := -(1 / (2 * ((n : ℝ) + 1)))
    have ht_ge : -1 ≤ t := by
      have hd : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hle : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hd
      simp only [t]
      linarith
    have hbern := bernoulli_ineq_real ht_ge n
    have hnt : (1 / 2 : ℝ) ≤ 1 + (n : ℝ) * t := by
      have hd : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
      have hquot : (n : ℝ) / (2 * ((n : ℝ) + 1)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hd (by norm_num : (0 : ℝ) < 2)]
        linarith
      simp only [t]
      linarith [show (n : ℝ) * -(1 / (2 * ((n : ℝ) + 1))) = -((n : ℝ) / (2 * ((n : ℝ) + 1))) by ring]
    simpa [t, sub_eq_add_neg] using hnt.trans hbern
  have hfx0 : starFun powLimitFun x = 0 :=
    Germ.coe_eq.2 ((ofSeq_lt_ofSeq.1 hx_lt1).mono fun n hn ↦ by simp [powLimitFun, hn.ne])
  exact ⟨x, hx_mem, hx_lt1, hx_close1, hpow_ge, hfx0⟩

/-! ## §7.13–7.14 Continuity of a Uniform Limit & Extended Hypersequence Continuity -/

/-- Goldblatt §7.13, Theorem 7.13.1 (pp. 87–88) — **First Proof (`ε / 4 + infinitesimal + ε / 4`)**:
If every `F n` is continuous on `A ⊆ ℝ` and `F` converges uniformly to `f` on `A`, then `f` is
continuous on `A`! -/
theorem continuousOn_of_tendstoUniformlyOn_hybrid {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {A : Set ℝ}
    (hcont : ∀ n : ℕ, ContinuousOn (F n) A)
    (hunif : TendstoUniformlyOn F f atTop A) :
    ContinuousOn f A := by
  rw [tendstoUniformlyOn_iff_epsDelta] at hunif
  rw [continuousOn_iff_infClose]
  intro c hc x hxA hxc ε hε
  obtain ⟨m, hm⟩ := hunif (ε / 4) (by positivity)
  set n : ℕ := m + 1
  -- Transfer `∀ t ∈ A, |F n t - f t| < ε / 4` to `x ∈ starSet A`
  have hFnx : |starFun (F n) x - starFun f x| < ((ε / 4 : ℝ) : ℝ*) := by
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    exact ofSeq_lt_ofSeq.2 (hxA.mono fun k hk ↦ hm n (Nat.le_succ m) (r k) hk)
  have hFnc : |(F n c : ℝ*) - (f c : ℝ*)| < ((ε / 4 : ℝ) : ℝ*) := by
    have hreal : |F n c - f c| < ε / 4 := hm n (Nat.le_succ m) c hc
    simpa [Hyperreal.coe_sub, Hyperreal.coe_abs] using Hyperreal.coe_lt_coe.2 hreal
  -- Middle term `|*F_n(x) - F_n(c)|` is infinitesimal since `F n` is continuous at `c`
  have hmid : |starFun (F n) x - (F n c : ℝ*)| < ((ε / 4 : ℝ) : ℝ*) :=
    ((continuousOn_iff_infClose.1 (hcont n)) c hc x hxA hxc) (ε / 4) (by positivity)
  -- Equation (x) in Goldblatt p. 88: triangle inequality across the three terms
  have htri : |starFun f x - (f c : ℝ*)| ≤
      |starFun f x - starFun (F n) x| + |starFun (F n) x - (F n c : ℝ*)| +
        |(F n c : ℝ*) - (f c : ℝ*)| := by
    have h1 : starFun f x - (f c : ℝ*) =
        ((starFun f x - starFun (F n) x) + (starFun (F n) x - (F n c : ℝ*))) +
          ((F n c : ℝ*) - (f c : ℝ*)) := by ring
    rw [h1]
    have ha := abs_add_le ((starFun f x - starFun (F n) x) + (starFun (F n) x - (F n c : ℝ*)))
      ((F n c : ℝ*) - (f c : ℝ*))
    have hb := abs_add_le (starFun f x - starFun (F n) x) (starFun (F n) x - (F n c : ℝ*))
    linarith
  rw [abs_sub_comm (starFun f x) (starFun (F n) x)] at htri
  have hsum_lt : |starFun (F n) x - starFun f x| + |starFun (F n) x - (F n c : ℝ*)| +
      |(F n c : ℝ*) - (f c : ℝ*)| < (ε : ℝ*) := by
    have h34 : ((ε / 4 : ℝ) : ℝ*) + ((ε / 4 : ℝ) : ℝ*) + ((ε / 4 : ℝ) : ℝ*) < (ε : ℝ*) := by
      have : ε / 4 + ε / 4 + ε / 4 < ε := by linarith
      simpa [Hyperreal.coe_add] using Hyperreal.coe_lt_coe.2 this
    exact (add_lt_add (add_lt_add hFnx hmid) hFnc).trans h34
  exact htri.trans_lt hsum_lt

/-- Goldblatt §7.14, Theorem 7.14.1 (p. 89): **Infinitesimal Continuity in the Extended
Hypersequence!**
If `(F n : n ∈ ℕ)` are all continuous on `A ⊆ ℝ`, then for ANY `N ∈ ℕ*` (even unlimited!) and ANY
`y ∈ *A`, there exists a positive infinitesimal `d` such that `*F_N(x) ≈ₕ *F_N(y)` for all
`x ∈ *A` with `|x - y| < d`! -/
theorem exists_posInfinitesimal_starFunSeq_infClose {F : ℕ → ℝ → ℝ} {A : Set ℝ}
    (hcont : ∀ n : ℕ, ContinuousOn (F n) A) (N : ℕ*) {y : ℝ*} (hy : y ∈ starSet A) :
    ∃ d : ℝ*, IsPosInfinitesimal d ∧
      ∀ x ∈ starSet A, |x - y| < d → starFunSeq F N x ≈ₕ starFunSeq F N y := by
  induction N using Germ.inductionOn with | _ a =>
  rcases ofSeq_surjective y with ⟨s, rfl⟩
  -- At each index `k` with `s k ∈ A`, choose `δ_k > 0` for `F (a k)` at `s k` with `ε_k = (k + 1)⁻¹`
  have hex_δ : ∀ k : ℕ, s k ∈ A → ∃ δ : ℝ, 0 < δ ∧
      ∀ t ∈ A, |t - s k| < δ → |F (a k) t - F (a k) (s k)| < ((k : ℝ) + 1)⁻¹ := by
    intro k hk
    exact (continuousWithinAt_iff_epsDelta.1 (hcont (a k) (s k) hk))
      ((k : ℝ) + 1)⁻¹ (by positivity)
  let δSeq : ℕ → ℝ := fun k ↦ if hk : s k ∈ A then (hex_δ k hk).choose else 1
  have hδ_pos : ∀ k : ℕ, 0 < δSeq k := by
    intro k
    by_cases hk : s k ∈ A
    · simp only [δSeq, hk, ↓reduceDIte]
      exact (hex_δ k hk).choose_spec.1
    · simp [δSeq, hk]
  -- Replace `δ` by the positive infinitesimal `d_k = min (δ_k / 2) ((k + 1)⁻¹)` (Goldblatt p. 89!)
  let dSeq : ℕ → ℝ := fun k ↦ min (δSeq k / 2) ((k : ℝ) + 1)⁻¹
  refine ⟨ofSeq dSeq, ⟨?_, ?_⟩, ?_⟩
  · exact ofSeq_lt_ofSeq.2 (Eventually.of_forall fun k ↦
      lt_min (half_pos (hδ_pos k)) (by positivity))
  · intro r hr
    have hle : ofSeq dSeq ≤ ofSeq (fun k : ℕ ↦ ((k : ℝ) + 1)⁻¹) :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun k ↦ min_le_right _ _)
    have hlt := isPosInfinitesimal_inv_nat_succ.2 r hr
    exact hle.trans_lt hlt
  · intro x hxA hlt_d
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hr_lt : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), |r k - s k| < dSeq k :=
      ofSeq_lt_ofSeq.1 hlt_d
    refine isInfinitesimal_of_abs_le isInfinitesimal_inv_nat_succ ?_
    have hpos : 0 ≤ ofSeq (fun k : ℕ ↦ ((k : ℝ) + 1)⁻¹) :=
      ofSeq_le_ofSeq.2 (Eventually.of_forall fun k ↦ by positivity)
    rw [abs_of_nonneg hpos]
    refine ofSeq_le_ofSeq.2 (((hxA.and hy).and hr_lt).mono fun k ⟨⟨hkr, hks⟩, hkd⟩ ↦ ?_)
    change |F (a k) (r k) - F (a k) (s k)| ≤ ((k : ℝ) + 1)⁻¹
    have hlt_δk : |r k - s k| < δSeq k := by
      have h1 : dSeq k ≤ δSeq k / 2 := min_le_left _ _
      exact (hkd.trans_le h1).trans (half_lt_self (hδ_pos k))
    simp only [δSeq, hks, ↓reduceDIte] at hlt_δk
    exact ((hex_δ k hks).choose_spec.2 (r k) hkr hlt_δk).le

/-- Goldblatt §7.14 (pp. 89–90): **Purely Nonstandard Proof of Theorem 7.13.1** (Uniform Limit of
Continuous Functions is Continuous) via the 3-step `≈ₕ` chain
`*f(x) ≈ₕ *F_ω(x) ≈ₕ *F_ω(c) ≈ₕ f(c)`, combining Theorem 7.14.1, Theorem 7.12.2, and
Theorem 7.1.3(3)! -/
theorem continuousOn_of_tendstoUniformlyOn_nonstandard {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {A : Set ℝ}
    (hcont : ∀ n : ℕ, ContinuousOn (F n) A)
    (hunif : TendstoUniformlyOn F f atTop A) :
    ContinuousOn f A := by
  have hunif' := (tendstoUniformlyOn_iff_starFunSeq_infClose.1 hunif)
    omegaNat isUnlimitedNat_omegaNat
  intro c hc
  rw [continuousWithinAt_iff_exists_posInfinitesimal]
  obtain ⟨d, hd_inf, hd⟩ :=
    exists_posInfinitesimal_starFunSeq_infClose hcont omegaNat (coe_mem_starSet.2 hc)
  refine ⟨d, hd_inf, fun x hxA hxd ↦ ?_⟩
  have h1 : starFun f x ≈ₕ starFunSeq F omegaNat x := (hunif' x hxA).symm
  have h2 : starFunSeq F omegaNat x ≈ₕ starFunSeq F omegaNat (c : ℝ*) := hd x hxA hxd
  have h3 : starFunSeq F omegaNat (c : ℝ*) ≈ₕ (f c : ℝ*) := by
    simpa using hunif' (c : ℝ*) (coe_mem_starSet.2 hc)
  exact h1.trans (h2.trans h3)

/-! ## §7.15 Was Cauchy Right? Series of Continuous Functions & Cauchy's Sum Theorem -/

/-- Partial sum `partialSumFun u n x = ∑_{k < n} u k x` of a series of functions `u : ℕ → ℝ → ℝ`. -/
def partialSumFun (u : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.range n).sum (fun k ↦ u k x)

/-- Finite partial sums of functions continuous on `A` are continuous on `A`. -/
theorem continuousOn_partialSumFun {u : ℕ → ℝ → ℝ} {A : Set ℝ}
    (hu : ∀ k : ℕ, ContinuousOn (u k) A) (n : ℕ) :
    ContinuousOn (partialSumFun u n) A := by
  induction n with
  | zero =>
      have heq : partialSumFun u 0 = fun _ ↦ 0 := by ext; simp [partialSumFun]
      rw [heq]
      exact continuousOn_const
  | succ k ih =>
      intro x hx
      have heq : partialSumFun u (k + 1) = fun t ↦ partialSumFun u k t + u k t := by
        ext t
        simp [partialSumFun, Finset.sum_range_succ]
      rw [heq]
      exact continuousWithinAt_add_nonstandard (ih x hx) (hu k x hx)

/-- Classical geometric-telescoping series counterexample `u_k(x) = (1 - x) x^k` on `[0, 1]`
(illustrating why the standard reading of Cauchy's 1821 sum theorem fails without uniform or
halo convergence, §7.15, p. 90). -/
def cauchySeriesTerm (k : ℕ) (x : ℝ) : ℝ := (1 - x) * x ^ k

/-- Sum function of `∑_{k=0}^∞ (1 - x) x^k` on `[0, 1]`: `1` on `[0, 1)` and `0` at `x = 1`. -/
def cauchySeriesSum (x : ℝ) : ℝ := if x = 1 then 0 else 1

/-- Telescoping identity `∑_{k < n} (1 - x) x^k = 1 - x^n`. -/
theorem partialSumFun_cauchySeriesTerm (n : ℕ) (x : ℝ) :
    partialSumFun cauchySeriesTerm n x = 1 - x ^ n := by
  induction n with
  | zero => simp [partialSumFun]
  | succ k ih =>
      simp only [partialSumFun, Finset.sum_range_succ, cauchySeriesTerm] at ih ⊢
      rw [ih]
      ring

/-- Every term `cauchySeriesTerm k` is continuous on `[0, 1]` and the series converges pointwise on
`[0, 1]` to `cauchySeriesSum`, yet `cauchySeriesSum` is discontinuous at `x = 1`! -/
theorem cauchySeries_counterexample :
    (∀ k : ℕ, ContinuousOn (cauchySeriesTerm k) (Set.Icc 0 1)) ∧
    (∀ x ∈ Set.Icc 0 1,
      Tendsto (fun n ↦ partialSumFun cauchySeriesTerm n x) atTop (𝓝 (cauchySeriesSum x))) ∧
    ¬ ContinuousWithinAt cauchySeriesSum (Set.Icc 0 1) 1 := by
  refine ⟨fun k ↦ ((continuous_const.sub continuous_id).mul (continuous_pow k)).continuousOn,
    ?_, ?_⟩
  · intro x hx
    simp only [partialSumFun_cauchySeriesTerm]
    rcases eq_or_lt_of_le hx.2 with rfl | hlt1
    · simp [cauchySeriesSum]
    · have hsum : cauchySeriesSum x = 1 := by simp [cauchySeriesSum, hlt1.ne]
      rw [hsum]
      simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one hx.1 hlt1)
  · have heq : cauchySeriesSum = fun x ↦ 1 - powLimitFun x := by
      ext x
      by_cases hx : x = 1 <;> simp [cauchySeriesSum, powLimitFun, hx]
    intro hcont
    apply powFunSeq_continuous_pointwise_and_limit_discontinuous.2.2
    have hpow : powLimitFun = fun x ↦ 1 - cauchySeriesSum x := by
      ext x
      rw [heq]
      ring
    rw [hpow]
    exact continuousWithinAt_sub_nonstandard continuousWithinAt_const hcont

/-- Goldblatt §7.15 (p. 90) — **Cauchy's 1821 Sum Theorem Vindicated** (Robinson / Cleave 1971 /
Lakatos 1978):
If each term `u k` of the series `u₀ + u₁ + …` is continuous on `A ⊆ ℝ`, and in the infinitesimal
neighborhood `hal(c) ∩ *A` of `c ∈ A` the extended partial sum `*S_N(x)` (for some unlimited
`N ∈ ℕ*`) is infinitely close to `*s(x)`, then the sum `s` IS continuous within `A` at `c`! -/
theorem cauchy_sum_theorem_nonstandard {u : ℕ → ℝ → ℝ} {s : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (hc : c ∈ A) (hu : ∀ k : ℕ, ContinuousOn (u k) A)
    {N : ℕ*} (_hN : IsUnlimitedNat N)
    (hconv_halo : ∀ x ∈ starSet A, x ≈ₕ (c : ℝ*) →
      starFunSeq (partialSumFun u) N x ≈ₕ starFun s x) :
    ContinuousWithinAt s A c := by
  rw [continuousWithinAt_iff_exists_posInfinitesimal]
  obtain ⟨d, hd_inf, hd⟩ := exists_posInfinitesimal_starFunSeq_infClose
    (continuousOn_partialSumFun hu) N (coe_mem_starSet.2 hc)
  refine ⟨d, hd_inf, fun x hxA hxd ↦ ?_⟩
  have hxc : x ≈ₕ (c : ℝ*) :=
    isInfinitesimal_of_abs_le (isInfinitesimal_iff_trichotomy.2 (Or.inl hd_inf))
      (hxd.le.trans (le_abs_self d))
  have h1 : starFun s x ≈ₕ starFunSeq (partialSumFun u) N x := (hconv_halo x hxA hxc).symm
  have h2 : starFunSeq (partialSumFun u) N x ≈ₕ starFunSeq (partialSumFun u) N (c : ℝ*) :=
    hd x hxA hxd
  have h3 : starFunSeq (partialSumFun u) N (c : ℝ*) ≈ₕ (s c : ℝ*) := by
    simpa using hconv_halo (c : ℝ*) (coe_mem_starSet.2 hc) (InfClose.refl _)
  exact h1.trans (h2.trans h3)

end Goldblatt.Ch07
end
