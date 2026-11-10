import LecturesOnTheHyperreals.Ch05_HyperrealsGreatAndSmall
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.ClusterPt
import Mathlib.Data.EReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Chapter 6: Convergence of Sequences and Series

Formalization of Robert Goldblatt, *Lectures on the Hyperreals*, Chapter 6 (pp. 61–74):

* **§6.1** Enlarging sequences (`starSeq`), the extended tail (`extendedTail`), nonstandard
  underflow/overspill principles on `ℕ*`, and the nonstandard characterization of convergence
  (Theorem 6.1.1), plus basic sequences and subsequences.
* **§6.2** Monotone Convergence Theorem via shadows of extended terms (Theorem 6.2.1) and the
  nonstandard proof that `c ^ n → 0` for `|c| < 1`.
* **§6.3** Uniqueness of limits, algebraic and order properties of limits (Theorem 6.3.1,
  Exercise 6.7(1)), absolute values, square roots, and the Squeeze/Sandwich Theorem
  (Exercise 6.7(2)).
* **§6.4** Nonstandard characterizations of boundedness, upper/lower boundedness, and divergence
  to `±∞` (Theorems 6.4.1–6.4.2).
* **§6.5** Nonstandard characterization of Cauchy sequences (Theorem 6.5.1) and Cauchy's
  Convergence Criterion via `shadow (starSeq s omegaNat)` (Theorem 6.5.2).
* **§6.6–6.7** Sequential, filter (`MapClusterPt`), subsequence, and nonstandard characterizations
  of cluster points (Theorem 6.6.1), the Bolzano–Weierstrass Theorem (Theorem 6.6.2), and
  Exercises 6.7(3)–(4) (including unbounded counterexample with a unique cluster point).
* **§6.8–6.9** The cluster-point set `clusterSet` (closed, nonempty, bounded for bounded sequences),
  `seqLimsup` and `seqLiminf` as greatest/least cluster points (Exercise 6.8.1), nonstandard and
  `ε`-characterizations (Theorems 6.8.2–6.8.4), tail-supremum/infimum limit formulas
  (Theorem 6.8.5), extended-real `erealSeqLimsup`/`erealSeqLiminf`, and Exercises 6.9(1)–(3).
* **§6.10–6.11** Infinite series (`partialSum`, `SeriesConvergesTo`, `SeriesConverges`,
  `SeriesAbsConverges`), hyperfinite partial sums and the nonstandard Cauchy tail criterion,
  vanishing general term, Oresme's divergence proof for the harmonic series, comparison and limit
  comparison tests, geometric series, D'Alembert's ratio test (convergence & divergence),
  infinitesimality of `x ^ N / N!`, and Leibniz's alternating series test (Exercises 6.11(1)–(11)).
-/

noncomputable section

namespace Goldblatt.Ch06

open Filter
open Hyperreal (ofSeq ofSeq_lt_ofSeq ofSeq_le_ofSeq ofSeq_surjective)
open scoped Topology Classical BigOperators

/-! ## §6.1 Enlarging Sequences, Transfer Principles on `ℕ*`, and Convergence -/

/-- Constant hypersequence evaluation: `starSeq (fun _ ↦ c) N = (c : ℝ*)`. -/
@[simp]
theorem starSeq_const (c : ℝ) (N : ℕ*) :
    starSeq (fun _ : ℕ ↦ c) N = (c : ℝ*) :=
  Germ.inductionOn N fun _ ↦ rfl

/-- Negation of a hypersequence. -/
theorem starSeq_neg (s : ℕ → ℝ) (N : ℕ*) :
    starSeq (fun n ↦ -s n) N = -starSeq s N :=
  Germ.inductionOn N fun _ ↦ rfl

/-- Scalar multiplication of a hypersequence. -/
theorem starSeq_const_mul (c : ℝ) (s : ℕ → ℝ) (N : ℕ*) :
    starSeq (fun n ↦ c * s n) N = (c : ℝ*) * starSeq s N :=
  Germ.inductionOn N fun _ ↦ rfl

/-- Quotient of two hypersequences. -/
theorem starSeq_div (s t : ℕ → ℝ) (N : ℕ*) :
    starSeq (fun n ↦ s n / t n) N = starSeq s N / starSeq t N :=
  Germ.inductionOn N fun _ ↦ rfl

/-- Natural power of a hypersequence. -/
theorem starSeq_pow (s : ℕ → ℝ) (k : ℕ) (N : ℕ*) :
    starSeq (fun n ↦ s n ^ k) N = starSeq s N ^ k := by
  induction k with
  | zero =>
      simp [pow_zero]
  | succ m ih =>
      simp only [pow_succ, starSeq_mul, ih]

/-- Composition of `starSeq s` with a lifted index map `φ : ℕ → ℕ`. -/
theorem starSeq_comp (s : ℕ → ℝ) (φ : ℕ → ℕ) (N : ℕ*) :
    starSeq (s ∘ φ) N = starSeq s (Germ.map φ N) :=
  Germ.inductionOn N fun _ ↦ rfl

/-- Pointwise order `∀ n, s n ≤ t n` lifts to `starSeq s N ≤ starSeq t N` for all `N ∈ ℕ*`. -/
theorem starSeq_le_of_forall_le {s t : ℕ → ℝ} (h : ∀ n : ℕ, s n ≤ t n) (N : ℕ*) :
    starSeq s N ≤ starSeq t N := by
  induction N using Germ.inductionOn with | _ a =>
  exact ofSeq_le_ofSeq.2 (Eventually.of_forall fun i ↦ h (a i))

/-- Pointwise upper bound `∀ n, s n ≤ b` lifts to `starSeq s N ≤ (b : ℝ*)`. -/
theorem starSeq_le_coe_of_forall_le {s : ℕ → ℝ} {b : ℝ} (h : ∀ n : ℕ, s n ≤ b) (N : ℕ*) :
    starSeq s N ≤ (b : ℝ*) := by
  simpa using starSeq_le_of_forall_le h N

/-- Pointwise lower bound `∀ n, a ≤ s n` lifts to `(a : ℝ*) ≤ starSeq s N`. -/
theorem coe_le_starSeq_of_forall_le {s : ℕ → ℝ} {a : ℝ} (h : ∀ n : ℕ, a ≤ s n) (N : ℕ*) :
    (a : ℝ*) ≤ starSeq s N := by
  simpa using starSeq_le_of_forall_le h N

/-- Eventual order `∀ n ≥ k, s n ≤ t n` lifts along `(k : ℕ*) ≤ N`. -/
theorem starSeq_le_of_le_of_eventually_le {s t : ℕ → ℝ} {k : ℕ}
    (h : ∀ n : ℕ, k ≤ n → s n ≤ t n) {N : ℕ*} (hN : (k : ℕ*) ≤ N) :
    starSeq s N ≤ starSeq t N := by
  induction N using Germ.inductionOn with | _ a =>
  exact ofSeq_le_ofSeq.2 ((Germ.coe_le.1 hN).mono fun i hi ↦ h (a i) hi)

/-- Monotonicity of `s : ℕ → ℝ` lifts to `starSeq s : ℕ* → ℝ*`. -/
theorem starSeq_mono {s : ℕ → ℝ} (hs : Monotone s) {M N : ℕ*} (hMN : M ≤ N) :
    starSeq s M ≤ starSeq s N := by
  induction M using Germ.inductionOn with | _ a =>
  induction N using Germ.inductionOn with | _ b =>
  exact ofSeq_le_ofSeq.2 ((Germ.coe_le.1 hMN).mono fun i hi ↦ hs hi)

/-- Antitonicity of `s : ℕ → ℝ` lifts to `starSeq s : ℕ* → ℝ*`. -/
theorem starSeq_anti {s : ℕ → ℝ} (hs : Antitone s) {M N : ℕ*} (hMN : M ≤ N) :
    starSeq s N ≤ starSeq s M := by
  induction M using Germ.inductionOn with | _ a =>
  induction N using Germ.inductionOn with | _ b =>
  exact ofSeq_le_ofSeq.2 ((Germ.coe_le.1 hMN).mono fun i hi ↦ hs hi)

/-- Every hypernatural `N ∈ ℕ*` is nonnegative (`0 ≤ N`). -/
theorem zero_le_hypernat (N : ℕ*) : (0 : ℕ*) ≤ N := by
  induction N using Germ.inductionOn with | _ a =>
  exact Germ.coe_le.2 (Eventually.of_forall fun i ↦ Nat.zero_le (a i))

/-- `M ≤ M + K` in `ℕ*`. -/
theorem le_add_right_hypernat (M K : ℕ*) : M ≤ M + K := by
  induction M using Germ.inductionOn with | _ a =>
  induction K using Germ.inductionOn with | _ b =>
  exact Germ.coe_le.2 (Eventually.of_forall fun i ↦ Nat.le_add_right (a i) (b i))

/-- Upward closure of `IsUnlimitedNat`: if `M` is unlimited and `M ≤ N`, then `N` is unlimited. -/
theorem isUnlimitedNat_of_le {M N : ℕ*} (hM : IsUnlimitedNat M) (hMN : M ≤ N) :
    IsUnlimitedNat N :=
  fun n ↦ (hM n).trans_le hMN

/-- Adding any hypernatural `K` to an unlimited hypernatural `M` yields an unlimited hypernatural. -/
theorem isUnlimitedNat_add_right {M : ℕ*} (hM : IsUnlimitedNat M) (K : ℕ*) :
    IsUnlimitedNat (M + K) :=
  isUnlimitedNat_of_le hM (le_add_right_hypernat M K)

/-- Multiplying an unlimited hypernatural by a positive standard integer yields an unlimited
hypernatural. -/
theorem isUnlimitedNat_mul_left {k : ℕ} (hk : 1 ≤ k) {N : ℕ*} (hN : IsUnlimitedNat N) :
    IsUnlimitedNat ((k : ℕ*) * N) := by
  refine isUnlimitedNat_of_le hN ?_
  induction N using Germ.inductionOn with | _ a =>
  exact Germ.coe_le.2 (Eventually.of_forall fun i ↦ Nat.le_mul_of_pos_left (a i) hk)

/-- A strictly monotone map `φ : ℕ → ℕ` sends unlimited hypernaturals to unlimited hypernaturals. -/
theorem isUnlimitedNat_map_of_strictMono {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {N : ℕ*} (hN : IsUnlimitedNat N) : IsUnlimitedNat (Germ.map φ N) := by
  refine isUnlimitedNat_of_le hN ?_
  induction N using Germ.inductionOn with | _ a =>
  exact Germ.coe_le.2 (Eventually.of_forall fun i ↦ hφ.id_le (a i))

/-- Ultrafilter negation law for predicates lifted to `ℕ*`. -/
theorem liftPred_not_iff {P : ℕ → Prop} {N : ℕ*} :
    Germ.LiftPred (fun n ↦ ¬ P n) N ↔ ¬ Germ.LiftPred P N := by
  induction N using Germ.inductionOn with | _ a =>
  exact Ultrafilter.eventually_not

/-- **Goldblatt §6.8 Principle (a) (p. 69)**: A standard predicate `P : ℕ → Prop` holds for all
unlimited `N ∈ *ℕ_∞` if and only if `P` holds on some standard tail `{n ∈ ℕ | k ≤ n}`. -/
theorem forall_isUnlimitedNat_liftPred_iff {P : ℕ → Prop} :
    (∀ N : ℕ*, IsUnlimitedNat N → Germ.LiftPred P N) ↔ ∃ k : ℕ, ∀ n : ℕ, k ≤ n → P n := by
  constructor
  · intro h
    by_contra hnot
    push Not at hnot
    choose a ha using hnot
    have hle : omegaNat ≤ (a : ℕ*) :=
      Germ.coe_le.2 (Eventually.of_forall fun k ↦ (ha k).1)
    have hunl : IsUnlimitedNat (a : ℕ*) := isUnlimitedNat_of_le isUnlimitedNat_omegaNat hle
    have hP : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), P (a k) := h (a : ℕ*) hunl
    have hnP : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), ¬ P (a k) :=
      Eventually.of_forall fun k ↦ (ha k).2
    obtain ⟨k, hPk, hnPk⟩ := (hP.and hnP).exists
    exact hnPk hPk
  · rintro ⟨k, hk⟩ N hN
    induction N using Germ.inductionOn with | _ a =>
    exact (Germ.coe_lt.1 (hN k)).mono fun i hi ↦ hk (a i) hi.le

/-- **Goldblatt §6.8 Principle (b) (p. 69)**: A standard predicate `P : ℕ → Prop` holds for at
least one unlimited `N ∈ *ℕ_∞` if and only if `P` holds for arbitrarily large `n ∈ ℕ`. -/
theorem exists_isUnlimitedNat_liftPred_iff {P : ℕ → Prop} :
    (∃ N : ℕ*, IsUnlimitedNat N ∧ Germ.LiftPred P N) ↔ ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ P n := by
  have h := forall_isUnlimitedNat_liftPred_iff (P := fun n ↦ ¬ P n)
  constructor
  · rintro ⟨N, hN, hPN⟩ k
    by_contra hno
    push Not at hno
    have hall : ∀ M : ℕ*, IsUnlimitedNat M → Germ.LiftPred (fun n ↦ ¬ P n) M :=
      h.2 ⟨k, hno⟩
    exact (liftPred_not_iff.1 (hall N hN)) hPN
  · intro hfreq
    by_contra hnone
    push Not at hnone
    have hall : ∀ N : ℕ*, IsUnlimitedNat N → Germ.LiftPred (fun n ↦ ¬ P n) N :=
      fun N hN ↦ liftPred_not_iff.2 (hnone N hN)
    obtain ⟨k, hk⟩ := h.1 hall
    obtain ⟨n, hkn, hPn⟩ := hfreq k
    exact hk n hkn hPn

/-- Binary transfer principle on `*ℕ_∞ × *ℕ_∞`: a binary relation `R : ℕ → ℕ → Prop` holds for all
unlimited `M, N ∈ *ℕ_∞` iff `R m n` holds for all sufficiently large `m, n ∈ ℕ`. -/
theorem forall_isUnlimitedNat₂_liftRel_iff {R : ℕ → ℕ → Prop} :
    (∀ M N : ℕ*, IsUnlimitedNat M → IsUnlimitedNat N → Germ.LiftRel R M N) ↔
      ∃ k : ℕ, ∀ m n : ℕ, k ≤ m → k ≤ n → R m n := by
  constructor
  · intro h
    by_contra hnot
    push Not at hnot
    choose a b hab using hnot
    have ha_unl : IsUnlimitedNat (a : ℕ*) :=
      isUnlimitedNat_of_le isUnlimitedNat_omegaNat
        (Germ.coe_le.2 (Eventually.of_forall fun k ↦ (hab k).1))
    have hb_unl : IsUnlimitedNat (b : ℕ*) :=
      isUnlimitedNat_of_le isUnlimitedNat_omegaNat
        (Germ.coe_le.2 (Eventually.of_forall fun k ↦ (hab k).2.1))
    have hR : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), R (a k) (b k) := h (a : ℕ*) (b : ℕ*) ha_unl hb_unl
    have hnR : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), ¬ R (a k) (b k) :=
      Eventually.of_forall fun k ↦ (hab k).2.2
    obtain ⟨k, hRk, hnRk⟩ := (hR.and hnR).exists
    exact hnRk hRk
  · rintro ⟨k, hk⟩ M N hM hN
    induction M using Germ.inductionOn with | _ a =>
    induction N using Germ.inductionOn with | _ b =>
    exact ((Germ.coe_lt.1 (hM k)).and (Germ.coe_lt.1 (hN k))).mono
      fun i ⟨hia, hib⟩ ↦ hk (a i) (b i) hia.le hib.le

/-- Expressing `|starSeq s N - (L : ℝ*)| < (ε : ℝ*)` as `Germ.LiftPred`. -/
theorem starSeq_abs_sub_lt_iff (s : ℕ → ℝ) (L ε : ℝ) (N : ℕ*) :
    |starSeq s N - (L : ℝ*)| < (ε : ℝ*) ↔ Germ.LiftPred (fun n ↦ |s n - L| < ε) N := by
  induction N using Germ.inductionOn with | _ a =>
  exact ofSeq_lt_ofSeq

/-- Expressing `|starSeq s M - starSeq s N| < (ε : ℝ*)` as `Germ.LiftRel`. -/
theorem starSeq_abs_sub_starSeq_lt_iff (s : ℕ → ℝ) (ε : ℝ) (M N : ℕ*) :
    |starSeq s M - starSeq s N| < (ε : ℝ*) ↔ Germ.LiftRel (fun m n ↦ |s m - s n| < ε) M N := by
  induction M using Germ.inductionOn with | _ a =>
  induction N using Germ.inductionOn with | _ b =>
  exact ofSeq_lt_ofSeq

/-- Goldblatt Chapter 6 intro (p. 61): The extended tail `{s_N | N ∈ *ℕ_∞}` of a real sequence `s`. -/
def extendedTail (s : ℕ → ℝ) : Set ℝ* :=
  {x : ℝ* | ∃ N : ℕ*, IsUnlimitedNat N ∧ x = starSeq s N}

/-- Goldblatt §6.1 (p. 61): Classical `ε`-`m` definition of convergence of `s : ℕ → ℝ` to `L : ℝ`. -/
def SeqConvergesTo (s : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → |s n - L| < ε

/-- Equivalence between `m ≤ n` and Goldblatt's `m < n` formulation of convergence (p. 61). -/
theorem seqConvergesTo_iff_strict {s : ℕ → ℝ} {L : ℝ} :
    SeqConvergesTo s L ↔ ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ∀ n : ℕ, m < n → |s n - L| < ε := by
  constructor
  · intro h ε hε
    obtain ⟨m, hm⟩ := h ε hε
    exact ⟨m, fun n hn ↦ hm n hn.le⟩
  · intro h ε hε
    obtain ⟨m, hm⟩ := h ε hε
    exact ⟨m + 1, fun n hn ↦ hm n (Nat.lt_of_succ_le hn)⟩

/-- Equivalence between Mathlib's `Tendsto s atTop (𝓝 L)` and `SeqConvergesTo s L`. -/
theorem tendsto_nhds_iff_seqConvergesTo {s : ℕ → ℝ} {L : ℝ} :
    Tendsto s atTop (𝓝 L) ↔ SeqConvergesTo s L := by
  rw [Metric.tendsto_atTop]
  simp only [Real.dist_eq, SeqConvergesTo]

/-- **Goldblatt Theorem 6.1.1 (pp. 61–62)**: `SeqConvergesTo s L` holds if and only if
`starSeq s N ≈ₕ (L : ℝ*)` for every unlimited hypernatural `N ∈ *ℕ_∞`. -/
theorem seqConvergesTo_iff_forall_unlimited_infClose {s : ℕ → ℝ} {L : ℝ} :
    SeqConvergesTo s L ↔ ∀ N : ℕ*, IsUnlimitedNat N → starSeq s N ≈ₕ (L : ℝ*) := by
  unfold SeqConvergesTo InfClose IsInfinitesimal
  constructor
  · intro h N hN ε hε
    exact (starSeq_abs_sub_lt_iff s L ε N).2
      ((forall_isUnlimitedNat_liftPred_iff (P := fun n ↦ |s n - L| < ε)).2 (h ε hε) N hN)
  · intro h ε hε
    refine (forall_isUnlimitedNat_liftPred_iff (P := fun n ↦ |s n - L| < ε)).1 fun N hN ↦ ?_
    exact (starSeq_abs_sub_lt_iff s L ε N).1 (h N hN ε hε)

/-- **Goldblatt Theorem 6.1.1 (pp. 61–62)** (Mathlib `Tendsto` formulation):
A sequence `s : ℕ → ℝ` converges to `L ∈ ℝ` if and only if `starSeq s N ≈ₕ (L : ℝ*)` for every
unlimited hypernatural `N ∈ *ℕ_∞`. -/
theorem tendsto_nhds_iff_forall_unlimited_infClose {s : ℕ → ℝ} {L : ℝ} :
    Tendsto s atTop (𝓝 L) ↔ ∀ N : ℕ*, IsUnlimitedNat N → starSeq s N ≈ₕ (L : ℝ*) :=
  tendsto_nhds_iff_seqConvergesTo.trans seqConvergesTo_iff_forall_unlimited_infClose

/-- Goldblatt §6.1 (p. 62): `s` converges to `L` iff its extended tail is contained in `halo L`. -/
theorem tendsto_nhds_iff_extendedTail_subset_halo {s : ℕ → ℝ} {L : ℝ} :
    Tendsto s atTop (𝓝 L) ↔ extendedTail s ⊆ halo (L : ℝ*) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose]
  constructor
  · rintro h _ ⟨N, hN, rfl⟩
    exact (h N hN).symm
  · intro h N hN
    exact (h ⟨N, hN, rfl⟩).symm

/-- Shadow characterization of convergence: `s → L` iff every extended term is limited with
shadow `L`. -/
theorem tendsto_nhds_iff_forall_unlimited_shadow {s : ℕ → ℝ} {L : ℝ} :
    Tendsto s atTop (𝓝 L) ↔
      ∀ N : ℕ*, IsUnlimitedNat N → IsLimited (starSeq s N) ∧ shadow (starSeq s N) = L := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose]
  constructor
  · intro h N hN
    have hclose := h N hN
    have hlim : IsLimited (starSeq s N) := by
      have : starSeq s N = (L : ℝ*) + (starSeq s N - (L : ℝ*)) := by ring
      rw [this]
      exact (isLimited_coe L).add hclose.isLimited
    exact ⟨hlim, shadow_eq_of_infClose hclose⟩
  · intro h N hN
    obtain ⟨hlim, hsh⟩ := h N hN
    rw [← hsh]
    exact infClose_shadow hlim

/-- Constant sequences converge to their constant value (nonstandard proof). -/
theorem tendsto_const_nonstandard (c : ℝ) :
    Tendsto (fun _ : ℕ ↦ c) atTop (𝓝 c) :=
  tendsto_nhds_iff_forall_unlimited_infClose.2 fun N _ ↦ by
    rw [starSeq_const]

/-- Nonstandard proof that `1 / (n + 1) → 0`: for unlimited `N`, `N + 1` is unlimited, hence its
reciprocal is infinitesimal. -/
theorem tendsto_one_div_add_one_zero_nonstandard :
    Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose]
  intro N hN
  rw [Hyperreal.coe_zero, infClose_zero_iff]
  have hpos_unl : IsPosUnlimited (Hypernat.toHyperreal N + 1) := fun r ↦ by
    have := isUnlimitedNat_iff_isPosUnlimited.1 hN (r - 1)
    push_cast at this
    linarith
  have hunl : IsUnlimited (Hypernat.toHyperreal N + 1) :=
    isUnlimited_iff_pos_or_neg.2 (Or.inl hpos_unl)
  have heq : starSeq (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) N = (Hypernat.toHyperreal N + 1)⁻¹ := by
    induction N using Germ.inductionOn with | _ a =>
    exact Germ.coe_eq.2 (Eventually.of_forall fun i ↦ one_div ((a i : ℝ) + 1))
  rw [heq]
  exact hunl.inv_isInfinitesimal

/-- Nonstandard proof that `1 / n → 0`. -/
theorem tendsto_one_div_nat_zero_nonstandard :
    Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose]
  intro N hN
  rw [Hyperreal.coe_zero, infClose_zero_iff]
  have hunl : IsUnlimited (Hypernat.toHyperreal N) :=
    isUnlimited_iff_pos_or_neg.2 (Or.inl (isUnlimitedNat_iff_isPosUnlimited.1 hN))
  have heq : starSeq (fun n : ℕ ↦ 1 / (n : ℝ)) N = (Hypernat.toHyperreal N)⁻¹ := by
    induction N using Germ.inductionOn with | _ a =>
    exact Germ.coe_eq.2 (Eventually.of_forall fun i ↦ one_div (a i : ℝ))
  rw [heq]
  exact hunl.inv_isInfinitesimal

/-- Every subsequence `s ∘ φ` (with `StrictMono φ`) of a convergent sequence converges to the
same limit: for unlimited `N`, `Germ.map φ N` is unlimited, so `starSeq (s ∘ φ) N ≈ₕ L`. -/
theorem tendsto_subseq_of_tendsto_nonstandard {s : ℕ → ℝ} {L : ℝ}
    (hs : Tendsto s atTop (𝓝 L)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tendsto (s ∘ φ) atTop (𝓝 L) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose] at hs ⊢
  intro N hN
  rw [starSeq_comp]
  exact hs (Germ.map φ N) (isUnlimitedNat_map_of_strictMono hφ hN)

/-- Shifting a sequence by `k : ℕ` preserves convergence to `L` (nonstandard proof). -/
theorem tendsto_shift_iff_nonstandard {s : ℕ → ℝ} {L : ℝ} (k : ℕ) :
    Tendsto (fun n ↦ s (n + k)) atTop (𝓝 L) ↔ Tendsto s atTop (𝓝 L) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose, tendsto_nhds_iff_forall_unlimited_infClose]
  constructor
  · intro h N hN
    induction N using Germ.inductionOn with | _ a =>
    let M : ℕ* := ((fun i ↦ a i - k) : ℕ*)
    have hM_unl : IsUnlimitedNat M := fun m ↦ by
      have hgt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), m + k < a i := Germ.coe_lt.1 (hN (m + k))
      exact Germ.coe_lt.2 (hgt.mono fun i hi ↦ by change m < a i - k; omega)
    have hMN : starSeq (fun n ↦ s (n + k)) M = starSeq s (a : ℕ*) := by
      have hge : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), k < a i := Germ.coe_lt.1 (hN k)
      exact Germ.coe_eq.2 (hge.mono fun i hi ↦ by
        change s (a i - k + k) = s (a i)
        rw [Nat.sub_add_cancel hi.le])
    rw [← hMN]
    exact h M hM_unl
  · intro h N hN
    have heq : starSeq (fun n ↦ s (n + k)) N = starSeq s (N + (k : ℕ*)) :=
      Germ.inductionOn N fun _ ↦ rfl
    rw [heq]
    exact h (N + (k : ℕ*)) (isUnlimitedNat_add_right hN (k : ℕ*))

/-! ## §6.2 Monotone Convergence -/

/-- If `s : ℕ → ℝ` is monotone nondecreasing and bounded above, then `starSeq s N` is limited for
every `N ∈ ℕ*`. -/
theorem isLimited_starSeq_of_monotone_bddAbove {s : ℕ → ℝ}
    (hs : Monotone s) (hbdd : BddAbove (Set.range s)) (N : ℕ*) :
    IsLimited (starSeq s N) := by
  obtain ⟨b, hb⟩ := hbdd
  have hlo : (s 0 : ℝ*) ≤ starSeq s N :=
    coe_le_starSeq_of_forall_le (fun n ↦ hs (Nat.zero_le n)) N
  have hhi : starSeq s N ≤ (b : ℝ*) :=
    starSeq_le_coe_of_forall_le (fun n ↦ hb ⟨n, rfl⟩) N
  exact isLimited_iff_exists_real.2 ⟨s 0 - 1, b + 1,
    (Hyperreal.coe_lt_coe.2 (by linarith)).trans_le hlo,
    hhi.trans_lt (Hyperreal.coe_lt_coe.2 (by linarith))⟩

/-- **Goldblatt Theorem 6.2.1(1) (p. 63)**: For a bounded-above nondecreasing sequence `s : ℕ → ℝ`
and any unlimited `N ∈ *ℕ_∞`, `shadow (starSeq s N)` is the least upper bound of `Set.range s`. -/
theorem isLUB_shadow_starSeq_of_monotone_bddAbove {s : ℕ → ℝ}
    (hs : Monotone s) (hbdd : BddAbove (Set.range s)) {N : ℕ*} (hN : IsUnlimitedNat N) :
    IsLUB (Set.range s) (shadow (starSeq s N)) := by
  have hlim : IsLimited (starSeq s N) := isLimited_starSeq_of_monotone_bddAbove hs hbdd N
  have hsh : starSeq s N ≈ₕ (shadow (starSeq s N) : ℝ*) := infClose_shadow hlim
  refine ⟨?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    have hnN : (s n : ℝ*) ≤ starSeq s N := by
      simpa using starSeq_mono hs (hN n).le
    exact coe_le_of_infClose_le (InfClose.refl _) hnN hsh
  · intro r hr
    have hNr : starSeq s N ≤ (r : ℝ*) :=
      starSeq_le_coe_of_forall_le (fun n ↦ hr ⟨n, rfl⟩) N
    exact coe_le_of_infClose_le hsh.symm hNr (InfClose.refl _)

/-- **Goldblatt Theorem 6.2.1(1) (p. 63)**: Every bounded-above nondecreasing sequence `s : ℕ → ℝ`
converges to `sSup (Set.range s)` (proved via shadows of extended terms). -/
theorem tendsto_sSup_of_monotone_bddAbove {s : ℕ → ℝ}
    (hs : Monotone s) (hbdd : BddAbove (Set.range s)) :
    Tendsto s atTop (𝓝 (sSup (Set.range s))) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose]
  intro N hN
  have hlub := isLUB_shadow_starSeq_of_monotone_bddAbove hs hbdd hN
  have hne : (Set.range s).Nonempty := ⟨s 0, 0, rfl⟩
  rw [hlub.csSup_eq hne]
  exact infClose_shadow (isLimited_starSeq_of_monotone_bddAbove hs hbdd N)

/-- If `s : ℕ → ℝ` is monotone nonincreasing and bounded below, then `starSeq s N` is limited for
every `N ∈ ℕ*`. -/
theorem isLimited_starSeq_of_antitone_bddBelow {s : ℕ → ℝ}
    (hs : Antitone s) (hbdd : BddBelow (Set.range s)) (N : ℕ*) :
    IsLimited (starSeq s N) := by
  obtain ⟨a, ha⟩ := hbdd
  have hlo : (a : ℝ*) ≤ starSeq s N :=
    coe_le_starSeq_of_forall_le (fun n ↦ ha ⟨n, rfl⟩) N
  have hhi : starSeq s N ≤ (s 0 : ℝ*) :=
    starSeq_le_coe_of_forall_le (fun n ↦ hs (Nat.zero_le n)) N
  exact isLimited_iff_exists_real.2 ⟨a - 1, s 0 + 1,
    (Hyperreal.coe_lt_coe.2 (by linarith)).trans_le hlo,
    hhi.trans_lt (Hyperreal.coe_lt_coe.2 (by linarith))⟩

/-- **Goldblatt Theorem 6.2.1(2) (p. 63)**: For a bounded-below nonincreasing sequence `s : ℕ → ℝ`
and any unlimited `N ∈ *ℕ_∞`, `shadow (starSeq s N)` is the greatest lower bound of `Set.range s`. -/
theorem isGLB_shadow_starSeq_of_antitone_bddBelow {s : ℕ → ℝ}
    (hs : Antitone s) (hbdd : BddBelow (Set.range s)) {N : ℕ*} (hN : IsUnlimitedNat N) :
    IsGLB (Set.range s) (shadow (starSeq s N)) := by
  have hlim : IsLimited (starSeq s N) := isLimited_starSeq_of_antitone_bddBelow hs hbdd N
  have hsh : starSeq s N ≈ₕ (shadow (starSeq s N) : ℝ*) := infClose_shadow hlim
  refine ⟨?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    have hNn : starSeq s N ≤ (s n : ℝ*) := by
      simpa using starSeq_anti hs (hN n).le
    exact coe_le_of_infClose_le hsh.symm hNn (InfClose.refl _)
  · intro r hr
    have hrN : (r : ℝ*) ≤ starSeq s N :=
      coe_le_starSeq_of_forall_le (fun n ↦ hr ⟨n, rfl⟩) N
    exact coe_le_of_infClose_le (InfClose.refl _) hrN hsh

/-- **Goldblatt Theorem 6.2.1(2) (p. 63)**: Every bounded-below nonincreasing sequence `s : ℕ → ℝ`
converges to `sInf (Set.range s)` (proved via shadows of extended terms). -/
theorem tendsto_sInf_of_antitone_bddBelow {s : ℕ → ℝ}
    (hs : Antitone s) (hbdd : BddBelow (Set.range s)) :
    Tendsto s atTop (𝓝 (sInf (Set.range s))) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose]
  intro N hN
  have hglb := isGLB_shadow_starSeq_of_antitone_bddBelow hs hbdd hN
  have hne : (Set.range s).Nonempty := ⟨s 0, 0, rfl⟩
  rw [hglb.csInf_eq hne]
  exact infClose_shadow (isLimited_starSeq_of_antitone_bddBelow hs hbdd N)

/-- **Goldblatt Theorem 6.2.1 (p. 63)**: Combined monotone convergence theorem. -/
theorem monotone_convergence_nonstandard {s : ℕ → ℝ}
    (h : (Monotone s ∧ BddAbove (Set.range s)) ∨ (Antitone s ∧ BddBelow (Set.range s))) :
    ∃ L : ℝ, Tendsto s atTop (𝓝 L) := by
  rcases h with ⟨hmono, hbdd⟩ | ⟨hanti, hbdd⟩
  · exact ⟨sSup (Set.range s), tendsto_sSup_of_monotone_bddAbove hmono hbdd⟩
  · exact ⟨sInf (Set.range s), tendsto_sInf_of_antitone_bddBelow hanti hbdd⟩

/-- **Goldblatt §6.2 Application (p. 63)**: Nonstandard proof that `c ^ n → 0` for `0 ≤ c < 1`,
using Theorem 6.2.1 and the hyperpower identity `c ^ (N + 1) = c · c ^ N` (`L ≈ₕ c · L`). -/
theorem tendsto_pow_zero_of_nonneg_lt_one_nonstandard {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Tendsto (fun n : ℕ ↦ c ^ n) atTop (𝓝 0) := by
  have hanti : Antitone (fun n : ℕ ↦ c ^ n) :=
    fun _ _ hmn ↦ pow_le_pow_of_le_one hc0 hc1.le hmn
  have hbdd : BddBelow (Set.range (fun n : ℕ ↦ c ^ n)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact pow_nonneg hc0 n⟩
  obtain ⟨L, hL⟩ := monotone_convergence_nonstandard (Or.inr ⟨hanti, hbdd⟩)
  have hN : starSeq (fun n : ℕ ↦ c ^ n) omegaNat ≈ₕ (L : ℝ*) :=
    tendsto_nhds_iff_forall_unlimited_infClose.1 hL omegaNat isUnlimitedNat_omegaNat
  have hN1 : starSeq (fun n : ℕ ↦ c ^ n) (omegaNat + 1) ≈ₕ (L : ℝ*) :=
    tendsto_nhds_iff_forall_unlimited_infClose.1 hL (omegaNat + 1)
      (isUnlimitedNat_add_right isUnlimitedNat_omegaNat 1)
  have hstep : starSeq (fun n : ℕ ↦ c ^ n) (omegaNat + 1) =
      (c : ℝ*) * starSeq (fun n : ℕ ↦ c ^ n) omegaNat :=
    Germ.coe_eq.2 (Eventually.of_forall fun n ↦ pow_succ' c n)
  have hcL : (c : ℝ*) * starSeq (fun n : ℕ ↦ c ^ n) omegaNat ≈ₕ ((c * L : ℝ) : ℝ*) := by
    rw [Hyperreal.coe_mul]
    exact InfClose.mul_left_of_isLimited (isLimited_coe c) hN
  have hLcL : (L : ℝ*) ≈ₕ ((c * L : ℝ) : ℝ*) := by
    refine hN1.symm.trans ?_
    rw [hstep]
    exact hcL
  have heq : L = c * L := coe_eq_of_infClose hLcL
  have hL0 : L = 0 := by
    have hsub : (1 - c) * L = 0 := by linarith
    rcases mul_eq_zero.1 hsub with h1c | h0
    · linarith
    · exact h0
  rwa [hL0] at hL

/-- Extension of Goldblatt §6.2 (p. 63): `c ^ n → 0` whenever `|c| < 1`. -/
theorem tendsto_pow_zero_of_abs_lt_one_nonstandard {c : ℝ} (hc : |c| < 1) :
    Tendsto (fun n : ℕ ↦ c ^ n) atTop (𝓝 0) := by
  have habs := tendsto_pow_zero_of_nonneg_lt_one_nonstandard (abs_nonneg c) hc
  rw [tendsto_nhds_iff_forall_unlimited_infClose] at habs ⊢
  intro N hN
  rw [Hyperreal.coe_zero, infClose_zero_iff]
  have h1 : IsInfinitesimal (starSeq (fun n : ℕ ↦ |c| ^ n) N) := by
    simpa [InfClose] using habs N hN
  refine isInfinitesimal_of_abs_le h1 ?_
  have heq : |starSeq (fun n : ℕ ↦ c ^ n) N| = starSeq (fun n : ℕ ↦ |c| ^ n) N :=
    Germ.inductionOn N fun a ↦ Germ.coe_eq.2 (Eventually.of_forall fun i ↦ abs_pow c (a i))
  rw [heq]
  exact le_abs_self _

/-- For `|c| < 1` and any unlimited `N ∈ *ℕ_∞`, `starSeq (c ^ ·) N` is infinitesimal. -/
theorem isInfinitesimal_starSeq_pow {c : ℝ} (hc : |c| < 1) {N : ℕ*} (hN : IsUnlimitedNat N) :
    IsInfinitesimal (starSeq (fun n : ℕ ↦ c ^ n) N) := by
  have h := tendsto_nhds_iff_forall_unlimited_infClose.1
    (tendsto_pow_zero_of_abs_lt_one_nonstandard hc) N hN
  simpa [InfClose] using h

/-! ## §6.3 Properties of Limits and Squeeze Theorem -/

/-- **Goldblatt §6.3 (p. 63)**: Uniqueness of limits proved via `coe_eq_of_infClose`. -/
theorem tendsto_nhds_unique_nonstandard {s : ℕ → ℝ} {L M : ℝ}
    (hL : Tendsto s atTop (𝓝 L)) (hM : Tendsto s atTop (𝓝 M)) : L = M := by
  have h1 := tendsto_nhds_iff_forall_unlimited_infClose.1 hL omegaNat isUnlimitedNat_omegaNat
  have h2 := tendsto_nhds_iff_forall_unlimited_infClose.1 hM omegaNat isUnlimitedNat_omegaNat
  exact coe_eq_of_infClose (h1.symm.trans h2)

/-- **Goldblatt Theorem 6.3.1(1) (p. 64)**: Limit of a sum `s + t`. -/
theorem tendsto_add_nonstandard {s t : ℕ → ℝ} {L M : ℝ}
    (hs : Tendsto s atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 M)) :
    Tendsto (fun n ↦ s n + t n) atTop (𝓝 (L + M)) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose] at hs ht ⊢
  intro N hN
  rw [starSeq_add, Hyperreal.coe_add]
  exact (hs N hN).add (ht N hN)

/-- Limit of `-s`. -/
theorem tendsto_neg_nonstandard {s : ℕ → ℝ} {L : ℝ}
    (hs : Tendsto s atTop (𝓝 L)) :
    Tendsto (fun n ↦ -s n) atTop (𝓝 (-L)) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose] at hs ⊢
  intro N hN
  rw [starSeq_neg, Hyperreal.coe_neg]
  exact (hs N hN).neg

/-- Limit of a difference `s - t`. -/
theorem tendsto_sub_nonstandard {s t : ℕ → ℝ} {L M : ℝ}
    (hs : Tendsto s atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 M)) :
    Tendsto (fun n ↦ s n - t n) atTop (𝓝 (L - M)) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose] at hs ht ⊢
  intro N hN
  rw [starSeq_sub, Hyperreal.coe_sub]
  exact (hs N hN).sub (ht N hN)

/-- **Goldblatt Theorem 6.3.1(2) (p. 64)**: Limit of a scalar multiple `c * s`. -/
theorem tendsto_const_mul_nonstandard (c : ℝ) {s : ℕ → ℝ} {L : ℝ}
    (hs : Tendsto s atTop (𝓝 L)) :
    Tendsto (fun n ↦ c * s n) atTop (𝓝 (c * L)) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose] at hs ⊢
  intro N hN
  rw [starSeq_const_mul, Hyperreal.coe_mul]
  exact InfClose.mul_left_of_isLimited (isLimited_coe c) (hs N hN)

/-- **Goldblatt Theorem 6.3.1(3) (p. 64)**: Limit of a product `s * t`. -/
theorem tendsto_mul_nonstandard {s t : ℕ → ℝ} {L M : ℝ}
    (hs : Tendsto s atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 M)) :
    Tendsto (fun n ↦ s n * t n) atTop (𝓝 (L * M)) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose] at hs ht ⊢
  intro N hN
  rw [starSeq_mul, Hyperreal.coe_mul]
  exact (InfClose.mul (isLimited_coe L) (isLimited_coe M) (hs N hN).symm (ht N hN).symm).symm

/-- **Goldblatt Theorem 6.3.1(4) (p. 64)**: Limit of a quotient `s / t` when `M ≠ 0`. -/
theorem tendsto_div_nonstandard {s t : ℕ → ℝ} {L M : ℝ}
    (hs : Tendsto s atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 M)) (hM : M ≠ 0) :
    Tendsto (fun n ↦ s n / t n) atTop (𝓝 (L / M)) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose] at hs ht ⊢
  intro N hN
  rw [starSeq_div, Hyperreal.coe_div]
  exact (InfClose.div (isLimited_coe L) (isAppreciable_coe_iff.2 hM)
    (hs N hN).symm (ht N hN).symm).symm

/-- Limit of powers `s n ^ k`. -/
theorem tendsto_pow_nonstandard {s : ℕ → ℝ} {L : ℝ}
    (hs : Tendsto s atTop (𝓝 L)) (k : ℕ) :
    Tendsto (fun n ↦ s n ^ k) atTop (𝓝 (L ^ k)) := by
  induction k with
  | zero =>
      simp [pow_zero]
  | succ m ih =>
      simp only [pow_succ]
      exact tendsto_mul_nonstandard ih hs

/-- Limit of absolute values `|s n| → |L|` via nonstandard characterization. -/
theorem tendsto_abs_nonstandard {s : ℕ → ℝ} {L : ℝ}
    (hs : Tendsto s atTop (𝓝 L)) :
    Tendsto (fun n ↦ |s n|) atTop (𝓝 |L|) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose] at hs ⊢
  intro N hN ε hε
  rw [starSeq_abs, Hyperreal.coe_abs]
  exact (abs_abs_sub_abs_le (starSeq s N) (L : ℝ*)).trans_lt (hs N hN ε hε)

/-- Limit of square roots `Real.sqrt (s n) → Real.sqrt L` via nonstandard `shadow_sqrt` and
`isInfinitesimal_starFun_sqrt`. -/
theorem tendsto_sqrt_nonstandard {s : ℕ → ℝ} {L : ℝ}
    (hs : Tendsto s atTop (𝓝 L)) :
    Tendsto (fun n ↦ Real.sqrt (s n)) atTop (𝓝 (Real.sqrt L)) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose] at hs ⊢
  intro N hN
  have hcomp : starSeq (fun n ↦ Real.sqrt (s n)) N = starFun Real.sqrt (starSeq s N) :=
    Germ.inductionOn N fun _ ↦ rfl
  rw [hcomp]
  rcases lt_trichotomy L 0 with hneg | rfl | hpos
  · have hlt : starSeq s N < 0 := by
      have h := hs N hN (-L / 2) (by linarith)
      have hhi := (abs_lt.1 h).2
      have hc : (L : ℝ*) + ((-L / 2 : ℝ) : ℝ*) < (0 : ℝ*) := by
        rw [← Hyperreal.coe_add, ← Hyperreal.coe_zero]
        exact Hyperreal.coe_lt_coe.2 (by linarith)
      linarith
    have hzero : starFun Real.sqrt (starSeq s N) = 0 := by
      induction N using Germ.inductionOn with | _ a =>
      have ha : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), s (a i) < 0 := ofSeq_lt_ofSeq.1 hlt
      exact Germ.coe_eq.2 (ha.mono fun i hi ↦ Real.sqrt_eq_zero_of_nonpos hi.le)
    rw [hzero, Real.sqrt_eq_zero_of_nonpos hneg.le, Hyperreal.coe_zero]
  · rw [Real.sqrt_zero, Hyperreal.coe_zero, infClose_zero_iff]
    have hinf : IsInfinitesimal |starSeq s N| := by
      have h0 : starSeq s N ≈ₕ 0 := hs N hN
      exact (infClose_zero_iff.1 h0).abs
    have hsq_inf : IsInfinitesimal (starFun Real.sqrt |starSeq s N|) :=
      isInfinitesimal_starFun_sqrt (abs_nonneg _) hinf
    refine isInfinitesimal_of_abs_le hsq_inf ?_
    induction N using Germ.inductionOn with | _ a =>
    refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun i ↦ ?_)
    change |Real.sqrt (s (a i))| ≤ |Real.sqrt (|s (a i)|)|
    rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (le_abs_self _)
  · have hnn : 0 ≤ starSeq s N := by
      have h := hs N hN (L / 2) (half_pos hpos)
      have hlo := (abs_lt.1 h).1
      have hc : (0 : ℝ*) < (L : ℝ*) - ((L / 2 : ℝ) : ℝ*) := by
        rw [← Hyperreal.coe_sub]
        exact Hyperreal.coe_pos.2 (by linarith)
      linarith
    have hlim : IsLimited (starSeq s N) := by
      have : starSeq s N = (L : ℝ*) + (starSeq s N - (L : ℝ*)) := by ring
      rw [this]
      exact (isLimited_coe L).add (hs N hN).isLimited
    have hsq_lim : IsLimited (starFun Real.sqrt (starSeq s N)) := by
      obtain ⟨B, _, hB⟩ := isLimited_iff_abs_le_real.1 hlim
      refine isLimited_iff_abs_le_real.2 ⟨Real.sqrt B, Real.sqrt_nonneg B, ?_⟩
      induction N using Germ.inductionOn with | _ a =>
      have hab : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), |s (a i)| ≤ B := ofSeq_le_ofSeq.1 hB
      refine ofSeq_le_ofSeq.2 (hab.mono fun i hi ↦ ?_)
      change |Real.sqrt (s (a i))| ≤ Real.sqrt B
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt ((le_abs_self _).trans hi)
    have hsh : shadow (starFun Real.sqrt (starSeq s N)) = Real.sqrt L := by
      rw [shadow_sqrt hlim hnn, shadow_eq_of_infClose (hs N hN)]
    rw [← hsh]
    exact infClose_shadow hsq_lim

/-- **Goldblatt Exercise 6.7(1) (p. 66)**: Eventual order `s n ≤ t n` is preserved in the limit. -/
theorem le_of_tendsto_of_tendsto_eventually_nonstandard {s t : ℕ → ℝ} {L M : ℝ}
    (hs : Tendsto s atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 M))
    {k : ℕ} (h : ∀ n : ℕ, k ≤ n → s n ≤ t n) : L ≤ M := by
  have h1 := tendsto_nhds_iff_forall_unlimited_infClose.1 hs omegaNat isUnlimitedNat_omegaNat
  have h2 := tendsto_nhds_iff_forall_unlimited_infClose.1 ht omegaNat isUnlimitedNat_omegaNat
  have hle := starSeq_le_of_le_of_eventually_le h (isUnlimitedNat_omegaNat k).le
  exact coe_le_of_infClose_le h1.symm hle h2

/-- **Goldblatt Exercise 6.7(1) (p. 66)**: Pointwise order `s n ≤ t n` implies `L ≤ M`. -/
theorem le_of_tendsto_of_tendsto_nonstandard {s t : ℕ → ℝ} {L M : ℝ}
    (hs : Tendsto s atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 M))
    (h : ∀ n : ℕ, s n ≤ t n) : L ≤ M :=
  le_of_tendsto_of_tendsto_eventually_nonstandard hs ht (k := 0) (fun n _ ↦ h n)

/-- **Goldblatt Exercise 6.7(2) — Squeeze / Sandwich Theorem (p. 67)** (eventual version):
If `r n ≤ s n ≤ t n` for all `n ≥ k` and `r → L`, `t → L`, then `s → L`. -/
theorem tendsto_of_le_of_le_eventually_nonstandard {r s t : ℕ → ℝ} {L : ℝ} {k : ℕ}
    (hrs : ∀ n : ℕ, k ≤ n → r n ≤ s n) (hst : ∀ n : ℕ, k ≤ n → s n ≤ t n)
    (hr : Tendsto r atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 L)) :
    Tendsto s atTop (𝓝 L) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose] at hr ht ⊢
  intro N hN ε hε
  have hkN : (k : ℕ*) ≤ N := (hN k).le
  have h1 : starSeq r N ≤ starSeq s N := starSeq_le_of_le_of_eventually_le hrs hkN
  have h2 : starSeq s N ≤ starSeq t N := starSeq_le_of_le_of_eventually_le hst hkN
  have hrε := abs_lt.1 (hr N hN ε hε)
  have htε := abs_lt.1 (ht N hN ε hε)
  exact abs_lt.2 ⟨by linarith, by linarith⟩

/-- **Goldblatt Exercise 6.7(2) — Squeeze / Sandwich Theorem (p. 67)**:
If `r n ≤ s n ≤ t n` for all `n ∈ ℕ` and `r → L`, `t → L`, then `s → L`. -/
theorem tendsto_of_le_of_le_nonstandard {r s t : ℕ → ℝ} {L : ℝ}
    (hrs : ∀ n : ℕ, r n ≤ s n) (hst : ∀ n : ℕ, s n ≤ t n)
    (hr : Tendsto r atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 L)) :
    Tendsto s atTop (𝓝 L) :=
  tendsto_of_le_of_le_eventually_nonstandard (k := 0)
    (fun n _ ↦ hrs n) (fun n _ ↦ hst n) hr ht

/-! ## §6.4 Boundedness and Divergence -/

/-- Equivalence between `Bornology.IsBounded (Set.range s)` and `∃ B : ℝ, ∀ n, |s n| ≤ B`. -/
theorem isBounded_range_iff_exists_abs_le {s : ℕ → ℝ} :
    Bornology.IsBounded (Set.range s) ↔ ∃ B : ℝ, ∀ n : ℕ, |s n| ≤ B := by
  rw [isBounded_iff_forall_norm_le]
  simp only [Set.forall_mem_range, Real.norm_eq_abs]

/-- `starSeq s N` is limited for all `N ∈ ℕ*` iff it is limited for all unlimited `N ∈ *ℕ_∞`. -/
theorem forall_isLimited_starSeq_iff_forall_unlimited {s : ℕ → ℝ} :
    (∀ N : ℕ*, IsLimited (starSeq s N)) ↔
      (∀ N : ℕ*, IsUnlimitedNat N → IsLimited (starSeq s N)) := by
  constructor
  · exact fun h N _ ↦ h N
  · intro h N
    by_cases hN : IsUnlimitedNat N
    · exact h N hN
    · obtain ⟨n, rfl⟩ := not_isUnlimitedNat_iff_exists_nat.1 hN
      simp

/-- **Goldblatt Theorem 6.4.1 (p. 64)** (`∃ B, ∀ n, |s n| ≤ B` formulation):
A sequence `s : ℕ → ℝ` is bounded in `ℝ` if and only if all of its extended terms are limited. -/
theorem exists_abs_le_iff_forall_unlimited_isLimited {s : ℕ → ℝ} :
    (∃ B : ℝ, ∀ n : ℕ, |s n| ≤ B) ↔ ∀ N : ℕ*, IsUnlimitedNat N → IsLimited (starSeq s N) := by
  rw [← forall_isLimited_starSeq_iff_forall_unlimited]
  constructor
  · rintro ⟨B, hB⟩ N
    refine isLimited_iff_abs_le_real.2 ⟨max B 0, le_max_right B 0, ?_⟩
    rw [← starSeq_abs]
    exact starSeq_le_coe_of_forall_le (fun n ↦ (hB n).trans (le_max_left B 0)) N
  · intro h
    by_contra hnot
    push Not at hnot
    choose a ha using fun k : ℕ ↦ hnot (k : ℝ)
    have hunl : IsUnlimited (starSeq s (a : ℕ*)) := by
      intro m
      rw [← starSeq_abs]
      have hev : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), (m : ℝ) < |s (a k)| := by
        have hat : ∀ᶠ k in atTop, (m : ℝ) < |s (a k)| :=
          eventually_atTop.2 ⟨m, fun k hk ↦ (Nat.cast_le.2 hk).trans_lt (ha k)⟩
        exact hat.filter_mono Nat.hyperfilter_le_atTop
      exact ofSeq_lt_ofSeq.2 hev
    exact (isUnlimited_iff_not_isLimited.1 hunl) (h (a : ℕ*))

/-- **Goldblatt Theorem 6.4.1 (p. 64)** (`Bornology.IsBounded` formulation):
`Bornology.IsBounded (Set.range s)` iff `IsLimited (starSeq s N)` for every unlimited `N ∈ *ℕ_∞`. -/
theorem isBounded_range_iff_forall_unlimited_isLimited {s : ℕ → ℝ} :
    Bornology.IsBounded (Set.range s) ↔ ∀ N : ℕ*, IsUnlimitedNat N → IsLimited (starSeq s N) :=
  isBounded_range_iff_exists_abs_le.trans exists_abs_le_iff_forall_unlimited_isLimited

/-- **Goldblatt Theorem 6.4.1 (p. 64)** (all hypernaturals `N ∈ ℕ*` formulation). -/
theorem isBounded_range_iff_forall_isLimited {s : ℕ → ℝ} :
    Bornology.IsBounded (Set.range s) ↔ ∀ N : ℕ*, IsLimited (starSeq s N) :=
  isBounded_range_iff_forall_unlimited_isLimited.trans
    forall_isLimited_starSeq_iff_forall_unlimited.symm

/-- Corollary of Theorems 6.1.1 and 6.4.1: Every convergent real sequence is bounded. -/
theorem isBounded_range_of_tendsto_nonstandard {s : ℕ → ℝ} {L : ℝ}
    (hs : Tendsto s atTop (𝓝 L)) : Bornology.IsBounded (Set.range s) := by
  rw [isBounded_range_iff_forall_unlimited_isLimited]
  intro N hN
  exact (tendsto_nhds_iff_forall_unlimited_shadow.1 hs N hN).1

/-- **Goldblatt §6.4 Refinement 1 (p. 64)**: `s` is bounded above in `ℝ` iff it has no positive
unlimited extended terms. -/
theorem bddAbove_range_iff_forall_unlimited_not_isPosUnlimited {s : ℕ → ℝ} :
    BddAbove (Set.range s) ↔ ∀ N : ℕ*, IsUnlimitedNat N → ¬ IsPosUnlimited (starSeq s N) := by
  constructor
  · rintro ⟨B, hB⟩ N _ hpos
    have hle : starSeq s N ≤ (B : ℝ*) := starSeq_le_coe_of_forall_le (fun n ↦ hB ⟨n, rfl⟩) N
    exact lt_irrefl (B : ℝ*) ((hpos B).trans_le hle)
  · intro h
    by_contra hnot
    have hunb : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ (k : ℝ) < s n := by
      intro k
      by_contra hk
      push Not at hk
      -- Bound `{s 0, ..., s k}` and tail `n ≥ k` simultaneously
      let B : ℝ := (∑ i ∈ Finset.range (k + 1), |s i|) + (k : ℝ)
      apply hnot
      refine ⟨B, ?_⟩
      rintro _ ⟨n, rfl⟩
      by_cases hnk : n ≤ k
      · have hmem : n ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hnk)
        have hsum : |s n| ≤ ∑ i ∈ Finset.range (k + 1), |s i| :=
          Finset.single_le_sum (fun i _ ↦ abs_nonneg (s i)) hmem
        have h1 : s n ≤ |s n| := le_abs_self (s n)
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      · have hkn : k ≤ n := by omega
        have hsn : s n ≤ (k : ℝ) := hk n hkn
        have hsum0 : 0 ≤ ∑ i ∈ Finset.range (k + 1), |s i| :=
          Finset.sum_nonneg fun i _ ↦ abs_nonneg (s i)
        linarith
    choose a ha using hunb
    have ha_unl : IsUnlimitedNat (a : ℕ*) :=
      isUnlimitedNat_of_le isUnlimitedNat_omegaNat
        (Germ.coe_le.2 (Eventually.of_forall fun k ↦ (ha k).1))
    have hpos : IsPosUnlimited (starSeq s (a : ℕ*)) := by
      intro r
      obtain ⟨m, hm⟩ := exists_nat_gt r
      have hev : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), r < s (a k) := by
        have hat : ∀ᶠ k in atTop, r < s (a k) :=
          eventually_atTop.2 ⟨m, fun k hk ↦ hm.trans ((Nat.cast_le.2 hk).trans_lt (ha k).2)⟩
        exact hat.filter_mono Nat.hyperfilter_le_atTop
      exact ofSeq_lt_ofSeq.2 hev
    exact h (a : ℕ*) ha_unl hpos

/-- **Goldblatt §6.4 Refinement 2 (p. 64)**: `s` is bounded below in `ℝ` iff it has no negative
unlimited extended terms. -/
theorem bddBelow_range_iff_forall_unlimited_not_isNegUnlimited {s : ℕ → ℝ} :
    BddBelow (Set.range s) ↔ ∀ N : ℕ*, IsUnlimitedNat N → ¬ IsNegUnlimited (starSeq s N) := by
  have hb : BddBelow (Set.range s) ↔ BddAbove (Set.range (fun n ↦ -s n)) := by
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨-a, by rintro _ ⟨n, rfl⟩; exact neg_le_neg (ha ⟨n, rfl⟩)⟩
    · rintro ⟨b, hb⟩
      exact ⟨-b, by rintro _ ⟨n, rfl⟩; exact neg_le.1 (hb ⟨n, rfl⟩)⟩
  rw [hb, bddAbove_range_iff_forall_unlimited_not_isPosUnlimited]
  constructor
  · intro h N hN hneg
    refine h N hN fun r ↦ ?_
    rw [starSeq_neg]
    have := hneg (-r)
    rw [Hyperreal.coe_neg] at this
    exact lt_neg.2 this
  · intro h N hN hpos
    refine h N hN fun r ↦ ?_
    have := hpos (-r)
    rw [starSeq_neg, Hyperreal.coe_neg] at this
    exact neg_lt_neg_iff.1 this

/-- Goldblatt §6.4 (p. 64): Standard definition of divergence of `s` to `+∞`. -/
def SeqDivergesToPosInf (s : ℕ → ℝ) : Prop :=
  ∀ r : ℝ, ∃ k : ℕ, ∀ n : ℕ, k ≤ n → r < s n

/-- Goldblatt §6.4 (p. 64): Standard definition of divergence of `s` to `-∞`. -/
def SeqDivergesToNegInf (s : ℕ → ℝ) : Prop :=
  ∀ r : ℝ, ∃ k : ℕ, ∀ n : ℕ, k ≤ n → s n < r

/-- Equivalence between `Tendsto s atTop atTop` and `SeqDivergesToPosInf s`. -/
theorem tendsto_atTop_iff_seqDivergesToPosInf {s : ℕ → ℝ} :
    Tendsto s atTop atTop ↔ SeqDivergesToPosInf s := by
  rw [tendsto_atTop_atTop]
  constructor
  · intro h r
    obtain ⟨k, hk⟩ := h (r + 1)
    exact ⟨k, fun n hn ↦ (lt_add_one r).trans_le (hk n hn)⟩
  · intro h r
    obtain ⟨k, hk⟩ := h r
    exact ⟨k, fun n hn ↦ (hk n hn).le⟩

/-- Equivalence between `Tendsto s atTop atBot` and `SeqDivergesToNegInf s`. -/
theorem tendsto_atBot_iff_seqDivergesToNegInf {s : ℕ → ℝ} :
    Tendsto s atTop atBot ↔ SeqDivergesToNegInf s := by
  rw [tendsto_atTop_atBot]
  constructor
  · intro h r
    obtain ⟨k, hk⟩ := h (r - 1)
    exact ⟨k, fun n hn ↦ (hk n hn).trans_lt (sub_one_lt r)⟩
  · intro h r
    obtain ⟨k, hk⟩ := h r
    exact ⟨k, fun n hn ↦ (hk n hn).le⟩

/-- **Goldblatt Theorem 6.4.2(1) (p. 65)**: A sequence `s : ℕ → ℝ` diverges to `+∞` if and only if
all of its extended terms are positive unlimited. -/
theorem tendsto_atTop_iff_forall_unlimited_isPosUnlimited {s : ℕ → ℝ} :
    Tendsto s atTop atTop ↔ ∀ N : ℕ*, IsUnlimitedNat N → IsPosUnlimited (starSeq s N) := by
  rw [tendsto_atTop_iff_seqDivergesToPosInf]
  unfold SeqDivergesToPosInf IsPosUnlimited
  constructor
  · intro h N hN r
    have hN' : Germ.LiftPred (fun n ↦ r < s n) N :=
      (forall_isUnlimitedNat_liftPred_iff (P := fun n ↦ r < s n)).2 (h r) N hN
    induction N using Germ.inductionOn with | _ a =>
    exact ofSeq_lt_ofSeq.2 hN'
  · intro h r
    refine (forall_isUnlimitedNat_liftPred_iff (P := fun n ↦ r < s n)).1 fun N hN ↦ ?_
    have hr := h N hN r
    induction N using Germ.inductionOn with | _ a =>
    exact ofSeq_lt_ofSeq.1 hr

/-- **Goldblatt Theorem 6.4.2(2) (p. 65)**: A sequence `s : ℕ → ℝ` diverges to `-∞` if and only if
all of its extended terms are negative unlimited. -/
theorem tendsto_atBot_iff_forall_unlimited_isNegUnlimited {s : ℕ → ℝ} :
    Tendsto s atTop atBot ↔ ∀ N : ℕ*, IsUnlimitedNat N → IsNegUnlimited (starSeq s N) := by
  rw [tendsto_atBot_iff_seqDivergesToNegInf]
  unfold SeqDivergesToNegInf IsNegUnlimited
  constructor
  · intro h N hN r
    have hN' : Germ.LiftPred (fun n ↦ s n < r) N :=
      (forall_isUnlimitedNat_liftPred_iff (P := fun n ↦ s n < r)).2 (h r) N hN
    induction N using Germ.inductionOn with | _ a =>
    exact ofSeq_lt_ofSeq.2 hN'
  · intro h r
    refine (forall_isUnlimitedNat_liftPred_iff (P := fun n ↦ s n < r)).1 fun N hN ↦ ?_
    have hr := h N hN r
    induction N using Germ.inductionOn with | _ a =>
    exact ofSeq_lt_ofSeq.1 hr

/-! ## §6.5 Cauchy Sequences -/

/-- Equivalence between Mathlib's `CauchySeq s` and `IsRealCauchy s`. -/
theorem cauchySeq_iff_isRealCauchy {s : ℕ → ℝ} :
    CauchySeq s ↔ IsRealCauchy s := by
  rw [Metric.cauchySeq_iff]
  simp only [Real.dist_eq, IsRealCauchy]
  exact ⟨fun h ε hε ↦ (h ε hε).imp fun k hk m n hm hn ↦ hk m hm n hn,
         fun h ε hε ↦ (h ε hε).imp fun k hk m hm n hn ↦ hk m n hm hn⟩

/-- **Goldblatt Theorem 6.5.1 (p. 65)** (`IsRealCauchy` formulation):
A sequence `s : ℕ → ℝ` is Cauchy in `ℝ` iff all of its extended terms are infinitely close to each
other (`starSeq s M ≈ₕ starSeq s N` for all `M, N ∈ *ℕ_∞`). -/
theorem isRealCauchy_iff_forall_unlimited_infClose {s : ℕ → ℝ} :
    IsRealCauchy s ↔
      ∀ M N : ℕ*, IsUnlimitedNat M → IsUnlimitedNat N → starSeq s M ≈ₕ starSeq s N := by
  unfold IsRealCauchy InfClose IsInfinitesimal
  constructor
  · intro h M N hM hN ε hε
    exact (starSeq_abs_sub_starSeq_lt_iff s ε M N).2
      ((forall_isUnlimitedNat₂_liftRel_iff (R := fun m n ↦ |s m - s n| < ε)).2 (h ε hε) M N hM hN)
  · intro h ε hε
    refine (forall_isUnlimitedNat₂_liftRel_iff (R := fun m n ↦ |s m - s n| < ε)).1 fun M N hM hN ↦ ?_
    exact (starSeq_abs_sub_starSeq_lt_iff s ε M N).1 (h M N hM hN ε hε)

/-- **Goldblatt Theorem 6.5.1 (p. 65)** (`CauchySeq` formulation). -/
theorem cauchySeq_iff_forall_unlimited_infClose {s : ℕ → ℝ} :
    CauchySeq s ↔
      ∀ M N : ℕ*, IsUnlimitedNat M → IsUnlimitedNat N → starSeq s M ≈ₕ starSeq s N :=
  cauchySeq_iff_isRealCauchy.trans isRealCauchy_iff_forall_unlimited_infClose

/-- Every Cauchy sequence `s : ℕ → ℝ` is bounded (answering Goldblatt's question on p. 65). -/
theorem isBounded_range_of_isRealCauchy {s : ℕ → ℝ} (hs : IsRealCauchy s) :
    Bornology.IsBounded (Set.range s) := by
  rw [isBounded_range_iff_exists_abs_le]
  obtain ⟨k, hk⟩ := hs 1 one_pos
  refine ⟨(∑ i ∈ Finset.range (k + 1), |s i|) + 1, fun n ↦ ?_⟩
  by_cases hnk : n ≤ k
  · have hmem : n ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hnk)
    have hle : |s n| ≤ ∑ i ∈ Finset.range (k + 1), |s i| :=
      Finset.single_le_sum (fun i _ ↦ abs_nonneg (s i)) hmem
    linarith
  · have hkn : k ≤ n := by omega
    have hdiff : |s n - s k| < 1 := hk n k hkn le_rfl
    have htri : |s n| ≤ |s n - s k| + |s k| := by
      have : s n = (s n - s k) + s k := by ring
      conv_lhs => rw [this]
      exact abs_add_le _ _
    have hmem : k ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_self k)
    have hsk : |s k| ≤ ∑ i ∈ Finset.range (k + 1), |s i| :=
      Finset.single_le_sum (fun i _ ↦ abs_nonneg (s i)) hmem
    linarith

/-- **Goldblatt Theorem 6.5.2 — Cauchy's Convergence Criterion (p. 65)** (`IsRealCauchy` version):
A sequence `s : ℕ → ℝ` is Cauchy iff it converges in `ℝ`, proved by taking the shadow of
`starSeq s omegaNat`. -/
theorem isRealCauchy_iff_exists_tendsto_nonstandard {s : ℕ → ℝ} :
    IsRealCauchy s ↔ ∃ L : ℝ, Tendsto s atTop (𝓝 L) := by
  constructor
  · intro hs
    have hbdd : Bornology.IsBounded (Set.range s) := isBounded_range_of_isRealCauchy hs
    have hlim : IsLimited (starSeq s omegaNat) :=
      isBounded_range_iff_forall_unlimited_isLimited.1 hbdd omegaNat isUnlimitedNat_omegaNat
    refine ⟨shadow (starSeq s omegaNat), tendsto_nhds_iff_forall_unlimited_infClose.2 fun N hN ↦ ?_⟩
    have hMN : starSeq s N ≈ₕ starSeq s omegaNat :=
      isRealCauchy_iff_forall_unlimited_infClose.1 hs N omegaNat hN isUnlimitedNat_omegaNat
    exact hMN.trans (infClose_shadow hlim)
  · rintro ⟨L, hL⟩
    rw [isRealCauchy_iff_forall_unlimited_infClose]
    intro M N hM hN
    have hML := tendsto_nhds_iff_forall_unlimited_infClose.1 hL M hM
    have hNL := tendsto_nhds_iff_forall_unlimited_infClose.1 hL N hN
    exact hML.trans hNL.symm

/-- **Goldblatt Theorem 6.5.2 — Cauchy's Convergence Criterion (p. 65)** (`CauchySeq` version). -/
theorem cauchySeq_iff_exists_tendsto_nonstandard {s : ℕ → ℝ} :
    CauchySeq s ↔ ∃ L : ℝ, Tendsto s atTop (𝓝 L) :=
  cauchySeq_iff_isRealCauchy.trans isRealCauchy_iff_exists_tendsto_nonstandard

/-! ## §6.6–6.7 Cluster Points and the Bolzano–Weierstrass Theorem -/

/-- Goldblatt §6.6 (p. 66): Sequential definition of a cluster point `L ∈ ℝ` of `s : ℕ → ℝ`. -/
def IsSeqClusterPt (s : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ n : ℕ, m ≤ n ∧ |s n - L| < ε

/-- Equivalence with Goldblatt's strict-inequality formulation `n > m` (p. 66, formula (i)). -/
theorem isSeqClusterPt_iff_strict {s : ℕ → ℝ} {L : ℝ} :
    IsSeqClusterPt s L ↔ ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ n : ℕ, m < n ∧ |s n - L| < ε := by
  constructor
  · intro h ε hε m
    obtain ⟨n, hmn, hn⟩ := h ε hε (m + 1)
    exact ⟨n, Nat.lt_of_succ_le hmn, hn⟩
  · intro h ε hε m
    obtain ⟨n, hmn, hn⟩ := h ε hε m
    exact ⟨n, hmn.le, hn⟩

/-- Equivalence between Mathlib's `MapClusterPt L atTop s` and `IsSeqClusterPt s L`. -/
theorem mapClusterPt_iff_isSeqClusterPt {s : ℕ → ℝ} {L : ℝ} :
    MapClusterPt L atTop s ↔ IsSeqClusterPt s L := by
  rw [mapClusterPt_iff_frequently]
  constructor
  · intro h ε hε m
    have hball : Metric.ball L ε ∈ 𝓝 L := Metric.ball_mem_nhds L hε
    obtain ⟨n, hmn, hn⟩ := Filter.frequently_atTop.1 (h (Metric.ball L ε) hball) m
    rw [Metric.mem_ball, Real.dist_eq] at hn
    exact ⟨n, hmn, hn⟩
  · intro h U hU
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 hU
    refine Filter.frequently_atTop.2 fun m ↦ ?_
    obtain ⟨n, hmn, hn⟩ := h ε hε m
    exact ⟨n, hmn, hsub (by rwa [Metric.mem_ball, Real.dist_eq])⟩

/-- **Goldblatt Theorem 6.6.1 (p. 66)**: `L ∈ ℝ` is a cluster point of `s : ℕ → ℝ` if and only if
`starSeq s N ≈ₕ (L : ℝ*)` for some unlimited hypernatural `N ∈ *ℕ_∞`. -/
theorem isSeqClusterPt_iff_exists_unlimited_infClose {s : ℕ → ℝ} {L : ℝ} :
    IsSeqClusterPt s L ↔ ∃ N : ℕ*, IsUnlimitedNat N ∧ starSeq s N ≈ₕ (L : ℝ*) := by
  constructor
  · intro h
    choose a ha using fun k : ℕ ↦ h (1 / ((k : ℝ) + 1)) (by positivity) k
    have ha_unl : IsUnlimitedNat (a : ℕ*) :=
      isUnlimitedNat_of_le isUnlimitedNat_omegaNat
        (Germ.coe_le.2 (Eventually.of_forall fun k ↦ (ha k).1))
    refine ⟨(a : ℕ*), ha_unl, ?_⟩
    have hinv_inf : IsInfinitesimal (starSeq (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) omegaNat) := by
      have h0 := tendsto_nhds_iff_forall_unlimited_infClose.1
        tendsto_one_div_add_one_zero_nonstandard omegaNat isUnlimitedNat_omegaNat
      simpa [InfClose] using h0
    refine isInfinitesimal_of_abs_le hinv_inf ?_
    refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun k ↦ ?_)
    change |s (a k) - L| ≤ |1 / ((k : ℝ) + 1)|
    exact (ha k).2.le.trans (le_abs_self _)
  · rintro ⟨N, hN, hclose⟩ ε hε m
    have hNP : Germ.LiftPred (fun n ↦ |s n - L| < ε) N :=
      (starSeq_abs_sub_lt_iff s L ε N).1 (hclose ε hε)
    exact (exists_isUnlimitedNat_liftPred_iff (P := fun n ↦ |s n - L| < ε)).1 ⟨N, hN, hNP⟩ m

/-- **Goldblatt Theorem 6.6.1 (p. 66)** (`MapClusterPt` formulation). -/
theorem mapClusterPt_iff_exists_unlimited_infClose {s : ℕ → ℝ} {L : ℝ} :
    MapClusterPt L atTop s ↔ ∃ N : ℕ*, IsUnlimitedNat N ∧ starSeq s N ≈ₕ (L : ℝ*) :=
  mapClusterPt_iff_isSeqClusterPt.trans isSeqClusterPt_iff_exists_unlimited_infClose

/-- Goldblatt §6.6 (p. 66): Cluster points are precisely the shadows of limited extended terms. -/
theorem isSeqClusterPt_iff_exists_unlimited_shadow {s : ℕ → ℝ} {L : ℝ} :
    IsSeqClusterPt s L ↔
      ∃ N : ℕ*, IsUnlimitedNat N ∧ IsLimited (starSeq s N) ∧ shadow (starSeq s N) = L := by
  rw [isSeqClusterPt_iff_exists_unlimited_infClose]
  constructor
  · rintro ⟨N, hN, hclose⟩
    have hlim : IsLimited (starSeq s N) := by
      have : starSeq s N = (L : ℝ*) + (starSeq s N - (L : ℝ*)) := by ring
      rw [this]
      exact (isLimited_coe L).add hclose.isLimited
    exact ⟨N, hN, hlim, shadow_eq_of_infClose hclose⟩
  · rintro ⟨N, hN, hlim, rfl⟩
    exact ⟨N, hN, infClose_shadow hlim⟩

/-- Equivalence between sequential cluster points and limits of strictly monotone subsequences. -/
theorem isSeqClusterPt_iff_exists_subseq {s : ℕ → ℝ} {L : ℝ} :
    IsSeqClusterPt s L ↔ ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (s ∘ φ) atTop (𝓝 L) := by
  constructor
  · intro h
    let step : ℕ → ℕ → ℕ := fun k prev ↦
      (h (1 / ((k : ℝ) + 1)) (by positivity) (prev + 1)).choose
    let φ : ℕ → ℕ := fun k ↦ Nat.rec ((h 1 one_pos 0).choose) (fun m prev ↦ step (m + 1) prev) k
    have hφ_lt : ∀ k : ℕ, φ k < φ (k + 1) := fun k ↦ by
      have hspec := (h (1 / (((k + 1 : ℕ) : ℝ) + 1)) (by positivity) (φ k + 1)).choose_spec
      exact Nat.lt_of_succ_le hspec.1
    have hφ_mono : StrictMono φ := strictMono_nat_of_lt_succ hφ_lt
    have hφ_dist : ∀ k : ℕ, |(s ∘ φ) k - L| < 1 / ((k : ℝ) + 1) := by
      intro k
      cases k with
      | zero =>
          simp only [Function.comp_apply, φ, Nat.cast_zero, zero_add, div_one]
          exact (h 1 one_pos 0).choose_spec.2
      | succ m =>
          exact (h (1 / (((m + 1 : ℕ) : ℝ) + 1)) (by positivity) (φ m + 1)).choose_spec.2
    refine ⟨φ, hφ_mono, ?_⟩
    rw [tendsto_nhds_iff_forall_unlimited_infClose]
    intro N hN
    have hinv_inf : IsInfinitesimal (starSeq (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) N) := by
      have h0 := tendsto_nhds_iff_forall_unlimited_infClose.1
        tendsto_one_div_add_one_zero_nonstandard N hN
      simpa [InfClose] using h0
    refine isInfinitesimal_of_abs_le hinv_inf ?_
    induction N using Germ.inductionOn with | _ a =>
    refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun i ↦ ?_)
    change |(s ∘ φ) (a i) - L| ≤ |1 / ((a i : ℝ) + 1)|
    exact (hφ_dist (a i)).le.trans (le_abs_self _)
  · rintro ⟨φ, hφ_mono, hφ_lim⟩
    rw [isSeqClusterPt_iff_exists_unlimited_infClose]
    refine ⟨Germ.map φ omegaNat, isUnlimitedNat_map_of_strictMono hφ_mono isUnlimitedNat_omegaNat, ?_⟩
    rw [← starSeq_comp]
    exact tendsto_nhds_iff_forall_unlimited_infClose.1 hφ_lim omegaNat isUnlimitedNat_omegaNat

/-- **Goldblatt Theorem 6.6.2 — Bolzano–Weierstrass Theorem (p. 66)**:
Every bounded sequence `s : ℕ → ℝ` has a cluster point in `ℝ` (namely `shadow (starSeq s omegaNat)`). -/
theorem bolzano_weierstrass_clusterPt {s : ℕ → ℝ} (hs : Bornology.IsBounded (Set.range s)) :
    ∃ L : ℝ, IsSeqClusterPt s L := by
  have hlim : IsLimited (starSeq s omegaNat) :=
    isBounded_range_iff_forall_unlimited_isLimited.1 hs omegaNat isUnlimitedNat_omegaNat
  exact ⟨shadow (starSeq s omegaNat),
    isSeqClusterPt_iff_exists_unlimited_infClose.2
      ⟨omegaNat, isUnlimitedNat_omegaNat, infClose_shadow hlim⟩⟩

/-- **Bolzano–Weierstrass Subsequence Corollary**: Every bounded sequence `s : ℕ → ℝ` has a
convergent subsequence. -/
theorem bolzano_weierstrass_subseq {s : ℕ → ℝ} (hs : Bornology.IsBounded (Set.range s)) :
    ∃ L : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (s ∘ φ) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := bolzano_weierstrass_clusterPt hs
  exact ⟨L, isSeqClusterPt_iff_exists_subseq.1 hL⟩

/-- **Goldblatt Exercise 6.7(3) (p. 67)**: If `s` converges to `L ∈ ℝ`, then `L` is its unique
cluster point. -/
theorem clusterPt_unique_of_tendsto {s : ℕ → ℝ} {L : ℝ}
    (hs : Tendsto s atTop (𝓝 L)) : {c : ℝ | IsSeqClusterPt s c} = {L} := by
  ext c
  change IsSeqClusterPt s c ↔ c = L
  rw [isSeqClusterPt_iff_exists_unlimited_infClose]
  constructor
  · rintro ⟨N, hN, hc⟩
    have hL := tendsto_nhds_iff_forall_unlimited_infClose.1 hs N hN
    exact coe_eq_of_infClose (hc.symm.trans hL)
  · rintro rfl
    exact ⟨omegaNat, isUnlimitedNat_omegaNat,
      tendsto_nhds_iff_forall_unlimited_infClose.1 hs omegaNat isUnlimitedNat_omegaNat⟩

/-- **Goldblatt Exercise 6.7(4a) (p. 67)**: If a bounded sequence `s : ℕ → ℝ` has a unique cluster
point `L`, then `s` converges to `L`. -/
theorem tendsto_of_isBounded_unique_clusterPt {s : ℕ → ℝ} {L : ℝ}
    (hbdd : Bornology.IsBounded (Set.range s))
    (huniq : ∀ c : ℝ, IsSeqClusterPt s c ↔ c = L) :
    Tendsto s atTop (𝓝 L) := by
  rw [tendsto_nhds_iff_forall_unlimited_infClose]
  intro N hN
  have hlim : IsLimited (starSeq s N) :=
    isBounded_range_iff_forall_unlimited_isLimited.1 hbdd N hN
  have hcl : IsSeqClusterPt s (shadow (starSeq s N)) :=
    isSeqClusterPt_iff_exists_unlimited_infClose.2 ⟨N, hN, infClose_shadow hlim⟩
  have hsh : shadow (starSeq s N) = L := (huniq _).1 hcl
  rw [← hsh]
  exact infClose_shadow hlim

/-- **Goldblatt Exercise 6.7(4b) (p. 67)**: An *unbounded* sequence can have a unique cluster
point without converging (`s n = 0` for even `n`, `s n = n` for odd `n`). -/
theorem exists_unbounded_unique_clusterPt_not_convergent :
    ∃ s : ℕ → ℝ, ¬ Bornology.IsBounded (Set.range s) ∧
      {c : ℝ | IsSeqClusterPt s c} = {0} ∧ ¬ ∃ L : ℝ, Tendsto s atTop (𝓝 L) := by
  let s : ℕ → ℝ := fun n ↦ if Even n then 0 else (n : ℝ)
  have hunb : ¬ Bornology.IsBounded (Set.range s) := by
    rw [isBounded_range_iff_exists_abs_le]
    rintro ⟨B, hB⟩
    obtain ⟨k, hk⟩ := exists_nat_gt B
    have hodd : ¬ Even (2 * k + 1) := by simp
    have hsodd : s (2 * k + 1) = ((2 * k + 1 : ℕ) : ℝ) := by simp [s, hodd]
    have hle := hB (2 * k + 1)
    rw [hsodd, abs_of_nonneg (Nat.cast_nonneg _)] at hle
    push_cast at hle
    linarith
  refine ⟨s, hunb, ?_, ?_⟩
  · ext c
    change IsSeqClusterPt s c ↔ c = 0
    constructor
    · intro hc
      by_contra hne
      have hpos : 0 < |c| / 2 := half_pos (abs_pos.2 hne)
      obtain ⟨m, hm⟩ := exists_nat_gt (|c| + |c| / 2)
      obtain ⟨n, hmn, hdist⟩ := hc (|c| / 2) hpos m
      by_cases hev : Even n
      · simp only [s, hev, ↓reduceIte, zero_sub, abs_neg] at hdist
        linarith
      · simp only [s, hev, ↓reduceIte] at hdist
        have hn_gt : |c| + |c| / 2 < (n : ℝ) := hm.trans_le (Nat.cast_le.2 hmn)
        have htri : (n : ℝ) - |c| ≤ |(n : ℝ) - c| := by
          have := abs_sub_abs_le_abs_sub (n : ℝ) c
          have hnn : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
          linarith [le_abs_self (|(n : ℝ)| - |c|)]
        linarith
    · rintro rfl ε hε m
      refine ⟨2 * m, by omega, ?_⟩
      have hev : Even (2 * m) := even_two_mul m
      simp [s, hev, hε]
  · rintro ⟨L, hL⟩
    exact hunb (isBounded_range_of_tendsto_nonstandard hL)

/-! ## §6.8–6.9 Limits Superior and Inferior (`limsup` and `liminf`) -/

/-- Goldblatt §6.8 (p. 67): Set `C_s` of cluster points of `s`, defined nonstandardly as the set of
standard reals infinitely close to some extended term. -/
def clusterSet (s : ℕ → ℝ) : Set ℝ :=
  {c : ℝ | ∃ N : ℕ*, IsUnlimitedNat N ∧ starSeq s N ≈ₕ (c : ℝ*)}

/-- Membership in `clusterSet s` is equivalent to `IsSeqClusterPt s c` (by Theorem 6.6.1). -/
theorem mem_clusterSet_iff_isSeqClusterPt {s : ℕ → ℝ} {c : ℝ} :
    c ∈ clusterSet s ↔ IsSeqClusterPt s c :=
  isSeqClusterPt_iff_exists_unlimited_infClose.symm

/-- Goldblatt §6.8 (p. 67): For a bounded sequence `s`, `clusterSet s` is precisely the set of
shadows `{sh(s_N) | N ∈ *ℕ_∞}` of the extended tail. -/
theorem clusterSet_eq_shadows_of_isBounded {s : ℕ → ℝ}
    (hbdd : Bornology.IsBounded (Set.range s)) :
    clusterSet s = {c : ℝ | ∃ N : ℕ*, IsUnlimitedNat N ∧ shadow (starSeq s N) = c} := by
  ext c
  constructor
  · rintro ⟨N, hN, hc⟩
    exact ⟨N, hN, shadow_eq_of_infClose hc⟩
  · rintro ⟨N, hN, rfl⟩
    have hlim := isBounded_range_iff_forall_unlimited_isLimited.1 hbdd N hN
    exact ⟨N, hN, infClose_shadow hlim⟩

/-- For any bounded sequence `s`, `clusterSet s` is nonempty. -/
theorem clusterSet_nonempty_of_isBounded {s : ℕ → ℝ}
    (hbdd : Bornology.IsBounded (Set.range s)) : (clusterSet s).Nonempty := by
  obtain ⟨L, hL⟩ := bolzano_weierstrass_clusterPt hbdd
  exact ⟨L, mem_clusterSet_iff_isSeqClusterPt.2 hL⟩

/-- Goldblatt §6.8 (p. 67): Any real upper bound of `s` is an upper bound of `clusterSet s`. -/
theorem clusterSet_le_of_upperBound {s : ℕ → ℝ} {b : ℝ} (hb : ∀ n : ℕ, s n ≤ b)
    {c : ℝ} (hc : c ∈ clusterSet s) : c ≤ b := by
  rcases hc with ⟨N, _, hclose⟩
  exact coe_le_of_infClose_le hclose.symm (starSeq_le_coe_of_forall_le hb N) (InfClose.refl _)

/-- Goldblatt §6.8 (p. 67): Any real lower bound of `s` is a lower bound of `clusterSet s`. -/
theorem le_clusterSet_of_lowerBound {s : ℕ → ℝ} {a : ℝ} (ha : ∀ n : ℕ, a ≤ s n)
    {c : ℝ} (hc : c ∈ clusterSet s) : a ≤ c := by
  rcases hc with ⟨N, _, hclose⟩
  exact coe_le_of_infClose_le (InfClose.refl _) (coe_le_starSeq_of_forall_le ha N) hclose

/-- If `s` is bounded above, `clusterSet s` is bounded above. -/
theorem bddAbove_clusterSet_of_bddAbove {s : ℕ → ℝ} (hbdd : BddAbove (Set.range s)) :
    BddAbove (clusterSet s) := by
  rcases hbdd with ⟨b, hb⟩
  exact ⟨b, fun _ hc ↦ clusterSet_le_of_upperBound (fun n ↦ hb ⟨n, rfl⟩) hc⟩

/-- If `s` is bounded below, `clusterSet s` is bounded below. -/
theorem bddBelow_clusterSet_of_bddBelow {s : ℕ → ℝ} (hbdd : BddBelow (Set.range s)) :
    BddBelow (clusterSet s) := by
  rcases hbdd with ⟨a, ha⟩
  exact ⟨a, fun _ hc ↦ le_clusterSet_of_lowerBound (fun n ↦ ha ⟨n, rfl⟩) hc⟩

/-- If `s` is bounded, `clusterSet s` is bounded above, bounded below, and `Bornology.IsBounded`. -/
theorem isBounded_clusterSet_of_isBounded {s : ℕ → ℝ}
    (hbdd : Bornology.IsBounded (Set.range s)) :
    BddAbove (clusterSet s) ∧ BddBelow (clusterSet s) ∧ Bornology.IsBounded (clusterSet s) := by
  obtain ⟨B, hB⟩ := isBounded_range_iff_exists_abs_le.1 hbdd
  refine ⟨⟨B, fun c hc ↦ clusterSet_le_of_upperBound (fun n ↦ (abs_le.1 (hB n)).2) hc⟩,
          ⟨-B, fun c hc ↦ le_clusterSet_of_lowerBound (fun n ↦ (abs_le.1 (hB n)).1) hc⟩,
          isBounded_iff_forall_norm_le.2 ⟨B, fun c hc ↦ ?_⟩⟩
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_clusterSet_of_lowerBound (fun n ↦ (abs_le.1 (hB n)).1) hc,
         clusterSet_le_of_upperBound (fun n ↦ (abs_le.1 (hB n)).2) hc⟩

/-- For *every* sequence `s : ℕ → ℝ`, `clusterSet s` is a closed subset of `ℝ`. -/
theorem isClosed_clusterSet (s : ℕ → ℝ) : IsClosed (clusterSet s) := by
  rw [← closure_subset_iff_isClosed]
  intro c hc
  rw [mem_clusterSet_iff_isSeqClusterPt]
  intro ε hε m
  obtain ⟨x, hx, hxc⟩ := Metric.mem_closure_iff.1 hc (ε / 2) (half_pos hε)
  rw [Real.dist_eq] at hxc
  obtain ⟨n, hmn, hnx⟩ := (mem_clusterSet_iff_isSeqClusterPt.1 hx) (ε / 2) (half_pos hε) m
  refine ⟨n, hmn, ?_⟩
  have htri : |s n - c| ≤ |s n - x| + |c - x| := by
    have : s n - c = (s n - x) + (x - c) := by ring
    rw [this, abs_sub_comm c x]
    exact abs_add_le _ _
  linarith

/-- Goldblatt §6.8 (p. 67): Limit superior `limsup_{n → ∞} s_n = sup C_s`. -/
def seqLimsup (s : ℕ → ℝ) : ℝ := sSup (clusterSet s)

/-- Goldblatt §6.8 (p. 67): Limit inferior `liminf_{n → ∞} s_n = inf C_s`. -/
def seqLiminf (s : ℕ → ℝ) : ℝ := sInf (clusterSet s)

/-- **Goldblatt Exercise 6.8.1 (pp. 67–68)**: Nonstandard proof that `seqLimsup s` is itself a
cluster point of any bounded sequence `s` (hence the maximum element of `clusterSet s`). -/
theorem seqLimsup_mem_clusterSet {s : ℕ → ℝ} (hbdd : Bornology.IsBounded (Set.range s)) :
    seqLimsup s ∈ clusterSet s := by
  -- Nonstandard diagonalization: for each `k`, choose `c_k ∈ clusterSet s` within `1/(k+1)` of `sSup`
  -- and `a k ≥ k` with `|s (a k) - c_k| < 1/(k+1)`, then lift `a` to `N ∈ *ℕ_∞`!
  have hne := clusterSet_nonempty_of_isBounded hbdd
  have hub := (isBounded_clusterSet_of_isBounded hbdd).1
  have hex : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ |s n - seqLimsup s| < 2 / ((k : ℝ) + 1) := by
    intro k
    have hlt : seqLimsup s - 1 / ((k : ℝ) + 1) < sSup (clusterSet s) := by
      unfold seqLimsup
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    obtain ⟨c, hc_mem, hc_gt⟩ := exists_lt_of_lt_csSup hne hlt
    have hc_le : c ≤ seqLimsup s := le_csSup hub hc_mem
    obtain ⟨n, hkn, hsn⟩ :=
      (mem_clusterSet_iff_isSeqClusterPt.1 hc_mem) (1 / ((k : ℝ) + 1)) (by positivity) k
    refine ⟨n, hkn, ?_⟩
    have htri : |s n - seqLimsup s| ≤ |s n - c| + |c - seqLimsup s| := by
      have : s n - seqLimsup s = (s n - c) + (c - seqLimsup s) := by ring
      rw [this]
      exact abs_add_le _ _
    have hc_dist : |c - seqLimsup s| < 1 / ((k : ℝ) + 1) := by
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    have h2 : 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) = 2 / ((k : ℝ) + 1) := by ring
    linarith
  choose a ha using hex
  have ha_unl : IsUnlimitedNat (a : ℕ*) :=
    isUnlimitedNat_of_le isUnlimitedNat_omegaNat
      (Germ.coe_le.2 (Eventually.of_forall fun k ↦ (ha k).1))
  refine ⟨(a : ℕ*), ha_unl, ?_⟩
  have h2_inf : IsInfinitesimal (starSeq (fun k : ℕ ↦ 2 / ((k : ℝ) + 1)) omegaNat) := by
    have h1 := tendsto_const_mul_nonstandard 2 tendsto_one_div_add_one_zero_nonstandard
    rw [mul_zero] at h1
    have h2 := tendsto_nhds_iff_forall_unlimited_infClose.1 h1 omegaNat isUnlimitedNat_omegaNat
    have heq : starSeq (fun k : ℕ ↦ 2 / ((k : ℝ) + 1)) omegaNat =
        starSeq (fun k : ℕ ↦ 2 * (1 / ((k : ℝ) + 1))) omegaNat :=
      Germ.coe_eq.2 (Eventually.of_forall fun k ↦ div_eq_mul_one_div 2 ((k : ℝ) + 1))
    rw [heq]
    simpa [InfClose] using h2
  refine isInfinitesimal_of_abs_le h2_inf ?_
  refine ofSeq_le_ofSeq.2 (Eventually.of_forall fun k ↦ ?_)
  change |s (a k) - seqLimsup s| ≤ |2 / ((k : ℝ) + 1)|
  exact (ha k).2.le.trans (le_abs_self _)

/-- **Goldblatt Exercise 6.8.1 (pp. 67–68)**: `seqLiminf s` is a cluster point of any bounded
sequence `s` (hence the minimum element of `clusterSet s`). -/
theorem seqLiminf_mem_clusterSet {s : ℕ → ℝ} (hbdd : Bornology.IsBounded (Set.range s)) :
    seqLiminf s ∈ clusterSet s :=
  (isClosed_clusterSet s).csInf_mem
    (clusterSet_nonempty_of_isBounded hbdd) (isBounded_clusterSet_of_isBounded hbdd).2.1

/-- `seqLimsup s` is the greatest cluster point of a bounded sequence `s`. -/
theorem isGreatest_clusterSet_seqLimsup {s : ℕ → ℝ} (hbdd : Bornology.IsBounded (Set.range s)) :
    IsGreatest (clusterSet s) (seqLimsup s) :=
  ⟨seqLimsup_mem_clusterSet hbdd, fun _ hc ↦ le_csSup (isBounded_clusterSet_of_isBounded hbdd).1 hc⟩

/-- `seqLiminf s` is the least cluster point of a bounded sequence `s`. -/
theorem isLeast_clusterSet_seqLiminf {s : ℕ → ℝ} (hbdd : Bornology.IsBounded (Set.range s)) :
    IsLeast (clusterSet s) (seqLiminf s) :=
  ⟨seqLiminf_mem_clusterSet hbdd, fun _ hc ↦ csInf_le (isBounded_clusterSet_of_isBounded hbdd).2.1 hc⟩

/-- For any bounded sequence `s`, `seqLiminf s ≤ seqLimsup s`. -/
theorem seqLiminf_le_seqLimsup {s : ℕ → ℝ} (hbdd : Bornology.IsBounded (Set.range s)) :
    seqLiminf s ≤ seqLimsup s :=
  (isLeast_clusterSet_seqLiminf hbdd).2 (seqLimsup_mem_clusterSet hbdd)

/-- Helper for Goldblatt Theorem 6.8.2 (p. 68): for limited `x ∈ ℝ*` and `L ∈ ℝ`,
`x < L ∨ x ≈ₕ L` iff `shadow x ≤ L`. -/
theorem lt_or_infClose_iff_shadow_le {x : ℝ*} (hx : IsLimited x) {L : ℝ} :
    (x < (L : ℝ*) ∨ x ≈ₕ (L : ℝ*)) ↔ shadow x ≤ L := by
  constructor
  · rintro (hlt | hclose)
    · exact coe_le_of_infClose_le (infClose_shadow hx).symm hlt.le (InfClose.refl _)
    · exact (shadow_eq_of_infClose hclose).le
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · left
      have hpos : 0 < L - shadow x := sub_pos.2 hlt
      have h := (abs_lt.1 (infClose_shadow hx (L - shadow x) hpos)).2
      have hc : (shadow x : ℝ*) + ((L - shadow x : ℝ) : ℝ*) = (L : ℝ*) := by
        rw [← Hyperreal.coe_add, add_sub_cancel]
      linarith
    · right
      rw [← heq]
      exact infClose_shadow hx

/-- Dual helper for `seqLiminf`: for limited `x ∈ ℝ*` and `L ∈ ℝ`,
`L < x ∨ x ≈ₕ L` iff `L ≤ shadow x`. -/
theorem gt_or_infClose_iff_le_shadow {x : ℝ*} (hx : IsLimited x) {L : ℝ} :
    ((L : ℝ*) < x ∨ x ≈ₕ (L : ℝ*)) ↔ L ≤ shadow x := by
  constructor
  · rintro (hgt | hclose)
    · exact coe_le_of_infClose_le (InfClose.refl _) hgt.le (infClose_shadow hx)
    · exact (shadow_eq_of_infClose hclose).ge
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · left
      have hpos : 0 < shadow x - L := sub_pos.2 hlt
      have h := (abs_lt.1 (infClose_shadow hx (shadow x - L) hpos)).1
      have hc : (shadow x : ℝ*) - ((shadow x - L : ℝ) : ℝ*) = (L : ℝ*) := by
        rw [← Hyperreal.coe_sub, sub_sub_cancel]
      linarith
    · right
      rw [heq]
      exact infClose_shadow hx

/-- **Goldblatt Theorem 6.8.2 (p. 68)**: Nonstandard characterization of `seqLimsup s` for bounded `s`. -/
theorem eq_seqLimsup_iff_nonstandard {s : ℕ → ℝ}
    (hbdd : Bornology.IsBounded (Set.range s)) {L : ℝ} :
    L = seqLimsup s ↔
      (∀ N : ℕ*, IsUnlimitedNat N → starSeq s N < (L : ℝ*) ∨ starSeq s N ≈ₕ (L : ℝ*)) ∧
      (∃ N : ℕ*, IsUnlimitedNat N ∧ starSeq s N ≈ₕ (L : ℝ*)) := by
  have hmax := isGreatest_clusterSet_seqLimsup hbdd
  constructor
  · rintro rfl
    refine ⟨fun N hN ↦ ?_, hmax.1⟩
    have hlim := isBounded_range_iff_forall_unlimited_isLimited.1 hbdd N hN
    rw [lt_or_infClose_iff_shadow_le hlim]
    exact hmax.2 ⟨N, hN, infClose_shadow hlim⟩
  · rintro ⟨hub, hmem⟩
    apply le_antisymm
    · exact hmax.2 hmem
    · obtain ⟨N, hN, hsup⟩ := hmax.1
      have hlim := isBounded_range_iff_forall_unlimited_isLimited.1 hbdd N hN
      have hsh : shadow (starSeq s N) = seqLimsup s := shadow_eq_of_infClose hsup
      rw [← hsh]
      exact (lt_or_infClose_iff_shadow_le hlim).1 (hub N hN)

/-- Dual of Theorem 6.8.2 (p. 68): Nonstandard characterization of `seqLiminf s` for bounded `s`. -/
theorem eq_seqLiminf_iff_nonstandard {s : ℕ → ℝ}
    (hbdd : Bornology.IsBounded (Set.range s)) {L : ℝ} :
    L = seqLiminf s ↔
      (∀ N : ℕ*, IsUnlimitedNat N → (L : ℝ*) < starSeq s N ∨ starSeq s N ≈ₕ (L : ℝ*)) ∧
      (∃ N : ℕ*, IsUnlimitedNat N ∧ starSeq s N ≈ₕ (L : ℝ*)) := by
  have hmin := isLeast_clusterSet_seqLiminf hbdd
  constructor
  · rintro rfl
    refine ⟨fun N hN ↦ ?_, hmin.1⟩
    have hlim := isBounded_range_iff_forall_unlimited_isLimited.1 hbdd N hN
    rw [gt_or_infClose_iff_le_shadow hlim]
    exact hmin.2 ⟨N, hN, infClose_shadow hlim⟩
  · rintro ⟨hlb, hmem⟩
    apply le_antisymm
    · obtain ⟨N, hN, hinf⟩ := hmin.1
      have hlim := isBounded_range_iff_forall_unlimited_isLimited.1 hbdd N hN
      have hsh : shadow (starSeq s N) = seqLiminf s := shadow_eq_of_infClose hinf
      rw [← hsh]
      exact (gt_or_infClose_iff_le_shadow hlim).1 (hlb N hN)
    · exact hmin.2 hmem

/-- **Goldblatt Theorem 6.8.3 (p. 68)**: A bounded sequence `s : ℕ → ℝ` converges to `L ∈ ℝ` if
and only if `seqLimsup s = L` and `seqLiminf s = L`. -/
theorem tendsto_iff_seqLimsup_eq_seqLiminf_of_isBounded {s : ℕ → ℝ}
    (hbdd : Bornology.IsBounded (Set.range s)) {L : ℝ} :
    Tendsto s atTop (𝓝 L) ↔ seqLimsup s = L ∧ seqLiminf s = L := by
  constructor
  · intro hs
    have hcl : clusterSet s = {L} := by
      ext c
      rw [mem_clusterSet_iff_isSeqClusterPt]
      exact Set.ext_iff.1 (clusterPt_unique_of_tendsto hs) c
    simp [seqLimsup, seqLiminf, hcl]
  · rintro ⟨hsup, hinf⟩
    rw [tendsto_nhds_iff_forall_unlimited_shadow]
    intro N hN
    have hlim := isBounded_range_iff_forall_unlimited_isLimited.1 hbdd N hN
    have hmem : shadow (starSeq s N) ∈ clusterSet s := ⟨N, hN, infClose_shadow hlim⟩
    have hle : shadow (starSeq s N) ≤ L := hsup ▸ (isGreatest_clusterSet_seqLimsup hbdd).2 hmem
    have hge : L ≤ shadow (starSeq s N) := hinf ▸ (isLeast_clusterSet_seqLiminf hbdd).2 hmem
    exact ⟨hlim, le_antisymm hle hge⟩

/-- Unconditional version of Theorem 6.8.3: an arbitrary sequence `s : ℕ → ℝ` converges to `L ∈ ℝ`
iff `s` is bounded and `seqLiminf s = L` and `seqLimsup s = L`. -/
theorem tendsto_iff_isBounded_and_liminf_eq_limsup {s : ℕ → ℝ} {L : ℝ} :
    Tendsto s atTop (𝓝 L) ↔
      Bornology.IsBounded (Set.range s) ∧ seqLiminf s = L ∧ seqLimsup s = L := by
  constructor
  · intro hs
    have hbdd := isBounded_range_of_tendsto_nonstandard hs
    obtain ⟨hsup, hinf⟩ := (tendsto_iff_seqLimsup_eq_seqLiminf_of_isBounded hbdd).1 hs
    exact ⟨hbdd, hinf, hsup⟩
  · rintro ⟨hbdd, hinf, hsup⟩
    exact (tendsto_iff_seqLimsup_eq_seqLiminf_of_isBounded hbdd).2 ⟨hsup, hinf⟩

/-- **Goldblatt Theorem 6.8.4 (pp. 68–69)**: Nonstandard proof of the `ε`-properties of `seqLimsup`
using Principles (a) and (b) (`forall_isUnlimitedNat_liftPred_iff` and
`exists_isUnlimitedNat_liftPred_iff`). -/
theorem seqLimsup_eventually_lt_and_frequently_gt {s : ℕ → ℝ}
    (hbdd : Bornology.IsBounded (Set.range s)) {ε : ℝ} (hε : 0 < ε) :
    (∃ k : ℕ, ∀ n : ℕ, k ≤ n → s n < seqLimsup s + ε) ∧
    (∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ seqLimsup s - ε < s n) := by
  refine ⟨?_, ?_⟩
  · refine (forall_isUnlimitedNat_liftPred_iff (P := fun n ↦ s n < seqLimsup s + ε)).1 fun N hN ↦ ?_
    have hlim := isBounded_range_iff_forall_unlimited_isLimited.1 hbdd N hN
    have hle : shadow (starSeq s N) ≤ seqLimsup s :=
      (isGreatest_clusterSet_seqLimsup hbdd).2 ⟨N, hN, infClose_shadow hlim⟩
    have hlt_sh : shadow (starSeq s N) < seqLimsup s + ε := by linarith
    have hlt_hyp : starSeq s N < ((seqLimsup s + ε : ℝ) : ℝ*) := by
      rcases (lt_or_infClose_iff_shadow_le hlim (L := seqLimsup s + ε)).2 hlt_sh.le with hlt | hcl
      · exact hlt
      · exfalso
        exact hlt_sh.ne (shadow_eq_of_infClose hcl)
    induction N using Germ.inductionOn with | _ a =>
    exact ofSeq_lt_ofSeq.1 hlt_hyp
  · refine (exists_isUnlimitedNat_liftPred_iff (P := fun n ↦ seqLimsup s - ε < s n)).1 ?_
    obtain ⟨N, hN, hclose⟩ := seqLimsup_mem_clusterSet hbdd
    refine ⟨N, hN, ?_⟩
    have hlo := (abs_lt.1 (hclose ε hε)).1
    have hgt : ((seqLimsup s - ε : ℝ) : ℝ*) < starSeq s N := by
      rw [Hyperreal.coe_sub]
      linarith
    induction N using Germ.inductionOn with | _ a =>
    exact ofSeq_lt_ofSeq.1 hgt

/-- Complete `ε`-characterization of `seqLimsup s` for bounded `s`:
`L = seqLimsup s` iff `(∀ ε > 0, ∃ k, ∀ n ≥ k, s n < L + ε)` and
`(∀ ε > 0, ∀ k, ∃ n ≥ k, L - ε < s n)`. -/
theorem eq_seqLimsup_iff_eps {s : ℕ → ℝ} (hbdd : Bornology.IsBounded (Set.range s)) {L : ℝ} :
    L = seqLimsup s ↔
      (∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ n : ℕ, k ≤ n → s n < L + ε) ∧
      (∀ ε : ℝ, 0 < ε → ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ L - ε < s n) := by
  constructor
  · rintro rfl
    exact ⟨fun ε hε ↦ (seqLimsup_eventually_lt_and_frequently_gt hbdd hε).1,
           fun ε hε ↦ (seqLimsup_eventually_lt_and_frequently_gt hbdd hε).2⟩
  · rintro ⟨hhi, hlo⟩
    apply le_antisymm
    · by_contra hgt
      push Not at hgt
      set ε := (L - seqLimsup s) / 3
      have hε : 0 < ε := by positivity
      obtain ⟨k₁, hk₁⟩ := (seqLimsup_eventually_lt_and_frequently_gt hbdd hε).1
      obtain ⟨n, hkn, hn⟩ := hlo ε hε k₁
      have hn' := hk₁ n hkn
      linarith [show ε = (L - seqLimsup s) / 3 from rfl]
    · by_contra hlt
      push Not at hlt
      set ε := (seqLimsup s - L) / 3
      have hε : 0 < ε := by positivity
      obtain ⟨k₁, hk₁⟩ := hhi ε hε
      obtain ⟨n, hkn, hn⟩ := (seqLimsup_eventually_lt_and_frequently_gt hbdd hε).2 k₁
      have hn' := hk₁ n hkn
      linarith [show ε = (seqLimsup s - L) / 3 from rfl]

/-- **Goldblatt Exercise 6.9(2a) (p. 70)**: Dual `ε`-properties and complete characterization of
`seqLiminf s` for bounded `s`. -/
theorem seqLiminf_eventually_gt_and_frequently_lt {s : ℕ → ℝ}
    (hbdd : Bornology.IsBounded (Set.range s)) {ε : ℝ} (hε : 0 < ε) :
    (∃ k : ℕ, ∀ n : ℕ, k ≤ n → seqLiminf s - ε < s n) ∧
    (∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ s n < seqLiminf s + ε) := by
  refine ⟨?_, ?_⟩
  · refine (forall_isUnlimitedNat_liftPred_iff (P := fun n ↦ seqLiminf s - ε < s n)).1 fun N hN ↦ ?_
    have hlim := isBounded_range_iff_forall_unlimited_isLimited.1 hbdd N hN
    have hge : seqLiminf s ≤ shadow (starSeq s N) :=
      (isLeast_clusterSet_seqLiminf hbdd).2 ⟨N, hN, infClose_shadow hlim⟩
    have hgt_sh : seqLiminf s - ε < shadow (starSeq s N) := by linarith
    have hgt_hyp : ((seqLiminf s - ε : ℝ) : ℝ*) < starSeq s N := by
      rcases (gt_or_infClose_iff_le_shadow hlim (L := seqLiminf s - ε)).2 hgt_sh.le with hgt | hcl
      · exact hgt
      · exfalso
        exact hgt_sh.ne' (shadow_eq_of_infClose hcl)
    induction N using Germ.inductionOn with | _ a =>
    exact ofSeq_lt_ofSeq.1 hgt_hyp
  · refine (exists_isUnlimitedNat_liftPred_iff (P := fun n ↦ s n < seqLiminf s + ε)).1 ?_
    obtain ⟨N, hN, hclose⟩ := seqLiminf_mem_clusterSet hbdd
    refine ⟨N, hN, ?_⟩
    have hhi := (abs_lt.1 (hclose ε hε)).2
    have hlt : starSeq s N < ((seqLiminf s + ε : ℝ) : ℝ*) := by
      rw [Hyperreal.coe_add]
      linarith
    induction N using Germ.inductionOn with | _ a =>
    exact ofSeq_lt_ofSeq.1 hlt

/-- Complete `ε`-characterization of `seqLiminf s` for bounded `s`. -/
theorem eq_seqLiminf_iff_eps {s : ℕ → ℝ} (hbdd : Bornology.IsBounded (Set.range s)) {L : ℝ} :
    L = seqLiminf s ↔
      (∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ n : ℕ, k ≤ n → L - ε < s n) ∧
      (∀ ε : ℝ, 0 < ε → ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ s n < L + ε) := by
  constructor
  · rintro rfl
    exact ⟨fun ε hε ↦ (seqLiminf_eventually_gt_and_frequently_lt hbdd hε).1,
           fun ε hε ↦ (seqLiminf_eventually_gt_and_frequently_lt hbdd hε).2⟩
  · rintro ⟨hlo, hhi⟩
    apply le_antisymm
    · by_contra hgt
      push Not at hgt
      set ε := (L - seqLiminf s) / 3
      have hε : 0 < ε := by positivity
      obtain ⟨k₁, hk₁⟩ := hlo ε hε
      obtain ⟨n, hkn, hn⟩ := (seqLiminf_eventually_gt_and_frequently_lt hbdd hε).2 k₁
      have hn' := hk₁ n hkn
      linarith [show ε = (L - seqLiminf s) / 3 from rfl]
    · by_contra hlt
      push Not at hlt
      set ε := (seqLiminf s - L) / 3
      have hε : 0 < ε := by positivity
      obtain ⟨k₁, hk₁⟩ := (seqLiminf_eventually_gt_and_frequently_lt hbdd hε).1
      obtain ⟨n, hkn, hn⟩ := hhi ε hε k₁
      have hn' := hk₁ n hkn
      linarith [show ε = (seqLiminf s - L) / 3 from rfl]

/-- **Goldblatt Exercise 6.9(3) (p. 70)**: For any bounded sequence `s` and `ε > 0`, some standard
tail of `s` lies strictly inside `(seqLiminf s - ε, seqLimsup s + ε)`. -/
theorem eventually_mem_Ioo_seqLiminf_seqLimsup {s : ℕ → ℝ}
    (hbdd : Bornology.IsBounded (Set.range s)) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → seqLiminf s - ε < s n ∧ s n < seqLimsup s + ε := by
  obtain ⟨k₁, hk₁⟩ := (seqLiminf_eventually_gt_and_frequently_lt hbdd hε).1
  obtain ⟨k₂, hk₂⟩ := (seqLimsup_eventually_lt_and_frequently_gt hbdd hε).1
  exact ⟨max k₁ k₂, fun n hn ↦
    ⟨hk₁ n ((le_max_left k₁ k₂).trans hn), hk₂ n ((le_max_right k₁ k₂).trans hn)⟩⟩

/-- Goldblatt §6.8 (p. 69): Supremum `S_n = sup_{m ≥ n} s_m` of the `n`-th standard tail. -/
def tailSup (s : ℕ → ℝ) (n : ℕ) : ℝ := sSup (s '' Set.Ici n)

/-- Dual of `tailSup`: Infimum `I_n = inf_{m ≥ n} s_m` of the `n`-th standard tail. -/
def tailInf (s : ℕ → ℝ) (n : ℕ) : ℝ := sInf (s '' Set.Ici n)

/-- For bounded `s`, `tailSup s` is antitone (`S_n ≥ S_{n+1}`). -/
theorem antitone_tailSup {s : ℕ → ℝ} (hbdd : Bornology.IsBounded (Set.range s)) :
    Antitone (tailSup s) := by
  obtain ⟨B, hB⟩ := isBounded_range_iff_exists_abs_le.1 hbdd
  intro m n hmn
  unfold tailSup
  apply csSup_le_csSup
  · refine ⟨B, ?_⟩
    rintro _ ⟨k, _, rfl⟩
    exact (le_abs_self (s k)).trans (hB k)
  · exact ⟨s n, ⟨n, Set.mem_Ici.2 le_rfl, rfl⟩⟩
  · exact Set.image_mono (Set.Ici_subset_Ici.2 hmn)

/-- For bounded `s`, `Set.range (tailSup s)` is bounded below. -/
theorem bddBelow_range_tailSup {s : ℕ → ℝ} (hbdd : Bornology.IsBounded (Set.range s)) :
    BddBelow (Set.range (tailSup s)) := by
  obtain ⟨B, hB⟩ := isBounded_range_iff_exists_abs_le.1 hbdd
  refine ⟨-B, ?_⟩
  rintro _ ⟨n, rfl⟩
  unfold tailSup
  have hsn : -B ≤ s n := (abs_le.1 (hB n)).1
  have hub : BddAbove (s '' Set.Ici n) :=
    ⟨B, by rintro _ ⟨k, _, rfl⟩; exact (abs_le.1 (hB k)).2⟩
  exact hsn.trans (le_csSup hub ⟨n, Set.mem_Ici.2 le_rfl, rfl⟩)

/-- **Goldblatt Theorem 6.8.5 (pp. 69–70)**: For any bounded sequence `s`,
`seqLimsup s = lim_{n → ∞} (sup_{m ≥ n} s_m) = sInf (Set.range (tailSup s))`, proved via transfer
along an extended term infinitely close to `seqLimsup s`. -/
theorem seqLimsup_eq_sInf_tailSup {s : ℕ → ℝ} (hbdd : Bornology.IsBounded (Set.range s)) :
    seqLimsup s = sInf (Set.range (tailSup s)) := by
  obtain ⟨B, hB⟩ := isBounded_range_iff_exists_abs_le.1 hbdd
  have hstep1 : ∀ m : ℕ, seqLimsup s ≤ tailSup s m := by
    intro m
    obtain ⟨N, hN, hclose⟩ := seqLimsup_mem_clusterSet hbdd
    have hub_m : BddAbove (s '' Set.Ici m) :=
      ⟨B, by rintro _ ⟨k, _, rfl⟩; exact (abs_le.1 (hB k)).2⟩
    have hsm_le : ∀ n : ℕ, m ≤ n → s n ≤ tailSup s m :=
      fun n hmn ↦ le_csSup hub_m ⟨n, Set.mem_Ici.2 hmn, rfl⟩
    have hN_le : starSeq s N ≤ (tailSup s m : ℝ*) := by
      have hmN : (m : ℕ*) ≤ N := (hN m).le
      induction N using Germ.inductionOn with | _ a =>
      exact ofSeq_le_ofSeq.2 ((Germ.coe_le.1 hmN).mono fun i hi ↦ hsm_le (a i) hi)
    exact coe_le_of_infClose_le hclose.symm hN_le (InfClose.refl _)
  apply le_antisymm
  · exact le_csInf ⟨tailSup s 0, 0, rfl⟩ (by rintro _ ⟨m, rfl⟩; exact hstep1 m)
  · by_contra hlt
    push Not at hlt
    set ε := (sInf (Set.range (tailSup s)) - seqLimsup s) / 2
    have hε : 0 < ε := by positivity
    obtain ⟨n, hn⟩ := (seqLimsup_eventually_lt_and_frequently_gt hbdd hε).1
    have hSn_le : tailSup s n ≤ seqLimsup s + ε := by
      unfold tailSup
      apply csSup_le (s := s '' Set.Ici n) ⟨s n, ⟨n, Set.mem_Ici.2 le_rfl, rfl⟩⟩
      rintro _ ⟨k, hnk, rfl⟩
      exact (hn k hnk).le
    have hinf_le : sInf (Set.range (tailSup s)) ≤ tailSup s n :=
      csInf_le (bddBelow_range_tailSup hbdd) ⟨n, rfl⟩
    linarith [show ε = (sInf (Set.range (tailSup s)) - seqLimsup s) / 2 from rfl]

/-- **Goldblatt Theorem 6.8.5 (pp. 69–70)**: `tailSup s` converges to `seqLimsup s`. -/
theorem tendsto_tailSup_seqLimsup {s : ℕ → ℝ} (hbdd : Bornology.IsBounded (Set.range s)) :
    Tendsto (tailSup s) atTop (𝓝 (seqLimsup s)) := by
  rw [seqLimsup_eq_sInf_tailSup hbdd]
  exact tendsto_sInf_of_antitone_bddBelow (antitone_tailSup hbdd) (bddBelow_range_tailSup hbdd)

/-- **Goldblatt Exercise 6.9(2b) (p. 70)**: Dual tail-infimum convergence `tailInf s → seqLiminf s`. -/
theorem monotone_tailInf {s : ℕ → ℝ} (hbdd : Bornology.IsBounded (Set.range s)) :
    Monotone (tailInf s) := by
  obtain ⟨B, hB⟩ := isBounded_range_iff_exists_abs_le.1 hbdd
  intro m n hmn
  unfold tailInf
  apply csInf_le_csInf
  · refine ⟨-B, ?_⟩
    rintro _ ⟨k, _, rfl⟩
    exact (abs_le.1 (hB k)).1
  · exact ⟨s n, ⟨n, Set.mem_Ici.2 le_rfl, rfl⟩⟩
  · exact Set.image_mono (Set.Ici_subset_Ici.2 hmn)

/-- For bounded `s`, `Set.range (tailInf s)` is bounded above. -/
theorem bddAbove_range_tailInf {s : ℕ → ℝ} (hbdd : Bornology.IsBounded (Set.range s)) :
    BddAbove (Set.range (tailInf s)) := by
  obtain ⟨B, hB⟩ := isBounded_range_iff_exists_abs_le.1 hbdd
  refine ⟨B, ?_⟩
  rintro _ ⟨n, rfl⟩
  unfold tailInf
  have hsn : s n ≤ B := (abs_le.1 (hB n)).2
  have hlb : BddBelow (s '' Set.Ici n) :=
    ⟨-B, by rintro _ ⟨k, _, rfl⟩; exact (abs_le.1 (hB k)).1⟩
  exact (csInf_le hlb ⟨n, Set.mem_Ici.2 le_rfl, rfl⟩).trans hsn

/-- Dual of Theorem 6.8.5: `seqLiminf s = sSup (Set.range (tailInf s))`. -/
theorem seqLiminf_eq_sSup_tailInf {s : ℕ → ℝ} (hbdd : Bornology.IsBounded (Set.range s)) :
    seqLiminf s = sSup (Set.range (tailInf s)) := by
  obtain ⟨B, hB⟩ := isBounded_range_iff_exists_abs_le.1 hbdd
  have hstep1 : ∀ m : ℕ, tailInf s m ≤ seqLiminf s := by
    intro m
    obtain ⟨N, hN, hclose⟩ := seqLiminf_mem_clusterSet hbdd
    have hlb_m : BddBelow (s '' Set.Ici m) :=
      ⟨-B, by rintro _ ⟨k, _, rfl⟩; exact (abs_le.1 (hB k)).1⟩
    have hsm_ge : ∀ n : ℕ, m ≤ n → tailInf s m ≤ s n :=
      fun n hmn ↦ csInf_le hlb_m ⟨n, Set.mem_Ici.2 hmn, rfl⟩
    have hN_ge : (tailInf s m : ℝ*) ≤ starSeq s N := by
      have hmN : (m : ℕ*) ≤ N := (hN m).le
      induction N using Germ.inductionOn with | _ a =>
      exact ofSeq_le_ofSeq.2 ((Germ.coe_le.1 hmN).mono fun i hi ↦ hsm_ge (a i) hi)
    exact coe_le_of_infClose_le (InfClose.refl _) hN_ge hclose
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    set ε := (seqLiminf s - sSup (Set.range (tailInf s))) / 2
    have hε : 0 < ε := by positivity
    obtain ⟨n, hn⟩ := (seqLiminf_eventually_gt_and_frequently_lt hbdd hε).1
    have hIn_ge : seqLiminf s - ε ≤ tailInf s n := by
      unfold tailInf
      apply le_csInf (s := s '' Set.Ici n) ⟨s n, ⟨n, Set.mem_Ici.2 le_rfl, rfl⟩⟩
      rintro _ ⟨k, hnk, rfl⟩
      exact (hn k hnk).le
    have hsup_ge : tailInf s n ≤ sSup (Set.range (tailInf s)) :=
      le_csSup (bddAbove_range_tailInf hbdd) ⟨n, rfl⟩
    linarith [show ε = (seqLiminf s - sSup (Set.range (tailInf s))) / 2 from rfl]
  · exact csSup_le ⟨tailInf s 0, 0, rfl⟩ (by rintro _ ⟨m, rfl⟩; exact hstep1 m)

/-- Dual of Theorem 6.8.5: `tailInf s` converges to `seqLiminf s`. -/
theorem tendsto_tailInf_seqLiminf {s : ℕ → ℝ} (hbdd : Bornology.IsBounded (Set.range s)) :
    Tendsto (tailInf s) atTop (𝓝 (seqLiminf s)) := by
  rw [seqLiminf_eq_sSup_tailInf hbdd]
  exact tendsto_sSup_of_monotone_bddAbove (monotone_tailInf hbdd) (bddAbove_range_tailInf hbdd)

/-- **Goldblatt §6.8 Case Analysis (p. 70)**: If `s` is bounded above and does not diverge to `-∞`,
then `clusterSet s` is nonempty and bounded above. -/
theorem clusterSet_nonempty_bddAbove_of_bddAbove_not_tendsto_atBot {s : ℕ → ℝ}
    (hbdd : BddAbove (Set.range s)) (hnot : ¬ Tendsto s atTop atBot) :
    (clusterSet s).Nonempty ∧ BddAbove (clusterSet s) := by
  refine ⟨?_, bddAbove_clusterSet_of_bddAbove hbdd⟩
  rw [tendsto_atBot_iff_forall_unlimited_isNegUnlimited] at hnot
  push Not at hnot
  obtain ⟨N, hN, hnot_neg⟩ := hnot
  have hnot_pos : ¬ IsPosUnlimited (starSeq s N) :=
    bddAbove_range_iff_forall_unlimited_not_isPosUnlimited.1 hbdd N hN
  have hlim : IsLimited (starSeq s N) := by
    by_contra hunl
    rcases isUnlimited_iff_pos_or_neg.1 (isUnlimited_iff_not_isLimited.2 hunl) with hp | hn
    · exact hnot_pos hp
    · exact hnot_neg hn
  exact ⟨shadow (starSeq s N), N, hN, infClose_shadow hlim⟩

/-- **Goldblatt Exercise 6.9(1) (p. 70)**: If `s` is bounded below and does not diverge to `+∞`,
then `clusterSet s` is nonempty and bounded below. -/
theorem clusterSet_nonempty_bddBelow_of_bddBelow_not_tendsto_atTop {s : ℕ → ℝ}
    (hbdd : BddBelow (Set.range s)) (hnot : ¬ Tendsto s atTop atTop) :
    (clusterSet s).Nonempty ∧ BddBelow (clusterSet s) := by
  refine ⟨?_, bddBelow_clusterSet_of_bddBelow hbdd⟩
  rw [tendsto_atTop_iff_forall_unlimited_isPosUnlimited] at hnot
  push Not at hnot
  obtain ⟨N, hN, hnot_pos⟩ := hnot
  have hnot_neg : ¬ IsNegUnlimited (starSeq s N) :=
    bddBelow_range_iff_forall_unlimited_not_isNegUnlimited.1 hbdd N hN
  have hlim : IsLimited (starSeq s N) := by
    by_contra hunl
    rcases isUnlimited_iff_pos_or_neg.1 (isUnlimited_iff_not_isLimited.2 hunl) with hp | hn
    · exact hnot_pos hp
    · exact hnot_neg hn
  exact ⟨shadow (starSeq s N), N, hN, infClose_shadow hlim⟩

/-- **Goldblatt §6.8 (p. 70)**: Extended-real limit superior `erealSeqLimsup s ∈ EReal` defined for
any sequence `s : ℕ → ℝ`, bounded or unbounded. -/
def erealSeqLimsup (s : ℕ → ℝ) : EReal :=
  if ¬ BddAbove (Set.range s) then ⊤
  else if Tendsto s atTop atBot then ⊥
  else (seqLimsup s : EReal)

/-- **Goldblatt Exercise 6.9(1) (p. 70)**: Extended-real limit inferior `erealSeqLiminf s ∈ EReal`
defined for any sequence `s : ℕ → ℝ`, bounded or unbounded. -/
def erealSeqLiminf (s : ℕ → ℝ) : EReal :=
  if ¬ BddBelow (Set.range s) then ⊥
  else if Tendsto s atTop atTop then ⊤
  else (seqLiminf s : EReal)

/-- For bounded `s`, `erealSeqLimsup s` agrees with `(seqLimsup s : EReal)`. -/
theorem erealSeqLimsup_eq_coe_of_isBounded {s : ℕ → ℝ}
    (hbdd : Bornology.IsBounded (Set.range s)) :
    erealSeqLimsup s = (seqLimsup s : EReal) := by
  obtain ⟨B, hB⟩ := isBounded_range_iff_exists_abs_le.1 hbdd
  have hba : BddAbove (Set.range s) := ⟨B, by rintro _ ⟨n, rfl⟩; exact (abs_le.1 (hB n)).2⟩
  have hnot_bot : ¬ Tendsto s atTop atBot := by
    rw [tendsto_atBot_iff_forall_unlimited_isNegUnlimited]
    intro hneg
    have hlim := isBounded_range_iff_forall_unlimited_isLimited.1 hbdd omegaNat isUnlimitedNat_omegaNat
    have hunl : IsUnlimited (starSeq s omegaNat) :=
      isUnlimited_iff_pos_or_neg.2 (Or.inr (hneg omegaNat isUnlimitedNat_omegaNat))
    exact (isUnlimited_iff_not_isLimited.1 hunl) hlim
  simp [erealSeqLimsup, hba, hnot_bot]

/-- For bounded `s`, `erealSeqLiminf s` agrees with `(seqLiminf s : EReal)`. -/
theorem erealSeqLiminf_eq_coe_of_isBounded {s : ℕ → ℝ}
    (hbdd : Bornology.IsBounded (Set.range s)) :
    erealSeqLiminf s = (seqLiminf s : EReal) := by
  obtain ⟨B, hB⟩ := isBounded_range_iff_exists_abs_le.1 hbdd
  have hbb : BddBelow (Set.range s) := ⟨-B, by rintro _ ⟨n, rfl⟩; exact (abs_le.1 (hB n)).1⟩
  have hnot_top : ¬ Tendsto s atTop atTop := by
    rw [tendsto_atTop_iff_forall_unlimited_isPosUnlimited]
    intro hpos
    have hlim := isBounded_range_iff_forall_unlimited_isLimited.1 hbdd omegaNat isUnlimitedNat_omegaNat
    have hunl : IsUnlimited (starSeq s omegaNat) :=
      isUnlimited_iff_pos_or_neg.2 (Or.inl (hpos omegaNat isUnlimitedNat_omegaNat))
    exact (isUnlimited_iff_not_isLimited.1 hunl) hlim
  simp [erealSeqLiminf, hbb, hnot_top]

/-! ## §6.10–6.11 Infinite Series and Exercises 6.11(1)–(11) -/

/-- Goldblatt §6.10 (p. 71): `n`-th partial sum `∑_{k=0}^{n-1} a_k` of a real series `a : ℕ → ℝ`. -/
def partialSum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, a k

/-- The `0`-th partial sum of any series is `0`. -/
@[simp]
theorem partialSum_zero (a : ℕ → ℝ) : partialSum a 0 = 0 :=
  Finset.sum_range_zero a

/-- Step recurrence for partial sums: `partialSum a (n + 1) = partialSum a n + a n`. -/
@[simp]
theorem partialSum_succ (a : ℕ → ℝ) (n : ℕ) :
    partialSum a (n + 1) = partialSum a n + a n :=
  Finset.sum_range_succ a n

/-- Difference of partial sums equals the finite interval sum `∑_{k ∈ [m, n)} a_k` when `m ≤ n`. -/
theorem partialSum_sub_partialSum {a : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n) :
    partialSum a n - partialSum a m = ∑ k ∈ Finset.Ico m n, a k :=
  (Finset.sum_Ico_eq_sub a hmn).symm

/-- Goldblatt §6.10 (p. 71): Convergence of an infinite series `∑ a_k` to `L ∈ ℝ`. -/
def SeriesConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  Tendsto (partialSum a) atTop (𝓝 L)

/-- Goldblatt §6.10 (p. 71): Convergence of an infinite series `∑ a_k` in `ℝ`. -/
def SeriesConverges (a : ℕ → ℝ) : Prop :=
  ∃ L : ℝ, SeriesConvergesTo a L

/-- Goldblatt §6.10 (p. 71): Absolute convergence of `∑ a_k`, i.e., convergence of `∑ |a_k|`. -/
def SeriesAbsConverges (a : ℕ → ℝ) : Prop :=
  SeriesConverges (fun n ↦ |a n|)

/-- Goldblatt §6.10 (p. 71): Hyperfinite partial sum `∑_{k=0}^{N-1} a_k = starSeq (partialSum a) N`. -/
def hyperPartialSum (a : ℕ → ℝ) (N : ℕ*) : ℝ* :=
  starSeq (partialSum a) N

/-- Goldblatt §6.10 (p. 71): Hyperfinite tail sum `starSeq (partialSum a) N - starSeq (partialSum a) M`. -/
def hyperTailSum (a : ℕ → ℝ) (M N : ℕ*) : ℝ* :=
  starSeq (partialSum a) N - starSeq (partialSum a) M

/-- Step identity for hyperfinite partial sums: `S_{N+1} = S_N + a_N`. -/
theorem starSeq_partialSum_succ (a : ℕ → ℝ) (N : ℕ*) :
    starSeq (partialSum a) (N + 1) = starSeq (partialSum a) N + starSeq a N :=
  Germ.inductionOn N fun m ↦
    Germ.coe_eq.2 (Eventually.of_forall fun i ↦ partialSum_succ a (m i))

/-- Single-term tail identity: `S_{N+1} - S_N = a_N`. -/
theorem starSeq_partialSum_succ_sub (a : ℕ → ℝ) (N : ℕ*) :
    starSeq (partialSum a) (N + 1) - starSeq (partialSum a) N = starSeq a N := by
  rw [starSeq_partialSum_succ]
  ring

/-- **Goldblatt §6.10 Criterion 1 (p. 71)**: `∑ a_k = L` in `ℝ` if and only if every unlimited
hyperfinite partial sum `starSeq (partialSum a) N` is infinitely close to `L`. -/
theorem seriesConvergesTo_iff_forall_unlimited_infClose {a : ℕ → ℝ} {L : ℝ} :
    SeriesConvergesTo a L ↔
      ∀ N : ℕ*, IsUnlimitedNat N → starSeq (partialSum a) N ≈ₕ (L : ℝ*) :=
  tendsto_nhds_iff_forall_unlimited_infClose

/-- **Goldblatt §6.10 Shadow Formula (p. 71)**: If `∑ a_k = L`, then `L = shadow (starSeq (partialSum a) N)`
for every unlimited `N ∈ *ℕ_∞`. -/
theorem shadow_starSeq_partialSum_of_seriesConvergesTo {a : ℕ → ℝ} {L : ℝ}
    (ha : SeriesConvergesTo a L) {N : ℕ*} (hN : IsUnlimitedNat N) :
    shadow (starSeq (partialSum a) N) = L :=
  (tendsto_nhds_iff_forall_unlimited_shadow.1 ha N hN).2

/-- **Goldblatt §6.10 Criterion 2 — Nonstandard Cauchy Tail Criterion for Series (p. 71)**:
`∑ a_k` converges in `ℝ` iff `starSeq (partialSum a) N - starSeq (partialSum a) M ≈ₕ 0` for all
unlimited `M, N ∈ *ℕ_∞` with `M ≤ N`. -/
theorem seriesConverges_iff_forall_unlimited_tail_infClose_zero {a : ℕ → ℝ} :
    SeriesConverges a ↔
      ∀ M N : ℕ*, IsUnlimitedNat M → M ≤ N →
        starSeq (partialSum a) N - starSeq (partialSum a) M ≈ₕ 0 := by
  unfold SeriesConverges SeriesConvergesTo
  rw [← cauchySeq_iff_exists_tendsto_nonstandard, cauchySeq_iff_forall_unlimited_infClose]
  constructor
  · intro h M N hM hMN
    have hN : IsUnlimitedNat N := isUnlimitedNat_of_le hM hMN
    rw [infClose_zero_iff]
    exact h N M hN hM
  · intro h M N hM hN
    rcases le_total M N with hMN | hNM
    · have hclose : starSeq (partialSum a) N ≈ₕ starSeq (partialSum a) M :=
        infClose_zero_iff.1 (h M N hM hMN)
      exact hclose.symm
    · exact infClose_zero_iff.1 (h N M hN hNM)

/-- **Goldblatt §6.10 Vanishing General Term (p. 71)** (nonstandard form):
If `∑ a_k` converges, then `starSeq a N ≈ₕ 0` for every unlimited `N ∈ *ℕ_∞`. -/
theorem starSeq_infClose_zero_of_seriesConverges {a : ℕ → ℝ} (ha : SeriesConverges a)
    {N : ℕ*} (hN : IsUnlimitedNat N) : starSeq a N ≈ₕ 0 := by
  have htail := seriesConverges_iff_forall_unlimited_tail_infClose_zero.1 ha N (N + 1)
    hN (le_add_right_hypernat N 1)
  rwa [starSeq_partialSum_succ_sub] at htail

/-- **Goldblatt §6.10 Vanishing General Term (p. 71)** (standard form):
If `∑ a_k` converges in `ℝ`, then `lim_{n → ∞} a_n = 0`. -/
theorem tendsto_zero_of_seriesConverges {a : ℕ → ℝ} (ha : SeriesConverges a) :
    Tendsto a atTop (𝓝 0) :=
  tendsto_nhds_iff_forall_unlimited_infClose.2 fun _ hN ↦
    starSeq_infClose_zero_of_seriesConverges ha hN

/-- **Goldblatt §6.10 Absolute Convergence Theorem (p. 71)**: Every absolutely convergent real
series is convergent, proved via transfer of the triangle inequality on hyperfinite tails. -/
theorem seriesConverges_of_seriesAbsConverges {a : ℕ → ℝ} (ha : SeriesAbsConverges a) :
    SeriesConverges a := by
  rw [seriesConverges_iff_forall_unlimited_tail_infClose_zero]
  intro M N hM hMN
  have htail_abs :
      IsInfinitesimal
        (starSeq (partialSum (fun k ↦ |a k|)) N - starSeq (partialSum (fun k ↦ |a k|)) M) :=
    infClose_zero_iff.1
      (seriesConverges_iff_forall_unlimited_tail_infClose_zero.1 ha M N hM hMN)
  rw [infClose_zero_iff]
  refine isInfinitesimal_of_abs_le htail_abs ?_
  induction M using Germ.inductionOn with | _ u =>
  induction N using Germ.inductionOn with | _ v =>
  have huv : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), u i ≤ v i := Germ.coe_le.1 hMN
  refine ofSeq_le_ofSeq.2 (huv.mono fun i hi ↦ ?_)
  change |partialSum a (v i) - partialSum a (u i)| ≤
    |partialSum (fun k ↦ |a k|) (v i) - partialSum (fun k ↦ |a k|) (u i)|
  rw [partialSum_sub_partialSum hi, partialSum_sub_partialSum hi]
  exact (Finset.abs_sum_le_sum_abs a (Finset.Ico (u i) (v i))).trans (le_abs_self _)

/-- General term `1 / (n + 1)` of the harmonic series. -/
def harmonicTerm (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- Oresme's grouping inequality for standard partial sums of the harmonic series (`n ≥ 1`):
`partialSum harmonicTerm (2 * n) - partialSum harmonicTerm n ≥ 1 / 2`. -/
theorem harmonic_oresme_grouping_real {n : ℕ} (hn : 1 ≤ n) :
    (1 / 2 : ℝ) ≤ partialSum harmonicTerm (2 * n) - partialSum harmonicTerm n := by
  rw [partialSum_sub_partialSum (by omega : n ≤ 2 * n)]
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hterm : ∀ k ∈ Finset.Ico n (2 * n), 1 / (2 * (n : ℝ)) ≤ harmonicTerm k := by
    intro k hk
    have hk_lt : k < 2 * n := (Finset.mem_Ico.1 hk).2
    have hk_le : (k : ℝ) + 1 ≤ 2 * (n : ℝ) := by
      have : k + 1 ≤ 2 * n := by omega
      exact_mod_cast this
    unfold harmonicTerm
    exact one_div_le_one_div_of_le (by positivity) hk_le
  have hsum_ge :
      ∑ _k ∈ Finset.Ico n (2 * n), (1 / (2 * (n : ℝ))) ≤
        ∑ k ∈ Finset.Ico n (2 * n), harmonicTerm k :=
    Finset.sum_le_sum hterm
  have hconst :
      ∑ _k ∈ Finset.Ico n (2 * n), (1 / (2 * (n : ℝ))) = (1 / 2 : ℝ) := by
    rw [Finset.sum_const, Nat.card_Ico, show 2 * n - n = n by omega, nsmul_eq_mul]
    field_simp [hn_pos.ne']
  linarith

/-- Nonstandard Oresme grouping inequality: for any unlimited `N ∈ *ℕ_∞`,
`starSeq (partialSum harmonicTerm) (2 * N) - starSeq (partialSum harmonicTerm) N ≥ 1 / 2`. -/
theorem harmonic_oresme_grouping_hyperreal {N : ℕ*} (hN : IsUnlimitedNat N) :
    ((1 / 2 : ℝ) : ℝ*) ≤
      starSeq (partialSum harmonicTerm) (2 * N) - starSeq (partialSum harmonicTerm) N := by
  have h1 : (1 : ℕ*) ≤ N := (hN 1).le
  induction N using Germ.inductionOn with | _ a =>
  have ha : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 1 ≤ a i := Germ.coe_le.1 h1
  exact ofSeq_le_ofSeq.2 (ha.mono fun i hi ↦ harmonic_oresme_grouping_real hi)

/-- **Divergence of the Harmonic Series** via Oresme grouping and the nonstandard Cauchy tail
criterion. -/
theorem harmonic_series_diverges : ¬ SeriesConverges harmonicTerm := by
  intro hconv
  have hle : omegaNat ≤ 2 * omegaNat :=
    Germ.coe_le.2 (Eventually.of_forall fun i ↦ by change i ≤ 2 * i; omega)
  have htail := seriesConverges_iff_forall_unlimited_tail_infClose_zero.1 hconv
    omegaNat (2 * omegaNat) isUnlimitedNat_omegaNat hle
  have hge := harmonic_oresme_grouping_hyperreal isUnlimitedNat_omegaNat
  have hbad : (1 / 2 : ℝ) ≤ 0 :=
    coe_le_of_infClose_le (InfClose.refl _) hge htail
  norm_num at hbad

/-- **Goldblatt Exercise 6.11(1) (p. 71)**: There exists a real series (`harmonicTerm`) that
diverges even though `starSeq a N` is infinitesimal for every unlimited `N ∈ *ℕ_∞`. -/
theorem exists_divergent_series_with_infinitesimal_terms :
    ∃ a : ℕ → ℝ,
      (∀ N : ℕ*, IsUnlimitedNat N → IsInfinitesimal (starSeq a N)) ∧ ¬ SeriesConverges a := by
  refine ⟨harmonicTerm, fun N hN ↦ ?_, harmonic_series_diverges⟩
  unfold harmonicTerm
  have h0 := tendsto_nhds_iff_forall_unlimited_infClose.1
    tendsto_one_div_add_one_zero_nonstandard N hN
  simpa [InfClose] using h0

/-- **Goldblatt Exercise 6.11(2a) (p. 71)**: Termwise addition of convergent series (nonstandard proof). -/
theorem seriesConvergesTo_add {a b : ℕ → ℝ} {L M : ℝ}
    (ha : SeriesConvergesTo a L) (hb : SeriesConvergesTo b M) :
    SeriesConvergesTo (fun i ↦ a i + b i) (L + M) := by
  rw [seriesConvergesTo_iff_forall_unlimited_infClose] at ha hb ⊢
  intro N hN
  have hsum : partialSum (fun i ↦ a i + b i) = fun n ↦ partialSum a n + partialSum b n := by
    ext n
    exact Finset.sum_add_distrib
  rw [hsum, starSeq_add, Hyperreal.coe_add]
  exact (ha N hN).add (hb N hN)

/-- **Goldblatt Exercise 6.11(2b) (p. 71)**: Termwise subtraction of convergent series. -/
theorem seriesConvergesTo_sub {a b : ℕ → ℝ} {L M : ℝ}
    (ha : SeriesConvergesTo a L) (hb : SeriesConvergesTo b M) :
    SeriesConvergesTo (fun i ↦ a i - b i) (L - M) := by
  rw [seriesConvergesTo_iff_forall_unlimited_infClose] at ha hb ⊢
  intro N hN
  have hsub : partialSum (fun i ↦ a i - b i) = fun n ↦ partialSum a n - partialSum b n := by
    ext n
    exact Finset.sum_sub_distrib _ _
  rw [hsub, starSeq_sub, Hyperreal.coe_sub]
  exact (ha N hN).sub (hb N hN)

/-- **Goldblatt Exercise 6.11(2c) (p. 71)**: Scalar multiplication of a convergent series. -/
theorem seriesConvergesTo_const_mul (c : ℝ) {a : ℕ → ℝ} {L : ℝ}
    (ha : SeriesConvergesTo a L) :
    SeriesConvergesTo (fun i ↦ c * a i) (c * L) := by
  rw [seriesConvergesTo_iff_forall_unlimited_infClose] at ha ⊢
  intro N hN
  have hmul : partialSum (fun i ↦ c * a i) = fun n ↦ c * partialSum a n := by
    ext n
    exact (Finset.mul_sum (Finset.range n) a c).symm
  rw [hmul, starSeq_const_mul, Hyperreal.coe_mul]
  exact InfClose.mul_left_of_isLimited (isLimited_coe c) (ha N hN)

/-- Monotonicity of `partialSum a` for nonnegative series `∀ i, 0 ≤ a i`. -/
theorem monotone_partialSum_of_nonneg {a : ℕ → ℝ} (ha : ∀ i : ℕ, 0 ≤ a i) :
    Monotone (partialSum a) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [partialSum_succ]
  linarith [ha n]

/-- **Goldblatt Exercise 6.11(3a) (p. 72)**: For nonnegative `a_i ≥ 0`, `∑ a_i` converges iff
`starSeq (partialSum a) N` is limited for *all* unlimited `N ∈ *ℕ_∞`. -/
theorem seriesConverges_nonneg_iff_forall_unlimited_isLimited {a : ℕ → ℝ}
    (ha : ∀ i : ℕ, 0 ≤ a i) :
    SeriesConverges a ↔ ∀ N : ℕ*, IsUnlimitedNat N → IsLimited (starSeq (partialSum a) N) := by
  constructor
  · rintro ⟨L, hL⟩
    exact isBounded_range_iff_forall_unlimited_isLimited.1
      (isBounded_range_of_tendsto_nonstandard hL)
  · intro hlim
    have hbdd : Bornology.IsBounded (Set.range (partialSum a)) :=
      isBounded_range_iff_forall_unlimited_isLimited.2 hlim
    obtain ⟨B, hB⟩ := isBounded_range_iff_exists_abs_le.1 hbdd
    have hub : BddAbove (Set.range (partialSum a)) :=
      ⟨B, by rintro _ ⟨n, rfl⟩; exact (abs_le.1 (hB n)).2⟩
    exact ⟨sSup (Set.range (partialSum a)),
      tendsto_sSup_of_monotone_bddAbove (monotone_partialSum_of_nonneg ha) hub⟩

/-- **Goldblatt Exercise 6.11(3b) (p. 72)**: For nonnegative `a_i ≥ 0`, `∑ a_i` converges iff
`starSeq (partialSum a) N` is limited for *some* unlimited `N ∈ *ℕ_∞`. -/
theorem seriesConverges_nonneg_iff_exists_unlimited_isLimited {a : ℕ → ℝ}
    (ha : ∀ i : ℕ, 0 ≤ a i) :
    SeriesConverges a ↔ ∃ N : ℕ*, IsUnlimitedNat N ∧ IsLimited (starSeq (partialSum a) N) := by
  constructor
  · intro hconv
    exact ⟨omegaNat, isUnlimitedNat_omegaNat,
      (seriesConverges_nonneg_iff_forall_unlimited_isLimited ha).1 hconv
        omegaNat isUnlimitedNat_omegaNat⟩
  · rintro ⟨N, hN, hlim⟩
    obtain ⟨B, _, hB⟩ := isLimited_iff_abs_le_real.1 hlim
    have hmono := monotone_partialSum_of_nonneg ha
    have hub : BddAbove (Set.range (partialSum a)) := by
      refine ⟨B, ?_⟩
      rintro _ ⟨k, rfl⟩
      have hkN : (partialSum a k : ℝ*) ≤ starSeq (partialSum a) N := by
        simpa using starSeq_mono hmono (hN k).le
      have hkB : (partialSum a k : ℝ*) ≤ (B : ℝ*) :=
        (hkN.trans (le_abs_self _)).trans hB
      exact Hyperreal.coe_le_coe.1 hkB
    exact ⟨sSup (Set.range (partialSum a)), tendsto_sSup_of_monotone_bddAbove hmono hub⟩

/-- **Goldblatt Exercise 6.11(4) — Comparison Test (p. 72)**: If `0 ≤ a_i ≤ b_i` for all `i ∈ ℕ`
and `∑ b_i` converges, then `∑ a_i` converges (proved via Exercise 6.11(3)). -/
theorem seriesConverges_of_nonneg_le {a b : ℕ → ℝ}
    (ha : ∀ i : ℕ, 0 ≤ a i) (hab : ∀ i : ℕ, a i ≤ b i) (hb : SeriesConverges b) :
    SeriesConverges a := by
  have hb_nn : ∀ i : ℕ, 0 ≤ b i := fun i ↦ (ha i).trans (hab i)
  rw [seriesConverges_nonneg_iff_exists_unlimited_isLimited ha]
  have hb_lim : IsLimited (starSeq (partialSum b) omegaNat) :=
    (seriesConverges_nonneg_iff_forall_unlimited_isLimited hb_nn).1 hb
      omegaNat isUnlimitedNat_omegaNat
  refine ⟨omegaNat, isUnlimitedNat_omegaNat, isLimited_of_abs_le hb_lim ?_⟩
  have hpa_nn : 0 ≤ starSeq (partialSum a) omegaNat :=
    coe_le_starSeq_of_forall_le (fun n ↦ Finset.sum_nonneg fun k _ ↦ ha k) omegaNat
  have hpb_nn : 0 ≤ starSeq (partialSum b) omegaNat :=
    coe_le_starSeq_of_forall_le (fun n ↦ Finset.sum_nonneg fun k _ ↦ hb_nn k) omegaNat
  rw [abs_of_nonneg hpa_nn, abs_of_nonneg hpb_nn]
  exact starSeq_le_of_forall_le (fun n ↦ Finset.sum_le_sum fun k _ ↦ hab k) omegaNat

/-- **Goldblatt Exercise 6.11(5b) (p. 72)**: `starSeq a N ≤ starSeq b N` for all unlimited
`N ∈ *ℕ_∞` iff there exists `k ∈ ℕ` such that `a n ≤ b n` for all `n ≥ k`. -/
theorem forall_unlimited_starSeq_le_iff_eventually_le {a b : ℕ → ℝ} :
    (∀ N : ℕ*, IsUnlimitedNat N → starSeq a N ≤ starSeq b N) ↔
      ∃ k : ℕ, ∀ n : ℕ, k ≤ n → a n ≤ b n := by
  rw [← forall_isUnlimitedNat_liftPred_iff (P := fun n ↦ a n ≤ b n)]
  constructor <;> intro h N hN
  · have hle := h N hN
    induction N using Germ.inductionOn with | _ u =>
    exact ofSeq_le_ofSeq.1 hle
  · have hP := h N hN
    induction N using Germ.inductionOn with | _ u =>
    exact ofSeq_le_ofSeq.2 hP

/-- **Goldblatt Exercise 6.11(5a) — Asymptotic Nonstandard Comparison Test (p. 72)**:
If `0 ≤ starSeq a N ≤ starSeq b N` for all unlimited `N ∈ *ℕ_∞` and `∑ b_i` converges, then
`∑ a_i` converges (proved via the Cauchy tail criterion). -/
theorem seriesConverges_of_unlimited_nonneg_le {a b : ℕ → ℝ}
    (ha : ∀ N : ℕ*, IsUnlimitedNat N → 0 ≤ starSeq a N)
    (hab : ∀ N : ℕ*, IsUnlimitedNat N → starSeq a N ≤ starSeq b N)
    (hb : SeriesConverges b) : SeriesConverges a := by
  obtain ⟨k₁, hk₁⟩ := (forall_unlimited_starSeq_le_iff_eventually_le (a := fun _ ↦ 0) (b := a)).1
    fun N hN ↦ by simpa using ha N hN
  obtain ⟨k₂, hk₂⟩ := forall_unlimited_starSeq_le_iff_eventually_le.1 hab
  let k := max k₁ k₂
  rw [seriesConverges_iff_forall_unlimited_tail_infClose_zero]
  intro M N hM hMN
  have htail_b : IsInfinitesimal (starSeq (partialSum b) N - starSeq (partialSum b) M) :=
    infClose_zero_iff.1
      (seriesConverges_iff_forall_unlimited_tail_infClose_zero.1 hb M N hM hMN)
  rw [infClose_zero_iff]
  refine isInfinitesimal_of_abs_le htail_b ?_
  have hkM : (k : ℕ*) ≤ M := (hM k).le
  induction M using Germ.inductionOn with | _ u =>
  induction N using Germ.inductionOn with | _ v =>
  have hku : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), k ≤ u i := Germ.coe_le.1 hkM
  have huv : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), u i ≤ v i := Germ.coe_le.1 hMN
  refine ofSeq_le_ofSeq.2 ((hku.and huv).mono fun i ⟨hi_k, hi_uv⟩ ↦ ?_)
  change |partialSum a (v i) - partialSum a (u i)| ≤ |partialSum b (v i) - partialSum b (u i)|
  rw [partialSum_sub_partialSum hi_uv, partialSum_sub_partialSum hi_uv]
  have hsum_nn : 0 ≤ ∑ j ∈ Finset.Ico (u i) (v i), a j := by
    refine Finset.sum_nonneg fun j hj ↦ hk₁ j ?_
    exact (le_max_left k₁ k₂).trans (hi_k.trans (Finset.mem_Ico.1 hj).1)
  have hsum_le :
      ∑ j ∈ Finset.Ico (u i) (v i), a j ≤ ∑ j ∈ Finset.Ico (u i) (v i), b j := by
    refine Finset.sum_le_sum fun j hj ↦ hk₂ j ?_
    exact (le_max_right k₁ k₂).trans (hi_k.trans (Finset.mem_Ico.1 hj).1)
  rw [abs_of_nonneg hsum_nn, abs_of_nonneg (hsum_nn.trans hsum_le)]
  exact hsum_le

/-- **Goldblatt Exercise 6.11(6) — Limit Comparison Test (one-way, arbitrary limit `L`, p. 72)**:
If `a_i > 0`, `b_i > 0`, and `a_i / b_i → L` in `ℝ`, then for all unlimited `M ≤ N`,
infinitesimality of `∑_M^N b_i` implies infinitesimality of `∑_M^N a_i`, so `∑ b_i` convergent
implies `∑ a_i` convergent. -/
theorem limit_comparison_one_way {a b : ℕ → ℝ} {L : ℝ}
    (ha : ∀ i : ℕ, 0 < a i) (hb : ∀ i : ℕ, 0 < b i)
    (hlim : Tendsto (fun i ↦ a i / b i) atTop (𝓝 L)) :
    (∀ M N : ℕ*, IsUnlimitedNat M → M ≤ N →
      starSeq (partialSum b) N - starSeq (partialSum b) M ≈ₕ 0 →
      starSeq (partialSum a) N - starSeq (partialSum a) M ≈ₕ 0) ∧
    (SeriesConverges b → SeriesConverges a) := by
  have hL_nn : 0 ≤ L := le_of_tendsto_of_tendsto_nonstandard
    (tendsto_const_nonstandard 0) hlim (fun i ↦ div_nonneg (ha i).le (hb i).le)
  obtain ⟨k, hk⟩ := (tendsto_nhds_iff_seqConvergesTo.1 hlim) 1 one_pos
  have hab_ev : ∀ n : ℕ, k ≤ n → a n ≤ (L + 1) * b n := by
    intro n hn
    have hlt : a n / b n < L + 1 := by linarith [(abs_lt.1 (hk n hn)).2]
    exact (div_lt_iff₀ (hb n)).1 hlt |>.le
  have htail : ∀ M N : ℕ*, IsUnlimitedNat M → M ≤ N →
      starSeq (partialSum b) N - starSeq (partialSum b) M ≈ₕ 0 →
      starSeq (partialSum a) N - starSeq (partialSum a) M ≈ₕ 0 := by
    intro M N hM hMN hb_inf
    have hscaled : IsInfinitesimal
        (((L + 1 : ℝ) : ℝ*) * (starSeq (partialSum b) N - starSeq (partialSum b) M)) :=
      (isLimited_coe (L + 1)).mul_isInfinitesimal (infClose_zero_iff.1 hb_inf)
    rw [infClose_zero_iff]
    refine isInfinitesimal_of_abs_le hscaled ?_
    have hkM : (k : ℕ*) ≤ M := (hM k).le
    induction M using Germ.inductionOn with | _ u =>
    induction N using Germ.inductionOn with | _ v =>
    have hku : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), k ≤ u i := Germ.coe_le.1 hkM
    have huv : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), u i ≤ v i := Germ.coe_le.1 hMN
    refine ofSeq_le_ofSeq.2 ((hku.and huv).mono fun i ⟨hi_k, hi_uv⟩ ↦ ?_)
    change |partialSum a (v i) - partialSum a (u i)| ≤
      |(L + 1) * (partialSum b (v i) - partialSum b (u i))|
    rw [partialSum_sub_partialSum hi_uv, partialSum_sub_partialSum hi_uv, Finset.mul_sum]
    have hnn_a : 0 ≤ ∑ j ∈ Finset.Ico (u i) (v i), a j :=
      Finset.sum_nonneg fun j _ ↦ (ha j).le
    have hle : ∑ j ∈ Finset.Ico (u i) (v i), a j ≤
        ∑ j ∈ Finset.Ico (u i) (v i), (L + 1) * b j :=
      Finset.sum_le_sum fun j hj ↦ hab_ev j (hi_k.trans (Finset.mem_Ico.1 hj).1)
    rw [abs_of_nonneg hnn_a, abs_of_nonneg (hnn_a.trans hle)]
    exact hle
  refine ⟨htail, fun hb_conv ↦ ?_⟩
  rw [seriesConverges_iff_forall_unlimited_tail_infClose_zero] at hb_conv ⊢
  exact fun M N hM hMN ↦ htail M N hM hMN (hb_conv M N hM hMN)

/-- **Goldblatt Exercise 6.11(6) — Limit Comparison Test (`0 < L` equivalence, p. 72)**:
When `a_i > 0`, `b_i > 0`, and `a_i / b_i → L > 0`, the hyperfinite tails of `a` and `b` are
infinitesimal iff each other, so `SeriesConverges a ↔ SeriesConverges b`. -/
theorem limit_comparison_iff {a b : ℕ → ℝ} {L : ℝ}
    (ha : ∀ i : ℕ, 0 < a i) (hb : ∀ i : ℕ, 0 < b i)
    (hlim : Tendsto (fun i ↦ a i / b i) atTop (𝓝 L)) (hL : 0 < L) :
    (∀ M N : ℕ*, IsUnlimitedNat M → M ≤ N →
      (starSeq (partialSum a) N - starSeq (partialSum a) M ≈ₕ 0 ↔
       starSeq (partialSum b) N - starSeq (partialSum b) M ≈ₕ 0)) ∧
    (SeriesConverges a ↔ SeriesConverges b) := by
  have h1 := limit_comparison_one_way ha hb hlim
  have hinv_eq : (fun i ↦ b i / a i) = fun i ↦ 1 / (a i / b i) := by
    ext i
    field_simp [(ha i).ne', (hb i).ne']
  have hlim_inv : Tendsto (fun i ↦ b i / a i) atTop (𝓝 (1 / L)) := by
    rw [hinv_eq]
    exact tendsto_div_nonstandard (tendsto_const_nonstandard 1) hlim hL.ne'
  have h2 := limit_comparison_one_way hb ha hlim_inv
  exact ⟨fun M N hM hMN ↦ ⟨h2.1 M N hM hMN, h1.1 M N hM hMN⟩, ⟨h2.2, h1.2⟩⟩

/-- Geometric sum identity for `partialSum (fun k ↦ c ^ k) n` when `c ≠ 1`. -/
theorem partialSum_geom_eq {c : ℝ} (hc : c ≠ 1) (n : ℕ) :
    partialSum (fun k ↦ c ^ k) n = (1 - c ^ n) / (1 - c) := by
  have h1c : 1 - c ≠ 0 := sub_ne_zero.2 hc.symm
  induction n with
  | zero =>
      simp
  | succ m ih =>
      rw [partialSum_succ, ih, pow_succ]
      field_simp [h1c]
      ring

/-- **Goldblatt Exercise 6.11(7a) — Geometric Series (p. 72)**:
For `|c| < 1`, `∑_{k=0}^∞ c^k = 1 / (1 - c)` via unlimited hypernatural `N` and `c^N ≈ₕ 0`. -/
theorem geometric_series_convergesTo {c : ℝ} (hc : |c| < 1) :
    SeriesConvergesTo (fun k ↦ c ^ k) (1 / (1 - c)) := by
  have hc1 : c ≠ 1 := by
    rintro rfl
    simp at hc
  have h1c : 1 - c ≠ 0 := sub_ne_zero.2 hc1.symm
  rw [seriesConvergesTo_iff_forall_unlimited_infClose]
  intro N hN
  have heq : starSeq (partialSum (fun k ↦ c ^ k)) N =
      (1 - starSeq (fun k ↦ c ^ k) N) / ((1 - c : ℝ) : ℝ*) :=
    Germ.inductionOn N fun m ↦
      Germ.coe_eq.2 (Eventually.of_forall fun i ↦ partialSum_geom_eq hc1 (m i))
  rw [heq]
  have hpow : starSeq (fun k ↦ c ^ k) N ≈ₕ (0 : ℝ*) :=
    infClose_zero_iff.2 (isInfinitesimal_starSeq_pow hc hN)
  have hnum : (1 : ℝ*) - starSeq (fun k ↦ c ^ k) N ≈ₕ (1 : ℝ*) := by
    simpa using (InfClose.refl (1 : ℝ*)).sub hpow
  have htarget : ((1 / (1 - c) : ℝ) : ℝ*) = (1 : ℝ*) / ((1 - c : ℝ) : ℝ*) := by
    rw [Hyperreal.coe_div, Hyperreal.coe_one]
  rw [htarget]
  exact (InfClose.div (isLimited_coe 1) (isAppreciable_coe_iff.2 h1c)
    hnum.symm (InfClose.refl _)).symm

/-- **Goldblatt Exercise 6.11(7b) (p. 72)**: For `|c| < 1` and unlimited `M ≤ N`, the hyperfinite
geometric tail `starSeq (partialSum (c ^ ·)) N - starSeq (partialSum (c ^ ·)) M` is infinitesimal. -/
theorem geometric_series_tail_infClose_zero {c : ℝ} (hc : |c| < 1)
    {M N : ℕ*} (hM : IsUnlimitedNat M) (hMN : M ≤ N) :
    starSeq (partialSum (fun k ↦ c ^ k)) N - starSeq (partialSum (fun k ↦ c ^ k)) M ≈ₕ 0 :=
  seriesConverges_iff_forall_unlimited_tail_infClose_zero.1
    ⟨1 / (1 - c), geometric_series_convergesTo hc⟩ M N hM hMN

/-- **Goldblatt Exercise 6.11(8a) (p. 72)**: If `a_i ≠ 0` and the bounded ratio sequence
`|a_{i+1}| / |a_i|` has `seqLimsup < 1`, then there exists `0 < c < 1` such that
`|starSeq a (N + 1)| < c * |starSeq a N|` for all unlimited `N ∈ *ℕ_∞`. -/
theorem ratio_test_step_a {a : ℕ → ℝ} (ha : ∀ n : ℕ, a n ≠ 0)
    (hbdd : Bornology.IsBounded (Set.range (fun n ↦ |a (n + 1)| / |a n|)))
    (hsup : seqLimsup (fun n ↦ |a (n + 1)| / |a n|) < 1) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      ∀ N : ℕ*, IsUnlimitedNat N →
        |starSeq a (N + 1)| < (c : ℝ*) * |starSeq a N| := by
  let r : ℕ → ℝ := fun n ↦ |a (n + 1)| / |a n|
  have hr_nn : 0 ≤ seqLimsup r := by
    obtain ⟨L, hL⟩ := clusterSet_nonempty_of_isBounded hbdd
    have h0L : 0 ≤ L := le_clusterSet_of_lowerBound
      (fun n ↦ div_nonneg (abs_nonneg _) (abs_nonneg _)) hL
    exact h0L.trans ((isGreatest_clusterSet_seqLimsup hbdd).2 hL)
  let c : ℝ := (seqLimsup r + 1) / 2
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 := by
    change (seqLimsup r + 1) / 2 < 1
    linarith
  have hrc : seqLimsup r < c := by
    change seqLimsup r < (seqLimsup r + 1) / 2
    linarith
  refine ⟨c, hc0, hc1, fun N hN ↦ ?_⟩
  have hlim := isBounded_range_iff_forall_unlimited_isLimited.1 hbdd N hN
  have hsh_le : shadow (starSeq r N) ≤ seqLimsup r :=
    (isGreatest_clusterSet_seqLimsup hbdd).2 ⟨N, hN, infClose_shadow hlim⟩
  have hsh_lt : shadow (starSeq r N) < c := hsh_le.trans_lt hrc
  have hr_lt : starSeq r N < (c : ℝ*) := by
    rcases (lt_or_infClose_iff_shadow_le hlim (L := c)).2 hsh_lt.le with hlt | hcl
    · exact hlt
    · exfalso
      exact hsh_lt.ne (shadow_eq_of_infClose hcl)
  induction N using Germ.inductionOn with | _ u =>
  have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), |a (u i + 1)| / |a (u i)| < c :=
    ofSeq_lt_ofSeq.1 hr_lt
  refine ofSeq_lt_ofSeq.2 (hev.mono fun i hi ↦ ?_)
  exact (div_lt_iff₀ (abs_pos.2 (ha (u i)))).1 hi

/-- **Goldblatt Exercise 6.11(8b) (p. 72)**: Transferring `|starSeq a (N + 1)| < c * |starSeq a N|`
from `*ℕ_∞` yields a standard threshold `k ∈ ℕ` such that `|a (n + 1)| < c * |a n|` for all `n ≥ k`. -/
theorem ratio_test_step_b {a : ℕ → ℝ} {c : ℝ}
    (hN : ∀ N : ℕ*, IsUnlimitedNat N → |starSeq a (N + 1)| < (c : ℝ*) * |starSeq a N|) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → |a (n + 1)| < c * |a n| := by
  refine (forall_isUnlimitedNat_liftPred_iff (P := fun n ↦ |a (n + 1)| < c * |a n|)).1 fun N hunl ↦ ?_
  have hlt := hN N hunl
  induction N using Germ.inductionOn with | _ u =>
  exact ofSeq_lt_ofSeq.1 hlt

/-- **Goldblatt Exercise 6.11(8c) (p. 72)**: From `|a (n + 1)| < c * |a n|` for `n ≥ k` (with `c ≥ 0`),
one gets `|a (k + j)| ≤ c ^ j * |a k|` and the geometric tail bound for `k ≤ m ≤ n`. -/
theorem ratio_test_step_c {a : ℕ → ℝ} {c : ℝ} (hc0 : 0 ≤ c) {k : ℕ}
    (hk : ∀ n : ℕ, k ≤ n → |a (n + 1)| < c * |a n|) :
    (∀ j : ℕ, |a (k + j)| ≤ c ^ j * |a k|) ∧
    (∀ m n : ℕ, k ≤ m → m ≤ n →
      partialSum (fun i ↦ |a i|) n - partialSum (fun i ↦ |a i|) m ≤
        |a k| * (partialSum (fun j ↦ c ^ j) (n - k) - partialSum (fun j ↦ c ^ j) (m - k))) := by
  have hpow : ∀ j : ℕ, |a (k + j)| ≤ c ^ j * |a k| := by
    intro j
    induction j with
    | zero =>
        simp
    | succ d ih =>
        have hstep : |a (k + d + 1)| < c * |a (k + d)| := hk (k + d) (Nat.le_add_right k d)
        calc |a (k + (d + 1))|
            = |a (k + d + 1)| := by rw [Nat.add_assoc]
          _ ≤ c * |a (k + d)| := hstep.le
          _ ≤ c * (c ^ d * |a k|) := mul_le_mul_of_nonneg_left ih hc0
          _ = c ^ (d + 1) * |a k| := by rw [pow_succ']; ring
  refine ⟨hpow, fun m n hkm hmn ↦ ?_⟩
  rw [partialSum_sub_partialSum hmn, partialSum_sub_partialSum (Nat.sub_le_sub_right hmn k),
      Finset.mul_sum]
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  have hlen : n - k - (m - k) = n - m := by omega
  rw [hlen]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  have hidx : m + j = k + (m - k + j) := by omega
  rw [hidx, mul_comm |a k|]
  exact hpow (m - k + j)

/-- **Goldblatt Exercise 6.11(8d) — D'Alembert's Ratio Test: Absolute Convergence (pp. 72–73)**:
If `a_n ≠ 0`, `|a_{n+1}| / |a_n|` is bounded, and `seqLimsup (fun n ↦ |a (n + 1)| / |a n|) < 1`,
then `∑ a_n` is absolutely convergent (and hence convergent). -/
theorem ratio_test_abs_converges {a : ℕ → ℝ} (ha : ∀ n : ℕ, a n ≠ 0)
    (hbdd : Bornology.IsBounded (Set.range (fun n ↦ |a (n + 1)| / |a n|)))
    (hsup : seqLimsup (fun n ↦ |a (n + 1)| / |a n|) < 1) :
    SeriesAbsConverges a := by
  obtain ⟨c, hc0, hc1, hstep_a⟩ := ratio_test_step_a ha hbdd hsup
  obtain ⟨k, hk⟩ := ratio_test_step_b hstep_a
  have hstep_c := (ratio_test_step_c hc0.le hk).2
  have hc_abs : |c| < 1 := abs_lt.2 ⟨by linarith, hc1⟩
  rw [SeriesAbsConverges, seriesConverges_iff_forall_unlimited_tail_infClose_zero]
  intro M N hM hMN
  rw [infClose_zero_iff]
  induction M using Germ.inductionOn with | _ u =>
  induction N using Germ.inductionOn with | _ v =>
  let M' : ℕ* := ((fun i ↦ u i - k) : ℕ*)
  let N' : ℕ* := ((fun i ↦ v i - k) : ℕ*)
  have hM'_unl : IsUnlimitedNat M' := fun m ↦ by
    have hgt : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), m + k < u i := Germ.coe_lt.1 (hM (m + k))
    exact Germ.coe_lt.2 (hgt.mono fun i hi ↦ by change m < u i - k; omega)
  have hM'N' : M' ≤ N' :=
    Germ.coe_le.2 ((Germ.coe_le.1 hMN).mono fun i hi ↦ Nat.sub_le_sub_right hi k)
  have hgeom_inf : IsInfinitesimal
      ((|a k| : ℝ*) *
        (starSeq (partialSum (fun j ↦ c ^ j)) N' - starSeq (partialSum (fun j ↦ c ^ j)) M')) :=
    (isLimited_coe |a k|).mul_isInfinitesimal
      (infClose_zero_iff.1 (geometric_series_tail_infClose_zero hc_abs hM'_unl hM'N'))
  refine isInfinitesimal_of_abs_le hgeom_inf ?_
  have hku : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), k < u i := Germ.coe_lt.1 (hM k)
  have huv : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), u i ≤ v i := Germ.coe_le.1 hMN
  refine ofSeq_le_ofSeq.2 ((hku.and huv).mono fun i ⟨hi_k, hi_uv⟩ ↦ ?_)
  change |partialSum (fun d ↦ |a d|) (v i) - partialSum (fun d ↦ |a d|) (u i)| ≤
    |(|a k| * (partialSum (fun j ↦ c ^ j) (v i - k) - partialSum (fun j ↦ c ^ j) (u i - k)))|
  have hnn : 0 ≤ partialSum (fun d ↦ |a d|) (v i) - partialSum (fun d ↦ |a d|) (u i) := by
    rw [partialSum_sub_partialSum hi_uv]
    exact Finset.sum_nonneg fun d _ ↦ abs_nonneg (a d)
  have hle := hstep_c (u i) (v i) hi_k.le hi_uv
  rw [abs_of_nonneg hnn]
  exact hle.trans (le_abs_self _)

/-- **Goldblatt Exercise 6.11(9a) (p. 73)**: If `|starSeq a (N + 1)| > |starSeq a N|` for all
unlimited `N ∈ *ℕ_∞` (with `a_n ≠ 0`), then there exists `k ∈ ℕ` such that `0 < |a k| < |a n|`
for all `n > k`. -/
theorem ratio_test_div_step_a {a : ℕ → ℝ} (ha : ∀ n : ℕ, a n ≠ 0)
    (hgt : ∀ N : ℕ*, IsUnlimitedNat N → |starSeq a N| < |starSeq a (N + 1)|) :
    ∃ k : ℕ, 0 < |a k| ∧ ∀ n : ℕ, k < n → |a k| < |a n| := by
  have hev : ∃ k : ℕ, ∀ m : ℕ, k ≤ m → |a m| < |a (m + 1)| := by
    refine (forall_isUnlimitedNat_liftPred_iff (P := fun m ↦ |a m| < |a (m + 1)|)).1 fun N hN ↦ ?_
    have h1 := hgt N hN
    induction N using Germ.inductionOn with | _ u =>
    exact ofSeq_lt_ofSeq.1 h1
  obtain ⟨k, hk⟩ := hev
  refine ⟨k, abs_pos.2 (ha k), fun n hkn ↦ ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = k + (d + 1) := ⟨n - k - 1, by omega⟩
  induction d with
  | zero =>
      simpa using hk k le_rfl
  | succ m ih =>
      exact ih (by omega) |>.trans (by
        have := hk (k + (m + 1)) (Nat.le_add_right k (m + 1))
        simpa [Nat.add_assoc] using this)

/-- **Goldblatt Exercise 6.11(9b) — D'Alembert's Ratio Test: Divergence (p. 73)**:
If `a_n ≠ 0`, `|a_{n+1}| / |a_n|` is bounded, and `1 < seqLiminf (fun n ↦ |a (n + 1)| / |a n|)`,
then `∑ a_n` diverges. -/
theorem ratio_test_diverges {a : ℕ → ℝ} (ha : ∀ n : ℕ, a n ≠ 0)
    (hbdd : Bornology.IsBounded (Set.range (fun n ↦ |a (n + 1)| / |a n|)))
    (hinf : 1 < seqLiminf (fun n ↦ |a (n + 1)| / |a n|)) :
    ¬ SeriesConverges a := by
  let r : ℕ → ℝ := fun n ↦ |a (n + 1)| / |a n|
  have hgt_unl : ∀ N : ℕ*, IsUnlimitedNat N → |starSeq a N| < |starSeq a (N + 1)| := by
    intro N hN
    have hlim := isBounded_range_iff_forall_unlimited_isLimited.1 hbdd N hN
    have hge : seqLiminf r ≤ shadow (starSeq r N) :=
      (isLeast_clusterSet_seqLiminf hbdd).2 ⟨N, hN, infClose_shadow hlim⟩
    have hgt1 : 1 < shadow (starSeq r N) := hinf.trans_le hge
    have hr_gt1 : (1 : ℝ*) < starSeq r N := by
      rcases (gt_or_infClose_iff_le_shadow hlim (L := 1)).2 hgt1.le with hgt | hcl
      · exact hgt
      · exfalso
        exact hgt1.ne' (shadow_eq_of_infClose hcl)
    rw [← starSeq_abs, ← starSeq_abs]
    induction N using Germ.inductionOn with | _ u =>
    have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 1 < |a (u i + 1)| / |a (u i)| :=
      ofSeq_lt_ofSeq.1 hr_gt1
    refine ofSeq_lt_ofSeq.2 (hev.mono fun i hi ↦ ?_)
    change |a (u i)| < |a (u i + 1)|
    have hpos : 0 < |a (u i)| := abs_pos.2 (ha (u i))
    simpa using (lt_div_iff₀ hpos).1 hi
  obtain ⟨k, hak_pos, hk_lt⟩ := ratio_test_div_step_a ha hgt_unl
  intro hconv
  have h0 : starSeq a omegaNat ≈ₕ 0 :=
    starSeq_infClose_zero_of_seriesConverges hconv isUnlimitedNat_omegaNat
  have hsmall : |starSeq a omegaNat| < (|a k| : ℝ*) := by
    simpa [InfClose] using h0 |a k| hak_pos
  have hbig : (|a k| : ℝ*) ≤ |starSeq a omegaNat| := by
    have hk_om : (k : ℕ*) < omegaNat := isUnlimitedNat_omegaNat k
    have hev : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), k < i := Germ.coe_lt.1 hk_om
    exact ofSeq_le_ofSeq.2 (hev.mono fun i hi ↦ (hk_lt i hi).le)
  exact lt_irrefl _ (hsmall.trans_le hbig)

/-- **Goldblatt Exercise 6.11(10a) (p. 73)**: For every `x ∈ ℝ`, the exponential series
`∑ x^n / n!` is absolutely convergent (proved via D'Alembert's ratio test for `x ≠ 0`). -/
theorem exp_series_abs_converges (x : ℝ) :
    SeriesAbsConverges (fun n ↦ x ^ n / (n.factorial : ℝ)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [SeriesAbsConverges]
    refine ⟨1, ?_⟩
    have hconst : ∀ n : ℕ, 1 ≤ n → partialSum (fun k ↦ |(0 : ℝ) ^ k / (k.factorial : ℝ)|) n = 1 := by
      intro n hn
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
      induction m with
      | zero =>
          simp [partialSum]
      | succ d ih =>
          rw [partialSum_succ, ih (by omega)]
          simp [zero_pow (Nat.succ_ne_zero d)]
    rw [SeriesConvergesTo, tendsto_nhds_iff_forall_unlimited_infClose]
    intro N hN
    have h1 : (1 : ℕ*) ≤ N := (hN 1).le
    have heq : starSeq (partialSum (fun k ↦ |(0 : ℝ) ^ k / (k.factorial : ℝ)|)) N = (1 : ℝ*) := by
      induction N using Germ.inductionOn with | _ u =>
      exact Germ.coe_eq.2 ((Germ.coe_le.1 h1).mono fun i hi ↦ hconst (u i) hi)
    rw [heq, Hyperreal.coe_one]
  · let a : ℕ → ℝ := fun n ↦ x ^ n / (n.factorial : ℝ)
    have ha_ne : ∀ n : ℕ, a n ≠ 0 := fun n ↦
      div_ne_zero (pow_ne_zero n hx) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n))
    have hratio_eq : (fun n ↦ |a (n + 1)| / |a n|) = fun n : ℕ ↦ |x| * (1 / ((n : ℝ) + 1)) := by
      ext n
      have hfn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have hxpow : |x| ^ n ≠ 0 := pow_ne_zero n (abs_ne_zero.2 hx)
      have hf_pos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos n)
      simp only [a, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        abs_div, abs_mul, abs_pow, abs_of_pos hf_pos,
        abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      field_simp [hfn, hn1, hxpow]
    have hratio_lim : Tendsto (fun n ↦ |a (n + 1)| / |a n|) atTop (𝓝 0) := by
      rw [hratio_eq, ← mul_zero |x|]
      exact tendsto_const_mul_nonstandard |x| tendsto_one_div_add_one_zero_nonstandard
    have hbdd := isBounded_range_of_tendsto_nonstandard hratio_lim
    have hsup0 : seqLimsup (fun n ↦ |a (n + 1)| / |a n|) = 0 :=
      ((tendsto_iff_seqLimsup_eq_seqLiminf_of_isBounded hbdd).1 hratio_lim).1
    exact ratio_test_abs_converges ha_ne hbdd (by linarith)

/-- **Goldblatt Exercise 6.11(10b) (p. 73)**: For every real number `x ∈ ℝ` and every unlimited
hypernatural `N ∈ *ℕ_∞`, `starSeq (fun n ↦ x ^ n / n!) N` is infinitesimal. -/
theorem isInfinitesimal_pow_div_factorial (x : ℝ) {N : ℕ*} (hN : IsUnlimitedNat N) :
    IsInfinitesimal (starSeq (fun n ↦ x ^ n / (n.factorial : ℝ)) N) := by
  have hconv := seriesConverges_of_seriesAbsConverges (exp_series_abs_converges x)
  exact infClose_zero_iff.1 (starSeq_infClose_zero_of_seriesConverges hconv hN)

/-- Finite alternating tail bound for Leibniz's test: if `a` is antitone and nonnegative, then
`|partialSum (fun i ↦ (-1)^i * a i) n - partialSum (fun i ↦ (-1)^i * a i) m| ≤ a m` for `m ≤ n`. -/
theorem alternating_tail_abs_le {a : ℕ → ℝ} (hanti : Antitone a) (hnn : ∀ i : ℕ, 0 ≤ a i)
    {m n : ℕ} (hmn : m ≤ n) :
    |partialSum (fun i ↦ (-1 : ℝ) ^ i * a i) n -
      partialSum (fun i ↦ (-1 : ℝ) ^ i * a i) m| ≤ a m := by
  let S : ℕ → ℕ → ℝ := fun p k ↦ ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * a (p + j)
  have hS_bounds : ∀ k p : ℕ, 0 ≤ S p k ∧ S p k ≤ a p := by
    intro k
    induction k with
    | zero =>
        intro p
        simp [S, hnn p]
    | succ d ih =>
        intro p
        have hrec : S p (d + 1) = a p - S (p + 1) d := by
          unfold S
          rw [Finset.sum_range_succ']
          have hsum :
              ∑ x ∈ Finset.range d, (-1 : ℝ) ^ (x + 1) * a (p + (x + 1)) =
                - ∑ x ∈ Finset.range d, (-1 : ℝ) ^ x * a (p + 1 + x) := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun x _ ↦ ?_
            rw [pow_succ, show p + (x + 1) = p + 1 + x by omega]
            ring
          rw [hsum, pow_zero, one_mul, Nat.add_zero]
          exact neg_add_eq_sub _ _
        obtain ⟨hlo, hhi⟩ := ih (p + 1)
        have hap : a (p + 1) ≤ a p := hanti (Nat.le_succ p)
        rw [hrec]
        exact ⟨by linarith, by linarith⟩
  rw [partialSum_sub_partialSum hmn, Finset.sum_Ico_eq_sum_range]
  have hfactor :
      ∑ k ∈ Finset.range (n - m), (-1 : ℝ) ^ (m + k) * a (m + k) =
        (-1 : ℝ) ^ m * S m (n - m) := by
    unfold S
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [pow_add]
    ring
  rw [hfactor, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (hS_bounds (n - m) m).1]
  exact (hS_bounds (n - m) m).2

/-- **Goldblatt Exercise 6.11(11) — Leibniz's Alternating Series Test (p. 73)**:
If `a : ℕ → ℝ` is nonincreasing (`Antitone a`) and `Tendsto a atTop (𝓝 0)`, then the alternating
series `∑ (-1)^i * a_i` converges in `ℝ` (proved via hyperfinite tails and `alternating_tail_abs_le`). -/
theorem leibniz_alternating_series_converges {a : ℕ → ℝ}
    (hanti : Antitone a) (ha0 : Tendsto a atTop (𝓝 0)) :
    SeriesConverges (fun i ↦ (-1 : ℝ) ^ i * a i) := by
  have hnn : ∀ m : ℕ, 0 ≤ a m := by
    intro m
    have h0 := tendsto_nhds_iff_forall_unlimited_infClose.1 ha0 omegaNat isUnlimitedNat_omegaNat
    have hle : starSeq a omegaNat ≤ (a m : ℝ*) := by
      simpa using starSeq_anti hanti (isUnlimitedNat_omegaNat m).le
    exact coe_le_of_infClose_le h0.symm hle (InfClose.refl _)
  rw [seriesConverges_iff_forall_unlimited_tail_infClose_zero]
  intro M N hM hMN
  have haM_inf : IsInfinitesimal (starSeq a M) := by
    simpa [InfClose] using tendsto_nhds_iff_forall_unlimited_infClose.1 ha0 M hM
  rw [infClose_zero_iff]
  refine isInfinitesimal_of_abs_le haM_inf ?_
  induction M using Germ.inductionOn with | _ u =>
  induction N using Germ.inductionOn with | _ v =>
  have huv : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), u i ≤ v i := Germ.coe_le.1 hMN
  refine ofSeq_le_ofSeq.2 (huv.mono fun i hi ↦ ?_)
  exact (alternating_tail_abs_le hanti hnn hi).trans (le_abs_self _)

end Goldblatt.Ch06
end
