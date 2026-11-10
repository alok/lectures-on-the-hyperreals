import LecturesOnTheHyperreals.Ch03_UltrapowerConstruction
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Chapter 4: The Transfer Principle

Formalization of Robert Goldblatt, *Lectures on the Hyperreals*, Chapter 4 (pp. 35–48):

* **§4.2** Relational structures `S = (S, Rel_S, Fun_S)` with partial finitary functions
  (`PartialFun`, `RelStructure`, `realStructure`, `starRealStructure`) and Exercise 4.2.1 showing
  no infinite standard subset (`ℕ`, `ℤ`, `ℚ`, `ℝ`, etc.) belongs to `Rel_{*ℜ}`.
* **§4.3** The first-order bounded-quantifier language `ℒ_S` (`LTerm`, `LFormula`), partial term
  evaluation (`evalTerm`), closed/defined terms (`freeVarsTerm`, `IsClosedTerm`, `IsDefinedTerm`),
  defined formulas (`IsDefinedFormula`), truth evaluation (`Holds`), invariance of sentences under
  variable assignments (`holds_congr`, `holds_of_isSentence`), and Goldblatt's partial-function
  example `(∀ x ∈ ℝ) [tan(-x) = -tan(x)]` where `tan(π/2)` is undefined (pp. 39, 41).
* **§4.4** `*-Transforms` (`starPartialFunN`, `starTerm`, `starFormula`), evaluation of enlarged
  terms (`evalTerm_starTerm_of_total`, `isDefinedTerm_starTerm_iff`), and Exercise 4.4.1
  compatibility with `=`, `<`, `≤`, and `∈`.
* **§4.5–4.6** Statement-value sets (`stmtVal`), **Łoś's Theorem** (`los_theorem`,
  `los_theorem_total`, p. 47), **The Transfer Principle** (`transfer_principle`, pp. 44, 47),
  **Universal Transfer** (`universal_transfer`, p. 45), **Existential Transfer**
  (`existential_transfer`, pp. 45–46), boundedness transfer for hypersequences
  (`starSeq_bounded_iff_bounded`, pp. 45–46), transcendental function identities on `ℝ*`
  (`starFun_sin_pi_sub`, `starFun_cosh_add_sinh`, `starFun_log_mul`, p. 45), and Exercise 4.5.1.
* **§4.1** Concrete transfer examples (pp. 35–37 & Exercise 4.1.1):
  (1) Eudoxus–Archimedes in `ℝ*` (`eudoxus_archimedes_hyperreal`, and failure over standard `ℕ`),
  (2) Density of `ℚ*` in `ℝ*` (`dense_hyperrat_in_hyperreal`),
  (3) Finite subsets of `ℝ` via transfer (`mem_starSet_finite_via_transfer`),
  (4) Finitary Boolean operations via transfer (`mem_starSet_union_via_transfer`),
  (5) Discreteness of `ℕ*` (`hypernat_discrete_between_nat`, `hypernat_one_le_of_ne_zero`,
      `hypernat_gt_all_nat_of_nonstandard`),
  (6) Unbounded sets of reals (`exists_unlimited_mem_starSet_iff_unbounded`).
* **§4.7** Parametric ultrapower enlargement and **Parametric Łoś's Theorem**
  (`parametric_los_theorem`, `parametric_transfer_principle`, `complex_transfer_principle`, p. 47)
  for `Germ (U : Filter I) S` over an arbitrary carrier type `S` and arbitrary ultrafilter `U`.
-/

noncomputable section

namespace Goldblatt.Ch04

open Filter Hyperreal
open scoped Topology Classical

/-! ## §4.2 Relational Structures and Partial Functions -/

/-- Goldblatt §4.2 (p. 38): An `m`-ary (possibly partial) function on a carrier `S`, equipped with
an explicit domain `dom ⊆ S^m` and an underlying mapping `toFun : (Fin m → S) → S`. -/
structure PartialFun (S : Type*) (m : ℕ) where
  /-- The domain of definition of the `m`-ary partial function. -/
  dom : Set (Fin m → S)
  /-- Value of the `m`-ary function on tuples in `S^m`. -/
  toFun : (Fin m → S) → S

/-- Predicate asserting that an `m`-ary `PartialFun` is everywhere defined (`dom = Set.univ`). -/
def PartialFun.IsTotal {S : Type*} {m : ℕ} (f : PartialFun S m) : Prop :=
  f.dom = Set.univ

/-- Construct a total `m`-ary function in `PartialFun S m`. -/
def PartialFun.total {S : Type*} {m : ℕ} (f : (Fin m → S) → S) : PartialFun S m :=
  ⟨Set.univ, f⟩

/-- Construct a unary partial function on `S` with explicit domain `d ⊆ S`. -/
def PartialFun.unary {S : Type*} (d : Set S) (f : S → S) : PartialFun S 1 :=
  ⟨{v | v 0 ∈ d}, fun v ↦ f (v 0)⟩

/-- Construct a total unary function on `S`. -/
def PartialFun.totalUnary {S : Type*} (f : S → S) : PartialFun S 1 :=
  PartialFun.total (fun v ↦ f (v 0))

/-- Construct a total binary function on `S`. -/
def PartialFun.totalBinary {S : Type*} (f : S → S → S) : PartialFun S 2 :=
  PartialFun.total (fun v ↦ f (v 0) (v 1))

/-- `PartialFun.total f` is a total function. -/
@[simp]
theorem PartialFun.isTotal_total {S : Type*} {m : ℕ} (f : (Fin m → S) → S) :
    (PartialFun.total f).IsTotal := rfl

/-- `PartialFun.totalUnary f` is a total unary function. -/
@[simp]
theorem PartialFun.isTotal_totalUnary {S : Type*} (f : S → S) :
    (PartialFun.totalUnary f).IsTotal := rfl

/-- `PartialFun.totalBinary f` is a total binary function. -/
@[simp]
theorem PartialFun.isTotal_totalBinary {S : Type*} (f : S → S → S) :
    (PartialFun.totalBinary f).IsTotal := rfl

/-- Goldblatt §4.2 (p. 38): A relational structure `S = (S, Rel_S, Fun_S)` consisting of collections
of finitary relations and (possibly partial) finitary functions on `S` indexed by arity. -/
structure RelStructure (S : Type*) where
  /-- Collection of `k`-ary relations belonging to the structure. -/
  rels : ∀ k : ℕ, Set (Set (Fin k → S))
  /-- Collection of `m`-ary partial functions belonging to the structure. -/
  funs : ∀ m : ℕ, Set (PartialFun S m)

/-- Goldblatt §4.2 (p. 38): The full relational structure on `S`, containing all finitary relations
and all finitary partial functions on `S`. -/
def RelStructure.full (S : Type*) : RelStructure S where
  rels _ := Set.univ
  funs _ := Set.univ

/-- Goldblatt §4.2 (p. 38): The full relational structure `ℜ` based on `ℝ`. -/
def realStructure : RelStructure ℝ := RelStructure.full ℝ

/-! ## §4.3 The Language `ℒ_S`: Terms, Definedness, Formulae, and Truth -/

/-- Goldblatt §4.3 (p. 39): Terms of the language `ℒ_S` of a relational structure on `S`, built from
countably many variables (`ℕ`), constants from `S`, and applications of `m`-ary partial functions. -/
inductive LTerm (S : Type*) where
  /-- Variable symbol `x_n`. -/
  | var (x : ℕ) : LTerm S
  /-- Constant symbol naming `s : S`. -/
  | const (s : S) : LTerm S
  /-- Application `f(τ_1, …, τ_m)` of an `m`-ary partial function. -/
  | app {m : ℕ} (f : PartialFun S m) (args : Fin m → LTerm S) : LTerm S

/-- Helper evaluating an `m`-ary partial function `f` on `Option S` argument values. -/
def evalTermAppAux {S : Type*} {m : ℕ} (f : PartialFun S m) (vals : Fin m → Option S) : Option S :=
  if h : ∀ i, (vals i).isSome then
    if (fun i ↦ (vals i).get (h i)) ∈ f.dom then
      some (f.toFun (fun i ↦ (vals i).get (h i)))
    else
      none
  else
    none

/-- Goldblatt §4.3 (p. 39): Partial evaluation of an `ℒ_S`-term under a variable assignment
`env : ℕ → S`, returning `some val` when the term is defined and `none` when undefined:
* `var x` names `env x`;
* `const s` names `s`;
* `app f args` names `f.toFun v` if each `args i` names `v i` and `v ∈ f.dom`, and is `none`
  otherwise. -/
def evalTerm {S : Type*} (env : ℕ → S) : LTerm S → Option S
  | .var x => some (env x)
  | .const s => some s
  | .app f args =>
      let vals := fun i ↦ evalTerm env (args i)
      evalTermAppAux f vals

/-- Evaluating a variable symbol `.var x` returns `some (env x)`. -/
@[simp]
theorem evalTerm_var {S : Type*} (env : ℕ → S) (x : ℕ) :
    evalTerm env (.var x) = some (env x) := rfl

/-- Evaluating a constant symbol `.const s` returns `some s`. -/
@[simp]
theorem evalTerm_const {S : Type*} (env : ℕ → S) (s : S) :
    evalTerm env (.const s) = some s := rfl

/-- Evaluating a function application `.app f args` unfolds via `evalTermAppAux`. -/
@[simp]
theorem evalTerm_app {S : Type*} (env : ℕ → S) {m : ℕ} (f : PartialFun S m)
    (args : Fin m → LTerm S) :
    evalTerm env (.app f args) = evalTermAppAux f (fun i ↦ evalTerm env (args i)) := rfl

/-- Characterization of when `evalTermAppAux f vals` succeeds with `some s`. -/
theorem evalTermAppAux_eq_some {S : Type*} {m : ℕ} {f : PartialFun S m}
    {vals : Fin m → Option S} {s : S} :
    evalTermAppAux f vals = some s ↔
      ∃ v : Fin m → S, (∀ i, vals i = some (v i)) ∧ v ∈ f.dom ∧ f.toFun v = s := by
  unfold evalTermAppAux
  constructor
  · intro h
    split_ifs at h with hall hdom
    refine ⟨fun i ↦ (vals i).get (hall i), fun i ↦ ?_, hdom, Option.some.inj h⟩
    exact (Option.some_get (hall i)).symm
  · rintro ⟨v, hv, hdom, rfl⟩
    have hall : ∀ i, (vals i).isSome := fun i ↦ by rw [hv i]; rfl
    have hget : ∀ (h : ∀ i, (vals i).isSome), (fun i ↦ (vals i).get (h i)) = v := fun _ ↦
      funext fun i ↦ by simp [hv i]
    split_ifs with h₁
    · rw [hget hall]
    · rw [hget hall] at h₁
      exact absurd hdom h₁

/-- Characterization of when `evalTermAppAux f vals` is undefined (`none`). -/
theorem evalTermAppAux_eq_none {S : Type*} {m : ℕ} {f : PartialFun S m}
    {vals : Fin m → Option S} :
    evalTermAppAux f vals = none ↔
      (∃ i, vals i = none) ∨
        ∃ v : Fin m → S, (∀ i, vals i = some (v i)) ∧ v ∉ f.dom := by
  unfold evalTermAppAux
  constructor
  · intro h
    split_ifs at h with hall hdom
    · exact Or.inr ⟨fun i ↦ (vals i).get (hall i),
        fun i ↦ (Option.some_get (hall i)).symm, hdom⟩
    · rcases Classical.not_forall.1 hall with ⟨i, hi⟩
      cases hvi : vals i with
      | none => exact Or.inl ⟨i, hvi⟩
      | some a =>
          rw [hvi] at hi
          exact absurd rfl hi
  · rintro (⟨i, hi⟩ | ⟨v, hv, hndom⟩)
    · split_ifs with h₁
      · exfalso
        have := h₁ i
        rw [hi] at this
        contradiction
      · rfl
      · rfl
    · have hall : ∀ i, (vals i).isSome := fun i ↦ by rw [hv i]; rfl
      have hget : ∀ (h : ∀ i, (vals i).isSome), (fun i ↦ (vals i).get (h i)) = v := fun _ ↦
        funext fun i ↦ by simp [hv i]
      split_ifs with h₁
      · rw [hget hall] at h₁
        exact absurd h₁ hndom
      · rfl

/-- Goldblatt §4.3 (p. 39): `f(τ_1, …, τ_m)` evaluates to `some s` iff each `τ_i` evaluates to
some `v i`, the tuple `v` lies in `f.dom`, and `f.toFun v = s`. -/
theorem evalTerm_app_eq_some {S : Type*} {env : ℕ → S} {m : ℕ}
    {f : PartialFun S m} {args : Fin m → LTerm S} {s : S} :
    evalTerm env (.app f args) = some s ↔
      ∃ v : Fin m → S, (∀ i, evalTerm env (args i) = some (v i)) ∧ v ∈ f.dom ∧ f.toFun v = s :=
  evalTermAppAux_eq_some

/-- Goldblatt §4.3 (p. 39): `f(τ_1, …, τ_m)` is undefined (`none`) iff some argument `τ_i` is
undefined, or all arguments are defined with values `v` outside `f.dom`. -/
theorem evalTerm_app_eq_none {S : Type*} {env : ℕ → S} {m : ℕ}
    {f : PartialFun S m} {args : Fin m → LTerm S} :
    evalTerm env (.app f args) = none ↔
      (∃ i, evalTerm env (args i) = none) ∨
        ∃ v : Fin m → S, (∀ i, evalTerm env (args i) = some (v i)) ∧ v ∉ f.dom :=
  evalTermAppAux_eq_none

/-- Variables occurring in an `ℒ_S`-term. -/
def freeVarsTerm {S : Type*} : LTerm S → Finset ℕ
  | .var x => {x}
  | .const _ => ∅
  | .app _ args =>
      let fv := fun i ↦ freeVarsTerm (args i)
      Finset.univ.biUnion fv

/-- Goldblatt §4.3 (p. 39): A closed term is one that contains no variables. -/
def IsClosedTerm {S : Type*} (t : LTerm S) : Prop :=
  freeVarsTerm t = ∅

/-- Goldblatt §4.3 (p. 39): A term is defined under `env` if its evaluation is not `none`. -/
def IsDefinedTerm {S : Type*} (env : ℕ → S) (t : LTerm S) : Prop :=
  evalTerm env t ≠ none

/-- Term evaluation depends only on the values assigned to variables occurring in the term. -/
theorem evalTerm_congr {S : Type*} {env₁ env₂ : ℕ → S} {t : LTerm S}
    (h : ∀ x ∈ freeVarsTerm t, env₁ x = env₂ x) :
    evalTerm env₁ t = evalTerm env₂ t := by
  induction t with
  | var x =>
      simp [h x (Finset.mem_singleton_self x)]
  | const s =>
      rfl
  | app f args ih =>
      rw [evalTerm_app, evalTerm_app]
      congr 1
      funext i
      exact ih i fun x hx ↦ h x (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, hx⟩)

/-- Goldblatt §4.3 (p. 39): Closed terms evaluate identically under any two variable assignments. -/
theorem evalTerm_of_isClosedTerm {S : Type*} {t : LTerm S} (ht : IsClosedTerm t)
    (env₁ env₂ : ℕ → S) :
    evalTerm env₁ t = evalTerm env₂ t :=
  evalTerm_congr fun x hx ↦ by
    rw [ht] at hx
    exact absurd hx (Finset.notMem_empty x)

/-- Predicate asserting that every function symbol occurring in an `ℒ_S`-term is total. -/
def IsTotalTerm {S : Type*} : LTerm S → Prop
  | .var _ => True
  | .const _ => True
  | .app f args =>
      let tot := fun i ↦ IsTotalTerm (args i)
      f.IsTotal ∧ ∀ i, tot i

/-- Direct total evaluation of an `ℒ_S`-term using `toFun` at each application node. When
`IsTotalTerm t` holds, `evalTerm env t = some (evalTermTotal env t)`. -/
def evalTermTotal {S : Type*} (env : ℕ → S) : LTerm S → S
  | .var x => env x
  | .const s => s
  | .app f args =>
      let vals := fun i ↦ evalTermTotal env (args i)
      f.toFun vals

/-- Every total-function term evaluates to `some (evalTermTotal env t)` under every environment. -/
theorem evalTerm_eq_some_evalTermTotal {S : Type*} {env : ℕ → S} {t : LTerm S}
    (ht : IsTotalTerm t) :
    evalTerm env t = some (evalTermTotal env t) := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | app f args ih =>
      rcases ht with ⟨hdom, hargs⟩
      rw [evalTerm_app_eq_some]
      refine ⟨fun i ↦ evalTermTotal env (args i), fun i ↦ ih i (hargs i), ?_, rfl⟩
      rw [hdom]
      exact Set.mem_univ _

/-- Total-function terms are everywhere defined. -/
theorem isDefinedTerm_of_isTotalTerm {S : Type*} {t : LTerm S} (ht : IsTotalTerm t)
    (env : ℕ → S) : IsDefinedTerm env t := by
  rw [IsDefinedTerm, evalTerm_eq_some_evalTermTotal ht]
  exact Option.some_ne_none _

/-- Goldblatt §4.3 (pp. 40–41): First-order bounded-quantifier formulae of the language `ℒ_S`. -/
inductive LFormula (S : Type*) where
  /-- Atomic formula `P(τ_1, …, τ_k)` for a `k`-ary relation `P ⊆ S^k`. -/
  | rel {k : ℕ} (P : Set (Fin k → S)) (args : Fin k → LTerm S) : LFormula S
  /-- Conjunction `φ ∧ ψ`. -/
  | conj (φ ψ : LFormula S) : LFormula S
  /-- Disjunction `φ ∨ ψ`. -/
  | disj (φ ψ : LFormula S) : LFormula S
  /-- Negation `¬ φ`. -/
  | neg (φ : LFormula S) : LFormula S
  /-- Implication `φ → ψ`. -/
  | imp (φ ψ : LFormula S) : LFormula S
  /-- Biconditional `φ ↔ ψ`. -/
  | iff (φ ψ : LFormula S) : LFormula S
  /-- Bounded universal quantification `(∀ x ∈ P) φ`. -/
  | forallIn (P : Set S) (x : ℕ) (φ : LFormula S) : LFormula S
  /-- Bounded existential quantification `(∃ x ∈ P) φ`. -/
  | existsIn (P : Set S) (x : ℕ) (φ : LFormula S) : LFormula S

/-- Goldblatt §4.3 (p. 40): Atomic equality formula `τ_1 = τ_2`. -/
def LFormula.eq {S : Type*} (t₁ t₂ : LTerm S) : LFormula S :=
  .rel {v : Fin 2 → S | v 0 = v 1} ![t₁, t₂]

/-- Goldblatt §4.3 (p. 40): Atomic strict inequality formula `τ_1 < τ_2`. -/
def LFormula.lt {S : Type*} [LT S] (t₁ t₂ : LTerm S) : LFormula S :=
  .rel {v : Fin 2 → S | v 0 < v 1} ![t₁, t₂]

/-- Goldblatt §4.3 (p. 40): Atomic weak inequality formula `τ_1 ≤ τ_2`. -/
def LFormula.le {S : Type*} [LE S] (t₁ t₂ : LTerm S) : LFormula S :=
  .rel {v : Fin 2 → S | v 0 ≤ v 1} ![t₁, t₂]

/-- Goldblatt §4.3 (p. 40): Unary membership atomic formula `τ ∈ P`. -/
def LFormula.mem {S : Type*} (t : LTerm S) (P : Set S) : LFormula S :=
  .rel {v : Fin 1 → S | v 0 ∈ P} ![t]

/-- Goldblatt §4.3 (p. 41): Set of free variables occurring in an `ℒ_S`-formula. -/
def freeVarsFormula {S : Type*} : LFormula S → Finset ℕ
  | .rel _ args =>
      let fv := fun i ↦ freeVarsTerm (args i)
      Finset.univ.biUnion fv
  | .conj φ ψ | .disj φ ψ | .imp φ ψ | .iff φ ψ =>
      freeVarsFormula φ ∪ freeVarsFormula ψ
  | .neg φ => freeVarsFormula φ
  | .forallIn _ x φ | .existsIn _ x φ =>
      (freeVarsFormula φ).erase x

/-- Goldblatt §4.3 (p. 41): A sentence is an `ℒ_S`-formula in which all variables are bound
(no free variables). -/
def IsSentence {S : Type*} (φ : LFormula S) : Prop :=
  freeVarsFormula φ = ∅

/-- Predicate asserting that every term occurring in an `ℒ_S`-formula uses only total functions. -/
def IsTotalFormula {S : Type*} : LFormula S → Prop
  | .rel _ args => ∀ i, IsTotalTerm (args i)
  | .conj φ ψ | .disj φ ψ | .imp φ ψ | .iff φ ψ => IsTotalFormula φ ∧ IsTotalFormula ψ
  | .neg φ => IsTotalFormula φ
  | .forallIn _ _ φ | .existsIn _ _ φ => IsTotalFormula φ

/-- Helper checking that every subterm of `t` that is closed relative to the set `bound` of
enclosing bound variables is defined under `env` (Goldblatt §4.3, p. 40). -/
def allClosedSubtermsDefined {S : Type*} (env : ℕ → S) (bound : Finset ℕ) : LTerm S → Prop
  | .var _ => True
  | .const _ => True
  | .app f args =>
      let sub := fun i ↦ allClosedSubtermsDefined env bound (args i)
      (Disjoint (freeVarsTerm (.app f args)) bound → IsDefinedTerm env (.app f args)) ∧
        ∀ i, sub i

/-- Helper checking definedness of a formula relative to enclosing bound variables `bound`. -/
def IsDefinedFormulaWithBound {S : Type*} (env : ℕ → S) (bound : Finset ℕ) : LFormula S → Prop
  | .rel _ args => ∀ i, allClosedSubtermsDefined env bound (args i)
  | .conj φ ψ | .disj φ ψ | .imp φ ψ | .iff φ ψ =>
      IsDefinedFormulaWithBound env bound φ ∧ IsDefinedFormulaWithBound env bound ψ
  | .neg φ => IsDefinedFormulaWithBound env bound φ
  | .forallIn _ x φ | .existsIn _ x φ =>
      IsDefinedFormulaWithBound env (insert x bound) φ

/-- Goldblatt §4.3 (p. 40): A formula (with free variables interpreted by `env`) is *defined* iff
all of its closed subterms (those containing no bound variables) are defined. -/
def IsDefinedFormula {S : Type*} (env : ℕ → S) (φ : LFormula S) : Prop :=
  IsDefinedFormulaWithBound env ∅ φ

/-- When `bound = ∅`, `allClosedSubtermsDefined env ∅ t` is equivalent to `IsDefinedTerm env t`. -/
theorem allClosedSubtermsDefined_empty_iff {S : Type*} (env : ℕ → S) (t : LTerm S) :
    allClosedSubtermsDefined env ∅ t ↔ IsDefinedTerm env t := by
  induction t with
  | var _ =>
      simp [allClosedSubtermsDefined, IsDefinedTerm]
  | const _ =>
      simp [allClosedSubtermsDefined, IsDefinedTerm]
  | app f args ih =>
      simp only [allClosedSubtermsDefined, Finset.disjoint_empty_right, true_implies]
      constructor
      · exact fun h ↦ h.1
      · intro hdef
        refine ⟨hdef, fun i ↦ (ih i).2 ?_⟩
        intro hnone
        apply hdef
        exact evalTerm_app_eq_none.2 (Or.inl ⟨i, hnone⟩)

/-- Every subterm of a total term `t` is defined regardless of bound variables. -/
theorem allClosedSubtermsDefined_of_isTotalTerm {S : Type*} {t : LTerm S} (ht : IsTotalTerm t)
    (env : ℕ → S) (bound : Finset ℕ) :
    allClosedSubtermsDefined env bound t := by
  induction t with
  | var _ => trivial
  | const _ => trivial
  | app f args ih =>
      refine ⟨fun _ ↦ isDefinedTerm_of_isTotalTerm ht env, fun i ↦ ih i (ht.2 i)⟩

/-- Every total formula satisfies `IsDefinedFormulaWithBound` for any `bound`. -/
theorem isDefinedFormulaWithBound_of_isTotalFormula {S : Type*} {φ : LFormula S}
    (hφ : IsTotalFormula φ) (env : ℕ → S) (bound : Finset ℕ) :
    IsDefinedFormulaWithBound env bound φ := by
  induction φ generalizing bound with
  | rel _ _ => exact fun i ↦ allClosedSubtermsDefined_of_isTotalTerm (hφ i) env bound
  | conj _ _ ih₁ ih₂ | disj _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ | iff _ _ ih₁ ih₂ =>
      exact ⟨ih₁ hφ.1 bound, ih₂ hφ.2 bound⟩
  | neg _ ih => exact ih hφ bound
  | forallIn _ x _ ih | existsIn _ x _ ih =>
      exact ih hφ (insert x bound)

/-- Every total-term formula is defined under every variable assignment. -/
theorem isDefinedFormula_of_isTotalFormula {S : Type*} {φ : LFormula S}
    (hφ : IsTotalFormula φ) (env : ℕ → S) :
    IsDefinedFormula env φ :=
  isDefinedFormulaWithBound_of_isTotalFormula hφ env ∅

/-- Goldblatt §4.3 (pp. 41–42): Truth evaluation `Holds env φ` of an `ℒ_S`-formula under `env`:
* `P(τ_1, …, τ_k)` holds iff every `τ_i` evaluates to some `v i` and `v ∈ P`;
* Boolean connectives `∧, ∨, ¬, →, ↔` have their standard truth-table meanings;
* `(∀ x ∈ P) φ` holds iff for all `s ∈ P`, if `φ(s)` is defined then `φ(s)` holds;
* `(∃ x ∈ P) φ` holds iff there is some `s ∈ P` for which `φ(s)` is defined and holds. -/
def Holds {S : Type*} (env : ℕ → S) : LFormula S → Prop
  | .rel P args =>
      ∃ v : Fin _ → S, (∀ i, evalTerm env (args i) = some (v i)) ∧ v ∈ P
  | .conj φ ψ => Holds env φ ∧ Holds env ψ
  | .disj φ ψ => Holds env φ ∨ Holds env ψ
  | .neg φ => ¬ Holds env φ
  | .imp φ ψ => Holds env φ → Holds env ψ
  | .iff φ ψ => (Holds env φ ↔ Holds env ψ)
  | .forallIn P x φ =>
      ∀ s ∈ P, IsDefinedFormula (Function.update env x s) φ →
        Holds (Function.update env x s) φ
  | .existsIn P x φ =>
      ∃ s ∈ P, IsDefinedFormula (Function.update env x s) φ ∧
        Holds (Function.update env x s) φ

/-- Unfolding `Holds` on an atomic relational formula `.rel P args`. -/
@[simp]
theorem holds_rel {S : Type*} (env : ℕ → S) {k : ℕ} (P : Set (Fin k → S))
    (args : Fin k → LTerm S) :
    Holds env (.rel P args) ↔
      ∃ v : Fin k → S, (∀ i, evalTerm env (args i) = some (v i)) ∧ v ∈ P := Iff.rfl

/-- Unfolding `Holds` on a conjunction `.conj φ ψ`. -/
@[simp]
theorem holds_conj {S : Type*} (env : ℕ → S) (φ ψ : LFormula S) :
    Holds env (.conj φ ψ) ↔ Holds env φ ∧ Holds env ψ := Iff.rfl

/-- Unfolding `Holds` on a disjunction `.disj φ ψ`. -/
@[simp]
theorem holds_disj {S : Type*} (env : ℕ → S) (φ ψ : LFormula S) :
    Holds env (.disj φ ψ) ↔ Holds env φ ∨ Holds env ψ := Iff.rfl

/-- Unfolding `Holds` on a negation `.neg φ`. -/
@[simp]
theorem holds_neg {S : Type*} (env : ℕ → S) (φ : LFormula S) :
    Holds env (.neg φ) ↔ ¬ Holds env φ := Iff.rfl

/-- Unfolding `Holds` on an implication `.imp φ ψ`. -/
@[simp]
theorem holds_imp {S : Type*} (env : ℕ → S) (φ ψ : LFormula S) :
    Holds env (.imp φ ψ) ↔ (Holds env φ → Holds env ψ) := Iff.rfl

/-- Unfolding `Holds` on a bi-implication `.iff φ ψ`. -/
@[simp]
theorem holds_iff {S : Type*} (env : ℕ → S) (φ ψ : LFormula S) :
    Holds env (.iff φ ψ) ↔ (Holds env φ ↔ Holds env ψ) := Iff.rfl

/-- Unfolding `Holds` on a bounded universal quantification `.forallIn P x φ`. -/
@[simp]
theorem holds_forallIn {S : Type*} (env : ℕ → S) (P : Set S) (x : ℕ) (φ : LFormula S) :
    Holds env (.forallIn P x φ) ↔
      ∀ s ∈ P, IsDefinedFormula (Function.update env x s) φ →
        Holds (Function.update env x s) φ := Iff.rfl

/-- Unfolding `Holds` on a bounded existential quantification `.existsIn P x φ`. -/
@[simp]
theorem holds_existsIn {S : Type*} (env : ℕ → S) (P : Set S) (x : ℕ) (φ : LFormula S) :
    Holds env (.existsIn P x φ) ↔
      ∃ s ∈ P, IsDefinedFormula (Function.update env x s) φ ∧
        Holds (Function.update env x s) φ := Iff.rfl

/-- For total-term atomic formulas, `Holds` reduces directly to tuple membership of
`evalTermTotal`. -/
theorem holds_rel_of_total {S : Type*} (env : ℕ → S) {k : ℕ} (P : Set (Fin k → S))
    {args : Fin k → LTerm S} (hargs : ∀ i, IsTotalTerm (args i)) :
    Holds env (.rel P args) ↔ (fun i ↦ evalTermTotal env (args i)) ∈ P := by
  simp only [holds_rel]
  constructor
  · rintro ⟨v, hv, hvP⟩
    have heq : (fun i ↦ evalTermTotal env (args i)) = v := by
      ext i
      have := (evalTerm_eq_some_evalTermTotal (hargs i)).symm.trans (hv i)
      exact Option.some.inj this
    rwa [heq]
  · intro hP
    exact ⟨fun i ↦ evalTermTotal env (args i),
      fun i ↦ evalTerm_eq_some_evalTermTotal (hargs i), hP⟩

/-- For total-term formulas, `(∀ x ∈ P) φ` reduces to `∀ s ∈ P, Holds (update env x s) φ`. -/
theorem holds_forallIn_of_total {S : Type*} (env : ℕ → S) (P : Set S) (x : ℕ)
    {φ : LFormula S} (hφ : IsTotalFormula φ) :
    Holds env (.forallIn P x φ) ↔ ∀ s ∈ P, Holds (Function.update env x s) φ := by
  simp only [holds_forallIn]
  exact forall₂_congr fun s _ ↦
    ⟨fun h ↦ h (isDefinedFormula_of_isTotalFormula hφ _), fun h _ ↦ h⟩

/-- For total-term formulas, `(∃ x ∈ P) φ` reduces to `∃ s ∈ P, Holds (update env x s) φ`. -/
theorem holds_existsIn_of_total {S : Type*} (env : ℕ → S) (P : Set S) (x : ℕ)
    {φ : LFormula S} (hφ : IsTotalFormula φ) :
    Holds env (.existsIn P x φ) ↔ ∃ s ∈ P, Holds (Function.update env x s) φ := by
  simp only [holds_existsIn]
  exact exists_congr fun s ↦ and_congr_right fun _ ↦
    and_iff_right (isDefinedFormula_of_isTotalFormula hφ _)

/-- Satisfaction of atomic equality `LFormula.eq t₁ t₂` for total terms. -/
@[simp]
theorem holds_eq_of_total {S : Type*} (env : ℕ → S) {t₁ t₂ : LTerm S}
    (ht₁ : IsTotalTerm t₁) (ht₂ : IsTotalTerm t₂) :
    Holds env (LFormula.eq t₁ t₂) ↔ evalTermTotal env t₁ = evalTermTotal env t₂ := by
  have htot : ∀ i : Fin 2, IsTotalTerm (![t₁, t₂] i) := Fin.forall_fin_two.2 ⟨ht₁, ht₂⟩
  simpa [LFormula.eq] using holds_rel_of_total env {v : Fin 2 → S | v 0 = v 1} htot

/-- Satisfaction of strict inequality `LFormula.lt t₁ t₂` for total terms. -/
@[simp]
theorem holds_lt_of_total {S : Type*} [LT S] (env : ℕ → S) {t₁ t₂ : LTerm S}
    (ht₁ : IsTotalTerm t₁) (ht₂ : IsTotalTerm t₂) :
    Holds env (LFormula.lt t₁ t₂) ↔ evalTermTotal env t₁ < evalTermTotal env t₂ := by
  have htot : ∀ i : Fin 2, IsTotalTerm (![t₁, t₂] i) := Fin.forall_fin_two.2 ⟨ht₁, ht₂⟩
  simpa [LFormula.lt] using holds_rel_of_total env {v : Fin 2 → S | v 0 < v 1} htot

/-- Satisfaction of nonstrict inequality `LFormula.le t₁ t₂` for total terms. -/
@[simp]
theorem holds_le_of_total {S : Type*} [LE S] (env : ℕ → S) {t₁ t₂ : LTerm S}
    (ht₁ : IsTotalTerm t₁) (ht₂ : IsTotalTerm t₂) :
    Holds env (LFormula.le t₁ t₂) ↔ evalTermTotal env t₁ ≤ evalTermTotal env t₂ := by
  have htot : ∀ i : Fin 2, IsTotalTerm (![t₁, t₂] i) := Fin.forall_fin_two.2 ⟨ht₁, ht₂⟩
  simpa [LFormula.le] using holds_rel_of_total env {v : Fin 2 → S | v 0 ≤ v 1} htot

/-- Satisfaction of unary membership `LFormula.mem t P` for a total term `t`. -/
@[simp]
theorem holds_mem_of_total {S : Type*} (env : ℕ → S) {t : LTerm S} (P : Set S)
    (ht : IsTotalTerm t) :
    Holds env (LFormula.mem t P) ↔ evalTermTotal env t ∈ P := by
  have htot : ∀ i : Fin 1, IsTotalTerm (![t] i) := fun i ↦ by fin_cases i; exact ht
  simpa [LFormula.mem] using holds_rel_of_total env {v : Fin 1 → S | v 0 ∈ P} htot

/-- Congruence of `allClosedSubtermsDefined` under variable assignments agreeing outside `bound`. -/
theorem allClosedSubtermsDefined_congr {S : Type*} {env₁ env₂ : ℕ → S} {bound : Finset ℕ}
    {t : LTerm S} (h : ∀ x ∈ freeVarsTerm t \ bound, env₁ x = env₂ x) :
    allClosedSubtermsDefined env₁ bound t ↔ allClosedSubtermsDefined env₂ bound t := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | app f args ih =>
      simp only [allClosedSubtermsDefined]
      apply and_congr
      · refine imp_congr_right fun hdisj ↦ ?_
        have heq : evalTerm env₁ (.app f args) = evalTerm env₂ (.app f args) := by
          apply evalTerm_congr
          intro x hx
          apply h x
          exact Finset.mem_sdiff.2 ⟨hx, Finset.disjoint_left.1 hdisj hx⟩
        simp only [IsDefinedTerm, heq]
      · refine forall_congr' fun i ↦ ih i fun x hx ↦ h x ?_
        rcases Finset.mem_sdiff.1 hx with ⟨hxi, hxb⟩
        exact Finset.mem_sdiff.2 ⟨Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, hxi⟩, hxb⟩

/-- Congruence of `IsDefinedFormulaWithBound` under variable assignments agreeing outside `bound`. -/
theorem isDefinedFormulaWithBound_congr {S : Type*} {env₁ env₂ : ℕ → S} {bound : Finset ℕ}
    {φ : LFormula S} (h : ∀ x ∈ freeVarsFormula φ \ bound, env₁ x = env₂ x) :
    IsDefinedFormulaWithBound env₁ bound φ ↔ IsDefinedFormulaWithBound env₂ bound φ := by
  induction φ generalizing bound with
  | rel P args =>
      refine forall_congr' fun i ↦ allClosedSubtermsDefined_congr fun x hx ↦ h x ?_
      rcases Finset.mem_sdiff.1 hx with ⟨hxi, hxb⟩
      exact Finset.mem_sdiff.2 ⟨Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, hxi⟩, hxb⟩
  | conj φ ψ ih₁ ih₂ | disj φ ψ ih₁ ih₂ | imp φ ψ ih₁ ih₂ | iff φ ψ ih₁ ih₂ =>
      exact and_congr
        (ih₁ fun x hx ↦ h x
          (Finset.sdiff_subset_sdiff Finset.subset_union_left (Finset.Subset.refl _) hx))
        (ih₂ fun x hx ↦ h x
          (Finset.sdiff_subset_sdiff Finset.subset_union_right (Finset.Subset.refl _) hx))
  | neg φ ih =>
      exact ih h
  | forallIn P y φ ih | existsIn P y φ ih =>
      refine ih fun x hx ↦ h x ?_
      rcases Finset.mem_sdiff.1 hx with ⟨hxφ, hxins⟩
      rw [Finset.mem_insert, not_or] at hxins
      exact Finset.mem_sdiff.2 ⟨Finset.mem_erase.2 ⟨hxins.1, hxφ⟩, hxins.2⟩

/-- Definedness of a formula depends only on its free variables. -/
theorem isDefinedFormula_congr {S : Type*} {env₁ env₂ : ℕ → S} {φ : LFormula S}
    (h : ∀ x ∈ freeVarsFormula φ, env₁ x = env₂ x) :
    IsDefinedFormula env₁ φ ↔ IsDefinedFormula env₂ φ :=
  isDefinedFormulaWithBound_congr fun x hx ↦ h x (Finset.sdiff_subset hx)

/-- Definedness of a sentence is independent of the variable assignment. -/
theorem isDefinedFormula_of_isSentence {S : Type*} {φ : LFormula S} (hφ : IsSentence φ)
    (env₁ env₂ : ℕ → S) :
    IsDefinedFormula env₁ φ ↔ IsDefinedFormula env₂ φ :=
  isDefinedFormula_congr fun x hx ↦ by
    rw [hφ] at hx
    exact absurd hx (Finset.notMem_empty x)

/-- Goldblatt §4.3 (p. 41): Truth of a formula depends only on the values assigned to its free
variables. -/
theorem holds_congr {S : Type*} {env₁ env₂ : ℕ → S} {φ : LFormula S}
    (h : ∀ x ∈ freeVarsFormula φ, env₁ x = env₂ x) :
    Holds env₁ φ ↔ Holds env₂ φ := by
  induction φ generalizing env₁ env₂ with
  | rel P args =>
      simp only [holds_rel]
      refine exists_congr fun v ↦ and_congr_left fun _ ↦ forall_congr' fun i ↦ ?_
      have heq : evalTerm env₁ (args i) = evalTerm env₂ (args i) :=
        evalTerm_congr fun x hx ↦ h x (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, hx⟩)
      rw [heq]
  | conj φ ψ ih₁ ih₂ =>
      exact and_congr
        (ih₁ fun x hx ↦ h x (Finset.mem_union_left _ hx))
        (ih₂ fun x hx ↦ h x (Finset.mem_union_right _ hx))
  | disj φ ψ ih₁ ih₂ =>
      exact or_congr
        (ih₁ fun x hx ↦ h x (Finset.mem_union_left _ hx))
        (ih₂ fun x hx ↦ h x (Finset.mem_union_right _ hx))
  | neg φ ih =>
      exact not_congr (ih h)
  | imp φ ψ ih₁ ih₂ =>
      exact imp_congr
        (ih₁ fun x hx ↦ h x (Finset.mem_union_left _ hx))
        (ih₂ fun x hx ↦ h x (Finset.mem_union_right _ hx))
  | iff φ ψ ih₁ ih₂ =>
      exact iff_congr
        (ih₁ fun x hx ↦ h x (Finset.mem_union_left _ hx))
        (ih₂ fun x hx ↦ h x (Finset.mem_union_right _ hx))
  | forallIn P y φ ih =>
      simp only [holds_forallIn]
      refine forall₂_congr fun s _ ↦ ?_
      have hupd : ∀ x ∈ freeVarsFormula φ,
          Function.update env₁ y s x = Function.update env₂ y s x := by
        intro x hx
        by_cases hxy : x = y
        · subst hxy; simp
        · simp [hxy, h x (Finset.mem_erase.2 ⟨hxy, hx⟩)]
      exact imp_congr (isDefinedFormula_congr hupd) (ih hupd)
  | existsIn P y φ ih =>
      simp only [holds_existsIn]
      refine exists_congr fun s ↦ and_congr_right fun _ ↦ ?_
      have hupd : ∀ x ∈ freeVarsFormula φ,
          Function.update env₁ y s x = Function.update env₂ y s x := by
        intro x hx
        by_cases hxy : x = y
        · subst hxy; simp
        · simp [hxy, h x (Finset.mem_erase.2 ⟨hxy, hx⟩)]
      exact and_congr (isDefinedFormula_congr hupd) (ih hupd)

/-- Goldblatt §4.3 (p. 41) & §4.6 (p. 47): A sentence has no free variables, so its truth value
is independent of the variable assignment `env`. -/
theorem holds_of_isSentence {S : Type*} {φ : LFormula S} (hφ : IsSentence φ)
    (env₁ env₂ : ℕ → S) :
    Holds env₁ φ ↔ Holds env₂ φ :=
  holds_congr fun x hx ↦ by
    rw [hφ] at hx
    exact absurd hx (Finset.notMem_empty x)

/-! ## §4.4 `*-Transforms` and Exercise 4.2.1 -/

/-- Goldblatt §4.4 (pp. 42–43): Enlargement `*f : PartialFun ℝ* m` of an `m`-ary partial function
`f : PartialFun ℝ m`, with domain `starRel f.dom` and underlying map `starFunN f.toFun`. -/
def starPartialFunN {m : ℕ} (f : PartialFun ℝ m) : PartialFun ℝ* m where
  dom := starRel f.dom
  toFun := starFunN f.toFun

/-- Goldblatt §4.2 (p. 38): The enlarged relational structure `*ℜ = (ℝ*, {*P}, {*f})` associated
with the full real structure `ℜ`. -/
def starRealStructure : RelStructure ℝ* where
  rels k := Set.range (starRel (k := k))
  funs m := Set.range (starPartialFunN (m := m))

/-- Goldblatt Exercise 4.2.1 (p. 38): For any infinite subset `A ⊆ ℝ`, its standard copy inside `ℝ*`
cannot equal `starSet P` for any `P ⊆ ℝ`. -/
theorem infinite_coe_image_ne_starSet {A : Set ℝ} (hA : A.Infinite) (P : Set ℝ) :
    ((↑) : ℝ → ℝ*) '' A ≠ starSet P := by
  intro h
  have hPA : P = A := by
    ext r
    calc
      r ∈ P ↔ (r : ℝ*) ∈ starSet P := coe_mem_starSet.symm
      _ ↔ (r : ℝ*) ∈ ((↑) : ℝ → ℝ*) '' A := by rw [← h]
      _ ↔ r ∈ A := ⟨fun ⟨a, ha, heq⟩ ↦ (Hyperreal.coe_eq_coe.1 heq) ▸ ha, fun hr ↦ ⟨r, hr, rfl⟩⟩
  subst hPA
  obtain ⟨x, hxStar, hxNotStd⟩ := exists_nonstandard_mem_starSet_of_infinite hA
  rw [← h] at hxStar
  exact hxNotStd hxStar

/-- Goldblatt Exercise 4.2.1 (p. 38): No infinite subset `A ⊆ ℝ` (viewed as a unary relation on
standard elements of `ℝ*`) belongs to `Rel_{*ℜ}`. -/
theorem not_mem_starRealStructure_rels_of_infinite {A : Set ℝ} (hA : A.Infinite) :
    {v : Fin 1 → ℝ* | v 0 ∈ ((↑) : ℝ → ℝ*) '' A} ∉ starRealStructure.rels 1 := by
  rintro ⟨Q, hQ⟩
  let P : Set ℝ := {r : ℝ | (fun _ : Fin 1 ↦ r) ∈ Q}
  have hstar : ((↑) : ℝ → ℝ*) '' A = starSet P := by
    ext x
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    have hmem : ((fun _ : Fin 1 ↦ ofSeq r) ∈ {v : Fin 1 → ℝ* | v 0 ∈ ((↑) : ℝ → ℝ*) '' A}) ↔
        (fun _ : Fin 1 ↦ ofSeq r) ∈ starRel Q := by
      rw [hQ]
    simpa [P, starRel_ofSeq, ofSeq_mem_starSet] using hmem
  exact infinite_coe_image_ne_starSet hA P hstar

/-- Goldblatt Exercise 4.2.1 (p. 38): None of the standard sets `ℕ`, `ℤ`, `ℚ`, `ℝ` inside `ℝ*`
belongs to `Rel_{*ℜ}`. -/
theorem nat_int_rat_real_not_mem_starRealStructure :
    {v : Fin 1 → ℝ* | v 0 ∈ ((↑) : ℝ → ℝ*) '' Set.range (Nat.cast : ℕ → ℝ)} ∉
        starRealStructure.rels 1 ∧
      {v : Fin 1 → ℝ* | v 0 ∈ ((↑) : ℝ → ℝ*) '' Set.range (Int.cast : ℤ → ℝ)} ∉
        starRealStructure.rels 1 ∧
      {v : Fin 1 → ℝ* | v 0 ∈ ((↑) : ℝ → ℝ*) '' Set.range (Rat.cast : ℚ → ℝ)} ∉
        starRealStructure.rels 1 ∧
      {v : Fin 1 → ℝ* | v 0 ∈ ((↑) : ℝ → ℝ*) '' (Set.univ : Set ℝ)} ∉
        starRealStructure.rels 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact not_mem_starRealStructure_rels_of_infinite
      (Set.infinite_range_of_injective Nat.cast_injective)
  · exact not_mem_starRealStructure_rels_of_infinite
      (Set.infinite_range_of_injective Int.cast_injective)
  · exact not_mem_starRealStructure_rels_of_infinite
      (Set.infinite_range_of_injective Rat.cast_injective)
  · exact not_mem_starRealStructure_rels_of_infinite Set.infinite_univ

/-- Goldblatt §4.4 (pp. 42–43): The `*-transform` `*τ : LTerm ℝ*` of an `ℒ_ℝ`-term `τ : LTerm ℝ`,
replacing every function `f` by `*f` and embedding real constants `r : ℝ` as `(r : ℝ*)`. -/
def starTerm : LTerm ℝ → LTerm ℝ*
  | .var x => .var x
  | .const r => .const (r : ℝ*)
  | .app f args =>
      let sargs := fun i ↦ starTerm (args i)
      .app (starPartialFunN f) sargs

/-- Goldblatt §4.4 (p. 43): The `*-transform` `*φ : LFormula ℝ*` of an `ℒ_ℝ`-formula `φ`,
replacing every term `τ` by `*τ`, every atomic relation `P` by `starRel P`, and every quantifier
bound `P` by `starSet P`. -/
def starFormula : LFormula ℝ → LFormula ℝ*
  | .rel P args => .rel (starRel P) (fun i ↦ starTerm (args i))
  | .conj φ ψ => .conj (starFormula φ) (starFormula ψ)
  | .disj φ ψ => .disj (starFormula φ) (starFormula ψ)
  | .neg φ => .neg (starFormula φ)
  | .imp φ ψ => .imp (starFormula φ) (starFormula ψ)
  | .iff φ ψ => .iff (starFormula φ) (starFormula ψ)
  | .forallIn P x φ => .forallIn (starSet P) x (starFormula φ)
  | .existsIn P x φ => .existsIn (starSet P) x (starFormula φ)

/-- `*-transform` preserves the set of variables occurring in a term. -/
@[simp]
theorem freeVarsTerm_starTerm (t : LTerm ℝ) :
    freeVarsTerm (starTerm t) = freeVarsTerm t := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | app _ args ih =>
      simp only [starTerm, freeVarsTerm]
      congr 1
      funext i
      exact ih i

/-- `*τ` is closed iff `τ` is closed. -/
@[simp]
theorem isClosedTerm_starTerm_iff (t : LTerm ℝ) :
    IsClosedTerm (starTerm t) ↔ IsClosedTerm t := by
  simp [IsClosedTerm]

/-- `*-transform` preserves the free variables of a formula. -/
@[simp]
theorem freeVarsFormula_starFormula (φ : LFormula ℝ) :
    freeVarsFormula (starFormula φ) = freeVarsFormula φ := by
  induction φ with
  | rel _ args =>
      simp only [starFormula, freeVarsFormula, freeVarsTerm_starTerm]
  | conj _ _ ih₁ ih₂ | disj _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ | iff _ _ ih₁ ih₂ =>
      simp only [starFormula, freeVarsFormula, ih₁, ih₂]
  | neg _ ih =>
      simp only [starFormula, freeVarsFormula, ih]
  | forallIn _ _ _ ih | existsIn _ _ _ ih =>
      simp only [starFormula, freeVarsFormula, ih]

/-- `*φ` is a sentence iff `φ` is a sentence. -/
@[simp]
theorem isSentence_starFormula_iff (φ : LFormula ℝ) :
    IsSentence (starFormula φ) ↔ IsSentence φ := by
  simp [IsSentence]

/-- Enlarging the universal `k`-ary relation `Set.univ` yields `Set.univ`. -/
@[simp]
theorem starRel_univ (k : ℕ) :
    starRel (Set.univ : Set (Fin k → ℝ)) = Set.univ := by
  ext v
  choose r hr using fun i ↦ ofSeq_surjective (v i)
  have hv : v = fun i ↦ ofSeq (r i) := funext fun i ↦ (hr i).symm
  rw [hv, starRel_ofSeq]
  simp

/-- `*f` is a total `m`-ary function iff `f` is total. -/
@[simp]
theorem isTotal_starPartialFunN_iff {m : ℕ} (f : PartialFun ℝ m) :
    (starPartialFunN f).IsTotal ↔ f.IsTotal := by
  constructor
  · intro h
    ext x
    have hmem : (fun i ↦ (x i : ℝ*)) ∈ (starPartialFunN f).dom := by
      rw [h]
      exact Set.mem_univ _
    simpa [starPartialFunN] using hmem
  · intro h
    rw [PartialFun.IsTotal] at h
    simp [PartialFun.IsTotal, starPartialFunN, h]

/-- `*τ` is built solely from total functions iff `τ` is. -/
@[simp]
theorem isTotalTerm_starTerm_iff (t : LTerm ℝ) :
    IsTotalTerm (starTerm t) ↔ IsTotalTerm t := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | app f args ih =>
      simp only [starTerm, IsTotalTerm, isTotal_starPartialFunN_iff, ih]

/-- `*φ` is built solely from total functions iff `φ` is. -/
@[simp]
theorem isTotalFormula_starFormula_iff (φ : LFormula ℝ) :
    IsTotalFormula (starFormula φ) ↔ IsTotalFormula φ := by
  induction φ with
  | rel _ _ => simp [starFormula, IsTotalFormula]
  | conj _ _ ih₁ ih₂ | disj _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ | iff _ _ ih₁ ih₂ =>
      simp [starFormula, IsTotalFormula, ih₁, ih₂]
  | neg _ ih => simp [starFormula, IsTotalFormula, ih]
  | forallIn _ _ _ ih | existsIn _ _ _ ih =>
      simp [starFormula, IsTotalFormula, ih]

/-- Total evaluation of `*τ` under hyperreal sequence representatives `fun v ↦ ofSeq (rs v)`
commutes with `ofSeq`. -/
@[simp]
theorem evalTermTotal_starTerm (rs : ℕ → ℕ → ℝ) (t : LTerm ℝ) :
    evalTermTotal (fun v ↦ ofSeq (rs v)) (starTerm t) =
      ofSeq (fun n ↦ evalTermTotal (fun v ↦ rs v n) t) := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | app f args ih =>
      simp only [starTerm, evalTermTotal, starPartialFunN]
      have hargs : (fun i ↦ evalTermTotal (fun v ↦ ofSeq (rs v)) (starTerm (args i))) =
          fun i ↦ ofSeq (fun n ↦ evalTermTotal (fun v ↦ rs v n) (args i)) :=
        funext ih
      rw [hargs, starFunN_ofSeq]

/-- Goldblatt §4.4 & §4.6: For any total-function term `t : LTerm ℝ`, evaluating `starTerm t` on
hyperreals `[rs v]` produces `some (ofSeq (fun n ↦ evalTermTotal (fun v ↦ rs v n) t))`. -/
theorem evalTerm_starTerm_of_total (rs : ℕ → ℕ → ℝ) {t : LTerm ℝ} (ht : IsTotalTerm t) :
    evalTerm (fun v ↦ ofSeq (rs v)) (starTerm t) =
      some (ofSeq (fun n ↦ evalTermTotal (fun v ↦ rs v n) t)) := by
  have hts : IsTotalTerm (starTerm t) := (isTotalTerm_starTerm_iff t).2 ht
  rw [evalTerm_eq_some_evalTermTotal hts, evalTermTotal_starTerm]

/-- Goldblatt §4.4 (pp. 43–44) & Exercise 4.4.1: Enlarging equality on `ℝ` yields equality on `ℝ*`. -/
@[simp]
theorem starRel_eq :
    starRel {v : Fin 2 → ℝ | v 0 = v 1} = {v : Fin 2 → ℝ* | v 0 = v 1} := by
  ext v
  rcases ofSeq_surjective (v 0) with ⟨r₀, hr₀⟩
  rcases ofSeq_surjective (v 1) with ⟨r₁, hr₁⟩
  have hv : v = ![ofSeq r₀, ofSeq r₁] := by
    ext i
    fin_cases i <;> simp [hr₀, hr₁]
  rw [hv]
  change (fun i ↦ ofSeq (![r₀, r₁] i)) ∈ starRel {u : Fin 2 → ℝ | u 0 = u 1} ↔
    ofSeq r₀ = ofSeq r₁
  rw [starRel_ofSeq]
  exact Germ.coe_eq.symm

/-- Goldblatt §4.4 (pp. 43–44) & Exercise 4.4.1: Enlarging `<` on `ℝ` yields `<` on `ℝ*`. -/
@[simp]
theorem starRel_lt :
    starRel {v : Fin 2 → ℝ | v 0 < v 1} = {v : Fin 2 → ℝ* | v 0 < v 1} := by
  ext v
  rcases ofSeq_surjective (v 0) with ⟨r₀, hr₀⟩
  rcases ofSeq_surjective (v 1) with ⟨r₁, hr₁⟩
  have hv : v = ![ofSeq r₀, ofSeq r₁] := by
    ext i
    fin_cases i <;> simp [hr₀, hr₁]
  rw [hv]
  change (fun i ↦ ofSeq (![r₀, r₁] i)) ∈ starRel {u : Fin 2 → ℝ | u 0 < u 1} ↔
    ofSeq r₀ < ofSeq r₁
  rw [starRel_ofSeq]
  exact ofSeq_lt_ofSeq.symm

/-- Goldblatt §4.4 (pp. 43–44) & Exercise 4.4.1: Enlarging `≤` on `ℝ` yields `≤` on `ℝ*`. -/
@[simp]
theorem starRel_le :
    starRel {v : Fin 2 → ℝ | v 0 ≤ v 1} = {v : Fin 2 → ℝ* | v 0 ≤ v 1} := by
  ext v
  rcases ofSeq_surjective (v 0) with ⟨r₀, hr₀⟩
  rcases ofSeq_surjective (v 1) with ⟨r₁, hr₁⟩
  have hv : v = ![ofSeq r₀, ofSeq r₁] := by
    ext i
    fin_cases i <;> simp [hr₀, hr₁]
  rw [hv]
  change (fun i ↦ ofSeq (![r₀, r₁] i)) ∈ starRel {u : Fin 2 → ℝ | u 0 ≤ u 1} ↔
    ofSeq r₀ ≤ ofSeq r₁
  rw [starRel_ofSeq]
  exact ofSeq_le_ofSeq.symm

/-- Goldblatt §4.4 (pp. 43–44) & Exercise 4.4.1: Enlarging unary membership `τ ∈ P` yields
`τ ∈ starSet P`. -/
@[simp]
theorem starRel_mem (P : Set ℝ) :
    starRel {v : Fin 1 → ℝ | v 0 ∈ P} = {v : Fin 1 → ℝ* | v 0 ∈ starSet P} := by
  ext v
  rcases ofSeq_surjective (v 0) with ⟨r, hr⟩
  have hv : v = ![ofSeq r] := by
    ext i
    fin_cases i
    simpa using hr.symm
  rw [hv]
  change (fun i ↦ ofSeq (![r] i)) ∈ starRel {u : Fin 1 → ℝ | u 0 ∈ P} ↔
    ofSeq r ∈ starSet P
  rw [starRel_ofSeq, ofSeq_mem_starSet]
  rfl

/-- `*-transform` of atomic equality `LFormula.eq t₁ t₂`. -/
@[simp]
theorem starFormula_eq (t₁ t₂ : LTerm ℝ) :
    starFormula (LFormula.eq t₁ t₂) = LFormula.eq (starTerm t₁) (starTerm t₂) := by
  unfold LFormula.eq starFormula
  rw [starRel_eq]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- `*-transform` of strict inequality `LFormula.lt t₁ t₂`. -/
@[simp]
theorem starFormula_lt (t₁ t₂ : LTerm ℝ) :
    starFormula (LFormula.lt t₁ t₂) = LFormula.lt (starTerm t₁) (starTerm t₂) := by
  unfold LFormula.lt starFormula
  rw [starRel_lt]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- `*-transform` of nonstrict inequality `LFormula.le t₁ t₂`. -/
@[simp]
theorem starFormula_le (t₁ t₂ : LTerm ℝ) :
    starFormula (LFormula.le t₁ t₂) = LFormula.le (starTerm t₁) (starTerm t₂) := by
  unfold LFormula.le starFormula
  rw [starRel_le]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- `*-transform` of unary membership `LFormula.mem t P`. -/
@[simp]
theorem starFormula_mem (t : LTerm ℝ) (P : Set ℝ) :
    starFormula (LFormula.mem t P) = LFormula.mem (starTerm t) (starSet P) := by
  unfold LFormula.mem starFormula
  rw [starRel_mem]
  congr 1
  ext i
  fin_cases i
  rfl

/-! ## §4.6 & §4.7 Parametric Ultrapower Enlargement and Łoś's Theorem -/

/-- Constructive tuple-to-germ lifting `(Fin k → Germ l S) → Germ l (Fin k → S)` over an arbitrary
index type `I` and filter `l : Filter I`. -/
def piToGermGen {I S : Type*} {l : Filter I} :
    {k : ℕ} → (Fin k → Germ l S) → Germ l (Fin k → S)
  | 0, _ => Germ.const Fin.elim0
  | _ + 1, v => Germ.map₂ Fin.cons (v 0) (piToGermGen (Fin.tail v))

/-- `piToGermGen` applied to coerced families `r : Fin k → I → S` equals the germ of `idx ↦ j ↦ r j idx`. -/
@[simp]
theorem piToGermGen_coe {I S : Type*} {l : Filter I} :
    ∀ {k : ℕ} (r : Fin k → I → S),
      piToGermGen (l := l) (fun j ↦ (r j : Germ l S)) =
        ((fun idx j ↦ r j idx) : Germ l (Fin k → S))
  | 0, _ => Germ.coe_eq.2 <| Eventually.of_forall fun _ ↦ funext fun j ↦ Fin.elim0 j
  | _ + 1, r => by
      unfold piToGermGen
      have htail : (Fin.tail fun j ↦ (r j : Germ l S)) = fun j ↦ (r j.succ : Germ l S) := rfl
      rw [htail, piToGermGen_coe (fun j ↦ r j.succ), Germ.map₂_coe]
      exact Germ.coe_eq.2 <| Eventually.of_forall fun _ ↦ funext fun j ↦
        Fin.cases rfl (fun _ ↦ rfl) j

/-- `piToGermGen` over `ℕ` coincides with `piToGerm` from Chapter 3. -/
theorem piToGermGen_eq_piToGerm {S : Type*} {l : Filter ℕ} :
    ∀ {k : ℕ} (v : Fin k → Germ l S), piToGermGen v = piToGerm v
  | 0, _ => rfl
  | _ + 1, v => by
      simp only [piToGermGen, piToGerm, piToGermGen_eq_piToGerm (Fin.tail v)]

/-- Goldblatt §4.7 (p. 47): Enlargement of a subset `A ⊆ S` in the ultrapower `Germ U S`. -/
def ultrapowerSet {I S : Type*} (U : Ultrafilter I) (A : Set S) : Set (Germ (U : Filter I) S) :=
  {x | Germ.LiftPred (· ∈ A) x}

/-- Goldblatt §4.7 (p. 47): Enlargement of an `m`-ary function `f : S^m → S` on `Germ U S`. -/
def ultrapowerFunN {I S : Type*} (U : Ultrafilter I) {m : ℕ}
    (f : (Fin m → S) → S) (v : Fin m → Germ (U : Filter I) S) : Germ (U : Filter I) S :=
  (piToGermGen (l := (U : Filter I)) v).map f

/-- Goldblatt §4.7 (p. 47): Enlargement of a `k`-ary relation `P ⊆ S^k` on `Germ U S`. -/
def ultrapowerRel {I S : Type*} (U : Ultrafilter I) {k : ℕ}
    (P : Set (Fin k → S)) : Set (Fin k → Germ (U : Filter I) S) :=
  {v | (piToGermGen (l := (U : Filter I)) v).LiftPred (· ∈ P)}

/-- Goldblatt §4.7 (p. 47): Enlargement of an `m`-ary partial function `f : PartialFun S m` on
`Germ U S`. -/
def ultrapowerPartialFun {I S : Type*} (U : Ultrafilter I) {m : ℕ}
    (f : PartialFun S m) : PartialFun (Germ (U : Filter I) S) m where
  dom := ultrapowerRel U f.dom
  toFun := ultrapowerFunN U f.toFun

/-- Goldblatt §4.7 (p. 47): Parametric `*-transform` of an `ℒ_S`-term into `ℒ_{Germ U S}`. -/
def ultrapowerTerm {I S : Type*} (U : Ultrafilter I) : LTerm S → LTerm (Germ (U : Filter I) S)
  | .var x => .var x
  | .const s => .const (s : Germ (U : Filter I) S)
  | .app f args =>
      let sargs := fun j ↦ ultrapowerTerm U (args j)
      .app (ultrapowerPartialFun U f) sargs

/-- Goldblatt §4.7 (p. 47): Parametric `*-transform` of an `ℒ_S`-formula into `ℒ_{Germ U S}`. -/
def ultrapowerFormula {I S : Type*} (U : Ultrafilter I) :
    LFormula S → LFormula (Germ (U : Filter I) S)
  | .rel P args => .rel (ultrapowerRel U P) (fun j ↦ ultrapowerTerm U (args j))
  | .conj φ ψ => .conj (ultrapowerFormula U φ) (ultrapowerFormula U ψ)
  | .disj φ ψ => .disj (ultrapowerFormula U φ) (ultrapowerFormula U ψ)
  | .neg φ => .neg (ultrapowerFormula U φ)
  | .imp φ ψ => .imp (ultrapowerFormula U φ) (ultrapowerFormula U ψ)
  | .iff φ ψ => .iff (ultrapowerFormula U φ) (ultrapowerFormula U ψ)
  | .forallIn P x φ => .forallIn (ultrapowerSet U P) x (ultrapowerFormula U φ)
  | .existsIn P x φ => .existsIn (ultrapowerSet U P) x (ultrapowerFormula U φ)

/-- Membership of a tuple of germs in `ultrapowerRel U P` holds iff the tuple of representatives
eventually belongs to `P` along `U`. -/
@[simp]
theorem ultrapowerRel_coe {I S : Type*} (U : Ultrafilter I) {k : ℕ}
    (P : Set (Fin k → S)) (r : Fin k → I → S) :
    (fun j ↦ ((r j : I → S) : Germ (U : Filter I) S)) ∈ ultrapowerRel U P ↔
      ∀ᶠ idx in (U : Filter I), (fun j ↦ r j idx) ∈ P := by
  change (piToGermGen (l := (U : Filter I))
    (fun j ↦ ((r j : I → S) : Germ (U : Filter I) S))).LiftPred (· ∈ P) ↔ _
  rw [piToGermGen_coe, Germ.liftPred_coe]

/-- `ultrapowerFunN U f` acts componentwise on germ representatives. -/
@[simp]
theorem ultrapowerFunN_coe {I S : Type*} (U : Ultrafilter I) {m : ℕ}
    (f : (Fin m → S) → S) (r : Fin m → I → S) :
    ultrapowerFunN U f (fun j ↦ ((r j : I → S) : Germ (U : Filter I) S)) =
      ((fun idx ↦ f (fun j ↦ r j idx)) : Germ (U : Filter I) S) := by
  unfold ultrapowerFunN
  rw [piToGermGen_coe]
  rfl

/-- `ultrapowerTerm U` preserves the variables occurring in a term. -/
@[simp]
theorem freeVarsTerm_ultrapowerTerm {I S : Type*} (U : Ultrafilter I) (t : LTerm S) :
    freeVarsTerm (ultrapowerTerm U t) = freeVarsTerm t := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | app _ args ih =>
      simp only [ultrapowerTerm, freeVarsTerm]
      congr 1
      funext j
      exact ih j

/-- `ultrapowerFormula U` preserves the free variables of a formula. -/
@[simp]
theorem freeVarsFormula_ultrapowerFormula {I S : Type*} (U : Ultrafilter I) (φ : LFormula S) :
    freeVarsFormula (ultrapowerFormula U φ) = freeVarsFormula φ := by
  induction φ with
  | rel _ _ => simp [ultrapowerFormula, freeVarsFormula]
  | conj _ _ ih₁ ih₂ | disj _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ | iff _ _ ih₁ ih₂ =>
      simp [ultrapowerFormula, freeVarsFormula, ih₁, ih₂]
  | neg _ ih => simp [ultrapowerFormula, freeVarsFormula, ih]
  | forallIn _ _ _ ih | existsIn _ _ _ ih =>
      simp [ultrapowerFormula, freeVarsFormula, ih]

/-- `starTerm` coincides definitionally/extensionally with `ultrapowerTerm (hyperfilter ℕ)`. -/
theorem starTerm_eq_ultrapowerTerm (t : LTerm ℝ) :
    (starTerm t : LTerm (Germ (hyperfilter ℕ : Filter ℕ) ℝ)) =
      ultrapowerTerm (hyperfilter ℕ) t := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | app f args ih =>
      change LTerm.app (S := Germ (hyperfilter ℕ : Filter ℕ) ℝ) (starPartialFunN f)
          (fun j ↦ (starTerm (args j) : LTerm (Germ (hyperfilter ℕ : Filter ℕ) ℝ))) =
        LTerm.app (ultrapowerPartialFun (hyperfilter ℕ) f)
          (fun j ↦ ultrapowerTerm (hyperfilter ℕ) (args j))
      have hpf : (starPartialFunN f : PartialFun (Germ (hyperfilter ℕ : Filter ℕ) ℝ) _) =
          ultrapowerPartialFun (hyperfilter ℕ) f := by
        cases f with
        | mk dom toFun =>
            change PartialFun.mk
                {v : Fin _ → Germ (hyperfilter ℕ : Filter ℕ) ℝ |
                  (piToGerm v).LiftPred (· ∈ dom)}
                (fun v ↦ (piToGerm v).map toFun) =
              PartialFun.mk
                {v : Fin _ → Germ (hyperfilter ℕ : Filter ℕ) ℝ |
                  (piToGermGen v).LiftPred (· ∈ dom)}
                (fun v ↦ (piToGermGen v).map toFun)
            simp only [piToGermGen_eq_piToGerm]
      rw [hpf]
      congr 1
      funext j
      exact ih j

/-- `starFormula` coincides with `ultrapowerFormula (hyperfilter ℕ)` on `Germ (hyperfilter ℕ) ℝ`. -/
theorem starFormula_eq_ultrapowerFormula (φ : LFormula ℝ) :
    (starFormula φ : LFormula (Germ (hyperfilter ℕ : Filter ℕ) ℝ)) =
      ultrapowerFormula (hyperfilter ℕ) φ := by
  induction φ with
  | rel P args =>
      change LFormula.rel (S := Germ (hyperfilter ℕ : Filter ℕ) ℝ)
          {v : Fin _ → Germ (hyperfilter ℕ : Filter ℕ) ℝ | (piToGerm v).LiftPred (· ∈ P)}
          (fun j ↦ (starTerm (args j) : LTerm (Germ (hyperfilter ℕ : Filter ℕ) ℝ))) =
        LFormula.rel (ultrapowerRel (hyperfilter ℕ) P)
          (fun j ↦ ultrapowerTerm (hyperfilter ℕ) (args j))
      have hrel :
          {v : Fin _ → Germ (hyperfilter ℕ : Filter ℕ) ℝ | (piToGerm v).LiftPred (· ∈ P)} =
            ultrapowerRel (hyperfilter ℕ) P := by
        ext v
        simp [ultrapowerRel, piToGermGen_eq_piToGerm]
      rw [hrel]
      congr 1
      funext j
      exact starTerm_eq_ultrapowerTerm (args j)
  | conj φ ψ ih₁ ih₂ =>
      change LFormula.conj (S := Germ (hyperfilter ℕ : Filter ℕ) ℝ) (starFormula φ) (starFormula ψ) =
        LFormula.conj (ultrapowerFormula (hyperfilter ℕ) φ) (ultrapowerFormula (hyperfilter ℕ) ψ)
      rw [ih₁, ih₂]
  | disj φ ψ ih₁ ih₂ =>
      change LFormula.disj (S := Germ (hyperfilter ℕ : Filter ℕ) ℝ) (starFormula φ) (starFormula ψ) =
        LFormula.disj (ultrapowerFormula (hyperfilter ℕ) φ) (ultrapowerFormula (hyperfilter ℕ) ψ)
      rw [ih₁, ih₂]
  | imp φ ψ ih₁ ih₂ =>
      change LFormula.imp (S := Germ (hyperfilter ℕ : Filter ℕ) ℝ) (starFormula φ) (starFormula ψ) =
        LFormula.imp (ultrapowerFormula (hyperfilter ℕ) φ) (ultrapowerFormula (hyperfilter ℕ) ψ)
      rw [ih₁, ih₂]
  | iff φ ψ ih₁ ih₂ =>
      change LFormula.iff (S := Germ (hyperfilter ℕ : Filter ℕ) ℝ) (starFormula φ) (starFormula ψ) =
        LFormula.iff (ultrapowerFormula (hyperfilter ℕ) φ) (ultrapowerFormula (hyperfilter ℕ) ψ)
      rw [ih₁, ih₂]
  | neg φ ih =>
      change LFormula.neg (S := Germ (hyperfilter ℕ : Filter ℕ) ℝ) (starFormula φ) =
        LFormula.neg (ultrapowerFormula (hyperfilter ℕ) φ)
      rw [ih]
  | forallIn P x φ ih =>
      change LFormula.forallIn (S := Germ (hyperfilter ℕ : Filter ℕ) ℝ)
          (ultrapowerSet (hyperfilter ℕ) P) x (starFormula φ) =
        LFormula.forallIn (ultrapowerSet (hyperfilter ℕ) P) x
          (ultrapowerFormula (hyperfilter ℕ) φ)
      rw [ih]
  | existsIn P x φ ih =>
      change LFormula.existsIn (S := Germ (hyperfilter ℕ : Filter ℕ) ℝ)
          (ultrapowerSet (hyperfilter ℕ) P) x (starFormula φ) =
        LFormula.existsIn (ultrapowerSet (hyperfilter ℕ) P) x
          (ultrapowerFormula (hyperfilter ℕ) φ)
      rw [ih]

/-- Characterization of `IsDefinedTerm` on `app f args` via `Option.getD` with a fallback value. -/
theorem isDefinedTerm_app_iff_getD {S : Type*} (env : ℕ → S) (fallback : S) {m : ℕ}
    (f : PartialFun S m) (args : Fin m → LTerm S) :
    IsDefinedTerm env (.app f args) ↔
      (∀ j, IsDefinedTerm env (args j)) ∧
        (fun j ↦ (evalTerm env (args j)).getD fallback) ∈ f.dom := by
  constructor
  · intro hdef
    rcases Option.ne_none_iff_exists'.1 hdef with ⟨val, hval⟩
    rcases evalTerm_app_eq_some.1 hval with ⟨v, hv, hdom, _⟩
    refine ⟨fun j ↦ by rw [IsDefinedTerm, hv j]; exact Option.some_ne_none _, ?_⟩
    have hv_eq : (fun j ↦ (evalTerm env (args j)).getD fallback) = v := by
      ext j
      simp [hv j]
    rwa [hv_eq]
  · rintro ⟨hall, hdom⟩
    have hv : ∀ j, evalTerm env (args j) = some ((evalTerm env (args j)).getD fallback) := by
      intro j
      rcases Option.ne_none_iff_exists'.1 (hall j) with ⟨a, ha⟩
      simp [ha]
    rw [IsDefinedTerm]
    intro hnone
    have hsome : evalTerm env (.app f args) =
        some (f.toFun (fun j ↦ (evalTerm env (args j)).getD fallback)) :=
      evalTerm_app_eq_some.2 ⟨_, hv, hdom, rfl⟩
    rw [hsome] at hnone
    exact Option.some_ne_none _ hnone

/-- When `.app f args` is defined, `(evalTerm env (.app f args)).getD fallback` equals `f.toFun`
applied to the `getD` values of its arguments. -/
theorem getD_evalTerm_app_of_isDefinedTerm {S : Type*} {env : ℕ → S} (fallback : S) {m : ℕ}
    {f : PartialFun S m} {args : Fin m → LTerm S}
    (hdef : IsDefinedTerm env (.app f args)) :
    (evalTerm env (.app f args)).getD fallback =
      f.toFun (fun j ↦ (evalTerm env (args j)).getD fallback) := by
  rcases Option.ne_none_iff_exists'.1 hdef with ⟨val, hval⟩
  rcases evalTerm_app_eq_some.1 hval with ⟨v, hv, _, rfl⟩
  have hv_eq : (fun j ↦ (evalTerm env (args j)).getD fallback) = v := by
    ext j
    simp [hv j]
  simp [hval, hv_eq]

/-- Complete evaluation characterization of `ultrapowerTerm U t` for arbitrary partial-function
terms `t : LTerm S`. -/
theorem evalTerm_ultrapowerTerm_characterization {I S : Type*} (U : Ultrafilter I)
    (rs : ℕ → I → S) (t : LTerm S) :
    ((∀ᶠ idx in (U : Filter I), IsDefinedTerm (fun v ↦ rs v idx) t) →
      evalTerm (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)) (ultrapowerTerm U t) =
        some (((fun idx ↦ (evalTerm (fun v ↦ rs v idx) t).getD (rs 0 idx)) : I → S) :
          Germ (U : Filter I) S)) ∧
    ((¬ ∀ᶠ idx in (U : Filter I), IsDefinedTerm (fun v ↦ rs v idx) t) →
      evalTerm (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)) (ultrapowerTerm U t) = none) := by
  induction t with
  | var x =>
      refine ⟨fun _ ↦ rfl, fun hnot ↦ ?_⟩
      exfalso
      exact hnot (Eventually.of_forall fun _ ↦ Option.some_ne_none _)
  | const s =>
      refine ⟨fun _ ↦ rfl, fun hnot ↦ ?_⟩
      exfalso
      exact hnot (Eventually.of_forall fun _ ↦ Option.some_ne_none _)
  | app f args ih =>
      let w : Fin _ → I → S := fun j idx ↦ (evalTerm (fun v ↦ rs v idx) (args j)).getD (rs 0 idx)
      constructor
      · intro hdef
        have hdecomp : ∀ᶠ idx in (U : Filter I),
            (∀ j, IsDefinedTerm (fun v ↦ rs v idx) (args j)) ∧ (fun j ↦ w j idx) ∈ f.dom :=
          hdef.mono fun idx hidx ↦
            (isDefinedTerm_app_iff_getD (fun v ↦ rs v idx) (rs 0 idx) f args).1 hidx
        have hall_j : ∀ j, ∀ᶠ idx in (U : Filter I), IsDefinedTerm (fun v ↦ rs v idx) (args j) :=
          fun j ↦ hdecomp.mono fun idx hidx ↦ hidx.1 j
        have hdom_ev : ∀ᶠ idx in (U : Filter I), (fun j ↦ w j idx) ∈ f.dom :=
          hdecomp.mono fun idx hidx ↦ hidx.2
        have heval_j : ∀ j,
            evalTerm (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S))
              (ultrapowerTerm U (args j)) =
              some ((w j : I → S) : Germ (U : Filter I) S) :=
          fun j ↦ (ih j).1 (hall_j j)
        have hdom_germ : (fun j ↦ ((w j : I → S) : Germ (U : Filter I) S)) ∈
            (ultrapowerPartialFun U f).dom :=
          (ultrapowerRel_coe U f.dom w).2 hdom_ev
        rw [ultrapowerTerm, evalTerm_app_eq_some]
        refine ⟨fun j ↦ ((w j : I → S) : Germ (U : Filter I) S), heval_j, hdom_germ, ?_⟩
        change ultrapowerFunN U f.toFun (fun j ↦ ((w j : I → S) : Germ (U : Filter I) S)) = _
        rw [ultrapowerFunN_coe]
        exact Germ.coe_eq.2 <| hdef.mono fun idx hidx ↦
          (getD_evalTerm_app_of_isDefinedTerm (rs 0 idx) hidx).symm
      · intro hndef
        rw [ultrapowerTerm, evalTerm_app_eq_none]
        by_cases hall_j : ∀ j, ∀ᶠ idx in (U : Filter I), IsDefinedTerm (fun v ↦ rs v idx) (args j)
        · right
          refine ⟨fun j ↦ ((w j : I → S) : Germ (U : Filter I) S),
            fun j ↦ (ih j).1 (hall_j j), ?_⟩
          intro hdom_germ
          have hdom_ev : ∀ᶠ idx in (U : Filter I), (fun j ↦ w j idx) ∈ f.dom :=
            (ultrapowerRel_coe U f.dom w).1 hdom_germ
          have hall_ev : ∀ᶠ idx in (U : Filter I),
              ∀ j, IsDefinedTerm (fun v ↦ rs v idx) (args j) :=
            eventually_all.2 hall_j
          apply hndef
          exact (hall_ev.and hdom_ev).mono fun idx ⟨hj, hd⟩ ↦
            (isDefinedTerm_app_iff_getD (fun v ↦ rs v idx) (rs 0 idx) f args).2 ⟨hj, hd⟩
        · left
          rcases Classical.not_forall.1 hall_j with ⟨j, hj⟩
          exact ⟨j, (ih j).2 hj⟩

/-- `ultrapowerTerm U t` is defined on germs iff `t` is defined almost everywhere wrt `U`. -/
theorem isDefinedTerm_ultrapowerTerm_iff {I S : Type*} (U : Ultrafilter I)
    (rs : ℕ → I → S) (t : LTerm S) :
    IsDefinedTerm (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)) (ultrapowerTerm U t) ↔
      ∀ᶠ idx in (U : Filter I), IsDefinedTerm (fun v ↦ rs v idx) t := by
  have hchar := evalTerm_ultrapowerTerm_characterization U rs t
  constructor
  · intro hdef
    by_contra hnot
    exact hdef (hchar.2 hnot)
  · intro hev
    rw [IsDefinedTerm, hchar.1 hev]
    exact Option.some_ne_none _

/-- Specialization of `isDefinedTerm_ultrapowerTerm_iff` to `ℝ*`: `*τ` is defined iff `τ` is
defined for almost all `n ∈ ℕ`. -/
theorem isDefinedTerm_starTerm_iff (rs : ℕ → ℕ → ℝ) (t : LTerm ℝ) :
    IsDefinedTerm (fun v ↦ ofSeq (rs v)) (starTerm t) ↔
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), IsDefinedTerm (fun v ↦ rs v n) t := by
  change IsDefinedTerm (S := Germ (hyperfilter ℕ : Filter ℕ) ℝ)
      (fun v ↦ ((rs v : ℕ → ℝ) : Germ (hyperfilter ℕ : Filter ℕ) ℝ))
      (starTerm t : LTerm (Germ (hyperfilter ℕ : Filter ℕ) ℝ)) ↔ _
  rw [starTerm_eq_ultrapowerTerm]
  exact isDefinedTerm_ultrapowerTerm_iff (hyperfilter ℕ) rs t

/-- Implication from an index-independent proposition `P` commutes with `∀ᶠ idx in l`. -/
theorem eventually_imp_of_const_left {I : Type*} {l : Filter I} (P : Prop) {Q : I → Prop} :
    (P → ∀ᶠ idx in l, Q idx) ↔ ∀ᶠ idx in l, (P → Q idx) := by
  constructor
  · intro h
    by_cases hp : P
    · exact (h hp).mono fun _ hq _ ↦ hq
    · exact Eventually.of_forall fun _ hp' ↦ absurd hp' hp
  · exact fun h hp ↦ h.mono fun _ hq ↦ hq hp

/-- `allClosedSubtermsDefined` on `ultrapowerTerm U t` holds iff it holds eventually along `U`. -/
theorem allClosedSubtermsDefined_ultrapowerTerm_iff {I S : Type*} (U : Ultrafilter I)
    (rs : ℕ → I → S) (bound : Finset ℕ) (t : LTerm S) :
    allClosedSubtermsDefined (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)) bound
        (ultrapowerTerm U t) ↔
      ∀ᶠ idx in (U : Filter I), allClosedSubtermsDefined (fun v ↦ rs v idx) bound t := by
  induction t with
  | var _ => simp [ultrapowerTerm, allClosedSubtermsDefined]
  | const _ => simp [ultrapowerTerm, allClosedSubtermsDefined]
  | app f args ih =>
      have hfv : freeVarsTerm (ultrapowerTerm U (.app f args)) = freeVarsTerm (.app f args) :=
        freeVarsTerm_ultrapowerTerm U (.app f args)
      have htop :
          (Disjoint (freeVarsTerm (ultrapowerTerm U (.app f args))) bound →
            IsDefinedTerm (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S))
              (ultrapowerTerm U (.app f args))) ↔
          ∀ᶠ idx in (U : Filter I),
            (Disjoint (freeVarsTerm (.app f args)) bound →
              IsDefinedTerm (fun v ↦ rs v idx) (.app f args)) := by
        rw [hfv, isDefinedTerm_ultrapowerTerm_iff, eventually_imp_of_const_left]
      have hsub :
          (∀ j, allClosedSubtermsDefined
            (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)) bound
            (ultrapowerTerm U (args j))) ↔
          ∀ᶠ idx in (U : Filter I),
            ∀ j, allClosedSubtermsDefined (fun v ↦ rs v idx) bound (args j) := by
        rw [forall_congr' ih, eventually_all]
      change (Disjoint (freeVarsTerm (ultrapowerTerm U (.app f args))) bound →
          IsDefinedTerm (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S))
            (ultrapowerTerm U (.app f args))) ∧
        (∀ j, allClosedSubtermsDefined
          (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)) bound
          (ultrapowerTerm U (args j))) ↔ _
      rw [htop, hsub, ← eventually_and]
      rfl

/-- `IsDefinedFormulaWithBound` on `ultrapowerFormula U φ` holds iff it holds eventually along `U`. -/
theorem isDefinedFormulaWithBound_ultrapowerFormula_iff {I S : Type*} (U : Ultrafilter I)
    (rs : ℕ → I → S) (bound : Finset ℕ) (φ : LFormula S) :
    IsDefinedFormulaWithBound (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)) bound
        (ultrapowerFormula U φ) ↔
      ∀ᶠ idx in (U : Filter I), IsDefinedFormulaWithBound (fun v ↦ rs v idx) bound φ := by
  induction φ generalizing bound with
  | rel P args =>
      simp only [ultrapowerFormula, IsDefinedFormulaWithBound,
        allClosedSubtermsDefined_ultrapowerTerm_iff, eventually_all]
  | conj _ _ ih₁ ih₂ | disj _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ | iff _ _ ih₁ ih₂ =>
      simp only [ultrapowerFormula, IsDefinedFormulaWithBound, ih₁ bound, ih₂ bound, eventually_and]
  | neg _ ih =>
      exact ih bound
  | forallIn _ x _ ih | existsIn _ x _ ih =>
      exact ih (insert x bound)

/-- Definedness of `ultrapowerFormula U φ` holds iff `φ` is defined almost everywhere wrt `U`. -/
theorem isDefinedFormula_ultrapowerFormula_iff {I S : Type*} (U : Ultrafilter I)
    (rs : ℕ → I → S) (φ : LFormula S) :
    IsDefinedFormula (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)) (ultrapowerFormula U φ) ↔
      ∀ᶠ idx in (U : Filter I), IsDefinedFormula (fun v ↦ rs v idx) φ :=
  isDefinedFormulaWithBound_ultrapowerFormula_iff U rs ∅ φ

/-- Along an ultrafilter `U`, implication commutes with `∀ᶠ`. -/
theorem ultrafilter_eventually_imp {I : Type*} (U : Ultrafilter I) {P Q : I → Prop} :
    ((∀ᶠ idx in (U : Filter I), P idx) → (∀ᶠ idx in (U : Filter I), Q idx)) ↔
      ∀ᶠ idx in (U : Filter I), (P idx → Q idx) := by
  constructor
  · intro h
    by_cases hP : ∀ᶠ idx in (U : Filter I), P idx
    · exact (h hP).mono fun _ hq _ ↦ hq
    · exact (Ultrafilter.eventually_not.2 hP).mono fun _ hnp hp ↦ absurd hp hnp
  · exact fun h hP ↦ (h.and hP).mono fun _ ⟨hpq, hp⟩ ↦ hpq hp

/-- Along an ultrafilter `U`, logical equivalence commutes with `∀ᶠ`. -/
theorem ultrafilter_eventually_iff {I : Type*} (U : Ultrafilter I) {P Q : I → Prop} :
    ((∀ᶠ idx in (U : Filter I), P idx) ↔ (∀ᶠ idx in (U : Filter I), Q idx)) ↔
      ∀ᶠ idx in (U : Filter I), (P idx ↔ Q idx) := by
  constructor
  · intro h
    by_cases hP : ∀ᶠ idx in (U : Filter I), P idx
    · exact (hP.and (h.1 hP)).mono fun _ ⟨hp, hq⟩ ↦ ⟨fun _ ↦ hq, fun _ ↦ hp⟩
    · have hnP : ∀ᶠ idx in (U : Filter I), ¬ P idx := Ultrafilter.eventually_not.2 hP
      have hnQ : ∀ᶠ idx in (U : Filter I), ¬ Q idx := Ultrafilter.eventually_not.2 (hP ∘ h.2)
      exact (hnP.and hnQ).mono fun _ ⟨hnp, hnq⟩ ↦
        ⟨fun hp ↦ absurd hp hnp, fun hq ↦ absurd hq hnq⟩
  · intro h
    exact ⟨fun hP ↦ (h.and hP).mono fun _ ⟨hpq, hp⟩ ↦ hpq.1 hp,
           fun hQ ↦ (h.and hQ).mono fun _ ⟨hpq, hq⟩ ↦ hpq.2 hq⟩

/-- Goldblatt §4.7 (p. 47): Parametric statement-value set `⟦φ(rs)⟧ = {i ∈ I | Holds (rs · i) φ}`. -/
def parametricStmtVal (I : Type*) {S : Type*} (φ : LFormula S) (rs : ℕ → I → S) : Set I :=
  {idx : I | Holds (fun v ↦ rs v idx) φ}

/-- Goldblatt §4.7 (p. 47): **Parametric Łoś's Theorem** for the ultrapower `Germ (U : Filter I) S`
of an arbitrary carrier type `S` modulo an arbitrary ultrafilter `U : Ultrafilter I`. -/
theorem parametric_los_theorem {I S : Type*} (U : Ultrafilter I)
    (φ : LFormula S) (rs : ℕ → I → S) :
    Holds (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)) (ultrapowerFormula U φ) ↔
      parametricStmtVal I φ rs ∈ (U : Filter I) := by
  change Holds (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)) (ultrapowerFormula U φ) ↔
    ∀ᶠ idx in (U : Filter I), Holds (fun v ↦ rs v idx) φ
  induction φ generalizing rs with
  | rel P args =>
      simp only [ultrapowerFormula, holds_rel]
      let w : Fin _ → I → S := fun j idx ↦ (evalTerm (fun v ↦ rs v idx) (args j)).getD (rs 0 idx)
      constructor
      · rintro ⟨vGerm, hvGerm, hvP⟩
        have hall_j : ∀ j, ∀ᶠ idx in (U : Filter I),
            IsDefinedTerm (fun v ↦ rs v idx) (args j) := by
          intro j
          apply (isDefinedTerm_ultrapowerTerm_iff U rs (args j)).1
          rw [IsDefinedTerm, hvGerm j]
          exact Option.some_ne_none _
        have hv_eq : vGerm = fun j ↦ ((w j : I → S) : Germ (U : Filter I) S) := by
          ext j
          have hchar := (evalTerm_ultrapowerTerm_characterization U rs (args j)).1 (hall_j j)
          exact Option.some.inj ((hvGerm j).symm.trans hchar)
        rw [hv_eq, ultrapowerRel_coe] at hvP
        have hall_ev : ∀ᶠ idx in (U : Filter I),
            ∀ j, IsDefinedTerm (fun v ↦ rs v idx) (args j) := eventually_all.2 hall_j
        refine (hall_ev.and hvP).mono fun idx ⟨hdef_idx, hP_idx⟩ ↦ ?_
        refine ⟨fun j ↦ w j idx, fun j ↦ ?_, hP_idx⟩
        rcases Option.ne_none_iff_exists'.1 (hdef_idx j) with ⟨a, ha⟩
        simp [w, ha]
      · intro hev
        have hall_j : ∀ j, ∀ᶠ idx in (U : Filter I),
            IsDefinedTerm (fun v ↦ rs v idx) (args j) := by
          intro j
          refine hev.mono fun idx ⟨v, hv, _⟩ ↦ ?_
          rw [IsDefinedTerm, hv j]
          exact Option.some_ne_none _
        have hwP : ∀ᶠ idx in (U : Filter I), (fun j ↦ w j idx) ∈ P := by
          refine hev.mono fun idx ⟨v, hv, hvP⟩ ↦ ?_
          have hweq : (fun j ↦ w j idx) = v := by
            ext j
            simp [w, hv j]
          rwa [hweq]
        refine ⟨fun j ↦ ((w j : I → S) : Germ (U : Filter I) S),
          fun j ↦ (evalTerm_ultrapowerTerm_characterization U rs (args j)).1 (hall_j j),
          (ultrapowerRel_coe U P w).2 hwP⟩
  | conj φ ψ ih₁ ih₂ =>
      simp only [ultrapowerFormula, holds_conj, ih₁ rs, ih₂ rs, eventually_and]
  | disj φ ψ ih₁ ih₂ =>
      simp only [ultrapowerFormula, holds_disj, ih₁ rs, ih₂ rs, Ultrafilter.eventually_or]
  | neg φ ih =>
      simp only [ultrapowerFormula, holds_neg, ih rs, Ultrafilter.eventually_not]
  | imp φ ψ ih₁ ih₂ =>
      simp only [ultrapowerFormula, holds_imp, ih₁ rs, ih₂ rs, ultrafilter_eventually_imp]
  | iff φ ψ ih₁ ih₂ =>
      simp only [ultrapowerFormula, holds_iff, ih₁ rs, ih₂ rs, ultrafilter_eventually_iff]
  | forallIn P x φ ih =>
      simp only [ultrapowerFormula, holds_forallIn]
      constructor
      · intro hfor
        by_contra hnot
        have hev_not : ∀ᶠ idx in (U : Filter I),
            ∃ s ∈ P, IsDefinedFormula (Function.update (fun v ↦ rs v idx) x s) φ ∧
              ¬ Holds (Function.update (fun v ↦ rs v idx) x s) φ := by
          refine (Ultrafilter.eventually_not.2 hnot).mono fun idx hidx ↦ ?_
          rcases Classical.not_forall.1 hidx with ⟨s, hs⟩
          rcases Classical.not_imp.1 hs with ⟨hsP, hs'⟩
          rcases Classical.not_imp.1 hs' with ⟨hdef, hnholds⟩
          exact ⟨s, hsP, hdef, hnholds⟩
        let w : I → S := fun idx ↦
          if h : ∃ s ∈ P, IsDefinedFormula (Function.update (fun v ↦ rs v idx) x s) φ ∧
              ¬ Holds (Function.update (fun v ↦ rs v idx) x s) φ
          then h.choose else rs 0 idx
        let rs' : ℕ → I → S := Function.update rs x w
        have hupd_germ : Function.update (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)) x
            ((w : I → S) : Germ (U : Filter I) S) =
            fun v ↦ ((rs' v : I → S) : Germ (U : Filter I) S) := by
          ext v
          by_cases hv : v = x <;> simp [rs', hv]
        have hupd_idx : ∀ idx : I,
            Function.update (fun v ↦ rs v idx) x (w idx) = fun v ↦ rs' v idx := by
          intro idx
          ext v
          by_cases hv : v = x <;> simp [rs', hv]
        have hwP : ((w : I → S) : Germ (U : Filter I) S) ∈ ultrapowerSet U P := by
          refine hev_not.mono fun idx hidx ↦ ?_
          have hw_eq : w idx = hidx.choose := dite_eq_left_of_eq_true (eq_true hidx)
          rw [hw_eq]
          exact hidx.choose_spec.1
        have hwDef : IsDefinedFormula
            (Function.update (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)) x
              ((w : I → S) : Germ (U : Filter I) S)) (ultrapowerFormula U φ) := by
          rw [hupd_germ, isDefinedFormula_ultrapowerFormula_iff]
          refine hev_not.mono fun idx hidx ↦ ?_
          rw [← hupd_idx idx]
          have hw_eq : w idx = hidx.choose := dite_eq_left_of_eq_true (eq_true hidx)
          rw [hw_eq]
          exact hidx.choose_spec.2.1
        have hwHolds : Holds (fun v ↦ ((rs' v : I → S) : Germ (U : Filter I) S))
            (ultrapowerFormula U φ) := by
          rw [← hupd_germ]
          exact hfor _ hwP hwDef
        have hevHolds : ∀ᶠ idx in (U : Filter I), Holds (fun v ↦ rs' v idx) φ :=
          (ih rs').1 hwHolds
        have hevNotHolds : ∀ᶠ idx in (U : Filter I), ¬ Holds (fun v ↦ rs' v idx) φ := by
          refine hev_not.mono fun idx hidx ↦ ?_
          rw [← hupd_idx idx]
          have hw_eq : w idx = hidx.choose := dite_eq_left_of_eq_true (eq_true hidx)
          rw [hw_eq]
          exact hidx.choose_spec.2.2
        exact (Ultrafilter.eventually_not.1 hevNotHolds) hevHolds
      · intro hev sGerm
        refine Germ.inductionOn sGerm fun w hsP hsDef ↦ ?_
        let rs' : ℕ → I → S := Function.update rs x w
        have hupd_germ : Function.update (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)) x
            ((w : I → S) : Germ (U : Filter I) S) =
            fun v ↦ ((rs' v : I → S) : Germ (U : Filter I) S) := by
          ext v
          by_cases hv : v = x <;> simp [rs', hv]
        have hupd_idx : ∀ idx : I,
            Function.update (fun v ↦ rs v idx) x (w idx) = fun v ↦ rs' v idx := by
          intro idx
          ext v
          by_cases hv : v = x <;> simp [rs', hv]
        have hwP_ev : ∀ᶠ idx in (U : Filter I), w idx ∈ P := hsP
        have hwDef_ev : ∀ᶠ idx in (U : Filter I), IsDefinedFormula (fun v ↦ rs' v idx) φ := by
          rw [hupd_germ, isDefinedFormula_ultrapowerFormula_iff] at hsDef
          exact hsDef
        rw [hupd_germ, ih rs']
        refine ((hev.and hwP_ev).and hwDef_ev).mono fun idx ⟨⟨hfor_idx, hP_idx⟩, hdef_idx⟩ ↦ ?_
        rw [← hupd_idx idx] at hdef_idx ⊢
        exact hfor_idx (w idx) hP_idx hdef_idx
  | existsIn P x φ ih =>
      simp only [ultrapowerFormula, holds_existsIn]
      constructor
      · rintro ⟨sGerm, hs⟩
        refine Germ.inductionOn sGerm (fun w hw ↦ ?_) hs
        rcases hw with ⟨hsP, hsDef, hsHolds⟩
        let rs' : ℕ → I → S := Function.update rs x w
        have hupd_germ : Function.update (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)) x
            ((w : I → S) : Germ (U : Filter I) S) =
            fun v ↦ ((rs' v : I → S) : Germ (U : Filter I) S) := by
          ext v
          by_cases hv : v = x <;> simp [rs', hv]
        have hupd_idx : ∀ idx : I,
            Function.update (fun v ↦ rs v idx) x (w idx) = fun v ↦ rs' v idx := by
          intro idx
          ext v
          by_cases hv : v = x <;> simp [rs', hv]
        have hwP_ev : ∀ᶠ idx in (U : Filter I), w idx ∈ P := hsP
        have hwDef_ev : ∀ᶠ idx in (U : Filter I), IsDefinedFormula (fun v ↦ rs' v idx) φ := by
          rw [hupd_germ, isDefinedFormula_ultrapowerFormula_iff] at hsDef
          exact hsDef
        have hwHolds_ev : ∀ᶠ idx in (U : Filter I), Holds (fun v ↦ rs' v idx) φ := by
          rw [hupd_germ, ih rs'] at hsHolds
          exact hsHolds
        refine ((hwP_ev.and hwDef_ev).and hwHolds_ev).mono fun idx ⟨⟨hP_idx, hdef_idx⟩, hh_idx⟩ ↦ ?_
        rw [← hupd_idx idx] at hdef_idx hh_idx
        exact ⟨w idx, hP_idx, hdef_idx, hh_idx⟩
      · intro hev
        let w : I → S := fun idx ↦
          if h : ∃ s ∈ P, IsDefinedFormula (Function.update (fun v ↦ rs v idx) x s) φ ∧
              Holds (Function.update (fun v ↦ rs v idx) x s) φ
          then h.choose else rs 0 idx
        let rs' : ℕ → I → S := Function.update rs x w
        have hupd_germ : Function.update (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)) x
            ((w : I → S) : Germ (U : Filter I) S) =
            fun v ↦ ((rs' v : I → S) : Germ (U : Filter I) S) := by
          ext v
          by_cases hv : v = x <;> simp [rs', hv]
        have hupd_idx : ∀ idx : I,
            Function.update (fun v ↦ rs v idx) x (w idx) = fun v ↦ rs' v idx := by
          intro idx
          ext v
          by_cases hv : v = x <;> simp [rs', hv]
        refine ⟨((w : I → S) : Germ (U : Filter I) S), ?_, ?_, ?_⟩
        · refine hev.mono fun idx hidx ↦ ?_
          have hw_eq : w idx = hidx.choose := dite_eq_left_of_eq_true (eq_true hidx)
          rw [hw_eq]
          exact hidx.choose_spec.1
        · rw [hupd_germ, isDefinedFormula_ultrapowerFormula_iff]
          refine hev.mono fun idx hidx ↦ ?_
          rw [← hupd_idx idx]
          have hw_eq : w idx = hidx.choose := dite_eq_left_of_eq_true (eq_true hidx)
          rw [hw_eq]
          exact hidx.choose_spec.2.1
        · rw [hupd_germ, ih rs']
          refine hev.mono fun idx hidx ↦ ?_
          rw [← hupd_idx idx]
          have hw_eq : w idx = hidx.choose := dite_eq_left_of_eq_true (eq_true hidx)
          rw [hw_eq]
          exact hidx.choose_spec.2.2

/-- Goldblatt §4.6 (p. 46): Statement-value set `⟦φ(r^1, …, r^p)⟧ = {n ∈ ℕ | Holds (r · n) φ}`
extending `⟦r = s⟧` and `⟦r < s⟧` to arbitrary `ℒ_ℝ`-formulae. -/
def stmtVal (φ : LFormula ℝ) (rs : ℕ → ℕ → ℝ) : Set ℕ :=
  {n : ℕ | Holds (fun v ↦ rs v n) φ}

/-- Goldblatt §4.6 (p. 47): **Łoś's Theorem** for `ℝ*`: for any `ℒ_ℝ`-formula `φ` (including
partial functions) and sequences `rs : ℕ → ℕ → ℝ`, `*φ([rs])` holds in `ℝ*` if and only if
`stmtVal φ rs` belongs to the nonprincipal ultrafilter `hyperfilter ℕ`. -/
theorem los_theorem (φ : LFormula ℝ) (rs : ℕ → ℕ → ℝ) :
    Holds (fun v ↦ ofSeq (rs v)) (starFormula φ) ↔
      stmtVal φ rs ∈ (hyperfilter ℕ : Filter ℕ) := by
  change Holds (S := Germ (hyperfilter ℕ : Filter ℕ) ℝ)
      (fun v ↦ ((rs v : ℕ → ℝ) : Germ (hyperfilter ℕ : Filter ℕ) ℝ))
      (starFormula φ : LFormula (Germ (hyperfilter ℕ : Filter ℕ) ℝ)) ↔
    parametricStmtVal ℕ φ rs ∈ (hyperfilter ℕ : Filter ℕ)
  rw [starFormula_eq_ultrapowerFormula]
  exact parametric_los_theorem (hyperfilter ℕ) φ rs

/-- Goldblatt §4.6 (p. 47): **Łoś's Theorem** stated in filter-eventually form for total-term
formulae (`∀ᶠ n in hyperfilter ℕ, Holds (fun v ↦ rs v n) φ`). -/
theorem los_theorem_total {φ : LFormula ℝ} (_hφ : IsTotalFormula φ) (rs : ℕ → ℕ → ℝ) :
    Holds (fun v ↦ ofSeq (rs v)) (starFormula φ) ↔
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), Holds (fun v ↦ rs v n) φ :=
  los_theorem φ rs

/-! ## §4.5 The Transfer Principle, Universal Transfer, and Existential Transfer -/

/-- Definedness of a closed `ℒ_ℝ`-sentence is preserved and reflected by `*-transformation`. -/
theorem isDefinedFormula_starFormula_iff_of_isSentence {φ : LFormula ℝ} (hφ : IsSentence φ) :
    IsDefinedFormula default (starFormula φ) ↔ IsDefinedFormula default φ := by
  let rs : ℕ → ℕ → ℝ := fun _ _ ↦ 0
  have hstar : IsSentence (starFormula φ) := (isSentence_starFormula_iff φ).2 hφ
  rw [isDefinedFormula_of_isSentence hstar default (fun v ↦ ofSeq (rs v))]
  change IsDefinedFormula (S := Germ (hyperfilter ℕ : Filter ℕ) ℝ)
      (fun v ↦ ((rs v : ℕ → ℝ) : Germ (hyperfilter ℕ : Filter ℕ) ℝ))
      (starFormula φ : LFormula (Germ (hyperfilter ℕ : Filter ℕ) ℝ)) ↔ _
  rw [starFormula_eq_ultrapowerFormula,
      isDefinedFormula_ultrapowerFormula_iff (hyperfilter ℕ) rs φ]
  have hconst : (fun n ↦ IsDefinedFormula (fun v ↦ rs v n) φ) =
      fun _ ↦ IsDefinedFormula default φ := by
    ext n
    exact isDefinedFormula_of_isSentence hφ (fun v ↦ rs v n) default
  rw [hconst, eventually_const]

/-- Goldblatt §4.5 (p. 44) & §4.6 (p. 47): **The Transfer Principle** — an `ℒ_ℝ`-sentence `φ`
is true in `ℝ` if and only if its `*-transform` `*φ` is true in `ℝ*`. -/
theorem transfer_principle {φ : LFormula ℝ} (hφ : IsSentence φ) :
    Holds default (starFormula φ) ↔ Holds default φ := by
  let rs : ℕ → ℕ → ℝ := fun _ _ ↦ 0
  have hstar : IsSentence (starFormula φ) := (isSentence_starFormula_iff φ).2 hφ
  rw [holds_of_isSentence hstar default (fun v ↦ ofSeq (rs v)), los_theorem]
  change (∀ᶠ n in (hyperfilter ℕ : Filter ℕ), Holds (fun v ↦ rs v n) φ) ↔ Holds default φ
  have hconst : (fun n ↦ Holds (fun v ↦ rs v n) φ) = fun _ ↦ Holds default φ := by
    ext n
    exact holds_of_isSentence hφ (fun v ↦ rs v n) default
  rw [hconst, eventually_const]

/-- Goldblatt §4.7 (p. 47): **Parametric Transfer Principle** for any inhabited carrier `S` and
ultrafilter `U : Ultrafilter I`. -/
theorem parametric_transfer_principle {I S : Type*} [Inhabited S] (U : Ultrafilter I)
    {φ : LFormula S} (hφ : IsSentence φ) :
    Holds default (ultrapowerFormula U φ) ↔ Holds default φ := by
  let rs : ℕ → I → S := fun _ _ ↦ default
  have hstar : IsSentence (ultrapowerFormula U φ) := by
    rw [IsSentence] at hφ ⊢
    simp [hφ]
  rw [holds_of_isSentence hstar default
      (fun v ↦ ((rs v : I → S) : Germ (U : Filter I) S)),
      parametric_los_theorem]
  change (∀ᶠ idx in (U : Filter I), Holds (fun v ↦ rs v idx) φ) ↔ Holds default φ
  have hconst : (fun idx ↦ Holds (fun v ↦ rs v idx) φ) = fun _ ↦ Holds default φ := by
    ext idx
    exact holds_of_isSentence hφ (fun v ↦ rs v idx) default
  rw [hconst, eventually_const]

/-- Goldblatt §4.5 (p. 45): **Universal Transfer** (general partial-function form) for any formula
`φ` with at most `x` free. -/
theorem universal_transfer {P : Set ℝ} {x : ℕ} {φ : LFormula ℝ}
    (hfree : freeVarsFormula φ ⊆ {x}) :
    (∀ X ∈ starSet P,
      IsDefinedFormula (Function.update default x X) (starFormula φ) →
        Holds (Function.update default x X) (starFormula φ)) ↔
    (∀ r ∈ P,
      IsDefinedFormula (Function.update default x r) φ →
        Holds (Function.update default x r) φ) := by
  have hsent : IsSentence (.forallIn P x φ) := by
    rw [IsSentence, freeVarsFormula, Finset.erase_eq_empty_iff]
    by_cases h : freeVarsFormula φ = ∅
    · exact Or.inl h
    · right
      apply Finset.Subset.antisymm hfree
      rcases Finset.nonempty_iff_ne_empty.2 h with ⟨y, hy⟩
      have hyx : y = x := Finset.mem_singleton.1 (hfree hy)
      subst hyx
      exact Finset.singleton_subset_iff.2 hy
  simpa [starFormula] using transfer_principle hsent

/-- Goldblatt §4.5 (p. 45): **Universal Transfer** for total-term unary formulas. -/
theorem universal_transfer_total {P : Set ℝ} {x : ℕ} {φ : LFormula ℝ}
    (htot : IsTotalFormula φ) (hfree : freeVarsFormula φ ⊆ {x}) :
    (∀ X ∈ starSet P, Holds (Function.update default x X) (starFormula φ)) ↔
      (∀ r ∈ P, Holds (Function.update default x r) φ) := by
  have hstar_tot : IsTotalFormula (starFormula φ) := (isTotalFormula_starFormula_iff φ).2 htot
  have h := universal_transfer (P := P) hfree
  simpa [isDefinedFormula_of_isTotalFormula htot,
    isDefinedFormula_of_isTotalFormula hstar_tot] using h

/-- Goldblatt §4.5 (p. 45): **Binary Universal Transfer** for total-term formulas in two distinct
variables `x ≠ y`. -/
theorem universal_transfer₂_total {P Q : Set ℝ} {x y : ℕ} {φ : LFormula ℝ}
    (hxy : x ≠ y) (htot : IsTotalFormula φ) (hfree : freeVarsFormula φ ⊆ {x, y}) :
    (∀ X ∈ starSet P, ∀ Y ∈ starSet Q,
      Holds (Function.update (Function.update default x X) y Y) (starFormula φ)) ↔
    (∀ r ∈ P, ∀ s ∈ Q,
      Holds (Function.update (Function.update default x r) y s) φ) := by
  have hsent : IsSentence (.forallIn P x (.forallIn Q y φ)) := by
    rw [IsSentence, freeVarsFormula, freeVarsFormula]
    ext z
    simp only [Finset.mem_erase, Finset.notMem_empty, iff_false, not_and]
    intro hzx hzy hzf
    rcases Finset.mem_insert.1 (hfree hzf) with rfl | hzy'
    · exact hzx rfl
    · exact hzy (Finset.mem_singleton.1 hzy')
  have hstar_tot : IsTotalFormula (starFormula φ) := (isTotalFormula_starFormula_iff φ).2 htot
  have htr := transfer_principle hsent
  rw [starFormula, starFormula,
      holds_forallIn_of_total _ _ _ (by exact hstar_tot),
      holds_forallIn_of_total _ _ _ (by exact htot)] at htr
  refine (forall₂_congr fun X _ ↦ ?_).trans
    (htr.trans (forall₂_congr fun r _ ↦ holds_forallIn_of_total _ _ _ htot))
  exact (holds_forallIn_of_total _ _ _ hstar_tot).symm

/-- Goldblatt §4.5 (pp. 45–46): **Existential Transfer** (general partial-function form) for any
formula `φ` with at most `x` free. -/
theorem existential_transfer {P : Set ℝ} {x : ℕ} {φ : LFormula ℝ}
    (hfree : freeVarsFormula φ ⊆ {x}) :
    (∃ X ∈ starSet P,
      IsDefinedFormula (Function.update default x X) (starFormula φ) ∧
        Holds (Function.update default x X) (starFormula φ)) ↔
    (∃ r ∈ P,
      IsDefinedFormula (Function.update default x r) φ ∧
        Holds (Function.update default x r) φ) := by
  have hsent : IsSentence (.existsIn P x φ) := by
    rw [IsSentence, freeVarsFormula, Finset.erase_eq_empty_iff]
    by_cases h : freeVarsFormula φ = ∅
    · exact Or.inl h
    · right
      apply Finset.Subset.antisymm hfree
      rcases Finset.nonempty_iff_ne_empty.2 h with ⟨y, hy⟩
      have hyx : y = x := Finset.mem_singleton.1 (hfree hy)
      subst hyx
      exact Finset.singleton_subset_iff.2 hy
  simpa [starFormula] using transfer_principle hsent

/-- Goldblatt §4.5 (pp. 45–46): **Existential Transfer** for total-term formulas. -/
theorem existential_transfer_total {P : Set ℝ} {x : ℕ} {φ : LFormula ℝ}
    (htot : IsTotalFormula φ) (hfree : freeVarsFormula φ ⊆ {x}) :
    (∃ X ∈ starSet P, Holds (Function.update default x X) (starFormula φ)) ↔
      (∃ r ∈ P, Holds (Function.update default x r) φ) := by
  have hstar_tot : IsTotalFormula (starFormula φ) := (isTotalFormula_starFormula_iff φ).2 htot
  have h := existential_transfer (P := P) hfree
  simpa [isDefinedFormula_of_isTotalFormula htot,
    isDefinedFormula_of_isTotalFormula hstar_tot] using h

/-! ## Term Constructors and Evaluation Simp Lemmas for Concrete Transfer Proofs -/

/-- Total unary function application term `f(τ)`. -/
def LTerm.unary {S : Type*} (f : S → S) (t : LTerm S) : LTerm S :=
  .app (PartialFun.totalUnary f) ![t]

/-- Total binary function application term `g(τ_1, τ_2)`. -/
def LTerm.binary {S : Type*} (g : S → S → S) (t₁ t₂ : LTerm S) : LTerm S :=
  .app (PartialFun.totalBinary g) ![t₁, t₂]

/-- Variable terms are total. -/
@[simp]
theorem isTotalTerm_var {S : Type*} (x : ℕ) : IsTotalTerm (.var x : LTerm S) := trivial

/-- Constant terms are total. -/
@[simp]
theorem isTotalTerm_const {S : Type*} (s : S) : IsTotalTerm (.const s : LTerm S) := trivial

/-- `LTerm.unary f t` is total iff `t` is total. -/
@[simp]
theorem isTotalTerm_unary {S : Type*} (f : S → S) (t : LTerm S) :
    IsTotalTerm (LTerm.unary f t) ↔ IsTotalTerm t := by
  simp [LTerm.unary, IsTotalTerm]

/-- `LTerm.binary g t₁ t₂` is total iff `t₁` and `t₂` are total. -/
@[simp]
theorem isTotalTerm_binary {S : Type*} (g : S → S → S) (t₁ t₂ : LTerm S) :
    IsTotalTerm (LTerm.binary g t₁ t₂) ↔ IsTotalTerm t₁ ∧ IsTotalTerm t₂ := by
  simp [LTerm.binary, IsTotalTerm, Fin.forall_fin_two]

/-- Free variables of `.var x`. -/
@[simp]
theorem freeVarsTerm_var {S : Type*} (x : ℕ) :
    freeVarsTerm (.var x : LTerm S) = {x} := rfl

/-- Free variables of `.const s`. -/
@[simp]
theorem freeVarsTerm_const {S : Type*} (s : S) :
    freeVarsTerm (.const s : LTerm S) = ∅ := rfl

/-- Free variables of `LTerm.unary f t`. -/
@[simp]
theorem freeVarsTerm_unary {S : Type*} (f : S → S) (t : LTerm S) :
    freeVarsTerm (LTerm.unary f t) = freeVarsTerm t := by
  ext z
  simp [LTerm.unary, freeVarsTerm]

/-- Free variables of `LTerm.binary g t₁ t₂`. -/
@[simp]
theorem freeVarsTerm_binary {S : Type*} (g : S → S → S) (t₁ t₂ : LTerm S) :
    freeVarsTerm (LTerm.binary g t₁ t₂) = freeVarsTerm t₁ ∪ freeVarsTerm t₂ := by
  ext z
  simp [LTerm.binary, freeVarsTerm, Fin.exists_fin_two]

/-- Free variables of `LFormula.eq t₁ t₂`. -/
@[simp]
theorem freeVarsFormula_eq {S : Type*} (t₁ t₂ : LTerm S) :
    freeVarsFormula (LFormula.eq t₁ t₂) = freeVarsTerm t₁ ∪ freeVarsTerm t₂ := by
  ext z
  simp [LFormula.eq, freeVarsFormula, Fin.exists_fin_two]

/-- Free variables of `LFormula.lt t₁ t₂`. -/
@[simp]
theorem freeVarsFormula_lt {S : Type*} [LT S] (t₁ t₂ : LTerm S) :
    freeVarsFormula (LFormula.lt t₁ t₂) = freeVarsTerm t₁ ∪ freeVarsTerm t₂ := by
  ext z
  simp [LFormula.lt, freeVarsFormula, Fin.exists_fin_two]

/-- Free variables of `LFormula.le t₁ t₂`. -/
@[simp]
theorem freeVarsFormula_le {S : Type*} [LE S] (t₁ t₂ : LTerm S) :
    freeVarsFormula (LFormula.le t₁ t₂) = freeVarsTerm t₁ ∪ freeVarsTerm t₂ := by
  ext z
  simp [LFormula.le, freeVarsFormula, Fin.exists_fin_two]

/-- Free variables of `LFormula.mem t P`. -/
@[simp]
theorem freeVarsFormula_mem {S : Type*} (t : LTerm S) (P : Set S) :
    freeVarsFormula (LFormula.mem t P) = freeVarsTerm t := by
  ext z
  simp [LFormula.mem, freeVarsFormula]

/-- Totality of `LFormula.eq t₁ t₂`. -/
@[simp]
theorem isTotalFormula_eq {S : Type*} (t₁ t₂ : LTerm S) :
    IsTotalFormula (LFormula.eq t₁ t₂) ↔ IsTotalTerm t₁ ∧ IsTotalTerm t₂ := by
  simp [LFormula.eq, IsTotalFormula, Fin.forall_fin_two]

/-- Totality of `LFormula.lt t₁ t₂`. -/
@[simp]
theorem isTotalFormula_lt {S : Type*} [LT S] (t₁ t₂ : LTerm S) :
    IsTotalFormula (LFormula.lt t₁ t₂) ↔ IsTotalTerm t₁ ∧ IsTotalTerm t₂ := by
  simp [LFormula.lt, IsTotalFormula, Fin.forall_fin_two]

/-- Totality of `LFormula.le t₁ t₂`. -/
@[simp]
theorem isTotalFormula_le {S : Type*} [LE S] (t₁ t₂ : LTerm S) :
    IsTotalFormula (LFormula.le t₁ t₂) ↔ IsTotalTerm t₁ ∧ IsTotalTerm t₂ := by
  simp [LFormula.le, IsTotalFormula, Fin.forall_fin_two]

/-- Totality of `LFormula.mem t P`. -/
@[simp]
theorem isTotalFormula_mem {S : Type*} (t : LTerm S) (P : Set S) :
    IsTotalFormula (LFormula.mem t P) ↔ IsTotalTerm t := by
  simp [LFormula.mem, IsTotalFormula]

/-- Total evaluation of `.var x`. -/
@[simp]
theorem evalTermTotal_var {S : Type*} (env : ℕ → S) (x : ℕ) :
    evalTermTotal env (.var x) = env x := rfl

/-- Total evaluation of `.const s`. -/
@[simp]
theorem evalTermTotal_const {S : Type*} (env : ℕ → S) (s : S) :
    evalTermTotal env (.const s) = s := rfl

/-- Total evaluation of `LTerm.unary f t`. -/
@[simp]
theorem evalTermTotal_unary {S : Type*} (env : ℕ → S) (f : S → S) (t : LTerm S) :
    evalTermTotal env (LTerm.unary f t) = f (evalTermTotal env t) := rfl

/-- Total evaluation of `LTerm.binary g t₁ t₂`. -/
@[simp]
theorem evalTermTotal_binary {S : Type*} (env : ℕ → S) (g : S → S → S) (t₁ t₂ : LTerm S) :
    evalTermTotal env (LTerm.binary g t₁ t₂) =
      g (evalTermTotal env t₁) (evalTermTotal env t₂) := rfl

/-- Total evaluation of `starTerm (.var x)`. -/
@[simp]
theorem evalTermTotal_starTerm_var (env : ℕ → ℝ*) (x : ℕ) :
    evalTermTotal env (starTerm (.var x)) = env x := rfl

/-- Total evaluation of `starTerm (.const r)`. -/
@[simp]
theorem evalTermTotal_starTerm_const (env : ℕ → ℝ*) (r : ℝ) :
    evalTermTotal env (starTerm (.const r)) = (r : ℝ*) := rfl

/-- Total evaluation of `starTerm (LTerm.unary f t)` via `starFun f`. -/
@[simp]
theorem evalTermTotal_starTerm_unary (env : ℕ → ℝ*) (f : ℝ → ℝ) (t : LTerm ℝ) :
    evalTermTotal env (starTerm (LTerm.unary f t)) =
      starFun f (evalTermTotal env (starTerm t)) := by
  simp only [LTerm.unary, starTerm, evalTermTotal, starPartialFunN, PartialFun.totalUnary,
    PartialFun.total]
  rcases ofSeq_surjective (evalTermTotal env (starTerm t)) with ⟨r, hr⟩
  rw [← hr]
  have harg : (fun i : Fin 1 ↦ evalTermTotal env (starTerm (![t] i))) = fun _ ↦ ofSeq r := by
    ext i
    fin_cases i
    simpa using hr.symm
  rw [harg, starFunN_ofSeq, starFun_ofSeq]
  rfl

/-- Total evaluation of `starTerm (LTerm.binary g t₁ t₂)` via `starFun₂ g`. -/
@[simp]
theorem evalTermTotal_starTerm_binary (env : ℕ → ℝ*) (g : ℝ → ℝ → ℝ) (t₁ t₂ : LTerm ℝ) :
    evalTermTotal env (starTerm (LTerm.binary g t₁ t₂)) =
      starFun₂ g (evalTermTotal env (starTerm t₁)) (evalTermTotal env (starTerm t₂)) := by
  simp only [LTerm.binary, starTerm, evalTermTotal, starPartialFunN, PartialFun.totalBinary,
    PartialFun.total]
  rcases ofSeq_surjective (evalTermTotal env (starTerm t₁)) with ⟨r₁, hr₁⟩
  rcases ofSeq_surjective (evalTermTotal env (starTerm t₂)) with ⟨r₂, hr₂⟩
  rw [← hr₁, ← hr₂]
  have harg : (fun i : Fin 2 ↦ evalTermTotal env (starTerm (![t₁, t₂] i))) =
      fun i ↦ ofSeq (![r₁, r₂] i) := by
    ext i
    fin_cases i <;> simp [hr₁, hr₂]
  rw [harg, starFunN_ofSeq, starFun₂_ofSeq]
  rfl

/-- `starFun Neg.neg` agrees with negation on `ℝ*`. -/
@[simp]
theorem starFun_neg_eq (x : ℝ*) : starFun Neg.neg x = -x := by
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  rfl

/-- `starFun₂ (· + ·)` agrees with addition on `ℝ*`. -/
@[simp]
theorem starFun₂_add_eq (x y : ℝ*) : starFun₂ (· + ·) x y = x + y := by
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  rcases ofSeq_surjective y with ⟨s, rfl⟩
  rfl

/-- `starFun₂ (· - ·)` agrees with subtraction on `ℝ*`. -/
@[simp]
theorem starFun₂_sub_eq (x y : ℝ*) : starFun₂ (· - ·) x y = x - y := by
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  rcases ofSeq_surjective y with ⟨s, rfl⟩
  rfl

/-- `starFun₂ (· * ·)` agrees with multiplication on `ℝ*`. -/
@[simp]
theorem starFun₂_mul_eq (x y : ℝ*) : starFun₂ (· * ·) x y = x * y := by
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  rcases ofSeq_surjective y with ⟨s, rfl⟩
  rfl

/-! ## §4.3 Partial-Function Transfer Example: `tan(-x) = -tan(x)` -/

/-- Domain `{x ∈ ℝ | cos x ≠ 0}` of the partial tangent function (Goldblatt §4.3, p. 39). -/
def tanDom : Set ℝ := {x : ℝ | Real.cos x ≠ 0}

/-- Partial unary function `tan` on `ℝ` with domain `tanDom = {x | cos x ≠ 0}`, so `tan(π/2)` is
genuinely undefined in `ℒ_ℝ` (Goldblatt §4.3, p. 39). -/
def tanPartialFun : PartialFun ℝ 1 :=
  PartialFun.unary tanDom Real.tan

/-- Goldblatt §4.3 (p. 39): The closed term `tan(π/2)` is undefined (`evalTerm = none`). -/
theorem tan_pi_div_two_undefined :
    evalTerm default (.app tanPartialFun ![.const (Real.pi / 2)]) = none := by
  rw [evalTerm_app_eq_none]
  right
  refine ⟨fun _ ↦ Real.pi / 2, fun i ↦ by fin_cases i; rfl, ?_⟩
  simp [tanPartialFun, PartialFun.unary, tanDom, Real.cos_pi_div_two]

/-- Open formula `tan(-x) = -tan(x)` in variable `0` (Goldblatt §4.3, p. 41). -/
def tanOddBody : LFormula ℝ :=
  LFormula.eq
    (.app tanPartialFun ![LTerm.unary Neg.neg (.var 0)])
    (LTerm.unary Neg.neg (.app tanPartialFun ![.var 0]))

/-- Sentence `(∀ x ∈ ℝ) [tan(-x) = -tan(x)]` (Goldblatt §4.3, p. 41). -/
def tanOddSentence : LFormula ℝ :=
  .forallIn Set.univ 0 tanOddBody

/-- Goldblatt §4.3 (p. 41): Substituting `π/2` for `x` in `tan(-x) = -tan(x)` produces an
undefined atomic sentence. -/
theorem tanOddBody_undefined_at_pi_div_two :
    ¬ IsDefinedFormula (Function.update default 0 (Real.pi / 2)) tanOddBody := by
  intro hdef
  have harg1 : IsDefinedTerm (Function.update default 0 (Real.pi / 2))
      (LTerm.unary Neg.neg (.app tanPartialFun ![.var 0])) :=
    (allClosedSubtermsDefined_empty_iff _ _).1 (hdef 1)
  apply harg1
  rw [LTerm.unary, evalTerm_app_eq_none]
  left
  refine ⟨0, ?_⟩
  rw [Matrix.cons_val_zero, evalTerm_app_eq_none]
  right
  refine ⟨fun _ ↦ Real.pi / 2, fun i ↦ by fin_cases i; simp, ?_⟩
  simp [tanPartialFun, PartialFun.unary, tanDom, Real.cos_pi_div_two]

/-- Goldblatt §4.3 (p. 41): The universally quantified sentence `(∀ x ∈ ℝ) [tan(-x) = -tan(x)]`
is itself a *defined* sentence (it contains no closed subterms). -/
theorem tanOddSentence_isDefined : IsDefinedFormula default tanOddSentence := by
  intro i
  fin_cases i
  · refine ⟨fun hdisj ↦ ?_, fun j ↦ ?_⟩
    · exfalso
      have hmem : (0 : ℕ) ∈ freeVarsTerm (.app tanPartialFun ![LTerm.unary Neg.neg (.var 0)]) := by
        simp [freeVarsTerm]
      exact Finset.disjoint_left.1 hdisj hmem (Finset.mem_singleton_self 0)
    · fin_cases j
      refine ⟨fun hdisj ↦ ?_, fun k ↦ by fin_cases k; trivial⟩
      exfalso
      have hmem : (0 : ℕ) ∈ freeVarsTerm (LTerm.unary Neg.neg (.var 0 : LTerm ℝ)) := by simp
      exact Finset.disjoint_left.1 hdisj hmem (Finset.mem_singleton_self 0)
  · refine ⟨fun hdisj ↦ ?_, fun j ↦ ?_⟩
    · exfalso
      have hmem : (0 : ℕ) ∈ freeVarsTerm
          (LTerm.unary Neg.neg (.app tanPartialFun ![.var 0])) := by
        simp [freeVarsTerm]
      exact Finset.disjoint_left.1 hdisj hmem (Finset.mem_singleton_self 0)
    · fin_cases j
      refine ⟨fun hdisj ↦ ?_, fun k ↦ by fin_cases k; trivial⟩
      exfalso
      have hmem : (0 : ℕ) ∈ freeVarsTerm (.app tanPartialFun ![.var 0]) := by
        simp [freeVarsTerm]
      exact Finset.disjoint_left.1 hdisj hmem (Finset.mem_singleton_self 0)

/-- `tanOddSentence` has no free variables. -/
theorem tanOddSentence_isSentence : IsSentence tanOddSentence := by
  rw [IsSentence, tanOddSentence, freeVarsFormula]
  ext z
  simp [tanOddBody, freeVarsTerm]

/-- Goldblatt §4.3 (p. 41): `(∀ x ∈ ℝ) [tan(-x) = -tan(x)]` is true in `ℝ`. -/
theorem tanOddSentence_holds : Holds default tanOddSentence := by
  rw [tanOddSentence, holds_forallIn]
  intro s _ hdef
  have hdef0 : IsDefinedTerm (Function.update default 0 s)
      (.app tanPartialFun ![LTerm.unary Neg.neg (.var 0)]) :=
    (allClosedSubtermsDefined_empty_iff _ _).1 (hdef 0)
  have hdef1 : IsDefinedTerm (Function.update default 0 s)
      (LTerm.unary Neg.neg (.app tanPartialFun ![.var 0])) :=
    (allClosedSubtermsDefined_empty_iff _ _).1 (hdef 1)
  rcases Option.ne_none_iff_exists'.1 hdef0 with ⟨val0, hval0⟩
  rcases evalTerm_app_eq_some.1 hval0 with ⟨v0, hv0, _, rfl⟩
  have hv0_eq : v0 0 = -s := by
    have h0 := hv0 0
    simp only [Matrix.cons_val_zero] at h0
    have htot : IsTotalTerm (LTerm.unary Neg.neg (.var 0 : LTerm ℝ)) := by simp
    rw [evalTerm_eq_some_evalTermTotal htot] at h0
    simpa using (Option.some.inj h0).symm
  rcases Option.ne_none_iff_exists'.1 hdef1 with ⟨val1, hval1⟩
  rcases evalTerm_app_eq_some.1 hval1 with ⟨v1, hv1, _, rfl⟩
  have hv1_0 := hv1 0
  simp only [Matrix.cons_val_zero] at hv1_0
  rcases evalTerm_app_eq_some.1 hv1_0 with ⟨u1, hu1, _, hu1_val⟩
  have hu1_eq : u1 0 = s := by
    have := hu1 0
    simp at this
    exact this.symm
  rw [tanOddBody, LFormula.eq, holds_rel]
  refine ⟨![tanPartialFun.toFun v0, (PartialFun.totalUnary Neg.neg).toFun v1],
    Fin.forall_fin_two.2 ⟨hval0, hval1⟩, ?_⟩
  change tanPartialFun.toFun v0 = (PartialFun.totalUnary Neg.neg).toFun v1
  have hl : tanPartialFun.toFun v0 = Real.tan (-s) := by
    simp [tanPartialFun, PartialFun.unary, hv0_eq]
  have hr : (PartialFun.totalUnary Neg.neg).toFun v1 = - Real.tan s := by
    change - (v1 0) = - Real.tan s
    rw [← hu1_val]
    simp [tanPartialFun, PartialFun.unary, hu1_eq]
  rw [hl, hr, Real.tan_neg]

/-- Goldblatt §4.3 (p. 41) & §4.5 (p. 44): By the Transfer Principle, the `*-transform` of
`(∀ x ∈ ℝ) [tan(-x) = -tan(x)]` holds in `ℝ*`. -/
theorem star_tanOddSentence_holds : Holds default (starFormula tanOddSentence) :=
  (transfer_principle tanOddSentence_isSentence).2 tanOddSentence_holds

/-- Unpacked hyperreal partial-function transfer of `tan(-x) = -tan(x)` on `starSet tanDom`:
whenever `x ∈ starSet tanDom` (i.e., `*cos(x) ≠ 0`), `-x ∈ starSet tanDom` and
`*tan(-x) = -*tan(x)`. -/
theorem starPartialFun_tan_neg {x : ℝ*} (hx : x ∈ starSet tanDom) :
    -x ∈ starSet tanDom ∧
      starPartialFun (fun a : tanDom ↦ Real.tan a.1) ⟨-x, by
        rcases ofSeq_surjective x with ⟨r, rfl⟩
        exact hx.mono fun n hn ↦ by simpa [tanDom, Real.cos_neg] using hn⟩ =
        - starPartialFun (fun a : tanDom ↦ Real.tan a.1) ⟨x, hx⟩ := by
  have hneg_mem : -x ∈ starSet tanDom := by
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    exact hx.mono fun n hn ↦ by simpa [tanDom, Real.cos_neg] using hn
  refine ⟨hneg_mem, ?_⟩
  have hdom_x : (fun _ : Fin 1 ↦ x) ∈ (starPartialFunN tanPartialFun).dom := by
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    simpa [starPartialFunN, tanPartialFun, PartialFun.unary] using hx
  have hdom_negx : (fun _ : Fin 1 ↦ -x) ∈ (starPartialFunN tanPartialFun).dom := by
    rcases ofSeq_surjective x with ⟨r, rfl⟩
    change (fun _ : Fin 1 ↦ ofSeq (fun n ↦ -r n)) ∈ starRel tanPartialFun.dom
    rw [starRel_ofSeq]
    exact hneg_mem
  let envX := Function.update (default : ℕ → ℝ*) 0 x
  have hev0 : evalTerm envX (starTerm (.app tanPartialFun ![LTerm.unary Neg.neg (.var 0)])) =
      some ((starPartialFunN tanPartialFun).toFun (fun _ ↦ -x)) := by
    rw [starTerm, evalTerm_app_eq_some]
    refine ⟨fun _ ↦ -x, fun i ↦ ?_, hdom_negx, rfl⟩
    fin_cases i
    change evalTerm envX (starTerm (LTerm.unary Neg.neg (.var 0))) = some (-x)
    have htot : IsTotalTerm (starTerm (LTerm.unary Neg.neg (.var 0 : LTerm ℝ))) := by simp
    rw [evalTerm_eq_some_evalTermTotal htot]
    simp [envX]
  have hev_inner : evalTerm envX (starTerm (.app tanPartialFun ![.var 0])) =
      some ((starPartialFunN tanPartialFun).toFun (fun _ ↦ x)) := by
    rw [starTerm, evalTerm_app_eq_some]
    refine ⟨fun _ ↦ x, fun i ↦ ?_, hdom_x, rfl⟩
    fin_cases i
    simp [envX, starTerm]
  have hev1 : evalTerm envX (starTerm (LTerm.unary Neg.neg (.app tanPartialFun ![.var 0]))) =
      some (- (starPartialFunN tanPartialFun).toFun (fun _ ↦ x)) := by
    rw [LTerm.unary, starTerm, evalTerm_app_eq_some]
    refine ⟨fun _ ↦ (starPartialFunN tanPartialFun).toFun (fun _ ↦ x), fun i ↦ ?_, ?_, ?_⟩
    · fin_cases i
      exact hev_inner
    · simp [starPartialFunN, PartialFun.totalUnary, PartialFun.total]
    · rcases ofSeq_surjective ((starPartialFunN tanPartialFun).toFun (fun _ ↦ x)) with ⟨u, hu⟩
      rw [← hu]
      simp [starPartialFunN, PartialFun.totalUnary, PartialFun.total, starFunN_ofSeq]
      rfl
  have hdefX : IsDefinedFormula envX (starFormula tanOddBody) := by
    intro i
    rw [allClosedSubtermsDefined_empty_iff]
    fin_cases i
    · change IsDefinedTerm envX (starTerm (.app tanPartialFun ![LTerm.unary Neg.neg (.var 0)]))
      rw [IsDefinedTerm, hev0]
      exact Option.some_ne_none _
    · change IsDefinedTerm envX (starTerm (LTerm.unary Neg.neg (.app tanPartialFun ![.var 0])))
      rw [IsDefinedTerm, hev1]
      exact Option.some_ne_none _
  have hholdsX := star_tanOddSentence_holds x (by simp) hdefX
  rw [tanOddBody, starFormula_eq, LFormula.eq, holds_rel] at hholdsX
  rcases hholdsX with ⟨v, hv, hv_eq⟩
  have hv0 : v 0 = (starPartialFunN tanPartialFun).toFun (fun _ ↦ -x) := by
    have := hv 0
    simp only [Matrix.cons_val_zero] at this
    exact Option.some.inj (this.symm.trans hev0)
  have hv1 : v 1 = - (starPartialFunN tanPartialFun).toFun (fun _ ↦ x) := by
    have := hv 1
    simp only [Matrix.cons_val_one] at this
    exact Option.some.inj (this.symm.trans hev1)
  have hmain : (starPartialFunN tanPartialFun).toFun (fun _ ↦ -x) =
      - (starPartialFunN tanPartialFun).toFun (fun _ ↦ x) := by
    have hveq : v 0 = v 1 := hv_eq
    rwa [hv0, hv1] at hveq
  rcases ofSeq_surjective x with ⟨r, rfl⟩
  have hlhs : starPartialFun (fun a : tanDom ↦ Real.tan a.1) ⟨-ofSeq r, hneg_mem⟩ =
      (starPartialFunN tanPartialFun).toFun (fun _ ↦ -ofSeq r) := by
    change ofSeq (fun n ↦ if h : -r n ∈ tanDom then Real.tan (-r n) else 0) =
      starFunN (fun v : Fin 1 → ℝ ↦ Real.tan (v 0)) (fun _ ↦ ofSeq (fun n ↦ -r n))
    rw [starFunN_ofSeq]
    exact Germ.coe_eq.2 (hneg_mem.mono fun n hn ↦ dite_eq_left_of_eq_true (eq_true hn))
  have hrhs : starPartialFun (fun a : tanDom ↦ Real.tan a.1) ⟨ofSeq r, hx⟩ =
      (starPartialFunN tanPartialFun).toFun (fun _ ↦ ofSeq r) := by
    change ofSeq (fun n ↦ if h : r n ∈ tanDom then Real.tan (r n) else 0) =
      starFunN (fun v : Fin 1 → ℝ ↦ Real.tan (v 0)) (fun _ ↦ ofSeq r)
    rw [starFunN_ofSeq]
    exact Germ.coe_eq.2 (hx.mono fun n hn ↦ dite_eq_left_of_eq_true (eq_true hn))
  rw [hlhs, hrhs]
  exact hmain

/-! ## §4.5 Concrete Illustrations: Field Inverses, Intervals, Transcendental Identities, and
Bounded Hypersequences -/

/-- Goldblatt §4.5 (p. 44): Existence of multiplicative inverses in `ℝ*` proved directly via the
Transfer Principle from `(∀ x ∈ ℝ) [x ≠ 0 → (∃ y ∈ ℝ) x · y = 1]`. -/
theorem hyperreal_mul_inv_exists_via_transfer (x : ℝ*) (hx : x ≠ 0) :
    ∃ y : ℝ*, x * y = 1 := by
  let inner : LFormula ℝ := LFormula.eq (LTerm.binary (· * ·) (.var 0) (.var 1)) (.const 1)
  let φ : LFormula ℝ :=
    .imp (.neg (LFormula.eq (.var 0) (.const 0))) (.existsIn Set.univ 1 inner)
  have htot_inner : IsTotalFormula inner := by simp [inner]
  have htot : IsTotalFormula φ := by simp [φ, inner, IsTotalFormula]
  have hfree : freeVarsFormula φ ⊆ {0} := by
    intro z hz
    simp only [φ, inner, freeVarsFormula, freeVarsFormula_eq, freeVarsTerm_var, freeVarsTerm_const,
      freeVarsTerm_binary, Finset.union_empty, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton] at hz
    rcases hz with rfl | ⟨hz1, rfl | rfl⟩
    · exact Finset.mem_singleton_self 0
    · exact Finset.mem_singleton_self 0
    · exact absurd rfl hz1
  have hstd : ∀ r ∈ (Set.univ : Set ℝ), Holds (Function.update default 0 r) φ := by
    intro r _
    rw [holds_imp, holds_neg, holds_existsIn_of_total _ _ _ htot_inner]
    intro hr0
    have hr : r ≠ 0 := by simpa using hr0
    refine ⟨r⁻¹, Set.mem_univ _, ?_⟩
    simp [inner, mul_inv_cancel₀ hr]
  have hhyp := (universal_transfer_total htot hfree).2 hstd x (by simp)
  have hstar_inner : IsTotalFormula (starFormula inner) :=
    (isTotalFormula_starFormula_iff _).2 htot_inner
  dsimp only [φ] at hhyp
  rw [starFormula, holds_imp, starFormula, holds_neg,
      starFormula, holds_existsIn_of_total _ _ _ hstar_inner] at hhyp
  have hx' : ¬ Holds (Function.update default 0 x)
      (starFormula (LFormula.eq (.var 0) (.const 0))) := by
    simpa using hx
  obtain ⟨y, _, hy⟩ := hhyp hx'
  refine ⟨y, ?_⟩
  simpa [inner] using hy

/-- Goldblatt §4.5 (pp. 44–45) & Exercise 4.5.1: Closed interval enlargement
`*[a, b] = {x ∈ ℝ* | a ≤ x ≤ b}` proved via Universal Transfer. -/
theorem mem_starSet_Icc_via_transfer (a b : ℝ) (x : ℝ*) :
    x ∈ starSet (Set.Icc a b) ↔ (a : ℝ*) ≤ x ∧ x ≤ (b : ℝ*) := by
  let φ : LFormula ℝ :=
    .iff (LFormula.mem (.var 0) (Set.Icc a b))
      (.conj (LFormula.le (.const a) (.var 0)) (LFormula.le (.var 0) (.const b)))
  have htot : IsTotalFormula φ := by simp [φ, IsTotalFormula]
  have hfree : freeVarsFormula φ ⊆ {0} := by
    intro z hz
    simp [φ, freeVarsFormula] at hz
    exact Finset.mem_singleton.2 hz
  have hstd : ∀ r ∈ (Set.univ : Set ℝ), Holds (Function.update default 0 r) φ := by
    intro r _
    simp [φ]
  have hhyp := (universal_transfer_total htot hfree).2 hstd x (by simp)
  simp only [φ, starFormula, starFormula_mem, starFormula_le, holds_iff, holds_conj,
    holds_mem_of_total, holds_le_of_total, isTotalTerm_starTerm_iff, isTotalTerm_var,
    isTotalTerm_const, evalTermTotal_starTerm_var, evalTermTotal_starTerm_const,
    Function.update_self] at hhyp
  exact hhyp

/-- Goldblatt §4.5 (p. 45): `(∀ x ∈ ℝ*) sin(π - x) = sin x`, proved via Universal Transfer. -/
theorem starFun_sin_pi_sub (x : ℝ*) :
    starFun Real.sin ((Real.pi : ℝ*) - x) = starFun Real.sin x := by
  let φ : LFormula ℝ :=
    LFormula.eq
      (LTerm.unary Real.sin (LTerm.binary (· - ·) (.const Real.pi) (.var 0)))
      (LTerm.unary Real.sin (.var 0))
  have htot : IsTotalFormula φ := by simp [φ]
  have hfree : freeVarsFormula φ ⊆ {0} := by
    intro z hz
    simp [φ] at hz
    exact Finset.mem_singleton.2 hz
  have hstd : ∀ r ∈ (Set.univ : Set ℝ), Holds (Function.update default 0 r) φ := by
    intro r _
    rw [holds_eq_of_total _ (by simp) (by simp)]
    simp [Real.sin_pi_sub]
  have hhyp := (universal_transfer_total htot hfree).2 hstd x (by simp)
  rw [starFormula_eq, holds_eq_of_total _ (by simp) (by simp)] at hhyp
  simpa using hhyp

/-- Goldblatt §4.5 (p. 45): `(∀ x ∈ ℝ*) cosh x + sinh x = exp x`, proved via Universal Transfer. -/
theorem starFun_cosh_add_sinh (x : ℝ*) :
    starFun Real.cosh x + starFun Real.sinh x = starFun Real.exp x := by
  let φ : LFormula ℝ :=
    LFormula.eq
      (LTerm.binary (· + ·) (LTerm.unary Real.cosh (.var 0)) (LTerm.unary Real.sinh (.var 0)))
      (LTerm.unary Real.exp (.var 0))
  have htot : IsTotalFormula φ := by simp [φ]
  have hfree : freeVarsFormula φ ⊆ {0} := by
    intro z hz
    simp [φ] at hz
    exact Finset.mem_singleton.2 hz
  have hstd : ∀ r ∈ (Set.univ : Set ℝ), Holds (Function.update default 0 r) φ := by
    intro r _
    rw [holds_eq_of_total _ (by simp) (by simp)]
    simp [Real.cosh_add_sinh]
  have hhyp := (universal_transfer_total htot hfree).2 hstd x (by simp)
  rw [starFormula_eq, holds_eq_of_total _ (by simp) (by simp)] at hhyp
  simpa using hhyp

/-- Goldblatt §4.5 (p. 45): `(∀ x, y ∈ (ℝ*)⁺) log(x * y) = log x + log y`, proved via Binary
Universal Transfer. -/
theorem starFun_log_mul (x y : ℝ*) (hx : 0 < x) (hy : 0 < y) :
    starFun Real.log (x * y) = starFun Real.log x + starFun Real.log y := by
  let Ppos : Set ℝ := {r : ℝ | 0 < r}
  let φ : LFormula ℝ :=
    LFormula.eq
      (LTerm.unary Real.log (LTerm.binary (· * ·) (.var 0) (.var 1)))
      (LTerm.binary (· + ·) (LTerm.unary Real.log (.var 0)) (LTerm.unary Real.log (.var 1)))
  have htot : IsTotalFormula φ := by simp [φ]
  have hfree : freeVarsFormula φ ⊆ {0, 1} := by
    intro z hz
    simp [φ] at hz
    rcases hz with rfl | rfl <;> simp
  have hstd : ∀ r ∈ Ppos, ∀ s ∈ Ppos,
      Holds (Function.update (Function.update default 0 r) 1 s) φ := by
    intro r hr s hs
    rw [holds_eq_of_total _ (by simp) (by simp)]
    have hr' : r ≠ 0 := ne_of_gt hr
    have hs' : s ≠ 0 := ne_of_gt hs
    simp [Real.log_mul hr' hs']
  have hxP : x ∈ starSet Ppos := by
    rw [show Ppos = {r : ℝ | 0 < r} from rfl, starSet_pos]
    exact hx
  have hyP : y ∈ starSet Ppos := by
    rw [show Ppos = {r : ℝ | 0 < r} from rfl, starSet_pos]
    exact hy
  have hhyp := (universal_transfer₂_total (by decide : (0 : ℕ) ≠ 1) htot hfree).2
    hstd x hxP y hyP
  rw [starFormula_eq, holds_eq_of_total _ (by simp) (by simp)] at hhyp
  simpa using hhyp

/-- Goldblatt §4.5 (pp. 45–46): **Concrete Existential Transfer for Hypersequences** — a
hypersequence `starSeq s : ℕ* → ℝ*` has a hyperreal upper bound `Y : ℝ*` (`∀ N : ℕ*, |*s(N)| < Y`)
if and only if `s : ℕ → ℝ` has a standard real upper bound `y : ℝ` (`∀ n : ℕ, |s n| < y`). -/
theorem starSeq_bounded_iff_bounded (s : ℕ → ℝ) :
    (∃ Y : ℝ*, ∀ N : ℕ*, |starSeq s N| < Y) ↔ (∃ y : ℝ, ∀ n : ℕ, |s n| < y) := by
  let natSet : Set ℝ := Set.range (Nat.cast : ℕ → ℝ)
  let sExt : ℝ → ℝ := fun r ↦ if h : r ∈ natSet then s h.choose else 0
  have hsExt_nat : ∀ n : ℕ, sExt (n : ℝ) = s n := by
    intro n
    have hn : (n : ℝ) ∈ natSet := ⟨n, rfl⟩
    have heq : sExt (n : ℝ) = s hn.choose := dite_eq_left_of_eq_true (eq_true hn)
    rw [heq, Nat.cast_injective hn.choose_spec]
  have hsExt_hypernat : ∀ N : ℕ*, starFun sExt (Hypernat.toHyperreal N) = starSeq s N := by
    intro N
    refine Germ.inductionOn N fun a ↦ ?_
    change ofSeq (fun k ↦ sExt (a k : ℝ)) = ofSeq (fun k ↦ s (a k))
    simp only [hsExt_nat]
  let body : LFormula ℝ :=
    LFormula.lt (LTerm.unary abs (LTerm.unary sExt (.var 1))) (.var 0)
  let φ : LFormula ℝ := .forallIn natSet 1 body
  have htot_body : IsTotalFormula body := by simp [body]
  have htot : IsTotalFormula φ := htot_body
  have hfree : freeVarsFormula φ ⊆ {0} := by
    intro z hz
    simp only [φ, body, freeVarsFormula, freeVarsFormula_lt, freeVarsTerm_unary,
      freeVarsTerm_var, Finset.mem_erase, Finset.mem_union, Finset.mem_singleton] at hz
    rcases hz with ⟨hz1, rfl | rfl⟩
    · exact absurd rfl hz1
    · exact Finset.mem_singleton_self 0
  have hstar_body : IsTotalFormula (starFormula body) :=
    (isTotalFormula_starFormula_iff body).2 htot_body
  have htr := existential_transfer_total (P := Set.univ) htot hfree
  constructor
  · rintro ⟨Y, hY⟩
    have hex_star : ∃ X ∈ starSet Set.univ, Holds (Function.update default 0 X) (starFormula φ) := by
      refine ⟨Y, by simp, ?_⟩
      rw [starFormula, holds_forallIn_of_total _ _ _ hstar_body]
      intro Xn hXn
      rw [← range_hypernat_toHyperreal] at hXn
      rcases hXn with ⟨N, rfl⟩
      simpa [body, hsExt_hypernat N] using hY N
    obtain ⟨y, _, hy⟩ := htr.1 hex_star
    rw [holds_forallIn_of_total _ _ _ htot_body] at hy
    refine ⟨y, fun n ↦ ?_⟩
    have hyn := hy (n : ℝ) ⟨n, rfl⟩
    simpa [body, hsExt_nat n] using hyn
  · rintro ⟨y, hy⟩
    have hex_std : ∃ r ∈ (Set.univ : Set ℝ), Holds (Function.update default 0 r) φ := by
      refine ⟨y, Set.mem_univ _, ?_⟩
      rw [holds_forallIn_of_total _ _ _ htot_body]
      rintro _ ⟨n, rfl⟩
      simpa [body, hsExt_nat n] using hy n
    obtain ⟨Y, _, hY⟩ := htr.2 hex_std
    rw [starFormula, holds_forallIn_of_total _ _ _ hstar_body] at hY
    refine ⟨Y, fun N ↦ ?_⟩
    have hN : Hypernat.toHyperreal N ∈ starSet natSet := by
      rw [← range_hypernat_toHyperreal]
      exact ⟨N, rfl⟩
    have hYN := hY (Hypernat.toHyperreal N) hN
    simpa [body, hsExt_hypernat N] using hYN

/-- Goldblatt §4.5 (pp. 45–46): Forward direction of boundedness transfer — if `starSeq s` has a
hyperreal bound, then `s` has a standard real bound. -/
theorem bounded_of_starSeq_bounded {s : ℕ → ℝ}
    (h : ∃ Y : ℝ*, ∀ N : ℕ*, |starSeq s N| < Y) :
    ∃ y : ℝ, ∀ n : ℕ, |s n| < y :=
  (starSeq_bounded_iff_bounded s).1 h

/-- Goldblatt §4.5 (pp. 45–46): If the extended hypersequence `*s : ℕ* → ℝ*` never takes unlimited
values (`∀ N : ℕ*, ∃ m : ℕ, |*s(N)| < m`), then `|*s(N)| < ω` for all `N : ℕ*`, and hence by
Existential Transfer `s` is bounded in `ℝ`. -/
theorem bounded_of_starSeq_always_limited {s : ℕ → ℝ}
    (hlim : ∀ N : ℕ*, ∃ m : ℕ, |starSeq s N| < (m : ℝ*)) :
    ∃ y : ℝ, ∀ n : ℕ, |s n| < y := by
  apply bounded_of_starSeq_bounded
  refine ⟨Hyperreal.omega, fun N ↦ ?_⟩
  obtain ⟨m, hm⟩ := hlim N
  exact hm.trans (omega_unlimited_and_nonstandard.1 (m : ℝ))

/-- Goldblatt Exercise 4.5.1 (p. 46) / Exercise 3.10(2a): `A ⊆ B ↔ *A ⊆ *B` proved via Transfer. -/
theorem starSet_subset_iff_via_transfer (A B : Set ℝ) :
    starSet A ⊆ starSet B ↔ A ⊆ B := by
  let φ : LFormula ℝ := .forallIn A 0 (LFormula.mem (.var 0) B)
  have hsent : IsSentence φ := by
    rw [IsSentence, freeVarsFormula, freeVarsFormula_mem, freeVarsTerm_var]
    simp
  have htot : IsTotalFormula (LFormula.mem (.var 0 : LTerm ℝ) B) := by simp
  have hstar_tot : IsTotalFormula (starFormula (LFormula.mem (.var 0 : LTerm ℝ) B)) :=
    (isTotalFormula_starFormula_iff _).2 htot
  have htr := transfer_principle hsent
  rw [starFormula, holds_forallIn_of_total _ _ _ hstar_tot,
      holds_forallIn_of_total _ _ _ htot] at htr
  refine (forall₂_congr fun x _ ↦ ?_).trans
    (htr.trans (forall₂_congr fun r _ ↦ ?_))
  · simp
  · simp

/-- Goldblatt Exercise 4.5.1 (p. 46) / Exercise 3.10(8): `*(ℝ⁺) = (ℝ*)⁺` proved via Transfer. -/
theorem mem_starSet_pos_via_transfer (x : ℝ*) :
    x ∈ starSet {r : ℝ | 0 < r} ↔ 0 < x := by
  let Ppos : Set ℝ := {r : ℝ | 0 < r}
  let φ : LFormula ℝ := .iff (LFormula.mem (.var 0) Ppos) (LFormula.lt (.const 0) (.var 0))
  have htot : IsTotalFormula φ := by simp [φ, IsTotalFormula]
  have hfree : freeVarsFormula φ ⊆ {0} := by
    intro z hz
    simp [φ, freeVarsFormula] at hz
    exact Finset.mem_singleton.2 hz
  have hstd : ∀ r ∈ (Set.univ : Set ℝ), Holds (Function.update default 0 r) φ := by
    intro r _
    simp [φ, Ppos]
  have hhyp := (universal_transfer_total htot hfree).2 hstd x (by simp)
  simpa [φ, Ppos, starFormula] using hhyp

/-! ## §4.1 Concrete Transfer Examples (1)–(6) and Exercise 4.1.1 -/

/-- Goldblatt §4.1 Example 1 (pp. 35–36) & Exercise 4.1.1: **Eudoxus–Archimedes Principle in `ℝ*`**
— for every hyperreal `x : ℝ*`, there exists a hypernatural `N : ℕ*` with `x < N`, proved via
Universal Transfer from `∀ x ∈ ℝ, ∃ m ∈ ℕ, x < m`. -/
theorem eudoxus_archimedes_hyperreal (x : ℝ*) :
    ∃ N : ℕ*, x < Hypernat.toHyperreal N := by
  let natSet : Set ℝ := Set.range (Nat.cast : ℕ → ℝ)
  let body : LFormula ℝ := LFormula.lt (.var 0) (.var 1)
  let φ : LFormula ℝ := .existsIn natSet 1 body
  have htot_body : IsTotalFormula body := by simp [body]
  have htot : IsTotalFormula φ := htot_body
  have hfree : freeVarsFormula φ ⊆ {0} := by
    intro z hz
    simp only [φ, body, freeVarsFormula, freeVarsFormula_lt, freeVarsTerm_var,
      Finset.mem_erase, Finset.mem_union, Finset.mem_singleton] at hz
    rcases hz with ⟨hz1, rfl | rfl⟩
    · exact Finset.mem_singleton_self 0
    · exact absurd rfl hz1
  have hstd : ∀ r ∈ (Set.univ : Set ℝ), Holds (Function.update default 0 r) φ := by
    intro r _
    rw [holds_existsIn_of_total _ _ _ htot_body]
    obtain ⟨m, hm⟩ := exists_nat_gt r
    refine ⟨(m : ℝ), ⟨m, rfl⟩, ?_⟩
    simpa [body] using hm
  have hstar_body : IsTotalFormula (starFormula body) :=
    (isTotalFormula_starFormula_iff body).2 htot_body
  have hhyp := (universal_transfer_total htot hfree).2 hstd x (by simp)
  rw [starFormula, holds_existsIn_of_total _ _ _ hstar_body] at hhyp
  obtain ⟨Y, hYnat, hYlt⟩ := hhyp
  rw [← range_hypernat_toHyperreal] at hYnat
  rcases hYnat with ⟨N, rfl⟩
  exact ⟨N, by simpa [body] using hYlt⟩

/-- Goldblatt §4.1 Example 1 (p. 36): Without replacing `ℕ` by `*ℕ`, the statement
`∀ x ∈ ℝ*, ∃ n ∈ ℕ, x < n` is **false** (witnessed by `ω = [(0, 1, 2, …)]`). -/
theorem not_archimedean_standard_nat_in_hyperreal :
    ¬ ∀ x : ℝ*, ∃ n : ℕ, x < (n : ℝ*) := by
  intro h
  obtain ⟨n, hn⟩ := h Hyperreal.omega
  exact lt_asymm hn (omega_unlimited_and_nonstandard.1 (n : ℝ))

/-- Goldblatt §4.1 Example 2 (p. 36) & Exercise 4.1.1: **Density of `ℚ*` in `ℝ*`** — between any
two hyperreals `x < y` lies a hyperrational `q : ℚ*`, proved via Binary Universal Transfer from
`∀ x, y ∈ ℝ, x < y → ∃ q ∈ ℚ, x < q ∧ q < y`. -/
theorem dense_hyperrat_in_hyperreal (x y : ℝ*) (hxy : x < y) :
    ∃ q : ℚ*, x < Hyperrat.toHyperreal q ∧ Hyperrat.toHyperreal q < y := by
  let ratSet : Set ℝ := Set.range (Rat.cast : ℚ → ℝ)
  let inner : LFormula ℝ := .conj (LFormula.lt (.var 0) (.var 2)) (LFormula.lt (.var 2) (.var 1))
  let φ : LFormula ℝ := .imp (LFormula.lt (.var 0) (.var 1)) (.existsIn ratSet 2 inner)
  have htot_inner : IsTotalFormula inner := by simp [inner, IsTotalFormula]
  have htot : IsTotalFormula φ := by simp [φ, inner, IsTotalFormula]
  have hfree : freeVarsFormula φ ⊆ {0, 1} := by
    intro z hz
    simp only [φ, inner, freeVarsFormula, freeVarsFormula_lt, freeVarsTerm_var,
      Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at hz
    rcases hz with (rfl | rfl) | ⟨hz2, (rfl | rfl) | (rfl | rfl)⟩
    · simp
    · simp
    · simp
    · exact absurd rfl hz2
    · exact absurd rfl hz2
    · simp
  have hstd : ∀ r ∈ (Set.univ : Set ℝ), ∀ s ∈ (Set.univ : Set ℝ),
      Holds (Function.update (Function.update default 0 r) 1 s) φ := by
    intro r _ s _
    rw [holds_imp, holds_existsIn_of_total _ _ _ htot_inner]
    intro hrs
    have hrs' : r < s := by simpa using hrs
    obtain ⟨q, hqr, hqs⟩ := exists_rat_btwn hrs'
    refine ⟨(q : ℝ), ⟨q, rfl⟩, ?_⟩
    simp only [inner, holds_conj]
    exact ⟨by simpa using hqr, by simpa using hqs⟩
  have hstar_inner : IsTotalFormula (starFormula inner) :=
    (isTotalFormula_starFormula_iff inner).2 htot_inner
  have hhyp := (universal_transfer₂_total (by decide : (0 : ℕ) ≠ 1) htot hfree).2
    hstd x (by simp) y (by simp)
  rw [starFormula, starFormula_lt, holds_imp,
      starFormula, holds_existsIn_of_total _ _ _ hstar_inner] at hhyp
  have hxy' : Holds (Function.update (Function.update default 0 x) 1 y)
      (LFormula.lt (starTerm (.var 0)) (starTerm (.var 1))) := by
    simpa using hxy
  obtain ⟨Qval, hQrat, hQbtwn⟩ := hhyp hxy'
  rw [← range_hyperrat_toHyperreal] at hQrat
  rcases hQrat with ⟨q, rfl⟩
  simp only [inner, starFormula, starFormula_lt, holds_conj] at hQbtwn
  exact ⟨q, by simpa using hQbtwn.1, by simpa using hQbtwn.2⟩

/-- Helper building the finite disjunction `x_0 = r_1 ∨ … ∨ x_0 = r_k` in `LFormula ℝ` for
Goldblatt §4.1 Example 3 (p. 36). -/
def finDisjEqVarZero : List ℝ → LFormula ℝ
  | [] => .neg (LFormula.eq (.var 0) (.var 0))
  | r :: rs => .disj (LFormula.eq (.var 0) (.const r)) (finDisjEqVarZero rs)

/-- `finDisjEqVarZero L` is a total formula for every finite list `L : List ℝ`. -/
theorem isTotalFormula_finDisjEqVarZero (L : List ℝ) :
    IsTotalFormula (finDisjEqVarZero L) := by
  induction L with
  | nil => simp [finDisjEqVarZero, IsTotalFormula]
  | cons _ _ ih => simp [finDisjEqVarZero, IsTotalFormula, ih]

/-- The free variables of `finDisjEqVarZero L` are contained in `{0}`. -/
theorem freeVarsFormula_finDisjEqVarZero_subset (L : List ℝ) :
    freeVarsFormula (finDisjEqVarZero L) ⊆ {0} := by
  induction L with
  | nil => simp [finDisjEqVarZero, freeVarsFormula]
  | cons r rs ih =>
      intro z hz
      simp only [finDisjEqVarZero, freeVarsFormula, freeVarsFormula_eq, freeVarsTerm_var,
        freeVarsTerm_const, Finset.union_empty, Finset.mem_union] at hz
      rcases hz with h0 | hrs
      · exact h0
      · exact ih hrs

/-- Standard satisfaction of `finDisjEqVarZero L` characterizes membership `env 0 ∈ L`. -/
theorem holds_finDisjEqVarZero_iff (env : ℕ → ℝ) (L : List ℝ) :
    Holds env (finDisjEqVarZero L) ↔ env 0 ∈ L := by
  induction L with
  | nil => simp [finDisjEqVarZero]
  | cons r rs ih => simp [finDisjEqVarZero, ih]

/-- Hyperreal satisfaction of `starFormula (finDisjEqVarZero L)` characterizes equality with a
standard real from `L`. -/
theorem holds_starFormula_finDisjEqVarZero_iff (env : ℕ → ℝ*) (L : List ℝ) :
    Holds env (starFormula (finDisjEqVarZero L)) ↔ ∃ r ∈ L, env 0 = (r : ℝ*) := by
  induction L with
  | nil => simp [finDisjEqVarZero, starFormula]
  | cons r rs ih => simp [finDisjEqVarZero, starFormula, ih, exists_eq_or_imp]

/-- Goldblatt §4.1 Example 3 (p. 36) & Exercise 4.1.1: **Finite Subsets via Transfer** — for any
finite subset `A = {r_1, …, r_k} ⊆ ℝ`, transferring `∀ x ∈ A (x = r_1 ∨ … ∨ x = r_k)` proves
that every member of `*A` is a standard element of `A`. -/
theorem mem_starSet_finite_via_transfer {A : Set ℝ} (hA : A.Finite) (x : ℝ*) :
    x ∈ starSet A ↔ ∃ r ∈ A, x = (r : ℝ*) := by
  let L : List ℝ := hA.toFinset.toList
  have hmemL : ∀ r : ℝ, r ∈ L ↔ r ∈ A := by
    intro r
    simp [L]
  have hstd : ∀ r ∈ A, Holds (Function.update default 0 r) (finDisjEqVarZero L) := by
    intro r hr
    rw [holds_finDisjEqVarZero_iff]
    simpa [hmemL] using hr
  have htr := (universal_transfer_total (P := A)
    (isTotalFormula_finDisjEqVarZero L) (freeVarsFormula_finDisjEqVarZero_subset L)).2 hstd
  constructor
  · intro hx
    have hh := htr x hx
    rw [holds_starFormula_finDisjEqVarZero_iff] at hh
    rcases hh with ⟨r, hrL, rfl⟩
    exact ⟨r, (hmemL r).1 hrL, rfl⟩
  · rintro ⟨r, hrA, rfl⟩
    exact coe_mem_starSet.2 hrA

/-- Goldblatt §4.1 Example 4 (pp. 36–37) & Exercise 4.1.1: **Finitary Set Union via Transfer** —
transferring `∀ x ∈ ℝ (x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B)` proves `*(A ∪ B) = *A ∪ *B`. -/
theorem mem_starSet_union_via_transfer (A B : Set ℝ) (x : ℝ*) :
    x ∈ starSet (A ∪ B) ↔ x ∈ starSet A ∨ x ∈ starSet B := by
  let φ : LFormula ℝ :=
    .iff (LFormula.mem (.var 0) (A ∪ B))
      (.disj (LFormula.mem (.var 0) A) (LFormula.mem (.var 0) B))
  have htot : IsTotalFormula φ := by simp [φ, IsTotalFormula]
  have hfree : freeVarsFormula φ ⊆ {0} := by
    intro z hz
    simp [φ, freeVarsFormula] at hz
    exact Finset.mem_singleton.2 hz
  have hstd : ∀ r ∈ (Set.univ : Set ℝ), Holds (Function.update default 0 r) φ := by
    intro r _
    simp [φ]
  have hhyp := (universal_transfer_total htot hfree).2 hstd x (by simp)
  simp only [φ, starFormula, starFormula_mem, holds_iff, holds_disj, holds_mem_of_total,
    isTotalTerm_starTerm_iff, isTotalTerm_var, evalTermTotal_starTerm_var,
    Function.update_self] at hhyp
  exact hhyp

/-- Goldblatt §4.1 Example 5 (p. 37) & Exercise 4.1.1: **Discreteness of `ℕ*`** — no hypernatural
occurs strictly between `n` and `n + 1` for any standard `n : ℕ`, proved via Universal Transfer. -/
theorem hypernat_discrete_between_nat (N : ℕ*) (n : ℕ)
    (h : (n : ℕ*) ≤ N ∧ N ≤ (n + 1 : ℕ*)) :
    N = (n : ℕ*) ∨ N = (n + 1 : ℕ*) := by
  let natSet : Set ℝ := Set.range (Nat.cast : ℕ → ℝ)
  let φ : LFormula ℝ :=
    .imp (.conj (LFormula.le (.const (n : ℝ)) (.var 0))
                (LFormula.le (.var 0) (.const ((n + 1 : ℕ) : ℝ))))
         (.disj (LFormula.eq (.var 0) (.const (n : ℝ)))
                (LFormula.eq (.var 0) (.const ((n + 1 : ℕ) : ℝ))))
  have htot : IsTotalFormula φ := by simp [φ, IsTotalFormula]
  have hfree : freeVarsFormula φ ⊆ {0} := by
    intro z hz
    simp [φ, freeVarsFormula] at hz
    exact Finset.mem_singleton.2 hz
  have hstd : ∀ r ∈ natSet, Holds (Function.update default 0 r) φ := by
    rintro _ ⟨m, rfl⟩
    simp only [φ, holds_imp, holds_conj, holds_disj, holds_le_of_total, holds_eq_of_total,
      isTotalTerm_const, isTotalTerm_var, evalTermTotal_var, evalTermTotal_const,
      Function.update_self, Nat.cast_le, Nat.cast_inj]
    omega
  have hNmem : Hypernat.toHyperreal N ∈ starSet natSet := by
    rw [← range_hypernat_toHyperreal]
    exact ⟨N, rfl⟩
  have hhyp := (universal_transfer_total htot hfree).2 hstd (Hypernat.toHyperreal N) hNmem
  simp only [φ, starFormula, starFormula_le, starFormula_eq, holds_imp, holds_conj, holds_disj,
    holds_le_of_total, holds_eq_of_total, isTotalTerm_starTerm_iff, isTotalTerm_const,
    isTotalTerm_var, evalTermTotal_starTerm_var, evalTermTotal_starTerm_const,
    Function.update_self] at hhyp
  have hcast_n : ((n : ℝ) : ℝ*) = Hypernat.toHyperreal (n : ℕ*) := rfl
  have hcast_n1 : (((n + 1 : ℕ) : ℝ) : ℝ*) = Hypernat.toHyperreal (n + 1 : ℕ*) := by
    have h1 : (((n + 1 : ℕ) : ℝ) : ℝ*) = ((n + 1 : ℕ) : ℝ*) := rfl
    have h2 : ((n + 1 : ℕ) : ℕ*) = (n + 1 : ℕ*) := by simp
    rw [h1, ← Hypernat.toHyperreal_natCast (n + 1), h2]
  rw [hcast_n, hcast_n1, Hypernat.toHyperreal_le_iff, Hypernat.toHyperreal_le_iff] at hhyp
  rcases hhyp h with hleft | hright
  · exact Or.inl (Hypernat.toHyperreal_injective hleft)
  · exact Or.inr (Hypernat.toHyperreal_injective hright)

/-- Goldblatt §4.1 Example 5 (p. 37) & Exercise 4.1.1: Every nonzero hypernatural satisfies
`1 ≤ N`, proved via Universal Transfer. -/
theorem hypernat_one_le_of_ne_zero (N : ℕ*) (hN : N ≠ 0) : (1 : ℕ*) ≤ N := by
  let natSet : Set ℝ := Set.range (Nat.cast : ℕ → ℝ)
  let φ : LFormula ℝ :=
    .imp (.neg (LFormula.eq (.var 0) (.const 0))) (LFormula.le (.const 1) (.var 0))
  have htot : IsTotalFormula φ := by simp [φ, IsTotalFormula]
  have hfree : freeVarsFormula φ ⊆ {0} := by
    intro z hz
    simp [φ, freeVarsFormula] at hz
    exact Finset.mem_singleton.2 hz
  have hstd : ∀ r ∈ natSet, Holds (Function.update default 0 r) φ := by
    rintro _ ⟨m, rfl⟩
    simp only [φ, holds_imp, holds_neg, holds_eq_of_total, holds_le_of_total,
      isTotalTerm_var, isTotalTerm_const, evalTermTotal_var, evalTermTotal_const,
      Function.update_self]
    intro hm0
    have hm : m ≠ 0 := fun h0 ↦ hm0 (by simp [h0])
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hm
  have hNmem : Hypernat.toHyperreal N ∈ starSet natSet := by
    rw [← range_hypernat_toHyperreal]
    exact ⟨N, rfl⟩
  have hhyp := (universal_transfer_total htot hfree).2 hstd (Hypernat.toHyperreal N) hNmem
  simp only [φ, starFormula, starFormula_eq, starFormula_le, holds_imp, holds_neg,
    holds_eq_of_total, holds_le_of_total, isTotalTerm_starTerm_iff, isTotalTerm_var,
    isTotalTerm_const, evalTermTotal_starTerm_var, evalTermTotal_starTerm_const,
    Function.update_self] at hhyp
  have hzero : ((0 : ℝ) : ℝ*) = Hypernat.toHyperreal (0 : ℕ*) := by
    simpa using (Hypernat.toHyperreal_natCast 0).symm
  have hone : ((1 : ℝ) : ℝ*) = Hypernat.toHyperreal (1 : ℕ*) := by
    simpa using (Hypernat.toHyperreal_natCast 1).symm
  have hN0 : Hypernat.toHyperreal N ≠ ((0 : ℝ) : ℝ*) := by
    rw [hzero]
    exact fun h0 ↦ hN (Hypernat.toHyperreal_injective h0)
  have h1 := hhyp hN0
  rw [hone, Hypernat.toHyperreal_le_iff] at h1
  exact h1

/-- Goldblatt §4.1 Example 5 (p. 37): Any nonstandard hypernatural (`∀ n : ℕ, N ≠ n`) exceeds
every standard natural number, deduced directly from `hypernat_one_le_of_ne_zero` and
`hypernat_discrete_between_nat`. -/
theorem hypernat_gt_all_nat_of_nonstandard {N : ℕ*} (hnonstd : ∀ n : ℕ, N ≠ (n : ℕ*)) (n : ℕ) :
    (n : ℕ*) < N := by
  induction n with
  | zero =>
      have h1 : (1 : ℕ*) ≤ N := hypernat_one_le_of_ne_zero N (by simpa using hnonstd 0)
      have h01 : ((0 : ℕ) : ℕ*) < (1 : ℕ*) := by
        rw [← Hypernat.toHyperreal_lt_iff]
        have : Hypernat.toHyperreal (1 : ℕ*) = (1 : ℝ*) := by
          simpa using Hypernat.toHyperreal_natCast 1
        rw [Hypernat.toHyperreal_natCast 0, this]
        norm_num
      exact lt_of_lt_of_le h01 h1
  | succ n ih =>
      have hle_n : (n : ℕ*) ≤ N := le_of_lt ih
      rcases lt_or_ge (Hypernat.toHyperreal (n + 1 : ℕ*)) (Hypernat.toHyperreal N) with hlt | hge
      · have hcast : ((n + 1 : ℕ) : ℕ*) = (n + 1 : ℕ*) := by simp
        rw [hcast]
        exact Hypernat.toHyperreal_lt_iff.1 hlt
      · exfalso
        have hN_le : N ≤ (n + 1 : ℕ*) := Hypernat.toHyperreal_le_iff.1 hge
        rcases hypernat_discrete_between_nat N n ⟨hle_n, hN_le⟩ with rfl | heq
        · exact hnonstd n rfl
        · have hcast : ((n + 1 : ℕ) : ℕ*) = (n + 1 : ℕ*) := by simp
          exact hnonstd (n + 1) (heq.trans hcast.symm)

/-- Goldblatt §4.1 Example 6 (p. 37): **Unbounded Sets of Reals** — the enlargement `*A` of a
subset `A ⊆ ℝ` contains a positive unlimited member (`∀ r : ℝ, r < x`) if and only if `A` is
unbounded above in `ℝ` (`∀ r : ℝ, ∃ a ∈ A, r < a`), with the forward direction proved via
Existential Transfer. -/
theorem exists_unlimited_mem_starSet_iff_unbounded (A : Set ℝ) :
    (∃ x ∈ starSet A, ∀ r : ℝ, (r : ℝ*) < x) ↔ ∀ r : ℝ, ∃ a ∈ A, r < a := by
  constructor
  · rintro ⟨x, hxA, hxUnlim⟩ r
    let φ : LFormula ℝ := LFormula.lt (.const r) (.var 0)
    have htot : IsTotalFormula φ := by simp [φ]
    have hfree : freeVarsFormula φ ⊆ {0} := by
      intro z hz
      simp [φ] at hz
      exact Finset.mem_singleton.2 hz
    have hex_star : ∃ X ∈ starSet A, Holds (Function.update default 0 X) (starFormula φ) :=
      ⟨x, hxA, by simpa [φ] using hxUnlim r⟩
    obtain ⟨a, haA, haLt⟩ := (existential_transfer_total htot hfree).1 hex_star
    exact ⟨a, haA, by simpa [φ] using haLt⟩
  · intro hunb
    choose a haA haGt using fun n : ℕ ↦ hunb (n : ℝ)
    refine ⟨ofSeq a, ofSeq_mem_starSet.2 (Eventually.of_forall haA), ?_⟩
    have htend : Tendsto a atTop atTop :=
      tendsto_atTop_mono (fun n ↦ (haGt n).le) tendsto_natCast_atTop_atTop
    exact ofSeq_unlimited_of_tendsto_atTop htend

/-! ## §4.7 Nonstandard Complex Numbers Illustration -/

/-- Goldblatt §4.7 (p. 47): The nonstandard complex numbers `ℂ*` as the ultrapower of `ℂ` modulo
`hyperfilter ℕ`. -/
abbrev Hypercomplex : Type := Germ (hyperfilter ℕ : Filter ℕ) ℂ

/-- `Hypercomplex` inherits a `Field` structure as an ultrapower of `ℂ`. -/
instance instFieldHypercomplex : Field Hypercomplex := inferInstance

/-- Goldblatt §4.7 (p. 47): Transfer Principle specialized to the language `ℒ_ℂ` of the complex
numbers and its ultrapower `Hypercomplex`. -/
theorem complex_transfer_principle {φ : LFormula ℂ} (hφ : IsSentence φ) :
    Holds default (ultrapowerFormula (hyperfilter ℕ) φ) ↔ Holds default φ :=
  parametric_transfer_principle (hyperfilter ℕ) hφ

end Goldblatt.Ch04
end
