import LecturesOnTheHyperreals.Ch12_InternalFunctions
import Mathlib.Data.Set.Card

/-!
# Chapter 13: Universes and Frameworks

Complete formalization of Robert Goldblatt, *Lectures on the Hyperreals: An Introduction to
Nonstandard Analysis* (GTM 188), Chapter 13: *Universes and Frameworks* (pp. 157–182):

* **§13.1–13.3 Entities, Kuratowski Pairs, Tuples, Relations, and Functions** (pp. 158–161):
  - Cumulative superstructure stages `RawStage X n`, extensional equivalence `RawEquiv`, and the
    quotient superstructure `Entity X : Type u` over any base type `X : Type u` of individuals.
  - Individuals `Entity.atom` (rank `0`, empty extension, distinct from `∅`), sets `Entity.IsSet`,
    set extensionality (`Entity.set_ext`), bounded-rank comprehension (`Entity.setOfBounded`),
    `∅`, `{a}`, `{a, b}`, `∪`, `∩`, `\`, `𝒫(A)`, `𝒫_F(A)`, `⋃ Y`, `⋂ Y`.
  - Kuratowski ordered pairs `(a, b) = {{a}, {a, b}}` (`Entity.kpair`), iterated `m`-tuples
    (`Entity.ktuple`) and indexed `m`-tuples (`Entity.indexedTuple`), **Exercise 13.3.1(i)–(ii)**,
    Cartesian products `A × B` (`Entity.prod`) and `A₁ × ⋯ × A_m` (`Entity.prodTuple`), binary
    relations (`dom`, `ran`, `R⁻¹`, `R''(C)`, `R⁻¹(D)`, `R ∘ S`), set-theoretic functions,
    function spaces `B^A` (`Entity.funSpace`), and indexed products `∏_{i ∈ I} A_i` (`Entity.piSpace`).
* **§13.4–13.5 Transitivity, Strong Transitivity, and Universes** (pp. 161–164):
  - Transitive sets (`Entity.IsTransitiveSet`), strongly transitive collections
    (`IsStronglyTransitive`), abstract universes (`IsUniverse`), universes over `X`
    (`IsUniverseOver`), and every closure law of §13.5 (pairs, singletons, finite sets, subsets,
    `∅`, finite and bounded indexed unions, arbitrary nonempty intersections, Kuratowski pairs,
    finitary relations, `dom R` via strong transitivity, `ran R`, `R''(C)`, `R⁻¹`, `R ∘ S`,
    function graphs, images, preimages, `B^A`, and `∏_{i ∈ I} A_i`).
* **§13.6 Superstructures `𝕌_n(X)` and `𝕌(X)`** (pp. 164–166):
  - Cumulative stages `VStage X n` and stage entities `vStageEntity X n`, rank `Entity.rank`,
    Properties (1)–(6) of §13.6, **Exercise 13.6.1** (showing `𝕌(X)` is the smallest universe
    containing `X`, plus functoriality `X ↪ Y ⇒ 𝕌(X) ↪ 𝕌(Y)`), and rank bounds for functions,
    topologies (`𝕌_2` / `𝕌_3`), measures (`𝕌_4` / `𝕌_5`), metrics (`𝕌_5` / `𝕌_6`), and Riemann
    integrals (`𝕌_6`).
* **§13.7–13.8 Language `ℒ_𝕌`, `Δ₀` Formulae, Nonstandard Frameworks, and Ultrapower Models**
  (pp. 166–170):
  - Terms `UTerm X` (variables, constants, tuples, function applications), partial evaluation
    `evalUTerm`, bounded-quantifier (`Δ₀`) formulae `UFormula X`, satisfaction `Holds`,
    `*-transforms`, `Framework X Y`, preservation laws (**Exercise 13.8.1** & **Exercise 13.8.2**),
    and the concrete **Ultrapower Superstructure Framework** `ultrapowerFramework U` (proved via
    bounded-rank Zakon collapse and Łoś's Theorem) specialized to `hyperrealFramework`.
* **§13.9–13.12 Standard, Internal, and External Entities, and Transformed Power Sets**
  (pp. 170–175):
  - Standard entities (`IsStandard`), external image `im A` (`sigmaImage`), **Theorem 13.9.2**,
    **Exercise 13.9.1** (standard open intervals in `*Int`), **Exercise 13.9.3** (standard sets
    determined by standard members), internal/external entities (`IsInternalEntity`,
    `IsExternalEntity`), **Theorem 13.10.1** (strong transitivity of `*𝕌`), closure properties of
    internal sets (**§13.11 & Exercise 13.11.1**), and **Theorem 13.12.1** (`*𝒫(A)` = internal
    subsets of `*A`).
* **§13.13–13.16 Internal Principles, External Images, and Comprehension** (pp. 176–178):
  - **Exercises 13.13(1)–(3)** (internal least number principle, internal induction, internal
    order-completeness, characteristic functions, and `*(B^A)` = internal functions `*A → *B`),
    **Theorem 13.14.1** (`im A` is external for infinite `A`), **Exercises 13.14.2–13.14.3**,
    **§13.15 Internal Set Definition Principle**, and **§13.16 Internal Function Definition
    Principle**.
* **§13.17–13.20 Hyperfiniteness, Internal Cardinality, and Hyperfinite Summation** (pp. 178–181):
  - Hyperfinite sets `*𝒫_F(A)`, **Theorem 13.17.1** (characterization via internal bijections with
    `{1, …, n}`), internal cardinality `|B|`, **Exercises 13.18(1)–(6)** (including Pigeonhole
    Principle and `|𝒫_I(A)| = 2^{|A|}`), and **§13.19–13.20** hyperfinite summation with
    **Exercises 13.20(1)–(2)**.
* **§13.21 Unification Bridges to Chapters 11 and 12 (`hyperrealFramework`)**:
  - Exact equivalences connecting `Goldblatt.IsInternal` (`isInternal_iff_mkAtomSet_mem_star_powerset`),
    `Goldblatt.IsHyperfinite` (`isHyperfinite_iff_mkAtomSet_mem_star_finPowerset`), and
    `Goldblatt.IsInternalFun` (`isInternalFun_iff_isInternalEntity_partialFunToEntity`,
    `isInternalFun_total_iff_mem_star_funSpace`) to `hyperrealFramework`.
-/

noncomputable section

namespace Goldblatt.Ch13

open Filter
open Hyperreal (ofSeq ofSeq_lt_ofSeq ofSeq_le_ofSeq ofSeq_surjective)
open scoped Topology Classical BigOperators

/-! ## §13.1–13.3 Cumulative Superstructure Entities, Pairs, Tuples, Relations, and Functions -/

/-- Goldblatt §13.6 (p. 164): Raw `n`-th cumulative stage over a base type `X` of individuals:
stage `0` consists of individuals `X`, and stage `n + 1` consists of either individuals `X` or
subsets of stage `n` (`𝕌_{n+1}(X) = X ∪ 𝒫(𝕌_n(X))`). -/
def RawStage (X : Type*) : ℕ → Type _
  | 0 => X
  | n + 1 => X ⊕ Set (RawStage X n)

/-- Extensional equivalence across arbitrary raw stages `RawStage X m` and `RawStage X n`:
atoms match iff equal in `X`, sets match iff mutually cofinal under `RawEquiv`, and an atom is
never equivalent to a set (in particular, individuals are distinct from `∅`; Goldblatt §13.5,
p. 162). -/
def RawEquiv {X : Type*} : ∀ {m n : ℕ}, RawStage X m → RawStage X n → Prop
  | 0, 0, x, y => x = y
  | 0, _ + 1, x, .inl y => x = y
  | 0, _ + 1, _, .inr _ => False
  | _ + 1, 0, .inl x, y => x = y
  | _ + 1, 0, .inr _, _ => False
  | _ + 1, _ + 1, .inl x, .inl y => x = y
  | _ + 1, _ + 1, .inl _, .inr _ => False
  | _ + 1, _ + 1, .inr _, .inl _ => False
  | _ + 1, _ + 1, .inr A, .inr B =>
      (∀ a ∈ A, ∃ b ∈ B, RawEquiv a b) ∧ (∀ b ∈ B, ∃ a ∈ A, RawEquiv a b)

/-- Reflexivity of `RawEquiv` at any stage `m` (Goldblatt §13.6, p. 164). -/
theorem RawEquiv.refl {X : Type*} : ∀ {m : ℕ} (a : RawStage X m), RawEquiv a a
  | 0, _ => rfl
  | _ + 1, .inl _ => rfl
  | _ + 1, .inr _ => ⟨fun a ha ↦ ⟨a, ha, RawEquiv.refl a⟩, fun b hb ↦ ⟨b, hb, RawEquiv.refl b⟩⟩

/-- Symmetry of `RawEquiv` across arbitrary stages (Goldblatt §13.6, p. 164). -/
theorem RawEquiv.symm {X : Type*} :
    ∀ {m n : ℕ} {a : RawStage X m} {b : RawStage X n}, RawEquiv a b → RawEquiv b a
  | 0, 0, _, _, h => Eq.symm h
  | 0, _ + 1, _, .inl _, h => Eq.symm h
  | 0, _ + 1, _, .inr _, h => False.elim h
  | _ + 1, 0, .inl _, _, h => Eq.symm h
  | _ + 1, 0, .inr _, _, h => False.elim h
  | _ + 1, _ + 1, .inl _, .inl _, h => Eq.symm h
  | _ + 1, _ + 1, .inl _, .inr _, h => False.elim h
  | _ + 1, _ + 1, .inr _, .inl _, h => False.elim h
  | _ + 1, _ + 1, .inr _, .inr _, ⟨hAB, hBA⟩ =>
      ⟨fun b hb ↦ let ⟨a, ha, hab⟩ := hBA b hb; ⟨a, ha, RawEquiv.symm hab⟩,
       fun a ha ↦ let ⟨b, hb, hab⟩ := hAB a ha; ⟨b, hb, RawEquiv.symm hab⟩⟩

/-- Transitivity of `RawEquiv` across arbitrary stages (Goldblatt §13.6, p. 164). -/
theorem RawEquiv.trans {X : Type*} :
    ∀ {m n p : ℕ} {a : RawStage X m} {b : RawStage X n} {c : RawStage X p},
      RawEquiv a b → RawEquiv b c → RawEquiv a c
  | 0, 0, 0, _, _, _, h1, h2 => Eq.trans h1 h2
  | 0, 0, _ + 1, _, _, .inl _, h1, h2 => Eq.trans h1 h2
  | 0, 0, _ + 1, _, _, .inr _, _, h2 => False.elim h2
  | 0, _ + 1, 0, _, .inl _, _, h1, h2 => Eq.trans h1 h2
  | 0, _ + 1, _ + 1, _, .inl _, .inl _, h1, h2 => Eq.trans h1 h2
  | 0, _ + 1, _ + 1, _, .inl _, .inr _, _, h2 => False.elim h2
  | 0, _ + 1, _, _, .inr _, _, h1, _ => False.elim h1
  | _ + 1, 0, 0, .inl _, _, _, h1, h2 => Eq.trans h1 h2
  | _ + 1, 0, _ + 1, .inl _, _, .inl _, h1, h2 => Eq.trans h1 h2
  | _ + 1, 0, _ + 1, .inl _, _, .inr _, _, h2 => False.elim h2
  | _ + 1, 0, _, .inr _, _, _, h1, _ => False.elim h1
  | _ + 1, _ + 1, 0, .inl _, .inl _, _, h1, h2 => Eq.trans h1 h2
  | _ + 1, _ + 1, 0, .inl _, .inr _, _, h1, _ => False.elim h1
  | _ + 1, _ + 1, 0, .inr _, .inl _, _, h1, _ => False.elim h1
  | _ + 1, _ + 1, 0, .inr _, .inr _, _, _, h2 => False.elim h2
  | _ + 1, _ + 1, _ + 1, .inl _, .inl _, .inl _, h1, h2 => Eq.trans h1 h2
  | _ + 1, _ + 1, _ + 1, .inl _, .inl _, .inr _, _, h2 => False.elim h2
  | _ + 1, _ + 1, _ + 1, .inl _, .inr _, _, h1, _ => False.elim h1
  | _ + 1, _ + 1, _ + 1, .inr _, .inl _, _, h1, _ => False.elim h1
  | _ + 1, _ + 1, _ + 1, .inr _, .inr _, .inl _, _, h2 => False.elim h2
  | _ + 1, _ + 1, _ + 1, .inr _, .inr _, .inr _, ⟨hAB, hBA⟩, ⟨hBC, hCB⟩ =>
      ⟨fun a ha ↦
        let ⟨b, hb, hab⟩ := hAB a ha
        let ⟨c, hc, hbc⟩ := hBC b hb
        ⟨c, hc, RawEquiv.trans hab hbc⟩,
       fun c hc ↦
        let ⟨b, hb, hcb⟩ := hCB c hc
        let ⟨a, ha, hba⟩ := hBA b hb
        ⟨a, ha, RawEquiv.trans hba hcb⟩⟩

/-- One-step cumulative stage inclusion `RawStage X m → RawStage X (m + 1)`
(Goldblatt §13.6, p. 164). -/
def RawStage.liftOne {X : Type*} : ∀ {m : ℕ}, RawStage X m → RawStage X (m + 1)
  | 0, x => .inl x
  | _ + 1, .inl x => .inl x
  | _ + 1, .inr A => .inr (RawStage.liftOne '' A)

/-- `RawStage.liftOne` preserves `RawEquiv` (Goldblatt §13.6, p. 164). -/
theorem RawEquiv.liftOne_self {X : Type*} :
    ∀ {m : ℕ} (a : RawStage X m), RawEquiv a (RawStage.liftOne a)
  | 0, _ => rfl
  | _ + 1, .inl _ => rfl
  | _ + 1, .inr _ =>
      ⟨fun a ha ↦ ⟨RawStage.liftOne a, ⟨a, ha, rfl⟩, RawEquiv.liftOne_self a⟩,
       fun _ ⟨a, ha, hEq⟩ ↦ hEq ▸ ⟨a, ha, RawEquiv.liftOne_self a⟩⟩

/-- Iterated cumulative stage inclusion `RawStage X m → RawStage X (m + k)`
(Goldblatt §13.6, p. 164). -/
def RawStage.liftAdd {X : Type*} {m : ℕ} : ∀ k : ℕ, RawStage X m → RawStage X (m + k)
  | 0, a => a
  | k + 1, a => RawStage.liftOne (RawStage.liftAdd k a)

/-- `RawStage.liftAdd` preserves `RawEquiv` (Goldblatt §13.6, p. 164). -/
theorem RawEquiv.liftAdd_self {X : Type*} {m : ℕ} :
    ∀ (k : ℕ) (a : RawStage X m), RawEquiv a (RawStage.liftAdd k a)
  | 0, a => RawEquiv.refl a
  | k + 1, a => (RawEquiv.liftAdd_self k a).trans (RawEquiv.liftOne_self _)

/-- `RawEquiv` is invariant under stage-equality casts on the right (Goldblatt §13.6, p. 164). -/
theorem RawEquiv.cast_right {X : Type*} {m n n' : ℕ} (hn : n = n')
    (a : RawStage X m) (b : RawStage X n) (hab : RawEquiv a b) :
    RawEquiv a (hn ▸ b) := by
  subst hn
  exact hab

/-- Cumulative stage inclusion `RawStage X m → RawStage X n` whenever `m ≤ n`
(Goldblatt §13.6, p. 164). -/
def RawStage.liftLE {X : Type*} {m n : ℕ} (h : m ≤ n) (a : RawStage X m) : RawStage X n :=
  Nat.add_sub_of_le h ▸ RawStage.liftAdd (n - m) a

/-- `RawStage.liftLE` preserves `RawEquiv` (Goldblatt §13.6, p. 164). -/
theorem RawEquiv.liftLE_self {X : Type*} {m n : ℕ} (h : m ≤ n) (a : RawStage X m) :
    RawEquiv a (RawStage.liftLE h a) :=
  RawEquiv.cast_right (Nat.add_sub_of_le h) a (RawStage.liftAdd (n - m) a)
    (RawEquiv.liftAdd_self (n - m) a)

/-- Setoid on `(m : ℕ) × RawStage X m` identifying stage elements via `RawEquiv`
(Goldblatt §13.6, p. 164). -/
def rawStageSetoid (X : Type*) : Setoid ((m : ℕ) × RawStage X m) where
  r p q := RawEquiv p.2 q.2
  iseqv := ⟨fun p ↦ RawEquiv.refl p.2, fun h ↦ h.symm, fun h1 h2 ↦ h1.trans h2⟩

/-- Goldblatt §13.1 & §13.6 (pp. 158, 164): The superstructure `Entity X` (`𝕌(X) = ⋃_{n : ℕ} 𝕌_n(X)`)
over a base type `X` of individuals, constructed in the same universe level as `X`. -/
def Entity (X : Type*) : Type _ :=
  Quotient (rawStageSetoid X)

/-- Canonical quotient constructor placing `a : RawStage X m` into `Entity X`
(Goldblatt §13.6, p. 164). -/
def Entity.ofRaw {X : Type*} {m : ℕ} (a : RawStage X m) : Entity X :=
  Quotient.mk (rawStageSetoid X) ⟨m, a⟩

/-- Equality of `Entity.ofRaw` values reduces to `RawEquiv` (Goldblatt §13.6, p. 164). -/
theorem Entity.ofRaw_eq_iff {X : Type*} {m n : ℕ} {a : RawStage X m} {b : RawStage X n} :
    Entity.ofRaw a = Entity.ofRaw b ↔ RawEquiv a b :=
  Quotient.eq (r := rawStageSetoid X)

/-- `Entity.ofRaw` is invariant under `RawStage.liftLE` (Goldblatt §13.6, p. 164). -/
theorem Entity.ofRaw_liftLE {X : Type*} {m n : ℕ} (h : m ≤ n) (a : RawStage X m) :
    Entity.ofRaw (RawStage.liftLE h a) = Entity.ofRaw a :=
  Entity.ofRaw_eq_iff.2 (RawEquiv.liftLE_self h a).symm

/-- Goldblatt §13.1 & §13.6 (pp. 158, 164): Embedding of an individual `x : X` as a rank-`0` atom
in `Entity X`. -/
def Entity.atom {X : Type*} (x : X) : Entity X :=
  Entity.ofRaw (m := 0) x

/-- `Entity.atom` is injective (Goldblatt §13.6, p. 164). -/
theorem Entity.atom_injective {X : Type*} : Function.Injective (Entity.atom (X := X)) :=
  fun _ _ h ↦ Entity.ofRaw_eq_iff.1 h

/-- Equality of atoms in `Entity X` (Goldblatt §13.6, p. 164). -/
@[simp]
theorem Entity.atom_inj {X : Type*} {x y : X} :
    Entity.atom x = Entity.atom y ↔ x = y :=
  ⟨fun h ↦ Entity.atom_injective h, congrArg Entity.atom⟩

/-- Stage `(n + 1)` left injection represents `Entity.atom x` (Goldblatt §13.6, p. 164). -/
@[simp]
theorem Entity.ofRaw_inl {X : Type*} {n : ℕ} (x : X) :
    Entity.ofRaw (m := n + 1) (.inl x) = Entity.atom x :=
  Entity.ofRaw_eq_iff.2 rfl

/-- Raw membership relation `a ∈ b` on `RawStage X` (Goldblatt §13.1, p. 158). -/
def RawMem {X : Type*} {m : ℕ} (a : RawStage X m) : ∀ {n : ℕ}, RawStage X n → Prop
  | 0, _ => False
  | _ + 1, .inl _ => False
  | _ + 1, .inr B => ∃ b ∈ B, RawEquiv a b

/-- `RawMem` respects `RawEquiv` in both arguments (Goldblatt §13.1, p. 158). -/
theorem RawMem.congr {X : Type*} {m₁ m₂ n₁ n₂ : ℕ}
    {a₁ : RawStage X m₁} {a₂ : RawStage X m₂} {b₁ : RawStage X n₁} {b₂ : RawStage X n₂}
    (ha : RawEquiv a₁ a₂) (hb : RawEquiv b₁ b₂) :
    RawMem a₁ b₁ ↔ RawMem a₂ b₂ := by
  cases n₁ with
  | zero =>
      cases n₂ with
      | zero => rfl
      | succ k₂ =>
          cases b₂ with
          | inl _ => rfl
          | inr _ => exact False.elim hb
  | succ k₁ =>
      cases b₁ with
      | inl _ =>
          cases n₂ with
          | zero => rfl
          | succ k₂ =>
              cases b₂ with
              | inl _ => rfl
              | inr _ => exact False.elim hb
      | inr B₁ =>
          cases n₂ with
          | zero => exact False.elim hb
          | succ k₂ =>
              cases b₂ with
              | inl _ => exact False.elim hb
              | inr B₂ =>
                  rcases hb with ⟨h12, h21⟩
                  constructor
                  · rintro ⟨u, hu, hau⟩
                    obtain ⟨v, hv, huv⟩ := h12 u hu
                    exact ⟨v, hv, ha.symm.trans (hau.trans huv)⟩
                  · rintro ⟨v, hv, hav⟩
                    obtain ⟨u, hu, huv⟩ := h21 v hv
                    exact ⟨u, hu, ha.trans (hav.trans huv.symm)⟩

/-- Goldblatt §13.1 (p. 158): Set-theoretic membership `a ∈ b` on `Entity X`. -/
def Entity.Mem {X : Type*} (a b : Entity X) : Prop :=
  Quotient.lift₂ (s₁ := rawStageSetoid X) (s₂ := rawStageSetoid X)
    (fun p q ↦ RawMem p.2 q.2)
    (fun _ _ _ _ ha hb ↦ propext (RawMem.congr ha hb)) a b

/-- `Membership` instance enabling `a ∈ b` and `a ∉ b` for `a, b : Entity X`
(Goldblatt §13.1, p. 158). -/
instance Entity.instMembership {X : Type*} : Membership (Entity X) (Entity X) where
  mem b a := Entity.Mem a b

/-- Unfolding `a ∈ Entity.ofRaw (.inr B)` at stage `n + 1` (Goldblatt §13.6, p. 164). -/
theorem Entity.mem_ofRaw_inr {X : Type*} {n : ℕ} {a : Entity X} {B : Set (RawStage X n)} :
    a ∈ Entity.ofRaw (m := n + 1) (.inr B) ↔ ∃ b ∈ B, a = Entity.ofRaw b := by
  refine Quotient.inductionOn a fun ⟨m, a₀⟩ ↦ ?_
  change (∃ b ∈ B, RawEquiv a₀ b) ↔ ∃ b ∈ B, Entity.ofRaw a₀ = Entity.ofRaw b
  simp only [Entity.ofRaw_eq_iff]

/-- Goldblatt §13.1 & §13.5 (pp. 158, 162): Individuals `Entity.atom x` have no members. -/
@[simp]
theorem Entity.not_mem_atom {X : Type*} (a : Entity X) (x : X) :
    a ∉ Entity.atom x := by
  refine Quotient.inductionOn a fun ⟨_, _⟩ ↦ ?_
  exact id

/-- Goldblatt §13.6 (p. 164): Predicate identifying rank-`0` individuals in `Entity X`. -/
def Entity.IsAtom {X : Type*} (e : Entity X) : Prop :=
  ∃ x : X, e = Entity.atom x

/-- Goldblatt §13.6 (p. 164): Predicate identifying set entities (all non-atom members of
`Entity X`). -/
def Entity.IsSet {X : Type*} (e : Entity X) : Prop :=
  ¬ e.IsAtom

/-- `Entity.atom x` is an atom (Goldblatt §13.6, p. 164). -/
@[simp]
theorem Entity.isAtom_atom {X : Type*} (x : X) : (Entity.atom x).IsAtom :=
  ⟨x, rfl⟩

/-- `Entity.atom x` is not a set (Goldblatt §13.6, p. 164). -/
@[simp]
theorem Entity.not_isSet_atom {X : Type*} (x : X) : ¬ (Entity.atom x).IsSet :=
  fun h ↦ h ⟨x, rfl⟩

/-- `Entity.ofRaw (m := n + 1) (.inr B)` is always a set, never an atom (Goldblatt §13.6, p. 164). -/
@[simp]
theorem Entity.isSet_ofRaw_inr {X : Type*} {n : ℕ} (B : Set (RawStage X n)) :
    (Entity.ofRaw (m := n + 1) (.inr B)).IsSet := by
  rintro ⟨x, hx⟩
  exact Entity.ofRaw_eq_iff.1 hx

/-- Every entity in `Entity X` is either an atom or a set represented by `.inr B` at some stage
`n + 1` (Goldblatt §13.6, p. 164). -/
theorem Entity.isAtom_or_exists_inr {X : Type*} (e : Entity X) :
    e.IsAtom ∨ ∃ (n : ℕ) (B : Set (RawStage X n)), e = Entity.ofRaw (m := n + 1) (.inr B) := by
  refine Quotient.inductionOn e fun ⟨m, r⟩ ↦ ?_
  cases m with
  | zero => exact Or.inl ⟨r, rfl⟩
  | succ n =>
      cases r with
      | inl x => exact Or.inl ⟨x, Entity.ofRaw_inl x⟩
      | inr B => exact Or.inr ⟨n, B, rfl⟩

/-- Characterization of `Entity.IsSet` via stage set representatives (Goldblatt §13.6, p. 164). -/
theorem Entity.isSet_iff_exists_inr {X : Type*} {e : Entity X} :
    e.IsSet ↔ ∃ (n : ℕ) (B : Set (RawStage X n)), e = Entity.ofRaw (m := n + 1) (.inr B) := by
  constructor
  · intro hs
    exact (Entity.isAtom_or_exists_inr e).resolve_left hs
  · rintro ⟨n, B, rfl⟩
    exact Entity.isSet_ofRaw_inr B

/-- Any entity that has at least one member is a set (Goldblatt §13.5, p. 162). -/
theorem Entity.isSet_of_mem {X : Type*} {a b : Entity X} (h : a ∈ b) : b.IsSet := by
  rintro ⟨x, rfl⟩
  exact Entity.not_mem_atom a x h

/-- **Set Extensionality** in `Entity X` (Goldblatt §13.1 & §13.5, pp. 158, 162): two set entities
with the exact same members are equal. -/
theorem Entity.set_ext {X : Type*} {A B : Entity X} (hA : A.IsSet) (hB : B.IsSet)
    (hext : ∀ z : Entity X, z ∈ A ↔ z ∈ B) :
    A = B := by
  obtain ⟨m, A₀, hAeq⟩ := Entity.isSet_iff_exists_inr.1 hA
  obtain ⟨n, B₀, hBeq⟩ := Entity.isSet_iff_exists_inr.1 hB
  rw [hAeq, hBeq]
  refine Entity.ofRaw_eq_iff.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · have hmem : Entity.ofRaw a ∈ Entity.ofRaw (m := n + 1) (.inr B₀) := by
      rw [← hBeq, ← hext, hAeq, Entity.mem_ofRaw_inr]
      exact ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hab⟩ := Entity.mem_ofRaw_inr.1 hmem
    exact ⟨b, hb, Entity.ofRaw_eq_iff.1 hab⟩
  · have hmem : Entity.ofRaw b ∈ Entity.ofRaw (m := m + 1) (.inr A₀) := by
      rw [← hAeq, hext, hBeq, Entity.mem_ofRaw_inr]
      exact ⟨b, hb, rfl⟩
    obtain ⟨a, ha, hba⟩ := Entity.mem_ofRaw_inr.1 hmem
    exact ⟨a, ha, Entity.ofRaw_eq_iff.1 hba.symm⟩

/-- Extension `{z : Entity X | z ∈ e}` of an entity as a Lean `Set (Entity X)`
(Goldblatt §13.1, p. 158). -/
def Entity.extSet {X : Type*} (e : Entity X) : Set (Entity X) :=
  {z : Entity X | z ∈ e}

/-- Membership in `Entity.extSet` is just `∈` (Goldblatt §13.1, p. 158). -/
@[simp]
theorem Entity.mem_extSet {X : Type*} {z e : Entity X} :
    z ∈ e.extSet ↔ z ∈ e := Iff.rfl

/-- Goldblatt §13.5 (p. 163): The empty set `∅` in `Entity X` (represented at stage `1`). -/
def Entity.empty {X : Type*} : Entity X :=
  Entity.ofRaw (m := 1) (.inr ∅)

/-- `EmptyCollection` instance on `Entity X` so `∅ : Entity X` denotes `Entity.empty`
(Goldblatt §13.5, p. 163). -/
instance Entity.instEmptyCollection {X : Type*} : EmptyCollection (Entity X) where
  emptyCollection := Entity.empty

/-- `∅ : Entity X` is a set, not an individual (Goldblatt §13.5, p. 162: `∀ x ∈ X, x ≠ ∅`). -/
@[simp]
theorem Entity.isSet_empty {X : Type*} : (∅ : Entity X).IsSet :=
  Entity.isSet_ofRaw_inr ∅

/-- Every atom is distinct from `∅` (Goldblatt §13.5, p. 162 & §13.6, p. 164). -/
@[simp]
theorem Entity.atom_ne_empty {X : Type*} (x : X) : Entity.atom x ≠ (∅ : Entity X) :=
  fun h ↦ Entity.not_isSet_atom x (h ▸ Entity.isSet_empty)

/-- No entity belongs to `∅ : Entity X` (Goldblatt §13.5, p. 163). -/
@[simp]
theorem Entity.not_mem_empty {X : Type*} (z : Entity X) : z ∉ (∅ : Entity X) := by
  change ¬ (z ∈ Entity.ofRaw (m := 1) (.inr ∅))
  rw [Entity.mem_ofRaw_inr]
  rintro ⟨_, hb, _⟩
  exact hb

/-- A set entity is equal to `∅` iff it has no members (Goldblatt §13.5, p. 163). -/
theorem Entity.eq_empty_iff_forall_not_mem {X : Type*} {A : Entity X} (hA : A.IsSet) :
    A = ∅ ↔ ∀ z : Entity X, z ∉ A := by
  constructor
  · rintro rfl z
    exact Entity.not_mem_empty z
  · intro h
    exact Entity.set_ext hA Entity.isSet_empty fun z ↦ ⟨fun hz ↦ (h z hz).elim,
      fun hz ↦ (Entity.not_mem_empty z hz).elim⟩

/-- First-order (`Δ₀`) characterization of sets vs individuals in `Entity X`
(Goldblatt §13.8, p. 169): an entity `e` is a set iff `e = ∅` or `e` has at least one member. -/
theorem Entity.isSet_iff_eq_empty_or_nonempty {X : Type*} {e : Entity X} :
    e.IsSet ↔ e = ∅ ∨ ∃ z : Entity X, z ∈ e := by
  constructor
  · intro hs
    by_cases hne : ∃ z : Entity X, z ∈ e
    · exact Or.inr hne
    · push Not at hne
      exact Or.inl ((Entity.eq_empty_iff_forall_not_mem hs).2 hne)
  · rintro (rfl | ⟨z, hz⟩)
    · exact Entity.isSet_empty
    · exact Entity.isSet_of_mem hz

/-- First-order (`Δ₀`) characterization of individuals in `Entity X` (Goldblatt §13.5, p. 162 &
§13.8, p. 169): `e` is an individual iff `e ≠ ∅` and `e` has no members. -/
theorem Entity.isAtom_iff_ne_empty_and_forall_not_mem {X : Type*} {e : Entity X} :
    e.IsAtom ↔ e ≠ ∅ ∧ ∀ z : Entity X, z ∉ e := by
  have h : ¬ e.IsSet ↔ ¬ (e = ∅ ∨ ∃ z : Entity X, z ∈ e) := not_congr Entity.isSet_iff_eq_empty_or_nonempty
  rw [Entity.IsSet, Decidable.not_not] at h
  rw [h]
  push Not
  rfl

/-! ## §13.6 Cumulative Power Set Stages `VStage X n`, Rank, and Bounded Comprehension -/

/-- Goldblatt §13.6 (p. 164): The `n`-th cumulative superstructure stage `𝕌_n(X)` as a subset of
`Entity X`. -/
def VStage (X : Type*) (n : ℕ) : Set (Entity X) :=
  Set.range (Entity.ofRaw (X := X) (m := n))

/-- Stage `0` consists precisely of the individuals (`VStage X 0 = {atom x | x : X}`;
Goldblatt §13.6, p. 164). -/
theorem mem_vStage_zero_iff {X : Type*} {e : Entity X} :
    e ∈ VStage X 0 ↔ e.IsAtom :=
  ⟨fun ⟨x, hx⟩ ↦ ⟨x, hx.symm⟩, fun ⟨x, hx⟩ ↦ ⟨x, hx.symm⟩⟩

/-- Monotonicity of cumulative stages: `m ≤ n → VStage X m ⊆ VStage X n`
(Goldblatt §13.6, p. 164). -/
theorem vStage_mono {X : Type*} {m n : ℕ} (h : m ≤ n) :
    VStage X m ⊆ VStage X n := by
  rintro _ ⟨r, rfl⟩
  exact ⟨RawStage.liftLE h r, Entity.ofRaw_liftLE h r⟩

/-- `𝕌(X) = ⋃_{n : ℕ} 𝕌_n(X)`: every entity in `Entity X` belongs to some stage `VStage X n`
(Goldblatt §13.6, p. 164). -/
theorem exists_mem_vStage {X : Type*} (e : Entity X) :
    ∃ n : ℕ, e ∈ VStage X n :=
  Quotient.inductionOn e fun ⟨n, r⟩ ↦ ⟨n, r, rfl⟩

/-- `⋃ n, VStage X n = Set.univ` (Goldblatt §13.6, p. 164). -/
theorem iUnion_vStage {X : Type*} :
    (⋃ n : ℕ, VStage X n) = Set.univ :=
  Set.eq_univ_of_forall fun e ↦ Set.mem_iUnion.2 (exists_mem_vStage e)

/-- Goldblatt §13.6 (p. 164): The **rank** of an entity `e : Entity X` is the least `n : ℕ` such
that `e ∈ VStage X n`. -/
def Entity.rank {X : Type*} (e : Entity X) : ℕ :=
  Nat.find (exists_mem_vStage e)

/-- Every entity `e` belongs to `VStage X e.rank` (Goldblatt §13.6, p. 164). -/
theorem Entity.mem_vStage_rank {X : Type*} (e : Entity X) :
    e ∈ VStage X e.rank :=
  Nat.find_spec (exists_mem_vStage e)

/-- `e ∈ VStage X n` if and only if `e.rank ≤ n` (Goldblatt §13.6, p. 164). -/
theorem mem_vStage_iff_rank_le {X : Type*} {e : Entity X} {n : ℕ} :
    e ∈ VStage X n ↔ e.rank ≤ n :=
  ⟨Nat.find_min' (exists_mem_vStage e), fun h ↦ vStage_mono h e.mem_vStage_rank⟩

/-- Rank `0` entities are precisely the individuals (`e.rank = 0 ↔ e.IsAtom`;
Goldblatt §13.6, p. 164). -/
theorem Entity.rank_eq_zero_iff {X : Type*} {e : Entity X} :
    e.rank = 0 ↔ e.IsAtom := by
  rw [← Nat.le_zero, ← mem_vStage_iff_rank_le, mem_vStage_zero_iff]

/-- Every individual `Entity.atom x` has rank `0` (Goldblatt §13.6, p. 164). -/
@[simp]
theorem Entity.rank_atom {X : Type*} (x : X) : (Entity.atom x).rank = 0 :=
  Entity.rank_eq_zero_iff.2 (Entity.isAtom_atom x)

/-- Set entities are precisely those of positive rank (`1 ≤ e.rank ↔ e.IsSet`;
Goldblatt §13.6, p. 164). -/
theorem Entity.one_le_rank_iff_isSet {X : Type*} {e : Entity X} :
    1 ≤ e.rank ↔ e.IsSet := by
  rw [Entity.IsSet, ← Entity.rank_eq_zero_iff]
  omega

/-- `∅` has rank `1` (Goldblatt §13.6, p. 164). -/
@[simp]
theorem Entity.rank_empty {X : Type*} : (∅ : Entity X).rank = 1 := by
  have h1 : (∅ : Entity X).rank ≤ 1 := mem_vStage_iff_rank_le.1 ⟨.inr ∅, rfl⟩
  have h2 : 1 ≤ (∅ : Entity X).rank := Entity.one_le_rank_iff_isSet.2 Entity.isSet_empty
  omega

/-- Goldblatt §13.6 (p. 165): A subset `S : Set (Entity X)` has **bounded rank** if `S ⊆ VStage X n`
for some `n : ℕ`. -/
def IsBoundedRank {X : Type*} (S : Set (Entity X)) : Prop :=
  ∃ n : ℕ, S ⊆ VStage X n

/-- Every subset of a bounded-rank set has bounded rank (Goldblatt §13.6, p. 165). -/
theorem IsBoundedRank.subset {X : Type*} {S T : Set (Entity X)}
    (hT : IsBoundedRank T) (hST : S ⊆ T) : IsBoundedRank S :=
  let ⟨n, hn⟩ := hT
  ⟨n, hST.trans hn⟩

/-- Goldblatt §13.6 (p. 165): Forming a set entity `Entity.setOfBounded S` from any subset
`S : Set (Entity X)`. When `S` has bounded rank (`S ⊆ VStage X n`), `Entity.setOfBounded S` is the
unique set entity in `Entity X` whose members are precisely the elements of `S`; otherwise it
defaults to `∅`. -/
def Entity.setOfBounded {X : Type*} (S : Set (Entity X)) : Entity X :=
  if h : IsBoundedRank S then
    Entity.ofRaw (m := h.choose + 1) (.inr {r : RawStage X h.choose | Entity.ofRaw r ∈ S})
  else
    ∅

/-- `Entity.setOfBounded S` is always a set entity (Goldblatt §13.6, p. 165). -/
@[simp]
theorem Entity.isSet_setOfBounded {X : Type*} (S : Set (Entity X)) :
    (Entity.setOfBounded S).IsSet := by
  unfold Entity.setOfBounded
  split_ifs with h
  · exact Entity.isSet_ofRaw_inr _
  · exact Entity.isSet_empty

/-- Membership in `Entity.setOfBounded S` when `S` has bounded rank (Goldblatt §13.6, p. 165). -/
theorem Entity.mem_setOfBounded {X : Type*} {S : Set (Entity X)} (hS : IsBoundedRank S)
    {z : Entity X} :
    z ∈ Entity.setOfBounded S ↔ z ∈ S := by
  unfold Entity.setOfBounded
  simp only [hS, ↓reduceDIte]
  rw [Entity.mem_ofRaw_inr]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro hz
    obtain ⟨b, rfl⟩ := hS.choose_spec hz
    exact ⟨b, hz, rfl⟩

/-- Stage bound for `Entity.setOfBounded S`: if `S ⊆ VStage X n`, then
`Entity.setOfBounded S ∈ VStage X (n + 1)` (Goldblatt §13.6, p. 165). -/
theorem Entity.setOfBounded_mem_vStage {X : Type*} {S : Set (Entity X)} {n : ℕ}
    (hS : S ⊆ VStage X n) :
    Entity.setOfBounded S ∈ VStage X (n + 1) := by
  have hbdd : IsBoundedRank S := ⟨n, hS⟩
  refine ⟨.inr {r : RawStage X n | Entity.ofRaw r ∈ S}, ?_⟩
  refine Entity.set_ext (Entity.isSet_ofRaw_inr _) (Entity.isSet_setOfBounded S) fun z ↦ ?_
  rw [Entity.mem_ofRaw_inr, Entity.mem_setOfBounded hbdd]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro hz
    obtain ⟨b, rfl⟩ := hS hz
    exact ⟨b, hz, rfl⟩

/-- Goldblatt §13.6 Property (3) (p. 165): If `a ∈ B` and `B ∈ VStage X (n + 1)`, then
`a ∈ VStage X n`. -/
theorem mem_vStage_of_mem_vStage_succ {X : Type*} {a B : Entity X} {n : ℕ}
    (haB : a ∈ B) (hB : B ∈ VStage X (n + 1)) :
    a ∈ VStage X n := by
  obtain ⟨r, rfl⟩ := hB
  cases r with
  | inl x =>
      rw [Entity.ofRaw_inl] at haB
      exact (Entity.not_mem_atom a x haB).elim
  | inr B₀ =>
      obtain ⟨b, _, rfl⟩ := Entity.mem_ofRaw_inr.1 haB
      exact ⟨b, rfl⟩

/-- Strictly decreasing rank along membership: if `a ∈ B`, then `a.rank < B.rank`
(Goldblatt §13.6, p. 165). -/
theorem Entity.rank_lt_of_mem {X : Type*} {a B : Entity X} (haB : a ∈ B) :
    a.rank < B.rank := by
  have hBset : B.IsSet := Entity.isSet_of_mem haB
  have hBpos : 1 ≤ B.rank := Entity.one_le_rank_iff_isSet.2 hBset
  have hBstage : B ∈ VStage X ((B.rank - 1) + 1) := by
    have heq : (B.rank - 1) + 1 = B.rank := by omega
    rw [heq]
    exact B.mem_vStage_rank
  have haStage : a ∈ VStage X (B.rank - 1) := mem_vStage_of_mem_vStage_succ haB hBstage
  have hale : a.rank ≤ B.rank - 1 := mem_vStage_iff_rank_le.1 haStage
  omega

/-- Membership is irreflexive (`a ∉ a`) in `Entity X` (foundation/regularity of `𝕌(X)`). -/
theorem Entity.not_mem_self {X : Type*} (a : Entity X) : a ∉ a :=
  fun h ↦ lt_irrefl a.rank (Entity.rank_lt_of_mem h)

/-- Every entity's extension `e.extSet` automatically has bounded rank (Goldblatt §13.6, p. 165). -/
theorem Entity.isBoundedRank_extSet {X : Type*} (e : Entity X) :
    IsBoundedRank e.extSet :=
  ⟨e.rank, fun _ hz ↦ mem_vStage_iff_rank_le.2 (Entity.rank_lt_of_mem hz).le⟩

/-- Every set entity `A` equals `Entity.setOfBounded A.extSet` (Goldblatt §13.6, p. 165). -/
theorem Entity.eq_setOfBounded_extSet {X : Type*} {A : Entity X} (hA : A.IsSet) :
    A = Entity.setOfBounded A.extSet :=
  Entity.set_ext hA (Entity.isSet_setOfBounded _) fun _ ↦
    (Entity.mem_setOfBounded (Entity.isBoundedRank_extSet A)).symm

/-- Goldblatt §13.6 (p. 165): A set `S : Set (Entity X)` is the extension of some set entity in
`Entity X` **if and only if** `S` has bounded rank! -/
theorem exists_entity_extSet_eq_iff_isBoundedRank {X : Type*} {S : Set (Entity X)} :
    (∃ A : Entity X, A.IsSet ∧ A.extSet = S) ↔ IsBoundedRank S := by
  constructor
  · rintro ⟨A, _, rfl⟩
    exact A.isBoundedRank_extSet
  · intro hS
    refine ⟨Entity.setOfBounded S, Entity.isSet_setOfBounded S, ?_⟩
    ext z
    exact Entity.mem_setOfBounded hS

/-- Goldblatt §13.6 Property (1) (p. 164): `𝕌_{n+1}(X) = X ∪ 𝒫(𝕌_n(X))`. -/
theorem vStage_succ_eq {X : Type*} (n : ℕ) :
    VStage X (n + 1) = VStage X 0 ∪ {A : Entity X | A.IsSet ∧ A.extSet ⊆ VStage X n} := by
  ext e
  constructor
  · intro he
    rcases Entity.isAtom_or_exists_inr e with hatom | ⟨m, B₀, hEq⟩
    · exact Or.inl (mem_vStage_zero_iff.2 hatom)
    · refine Or.inr ⟨hEq ▸ Entity.isSet_ofRaw_inr B₀, fun z hz ↦ ?_⟩
      exact mem_vStage_of_mem_vStage_succ hz he
  · rintro (h0 | ⟨hset, hsub⟩)
    · exact vStage_mono (Nat.zero_le _) h0
    · rw [Entity.eq_setOfBounded_extSet hset]
      exact Entity.setOfBounded_mem_vStage hsub

/-- Stage entity `vStageEntity X n : Entity X` representing `𝕌_n(X)` as an element of `Entity X`
(Goldblatt §13.6 Property (2), p. 165). -/
def vStageEntity (X : Type*) (n : ℕ) : Entity X :=
  Entity.setOfBounded (VStage X n)

/-- `vStageEntity X n` is a set whose members are precisely `VStage X n`
(Goldblatt §13.6, p. 165). -/
@[simp]
theorem mem_vStageEntity {X : Type*} {n : ℕ} {e : Entity X} :
    e ∈ vStageEntity X n ↔ e ∈ VStage X n :=
  Entity.mem_setOfBounded ⟨n, Set.Subset.rfl⟩

/-- `vStageEntity X n` is a set entity (Goldblatt §13.6, p. 165). -/
@[simp]
theorem isSet_vStageEntity (X : Type*) (n : ℕ) : (vStageEntity X n).IsSet :=
  Entity.isSet_setOfBounded _

/-- Goldblatt §13.6 Property (2) (p. 165): `𝕌_n(X) ∈ 𝕌_{n+1}(X)`. -/
theorem vStageEntity_mem_vStage_succ (X : Type*) (n : ℕ) :
    vStageEntity X n ∈ VStage X (n + 1) :=
  Entity.setOfBounded_mem_vStage Set.Subset.rfl

/-- `vStageEntity X n ∈ vStageEntity X (n + 1)` (Goldblatt §13.6 Property (2), p. 165). -/
theorem vStageEntity_mem_vStageEntity_succ (X : Type*) (n : ℕ) :
    vStageEntity X n ∈ vStageEntity X (n + 1) :=
  mem_vStageEntity.2 (vStageEntity_mem_vStage_succ X n)

/-- The set `baseSet X : Entity X` of all individuals `X = 𝕌_0(X)` as an element of `Entity X`
(Goldblatt §13.5–13.6, pp. 162, 165). -/
def baseSet (X : Type*) : Entity X :=
  vStageEntity X 0

/-- Membership in `baseSet X` characterizes individuals (`e ∈ baseSet X ↔ e.IsAtom`;
Goldblatt §13.6, p. 164). -/
@[simp]
theorem mem_baseSet_iff {X : Type*} {e : Entity X} :
    e ∈ baseSet X ↔ e.IsAtom := by
  rw [baseSet, mem_vStageEntity, mem_vStage_zero_iff]

/-- Any subset `S : Set X` of individuals defines a rank-`1` set entity `mkAtomSet S : Entity X`
(Goldblatt §13.6, p. 164). -/
def mkAtomSet {X : Type*} (S : Set X) : Entity X :=
  Entity.setOfBounded (Entity.atom '' S)

/-- `mkAtomSet S` is a set entity in `VStage X 1` (Goldblatt §13.6, p. 164). -/
theorem mkAtomSet_mem_vStage_one {X : Type*} (S : Set X) :
    mkAtomSet S ∈ VStage X 1 := by
  refine Entity.setOfBounded_mem_vStage ?_
  rintro _ ⟨x, _, rfl⟩
  exact mem_vStage_zero_iff.2 (Entity.isAtom_atom x)

/-- Membership in `mkAtomSet S` (Goldblatt §13.6, p. 164). -/
@[simp]
theorem mem_mkAtomSet_iff {X : Type*} {S : Set X} {e : Entity X} :
    e ∈ mkAtomSet S ↔ ∃ x ∈ S, e = Entity.atom x := by
  have hbdd : IsBoundedRank (Entity.atom '' S) :=
    ⟨0, by rintro _ ⟨x, _, rfl⟩; exact mem_vStage_zero_iff.2 (Entity.isAtom_atom x)⟩
  rw [mkAtomSet, Entity.mem_setOfBounded hbdd]
  exact ⟨fun ⟨x, hx, heq⟩ ↦ ⟨x, hx, heq.symm⟩, fun ⟨x, hx, heq⟩ ↦ ⟨x, hx, heq.symm⟩⟩

/-- Atom membership in `mkAtomSet S` (`Entity.atom x ∈ mkAtomSet S ↔ x ∈ S`;
Goldblatt §13.6, p. 164). -/
@[simp]
theorem atom_mem_mkAtomSet_iff {X : Type*} {S : Set X} {x : X} :
    Entity.atom x ∈ mkAtomSet S ↔ x ∈ S := by
  simp [mem_mkAtomSet_iff]

/-! ## §13.1–13.3 Set Operations, Kuratowski Pairs, Tuples, Relations, and Functions -/

/-- Goldblatt §13.5 (p. 162): Unordered pair `{a, b}` in `Entity X`. -/
def Entity.upair {X : Type*} (a b : Entity X) : Entity X :=
  Entity.setOfBounded {a, b}

/-- Bounded rank of `{a, b}` (Goldblatt §13.6 Property (4), p. 165). -/
theorem Entity.isBoundedRank_pair {X : Type*} (a b : Entity X) :
    IsBoundedRank ({a, b} : Set (Entity X)) :=
  ⟨max a.rank b.rank, by
    rintro z (rfl | rfl)
    · exact mem_vStage_iff_rank_le.2 (le_max_left _ _)
    · exact mem_vStage_iff_rank_le.2 (le_max_right _ _)⟩

/-- `Entity.upair a b` is a set entity (Goldblatt §13.5, p. 162). -/
@[simp]
theorem Entity.isSet_upair {X : Type*} (a b : Entity X) : (Entity.upair a b).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.upair a b` (`z ∈ {a, b} ↔ z = a ∨ z = b`; Goldblatt §13.5, p. 162). -/
@[simp]
theorem Entity.mem_upair_iff {X : Type*} {z a b : Entity X} :
    z ∈ Entity.upair a b ↔ z = a ∨ z = b :=
  Entity.mem_setOfBounded (Entity.isBoundedRank_pair a b)

/-- Goldblatt §13.6 Property (4) (p. 165): If `a, b ∈ VStage X n`, then
`{a, b} ∈ VStage X (n + 1)`. -/
theorem Entity.upair_mem_vStage {X : Type*} {a b : Entity X} {n : ℕ}
    (ha : a ∈ VStage X n) (hb : b ∈ VStage X n) :
    Entity.upair a b ∈ VStage X (n + 1) :=
  Entity.setOfBounded_mem_vStage (by rintro z (rfl | rfl) <;> assumption)

/-- Goldblatt §13.5 (p. 163): Singleton `{a} = {a, a}` in `Entity X`. -/
def Entity.singleton {X : Type*} (a : Entity X) : Entity X :=
  Entity.upair a a

/-- `Entity.singleton a` is a set entity (Goldblatt §13.5, p. 163). -/
@[simp]
theorem Entity.isSet_singleton {X : Type*} (a : Entity X) : (Entity.singleton a).IsSet :=
  Entity.isSet_upair a a

/-- Membership in `Entity.singleton a` (`z ∈ {a} ↔ z = a`; Goldblatt §13.5, p. 163). -/
@[simp]
theorem Entity.mem_singleton_iff {X : Type*} {z a : Entity X} :
    z ∈ Entity.singleton a ↔ z = a := by
  simp [Entity.singleton]

/-- Equality of singletons (`{a} = {b} ↔ a = b`; Goldblatt §13.3, p. 161). -/
@[simp]
theorem Entity.singleton_inj {X : Type*} {a b : Entity X} :
    Entity.singleton a = Entity.singleton b ↔ a = b := by
  constructor
  · intro h
    have : a ∈ Entity.singleton b := h ▸ Entity.mem_singleton_iff.2 rfl
    exact Entity.mem_singleton_iff.1 this
  · exact congrArg Entity.singleton

/-- Goldblatt §13.1 & §13.5 (pp. 159, 162): Binary union `A ∪ B` of entities in `Entity X`. -/
def Entity.union {X : Type*} (A B : Entity X) : Entity X :=
  Entity.setOfBounded (A.extSet ∪ B.extSet)

/-- `A.extSet ∪ B.extSet` has bounded rank (Goldblatt §13.6 Property (5), p. 165). -/
theorem Entity.isBoundedRank_union {X : Type*} (A B : Entity X) :
    IsBoundedRank (A.extSet ∪ B.extSet) := by
  obtain ⟨m, hm⟩ := A.isBoundedRank_extSet
  obtain ⟨n, hn⟩ := B.isBoundedRank_extSet
  exact ⟨max m n, Set.union_subset
    (hm.trans (vStage_mono (le_max_left m n)))
    (hn.trans (vStage_mono (le_max_right m n)))⟩

/-- `Entity.union A B` is a set entity (Goldblatt §13.5, p. 162). -/
@[simp]
theorem Entity.isSet_union {X : Type*} (A B : Entity X) : (Entity.union A B).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.union A B` (`z ∈ A ∪ B ↔ z ∈ A ∨ z ∈ B`; Goldblatt §13.1, p. 159). -/
@[simp]
theorem Entity.mem_union_iff {X : Type*} {z A B : Entity X} :
    z ∈ Entity.union A B ↔ z ∈ A ∨ z ∈ B :=
  Entity.mem_setOfBounded (Entity.isBoundedRank_union A B)

/-- Goldblatt §13.6 Property (5) (p. 165): If `A, B ∈ VStage X n`, then
`Entity.union A B ∈ VStage X (n + 1)` (and even `∈ VStage X n` when `n ≥ 1`). -/
theorem Entity.union_mem_vStage {X : Type*} {A B : Entity X} {n : ℕ}
    (hA : A ∈ VStage X n) (hB : B ∈ VStage X n) :
    Entity.union A B ∈ VStage X (n + 1) := by
  refine Entity.setOfBounded_mem_vStage ?_
  rintro z (hzA | hzB)
  · exact mem_vStage_of_mem_vStage_succ hzA (vStage_mono (Nat.le_succ n) hA)
  · exact mem_vStage_of_mem_vStage_succ hzB (vStage_mono (Nat.le_succ n) hB)

/-- Goldblatt §13.1 (p. 159): Binary intersection `A ∩ B` in `Entity X`. -/
def Entity.inter {X : Type*} (A B : Entity X) : Entity X :=
  Entity.setOfBounded (A.extSet ∩ B.extSet)

/-- `Entity.inter A B` is a set entity (Goldblatt §13.1, p. 159). -/
@[simp]
theorem Entity.isSet_inter {X : Type*} (A B : Entity X) : (Entity.inter A B).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.inter A B` (`z ∈ A ∩ B ↔ z ∈ A ∧ z ∈ B`; Goldblatt §13.1, p. 159). -/
@[simp]
theorem Entity.mem_inter_iff {X : Type*} {z A B : Entity X} :
    z ∈ Entity.inter A B ↔ z ∈ A ∧ z ∈ B :=
  Entity.mem_setOfBounded (A.isBoundedRank_extSet.subset Set.inter_subset_left)

/-- Goldblatt §13.1 (p. 159): Set difference `A \ B` (`A - B`) in `Entity X`. -/
def Entity.sdiff {X : Type*} (A B : Entity X) : Entity X :=
  Entity.setOfBounded (A.extSet \ B.extSet)

/-- `Entity.sdiff A B` is a set entity (Goldblatt §13.1, p. 159). -/
@[simp]
theorem Entity.isSet_sdiff {X : Type*} (A B : Entity X) : (Entity.sdiff A B).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.sdiff A B` (`z ∈ A \ B ↔ z ∈ A ∧ z ∉ B`; Goldblatt §13.1, p. 159). -/
@[simp]
theorem Entity.mem_sdiff_iff {X : Type*} {z A B : Entity X} :
    z ∈ Entity.sdiff A B ↔ z ∈ A ∧ z ∉ B :=
  Entity.mem_setOfBounded (A.isBoundedRank_extSet.subset Set.sdiff_subset)

/-- Finite set entity `{a₁, …, a_m}` constructed from any `Finset (Entity X)`
(Goldblatt §13.5, p. 163). -/
def Entity.finsetEntity {X : Type*} (S : Finset (Entity X)) : Entity X :=
  Entity.setOfBounded (S : Set (Entity X))

/-- Every `Finset (Entity X)` has bounded rank (Goldblatt §13.5, p. 163). -/
theorem Entity.isBoundedRank_finset {X : Type*} (S : Finset (Entity X)) :
    IsBoundedRank (S : Set (Entity X)) :=
  ⟨S.sup Entity.rank, fun _ hz ↦ mem_vStage_iff_rank_le.2 (Finset.le_sup (Finset.mem_coe.1 hz))⟩

/-- `Entity.finsetEntity S` is a set entity (Goldblatt §13.5, p. 163). -/
@[simp]
theorem Entity.isSet_finsetEntity {X : Type*} (S : Finset (Entity X)) :
    (Entity.finsetEntity S).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.finsetEntity S` (`z ∈ finsetEntity S ↔ z ∈ S`;
Goldblatt §13.5, p. 163). -/
@[simp]
theorem Entity.mem_finsetEntity_iff {X : Type*} {S : Finset (Entity X)} {z : Entity X} :
    z ∈ Entity.finsetEntity S ↔ z ∈ S :=
  Entity.mem_setOfBounded (Entity.isBoundedRank_finset S)

/-- Goldblatt §13.1 & §13.5 (pp. 159, 162): Power set `𝒫(A)` of a set entity `A` in `Entity X`
(all set entities `B` whose members belong to `A`). -/
def Entity.powerset {X : Type*} (A : Entity X) : Entity X :=
  Entity.setOfBounded {B : Entity X | B.IsSet ∧ B.extSet ⊆ A.extSet}

/-- Bounded rank of `{B | B.IsSet ∧ B.extSet ⊆ A.extSet}` (Goldblatt §13.6 Property (6), p. 165). -/
theorem Entity.isBoundedRank_powerset {X : Type*} (A : Entity X) :
    IsBoundedRank {B : Entity X | B.IsSet ∧ B.extSet ⊆ A.extSet} := by
  obtain ⟨n, hn⟩ := A.isBoundedRank_extSet
  refine ⟨n + 1, fun B ⟨hBset, hBsub⟩ ↦ ?_⟩
  rw [Entity.eq_setOfBounded_extSet hBset]
  exact Entity.setOfBounded_mem_vStage (hBsub.trans hn)

/-- `Entity.powerset A` is a set entity (Goldblatt §13.5, p. 162). -/
@[simp]
theorem Entity.isSet_powerset {X : Type*} (A : Entity X) : (Entity.powerset A).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.powerset A` (`B ∈ 𝒫(A) ↔ B.IsSet ∧ ∀ z ∈ B, z ∈ A`;
Goldblatt §13.1, p. 159). -/
@[simp]
theorem Entity.mem_powerset_iff {X : Type*} {B A : Entity X} :
    B ∈ Entity.powerset A ↔ B.IsSet ∧ ∀ z : Entity X, z ∈ B → z ∈ A :=
  Entity.mem_setOfBounded (Entity.isBoundedRank_powerset A)

/-- Goldblatt §13.6 Property (6) (p. 165): If `A ∈ VStage X n`, then
`Entity.powerset A ∈ VStage X (n + 2)`. -/
theorem Entity.powerset_mem_vStage {X : Type*} {A : Entity X} {n : ℕ}
    (hA : A ∈ VStage X n) :
    Entity.powerset A ∈ VStage X (n + 2) := by
  have hsub : A.extSet ⊆ VStage X n := fun z hz ↦
    mem_vStage_of_mem_vStage_succ hz (vStage_mono (Nat.le_succ n) hA)
  refine Entity.setOfBounded_mem_vStage ?_
  rintro B ⟨hBset, hBA⟩
  rw [Entity.eq_setOfBounded_extSet hBset]
  exact Entity.setOfBounded_mem_vStage (hBA.trans hsub)

/-- Sharp rank bound for power sets of set entities: if `A.IsSet` and `A ∈ VStage X n`, then
`Entity.powerset A ∈ VStage X (n + 1)` (Goldblatt §13.6, p. 165). -/
theorem Entity.powerset_mem_vStage_succ_of_isSet {X : Type*} {A : Entity X} {n : ℕ}
    (hAs : A.IsSet) (hA : A ∈ VStage X n) :
    Entity.powerset A ∈ VStage X (n + 1) := by
  rcases n with _ | k
  · exact absurd (mem_vStage_zero_iff.1 hA) hAs
  · have hsub : A.extSet ⊆ VStage X k := fun z hz ↦ mem_vStage_of_mem_vStage_succ hz hA
    refine Entity.setOfBounded_mem_vStage ?_
    rintro B ⟨hBset, hBA⟩
    rw [Entity.eq_setOfBounded_extSet hBset]
    exact Entity.setOfBounded_mem_vStage (hBA.trans hsub)

/-- Goldblatt §13.17 (p. 178): Finite power set `𝒫_F(A) = {B ⊆ A : B is finite}` in `Entity X`. -/
def Entity.finPowerset {X : Type*} (A : Entity X) : Entity X :=
  Entity.setOfBounded {B : Entity X | B.IsSet ∧ B.extSet ⊆ A.extSet ∧ B.extSet.Finite}

/-- `Entity.finPowerset A` is a set entity (Goldblatt §13.17, p. 178). -/
@[simp]
theorem Entity.isSet_finPowerset {X : Type*} (A : Entity X) : (Entity.finPowerset A).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.finPowerset A` (`B ∈ 𝒫_F(A) ↔ B.IsSet ∧ B ⊆ A ∧ B.extSet.Finite`;
Goldblatt §13.17, p. 178). -/
@[simp]
theorem Entity.mem_finPowerset_iff {X : Type*} {B A : Entity X} :
    B ∈ Entity.finPowerset A ↔
      B.IsSet ∧ (∀ z : Entity X, z ∈ B → z ∈ A) ∧ B.extSet.Finite :=
  Entity.mem_setOfBounded
    ((Entity.isBoundedRank_powerset A).subset (by rintro _ ⟨h1, h2, _⟩; exact ⟨h1, h2⟩))

/-- Goldblatt §13.1 & §13.5 (pp. 159, 163): Union `⋃ Y` of a collection of sets `Y : Entity X`. -/
def Entity.sUnion {X : Type*} (Y : Entity X) : Entity X :=
  Entity.setOfBounded {z : Entity X | ∃ A : Entity X, A ∈ Y ∧ z ∈ A}

/-- Bounded rank of `{z | ∃ A ∈ Y, z ∈ A}` (Goldblatt §13.5, p. 163). -/
theorem Entity.isBoundedRank_sUnion {X : Type*} (Y : Entity X) :
    IsBoundedRank {z : Entity X | ∃ A : Entity X, A ∈ Y ∧ z ∈ A} := by
  refine ⟨Y.rank, ?_⟩
  rintro z ⟨A, hAY, hzA⟩
  have h1 : z.rank < A.rank := Entity.rank_lt_of_mem hzA
  have h2 : A.rank < Y.rank := Entity.rank_lt_of_mem hAY
  exact mem_vStage_iff_rank_le.2 (by omega)

/-- `Entity.sUnion Y` is a set entity (Goldblatt §13.5, p. 163). -/
@[simp]
theorem Entity.isSet_sUnion {X : Type*} (Y : Entity X) : (Entity.sUnion Y).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.sUnion Y` (`z ∈ ⋃ Y ↔ ∃ A ∈ Y, z ∈ A`; Goldblatt §13.5, p. 163). -/
@[simp]
theorem Entity.mem_sUnion_iff {X : Type*} {z Y : Entity X} :
    z ∈ Entity.sUnion Y ↔ ∃ A : Entity X, A ∈ Y ∧ z ∈ A :=
  Entity.mem_setOfBounded (Entity.isBoundedRank_sUnion Y)

/-- Goldblatt §13.1 & §13.5 (pp. 159, 163): Intersection `⋂ Y` of a nonempty collection `Y`
(defaulting to `∅` when `Y` has no members). -/
def Entity.sInter {X : Type*} (Y : Entity X) : Entity X :=
  if _ : ∃ A : Entity X, A ∈ Y then
    Entity.setOfBounded {z : Entity X | ∀ A : Entity X, A ∈ Y → z ∈ A}
  else
    ∅

/-- `Entity.sInter Y` is a set entity (Goldblatt §13.5, p. 163). -/
@[simp]
theorem Entity.isSet_sInter {X : Type*} (Y : Entity X) : (Entity.sInter Y).IsSet := by
  unfold Entity.sInter
  split_ifs <;> simp

/-- Membership in `Entity.sInter Y` when `Y` is nonempty (Goldblatt §13.5, p. 163). -/
theorem Entity.mem_sInter_iff {X : Type*} {z Y : Entity X} (hne : ∃ A : Entity X, A ∈ Y) :
    z ∈ Entity.sInter Y ↔ ∀ A : Entity X, A ∈ Y → z ∈ A := by
  unfold Entity.sInter
  have hbdd : IsBoundedRank {w : Entity X | ∀ A : Entity X, A ∈ Y → w ∈ A} := by
    obtain ⟨A₀, hA₀⟩ := hne
    exact A₀.isBoundedRank_extSet.subset fun w hw ↦ hw A₀ hA₀
  simp only [hne, ↓reduceDIte]
  exact Entity.mem_setOfBounded hbdd

/-- Goldblatt §13.3 (p. 161): Kuratowski ordered pair `(a, b) = {{a}, {a, b}}` in `Entity X`. -/
def Entity.kpair {X : Type*} (a b : Entity X) : Entity X :=
  Entity.upair (Entity.singleton a) (Entity.upair a b)

/-- `Entity.kpair a b` is a set entity (Goldblatt §13.3, p. 161). -/
@[simp]
theorem Entity.isSet_kpair {X : Type*} (a b : Entity X) : (Entity.kpair a b).IsSet :=
  Entity.isSet_upair _ _

/-- Stage bound for Kuratowski pairs: if `a, b ∈ VStage X n`, then
`Entity.kpair a b ∈ VStage X (n + 2)` (Goldblatt §13.6, p. 165). -/
theorem Entity.kpair_mem_vStage {X : Type*} {a b : Entity X} {n : ℕ}
    (ha : a ∈ VStage X n) (hb : b ∈ VStage X n) :
    Entity.kpair a b ∈ VStage X (n + 2) :=
  Entity.upair_mem_vStage (Entity.upair_mem_vStage ha ha) (Entity.upair_mem_vStage ha hb)

/-- Goldblatt **Exercise 13.3.1(i)** (p. 161):
`{{a}, {a, b}} = {{c}, {c, d}}` **if and only if** `a = c` and `b = d`! -/
theorem Entity.kpair_inj {X : Type*} {a b c d : Entity X} :
    Entity.kpair a b = Entity.kpair c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have hca : Entity.singleton c ∈ Entity.kpair a b := by
      rw [h]; exact Entity.mem_upair_iff.2 (Or.inl rfl)
    have h_ac : a = c := by
      rcases Entity.mem_upair_iff.1 hca with h1 | h2
      · exact (Entity.singleton_inj.1 h1).symm
      · have ha_in : a ∈ Entity.singleton c := h2 ▸ Entity.mem_upair_iff.2 (Or.inl rfl)
        exact Entity.mem_singleton_iff.1 ha_in
    subst c
    have hbd : Entity.upair a b ∈ Entity.kpair a d := by
      rw [← h]; exact Entity.mem_upair_iff.2 (Or.inr rfl)
    have hdb : Entity.upair a d ∈ Entity.kpair a b := by
      rw [h]; exact Entity.mem_upair_iff.2 (Or.inr rfl)
    rcases Entity.mem_upair_iff.1 hbd with hb_sing | hb_pair
    · have hb_eq_a : b = a := by
        have : b ∈ Entity.singleton a := hb_sing ▸ Entity.mem_upair_iff.2 (Or.inr rfl)
        exact Entity.mem_singleton_iff.1 this
      subst b
      rcases Entity.mem_upair_iff.1 hdb with hd_sing | hd_pair
      · have : d ∈ Entity.singleton a := hd_sing ▸ Entity.mem_upair_iff.2 (Or.inr rfl)
        exact ⟨rfl, (Entity.mem_singleton_iff.1 this).symm⟩
      · have : d ∈ Entity.upair a a := hd_pair ▸ Entity.mem_upair_iff.2 (Or.inr rfl)
        rcases Entity.mem_upair_iff.1 this with rfl | rfl <;> exact ⟨rfl, rfl⟩
    · have : b ∈ Entity.upair a d := hb_pair ▸ Entity.mem_upair_iff.2 (Or.inr rfl)
      rcases Entity.mem_upair_iff.1 this with hba | rfl
      · subst b
        rcases Entity.mem_upair_iff.1 hdb with hd_sing | hd_pair
        · have : d ∈ Entity.singleton a := hd_sing ▸ Entity.mem_upair_iff.2 (Or.inr rfl)
          exact ⟨rfl, (Entity.mem_singleton_iff.1 this).symm⟩
        · have : d ∈ Entity.upair a a := hd_pair ▸ Entity.mem_upair_iff.2 (Or.inr rfl)
          rcases Entity.mem_upair_iff.1 this with rfl | rfl <;> exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Goldblatt §13.2 (p. 160, iterated ordered-pair representation): `m`-tuple `(a₁, …, a_m)` in
`Entity X` over any base type `X`, agreeing with `Entity.kpair` at `m = 2`. -/
def Entity.ktuple {X : Type*} : ∀ {m : ℕ}, (Fin m → Entity X) → Entity X
  | 0, _ => ∅
  | 1, v => v 0
  | 2, v => Entity.kpair (v 0) (v 1)
  | m + 3, v => Entity.kpair (Entity.ktuple (m := m + 2) (Fin.init v)) (v (Fin.last (m + 2)))

/-- At `m = 2`, `Entity.ktuple ![a, b] = Entity.kpair a b` (Goldblatt §13.2, p. 160). -/
@[simp]
theorem Entity.ktuple_two {X : Type*} (a b : Entity X) :
    Entity.ktuple ![a, b] = Entity.kpair a b := rfl

/-- Goldblatt **Exercise 13.3.1(ii)** (p. 161, iterated tuple form): for every `m : ℕ`,
`(a₁, …, a_m) = (b₁, …, b_m)` **if and only if** `a_i = b_i` for all `i : Fin m`! -/
theorem Entity.ktuple_inj {X : Type*} :
    ∀ {m : ℕ} {v w : Fin m → Entity X}, Entity.ktuple v = Entity.ktuple w ↔ v = w
  | 0, _, _ => by
      simp only [Entity.ktuple, true_iff]
      ext i
      exact Fin.elim0 i
  | 1, _, _ => by
      simp only [Entity.ktuple]
      exact ⟨fun h ↦ funext fun i ↦ by fin_cases i; exact h, fun h ↦ congrFun h 0⟩
  | 2, _, _ => by
      simp only [Entity.ktuple, Entity.kpair_inj]
      constructor
      · rintro ⟨h0, h1⟩
        ext i
        fin_cases i
        · exact h0
        · exact h1
      · rintro rfl
        exact ⟨rfl, rfl⟩
  | _ + 3, _, _ => by
      simp only [Entity.ktuple, Entity.kpair_inj, Entity.ktuple_inj]
      constructor
      · rintro ⟨hinit, hlast⟩
        ext i
        refine Fin.lastCases hlast (fun j ↦ ?_) i
        exact congrFun hinit j
      · rintro rfl
        exact ⟨rfl, rfl⟩

/-- Uniform stage bound for `Entity.ktuple`: if every `v i ∈ VStage X n`, then
`Entity.ktuple v ∈ VStage X (n + 2 * m + 1)` (Goldblatt §13.6, p. 165). -/
theorem Entity.ktuple_mem_vStage {X : Type*} :
    ∀ {m : ℕ} {v : Fin m → Entity X} {n : ℕ},
      (∀ i : Fin m, v i ∈ VStage X n) → Entity.ktuple v ∈ VStage X (n + 2 * m + 1)
  | 0, _, n, _ => by
      have hemp : (∅ : Entity X) ∈ VStage X 1 := mem_vStage_iff_rank_le.2 (by simp)
      exact vStage_mono (by omega) hemp
  | 1, v, n, hv =>
      vStage_mono (by omega) (hv 0)
  | 2, v, n, hv =>
      vStage_mono (by omega) (Entity.kpair_mem_vStage (hv 0) (hv 1))
  | m + 3, v, n, hv => by
      have hinit : Entity.ktuple (Fin.init v) ∈ VStage X (n + 2 * (m + 2) + 1) :=
        Entity.ktuple_mem_vStage fun j ↦ hv j.castSucc
      have hlast : v (Fin.last (m + 2)) ∈ VStage X (n + 2 * (m + 2) + 1) :=
        vStage_mono (by omega) (hv (Fin.last (m + 2)))
      have hk := Entity.kpair_mem_vStage hinit hlast
      exact vStage_mono (by omega) hk

/-- Goldblatt §13.2 (p. 160, indexed function-graph representation): given an injection `ι : ℕ ↪ X`
embedding positive integers `1, …, m` as individuals, the `m`-tuple
`(a₁, …, a_m) = {(1, a₁), …, (m, a_m)}`. -/
def Entity.indexedTuple {X : Type*} (ι : ℕ ↪ X) {m : ℕ} (v : Fin m → Entity X) : Entity X :=
  Entity.finsetEntity (Finset.univ.image fun i : Fin m ↦
    Entity.kpair (Entity.atom (ι (i.val + 1))) (v i))

/-- Goldblatt **Exercise 13.3.1(ii)** (p. 161, indexed tuple form):
`{(1, a₁), …, (m, a_m)} = {(1, b₁), …, (m, b_m)}` **if and only if** `a_i = b_i` for all `i`! -/
theorem Entity.indexedTuple_inj {X : Type*} (ι : ℕ ↪ X) {m : ℕ} {v w : Fin m → Entity X} :
    Entity.indexedTuple ι v = Entity.indexedTuple ι w ↔ v = w := by
  constructor
  · intro h
    ext i
    have hmem : Entity.kpair (Entity.atom (ι (i.val + 1))) (v i) ∈ Entity.indexedTuple ι w := by
      rw [← h, Entity.indexedTuple, Entity.mem_finsetEntity_iff, Finset.mem_image]
      exact ⟨i, Finset.mem_univ i, rfl⟩
    rw [Entity.indexedTuple, Entity.mem_finsetEntity_iff, Finset.mem_image] at hmem
    obtain ⟨j, _, hj⟩ := hmem
    obtain ⟨hidx, hval⟩ := Entity.kpair_inj.1 hj.symm
    have hij : i = j := Fin.ext (Nat.succ_inj.1 (ι.injective (Entity.atom_inj.1 hidx)))
    subst hij
    exact hval
  · rintro rfl
    rfl

/-- Goldblatt §13.1 & §13.3 (pp. 158, 161): Binary Cartesian product `A × B = {(a, b) : a ∈ A, b ∈ B}`
in `Entity X`. -/
def Entity.prod {X : Type*} (A B : Entity X) : Entity X :=
  Entity.setOfBounded {p : Entity X | ∃ a ∈ A, ∃ b ∈ B, p = Entity.kpair a b}

/-- Bounded rank of `A × B` (Goldblatt §13.3, p. 161 & §13.6, p. 165). -/
theorem Entity.isBoundedRank_prod {X : Type*} (A B : Entity X) :
    IsBoundedRank {p : Entity X | ∃ a ∈ A, ∃ b ∈ B, p = Entity.kpair a b} := by
  obtain ⟨m, hm⟩ := A.isBoundedRank_extSet
  obtain ⟨n, hn⟩ := B.isBoundedRank_extSet
  refine ⟨max m n + 2, ?_⟩
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact Entity.kpair_mem_vStage
    (vStage_mono (le_max_left m n) (hm ha))
    (vStage_mono (le_max_right m n) (hn hb))

/-- `Entity.prod A B` is a set entity (Goldblatt §13.3, p. 161). -/
@[simp]
theorem Entity.isSet_prod {X : Type*} (A B : Entity X) : (Entity.prod A B).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.prod A B` (`p ∈ A × B ↔ ∃ a ∈ A, ∃ b ∈ B, p = (a, b)`;
Goldblatt §13.3, p. 161). -/
@[simp]
theorem Entity.mem_prod_iff {X : Type*} {p A B : Entity X} :
    p ∈ Entity.prod A B ↔ ∃ a ∈ A, ∃ b ∈ B, p = Entity.kpair a b :=
  Entity.mem_setOfBounded (Entity.isBoundedRank_prod A B)

/-- Ordered pair membership in `Entity.prod A B`: `(a, b) ∈ A × B ↔ a ∈ A ∧ b ∈ B`
(Goldblatt §13.3, p. 161). -/
@[simp]
theorem Entity.kpair_mem_prod_iff {X : Type*} {a b A B : Entity X} :
    Entity.kpair a b ∈ Entity.prod A B ↔ a ∈ A ∧ b ∈ B := by
  rw [Entity.mem_prod_iff]
  constructor
  · rintro ⟨a', ha', b', hb', heq⟩
    obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 heq
    exact ⟨ha', hb'⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, ha, b, hb, rfl⟩

/-- Goldblatt §13.2 (p. 160): `m`-fold Cartesian product `A₁ × ⋯ × A_m` in `Entity X` using
`Entity.ktuple`. -/
def Entity.prodTuple {X : Type*} {m : ℕ} (A : Fin m → Entity X) : Entity X :=
  Entity.setOfBounded {p : Entity X | ∃ v : Fin m → Entity X, (∀ i, v i ∈ A i) ∧ p = Entity.ktuple v}

/-- Bounded rank of `Entity.prodTuple A` (Goldblatt §13.5, p. 163). -/
theorem Entity.isBoundedRank_prodTuple {X : Type*} {m : ℕ} (A : Fin m → Entity X) :
    IsBoundedRank {p : Entity X | ∃ v : Fin m → Entity X, (∀ i, v i ∈ A i) ∧ p = Entity.ktuple v} := by
  let N : ℕ := Finset.univ.sup fun i : Fin m ↦ (A i).rank
  refine ⟨N + 2 * m + 1, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  refine Entity.ktuple_mem_vStage fun i ↦ ?_
  have h1 : (v i).rank < (A i).rank := Entity.rank_lt_of_mem (hv i)
  have h2 : (A i).rank ≤ N := Finset.le_sup (f := fun j : Fin m ↦ (A j).rank) (Finset.mem_univ i)
  exact mem_vStage_iff_rank_le.2 (by omega)

/-- `Entity.prodTuple A` is a set entity (Goldblatt §13.2, p. 160). -/
@[simp]
theorem Entity.isSet_prodTuple {X : Type*} {m : ℕ} (A : Fin m → Entity X) :
    (Entity.prodTuple A).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.prodTuple A` (Goldblatt §13.2, p. 160). -/
@[simp]
theorem Entity.mem_prodTuple_iff {X : Type*} {m : ℕ} {A : Fin m → Entity X} {p : Entity X} :
    p ∈ Entity.prodTuple A ↔
      ∃ v : Fin m → Entity X, (∀ i, v i ∈ A i) ∧ p = Entity.ktuple v :=
  Entity.mem_setOfBounded (Entity.isBoundedRank_prodTuple A)

/-- Tuple membership in `Entity.prodTuple A` (Goldblatt §13.2, p. 160). -/
@[simp]
theorem Entity.ktuple_mem_prodTuple_iff {X : Type*} {m : ℕ} {A : Fin m → Entity X}
    {v : Fin m → Entity X} :
    Entity.ktuple v ∈ Entity.prodTuple A ↔ ∀ i, v i ∈ A i := by
  rw [Entity.mem_prodTuple_iff]
  constructor
  · rintro ⟨w, hw, heq⟩
    obtain rfl := Entity.ktuple_inj.1 heq
    exact hw
  · exact fun hv ↦ ⟨v, hv, rfl⟩

/-- Goldblatt §13.2 (p. 160): `R` is an `m`-ary relation in `Entity X` if `R` is a set of
`m`-tuples (`m ≥ 2`). -/
def Entity.IsRelArity {X : Type*} (m : ℕ) (R : Entity X) : Prop :=
  R.IsSet ∧ ∀ p ∈ R, ∃ v : Fin m → Entity X, p = Entity.ktuple v

/-- Goldblatt §13.1 & §13.5 (pp. 159, 163): `R` is a binary relation in `Entity X` if `R` is a set
of Kuratowski ordered pairs. -/
def Entity.IsBinaryRel {X : Type*} (R : Entity X) : Prop :=
  R.IsSet ∧ ∀ p ∈ R, ∃ a b : Entity X, p = Entity.kpair a b

/-- Coordinate rank bound for Kuratowski pairs inside an entity `R`: if `(a, b) ∈ R`, then
`a.rank < R.rank` and `b.rank < R.rank` (Goldblatt §13.4, p. 161: `a ∈ {a} ∈ (a, b) ∈ R`). -/
theorem Entity.rank_lt_of_kpair_mem {X : Type*} {a b R : Entity X}
    (hp : Entity.kpair a b ∈ R) :
    a.rank < R.rank ∧ b.rank < R.rank := by
  have hpR : (Entity.kpair a b).rank < R.rank := Entity.rank_lt_of_mem hp
  have hab_in : Entity.upair a b ∈ Entity.kpair a b := Entity.mem_upair_iff.2 (Or.inr rfl)
  have hu : (Entity.upair a b).rank < (Entity.kpair a b).rank := Entity.rank_lt_of_mem hab_in
  have ha : a.rank < (Entity.upair a b).rank :=
    Entity.rank_lt_of_mem (Entity.mem_upair_iff.2 (Or.inl rfl))
  have hb : b.rank < (Entity.upair a b).rank :=
    Entity.rank_lt_of_mem (Entity.mem_upair_iff.2 (Or.inr rfl))
  exact ⟨by omega, by omega⟩

/-- Goldblatt §13.5 (p. 163): Domain `dom R = {a : ∃ b, (a, b) ∈ R}` of a binary relation `R`. -/
def Entity.relDom {X : Type*} (R : Entity X) : Entity X :=
  Entity.setOfBounded {a : Entity X | ∃ b : Entity X, Entity.kpair a b ∈ R}

/-- Bounded rank of `dom R` (Goldblatt §13.4–13.5, pp. 161–163). -/
theorem Entity.isBoundedRank_relDom {X : Type*} (R : Entity X) :
    IsBoundedRank {a : Entity X | ∃ b : Entity X, Entity.kpair a b ∈ R} :=
  ⟨R.rank, fun _ ⟨_, hp⟩ ↦ mem_vStage_iff_rank_le.2 (Entity.rank_lt_of_kpair_mem hp).1.le⟩

/-- `Entity.relDom R` is a set entity (Goldblatt §13.5, p. 163). -/
@[simp]
theorem Entity.isSet_relDom {X : Type*} (R : Entity X) : (Entity.relDom R).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.relDom R` (`a ∈ dom R ↔ ∃ b, (a, b) ∈ R`; Goldblatt §13.5, p. 163). -/
@[simp]
theorem Entity.mem_relDom_iff {X : Type*} {a R : Entity X} :
    a ∈ Entity.relDom R ↔ ∃ b : Entity X, Entity.kpair a b ∈ R :=
  Entity.mem_setOfBounded (Entity.isBoundedRank_relDom R)

/-- Goldblatt §13.5 (p. 163): Range `ran R = {b : ∃ a, (a, b) ∈ R}` of a binary relation `R`. -/
def Entity.relRan {X : Type*} (R : Entity X) : Entity X :=
  Entity.setOfBounded {b : Entity X | ∃ a : Entity X, Entity.kpair a b ∈ R}

/-- Bounded rank of `ran R` (Goldblatt §13.5, p. 163). -/
theorem Entity.isBoundedRank_relRan {X : Type*} (R : Entity X) :
    IsBoundedRank {b : Entity X | ∃ a : Entity X, Entity.kpair a b ∈ R} :=
  ⟨R.rank, fun _ ⟨_, hp⟩ ↦ mem_vStage_iff_rank_le.2 (Entity.rank_lt_of_kpair_mem hp).2.le⟩

/-- `Entity.relRan R` is a set entity (Goldblatt §13.5, p. 163). -/
@[simp]
theorem Entity.isSet_relRan {X : Type*} (R : Entity X) : (Entity.relRan R).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.relRan R` (`b ∈ ran R ↔ ∃ a, (a, b) ∈ R`; Goldblatt §13.5, p. 163). -/
@[simp]
theorem Entity.mem_relRan_iff {X : Type*} {b R : Entity X} :
    b ∈ Entity.relRan R ↔ ∃ a : Entity X, Entity.kpair a b ∈ R :=
  Entity.mem_setOfBounded (Entity.isBoundedRank_relRan R)

/-- Goldblatt §13.5 (p. 164): Relational image `R''(C) = {b : ∃ a ∈ C, (a, b) ∈ R}`. -/
def Entity.relImage {X : Type*} (R C : Entity X) : Entity X :=
  Entity.setOfBounded {b : Entity X | ∃ a ∈ C, Entity.kpair a b ∈ R}

/-- `Entity.relImage R C` is a set entity (Goldblatt §13.5, p. 164). -/
@[simp]
theorem Entity.isSet_relImage {X : Type*} (R C : Entity X) : (Entity.relImage R C).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.relImage R C` (`b ∈ R''(C) ↔ ∃ a ∈ C, (a, b) ∈ R`;
Goldblatt §13.5, p. 164). -/
@[simp]
theorem Entity.mem_relImage_iff {X : Type*} {b R C : Entity X} :
    b ∈ Entity.relImage R C ↔ ∃ a ∈ C, Entity.kpair a b ∈ R :=
  Entity.mem_setOfBounded ((Entity.isBoundedRank_relRan R).subset (by rintro _ ⟨a, _, hp⟩; exact ⟨a, hp⟩))

/-- Goldblatt §13.5 & §13.8 (pp. 164, 169): Relational preimage
`R⁻¹(D) = {a : ∃ b ∈ D, (a, b) ∈ R}`. -/
def Entity.relPreimage {X : Type*} (R D : Entity X) : Entity X :=
  Entity.setOfBounded {a : Entity X | ∃ b ∈ D, Entity.kpair a b ∈ R}

/-- `Entity.relPreimage R D` is a set entity (Goldblatt §13.5, p. 164). -/
@[simp]
theorem Entity.isSet_relPreimage {X : Type*} (R D : Entity X) :
    (Entity.relPreimage R D).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.relPreimage R D` (`a ∈ R⁻¹(D) ↔ ∃ b ∈ D, (a, b) ∈ R`;
Goldblatt §13.5 & §13.8, pp. 164, 169). -/
@[simp]
theorem Entity.mem_relPreimage_iff {X : Type*} {a R D : Entity X} :
    a ∈ Entity.relPreimage R D ↔ ∃ b ∈ D, Entity.kpair a b ∈ R :=
  Entity.mem_setOfBounded ((Entity.isBoundedRank_relDom R).subset (by rintro _ ⟨b, _, hp⟩; exact ⟨b, hp⟩))

/-- Goldblatt §13.5 (p. 164): Converse/inverse relation `R⁻¹ = {(b, a) : (a, b) ∈ R}`. -/
def Entity.relInv {X : Type*} (R : Entity X) : Entity X :=
  Entity.setOfBounded {p : Entity X | ∃ a b : Entity X, Entity.kpair a b ∈ R ∧ p = Entity.kpair b a}

/-- Bounded rank of `R⁻¹` (Goldblatt §13.5, p. 164). -/
theorem Entity.isBoundedRank_relInv {X : Type*} (R : Entity X) :
    IsBoundedRank {p : Entity X | ∃ a b : Entity X, Entity.kpair a b ∈ R ∧ p = Entity.kpair b a} :=
  (Entity.isBoundedRank_prod (Entity.relRan R) (Entity.relDom R)).subset fun _ ⟨a, b, hp, heq⟩ ↦
    ⟨b, Entity.mem_relRan_iff.2 ⟨a, hp⟩, a, Entity.mem_relDom_iff.2 ⟨b, hp⟩, heq⟩

/-- `Entity.relInv R` is a set entity (Goldblatt §13.5, p. 164). -/
@[simp]
theorem Entity.isSet_relInv {X : Type*} (R : Entity X) : (Entity.relInv R).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.relInv R` (Goldblatt §13.5, p. 164). -/
@[simp]
theorem Entity.mem_relInv_iff {X : Type*} {p R : Entity X} :
    p ∈ Entity.relInv R ↔ ∃ a b : Entity X, Entity.kpair a b ∈ R ∧ p = Entity.kpair b a :=
  Entity.mem_setOfBounded (Entity.isBoundedRank_relInv R)

/-- Pair membership in `Entity.relInv R`: `(b, a) ∈ R⁻¹ ↔ (a, b) ∈ R` (Goldblatt §13.5, p. 164). -/
@[simp]
theorem Entity.kpair_mem_relInv_iff {X : Type*} {a b R : Entity X} :
    Entity.kpair b a ∈ Entity.relInv R ↔ Entity.kpair a b ∈ R := by
  rw [Entity.mem_relInv_iff]
  constructor
  · rintro ⟨a', b', hp, heq⟩
    obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 heq
    exact hp
  · exact fun hp ↦ ⟨a, b, hp, rfl⟩

/-- Goldblatt §13.5 (p. 164): Composition of binary relations
`R ∘ S = {(a, c) : ∃ b, (a, b) ∈ R ∧ (b, c) ∈ S}` (using Goldblatt's diagrammatic order on p. 164). -/
def Entity.relComp {X : Type*} (R S : Entity X) : Entity X :=
  Entity.setOfBounded {p : Entity X |
    ∃ a b c : Entity X, Entity.kpair a b ∈ R ∧ Entity.kpair b c ∈ S ∧ p = Entity.kpair a c}

/-- Bounded rank of `R ∘ S` (Goldblatt §13.5, p. 164). -/
theorem Entity.isBoundedRank_relComp {X : Type*} (R S : Entity X) :
    IsBoundedRank {p : Entity X |
      ∃ a b c : Entity X, Entity.kpair a b ∈ R ∧ Entity.kpair b c ∈ S ∧ p = Entity.kpair a c} :=
  (Entity.isBoundedRank_prod (Entity.relDom R) (Entity.relRan S)).subset
    fun _ ⟨a, b, c, hpR, hpS, heq⟩ ↦
      ⟨a, Entity.mem_relDom_iff.2 ⟨b, hpR⟩, c, Entity.mem_relRan_iff.2 ⟨b, hpS⟩, heq⟩

/-- `Entity.relComp R S` is a set entity (Goldblatt §13.5, p. 164). -/
@[simp]
theorem Entity.isSet_relComp {X : Type*} (R S : Entity X) : (Entity.relComp R S).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.relComp R S` (Goldblatt §13.5, p. 164). -/
@[simp]
theorem Entity.mem_relComp_iff {X : Type*} {p R S : Entity X} :
    p ∈ Entity.relComp R S ↔
      ∃ a b c : Entity X, Entity.kpair a b ∈ R ∧ Entity.kpair b c ∈ S ∧ p = Entity.kpair a c :=
  Entity.mem_setOfBounded (Entity.isBoundedRank_relComp R S)

/-- Pair membership in `Entity.relComp R S` (Goldblatt §13.5, p. 164). -/
@[simp]
theorem Entity.kpair_mem_relComp_iff {X : Type*} {a c R S : Entity X} :
    Entity.kpair a c ∈ Entity.relComp R S ↔
      ∃ b : Entity X, Entity.kpair a b ∈ R ∧ Entity.kpair b c ∈ S := by
  rw [Entity.mem_relComp_iff]
  constructor
  · rintro ⟨a', b', c', hR, hS, heq⟩
    obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 heq
    exact ⟨b', hR, hS⟩
  · rintro ⟨b, hR, hS⟩
    exact ⟨a, b, c, hR, hS, rfl⟩

/-- Goldblatt §13.2 (p. 160): Set-theoretic functionality predicate: `f` is a binary relation
such that `(a, b) ∈ f ∧ (a, c) ∈ f → b = c`. -/
def Entity.IsFuncEntity {X : Type*} (f : Entity X) : Prop :=
  f.IsBinaryRel ∧ ∀ a b c : Entity X, Entity.kpair a b ∈ f → Entity.kpair a c ∈ f → b = c

/-- Goldblatt §13.2 (p. 160): Set-theoretic function `f : A → B` between entities `A` and `B`,
matching Goldblatt's clauses (i)–(iii) verbatim:
(i) every member of `f` is `(a, b)` with `a ∈ A` and `b ∈ B`;
(ii) `(a, b), (a, c) ∈ f → b = c`;
(iii) `∀ a ∈ A, ∃ b ∈ B, (a, b) ∈ f`. -/
def Entity.IsFuncFromTo {X : Type*} (f A B : Entity X) : Prop :=
  f.IsSet ∧
  (∀ p ∈ f, ∃ a ∈ A, ∃ b ∈ B, p = Entity.kpair a b) ∧
  (∀ a b c : Entity X, Entity.kpair a b ∈ f → Entity.kpair a c ∈ f → b = c) ∧
  (∀ a ∈ A, ∃ b ∈ B, Entity.kpair a b ∈ f)

/-- Every `f` satisfying `IsFuncFromTo f A B` is a function entity (`IsFuncEntity f`)
(Goldblatt §13.2, p. 160). -/
theorem Entity.IsFuncFromTo.isFuncEntity {X : Type*} {f A B : Entity X}
    (hf : Entity.IsFuncFromTo f A B) : Entity.IsFuncEntity f :=
  ⟨⟨hf.1, fun p hp ↦ let ⟨a, _, b, _, heq⟩ := hf.2.1 p hp; ⟨a, b, heq⟩⟩, hf.2.2.1⟩

/-- Domain of `f` when `IsFuncFromTo f A B` and `A` is a set: `relDom f = A`
(Goldblatt §13.2, p. 160). -/
theorem Entity.IsFuncFromTo.relDom_eq {X : Type*} {f A B : Entity X}
    (hf : Entity.IsFuncFromTo f A B) (hA : A.IsSet) :
    Entity.relDom f = A := by
  refine Entity.set_ext (Entity.isSet_relDom f) hA fun a ↦ ?_
  rw [Entity.mem_relDom_iff]
  constructor
  · rintro ⟨b, hp⟩
    obtain ⟨a', ha', b', _, heq⟩ := hf.2.1 _ hp
    obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 heq
    exact ha'
  · intro ha
    obtain ⟨b, _, hp⟩ := hf.2.2.2 a ha
    exact ⟨b, hp⟩

/-- Every value in `relRan f` belongs to `B` when `IsFuncFromTo f A B`
(Goldblatt §13.2, p. 160). -/
theorem Entity.IsFuncFromTo.mem_of_mem_relRan {X : Type*} {f A B b : Entity X}
    (hf : Entity.IsFuncFromTo f A B) (hb : b ∈ Entity.relRan f) :
    b ∈ B := by
  obtain ⟨a, hp⟩ := Entity.mem_relRan_iff.1 hb
  obtain ⟨a', _, b', hb', heq⟩ := hf.2.1 _ hp
  obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 heq
  exact hb'

/-- Evaluation `Entity.funcApp f a` of a function entity `f` at `a` (returning the unique `b`
with `(a, b) ∈ f` when `f` is a function and `a ∈ dom f`, and `∅` otherwise;
Goldblatt §13.7, p. 166). -/
def Entity.funcApp {X : Type*} (f a : Entity X) : Entity X :=
  if h : ∃ b : Entity X, Entity.kpair a b ∈ f then h.choose else ∅

/-- Fundamental characterization of `Entity.funcApp`: when `IsFuncEntity f` and `a ∈ relDom f`,
`(a, funcApp f a) ∈ f` (Goldblatt §13.2 & §13.7, pp. 160, 166). -/
theorem Entity.kpair_funcApp_mem {X : Type*} {f a : Entity X}
    (ha : a ∈ Entity.relDom f) :
    Entity.kpair a (Entity.funcApp f a) ∈ f := by
  have hex : ∃ b : Entity X, Entity.kpair a b ∈ f := Entity.mem_relDom_iff.1 ha
  simpa only [Entity.funcApp, hex, ↓reduceDIte] using hex.choose_spec

/-- Uniqueness of `Entity.funcApp`: when `IsFuncEntity f`, `(a, b) ∈ f ↔ a ∈ relDom f ∧ funcApp f a = b`
(Goldblatt §13.2 & §13.7, pp. 160, 166). -/
theorem Entity.kpair_mem_iff_funcApp_eq {X : Type*} {f a b : Entity X}
    (hf : Entity.IsFuncEntity f) :
    Entity.kpair a b ∈ f ↔ a ∈ Entity.relDom f ∧ Entity.funcApp f a = b := by
  constructor
  · intro hp
    have ha : a ∈ Entity.relDom f := Entity.mem_relDom_iff.2 ⟨b, hp⟩
    exact ⟨ha, hf.2 a _ b (Entity.kpair_funcApp_mem ha) hp⟩
  · rintro ⟨ha, rfl⟩
    exact Entity.kpair_funcApp_mem ha

/-- Construct a function entity `mkFuncEntity A g` with domain `A.extSet` from any Lean function
`g : Entity X → Entity X` whose values on `A.extSet` have bounded rank (Goldblatt §13.5, p. 164). -/
def Entity.mkFuncEntity {X : Type*} (A : Entity X) (g : Entity X → Entity X) : Entity X :=
  Entity.setOfBounded {p : Entity X | ∃ a ∈ A, p = Entity.kpair a (g a)}

/-- If `g '' A.extSet ⊆ B.extSet`, then `Entity.mkFuncEntity A g` satisfies
`IsFuncFromTo (mkFuncEntity A g) A B` (Goldblatt §13.5, p. 164). -/
theorem Entity.isFuncFromTo_mkFuncEntity {X : Type*} {A B : Entity X} {g : Entity X → Entity X}
    (hg : ∀ a ∈ A, g a ∈ B) :
    Entity.IsFuncFromTo (Entity.mkFuncEntity A g) A B := by
  have hbdd : IsBoundedRank {p : Entity X | ∃ a ∈ A, p = Entity.kpair a (g a)} :=
    (Entity.isBoundedRank_prod A B).subset fun _ ⟨a, ha, heq⟩ ↦ ⟨a, ha, g a, hg a ha, heq⟩
  refine ⟨Entity.isSet_setOfBounded _, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := (Entity.mem_setOfBounded hbdd).1 hp
    exact ⟨a, ha, g a, hg a ha, rfl⟩
  · intro a b c hb hc
    obtain ⟨a₁, _, h1⟩ := (Entity.mem_setOfBounded hbdd).1 hb
    obtain ⟨a₂, _, h2⟩ := (Entity.mem_setOfBounded hbdd).1 hc
    obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 h1
    obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 h2
    rfl
  · intro a ha
    exact ⟨g a, hg a ha, (Entity.mem_setOfBounded hbdd).2 ⟨a, ha, rfl⟩⟩

/-- Evaluation of `Entity.mkFuncEntity A g` on `a ∈ A` (Goldblatt §13.5, p. 164). -/
theorem Entity.funcApp_mkFuncEntity {X : Type*} {A B : Entity X} {g : Entity X → Entity X}
    (hg : ∀ a ∈ A, g a ∈ B) {a : Entity X} (ha : a ∈ A) :
    Entity.funcApp (Entity.mkFuncEntity A g) a = g a := by
  have hbdd : IsBoundedRank {p : Entity X | ∃ a ∈ A, p = Entity.kpair a (g a)} :=
    (Entity.isBoundedRank_prod A B).subset fun _ ⟨x, hx, heq⟩ ↦ ⟨x, hx, g x, hg x hx, heq⟩
  have hf := (Entity.isFuncFromTo_mkFuncEntity hg).isFuncEntity
  have hp : Entity.kpair a (g a) ∈ Entity.mkFuncEntity A g :=
    (Entity.mem_setOfBounded hbdd).2 ⟨a, ha, rfl⟩
  exact ((Entity.kpair_mem_iff_funcApp_eq hf).1 hp).2

/-- Injectivity of a function entity `f` (`(a₁, b) ∈ f ∧ (a₂, b) ∈ f → a₁ = a₂`;
Goldblatt §13.8, p. 169). -/
def Entity.IsInjectiveFunc {X : Type*} (f : Entity X) : Prop :=
  f.IsFuncEntity ∧ ∀ a₁ a₂ b : Entity X,
    Entity.kpair a₁ b ∈ f → Entity.kpair a₂ b ∈ f → a₁ = a₂

/-- Surjectivity of `f : A → B` onto `B` (Goldblatt §13.8, p. 169). -/
def Entity.IsSurjectiveFromTo {X : Type*} (f A B : Entity X) : Prop :=
  Entity.IsFuncFromTo f A B ∧ ∀ b ∈ B, ∃ a ∈ A, Entity.kpair a b ∈ f

/-- Bijectivity of `f : A → B` between `A` and `B` (Goldblatt §13.13 & §13.17, pp. 176, 179). -/
def Entity.IsBijectiveFromTo {X : Type*} (f A B : Entity X) : Prop :=
  Entity.IsSurjectiveFromTo f A B ∧ f.IsInjectiveFunc

/-- Goldblatt §13.1 & §13.5 (pp. 158, 164): Function space `B^A` of all set-theoretic functions
from `A` to `B`. -/
def Entity.funSpace {X : Type*} (A B : Entity X) : Entity X :=
  Entity.setOfBounded {f : Entity X | Entity.IsFuncFromTo f A B}

/-- Bounded rank of `B^A` (every `f : A → B` is a subset of `A × B`;
Goldblatt §13.5–13.6, pp. 164–165). -/
theorem Entity.isBoundedRank_funSpace {X : Type*} (A B : Entity X) :
    IsBoundedRank {f : Entity X | Entity.IsFuncFromTo f A B} :=
  (Entity.isBoundedRank_powerset (Entity.prod A B)).subset fun _ hf ↦
    ⟨hf.1, fun p hp ↦
      let ⟨a, ha, b, hb, heq⟩ := hf.2.1 p hp
      Entity.mem_prod_iff.2 ⟨a, ha, b, hb, heq⟩⟩

/-- `Entity.funSpace A B` is a set entity (Goldblatt §13.5, p. 164). -/
@[simp]
theorem Entity.isSet_funSpace {X : Type*} (A B : Entity X) : (Entity.funSpace A B).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `Entity.funSpace A B` (`f ∈ B^A ↔ IsFuncFromTo f A B`;
Goldblatt §13.5, p. 164). -/
@[simp]
theorem Entity.mem_funSpace_iff {X : Type*} {f A B : Entity X} :
    f ∈ Entity.funSpace A B ↔ Entity.IsFuncFromTo f A B :=
  Entity.mem_setOfBounded (Entity.isBoundedRank_funSpace A B)

/-- Goldblatt §13.5 (p. 164): Indexed Cartesian product `∏_{i ∈ I} A_i`, given an index entity `I`
and an indexed family represented by a function entity `fam` with domain `I` (`i ↦ A_i`). -/
def Entity.piSpace {X : Type*} (I fam : Entity X) : Entity X :=
  Entity.setOfBounded {f : Entity X |
    f ∈ Entity.funSpace I (Entity.sUnion (Entity.relRan fam)) ∧
    ∀ i ∈ I, ∀ Ai : Entity X, Entity.kpair i Ai ∈ fam → Entity.funcApp f i ∈ Ai}

/-- `Entity.piSpace I fam` is a set entity with clean membership characterization
(Goldblatt §13.5, p. 164). -/
@[simp]
theorem Entity.mem_piSpace_iff {X : Type*} {f I fam : Entity X} :
    f ∈ Entity.piSpace I fam ↔
      f ∈ Entity.funSpace I (Entity.sUnion (Entity.relRan fam)) ∧
      ∀ i ∈ I, ∀ Ai : Entity X, Entity.kpair i Ai ∈ fam → Entity.funcApp f i ∈ Ai :=
  Entity.mem_setOfBounded
    ((Entity.sUnion (Entity.relRan fam) |> Entity.funSpace I).isBoundedRank_extSet.subset
      fun _ hf ↦ hf.1)

/-! ## §13.4–13.5 Transitivity, Strong Transitivity, Universes, and Closure Properties -/

/-- Goldblatt §13.1, §13.4 & §13.8 (pp. 159, 162, 169): A set entity `T : Entity X` is
**transitive** if `∀ x ∈ T, ∀ y ∈ x, y ∈ T`. -/
def Entity.IsTransitiveSet {X : Type*} (T : Entity X) : Prop :=
  T.IsSet ∧ ∀ x ∈ T, ∀ y ∈ x, y ∈ T

/-- Goldblatt §13.6 Property (3) (p. 165): Every positive cumulative stage `vStageEntity X (n + 1)`
(`𝕌_{n+1}(X)`) is a **transitive** set! -/
theorem isTransitiveSet_vStageEntity_succ (X : Type*) (n : ℕ) :
    (vStageEntity X (n + 1)).IsTransitiveSet := by
  refine ⟨isSet_vStageEntity X (n + 1), fun x hx y hy ↦ ?_⟩
  rw [mem_vStageEntity] at hx ⊢
  exact vStage_mono (Nat.le_succ n) (mem_vStage_of_mem_vStage_succ hy hx)

/-- Goldblatt §13.1 (p. 159): A collection `U : Set (Entity X)` of entities is **transitive** if
`a ∈ A` and `A ∈ U` imply `a ∈ U`. -/
def IsTransitiveCollection {X : Type*} (U : Set (Entity X)) : Prop :=
  ∀ ⦃a A : Entity X⦄, a ∈ A → A ∈ U → a ∈ U

/-- Goldblatt §13.4 (p. 162): A collection `U : Set (Entity X)` is **strongly transitive** if for
every set `A ∈ U`, there exists a transitive set `B ∈ U` with `A ⊆ B ⊆ U`. -/
def IsStronglyTransitive {X : Type*} (U : Set (Entity X)) : Prop :=
  ∀ ⦃A : Entity X⦄, A ∈ U → A.IsSet →
    ∃ B ∈ U, B.IsTransitiveSet ∧ A.extSet ⊆ B.extSet ∧ B.extSet ⊆ U

/-- Goldblatt §13.4 (p. 162): Strong transitivity implies transitivity (`a ∈ A ∈ U → a ∈ U`). -/
theorem IsStronglyTransitive.isTransitiveCollection {X : Type*} {U : Set (Entity X)}
    (hU : IsStronglyTransitive U) : IsTransitiveCollection U := by
  intro a A haA hAU
  obtain ⟨B, _, _, hAB, hBU⟩ := hU hAU (Entity.isSet_of_mem haA)
  exact hBU (hAB haA)

/-- Goldblatt §13.5 (pp. 162–163): A **universe** `U : Set (Entity X)` is a strongly transitive
collection containing at least one set and closed under unordered pairs `{a, b}`, binary unions of
sets `A ∪ B`, and power sets of sets `𝒫(A)`. -/
structure IsUniverse {X : Type*} (U : Set (Entity X)) : Prop where
  /-- Strong transitivity (§13.4, p. 162). -/
  stronglyTransitive : IsStronglyTransitive U
  /-- Contains at least one set (§13.5, p. 163). -/
  exists_set : ∃ A ∈ U, A.IsSet
  /-- Closure under unordered pairs `{a, b}` (§13.5, p. 162). -/
  upair_mem : ∀ ⦃a b : Entity X⦄, a ∈ U → b ∈ U → Entity.upair a b ∈ U
  /-- Closure under binary unions of sets (§13.5, p. 162). -/
  union_mem : ∀ ⦃A B : Entity X⦄, A ∈ U → B ∈ U → A.IsSet → B.IsSet → Entity.union A B ∈ U
  /-- Closure under power sets of sets (§13.5, p. 162). -/
  powerset_mem : ∀ ⦃A : Entity X⦄, A ∈ U → A.IsSet → Entity.powerset A ∈ U

/-- Goldblatt §13.5 (p. 162): `U` is a **universe over `X₀`** if `U` is a universe, `X₀ ∈ U` is a
set, and every member of `X₀` is an individual (`x ≠ ∅ ∧ ∀ y ∈ U, y ∉ x`). -/
structure IsUniverseOver {X : Type*} (U : Set (Entity X)) (X₀ : Entity X) : Prop extends
    IsUniverse U where
  /-- The base set `X₀` belongs to `U`. -/
  base_mem : X₀ ∈ U
  /-- `X₀` is a set entity. -/
  base_isSet : X₀.IsSet
  /-- Members of `X₀` are individuals with no members in `U` (Goldblatt §13.5, p. 162). -/
  individuals_spec : ∀ x ∈ X₀, x ≠ ∅ ∧ ∀ y ∈ U, y ∉ x

/-- Goldblatt §13.1 & §13.5 (pp. 159, 163): Every universe is transitive (`a ∈ A ∈ U → a ∈ U`). -/
theorem IsUniverse.mem_of_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {a A : Entity X} (haA : a ∈ A) (hAU : A ∈ U) : a ∈ U :=
  hU.stronglyTransitive.isTransitiveCollection haA hAU

/-- Goldblatt §13.1 & §13.5 (pp. 159, 163, **Subset Closure**): If `A` and `B` are sets with
`A ⊆ B` and `B ∈ U`, then `A ∈ U` (`A ∈ 𝒫(B) ∈ U`). -/
theorem IsUniverse.subset_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {A B : Entity X} (hA : A.IsSet) (hB : B.IsSet) (hAB : A.extSet ⊆ B.extSet) (hBU : B ∈ U) :
    A ∈ U :=
  hU.mem_of_mem (Entity.mem_powerset_iff.2 ⟨hA, hAB⟩) (hU.powerset_mem hBU hB)

/-- Goldblatt §13.5 (p. 163): `∅ ∈ U` for every universe `U`. -/
theorem IsUniverse.empty_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U) :
    (∅ : Entity X) ∈ U := by
  obtain ⟨A, hAU, hAs⟩ := hU.exists_set
  exact hU.subset_mem Entity.isSet_empty hAs
    (fun z hz ↦ (Entity.not_mem_empty z hz).elim) hAU

/-- Goldblatt §13.5 (p. 163): If `a ∈ U`, then `{a} ∈ U`. -/
theorem IsUniverse.singleton_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {a : Entity X} (ha : a ∈ U) : Entity.singleton a ∈ U :=
  hU.upair_mem ha ha

/-- Goldblatt §13.5 (p. 163): Every universe contains all of its finite subsets (`finsetEntity S ∈ U`
whenever `↑S ⊆ U`). -/
theorem IsUniverse.finsetEntity_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {S : Finset (Entity X)} (hS : ∀ a ∈ S, a ∈ U) :
    Entity.finsetEntity S ∈ U := by
  induction S using Finset.cons_induction with
  | empty =>
      have hemp : Entity.finsetEntity (∅ : Finset (Entity X)) = ∅ :=
        Entity.set_ext (Entity.isSet_finsetEntity _) Entity.isSet_empty fun z ↦ by simp
      rw [hemp]
      exact hU.empty_mem
  | cons a t hat ih =>
      have heq : Entity.finsetEntity (Finset.cons a t hat) =
          Entity.union (Entity.singleton a) (Entity.finsetEntity t) := by
        refine Entity.set_ext (Entity.isSet_finsetEntity _) (Entity.isSet_union _ _) fun z ↦ ?_
        simp
      rw [heq]
      exact hU.union_mem
        (hU.singleton_mem (hS a (Finset.mem_cons_self a t)))
        (ih fun b hb ↦ hS b (Finset.mem_cons_of_mem hb))
        (Entity.isSet_singleton a)
        (Entity.isSet_finsetEntity t)

/-- Goldblatt §13.5 (p. 163): Finite unions `A₁ ∪ ⋯ ∪ A_m ∈ U` of sets in `U`. -/
theorem IsUniverse.finUnion_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {ι : Type*} (S : Finset ι) {A : ι → Entity X}
    (hA_mem : ∀ i ∈ S, A i ∈ U) (hA_set : ∀ i ∈ S, (A i).IsSet) :
    Entity.sUnion (Entity.finsetEntity (S.image A)) ∈ U := by
  induction S using Finset.cons_induction with
  | empty =>
      have hemp : Entity.sUnion (Entity.finsetEntity ((∅ : Finset ι).image A)) = ∅ :=
        Entity.set_ext (Entity.isSet_sUnion _) Entity.isSet_empty fun z ↦ by simp
      rw [hemp]
      exact hU.empty_mem
  | cons i₀ t hi₀ ih =>
      have heq : Entity.sUnion (Entity.finsetEntity ((Finset.cons i₀ t hi₀).image A)) =
          Entity.union (A i₀) (Entity.sUnion (Entity.finsetEntity (t.image A))) := by
        refine Entity.set_ext (Entity.isSet_sUnion _) (Entity.isSet_union _ _) fun z ↦ ?_
        simp only [Entity.mem_sUnion_iff, Entity.mem_finsetEntity_iff, Finset.mem_image,
          Finset.mem_cons, Entity.mem_union_iff]
        constructor
        · rintro ⟨B, ⟨j, rfl | hj, rfl⟩, hzB⟩
          · exact Or.inl hzB
          · exact Or.inr ⟨A j, ⟨j, hj, rfl⟩, hzB⟩
        · rintro (hz0 | ⟨B, ⟨j, hj, rfl⟩, hzB⟩)
          · exact ⟨A i₀, ⟨i₀, Or.inl rfl, rfl⟩, hz0⟩
          · exact ⟨A j, ⟨j, Or.inr hj, rfl⟩, hzB⟩
      rw [heq]
      exact hU.union_mem
        (hA_mem i₀ (Finset.mem_cons_self i₀ t))
        (ih (fun j hj ↦ hA_mem j (Finset.mem_cons_of_mem hj))
            (fun j hj ↦ hA_set j (Finset.mem_cons_of_mem hj)))
        (hA_set i₀ (Finset.mem_cons_self i₀ t))
        (Entity.isSet_sUnion _)

/-- Goldblatt §13.5 (p. 163): Closure under unions of sets of sets (`⋃ Y ∈ U` when `Y ∈ U`),
proved using **strong transitivity**! -/
theorem IsUniverse.sUnion_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {Y : Entity X} (hYU : Y ∈ U) (hYs : Y.IsSet) :
    Entity.sUnion Y ∈ U := by
  obtain ⟨B, hBU, hBtrans, hYB, _⟩ := hU.stronglyTransitive hYU hYs
  refine hU.subset_mem (Entity.isSet_sUnion Y) hBtrans.1 ?_ hBU
  intro z hz
  obtain ⟨A, hAY, hzA⟩ := Entity.mem_sUnion_iff.1 hz
  exact hBtrans.2 A (hYB hAY) z hzA

/-- Goldblatt §13.5 (p. 163): If `{A_i : i ∈ I} ⊆ A ∈ U` (with `A` a set in `U`), then
`⋃_{i ∈ I} A_i ∈ U` (proved via strong transitivity of `U`). -/
theorem IsUniverse.iUnion_mem_of_subset {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {ι : Type*} {fam : ι → Entity X} {A : Entity X} (hAU : A ∈ U) (hAs : A.IsSet)
    (hfam : ∀ i : ι, fam i ∈ A) :
    Entity.setOfBounded {z : Entity X | ∃ i : ι, z ∈ fam i} ∈ U := by
  obtain ⟨B, hBU, hBtrans, hAB, _⟩ := hU.stronglyTransitive hAU hAs
  have hsub : {z : Entity X | ∃ i : ι, z ∈ fam i} ⊆ B.extSet := by
    rintro z ⟨i, hzi⟩
    exact hBtrans.2 (fam i) (hAB (hfam i)) z hzi
  have hbdd : IsBoundedRank {z : Entity X | ∃ i : ι, z ∈ fam i} :=
    B.isBoundedRank_extSet.subset hsub
  refine hU.subset_mem (Entity.isSet_setOfBounded _) hBtrans.1 ?_ hBU
  intro z hz
  exact hsub ((Entity.mem_setOfBounded hbdd).1 hz)

/-- Goldblatt §13.5 (p. 163): Closure under arbitrary nonempty intersections: if `{A_i : i ∈ I} ⊆ U`
with `I` nonempty, then `⋂_{i ∈ I} A_i ∈ U` whether or not `{A_i : i ∈ I}` itself belongs to `U`! -/
theorem IsUniverse.iInter_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {ι : Type*} [Nonempty ι] {fam : ι → Entity X}
    (hfamU : ∀ i : ι, fam i ∈ U) (hfamSet : ∀ i : ι, (fam i).IsSet) :
    Entity.setOfBounded {z : Entity X | ∀ i : ι, z ∈ fam i} ∈ U := by
  let i₀ : ι := Classical.arbitrary ι
  have hsub : {z : Entity X | ∀ i : ι, z ∈ fam i} ⊆ (fam i₀).extSet := fun z hz ↦ hz i₀
  have hbdd : IsBoundedRank {z : Entity X | ∀ i : ι, z ∈ fam i} :=
    (fam i₀).isBoundedRank_extSet.subset hsub
  refine hU.subset_mem (Entity.isSet_setOfBounded _) (hfamSet i₀) ?_ (hfamU i₀)
  intro z hz
  exact hsub ((Entity.mem_setOfBounded hbdd).1 hz)

/-- Goldblatt §13.5 (p. 163): If `a, b ∈ U`, then `(a, b) ∈ U`. -/
theorem IsUniverse.kpair_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {a b : Entity X} (ha : a ∈ U) (hb : b ∈ U) : Entity.kpair a b ∈ U :=
  hU.upair_mem (hU.singleton_mem ha) (hU.upair_mem ha hb)

/-- Goldblatt §13.3 & §13.5 (pp. 161, 163, **Product Closure**): If `A, B ∈ U` are sets, then
`A × B ∈ U` (`A × B ⊆ 𝒫(𝒫(A ∪ B))`, so `A × B ∈ 𝒫(𝒫(𝒫(A ∪ B))) ∈ U`). -/
theorem IsUniverse.prod_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {A B : Entity X} (hAU : A ∈ U) (hBU : B ∈ U) (hAs : A.IsSet) (hBs : B.IsSet) :
    Entity.prod A B ∈ U := by
  have hAB : Entity.union A B ∈ U := hU.union_mem hAU hBU hAs hBs
  have hP1 : Entity.powerset (Entity.union A B) ∈ U :=
    hU.powerset_mem hAB (Entity.isSet_union A B)
  have hP2 : Entity.powerset (Entity.powerset (Entity.union A B)) ∈ U :=
    hU.powerset_mem hP1 (Entity.isSet_powerset _)
  refine hU.subset_mem (Entity.isSet_prod A B) (Entity.isSet_powerset _) ?_ hP2
  intro p hp
  obtain ⟨a, ha, b, hb, rfl⟩ := Entity.mem_prod_iff.1 hp
  rw [Entity.mem_extSet, Entity.mem_powerset_iff]
  refine ⟨Entity.isSet_kpair a b, fun u hu ↦ ?_⟩
  rw [Entity.mem_powerset_iff]
  rcases Entity.mem_upair_iff.1 hu with rfl | rfl
  · refine ⟨Entity.isSet_singleton a, fun z hz ↦ ?_⟩
    rw [Entity.mem_singleton_iff.1 hz]
    exact Entity.mem_union_iff.2 (Or.inl ha)
  · refine ⟨Entity.isSet_upair a b, fun z hz ↦ ?_⟩
    rcases Entity.mem_upair_iff.1 hz with rfl | rfl
    · exact Entity.mem_union_iff.2 (Or.inl ha)
    · exact Entity.mem_union_iff.2 (Or.inr hb)

/-- Goldblatt §13.1 & §13.5 (pp. 159, 163, **Relation Closure**): If `A, B ∈ U` are sets and `R`
is a set with `R ⊆ A × B`, then `R ∈ U`. -/
theorem IsUniverse.rel_subset_prod_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {A B R : Entity X} (hAU : A ∈ U) (hBU : B ∈ U) (hAs : A.IsSet) (hBs : B.IsSet)
    (hRs : R.IsSet) (hR : R.extSet ⊆ (Entity.prod A B).extSet) :
    R ∈ U :=
  hU.subset_mem hRs (Entity.isSet_prod A B) hR (hU.prod_mem hAU hBU hAs hBs)

/-- Goldblatt §13.5 (p. 163): If `a₁, …, a_m ∈ U`, then `(a₁, …, a_m) ∈ U`. -/
theorem IsUniverse.ktuple_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U) :
    ∀ {m : ℕ} {v : Fin m → Entity X}, (∀ i, v i ∈ U) → Entity.ktuple v ∈ U
  | 0, _, _ => hU.empty_mem
  | 1, _, hv => hv 0
  | 2, _, hv => hU.kpair_mem (hv 0) (hv 1)
  | _ + 3, _, hv =>
      hU.kpair_mem (hU.ktuple_mem fun j ↦ hv j.castSucc) (hv (Fin.last _))

/-- Goldblatt §13.5 (p. 163): Closure under `m`-fold Cartesian products `A₁ × ⋯ × A_m ∈ U` for sets
`A_i ∈ U`. -/
theorem IsUniverse.prodTuple_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U) :
    ∀ {m : ℕ} {A : Fin m → Entity X},
      (∀ i, A i ∈ U) → (∀ i, (A i).IsSet) → Entity.prodTuple A ∈ U
  | 0, A, _, _ => by
      have heq : Entity.prodTuple A = Entity.singleton ∅ := by
        refine Entity.set_ext (Entity.isSet_prodTuple A) (Entity.isSet_singleton ∅) fun p ↦ ?_
        simp only [Entity.mem_prodTuple_iff, Entity.mem_singleton_iff]
        exact ⟨fun ⟨_, _, hp⟩ ↦ hp, fun hp ↦ ⟨Fin.elim0, fun i ↦ Fin.elim0 i, hp⟩⟩
      rw [heq]
      exact hU.singleton_mem hU.empty_mem
  | 1, A, hAU, hAs => by
      have heq : Entity.prodTuple A = A 0 := by
        refine Entity.set_ext (Entity.isSet_prodTuple A) (hAs 0) fun p ↦ ?_
        simp only [Entity.mem_prodTuple_iff]
        exact ⟨fun ⟨v, hv, hp⟩ ↦ hp ▸ hv 0,
               fun hp ↦ ⟨fun _ ↦ p, fun i ↦ by fin_cases i; exact hp, rfl⟩⟩
      rw [heq]
      exact hAU 0
  | 2, A, hAU, hAs => by
      have heq : Entity.prodTuple A = Entity.prod (A 0) (A 1) := by
        refine Entity.set_ext (Entity.isSet_prodTuple A) (Entity.isSet_prod _ _) fun p ↦ ?_
        simp only [Entity.mem_prodTuple_iff, Entity.mem_prod_iff]
        constructor
        · rintro ⟨v, hv, rfl⟩
          exact ⟨v 0, hv 0, v 1, hv 1, rfl⟩
        · rintro ⟨a, ha, b, hb, rfl⟩
          exact ⟨![a, b], fun i ↦ by fin_cases i <;> assumption, rfl⟩
      rw [heq]
      exact hU.prod_mem (hAU 0) (hAU 1) (hAs 0) (hAs 1)
  | m + 3, A, hAU, hAs => by
      have hinit : Entity.prodTuple (m := m + 2) (Fin.init A) ∈ U :=
        hU.prodTuple_mem (fun j ↦ hAU j.castSucc) (fun j ↦ hAs j.castSucc)
      have hprod : Entity.prod (Entity.prodTuple (Fin.init A)) (A (Fin.last (m + 2))) ∈ U :=
        hU.prod_mem hinit (hAU (Fin.last _)) (Entity.isSet_prodTuple _) (hAs (Fin.last _))
      refine hU.subset_mem (Entity.isSet_prodTuple A) (Entity.isSet_prod _ _) ?_ hprod
      intro p hp
      obtain ⟨v, hv, rfl⟩ := Entity.mem_prodTuple_iff.1 hp
      exact Entity.mem_prod_iff.2
        ⟨Entity.ktuple (Fin.init v),
         Entity.mem_prodTuple_iff.2 ⟨Fin.init v, fun j ↦ hv j.castSucc, rfl⟩,
         v (Fin.last (m + 2)), hv (Fin.last (m + 2)), rfl⟩

/-- Goldblatt §13.5 (p. 163, **Finitary Relation Closure**): If `A₁, …, A_m ∈ U` are sets and
`R ⊆ A₁ × ⋯ × A_m` is a set, then `R ∈ U`. -/
theorem IsUniverse.finitaryRel_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {m : ℕ} {A : Fin m → Entity X} {R : Entity X}
    (hAU : ∀ i, A i ∈ U) (hAs : ∀ i, (A i).IsSet) (hRs : R.IsSet)
    (hR : R.extSet ⊆ (Entity.prodTuple A).extSet) :
    R ∈ U :=
  hU.subset_mem hRs (Entity.isSet_prodTuple A) hR (hU.prodTuple_mem hAU hAs)

/-- Goldblatt §13.4 & §13.5 (pp. 161–163): For any set `R ∈ U`, `dom R ∈ U` (proved via **strong
transitivity**: `a ∈ {a} ∈ (a, b) ∈ R ⊆ B ∈ U`, so `dom R ⊆ B ∈ U`)! -/
theorem IsUniverse.relDom_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {R : Entity X} (hRU : R ∈ U) (hRs : R.IsSet) :
    Entity.relDom R ∈ U := by
  obtain ⟨B, hBU, hBtrans, hRB, _⟩ := hU.stronglyTransitive hRU hRs
  refine hU.subset_mem (Entity.isSet_relDom R) hBtrans.1 ?_ hBU
  intro a ha
  obtain ⟨b, hp⟩ := Entity.mem_relDom_iff.1 ha
  have hpB : Entity.kpair a b ∈ B := hRB hp
  have hsB : Entity.singleton a ∈ B :=
    hBtrans.2 _ hpB _ (Entity.mem_upair_iff.2 (Or.inl rfl))
  exact hBtrans.2 _ hsB a (Entity.mem_singleton_iff.2 rfl)

/-- Goldblatt §13.5 (p. 163): For any set `R ∈ U`, `ran R ∈ U` (via strong transitivity:
`b ∈ {a, b} ∈ (a, b) ∈ R ⊆ B ∈ U`)! -/
theorem IsUniverse.relRan_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {R : Entity X} (hRU : R ∈ U) (hRs : R.IsSet) :
    Entity.relRan R ∈ U := by
  obtain ⟨B, hBU, hBtrans, hRB, _⟩ := hU.stronglyTransitive hRU hRs
  refine hU.subset_mem (Entity.isSet_relRan R) hBtrans.1 ?_ hBU
  intro b hb
  obtain ⟨a, hp⟩ := Entity.mem_relRan_iff.1 hb
  have hpB : Entity.kpair a b ∈ B := hRB hp
  have huB : Entity.upair a b ∈ B :=
    hBtrans.2 _ hpB _ (Entity.mem_upair_iff.2 (Or.inr rfl))
  exact hBtrans.2 _ huB b (Entity.mem_upair_iff.2 (Or.inr rfl))

/-- Goldblatt §13.5 (p. 164): For any set `R ∈ U` and any `C`, `R''(C) ∈ U` (`R''(C) ⊆ ran R ∈ U`). -/
theorem IsUniverse.relImage_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {R : Entity X} (hRU : R ∈ U) (hRs : R.IsSet) (C : Entity X) :
    Entity.relImage R C ∈ U :=
  hU.subset_mem (Entity.isSet_relImage R C) (Entity.isSet_relRan R)
    (fun _ hb ↦ let ⟨a, _, hp⟩ := Entity.mem_relImage_iff.1 hb; Entity.mem_relRan_iff.2 ⟨a, hp⟩)
    (hU.relRan_mem hRU hRs)

/-- Goldblatt §13.5 (p. 164): For any set `R ∈ U` and any `D`, `R⁻¹(D) ∈ U` (`R⁻¹(D) ⊆ dom R ∈ U`). -/
theorem IsUniverse.relPreimage_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {R : Entity X} (hRU : R ∈ U) (hRs : R.IsSet) (D : Entity X) :
    Entity.relPreimage R D ∈ U :=
  hU.subset_mem (Entity.isSet_relPreimage R D) (Entity.isSet_relDom R)
    (fun _ ha ↦ let ⟨b, _, hp⟩ := Entity.mem_relPreimage_iff.1 ha; Entity.mem_relDom_iff.2 ⟨b, hp⟩)
    (hU.relDom_mem hRU hRs)

/-- Goldblatt §13.5 (p. 164): For any set `R ∈ U`, `R⁻¹ ∈ U` (`R⁻¹ ⊆ ran R × dom R ∈ U`). -/
theorem IsUniverse.relInv_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {R : Entity X} (hRU : R ∈ U) (hRs : R.IsSet) :
    Entity.relInv R ∈ U :=
  hU.rel_subset_prod_mem (hU.relRan_mem hRU hRs) (hU.relDom_mem hRU hRs)
    (Entity.isSet_relRan R) (Entity.isSet_relDom R) (Entity.isSet_relInv R)
    fun _ hp ↦
      let ⟨a, b, hab, heq⟩ := Entity.mem_relInv_iff.1 hp
      Entity.mem_prod_iff.2 ⟨b, Entity.mem_relRan_iff.2 ⟨a, hab⟩,
        a, Entity.mem_relDom_iff.2 ⟨b, hab⟩, heq⟩

/-- Goldblatt §13.5 (p. 164): For any sets `R, S ∈ U`, `R ∘ S ∈ U` (`R ∘ S ⊆ dom R × ran S ∈ U`). -/
theorem IsUniverse.relComp_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {R S : Entity X} (hRU : R ∈ U) (hSU : S ∈ U) (hRs : R.IsSet) (hSs : S.IsSet) :
    Entity.relComp R S ∈ U :=
  hU.rel_subset_prod_mem (hU.relDom_mem hRU hRs) (hU.relRan_mem hSU hSs)
    (Entity.isSet_relDom R) (Entity.isSet_relRan S) (Entity.isSet_relComp R S)
    fun _ hp ↦
      let ⟨a, b, c, hR, hS, heq⟩ := Entity.mem_relComp_iff.1 hp
      Entity.mem_prod_iff.2 ⟨a, Entity.mem_relDom_iff.2 ⟨b, hR⟩,
        c, Entity.mem_relRan_iff.2 ⟨b, hS⟩, heq⟩

/-- Goldblatt §13.5 (p. 164): If `A, B ∈ U` are sets and `f : A → B`, then `f ∈ U`. -/
theorem IsUniverse.func_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {f A B : Entity X} (hAU : A ∈ U) (hBU : B ∈ U) (hAs : A.IsSet) (hBs : B.IsSet)
    (hf : Entity.IsFuncFromTo f A B) :
    f ∈ U :=
  hU.rel_subset_prod_mem hAU hBU hAs hBs hf.1 fun p hp ↦
    let ⟨a, ha, b, hb, heq⟩ := hf.2.1 p hp
    Entity.mem_prod_iff.2 ⟨a, ha, b, hb, heq⟩

/-- Goldblatt §13.5 (p. 164): If `A, B ∈ U` are sets, then `B^A ∈ U` (`B^A ⊆ 𝒫(A × B) ∈ U`). -/
theorem IsUniverse.funSpace_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {A B : Entity X} (hAU : A ∈ U) (hBU : B ∈ U) (hAs : A.IsSet) (hBs : B.IsSet) :
    Entity.funSpace A B ∈ U :=
  hU.subset_mem (Entity.isSet_funSpace A B) (Entity.isSet_powerset _)
    (fun _ hf ↦
      let hf' := Entity.mem_funSpace_iff.1 hf
      Entity.mem_powerset_iff.2 ⟨hf'.1, fun p hp ↦
        let ⟨a, ha, b, hb, heq⟩ := hf'.2.1 p hp
        Entity.mem_prod_iff.2 ⟨a, ha, b, hb, heq⟩⟩)
    (hU.powerset_mem (hU.prod_mem hAU hBU hAs hBs) (Entity.isSet_prod A B))

/-- Goldblatt §13.5 (p. 164): If `I ∈ U` and `fam ∈ U` are sets, then `∏_{i ∈ I} A_i ∈ U`. -/
theorem IsUniverse.piSpace_mem {X : Type*} {U : Set (Entity X)} (hU : IsUniverse U)
    {I fam : Entity X} (hIU : I ∈ U) (hfamU : fam ∈ U) (hIs : I.IsSet) (hfams : fam.IsSet) :
    Entity.piSpace I fam ∈ U := by
  have hran : Entity.relRan fam ∈ U := hU.relRan_mem hfamU hfams
  have hunion : Entity.sUnion (Entity.relRan fam) ∈ U :=
    hU.sUnion_mem hran (Entity.isSet_relRan fam)
  have hfs : Entity.funSpace I (Entity.sUnion (Entity.relRan fam)) ∈ U :=
    hU.funSpace_mem hIU hunion hIs (Entity.isSet_sUnion _)
  exact hU.subset_mem (Entity.isSet_setOfBounded _) (Entity.isSet_funSpace _ _)
    (fun _ hf ↦ (Entity.mem_piSpace_iff.1 hf).1) hfs

/-! ## §13.6 Superstructure Theorems, Minimality (Exercise 13.6.1), and Rank Bounds -/

/-- Goldblatt §13.6 (p. 165): The full superstructure `Set.univ : Set (Entity X)` (`𝕌(X)`) is
**strongly transitive**. -/
theorem isStronglyTransitive_superstructure (X : Type*) :
    IsStronglyTransitive (Set.univ : Set (Entity X)) := by
  intro A _ _
  refine ⟨vStageEntity X (A.rank + 1), Set.mem_univ _,
    isTransitiveSet_vStageEntity_succ X A.rank, ?_, fun _ _ ↦ Set.mem_univ _⟩
  intro z hz
  rw [Entity.mem_extSet, mem_vStageEntity, mem_vStage_iff_rank_le]
  have hlt : z.rank < A.rank := Entity.rank_lt_of_mem hz
  omega

/-- Goldblatt §13.6 (p. 165): `𝕌(X)` (`Set.univ : Set (Entity X)`) is a **universe over
`baseSet X`**! -/
theorem isUniverseOver_superstructure (X : Type*) :
    IsUniverseOver (Set.univ : Set (Entity X)) (baseSet X) where
  stronglyTransitive := isStronglyTransitive_superstructure X
  exists_set := ⟨∅, Set.mem_univ _, Entity.isSet_empty⟩
  upair_mem _ _ _ _ := Set.mem_univ _
  union_mem _ _ _ _ _ _ := Set.mem_univ _
  powerset_mem _ _ _ := Set.mem_univ _
  base_mem := Set.mem_univ _
  base_isSet := isSet_vStageEntity X 0
  individuals_spec x hx := by
    obtain ⟨a, rfl⟩ := mem_baseSet_iff.1 hx
    exact ⟨Entity.atom_ne_empty a, fun y _ ↦ Entity.not_mem_atom y a⟩

/-- Goldblatt **Exercise 13.6.1** (p. 165, **Minimality of the Superstructure**): `𝕌(X)` is the
smallest universe containing `baseSet X` — in fact, it is the smallest transitive collection in
`Entity X` containing `baseSet X` and closed under binary unions of sets and power sets of sets! -/
theorem superstructure_minimal {X : Type*} {U : Set (Entity X)}
    (htrans : IsTransitiveCollection U)
    (hbase : baseSet X ∈ U)
    (hunion : ∀ ⦃A B : Entity X⦄, A ∈ U → B ∈ U → A.IsSet → B.IsSet → Entity.union A B ∈ U)
    (hpow : ∀ ⦃A : Entity X⦄, A ∈ U → A.IsSet → Entity.powerset A ∈ U) :
    U = Set.univ := by
  suffices hstage : ∀ n : ℕ, vStageEntity X n ∈ U ∧ VStage X n ⊆ U by
    refine Set.eq_univ_of_forall fun e ↦ ?_
    obtain ⟨n, hn⟩ := exists_mem_vStage e
    exact (hstage n).2 hn
  intro n
  induction n with
  | zero =>
      refine ⟨hbase, fun e he ↦ htrans ?_ hbase⟩
      exact mem_vStageEntity.2 he
  | succ k ih =>
      have hv_eq : vStageEntity X (k + 1) =
          Entity.union (baseSet X) (Entity.powerset (vStageEntity X k)) := by
        refine Entity.set_ext (isSet_vStageEntity X (k + 1)) (Entity.isSet_union _ _) fun e ↦ ?_
        rw [mem_vStageEntity, vStage_succ_eq, Set.mem_union, Entity.mem_union_iff,
            mem_baseSet_iff, ← mem_vStage_zero_iff, Entity.mem_powerset_iff]
        refine or_congr Iff.rfl ⟨fun ⟨hs, hsub⟩ ↦ ⟨hs, fun z hz ↦ mem_vStageEntity.2 (hsub hz)⟩,
          fun ⟨hs, hsub⟩ ↦ ⟨hs, fun z hz ↦ mem_vStageEntity.1 (hsub z hz)⟩⟩
      have hvU : vStageEntity X (k + 1) ∈ U := by
        rw [hv_eq]
        exact hunion hbase (hpow ih.1 (isSet_vStageEntity X k))
          (isSet_vStageEntity X 0) (Entity.isSet_powerset _)
      exact ⟨hvU, fun e he ↦ htrans (mem_vStageEntity.2 he) hvU⟩

/-- Corollary of Exercise 13.6.1 (p. 165): Any universe `U : Set (Entity X)` with `baseSet X ∈ U`
equals `Set.univ` (`𝕌(X)`). -/
theorem IsUniverse.eq_univ_of_baseSet_mem {X : Type*} {U : Set (Entity X)}
    (hU : IsUniverse U) (hbase : baseSet X ∈ U) :
    U = Set.univ :=
  superstructure_minimal hU.stronglyTransitive.isTransitiveCollection hbase
    hU.union_mem hU.powerset_mem

/-- Raw stage functorial map induced by an injection `ι : X ↪ Y` (Goldblatt Exercise 13.6.1, p. 165). -/
def RawStage.map {X Y : Type*} (f : X → Y) : ∀ {m : ℕ}, RawStage X m → RawStage Y m
  | 0, x => f x
  | _ + 1, .inl x => .inl (f x)
  | _ + 1, .inr A => .inr (RawStage.map f '' A)

/-- Injectivity of `f : X → Y` makes `RawStage.map f` preserve and reflect `RawEquiv`
(Goldblatt Exercise 13.6.1, p. 165). -/
theorem RawEquiv.map_iff {X Y : Type*} {f : X → Y} (hf : Function.Injective f) :
    ∀ {m n : ℕ} (a : RawStage X m) (b : RawStage X n),
      RawEquiv (RawStage.map f a) (RawStage.map f b) ↔ RawEquiv a b
  | 0, 0, _, _ => hf.eq_iff
  | 0, _ + 1, _, .inl _ => hf.eq_iff
  | 0, _ + 1, _, .inr _ => Iff.rfl
  | _ + 1, 0, .inl _, _ => hf.eq_iff
  | _ + 1, 0, .inr _, _ => Iff.rfl
  | _ + 1, _ + 1, .inl _, .inl _ => hf.eq_iff
  | _ + 1, _ + 1, .inl _, .inr _ => Iff.rfl
  | _ + 1, _ + 1, .inr _, .inl _ => Iff.rfl
  | _ + 1, _ + 1, .inr A, .inr B => by
      simp only [RawStage.map, RawEquiv]
      constructor
      · rintro ⟨hAB, hBA⟩
        refine ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
        · obtain ⟨_, ⟨b, hb, rfl⟩, hab⟩ := hAB (RawStage.map f a) ⟨a, ha, rfl⟩
          exact ⟨b, hb, (RawEquiv.map_iff hf a b).1 hab⟩
        · obtain ⟨_, ⟨a, ha, rfl⟩, hba⟩ := hBA (RawStage.map f b) ⟨b, hb, rfl⟩
          exact ⟨a, ha, (RawEquiv.map_iff hf a b).1 hba⟩
      · rintro ⟨hAB, hBA⟩
        refine ⟨?_, ?_⟩
        · rintro _ ⟨a, ha, rfl⟩
          obtain ⟨b, hb, hab⟩ := hAB a ha
          exact ⟨RawStage.map f b, ⟨b, hb, rfl⟩, (RawEquiv.map_iff hf a b).2 hab⟩
        · rintro _ ⟨b, hb, rfl⟩
          obtain ⟨a, ha, hba⟩ := hBA b hb
          exact ⟨RawStage.map f a, ⟨a, ha, rfl⟩, (RawEquiv.map_iff hf a b).2 hba⟩

/-- Goldblatt **Exercise 13.6.1** (p. 165, `X ⊆ Y ⇒ 𝕌(ℝ) ⊆ 𝕌(X) ⊆ 𝕌(Y)`): Any embedding
`ι : X ↪ Y` induces a canonical injective superstructure embedding `Entity.mapEmbed ι : Entity X ↪ Entity Y`
preserving atoms, sets, membership, and rank! -/
def Entity.mapEmbed {X Y : Type*} (ι : X ↪ Y) : Entity X ↪ Entity Y where
  toFun := Quotient.lift (s := rawStageSetoid X)
    (fun p ↦ Entity.ofRaw (RawStage.map ι p.2))
    (fun _ _ h ↦ Entity.ofRaw_eq_iff.2 ((RawEquiv.map_iff ι.injective _ _).2 h))
  inj' e₁ e₂ := Quotient.inductionOn₂ e₁ e₂ fun p q h ↦
    Quotient.sound ((RawEquiv.map_iff ι.injective p.2 q.2).1 (Entity.ofRaw_eq_iff.1 h))

/-- `Entity.mapEmbed` composes functorially (`ℝ ↪ X ↪ Y ⇒ 𝕌(ℝ) ↪ 𝕌(X) ↪ 𝕌(Y)`;
Goldblatt Exercise 13.6.1, p. 165). -/
theorem Entity.mapEmbed_trans {R X Y : Type*} (ι₁ : R ↪ X) (ι₂ : X ↪ Y) (e : Entity R) :
    Entity.mapEmbed (ι₁.trans ι₂) e = Entity.mapEmbed ι₂ (Entity.mapEmbed ι₁ e) := by
  refine Quotient.inductionOn e fun ⟨m, r⟩ ↦ ?_
  suffices h : ∀ {k : ℕ} (a : RawStage R k),
      RawStage.map (ι₂ ∘ ι₁) a = RawStage.map ι₂ (RawStage.map ι₁ a) by
    change Entity.ofRaw (RawStage.map (ι₂ ∘ ι₁) r) =
      Entity.ofRaw (RawStage.map ι₂ (RawStage.map ι₁ r))
    rw [h r]
  intro k a
  induction k with
  | zero => rfl
  | succ j ih =>
      cases a with
      | inl _ => rfl
      | inr A =>
          simp only [RawStage.map, Set.image_image, ih]
          rfl

/-- Goldblatt §13.6 (p. 165, **Rank Bound for Relations and Functions**): If `A, B ∈ VStage X n`
are sets (`1 ≤ n`), then any set `R ⊆ A × B` (and in particular `A × B` itself and any function
`f : A → B`) belongs to `VStage X (n + 2)`! -/
theorem subset_prod_mem_vStage_add_two {X : Type*} {A B R : Entity X} {n : ℕ}
    (hAs : A.IsSet) (_hBs : B.IsSet) (hA : A ∈ VStage X n) (hB : B ∈ VStage X n)
    (hRs : R.IsSet) (hR : R.extSet ⊆ (Entity.prod A B).extSet) :
    R ∈ VStage X (n + 2) := by
  rcases n with _ | k
  · exact absurd (mem_vStage_zero_iff.1 hA) hAs
  · rw [Entity.eq_setOfBounded_extSet hRs]
    refine Entity.setOfBounded_mem_vStage fun p hp ↦ ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Entity.mem_prod_iff.1 (hR hp)
    exact Entity.kpair_mem_vStage
      (mem_vStage_of_mem_vStage_succ ha hA)
      (mem_vStage_of_mem_vStage_succ hb hB)

/-- Goldblatt §13.6 Bullet 1 (p. 165): Every topology `τ` on `X` (viewed as a set of subsets of
`baseSet X`) belongs to `VStage X 2`, and the set of all topologies on `X` belongs to `VStage X 3`. -/
theorem topologies_mem_vStage_three (X : Type*) :
    (∀ τ : Entity X, τ.IsSet → τ.extSet ⊆ (Entity.powerset (baseSet X)).extSet →
      τ ∈ VStage X 2) ∧
    Entity.setOfBounded {τ : Entity X |
      τ.IsSet ∧ τ.extSet ⊆ (Entity.powerset (baseSet X)).extSet ∧
      ∅ ∈ τ ∧ baseSet X ∈ τ ∧
      (∀ U₁ ∈ τ, ∀ U₂ ∈ τ, Entity.inter U₁ U₂ ∈ τ) ∧
      (∀ S : Entity X, S.IsSet → S.extSet ⊆ τ.extSet → Entity.sUnion S ∈ τ)} ∈ VStage X 3 := by
  have hP : Entity.powerset (baseSet X) ∈ VStage X 2 :=
    Entity.powerset_mem_vStage_succ_of_isSet (isSet_vStageEntity X 0)
      (vStageEntity_mem_vStage_succ X 0)
  have hτ2 : ∀ τ : Entity X, τ.IsSet → τ.extSet ⊆ (Entity.powerset (baseSet X)).extSet →
      τ ∈ VStage X 2 := by
    intro τ hτs hsub
    rw [Entity.eq_setOfBounded_extSet hτs]
    refine Entity.setOfBounded_mem_vStage fun U₀ hU₀ ↦ ?_
    exact mem_vStage_of_mem_vStage_succ (hsub hU₀) hP
  exact ⟨hτ2, Entity.setOfBounded_mem_vStage fun τ hτ ↦ hτ2 τ hτ.1 hτ.2.1⟩

/-- Goldblatt §13.6 Bullet 2 (p. 165): Given `ℝ ↪ X` (`R₀ = mkAtomSet (range emb) ∈ VStage X 1`),
any `ℝ`-valued measure `μ : A → R₀` with `A ⊆ 𝒫(baseSet X)` belongs to `VStage X 4`, and the set of
all such measures belongs to `VStage X 5`! -/
theorem measures_mem_vStage_five {X : Type*} (emb : ℝ ↪ X) :
    let R₀ := mkAtomSet (Set.range emb)
    (∀ (A μ : Entity X), A.IsSet → A.extSet ⊆ (Entity.powerset (baseSet X)).extSet →
      Entity.IsFuncFromTo μ A R₀ → μ ∈ VStage X 4) ∧
    Entity.setOfBounded {μ : Entity X | ∃ A : Entity X,
      A.IsSet ∧ A.extSet ⊆ (Entity.powerset (baseSet X)).extSet ∧
      Entity.IsFuncFromTo μ A R₀} ∈ VStage X 5 := by
  intro R₀
  have hR₀ : R₀ ∈ VStage X 2 := vStage_mono (by omega) (mkAtomSet_mem_vStage_one _)
  have hμ4 : ∀ (A μ : Entity X), A.IsSet → A.extSet ⊆ (Entity.powerset (baseSet X)).extSet →
      Entity.IsFuncFromTo μ A R₀ → μ ∈ VStage X 4 := by
    intro A μ hAs hAsub hμ
    have hA2 : A ∈ VStage X 2 := (topologies_mem_vStage_three X).1 A hAs hAsub
    exact subset_prod_mem_vStage_add_two hAs (Entity.isSet_setOfBounded _) hA2 hR₀ hμ.1
      fun p hp ↦ let ⟨a, ha, b, hb, heq⟩ := hμ.2.1 p hp; Entity.mem_prod_iff.2 ⟨a, ha, b, hb, heq⟩
  exact ⟨hμ4, Entity.setOfBounded_mem_vStage fun μ ⟨A, hAs, hAsub, hμ⟩ ↦ hμ4 A μ hAs hAsub hμ⟩

/-- Goldblatt §13.6 Bullet 3 (p. 165): Given `ℝ ↪ X`, any metric `d : X × X → ℝ` belongs to
`VStage X 5`, and the set of all functions `X × X → ℝ` (hence any set of metrics on `X`) belongs to
`VStage X 6`! -/
theorem metrics_mem_vStage_six {X : Type*} (emb : ℝ ↪ X) :
    let R₀ := mkAtomSet (Set.range emb)
    let XX := Entity.prod (baseSet X) (baseSet X)
    (∀ d : Entity X, Entity.IsFuncFromTo d XX R₀ → d ∈ VStage X 5) ∧
    ∀ M : Entity X, M.IsSet → M.extSet ⊆ (Entity.funSpace XX R₀).extSet → M ∈ VStage X 6 := by
  intro R₀ XX
  have hX1 : baseSet X ∈ VStage X 1 := vStageEntity_mem_vStage_succ X 0
  have hXX3 : XX ∈ VStage X 3 :=
    subset_prod_mem_vStage_add_two (isSet_vStageEntity X 0) (isSet_vStageEntity X 0)
      hX1 hX1 (Entity.isSet_prod _ _) Set.Subset.rfl
  have hR3 : R₀ ∈ VStage X 3 := vStage_mono (by omega) (mkAtomSet_mem_vStage_one _)
  have hd5 : ∀ d : Entity X, Entity.IsFuncFromTo d XX R₀ → d ∈ VStage X 5 := fun d hd ↦
    subset_prod_mem_vStage_add_two (Entity.isSet_prod _ _) (Entity.isSet_setOfBounded _)
      hXX3 hR3 hd.1 fun p hp ↦
        let ⟨a, ha, b, hb, heq⟩ := hd.2.1 p hp
        Entity.mem_prod_iff.2 ⟨a, ha, b, hb, heq⟩
  refine ⟨hd5, fun M hMs hMsub ↦ ?_⟩
  rw [Entity.eq_setOfBounded_extSet hMs]
  exact Entity.setOfBounded_mem_vStage fun d hd ↦ hd5 d (Entity.mem_funSpace_iff.1 (hMsub hd))

/-- Goldblatt §13.6 Bullet 4 (pp. 165–166): For `[a, b] ⊆ ℝ` (`Iab ∈ VStage ℝ 1`), every function
`f : [a, b] → ℝ` belongs to `VStage ℝ 3`, any family `Rab` of such functions (such as `R[a, b]`)
belongs to `VStage ℝ 4`, and any functional `J : Rab → ℝ` (such as `∫_a^b`) belongs to
`VStage ℝ 6`! -/
theorem riemannIntegral_mem_vStage_six (a b : ℝ) (Rab J : Entity ℝ)
    (hRabSet : Rab.IsSet)
    (hRabSub : Rab.extSet ⊆
      (Entity.funSpace (mkAtomSet (Set.Icc a b)) (baseSet ℝ)).extSet)
    (hJ : Entity.IsFuncFromTo J Rab (baseSet ℝ)) :
    Rab ∈ VStage ℝ 4 ∧ J ∈ VStage ℝ 6 := by
  have hI1 : mkAtomSet (Set.Icc a b) ∈ VStage ℝ 1 := mkAtomSet_mem_vStage_one _
  have hR1 : baseSet ℝ ∈ VStage ℝ 1 := vStageEntity_mem_vStage_succ ℝ 0
  have hf3 : ∀ f : Entity ℝ,
      Entity.IsFuncFromTo f (mkAtomSet (Set.Icc a b)) (baseSet ℝ) → f ∈ VStage ℝ 3 := fun f hf ↦
    subset_prod_mem_vStage_add_two (Entity.isSet_setOfBounded _) (isSet_vStageEntity ℝ 0)
      hI1 hR1 hf.1 fun p hp ↦
        let ⟨x, hx, y, hy, heq⟩ := hf.2.1 p hp
        Entity.mem_prod_iff.2 ⟨x, hx, y, hy, heq⟩
  have hRab4 : Rab ∈ VStage ℝ 4 := by
    rw [Entity.eq_setOfBounded_extSet hRabSet]
    exact Entity.setOfBounded_mem_vStage fun f hf ↦ hf3 f (Entity.mem_funSpace_iff.1 (hRabSub hf))
  have hR4 : baseSet ℝ ∈ VStage ℝ 4 := vStage_mono (by omega) hR1
  have hJ6 : J ∈ VStage ℝ 6 :=
    subset_prod_mem_vStage_add_two hRabSet (isSet_vStageEntity ℝ 0) hRab4 hR4 hJ.1 fun p hp ↦
      let ⟨x, hx, y, hy, heq⟩ := hJ.2.1 p hp
      Entity.mem_prod_iff.2 ⟨x, hx, y, hy, heq⟩
  exact ⟨hRab4, hJ6⟩

/-! ## §13.7 The Language of a Universe (`ℒ_𝕌`) -/

/-- Goldblatt §13.7 (pp. 166–167): Terms of the universe language `ℒ_𝕌` over `Entity X`:
- variables `var v` (`v : ℕ`);
- constant entity symbols `const c` (`c : Entity X`);
- `m`-tuples `(τ₁, …, τ_m)` (`tuple hm args`, with `2 ≤ m`);
- function-value terms `τ(σ)` (`app fn arg`). -/
inductive UTerm (X : Type*) : Type _
  | var (v : ℕ) : UTerm X
  | const (c : Entity X) : UTerm X
  | tuple {m : ℕ} (hm : 2 ≤ m) (args : Fin m → UTerm X) : UTerm X
  | app (fn arg : UTerm X) : UTerm X

/-- Ordered-pair `ℒ_𝕌`-term `(τ₁, τ₂)` as the `m = 2` special case of `UTerm.tuple`
(Goldblatt §13.7, p. 166). -/
def UTerm.pair {X : Type*} (t₁ t₂ : UTerm X) : UTerm X :=
  .tuple (by omega : 2 ≤ 2) ![t₁, t₂]

/-- Goldblatt §13.7 (p. 166): Partial evaluation of an `ℒ_𝕌`-term under a variable assignment
`env : ℕ → Entity X`, matching Goldblatt's definedness rules verbatim:
- `(τ₁, …, τ_m)` denotes `(a₁, …, a_m)` iff each `τ_j` denotes `a_j`, and is undefined (`none`)
  otherwise;
- `τ(σ)` denotes `f(a)` iff `τ` denotes a function `f` and `σ` denotes `a ∈ dom f`, and is
  undefined (`none`) otherwise. -/
def evalUTerm {X : Type*} (env : ℕ → Entity X) : UTerm X → Option (Entity X)
  | .var v => some (env v)
  | .const c => some c
  | .tuple _ args =>
      if h : ∀ j, (evalUTerm env (args j)).isSome then
        some (Entity.ktuple fun j ↦ (evalUTerm env (args j)).get (h j))
      else
        none
  | .app fn arg =>
      match evalUTerm env fn, evalUTerm env arg with
      | some f, some a =>
          if f.IsFuncEntity ∧ a ∈ Entity.relDom f then
            some (Entity.funcApp f a)
          else
            none
      | _, _ => none

/-- Evaluation of `UTerm.var` (Goldblatt §13.7, p. 166). -/
@[simp]
theorem evalUTerm_var {X : Type*} (env : ℕ → Entity X) (v : ℕ) :
    evalUTerm env (.var v) = some (env v) := rfl

/-- Evaluation of `UTerm.const` (Goldblatt §13.7, p. 166). -/
@[simp]
theorem evalUTerm_const {X : Type*} (env : ℕ → Entity X) (c : Entity X) :
    evalUTerm env (.const c) = some c := rfl

/-- Evaluation of `UTerm.pair` reduces directly to `match` on its two subterms
(Goldblatt §13.7, p. 166). -/
@[simp]
theorem evalUTerm_pair {X : Type*} (env : ℕ → Entity X) (t₁ t₂ : UTerm X) :
    evalUTerm env (UTerm.pair t₁ t₂) =
      match evalUTerm env t₁, evalUTerm env t₂ with
      | some a, some b => some (Entity.kpair a b)
      | _, _ => none := by
  rw [UTerm.pair, evalUTerm.eq_3]
  cases h1 : evalUTerm env t₁ with
  | none =>
      have hnot : ¬ ∀ j : Fin 2, (evalUTerm env (![t₁, t₂] j)).isSome := by
        intro hall
        have h0 := hall 0
        simp [h1] at h0
      simp [hnot]
  | some a =>
      cases h2 : evalUTerm env t₂ with
      | none =>
          have hnot : ¬ ∀ j : Fin 2, (evalUTerm env (![t₁, t₂] j)).isSome := by
            intro hall
            have h0 := hall 1
            simp [h2] at h0
          simp [hnot]
      | some b =>
          have hall : ∀ j : Fin 2, (evalUTerm env (![t₁, t₂] j)).isSome := by
            intro j
            fin_cases j <;> simp [h1, h2]
          have hfun : ∀ (h' : ∀ j : Fin 2, (evalUTerm env (![t₁, t₂] j)).isSome),
              (fun j : Fin 2 ↦ (evalUTerm env (![t₁, t₂] j)).get (h' j)) = ![a, b] := by
            intro h'
            ext j
            fin_cases j
            · exact Option.some.inj (by rw [Option.some_get]; exact h1)
            · exact Option.some.inj (by rw [Option.some_get]; exact h2)
          split_ifs with h'
          · rw [hfun h', Entity.ktuple_two]
          · exact absurd hall h'

/-- Evaluation of `UTerm.pair` when both subterms are defined (Goldblatt §13.7, p. 166). -/
theorem evalUTerm_pair_eq_some_iff {X : Type*} {env : ℕ → Entity X} {t₁ t₂ : UTerm X}
    {p : Entity X} :
    evalUTerm env (UTerm.pair t₁ t₂) = some p ↔
      ∃ a b : Entity X, evalUTerm env t₁ = some a ∧ evalUTerm env t₂ = some b ∧
        p = Entity.kpair a b := by
  rw [evalUTerm_pair]
  cases evalUTerm env t₁ <;> cases evalUTerm env t₂ <;> simp [eq_comm]

/-- Evaluation of `UTerm.pair` on two defined subterms (Goldblatt §13.7, p. 166). -/
theorem evalUTerm_pair_of_some {X : Type*} {env : ℕ → Entity X} {t₁ t₂ : UTerm X}
    {a b : Entity X} (h1 : evalUTerm env t₁ = some a) (h2 : evalUTerm env t₂ = some b) :
    evalUTerm env (UTerm.pair t₁ t₂) = some (Entity.kpair a b) := by
  simp [h1, h2]

/-- Evaluation of `UTerm.app` equals `some b` iff `fn` denotes a function `f`, `arg` denotes
`a ∈ dom f`, and `b = f(a)` (Goldblatt §13.7, p. 166). -/
theorem evalUTerm_app_eq_some_iff {X : Type*} {env : ℕ → Entity X} {fn arg : UTerm X}
    {b : Entity X} :
    evalUTerm env (.app fn arg) = some b ↔
      ∃ f a : Entity X, evalUTerm env fn = some f ∧ evalUTerm env arg = some a ∧
        f.IsFuncEntity ∧ a ∈ Entity.relDom f ∧ Entity.funcApp f a = b := by
  rw [evalUTerm.eq_4]
  cases hfn : evalUTerm env fn with
  | none => simp
  | some f =>
      cases harg : evalUTerm env arg with
      | none => simp
      | some a =>
          dsimp only
          split_ifs with hdom
          · simp only [Option.some.injEq]
            exact ⟨fun hb ↦ ⟨f, a, rfl, rfl, hdom.1, hdom.2, hb⟩,
              fun ⟨_, _, rfl, rfl, _, _, hb⟩ ↦ hb⟩
          · simp only [Option.some.injEq, false_iff]
            rintro ⟨_, _, rfl, rfl, hfc, hadom, _⟩
            exact hdom ⟨hfc, hadom⟩

/-- Free variables occurring in an `ℒ_𝕌`-term (Goldblatt §13.7, p. 166). -/
def freeVarsUTerm {X : Type*} : UTerm X → Finset ℕ
  | .var v => {v}
  | .const _ => ∅
  | .tuple _ args => Finset.univ.biUnion fun j ↦ freeVarsUTerm (args j)
  | .app fn arg => freeVarsUTerm fn ∪ freeVarsUTerm arg

/-- Free variables of `UTerm.pair t₁ t₂` (Goldblatt §13.7, p. 166). -/
@[simp]
theorem freeVarsUTerm_pair {X : Type*} (t₁ t₂ : UTerm X) :
    freeVarsUTerm (UTerm.pair t₁ t₂) = freeVarsUTerm t₁ ∪ freeVarsUTerm t₂ := by
  ext v
  simp only [UTerm.pair, freeVarsUTerm, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_union]
  constructor
  · rintro ⟨j, hj⟩
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr hj
  · rintro (h1 | h2)
    · exact ⟨0, h1⟩
    · exact ⟨1, h2⟩

/-- Goldblatt §13.7 (p. 166): An `ℒ_𝕌`-term is **closed** if no variables occur in it. -/
def IsClosedUTerm {X : Type*} (t : UTerm X) : Prop :=
  freeVarsUTerm t = ∅

/-- `evalUTerm` depends only on the assignment to free variables of the term
(Goldblatt §13.7, p. 166). -/
theorem evalUTerm_congr {X : Type*} {env₁ env₂ : ℕ → Entity X} :
    ∀ {t : UTerm X}, (∀ v ∈ freeVarsUTerm t, env₁ v = env₂ v) →
      evalUTerm env₁ t = evalUTerm env₂ t
  | .var v, h => congrArg some (h v (Finset.mem_singleton_self v))
  | .const _, _ => rfl
  | .tuple hm args, h => by
      have hargs : ∀ j, evalUTerm env₁ (args j) = evalUTerm env₂ (args j) := fun j ↦
        evalUTerm_congr fun v hv ↦
          h v (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hv⟩)
      have hiff : (∀ j, (evalUTerm env₁ (args j)).isSome) ↔
          (∀ j, (evalUTerm env₂ (args j)).isSome) :=
        forall_congr' fun j ↦ by rw [hargs j]
      rw [evalUTerm.eq_3, evalUTerm.eq_3]
      split_ifs
      · apply congrArg some
        apply congrArg Entity.ktuple
        ext j
        exact Option.some.inj (by rw [Option.some_get, Option.some_get, hargs j])
      · exact absurd (hiff.1 ‹_›) ‹_›
      · exact absurd (hiff.2 ‹_›) ‹_›
      · rfl
  | .app fn arg, h => by
      have hfn := evalUTerm_congr (t := fn) fun v hv ↦ h v (Finset.mem_union_left _ hv)
      have harg := evalUTerm_congr (t := arg) fun v hv ↦ h v (Finset.mem_union_right _ hv)
      rw [evalUTerm.eq_4, evalUTerm.eq_4, hfn, harg]

/-- Goldblatt §13.7 (pp. 167–168): Formulae of the universe language `ℒ_𝕌` over `Entity X`:
atomic equality `τ = σ` and membership `τ ∈ σ`, propositional connectives `∧, ∨, ¬, →, ↔`, and
bounded quantifiers `(∀ x ∈ τ) φ` and `(∃ x ∈ τ) φ`. -/
inductive UFormula (X : Type*) : Type _
  | eq (t₁ t₂ : UTerm X) : UFormula X
  | mem (t₁ t₂ : UTerm X) : UFormula X
  | conj (φ ψ : UFormula X) : UFormula X
  | disj (φ ψ : UFormula X) : UFormula X
  | neg (φ : UFormula X) : UFormula X
  | imp (φ ψ : UFormula X) : UFormula X
  | iff (φ ψ : UFormula X) : UFormula X
  | forallIn (v : ℕ) (dom : UTerm X) (body : UFormula X) : UFormula X
  | existsIn (v : ℕ) (dom : UTerm X) (body : UFormula X) : UFormula X

/-- Goldblatt §13.7 (pp. 167–168): Satisfaction `Holds env φ` of an `ℒ_𝕌`-formula in `Entity X`
under variable assignment `env : ℕ → Entity X`. Following §4.3.1 & §13.7 (p. 166), atomic formulas
and bounded quantifiers require the bounding/compared terms to be defined (`isSome`). -/
def Holds {X : Type*} (env : ℕ → Entity X) : UFormula X → Prop
  | .eq t₁ t₂ => ∃ a : Entity X, evalUTerm env t₁ = some a ∧ evalUTerm env t₂ = some a
  | .mem t₁ t₂ =>
      ∃ a B : Entity X, evalUTerm env t₁ = some a ∧ evalUTerm env t₂ = some B ∧ a ∈ B
  | .conj φ ψ => Holds env φ ∧ Holds env ψ
  | .disj φ ψ => Holds env φ ∨ Holds env ψ
  | .neg φ => ¬ Holds env φ
  | .imp φ ψ => Holds env φ → Holds env ψ
  | .iff φ ψ => (Holds env φ ↔ Holds env ψ)
  | .forallIn v dom body =>
      ∃ A : Entity X, evalUTerm env dom = some A ∧
        ∀ a ∈ A, Holds (Function.update env v a) body
  | .existsIn v dom body =>
      ∃ A : Entity X, evalUTerm env dom = some A ∧
        ∃ a ∈ A, Holds (Function.update env v a) body

/-- Goldblatt §13.7 Remark (p. 167): When `f` is a function entity (`f.IsFuncEntity`), the two
atomic formulas `f(τ) = σ` and `(τ, σ) ∈ f` have the exact same truth value whenever `τ` and `σ`
are defined! -/
theorem holds_app_eq_iff_pair_mem {X : Type*} {env : ℕ → Entity X} {f a b : Entity X}
    {τ σ : UTerm X} (hf : f.IsFuncEntity)
    (hτ : evalUTerm env τ = some a) (hσ : evalUTerm env σ = some b) :
    Holds env (.eq (.app (.const f) τ) σ) ↔
      Holds env (.mem (UTerm.pair τ σ) (.const f)) := by
  simp only [Holds, evalUTerm_const, evalUTerm_pair_of_some hτ hσ]
  constructor
  · rintro ⟨z, happ, hz⟩
    obtain rfl := Option.some.inj (hσ.symm.trans hz)
    obtain ⟨f', a', hf', ha', _, hadom, hval⟩ := evalUTerm_app_eq_some_iff.1 happ
    obtain rfl := Option.some.inj hf'
    obtain rfl := Option.some.inj (hτ.symm.trans ha')
    exact ⟨Entity.kpair a b, f, rfl, rfl, (Entity.kpair_mem_iff_funcApp_eq hf).2 ⟨hadom, hval⟩⟩
  · rintro ⟨p, f', hp, hf', hmem⟩
    obtain rfl := Option.some.inj hp
    obtain rfl := Option.some.inj hf'
    obtain ⟨hadom, hval⟩ := (Entity.kpair_mem_iff_funcApp_eq hf).1 hmem
    exact ⟨b, evalUTerm_app_eq_some_iff.2 ⟨f, a, rfl, hτ, hf, hadom, hval⟩, hσ⟩

/-- Free variables of an `ℒ_𝕌`-formula (Goldblatt §13.7, p. 167). -/
def freeVarsUFormula {X : Type*} : UFormula X → Finset ℕ
  | .eq t₁ t₂ => freeVarsUTerm t₁ ∪ freeVarsUTerm t₂
  | .mem t₁ t₂ => freeVarsUTerm t₁ ∪ freeVarsUTerm t₂
  | .conj φ ψ => freeVarsUFormula φ ∪ freeVarsUFormula ψ
  | .disj φ ψ => freeVarsUFormula φ ∪ freeVarsUFormula ψ
  | .neg φ => freeVarsUFormula φ
  | .imp φ ψ => freeVarsUFormula φ ∪ freeVarsUFormula ψ
  | .iff φ ψ => freeVarsUFormula φ ∪ freeVarsUFormula ψ
  | .forallIn v dom body => freeVarsUTerm dom ∪ (freeVarsUFormula body).erase v
  | .existsIn v dom body => freeVarsUTerm dom ∪ (freeVarsUFormula body).erase v

/-- Goldblatt §13.7 (p. 167): An `ℒ_𝕌`-sentence is a formula with no free variables. -/
def IsSentence {X : Type*} (φ : UFormula X) : Prop :=
  freeVarsUFormula φ = ∅

/-- Truth of an `ℒ_𝕌`-formula depends only on the assignment to its free variables
(Goldblatt §13.7, p. 167). -/
theorem holds_congr {X : Type*} :
    ∀ {φ : UFormula X} {env₁ env₂ : ℕ → Entity X},
      (∀ v ∈ freeVarsUFormula φ, env₁ v = env₂ v) →
        (Holds env₁ φ ↔ Holds env₂ φ)
  | .eq t₁ t₂, env₁, env₂, h => by
      have h1 := evalUTerm_congr (env₁ := env₁) (env₂ := env₂) (t := t₁)
        fun v hv ↦ h v (Finset.mem_union_left _ hv)
      have h2 := evalUTerm_congr (env₁ := env₁) (env₂ := env₂) (t := t₂)
        fun v hv ↦ h v (Finset.mem_union_right _ hv)
      simp only [Holds, h1, h2]
  | .mem t₁ t₂, env₁, env₂, h => by
      have h1 := evalUTerm_congr (env₁ := env₁) (env₂ := env₂) (t := t₁)
        fun v hv ↦ h v (Finset.mem_union_left _ hv)
      have h2 := evalUTerm_congr (env₁ := env₁) (env₂ := env₂) (t := t₂)
        fun v hv ↦ h v (Finset.mem_union_right _ hv)
      simp only [Holds, h1, h2]
  | .conj φ ψ, _, _, h =>
      and_congr
        (holds_congr fun v hv ↦ h v (Finset.mem_union_left _ hv))
        (holds_congr fun v hv ↦ h v (Finset.mem_union_right _ hv))
  | .disj φ ψ, _, _, h =>
      or_congr
        (holds_congr fun v hv ↦ h v (Finset.mem_union_left _ hv))
        (holds_congr fun v hv ↦ h v (Finset.mem_union_right _ hv))
  | .neg φ, _, _, h => not_congr (holds_congr h)
  | .imp φ ψ, _, _, h =>
      imp_congr
        (holds_congr fun v hv ↦ h v (Finset.mem_union_left _ hv))
        (holds_congr fun v hv ↦ h v (Finset.mem_union_right _ hv))
  | .iff φ ψ, _, _, h =>
      iff_congr
        (holds_congr fun v hv ↦ h v (Finset.mem_union_left _ hv))
        (holds_congr fun v hv ↦ h v (Finset.mem_union_right _ hv))
  | .forallIn v dom body, env₁, env₂, h => by
      have hdom := evalUTerm_congr (env₁ := env₁) (env₂ := env₂) (t := dom)
        fun w hw ↦ h w (Finset.mem_union_left _ hw)
      simp only [Holds, hdom]
      refine exists_congr fun A ↦ and_congr_right fun _ ↦ forall₂_congr fun a _ ↦ ?_
      refine holds_congr fun w hw ↦ ?_
      by_cases hwv : w = v
      · subst hwv; simp
      · simp only [Function.update_of_ne hwv]
        exact h w (Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hwv, hw⟩))
  | .existsIn v dom body, env₁, env₂, h => by
      have hdom := evalUTerm_congr (env₁ := env₁) (env₂ := env₂) (t := dom)
        fun w hw ↦ h w (Finset.mem_union_left _ hw)
      simp only [Holds, hdom]
      refine exists_congr fun A ↦ and_congr_right fun _ ↦ exists_congr fun a ↦ and_congr_right fun _ ↦ ?_
      refine holds_congr fun w hw ↦ ?_
      by_cases hwv : w = v
      · subst hwv; simp
      · simp only [Function.update_of_ne hwv]
        exact h w (Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hwv, hw⟩))

/-- Goldblatt §13.7 (p. 167): Truth of an `ℒ_𝕌`-sentence (evaluated under the canonical default
environment `fun _ ↦ ∅`, and independent of the environment by `holds_congr`). -/
def SentenceHolds {X : Type*} (φ : UFormula X) : Prop :=
  Holds (fun _ ↦ ∅) φ

/-- For any sentence `φ`, `Holds env φ ↔ SentenceHolds φ` for every environment `env`
(Goldblatt §13.7, p. 167). -/
theorem holds_iff_sentenceHolds {X : Type*} {φ : UFormula X} (hφ : IsSentence φ)
    (env : ℕ → Entity X) :
    Holds env φ ↔ SentenceHolds φ :=
  holds_congr fun v hv ↦ by
    rw [IsSentence] at hφ
    simp [hφ] at hv

/-! ## §13.8 Nonstandard Frameworks and Preservation Laws -/

/-- Goldblatt §13.8 (p. 168): The `*-transform` `*τ` of an `ℒ_𝕌`-term obtained by replacing every
constant symbol `c` by `star c`. -/
@[simp]
def starTerm {X Y : Type*} (star : Entity X → Entity Y) : UTerm X → UTerm Y
  | .var v => .var v
  | .const c => .const (star c)
  | .tuple hm args => .tuple hm fun j ↦ starTerm star (args j)
  | .app fn arg => .app (starTerm star fn) (starTerm star arg)

/-- `starTerm` commutes with `UTerm.pair` (Goldblatt §13.8, p. 168). -/
@[simp]
theorem starTerm_pair {X Y : Type*} (star : Entity X → Entity Y) (t₁ t₂ : UTerm X) :
    starTerm star (UTerm.pair t₁ t₂) = UTerm.pair (starTerm star t₁) (starTerm star t₂) := by
  rw [UTerm.pair, starTerm.eq_3, UTerm.pair]
  congr 1
  funext j
  fin_cases j <;> rfl

/-- `starTerm` preserves free variables (Goldblatt §13.8, p. 168). -/
@[simp]
theorem freeVarsUTerm_starTerm {X Y : Type*} (star : Entity X → Entity Y) :
    ∀ t : UTerm X, freeVarsUTerm (starTerm star t) = freeVarsUTerm t
  | .var _ => rfl
  | .const _ => rfl
  | .tuple _ args => by
      simp only [starTerm, freeVarsUTerm]
      congr 1
      funext j
      exact freeVarsUTerm_starTerm star (args j)
  | .app fn arg => by
      simp [starTerm, freeVarsUTerm, freeVarsUTerm_starTerm star fn,
        freeVarsUTerm_starTerm star arg]

/-- Goldblatt §13.8 (p. 168): The `*-transform` `*φ` of an `ℒ_𝕌`-formula obtained by replacing every
constant `c` in atomic and bounding terms by `star c`. -/
@[simp]
def starFormula {X Y : Type*} (star : Entity X → Entity Y) : UFormula X → UFormula Y
  | .eq t₁ t₂ => .eq (starTerm star t₁) (starTerm star t₂)
  | .mem t₁ t₂ => .mem (starTerm star t₁) (starTerm star t₂)
  | .conj φ ψ => .conj (starFormula star φ) (starFormula star ψ)
  | .disj φ ψ => .disj (starFormula star φ) (starFormula star ψ)
  | .neg φ => .neg (starFormula star φ)
  | .imp φ ψ => .imp (starFormula star φ) (starFormula star ψ)
  | .iff φ ψ => .iff (starFormula star φ) (starFormula star ψ)
  | .forallIn v dom body => .forallIn v (starTerm star dom) (starFormula star body)
  | .existsIn v dom body => .existsIn v (starTerm star dom) (starFormula star body)

/-- `starFormula` preserves free variables (Goldblatt §13.8, p. 168). -/
@[simp]
theorem freeVarsUFormula_starFormula {X Y : Type*} (star : Entity X → Entity Y) :
    ∀ φ : UFormula X, freeVarsUFormula (starFormula star φ) = freeVarsUFormula φ
  | .eq _ _ => by simp [starFormula, freeVarsUFormula]
  | .mem _ _ => by simp [starFormula, freeVarsUFormula]
  | .conj φ ψ => by
      simp [starFormula, freeVarsUFormula, freeVarsUFormula_starFormula star φ,
        freeVarsUFormula_starFormula star ψ]
  | .disj φ ψ => by
      simp [starFormula, freeVarsUFormula, freeVarsUFormula_starFormula star φ,
        freeVarsUFormula_starFormula star ψ]
  | .neg φ => by simp [starFormula, freeVarsUFormula, freeVarsUFormula_starFormula star φ]
  | .imp φ ψ => by
      simp [starFormula, freeVarsUFormula, freeVarsUFormula_starFormula star φ,
        freeVarsUFormula_starFormula star ψ]
  | .iff φ ψ => by
      simp [starFormula, freeVarsUFormula, freeVarsUFormula_starFormula star φ,
        freeVarsUFormula_starFormula star ψ]
  | .forallIn _ _ body => by
      simp [starFormula, freeVarsUFormula, freeVarsUFormula_starFormula star body]
  | .existsIn _ _ body => by
      simp [starFormula, freeVarsUFormula, freeVarsUFormula_starFormula star body]

/-- Goldblatt §13.8 (p. 168): If `φ` is an `ℒ_𝕌`-sentence, then `*φ` is an `ℒ_𝕌'`-sentence. -/
theorem IsSentence.star {X Y : Type*} (star : Entity X → Entity Y) {φ : UFormula X}
    (hφ : IsSentence φ) : IsSentence (starFormula star φ) := by
  simpa [IsSentence] using hφ

/-- Goldblatt §13.8 (p. 168): A **nonstandard framework** (universe embedding / transfer map) from
`Entity X` into `Entity Y`, comprising an individual embedding `atomMap : X → Y` (identifying each
`a ∈ X` with `*a ∈ Y`) and a map `star : Entity X → Entity Y` (`a ↦ *a`) satisfying:
1. `*a = a` on individuals (`star (atom x) = atom (atomMap x)`);
2. `*∅ = ∅` (`star ∅ = ∅`);
3. **Transfer**: an `ℒ_𝕌`-sentence `φ` holds iff `*φ` holds. -/
structure Framework (X : Type*) (Y : Type*) where
  /-- Standard individual embedding `X → Y` (e.g. `coe : ℝ → ℝ*`). -/
  atomMap : X → Y
  /-- Transfer map `a ↦ *a` between universes `Entity X → Entity Y`. -/
  star : Entity X → Entity Y
  /-- `*a = a` for all individuals `a ∈ X` (Goldblatt §13.8, p. 168). -/
  star_atom : ∀ x : X, star (Entity.atom x) = Entity.atom (atomMap x)
  /-- `*∅ = ∅` (Goldblatt §13.8, p. 168). -/
  star_empty : star ∅ = ∅
  /-- **Transfer Principle** (Goldblatt §13.8, p. 168): `φ` is true iff `*φ` is true for every
  `ℒ_𝕌`-sentence `φ`. -/
  transfer : ∀ φ : UFormula X, IsSentence φ →
    (SentenceHolds φ ↔ SentenceHolds (starFormula star φ))

/-- Goldblatt §13.8 Bullet 1 (p. 168): `a = b ↔ *a = *b`. -/
@[simp]
theorem Framework.star_eq_iff {X Y : Type*} (F : Framework X Y) {a b : Entity X} :
    F.star a = F.star b ↔ a = b := by
  have h := F.transfer (.eq (.const a) (.const b)) (by simp [IsSentence, freeVarsUFormula, freeVarsUTerm])
  simp only [SentenceHolds, Holds, starFormula, starTerm, evalUTerm_const, Option.some.injEq] at h
  constructor
  · intro heq
    obtain ⟨z, rfl, hbz⟩ := h.2 ⟨F.star a, rfl, heq.symm⟩
    exact hbz.symm
  · rintro rfl
    rfl

/-- Goldblatt §13.8 Bullet 1 (p. 168): The transfer map `a ↦ *a` is injective. -/
theorem Framework.star_injective {X Y : Type*} (F : Framework X Y) :
    Function.Injective F.star :=
  fun _ _ h ↦ F.star_eq_iff.1 h

/-- `F.atomMap` is injective (Goldblatt §13.8, p. 168). -/
theorem Framework.atomMap_injective {X Y : Type*} (F : Framework X Y) :
    Function.Injective F.atomMap := by
  intro x₁ x₂ h
  have : F.star (Entity.atom x₁) = F.star (Entity.atom x₂) := by
    rw [F.star_atom, F.star_atom, h]
  exact Entity.atom_inj.1 (F.star_injective this)

/-- Goldblatt §13.8 Bullet 2 (p. 168): `a ∈ B ↔ *a ∈ *B`. -/
@[simp]
theorem Framework.mem_star_iff {X Y : Type*} (F : Framework X Y) {a B : Entity X} :
    F.star a ∈ F.star B ↔ a ∈ B := by
  have h := F.transfer (.mem (.const a) (.const B)) (by simp [IsSentence, freeVarsUFormula, freeVarsUTerm])
  simpa [SentenceHolds, Holds, starFormula, starTerm] using h.symm

/-- Nonemptiness of entities is preserved and reflected by `F.star` (Goldblatt §13.8, p. 169). -/
theorem Framework.exists_mem_star_iff {X Y : Type*} (F : Framework X Y) {A : Entity X} :
    (∃ y : Entity Y, y ∈ F.star A) ↔ ∃ x : Entity X, x ∈ A := by
  have h := F.transfer (.existsIn 0 (.const A) (.eq (.var 0) (.var 0)))
    (by simp [IsSentence, freeVarsUFormula, freeVarsUTerm])
  simpa [SentenceHolds, Holds, starFormula, starTerm] using h.symm

/-- `A` is a set entity iff `*A` is a set entity (`Δ₀`-preservation via `*∅ = ∅`;
Goldblatt §13.8, p. 169). -/
@[simp]
theorem Framework.isSet_star_iff {X Y : Type*} (F : Framework X Y) {A : Entity X} :
    (F.star A).IsSet ↔ A.IsSet := by
  rw [Entity.isSet_iff_eq_empty_or_nonempty, Entity.isSet_iff_eq_empty_or_nonempty,
    ← F.star_empty, F.star_eq_iff, F.exists_mem_star_iff]

/-- `a` is an individual iff `*a` is an individual (Goldblatt §13.8, p. 169). -/
@[simp]
theorem Framework.isAtom_star_iff {X Y : Type*} (F : Framework X Y) {a : Entity X} :
    (F.star a).IsAtom ↔ a.IsAtom := by
  rw [← Decidable.not_not (p := (F.star a).IsAtom), ← Decidable.not_not (p := a.IsAtom)]
  exact not_congr F.isSet_star_iff

/-- Goldblatt §13.8 Bullet 3 (p. 168): For sets `A, B`, `A ⊆ B ↔ *A ⊆ *B`. -/
theorem Framework.subset_star_iff {X Y : Type*} (F : Framework X Y) {A B : Entity X} :
    (∀ y ∈ F.star A, y ∈ F.star B) ↔ ∀ x ∈ A, x ∈ B := by
  have h := F.transfer (.forallIn 0 (.const A) (.mem (.var 0) (.const B)))
    (by simp [IsSentence, freeVarsUFormula, freeVarsUTerm])
  simpa [SentenceHolds, Holds, starFormula, starTerm] using h.symm

/-- Goldblatt §13.8 Bullet 4 (pp. 168–169): If `A ⊆ baseSet X` (`A = mkAtomSet S`), then
`atomMap '' S ⊆ *A ⊆ *(baseSet X)`. In particular, `atomMap '' X ⊆ *(baseSet X)`. -/
theorem Framework.atomSet_subset_star {X Y : Type*} (F : Framework X Y) {A : Entity X}
    (hAX : ∀ a ∈ A, a ∈ baseSet X) :
    (∀ x : X, Entity.atom x ∈ A → Entity.atom (F.atomMap x) ∈ F.star A) ∧
    (∀ y ∈ F.star A, y ∈ F.star (baseSet X)) := by
  refine ⟨fun x hx ↦ ?_, F.subset_star_iff.2 hAX⟩
  rw [← F.star_atom]
  exact F.mem_star_iff.2 hx

/-- Goldblatt §13.8 Bullet 9 (p. 169): All members of `*(baseSet X)` (`*X`) are individuals in
`Entity Y`! Proved exactly as in Goldblatt p. 169 by transferring
`(∀ x ∈ X) [x ≠ ∅ ∧ ¬ (∃ y ∈ x) (y ∈ x)]`. -/
theorem Framework.isAtom_of_mem_star_baseSet {X Y : Type*} (F : Framework X Y) {b : Entity Y}
    (hb : b ∈ F.star (baseSet X)) : b.IsAtom := by
  let φ : UFormula X :=
    .forallIn 0 (.const (baseSet X))
      (.conj (.neg (.eq (.var 0) (.const ∅)))
        (.neg (.existsIn 1 (.var 0) (.mem (.var 1) (.var 0)))))
  have hsent : IsSentence φ := by
    simp [φ, IsSentence, freeVarsUFormula, freeVarsUTerm]
  have hstd : SentenceHolds φ := by
    refine ⟨baseSet X, rfl, fun a ha ↦ ?_⟩
    obtain ⟨x, rfl⟩ := mem_baseSet_iff.1 ha
    refine ⟨?_, ?_⟩
    · intro heq
      obtain ⟨z, hz1, hz2⟩ := heq
      have h1 : Entity.atom x = z := Option.some.inj hz1
      have h2 : (∅ : Entity X) = z := Option.some.inj hz2
      exact Entity.atom_ne_empty x (h1.trans h2.symm)
    · rintro ⟨A, hA, y, hyA, _⟩
      have hEq : Entity.atom x = A := Option.some.inj hA
      exact Entity.not_mem_atom y x (hEq ▸ hyA)
  have htr := (F.transfer φ hsent).1 hstd
  obtain ⟨BX, hBX, hall⟩ := htr
  obtain rfl := Option.some.inj hBX
  obtain ⟨hne, hnomem⟩ := hall b hb
  refine Entity.isAtom_iff_ne_empty_and_forall_not_mem.2 ⟨?_, ?_⟩
  · intro hb0
    exact hne ⟨∅, by simp [hb0], by simp [F.star_empty]⟩
  · intro y hyb
    exact hnomem ⟨b, by simp, y, hyb, y, b, by simp, by simp, hyb⟩

/-- Goldblatt §13.8 Bullet 10 (p. 169): `star` preserves transitive sets (`IsTransitiveSet`). -/
theorem Framework.isTransitiveSet_star_iff {X Y : Type*} (F : Framework X Y) {A : Entity X} :
    (F.star A).IsTransitiveSet ↔ A.IsTransitiveSet := by
  let φ : UFormula X :=
    .forallIn 0 (.const A) (.forallIn 1 (.var 0) (.mem (.var 1) (.const A)))
  have hsent : IsSentence φ := by
    simp [φ, IsSentence, freeVarsUFormula, freeVarsUTerm]
  have htr := (F.transfer φ hsent).symm
  simp only [Entity.IsTransitiveSet, F.isSet_star_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · intro h x hx y hy
    have h' : SentenceHolds (starFormula F.star φ) :=
      ⟨F.star A, rfl, fun x' hx' ↦ ⟨x', by simp, fun y' hy' ↦
        ⟨y', F.star A, by simp, rfl, h x' hx' y' hy'⟩⟩⟩
    obtain ⟨A₀, hA₀, hall⟩ := htr.1 h'
    obtain rfl := Option.some.inj hA₀
    obtain ⟨x₀, hx₀, hyall⟩ := hall x hx
    obtain rfl := Option.some.inj hx₀
    obtain ⟨y₀, A₁, hy₀, hA₁, hmem⟩ := hyall y hy
    obtain rfl := Option.some.inj hy₀
    obtain rfl := Option.some.inj hA₁
    exact hmem
  · intro h x hxA y hyx
    have h' : SentenceHolds φ :=
      ⟨A, rfl, fun x' hx' ↦ ⟨x', by simp, fun y' hy' ↦
        ⟨y', A, by simp, rfl, h x' hx' y' hy'⟩⟩⟩
    obtain ⟨A₀, hA₀, hall⟩ := htr.2 h'
    obtain rfl := Option.some.inj hA₀
    obtain ⟨x₀, hx₀, hyall⟩ := hall x hxA
    obtain rfl := Option.some.inj hx₀
    obtain ⟨y₀, A₁, hy₀, hA₁, hmem⟩ := hyall y hyx
    obtain rfl := Option.some.inj hy₀
    obtain rfl := Option.some.inj hA₁
    exact hmem

/-- Goldblatt §13.8 Bullet 11 (p. 169–170): `*𝒫(E) ⊆ 𝒫(*E)` for every entity `E : Entity X`. -/
theorem Framework.mem_powerset_star_of_mem_star_powerset {X Y : Type*} (F : Framework X Y)
    {E : Entity X} {y : Entity Y}
    (hy : y ∈ F.star (Entity.powerset E)) :
    y ∈ Entity.powerset (F.star E) := by
  -- Transfer `∀ x ∈ 𝒫(E), (x = ∅ ∨ ∃ z ∈ x, z = z) ∧ ∀ z ∈ x, z ∈ E`
  let φ : UFormula X :=
    .forallIn 0 (.const (Entity.powerset E))
      (.conj
        (.disj (.eq (.var 0) (.const ∅)) (.existsIn 1 (.var 0) (.eq (.var 1) (.var 1))))
        (.forallIn 1 (.var 0) (.mem (.var 1) (.const E))))
  have hsent : IsSentence φ := by
    simp [φ, IsSentence, freeVarsUFormula, freeVarsUTerm]
  have hstd : SentenceHolds φ := by
    refine ⟨Entity.powerset E, rfl, fun x hx ↦ ?_⟩
    obtain ⟨hxset, hxsub⟩ := Entity.mem_powerset_iff.1 hx
    refine ⟨?_, ⟨x, by simp, fun z hzx ↦ ⟨z, E, by simp, rfl, hxsub z hzx⟩⟩⟩
    rcases Entity.isSet_iff_eq_empty_or_nonempty.1 hxset with rfl | ⟨z, hzx⟩
    · exact Or.inl ⟨∅, by simp, rfl⟩
    · exact Or.inr ⟨x, by simp, z, hzx, z, by simp, by simp⟩
  obtain ⟨P₀, hP₀, hall⟩ := (F.transfer φ hsent).1 hstd
  obtain rfl := Option.some.inj hP₀
  obtain ⟨hset_disj, x₀, hx₀, hsub⟩ := hall y hy
  obtain rfl := Option.some.inj hx₀
  refine Entity.mem_powerset_iff.2 ⟨?_, fun z hzy ↦ ?_⟩
  · refine Entity.isSet_iff_eq_empty_or_nonempty.2 ?_
    rcases hset_disj with ⟨w, hw1, hw2⟩ | ⟨w, hw, z, hzw, _⟩
    · have hyw : y = w := Option.some.inj hw1
      have h0w : F.star ∅ = w := Option.some.inj hw2
      exact Or.inl (hyw.trans (h0w.symm.trans F.star_empty))
    · obtain rfl := Option.some.inj hw
      exact Or.inr ⟨z, hzw⟩
  · obtain ⟨z₀, E₀, hz₀, hE₀, hmem⟩ := hsub z hzy
    obtain rfl := Option.some.inj hz₀
    obtain rfl := Option.some.inj hE₀
    exact hmem

/-- Master bounded comprehension preservation lemma for `Framework`: if `S ⊆ T` is a set in
`Entity X` characterized inside `T` by a single-variable `ℒ_𝕌`-formula `φ` (`freeVarsUFormula φ ⊆ {0}`),
then `*S = {b ∈ *T | *φ(b)}` (Goldblatt §13.8, pp. 168–170). -/
theorem Framework.star_set_eq_of_bounded {X Y : Type*} (F : Framework X Y)
    {S T : Entity X} {φ : UFormula X}
    (hS : S.IsSet)
    (hST : ∀ a ∈ S, a ∈ T)
    (hvars : ∀ v ∈ freeVarsUFormula φ, v = 0)
    (hchar : ∀ a ∈ T, (a ∈ S ↔ Holds (fun _ ↦ a) φ)) :
    F.star S =
      Entity.setOfBounded {b : Entity Y |
        b ∈ F.star T ∧ Holds (fun _ ↦ b) (starFormula F.star φ)} := by
  have hstarS : (F.star S).IsSet := F.isSet_star_iff.2 hS
  have hsub : ∀ b ∈ F.star S, b ∈ F.star T := F.subset_star_iff.2 hST
  have hbdd : IsBoundedRank {b : Entity Y |
      b ∈ F.star T ∧ Holds (fun _ ↦ b) (starFormula F.star φ)} :=
    (F.star T).isBoundedRank_extSet.subset fun _ hb ↦ hb.1
  let ψ : UFormula X := .forallIn 0 (.const T) (.iff (.mem (.var 0) (.const S)) φ)
  have hsent : IsSentence ψ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v hv
    simp only [ψ, freeVarsUFormula, freeVarsUTerm, Finset.empty_union,
      Finset.mem_erase, Finset.mem_union, Finset.mem_singleton] at hv
    rcases hv with ⟨hv0, (rfl | hv) | hv⟩
    · exact hv0 rfl
    · simp at hv
    · exact hv0 (hvars v hv)
  have hstd : SentenceHolds ψ := by
    refine ⟨T, rfl, fun a ha ↦ ?_⟩
    have hupd : Holds (Function.update (fun _ ↦ (∅ : Entity X)) 0 a) φ ↔ Holds (fun _ ↦ a) φ :=
      holds_congr fun v hv ↦ by obtain rfl := hvars v hv; simp
    rw [Holds, hupd, ← hchar a ha]
    constructor
    · rintro ⟨a', S', ha', hS', hm⟩
      obtain rfl := Option.some.inj (by simpa using ha')
      obtain rfl := Option.some.inj hS'
      exact hm
    · intro hm
      exact ⟨a, S, by simp, rfl, hm⟩
  obtain ⟨T₀, hT₀, hall⟩ := (F.transfer ψ hsent).1 hstd
  obtain rfl := Option.some.inj hT₀
  refine Entity.set_ext hstarS (Entity.isSet_setOfBounded _) fun b ↦ ?_
  rw [Entity.mem_setOfBounded hbdd]
  constructor
  · intro hbS
    have hbT : b ∈ F.star T := hsub b hbS
    have hiff := hall b hbT
    have hupd :
        Holds (Function.update (fun _ ↦ (∅ : Entity Y)) 0 b) (starFormula F.star φ) ↔
          Holds (fun _ ↦ b) (starFormula F.star φ) :=
      holds_congr fun v hv ↦ by
        rw [freeVarsUFormula_starFormula] at hv
        obtain rfl := hvars v hv
        simp
    exact ⟨hbT, hupd.1 (hiff.1 ⟨b, F.star S, by simp, rfl, hbS⟩)⟩
  · rintro ⟨hbT, hφb⟩
    have hiff := hall b hbT
    have hupd :
        Holds (Function.update (fun _ ↦ (∅ : Entity Y)) 0 b) (starFormula F.star φ) ↔
          Holds (fun _ ↦ b) (starFormula F.star φ) :=
      holds_congr fun v hv ↦ by
        rw [freeVarsUFormula_starFormula] at hv
        obtain rfl := hvars v hv
        simp
    obtain ⟨b', S', hb', hS', hm⟩ := hiff.2 (hupd.2 hφb)
    obtain rfl := Option.some.inj hb'
    obtain rfl := Option.some.inj hS'
    exact hm

/-- Goldblatt §13.8 Bullet 8 (p. 168): `*{a, b} = {*a, *b}`. -/
@[simp]
theorem Framework.star_upair {X Y : Type*} (F : Framework X Y) (a b : Entity X) :
    F.star (Entity.upair a b) = Entity.upair (F.star a) (F.star b) := by
  have h1 : F.star a ∈ F.star (Entity.upair a b) := F.mem_star_iff.2 (Entity.mem_upair_iff.2 (Or.inl rfl))
  have h2 : F.star b ∈ F.star (Entity.upair a b) := F.mem_star_iff.2 (Entity.mem_upair_iff.2 (Or.inr rfl))
  have hEq := F.star_set_eq_of_bounded (S := Entity.upair a b) (T := Entity.upair a b)
    (φ := .disj (.eq (.var 0) (.const a)) (.eq (.var 0) (.const b)))
    (Entity.isSet_upair a b) (fun _ h ↦ h)
    (by simp [freeVarsUFormula, freeVarsUTerm])
    (fun z _ ↦ by
      rw [Entity.mem_upair_iff]
      simp only [Holds, evalUTerm_var, evalUTerm_const, Option.some.injEq]
      constructor
      · rintro (rfl | rfl)
        · exact Or.inl ⟨z, rfl, rfl⟩
        · exact Or.inr ⟨z, rfl, rfl⟩
      · rintro (⟨w, rfl, rfl⟩ | ⟨w, rfl, rfl⟩)
        · exact Or.inl rfl
        · exact Or.inr rfl)
  refine Entity.set_ext (F.isSet_star_iff.2 (Entity.isSet_upair a b)) (Entity.isSet_upair _ _) fun y ↦ ?_
  rw [Entity.mem_upair_iff]
  constructor
  · intro hy
    rw [hEq, Entity.mem_setOfBounded ((F.star (Entity.upair a b)).isBoundedRank_extSet.subset fun _ h ↦ h.1)] at hy
    rcases hy.2 with ⟨w, hw1, hw2⟩ | ⟨w, hw1, hw2⟩
    · exact Or.inl ((Option.some.inj hw1).trans (Option.some.inj hw2).symm)
    · exact Or.inr ((Option.some.inj hw1).trans (Option.some.inj hw2).symm)
  · rintro (rfl | rfl)
    · exact h1
    · exact h2

/-- Goldblatt §13.8 Bullet 8 (p. 168): `*{a} = {*a}`. -/
@[simp]
theorem Framework.star_singleton {X Y : Type*} (F : Framework X Y) (a : Entity X) :
    F.star (Entity.singleton a) = Entity.singleton (F.star a) :=
  F.star_upair a a

/-- Goldblatt §13.8 (p. 169): `*(a, b) = (*a, *b)` for Kuratowski ordered pairs. -/
@[simp]
theorem Framework.star_kpair {X Y : Type*} (F : Framework X Y) (a b : Entity X) :
    F.star (Entity.kpair a b) = Entity.kpair (F.star a) (F.star b) := by
  simp [Entity.kpair]

/-- Goldblatt §13.8 (p. 169): `*(a₁, …, a_m) = (*a₁, …, *a_m)` for `m`-tuples. -/
@[simp]
theorem Framework.star_ktuple {X Y : Type*} (F : Framework X Y) :
    ∀ {m : ℕ} (v : Fin m → Entity X),
      F.star (Entity.ktuple v) = Entity.ktuple (fun i ↦ F.star (v i))
  | 0, _ => F.star_empty
  | 1, _ => rfl
  | 2, _ => F.star_kpair _ _
  | m + 3, v => by
      simp only [Entity.ktuple, F.star_kpair, F.star_ktuple (m := m + 2)]
      rfl

/-- Goldblatt §13.8 Bullet 5 (p. 168) & **Exercise 13.8.1**: `*(A ∩ B) = *A ∩ *B`. -/
@[simp]
theorem Framework.star_inter {X Y : Type*} (F : Framework X Y) (A B : Entity X) :
    F.star (Entity.inter A B) = Entity.inter (F.star A) (F.star B) := by
  have hEq := F.star_set_eq_of_bounded (S := Entity.inter A B) (T := A)
    (φ := .mem (.var 0) (.const B))
    (Entity.isSet_inter A B) (fun _ hz ↦ (Entity.mem_inter_iff.1 hz).1)
    (by simp [freeVarsUFormula, freeVarsUTerm])
    (fun a ha ↦ by
      simp only [Entity.mem_inter_iff, ha, true_and, Holds, evalUTerm_var, evalUTerm_const]
      exact ⟨fun hb ↦ ⟨a, B, rfl, rfl, hb⟩, fun ⟨_, _, h1, h2, hb⟩ ↦
        (Option.some.inj h1) ▸ (Option.some.inj h2) ▸ hb⟩)
  refine Entity.set_ext (F.isSet_star_iff.2 (Entity.isSet_inter A B)) (Entity.isSet_inter _ _) fun y ↦ ?_
  rw [hEq, Entity.mem_setOfBounded ((F.star A).isBoundedRank_extSet.subset fun _ h ↦ h.1),
    Entity.mem_inter_iff]
  simp only [starFormula, starTerm, Holds, evalUTerm_var, evalUTerm_const]
  exact and_congr_right fun _ ↦ ⟨fun ⟨_, _, h1, h2, hb⟩ ↦
    (Option.some.inj h1) ▸ (Option.some.inj h2) ▸ hb, fun hb ↦ ⟨y, F.star B, rfl, rfl, hb⟩⟩

/-- Goldblatt §13.8 Bullet 6 (p. 168) & **Exercise 13.8.1**: `*(A ∪ B) = *A ∪ *B`. -/
@[simp]
theorem Framework.star_union {X Y : Type*} (F : Framework X Y) (A B : Entity X) :
    F.star (Entity.union A B) = Entity.union (F.star A) (F.star B) := by
  have hsubA : ∀ y ∈ F.star A, y ∈ F.star (Entity.union A B) :=
    F.subset_star_iff.2 fun _ hx ↦ Entity.mem_union_iff.2 (Or.inl hx)
  have hsubB : ∀ y ∈ F.star B, y ∈ F.star (Entity.union A B) :=
    F.subset_star_iff.2 fun _ hx ↦ Entity.mem_union_iff.2 (Or.inr hx)
  have hEq := F.star_set_eq_of_bounded (S := Entity.union A B) (T := Entity.union A B)
    (φ := .disj (.mem (.var 0) (.const A)) (.mem (.var 0) (.const B)))
    (Entity.isSet_union A B) (fun _ h ↦ h)
    (by simp [freeVarsUFormula, freeVarsUTerm])
    (fun z _ ↦ by
      simp only [Entity.mem_union_iff, Holds, evalUTerm_var, evalUTerm_const]
      constructor
      · rintro (hz | hz)
        · exact Or.inl ⟨z, A, rfl, rfl, hz⟩
        · exact Or.inr ⟨z, B, rfl, rfl, hz⟩
      · rintro (⟨_, _, h1, h2, hz⟩ | ⟨_, _, h1, h2, hz⟩)
        · exact Or.inl ((Option.some.inj h1) ▸ (Option.some.inj h2) ▸ hz)
        · exact Or.inr ((Option.some.inj h1) ▸ (Option.some.inj h2) ▸ hz))
  refine Entity.set_ext (F.isSet_star_iff.2 (Entity.isSet_union A B)) (Entity.isSet_union _ _) fun y ↦ ?_
  rw [Entity.mem_union_iff]
  constructor
  · intro hy
    rw [hEq, Entity.mem_setOfBounded ((F.star (Entity.union A B)).isBoundedRank_extSet.subset fun _ h ↦ h.1)] at hy
    rcases hy.2 with ⟨_, _, h1, h2, hz⟩ | ⟨_, _, h1, h2, hz⟩
    · obtain rfl := Option.some.inj (by simpa using h1)
      obtain rfl := Option.some.inj (by simpa using h2)
      exact Or.inl hz
    · obtain rfl := Option.some.inj (by simpa using h1)
      obtain rfl := Option.some.inj (by simpa using h2)
      exact Or.inr hz
  · rintro (hy | hy)
    · exact hsubA y hy
    · exact hsubB y hy

/-- Goldblatt §13.8 Bullet 7 (p. 168) & **Exercise 13.8.1**: `*(A \ B) = *A \ *B`. -/
@[simp]
theorem Framework.star_sdiff {X Y : Type*} (F : Framework X Y) (A B : Entity X) :
    F.star (Entity.sdiff A B) = Entity.sdiff (F.star A) (F.star B) := by
  have hEq := F.star_set_eq_of_bounded (S := Entity.sdiff A B) (T := A)
    (φ := .neg (.mem (.var 0) (.const B)))
    (Entity.isSet_sdiff A B) (fun _ hz ↦ (Entity.mem_sdiff_iff.1 hz).1)
    (by simp [freeVarsUFormula, freeVarsUTerm])
    (fun a ha ↦ by
      simp only [Entity.mem_sdiff_iff, ha, true_and, Holds, evalUTerm_var, evalUTerm_const]
      exact not_congr ⟨fun hb ↦ ⟨a, B, rfl, rfl, hb⟩,
        fun ⟨_, _, h1, h2, hb⟩ ↦ (Option.some.inj h1) ▸ (Option.some.inj h2) ▸ hb⟩)
  refine Entity.set_ext (F.isSet_star_iff.2 (Entity.isSet_sdiff A B)) (Entity.isSet_sdiff _ _) fun y ↦ ?_
  rw [hEq, Entity.mem_setOfBounded ((F.star A).isBoundedRank_extSet.subset fun _ h ↦ h.1),
    Entity.mem_sdiff_iff]
  simp only [starFormula, starTerm, Holds, evalUTerm_var, evalUTerm_const]
  exact and_congr_right fun _ ↦ not_congr
    ⟨fun ⟨_, _, h1, h2, hb⟩ ↦ (Option.some.inj h1) ▸ (Option.some.inj h2) ▸ hb,
     fun hb ↦ ⟨y, F.star B, rfl, rfl, hb⟩⟩

/-- Goldblatt §13.8 Bullet 8 (p. 168) & **Exercise 13.8.1**: `*{a₁, …, a_m} = {*a₁, …, *a_m}` for
any `Finset (Entity X)`. -/
theorem Framework.star_finsetEntity {X Y : Type*} (F : Framework X Y) (S : Finset (Entity X)) :
    F.star (Entity.finsetEntity S) = Entity.finsetEntity (S.image F.star) := by
  induction S using Finset.induction_on with
  | empty =>
      have h0 : Entity.finsetEntity (∅ : Finset (Entity X)) = ∅ :=
        Entity.set_ext (Entity.isSet_finsetEntity _) Entity.isSet_empty fun z ↦ by simp
      have h0' : Entity.finsetEntity (∅ : Finset (Entity Y)) = ∅ :=
        Entity.set_ext (Entity.isSet_finsetEntity _) Entity.isSet_empty fun z ↦ by simp
      rw [h0, Finset.image_empty, h0', F.star_empty]
  | @insert a s _ ih =>
      have hins : Entity.finsetEntity (insert a s) =
          Entity.union (Entity.singleton a) (Entity.finsetEntity s) :=
        Entity.set_ext (Entity.isSet_finsetEntity _) (Entity.isSet_union _ _) fun z ↦ by simp
      have hins' : Entity.finsetEntity (insert (F.star a) (s.image F.star)) =
          Entity.union (Entity.singleton (F.star a)) (Entity.finsetEntity (s.image F.star)) :=
        Entity.set_ext (Entity.isSet_finsetEntity _) (Entity.isSet_union _ _) fun z ↦ by simp
      rw [hins, Finset.image_insert, hins', F.star_union, F.star_singleton, ih]

/-- Goldblatt §13.8 Bullet 8 (p. 168): If `A` is a finite set entity (`A.IsSet ∧ A.extSet.Finite`),
then `*A = {*a : a ∈ A}` (`y ∈ *A ↔ ∃ a ∈ A, y = *a`). -/
theorem Framework.mem_star_iff_of_finite {X Y : Type*} (F : Framework X Y) {A : Entity X}
    (hAset : A.IsSet) (hAfin : A.extSet.Finite) {y : Entity Y} :
    y ∈ F.star A ↔ ∃ a ∈ A, y = F.star a := by
  have hAeq : A = Entity.finsetEntity hAfin.toFinset :=
    Entity.set_ext hAset (Entity.isSet_finsetEntity _) fun z ↦ by simp
  rw [hAeq, F.star_finsetEntity, Entity.mem_finsetEntity_iff, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, by simpa [ ← hAeq ] using Entity.mem_finsetEntity_iff.2 ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, Entity.mem_finsetEntity_iff.1 ha, rfl⟩

/-- Goldblatt §13.8 Bullet 13 (p. 169) & **Exercise 13.8.1**: `*(A × B) = *A × *B`. -/
@[simp]
theorem Framework.star_prod {X Y : Type*} (F : Framework X Y) (A B : Entity X) :
    F.star (Entity.prod A B) = Entity.prod (F.star A) (F.star B) := by
  let φ₁ : UFormula X :=
    .forallIn 0 (.const A) (.forallIn 1 (.const B)
      (.mem (UTerm.pair (.var 0) (.var 1)) (.const (Entity.prod A B))))
  have hs₁ : IsSentence φ₁ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v
    simp [φ₁, freeVarsUFormula, freeVarsUTerm]; omega
  have hstd₁ : SentenceHolds φ₁ :=
    ⟨A, rfl, fun a ha ↦ ⟨B, rfl, fun b hb ↦
      ⟨Entity.kpair a b, Entity.prod A B, by simp, rfl,
        Entity.kpair_mem_prod_iff.2 ⟨ha, hb⟩⟩⟩⟩
  obtain ⟨A₀, hA₀, hall₁⟩ := (F.transfer φ₁ hs₁).1 hstd₁
  obtain rfl := Option.some.inj hA₀
  let φ₂ : UFormula X :=
    .forallIn 0 (.const (Entity.prod A B))
      (.existsIn 1 (.const A) (.existsIn 2 (.const B)
        (.eq (.var 0) (UTerm.pair (.var 1) (.var 2)))))
  have hs₂ : IsSentence φ₂ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v
    simp [φ₂, freeVarsUFormula, freeVarsUTerm]; omega
  have hstd₂ : SentenceHolds φ₂ := by
    refine ⟨Entity.prod A B, rfl, fun p hp ↦ ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Entity.mem_prod_iff.1 hp
    exact ⟨A, rfl, a, ha, B, rfl, b, hb, Entity.kpair a b, by simp, by simp⟩
  obtain ⟨P₀, hP₀, hall₂⟩ := (F.transfer φ₂ hs₂).1 hstd₂
  obtain rfl := Option.some.inj hP₀
  refine Entity.set_ext (F.isSet_star_iff.2 (Entity.isSet_prod A B)) (Entity.isSet_prod _ _) fun y ↦ ?_
  rw [Entity.mem_prod_iff]
  constructor
  · intro hy
    obtain ⟨A₁, hA₁, a', ha', B₁, hB₁, b', hb', z, hz1, hz2⟩ := hall₂ y hy
    obtain rfl := Option.some.inj hA₁
    obtain rfl := Option.some.inj hB₁
    have hyz : y = z := Option.some.inj (by simpa using hz1)
    have hpz : Entity.kpair a' b' = z := Option.some.inj (by simpa using hz2)
    exact ⟨a', ha', b', hb', hyz.trans hpz.symm⟩
  · rintro ⟨a', ha', b', hb', rfl⟩
    obtain ⟨B₁, hB₁, hball⟩ := hall₁ a' ha'
    obtain rfl := Option.some.inj hB₁
    obtain ⟨p', P₁, hp', hP₁, hmem⟩ := hball b' hb'
    obtain rfl := Option.some.inj hP₁
    have hpeq : Entity.kpair a' b' = p' := Option.some.inj (by simpa using hp')
    exact hpeq ▸ hmem

/-- Recursive decomposition of `Entity.prodTuple` at `m + 3`:
`prodTuple (m := m + 3) A = prod (prodTuple (Fin.init A)) (A (Fin.last (m + 2)))`
(Goldblatt §13.2 & §13.8, pp. 160, 169). -/
theorem Entity.prodTuple_succ_succ_succ {X : Type*} {m : ℕ} (A : Fin (m + 3) → Entity X) :
    Entity.prodTuple A =
      Entity.prod (Entity.prodTuple (Fin.init A)) (A (Fin.last (m + 2))) := by
  refine Entity.set_ext (Entity.isSet_prodTuple A) (Entity.isSet_prod _ _) fun p ↦ ?_
  rw [Entity.mem_prodTuple_iff, Entity.mem_prod_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Entity.ktuple (Fin.init v),
      Entity.mem_prodTuple_iff.2 ⟨Fin.init v, fun j ↦ hv j.castSucc, rfl⟩,
      v (Fin.last (m + 2)), hv (Fin.last (m + 2)), rfl⟩
  · rintro ⟨q, hq, b, hb, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Entity.mem_prodTuple_iff.1 hq
    refine ⟨Fin.snoc u b, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simpa using hb
      · intro j
        simpa [Fin.init] using hu j
    · simp [Entity.ktuple, Fin.init_snoc]

/-- Goldblatt §13.8 Bullet 13 (p. 169) & **Exercise 13.8.1**:
`*(A₁ × ⋯ × A_m) = *A₁ × ⋯ × *A_m` (hence `*(A^m) = (*A)^m`). -/
@[simp]
theorem Framework.star_prodTuple {X Y : Type*} (F : Framework X Y) :
    ∀ {m : ℕ} (A : Fin m → Entity X),
      F.star (Entity.prodTuple A) = Entity.prodTuple (fun i ↦ F.star (A i))
  | 0, A => by
      have h1 : Entity.prodTuple A = Entity.singleton ∅ := by
        refine Entity.set_ext (Entity.isSet_prodTuple A) (Entity.isSet_singleton _) fun p ↦ ?_
        simp only [Entity.mem_prodTuple_iff, Entity.ktuple, Entity.mem_singleton_iff]
        exact ⟨fun ⟨_, _, h⟩ ↦ h, fun h ↦ ⟨Fin.elim0, fun i ↦ Fin.elim0 i, h⟩⟩
      have h2 : Entity.prodTuple (fun i : Fin 0 ↦ F.star (A i)) = Entity.singleton ∅ := by
        refine Entity.set_ext (Entity.isSet_prodTuple _) (Entity.isSet_singleton _) fun p ↦ ?_
        simp only [Entity.mem_prodTuple_iff, Entity.ktuple, Entity.mem_singleton_iff]
        exact ⟨fun ⟨_, _, h⟩ ↦ h, fun h ↦ ⟨Fin.elim0, fun i ↦ Fin.elim0 i, h⟩⟩
      rw [h1, h2, F.star_singleton, F.star_empty]
  | 1, A => by
      have hEq := F.star_set_eq_of_bounded (S := Entity.prodTuple A) (T := A 0)
        (φ := .eq (.var 0) (.var 0))
        (Entity.isSet_prodTuple A)
        (fun p hp ↦ by
          obtain ⟨v, hv, rfl⟩ := Entity.mem_prodTuple_iff.1 hp
          exact hv 0)
        (by simp [freeVarsUFormula, freeVarsUTerm])
        (fun a ha ↦ by
          simp only [Entity.mem_prodTuple_iff, Entity.ktuple, Holds, evalUTerm_var]
          exact ⟨fun _ ↦ ⟨a, rfl, rfl⟩, fun _ ↦ ⟨fun _ ↦ a, fun i ↦ by fin_cases i; exact ha, rfl⟩⟩)
      refine Entity.set_ext (F.isSet_star_iff.2 (Entity.isSet_prodTuple A)) (Entity.isSet_prodTuple _) fun y ↦ ?_
      rw [hEq, Entity.mem_setOfBounded ((F.star (A 0)).isBoundedRank_extSet.subset fun _ h ↦ h.1),
        Entity.mem_prodTuple_iff]
      simp only [starFormula, starTerm, Holds, evalUTerm_var, Entity.ktuple]
      constructor
      · rintro ⟨hy, _⟩
        exact ⟨fun _ ↦ y, fun i ↦ by fin_cases i; exact hy, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨hv 0, v 0, rfl, rfl⟩
  | 2, A => by
      have h1 : Entity.prodTuple A = Entity.prod (A 0) (A 1) := by
        refine Entity.set_ext (Entity.isSet_prodTuple A) (Entity.isSet_prod _ _) fun p ↦ ?_
        rw [Entity.mem_prodTuple_iff, Entity.mem_prod_iff]
        exact ⟨fun ⟨v, hv, hp⟩ ↦ ⟨v 0, hv 0, v 1, hv 1, hp⟩,
          fun ⟨a, ha, b, hb, hp⟩ ↦ ⟨![a, b], fun i ↦ by fin_cases i <;> assumption, hp⟩⟩
      have h2 : Entity.prodTuple (fun i : Fin 2 ↦ F.star (A i)) =
          Entity.prod (F.star (A 0)) (F.star (A 1)) := by
        refine Entity.set_ext (Entity.isSet_prodTuple _) (Entity.isSet_prod _ _) fun p ↦ ?_
        rw [Entity.mem_prodTuple_iff, Entity.mem_prod_iff]
        exact ⟨fun ⟨v, hv, hp⟩ ↦ ⟨v 0, hv 0, v 1, hv 1, hp⟩,
          fun ⟨a, ha, b, hb, hp⟩ ↦ ⟨![a, b], fun i ↦ by fin_cases i <;> assumption, hp⟩⟩
      rw [h1, h2, F.star_prod]
  | m + 3, A => by
      rw [Entity.prodTuple_succ_succ_succ, Entity.prodTuple_succ_succ_succ, F.star_prod,
        F.star_prodTuple (m := m + 2)]
      rfl

/-- Helper: every coordinate `a`, `b` of a Kuratowski pair `(a, b) ∈ F.star R` belongs to
`F.star (Entity.sUnion (Entity.sUnion R))` (Goldblatt §13.4 & §13.8, pp. 161, 169). -/
theorem Framework.coords_mem_star_sUnion_sUnion {X Y : Type*} (F : Framework X Y)
    {R : Entity X} {a b : Entity Y} (hp : Entity.kpair a b ∈ F.star R) :
    a ∈ F.star (Entity.sUnion (Entity.sUnion R)) ∧
      b ∈ F.star (Entity.sUnion (Entity.sUnion R)) := by
  let U₂ : Entity X := Entity.sUnion (Entity.sUnion R)
  let φ : UFormula X :=
    .forallIn 0 (.const R) (.forallIn 1 (.var 0) (.forallIn 2 (.var 1)
      (.mem (.var 2) (.const U₂))))
  have hs : IsSentence φ := by simp [φ, IsSentence, freeVarsUFormula, freeVarsUTerm]
  have hstd : SentenceHolds φ := by
    refine ⟨R, rfl, fun r hr ↦ ⟨r, by simp, fun u hur ↦ ⟨u, by simp, fun x hxu ↦ ?_⟩⟩⟩
    exact ⟨x, U₂, by simp, rfl,
      Entity.mem_sUnion_iff.2 ⟨u, Entity.mem_sUnion_iff.2 ⟨r, hr, hur⟩, hxu⟩⟩
  obtain ⟨R₀, hR₀, hall⟩ := (F.transfer φ hs).1 hstd
  obtain rfl := Option.some.inj hR₀
  obtain ⟨p₀, hp₀, huall⟩ := hall (Entity.kpair a b) hp
  obtain rfl := Option.some.inj hp₀
  have hu : Entity.upair a b ∈ Entity.kpair a b := Entity.mem_upair_iff.2 (Or.inr rfl)
  obtain ⟨u₀, hu₀, hxall⟩ := huall (Entity.upair a b) hu
  obtain rfl := Option.some.inj hu₀
  obtain ⟨a₀, Ua, ha₀, hUa, hma⟩ := hxall a (Entity.mem_upair_iff.2 (Or.inl rfl))
  obtain ⟨b₀, Ub, hb₀, hUb, hmb⟩ := hxall b (Entity.mem_upair_iff.2 (Or.inr rfl))
  obtain rfl := Option.some.inj ha₀
  obtain rfl := Option.some.inj hUa
  obtain rfl := Option.some.inj hb₀
  obtain rfl := Option.some.inj hUb
  exact ⟨hma, hmb⟩

/-- Goldblatt §13.8 Bullet 12 (p. 169) & **Exercise 13.8.1**: If `R` is an `m`-ary relation (`m ≥ 2`),
then `*R` is an `m`-ary relation (and vice versa). -/
theorem Framework.isRelArity_star_iff {X Y : Type*} (F : Framework X Y) {m : ℕ} (hm : 2 ≤ m)
    {R : Entity X} :
    (F.star R).IsRelArity m ↔ R.IsRelArity m := by
  let T : Entity X := vStageEntity X (R.rank + 1)
  have hRsub : ∀ p ∈ R, p ∈ T := fun p hp ↦
    mem_vStageEntity.2 (mem_vStage_iff_rank_le.2 (by have := Entity.rank_lt_of_mem hp; omega))
  have hTtrans : T.IsTransitiveSet := isTransitiveSet_vStageEntity_succ X R.rank
  constructor
  · rintro ⟨hRset, hRtup⟩
    refine ⟨F.isSet_star_iff.1 hRset, ?_⟩
    have hstarTtrans : (F.star T).IsTransitiveSet := F.isTransitiveSet_star_iff.2 hTtrans
    have hcoords_in : ∀ {k : ℕ} (_ : 2 ≤ k) (w : Fin k → Entity Y),
        Entity.ktuple w ∈ F.star T → ∀ i, w i ∈ F.star T := by
      intro k hk w hkw
      induction k with
      | zero => omega
      | succ k ih =>
          rcases k with _ | _ | k'
          · omega
          · have hu : Entity.upair (w 0) (w 1) ∈ F.star T :=
              hstarTtrans.2 _ hkw _ (Entity.mem_upair_iff.2 (Or.inr rfl))
            intro i
            fin_cases i
            · exact hstarTtrans.2 _ hu _ (Entity.mem_upair_iff.2 (Or.inl rfl))
            · exact hstarTtrans.2 _ hu _ (Entity.mem_upair_iff.2 (Or.inr rfl))
          · have hu : Entity.upair (Entity.ktuple (m := k' + 2) (Fin.init w)) (w (Fin.last (k' + 2))) ∈ F.star T :=
              hstarTtrans.2 _ hkw _ (Entity.mem_upair_iff.2 (Or.inr rfl))
            have hinit : Entity.ktuple (m := k' + 2) (Fin.init w) ∈ F.star T :=
              hstarTtrans.2 _ hu _ (Entity.mem_upair_iff.2 (Or.inl rfl))
            have hlast : w (Fin.last (k' + 2)) ∈ F.star T :=
              hstarTtrans.2 _ hu _ (Entity.mem_upair_iff.2 (Or.inr rfl))
            intro i
            refine Fin.lastCases hlast (fun j ↦ ?_) i
            exact ih (by omega) (Fin.init w) hinit j
    have hstarSub : ∀ q ∈ F.star R, q ∈ Entity.prodTuple (fun _ : Fin m ↦ F.star T) := by
      intro q hq
      obtain ⟨w, rfl⟩ := hRtup q hq
      have hqT : Entity.ktuple w ∈ F.star T := (F.subset_star_iff.2 hRsub) _ hq
      exact Entity.mem_prodTuple_iff.2 ⟨w, hcoords_in hm w hqT, rfl⟩
    rw [← F.star_prodTuple] at hstarSub
    have hRprod : ∀ p ∈ R, p ∈ Entity.prodTuple (fun _ : Fin m ↦ T) :=
      F.subset_star_iff.1 hstarSub
    intro p hp
    obtain ⟨v, _, rfl⟩ := Entity.mem_prodTuple_iff.1 (hRprod p hp)
    exact ⟨v, rfl⟩
  · rintro ⟨hRset, hRtup⟩
    refine ⟨F.isSet_star_iff.2 hRset, ?_⟩
    have hcoords_in : ∀ {k : ℕ} (_ : 2 ≤ k) (v : Fin k → Entity X),
        Entity.ktuple v ∈ T → ∀ i, v i ∈ T := by
      intro k hk v hkv
      induction k with
      | zero => omega
      | succ k ih =>
          rcases k with _ | _ | k'
          · omega
          · have hu : Entity.upair (v 0) (v 1) ∈ T :=
              hTtrans.2 _ hkv _ (Entity.mem_upair_iff.2 (Or.inr rfl))
            intro i
            fin_cases i
            · exact hTtrans.2 _ hu _ (Entity.mem_upair_iff.2 (Or.inl rfl))
            · exact hTtrans.2 _ hu _ (Entity.mem_upair_iff.2 (Or.inr rfl))
          · have hu : Entity.upair (Entity.ktuple (m := k' + 2) (Fin.init v)) (v (Fin.last (k' + 2))) ∈ T :=
              hTtrans.2 _ hkv _ (Entity.mem_upair_iff.2 (Or.inr rfl))
            have hinit := hTtrans.2 _ hu _ (Entity.mem_upair_iff.2 (Or.inl rfl))
            have hlast := hTtrans.2 _ hu _ (Entity.mem_upair_iff.2 (Or.inr rfl))
            intro i
            refine Fin.lastCases hlast (fun j ↦ ?_) i
            exact ih (by omega) (Fin.init v) hinit j
    have hRprod : ∀ p ∈ R, p ∈ Entity.prodTuple (fun _ : Fin m ↦ T) := by
      intro p hp
      have hpT : p ∈ T := hRsub p hp
      obtain ⟨v, rfl⟩ := hRtup p hp
      exact Entity.mem_prodTuple_iff.2 ⟨v, hcoords_in hm v hpT, rfl⟩
    have hstarProd : ∀ q ∈ F.star R, q ∈ Entity.prodTuple (fun _ : Fin m ↦ F.star T) := by
      rw [← F.star_prodTuple]
      exact F.subset_star_iff.2 hRprod
    intro q hq
    obtain ⟨w, _, rfl⟩ := Entity.mem_prodTuple_iff.1 (hstarProd q hq)
    exact ⟨w, rfl⟩

/-- Equivalence between `IsRelArity 2` and `IsBinaryRel` (Goldblatt §13.2, p. 160). -/
theorem Entity.isRelArity_two_iff_isBinaryRel {X : Type*} {S : Entity X} :
    S.IsRelArity 2 ↔ S.IsBinaryRel := by
  refine and_congr_right fun _ ↦ forall₂_congr fun p _ ↦ ?_
  constructor
  · rintro ⟨v, hp⟩
    exact ⟨v 0, v 1, hp⟩
  · rintro ⟨a, b, hp⟩
    exact ⟨![a, b], hp.trans (Entity.ktuple_two a b).symm⟩

/-- Binary relation preservation: `(F.star R).IsBinaryRel ↔ R.IsBinaryRel`
(Goldblatt §13.8, p. 169). -/
@[simp]
theorem Framework.isBinaryRel_star_iff {X Y : Type*} (F : Framework X Y) {R : Entity X} :
    (F.star R).IsBinaryRel ↔ R.IsBinaryRel := by
  rw [← Entity.isRelArity_two_iff_isBinaryRel, ← Entity.isRelArity_two_iff_isBinaryRel]
  exact F.isRelArity_star_iff (m := 2) (by omega)

/-- Goldblatt §13.8 Bullet 14 (p. 169) & **Exercise 13.8.1**: `*(dom R) = dom *R`. -/
@[simp]
theorem Framework.star_relDom {X Y : Type*} (F : Framework X Y) (R : Entity X) :
    F.star (Entity.relDom R) = Entity.relDom (F.star R) := by
  let U₂ : Entity X := Entity.sUnion (Entity.sUnion R)
  have hsub : ∀ a ∈ Entity.relDom R, a ∈ U₂ := by
    intro a ha
    obtain ⟨b, hp⟩ := Entity.mem_relDom_iff.1 ha
    exact Entity.mem_sUnion_iff.2 ⟨Entity.upair a b,
      Entity.mem_sUnion_iff.2 ⟨Entity.kpair a b, hp, Entity.mem_upair_iff.2 (Or.inr rfl)⟩,
      Entity.mem_upair_iff.2 (Or.inl rfl)⟩
  have hEq := F.star_set_eq_of_bounded (S := Entity.relDom R) (T := U₂)
    (φ := .existsIn 1 (.const U₂) (.mem (UTerm.pair (.var 0) (.var 1)) (.const R)))
    (Entity.isSet_relDom R) hsub
    (by simp [freeVarsUFormula, freeVarsUTerm]; omega)
    (fun a _ ↦ by
      rw [Entity.mem_relDom_iff]
      constructor
      · rintro ⟨b, hp⟩
        have hbU : b ∈ U₂ := Entity.mem_sUnion_iff.2 ⟨Entity.upair a b,
          Entity.mem_sUnion_iff.2 ⟨Entity.kpair a b, hp, Entity.mem_upair_iff.2 (Or.inr rfl)⟩,
          Entity.mem_upair_iff.2 (Or.inr rfl)⟩
        exact ⟨U₂, rfl, b, hbU, Entity.kpair a b, R, by simp, rfl, hp⟩
      · rintro ⟨_, _, b, _, p, R', hp, hR', hm⟩
        obtain rfl := Option.some.inj hR'
        have hpeq : Entity.kpair a b = p := Option.some.inj (by simpa using hp)
        exact ⟨b, hpeq ▸ hm⟩)
  refine Entity.set_ext (F.isSet_star_iff.2 (Entity.isSet_relDom R)) (Entity.isSet_relDom _) fun a' ↦ ?_
  rw [hEq, Entity.mem_setOfBounded ((F.star U₂).isBoundedRank_extSet.subset fun _ h ↦ h.1),
    Entity.mem_relDom_iff]
  constructor
  · rintro ⟨_, _, _, b', _, p, R', hp, hR', hm⟩
    obtain rfl := Option.some.inj hR'
    have hpeq : Entity.kpair a' b' = p := Option.some.inj (by simpa using hp)
    exact ⟨b', hpeq ▸ hm⟩
  · rintro ⟨b', hp⟩
    obtain ⟨haU, hbU⟩ := F.coords_mem_star_sUnion_sUnion hp
    exact ⟨haU, F.star U₂, rfl, b', hbU, Entity.kpair a' b', F.star R, by simp, rfl, hp⟩

/-- Goldblatt §13.8 Bullet 14 (p. 169) & **Exercise 13.8.1**: `*(ran R) = ran *R`. -/
@[simp]
theorem Framework.star_relRan {X Y : Type*} (F : Framework X Y) (R : Entity X) :
    F.star (Entity.relRan R) = Entity.relRan (F.star R) := by
  let U₂ : Entity X := Entity.sUnion (Entity.sUnion R)
  have hsub : ∀ b ∈ Entity.relRan R, b ∈ U₂ := by
    intro b hb
    obtain ⟨a, hp⟩ := Entity.mem_relRan_iff.1 hb
    exact Entity.mem_sUnion_iff.2 ⟨Entity.upair a b,
      Entity.mem_sUnion_iff.2 ⟨Entity.kpair a b, hp, Entity.mem_upair_iff.2 (Or.inr rfl)⟩,
      Entity.mem_upair_iff.2 (Or.inr rfl)⟩
  have hEq := F.star_set_eq_of_bounded (S := Entity.relRan R) (T := U₂)
    (φ := .existsIn 1 (.const U₂) (.mem (UTerm.pair (.var 1) (.var 0)) (.const R)))
    (Entity.isSet_relRan R) hsub
    (by simp [freeVarsUFormula, freeVarsUTerm])
    (fun b _ ↦ by
      rw [Entity.mem_relRan_iff]
      constructor
      · rintro ⟨a, hp⟩
        have haU : a ∈ U₂ := Entity.mem_sUnion_iff.2 ⟨Entity.upair a b,
          Entity.mem_sUnion_iff.2 ⟨Entity.kpair a b, hp, Entity.mem_upair_iff.2 (Or.inr rfl)⟩,
          Entity.mem_upair_iff.2 (Or.inl rfl)⟩
        exact ⟨U₂, rfl, a, haU, Entity.kpair a b, R, by simp, rfl, hp⟩
      · rintro ⟨_, _, a, _, p, R', hp, hR', hm⟩
        obtain rfl := Option.some.inj hR'
        have hpeq : Entity.kpair a b = p := Option.some.inj (by simpa using hp)
        exact ⟨a, hpeq ▸ hm⟩)
  refine Entity.set_ext (F.isSet_star_iff.2 (Entity.isSet_relRan R)) (Entity.isSet_relRan _) fun b' ↦ ?_
  rw [hEq, Entity.mem_setOfBounded ((F.star U₂).isBoundedRank_extSet.subset fun _ h ↦ h.1),
    Entity.mem_relRan_iff]
  constructor
  · rintro ⟨_, _, _, a', _, p, R', hp, hR', hm⟩
    obtain rfl := Option.some.inj hR'
    have hpeq : Entity.kpair a' b' = p := Option.some.inj (by simpa using hp)
    exact ⟨a', hpeq ▸ hm⟩
  · rintro ⟨a', hp⟩
    obtain ⟨haU, hbU⟩ := F.coords_mem_star_sUnion_sUnion hp
    exact ⟨hbU, F.star U₂, rfl, a', haU, Entity.kpair a' b', F.star R, by simp, rfl, hp⟩

/-- Goldblatt §13.8 Bullet 14 (p. 169) & **Exercise 13.8.1**: `*(R⁻¹) = (*R)⁻¹`. -/
@[simp]
theorem Framework.star_relInv {X Y : Type*} (F : Framework X Y) (R : Entity X) :
    F.star (Entity.relInv R) = Entity.relInv (F.star R) := by
  let P : Entity X := Entity.prod (Entity.relRan R) (Entity.relDom R)
  have hsub : ∀ p ∈ Entity.relInv R, p ∈ P := by
    intro p hp
    obtain ⟨a, b, hab, rfl⟩ := Entity.mem_relInv_iff.1 hp
    exact Entity.kpair_mem_prod_iff.2 ⟨Entity.mem_relRan_iff.2 ⟨a, hab⟩, Entity.mem_relDom_iff.2 ⟨b, hab⟩⟩
  have hEq := F.star_set_eq_of_bounded (S := Entity.relInv R) (T := P)
    (φ := .existsIn 1 (.const (Entity.relDom R)) (.existsIn 2 (.const (Entity.relRan R))
      (.conj (.mem (UTerm.pair (.var 1) (.var 2)) (.const R))
             (.eq (.var 0) (UTerm.pair (.var 2) (.var 1))))))
    (Entity.isSet_relInv R) hsub
    (by simp [freeVarsUFormula, freeVarsUTerm]; omega)
    (fun p _ ↦ by
      rw [Entity.mem_relInv_iff]
      constructor
      · rintro ⟨a, b, hab, rfl⟩
        exact ⟨Entity.relDom R, rfl, a, Entity.mem_relDom_iff.2 ⟨b, hab⟩,
          Entity.relRan R, rfl, b, Entity.mem_relRan_iff.2 ⟨a, hab⟩,
          ⟨Entity.kpair a b, R, by simp, rfl, hab⟩,
          ⟨Entity.kpair b a, by simp, by simp⟩⟩
      · rintro ⟨_, _, a, _, _, _, b, _, ⟨_, R', hp1, hR', hab⟩, ⟨z, hz1, hz2⟩⟩
        obtain rfl := Option.some.inj hR'
        have h1 : Entity.kpair a b = _ := Option.some.inj (by simpa using hp1)
        have h2 : p = z := Option.some.inj (by simpa using hz1)
        have h3 : Entity.kpair b a = z := Option.some.inj (by simpa using hz2)
        exact ⟨a, b, h1 ▸ hab, h2.trans h3.symm⟩)
  refine Entity.set_ext (F.isSet_star_iff.2 (Entity.isSet_relInv R)) (Entity.isSet_relInv _) fun q ↦ ?_
  rw [hEq, Entity.mem_setOfBounded ((F.star P).isBoundedRank_extSet.subset fun _ h ↦ h.1),
    Entity.mem_relInv_iff]
  constructor
  · rintro ⟨_, _, _, a', _, _, _, b', _, ⟨_, R', hp1, hR', hab⟩, ⟨z, hz1, hz2⟩⟩
    obtain rfl := Option.some.inj hR'
    have h1 : Entity.kpair a' b' = _ := Option.some.inj (by simpa using hp1)
    have h2 : q = z := Option.some.inj (by simpa using hz1)
    have h3 : Entity.kpair b' a' = z := Option.some.inj (by simpa using hz2)
    exact ⟨a', b', h1 ▸ hab, h2.trans h3.symm⟩
  · rintro ⟨a', b', hab, rfl⟩
    have haD : a' ∈ F.star (Entity.relDom R) := by
      rw [F.star_relDom]; exact Entity.mem_relDom_iff.2 ⟨b', hab⟩
    have hbR : b' ∈ F.star (Entity.relRan R) := by
      rw [F.star_relRan]; exact Entity.mem_relRan_iff.2 ⟨a', hab⟩
    have hqP : Entity.kpair b' a' ∈ F.star P := by
      simp only [P, F.star_prod, Entity.kpair_mem_prod_iff]
      exact ⟨hbR, haD⟩
    exact ⟨hqP, F.star (Entity.relDom R), rfl, a', haD, F.star (Entity.relRan R), rfl, b', hbR,
      ⟨Entity.kpair a' b', F.star R, by simp, rfl, hab⟩,
      ⟨Entity.kpair b' a', by simp, by simp⟩⟩

/-- Goldblatt §13.8 Bullet 14 (p. 169) & **Exercise 13.8.1**: `*(R''(C)) = (*R)''(*C)`. -/
@[simp]
theorem Framework.star_relImage {X Y : Type*} (F : Framework X Y) (R C : Entity X) :
    F.star (Entity.relImage R C) = Entity.relImage (F.star R) (F.star C) := by
  have hsub : ∀ b ∈ Entity.relImage R C, b ∈ Entity.relRan R := by
    intro b hb
    obtain ⟨a, _, hp⟩ := Entity.mem_relImage_iff.1 hb
    exact Entity.mem_relRan_iff.2 ⟨a, hp⟩
  have hEq := F.star_set_eq_of_bounded (S := Entity.relImage R C) (T := Entity.relRan R)
    (φ := .existsIn 1 (.const C) (.mem (UTerm.pair (.var 1) (.var 0)) (.const R)))
    (Entity.isSet_relImage R C) hsub
    (by simp [freeVarsUFormula, freeVarsUTerm])
    (fun b _ ↦ by
      rw [Entity.mem_relImage_iff]
      constructor
      · rintro ⟨a, haC, hp⟩
        exact ⟨C, rfl, a, haC, Entity.kpair a b, R, by simp, rfl, hp⟩
      · rintro ⟨C', hC', a, haC, p, R', hp, hR', hm⟩
        obtain rfl := Option.some.inj hC'
        obtain rfl := Option.some.inj hR'
        have hpeq : Entity.kpair a b = p := Option.some.inj (by simpa using hp)
        exact ⟨a, haC, hpeq ▸ hm⟩)
  refine Entity.set_ext (F.isSet_star_iff.2 (Entity.isSet_relImage R C)) (Entity.isSet_relImage _ _) fun b' ↦ ?_
  rw [hEq, Entity.mem_setOfBounded ((F.star (Entity.relRan R)).isBoundedRank_extSet.subset fun _ h ↦ h.1),
    Entity.mem_relImage_iff]
  constructor
  · rintro ⟨_, C', hC', a', haC, p, R', hp, hR', hm⟩
    obtain rfl := Option.some.inj hC'
    obtain rfl := Option.some.inj hR'
    have hpeq : Entity.kpair a' b' = p := Option.some.inj (by simpa using hp)
    exact ⟨a', haC, hpeq ▸ hm⟩
  · rintro ⟨a', haC, hp⟩
    have hbR : b' ∈ F.star (Entity.relRan R) := by
      rw [F.star_relRan]; exact Entity.mem_relRan_iff.2 ⟨a', hp⟩
    exact ⟨hbR, F.star C, rfl, a', haC, Entity.kpair a' b', F.star R, by simp, rfl, hp⟩

/-- Goldblatt §13.8 Bullet 14 (p. 169) & **Exercise 13.8.1**: `*(R⁻¹(D)) = (*R)⁻¹(*D)`. -/
@[simp]
theorem Framework.star_relPreimage {X Y : Type*} (F : Framework X Y) (R D : Entity X) :
    F.star (Entity.relPreimage R D) = Entity.relPreimage (F.star R) (F.star D) := by
  have hsub : ∀ a ∈ Entity.relPreimage R D, a ∈ Entity.relDom R := by
    intro a ha
    obtain ⟨b, _, hp⟩ := Entity.mem_relPreimage_iff.1 ha
    exact Entity.mem_relDom_iff.2 ⟨b, hp⟩
  have hEq := F.star_set_eq_of_bounded (S := Entity.relPreimage R D) (T := Entity.relDom R)
    (φ := .existsIn 1 (.const D) (.mem (UTerm.pair (.var 0) (.var 1)) (.const R)))
    (Entity.isSet_relPreimage R D) hsub
    (by simp [freeVarsUFormula, freeVarsUTerm]; omega)
    (fun a _ ↦ by
      rw [Entity.mem_relPreimage_iff]
      constructor
      · rintro ⟨b, hbD, hp⟩
        exact ⟨D, rfl, b, hbD, Entity.kpair a b, R, by simp, rfl, hp⟩
      · rintro ⟨D', hD', b, hbD, p, R', hp, hR', hm⟩
        obtain rfl := Option.some.inj hD'
        obtain rfl := Option.some.inj hR'
        have hpeq : Entity.kpair a b = p := Option.some.inj (by simpa using hp)
        exact ⟨b, hbD, hpeq ▸ hm⟩)
  refine Entity.set_ext (F.isSet_star_iff.2 (Entity.isSet_relPreimage R D)) (Entity.isSet_relPreimage _ _) fun a' ↦ ?_
  rw [hEq, Entity.mem_setOfBounded ((F.star (Entity.relDom R)).isBoundedRank_extSet.subset fun _ h ↦ h.1),
    Entity.mem_relPreimage_iff]
  constructor
  · rintro ⟨_, D', hD', b', hbD, p, R', hp, hR', hm⟩
    obtain rfl := Option.some.inj hD'
    obtain rfl := Option.some.inj hR'
    have hpeq : Entity.kpair a' b' = p := Option.some.inj (by simpa using hp)
    exact ⟨b', hbD, hpeq ▸ hm⟩
  · rintro ⟨b', hbD, hp⟩
    have haD : a' ∈ F.star (Entity.relDom R) := by
      rw [F.star_relDom]; exact Entity.mem_relDom_iff.2 ⟨b', hp⟩
    exact ⟨haD, F.star D, rfl, b', hbD, Entity.kpair a' b', F.star R, by simp, rfl, hp⟩

/-- Goldblatt §13.8 Bullet 15 (p. 169) & **Exercise 13.8.1**: `*(R ∘ S) = *R ∘ *S`. -/
@[simp]
theorem Framework.star_relComp {X Y : Type*} (F : Framework X Y) (R S : Entity X) :
    F.star (Entity.relComp R S) = Entity.relComp (F.star R) (F.star S) := by
  let P : Entity X := Entity.prod (Entity.relDom R) (Entity.relRan S)
  have hsub : ∀ p ∈ Entity.relComp R S, p ∈ P := by
    intro p hp
    obtain ⟨a, b, c, hR, hS, rfl⟩ := Entity.mem_relComp_iff.1 hp
    exact Entity.kpair_mem_prod_iff.2 ⟨Entity.mem_relDom_iff.2 ⟨b, hR⟩, Entity.mem_relRan_iff.2 ⟨b, hS⟩⟩
  have hEq := F.star_set_eq_of_bounded (S := Entity.relComp R S) (T := P)
    (φ := .existsIn 1 (.const (Entity.relDom R))
      (.existsIn 2 (.const (Entity.relRan R))
        (.existsIn 3 (.const (Entity.relRan S))
          (.conj (.mem (UTerm.pair (.var 1) (.var 2)) (.const R))
            (.conj (.mem (UTerm.pair (.var 2) (.var 3)) (.const S))
                   (.eq (.var 0) (UTerm.pair (.var 1) (.var 3))))))))
    (Entity.isSet_relComp R S) hsub
    (by simp [freeVarsUFormula, freeVarsUTerm]; omega)
    (fun p _ ↦ by
      rw [Entity.mem_relComp_iff]
      constructor
      · rintro ⟨a, b, c, hR, hS, rfl⟩
        exact ⟨Entity.relDom R, rfl, a, Entity.mem_relDom_iff.2 ⟨b, hR⟩,
          Entity.relRan R, rfl, b, Entity.mem_relRan_iff.2 ⟨a, hR⟩,
          Entity.relRan S, rfl, c, Entity.mem_relRan_iff.2 ⟨b, hS⟩,
          ⟨Entity.kpair a b, R, by simp, rfl, hR⟩,
          ⟨Entity.kpair b c, S, by simp, rfl, hS⟩,
          ⟨Entity.kpair a c, by simp, by simp⟩⟩
      · rintro ⟨_, _, a, _, _, _, b, _, _, _, c, _,
          ⟨_, R', hp1, hR', hR⟩, ⟨_, S', hp2, hS', hS⟩, ⟨z, hz1, hz2⟩⟩
        obtain rfl := Option.some.inj hR'
        obtain rfl := Option.some.inj hS'
        have h1 : Entity.kpair a b = _ := Option.some.inj (by simpa using hp1)
        have h2 : Entity.kpair b c = _ := Option.some.inj (by simpa using hp2)
        have h3 : p = z := Option.some.inj (by simpa using hz1)
        have h4 : Entity.kpair a c = z := Option.some.inj (by simpa using hz2)
        exact ⟨a, b, c, h1 ▸ hR, h2 ▸ hS, h3.trans h4.symm⟩)
  refine Entity.set_ext (F.isSet_star_iff.2 (Entity.isSet_relComp R S)) (Entity.isSet_relComp _ _) fun q ↦ ?_
  rw [hEq, Entity.mem_setOfBounded ((F.star P).isBoundedRank_extSet.subset fun _ h ↦ h.1),
    Entity.mem_relComp_iff]
  constructor
  · rintro ⟨_, _, _, a', _, _, _, b', _, _, _, c', _,
      ⟨_, R', hp1, hR', hR⟩, ⟨_, S', hp2, hS', hS⟩, ⟨z, hz1, hz2⟩⟩
    obtain rfl := Option.some.inj hR'
    obtain rfl := Option.some.inj hS'
    have h1 : Entity.kpair a' b' = _ := Option.some.inj (by simpa using hp1)
    have h2 : Entity.kpair b' c' = _ := Option.some.inj (by simpa using hp2)
    have h3 : q = z := Option.some.inj (by simpa using hz1)
    have h4 : Entity.kpair a' c' = z := Option.some.inj (by simpa using hz2)
    exact ⟨a', b', c', h1 ▸ hR, h2 ▸ hS, h3.trans h4.symm⟩
  · rintro ⟨a', b', c', hR, hS, rfl⟩
    have haD : a' ∈ F.star (Entity.relDom R) := by
      rw [F.star_relDom]; exact Entity.mem_relDom_iff.2 ⟨b', hR⟩
    have hbR : b' ∈ F.star (Entity.relRan R) := by
      rw [F.star_relRan]; exact Entity.mem_relRan_iff.2 ⟨a', hR⟩
    have hcS : c' ∈ F.star (Entity.relRan S) := by
      rw [F.star_relRan]; exact Entity.mem_relRan_iff.2 ⟨b', hS⟩
    have hqP : Entity.kpair a' c' ∈ F.star P := by
      simp only [P, F.star_prod, Entity.kpair_mem_prod_iff]
      exact ⟨haD, hcS⟩
    exact ⟨hqP, F.star (Entity.relDom R), rfl, a', haD,
      F.star (Entity.relRan R), rfl, b', hbR,
      F.star (Entity.relRan S), rfl, c', hcS,
      ⟨Entity.kpair a' b', F.star R, by simp, rfl, hR⟩,
      ⟨Entity.kpair b' c', F.star S, by simp, rfl, hS⟩,
      ⟨Entity.kpair a' c', by simp, by simp⟩⟩

/-- Functionality preservation: `(F.star f).IsFuncEntity ↔ f.IsFuncEntity`
(Goldblatt §13.8 Bullet 16, p. 169). -/
@[simp]
theorem Framework.isFuncEntity_star_iff {X Y : Type*} (F : Framework X Y) {f : Entity X} :
    (F.star f).IsFuncEntity ↔ f.IsFuncEntity := by
  let φ : UFormula X :=
    .forallIn 0 (.const (Entity.relDom f))
      (.forallIn 1 (.const (Entity.relRan f))
        (.forallIn 2 (.const (Entity.relRan f))
          (.imp (.conj (.mem (UTerm.pair (.var 0) (.var 1)) (.const f))
                       (.mem (UTerm.pair (.var 0) (.var 2)) (.const f)))
                (.eq (.var 1) (.var 2)))))
  have hs : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v
    simp [φ, freeVarsUFormula, freeVarsUTerm]; omega
  have htr := (F.transfer φ hs).symm
  simp only [Entity.IsFuncEntity, F.isBinaryRel_star_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · intro hsv
    have hstar : SentenceHolds (starFormula F.star φ) := by
      refine ⟨F.star (Entity.relDom f), rfl, fun a' _ ↦ ⟨F.star (Entity.relRan f), rfl,
        fun b' _ ↦ ⟨F.star (Entity.relRan f), rfl, fun c' _ ⟨⟨_, f₁, hp1, hf1, hm1⟩, ⟨_, f₂, hp2, hf2, hm2⟩⟩ ↦ ?_⟩⟩⟩
      obtain rfl := Option.some.inj hf1
      obtain rfl := Option.some.inj hf2
      have h1 : Entity.kpair a' b' = _ := Option.some.inj (by simpa using hp1)
      have h2 : Entity.kpair a' c' = _ := Option.some.inj (by simpa using hp2)
      exact ⟨b', by simp, by simp [hsv a' b' c' (h1 ▸ hm1) (h2 ▸ hm2)]⟩
    obtain ⟨_, hD, hall⟩ := htr.1 hstar
    obtain rfl := Option.some.inj hD
    intro a b c hab hac
    have haD : a ∈ Entity.relDom f := Entity.mem_relDom_iff.2 ⟨b, hab⟩
    have hbR : b ∈ Entity.relRan f := Entity.mem_relRan_iff.2 ⟨a, hab⟩
    have hcR : c ∈ Entity.relRan f := Entity.mem_relRan_iff.2 ⟨a, hac⟩
    obtain ⟨_, hR1, hb_all⟩ := hall a haD
    obtain rfl := Option.some.inj hR1
    obtain ⟨_, hR2, hc_all⟩ := hb_all b hbR
    obtain rfl := Option.some.inj hR2
    obtain ⟨z, hz1, hz2⟩ := hc_all c hcR
      ⟨⟨Entity.kpair a b, f, by simp, rfl, hab⟩,
       ⟨Entity.kpair a c, f, by simp, rfl, hac⟩⟩
    exact (Option.some.inj (by simpa using hz1)).trans (Option.some.inj (by simpa using hz2)).symm
  · intro hsv
    have hstd : SentenceHolds φ := by
      refine ⟨Entity.relDom f, rfl, fun a _ ↦ ⟨Entity.relRan f, rfl,
        fun b _ ↦ ⟨Entity.relRan f, rfl, fun c _ ⟨⟨_, f₁, hp1, hf1, hm1⟩, ⟨_, f₂, hp2, hf2, hm2⟩⟩ ↦ ?_⟩⟩⟩
      obtain rfl := Option.some.inj hf1
      obtain rfl := Option.some.inj hf2
      have h1 : Entity.kpair a b = _ := Option.some.inj (by simpa using hp1)
      have h2 : Entity.kpair a c = _ := Option.some.inj (by simpa using hp2)
      exact ⟨b, by simp, by simp [hsv a b c (h1 ▸ hm1) (h2 ▸ hm2)]⟩
    obtain ⟨_, hD, hall⟩ := htr.2 hstd
    obtain rfl := Option.some.inj hD
    intro a' b' c' hab hac
    have haD : a' ∈ F.star (Entity.relDom f) := by
      rw [F.star_relDom]; exact Entity.mem_relDom_iff.2 ⟨b', hab⟩
    have hbR : b' ∈ F.star (Entity.relRan f) := by
      rw [F.star_relRan]; exact Entity.mem_relRan_iff.2 ⟨a', hab⟩
    have hcR : c' ∈ F.star (Entity.relRan f) := by
      rw [F.star_relRan]; exact Entity.mem_relRan_iff.2 ⟨a', hac⟩
    obtain ⟨_, hR1, hb_all⟩ := hall a' haD
    obtain rfl := Option.some.inj hR1
    obtain ⟨_, hR2, hc_all⟩ := hb_all b' hbR
    obtain rfl := Option.some.inj hR2
    obtain ⟨z, hz1, hz2⟩ := hc_all c' hcR
      ⟨⟨Entity.kpair a' b', F.star f, by simp, rfl, hab⟩,
       ⟨Entity.kpair a' c', F.star f, by simp, rfl, hac⟩⟩
    exact (Option.some.inj (by simpa using hz1)).trans (Option.some.inj (by simpa using hz2)).symm

/-- Relational characterization of `Entity.IsFuncFromTo` (Goldblatt §13.2 & §13.8, pp. 160, 169). -/
theorem Entity.isFuncFromTo_iff_rel {X : Type*} {g C D : Entity X} :
    Entity.IsFuncFromTo g C D ↔
      g.IsFuncEntity ∧ (∀ p ∈ g, p ∈ Entity.prod C D) ∧
        (∀ c ∈ C, c ∈ Entity.relDom g) := by
  constructor
  · rintro ⟨hgset, hgprod, hgsv, hgtot⟩
    refine ⟨⟨⟨hgset, fun p hp ↦ let ⟨a, _, b, _, h⟩ := hgprod p hp; ⟨a, b, h⟩⟩, hgsv⟩,
      fun p hp ↦ Entity.mem_prod_iff.2 (hgprod p hp),
      fun c hc ↦ let ⟨d, _, hp⟩ := hgtot c hc; Entity.mem_relDom_iff.2 ⟨d, hp⟩⟩
  · rintro ⟨⟨⟨hgset, _⟩, hgsv⟩, hgprod, hgtot⟩
    refine ⟨hgset, fun p hp ↦ Entity.mem_prod_iff.1 (hgprod p hp), hgsv, fun c hc ↦ ?_⟩
    obtain ⟨d, hp⟩ := Entity.mem_relDom_iff.1 (hgtot c hc)
    obtain ⟨_, hd⟩ := Entity.kpair_mem_prod_iff.1 (hgprod _ hp)
    exact ⟨d, hd, hp⟩

/-- Goldblatt §13.8 Bullet 16 (p. 169) & **Exercise 13.8.1**: `f : A → B` iff `*f : *A → *B`. -/
@[simp]
theorem Framework.isFuncFromTo_star_iff {X Y : Type*} (F : Framework X Y)
    {f A B : Entity X} :
    Entity.IsFuncFromTo (F.star f) (F.star A) (F.star B) ↔ Entity.IsFuncFromTo f A B := by
  rw [Entity.isFuncFromTo_iff_rel, Entity.isFuncFromTo_iff_rel, F.isFuncEntity_star_iff,
    ← F.star_prod, F.subset_star_iff, ← F.star_relDom, F.subset_star_iff]

/-- Goldblatt §13.8 Bullet 16 (p. 169): If `f` is a function entity and `a ∈ dom f`, then
`*(f(a)) = (*f)(*a)`. -/
theorem Framework.star_funcApp {X Y : Type*} (F : Framework X Y) {f a : Entity X}
    (hf : f.IsFuncEntity) (ha : a ∈ Entity.relDom f) :
    F.star (Entity.funcApp f a) = Entity.funcApp (F.star f) (F.star a) := by
  have hp : Entity.kpair a (Entity.funcApp f a) ∈ f := Entity.kpair_funcApp_mem ha
  have hp' : Entity.kpair (F.star a) (F.star (Entity.funcApp f a)) ∈ F.star f := by
    rw [← F.star_kpair]
    exact F.mem_star_iff.2 hp
  exact ((Entity.kpair_mem_iff_funcApp_eq (F.isFuncEntity_star_iff.2 hf)).1 hp').2.symm

/-- Converse-relation characterization of `Entity.IsInjectiveFunc`: `g` is an injective function
iff both `g` and `g⁻¹` are functions (Goldblatt §13.8, p. 169). -/
theorem Entity.isInjectiveFunc_iff_relInv {X : Type*} {g : Entity X} :
    g.IsInjectiveFunc ↔ g.IsFuncEntity ∧ (Entity.relInv g).IsFuncEntity := by
  constructor
  · rintro ⟨hgf, hginj⟩
    refine ⟨hgf, ⟨⟨Entity.isSet_relInv g, fun p hp ↦ ?_⟩, fun b a₁ a₂ h1 h2 ↦ ?_⟩⟩
    · obtain ⟨a, b, _, rfl⟩ := Entity.mem_relInv_iff.1 hp
      exact ⟨b, a, rfl⟩
    · exact hginj a₁ a₂ b (Entity.kpair_mem_relInv_iff.1 h1) (Entity.kpair_mem_relInv_iff.1 h2)
  · rintro ⟨hgf, ⟨_, hinv⟩⟩
    exact ⟨hgf, fun a₁ a₂ b h1 h2 ↦
      hinv b a₁ a₂ (Entity.kpair_mem_relInv_iff.2 h1) (Entity.kpair_mem_relInv_iff.2 h2)⟩

/-- Goldblatt §13.8 Bullet 16 (p. 169) & **Exercise 13.8.1**: `f` is injective iff `*f` is
injective! -/
@[simp]
theorem Framework.isInjectiveFunc_star_iff {X Y : Type*} (F : Framework X Y) {f : Entity X} :
    (F.star f).IsInjectiveFunc ↔ f.IsInjectiveFunc := by
  rw [Entity.isInjectiveFunc_iff_relInv, Entity.isInjectiveFunc_iff_relInv,
    F.isFuncEntity_star_iff, ← F.star_relInv, F.isFuncEntity_star_iff]

/-- Range characterization of `Entity.IsSurjectiveFromTo` (Goldblatt §13.8, p. 169). -/
theorem Entity.isSurjectiveFromTo_iff_relRan {X : Type*} {g C D : Entity X} :
    Entity.IsSurjectiveFromTo g C D ↔
      Entity.IsFuncFromTo g C D ∧ ∀ d ∈ D, d ∈ Entity.relRan g := by
  refine and_congr_right fun hgf ↦ forall₂_congr fun d _ ↦ ?_
  rw [Entity.mem_relRan_iff]
  exact ⟨fun ⟨c, _, hp⟩ ↦ ⟨c, hp⟩, fun ⟨c, hp⟩ ↦
    let ⟨c', hc', _, _, heq⟩ := hgf.2.1 _ hp
    ⟨c, (Entity.kpair_inj.1 heq).1 ▸ hc', hp⟩⟩

/-- Goldblatt §13.8 Bullet 16 (p. 169) & **Exercise 13.8.1**: `f : A → B` is surjective iff
`*f : *A → *B` is surjective! -/
@[simp]
theorem Framework.isSurjectiveFromTo_star_iff {X Y : Type*} (F : Framework X Y)
    {f A B : Entity X} :
    Entity.IsSurjectiveFromTo (F.star f) (F.star A) (F.star B) ↔
      Entity.IsSurjectiveFromTo f A B := by
  rw [Entity.isSurjectiveFromTo_iff_relRan, Entity.isSurjectiveFromTo_iff_relRan,
    F.isFuncFromTo_star_iff, ← F.star_relRan, F.subset_star_iff]

/-- Bijectivity preservation: `f : A → B` is bijective iff `*f : *A → *B` is bijective
(Goldblatt §13.8, p. 169). -/
@[simp]
theorem Framework.isBijectiveFromTo_star_iff {X Y : Type*} (F : Framework X Y)
    {f A B : Entity X} :
    Entity.IsBijectiveFromTo (F.star f) (F.star A) (F.star B) ↔
      Entity.IsBijectiveFromTo f A B :=
  and_congr F.isSurjectiveFromTo_star_iff F.isInjectiveFunc_star_iff

/-- Iterated universal bounded quantifier block `(∀ x₀ ∈ A) ⋯ (∀ x_{m-1} ∈ A) φ` on variables
`0, …, m - 1` (helper for Exercise 13.8.2; Goldblatt §13.8, p. 170). -/
def forallVarsIn {X : Type*} (A : UTerm X) : ℕ → UFormula X → UFormula X
  | 0, φ => φ
  | k + 1, φ => forallVarsIn A k (.forallIn k A φ)

/-- `starFormula` commutes with `forallVarsIn` (Goldblatt §13.8, p. 170). -/
theorem starFormula_forallVarsIn {X Y : Type*} (star : Entity X → Entity Y)
    (A : UTerm X) :
    ∀ (k : ℕ) (φ : UFormula X),
      starFormula star (forallVarsIn A k φ) =
        forallVarsIn (starTerm star A) k (starFormula star φ)
  | 0, _ => rfl
  | k + 1, φ => by
      simp [forallVarsIn, starFormula_forallVarsIn star A k (.forallIn k A φ), starFormula]

/-- Free variables of `forallVarsIn (.const A) k φ` are those of `φ` with `{0, …, k - 1}` removed
(Goldblatt §13.8, p. 170). -/
theorem freeVarsUFormula_forallVarsIn_const {X : Type*} (A : Entity X) :
    ∀ (k : ℕ) (φ : UFormula X) (v : ℕ),
      v ∈ freeVarsUFormula (forallVarsIn (.const A) k φ) ↔
        k ≤ v ∧ v ∈ freeVarsUFormula φ
  | 0, _, _ => by simp [forallVarsIn]
  | k + 1, φ, v => by
      rw [forallVarsIn, freeVarsUFormula_forallVarsIn_const A k (.forallIn k (.const A) φ)]
      simp only [freeVarsUFormula, freeVarsUTerm, Finset.empty_union, Finset.mem_erase]
      constructor
      · rintro ⟨hk, hne, hv⟩
        exact ⟨by omega, hv⟩
      · rintro ⟨hk, hv⟩
        exact ⟨by omega, by omega, hv⟩

/-- Satisfaction of `forallVarsIn (.const A) k φ` under environment `env`
(Goldblatt §13.8, p. 170). -/
theorem holds_forallVarsIn_const {X : Type*} (A : Entity X) :
    ∀ (k : ℕ) (φ : UFormula X) (env : ℕ → Entity X),
      Holds env (forallVarsIn (.const A) k φ) ↔
        ∀ w : Fin k → Entity X, (∀ j, w j ∈ A) →
          Holds (fun n ↦ if h : n < k then w ⟨n, h⟩ else env n) φ
  | 0, φ, env => by
      simp only [forallVarsIn, Nat.not_lt_zero, ↓reduceDIte]
      exact ⟨fun h _ _ ↦ h, fun h ↦ h Fin.elim0 fun j ↦ Fin.elim0 j⟩
  | k + 1, φ, env => by
      rw [forallVarsIn, holds_forallVarsIn_const A k (.forallIn k (.const A) φ) env]
      constructor
      · intro h w hw
        have hk := h (Fin.init w) (fun j ↦ hw j.castSucc)
        obtain ⟨A', hA', hall⟩ := hk
        obtain rfl := Option.some.inj hA'
        have hstep := hall (w (Fin.last k)) (hw (Fin.last k))
        refine (holds_congr ?_).1 hstep
        intro n _
        by_cases hnk : n = k
        · subst hnk
          simp [Fin.last]
        · rw [Function.update_of_ne hnk]
          by_cases hlt : n < k
          · have hlt' : n < k + 1 := by omega
            simp only [hlt, hlt', ↓reduceDIte, Fin.init]
            rfl
          · have hlt' : ¬ n < k + 1 := by omega
            simp [hlt, hlt']
      · intro h u hu
        refine ⟨A, rfl, fun a ha ↦ ?_⟩
        let w : Fin (k + 1) → Entity X := Fin.snoc u a
        have hw : ∀ j : Fin (k + 1), w j ∈ A := by
          intro j
          refine Fin.lastCases ?_ ?_ j
          · simpa [w] using ha
          · intro j₀
            simpa [w, Fin.snoc] using hu j₀
        refine (holds_congr ?_).2 (h w hw)
        intro n _
        by_cases hnk : n = k
        · subst hnk
          have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := rfl
          simp [w, hlast]
        · rw [Function.update_of_ne hnk]
          by_cases hlt : n < k
          · have hlt' : n < k + 1 := by omega
            simp [hlt, hlt', w, Fin.snoc]
          · have hlt' : ¬ n < k + 1 := by omega
            simp [hlt, hlt']

/-- Tuple term `(x₀, …, x_{m-1})` in `ℒ_𝕌` for `m ≥ 1` (`var 0` when `m = 1`, and `UTerm.tuple`
when `m ≥ 2`; Goldblatt **Exercise 13.8.2**, p. 170). -/
def varTupleTerm (X : Type*) : ∀ m : ℕ, 1 ≤ m → UTerm X
  | 0, h => absurd h (by omega)
  | 1, _ => .var 0
  | m + 2, _ => .tuple (by omega : 2 ≤ m + 2) (fun j : Fin (m + 2) ↦ .var j.1)

/-- `starTerm` maps `varTupleTerm X m hm` to `varTupleTerm Y m hm`
(Goldblatt **Exercise 13.8.2**, p. 170). -/
@[simp]
theorem starTerm_varTupleTerm {X Y : Type*} (star : Entity X → Entity Y)
    (m : ℕ) (hm : 1 ≤ m) :
    starTerm star (varTupleTerm X m hm) = varTupleTerm Y m hm := by
  rcases m with _ | _ | k
  · omega
  · rfl
  · rfl

/-- Evaluation of `varTupleTerm` on an environment extending `w : Fin m → Entity X`
(Goldblatt **Exercise 13.8.2**, p. 170). -/
theorem evalUTerm_varTupleTerm {X : Type*} {m : ℕ} (hm : 1 ≤ m)
    (env : ℕ → Entity X) (w : Fin m → Entity X)
    (henv : ∀ j : Fin m, env j.1 = w j) :
    evalUTerm env (varTupleTerm X m hm) = some (Entity.ktuple w) := by
  rcases m with _ | _ | k
  · omega
  · simp only [varTupleTerm, evalUTerm_var, Entity.ktuple, Option.some.injEq]
    exact henv 0
  · rw [varTupleTerm, evalUTerm.eq_3]
    split_ifs with hall
    · apply congrArg some
      apply congrArg Entity.ktuple
      ext j
      exact henv j
    · exact absurd (fun _ ↦ rfl) hall

/-- Free variables of `varTupleTerm X m hm` lie in `{0, …, m - 1}`
(Goldblatt **Exercise 13.8.2**, p. 170). -/
theorem freeVarsUTerm_varTupleTerm {X : Type*} {m : ℕ} (hm : 1 ≤ m) {v : ℕ}
    (hv : v ∈ freeVarsUTerm (varTupleTerm X m hm)) : v < m := by
  rcases m with _ | _ | k
  · omega
  · simp [varTupleTerm, freeVarsUTerm] at hv; omega
  · simp only [varTupleTerm, freeVarsUTerm, Finset.mem_biUnion, Finset.mem_univ,
      true_and, Finset.mem_singleton] at hv
    obtain ⟨j, rfl⟩ := hv
    exact j.2

/-- Goldblatt **Exercise 13.8.2** (p. 170): For any `m ≥ 1`, any `A : Entity X`, and any
`ℒ_𝕌`-formula `φ(x₀, …, x_{m-1})` with free variables in `{0, …, m - 1}`,
`*{(a₁, …, a_m) ∈ A^m : φ(a₁, …, a_m)} = {(b₁, …, b_m) ∈ (*A)^m : *φ(b₁, …, b_m)}`! -/
theorem Framework.star_tupleComprehension {X Y : Type*} (F : Framework X Y)
    {m : ℕ} (hm : 1 ≤ m) (A : Entity X) (φ : UFormula X)
    (hvars : ∀ v ∈ freeVarsUFormula φ, v < m) :
    F.star
      (Entity.setOfBounded {p : Entity X |
        ∃ v : Fin m → Entity X, (∀ j, v j ∈ A) ∧ p = Entity.ktuple v ∧
          Holds (fun n ↦ if h : n < m then v ⟨n, h⟩ else ∅) φ}) =
      Entity.setOfBounded {q : Entity Y |
        ∃ w : Fin m → Entity Y, (∀ j, w j ∈ F.star A) ∧ q = Entity.ktuple w ∧
          Holds (fun n ↦ if h : n < m then w ⟨n, h⟩ else ∅) (starFormula F.star φ)} := by
  let S : Entity X :=
    Entity.setOfBounded {p : Entity X |
      ∃ v : Fin m → Entity X, (∀ j, v j ∈ A) ∧ p = Entity.ktuple v ∧
        Holds (fun n ↦ if h : n < m then v ⟨n, h⟩ else ∅) φ}
  have hbddX : IsBoundedRank {p : Entity X |
      ∃ v : Fin m → Entity X, (∀ j, v j ∈ A) ∧ p = Entity.ktuple v ∧
        Holds (fun n ↦ if h : n < m then v ⟨n, h⟩ else ∅) φ} :=
    (Entity.isBoundedRank_prodTuple fun _ : Fin m ↦ A).subset
      fun _ ⟨v, hv, hp, _⟩ ↦ ⟨v, hv, hp⟩
  have hbddY : IsBoundedRank {q : Entity Y |
      ∃ w : Fin m → Entity Y, (∀ j, w j ∈ F.star A) ∧ q = Entity.ktuple w ∧
        Holds (fun n ↦ if h : n < m then w ⟨n, h⟩ else ∅) (starFormula F.star φ)} :=
    (Entity.isBoundedRank_prodTuple fun _ : Fin m ↦ F.star A).subset
      fun _ ⟨w, hw, hq, _⟩ ↦ ⟨w, hw, hq⟩
  have hSsub : ∀ p ∈ S, p ∈ Entity.prodTuple (fun _ : Fin m ↦ A) := fun p hp ↦ by
    obtain ⟨v, hv, rfl, _⟩ := (Entity.mem_setOfBounded hbddX).1 hp
    exact Entity.mem_prodTuple_iff.2 ⟨v, hv, rfl⟩
  have hstarSub : ∀ q ∈ F.star S, q ∈ Entity.prodTuple (fun _ : Fin m ↦ F.star A) := by
    rw [← F.star_prodTuple]
    exact F.subset_star_iff.2 hSsub
  let ψ : UFormula X :=
    forallVarsIn (.const A) m (.iff (.mem (varTupleTerm X m hm) (.const S)) φ)
  have hsent : IsSentence ψ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v hv
    obtain ⟨hvm, hvbody⟩ := (freeVarsUFormula_forallVarsIn_const A m _ v).1 hv
    simp only [freeVarsUFormula, Finset.mem_union, freeVarsUTerm] at hvbody
    rcases hvbody with (hvt | hvs) | hvφ
    · exact absurd (freeVarsUTerm_varTupleTerm hm hvt) (by omega)
    · simp at hvs
    · exact absurd (hvars v hvφ) (by omega)
  have hstd : SentenceHolds ψ := by
    rw [SentenceHolds, holds_forallVarsIn_const]
    intro v hv
    have htup : evalUTerm (fun n ↦ if h : n < m then v ⟨n, h⟩ else (∅ : Entity X))
        (varTupleTerm X m hm) = some (Entity.ktuple v) :=
      evalUTerm_varTupleTerm hm _ v fun j ↦ by simp [j.2]
    simp only [Holds, htup, evalUTerm_const]
    constructor
    · rintro ⟨_, S', hp1, hS', hmS⟩
      obtain rfl := Option.some.inj hp1
      obtain rfl := Option.some.inj hS'
      obtain ⟨v', _, hveq, hφ⟩ := (Entity.mem_setOfBounded hbddX).1 hmS
      obtain rfl := Entity.ktuple_inj.1 hveq
      exact hφ
    · intro hφ
      exact ⟨Entity.ktuple v, S, rfl, rfl, (Entity.mem_setOfBounded hbddX).2 ⟨v, hv, rfl, hφ⟩⟩
  have htr := (F.transfer ψ hsent).1 hstd
  simp only [ψ, starFormula_forallVarsIn, starFormula, starTerm_varTupleTerm,
    starTerm] at htr
  rw [SentenceHolds, holds_forallVarsIn_const] at htr
  refine Entity.set_ext (F.isSet_star_iff.2 (Entity.isSet_setOfBounded _))
    (Entity.isSet_setOfBounded _) fun q ↦ ?_
  rw [Entity.mem_setOfBounded hbddY]
  constructor
  · intro hqS
    obtain ⟨w, hw, rfl⟩ := Entity.mem_prodTuple_iff.1 (hstarSub q hqS)
    let envY := fun n ↦ if h : n < m then w ⟨n, h⟩ else (∅ : Entity Y)
    have htupY : evalUTerm envY (varTupleTerm Y m hm) = some (Entity.ktuple w) :=
      evalUTerm_varTupleTerm hm envY w fun j ↦ by simp [envY, j.2]
    have hiff := htr w hw
    exact ⟨w, hw, rfl, hiff.1 ⟨Entity.ktuple w, F.star S, htupY, rfl, hqS⟩⟩
  · rintro ⟨w, hw, rfl, hφw⟩
    let envY := fun n ↦ if h : n < m then w ⟨n, h⟩ else (∅ : Entity Y)
    have htupY : evalUTerm envY (varTupleTerm Y m hm) = some (Entity.ktuple w) :=
      evalUTerm_varTupleTerm hm envY w fun j ↦ by simp [envY, j.2]
    have hiff := htr w hw
    obtain ⟨q', S', hq', hS', hmS⟩ := hiff.2 hφw
    obtain rfl := Option.some.inj hS'
    have hqeq : Entity.ktuple w = q' := Option.some.inj (htupY.symm.trans hq')
    exact hqeq ▸ hmS

/-- Goldblatt §13.8 Warning Example (p. 170): Let `f : ℝ → 𝒫(ℝ)` be defined by
`f(r) = {x ∈ ℝ : x > r}`. Under any `Framework ℝ Y` (with `<` transformed to `*<`), for every
`r : ℝ`, `(*f)(r) = *(f(r)) = {x ∈ *ℝ : x *< *r}`. Whenever `*ℝ` contains a positive element not in
`atomMap '' ℝ` (such as `ω` or an infinitesimal `ε > 0` in `ℝ*`), `(*f)(0)` contains nonstandard
elements and hence is NOT equal to the standard image `{atom (atomMap x) : x > 0}`! -/
theorem Framework.upperRayFun_star_apply {Y : Type*} (F : Framework ℝ Y) (r : ℝ) :
    let ltRel : Entity ℝ :=
      Entity.setOfBounded {p : Entity ℝ | ∃ x y : ℝ, x < y ∧ p = Entity.kpair (Entity.atom x) (Entity.atom y)}
    let upperRay : ℝ → Entity ℝ := fun s ↦ mkAtomSet {x : ℝ | s < x}
    let f : Entity ℝ :=
      Entity.mkFuncEntity (baseSet ℝ)
        (fun a ↦ if h : ∃ s : ℝ, a = Entity.atom s then upperRay h.choose else ∅)
    Entity.funcApp (F.star f) (Entity.atom (F.atomMap r)) =
      Entity.setOfBounded {y : Entity Y |
        y ∈ F.star (baseSet ℝ) ∧ Entity.kpair (Entity.atom (F.atomMap r)) y ∈ F.star ltRel} := by
  intro ltRel upperRay f
  have hlt_bdd : IsBoundedRank {p : Entity ℝ |
      ∃ x y : ℝ, x < y ∧ p = Entity.kpair (Entity.atom x) (Entity.atom y)} :=
    (Entity.isBoundedRank_prod (baseSet ℝ) (baseSet ℝ)).subset fun _ ⟨x, y, _, hp⟩ ↦
      ⟨Entity.atom x, mem_baseSet_iff.2 ⟨x, rfl⟩, Entity.atom y, mem_baseSet_iff.2 ⟨y, rfl⟩, hp⟩
  let g : Entity ℝ → Entity ℝ :=
    fun a ↦ if h : ∃ s : ℝ, a = Entity.atom s then upperRay h.choose else ∅
  have hgP : ∀ a ∈ baseSet ℝ, g a ∈ Entity.powerset (baseSet ℝ) := by
    intro a ha
    obtain ⟨s, rfl⟩ := mem_baseSet_iff.1 ha
    have hex : ∃ s' : ℝ, Entity.atom s = Entity.atom s' := ⟨s, rfl⟩
    simp only [g, hex, ↓reduceDIte]
    exact Entity.mem_powerset_iff.2 ⟨Entity.isSet_setOfBounded _, fun z hz ↦ by
      obtain ⟨t, _, rfl⟩ := (mem_mkAtomSet_iff (S := {x : ℝ | hex.choose < x})).1 hz
      exact mem_baseSet_iff.2 ⟨t, rfl⟩⟩
  have hfFunc := Entity.isFuncFromTo_mkFuncEntity hgP
  have hdom : Entity.atom r ∈ Entity.relDom f := by
    rw [hfFunc.relDom_eq (isSet_vStageEntity ℝ 0)]
    exact mem_baseSet_iff.2 ⟨r, rfl⟩
  have happ : Entity.funcApp f (Entity.atom r) = upperRay r := by
    rw [Entity.funcApp_mkFuncEntity hgP (mem_baseSet_iff.2 ⟨r, rfl⟩)]
    have hex : ∃ s : ℝ, Entity.atom r = Entity.atom s := ⟨r, rfl⟩
    simp only [g, hex, ↓reduceDIte]
    rw [Entity.atom_inj.1 hex.choose_spec.symm]
  rw [← F.star_atom, ← F.star_funcApp hfFunc.isFuncEntity hdom, happ]
  have hEq := F.star_set_eq_of_bounded (S := upperRay r) (T := baseSet ℝ)
    (φ := .mem (UTerm.pair (.const (Entity.atom r)) (.var 0)) (.const ltRel))
    (Entity.isSet_setOfBounded _)
    (fun z hz ↦ by
      obtain ⟨t, _, rfl⟩ := mem_mkAtomSet_iff.1 hz
      exact mem_baseSet_iff.2 ⟨t, rfl⟩)
    (by simp [freeVarsUFormula, freeVarsUTerm])
    (fun z hz ↦ by
      obtain ⟨t, rfl⟩ := mem_baseSet_iff.1 hz
      rw [mem_mkAtomSet_iff]
      simp only [Holds, evalUTerm_pair, evalUTerm_const, evalUTerm_var]
      constructor
      · rintro ⟨t', ht', heq⟩
        obtain rfl := Entity.atom_inj.1 heq
        exact ⟨Entity.kpair (Entity.atom r) (Entity.atom t), ltRel, rfl, rfl,
          (Entity.mem_setOfBounded hlt_bdd).2 ⟨r, t, ht', rfl⟩⟩
      · rintro ⟨_, _, hp1, hlt', hmem⟩
        obtain rfl := Option.some.inj hp1
        obtain rfl := Option.some.inj hlt'
        obtain ⟨x, y, hxy, hpair⟩ := (Entity.mem_setOfBounded hlt_bdd).1 hmem
        obtain ⟨hx, hy⟩ := Entity.kpair_inj.1 hpair
        obtain rfl := Entity.atom_inj.1 hx
        obtain rfl := Entity.atom_inj.1 hy
        exact ⟨t, hxy, rfl⟩)
  rw [hEq]
  refine Entity.set_ext (Entity.isSet_setOfBounded _) (Entity.isSet_setOfBounded _) fun y ↦ ?_
  rw [Entity.mem_setOfBounded ((F.star (baseSet ℝ)).isBoundedRank_extSet.subset fun _ h ↦ h.1),
    Entity.mem_setOfBounded ((F.star (baseSet ℝ)).isBoundedRank_extSet.subset fun _ h ↦ h.1)]
  refine and_congr_right fun _ ↦ ?_
  simp only [starFormula, starTerm_pair, starTerm, F.star_atom, Holds, evalUTerm_pair,
    evalUTerm_const, evalUTerm_var]
  exact ⟨fun ⟨_, _, h1, h2, hm⟩ ↦ (Option.some.inj h1) ▸ (Option.some.inj h2) ▸ hm,
    fun hm ↦ ⟨Entity.kpair (Entity.atom (F.atomMap r)) y, F.star ltRel, rfl, rfl, hm⟩⟩

/-! ## §13.8 (Part 2) Concrete Ultrapower Superstructure (`ultrapowerFramework` & `hyperrealFramework`) -/

/-- `Germ.map Sum.inl` is injective for any filter `l` (helper for Zakon collapse; Goldblatt §13.8,
p. 168). -/
theorem germ_map_inl_injective {I A B : Type*} {l : Filter I} :
    Function.Injective (Germ.map Sum.inl : Germ l A → Germ l (A ⊕ B)) := by
  intro x y
  refine Germ.inductionOn₂ x y fun fx fy h ↦ ?_
  rw [Germ.map_coe, Germ.map_coe, Germ.coe_eq] at h
  exact Germ.coe_eq.2 (h.mono fun _ hi ↦ Sum.inl.inj hi)

/-- `Germ.map Sum.inl a` and `Germ.map Sum.inr b` are disjoint over any nontrivial filter
(Goldblatt §13.8, p. 168). -/
theorem germ_map_inl_ne_map_inr {I A B : Type*} {l : Filter I} [l.NeBot]
    (a : Germ l A) (b : Germ l B) :
    Germ.map Sum.inl a ≠ Germ.map Sum.inr b := by
  refine Germ.inductionOn₂ a b fun fa fb h ↦ ?_
  rw [Germ.map_coe, Germ.map_coe, Germ.coe_eq] at h
  have hfalse : ∀ᶠ _ : I in l, False := h.mono fun _ hi ↦ by simp at hi
  exact (Filter.eventually_const.1 hfalse)

/-- Ultrafilter sum dichotomy: every `g : Germ (U : Filter I) (A ⊕ B)` is either `Germ.map Sum.inl a`
or `Germ.map Sum.inr b` (Goldblatt §13.8, p. 168). -/
theorem germ_sum_dichotomy {I A B : Type*} (U : Ultrafilter I)
    (g : Germ (U : Filter I) (A ⊕ B)) :
    (∃ a : Germ (U : Filter I) A, g = Germ.map Sum.inl a) ∨
      (∃ b : Germ (U : Filter I) B, g = Germ.map Sum.inr b) := by
  refine Germ.inductionOn g fun f ↦ ?_
  let S : Set I := {i : I | ∃ a : A, f i = Sum.inl a}
  rcases Ultrafilter.mem_or_compl_mem U S with hS | hSc
  · obtain ⟨i₀, a₀, _⟩ := Filter.nonempty_of_mem hS
    let fa : I → A := fun i ↦ match f i with
      | Sum.inl a => a
      | Sum.inr _ => a₀
    refine Or.inl ⟨(fa : Germ (U : Filter I) A), ?_⟩
    rw [Germ.map_coe, Germ.coe_eq]
    exact Filter.eventually_iff_exists_mem.2 ⟨S, hS, fun i ⟨a, hi⟩ ↦ by simp [fa, hi]⟩
  · have hSc' : {i : I | ∃ b : B, f i = Sum.inr b} ∈ (U : Filter I) := by
      refine Filter.mem_of_superset hSc fun i hi ↦ ?_
      cases hfi : f i with
      | inl a => exact (hi ⟨a, hfi⟩).elim
      | inr b => exact ⟨b, hfi⟩
    obtain ⟨i₀, b₀, _⟩ := Filter.nonempty_of_mem hSc'
    let fb : I → B := fun i ↦ match f i with
      | Sum.inl _ => b₀
      | Sum.inr b => b
    refine Or.inr ⟨(fb : Germ (U : Filter I) B), ?_⟩
    rw [Germ.map_coe, Germ.coe_eq]
    exact Filter.eventually_iff_exists_mem.2 ⟨_, hSc', fun i ⟨b, hi⟩ ↦ by simp [fb, hi]⟩

/-- Zakon bounded-rank collapse from stage-`n` ultrafilter germs `Germ U (RawStage X n)` into the
superstructure `Entity (Germ U X)` (Goldblatt §13.8, p. 168). -/
def collapseStage {I X : Type*} (U : Ultrafilter I) :
    ∀ n : ℕ, Germ (U : Filter I) (RawStage X n) → Entity (Germ (U : Filter I) X)
  | 0, g => Entity.atom g
  | n + 1, g =>
      if h : ∃ x : Germ (U : Filter I) X, g = Germ.map Sum.inl x then
        Entity.atom h.choose
      else
        Entity.setOfBounded
          {y : Entity (Germ (U : Filter I) X) |
            ∃ a : Germ (U : Filter I) (RawStage X n),
              y = collapseStage U n a ∧
              Germ.LiftRel (fun u v ↦ ∃ B : Set (RawStage X n), v = Sum.inr B ∧ u ∈ B) a g}

/-- Stage bound for `collapseStage`: every stage-`n` germ collapses into `VStage (Germ U X) n`
(Goldblatt §13.8, p. 168). -/
theorem collapseStage_mem_vStage {I X : Type*} (U : Ultrafilter I) :
    ∀ (n : ℕ) (g : Germ (U : Filter I) (RawStage X n)),
      collapseStage U n g ∈ VStage (Germ (U : Filter I) X) n
  | 0, g => ⟨g, rfl⟩
  | n + 1, g => by
      unfold collapseStage
      split_ifs with h
      · exact vStage_mono (Nat.zero_le _) ⟨h.choose, rfl⟩
      · refine Entity.setOfBounded_mem_vStage fun y ⟨a, hy, _⟩ ↦ ?_
        rw [hy]
        exact collapseStage_mem_vStage U n a

/-- `collapseStage` at stage `0` on a sequence `a : I → RawStage X 0` (Goldblatt §13.8, p. 168). -/
@[simp]
theorem collapseStage_zero_coe {I X : Type*} (U : Ultrafilter I) (a : I → RawStage X 0) :
    collapseStage U 0 (a : Germ (U : Filter I) (RawStage X 0)) =
      Entity.atom (Germ.ofFun a : Germ (U : Filter I) X) := rfl

/-- Equality with `Entity.atom ↑fb` for `collapseStage U 0 ↑a` (Goldblatt §13.8, p. 168). -/
theorem collapseStage_zero_coe_eq_atom_iff {I X : Type*} (U : Ultrafilter I)
    (a : I → RawStage X 0) (fb : I → X) :
    collapseStage U 0 (a : Germ (U : Filter I) (RawStage X 0)) =
      Entity.atom (fb : Germ (U : Filter I) X) ↔
      ∀ᶠ i in (U : Filter I), (a i : X) = fb i :=
  Entity.atom_inj.trans Germ.coe_eq

/-- Stage-`n+1` ultrafilter dichotomy in `RawStage X (n + 1)` with explicit coordinate sequences
(Goldblatt §13.8, p. 168). -/
theorem germ_rawStage_succ_dichotomy {I X : Type*} (U : Ultrafilter I) (n : ℕ)
    (b : I → RawStage X (n + 1)) :
    (∃ fb : I → X, ∀ᶠ i in (U : Filter I), b i = Sum.inl (fb i)) ∨
    (∃ fB : I → Set (RawStage X n), ∀ᶠ i in (U : Filter I), b i = Sum.inr (fB i)) := by
  rcases germ_sum_dichotomy U (Germ.ofFun b : Germ (U : Filter I) (X ⊕ Set (RawStage X n))) with
    ⟨xb, hxb⟩ | ⟨Bb, hBb⟩
  · refine Germ.inductionOn xb (fun fb hxb ↦ ?_) hxb
    exact Or.inl ⟨fb, Germ.coe_eq.1 (hxb.trans (Germ.map_coe Sum.inl fb))⟩
  · refine Germ.inductionOn Bb (fun fB hBb ↦ ?_) hBb
    exact Or.inr ⟨fB, Germ.coe_eq.1 (hBb.trans (Germ.map_coe Sum.inr fB))⟩

/-- `collapseStage` on a sequence eventually equal to `Sum.inl (fb i)` yields `Entity.atom ↑fb`
(Goldblatt §13.8, p. 168). -/
theorem collapseStage_eq_atom_of_eventually_inl {I X : Type*} (U : Ultrafilter I) {n : ℕ}
    {b : I → RawStage X (n + 1)} {fb : I → X}
    (hevb : ∀ᶠ i in (U : Filter I), b i = Sum.inl (fb i)) :
    collapseStage U (n + 1) (b : Germ (U : Filter I) (RawStage X (n + 1))) =
      Entity.atom (fb : Germ (U : Filter I) X) := by
  rw [collapseStage.eq_2]
  have hmap : (b : Germ (U : Filter I) (RawStage X (n + 1))) =
      Germ.map Sum.inl (fb : Germ (U : Filter I) X) :=
    (Germ.coe_eq.2 hevb).trans (Germ.map_coe Sum.inl fb).symm
  have hex : ∃ y : Germ (U : Filter I) X,
      (b : Germ (U : Filter I) (RawStage X (n + 1))) = Germ.map Sum.inl y :=
    ⟨(fb : Germ (U : Filter I) X), hmap⟩
  simp only [hex, ↓reduceDIte]
  exact congrArg Entity.atom (germ_map_inl_injective (hex.choose_spec.symm.trans hmap))

/-- `collapseStage` on a sequence eventually equal to `Sum.inr (fB i)` is a set entity
(Goldblatt §13.8, p. 168). -/
theorem isSet_collapseStage_of_eventually_inr {I X : Type*} (U : Ultrafilter I) {n : ℕ}
    {b : I → RawStage X (n + 1)} {fB : I → Set (RawStage X n)}
    (hevb : ∀ᶠ i in (U : Filter I), b i = Sum.inr (fB i)) :
    (collapseStage U (n + 1) (b : Germ (U : Filter I) (RawStage X (n + 1)))).IsSet := by
  rw [collapseStage.eq_2]
  have hmap : (b : Germ (U : Filter I) (RawStage X (n + 1))) =
      Germ.map Sum.inr (fB : Germ (U : Filter I) (Set (RawStage X n))) :=
    (Germ.coe_eq.2 hevb).trans (Germ.map_coe Sum.inr fB).symm
  have hnot : ¬ ∃ x : Germ (U : Filter I) X,
      (b : Germ (U : Filter I) (RawStage X (n + 1))) = Germ.map Sum.inl x := by
    rintro ⟨x, hx⟩
    exact germ_map_inl_ne_map_inr x (fB : Germ (U : Filter I) (Set (RawStage X n)))
      (hx.symm.trans hmap)
  simp only [hnot, ↓reduceDIte]
  exact Entity.isSet_setOfBounded _

/-- Membership in `collapseStage` of a sequence eventually equal to `Sum.inr (fB i)`
(Goldblatt §13.8, p. 168). -/
theorem mem_collapseStage_of_eventually_inr {I X : Type*} (U : Ultrafilter I) {n : ℕ}
    {b : I → RawStage X (n + 1)} {fB : I → Set (RawStage X n)}
    (hevb : ∀ᶠ i in (U : Filter I), b i = Sum.inr (fB i))
    {y : Entity (Germ (U : Filter I) X)} :
    y ∈ collapseStage U (n + 1) (b : Germ (U : Filter I) (RawStage X (n + 1))) ↔
      ∃ u : I → RawStage X n,
        y = collapseStage U n (u : Germ (U : Filter I) (RawStage X n)) ∧
        (∀ᶠ i in (U : Filter I), u i ∈ fB i) := by
  rw [collapseStage.eq_2]
  have hmap : (b : Germ (U : Filter I) (RawStage X (n + 1))) =
      Germ.map Sum.inr (fB : Germ (U : Filter I) (Set (RawStage X n))) :=
    (Germ.coe_eq.2 hevb).trans (Germ.map_coe Sum.inr fB).symm
  have hnot : ¬ ∃ x : Germ (U : Filter I) X,
      (b : Germ (U : Filter I) (RawStage X (n + 1))) = Germ.map Sum.inl x := by
    rintro ⟨x, hx⟩
    exact germ_map_inl_ne_map_inr x (fB : Germ (U : Filter I) (Set (RawStage X n)))
      (hx.symm.trans hmap)
  simp only [hnot, ↓reduceDIte]
  have hbdd : IsBoundedRank
      {y : Entity (Germ (U : Filter I) X) |
        ∃ a : Germ (U : Filter I) (RawStage X n),
          y = collapseStage U n a ∧
          Germ.LiftRel (fun u v ↦ ∃ B' : Set (RawStage X n), v = Sum.inr B' ∧ u ∈ B') a
            (b : Germ (U : Filter I) (RawStage X (n + 1)))} :=
    ⟨n, fun _ ⟨a, hy, _⟩ ↦ hy ▸ collapseStage_mem_vStage U n a⟩
  rw [Entity.mem_setOfBounded hbdd]
  constructor
  · rintro ⟨a, rfl, hrel⟩
    refine Germ.inductionOn a (fun u hrel ↦ ?_) hrel
    have hrel' := Germ.liftRel_coe.1 hrel
    exact ⟨u, rfl, (hrel'.and hevb).mono fun i ⟨⟨B', hB', hui⟩, hbi⟩ ↦
      Sum.inr.inj (hbi.symm.trans hB') ▸ hui⟩
  · rintro ⟨u, rfl, hu⟩
    exact ⟨(u : Germ (U : Filter I) (RawStage X n)), rfl,
      Germ.liftRel_coe.2 ((hu.and hevb).mono fun i ⟨hui, hbi⟩ ↦ ⟨fB i, hbi, hui⟩)⟩

/-- Every member of `collapseStage U n g` is itself of the form `collapseStage U m ↑u` for some
`m < n` and `u : I → RawStage X m` (transitivity of the range of `collapseStage`;
Goldblatt §13.8 & §13.10, pp. 168, 173). -/
theorem exists_collapseStage_of_mem {I X : Type*} (U : Ultrafilter I) :
    ∀ {n : ℕ} {g : Germ (U : Filter I) (RawStage X n)} {y : Entity (Germ (U : Filter I) X)},
      y ∈ collapseStage U n g →
        ∃ (m : ℕ) (u : I → RawStage X m), m < n ∧
          y = collapseStage U m (u : Germ (U : Filter I) (RawStage X m))
  | 0, g, y, hy => (Entity.not_mem_atom y g hy).elim
  | n + 1, g, y, hy => by
      refine Germ.inductionOn g (fun b hy ↦ ?_) hy
      rcases germ_rawStage_succ_dichotomy U n b with ⟨fb, hevb⟩ | ⟨fB, hevb⟩
      · rw [collapseStage_eq_atom_of_eventually_inl U hevb] at hy
        exact (Entity.not_mem_atom y _ hy).elim
      · obtain ⟨u, rfl, _⟩ := (mem_collapseStage_of_eventually_inr U hevb).1 hy
        exact ⟨n, u, Nat.lt_succ_self n, rfl⟩

/-- Extensionality / atomic equality part of Łoś's Theorem across arbitrary stages `m, n`:
`collapseStage U m ↑a = collapseStage U n ↑b ↔ ∀ᶠ i in U, Entity.ofRaw (a i) = Entity.ofRaw (b i)`
(Goldblatt §13.8, p. 168). -/
theorem collapseStage_coe_eq_iff {I X : Type*} (U : Ultrafilter I) :
    ∀ {m n : ℕ} (a : I → RawStage X m) (b : I → RawStage X n),
      collapseStage U m (a : Germ (U : Filter I) (RawStage X m)) =
        collapseStage U n (b : Germ (U : Filter I) (RawStage X n)) ↔
        ∀ᶠ i in (U : Filter I), Entity.ofRaw (a i) = Entity.ofRaw (b i) := by
  suffices hmain : ∀ k : ℕ, ∀ m n : ℕ, m + n = k →
      ∀ (a : I → RawStage X m) (b : I → RawStage X n),
        collapseStage U m (a : Germ (U : Filter I) (RawStage X m)) =
          collapseStage U n (b : Germ (U : Filter I) (RawStage X n)) ↔
          ∀ᶠ i in (U : Filter I), Entity.ofRaw (a i) = Entity.ofRaw (b i) by
    intro m n a b
    exact hmain (m + n) m n rfl a b
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro m n hmn a b
      cases m with
      | zero =>
          cases n with
          | zero =>
              rw [collapseStage_zero_coe (U := U) b, collapseStage_zero_coe_eq_atom_iff U a b]
              exact Filter.eventually_congr (Filter.Eventually.of_forall fun _ ↦ Entity.atom_inj.symm)
          | succ n' =>
              rcases germ_rawStage_succ_dichotomy U n' b with ⟨fb, hevb⟩ | ⟨fB, hevb⟩
              · rw [collapseStage_eq_atom_of_eventually_inl U hevb,
                  collapseStage_zero_coe_eq_atom_iff U a fb]
                constructor
                · intro ha
                  exact (ha.and hevb).mono fun i ⟨hai, hbi⟩ ↦ by
                    rw [hbi, Entity.ofRaw_inl]; exact congrArg Entity.atom hai
                · intro heq
                  exact (heq.and hevb).mono fun i ⟨hei, hbi⟩ ↦ by
                    rw [hbi, Entity.ofRaw_inl] at hei
                    exact Entity.atom_inj.1 hei
              · have hne : collapseStage U 0 (a : Germ (U : Filter I) (RawStage X 0)) ≠
                    collapseStage U (n' + 1) (b : Germ (U : Filter I) (RawStage X (n' + 1))) := by
                  intro heq
                  have hset := isSet_collapseStage_of_eventually_inr U hevb
                  rw [← heq, collapseStage_zero_coe] at hset
                  exact hset (Entity.isAtom_atom _)
                constructor
                · intro h; exact (hne h).elim
                · intro heq
                  have hfalse : ∀ᶠ _ : I in (U : Filter I), False :=
                    (heq.and hevb).mono fun i ⟨hei, hbi⟩ ↦ by
                      rw [hbi] at hei
                      have hs := Entity.isSet_ofRaw_inr (fB i)
                      rw [← hei] at hs
                      exact hs (Entity.isAtom_atom _)
                  exact (Filter.eventually_const.1 hfalse).elim
      | succ m' =>
          cases n with
          | zero =>
              rcases germ_rawStage_succ_dichotomy U m' a with ⟨fa, heva⟩ | ⟨fA, heva⟩
              · rw [collapseStage_eq_atom_of_eventually_inl U heva, eq_comm,
                  collapseStage_zero_coe_eq_atom_iff U b fa]
                constructor
                · intro ha
                  exact (ha.and heva).mono fun i ⟨hai, hai'⟩ ↦ by
                    rw [hai', Entity.ofRaw_inl]; exact congrArg Entity.atom hai.symm
                · intro heq
                  exact (heq.and heva).mono fun i ⟨hei, hai'⟩ ↦ by
                    rw [hai', Entity.ofRaw_inl] at hei
                    exact (Entity.atom_inj.1 hei).symm
              · have hne : collapseStage U (m' + 1) (a : Germ (U : Filter I) (RawStage X (m' + 1))) ≠
                    collapseStage U 0 (b : Germ (U : Filter I) (RawStage X 0)) := by
                  intro heq
                  have hset := isSet_collapseStage_of_eventually_inr U heva
                  rw [heq, collapseStage_zero_coe] at hset
                  exact hset (Entity.isAtom_atom _)
                constructor
                · intro h; exact (hne h).elim
                · intro heq
                  have hfalse : ∀ᶠ _ : I in (U : Filter I), False :=
                    (heq.and heva).mono fun i ⟨hei, hai⟩ ↦ by
                      rw [hai] at hei
                      have hs := Entity.isSet_ofRaw_inr (fA i)
                      rw [hei] at hs
                      exact hs (Entity.isAtom_atom _)
                  exact (Filter.eventually_const.1 hfalse).elim
          | succ n' =>
              rcases germ_rawStage_succ_dichotomy U m' a with ⟨fa, heva⟩ | ⟨fA, heva⟩
              · rcases germ_rawStage_succ_dichotomy U n' b with ⟨fb, hevb⟩ | ⟨fB, hevb⟩
                · rw [collapseStage_eq_atom_of_eventually_inl U heva,
                    collapseStage_eq_atom_of_eventually_inl U hevb,
                    Entity.atom_inj, Germ.coe_eq]
                  constructor
                  · intro hab
                    exact ((hab.and heva).and hevb).mono fun i ⟨⟨hi, hai⟩, hbi⟩ ↦ by
                      rw [hai, hbi, Entity.ofRaw_inl, Entity.ofRaw_inl]
                      exact congrArg Entity.atom hi
                  · intro heq
                    exact ((heq.and heva).and hevb).mono fun i ⟨⟨hei, hai⟩, hbi⟩ ↦ by
                      rw [hai, hbi, Entity.ofRaw_inl, Entity.ofRaw_inl] at hei
                      exact Entity.atom_inj.1 hei
                · have hne : collapseStage U (m' + 1) (a : Germ (U : Filter I) (RawStage X (m' + 1))) ≠
                      collapseStage U (n' + 1) (b : Germ (U : Filter I) (RawStage X (n' + 1))) := by
                    intro heq
                    have hset := isSet_collapseStage_of_eventually_inr U hevb
                    rw [← heq, collapseStage_eq_atom_of_eventually_inl U heva] at hset
                    exact hset (Entity.isAtom_atom _)
                  constructor
                  · intro h; exact (hne h).elim
                  · intro heq
                    have hfalse : ∀ᶠ _ : I in (U : Filter I), False :=
                      ((heq.and heva).and hevb).mono fun i ⟨⟨hei, hai⟩, hbi⟩ ↦ by
                        rw [hai, hbi, Entity.ofRaw_inl] at hei
                        have hs := Entity.isSet_ofRaw_inr (fB i)
                        rw [← hei] at hs
                        exact hs (Entity.isAtom_atom _)
                    exact (Filter.eventually_const.1 hfalse).elim
              · rcases germ_rawStage_succ_dichotomy U n' b with ⟨fb, hevb⟩ | ⟨fB, hevb⟩
                · have hne : collapseStage U (m' + 1) (a : Germ (U : Filter I) (RawStage X (m' + 1))) ≠
                      collapseStage U (n' + 1) (b : Germ (U : Filter I) (RawStage X (n' + 1))) := by
                    intro heq
                    have hset := isSet_collapseStage_of_eventually_inr U heva
                    rw [heq, collapseStage_eq_atom_of_eventually_inl U hevb] at hset
                    exact hset (Entity.isAtom_atom _)
                  constructor
                  · intro h; exact (hne h).elim
                  · intro heq
                    have hfalse : ∀ᶠ _ : I in (U : Filter I), False :=
                      ((heq.and heva).and hevb).mono fun i ⟨⟨hei, hai⟩, hbi⟩ ↦ by
                        rw [hai, hbi, Entity.ofRaw_inl] at hei
                        have hs := Entity.isSet_ofRaw_inr (fA i)
                        rw [hei] at hs
                        exact hs (Entity.isAtom_atom _)
                    exact (Filter.eventually_const.1 hfalse).elim
                · have ih_mn : ∀ (u : I → RawStage X m') (v : I → RawStage X n'),
                      collapseStage U m' (u : Germ (U : Filter I) (RawStage X m')) =
                        collapseStage U n' (v : Germ (U : Filter I) (RawStage X n')) ↔
                        ∀ᶠ i in (U : Filter I), Entity.ofRaw (u i) = Entity.ofRaw (v i) :=
                    ih (m' + n') (by omega) m' n' rfl
                  constructor
                  · intro hEqSet
                    by_contra hnot
                    have hnot' : ∀ᶠ i in (U : Filter I),
                        Entity.ofRaw (a i) ≠ Entity.ofRaw (b i) :=
                      (Ultrafilter.eventually_not (f := U)).2 hnot
                    have hnotR : ∀ᶠ i in (U : Filter I),
                        ¬ RawEquiv (m := m' + 1) (n := n' + 1) (.inr (fA i)) (.inr (fB i)) :=
                      ((hnot'.and heva).and hevb).mono fun i ⟨⟨hne, hai⟩, hbi⟩ hr ↦
                        hne (by rw [hai, hbi]; exact Entity.ofRaw_eq_iff.2 hr)
                    have hor : ∀ᶠ i in (U : Filter I),
                        (∃ u ∈ fA i, ∀ v ∈ fB i, Entity.ofRaw u ≠ Entity.ofRaw v) ∨
                        (∃ v ∈ fB i, ∀ u ∈ fA i, Entity.ofRaw u ≠ Entity.ofRaw v) :=
                      hnotR.mono fun i hnr ↦ by
                        rw [RawEquiv, not_and_or] at hnr
                        push Not at hnr
                        rcases hnr with ⟨u, huA, hall⟩ | ⟨v, hvB, hall⟩
                        · exact Or.inl ⟨u, huA, fun v hvB h ↦ hall v hvB (Entity.ofRaw_eq_iff.1 h)⟩
                        · exact Or.inr ⟨v, hvB, fun u huA h ↦ hall u huA (Entity.ofRaw_eq_iff.1 h)⟩
                    rcases (Ultrafilter.eventually_or (f := U)).1 hor with hleft | hright
                    · obtain ⟨i₀, u₀, _, _⟩ := Filter.nonempty_of_mem hleft
                      let u : I → RawStage X m' := fun i ↦
                        if hi : ∃ u ∈ fA i, ∀ v ∈ fB i, Entity.ofRaw u ≠ Entity.ofRaw v then
                          hi.choose
                        else
                          u₀
                      have huA : ∀ᶠ i in (U : Filter I), u i ∈ fA i :=
                        hleft.mono fun i hi ↦ by simp only [u, hi, ↓reduceDIte]; exact hi.choose_spec.1
                      have huMem : collapseStage U m' (u : Germ (U : Filter I) (RawStage X m')) ∈
                          collapseStage U (m' + 1) (a : Germ (U : Filter I) (RawStage X (m' + 1))) :=
                        (mem_collapseStage_of_eventually_inr U heva).2 ⟨u, rfl, huA⟩
                      rw [hEqSet] at huMem
                      obtain ⟨v, hvEq, hvB'⟩ := (mem_collapseStage_of_eventually_inr U hevb).1 huMem
                      have huv := (ih_mn u v).1 hvEq
                      have hfalse : ∀ᶠ _ : I in (U : Filter I), False :=
                        ((hleft.and hvB').and huv).mono fun i ⟨⟨hi, hvi⟩, huvi⟩ ↦ by
                          have hspec : ∀ w ∈ fB i, Entity.ofRaw (u i) ≠ Entity.ofRaw w := by
                            simp only [u, hi, ↓reduceDIte]
                            exact hi.choose_spec.2
                          exact hspec (v i) hvi huvi
                      exact Filter.eventually_const.1 hfalse
                    · obtain ⟨i₀, v₀, _, _⟩ := Filter.nonempty_of_mem hright
                      let v : I → RawStage X n' := fun i ↦
                        if hi : ∃ v ∈ fB i, ∀ u ∈ fA i, Entity.ofRaw u ≠ Entity.ofRaw v then
                          hi.choose
                        else
                          v₀
                      have hvB : ∀ᶠ i in (U : Filter I), v i ∈ fB i :=
                        hright.mono fun i hi ↦ by simp only [v, hi, ↓reduceDIte]; exact hi.choose_spec.1
                      have hvMem : collapseStage U n' (v : Germ (U : Filter I) (RawStage X n')) ∈
                          collapseStage U (n' + 1) (b : Germ (U : Filter I) (RawStage X (n' + 1))) :=
                        (mem_collapseStage_of_eventually_inr U hevb).2 ⟨v, rfl, hvB⟩
                      rw [← hEqSet] at hvMem
                      obtain ⟨u, huEq, huA'⟩ := (mem_collapseStage_of_eventually_inr U heva).1 hvMem
                      have huv := (ih_mn u v).1 huEq.symm
                      have hfalse : ∀ᶠ _ : I in (U : Filter I), False :=
                        ((hright.and huA').and huv).mono fun i ⟨⟨hi, hui⟩, huvi⟩ ↦ by
                          have hspec : ∀ w ∈ fA i, Entity.ofRaw w ≠ Entity.ofRaw (v i) := by
                            simp only [v, hi, ↓reduceDIte]
                            exact hi.choose_spec.2
                          exact hspec (u i) hui huvi
                      exact Filter.eventually_const.1 hfalse
                  · intro heq
                    have hR : ∀ᶠ i in (U : Filter I),
                        RawEquiv (m := m' + 1) (n := n' + 1) (.inr (fA i)) (.inr (fB i)) :=
                      ((heq.and heva).and hevb).mono fun i ⟨⟨hei, hai⟩, hbi⟩ ↦ by
                        rw [hai, hbi] at hei
                        exact Entity.ofRaw_eq_iff.1 hei
                    refine Entity.set_ext
                      (isSet_collapseStage_of_eventually_inr U heva)
                      (isSet_collapseStage_of_eventually_inr U hevb) fun y ↦ ?_
                    rw [mem_collapseStage_of_eventually_inr U heva,
                      mem_collapseStage_of_eventually_inr U hevb]
                    constructor
                    · rintro ⟨u, rfl, huA'⟩
                      have hexv : ∀ᶠ i in (U : Filter I),
                          ∃ v ∈ fB i, Entity.ofRaw (u i) = Entity.ofRaw v :=
                        (hR.and huA').mono fun i ⟨hri, hui⟩ ↦ by
                          obtain ⟨v, hvi, hruv⟩ := hri.1 (u i) hui
                          exact ⟨v, hvi, Entity.ofRaw_eq_iff.2 hruv⟩
                      obtain ⟨i₀, v₀, _, _⟩ := Filter.nonempty_of_mem hexv
                      let v : I → RawStage X n' := fun i ↦
                        if hi : ∃ v ∈ fB i, Entity.ofRaw (u i) = Entity.ofRaw v then
                          hi.choose
                        else
                          v₀
                      have hv_spec : ∀ᶠ i in (U : Filter I),
                          v i ∈ fB i ∧ Entity.ofRaw (u i) = Entity.ofRaw (v i) :=
                        hexv.mono fun i hi ↦ by
                          simp only [v, hi, ↓reduceDIte]
                          exact hi.choose_spec
                      exact ⟨v, (ih_mn u v).2 (hv_spec.mono fun _ h ↦ h.2),
                        hv_spec.mono fun _ h ↦ h.1⟩
                    · rintro ⟨v, rfl, hvB'⟩
                      have hexu : ∀ᶠ i in (U : Filter I),
                          ∃ u ∈ fA i, Entity.ofRaw u = Entity.ofRaw (v i) :=
                        (hR.and hvB').mono fun i ⟨hri, hvi⟩ ↦ by
                          obtain ⟨u, hui, hruv⟩ := hri.2 (v i) hvi
                          exact ⟨u, hui, Entity.ofRaw_eq_iff.2 hruv⟩
                      obtain ⟨i₀, u₀, _, _⟩ := Filter.nonempty_of_mem hexu
                      let u : I → RawStage X m' := fun i ↦
                        if hi : ∃ u ∈ fA i, Entity.ofRaw u = Entity.ofRaw (v i) then
                          hi.choose
                        else
                          u₀
                      have hu_spec : ∀ᶠ i in (U : Filter I),
                          u i ∈ fA i ∧ Entity.ofRaw (u i) = Entity.ofRaw (v i) :=
                        hexu.mono fun i hi ↦ by
                          simp only [u, hi, ↓reduceDIte]
                          exact hi.choose_spec
                      exact ⟨u, ((ih_mn u v).2 (hu_spec.mono fun _ h ↦ h.2)).symm,
                        hu_spec.mono fun _ h ↦ h.1⟩

/-- Atomic membership part of Łoś's Theorem across arbitrary stages `m, n`:
`collapseStage U m ↑a ∈ collapseStage U n ↑b ↔ ∀ᶠ i in U, Entity.ofRaw (a i) ∈ Entity.ofRaw (b i)`
(Goldblatt §13.8, p. 168). -/
theorem collapseStage_coe_mem_iff {I X : Type*} (U : Ultrafilter I)
    {m n : ℕ} (a : I → RawStage X m) (b : I → RawStage X n) :
    collapseStage U m (a : Germ (U : Filter I) (RawStage X m)) ∈
      collapseStage U n (b : Germ (U : Filter I) (RawStage X n)) ↔
      ∀ᶠ i in (U : Filter I), Entity.ofRaw (a i) ∈ Entity.ofRaw (b i) := by
  cases n with
  | zero =>
      rw [collapseStage_zero_coe]
      constructor
      · intro h; exact (Entity.not_mem_atom _ _ h).elim
      · intro h
        have hfalse : ∀ᶠ _ : I in (U : Filter I), False :=
          h.mono fun i hi ↦ Entity.not_mem_atom _ _ hi
        exact (Filter.eventually_const.1 hfalse).elim
  | succ n' =>
      rcases germ_rawStage_succ_dichotomy U n' b with ⟨fb, hevb⟩ | ⟨fB, hevb⟩
      · rw [collapseStage_eq_atom_of_eventually_inl U hevb]
        constructor
        · intro h; exact (Entity.not_mem_atom _ _ h).elim
        · intro h
          have hfalse : ∀ᶠ _ : I in (U : Filter I), False :=
            (h.and hevb).mono fun i ⟨hi, hbi⟩ ↦ by
              rw [hbi, Entity.ofRaw_inl] at hi
              exact Entity.not_mem_atom _ _ hi
          exact (Filter.eventually_const.1 hfalse).elim
      · rw [mem_collapseStage_of_eventually_inr U hevb]
        constructor
        · rintro ⟨u, huEq, huB'⟩
          have huv := (collapseStage_coe_eq_iff U a u).1 huEq
          exact ((huv.and huB').and hevb).mono fun i ⟨⟨hei, hui⟩, hbi⟩ ↦ by
            rw [hbi, hei]
            exact Entity.mem_ofRaw_inr.2 ⟨u i, hui, rfl⟩
        · intro hmem
          have hex : ∀ᶠ i in (U : Filter I),
              ∃ u ∈ fB i, Entity.ofRaw (a i) = Entity.ofRaw u :=
            (hmem.and hevb).mono fun i ⟨hi, hbi⟩ ↦ by
              rw [hbi] at hi
              obtain ⟨u, hui, heq⟩ := Entity.mem_ofRaw_inr.1 hi
              exact ⟨u, hui, heq⟩
          obtain ⟨i₀, u₀, _, _⟩ := Filter.nonempty_of_mem hex
          let u : I → RawStage X n' := fun i ↦
            if hi : ∃ u ∈ fB i, Entity.ofRaw (a i) = Entity.ofRaw u then hi.choose else u₀
          have hu_spec : ∀ᶠ i in (U : Filter I),
              u i ∈ fB i ∧ Entity.ofRaw (a i) = Entity.ofRaw (u i) :=
            hex.mono fun i hi ↦ by simp only [u, hi, ↓reduceDIte]; exact hi.choose_spec
          exact ⟨u, (collapseStage_coe_eq_iff U a u).2 (hu_spec.mono fun _ h ↦ h.2),
            hu_spec.mono fun _ h ↦ h.1⟩

/-- Total representative extractor into `RawStage X (N + 1)` (always inhabited by `Sum.inr ∅`
without requiring `Nonempty X`; Goldblatt §13.6 & §13.8, pp. 164, 168). -/
def Entity.toRawAt {X : Type*} (N : ℕ) (e : Entity X) : RawStage X (N + 1) :=
  if h : e ∈ VStage X (N + 1) then h.choose else Sum.inr ∅

/-- `Entity.ofRaw (e.toRawAt N) = e` whenever `e ∈ VStage X (N + 1)` (Goldblatt §13.6, p. 164). -/
theorem Entity.ofRaw_toRawAt {X : Type*} {N : ℕ} {e : Entity X}
    (he : e ∈ VStage X (N + 1)) :
    Entity.ofRaw (e.toRawAt N) = e := by
  unfold Entity.toRawAt
  simp only [he, ↓reduceDIte]
  exact he.choose_spec

/-- Goldblatt §13.8 (p. 168): The concrete ultrapower superstructure transfer map
`ultrapowerStar U : Entity X → Entity (Germ U X)` sending each `[⟨m, a⟩]` to the collapse of its
constant stage-`m` germ. -/
def ultrapowerStar {I X : Type*} (U : Ultrafilter I) :
    Entity X → Entity (Germ (U : Filter I) X) :=
  Quotient.lift
    (fun s : (m : ℕ) × RawStage X m ↦
      collapseStage U s.1 ((fun _ : I ↦ s.2) : Germ (U : Filter I) (RawStage X s.1)))
    fun s₁ s₂ h ↦
      (collapseStage_coe_eq_iff U (fun _ ↦ s₁.2) (fun _ ↦ s₂.2)).2
        (Filter.Eventually.of_forall fun _ ↦ Entity.ofRaw_eq_iff.2 h)

/-- `ultrapowerStar U` on `Entity.ofRaw a` (Goldblatt §13.8, p. 168). -/
@[simp]
theorem ultrapowerStar_ofRaw {I X : Type*} (U : Ultrafilter I) {m : ℕ} (a : RawStage X m) :
    ultrapowerStar U (Entity.ofRaw a) =
      collapseStage U m ((fun _ : I ↦ a) : Germ (U : Filter I) (RawStage X m)) := rfl

/-- `ultrapowerStar U` maps each individual `atom x` to `atom ↑x` (Goldblatt §13.8, p. 168). -/
@[simp]
theorem ultrapowerStar_atom {I X : Type*} (U : Ultrafilter I) (x : X) :
    ultrapowerStar U (Entity.atom x) = Entity.atom (x : Germ (U : Filter I) X) := rfl

/-- `ultrapowerStar U ∅ = ∅` (Goldblatt §13.8, p. 168). -/
@[simp]
theorem ultrapowerStar_empty {I X : Type*} (U : Ultrafilter I) :
    ultrapowerStar U (∅ : Entity X) = ∅ := by
  let e₀ : I → RawStage X 1 := fun _ ↦ Sum.inr ∅
  have hev : ∀ᶠ i : I in (U : Filter I), e₀ i = Sum.inr ∅ :=
    Filter.Eventually.of_forall fun _ ↦ rfl
  change collapseStage U 1 (e₀ : Germ (U : Filter I) (RawStage X 1)) = ∅
  refine (Entity.eq_empty_iff_forall_not_mem (isSet_collapseStage_of_eventually_inr U hev)).2
    fun y hy ↦ ?_
  obtain ⟨u, _, hu⟩ := (mem_collapseStage_of_eventually_inr U hev).1 hy
  exact False.elim (Filter.eventually_const.1 (hu.mono fun _ h ↦ h))

/-- Setness part of Łoś's Theorem: `(collapseStage U N ↑r).IsSet ↔ ∀ᶠ i in U, (ofRaw (r i)).IsSet`
(Goldblatt §13.8, p. 169). -/
theorem collapseStage_isSet_iff {I X : Type*} (U : Ultrafilter I) {N : ℕ}
    (r : I → RawStage X N) :
    (collapseStage U N (r : Germ (U : Filter I) (RawStage X N))).IsSet ↔
      ∀ᶠ i in (U : Filter I), (Entity.ofRaw (r i)).IsSet := by
  cases N with
  | zero =>
      rw [collapseStage_zero_coe]
      constructor
      · intro hs; exact (hs (Entity.isAtom_atom _)).elim
      · intro hs
        exact (Filter.eventually_const.1 (hs.mono fun _ hi ↦ hi (Entity.isAtom_atom _))).elim
  | succ N' =>
      rcases germ_rawStage_succ_dichotomy U N' r with ⟨fr, hevr⟩ | ⟨fR, hevr⟩
      · rw [collapseStage_eq_atom_of_eventually_inl U hevr]
        constructor
        · intro hs; exact (hs (Entity.isAtom_atom _)).elim
        · intro hs
          have hfalse : ∀ᶠ _ : I in (U : Filter I), False :=
            (hs.and hevr).mono fun i ⟨hsi, hri⟩ ↦ by
              rw [hri, Entity.ofRaw_inl] at hsi
              exact hsi (Entity.isAtom_atom _)
          exact (Filter.eventually_const.1 hfalse).elim
      · exact ⟨fun _ ↦ hevr.mono fun i hri ↦ by rw [hri]; exact Entity.isSet_ofRaw_inr _,
          fun _ ↦ isSet_collapseStage_of_eventually_inr U hevr⟩

/-- Unordered-pair preservation under `collapseStage` (Goldblatt §13.8, p. 168). -/
theorem collapseStage_eq_upair_of_eventually {I X : Type*} (U : Ultrafilter I)
    {m n N : ℕ} (a : I → RawStage X m) (b : I → RawStage X n) (r : I → RawStage X N)
    (hr : ∀ᶠ i in (U : Filter I),
      Entity.ofRaw (r i) = Entity.upair (Entity.ofRaw (a i)) (Entity.ofRaw (b i))) :
    collapseStage U N (r : Germ (U : Filter I) (RawStage X N)) =
      Entity.upair (collapseStage U m (a : Germ (U : Filter I) (RawStage X m)))
        (collapseStage U n (b : Germ (U : Filter I) (RawStage X n))) := by
  have hr_set : (collapseStage U N (r : Germ (U : Filter I) (RawStage X N))).IsSet :=
    (collapseStage_isSet_iff U r).2 (hr.mono fun i hi ↦ by rw [hi]; exact Entity.isSet_upair _ _)
  refine Entity.set_ext hr_set (Entity.isSet_upair _ _) fun y ↦ ?_
  rw [Entity.mem_upair_iff]
  constructor
  · intro hy
    obtain ⟨k, u, _, rfl⟩ := exists_collapseStage_of_mem U hy
    have hmem := (collapseStage_coe_mem_iff U u r).1 hy
    have hor : ∀ᶠ i in (U : Filter I),
        Entity.ofRaw (u i) = Entity.ofRaw (a i) ∨ Entity.ofRaw (u i) = Entity.ofRaw (b i) :=
      (hmem.and hr).mono fun i ⟨hmi, hri⟩ ↦ by
        rw [hri, Entity.mem_upair_iff] at hmi
        exact hmi
    rcases (Ultrafilter.eventually_or (f := U)).1 hor with ha | hb
    · exact Or.inl ((collapseStage_coe_eq_iff U u a).2 ha)
    · exact Or.inr ((collapseStage_coe_eq_iff U u b).2 hb)
  · rintro (rfl | rfl)
    · exact (collapseStage_coe_mem_iff U a r).2 (hr.mono fun i hri ↦ by
        rw [hri]; exact Entity.mem_upair_iff.2 (Or.inl rfl))
    · exact (collapseStage_coe_mem_iff U b r).2 (hr.mono fun i hri ↦ by
        rw [hri]; exact Entity.mem_upair_iff.2 (Or.inr rfl))

/-- Kuratowski ordered-pair preservation under `collapseStage` (Goldblatt §13.8, p. 169). -/
theorem collapseStage_eq_kpair_of_eventually {I X : Type*} (U : Ultrafilter I)
    {m n N : ℕ} (a : I → RawStage X m) (b : I → RawStage X n) (r : I → RawStage X N)
    (hr : ∀ᶠ i in (U : Filter I),
      Entity.ofRaw (r i) = Entity.kpair (Entity.ofRaw (a i)) (Entity.ofRaw (b i))) :
    collapseStage U N (r : Germ (U : Filter I) (RawStage X N)) =
      Entity.kpair (collapseStage U m (a : Germ (U : Filter I) (RawStage X m)))
        (collapseStage U n (b : Germ (U : Filter I) (RawStage X n))) := by
  let M : ℕ := max m n
  let r₁ : I → RawStage X (M + 1) := fun i ↦
    (Entity.upair (Entity.ofRaw (a i)) (Entity.ofRaw (a i))).toRawAt M
  let r₂ : I → RawStage X (M + 1) := fun i ↦
    (Entity.upair (Entity.ofRaw (a i)) (Entity.ofRaw (b i))).toRawAt M
  have haM : ∀ i : I, Entity.ofRaw (a i) ∈ VStage X M := fun i ↦
    vStage_mono (Nat.le_max_left m n) ⟨a i, rfl⟩
  have hbM : ∀ i : I, Entity.ofRaw (b i) ∈ VStage X M := fun i ↦
    vStage_mono (Nat.le_max_right m n) ⟨b i, rfl⟩
  have hr₁ : ∀ i : I, Entity.ofRaw (r₁ i) = Entity.upair (Entity.ofRaw (a i)) (Entity.ofRaw (a i)) :=
    fun i ↦ Entity.ofRaw_toRawAt (Entity.upair_mem_vStage (haM i) (haM i))
  have hr₂ : ∀ i : I, Entity.ofRaw (r₂ i) = Entity.upair (Entity.ofRaw (a i)) (Entity.ofRaw (b i)) :=
    fun i ↦ Entity.ofRaw_toRawAt (Entity.upair_mem_vStage (haM i) (hbM i))
  have hc₁ := collapseStage_eq_upair_of_eventually U a a r₁ (Filter.Eventually.of_forall hr₁)
  have hc₂ := collapseStage_eq_upair_of_eventually U a b r₂ (Filter.Eventually.of_forall hr₂)
  have hc := collapseStage_eq_upair_of_eventually U r₁ r₂ r
    (hr.mono fun i hri ↦ by rw [hri, Entity.kpair, Entity.singleton, hr₁ i, hr₂ i])
  rw [hc, hc₁, hc₂, Entity.kpair, Entity.singleton]

/-- Iterated `k`-tuple preservation under `collapseStage` (Goldblatt §13.8, p. 169). -/
theorem collapseStage_eq_ktuple_of_eventually {I X : Type*} (U : Ultrafilter I) :
    ∀ {k N : ℕ} (w : Fin k → (m : ℕ) × (I → RawStage X m)) (r : I → RawStage X N),
      (∀ᶠ i in (U : Filter I),
        Entity.ofRaw (r i) = Entity.ktuple (fun j ↦ Entity.ofRaw ((w j).2 i))) →
      collapseStage U N (r : Germ (U : Filter I) (RawStage X N)) =
        Entity.ktuple (fun j ↦
          collapseStage U (w j).1 ((w j).2 : Germ (U : Filter I) (RawStage X (w j).1)))
  | 0, N, _, r, hr => by
      let e₀ : I → RawStage X 1 := fun _ ↦ Sum.inr ∅
      have hemp : collapseStage U 1 (e₀ : Germ (U : Filter I) (RawStage X 1)) = ∅ :=
        ultrapowerStar_empty U
      change collapseStage U N (r : Germ (U : Filter I) (RawStage X N)) = ∅
      rw [← hemp]
      exact (collapseStage_coe_eq_iff U r e₀).2 (hr.mono fun i hri ↦ by rw [hri]; rfl)
  | 1, N, w, r, hr =>
      (collapseStage_coe_eq_iff U r (w 0).2).2 hr
  | 2, N, w, r, hr =>
      collapseStage_eq_kpair_of_eventually U (w 0).2 (w 1).2 r hr
  | k + 3, N, w, r, hr => by
      let M : ℕ := Finset.univ.sup fun j : Fin (k + 3) ↦ (w j).1
      let K : ℕ := M + 2 * (k + 2) + 1
      let r_init : I → RawStage X (K + 1) := fun i ↦
        (Entity.ktuple (fun j : Fin (k + 2) ↦ Entity.ofRaw ((w j.castSucc).2 i))).toRawAt K
      have hr_init : ∀ i : I, Entity.ofRaw (r_init i) =
          Entity.ktuple (fun j : Fin (k + 2) ↦ Entity.ofRaw ((w j.castSucc).2 i)) := by
        intro i
        refine Entity.ofRaw_toRawAt (vStage_mono (Nat.le_succ K) ?_)
        refine Entity.ktuple_mem_vStage fun j ↦ ?_
        exact vStage_mono (Finset.le_sup (f := fun q : Fin (k + 3) ↦ (w q).1)
          (Finset.mem_univ j.castSucc)) ⟨(w j.castSucc).2 i, rfl⟩
      have hc_init := collapseStage_eq_ktuple_of_eventually U (Fin.init w) r_init
        (Filter.Eventually.of_forall hr_init)
      have hc := collapseStage_eq_kpair_of_eventually U r_init (w (Fin.last (k + 2))).2 r
        (hr.mono fun i hri ↦ by rw [hri, Entity.ktuple, hr_init i]; rfl)
      rw [hc, hc_init]
      rfl

/-- Both coordinates of a Kuratowski pair belonging to `collapseStage U N ↑f` themselves belong to
the range of `collapseStage` (Goldblatt §13.8 & §13.10, pp. 168, 173). -/
theorem exists_collapseStage_of_kpair_mem {I X : Type*} (U : Ultrafilter I)
    {N : ℕ} {f : I → RawStage X N} {A B : Entity (Germ (U : Filter I) X)}
    (hp : Entity.kpair A B ∈ collapseStage U N (f : Germ (U : Filter I) (RawStage X N))) :
    (∃ (ma : ℕ) (ua : I → RawStage X ma),
      A = collapseStage U ma (ua : Germ (U : Filter I) (RawStage X ma))) ∧
    (∃ (mb : ℕ) (ub : I → RawStage X mb),
      B = collapseStage U mb (ub : Germ (U : Filter I) (RawStage X mb))) := by
  obtain ⟨m₁, u₁, _, hpEq⟩ := exists_collapseStage_of_mem U hp
  have hu_mem : Entity.upair A B ∈ collapseStage U m₁ (u₁ : Germ (U : Filter I) (RawStage X m₁)) := by
    rw [← hpEq]
    exact Entity.mem_upair_iff.2 (Or.inr rfl)
  obtain ⟨m₂, u₂, _, huEq⟩ := exists_collapseStage_of_mem U hu_mem
  have hA_mem : A ∈ collapseStage U m₂ (u₂ : Germ (U : Filter I) (RawStage X m₂)) := by
    rw [← huEq]
    exact Entity.mem_upair_iff.2 (Or.inl rfl)
  have hB_mem : B ∈ collapseStage U m₂ (u₂ : Germ (U : Filter I) (RawStage X m₂)) := by
    rw [← huEq]
    exact Entity.mem_upair_iff.2 (Or.inr rfl)
  obtain ⟨ma, ua, _, hA⟩ := exists_collapseStage_of_mem U hA_mem
  obtain ⟨mb, ub, _, hB⟩ := exists_collapseStage_of_mem U hB_mem
  exact ⟨⟨ma, ua, hA⟩, ⟨mb, ub, hB⟩⟩

/-- Helper creating a uniform raw stage sequence for any `kpair` over two sequences
(Goldblatt §13.8, p. 169). -/
theorem kpair_collapseStage_mem_iff {I X : Type*} (U : Ultrafilter I)
    {ma mb N : ℕ} (ua : I → RawStage X ma) (ub : I → RawStage X mb) (f : I → RawStage X N) :
    Entity.kpair
      (collapseStage U ma (ua : Germ (U : Filter I) (RawStage X ma)))
      (collapseStage U mb (ub : Germ (U : Filter I) (RawStage X mb))) ∈
      collapseStage U N (f : Germ (U : Filter I) (RawStage X N)) ↔
      ∀ᶠ i in (U : Filter I),
        Entity.kpair (Entity.ofRaw (ua i)) (Entity.ofRaw (ub i)) ∈ Entity.ofRaw (f i) := by
  let M : ℕ := max ma mb + 2
  let rp : I → RawStage X (M + 1) := fun i ↦
    (Entity.kpair (Entity.ofRaw (ua i)) (Entity.ofRaw (ub i))).toRawAt M
  have hrp : ∀ i : I, Entity.ofRaw (rp i) =
      Entity.kpair (Entity.ofRaw (ua i)) (Entity.ofRaw (ub i)) := by
    intro i
    refine Entity.ofRaw_toRawAt (vStage_mono (by omega : max ma mb + 2 ≤ M + 1) ?_)
    exact Entity.kpair_mem_vStage
      (vStage_mono (Nat.le_max_left ma mb) ⟨ua i, rfl⟩)
      (vStage_mono (Nat.le_max_right ma mb) ⟨ub i, rfl⟩)
  rw [← collapseStage_eq_kpair_of_eventually U ua ub rp (Filter.Eventually.of_forall hrp),
    collapseStage_coe_mem_iff U rp f]
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun i ↦ by rw [hrp i])

/-- Functionality part of Łoś's Theorem: `(collapseStage U N ↑f).IsFuncEntity ↔ ∀ᶠ i in U, (ofRaw (f i)).IsFuncEntity`
(Goldblatt §13.8, p. 169). -/
theorem collapseStage_isFuncEntity_iff {I X : Type*} (U : Ultrafilter I)
    {N : ℕ} (f : I → RawStage X N) :
    (collapseStage U N (f : Germ (U : Filter I) (RawStage X N))).IsFuncEntity ↔
      ∀ᶠ i in (U : Filter I), (Entity.ofRaw (f i)).IsFuncEntity := by
  constructor
  · rintro ⟨⟨hfSet, hfRel⟩, hfSv⟩
    have hevSet := (collapseStage_isSet_iff U f).1 hfSet
    by_contra hnot
    have hnot' : ∀ᶠ i in (U : Filter I), ¬ (Entity.ofRaw (f i)).IsFuncEntity :=
      (Ultrafilter.eventually_not (f := U)).2 hnot
    have hor : ∀ᶠ i in (U : Filter I),
        (∃ p ∈ Entity.ofRaw (f i), ∀ a b : Entity X, p ≠ Entity.kpair a b) ∨
        (∃ a b c : Entity X,
          Entity.kpair a b ∈ Entity.ofRaw (f i) ∧
          Entity.kpair a c ∈ Entity.ofRaw (f i) ∧ b ≠ c) :=
      (hevSet.and hnot').mono fun i ⟨hsi, hni⟩ ↦ by
        by_cases hrel : (Entity.ofRaw (f i)).IsBinaryRel
        · refine Or.inr ?_
          have hnsv : ¬ ∀ a b c : Entity X,
              Entity.kpair a b ∈ Entity.ofRaw (f i) →
              Entity.kpair a c ∈ Entity.ofRaw (f i) → b = c := fun hsv ↦ hni ⟨hrel, hsv⟩
          push Not at hnsv
          exact hnsv
        · refine Or.inl ?_
          have hnrel : ¬ ∀ p ∈ Entity.ofRaw (f i), ∃ a b : Entity X, p = Entity.kpair a b :=
            fun hr ↦ hrel ⟨hsi, hr⟩
          push Not at hnrel
          exact hnrel
    rcases (Ultrafilter.eventually_or (f := U)).1 hor with hbadRel | hbadSv
    · let rp : I → RawStage X (N + 1) := fun i ↦
        if hi : ∃ p ∈ Entity.ofRaw (f i), ∀ a b : Entity X, p ≠ Entity.kpair a b then
          hi.choose.toRawAt N
        else
          Sum.inr ∅
      have hrp_spec : ∀ᶠ i in (U : Filter I),
          Entity.ofRaw (rp i) ∈ Entity.ofRaw (f i) ∧
          (∀ a b : Entity X, Entity.ofRaw (rp i) ≠ Entity.kpair a b) :=
        hbadRel.mono fun i hi ↦ by
          have hp_mem : hi.choose ∈ Entity.ofRaw (f i) := hi.choose_spec.1
          have hp_stage : hi.choose ∈ VStage X (N + 1) := by
            have hlt := Entity.rank_lt_of_mem hp_mem
            have hle : (Entity.ofRaw (f i)).rank ≤ N := mem_vStage_iff_rank_le.1 ⟨f i, rfl⟩
            exact mem_vStage_iff_rank_le.2 (by omega)
          have heq : Entity.ofRaw (rp i) = hi.choose := by
            simp only [rp, hi, ↓reduceDIte]
            exact Entity.ofRaw_toRawAt hp_stage
          exact ⟨heq ▸ hp_mem, heq ▸ hi.choose_spec.2⟩
      have hp_in : collapseStage U (N + 1) (rp : Germ (U : Filter I) (RawStage X (N + 1))) ∈
          collapseStage U N (f : Germ (U : Filter I) (RawStage X N)) :=
        (collapseStage_coe_mem_iff U rp f).2 (hrp_spec.mono fun _ h ↦ h.1)
      obtain ⟨A, B, hpAB⟩ := hfRel _ hp_in
      have hAB_in : Entity.kpair A B ∈ collapseStage U N (f : Germ (U : Filter I) (RawStage X N)) :=
        hpAB ▸ hp_in
      obtain ⟨⟨ma, ua, rfl⟩, ⟨mb, ub, rfl⟩⟩ := exists_collapseStage_of_kpair_mem U hAB_in
      let M : ℕ := max ma mb + 2
      let rq : I → RawStage X (M + 1) := fun i ↦
        (Entity.kpair (Entity.ofRaw (ua i)) (Entity.ofRaw (ub i))).toRawAt M
      have hrq : ∀ i : I, Entity.ofRaw (rq i) =
          Entity.kpair (Entity.ofRaw (ua i)) (Entity.ofRaw (ub i)) := fun i ↦
        Entity.ofRaw_toRawAt (vStage_mono (by omega : max ma mb + 2 ≤ M + 1)
          (Entity.kpair_mem_vStage
            (vStage_mono (Nat.le_max_left ma mb) ⟨ua i, rfl⟩)
            (vStage_mono (Nat.le_max_right ma mb) ⟨ub i, rfl⟩)))
      rw [← collapseStage_eq_kpair_of_eventually U ua ub rq (Filter.Eventually.of_forall hrq)] at hpAB
      have hpq := (collapseStage_coe_eq_iff U rp rq).1 hpAB
      have hfalse : ∀ᶠ _ : I in (U : Filter I), False :=
        (hrp_spec.and hpq).mono fun i ⟨⟨_, hne⟩, heqi⟩ ↦
          hne (Entity.ofRaw (ua i)) (Entity.ofRaw (ub i)) (heqi.trans (hrq i))
      exact Filter.eventually_const.1 hfalse
    · let ra : I → RawStage X (N + 1) := fun i ↦
        if hi : ∃ a b c : Entity X,
            Entity.kpair a b ∈ Entity.ofRaw (f i) ∧
            Entity.kpair a c ∈ Entity.ofRaw (f i) ∧ b ≠ c then
          hi.choose.toRawAt N
        else
          Sum.inr ∅
      let rb : I → RawStage X (N + 1) := fun i ↦
        if hi : ∃ a b c : Entity X,
            Entity.kpair a b ∈ Entity.ofRaw (f i) ∧
            Entity.kpair a c ∈ Entity.ofRaw (f i) ∧ b ≠ c then
          hi.choose_spec.choose.toRawAt N
        else
          Sum.inr ∅
      let rc : I → RawStage X (N + 1) := fun i ↦
        if hi : ∃ a b c : Entity X,
            Entity.kpair a b ∈ Entity.ofRaw (f i) ∧
            Entity.kpair a c ∈ Entity.ofRaw (f i) ∧ b ≠ c then
          hi.choose_spec.choose_spec.choose.toRawAt N
        else
          Sum.inr ∅
      have hspec : ∀ᶠ i in (U : Filter I),
          Entity.kpair (Entity.ofRaw (ra i)) (Entity.ofRaw (rb i)) ∈ Entity.ofRaw (f i) ∧
          Entity.kpair (Entity.ofRaw (ra i)) (Entity.ofRaw (rc i)) ∈ Entity.ofRaw (f i) ∧
          Entity.ofRaw (rb i) ≠ Entity.ofRaw (rc i) :=
        hbadSv.mono fun i hi ↦ by
          have h1 := hi.choose_spec.choose_spec.choose_spec.1
          have h2 := hi.choose_spec.choose_spec.choose_spec.2.1
          have h3 := hi.choose_spec.choose_spec.choose_spec.2.2
          have hfle : (Entity.ofRaw (f i)).rank ≤ N := mem_vStage_iff_rank_le.1 ⟨f i, rfl⟩
          have hab_lt := Entity.rank_lt_of_kpair_mem h1
          have hac_lt := Entity.rank_lt_of_kpair_mem h2
          have ha_eq : Entity.ofRaw (ra i) = hi.choose := by
            simp only [ra, hi, ↓reduceDIte]
            exact Entity.ofRaw_toRawAt (mem_vStage_iff_rank_le.2 (by omega))
          have hb_eq : Entity.ofRaw (rb i) = hi.choose_spec.choose := by
            simp only [rb, hi, ↓reduceDIte]
            exact Entity.ofRaw_toRawAt (mem_vStage_iff_rank_le.2 (by omega))
          have hc_eq : Entity.ofRaw (rc i) = hi.choose_spec.choose_spec.choose := by
            simp only [rc, hi, ↓reduceDIte]
            exact Entity.ofRaw_toRawAt (mem_vStage_iff_rank_le.2 (by omega))
          rw [ha_eq, hb_eq, hc_eq]
          exact ⟨h1, h2, h3⟩
      have hab' := (kpair_collapseStage_mem_iff U ra rb f).2 (hspec.mono fun _ h ↦ h.1)
      have hac' := (kpair_collapseStage_mem_iff U ra rc f).2 (hspec.mono fun _ h ↦ h.2.1)
      have hbcEq := (collapseStage_coe_eq_iff U rb rc).1 (hfSv _ _ _ hab' hac')
      exact Filter.eventually_const.1
        ((hspec.and hbcEq).mono fun _ ⟨⟨_, _, hne⟩, heq⟩ ↦ hne heq)
  · intro hf
    refine ⟨⟨(collapseStage_isSet_iff U f).2 (hf.mono fun _ h ↦ h.1.1), fun y hy ↦ ?_⟩,
      fun A B C hAB hAC ↦ ?_⟩
    · obtain ⟨m, u, _, rfl⟩ := exists_collapseStage_of_mem U hy
      have hu_in := (collapseStage_coe_mem_iff U u f).1 hy
      have hex : ∀ᶠ i in (U : Filter I),
          ∃ a b : Entity X, a ∈ VStage X (N + 1) ∧ b ∈ VStage X (N + 1) ∧
            Entity.ofRaw (u i) = Entity.kpair a b :=
        (hf.and hu_in).mono fun i ⟨hfi, hui⟩ ↦ by
          obtain ⟨a, b, hab⟩ := hfi.1.2 _ hui
          have hfle : (Entity.ofRaw (f i)).rank ≤ N := mem_vStage_iff_rank_le.1 ⟨f i, rfl⟩
          have hlt := Entity.rank_lt_of_kpair_mem (hab ▸ hui)
          exact ⟨a, b, mem_vStage_iff_rank_le.2 (by omega),
            mem_vStage_iff_rank_le.2 (by omega), hab⟩
      let ra : I → RawStage X (N + 1) := fun i ↦
        if hi : ∃ a b : Entity X, a ∈ VStage X (N + 1) ∧ b ∈ VStage X (N + 1) ∧
            Entity.ofRaw (u i) = Entity.kpair a b then
          hi.choose.toRawAt N
        else
          Sum.inr ∅
      let rb : I → RawStage X (N + 1) := fun i ↦
        if hi : ∃ a b : Entity X, a ∈ VStage X (N + 1) ∧ b ∈ VStage X (N + 1) ∧
            Entity.ofRaw (u i) = Entity.kpair a b then
          hi.choose_spec.choose.toRawAt N
        else
          Sum.inr ∅
      have hrab : ∀ᶠ i in (U : Filter I),
          Entity.ofRaw (u i) = Entity.kpair (Entity.ofRaw (ra i)) (Entity.ofRaw (rb i)) :=
        hex.mono fun i hi ↦ by
          have ha_eq : Entity.ofRaw (ra i) = hi.choose := by
            simp only [ra, hi, ↓reduceDIte]
            exact Entity.ofRaw_toRawAt hi.choose_spec.choose_spec.1
          have hb_eq : Entity.ofRaw (rb i) = hi.choose_spec.choose := by
            simp only [rb, hi, ↓reduceDIte]
            exact Entity.ofRaw_toRawAt hi.choose_spec.choose_spec.2.1
          rw [ha_eq, hb_eq]
          exact hi.choose_spec.choose_spec.2.2
      exact ⟨collapseStage U (N + 1) (ra : Germ (U : Filter I) (RawStage X (N + 1))),
        collapseStage U (N + 1) (rb : Germ (U : Filter I) (RawStage X (N + 1))),
        collapseStage_eq_kpair_of_eventually U ra rb u hrab⟩
    · obtain ⟨⟨ma, ua, rfl⟩, ⟨mb, ub, rfl⟩⟩ := exists_collapseStage_of_kpair_mem U hAB
      obtain ⟨_, ⟨mc, uc, rfl⟩⟩ := exists_collapseStage_of_kpair_mem U hAC
      have hab_ev := (kpair_collapseStage_mem_iff U ua ub f).1 hAB
      have hac_ev := (kpair_collapseStage_mem_iff U ua uc f).1 hAC
      exact (collapseStage_coe_eq_iff U ub uc).2
        (((hf.and hab_ev).and hac_ev).mono fun i ⟨⟨hfi, habi⟩, haci⟩ ↦
          hfi.2 _ _ _ habi haci)

/-- Domain membership part of Łoś's Theorem:
`collapseStage U m ↑a ∈ relDom (collapseStage U N ↑f) ↔ ∀ᶠ i in U, ofRaw (a i) ∈ relDom (ofRaw (f i))`
(Goldblatt §13.8, p. 169). -/
theorem collapseStage_mem_relDom_iff {I X : Type*} (U : Ultrafilter I)
    {m N : ℕ} (a : I → RawStage X m) (f : I → RawStage X N) :
    collapseStage U m (a : Germ (U : Filter I) (RawStage X m)) ∈
      Entity.relDom (collapseStage U N (f : Germ (U : Filter I) (RawStage X N))) ↔
      ∀ᶠ i in (U : Filter I), Entity.ofRaw (a i) ∈ Entity.relDom (Entity.ofRaw (f i)) := by
  rw [Entity.mem_relDom_iff]
  constructor
  · rintro ⟨B, hAB⟩
    obtain ⟨_, ⟨mb, ub, rfl⟩⟩ := exists_collapseStage_of_kpair_mem U hAB
    exact ((kpair_collapseStage_mem_iff U a ub f).1 hAB).mono fun i hi ↦
      Entity.mem_relDom_iff.2 ⟨Entity.ofRaw (ub i), hi⟩
  · intro hev
    let rb : I → RawStage X (N + 1) := fun i ↦
      if hi : ∃ b : Entity X, Entity.kpair (Entity.ofRaw (a i)) b ∈ Entity.ofRaw (f i) then
        hi.choose.toRawAt N
      else
        Sum.inr ∅
    have hrb : ∀ᶠ i in (U : Filter I),
        Entity.kpair (Entity.ofRaw (a i)) (Entity.ofRaw (rb i)) ∈ Entity.ofRaw (f i) :=
      hev.mono fun i hi ↦ by
        have hex := Entity.mem_relDom_iff.1 hi
        have hfle : (Entity.ofRaw (f i)).rank ≤ N := mem_vStage_iff_rank_le.1 ⟨f i, rfl⟩
        have hlt := Entity.rank_lt_of_kpair_mem hex.choose_spec
        have hb_eq : Entity.ofRaw (rb i) = hex.choose := by
          simp only [rb, hex, ↓reduceDIte]
          exact Entity.ofRaw_toRawAt (mem_vStage_iff_rank_le.2 (by omega))
        rw [hb_eq]
        exact hex.choose_spec
    exact ⟨collapseStage U (N + 1) (rb : Germ (U : Filter I) (RawStage X (N + 1))),
      (kpair_collapseStage_mem_iff U a rb f).2 hrb⟩

/-- Function-application part of Łoś's Theorem (Goldblatt §13.8, p. 169). -/
theorem collapseStage_eq_funcApp_of_eventually {I X : Type*} (U : Ultrafilter I)
    {m N M : ℕ} (a : I → RawStage X m) (f : I → RawStage X N) (rb : I → RawStage X M)
    (hf : (collapseStage U N (f : Germ (U : Filter I) (RawStage X N))).IsFuncEntity)
    (hadom : collapseStage U m (a : Germ (U : Filter I) (RawStage X m)) ∈
      Entity.relDom (collapseStage U N (f : Germ (U : Filter I) (RawStage X N))))
    (hrb : ∀ᶠ i in (U : Filter I),
      Entity.ofRaw (rb i) = Entity.funcApp (Entity.ofRaw (f i)) (Entity.ofRaw (a i))) :
    Entity.funcApp
      (collapseStage U N (f : Germ (U : Filter I) (RawStage X N)))
      (collapseStage U m (a : Germ (U : Filter I) (RawStage X m))) =
      collapseStage U M (rb : Germ (U : Filter I) (RawStage X M)) := by
  have hfev := (collapseStage_isFuncEntity_iff U f).1 hf
  have haev := (collapseStage_mem_relDom_iff U a f).1 hadom
  have hp_mem : Entity.kpair
      (collapseStage U m (a : Germ (U : Filter I) (RawStage X m)))
      (collapseStage U M (rb : Germ (U : Filter I) (RawStage X M))) ∈
      collapseStage U N (f : Germ (U : Filter I) (RawStage X N)) := by
    refine (kpair_collapseStage_mem_iff U a rb f).2 ?_
    exact ((hfev.and haev).and hrb).mono fun i ⟨⟨_, hai⟩, hrbi⟩ ↦ by
      rw [hrbi]
      exact Entity.kpair_funcApp_mem hai
  exact ((Entity.kpair_mem_iff_funcApp_eq hf).1 hp_mem).2

/-- Staged coordinatewise variable environments `ℕ → (m : ℕ) × (I → RawStage X m)` for Łoś's
Theorem on `ℒ_𝕌` (Goldblatt §13.8, p. 168). -/
abbrev StagedEnv (I X : Type*) := ℕ → (m : ℕ) × (I → RawStage X m)

/-- Coordinatewise `Entity X` environment at `i : I` induced by `senv : StagedEnv I X`
(Goldblatt §13.8, p. 168). -/
def stagedEnvAt {I X : Type*} (senv : StagedEnv I X) (i : I) : ℕ → Entity X :=
  fun v ↦ Entity.ofRaw ((senv v).2 i)

/-- Collapsed `Entity (Germ U X)` environment induced by `senv : StagedEnv I X`
(Goldblatt §13.8, p. 168). -/
def stagedEnvCollapse {I X : Type*} (U : Ultrafilter I) (senv : StagedEnv I X) :
    ℕ → Entity (Germ (U : Filter I) X) :=
  fun v ↦ collapseStage U (senv v).1 ((senv v).2 : Germ (U : Filter I) (RawStage X (senv v).1))

/-- `stagedEnvAt` commutes with `Function.update` (Goldblatt §13.8, p. 168). -/
@[simp]
theorem stagedEnvAt_update {I X : Type*} (senv : StagedEnv I X) (v : ℕ)
    (w : (m : ℕ) × (I → RawStage X m)) (i : I) :
    stagedEnvAt (Function.update senv v w) i =
      Function.update (stagedEnvAt senv i) v (Entity.ofRaw (w.2 i)) := by
  ext u
  by_cases huv : u = v
  · subst huv
    change Entity.ofRaw ((Function.update senv u w u).2 i) =
      Function.update (stagedEnvAt senv i) u (Entity.ofRaw (w.2 i)) u
    rw [Function.update_self, Function.update_self]
  · change Entity.ofRaw ((Function.update senv v w u).2 i) =
      Function.update (stagedEnvAt senv i) v (Entity.ofRaw (w.2 i)) u
    rw [Function.update_of_ne huv, Function.update_of_ne huv]
    rfl

/-- `stagedEnvCollapse` commutes with `Function.update` (Goldblatt §13.8, p. 168). -/
@[simp]
theorem stagedEnvCollapse_update {I X : Type*} (U : Ultrafilter I) (senv : StagedEnv I X)
    (v : ℕ) (w : (m : ℕ) × (I → RawStage X m)) :
    stagedEnvCollapse U (Function.update senv v w) =
      Function.update (stagedEnvCollapse U senv) v
        (collapseStage U w.1 (w.2 : Germ (U : Filter I) (RawStage X w.1))) := by
  ext u
  by_cases huv : u = v
  · subst huv
    change collapseStage U (Function.update senv u w u).1
        ((Function.update senv u w u).2 : Germ (U : Filter I) (RawStage X (Function.update senv u w u).1)) =
      Function.update (stagedEnvCollapse U senv) u
        (collapseStage U w.1 (w.2 : Germ (U : Filter I) (RawStage X w.1))) u
    rw [Function.update_self, Function.update_self]
  · change collapseStage U (Function.update senv v w u).1
        ((Function.update senv v w u).2 : Germ (U : Filter I) (RawStage X (Function.update senv v w u).1)) =
      Function.update (stagedEnvCollapse U senv) v
        (collapseStage U w.1 (w.2 : Germ (U : Filter I) (RawStage X w.1))) u
    rw [Function.update_of_ne huv, Function.update_of_ne huv]
    rfl

/-- **Term Łoś Theorem** for `ℒ_𝕌`: for every term `t : UTerm X` and staged environment `senv`,
either `*t` denotes `collapseStage U N ↑r` and `t` eventually denotes `ofRaw (r i)`, or both `*t`
and (eventually) `t` are undefined (`none`) (Goldblatt §13.8, p. 168). -/
theorem los_uterm {I X : Type*} (U : Ultrafilter I) (senv : StagedEnv I X) :
    ∀ t : UTerm X,
      (∃ (N : ℕ) (r : I → RawStage X N),
        evalUTerm (stagedEnvCollapse U senv) (starTerm (ultrapowerStar U) t) =
          some (collapseStage U N (r : Germ (U : Filter I) (RawStage X N))) ∧
        (∀ᶠ i in (U : Filter I),
          evalUTerm (stagedEnvAt senv i) t = some (Entity.ofRaw (r i)))) ∨
      (evalUTerm (stagedEnvCollapse U senv) (starTerm (ultrapowerStar U) t) = none ∧
        (∀ᶠ i in (U : Filter I), evalUTerm (stagedEnvAt senv i) t = none))
  | .var v =>
      Or.inl ⟨(senv v).1, (senv v).2, rfl, Filter.Eventually.of_forall fun _ ↦ rfl⟩
  | .const c =>
      Quotient.inductionOn c fun ⟨m, rc⟩ ↦
        Or.inl ⟨m, fun _ ↦ rc, rfl, Filter.Eventually.of_forall fun _ ↦ rfl⟩
  | @UTerm.tuple _ k hm args => by
      by_cases hall : ∀ j,
          ∃ (N : ℕ) (r : I → RawStage X N),
            evalUTerm (stagedEnvCollapse U senv) (starTerm (ultrapowerStar U) (args j)) =
              some (collapseStage U N (r : Germ (U : Filter I) (RawStage X N))) ∧
            (∀ᶠ i in (U : Filter I),
              evalUTerm (stagedEnvAt senv i) (args j) = some (Entity.ofRaw (r i)))
      · let w : Fin k → (m : ℕ) × (I → RawStage X m) := fun j ↦
          ⟨(hall j).choose, (hall j).choose_spec.choose⟩
        have hw_col : ∀ j,
            evalUTerm (stagedEnvCollapse U senv) (starTerm (ultrapowerStar U) (args j)) =
              some (collapseStage U (w j).1 ((w j).2 : Germ (U : Filter I) (RawStage X (w j).1))) :=
          fun j ↦ (hall j).choose_spec.choose_spec.1
        have hw_ev : ∀ j, ∀ᶠ i in (U : Filter I),
            evalUTerm (stagedEnvAt senv i) (args j) = some (Entity.ofRaw ((w j).2 i)) :=
          fun j ↦ (hall j).choose_spec.choose_spec.2
        have hw_ev_all : ∀ᶠ i in (U : Filter I),
            ∀ j, evalUTerm (stagedEnvAt senv i) (args j) = some (Entity.ofRaw ((w j).2 i)) :=
          Filter.eventually_all.2 hw_ev
        let M : ℕ := Finset.univ.sup fun j ↦ (w j).1
        let K : ℕ := M + 2 * k + 1
        let rt : I → RawStage X (K + 1) := fun i ↦
          (Entity.ktuple fun j ↦ Entity.ofRaw ((w j).2 i)).toRawAt K
        have hrt : ∀ i : I, Entity.ofRaw (rt i) =
            Entity.ktuple fun j ↦ Entity.ofRaw ((w j).2 i) := fun i ↦
          Entity.ofRaw_toRawAt (vStage_mono (Nat.le_succ K)
            (Entity.ktuple_mem_vStage fun j ↦
              vStage_mono (Finset.le_sup (f := fun q ↦ (w q).1) (Finset.mem_univ j))
                ⟨(w j).2 i, rfl⟩))
        refine Or.inl ⟨K + 1, rt, ?_, ?_⟩
        · rw [starTerm.eq_3, evalUTerm.eq_3]
          have hsome : ∀ j, (evalUTerm (stagedEnvCollapse U senv)
              (starTerm (ultrapowerStar U) (args j))).isSome := fun j ↦ by simp [hw_col j]
          split_ifs
          apply congrArg some
          rw [collapseStage_eq_ktuple_of_eventually U w rt (Filter.Eventually.of_forall hrt)]
          apply congrArg Entity.ktuple
          ext j
          exact Option.some.inj (by rw [Option.some_get, hw_col j])
        · exact hw_ev_all.mono fun i hi ↦ by
            rw [evalUTerm.eq_3]
            have hsi : ∀ j, (evalUTerm (stagedEnvAt senv i) (args j)).isSome :=
              fun j ↦ by simp [hi j]
            split_ifs
            apply congrArg some
            rw [hrt i]
            apply congrArg Entity.ktuple
            ext j
            exact Option.some.inj (by rw [Option.some_get, hi j])
      · obtain ⟨j₀, hj₀⟩ := not_forall.1 hall
        rcases los_uterm U senv (args j₀) with hex | ⟨hnone_col, hnone_ev⟩
        · exact (hj₀ hex).elim
        · refine Or.inr ⟨?_, ?_⟩
          · rw [starTerm.eq_3, evalUTerm.eq_3]
            have hns : ¬ ∀ j, (evalUTerm (stagedEnvCollapse U senv)
                (starTerm (ultrapowerStar U) (args j))).isSome := by
              intro hs
              have := hs j₀
              simp [hnone_col] at this
            split_ifs
            rfl
          · exact hnone_ev.mono fun i hi ↦ by
              rw [evalUTerm.eq_3]
              have hns : ¬ ∀ j, (evalUTerm (stagedEnvAt senv i) (args j)).isSome := by
                intro hs
                have := hs j₀
                simp [hi] at this
              split_ifs
              rfl
  | .app fn arg => by
      rcases los_uterm U senv fn with ⟨Nf, rf, hfn_col, hfn_ev⟩ | ⟨hfn_col, hfn_ev⟩
      · rcases los_uterm U senv arg with ⟨Na, ra, harg_col, harg_ev⟩ | ⟨harg_col, harg_ev⟩
        · by_cases hdom :
              (collapseStage U Nf (rf : Germ (U : Filter I) (RawStage X Nf))).IsFuncEntity ∧
              collapseStage U Na (ra : Germ (U : Filter I) (RawStage X Na)) ∈
                Entity.relDom (collapseStage U Nf (rf : Germ (U : Filter I) (RawStage X Nf)))
          · have hfev := (collapseStage_isFuncEntity_iff U rf).1 hdom.1
            have haev := (collapseStage_mem_relDom_iff U ra rf).1 hdom.2
            let rb : I → RawStage X (Nf + 1) := fun i ↦
              (Entity.funcApp (Entity.ofRaw (rf i)) (Entity.ofRaw (ra i))).toRawAt Nf
            have hrb : ∀ᶠ i in (U : Filter I),
                Entity.ofRaw (rb i) = Entity.funcApp (Entity.ofRaw (rf i)) (Entity.ofRaw (ra i)) :=
              (hfev.and haev).mono fun i ⟨_, hai⟩ ↦ by
                have hp := Entity.kpair_funcApp_mem hai
                have hlt := Entity.rank_lt_of_kpair_mem hp
                have hfle : (Entity.ofRaw (rf i)).rank ≤ Nf := mem_vStage_iff_rank_le.1 ⟨rf i, rfl⟩
                exact Entity.ofRaw_toRawAt (mem_vStage_iff_rank_le.2 (by omega))
            refine Or.inl ⟨Nf + 1, rb, ?_, ?_⟩
            · rw [starTerm.eq_4, evalUTerm.eq_4, hfn_col, harg_col]
              dsimp only
              split_ifs with hd
              · exact congrArg some (collapseStage_eq_funcApp_of_eventually U ra rf rb
                  hdom.1 hdom.2 hrb)
              · exact absurd hdom hd
            · exact ((((hfn_ev.and harg_ev).and hfev).and haev).and hrb).mono
                fun i ⟨⟨⟨⟨hfni, hargi⟩, hfi⟩, hai⟩, hrbi⟩ ↦ by
                  rw [evalUTerm.eq_4, hfni, hargi]
                  dsimp only
                  have hdi : (Entity.ofRaw (rf i)).IsFuncEntity ∧
                      Entity.ofRaw (ra i) ∈ Entity.relDom (Entity.ofRaw (rf i)) := ⟨hfi, hai⟩
                  split_ifs
                  exact congrArg some hrbi.symm
          · have hndom_ev : ∀ᶠ i in (U : Filter I),
                ¬ ((Entity.ofRaw (rf i)).IsFuncEntity ∧
                    Entity.ofRaw (ra i) ∈ Entity.relDom (Entity.ofRaw (rf i))) := by
              rw [Ultrafilter.eventually_not (f := U), Filter.eventually_and,
                ← collapseStage_isFuncEntity_iff U rf, ← collapseStage_mem_relDom_iff U ra rf]
              exact hdom
            refine Or.inr ⟨?_, ?_⟩
            · rw [starTerm.eq_4, evalUTerm.eq_4, hfn_col, harg_col]
              dsimp only
              split_ifs with hd
              · exact absurd hd hdom
              · rfl
            · exact ((hfn_ev.and harg_ev).and hndom_ev).mono fun i ⟨⟨hfni, hargi⟩, hndi⟩ ↦ by
                rw [evalUTerm.eq_4, hfni, hargi]
                dsimp only
                split_ifs
                rfl
        · refine Or.inr ⟨?_, ?_⟩
          · rw [starTerm.eq_4, evalUTerm.eq_4, hfn_col, harg_col]
          · exact (hfn_ev.and harg_ev).mono fun i ⟨hfni, hargi⟩ ↦ by
              rw [evalUTerm.eq_4, hfni, hargi]
      · refine Or.inr ⟨?_, ?_⟩
        · rw [starTerm.eq_4, evalUTerm.eq_4, hfn_col]
        · exact hfn_ev.mono fun i hfni ↦ by rw [evalUTerm.eq_4, hfni]

/-- **Łoś's Theorem for Bounded-Quantifier (`Δ₀`) Formulae** in `ℒ_𝕌`:
`Holds (stagedEnvCollapse U senv) (*φ) ↔ ∀ᶠ i in U, Holds (stagedEnvAt senv i) φ`
(Goldblatt §13.8, p. 168). -/
theorem los_uformula {I X : Type*} (U : Ultrafilter I) :
    ∀ (φ : UFormula X) (senv : StagedEnv I X),
      Holds (stagedEnvCollapse U senv) (starFormula (ultrapowerStar U) φ) ↔
        ∀ᶠ i in (U : Filter I), Holds (stagedEnvAt senv i) φ
  | .eq t₁ t₂, senv => by
      simp only [starFormula, Holds]
      rcases los_uterm U senv t₁ with ⟨N₁, r₁, ht₁_col, ht₁_ev⟩ | ⟨ht₁_col, ht₁_ev⟩
      · rcases los_uterm U senv t₂ with ⟨N₂, r₂, ht₂_col, ht₂_ev⟩ | ⟨ht₂_col, ht₂_ev⟩
        · rw [ht₁_col, ht₂_col]
          constructor
          · rintro ⟨z, hz₁, hz₂⟩
            have heq := (Option.some.inj hz₁).trans (Option.some.inj hz₂).symm
            have hev := (collapseStage_coe_eq_iff U r₁ r₂).1 heq
            exact ((ht₁_ev.and ht₂_ev).and hev).mono fun i ⟨⟨h1i, h2i⟩, hi⟩ ↦
              ⟨Entity.ofRaw (r₁ i), h1i, h2i.trans (congrArg some hi.symm)⟩
          · intro hev
            have heq : ∀ᶠ i in (U : Filter I), Entity.ofRaw (r₁ i) = Entity.ofRaw (r₂ i) :=
              ((hev.and ht₁_ev).and ht₂_ev).mono fun i ⟨⟨⟨z, hz1, hz2⟩, h1i⟩, h2i⟩ ↦
                (Option.some.inj (h1i.symm.trans hz1)).trans
                  (Option.some.inj (h2i.symm.trans hz2)).symm
            exact ⟨collapseStage U N₁ (r₁ : Germ (U : Filter I) (RawStage X N₁)), rfl,
              congrArg some ((collapseStage_coe_eq_iff U r₁ r₂).2 heq).symm⟩
        · rw [ht₁_col, ht₂_col]
          constructor
          · rintro ⟨_, _, h⟩; simp at h
          · intro hev
            exact False.elim (Filter.eventually_const.1
              ((hev.and ht₂_ev).mono fun _ ⟨⟨_, _, hz2⟩, h2⟩ ↦ by
                rw [h2] at hz2; simp at hz2))
      · rw [ht₁_col]
        constructor
        · rintro ⟨_, h, _⟩; simp at h
        · intro hev
          exact False.elim (Filter.eventually_const.1
            ((hev.and ht₁_ev).mono fun _ ⟨⟨_, hz1, _⟩, h1⟩ ↦ by
              rw [h1] at hz1; simp at hz1))
  | .mem t₁ t₂, senv => by
      simp only [starFormula, Holds]
      rcases los_uterm U senv t₁ with ⟨N₁, r₁, ht₁_col, ht₁_ev⟩ | ⟨ht₁_col, ht₁_ev⟩
      · rcases los_uterm U senv t₂ with ⟨N₂, r₂, ht₂_col, ht₂_ev⟩ | ⟨ht₂_col, ht₂_ev⟩
        · rw [ht₁_col, ht₂_col]
          constructor
          · rintro ⟨a, B, ha, hB, hm⟩
            obtain rfl := Option.some.inj ha
            obtain rfl := Option.some.inj hB
            have hev := (collapseStage_coe_mem_iff U r₁ r₂).1 hm
            exact ((ht₁_ev.and ht₂_ev).and hev).mono fun i ⟨⟨h1i, h2i⟩, hi⟩ ↦
              ⟨Entity.ofRaw (r₁ i), Entity.ofRaw (r₂ i), h1i, h2i, hi⟩
          · intro hev
            have hmem : ∀ᶠ i in (U : Filter I), Entity.ofRaw (r₁ i) ∈ Entity.ofRaw (r₂ i) :=
              ((hev.and ht₁_ev).and ht₂_ev).mono fun i ⟨⟨⟨a, B, ha, hB, hm⟩, h1i⟩, h2i⟩ ↦ by
                have ha' := Option.some.inj (h1i.symm.trans ha)
                have hB' := Option.some.inj (h2i.symm.trans hB)
                rwa [ha', hB']
            exact ⟨_, _, rfl, rfl, (collapseStage_coe_mem_iff U r₁ r₂).2 hmem⟩
        · rw [ht₁_col, ht₂_col]
          constructor
          · rintro ⟨_, _, _, h, _⟩; simp at h
          · intro hev
            exact False.elim (Filter.eventually_const.1
              ((hev.and ht₂_ev).mono fun _ ⟨⟨_, _, _, hz2, _⟩, h2⟩ ↦ by
                rw [h2] at hz2; simp at hz2))
      · rw [ht₁_col]
        constructor
        · rintro ⟨_, _, h, _, _⟩; simp at h
        · intro hev
          exact False.elim (Filter.eventually_const.1
            ((hev.and ht₁_ev).mono fun _ ⟨⟨_, _, hz1, _, _⟩, h1⟩ ↦ by
              rw [h1] at hz1; simp at hz1))
  | .conj φ ψ, senv => by
      simp only [starFormula, Holds, los_uformula U φ senv, los_uformula U ψ senv,
        Filter.eventually_and]
  | .disj φ ψ, senv => by
      simp only [starFormula, Holds, los_uformula U φ senv, los_uformula U ψ senv]
      exact (Ultrafilter.eventually_or (f := U)).symm
  | .neg φ, senv => by
      simp only [starFormula, Holds, los_uformula U φ senv]
      exact (Ultrafilter.eventually_not (f := U)).symm
  | .imp φ ψ, senv => by
      simp only [starFormula, Holds, los_uformula U φ senv, los_uformula U ψ senv]
      exact (Ultrafilter.eventually_imp (f := U)).symm
  | .iff φ ψ, senv => by
      simp only [starFormula, Holds, los_uformula U φ senv, los_uformula U ψ senv]
      constructor
      · intro h
        have h1 : ∀ᶠ i in (U : Filter I),
            Holds (stagedEnvAt senv i) φ → Holds (stagedEnvAt senv i) ψ :=
          (Ultrafilter.eventually_imp (f := U)).2 h.mp
        have h2 : ∀ᶠ i in (U : Filter I),
            Holds (stagedEnvAt senv i) ψ → Holds (stagedEnvAt senv i) φ :=
          (Ultrafilter.eventually_imp (f := U)).2 h.mpr
        exact (h1.and h2).mono fun _ ⟨h1i, h2i⟩ ↦ ⟨h1i, h2i⟩
      · intro hev
        exact ⟨(Ultrafilter.eventually_imp (f := U)).1 (hev.mono fun _ h ↦ h.mp),
          (Ultrafilter.eventually_imp (f := U)).1 (hev.mono fun _ h ↦ h.mpr)⟩
  | .existsIn v dom body, senv => by
      simp only [starFormula, Holds]
      rcases los_uterm U senv dom with ⟨N, rdom, hdom_col, hdom_ev⟩ | ⟨hdom_col, hdom_ev⟩
      · rw [hdom_col]
        constructor
        · rintro ⟨A, hA, a, haA, hbody⟩
          obtain rfl := Option.some.inj hA
          obtain ⟨ma, ra, _, rfl⟩ := exists_collapseStage_of_mem U haA
          have ha_ev := (collapseStage_coe_mem_iff U ra rdom).1 haA
          rw [← stagedEnvCollapse_update U senv v ⟨ma, ra⟩,
            los_uformula U body (Function.update senv v ⟨ma, ra⟩)] at hbody
          exact ((hdom_ev.and ha_ev).and hbody).mono fun i ⟨⟨hdi, hai⟩, hbi⟩ ↦ by
            rw [stagedEnvAt_update] at hbi
            exact ⟨Entity.ofRaw (rdom i), hdi, Entity.ofRaw (ra i), hai, hbi⟩
        · intro hev
          have hex : ∀ᶠ i in (U : Filter I),
              ∃ a ∈ Entity.ofRaw (rdom i),
                Holds (Function.update (stagedEnvAt senv i) v a) body :=
            (hev.and hdom_ev).mono fun i ⟨⟨A, hA, a, haA, hbi⟩, hdi⟩ ↦ by
              obtain rfl := Option.some.inj (hdi.symm.trans hA)
              exact ⟨a, haA, hbi⟩
          let ra : I → RawStage X (N + 1) := fun i ↦
            if hi : ∃ a ∈ Entity.ofRaw (rdom i),
                Holds (Function.update (stagedEnvAt senv i) v a) body then
              hi.choose.toRawAt N
            else
              Sum.inr ∅
          have hra_spec : ∀ᶠ i in (U : Filter I),
              Entity.ofRaw (ra i) ∈ Entity.ofRaw (rdom i) ∧
              Holds (stagedEnvAt (Function.update senv v ⟨N + 1, ra⟩) i) body :=
            hex.mono fun i hi ↦ by
              have ha_mem : hi.choose ∈ Entity.ofRaw (rdom i) := hi.choose_spec.1
              have hle : (Entity.ofRaw (rdom i)).rank ≤ N :=
                mem_vStage_iff_rank_le.1 ⟨rdom i, rfl⟩
              have hlt := Entity.rank_lt_of_mem ha_mem
              have ha_eq : Entity.ofRaw (ra i) = hi.choose := by
                simp only [ra, hi, ↓reduceDIte]
                exact Entity.ofRaw_toRawAt (mem_vStage_iff_rank_le.2 (by omega))
              rw [stagedEnvAt_update, ha_eq]
              exact hi.choose_spec
          refine ⟨_, rfl,
            collapseStage U (N + 1) (ra : Germ (U : Filter I) (RawStage X (N + 1))),
            (collapseStage_coe_mem_iff U ra rdom).2 (hra_spec.mono fun _ h ↦ h.1), ?_⟩
          rw [← stagedEnvCollapse_update U senv v ⟨N + 1, ra⟩,
            los_uformula U body (Function.update senv v ⟨N + 1, ra⟩)]
          exact hra_spec.mono fun _ h ↦ h.2
      · rw [hdom_col]
        constructor
        · rintro ⟨_, h, _⟩; simp at h
        · intro hev
          exact False.elim (Filter.eventually_const.1
            ((hev.and hdom_ev).mono fun _ ⟨⟨_, hz, _⟩, hd⟩ ↦ by
              rw [hd] at hz; simp at hz))
  | .forallIn v dom body, senv => by
      simp only [starFormula, Holds]
      rcases los_uterm U senv dom with ⟨N, rdom, hdom_col, hdom_ev⟩ | ⟨hdom_col, hdom_ev⟩
      · rw [hdom_col]
        constructor
        · rintro ⟨A, hA, hall⟩
          obtain rfl := Option.some.inj hA
          by_contra hnot
          have hnot' : ∀ᶠ i in (U : Filter I), ¬ Holds (stagedEnvAt senv i) (.forallIn v dom body) :=
            (Ultrafilter.eventually_not (f := U)).2 hnot
          have hex : ∀ᶠ i in (U : Filter I),
              ∃ a ∈ Entity.ofRaw (rdom i),
                ¬ Holds (Function.update (stagedEnvAt senv i) v a) body :=
            (hdom_ev.and hnot').mono fun i ⟨hdi, hni⟩ ↦ by
              have hnall : ¬ ∀ a ∈ Entity.ofRaw (rdom i),
                  Holds (Function.update (stagedEnvAt senv i) v a) body :=
                fun h ↦ hni ⟨Entity.ofRaw (rdom i), hdi, h⟩
              push Not at hnall
              exact hnall
          let ra : I → RawStage X (N + 1) := fun i ↦
            if hi : ∃ a ∈ Entity.ofRaw (rdom i),
                ¬ Holds (Function.update (stagedEnvAt senv i) v a) body then
              hi.choose.toRawAt N
            else
              Sum.inr ∅
          have hra_spec : ∀ᶠ i in (U : Filter I),
              Entity.ofRaw (ra i) ∈ Entity.ofRaw (rdom i) ∧
              ¬ Holds (stagedEnvAt (Function.update senv v ⟨N + 1, ra⟩) i) body :=
            hex.mono fun i hi ↦ by
              have ha_mem : hi.choose ∈ Entity.ofRaw (rdom i) := hi.choose_spec.1
              have hle : (Entity.ofRaw (rdom i)).rank ≤ N :=
                mem_vStage_iff_rank_le.1 ⟨rdom i, rfl⟩
              have hlt := Entity.rank_lt_of_mem ha_mem
              have ha_eq : Entity.ofRaw (ra i) = hi.choose := by
                simp only [ra, hi, ↓reduceDIte]
                exact Entity.ofRaw_toRawAt (mem_vStage_iff_rank_le.2 (by omega))
              rw [stagedEnvAt_update, ha_eq]
              exact hi.choose_spec
          have ha_col : collapseStage U (N + 1) (ra : Germ (U : Filter I) (RawStage X (N + 1))) ∈
              collapseStage U N (rdom : Germ (U : Filter I) (RawStage X N)) :=
            (collapseStage_coe_mem_iff U ra rdom).2 (hra_spec.mono fun _ h ↦ h.1)
          have hhold_col := hall _ ha_col
          rw [← stagedEnvCollapse_update U senv v ⟨N + 1, ra⟩,
            los_uformula U body (Function.update senv v ⟨N + 1, ra⟩)] at hhold_col
          exact Filter.eventually_const.1
            ((hra_spec.and hhold_col).mono fun _ ⟨⟨_, hnb⟩, hb⟩ ↦ hnb hb)
        · intro hev
          refine ⟨_, rfl, fun a ha ↦ ?_⟩
          obtain ⟨ma, ra, _, rfl⟩ := exists_collapseStage_of_mem U ha
          have ha_ev := (collapseStage_coe_mem_iff U ra rdom).1 ha
          rw [← stagedEnvCollapse_update U senv v ⟨ma, ra⟩,
            los_uformula U body (Function.update senv v ⟨ma, ra⟩)]
          exact ((hev.and hdom_ev).and ha_ev).mono fun i ⟨⟨⟨A, hA, hall⟩, hdi⟩, hai⟩ ↦ by
            obtain rfl := Option.some.inj (hdi.symm.trans hA)
            rw [stagedEnvAt_update]
            exact hall (Entity.ofRaw (ra i)) hai
      · rw [hdom_col]
        constructor
        · rintro ⟨_, h, _⟩; simp at h
        · intro hev
          exact False.elim (Filter.eventually_const.1
            ((hev.and hdom_ev).mono fun _ ⟨⟨_, hz, _⟩, hd⟩ ↦ by
              rw [hd] at hz; simp at hz))

/-- Goldblatt §13.8 (p. 168): Concrete **Ultrapower Superstructure Framework**
`ultrapowerFramework U X : Framework X (Germ U X)` for any index type `I`, ultrafilter
`U : Ultrafilter I`, and base set `X`, proved completely from Łoś's Theorem (`los_uformula`)
without axioms. -/
def ultrapowerFramework {I : Type*} (U : Ultrafilter I) (X : Type*) :
    Framework X (Germ (U : Filter I) X) where
  atomMap := fun x ↦ (x : Germ (U : Filter I) X)
  star := ultrapowerStar U
  star_atom := ultrapowerStar_atom U
  star_empty := ultrapowerStar_empty U
  transfer := fun φ _ ↦ by
    let senv₀ : StagedEnv I X := fun _ ↦ ⟨1, fun _ ↦ Sum.inr ∅⟩
    have hat : ∀ i : I, stagedEnvAt senv₀ i = fun _ ↦ (∅ : Entity X) := fun _ ↦ rfl
    have hcol : stagedEnvCollapse U senv₀ =
        fun _ ↦ (∅ : Entity (Germ (U : Filter I) X)) := by
      ext v
      exact ultrapowerStar_empty U
    have hlos := los_uformula U φ senv₀
    rw [hcol] at hlos
    simp only [hat] at hlos
    rw [SentenceHolds, SentenceHolds, hlos, Filter.eventually_const]

/-- Goldblatt §13.8 (p. 168): The **Hyperreal Superstructure Framework**
`hyperrealFramework : Framework ℝ ℝ*` over `hyperfilter ℕ`, uniting the ultrapower construction of
`ℝ*` (Chapters 3–12) with the universe framework of Chapter 13. -/
def hyperrealFramework : Framework ℝ ℝ* :=
  ultrapowerFramework (hyperfilter ℕ) ℝ

/-- Exact characterization of internal entities in `ultrapowerFramework U X`: an entity
`y : Entity (Germ U X)` belongs to `*A` for some `A : Entity X` **if and only if** `y` is in the
range of `collapseStage U`! (Goldblatt §13.8 & §13.10, pp. 168, 173.) -/
theorem exists_mem_ultrapowerStar_iff_exists_collapseStage {I X : Type*} (U : Ultrafilter I)
    (y : Entity (Germ (U : Filter I) X)) :
    (∃ A : Entity X, y ∈ (ultrapowerFramework U X).star A) ↔
      ∃ (n : ℕ) (g : I → RawStage X n),
        y = collapseStage U n (g : Germ (U : Filter I) (RawStage X n)) := by
  constructor
  · rintro ⟨A, hy⟩
    refine Quotient.inductionOn A (fun ⟨m, r⟩ hy ↦ ?_) hy
    obtain ⟨n, g, _, rfl⟩ := exists_collapseStage_of_mem U hy
    exact ⟨n, g, rfl⟩
  · rintro ⟨n, g, rfl⟩
    let uRaw : RawStage X (n + 1) := Sum.inr Set.univ
    refine ⟨Entity.ofRaw uRaw, ?_⟩
    let uStage : I → RawStage X (n + 1) := fun _ ↦ uRaw
    change collapseStage U n (g : Germ (U : Filter I) (RawStage X n)) ∈
      collapseStage U (n + 1) (uStage : Germ (U : Filter I) (RawStage X (n + 1)))
    exact (collapseStage_coe_mem_iff U g uStage).2
      (Filter.Eventually.of_forall fun i ↦ Entity.mem_ofRaw_inr.2 ⟨g i, trivial, rfl⟩)

/-! ## §13.9 Standard Entities, External Images `im A`, and `*Int` -/

/-- Goldblatt §13.9 (p. 170): An entity `b : Entity Y` in `𝕌'` is **standard** if `b = *a` for some
`a : Entity X` in `𝕌`. -/
def Framework.IsStandard {X Y : Type*} (F : Framework X Y) (b : Entity Y) : Prop :=
  ∃ a : Entity X, b = F.star a

/-- Goldblatt §13.9 (p. 170): An entity `b : Entity Y` in `𝕌'` is **nonstandard** if it is not of
the form `*a` for any `a : Entity X`. -/
def Framework.IsNonstandard {X Y : Type*} (F : Framework X Y) (b : Entity Y) : Prop :=
  ¬ F.IsStandard b

/-- Every entity `F.star a` is standard (Goldblatt §13.9, p. 170). -/
@[simp]
theorem Framework.isStandard_star {X Y : Type*} (F : Framework X Y) (a : Entity X) :
    F.IsStandard (F.star a) :=
  ⟨a, rfl⟩

/-- Every embedded individual `Entity.atom (F.atomMap x)` of `X` is standard, since
`Entity.atom (F.atomMap x) = F.star (Entity.atom x)` (Goldblatt §13.9, p. 170). -/
@[simp]
theorem Framework.isStandard_atom_atomMap {X Y : Type*} (F : Framework X Y) (x : X) :
    F.IsStandard (Entity.atom (F.atomMap x)) :=
  ⟨Entity.atom x, (F.star_atom x).symm⟩

/-- `∅ : Entity Y` is standard (`∅ = F.star ∅`; Goldblatt §13.8–13.9, pp. 168, 170). -/
@[simp]
theorem Framework.isStandard_empty {X Y : Type*} (F : Framework X Y) :
    F.IsStandard (∅ : Entity Y) :=
  ⟨∅, F.star_empty.symm⟩

/-- Goldblatt §13.9 (p. 172): The **image** (or **external image** when `A` is infinite)
`im A = {*a : a ∈ A}` of an entity `A : Entity X` under `F.star`. -/
def Framework.sigmaImage {X Y : Type*} (F : Framework X Y) (A : Entity X) : Set (Entity Y) :=
  F.star '' A.extSet

/-- Membership in `F.sigmaImage A` (`b ∈ im A ↔ ∃ a ∈ A, F.star a = b`; Goldblatt §13.9, p. 172). -/
@[simp]
theorem Framework.mem_sigmaImage_def {X Y : Type*} (F : Framework X Y) {A : Entity X}
    {b : Entity Y} :
    b ∈ F.sigmaImage A ↔ ∃ a ∈ A, F.star a = b := Iff.rfl

/-- `im A ⊆ *A`: every element of `F.sigmaImage A` belongs to `F.star A`
(Goldblatt §13.9, p. 172). -/
theorem Framework.sigmaImage_subset_star {X Y : Type*} (F : Framework X Y) (A : Entity X) :
    F.sigmaImage A ⊆ (F.star A).extSet := by
  rintro _ ⟨a, ha, rfl⟩
  exact F.mem_star_iff.2 ha

/-- `a ↦ *a` restricts to a bijection between `A.extSet` and `F.sigmaImage A`
(Goldblatt §13.9, p. 172). -/
def Framework.sigmaImageEquiv {X Y : Type*} (F : Framework X Y) (A : Entity X) :
    A.extSet ≃ F.sigmaImage A :=
  Equiv.Set.image F.star A.extSet F.star_injective

/-- Goldblatt **Theorem 13.9.2** (p. 172): `im A` is the set of all standard members of `*A`:
`im A = {b ∈ 𝕌' : b ∈ *A ∧ b is standard}`. Hence `*A` and `im A` have the exact same standard
elements. -/
theorem Framework.mem_sigmaImage_iff {X Y : Type*} (F : Framework X Y) {A : Entity X}
    {b : Entity Y} :
    b ∈ F.sigmaImage A ↔ b ∈ F.star A ∧ F.IsStandard b := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨F.mem_star_iff.2 ha, F.isStandard_star a⟩
  · rintro ⟨hbA, a, rfl⟩
    exact ⟨a, F.mem_star_iff.1 hbA, rfl⟩

/-- Corollary of **Theorem 13.9.2** (Goldblatt §13.9, p. 172): the nonstandard members of `*A` are
precisely the members of `*A \ im A`. -/
theorem Framework.mem_star_sdiff_sigmaImage_iff {X Y : Type*} (F : Framework X Y) {A : Entity X}
    {b : Entity Y} :
    b ∈ (F.star A).extSet \ F.sigmaImage A ↔ b ∈ F.star A ∧ F.IsNonstandard b := by
  rw [Set.mem_sdiff, Entity.mem_extSet, F.mem_sigmaImage_iff, Framework.IsNonstandard]
  tauto

/-- When `A` is a finite set, `*A` equals `im A` (`(F.star A).extSet = F.sigmaImage A`), so `*A`
has no nonstandard elements (Goldblatt §13.9, p. 172). -/
theorem Framework.star_extSet_eq_sigmaImage_of_finite {X Y : Type*} (F : Framework X Y)
    {A : Entity X} (hAs : A.IsSet) (hAfin : A.extSet.Finite) :
    (F.star A).extSet = F.sigmaImage A := by
  ext b
  rw [Entity.mem_extSet, F.mem_star_iff_of_finite hAs hAfin, F.mem_sigmaImage_def]
  exact ⟨fun ⟨a, ha, h⟩ ↦ ⟨a, ha, h.symm⟩, fun ⟨a, ha, h⟩ ↦ ⟨a, ha, h.symm⟩⟩

/-- Goldblatt **Exercise 13.9.3** (p. 172): Standard sets are uniquely determined by their standard
members — if two standard sets `*A` and `*B` have the exact same standard members, then `*A = *B`
(and `A = B`). -/
theorem Framework.star_eq_of_forall_isStandard_mem_iff {X Y : Type*} (F : Framework X Y)
    {A B : Entity X} (hAs : A.IsSet) (hBs : B.IsSet)
    (hstd : ∀ b : Entity Y, F.IsStandard b → (b ∈ F.star A ↔ b ∈ F.star B)) :
    F.star A = F.star B := by
  have hAB : A = B := by
    refine Entity.set_ext hAs hBs fun x ↦ ?_
    rw [← F.mem_star_iff, ← F.mem_star_iff]
    exact hstd (F.star x) (F.isStandard_star x)
  rw [hAB]

/-- First coordinate extractor for Kuratowski pairs (`pairFirst (a, b) = a`; helper for standard
functions on Cartesian products). -/
def Entity.pairFirst {X : Type*} (p : Entity X) : Entity X :=
  if h : ∃ a b : Entity X, p = Entity.kpair a b then h.choose else ∅

/-- Second coordinate extractor for Kuratowski pairs (`pairSecond (a, b) = b`). -/
def Entity.pairSecond {X : Type*} (p : Entity X) : Entity X :=
  if h : ∃ a b : Entity X, p = Entity.kpair a b then h.choose_spec.choose else ∅

/-- `Entity.pairFirst (Entity.kpair a b) = a` (Goldblatt §13.3, p. 161). -/
@[simp]
theorem Entity.pairFirst_kpair {X : Type*} (a b : Entity X) :
    Entity.pairFirst (Entity.kpair a b) = a := by
  have h : ∃ x y : Entity X, Entity.kpair a b = Entity.kpair x y := ⟨a, b, rfl⟩
  simp only [Entity.pairFirst, h, ↓reduceDIte]
  exact (Entity.kpair_inj.1 h.choose_spec.choose_spec).1.symm

/-- `Entity.pairSecond (Entity.kpair a b) = b` (Goldblatt §13.3, p. 161). -/
@[simp]
theorem Entity.pairSecond_kpair {X : Type*} (a b : Entity X) :
    Entity.pairSecond (Entity.kpair a b) = b := by
  have h : ∃ x y : Entity X, Entity.kpair a b = Entity.kpair x y := ⟨a, b, rfl⟩
  simp only [Entity.pairSecond, h, ↓reduceDIte]
  exact (Entity.kpair_inj.1 h.choose_spec.choose_spec).2.symm

/-- Underlying individual `x : X` extracted from an atom `Entity.atom x` (defaulting to `d`). -/
def Entity.atomVal {X : Type*} (d : X) (e : Entity X) : X :=
  if h : e.IsAtom then h.choose else d

/-- `Entity.atomVal d (Entity.atom x) = x` (Goldblatt §13.6, p. 164). -/
@[simp]
theorem Entity.atomVal_atom {X : Type*} (d x : X) :
    Entity.atomVal d (Entity.atom x) = x := by
  have h : (Entity.atom x).IsAtom := ⟨x, rfl⟩
  simp only [Entity.atomVal, h, ↓reduceDIte]
  exact Entity.atom_inj.1 h.choose_spec.symm

/-- Canonical copy of `ℝ` (`𝕌_0(ℝ)`) inside `Entity ℝ` (Goldblatt §13.9, p. 171). -/
def realEntity : Entity ℝ := baseSet ℝ

/-- Nonnegative natural numbers `ℕ₀ = {0, 1, 2, …}` as a rank-`1` entity in `Entity ℝ`
(Goldblatt §13.9 & §13.17, pp. 171, 178). -/
def nat0Entity : Entity ℝ := mkAtomSet (Set.range (Nat.cast : ℕ → ℝ))

/-- Positive natural numbers `ℕ = {1, 2, 3, …}` as a rank-`1` entity in `Entity ℝ`, matching
Goldblatt's convention `{1, …, n} ⊆ ℕ` (Goldblatt §13.9 & §13.17, pp. 171, 178). -/
def posNatEntity : Entity ℝ := mkAtomSet {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = (n : ℝ)}

/-- Integers `ℤ` as a rank-`1` entity in `Entity ℝ` (Goldblatt §13.10, p. 173). -/
def intEntity : Entity ℝ := mkAtomSet (Set.range (Int.cast : ℤ → ℝ))

/-- Standard order relation `≤` on `ℝ` as an entity in `Entity ℝ` (Goldblatt §13.9, p. 171). -/
def realLeRel : Entity ℝ :=
  Entity.setOfBounded {p : Entity ℝ |
    ∃ x y : ℝ, x ≤ y ∧ p = Entity.kpair (Entity.atom x) (Entity.atom y)}

/-- Membership of an ordered pair of atoms in `realLeRel` (`(atom x, atom y) ∈ realLeRel ↔ x ≤ y`). -/
@[simp]
theorem kpair_atom_mem_realLeRel_iff {x y : ℝ} :
    Entity.kpair (Entity.atom x) (Entity.atom y) ∈ realLeRel ↔ x ≤ y := by
  have hbdd : IsBoundedRank {p : Entity ℝ |
      ∃ a b : ℝ, a ≤ b ∧ p = Entity.kpair (Entity.atom a) (Entity.atom b)} :=
    (Entity.isBoundedRank_prod realEntity realEntity).subset fun _ ⟨a, b, _, hp⟩ ↦
      ⟨Entity.atom a, mem_baseSet_iff.2 ⟨a, rfl⟩, Entity.atom b, mem_baseSet_iff.2 ⟨b, rfl⟩, hp⟩
  rw [realLeRel, Entity.mem_setOfBounded hbdd]
  constructor
  · rintro ⟨a, b, hab, heq⟩
    obtain ⟨ha, hb⟩ := Entity.kpair_inj.1 heq
    obtain rfl := Entity.atom_inj.1 ha
    obtain rfl := Entity.atom_inj.1 hb
    exact hab
  · exact fun h ↦ ⟨x, y, h, rfl⟩

/-- Standard strict order relation `<` on `ℝ` as an entity in `Entity ℝ` (Goldblatt §13.9, p. 171). -/
def realLtRel : Entity ℝ :=
  Entity.setOfBounded {p : Entity ℝ |
    ∃ x y : ℝ, x < y ∧ p = Entity.kpair (Entity.atom x) (Entity.atom y)}

/-- Membership of an ordered pair of atoms in `realLtRel` (`(atom x, atom y) ∈ realLtRel ↔ x < y`). -/
@[simp]
theorem kpair_atom_mem_realLtRel_iff {x y : ℝ} :
    Entity.kpair (Entity.atom x) (Entity.atom y) ∈ realLtRel ↔ x < y := by
  have hbdd : IsBoundedRank {p : Entity ℝ |
      ∃ a b : ℝ, a < b ∧ p = Entity.kpair (Entity.atom a) (Entity.atom b)} :=
    (Entity.isBoundedRank_prod realEntity realEntity).subset fun _ ⟨a, b, _, hp⟩ ↦
      ⟨Entity.atom a, mem_baseSet_iff.2 ⟨a, rfl⟩, Entity.atom b, mem_baseSet_iff.2 ⟨b, rfl⟩, hp⟩
  rw [realLtRel, Entity.mem_setOfBounded hbdd]
  constructor
  · rintro ⟨a, b, hab, heq⟩
    obtain ⟨ha, hb⟩ := Entity.kpair_inj.1 heq
    obtain rfl := Entity.atom_inj.1 ha
    obtain rfl := Entity.atom_inj.1 hb
    exact hab
  · exact fun h ↦ ⟨x, y, h, rfl⟩

/-- Initial segment `{1, …, n} = {k ∈ ℕ : 1 ≤ k ≤ r}` as an entity in `Entity ℝ`
(giving `∅` when `r < 1` and `{1, …, n}` when `r = (n : ℝ)` with `n ≥ 1`;
Goldblatt §13.9 & §13.17, pp. 171, 178). -/
def initSegStd (r : ℝ) : Entity ℝ :=
  mkAtomSet {x : ℝ | ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ r ∧ x = (k : ℝ)}

/-- Each `initSegStd (n : ℝ)` belongs to `Entity.finPowerset posNatEntity`
(Goldblatt §13.17, p. 178). -/
theorem initSegStd_mem_finPowerset (n : ℕ) :
    initSegStd (n : ℝ) ∈ Entity.finPowerset posNatEntity := by
  rw [Entity.mem_finPowerset_iff]
  refine ⟨Entity.isSet_setOfBounded _, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, ⟨k, hk1, _, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 hz
    exact atom_mem_mkAtomSet_iff.2 ⟨k, hk1, rfl⟩
  · have hsub : (initSegStd (n : ℝ)).extSet ⊆
        (fun k : ℕ ↦ Entity.atom (k : ℝ)) '' (Finset.Icc 1 n : Set ℕ) := by
      intro z hz
      obtain ⟨x, ⟨k, hk1, hkle, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 hz
      have hkn : k ≤ n := by exact_mod_cast hkle
      exact ⟨k, Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨hk1, hkn⟩), rfl⟩
    exact ((Finset.finite_toSet (Finset.Icc 1 n)).image _).subset hsub

/-- Standard function `n ↦ {1, …, n}` from `nat0Entity` to `Entity.finPowerset posNatEntity`
(Goldblatt §13.9 & §13.17, pp. 171, 178). -/
def initSegFun : Entity ℝ :=
  Entity.mkFuncEntity nat0Entity (fun e ↦ initSegStd (Entity.atomVal 0 e))

/-- `initSegFun` is a set-theoretic function `nat0Entity → Entity.finPowerset posNatEntity`. -/
theorem isFuncFromTo_initSegFun :
    Entity.IsFuncFromTo initSegFun nat0Entity (Entity.finPowerset posNatEntity) := by
  refine Entity.isFuncFromTo_mkFuncEntity fun e he ↦ ?_
  obtain ⟨r, ⟨n, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 he
  simpa using initSegStd_mem_finPowerset n

/-- Hyperfinite initial segment `{1, …, N} = {x ∈ *ℕ : x ≤ N}` for `N ∈ *ℕ₀` in any framework
`F : Framework ℝ Y` (Goldblatt §13.9 & §13.17, pp. 171, 178). -/
def Framework.initSeg {Y : Type*} (F : Framework ℝ Y) (N : Entity Y) : Entity Y :=
  Entity.funcApp (F.star initSegFun) N

/-- For every `N ∈ F.star nat0Entity`, `F.initSeg N ∈ F.star (Entity.finPowerset posNatEntity)`
(and in particular `F.initSeg N ∈ F.star (Entity.powerset posNatEntity)`). -/
theorem Framework.initSeg_mem_star_finPowerset {Y : Type*} (F : Framework ℝ Y) {N : Entity Y}
    (hN : N ∈ F.star nat0Entity) :
    F.initSeg N ∈ F.star (Entity.finPowerset posNatEntity) := by
  have hf := (F.isFuncFromTo_star_iff).2 isFuncFromTo_initSegFun
  have hdom : N ∈ Entity.relDom (F.star initSegFun) := by
    rw [hf.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_setOfBounded _))]
    exact hN
  exact hf.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨N, Entity.kpair_funcApp_mem hdom⟩)

/-- Membership in `F.initSeg N`: for `N ∈ F.star nat0Entity`,
`x ∈ F.initSeg N ↔ x ∈ F.star posNatEntity ∧ (x, N) ∈ F.star realLeRel`
(Goldblatt §13.9, p. 171). -/
theorem Framework.mem_initSeg_iff {Y : Type*} (F : Framework ℝ Y) {N : Entity Y}
    (hN : N ∈ F.star nat0Entity) {x : Entity Y} :
    x ∈ F.initSeg N ↔ x ∈ F.star posNatEntity ∧ Entity.kpair x N ∈ F.star realLeRel := by
  have hsub : (F.initSeg N).IsSet ∧ (F.initSeg N).extSet ⊆ (F.star posNatEntity).extSet := by
    have hfp : ∀ B ∈ Entity.finPowerset posNatEntity, B ∈ Entity.powerset posNatEntity :=
      fun B hB ↦ by
        rw [Entity.mem_finPowerset_iff] at hB
        exact Entity.mem_powerset_iff.2 ⟨hB.1, hB.2.1⟩
    have hmemP : F.initSeg N ∈ F.star (Entity.powerset posNatEntity) :=
      (F.subset_star_iff.2 hfp) _ (F.initSeg_mem_star_finPowerset hN)
    exact Entity.mem_powerset_iff.1 (F.mem_powerset_star_of_mem_star_powerset hmemP)
  let φ : UFormula ℝ :=
    .forallIn 0 (.const nat0Entity)
      (.forallIn 1 (.const posNatEntity)
        (.iff
          (.mem (.var 1) (.app (.const initSegFun) (.var 0)))
          (.mem (UTerm.pair (.var 1) (.var 0)) (.const realLeRel))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v
    simp [φ, freeVarsUFormula, freeVarsUTerm]
  have hstd : SentenceHolds φ := by
    refine ⟨nat0Entity, rfl, fun eN heN ↦ ⟨posNatEntity, rfl, fun ex hex ↦ ?_⟩⟩
    obtain ⟨_, ⟨n, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 heN
    obtain ⟨_, ⟨k, hk1, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 hex
    have hfn_eval : evalUTerm
        (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0 (Entity.atom (n : ℝ))) 1
          (Entity.atom (k : ℝ)))
        (.app (.const initSegFun) (.var 0)) = some (initSegStd (n : ℝ)) := by
      rw [evalUTerm_app_eq_some_iff]
      refine ⟨initSegFun, Entity.atom (n : ℝ), rfl, by simp,
        isFuncFromTo_initSegFun.isFuncEntity, ?_, ?_⟩
      · rw [isFuncFromTo_initSegFun.relDom_eq (Entity.isSet_setOfBounded _)]
        exact heN
      · have happ := Entity.funcApp_mkFuncEntity
          (B := Entity.finPowerset posNatEntity)
          (g := fun e ↦ initSegStd (Entity.atomVal 0 e))
          (fun e he ↦ by
            obtain ⟨_, ⟨m, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 he
            simpa using initSegStd_mem_finPowerset m)
          heN
        simpa [initSegFun] using happ
    simp only [Holds, hfn_eval, evalUTerm_pair]
    have hev0 : evalUTerm
        (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0 (Entity.atom (n : ℝ))) 1
          (Entity.atom (k : ℝ))) (.var 0) = some (Entity.atom (n : ℝ)) := by simp
    have hev1 : evalUTerm
        (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0 (Entity.atom (n : ℝ))) 1
          (Entity.atom (k : ℝ))) (.var 1) = some (Entity.atom (k : ℝ)) := by simp
    rw [hev1, hev0]
    dsimp only
    constructor
    · rintro ⟨a, B, ha, hB, hm⟩
      obtain rfl := Option.some.inj ha
      obtain rfl := Option.some.inj hB
      obtain ⟨_, ⟨k', _, hkle, hkeq⟩, hat⟩ := mem_mkAtomSet_iff.1 hm
      have hkk' : (k : ℝ) = (k' : ℝ) := (Entity.atom_inj.1 hat).trans hkeq
      exact ⟨_, _, rfl, rfl, kpair_atom_mem_realLeRel_iff.2 (hkk' ▸ hkle)⟩
    · rintro ⟨p, R, hp, hR, hm⟩
      obtain rfl := Option.some.inj hp
      obtain rfl := Option.some.inj hR
      have hkle : (k : ℝ) ≤ (n : ℝ) := kpair_atom_mem_realLeRel_iff.1 hm
      exact ⟨_, _, rfl, rfl, atom_mem_mkAtomSet_iff.2 ⟨k, hk1, hkle, rfl⟩⟩
  have htr := (F.transfer φ hsent).1 hstd
  obtain ⟨_, hNdom, hallN⟩ := htr
  obtain rfl := Option.some.inj hNdom
  obtain ⟨_, hPdom, hallX⟩ := hallN N hN
  obtain rfl := Option.some.inj hPdom
  constructor
  · intro hx
    have hxP : x ∈ F.star posNatEntity := hsub.2 hx
    have hiff := hallX x hxP
    have hfn_star : evalUTerm
        (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 N) 1 x)
        (.app (.const (F.star initSegFun)) (.var 0)) = some (F.initSeg N) := by
      rw [evalUTerm_app_eq_some_iff]
      have hf := (F.isFuncFromTo_star_iff).2 isFuncFromTo_initSegFun
      refine ⟨F.star initSegFun, N, rfl, by simp, hf.isFuncEntity, ?_, rfl⟩
      rw [hf.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_setOfBounded _))]
      exact hN
    simp only [starFormula, starTerm_pair, starTerm, Holds, hfn_star, evalUTerm_pair] at hiff
    have hv0 : evalUTerm (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 N) 1 x)
        (.var 0) = some N := by simp
    have hv1 : evalUTerm (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 N) 1 x)
        (.var 1) = some x := by simp
    rw [hv1, hv0] at hiff
    dsimp only at hiff
    obtain ⟨p, R, hp, hR, hm⟩ := hiff.1 ⟨x, F.initSeg N, rfl, rfl, hx⟩
    obtain rfl := Option.some.inj hp
    obtain rfl := Option.some.inj hR
    exact ⟨hxP, hm⟩
  · rintro ⟨hxP, hle⟩
    have hiff := hallX x hxP
    have hfn_star : evalUTerm
        (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 N) 1 x)
        (.app (.const (F.star initSegFun)) (.var 0)) = some (F.initSeg N) := by
      rw [evalUTerm_app_eq_some_iff]
      have hf := (F.isFuncFromTo_star_iff).2 isFuncFromTo_initSegFun
      refine ⟨F.star initSegFun, N, rfl, by simp, hf.isFuncEntity, ?_, rfl⟩
      rw [hf.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_setOfBounded _))]
      exact hN
    simp only [starFormula, starTerm_pair, starTerm, Holds, hfn_star, evalUTerm_pair] at hiff
    have hv0 : evalUTerm (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 N) 1 x)
        (.var 0) = some N := by simp
    have hv1 : evalUTerm (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 N) 1 x)
        (.var 1) = some x := by simp
    rw [hv1, hv0] at hiff
    dsimp only at hiff
    obtain ⟨a, B, ha, hB, hm⟩ := hiff.2 ⟨Entity.kpair x N, F.star realLeRel, rfl, rfl, hle⟩
    obtain rfl := Option.some.inj ha
    obtain rfl := Option.some.inj hB
    exact hm

/-- Helper transferring universal 2-variable properties of `realLeRel` and `realLtRel` on
`realEntity` (used in §13.9–13.18). -/
theorem Framework.star_real_trichotomy {Y : Type*} (F : Framework ℝ Y)
    {α β : Entity Y} (hα : α ∈ F.star realEntity) (hβ : β ∈ F.star realEntity) :
    (Entity.kpair β α ∈ F.star realLeRel ↔ ¬ Entity.kpair α β ∈ F.star realLtRel) := by
  let φ : UFormula ℝ :=
    .forallIn 0 (.const realEntity)
      (.forallIn 1 (.const realEntity)
        (.iff
          (.mem (UTerm.pair (.var 1) (.var 0)) (.const realLeRel))
          (.neg (.mem (UTerm.pair (.var 0) (.var 1)) (.const realLtRel)))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm]; tauto
  have hstd : SentenceHolds φ := by
    refine ⟨realEntity, rfl, fun ea hea ↦ ⟨realEntity, rfl, fun eb heb ↦ ?_⟩⟩
    obtain ⟨a, rfl⟩ := mem_baseSet_iff.1 hea
    obtain ⟨b, rfl⟩ := mem_baseSet_iff.1 heb
    simp only [Holds, evalUTerm_pair]
    have hv0 : evalUTerm (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0
        (Entity.atom a)) 1 (Entity.atom b)) (.var 0) = some (Entity.atom a) := by simp
    have hv1 : evalUTerm (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0
        (Entity.atom a)) 1 (Entity.atom b)) (.var 1) = some (Entity.atom b) := by simp
    rw [hv0, hv1]; dsimp only
    constructor
    · rintro ⟨p, R, hp, hR, hm⟩ ⟨q, S, hq, hS, hlt⟩
      obtain rfl := Option.some.inj hp; obtain rfl := Option.some.inj hR
      obtain rfl := Option.some.inj hq; obtain rfl := Option.some.inj hS
      exact not_lt_of_ge (kpair_atom_mem_realLeRel_iff.1 hm) (kpair_atom_mem_realLtRel_iff.1 hlt)
    · intro hnot
      refine ⟨_, _, rfl, rfl, kpair_atom_mem_realLeRel_iff.2 (le_of_not_gt fun hlt ↦ ?_)⟩
      exact hnot ⟨_, _, rfl, rfl, kpair_atom_mem_realLtRel_iff.2 hlt⟩
  have htr := (F.transfer φ hsent).1 hstd
  obtain ⟨_, h1, hall1⟩ := htr; obtain rfl := Option.some.inj h1
  obtain ⟨_, h2, hall2⟩ := hall1 α hα; obtain rfl := Option.some.inj h2
  have hiff := hall2 β hβ
  simp only [starFormula, starTerm_pair, starTerm, Holds, evalUTerm_pair] at hiff
  have hv0 : evalUTerm (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 α) 1 β)
      (.var 0) = some α := by simp
  have hv1 : evalUTerm (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 α) 1 β)
      (.var 1) = some β := by simp
  rw [hv0, hv1] at hiff; dsimp only at hiff
  constructor
  · intro hle hlt
    exact (hiff.1 ⟨_, _, rfl, rfl, hle⟩) ⟨_, _, rfl, rfl, hlt⟩
  · intro hnlt
    obtain ⟨p, R, hp, hR, hm⟩ := hiff.2 fun ⟨p, R, hp, hR, hm⟩ ↦ by
      obtain rfl := Option.some.inj hp; obtain rfl := Option.some.inj hR
      exact hnlt hm
    obtain rfl := Option.some.inj hp; obtain rfl := Option.some.inj hR
    exact hm

/-- Goldblatt §13.9 (p. 171): When `N ∈ *ℕ \ im ℕ` is a nonstandard hypernatural, the initial
segment `F.initSeg N = {1, …, N}` is a **nonstandard** subset of `*ℕ`! -/
theorem Framework.isNonstandard_initSeg_of_nonstandard {Y : Type*} (F : Framework ℝ Y)
    {N : Entity Y} (hN : N ∈ F.star posNatEntity) (hNns : F.IsNonstandard N) :
    F.IsNonstandard (F.initSeg N) := by
  have hsub0 : ∀ z ∈ posNatEntity, z ∈ nat0Entity := fun z hz ↦ by
    obtain ⟨_, ⟨k, _, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 hz
    exact atom_mem_mkAtomSet_iff.2 ⟨k, rfl⟩
  have hN0 : N ∈ F.star nat0Entity := (F.subset_star_iff.2 hsub0) _ hN
  have hsubR : ∀ z ∈ posNatEntity, z ∈ realEntity := fun z hz ↦ by
    obtain ⟨r, _, rfl⟩ := mem_mkAtomSet_iff.1 hz
    exact mem_baseSet_iff.2 ⟨r, rfl⟩
  have hNR : N ∈ F.star realEntity := (F.subset_star_iff.2 hsubR) _ hN
  have hN_in_seg : N ∈ F.initSeg N := by
    rw [F.mem_initSeg_iff hN0]
    refine ⟨hN, (F.star_real_trichotomy hNR hNR).2 ?_⟩
    let φirr : UFormula ℝ :=
      .forallIn 0 (.const realEntity) (.neg (.mem (UTerm.pair (.var 0) (.var 0)) (.const realLtRel)))
    have hs_irr : IsSentence φirr := by
      rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
      intro v; simp [φirr, freeVarsUFormula, freeVarsUTerm]
    have hhold_irr : SentenceHolds φirr := by
      refine ⟨realEntity, rfl, fun ea hea ⟨p, R, hp, hR, hm⟩ ↦ ?_⟩
      obtain ⟨a, rfl⟩ := mem_baseSet_iff.1 hea
      simp only [evalUTerm_pair, Function.update_self, evalUTerm_var] at hp
      obtain rfl := Option.some.inj hp
      obtain rfl := Option.some.inj hR
      exact lt_irrefl a (kpair_atom_mem_realLtRel_iff.1 hm)
    obtain ⟨_, hd, hall⟩ := (F.transfer φirr hs_irr).1 hhold_irr
    obtain rfl := Option.some.inj hd
    intro hlt
    exact hall N hNR ⟨Entity.kpair N N, F.star realLtRel,
      by simp [starTerm_pair, evalUTerm_pair], rfl, hlt⟩
  rintro ⟨A, hEq⟩
  have hmemP : F.star A ∈ F.star (Entity.powerset posNatEntity) := by
    rw [← hEq]
    have hfp : ∀ B ∈ Entity.finPowerset posNatEntity, B ∈ Entity.powerset posNatEntity :=
      fun B hB ↦ by
        rw [Entity.mem_finPowerset_iff] at hB
        exact Entity.mem_powerset_iff.2 ⟨hB.1, hB.2.1⟩
    exact (F.subset_star_iff.2 hfp) _ (F.initSeg_mem_star_finPowerset hN0)
  obtain ⟨hAs, hAsub⟩ := Entity.mem_powerset_iff.1 ((F.mem_star_iff).1 hmemP)
  by_cases hfin : A.extSet.Finite
  · have hN_mem : N ∈ (F.star A).extSet := hEq ▸ hN_in_seg
    rw [F.star_extSet_eq_sigmaImage_of_finite hAs hfin] at hN_mem
    obtain ⟨a, _, rfl⟩ := hN_mem
    exact hNns (F.isStandard_star a)
  · have hinf : A.extSet.Infinite := hfin
    let ψunb : UFormula ℝ :=
      .forallIn 0 (.const posNatEntity)
        (.existsIn 1 (.const A) (.mem (UTerm.pair (.var 0) (.var 1)) (.const realLtRel)))
    have hs_unb : IsSentence ψunb := by
      rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
      intro v; simp [ψunb, freeVarsUFormula, freeVarsUTerm]; tauto
    have hhold_unb : SentenceHolds ψunb := by
      refine ⟨posNatEntity, rfl, fun em hem ↦ ⟨A, rfl, ?_⟩⟩
      obtain ⟨_, ⟨m, _, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 hem
      have hfin_le : ((fun k : ℕ ↦ Entity.atom (k : ℝ)) '' (Finset.Icc 1 m : Set ℕ)).Finite :=
        (Finset.finite_toSet (Finset.Icc 1 m)).image _
      obtain ⟨ex, hexA, hexNot⟩ := (hinf.sdiff hfin_le).nonempty
      obtain ⟨_, ⟨k, hk1, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 (hAsub ex hexA)
      have hmk : m < k := by
        by_contra hle
        push Not at hle
        exact hexNot ⟨k, Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨hk1, hle⟩), rfl⟩
      have hmlt : (m : ℝ) < (k : ℝ) := by exact_mod_cast hmk
      refine ⟨Entity.atom (k : ℝ), hexA, Entity.kpair (Entity.atom (m : ℝ)) (Entity.atom (k : ℝ)),
        realLtRel, ?_, rfl, kpair_atom_mem_realLtRel_iff.2 hmlt⟩
      simp [evalUTerm_pair]
    obtain ⟨_, hd, hall⟩ := (F.transfer ψunb hs_unb).1 hhold_unb
    obtain rfl := Option.some.inj hd
    obtain ⟨_, hAd, x, hxA, p, R, hp, hR, hlt⟩ := hall N hN
    obtain rfl := Option.some.inj hAd
    have hpeq : evalUTerm
        (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 N) 1 x)
        (starTerm F.star (UTerm.pair (.var 0) (.var 1))) = some (Entity.kpair N x) := by
      simp [starTerm_pair, evalUTerm_pair]
    obtain rfl := Option.some.inj (hpeq.symm.trans hp)
    obtain rfl := Option.some.inj hR
    have hx_seg : x ∈ F.initSeg N := hEq.symm ▸ hxA
    obtain ⟨hxP, hxle⟩ := (F.mem_initSeg_iff hN0).1 hx_seg
    have hxR : x ∈ F.star realEntity := (F.subset_star_iff.2 hsubR) _ hxP
    exact ((F.star_real_trichotomy hNR hxR).1 hxle) hlt

/-- Open real interval `(a, b) = {x ∈ ℝ : a < x < b}` as an entity in `Entity ℝ`
(Goldblatt §13.9, p. 171). -/
def openIntervalEntity (a b : ℝ) : Entity ℝ :=
  mkAtomSet (Set.Ioo a b)

/-- Standard function `(a, b) ↦ (a, b) ⊆ ℝ` from `realEntity × realEntity` to
`Entity.powerset realEntity` (Goldblatt §13.9, p. 171). -/
def openIntervalPairFun : Entity ℝ :=
  Entity.mkFuncEntity (Entity.prod realEntity realEntity) (fun p ↦
    openIntervalEntity (Entity.atomVal 0 (Entity.pairFirst p))
      (Entity.atomVal 0 (Entity.pairSecond p)))

/-- `openIntervalPairFun` is a function `realEntity × realEntity → 𝒫(realEntity)`. -/
theorem isFuncFromTo_openIntervalPairFun :
    Entity.IsFuncFromTo openIntervalPairFun
      (Entity.prod realEntity realEntity) (Entity.powerset realEntity) := by
  refine Entity.isFuncFromTo_mkFuncEntity fun p _ ↦ ?_
  rw [Entity.mem_powerset_iff]
  refine ⟨Entity.isSet_setOfBounded _, fun z hz ↦ ?_⟩
  obtain ⟨r, _, rfl⟩ := mem_mkAtomSet_iff.1 hz
  exact mem_baseSet_iff.2 ⟨r, rfl⟩

/-- Goldblatt §13.9 (p. 171): `Int ∈ 𝕌_2(ℝ)`, the set of all open subintervals
`{(a, b) ⊆ ℝ : a, b ∈ ℝ}` of the real line. -/
def openIntervalsCollection : Entity ℝ :=
  Entity.relRan openIntervalPairFun

/-- Membership in `openIntervalsCollection` (`I ∈ Int ↔ ∃ a b : ℝ, I = (a, b)`;
Goldblatt §13.9, p. 171). -/
theorem mem_openIntervalsCollection_iff {I : Entity ℝ} :
    I ∈ openIntervalsCollection ↔ ∃ a b : ℝ, I = openIntervalEntity a b := by
  rw [openIntervalsCollection, Entity.mem_relRan_iff]
  constructor
  · rintro ⟨p, hp⟩
    have hf := isFuncFromTo_openIntervalPairFun
    obtain ⟨p', hp', _, _, heq⟩ := hf.2.1 _ hp
    obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 heq
    obtain ⟨ea, hea, eb, heb, rfl⟩ := Entity.mem_prod_iff.1 hp'
    obtain ⟨a, rfl⟩ := mem_baseSet_iff.1 hea
    obtain ⟨b, rfl⟩ := mem_baseSet_iff.1 heb
    have happ := ((Entity.kpair_mem_iff_funcApp_eq hf.isFuncEntity).1 hp).2
    have hval : Entity.funcApp openIntervalPairFun (Entity.kpair (Entity.atom a) (Entity.atom b)) =
        openIntervalEntity a b := by
      have hv := Entity.funcApp_mkFuncEntity
        (B := Entity.powerset realEntity)
        (g := fun q ↦ openIntervalEntity (Entity.atomVal 0 (Entity.pairFirst q))
          (Entity.atomVal 0 (Entity.pairSecond q)))
        (fun q _ ↦ Entity.mem_powerset_iff.2 ⟨Entity.isSet_setOfBounded _, fun z hz ↦ by
          obtain ⟨r, _, rfl⟩ := mem_mkAtomSet_iff.1 hz
          exact mem_baseSet_iff.2 ⟨r, rfl⟩⟩)
        hp'
      simpa [openIntervalPairFun] using hv
    exact ⟨a, b, happ.symm.trans hval⟩
  · rintro ⟨a, b, rfl⟩
    have hp : Entity.kpair (Entity.atom a) (Entity.atom b) ∈ Entity.prod realEntity realEntity :=
      Entity.kpair_mem_prod_iff.2 ⟨mem_baseSet_iff.2 ⟨a, rfl⟩, mem_baseSet_iff.2 ⟨b, rfl⟩⟩
    have hf := isFuncFromTo_openIntervalPairFun
    have hdom : Entity.kpair (Entity.atom a) (Entity.atom b) ∈
        Entity.relDom openIntervalPairFun := by
      rw [hf.relDom_eq (Entity.isSet_prod _ _)]
      exact hp
    have hval : Entity.funcApp openIntervalPairFun (Entity.kpair (Entity.atom a) (Entity.atom b)) =
        openIntervalEntity a b := by
      have hv := Entity.funcApp_mkFuncEntity
        (B := Entity.powerset realEntity)
        (g := fun q ↦ openIntervalEntity (Entity.atomVal 0 (Entity.pairFirst q))
          (Entity.atomVal 0 (Entity.pairSecond q)))
        (fun q _ ↦ Entity.mem_powerset_iff.2 ⟨Entity.isSet_setOfBounded _, fun z hz ↦ by
          obtain ⟨r, _, rfl⟩ := mem_mkAtomSet_iff.1 hz
          exact mem_baseSet_iff.2 ⟨r, rfl⟩⟩)
        hp
      simpa [openIntervalPairFun] using hv
    exact ⟨Entity.kpair (Entity.atom a) (Entity.atom b),
      hval ▸ Entity.kpair_funcApp_mem hdom⟩

/-- Hyperreal open interval `(α, β) = {x ∈ *ℝ : α < x < β}` in any framework `F : Framework ℝ Y`
(Goldblatt §13.9, p. 171). -/
def Framework.starOpenInterval {Y : Type*} (F : Framework ℝ Y) (α β : Entity Y) : Entity Y :=
  Entity.setOfBounded {x : Entity Y |
    x ∈ F.star realEntity ∧
    Entity.kpair α x ∈ F.star realLtRel ∧
    Entity.kpair x β ∈ F.star realLtRel}

/-- Membership in `F.starOpenInterval α β` (Goldblatt §13.9, p. 171). -/
@[simp]
theorem Framework.mem_starOpenInterval_iff {Y : Type*} (F : Framework ℝ Y)
    {α β x : Entity Y} :
    x ∈ F.starOpenInterval α β ↔
      x ∈ F.star realEntity ∧
      Entity.kpair α x ∈ F.star realLtRel ∧
      Entity.kpair x β ∈ F.star realLtRel :=
  Entity.mem_setOfBounded ((F.star realEntity).isBoundedRank_extSet.subset fun _ h ↦ h.1)

/-- For `α, β ∈ F.star realEntity`, `Entity.funcApp (F.star openIntervalPairFun) (α, β)` equals
`F.starOpenInterval α β` (Goldblatt §13.9, p. 171). -/
theorem Framework.funcApp_star_openIntervalPairFun {Y : Type*} (F : Framework ℝ Y)
    {α β : Entity Y} (hα : α ∈ F.star realEntity) (hβ : β ∈ F.star realEntity) :
    Entity.funcApp (F.star openIntervalPairFun) (Entity.kpair α β) =
      F.starOpenInterval α β := by
  have hf := (F.isFuncFromTo_star_iff).2 isFuncFromTo_openIntervalPairFun
  have hp : Entity.kpair α β ∈ F.star (Entity.prod realEntity realEntity) := by
    rw [F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hα, hβ⟩
  have hdom : Entity.kpair α β ∈ Entity.relDom (F.star openIntervalPairFun) := by
    rw [hf.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _))]
    exact hp
  have hval_memP : Entity.funcApp (F.star openIntervalPairFun) (Entity.kpair α β) ∈
      F.star (Entity.powerset realEntity) :=
    hf.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hdom⟩)
  obtain ⟨hvalSet, hvalSub⟩ :=
    Entity.mem_powerset_iff.1 (F.mem_powerset_star_of_mem_star_powerset hval_memP)
  let φ : UFormula ℝ :=
    .forallIn 0 (.const realEntity)
      (.forallIn 1 (.const realEntity)
        (.forallIn 2 (.const realEntity)
          (.iff
            (.mem (.var 2) (.app (.const openIntervalPairFun) (UTerm.pair (.var 0) (.var 1))))
            (.conj
              (.mem (UTerm.pair (.var 0) (.var 2)) (.const realLtRel))
              (.mem (UTerm.pair (.var 2) (.var 1)) (.const realLtRel))))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm]; tauto
  have hstd : SentenceHolds φ := by
    refine ⟨realEntity, rfl, fun ea hea ↦ ⟨realEntity, rfl, fun eb heb ↦
      ⟨realEntity, rfl, fun ex hex ↦ ?_⟩⟩⟩
    obtain ⟨a, rfl⟩ := mem_baseSet_iff.1 hea
    obtain ⟨b, rfl⟩ := mem_baseSet_iff.1 heb
    obtain ⟨x, rfl⟩ := mem_baseSet_iff.1 hex
    let env := Function.update (Function.update
      (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0 (Entity.atom a)) 1 (Entity.atom b)) 2
      (Entity.atom x)
    have hp_ab : Entity.kpair (Entity.atom a) (Entity.atom b) ∈
        Entity.prod realEntity realEntity :=
      Entity.kpair_mem_prod_iff.2 ⟨hea, heb⟩
    have hfn_eval : evalUTerm env (.app (.const openIntervalPairFun)
        (UTerm.pair (.var 0) (.var 1))) = some (openIntervalEntity a b) := by
      rw [evalUTerm_app_eq_some_iff]
      refine ⟨openIntervalPairFun, Entity.kpair (Entity.atom a) (Entity.atom b), rfl,
        by simp [env, evalUTerm_pair], isFuncFromTo_openIntervalPairFun.isFuncEntity, ?_, ?_⟩
      · rw [isFuncFromTo_openIntervalPairFun.relDom_eq (Entity.isSet_prod _ _)]
        exact hp_ab
      · have hv := Entity.funcApp_mkFuncEntity
          (B := Entity.powerset realEntity)
          (g := fun q ↦ openIntervalEntity (Entity.atomVal 0 (Entity.pairFirst q))
            (Entity.atomVal 0 (Entity.pairSecond q)))
          (fun q _ ↦ Entity.mem_powerset_iff.2 ⟨Entity.isSet_setOfBounded _, fun z hz ↦ by
            obtain ⟨r, _, rfl⟩ := mem_mkAtomSet_iff.1 hz
            exact mem_baseSet_iff.2 ⟨r, rfl⟩⟩)
          hp_ab
        simpa [openIntervalPairFun] using hv
    change Holds env _
    simp only [Holds, hfn_eval]
    have hv0 : evalUTerm env (.var 0) = some (Entity.atom a) := by simp [env]
    have hv1 : evalUTerm env (.var 1) = some (Entity.atom b) := by simp [env]
    have hv2 : evalUTerm env (.var 2) = some (Entity.atom x) := by simp [env]
    simp only [evalUTerm_pair, hv0, hv1, hv2]
    constructor
    · rintro ⟨u, B, hu, hB, hm⟩
      obtain rfl := Option.some.inj hu; obtain rfl := Option.some.inj hB
      obtain ⟨hax, hxb⟩ := atom_mem_mkAtomSet_iff.1 hm
      exact ⟨⟨_, _, rfl, rfl, kpair_atom_mem_realLtRel_iff.2 hax⟩,
        ⟨_, _, rfl, rfl, kpair_atom_mem_realLtRel_iff.2 hxb⟩⟩
    · rintro ⟨⟨p1, R1, hp1, hR1, h1⟩, ⟨p2, R2, hp2, hR2, h2⟩⟩
      obtain rfl := Option.some.inj hp1; obtain rfl := Option.some.inj hR1
      obtain rfl := Option.some.inj hp2; obtain rfl := Option.some.inj hR2
      exact ⟨_, _, rfl, rfl, atom_mem_mkAtomSet_iff.2
        ⟨kpair_atom_mem_realLtRel_iff.1 h1, kpair_atom_mem_realLtRel_iff.1 h2⟩⟩
  obtain ⟨_, hd0, hall0⟩ := (F.transfer φ hsent).1 hstd; obtain rfl := Option.some.inj hd0
  obtain ⟨_, hd1, hall1⟩ := hall0 α hα; obtain rfl := Option.some.inj hd1
  obtain ⟨_, hd2, hall2⟩ := hall1 β hβ; obtain rfl := Option.some.inj hd2
  refine Entity.set_ext hvalSet (Entity.isSet_setOfBounded _) fun x ↦ ?_
  rw [F.mem_starOpenInterval_iff]
  constructor
  · intro hx
    have hxR : x ∈ F.star realEntity := hvalSub x hx
    have hiff := hall2 x hxR
    let envY := Function.update (Function.update
      (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 α) 1 β) 2 x
    have hfn_star : evalUTerm envY
        (.app (.const (F.star openIntervalPairFun)) (UTerm.pair (.var 0) (.var 1))) =
        some (Entity.funcApp (F.star openIntervalPairFun) (Entity.kpair α β)) := by
      rw [evalUTerm_app_eq_some_iff]
      exact ⟨F.star openIntervalPairFun, Entity.kpair α β, rfl,
        by simp [envY, evalUTerm_pair], hf.isFuncEntity, hdom, rfl⟩
    change Holds envY (starFormula F.star _) at hiff
    simp only [starFormula, starTerm_pair, starTerm, Holds, hfn_star] at hiff
    have hv0 : evalUTerm envY (.var 0) = some α := by simp [envY]
    have hv1 : evalUTerm envY (.var 1) = some β := by simp [envY]
    have hv2 : evalUTerm envY (.var 2) = some x := by simp [envY]
    simp only [evalUTerm_pair, hv0, hv1, hv2] at hiff
    obtain ⟨⟨p1, R1, hp1, hR1, h1⟩, ⟨p2, R2, hp2, hR2, h2⟩⟩ :=
      hiff.1 ⟨x, _, rfl, rfl, hx⟩
    obtain rfl := Option.some.inj hp1; obtain rfl := Option.some.inj hR1
    obtain rfl := Option.some.inj hp2; obtain rfl := Option.some.inj hR2
    exact ⟨hxR, h1, h2⟩
  · rintro ⟨hxR, h1, h2⟩
    have hiff := hall2 x hxR
    let envY := Function.update (Function.update
      (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 α) 1 β) 2 x
    have hfn_star : evalUTerm envY
        (.app (.const (F.star openIntervalPairFun)) (UTerm.pair (.var 0) (.var 1))) =
        some (Entity.funcApp (F.star openIntervalPairFun) (Entity.kpair α β)) := by
      rw [evalUTerm_app_eq_some_iff]
      exact ⟨F.star openIntervalPairFun, Entity.kpair α β, rfl,
        by simp [envY, evalUTerm_pair], hf.isFuncEntity, hdom, rfl⟩
    change Holds envY (starFormula F.star _) at hiff
    simp only [starFormula, starTerm_pair, starTerm, Holds, hfn_star] at hiff
    have hv0 : evalUTerm envY (.var 0) = some α := by simp [envY]
    have hv1 : evalUTerm envY (.var 1) = some β := by simp [envY]
    have hv2 : evalUTerm envY (.var 2) = some x := by simp [envY]
    simp only [evalUTerm_pair, hv0, hv1, hv2] at hiff
    obtain ⟨u, B, hu, hB, hm⟩ := hiff.2 ⟨⟨_, _, rfl, rfl, h1⟩, ⟨_, _, rfl, rfl, h2⟩⟩
    obtain rfl := Option.some.inj hu; obtain rfl := Option.some.inj hB
    exact hm

/-- For standard endpoints `a, b : ℝ`, `*(a, b) = {x ∈ *ℝ : *a < x < *b}`
(Goldblatt §13.9, p. 171). -/
theorem Framework.star_openIntervalEntity {Y : Type*} (F : Framework ℝ Y) (a b : ℝ) :
    F.star (openIntervalEntity a b) =
      F.starOpenInterval (F.star (Entity.atom a)) (F.star (Entity.atom b)) := by
  have hp : Entity.kpair (Entity.atom a) (Entity.atom b) ∈ Entity.prod realEntity realEntity :=
    Entity.kpair_mem_prod_iff.2 ⟨mem_baseSet_iff.2 ⟨a, rfl⟩, mem_baseSet_iff.2 ⟨b, rfl⟩⟩
  have hf := isFuncFromTo_openIntervalPairFun
  have hdom : Entity.kpair (Entity.atom a) (Entity.atom b) ∈
      Entity.relDom openIntervalPairFun := by
    rw [hf.relDom_eq (Entity.isSet_prod _ _)]; exact hp
  have hv : Entity.funcApp openIntervalPairFun (Entity.kpair (Entity.atom a) (Entity.atom b)) =
      openIntervalEntity a b := by
    have hv0 := Entity.funcApp_mkFuncEntity
      (B := Entity.powerset realEntity)
      (g := fun q ↦ openIntervalEntity (Entity.atomVal 0 (Entity.pairFirst q))
        (Entity.atomVal 0 (Entity.pairSecond q)))
      (fun q _ ↦ Entity.mem_powerset_iff.2 ⟨Entity.isSet_setOfBounded _, fun z hz ↦ by
        obtain ⟨r, _, rfl⟩ := mem_mkAtomSet_iff.1 hz
        exact mem_baseSet_iff.2 ⟨r, rfl⟩⟩)
      hp
    simpa [openIntervalPairFun] using hv0
  rw [← hv, F.star_funcApp hf.isFuncEntity hdom, F.star_kpair]
  exact F.funcApp_star_openIntervalPairFun
    (F.mem_star_iff.2 (mem_baseSet_iff.2 ⟨a, rfl⟩))
    (F.mem_star_iff.2 (mem_baseSet_iff.2 ⟨b, rfl⟩))

/-- Goldblatt §13.9 (pp. 171–172): `*Int` consists precisely of the hyperreal open intervals
`(α, β) = {x ∈ *ℝ : α < x < β}` for all `α, β ∈ *ℝ`! -/
theorem Framework.mem_star_openIntervalsCollection_iff {Y : Type*} (F : Framework ℝ Y)
    {A : Entity Y} :
    A ∈ F.star openIntervalsCollection ↔
      ∃ α ∈ F.star realEntity, ∃ β ∈ F.star realEntity, A = F.starOpenInterval α β := by
  rw [openIntervalsCollection, F.star_relRan, Entity.mem_relRan_iff]
  have hf := (F.isFuncFromTo_star_iff).2 isFuncFromTo_openIntervalPairFun
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨p', hp', _, _, heq⟩ := hf.2.1 _ hp
    obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 heq
    rw [F.star_prod, Entity.mem_prod_iff] at hp'
    obtain ⟨α, hα, β, hβ, rfl⟩ := hp'
    have happ := ((Entity.kpair_mem_iff_funcApp_eq hf.isFuncEntity).1 hp).2
    exact ⟨α, hα, β, hβ, happ.symm.trans (F.funcApp_star_openIntervalPairFun hα hβ)⟩
  · rintro ⟨α, hα, β, hβ, rfl⟩
    have hp : Entity.kpair α β ∈ F.star (Entity.prod realEntity realEntity) := by
      rw [F.star_prod]; exact Entity.kpair_mem_prod_iff.2 ⟨hα, hβ⟩
    have hdom : Entity.kpair α β ∈ Entity.relDom (F.star openIntervalPairFun) := by
      rw [hf.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _))]; exact hp
    rw [← F.funcApp_star_openIntervalPairFun hα hβ]
    exact ⟨Entity.kpair α β, Entity.kpair_funcApp_mem hdom⟩

/-- Goldblatt **Exercise 13.9.1** (p. 172): Exact characterization of the **standard** elements of
`*Int` — for `α, β ∈ *ℝ`, the hyperreal open interval `(α, β) ∈ *Int` is standard **if and only if**
either `β ≤ α` (in which case `(α, β) = ∅ = *∅`) or `α < β` with **both** `α` and `β` standard! -/
theorem Framework.isStandard_starOpenInterval_iff {Y : Type*} (F : Framework ℝ Y)
    {α β : Entity Y} (hα : α ∈ F.star realEntity) (hβ : β ∈ F.star realEntity) :
    F.IsStandard (F.starOpenInterval α β) ↔
      Entity.kpair β α ∈ F.star realLeRel ∨
      (Entity.kpair α β ∈ F.star realLtRel ∧ F.IsStandard α ∧ F.IsStandard β) := by
  -- Transfer density/emptiness of open intervals in ℝ: `α < β ↔ ∃ x ∈ *ℝ, α < x ∧ x < β`
  have hnonempty_iff : Entity.kpair α β ∈ F.star realLtRel ↔
      ∃ x : Entity Y, x ∈ F.starOpenInterval α β := by
    let φden : UFormula ℝ :=
      .forallIn 0 (.const realEntity)
        (.forallIn 1 (.const realEntity)
          (.iff
            (.mem (UTerm.pair (.var 0) (.var 1)) (.const realLtRel))
            (.existsIn 2 (.const realEntity)
              (.conj
                (.mem (UTerm.pair (.var 0) (.var 2)) (.const realLtRel))
                (.mem (UTerm.pair (.var 2) (.var 1)) (.const realLtRel))))))
    have hs_den : IsSentence φden := by
      rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
      intro v; simp [φden, freeVarsUFormula, freeVarsUTerm]; omega
    have hhold_den : SentenceHolds φden := by
      refine ⟨realEntity, rfl, fun ea hea ↦ ⟨realEntity, rfl, fun eb heb ↦ ?_⟩⟩
      obtain ⟨a, rfl⟩ := mem_baseSet_iff.1 hea
      obtain ⟨b, rfl⟩ := mem_baseSet_iff.1 heb
      let env0 := Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0 (Entity.atom a)) 1
        (Entity.atom b)
      change Holds env0 _
      simp only [Holds, evalUTerm_pair]
      have hv0 : evalUTerm env0 (.var 0) = some (Entity.atom a) := by simp [env0]
      have hv1 : evalUTerm env0 (.var 1) = some (Entity.atom b) := by simp [env0]
      rw [hv0, hv1]; dsimp only
      constructor
      · rintro ⟨p, R, hp, hR, hm⟩
        obtain rfl := Option.some.inj hp; obtain rfl := Option.some.inj hR
        have hab : a < b := kpair_atom_mem_realLtRel_iff.1 hm
        refine ⟨realEntity, rfl, Entity.atom ((a + b) / 2), mem_baseSet_iff.2 ⟨_, rfl⟩, ?_⟩
        exact ⟨⟨Entity.kpair (Entity.atom a) (Entity.atom ((a + b) / 2)), realLtRel,
            by simp [env0], rfl,
            kpair_atom_mem_realLtRel_iff.2 (by linarith)⟩,
          ⟨Entity.kpair (Entity.atom ((a + b) / 2)) (Entity.atom b), realLtRel,
            by simp [env0], rfl,
            kpair_atom_mem_realLtRel_iff.2 (by linarith)⟩⟩
      · rintro ⟨_, hRd, ex, hex, ⟨p1, R1, hp1, hR1, h1⟩, ⟨p2, R2, hp2, hR2, h2⟩⟩
        obtain rfl := Option.some.inj hRd
        obtain ⟨x, rfl⟩ := mem_baseSet_iff.1 hex
        have hv0' : evalUTerm (Function.update env0 2 (Entity.atom x)) (.var 0) =
            some (Entity.atom a) := by simp [env0]
        have hv1' : evalUTerm (Function.update env0 2 (Entity.atom x)) (.var 1) =
            some (Entity.atom b) := by simp [env0]
        have hv2' : evalUTerm (Function.update env0 2 (Entity.atom x)) (.var 2) =
            some (Entity.atom x) := by simp [env0]
        rw [hv0', hv2'] at hp1; rw [hv2', hv1'] at hp2
        dsimp only at hp1 hp2
        obtain rfl := Option.some.inj hp1; obtain rfl := Option.some.inj hR1
        obtain rfl := Option.some.inj hp2; obtain rfl := Option.some.inj hR2
        exact ⟨_, _, rfl, rfl, kpair_atom_mem_realLtRel_iff.2
          (lt_trans (kpair_atom_mem_realLtRel_iff.1 h1) (kpair_atom_mem_realLtRel_iff.1 h2))⟩
    obtain ⟨_, hd0, hall0⟩ := (F.transfer φden hs_den).1 hhold_den; obtain rfl := Option.some.inj hd0
    obtain ⟨_, hd1, hall1⟩ := hall0 α hα; obtain rfl := Option.some.inj hd1
    have hiff := hall1 β hβ
    let envY := Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 α) 1 β
    change Holds envY (starFormula F.star _) at hiff
    simp only [starFormula, starTerm_pair, starTerm, Holds, evalUTerm_pair] at hiff
    have hv0 : evalUTerm envY (.var 0) = some α := by simp [envY]
    have hv1 : evalUTerm envY (.var 1) = some β := by simp [envY]
    rw [hv0, hv1] at hiff; dsimp only at hiff
    constructor
    · intro hlt
      obtain ⟨_, hRd, x, hxR, ⟨p1, R1, hp1, hR1, h1⟩, ⟨p2, R2, hp2, hR2, h2⟩⟩ :=
        hiff.1 ⟨_, _, rfl, rfl, hlt⟩
      obtain rfl := Option.some.inj hRd
      have hv0' : evalUTerm (Function.update envY 2 x) (.var 0) = some α := by simp [envY]
      have hv1' : evalUTerm (Function.update envY 2 x) (.var 1) = some β := by simp [envY]
      have hv2' : evalUTerm (Function.update envY 2 x) (.var 2) = some x := by simp [envY]
      rw [hv0', hv2'] at hp1; rw [hv2', hv1'] at hp2
      dsimp only at hp1 hp2
      obtain rfl := Option.some.inj hp1; obtain rfl := Option.some.inj hR1
      obtain rfl := Option.some.inj hp2; obtain rfl := Option.some.inj hR2
      exact ⟨x, F.mem_starOpenInterval_iff.2 ⟨hxR, h1, h2⟩⟩
    · rintro ⟨x, hx⟩
      obtain ⟨hxR, h1, h2⟩ := F.mem_starOpenInterval_iff.1 hx
      obtain ⟨p, R, hp, hR, hm⟩ := hiff.2 ⟨F.star realEntity, rfl, x, hxR,
        ⟨_, _, by simp [envY], rfl, h1⟩, ⟨_, _, by simp [envY], rfl, h2⟩⟩
      obtain rfl := Option.some.inj hp; obtain rfl := Option.some.inj hR
      exact hm
  constructor
  · intro hstd
    by_cases hlt : Entity.kpair α β ∈ F.star realLtRel
    · refine Or.inr ⟨hlt, ?_⟩
      obtain ⟨C, hCeq⟩ := hstd
      have hC_in_Int : C ∈ openIntervalsCollection := by
        apply (F.mem_star_iff).1
        rw [← hCeq, F.mem_star_openIntervalsCollection_iff]
        exact ⟨α, hα, β, hβ, rfl⟩
      obtain ⟨a, b, rfl⟩ := mem_openIntervalsCollection_iff.1 hC_in_Int
      have hab : a < b := by
        by_contra hnot
        have hempC : openIntervalEntity a b = ∅ := by
          refine (Entity.eq_empty_iff_forall_not_mem (Entity.isSet_setOfBounded _)).2 fun z hz ↦ ?_
          obtain ⟨x, ⟨hax, hxb⟩, _⟩ := mem_mkAtomSet_iff.1 hz
          linarith
        obtain ⟨x, hx⟩ := hnonempty_iff.1 hlt
        rw [hCeq, hempC, F.star_empty] at hx
        exact Entity.not_mem_empty x hx
      -- Transfer endpoint uniqueness for nonempty open intervals on ℝ
      let ψuniq : UFormula ℝ :=
        forallVarsIn (.const realEntity) 4
          (.imp
            (.conj
              (.conj
                (.mem (UTerm.pair (.var 0) (.var 1)) (.const realLtRel))
                (.mem (UTerm.pair (.var 2) (.var 3)) (.const realLtRel)))
              (.forallIn 4 (.const realEntity)
                (.iff
                  (.conj
                    (.mem (UTerm.pair (.var 0) (.var 4)) (.const realLtRel))
                    (.mem (UTerm.pair (.var 4) (.var 1)) (.const realLtRel)))
                  (.conj
                    (.mem (UTerm.pair (.var 2) (.var 4)) (.const realLtRel))
                    (.mem (UTerm.pair (.var 4) (.var 3)) (.const realLtRel))))))
            (.conj (.eq (.var 0) (.var 2)) (.eq (.var 1) (.var 3))))
      have hs_uniq : IsSentence ψuniq := by
        rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
        intro v
        rw [freeVarsUFormula_forallVarsIn_const]
        simp [freeVarsUFormula, freeVarsUTerm]
        omega
      have hhold_uniq : SentenceHolds ψuniq := by
        rw [SentenceHolds, holds_forallVarsIn_const]
        intro w hw
        obtain ⟨r0, hr0⟩ := mem_baseSet_iff.1 (hw 0)
        obtain ⟨r1, hr1⟩ := mem_baseSet_iff.1 (hw 1)
        obtain ⟨r2, hr2⟩ := mem_baseSet_iff.1 (hw 2)
        obtain ⟨r3, hr3⟩ := mem_baseSet_iff.1 (hw 3)
        rintro ⟨⟨⟨p01, R01, hp01, hR01, hlt01⟩, ⟨p23, R23, hp23, hR23, hlt23⟩⟩, ⟨_, hRd, hext⟩⟩
        obtain rfl := Option.some.inj hRd
        have hp01' : p01 = Entity.kpair (Entity.atom r0) (Entity.atom r1) :=
          Option.some.inj (by simpa [evalUTerm_pair, hr0.symm, hr1.symm] using hp01.symm)
        have hp23' : p23 = Entity.kpair (Entity.atom r2) (Entity.atom r3) :=
          Option.some.inj (by simpa [evalUTerm_pair, hr2.symm, hr3.symm] using hp23.symm)
        subst hp01'; subst hp23'
        obtain rfl := Option.some.inj hR01
        obtain rfl := Option.some.inj hR23
        have h01 : r0 < r1 := kpair_atom_mem_realLtRel_iff.1 hlt01
        have h23 : r2 < r3 := kpair_atom_mem_realLtRel_iff.1 hlt23
        have hIoo : ∀ x : ℝ, (r0 < x ∧ x < r1) ↔ (r2 < x ∧ x < r3) := fun x ↦ by
          let env4 : ℕ → Entity ℝ :=
            Function.update (fun n : ℕ ↦ if h : n < 4 then w ⟨n, h⟩ else ∅) 4 (Entity.atom x)
          have hx := hext (Entity.atom x) (mem_baseSet_iff.2 ⟨x, rfl⟩)
          change Holds env4 _ at hx
          simp only [Holds, evalUTerm_pair] at hx
          have u0 : evalUTerm env4 (.var 0) = some (Entity.atom r0) := by
            simpa [env4] using hr0
          have u1 : evalUTerm env4 (.var 1) = some (Entity.atom r1) := by
            simpa [env4] using hr1
          have u2 : evalUTerm env4 (.var 2) = some (Entity.atom r2) := by
            simpa [env4] using hr2
          have u3 : evalUTerm env4 (.var 3) = some (Entity.atom r3) := by
            simpa [env4] using hr3
          have u4 : evalUTerm env4 (.var 4) = some (Entity.atom x) := by simp [env4]
          rw [u0, u1, u2, u3, u4] at hx; dsimp only at hx
          constructor
          · rintro ⟨ha, hb⟩
            obtain ⟨⟨_, _, hpa, hRa, hma⟩, ⟨_, _, hpb, hRb, hmb⟩⟩ := hx.1
              ⟨⟨_, _, rfl, rfl, kpair_atom_mem_realLtRel_iff.2 ha⟩,
               ⟨_, _, rfl, rfl, kpair_atom_mem_realLtRel_iff.2 hb⟩⟩
            obtain rfl := Option.some.inj hpa; obtain rfl := Option.some.inj hRa
            obtain rfl := Option.some.inj hpb; obtain rfl := Option.some.inj hRb
            exact ⟨kpair_atom_mem_realLtRel_iff.1 hma, kpair_atom_mem_realLtRel_iff.1 hmb⟩
          · rintro ⟨ha, hb⟩
            obtain ⟨⟨_, _, hpa, hRa, hma⟩, ⟨_, _, hpb, hRb, hmb⟩⟩ := hx.2
              ⟨⟨_, _, rfl, rfl, kpair_atom_mem_realLtRel_iff.2 ha⟩,
               ⟨_, _, rfl, rfl, kpair_atom_mem_realLtRel_iff.2 hb⟩⟩
            obtain rfl := Option.some.inj hpa; obtain rfl := Option.some.inj hRa
            obtain rfl := Option.some.inj hpb; obtain rfl := Option.some.inj hRb
            exact ⟨kpair_atom_mem_realLtRel_iff.1 hma, kpair_atom_mem_realLtRel_iff.1 hmb⟩
        have heq02 : r0 = r2 := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt' | hgt'
          · let m := (r0 + min r1 r2) / 2
            have hm0 : r0 < m := by simp [m]; linarith [lt_min h01 hlt']
            have hm1 : m < r1 := by
              have : min r1 r2 ≤ r1 := min_le_left _ _
              simp [m]; linarith
            have hm2 : m < r2 := by
              have : min r1 r2 ≤ r2 := min_le_right _ _
              simp [m]; linarith
            exact absurd ((hIoo m).1 ⟨hm0, hm1⟩).1 (not_lt_of_gt hm2)
          · let m := (r2 + min r3 r0) / 2
            have hm2 : r2 < m := by simp [m]; linarith [lt_min h23 hgt']
            have hm3 : m < r3 := by
              have : min r3 r0 ≤ r3 := min_le_left _ _
              simp [m]; linarith
            have hm0 : m < r0 := by
              have : min r3 r0 ≤ r0 := min_le_right _ _
              simp [m]; linarith
            exact absurd ((hIoo m).2 ⟨hm2, hm3⟩).1 (not_lt_of_gt hm0)
        have heq13 : r1 = r3 := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt' | hgt'
          · let m := (max r2 r1 + r3) / 2
            have hm2 : r2 < m := by
              have : r2 ≤ max r2 r1 := le_max_left _ _
              simp [m]; linarith
            have hm1 : r1 < m := by
              have : r1 ≤ max r2 r1 := le_max_right _ _
              simp [m]; linarith
            have hm3 : m < r3 := by simp [m]; linarith [max_lt h23 hlt']
            exact absurd ((hIoo m).2 ⟨hm2, hm3⟩).2 (not_lt_of_gt hm1)
          · let m := (max r0 r3 + r1) / 2
            have hm0 : r0 < m := by
              have : r0 ≤ max r0 r3 := le_max_left _ _
              simp [m]; linarith
            have hm3 : r3 < m := by
              have : r3 ≤ max r0 r3 := le_max_right _ _
              simp [m]; linarith
            have hm1 : m < r1 := by simp [m]; linarith [max_lt h01 hgt']
            exact absurd ((hIoo m).1 ⟨hm0, hm1⟩).2 (not_lt_of_gt hm3)
        exact ⟨⟨Entity.atom r0, by simpa using congrArg some hr0,
            by simpa [heq02] using congrArg some hr2⟩,
          ⟨Entity.atom r1, by simpa using congrArg some hr1,
            by simpa [heq13] using congrArg some hr3⟩⟩
      have htr := (F.transfer ψuniq hs_uniq).1 hhold_uniq
      rw [SentenceHolds, starFormula_forallVarsIn, starTerm, holds_forallVarsIn_const] at htr
      let wY : Fin 4 → Entity Y := ![α, β, F.star (Entity.atom a), F.star (Entity.atom b)]
      have hwY : ∀ j : Fin 4, wY j ∈ F.star realEntity := fun j ↦ by
        fin_cases j
        · exact hα
        · exact hβ
        · exact F.mem_star_iff.2 (mem_baseSet_iff.2 ⟨a, rfl⟩)
        · exact F.mem_star_iff.2 (mem_baseSet_iff.2 ⟨b, rfl⟩)
      have hab_star : Entity.kpair (F.star (Entity.atom a)) (F.star (Entity.atom b)) ∈
          F.star realLtRel := by
        rw [← F.star_kpair, F.mem_star_iff, kpair_atom_mem_realLtRel_iff]
        exact hab
      have hEqInt : F.starOpenInterval α β =
          F.starOpenInterval (F.star (Entity.atom a)) (F.star (Entity.atom b)) :=
        hCeq.trans (F.star_openIntervalEntity a b)
      have hres := htr wY hwY
      simp only [starFormula, starTerm_pair, starTerm, Holds] at hres
      obtain ⟨⟨z0, hz0a, hz0b⟩, ⟨z1, hz1a, hz1b⟩⟩ := hres ⟨⟨
        ⟨Entity.kpair α β, F.star realLtRel, by simp [wY, evalUTerm_pair], rfl, hlt⟩,
        ⟨Entity.kpair (F.star (Entity.atom a)) (F.star (Entity.atom b)), F.star realLtRel,
          by simp [wY, evalUTerm_pair], rfl, hab_star⟩⟩,
        ⟨F.star realEntity, rfl, fun x hxR ↦ by
          let env4 : ℕ → Entity Y :=
            Function.update (fun n ↦ if h : n < 4 then wY ⟨n, h⟩ else ∅) 4 x
          have hmem_eq : x ∈ F.starOpenInterval α β ↔
              x ∈ F.starOpenInterval (F.star (Entity.atom a)) (F.star (Entity.atom b)) := by
            rw [hEqInt]
          rw [F.mem_starOpenInterval_iff, F.mem_starOpenInterval_iff] at hmem_eq
          constructor
          · rintro ⟨⟨p1, R1, hp1, hR1, h1⟩, ⟨p2, R2, hp2, hR2, h2⟩⟩
            have u0 : evalUTerm env4 (.var 0) = some α := by simp [env4, wY]
            have u1 : evalUTerm env4 (.var 1) = some β := by simp [env4, wY]
            have u4 : evalUTerm env4 (.var 4) = some x := by simp [env4]
            change evalUTerm env4 _ = _ at hp1 hp2
            rw [evalUTerm_pair, u0, u4] at hp1; rw [evalUTerm_pair, u4, u1] at hp2
            dsimp only at hp1 hp2
            obtain rfl := Option.some.inj hp1; obtain rfl := Option.some.inj hR1
            obtain rfl := Option.some.inj hp2; obtain rfl := Option.some.inj hR2
            obtain ⟨_, h3, h4⟩ := hmem_eq.1 ⟨hxR, h1, h2⟩
            exact ⟨⟨Entity.kpair (F.star (Entity.atom a)) x, F.star realLtRel,
                by simp [wY, evalUTerm_pair], rfl, h3⟩,
              ⟨Entity.kpair x (F.star (Entity.atom b)), F.star realLtRel,
                by simp [wY, evalUTerm_pair], rfl, h4⟩⟩
          · rintro ⟨⟨p1, R1, hp1, hR1, h1⟩, ⟨p2, R2, hp2, hR2, h2⟩⟩
            have u2 : evalUTerm env4 (.var 2) = some (F.star (Entity.atom a)) := by simp [env4, wY]
            have u3 : evalUTerm env4 (.var 3) = some (F.star (Entity.atom b)) := by simp [env4, wY]
            have u4 : evalUTerm env4 (.var 4) = some x := by simp [env4]
            change evalUTerm env4 _ = _ at hp1 hp2
            rw [evalUTerm_pair, u2, u4] at hp1; rw [evalUTerm_pair, u4, u3] at hp2
            dsimp only at hp1 hp2
            obtain rfl := Option.some.inj hp1; obtain rfl := Option.some.inj hR1
            obtain rfl := Option.some.inj hp2; obtain rfl := Option.some.inj hR2
            obtain ⟨_, h3, h4⟩ := hmem_eq.2 ⟨hxR, h1, h2⟩
            exact ⟨⟨Entity.kpair α x, F.star realLtRel,
                by simp [wY, evalUTerm_pair], rfl, h3⟩,
              ⟨Entity.kpair x β, F.star realLtRel,
                by simp [wY, evalUTerm_pair], rfl, h4⟩⟩⟩⟩
      have hα_eq : α = F.star (Entity.atom a) :=
        (Option.some.inj (by simpa [wY] using hz0a)).trans
          (Option.some.inj (by simpa [wY] using hz0b)).symm
      have hβ_eq : β = F.star (Entity.atom b) :=
        (Option.some.inj (by simpa [wY] using hz1a)).trans
          (Option.some.inj (by simpa [wY] using hz1b)).symm
      exact ⟨⟨Entity.atom a, hα_eq⟩, ⟨Entity.atom b, hβ_eq⟩⟩
    · exact Or.inl ((F.star_real_trichotomy hα hβ).2 hlt)
  · rintro (hle | ⟨_, ⟨ea, rfl⟩, ⟨eb, rfl⟩⟩)
    · have hnlt : ¬ Entity.kpair α β ∈ F.star realLtRel :=
        (F.star_real_trichotomy hα hβ).1 hle
      have hemp : F.starOpenInterval α β = ∅ := by
        refine (Entity.eq_empty_iff_forall_not_mem (Entity.isSet_setOfBounded _)).2 fun x hx ↦ ?_
        exact hnlt (hnonempty_iff.2 ⟨x, hx⟩)
      rw [hemp]
      exact F.isStandard_empty
    · obtain ⟨a, rfl⟩ := mem_baseSet_iff.1 ((F.mem_star_iff).1 hα)
      obtain ⟨b, rfl⟩ := mem_baseSet_iff.1 ((F.mem_star_iff).1 hβ)
      rw [← F.star_openIntervalEntity a b]
      exact F.isStandard_star _

/-! ## §13.10 Internal Entities, Strong Transitivity of `*𝕌`, and Uniform Partitions -/

/-- Goldblatt §13.10 (p. 172): An entity `b : Entity Y` in `𝕌'` is **internal** if `b ∈ *A` for some
standard set `A : Entity X` in `𝕌`. -/
def Framework.IsInternalEntity {X Y : Type*} (F : Framework X Y) (b : Entity Y) : Prop :=
  ∃ A : Entity X, b ∈ F.star A

/-- Goldblatt §13.10 (p. 173): An entity `b : Entity Y` in `𝕌'` is **external** if it is not
internal (`b ∉ *A` for every `A : Entity X`). -/
def Framework.IsExternalEntity {X Y : Type*} (F : Framework X Y) (b : Entity Y) : Prop :=
  ¬ F.IsInternalEntity b

/-- Goldblatt §13.10 (p. 172): The collection `*𝕌 = {b ∈ 𝕌' : b is internal}` of all internal
entities. -/
def Framework.internalUniverse {X Y : Type*} (F : Framework X Y) : Set (Entity Y) :=
  {b : Entity Y | F.IsInternalEntity b}

/-- Membership in `F.internalUniverse` is `F.IsInternalEntity` (Goldblatt §13.10, p. 172). -/
@[simp]
theorem Framework.mem_internalUniverse_iff {X Y : Type*} (F : Framework X Y) {b : Entity Y} :
    b ∈ F.internalUniverse ↔ F.IsInternalEntity b := Iff.rfl

/-- Goldblatt §13.10 (p. 172): **Every standard entity is internal**, because `*a ∈ *{a}`! -/
theorem Framework.IsStandard.isInternalEntity {X Y : Type*} {F : Framework X Y} {b : Entity Y}
    (hb : F.IsStandard b) : F.IsInternalEntity b := by
  obtain ⟨a, rfl⟩ := hb
  exact ⟨Entity.singleton a, F.mem_star_iff.2 (Entity.mem_singleton_iff.2 rfl)⟩

/-- `F.star a` is always internal (Goldblatt §13.10, p. 173). -/
@[simp]
theorem Framework.isInternalEntity_star {X Y : Type*} (F : Framework X Y) (a : Entity X) :
    F.IsInternalEntity (F.star a) :=
  (F.isStandard_star a).isInternalEntity

/-- `∅ : Entity Y` is internal (Goldblatt §13.10, p. 173). -/
@[simp]
theorem Framework.isInternalEntity_empty {X Y : Type*} (F : Framework X Y) :
    F.IsInternalEntity (∅ : Entity Y) :=
  F.isStandard_empty.isInternalEntity

/-- Every finite family `w : ι → Entity Y` (over `[Finite ι]`) of internal entities belongs to a
**single** transitive standard set `F.star T` (specifically `T = vStageEntity X (N + 1)`;
Goldblatt §13.10, Theorem 13.10.1 & §13.15, pp. 173, 177). -/
theorem Framework.exists_common_star_transitiveSet {X Y : Type*} (F : Framework X Y)
    {ι : Type*} [Fintype ι] {w : ι → Entity Y} (hw : ∀ i : ι, F.IsInternalEntity (w i)) :
    ∃ T : Entity X, T.IsTransitiveSet ∧ (F.star T).IsTransitiveSet ∧
      ∀ i : ι, w i ∈ F.star T := by
  let B : ι → Entity X := fun i ↦ (hw i).choose
  let N : ℕ := Finset.univ.sup fun i : ι ↦ (B i).rank
  refine ⟨vStageEntity X (N + 1), isTransitiveSet_vStageEntity_succ X N,
    (F.isTransitiveSet_star_iff).2 (isTransitiveSet_vStageEntity_succ X N), fun i ↦ ?_⟩
  have hsub : ∀ z ∈ B i, z ∈ vStageEntity X (N + 1) := fun z hz ↦ by
    have hlt : z.rank < (B i).rank := Entity.rank_lt_of_mem hz
    have hle : (B i).rank ≤ N := Finset.le_sup (f := fun j : ι ↦ (B j).rank) (Finset.mem_univ i)
    exact mem_vStageEntity.2 (mem_vStage_iff_rank_le.2 (by omega))
  exact (F.subset_star_iff.2 hsub) _ (hw i).choose_spec

/-- Goldblatt **Theorem 13.10.1 (Part 1)** (p. 173): Any internal entity `A` belongs to `*T` for
some transitive standard set `T ∈ 𝕌` (with `*T` also transitive). -/
theorem Framework.exists_mem_star_transitiveSet_of_isInternalEntity {X Y : Type*}
    (F : Framework X Y) {A : Entity Y} (hA : F.IsInternalEntity A) :
    ∃ T : Entity X, T.IsTransitiveSet ∧ (F.star T).IsTransitiveSet ∧ A ∈ F.star T := by
  obtain ⟨T, hT1, hT2, hmem⟩ :=
    F.exists_common_star_transitiveSet (w := fun _ : Unit ↦ A) (fun _ ↦ hA)
  exact ⟨T, hT1, hT2, hmem ()⟩

/-- Goldblatt **Theorem 13.10.1 (Part 2)** (p. 173): The collection `*𝕌` (`F.internalUniverse`) of
all internal entities is **strongly transitive**! -/
theorem Framework.isStronglyTransitive_internalUniverse {X Y : Type*} (F : Framework X Y) :
    IsStronglyTransitive F.internalUniverse := by
  intro A hAU _
  obtain ⟨T, _, hstarT, hAT⟩ := F.exists_mem_star_transitiveSet_of_isInternalEntity hAU
  exact ⟨F.star T, F.isInternalEntity_star T, hstarT,
    fun z hz ↦ hstarT.2 A hAT z hz,
    fun z hz ↦ ⟨T, hz⟩⟩

/-- Goldblatt **Theorem 13.10.1 (Part 3)** (p. 173): **Every member of an internal set is
internal** (`a ∈ B → F.IsInternalEntity B → F.IsInternalEntity a`). -/
theorem Framework.IsInternalEntity.of_mem {X Y : Type*} {F : Framework X Y} {a B : Entity Y}
    (haB : a ∈ B) (hB : F.IsInternalEntity B) : F.IsInternalEntity a :=
  F.isStronglyTransitive_internalUniverse.isTransitiveCollection haB hB

/-- Every initial segment `F.initSeg N` (`N ∈ *ℕ₀`) is internal (Goldblatt §13.10, p. 173). -/
theorem Framework.isInternalEntity_initSeg {Y : Type*} (F : Framework ℝ Y) {N : Entity Y}
    (hN : N ∈ F.star nat0Entity) :
    F.IsInternalEntity (F.initSeg N) :=
  ⟨Entity.finPowerset posNatEntity, F.initSeg_mem_star_finPowerset hN⟩

/-- Every hyperreal open interval `(α, β)` (`α, β ∈ *ℝ`) is internal (Goldblatt §13.10, p. 173). -/
theorem Framework.isInternalEntity_starOpenInterval {Y : Type*} (F : Framework ℝ Y)
    {α β : Entity Y} (hα : α ∈ F.star realEntity) (hβ : β ∈ F.star realEntity) :
    F.IsInternalEntity (F.starOpenInterval α β) :=
  ⟨openIntervalsCollection,
    (F.mem_star_openIntervalsCollection_iff).2 ⟨α, hα, β, hβ, rfl⟩⟩

/-- Uniform partition `{a + k (b - a) / n : k ∈ ℤ, 0 ≤ k ≤ n}` of `[a, b]` into `n` equal pieces
as an entity in `Entity ℝ` (Goldblatt §13.10, p. 173). -/
def uniformPartitionStd (a b : ℝ) (n : ℕ) : Entity ℝ :=
  mkAtomSet {x : ℝ | ∃ k : ℤ, 0 ≤ k ∧ k ≤ (n : ℤ) ∧ x = a + (k : ℝ) * ((b - a) / (n : ℝ))}

/-- Each `uniformPartitionStd a b n` belongs to `Entity.finPowerset realEntity` (and hence
`Entity.powerset realEntity`; Goldblatt §13.10, p. 173). -/
theorem uniformPartitionStd_mem_finPowerset (a b : ℝ) (n : ℕ) :
    uniformPartitionStd a b n ∈ Entity.finPowerset realEntity := by
  rw [Entity.mem_finPowerset_iff]
  refine ⟨Entity.isSet_setOfBounded _, ?_, ?_⟩
  · intro z hz
    obtain ⟨r, _, rfl⟩ := mem_mkAtomSet_iff.1 hz
    exact mem_baseSet_iff.2 ⟨r, rfl⟩
  · have hsub : (uniformPartitionStd a b n).extSet ⊆
        (fun k : ℤ ↦ Entity.atom (a + (k : ℝ) * ((b - a) / (n : ℝ)))) ''
          (Finset.Icc (0 : ℤ) (n : ℤ) : Set ℤ) := by
      intro z hz
      obtain ⟨x, ⟨k, hk0, hkn, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 hz
      exact ⟨k, Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨hk0, hkn⟩), rfl⟩
    exact ((Finset.finite_toSet (Finset.Icc (0 : ℤ) (n : ℤ))).image _).subset hsub

/-- Standard function `((a, b), n) ↦ P^n_{[a, b]}` from `(ℝ × ℝ) × ℕ` to `𝒫_F(ℝ)`
(Goldblatt §13.10, p. 173). -/
def uniformPartitionMap : Entity ℝ :=
  Entity.mkFuncEntity (Entity.prod (Entity.prod realEntity realEntity) posNatEntity) (fun q ↦
    let ab := Entity.pairFirst q
    let en := Entity.pairSecond q
    uniformPartitionStd
      (Entity.atomVal 0 (Entity.pairFirst ab))
      (Entity.atomVal 0 (Entity.pairSecond ab))
      (Nat.floor (Entity.atomVal 1 en)))

/-- `uniformPartitionMap` maps `(realEntity × realEntity) × posNatEntity` into
`Entity.finPowerset realEntity`. -/
theorem isFuncFromTo_uniformPartitionMap :
    Entity.IsFuncFromTo uniformPartitionMap
      (Entity.prod (Entity.prod realEntity realEntity) posNatEntity)
      (Entity.finPowerset realEntity) :=
  Entity.isFuncFromTo_mkFuncEntity fun _ _ ↦ uniformPartitionStd_mem_finPowerset _ _ _

/-- Goldblatt §13.10 (p. 173): Hyperfinite uniform partition
`P^N_{[a, b]} = {a + k (b - a) / N : k ∈ *ℤ, 0 ≤ k ≤ N}` for `a, b ∈ *ℝ` and `N ∈ *ℕ`. -/
def Framework.uniformPartition {Y : Type*} (F : Framework ℝ Y) (a b N : Entity Y) : Entity Y :=
  Entity.funcApp (F.star uniformPartitionMap) (Entity.kpair (Entity.kpair a b) N)

/-- Goldblatt §13.10 (p. 173): Every uniform partition `P^N_{[a, b]}` (`a, b ∈ *ℝ`, `N ∈ *ℕ`)
belongs to `*𝒫_F(ℝ) ⊆ *𝒫(ℝ) ⊆ 𝒫(*ℝ)` and is therefore an internal (indeed hyperfinite) subset of
`*ℝ`! -/
theorem Framework.uniformPartition_mem_star_finPowerset {Y : Type*} (F : Framework ℝ Y)
    {a b N : Entity Y} (ha : a ∈ F.star realEntity) (hb : b ∈ F.star realEntity)
    (hN : N ∈ F.star posNatEntity) :
    F.uniformPartition a b N ∈ F.star (Entity.finPowerset realEntity) := by
  have hf := (F.isFuncFromTo_star_iff).2 isFuncFromTo_uniformPartitionMap
  have hp : Entity.kpair (Entity.kpair a b) N ∈
      F.star (Entity.prod (Entity.prod realEntity realEntity) posNatEntity) := by
    rw [F.star_prod, F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨Entity.kpair_mem_prod_iff.2 ⟨ha, hb⟩, hN⟩
  have hdom : Entity.kpair (Entity.kpair a b) N ∈
      Entity.relDom (F.star uniformPartitionMap) := by
    rw [hf.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _))]
    exact hp
  exact hf.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hdom⟩)

/-- Every uniform partition `P^N_{[a, b]}` is an internal entity (Goldblatt §13.10, p. 173). -/
theorem Framework.isInternalEntity_uniformPartition {Y : Type*} (F : Framework ℝ Y)
    {a b N : Entity Y} (ha : a ∈ F.star realEntity) (hb : b ∈ F.star realEntity)
    (hN : N ∈ F.star posNatEntity) :
    F.IsInternalEntity (F.uniformPartition a b N) :=
  ⟨Entity.finPowerset realEntity, F.uniformPartition_mem_star_finPowerset ha hb hN⟩

/-! ## §13.11 & §13.15 Core: Internal Formula Abstraction and Comprehension -/

/-- List of all entity constants occurring in an `ℒ_{𝕌'}`-term (Goldblatt §13.15, p. 177). -/
def constsUTerm {Y : Type*} : UTerm Y → List (Entity Y)
  | .var _ => []
  | .const c => [c]
  | .tuple (m := m) _ args => (List.finRange m).flatMap fun j ↦ constsUTerm (args j)
  | .app fn arg => constsUTerm fn ++ constsUTerm arg

/-- List of all entity constants occurring in an `ℒ_{𝕌'}`-formula (Goldblatt §13.15, p. 177). -/
def constsUFormula {Y : Type*} : UFormula Y → List (Entity Y)
  | .eq t₁ t₂ => constsUTerm t₁ ++ constsUTerm t₂
  | .mem t₁ t₂ => constsUTerm t₁ ++ constsUTerm t₂
  | .conj φ ψ => constsUFormula φ ++ constsUFormula ψ
  | .disj φ ψ => constsUFormula φ ++ constsUFormula ψ
  | .neg φ => constsUFormula φ
  | .imp φ ψ => constsUFormula φ ++ constsUFormula ψ
  | .iff φ ψ => constsUFormula φ ++ constsUFormula ψ
  | .forallIn _ dom body => constsUTerm dom ++ constsUFormula body
  | .existsIn _ dom body => constsUTerm dom ++ constsUFormula body

/-- Goldblatt §13.15 & §13.16 (pp. 177–178): An `ℒ_{𝕌'}`-term is **internal** if every constant
occurring in it is an internal entity. -/
def UTerm.AllConstsInternal {X Y : Type*} (F : Framework X Y) (t : UTerm Y) : Prop :=
  ∀ c ∈ constsUTerm t, F.IsInternalEntity c

/-- Goldblatt §13.15 (p. 177): An `ℒ_{𝕌'}`-formula is **internal** if every constant occurring in it
is an internal entity. -/
def UFormula.AllConstsInternal {X Y : Type*} (F : Framework X Y) (ψ : UFormula Y) : Prop :=
  ∀ c ∈ constsUFormula ψ, F.IsInternalEntity c

/-- Variable terms always have internal constants. -/
@[simp]
theorem UTerm.allConstsInternal_var {X Y : Type*} (F : Framework X Y) (v : ℕ) :
    (UTerm.var v : UTerm Y).AllConstsInternal F := by
  simp [UTerm.AllConstsInternal, constsUTerm]

/-- A constant term `.const c` is internal iff `c` is internal. -/
@[simp]
theorem UTerm.allConstsInternal_const {X Y : Type*} (F : Framework X Y) (c : Entity Y) :
    (UTerm.const c).AllConstsInternal F ↔ F.IsInternalEntity c := by
  simp [UTerm.AllConstsInternal, constsUTerm]

/-- `UTerm.tuple` is internal iff each argument term is internal. -/
@[simp]
theorem UTerm.allConstsInternal_tuple {X Y : Type*} (F : Framework X Y) {m : ℕ} (hm : 2 ≤ m)
    (args : Fin m → UTerm Y) :
    (UTerm.tuple hm args).AllConstsInternal F ↔ ∀ j : Fin m, (args j).AllConstsInternal F := by
  simp only [UTerm.AllConstsInternal, constsUTerm, List.mem_flatMap, List.mem_finRange, true_and]
  exact ⟨fun h j c hc ↦ h c ⟨j, hc⟩, fun h c ⟨j, hc⟩ ↦ h j c hc⟩

/-- `UTerm.pair` is internal iff both subterms are internal. -/
@[simp]
theorem UTerm.allConstsInternal_pair {X Y : Type*} (F : Framework X Y) (t₁ t₂ : UTerm Y) :
    (UTerm.pair t₁ t₂).AllConstsInternal F ↔
      t₁.AllConstsInternal F ∧ t₂.AllConstsInternal F := by
  rw [UTerm.pair, UTerm.allConstsInternal_tuple]
  exact ⟨fun h ↦ ⟨h 0, h 1⟩, fun ⟨h1, h2⟩ j ↦ by fin_cases j <;> assumption⟩

/-- `UTerm.app` is internal iff both function and argument terms are internal. -/
@[simp]
theorem UTerm.allConstsInternal_app {X Y : Type*} (F : Framework X Y) (fn arg : UTerm Y) :
    (UTerm.app fn arg).AllConstsInternal F ↔
      fn.AllConstsInternal F ∧ arg.AllConstsInternal F := by
  simp only [UTerm.AllConstsInternal, constsUTerm, List.mem_append]
  exact ⟨fun h ↦ ⟨fun c hc ↦ h c (Or.inl hc), fun c hc ↦ h c (Or.inr hc)⟩,
    fun ⟨h1, h2⟩ c hc ↦ hc.elim (h1 c) (h2 c)⟩

/-- `UFormula.eq` is internal iff both subterms are internal. -/
@[simp]
theorem UFormula.allConstsInternal_eq {X Y : Type*} (F : Framework X Y) (t₁ t₂ : UTerm Y) :
    (UFormula.eq t₁ t₂).AllConstsInternal F ↔
      t₁.AllConstsInternal F ∧ t₂.AllConstsInternal F := by
  simp only [UFormula.AllConstsInternal, UTerm.AllConstsInternal, constsUFormula, List.mem_append]
  exact ⟨fun h ↦ ⟨fun c hc ↦ h c (Or.inl hc), fun c hc ↦ h c (Or.inr hc)⟩,
    fun ⟨h1, h2⟩ c hc ↦ hc.elim (h1 c) (h2 c)⟩

/-- `UFormula.mem` is internal iff both subterms are internal. -/
@[simp]
theorem UFormula.allConstsInternal_mem {X Y : Type*} (F : Framework X Y) (t₁ t₂ : UTerm Y) :
    (UFormula.mem t₁ t₂).AllConstsInternal F ↔
      t₁.AllConstsInternal F ∧ t₂.AllConstsInternal F := by
  simp only [UFormula.AllConstsInternal, UTerm.AllConstsInternal, constsUFormula, List.mem_append]
  exact ⟨fun h ↦ ⟨fun c hc ↦ h c (Or.inl hc), fun c hc ↦ h c (Or.inr hc)⟩,
    fun ⟨h1, h2⟩ c hc ↦ hc.elim (h1 c) (h2 c)⟩

/-- `UFormula.conj` is internal iff both conjuncts are internal. -/
@[simp]
theorem UFormula.allConstsInternal_conj {X Y : Type*} (F : Framework X Y) (φ ψ : UFormula Y) :
    (UFormula.conj φ ψ).AllConstsInternal F ↔
      φ.AllConstsInternal F ∧ ψ.AllConstsInternal F := by
  simp only [UFormula.AllConstsInternal, constsUFormula, List.mem_append]
  exact ⟨fun h ↦ ⟨fun c hc ↦ h c (Or.inl hc), fun c hc ↦ h c (Or.inr hc)⟩,
    fun ⟨h1, h2⟩ c hc ↦ hc.elim (h1 c) (h2 c)⟩

/-- `UFormula.disj` is internal iff both disjuncts are internal. -/
@[simp]
theorem UFormula.allConstsInternal_disj {X Y : Type*} (F : Framework X Y) (φ ψ : UFormula Y) :
    (UFormula.disj φ ψ).AllConstsInternal F ↔
      φ.AllConstsInternal F ∧ ψ.AllConstsInternal F := by
  simp only [UFormula.AllConstsInternal, constsUFormula, List.mem_append]
  exact ⟨fun h ↦ ⟨fun c hc ↦ h c (Or.inl hc), fun c hc ↦ h c (Or.inr hc)⟩,
    fun ⟨h1, h2⟩ c hc ↦ hc.elim (h1 c) (h2 c)⟩

/-- `UFormula.neg` is internal iff the negated formula is internal. -/
@[simp]
theorem UFormula.allConstsInternal_neg {X Y : Type*} (F : Framework X Y) (φ : UFormula Y) :
    (UFormula.neg φ).AllConstsInternal F ↔ φ.AllConstsInternal F := Iff.rfl

/-- `UFormula.imp` is internal iff both antecedent and consequent are internal. -/
@[simp]
theorem UFormula.allConstsInternal_imp {X Y : Type*} (F : Framework X Y) (φ ψ : UFormula Y) :
    (UFormula.imp φ ψ).AllConstsInternal F ↔
      φ.AllConstsInternal F ∧ ψ.AllConstsInternal F := by
  simp only [UFormula.AllConstsInternal, constsUFormula, List.mem_append]
  exact ⟨fun h ↦ ⟨fun c hc ↦ h c (Or.inl hc), fun c hc ↦ h c (Or.inr hc)⟩,
    fun ⟨h1, h2⟩ c hc ↦ hc.elim (h1 c) (h2 c)⟩

/-- `UFormula.iff` is internal iff both sides are internal. -/
@[simp]
theorem UFormula.allConstsInternal_iff {X Y : Type*} (F : Framework X Y) (φ ψ : UFormula Y) :
    (UFormula.iff φ ψ).AllConstsInternal F ↔
      φ.AllConstsInternal F ∧ ψ.AllConstsInternal F := by
  simp only [UFormula.AllConstsInternal, constsUFormula, List.mem_append]
  exact ⟨fun h ↦ ⟨fun c hc ↦ h c (Or.inl hc), fun c hc ↦ h c (Or.inr hc)⟩,
    fun ⟨h1, h2⟩ c hc ↦ hc.elim (h1 c) (h2 c)⟩

/-- `UFormula.forallIn` is internal iff its bounding term and body are internal. -/
@[simp]
theorem UFormula.allConstsInternal_forallIn {X Y : Type*} (F : Framework X Y) (v : ℕ)
    (dom : UTerm Y) (body : UFormula Y) :
    (UFormula.forallIn v dom body).AllConstsInternal F ↔
      dom.AllConstsInternal F ∧ body.AllConstsInternal F := by
  simp only [UFormula.AllConstsInternal, UTerm.AllConstsInternal, constsUFormula, List.mem_append]
  exact ⟨fun h ↦ ⟨fun c hc ↦ h c (Or.inl hc), fun c hc ↦ h c (Or.inr hc)⟩,
    fun ⟨h1, h2⟩ c hc ↦ hc.elim (h1 c) (h2 c)⟩

/-- `UFormula.existsIn` is internal iff its bounding term and body are internal. -/
@[simp]
theorem UFormula.allConstsInternal_existsIn {X Y : Type*} (F : Framework X Y) (v : ℕ)
    (dom : UTerm Y) (body : UFormula Y) :
    (UFormula.existsIn v dom body).AllConstsInternal F ↔
      dom.AllConstsInternal F ∧ body.AllConstsInternal F := by
  simp only [UFormula.AllConstsInternal, UTerm.AllConstsInternal, constsUFormula, List.mem_append]
  exact ⟨fun h ↦ ⟨fun c hc ↦ h c (Or.inl hc), fun c hc ↦ h c (Or.inr hc)⟩,
    fun ⟨h1, h2⟩ c hc ↦ hc.elim (h1 c) (h2 c)⟩

/-- Constant-abstracting translation of an `ℒ_{𝕌'}`-term into a constant-free `ℒ_𝕌`-term: every
constant `c` is replaced by `.var (idxOf c)` (`< k`) while every variable `v` is shifted up to
`k + v` so no quantifier in a formula ever collides with constant variables (Goldblatt §13.15,
p. 177). -/
def abstractUTerm (X : Type*) {Y : Type*} {k : ℕ} (idxOf : Entity Y → Fin k) :
    UTerm Y → UTerm X
  | .var v => .var (k + v)
  | .const c => .var (idxOf c).1
  | .tuple hm args => .tuple hm fun j ↦ abstractUTerm X idxOf (args j)
  | .app fn arg => .app (abstractUTerm X idxOf fn) (abstractUTerm X idxOf arg)

/-- Constant-abstracting translation of an `ℒ_{𝕌'}`-formula into a constant-free `ℒ_𝕌`-formula
(Goldblatt §13.15, p. 177). -/
def abstractUFormula (X : Type*) {Y : Type*} {k : ℕ} (idxOf : Entity Y → Fin k) :
    UFormula Y → UFormula X
  | .eq t₁ t₂ => .eq (abstractUTerm X idxOf t₁) (abstractUTerm X idxOf t₂)
  | .mem t₁ t₂ => .mem (abstractUTerm X idxOf t₁) (abstractUTerm X idxOf t₂)
  | .conj φ ψ => .conj (abstractUFormula X idxOf φ) (abstractUFormula X idxOf ψ)
  | .disj φ ψ => .disj (abstractUFormula X idxOf φ) (abstractUFormula X idxOf ψ)
  | .neg φ => .neg (abstractUFormula X idxOf φ)
  | .imp φ ψ => .imp (abstractUFormula X idxOf φ) (abstractUFormula X idxOf ψ)
  | .iff φ ψ => .iff (abstractUFormula X idxOf φ) (abstractUFormula X idxOf ψ)
  | .forallIn v dom body =>
      .forallIn (k + v) (abstractUTerm X idxOf dom) (abstractUFormula X idxOf body)
  | .existsIn v dom body =>
      .existsIn (k + v) (abstractUTerm X idxOf dom) (abstractUFormula X idxOf body)

/-- Since `abstractUTerm X idxOf t` contains no constants, its `*-transform` is `abstractUTerm Y`
(Goldblatt §13.15, p. 177). -/
@[simp]
theorem starTerm_abstractUTerm {X Y : Type*} (star : Entity X → Entity Y) {k : ℕ}
    (idxOf : Entity Y → Fin k) :
    ∀ t : UTerm Y, starTerm star (abstractUTerm X idxOf t) = abstractUTerm Y idxOf t
  | .var _ => rfl
  | .const _ => rfl
  | .tuple _ args => by
      simp only [abstractUTerm, starTerm]
      congr 1; funext j; exact starTerm_abstractUTerm star idxOf (args j)
  | .app fn arg => by
      simp [abstractUTerm, starTerm, starTerm_abstractUTerm star idxOf fn,
        starTerm_abstractUTerm star idxOf arg]

/-- Since `abstractUFormula X idxOf ψ` contains no constants, its `*-transform` is
`abstractUFormula Y idxOf ψ` (Goldblatt §13.15, p. 177: "has no constants, hence is an `ℒ_𝕌`-formula
and is equal to its own `*-transform`"). -/
@[simp]
theorem starFormula_abstractUFormula {X Y : Type*} (star : Entity X → Entity Y) {k : ℕ}
    (idxOf : Entity Y → Fin k) :
    ∀ ψ : UFormula Y, starFormula star (abstractUFormula X idxOf ψ) = abstractUFormula Y idxOf ψ
  | .eq _ _ => by simp [abstractUFormula]
  | .mem _ _ => by simp [abstractUFormula]
  | .conj φ ψ => by
      simp [abstractUFormula, starFormula_abstractUFormula star idxOf φ,
        starFormula_abstractUFormula star idxOf ψ]
  | .disj φ ψ => by
      simp [abstractUFormula, starFormula_abstractUFormula star idxOf φ,
        starFormula_abstractUFormula star idxOf ψ]
  | .neg φ => by simp [abstractUFormula, starFormula_abstractUFormula star idxOf φ]
  | .imp φ ψ => by
      simp [abstractUFormula, starFormula_abstractUFormula star idxOf φ,
        starFormula_abstractUFormula star idxOf ψ]
  | .iff φ ψ => by
      simp [abstractUFormula, starFormula_abstractUFormula star idxOf φ,
        starFormula_abstractUFormula star idxOf ψ]
  | .forallIn _ _ body => by
      simp [abstractUFormula, starFormula_abstractUFormula star idxOf body]
  | .existsIn _ _ body => by
      simp [abstractUFormula, starFormula_abstractUFormula star idxOf body]

/-- Every free variable of `abstractUTerm` is either `< k` or `k + u` for a free variable `u` of the
original term. -/
theorem freeVarsUTerm_abstractUTerm {X Y : Type*} {k : ℕ} (idxOf : Entity Y → Fin k) :
    ∀ {t : UTerm Y} {v : ℕ},
      v ∈ freeVarsUTerm (abstractUTerm X idxOf t) →
        v < k ∨ ∃ u ∈ freeVarsUTerm t, v = k + u
  | .var u, v, hv => by
      simp only [abstractUTerm, freeVarsUTerm, Finset.mem_singleton] at hv
      exact Or.inr ⟨u, Finset.mem_singleton_self u, hv⟩
  | .const c, v, hv => by
      simp only [abstractUTerm, freeVarsUTerm, Finset.mem_singleton] at hv
      exact Or.inl (hv ▸ (idxOf c).2)
  | .tuple _ args, v, hv => by
      simp only [abstractUTerm, freeVarsUTerm, Finset.mem_biUnion, Finset.mem_univ, true_and] at hv ⊢
      obtain ⟨j, hj⟩ := hv
      rcases freeVarsUTerm_abstractUTerm idxOf hj with hlt | ⟨u, hu, rfl⟩
      · exact Or.inl hlt
      · exact Or.inr ⟨u, ⟨j, hu⟩, rfl⟩
  | .app fn arg, v, hv => by
      simp only [abstractUTerm, freeVarsUTerm, Finset.mem_union] at hv ⊢
      rcases hv with hfn | harg
      · rcases freeVarsUTerm_abstractUTerm idxOf hfn with hlt | ⟨u, hu, rfl⟩
        · exact Or.inl hlt
        · exact Or.inr ⟨u, Or.inl hu, rfl⟩
      · rcases freeVarsUTerm_abstractUTerm idxOf harg with hlt | ⟨u, hu, rfl⟩
        · exact Or.inl hlt
        · exact Or.inr ⟨u, Or.inr hu, rfl⟩

/-- Every free variable of `abstractUFormula` is either `< k` or `k + u` for a free variable `u` of
the original formula. -/
theorem freeVarsUFormula_abstractUFormula {X Y : Type*} {k : ℕ} (idxOf : Entity Y → Fin k) :
    ∀ {ψ : UFormula Y} {v : ℕ},
      v ∈ freeVarsUFormula (abstractUFormula X idxOf ψ) →
        v < k ∨ ∃ u ∈ freeVarsUFormula ψ, v = k + u
  | .eq _ _, _, hv | .mem _ _, _, hv => by
      simp only [abstractUFormula, freeVarsUFormula, Finset.mem_union] at hv ⊢
      rcases hv with h1 | h2
      · rcases freeVarsUTerm_abstractUTerm idxOf h1 with hlt | ⟨u, hu, rfl⟩
        · exact Or.inl hlt
        · exact Or.inr ⟨u, Or.inl hu, rfl⟩
      · rcases freeVarsUTerm_abstractUTerm idxOf h2 with hlt | ⟨u, hu, rfl⟩
        · exact Or.inl hlt
        · exact Or.inr ⟨u, Or.inr hu, rfl⟩
  | .conj _ _, _, hv | .disj _ _, _, hv | .imp _ _, _, hv | .iff _ _, _, hv => by
      simp only [abstractUFormula, freeVarsUFormula, Finset.mem_union] at hv ⊢
      rcases hv with h1 | h2
      · rcases freeVarsUFormula_abstractUFormula idxOf h1 with hlt | ⟨u, hu, rfl⟩
        · exact Or.inl hlt
        · exact Or.inr ⟨u, Or.inl hu, rfl⟩
      · rcases freeVarsUFormula_abstractUFormula idxOf h2 with hlt | ⟨u, hu, rfl⟩
        · exact Or.inl hlt
        · exact Or.inr ⟨u, Or.inr hu, rfl⟩
  | .neg φ, _, hv => freeVarsUFormula_abstractUFormula idxOf (ψ := φ) hv
  | .forallIn q _ _, _, hv | .existsIn q _ _, _, hv => by
      simp only [abstractUFormula, freeVarsUFormula, Finset.mem_union, Finset.mem_erase] at hv ⊢
      rcases hv with hdom | ⟨hne, hbody⟩
      · rcases freeVarsUTerm_abstractUTerm idxOf hdom with hlt | ⟨u, hu, rfl⟩
        · exact Or.inl hlt
        · exact Or.inr ⟨u, Or.inl hu, rfl⟩
      · rcases freeVarsUFormula_abstractUFormula idxOf hbody with hlt | ⟨u, hu, rfl⟩
        · exact Or.inl hlt
        · exact Or.inr ⟨u, Or.inr ⟨by omega, hu⟩, rfl⟩

/-- Combined environment placing `w : Fin k → Entity Y` in slots `0, …, k - 1` and `env (n - k)` in
slots `n ≥ k` (Goldblatt §13.15, p. 177). -/
def combineEnv {Y : Type*} {k : ℕ} (w : Fin k → Entity Y) (env : ℕ → Entity Y) : ℕ → Entity Y :=
  fun n ↦ if h : n < k then w ⟨n, h⟩ else env (n - k)

/-- Updating `combineEnv w env` at `k + v` commutes identically with `combineEnv w`. -/
@[simp]
theorem combineEnv_update_add {Y : Type*} {k : ℕ} (w : Fin k → Entity Y) (env : ℕ → Entity Y)
    (v : ℕ) (a : Entity Y) :
    Function.update (combineEnv w env) (k + v) a = combineEnv w (Function.update env v a) := by
  ext n
  by_cases hnk : n < k
  · have hne : n ≠ k + v := by omega
    simp [combineEnv, hnk, hne]
  · by_cases heq : n = k + v
    · subst heq
      have hsub : (k + v) - k = v := by omega
      simp [combineEnv, hnk, hsub]
    · have hne : n - k ≠ v := by omega
      simp [combineEnv, hnk, heq, hne]

/-- Term evaluation of `abstractUTerm Y idxOf t` under `combineEnv w env` equals `evalUTerm env t`
whenever `w (idxOf c) = c` for all constants `c` of `t`. -/
theorem evalUTerm_abstractUTerm {Y : Type*} {k : ℕ} {idxOf : Entity Y → Fin k}
    {w : Fin k → Entity Y} :
    ∀ {t : UTerm Y} {env : ℕ → Entity Y},
      (∀ c ∈ constsUTerm t, w (idxOf c) = c) →
        evalUTerm (combineEnv w env) (abstractUTerm Y idxOf t) = evalUTerm env t
  | .var v, env, _ => by
      have hnk : ¬ (k + v < k) := by omega
      have hsub : (k + v) - k = v := by omega
      simp [abstractUTerm, combineEnv, hnk, hsub]
  | .const c, _, hw => by
      have hc : w (idxOf c) = c := hw c (by simp [constsUTerm])
      simp [abstractUTerm, combineEnv, (idxOf c).2, hc]
  | .tuple hm args, env, hw => by
      have hargs : ∀ j,
          evalUTerm (combineEnv w env) (abstractUTerm Y idxOf (args j)) =
            evalUTerm env (args j) := fun j ↦
        evalUTerm_abstractUTerm fun c hc ↦
          hw c (by simp only [constsUTerm, List.mem_flatMap, List.mem_finRange, true_and]; exact ⟨j, hc⟩)
      have hiff : (∀ j, (evalUTerm (combineEnv w env) (abstractUTerm Y idxOf (args j))).isSome) ↔
          (∀ j, (evalUTerm env (args j)).isSome) :=
        forall_congr' fun j ↦ by rw [hargs j]
      simp only [abstractUTerm]
      rw [evalUTerm.eq_3, evalUTerm.eq_3]
      split_ifs
      · apply congrArg some; apply congrArg Entity.ktuple; ext j
        exact Option.some.inj (by rw [Option.some_get, Option.some_get, hargs j])
      · exact absurd (hiff.1 ‹_›) ‹_›
      · exact absurd (hiff.2 ‹_›) ‹_›
      · rfl
  | .app fn arg, env, hw => by
      have hfn := evalUTerm_abstractUTerm (t := fn) (env := env) fun c hc ↦
        hw c (by simp [constsUTerm, hc])
      have harg := evalUTerm_abstractUTerm (t := arg) (env := env) fun c hc ↦
        hw c (by simp [constsUTerm, hc])
      simp only [abstractUTerm]
      rw [evalUTerm.eq_4, evalUTerm.eq_4, hfn, harg]

/-- Formula satisfaction of `abstractUFormula Y idxOf ψ` under `combineEnv w env` coincides with
`Holds env ψ` whenever `w (idxOf c) = c` for all constants `c` of `ψ` (Goldblatt §13.15, p. 177). -/
theorem holds_abstractUFormula {Y : Type*} {k : ℕ} {idxOf : Entity Y → Fin k}
    {w : Fin k → Entity Y} :
    ∀ {ψ : UFormula Y} {env : ℕ → Entity Y},
      (∀ c ∈ constsUFormula ψ, w (idxOf c) = c) →
        (Holds (combineEnv w env) (abstractUFormula Y idxOf ψ) ↔ Holds env ψ)
  | .eq t₁ t₂, env, hw => by
      have h1 := evalUTerm_abstractUTerm (t := t₁) (env := env) fun c hc ↦
        hw c (by simp [constsUFormula, hc])
      have h2 := evalUTerm_abstractUTerm (t := t₂) (env := env) fun c hc ↦
        hw c (by simp [constsUFormula, hc])
      simp only [abstractUFormula, Holds, h1, h2]
  | .mem t₁ t₂, env, hw => by
      have h1 := evalUTerm_abstractUTerm (t := t₁) (env := env) fun c hc ↦
        hw c (by simp [constsUFormula, hc])
      have h2 := evalUTerm_abstractUTerm (t := t₂) (env := env) fun c hc ↦
        hw c (by simp [constsUFormula, hc])
      simp only [abstractUFormula, Holds, h1, h2]
  | .conj φ ψ, _, hw =>
      and_congr
        (holds_abstractUFormula fun c hc ↦ hw c (by simp [constsUFormula, hc]))
        (holds_abstractUFormula fun c hc ↦ hw c (by simp [constsUFormula, hc]))
  | .disj φ ψ, _, hw =>
      or_congr
        (holds_abstractUFormula fun c hc ↦ hw c (by simp [constsUFormula, hc]))
        (holds_abstractUFormula fun c hc ↦ hw c (by simp [constsUFormula, hc]))
  | .neg φ, _, hw => not_congr (holds_abstractUFormula hw)
  | .imp φ ψ, _, hw =>
      imp_congr
        (holds_abstractUFormula fun c hc ↦ hw c (by simp [constsUFormula, hc]))
        (holds_abstractUFormula fun c hc ↦ hw c (by simp [constsUFormula, hc]))
  | .iff φ ψ, _, hw =>
      iff_congr
        (holds_abstractUFormula fun c hc ↦ hw c (by simp [constsUFormula, hc]))
        (holds_abstractUFormula fun c hc ↦ hw c (by simp [constsUFormula, hc]))
  | .forallIn v dom body, env, hw => by
      have hdom := evalUTerm_abstractUTerm (t := dom) (env := env) fun c hc ↦
        hw c (by simp [constsUFormula, hc])
      simp only [abstractUFormula, Holds, hdom, combineEnv_update_add]
      exact exists_congr fun _ ↦ and_congr_right fun _ ↦ forall₂_congr fun _ _ ↦
        holds_abstractUFormula fun c hc ↦ hw c (by simp [constsUFormula, hc])
  | .existsIn v dom body, env, hw => by
      have hdom := evalUTerm_abstractUTerm (t := dom) (env := env) fun c hc ↦
        hw c (by simp [constsUFormula, hc])
      simp only [abstractUFormula, Holds, hdom, combineEnv_update_add]
      exact exists_congr fun _ ↦ and_congr_right fun _ ↦ exists_congr fun _ ↦ and_congr_right fun _ ↦
        holds_abstractUFormula fun c hc ↦ hw c (by simp [constsUFormula, hc])

/-- **Master Internal Set Comprehension Engine** (Goldblatt §13.15, p. 177): For any internal
entity `A : Entity Y` and any internal `ℒ_{𝕌'}`-formula `ψ` (`ψ.AllConstsInternal F`) whose only
free variable is at most `x`, the bounded comprehension `{a ∈ A : ψ(a)}` belongs to `*𝒫(T)` for a
transitive standard set `T` (and hence is internal!). -/
theorem Framework.isInternalEntity_comprehension {X Y : Type*} (F : Framework X Y)
    {A : Entity Y} (hA : F.IsInternalEntity A) (x : ℕ) {ψ : UFormula Y}
    (hvars : ∀ v ∈ freeVarsUFormula ψ, v = x)
    (hconsts : ψ.AllConstsInternal F) (env : ℕ → Entity Y) :
    F.IsInternalEntity
      (Entity.setOfBounded {a : Entity Y | a ∈ A ∧ Holds (Function.update env x a) ψ}) := by
  let cs : List (Entity Y) := constsUFormula ψ
  let m : ℕ := cs.length
  let k : ℕ := m + 1
  let wY : Fin k → Entity Y := fun j ↦
    if hj : j.1 < m then cs.get ⟨j.1, hj⟩ else A
  have hwY_int : ∀ j : Fin k, F.IsInternalEntity (wY j) := by
    intro j
    dsimp only [wY]
    split_ifs with hj
    · exact hconsts _ (List.get_mem cs ⟨j.1, hj⟩)
    · exact hA
  let idxOf : Entity Y → Fin k := fun c ↦
    if hc : c ∈ cs then
      ⟨(List.mem_iff_get.1 hc).choose.1, by have := (List.mem_iff_get.1 hc).choose.2; omega⟩
    else
      ⟨0, by omega⟩
  have hwY_idx : ∀ c ∈ cs, wY (idxOf c) = c := by
    intro c hc
    have hlt : (List.mem_iff_get.1 hc).choose.1 < m := (List.mem_iff_get.1 hc).choose.2
    simp only [idxOf, hc, ↓reduceDIte, wY, hlt]
    exact (List.mem_iff_get.1 hc).choose_spec
  obtain ⟨T, _, hstarT, hwYT⟩ := F.exists_common_star_transitiveSet hwY_int
  have hAT : A ∈ F.star T := by
    have hm : ¬ (m < m) := Nat.lt_irrefl m
    simpa [wY, hm] using hwYT ⟨m, by omega⟩
  let xVar : ℕ := k + x
  let zVar : ℕ := k + x + 1
  let φX : UFormula X := abstractUFormula X idxOf ψ
  have hφX_fv : ∀ v ∈ freeVarsUFormula φX, v < k ∨ v = xVar := by
    intro v hv
    rcases freeVarsUFormula_abstractUFormula idxOf hv with hlt | ⟨u, hu, rfl⟩
    · exact Or.inl hlt
    · exact Or.inr (by rw [hvars u hu])
  let bodyX : UFormula X :=
    .existsIn zVar (.const (Entity.powerset T))
      (.forallIn xVar (.const T)
        (.iff
          (.mem (.var xVar) (.var zVar))
          (.conj (.mem (.var xVar) (.var m)) φX)))
  let sentX : UFormula X := forallVarsIn (.const T) k bodyX
  have hsent : IsSentence sentX := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v hv
    obtain ⟨hkv, hvbody⟩ := (freeVarsUFormula_forallVarsIn_const T k bodyX v).1 hv
    simp only [bodyX, freeVarsUFormula, freeVarsUTerm, Finset.empty_union, Finset.mem_erase,
      Finset.mem_union, Finset.mem_singleton] at hvbody
    obtain ⟨hnz, hnx, (rfl | rfl) | ((rfl | rfl) | hvφ)⟩ := hvbody
    · exact hnx rfl
    · exact hnz rfl
    · exact hnx rfl
    · omega
    · rcases hφX_fv v hvφ with hlt | rfl
      · omega
      · exact hnx rfl
  have hstd : SentenceHolds sentX := by
    rw [SentenceHolds, holds_forallVarsIn_const]
    intro wX _
    let envX₀ : ℕ → Entity X := fun n ↦ if h : n < k then wX ⟨n, h⟩ else ∅
    let ZX : Entity X :=
      Entity.setOfBounded {a : Entity X |
        a ∈ T ∧ a ∈ wX ⟨m, by omega⟩ ∧ Holds (Function.update envX₀ xVar a) φX}
    have hZX_bdd : IsBoundedRank {a : Entity X |
        a ∈ T ∧ a ∈ wX ⟨m, by omega⟩ ∧ Holds (Function.update envX₀ xVar a) φX} :=
      T.isBoundedRank_extSet.subset fun _ h ↦ h.1
    have hZX_mem : ZX ∈ Entity.powerset T :=
      Entity.mem_powerset_iff.2 ⟨Entity.isSet_setOfBounded _, fun a ha ↦
        ((Entity.mem_setOfBounded hZX_bdd).1 ha).1⟩
    refine ⟨Entity.powerset T, rfl, ZX, hZX_mem, T, rfl, fun a haT ↦ ?_⟩
    let envX₂ := Function.update (Function.update envX₀ zVar ZX) xVar a
    have hx_ev : evalUTerm envX₂ (.var xVar) = some a := by simp [envX₂]
    have hz_ev : evalUTerm envX₂ (.var zVar) = some ZX := by
      have hne : zVar ≠ xVar := by omega
      simp [envX₂, Function.update_of_ne hne]
    have hm_ev : evalUTerm envX₂ (.var m) = some (wX ⟨m, by omega⟩) := by
      have h1 : m ≠ xVar := by omega
      have h2 : m ≠ zVar := by omega
      have hlt : m < k := by omega
      simp [envX₂, Function.update_of_ne h1, Function.update_of_ne h2, envX₀, hlt]
    have hφ_congr : Holds envX₂ φX ↔ Holds (Function.update envX₀ xVar a) φX :=
      holds_congr fun v hv ↦ by
        by_cases hvx : v = xVar
        · subst hvx; simp [envX₂]
        · have hvz : v ≠ zVar := by
            rcases hφX_fv v hv with hlt | rfl <;> omega
          simp [envX₂, Function.update_of_ne hvx, Function.update_of_ne hvz]
    change Holds envX₂ _
    simp only [Holds, hx_ev, hz_ev, hm_ev, hφ_congr]
    constructor
    · rintro ⟨_, _, h1, h2, haZ⟩
      obtain rfl := Option.some.inj h1; obtain rfl := Option.some.inj h2
      obtain ⟨_, haM, haφ⟩ := (Entity.mem_setOfBounded hZX_bdd).1 haZ
      exact ⟨⟨a, _, rfl, rfl, haM⟩, haφ⟩
    · rintro ⟨⟨_, _, h1, h2, haM⟩, haφ⟩
      obtain rfl := Option.some.inj h1; obtain rfl := Option.some.inj h2
      exact ⟨a, ZX, rfl, rfl, (Entity.mem_setOfBounded hZX_bdd).2 ⟨haT, haM, haφ⟩⟩
  have htr := (F.transfer sentX hsent).1 hstd
  simp only [sentX, bodyX, φX, starFormula_forallVarsIn, starFormula_abstractUFormula,
    starFormula, starTerm] at htr
  rw [SentenceHolds, holds_forallVarsIn_const] at htr
  obtain ⟨_, hP0, Z, hZP, _, hT0, hallZ⟩ := htr wY hwYT
  obtain rfl := Option.some.inj hP0
  obtain rfl := Option.some.inj hT0
  obtain ⟨hZset, hZsub⟩ := Entity.mem_powerset_iff.1 (F.mem_powerset_star_of_mem_star_powerset hZP)
  have htarget_bdd : IsBoundedRank {a : Entity Y | a ∈ A ∧ Holds (Function.update env x a) ψ} :=
    A.isBoundedRank_extSet.subset fun _ h ↦ h.1
  have hZeq : Z = Entity.setOfBounded {a : Entity Y | a ∈ A ∧ Holds (Function.update env x a) ψ} := by
    refine Entity.set_ext hZset (Entity.isSet_setOfBounded _) fun a ↦ ?_
    rw [Entity.mem_setOfBounded htarget_bdd]
    let envY₀ : ℕ → Entity Y := fun n ↦ if h : n < k then wY ⟨n, h⟩ else ∅
    have henv_comb : envY₀ = combineEnv wY (fun _ ↦ ∅) := rfl
    have hψ_equiv : ∀ b : Entity Y,
        Holds (Function.update (Function.update envY₀ zVar Z) xVar b) (abstractUFormula Y idxOf ψ) ↔
          Holds (Function.update env x b) ψ := by
      intro b
      have hc1 : Holds (Function.update (Function.update envY₀ zVar Z) xVar b)
          (abstractUFormula Y idxOf ψ) ↔
          Holds (Function.update envY₀ xVar b) (abstractUFormula Y idxOf ψ) :=
        holds_congr fun v hv ↦ by
          by_cases hvx : v = xVar
          · subst hvx; simp
          · have hvz : v ≠ zVar := by
              rcases freeVarsUFormula_abstractUFormula idxOf hv with hlt | ⟨u, hu, rfl⟩
              · omega
              · have := hvars u hu; omega
            simp [Function.update_of_ne hvx, Function.update_of_ne hvz]
      rw [hc1, henv_comb]
      change Holds (Function.update (combineEnv wY (fun _ ↦ ∅)) (k + x) b) _ ↔ _
      rw [combineEnv_update_add, holds_abstractUFormula hwY_idx]
      exact holds_congr fun v hv ↦ by
        obtain rfl := hvars v hv
        simp
    let envY₂ := Function.update (Function.update envY₀ zVar Z) xVar a
    have hx_ev : evalUTerm envY₂ (.var xVar) = some a := by simp [envY₂]
    have hz_ev : evalUTerm envY₂ (.var zVar) = some Z := by
      have hne : zVar ≠ xVar := by omega
      simp [envY₂, Function.update_of_ne hne]
    have hm_ev : evalUTerm envY₂ (.var m) = some A := by
      have h1 : m ≠ xVar := by omega
      have h2 : m ≠ zVar := by omega
      have hlt : m < k := by omega
      simp [envY₂, Function.update_of_ne h1, Function.update_of_ne h2, envY₀, hlt, wY]
    have hψ_ev : Holds envY₂ (abstractUFormula Y idxOf ψ) ↔ Holds (Function.update env x a) ψ :=
      hψ_equiv a
    constructor
    · intro haZ
      have haT : a ∈ F.star T := hZsub a haZ
      have hiff := hallZ a haT
      change Holds envY₂ _ at hiff
      simp only [Holds, hx_ev, hz_ev, hm_ev, hψ_ev] at hiff
      obtain ⟨⟨_, _, h1, h2, haA⟩, haψ⟩ := hiff.1 ⟨a, Z, rfl, rfl, haZ⟩
      obtain rfl := Option.some.inj h1; obtain rfl := Option.some.inj h2
      exact ⟨haA, haψ⟩
    · rintro ⟨haA, haψ⟩
      have haT : a ∈ F.star T := hstarT.2 A hAT a haA
      have hiff := hallZ a haT
      change Holds envY₂ _ at hiff
      simp only [Holds, hx_ev, hz_ev, hm_ev, hψ_ev] at hiff
      obtain ⟨_, _, h1, h2, haZ⟩ := hiff.2 ⟨⟨a, A, rfl, rfl, haA⟩, haψ⟩
      obtain rfl := Option.some.inj h1; obtain rfl := Option.some.inj h2
      exact haZ
  exact hZeq ▸ ⟨Entity.powerset T, hZP⟩

/-- Convenience wrapper for `Framework.isInternalEntity_comprehension`: any set entity `Z` whose
membership is characterized inside an internal entity `A` by an internal single-variable formula
`ψ(x₀)` is internal (Goldblatt §13.11 & §13.15, pp. 173–177). -/
theorem Framework.isInternalEntity_of_set_eq_comprehension {X Y : Type*} (F : Framework X Y)
    {Z A : Entity Y} (hZ : Z.IsSet) (hA : F.IsInternalEntity A)
    (ψ : UFormula Y) (hvars : ∀ v ∈ freeVarsUFormula ψ, v = 0)
    (hconsts : ψ.AllConstsInternal F)
    (hiff : ∀ a : Entity Y,
      a ∈ Z ↔ a ∈ A ∧ Holds (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 a) ψ) :
    F.IsInternalEntity Z := by
  have hbdd : IsBoundedRank {a : Entity Y |
      a ∈ A ∧ Holds (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 a) ψ} :=
    A.isBoundedRank_extSet.subset fun _ h ↦ h.1
  have hEq : Z = Entity.setOfBounded {a : Entity Y |
      a ∈ A ∧ Holds (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 a) ψ} :=
    Entity.set_ext hZ (Entity.isSet_setOfBounded _) fun a ↦ by
      rw [Entity.mem_setOfBounded hbdd, hiff a]; rfl
  exact hEq ▸ F.isInternalEntity_comprehension hA 0 hvars hconsts (fun _ ↦ ∅)

/-! ## §13.11 Closure Properties of Internal Sets (and Exercise 13.11.1) -/

/-- Coordinate helper: if `(a, b) ∈ R ∈ U` where `U` is a transitive set entity, then `a ∈ U` and
`b ∈ U` (since `a, b ∈ {a, b} ∈ (a, b) ∈ R ∈ U`; Goldblatt §13.4 & §13.11, pp. 161, 174). -/
theorem Entity.IsTransitiveSet.mem_of_kpair_mem_of_mem {Y : Type*} {U R a b : Entity Y}
    (hU : U.IsTransitiveSet) (hRU : R ∈ U) (hp : Entity.kpair a b ∈ R) :
    a ∈ U ∧ b ∈ U := by
  have hpU : Entity.kpair a b ∈ U := hU.2 R hRU _ hp
  have huU : Entity.upair a b ∈ U :=
    hU.2 _ hpU _ (Entity.mem_upair_iff.2 (Or.inr rfl))
  exact ⟨hU.2 _ huU a (Entity.mem_upair_iff.2 (Or.inl rfl)),
    hU.2 _ huU b (Entity.mem_upair_iff.2 (Or.inr rfl))⟩

/-- Goldblatt §13.11 Bullet 1 & **Exercise 13.11.1** (pp. 173–174): If `A` and `B` are internal,
then `A ∩ B` (`Entity.inter A B`) is internal. -/
theorem Framework.isInternalEntity_inter {X Y : Type*} (F : Framework X Y) {A B : Entity Y}
    (hA : F.IsInternalEntity A) (hB : F.IsInternalEntity B) :
    F.IsInternalEntity (Entity.inter A B) := by
  refine F.isInternalEntity_of_set_eq_comprehension (Entity.isSet_inter A B) hA
    (.mem (.var 0) (.const B))
    (by simp [freeVarsUFormula, freeVarsUTerm])
    (by simp [hB])
    fun a ↦ ?_
  rw [Entity.mem_inter_iff]
  refine and_congr_right fun _ ↦ ?_
  simp only [Holds, Function.update_self, evalUTerm_var, evalUTerm_const]
  exact ⟨fun hb ↦ ⟨a, B, rfl, rfl, hb⟩,
    fun ⟨_, _, h1, h2, hb⟩ ↦ (Option.some.inj h1) ▸ (Option.some.inj h2) ▸ hb⟩

/-- Goldblatt §13.11 Bullet 1 & **Exercise 13.11.1** (pp. 173–174): If `A` and `B` are internal,
then `A \ B` (`Entity.sdiff A B`) is internal. -/
theorem Framework.isInternalEntity_sdiff {X Y : Type*} (F : Framework X Y) {A B : Entity Y}
    (hA : F.IsInternalEntity A) (hB : F.IsInternalEntity B) :
    F.IsInternalEntity (Entity.sdiff A B) := by
  refine F.isInternalEntity_of_set_eq_comprehension (Entity.isSet_sdiff A B) hA
    (.neg (.mem (.var 0) (.const B)))
    (by simp [freeVarsUFormula, freeVarsUTerm])
    (by simp [hB])
    fun a ↦ ?_
  rw [Entity.mem_sdiff_iff]
  refine and_congr_right fun _ ↦ not_congr ?_
  simp only [Holds, Function.update_self, evalUTerm_var, evalUTerm_const]
  exact ⟨fun hb ↦ ⟨a, B, rfl, rfl, hb⟩,
    fun ⟨_, _, h1, h2, hb⟩ ↦ (Option.some.inj h1) ▸ (Option.some.inj h2) ▸ hb⟩

/-- Goldblatt §13.11 (pp. 173–174): If `A` and `B` are internal entities, then `A ∪ B`
(`Entity.union A B`) is internal (proved directly via a common transitive `*T` just as on p. 174). -/
theorem Framework.isInternalEntity_union {X Y : Type*} (F : Framework X Y) {A B : Entity Y}
    (hA : F.IsInternalEntity A) (hB : F.IsInternalEntity B) :
    F.IsInternalEntity (Entity.union A B) := by
  obtain ⟨T, _, hstarT, hwT⟩ := F.exists_common_star_transitiveSet
    (w := ![A, B]) (fun i ↦ by fin_cases i <;> assumption)
  have hAT : A ∈ F.star T := hwT 0
  have hBT : B ∈ F.star T := hwT 1
  refine F.isInternalEntity_of_set_eq_comprehension (Entity.isSet_union A B)
    (F.isInternalEntity_star T)
    (.disj (.mem (.var 0) (.const A)) (.mem (.var 0) (.const B)))
    (by simp [freeVarsUFormula, freeVarsUTerm])
    (by simp [hA, hB])
    fun u ↦ ?_
  rw [Entity.mem_union_iff]
  simp only [Holds, Function.update_self, evalUTerm_var, evalUTerm_const]
  constructor
  · rintro (huA | huB)
    · exact ⟨hstarT.2 A hAT u huA, Or.inl ⟨u, A, rfl, rfl, huA⟩⟩
    · exact ⟨hstarT.2 B hBT u huB, Or.inr ⟨u, B, rfl, rfl, huB⟩⟩
  · rintro ⟨_, ⟨_, _, h1, h2, huA⟩ | ⟨_, _, h1, h2, huB⟩⟩
    · exact Or.inl ((Option.some.inj h1) ▸ (Option.some.inj h2) ▸ huA)
    · exact Or.inr ((Option.some.inj h1) ▸ (Option.some.inj h2) ▸ huB)

/-- Goldblatt §13.11 Bullet 3 & **Exercise 13.11.1** (p. 174): If `a` and `b` are internal, then
the unordered pair `{a, b}` (`Entity.upair a b`) is internal. -/
theorem Framework.isInternalEntity_upair {X Y : Type*} (F : Framework X Y) {a b : Entity Y}
    (ha : F.IsInternalEntity a) (hb : F.IsInternalEntity b) :
    F.IsInternalEntity (Entity.upair a b) := by
  obtain ⟨T, _, _, hwT⟩ := F.exists_common_star_transitiveSet
    (w := ![a, b]) (fun i ↦ by fin_cases i <;> assumption)
  have haT : a ∈ F.star T := hwT 0
  have hbT : b ∈ F.star T := hwT 1
  refine F.isInternalEntity_of_set_eq_comprehension (Entity.isSet_upair a b)
    (F.isInternalEntity_star T)
    (.disj (.eq (.var 0) (.const a)) (.eq (.var 0) (.const b)))
    (by simp [freeVarsUFormula, freeVarsUTerm])
    (by simp [ha, hb])
    fun u ↦ ?_
  rw [Entity.mem_upair_iff]
  simp only [Holds, Function.update_self, evalUTerm_var, evalUTerm_const]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨haT, Or.inl ⟨u, rfl, rfl⟩⟩
    · exact ⟨hbT, Or.inr ⟨u, rfl, rfl⟩⟩
  · rintro ⟨_, ⟨w, h1, h2⟩ | ⟨w, h1, h2⟩⟩
    · exact Or.inl ((Option.some.inj h1).trans (Option.some.inj h2).symm)
    · exact Or.inr ((Option.some.inj h1).trans (Option.some.inj h2).symm)

/-- Goldblatt §13.11 Bullet 3 & **Exercise 13.11.1** (p. 174): If `a` is internal, then `{a}`
(`Entity.singleton a`) is internal. -/
theorem Framework.isInternalEntity_singleton {X Y : Type*} (F : Framework X Y) {a : Entity Y}
    (ha : F.IsInternalEntity a) :
    F.IsInternalEntity (Entity.singleton a) :=
  F.isInternalEntity_upair ha ha

/-- Goldblatt §13.11 Bullet 3 & **Exercise 13.11.1** (p. 174): If every `a ∈ S` (`S : Finset`) is
internal, then the finite set `{a₁, …, a_m}` (`Entity.finsetEntity S`) is internal. -/
theorem Framework.isInternalEntity_finsetEntity {X Y : Type*} (F : Framework X Y)
    {S : Finset (Entity Y)} (hS : ∀ a ∈ S, F.IsInternalEntity a) :
    F.IsInternalEntity (Entity.finsetEntity S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have h0 : Entity.finsetEntity (∅ : Finset (Entity Y)) = ∅ := by
        refine Entity.set_ext (Entity.isSet_finsetEntity _) Entity.isSet_empty fun z ↦ ?_
        simp
      exact h0 ▸ F.isInternalEntity_empty
  | @insert a s _ ih =>
      have hEq : Entity.finsetEntity (insert a s) =
          Entity.union (Entity.singleton a) (Entity.finsetEntity s) := by
        refine Entity.set_ext (Entity.isSet_finsetEntity _) (Entity.isSet_union _ _) fun z ↦ ?_
        simp [Entity.mem_union_iff, Entity.mem_singleton_iff]
      rw [hEq]
      exact F.isInternalEntity_union
        (F.isInternalEntity_singleton (hS a (Finset.mem_insert_self a s)))
        (ih fun b hb ↦ hS b (Finset.mem_insert_of_mem hb))

/-- Goldblatt §13.11 Bullet 3 & **Exercise 13.11.1** (p. 174): If `a` and `b` are internal, then
the Kuratowski ordered pair `(a, b)` (`Entity.kpair a b`) is internal. -/
theorem Framework.isInternalEntity_kpair {X Y : Type*} (F : Framework X Y) {a b : Entity Y}
    (ha : F.IsInternalEntity a) (hb : F.IsInternalEntity b) :
    F.IsInternalEntity (Entity.kpair a b) :=
  F.isInternalEntity_upair (F.isInternalEntity_singleton ha) (F.isInternalEntity_upair ha hb)

/-- Goldblatt §13.11 Bullet 3 & **Exercise 13.11.1** (p. 174): If `v₀, …, v_{m-1}` are internal,
then the `m`-tuple `(v₀, …, v_{m-1})` (`Entity.ktuple v`) is internal. -/
theorem Framework.isInternalEntity_ktuple {X Y : Type*} (F : Framework X Y) :
    ∀ {m : ℕ} {v : Fin m → Entity Y}, (∀ i : Fin m, F.IsInternalEntity (v i)) →
      F.IsInternalEntity (Entity.ktuple v)
  | 0, _, _ => F.isInternalEntity_empty
  | 1, _, hv => hv 0
  | 2, _, hv => F.isInternalEntity_kpair (hv 0) (hv 1)
  | m + 3, _, hv =>
      F.isInternalEntity_kpair
        (F.isInternalEntity_ktuple (m := m + 2) fun j ↦ hv j.castSucc)
        (hv (Fin.last (m + 2)))

/-- Goldblatt §13.11 Bullet 1 & **Exercise 13.11.1** (p. 173): If `A` and `B` are internal, then
their Cartesian product `A × B` (`Entity.prod A B`) is internal. -/
theorem Framework.isInternalEntity_prod {X Y : Type*} (F : Framework X Y) {A B : Entity Y}
    (hA : F.IsInternalEntity A) (hB : F.IsInternalEntity B) :
    F.IsInternalEntity (Entity.prod A B) := by
  obtain ⟨T, _, hstarT, hwT⟩ := F.exists_common_star_transitiveSet
    (w := ![A, B]) (fun i ↦ by fin_cases i <;> assumption)
  have hAT : A ∈ F.star T := hwT 0
  have hBT : B ∈ F.star T := hwT 1
  refine F.isInternalEntity_of_set_eq_comprehension (Entity.isSet_prod A B)
    (F.isInternalEntity_star (Entity.prod T T))
    (.existsIn 1 (.const A)
      (.existsIn 2 (.const B)
        (.eq (.var 0) (UTerm.pair (.var 1) (.var 2)))))
    (by intro v hv; simp [freeVarsUFormula, freeVarsUTerm] at hv; omega)
    (by simp [hA, hB])
    fun p ↦ ?_
  rw [Entity.mem_prod_iff]
  constructor
  · rintro ⟨a, haA, b, hbB, rfl⟩
    have hpT : Entity.kpair a b ∈ F.star (Entity.prod T T) := by
      rw [F.star_prod]
      exact Entity.kpair_mem_prod_iff.2 ⟨hstarT.2 A hAT a haA, hstarT.2 B hBT b hbB⟩
    refine ⟨hpT, A, rfl, a, haA, B, rfl, b, hbB, Entity.kpair a b, ?_, ?_⟩
    · simp
    · simp [evalUTerm_pair]
  · rintro ⟨_, _, hAd, a, haA, _, hBd, b, hbB, q, hq1, hq2⟩
    obtain rfl := Option.some.inj hAd
    obtain rfl := Option.some.inj hBd
    have h1 : p = q := Option.some.inj (by simpa using hq1)
    have h2 : Entity.kpair a b = q := Option.some.inj (by simpa [evalUTerm_pair] using hq2)
    exact ⟨a, haA, b, hbB, h1.trans h2.symm⟩

/-- Goldblatt §13.11 & **Exercise 13.11.1** (pp. 173–174): Finite Cartesian products
`A₀ × ⋯ × A_{m-1}` (`Entity.prodTuple A`) of internal entities are internal. -/
theorem Framework.isInternalEntity_prodTuple {X Y : Type*} (F : Framework X Y) :
    ∀ {m : ℕ} {A : Fin m → Entity Y}, (∀ i : Fin m, F.IsInternalEntity (A i)) →
      F.IsInternalEntity (Entity.prodTuple A)
  | 0, A, _ => by
      have hEq : Entity.prodTuple A = Entity.singleton ∅ := by
        refine Entity.set_ext (Entity.isSet_prodTuple A) (Entity.isSet_singleton _) fun p ↦ ?_
        simp only [Entity.mem_prodTuple_iff, Entity.ktuple, Entity.mem_singleton_iff]
        exact ⟨fun ⟨_, _, h⟩ ↦ h, fun h ↦ ⟨Fin.elim0, fun i ↦ Fin.elim0 i, h⟩⟩
      exact hEq ▸ F.isInternalEntity_singleton F.isInternalEntity_empty
  | 1, A, hA => by
      refine F.isInternalEntity_of_set_eq_comprehension (Entity.isSet_prodTuple A) (hA 0)
        (.eq (.var 0) (.var 0))
        (by simp [freeVarsUFormula, freeVarsUTerm])
        (by simp)
        fun p ↦ ?_
      simp only [Entity.mem_prodTuple_iff, Entity.ktuple, Holds, Function.update_self, evalUTerm_var]
      exact ⟨fun ⟨v, hv, hp⟩ ↦ ⟨hp ▸ hv 0, p, rfl, rfl⟩,
        fun ⟨hp, _⟩ ↦ ⟨fun _ ↦ p, fun i ↦ by fin_cases i; exact hp, rfl⟩⟩
  | 2, A, hA => by
      have hEq : Entity.prodTuple A = Entity.prod (A 0) (A 1) := by
        refine Entity.set_ext (Entity.isSet_prodTuple A) (Entity.isSet_prod _ _) fun p ↦ ?_
        rw [Entity.mem_prodTuple_iff, Entity.mem_prod_iff]
        constructor
        · rintro ⟨v, hv, rfl⟩
          exact ⟨v 0, hv 0, v 1, hv 1, rfl⟩
        · rintro ⟨a, ha, b, hb, rfl⟩
          exact ⟨![a, b], fun i ↦ by fin_cases i <;> assumption, rfl⟩
      exact hEq ▸ F.isInternalEntity_prod (hA 0) (hA 1)
  | m + 3, A, hA => by
      rw [Entity.prodTuple_succ_succ_succ]
      exact F.isInternalEntity_prod
        (F.isInternalEntity_prodTuple (m := m + 2) fun j ↦ hA j.castSucc)
        (hA (Fin.last (m + 2)))

/-- Goldblatt §13.11 Bullet 2 & **Exercise 13.11.1** (p. 173): The union `⋃ C` (`Entity.sUnion C`)
of any internal collection `C` is internal. -/
theorem Framework.isInternalEntity_sUnion {X Y : Type*} (F : Framework X Y) {C : Entity Y}
    (hC : F.IsInternalEntity C) :
    F.IsInternalEntity (Entity.sUnion C) := by
  obtain ⟨T, _, hstarT, hCT⟩ := F.exists_mem_star_transitiveSet_of_isInternalEntity hC
  refine F.isInternalEntity_of_set_eq_comprehension (Entity.isSet_sUnion C)
    (F.isInternalEntity_star T)
    (.existsIn 1 (.const C) (.mem (.var 0) (.var 1)))
    (by intro v hv; simp [freeVarsUFormula, freeVarsUTerm] at hv; omega)
    (by simp [hC])
    fun z ↦ ?_
  rw [Entity.mem_sUnion_iff]
  constructor
  · rintro ⟨B, hBC, hzB⟩
    have hBT : B ∈ F.star T := hstarT.2 C hCT B hBC
    exact ⟨hstarT.2 B hBT z hzB, C, rfl, B, hBC, z, B, by simp, by simp, hzB⟩
  · rintro ⟨_, _, hCd, B, hBC, z', B', hz', hB', hzB⟩
    obtain rfl := Option.some.inj hCd
    have h1 : z = z' := Option.some.inj (by simpa using hz')
    have h2 : B = B' := Option.some.inj (by simpa using hB')
    exact ⟨B, hBC, h1 ▸ h2 ▸ hzB⟩

/-- Goldblatt §13.11 Bullet 2 & **Exercise 13.11.1** (p. 173): The intersection `⋂ C`
(`Entity.sInter C`) of any internal collection `C` is internal. -/
theorem Framework.isInternalEntity_sInter {X Y : Type*} (F : Framework X Y) {C : Entity Y}
    (hC : F.IsInternalEntity C) :
    F.IsInternalEntity (Entity.sInter C) := by
  by_cases hne : ∃ A : Entity Y, A ∈ C
  · obtain ⟨A₀, hA₀C⟩ := hne
    have hA₀ : F.IsInternalEntity A₀ := hC.of_mem hA₀C
    refine F.isInternalEntity_of_set_eq_comprehension (Entity.isSet_sInter C) hA₀
      (.forallIn 1 (.const C) (.mem (.var 0) (.var 1)))
      (by intro v hv; simp [freeVarsUFormula, freeVarsUTerm] at hv; omega)
      (by simp [hC])
      fun z ↦ ?_
    rw [Entity.mem_sInter_iff ⟨A₀, hA₀C⟩]
    constructor
    · intro hall
      exact ⟨hall A₀ hA₀C, C, rfl, fun B hBC ↦ ⟨z, B, by simp, by simp, hall B hBC⟩⟩
    · rintro ⟨_, _, hCd, hall⟩
      obtain rfl := Option.some.inj hCd
      intro B hBC
      obtain ⟨z', B', hz', hB', hm⟩ := hall B hBC
      have h1 : z = z' := Option.some.inj (by simpa using hz')
      have h2 : B = B' := Option.some.inj (by simpa using hB')
      exact h1 ▸ h2 ▸ hm
  · have hEq : Entity.sInter C = ∅ := by simp [Entity.sInter, hne]
    exact hEq ▸ F.isInternalEntity_empty

/-- Goldblatt §13.11 Bullet 4 & **Exercise 13.11.1** (p. 174): If `R` is internal, then its domain
`dom R` (`Entity.relDom R`) is internal. -/
theorem Framework.isInternalEntity_relDom {X Y : Type*} (F : Framework X Y) {R : Entity Y}
    (hR : F.IsInternalEntity R) :
    F.IsInternalEntity (Entity.relDom R) := by
  obtain ⟨T, _, hstarT, hRT⟩ := F.exists_mem_star_transitiveSet_of_isInternalEntity hR
  refine F.isInternalEntity_of_set_eq_comprehension (Entity.isSet_relDom R)
    (F.isInternalEntity_star T)
    (.existsIn 1 (.const (F.star T)) (.mem (UTerm.pair (.var 0) (.var 1)) (.const R)))
    (by intro v hv; simp [freeVarsUFormula, freeVarsUTerm] at hv; omega)
    (by simp [hR])
    fun a ↦ ?_
  rw [Entity.mem_relDom_iff]
  constructor
  · rintro ⟨b, hp⟩
    obtain ⟨haT, hbT⟩ := hstarT.mem_of_kpair_mem_of_mem hRT hp
    exact ⟨haT, F.star T, rfl, b, hbT, Entity.kpair a b, R, by simp [evalUTerm_pair], rfl, hp⟩
  · rintro ⟨_, _, hTd, b, _, p, R', hp', hR', hp⟩
    obtain rfl := Option.some.inj hTd
    obtain rfl := Option.some.inj hR'
    have hpeq : Entity.kpair a b = p := Option.some.inj (by simpa [evalUTerm_pair] using hp')
    exact ⟨b, hpeq ▸ hp⟩

/-- Goldblatt §13.11 Bullet 4 & **Exercise 13.11.1** (p. 174): If `R` is internal, then its range
`ran R` (`Entity.relRan R`) is internal. -/
theorem Framework.isInternalEntity_relRan {X Y : Type*} (F : Framework X Y) {R : Entity Y}
    (hR : F.IsInternalEntity R) :
    F.IsInternalEntity (Entity.relRan R) := by
  obtain ⟨T, _, hstarT, hRT⟩ := F.exists_mem_star_transitiveSet_of_isInternalEntity hR
  refine F.isInternalEntity_of_set_eq_comprehension (Entity.isSet_relRan R)
    (F.isInternalEntity_star T)
    (.existsIn 1 (.const (F.star T)) (.mem (UTerm.pair (.var 1) (.var 0)) (.const R)))
    (by intro v hv; simp [freeVarsUFormula, freeVarsUTerm] at hv; omega)
    (by simp [hR])
    fun b ↦ ?_
  rw [Entity.mem_relRan_iff]
  constructor
  · rintro ⟨a, hp⟩
    obtain ⟨haT, hbT⟩ := hstarT.mem_of_kpair_mem_of_mem hRT hp
    exact ⟨hbT, F.star T, rfl, a, haT, Entity.kpair a b, R, by simp [evalUTerm_pair], rfl, hp⟩
  · rintro ⟨_, _, hTd, a, _, p, R', hp', hR', hp⟩
    obtain rfl := Option.some.inj hTd
    obtain rfl := Option.some.inj hR'
    have hpeq : Entity.kpair a b = p := Option.some.inj (by simpa [evalUTerm_pair] using hp')
    exact ⟨a, hpeq ▸ hp⟩

/-- Goldblatt §13.11 Bullet 4 & **Exercise 13.11.1** (p. 174): If `R` is internal, then its inverse
`R⁻¹` (`Entity.relInv R`) is internal. -/
theorem Framework.isInternalEntity_relInv {X Y : Type*} (F : Framework X Y) {R : Entity Y}
    (hR : F.IsInternalEntity R) :
    F.IsInternalEntity (Entity.relInv R) := by
  obtain ⟨T, _, hstarT, hRT⟩ := F.exists_mem_star_transitiveSet_of_isInternalEntity hR
  refine F.isInternalEntity_of_set_eq_comprehension (Entity.isSet_relInv R)
    (F.isInternalEntity_star (Entity.prod T T))
    (.existsIn 1 (.const (F.star T))
      (.existsIn 2 (.const (F.star T))
        (.conj
          (.mem (UTerm.pair (.var 1) (.var 2)) (.const R))
          (.eq (.var 0) (UTerm.pair (.var 2) (.var 1))))))
    (by intro v hv; simp [freeVarsUFormula, freeVarsUTerm] at hv; omega)
    (by simp [hR])
    fun p ↦ ?_
  rw [Entity.mem_relInv_iff]
  constructor
  · rintro ⟨a, b, hp, rfl⟩
    obtain ⟨haT, hbT⟩ := hstarT.mem_of_kpair_mem_of_mem hRT hp
    have hpT : Entity.kpair b a ∈ F.star (Entity.prod T T) := by
      rw [F.star_prod]; exact Entity.kpair_mem_prod_iff.2 ⟨hbT, haT⟩
    exact ⟨hpT, F.star T, rfl, a, haT, F.star T, rfl, b, hbT,
      ⟨Entity.kpair a b, R, by simp [evalUTerm_pair], rfl, hp⟩,
      ⟨Entity.kpair b a, by simp, by simp [evalUTerm_pair]⟩⟩
  · rintro ⟨_, _, hT1, a, _, _, hT2, b, _, ⟨q1, R', hq1, hR', hpR⟩, ⟨q2, hq2a, hq2b⟩⟩
    obtain rfl := Option.some.inj hT1; obtain rfl := Option.some.inj hT2
    obtain rfl := Option.some.inj hR'
    have hab : Entity.kpair a b = q1 := Option.some.inj (by simpa [evalUTerm_pair] using hq1)
    have hp1 : p = q2 := Option.some.inj (by simpa using hq2a)
    have hp2 : Entity.kpair b a = q2 := Option.some.inj (by simpa [evalUTerm_pair] using hq2b)
    exact ⟨a, b, hab ▸ hpR, hp1.trans hp2.symm⟩

/-- Goldblatt §13.11 Bullets 4 & 6 & **Exercise 13.11.1** (p. 174): If `R` and `C` are internal,
then the relational/functional image `R''(C)` (`Entity.relImage R C`) is internal. -/
theorem Framework.isInternalEntity_relImage {X Y : Type*} (F : Framework X Y) {R C : Entity Y}
    (hR : F.IsInternalEntity R) (hC : F.IsInternalEntity C) :
    F.IsInternalEntity (Entity.relImage R C) := by
  obtain ⟨T, _, hstarT, hRT⟩ := F.exists_mem_star_transitiveSet_of_isInternalEntity hR
  refine F.isInternalEntity_of_set_eq_comprehension (Entity.isSet_relImage R C)
    (F.isInternalEntity_star T)
    (.existsIn 1 (.const C) (.mem (UTerm.pair (.var 1) (.var 0)) (.const R)))
    (by intro v hv; simp [freeVarsUFormula, freeVarsUTerm] at hv; omega)
    (by simp [hR, hC])
    fun b ↦ ?_
  rw [Entity.mem_relImage_iff]
  constructor
  · rintro ⟨a, haC, hp⟩
    obtain ⟨_, hbT⟩ := hstarT.mem_of_kpair_mem_of_mem hRT hp
    exact ⟨hbT, C, rfl, a, haC, Entity.kpair a b, R, by simp [evalUTerm_pair], rfl, hp⟩
  · rintro ⟨_, _, hCd, a, haC, p, R', hp', hR', hp⟩
    obtain rfl := Option.some.inj hCd; obtain rfl := Option.some.inj hR'
    have hab : Entity.kpair a b = p := Option.some.inj (by simpa [evalUTerm_pair] using hp')
    exact ⟨a, haC, hab ▸ hp⟩

/-- Goldblatt §13.11 Bullet 6 & **Exercise 13.11.1** (p. 174): If `R` and `D` are internal, then
the inverse image `R⁻¹(D)` (`Entity.relPreimage R D`) is internal. -/
theorem Framework.isInternalEntity_relPreimage {X Y : Type*} (F : Framework X Y) {R D : Entity Y}
    (hR : F.IsInternalEntity R) (hD : F.IsInternalEntity D) :
    F.IsInternalEntity (Entity.relPreimage R D) := by
  obtain ⟨T, _, hstarT, hRT⟩ := F.exists_mem_star_transitiveSet_of_isInternalEntity hR
  refine F.isInternalEntity_of_set_eq_comprehension (Entity.isSet_relPreimage R D)
    (F.isInternalEntity_star T)
    (.existsIn 1 (.const D) (.mem (UTerm.pair (.var 0) (.var 1)) (.const R)))
    (by intro v hv; simp [freeVarsUFormula, freeVarsUTerm] at hv; omega)
    (by simp [hR, hD])
    fun a ↦ ?_
  rw [Entity.mem_relPreimage_iff]
  constructor
  · rintro ⟨b, hbD, hp⟩
    obtain ⟨haT, _⟩ := hstarT.mem_of_kpair_mem_of_mem hRT hp
    exact ⟨haT, D, rfl, b, hbD, Entity.kpair a b, R, by simp [evalUTerm_pair], rfl, hp⟩
  · rintro ⟨_, _, hDd, b, hbD, p, R', hp', hR', hp⟩
    obtain rfl := Option.some.inj hDd; obtain rfl := Option.some.inj hR'
    have hab : Entity.kpair a b = p := Option.some.inj (by simpa [evalUTerm_pair] using hp')
    exact ⟨b, hbD, hab ▸ hp⟩

/-- Goldblatt §13.11 Bullet 5 & **Exercise 13.11.1** (p. 174): If binary relations `R` and `S` are
internal, then their composition `R ∘ S` (`Entity.relComp R S`) is internal. -/
theorem Framework.isInternalEntity_relComp {X Y : Type*} (F : Framework X Y) {R S : Entity Y}
    (hR : F.IsInternalEntity R) (hS : F.IsInternalEntity S) :
    F.IsInternalEntity (Entity.relComp R S) := by
  obtain ⟨T, _, hstarT, hwT⟩ := F.exists_common_star_transitiveSet
    (w := ![R, S]) (fun i ↦ by fin_cases i <;> assumption)
  have hRT : R ∈ F.star T := hwT 0
  have hST : S ∈ F.star T := hwT 1
  refine F.isInternalEntity_of_set_eq_comprehension (Entity.isSet_relComp R S)
    (F.isInternalEntity_star (Entity.prod T T))
    (.existsIn 1 (.const (F.star T))
      (.existsIn 2 (.const (F.star T))
        (.existsIn 3 (.const (F.star T))
          (.conj
            (.mem (UTerm.pair (.var 1) (.var 2)) (.const R))
            (.conj
              (.mem (UTerm.pair (.var 2) (.var 3)) (.const S))
              (.eq (.var 0) (UTerm.pair (.var 1) (.var 3))))))))
    (by intro v hv; simp [freeVarsUFormula, freeVarsUTerm] at hv; omega)
    (by simp [hR, hS])
    fun p ↦ ?_
  rw [Entity.mem_relComp_iff]
  constructor
  · rintro ⟨a, b, c, hpR, hpS, rfl⟩
    obtain ⟨haT, hbT⟩ := hstarT.mem_of_kpair_mem_of_mem hRT hpR
    obtain ⟨_, hcT⟩ := hstarT.mem_of_kpair_mem_of_mem hST hpS
    have hpT : Entity.kpair a c ∈ F.star (Entity.prod T T) := by
      rw [F.star_prod]; exact Entity.kpair_mem_prod_iff.2 ⟨haT, hcT⟩
    exact ⟨hpT, F.star T, rfl, a, haT, F.star T, rfl, b, hbT, F.star T, rfl, c, hcT,
      ⟨Entity.kpair a b, R, by simp [evalUTerm_pair], rfl, hpR⟩,
      ⟨Entity.kpair b c, S, by simp [evalUTerm_pair], rfl, hpS⟩,
      ⟨Entity.kpair a c, by simp, by simp [evalUTerm_pair]⟩⟩
  · rintro ⟨_, _, hT1, a, _, _, hT2, b, _, _, hT3, c, _,
      ⟨q1, R', hq1, hR', hpR⟩, ⟨q2, S', hq2, hS', hpS⟩, ⟨q3, hq3a, hq3b⟩⟩
    obtain rfl := Option.some.inj hT1; obtain rfl := Option.some.inj hT2
    obtain rfl := Option.some.inj hT3; obtain rfl := Option.some.inj hR'
    obtain rfl := Option.some.inj hS'
    have hab : Entity.kpair a b = q1 := Option.some.inj (by simpa [evalUTerm_pair] using hq1)
    have hbc : Entity.kpair b c = q2 := Option.some.inj (by simpa [evalUTerm_pair] using hq2)
    have hp1 : p = q3 := Option.some.inj (by simpa using hq3a)
    have hp2 : Entity.kpair a c = q3 := Option.some.inj (by simpa [evalUTerm_pair] using hq3b)
    exact ⟨a, b, c, hab ▸ hpR, hbc ▸ hpS, hp1.trans hp2.symm⟩

/-- Goldblatt §13.11 Bullet 6 & **Exercise 13.11.1** (p. 174): If a function `f` is internal and
`a ∈ dom f`, then `f(a)` (`Entity.funcApp f a`) is internal! -/
theorem Framework.isInternalEntity_funcApp {X Y : Type*} (F : Framework X Y) {f a : Entity Y}
    (hf : F.IsInternalEntity f) (ha : a ∈ Entity.relDom f) :
    F.IsInternalEntity (Entity.funcApp f a) := by
  have hp : F.IsInternalEntity (Entity.kpair a (Entity.funcApp f a)) :=
    hf.of_mem (Entity.kpair_funcApp_mem ha)
  have hu : F.IsInternalEntity (Entity.upair a (Entity.funcApp f a)) :=
    hp.of_mem (Entity.mem_upair_iff.2 (Or.inr rfl))
  exact hu.of_mem (Entity.mem_upair_iff.2 (Or.inr rfl))

/-! ## §13.12 Transformed Power Sets (Theorem 13.12.1) -/

/-- Goldblatt **Theorem 13.12.1** (p. 175): For every entity `A : Entity X`, `*𝒫(A)` is the exact
set of all **internal** subsets of `*A`:
`B ∈ *𝒫(A) ↔ B ∈ 𝒫(*A) ∧ F.IsInternalEntity B` (`*𝒫(A) = 𝒫(*A) ∩ *𝕌`). -/
theorem Framework.mem_star_powerset_iff {X Y : Type*} (F : Framework X Y) {A : Entity X}
    {B : Entity Y} :
    B ∈ F.star (Entity.powerset A) ↔
      B ∈ Entity.powerset (F.star A) ∧ F.IsInternalEntity B := by
  constructor
  · intro hB
    exact ⟨F.mem_powerset_star_of_mem_star_powerset hB, ⟨Entity.powerset A, hB⟩⟩
  · rintro ⟨hBP, ⟨C, hBC⟩⟩
    obtain ⟨hBset, hBsub⟩ := Entity.mem_powerset_iff.1 hBP
    -- Transfer `(∀ x ∈ C) [((x = ∅ ∨ ∃ y ∈ x, y = y) ∧ ∀ y ∈ x, y ∈ A) → x ∈ 𝒫(A)]`
    let φ : UFormula X :=
      .forallIn 0 (.const C)
        (.imp
          (.conj
            (.disj (.eq (.var 0) (.const ∅)) (.existsIn 1 (.var 0) (.eq (.var 1) (.var 1))))
            (.forallIn 1 (.var 0) (.mem (.var 1) (.const A))))
          (.mem (.var 0) (.const (Entity.powerset A))))
    have hsent : IsSentence φ := by
      rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
      intro v; simp [φ, freeVarsUFormula, freeVarsUTerm]
    have hstd : SentenceHolds φ := by
      refine ⟨C, rfl, fun x _ ⟨hset_disj, x', hx', hall⟩ ↦ ?_⟩
      obtain rfl := Option.some.inj (by simpa using hx')
      have hxset : x.IsSet := by
        refine Entity.isSet_iff_eq_empty_or_nonempty.2 ?_
        rcases hset_disj with ⟨w, hw1, hw2⟩ | ⟨x'', hx'', y, hyx, _⟩
        · have h1 : x = w := Option.some.inj (by simpa using hw1)
          have h2 : (∅ : Entity X) = w := Option.some.inj hw2
          exact Or.inl (h1.trans h2.symm)
        · obtain rfl := Option.some.inj (by simpa using hx'')
          exact Or.inr ⟨y, hyx⟩
      refine ⟨x, Entity.powerset A, by simp, rfl, Entity.mem_powerset_iff.2 ⟨hxset, fun y hyx ↦ ?_⟩⟩
      obtain ⟨y', A', hy', hA', hm⟩ := hall y hyx
      have h1 : y = y' := Option.some.inj (by simpa using hy')
      obtain rfl := Option.some.inj hA'
      exact h1 ▸ hm
    obtain ⟨_, hCd, hallC⟩ := (F.transfer φ hsent).1 hstd
    obtain rfl := Option.some.inj hCd
    have hset_hold :
        Holds (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 B)
          (starFormula F.star (.disj (.eq (.var 0) (.const ∅))
            (.existsIn 1 (.var 0) (.eq (.var 1) (.var 1))))) := by
      rcases Entity.isSet_iff_eq_empty_or_nonempty.1 hBset with rfl | ⟨y, hyB⟩
      · exact Or.inl ⟨∅, by simp, by simp [F.star_empty]⟩
      · exact Or.inr ⟨B, by simp, y, hyB, y, by simp, by simp⟩
    have hsub_hold :
        Holds (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 B)
          (starFormula F.star (.forallIn 1 (.var 0) (.mem (.var 1) (.const A)))) :=
      ⟨B, by simp, fun y hyB ↦ ⟨y, F.star A, by simp, rfl, hBsub y hyB⟩⟩
    obtain ⟨B', P', hB', hP', hm⟩ := hallC B hBC ⟨hset_hold, hsub_hold⟩
    have h1 : B = B' := Option.some.inj (by simpa using hB')
    obtain rfl := Option.some.inj hP'
    exact h1 ▸ hm

/-- Set-theoretic reformulation of **Theorem 13.12.1** (Goldblatt §13.12, p. 175):
`(*𝒫(A)).extSet = (𝒫(*A)).extSet ∩ *𝕌`. -/
theorem Framework.star_powerset_extSet_eq {X Y : Type*} (F : Framework X Y) (A : Entity X) :
    (F.star (Entity.powerset A)).extSet =
      (Entity.powerset (F.star A)).extSet ∩ F.internalUniverse := by
  ext B
  exact F.mem_star_powerset_iff

/-- Goldblatt §13.12 (p. 175): Chain of power-set inclusions
`im 𝒫(A) ⊆ *𝒫(A) ⊆ 𝒫(*A)`! -/
theorem Framework.sigmaImage_powerset_subset_star_powerset {X Y : Type*} (F : Framework X Y)
    (A : Entity X) :
    F.sigmaImage (Entity.powerset A) ⊆ (F.star (Entity.powerset A)).extSet ∧
    (F.star (Entity.powerset A)).extSet ⊆ (Entity.powerset (F.star A)).extSet :=
  ⟨fun _ ⟨_, hb, hEq⟩ ↦ hEq ▸ F.mem_star_iff.2 hb,
    fun _ hB ↦ F.mem_powerset_star_of_mem_star_powerset hB⟩

/-! ## §13.13 Exercises on Internal Sets and Functions -/

/-- Successor function `n ↦ n + 1` on `posNatEntity = {1, 2, 3, …}` in `Entity ℝ`
(Goldblatt §13.12–13.13, pp. 175–176). -/
def posNatSucc : Entity ℝ :=
  Entity.mkFuncEntity posNatEntity (fun e ↦ Entity.atom (Entity.atomVal 0 e + 1))

/-- `posNatSucc` is a function `posNatEntity → posNatEntity`. -/
theorem isFuncFromTo_posNatSucc :
    Entity.IsFuncFromTo posNatSucc posNatEntity posNatEntity := by
  refine Entity.isFuncFromTo_mkFuncEntity fun e he ↦ ?_
  obtain ⟨_, ⟨k, hk1, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 he
  exact atom_mem_mkAtomSet_iff.2 ⟨k + 1, by omega, by simp [Entity.atomVal]⟩

/-- Evaluation of `posNatSucc` on `Entity.atom (k : ℝ)` (`k ≥ 1`). -/
theorem funcApp_posNatSucc {k : ℕ} (hk : 1 ≤ k) :
    Entity.funcApp posNatSucc (Entity.atom (k : ℝ)) = Entity.atom ((k + 1 : ℕ) : ℝ) := by
  have he : Entity.atom (k : ℝ) ∈ posNatEntity := atom_mem_mkAtomSet_iff.2 ⟨k, hk, rfl⟩
  have hv := Entity.funcApp_mkFuncEntity
    (B := posNatEntity)
    (g := fun e ↦ Entity.atom (Entity.atomVal 0 e + 1))
    (fun e he' ↦ by
      obtain ⟨_, ⟨m, hm1, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 he'
      exact atom_mem_mkAtomSet_iff.2 ⟨m + 1, by omega, by simp [Entity.atomVal]⟩)
    he
  simpa [posNatSucc, Entity.atomVal, Nat.cast_add, Nat.cast_one] using hv

/-- Goldblatt §13.12 (p. 175): **Internal Least Number Principle** in `*𝕌` — every nonempty
internal subset `B` of `*ℕ` (`B ∈ *𝒫(ℕ)`, equivalently `B ⊆ *ℕ` internal) has a `≤`-least
element! -/
theorem Framework.internal_least_number_principle {Y : Type*} (F : Framework ℝ Y)
    {B : Entity Y} (hB : B ∈ F.star (Entity.powerset posNatEntity))
    (hne : ∃ y : Entity Y, y ∈ B) :
    ∃ y ∈ B, ∀ z ∈ B, Entity.kpair y z ∈ F.star realLeRel := by
  let φ : UFormula ℝ :=
    .forallIn 0 (.const (Entity.powerset posNatEntity))
      (.imp
        (.existsIn 1 (.var 0) (.eq (.var 1) (.var 1)))
        (.existsIn 1 (.var 0)
          (.forallIn 2 (.var 0)
            (.mem (UTerm.pair (.var 1) (.var 2)) (.const realLeRel)))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm]; tauto
  have hstd : SentenceHolds φ := by
    refine ⟨Entity.powerset posNatEntity, rfl, fun X₀ hX₀ ⟨_, hx0, ey₀, hey₀, _⟩ ↦ ?_⟩
    obtain rfl := Option.some.inj (by simpa using hx0)
    obtain ⟨_, hXsub⟩ := Entity.mem_powerset_iff.1 hX₀
    obtain ⟨_, ⟨k₀, _, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 (hXsub ey₀ hey₀)
    classical
    have hex_nat : ∃ k : ℕ, Entity.atom (k : ℝ) ∈ X₀ := ⟨k₀, hey₀⟩
    let m := Nat.find hex_nat
    have hm_mem : Entity.atom (m : ℝ) ∈ X₀ := Nat.find_spec hex_nat
    refine ⟨X₀, by simp, Entity.atom (m : ℝ), hm_mem, X₀, by simp, fun ez hez ↦ ?_⟩
    obtain ⟨_, ⟨k, _, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 (hXsub ez hez)
    have hmk : m ≤ k := Nat.find_min' hex_nat hez
    have hmle : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    exact ⟨Entity.kpair (Entity.atom (m : ℝ)) (Entity.atom (k : ℝ)), realLeRel,
      by simp [evalUTerm_pair], rfl, kpair_atom_mem_realLeRel_iff.2 hmle⟩
  obtain ⟨_, hPd, hallB⟩ := (F.transfer φ hsent).1 hstd
  obtain rfl := Option.some.inj hPd
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨_, hB1, y, hyB, _, hB2, hallZ⟩ :=
    hallB B hB ⟨B, by simp, y₀, hy₀, y₀, by simp, by simp⟩
  obtain rfl := Option.some.inj (by simpa using hB1)
  obtain rfl := Option.some.inj (by simpa using hB2)
  refine ⟨y, hyB, fun z hzB ↦ ?_⟩
  obtain ⟨p, R', hp, hR', hm⟩ := hallZ z hzB
  obtain rfl := Option.some.inj hR'
  have hpeq : Entity.kpair y z = p := Option.some.inj (by simpa [starTerm_pair, evalUTerm_pair] using hp)
  exact hpeq ▸ hm

/-- Goldblatt §13.12 & **Exercise 13.13(1)** (pp. 175–176): **Internal Mathematical Induction** in
`*𝕌` — if `B ⊆ *ℕ` is an internal set containing `*1` and closed under `(*succ)(n) = n + 1`, then
`B = *ℕ`! -/
theorem Framework.internal_induction {Y : Type*} (F : Framework ℝ Y) {B : Entity Y}
    (hBset : B.IsSet) (hBsub : ∀ x ∈ B, x ∈ F.star posNatEntity)
    (hBint : F.IsInternalEntity B)
    (h1 : F.star (Entity.atom 1) ∈ B)
    (hstep : ∀ n ∈ B, Entity.funcApp (F.star posNatSucc) n ∈ B) :
    B = F.star posNatEntity := by
  have hBP : B ∈ F.star (Entity.powerset posNatEntity) :=
    F.mem_star_powerset_iff.2 ⟨Entity.mem_powerset_iff.2 ⟨hBset, hBsub⟩, hBint⟩
  let φ : UFormula ℝ :=
    .forallIn 0 (.const (Entity.powerset posNatEntity))
      (.imp
        (.conj
          (.mem (.const (Entity.atom 1)) (.var 0))
          (.forallIn 1 (.var 0) (.mem (.app (.const posNatSucc) (.var 1)) (.var 0))))
        (.eq (.var 0) (.const posNatEntity)))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm]
  have hstd : SentenceHolds φ := by
    refine ⟨Entity.powerset posNatEntity, rfl, fun X₀ hX₀ ⟨⟨a1, X1, ha1, hX1, hm1⟩, _, hX2, hall⟩ ↦ ?_⟩
    obtain rfl := Option.some.inj ha1
    obtain rfl := Option.some.inj (by simpa using hX1)
    obtain rfl := Option.some.inj (by simpa using hX2)
    obtain ⟨hXset, hXsub⟩ := Entity.mem_powerset_iff.1 hX₀
    have hind : ∀ k : ℕ, 1 ≤ k → Entity.atom (k : ℝ) ∈ X₀ := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => simpa using hm1
      | succ k hk ih =>
          have hkP : Entity.atom (k : ℝ) ∈ posNatEntity := atom_mem_mkAtomSet_iff.2 ⟨k, hk, rfl⟩
          obtain ⟨u, X3, hu, hX3, hmu⟩ := hall (Entity.atom (k : ℝ)) ih
          obtain rfl := Option.some.inj (by simpa using hX3)
          have hfn : evalUTerm
              (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0 X₀) 1
                (Entity.atom (k : ℝ)))
              (.app (.const posNatSucc) (.var 1)) =
              some (Entity.atom ((k + 1 : ℕ) : ℝ)) := by
            rw [evalUTerm_app_eq_some_iff]
            refine ⟨posNatSucc, Entity.atom (k : ℝ), rfl, by simp,
              isFuncFromTo_posNatSucc.isFuncEntity, ?_, funcApp_posNatSucc hk⟩
            rw [isFuncFromTo_posNatSucc.relDom_eq (Entity.isSet_setOfBounded _)]
            exact hkP
          obtain rfl := Option.some.inj (hfn.symm.trans hu)
          exact hmu
    have hEq : X₀ = posNatEntity := by
      refine Entity.set_ext hXset (Entity.isSet_setOfBounded _) fun z ↦
        ⟨fun hz ↦ hXsub z hz, fun hz ↦ ?_⟩
      obtain ⟨_, ⟨k, hk1, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 hz
      exact hind k hk1
    exact ⟨posNatEntity, by simp [hEq], rfl⟩
  obtain ⟨_, hPd, hallB⟩ := (F.transfer φ hsent).1 hstd
  obtain rfl := Option.some.inj hPd
  have hf_star := (F.isFuncFromTo_star_iff).2 isFuncFromTo_posNatSucc
  have hstep_hold :
      Holds (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 B)
        (starFormula F.star (.forallIn 1 (.var 0)
          (.mem (.app (.const posNatSucc) (.var 1)) (.var 0)))) := by
    refine ⟨B, by simp, fun n hnB ↦ ?_⟩
    have hn_dom : n ∈ Entity.relDom (F.star posNatSucc) := by
      rw [hf_star.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_setOfBounded _))]
      exact hBsub n hnB
    refine ⟨Entity.funcApp (F.star posNatSucc) n, B, ?_, by simp, hstep n hnB⟩
    rw [starTerm, evalUTerm_app_eq_some_iff]
    exact ⟨F.star posNatSucc, n, rfl, by simp, hf_star.isFuncEntity, hn_dom, rfl⟩
  obtain ⟨Z, hZ1, hZ2⟩ := hallB B hBP ⟨⟨F.star (Entity.atom 1), B, rfl, by simp, h1⟩, hstep_hold⟩
  exact (Option.some.inj (by simpa using hZ1)).trans (Option.some.inj hZ2).symm

/-- Goldblatt §13.12 (p. 175): Whenever `*ℕ` has a nonstandard element (`*ℕ \ im ℕ ≠ ∅`), the
standard copy `im ℕ = F.sigmaImage posNatEntity` is **external** (no internal set `B` has
`B.extSet = F.sigmaImage posNatEntity`)! -/
theorem Framework.not_exists_internal_extSet_eq_sigmaImage_posNat {Y : Type*} (F : Framework ℝ Y)
    (hns : ∃ ω ∈ F.star posNatEntity, F.IsNonstandard ω) :
    ¬ ∃ B : Entity Y, B.IsSet ∧ F.IsInternalEntity B ∧
        B.extSet = F.sigmaImage posNatEntity := by
  rintro ⟨B, hBset, hBint, hBeq⟩
  obtain ⟨ω, hωP, hωns⟩ := hns
  have hBsub : ∀ x ∈ B, x ∈ F.star posNatEntity := by
    intro x hx
    change x ∈ B.extSet at hx
    rw [hBeq] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact F.mem_star_iff.2 ha
  have h1 : F.star (Entity.atom 1) ∈ B := by
    change F.star (Entity.atom 1) ∈ B.extSet
    rw [hBeq]
    exact ⟨Entity.atom 1, atom_mem_mkAtomSet_iff.2 ⟨1, le_rfl, by norm_num⟩, rfl⟩
  have hstep : ∀ n ∈ B, Entity.funcApp (F.star posNatSucc) n ∈ B := by
    intro n hn
    change n ∈ B.extSet at hn
    rw [hBeq] at hn
    obtain ⟨a, ha, rfl⟩ := hn
    obtain ⟨_, ⟨k, hk1, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 ha
    have hdom : Entity.atom (k : ℝ) ∈ Entity.relDom posNatSucc := by
      rw [isFuncFromTo_posNatSucc.relDom_eq (Entity.isSet_setOfBounded _)]
      exact ha
    rw [← F.star_funcApp isFuncFromTo_posNatSucc.isFuncEntity hdom, funcApp_posNatSucc hk1]
    change F.star (Entity.atom ((k + 1 : ℕ) : ℝ)) ∈ B.extSet
    rw [hBeq]
    exact F.mem_sigmaImage_def.2
      ⟨Entity.atom ((k + 1 : ℕ) : ℝ), atom_mem_mkAtomSet_iff.2 ⟨k + 1, by omega, rfl⟩, rfl⟩
  have hEq : B = F.star posNatEntity := F.internal_induction hBset hBsub hBint h1 hstep
  have hω_sig : ω ∈ F.sigmaImage posNatEntity := by
    rw [← hBeq]
    change ω ∈ B
    exact hEq ▸ hωP
  obtain ⟨a, _, rfl⟩ := hω_sig
  exact hωns (F.isStandard_star a)

/-- Unconditional existence of a nonstandard hypernatural `Entity.atom Hyperreal.omega ∈ *ℕ` in the
concrete `hyperrealFramework` (Goldblatt §13.9 & §13.12, pp. 171, 175). -/
theorem hyperrealFramework_exists_nonstandard_posNat :
    ∃ ω ∈ hyperrealFramework.star posNatEntity, hyperrealFramework.IsNonstandard ω := by
  refine ⟨Entity.atom Hyperreal.omega, ?_, ?_⟩
  · obtain ⟨⟨mP, rP⟩, hrP_eq⟩ := Quotient.exists_rep posNatEntity
    have hev1 : ∀ᶠ n : ℕ in (hyperfilter ℕ : Filter ℕ), 1 ≤ n :=
      Filter.Eventually.filter_mono Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop 1)
    let gω : ℕ → RawStage ℝ 0 := fun n ↦ (n : ℝ)
    let gP : ℕ → RawStage ℝ mP := fun _ ↦ rP
    have hstar : hyperrealFramework.star posNatEntity =
        collapseStage (hyperfilter ℕ) mP (gP : Germ (hyperfilter ℕ : Filter ℕ) (RawStage ℝ mP)) := by
      change ultrapowerStar (hyperfilter ℕ) posNatEntity = _
      rw [← hrP_eq]
      exact ultrapowerStar_ofRaw (hyperfilter ℕ) rP
    rw [hstar]
    change collapseStage (hyperfilter ℕ) 0 (gω : Germ (hyperfilter ℕ : Filter ℕ) (RawStage ℝ 0)) ∈
      collapseStage (hyperfilter ℕ) mP (gP : Germ (hyperfilter ℕ : Filter ℕ) (RawStage ℝ mP))
    exact (collapseStage_coe_mem_iff (hyperfilter ℕ) gω gP).2 (hev1.mono fun n hn ↦ by
      change Entity.atom (n : ℝ) ∈ Entity.ofRaw rP
      have hrep : Entity.ofRaw rP = posNatEntity := hrP_eq
      rw [hrep]
      exact atom_mem_mkAtomSet_iff.2 ⟨n, hn, rfl⟩)
  · rintro ⟨a, haEq⟩
    have hatom : a.IsAtom :=
      (hyperrealFramework.isAtom_star_iff).1 (haEq ▸ Entity.isAtom_atom Hyperreal.omega)
    obtain ⟨r, rfl⟩ := hatom
    have hr : Hyperreal.omega = (r : ℝ*) :=
      Entity.atom_inj.1 (haEq.trans (hyperrealFramework.star_atom r))
    exact (Hyperreal.coe_lt_omega r).ne hr.symm

/-- Goldblatt **Exercise 13.13(1)** (p. 176): **Internal Order-Completeness** in `*𝕌` — every
nonempty internal subset `B ⊆ *ℝ` that is bounded above in `*ℝ` has a least upper bound in `*ℝ`! -/
theorem Framework.internal_order_completeness {Y : Type*} (F : Framework ℝ Y) {B : Entity Y}
    (hBset : B.IsSet) (hBsub : ∀ x ∈ B, x ∈ F.star realEntity)
    (hBint : F.IsInternalEntity B)
    (hne : ∃ x : Entity Y, x ∈ B)
    (hbdd : ∃ u ∈ F.star realEntity, ∀ x ∈ B, Entity.kpair x u ∈ F.star realLeRel) :
    ∃ s ∈ F.star realEntity,
      (∀ x ∈ B, Entity.kpair x s ∈ F.star realLeRel) ∧
      (∀ u ∈ F.star realEntity,
        (∀ x ∈ B, Entity.kpair x u ∈ F.star realLeRel) →
          Entity.kpair s u ∈ F.star realLeRel) := by
  have hBP : B ∈ F.star (Entity.powerset realEntity) :=
    F.mem_star_powerset_iff.2 ⟨Entity.mem_powerset_iff.2 ⟨hBset, hBsub⟩, hBint⟩
  let φ : UFormula ℝ :=
    .forallIn 0 (.const (Entity.powerset realEntity))
      (.imp
        (.conj
          (.existsIn 1 (.var 0) (.eq (.var 1) (.var 1)))
          (.existsIn 2 (.const realEntity)
            (.forallIn 1 (.var 0) (.mem (UTerm.pair (.var 1) (.var 2)) (.const realLeRel)))))
        (.existsIn 3 (.const realEntity)
          (.conj
            (.forallIn 1 (.var 0) (.mem (UTerm.pair (.var 1) (.var 3)) (.const realLeRel)))
            (.forallIn 2 (.const realEntity)
              (.imp
                (.forallIn 1 (.var 0) (.mem (UTerm.pair (.var 1) (.var 2)) (.const realLeRel)))
                (.mem (UTerm.pair (.var 3) (.var 2)) (.const realLeRel)))))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm]; tauto
  have hstd : SentenceHolds φ := by
    refine ⟨Entity.powerset realEntity, rfl,
      fun X₀ hX₀ ⟨⟨_, hX1, ex₀, hex₀, _⟩, ⟨_, hR1, eu₀, heu₀, _, hX2, hub₀⟩⟩ ↦ ?_⟩
    obtain rfl := Option.some.inj (by simpa using hX1)
    obtain rfl := Option.some.inj hR1
    obtain rfl := Option.some.inj (by simpa using hX2)
    obtain ⟨_, hXsub⟩ := Entity.mem_powerset_iff.1 hX₀
    obtain ⟨x₀, rfl⟩ := mem_baseSet_iff.1 (hXsub ex₀ hex₀)
    obtain ⟨u₀, rfl⟩ := mem_baseSet_iff.1 heu₀
    let S : Set ℝ := {r : ℝ | Entity.atom r ∈ X₀}
    have hS_ne : S.Nonempty := ⟨x₀, hex₀⟩
    have hS_bdd : BddAbove S := ⟨u₀, fun r hr ↦ by
      obtain ⟨p, R', hp, hR', hm⟩ := hub₀ (Entity.atom r) hr
      obtain rfl := Option.some.inj hR'
      have hpeq : Entity.kpair (Entity.atom r) (Entity.atom u₀) = p :=
        Option.some.inj (by simpa [evalUTerm_pair] using hp)
      exact kpair_atom_mem_realLeRel_iff.1 (hpeq ▸ hm)⟩
    let s : ℝ := sSup S
    refine ⟨realEntity, rfl, Entity.atom s, mem_baseSet_iff.2 ⟨s, rfl⟩,
      ⟨X₀, by simp, fun ex hex ↦ ?_⟩,
      ⟨realEntity, rfl, fun eu heu ⟨_, hX3, hub⟩ ↦ ?_⟩⟩
    · obtain ⟨r, rfl⟩ := mem_baseSet_iff.1 (hXsub ex hex)
      exact ⟨Entity.kpair (Entity.atom r) (Entity.atom s), realLeRel,
        by simp [evalUTerm_pair], rfl, kpair_atom_mem_realLeRel_iff.2 (le_csSup hS_bdd hex)⟩
    · obtain rfl := Option.some.inj (by simpa using hX3)
      obtain ⟨u, rfl⟩ := mem_baseSet_iff.1 heu
      have hle : s ≤ u := csSup_le hS_ne fun r hr ↦ by
        obtain ⟨p, R', hp, hR', hm⟩ := hub (Entity.atom r) hr
        obtain rfl := Option.some.inj hR'
        have hpeq : Entity.kpair (Entity.atom r) (Entity.atom u) = p :=
          Option.some.inj (by simpa [evalUTerm_pair] using hp)
        exact kpair_atom_mem_realLeRel_iff.1 (hpeq ▸ hm)
      exact ⟨Entity.kpair (Entity.atom s) (Entity.atom u), realLeRel,
        by simp [evalUTerm_pair], rfl, kpair_atom_mem_realLeRel_iff.2 hle⟩
  obtain ⟨_, hPd, hallB⟩ := (F.transfer φ hsent).1 hstd
  obtain rfl := Option.some.inj hPd
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨u₀, hu₀R, hu₀ub⟩ := hbdd
  obtain ⟨_, hRd, s, hsR, ⟨_, hB1, hs_ub⟩, ⟨_, hR2, hs_lub⟩⟩ := hallB B hBP ⟨
    ⟨B, by simp, x₀, hx₀, x₀, by simp, by simp⟩,
    ⟨F.star realEntity, rfl, u₀, hu₀R, B, by simp, fun x hxB ↦
      ⟨Entity.kpair x u₀, F.star realLeRel,
        by simp [starTerm_pair, evalUTerm_pair], rfl, hu₀ub x hxB⟩⟩⟩
  obtain rfl := Option.some.inj hRd
  obtain rfl := Option.some.inj (by simpa using hB1)
  obtain rfl := Option.some.inj hR2
  refine ⟨s, hsR, fun x hxB ↦ ?_, fun u huR hub ↦ ?_⟩
  · obtain ⟨p, R', hp, hR', hm⟩ := hs_ub x hxB
    obtain rfl := Option.some.inj hR'
    have hpeq : Entity.kpair x s = p :=
      Option.some.inj (by simpa [starTerm_pair, evalUTerm_pair] using hp)
    exact hpeq ▸ hm
  · obtain ⟨p, R', hp, hR', hm⟩ := hs_lub u huR
      ⟨B, by simp, fun x hxB ↦ ⟨Entity.kpair x u, F.star realLeRel,
        by simp [starTerm_pair, evalUTerm_pair], rfl, hub x hxB⟩⟩
    obtain rfl := Option.some.inj hR'
    have hpeq : Entity.kpair s u = p :=
      Option.some.inj (by simpa [starTerm_pair, evalUTerm_pair] using hp)
    exact hpeq ▸ hm

/-- Goldblatt **Exercise 13.13(3)** (p. 176): For any entities `A, B : Entity X`, `*(B^A)`
(`F.star (Entity.funSpace A B)`) is the exact set of all **internal** functions from `*A` to `*B`! -/
theorem Framework.mem_star_funSpace_iff {X Y : Type*} (F : Framework X Y) {A B : Entity X}
    {f : Entity Y} :
    f ∈ F.star (Entity.funSpace A B) ↔
      Entity.IsFuncFromTo f (F.star A) (F.star B) ∧ F.IsInternalEntity f := by
  let ψ : UFormula X :=
    .conj
      (.forallIn 1 (.const A)
        (.forallIn 2 (.const B)
          (.forallIn 3 (.const B)
            (.imp
              (.conj
                (.mem (UTerm.pair (.var 1) (.var 2)) (.var 0))
                (.mem (UTerm.pair (.var 1) (.var 3)) (.var 0)))
              (.eq (.var 2) (.var 3))))))
      (.forallIn 1 (.const A)
        (.existsIn 2 (.const B)
          (.mem (UTerm.pair (.var 1) (.var 2)) (.var 0))))
  have hsub : ∀ g ∈ Entity.funSpace A B, g ∈ Entity.powerset (Entity.prod A B) := fun g hg ↦ by
    obtain ⟨hgset, hgprod, _, _⟩ := Entity.mem_funSpace_iff.1 hg
    exact Entity.mem_powerset_iff.2 ⟨hgset, fun p hp ↦ Entity.mem_prod_iff.2 (hgprod p hp)⟩
  have hEq := F.star_set_eq_of_bounded
    (S := Entity.funSpace A B) (T := Entity.powerset (Entity.prod A B)) (φ := ψ)
    (Entity.isSet_funSpace A B) hsub
    (by intro v hv; simp [ψ, freeVarsUFormula, freeVarsUTerm] at hv; omega)
    (fun g hgP ↦ by
      obtain ⟨hgset, hgsub⟩ := Entity.mem_powerset_iff.1 hgP
      rw [Entity.mem_funSpace_iff]
      constructor
      · rintro ⟨_, _, hgsv, hgtot⟩
        refine ⟨⟨A, rfl, fun a ha ↦ ⟨B, rfl, fun b₁ hb₁ ↦ ⟨B, rfl, fun b₂ hb₂ ⟨⟨p1, g1, hp1, hg1, hm1⟩, ⟨p2, g2, hp2, hg2, hm2⟩⟩ ↦ ?_⟩⟩⟩,
          ⟨A, rfl, fun a ha ↦ ?_⟩⟩
        · obtain rfl := Option.some.inj (by simpa using hg1)
          obtain rfl := Option.some.inj (by simpa using hg2)
          have h1 : Entity.kpair a b₁ = p1 := Option.some.inj (by simpa [evalUTerm_pair] using hp1)
          have h2 : Entity.kpair a b₂ = p2 := Option.some.inj (by simpa [evalUTerm_pair] using hp2)
          have hbeq : b₁ = b₂ := hgsv a b₁ b₂ (h1 ▸ hm1) (h2 ▸ hm2)
          exact ⟨b₁, by simp, by simp [hbeq]⟩
        · obtain ⟨b, hbB, hp⟩ := hgtot a ha
          exact ⟨B, rfl, b, hbB, Entity.kpair a b, g, by simp [evalUTerm_pair], by simp, hp⟩
      · rintro ⟨⟨_, hAd, hsv⟩, ⟨_, hAd', htot⟩⟩
        obtain rfl := Option.some.inj hAd
        obtain rfl := Option.some.inj hAd'
        refine ⟨hgset, fun p hp ↦ Entity.mem_prod_iff.1 (hgsub p hp),
          fun a b₁ b₂ hm1 hm2 ↦ ?_, fun a ha ↦ ?_⟩
        · obtain ⟨ha, hb₁⟩ := Entity.kpair_mem_prod_iff.1 (hgsub _ hm1)
          obtain ⟨_, hb₂⟩ := Entity.kpair_mem_prod_iff.1 (hgsub _ hm2)
          obtain ⟨_, hB1, hb_all⟩ := hsv a ha; obtain rfl := Option.some.inj hB1
          obtain ⟨_, hB2, hc_all⟩ := hb_all b₁ hb₁; obtain rfl := Option.some.inj hB2
          obtain ⟨z, hz1, hz2⟩ := hc_all b₂ hb₂ ⟨
            ⟨Entity.kpair a b₁, g, by simp [evalUTerm_pair], by simp, hm1⟩,
            ⟨Entity.kpair a b₂, g, by simp [evalUTerm_pair], by simp, hm2⟩⟩
          exact (Option.some.inj (by simpa using hz1)).trans
            (Option.some.inj (by simpa using hz2)).symm
        · obtain ⟨_, hBd, b, hbB, p, g', hp, hg', hm⟩ := htot a ha
          obtain rfl := Option.some.inj hBd
          obtain rfl := Option.some.inj (by simpa using hg')
          have hpeq : Entity.kpair a b = p := Option.some.inj (by simpa [evalUTerm_pair] using hp)
          exact ⟨b, hbB, hpeq ▸ hm⟩)
  have hbdd : IsBoundedRank {g : Entity Y |
      g ∈ F.star (Entity.powerset (Entity.prod A B)) ∧
        Holds (fun _ ↦ g) (starFormula F.star ψ)} :=
    (F.star (Entity.powerset (Entity.prod A B))).isBoundedRank_extSet.subset fun _ h ↦ h.1
  rw [hEq, Entity.mem_setOfBounded hbdd, Set.mem_ofPred, F.mem_star_powerset_iff, F.star_prod]
  constructor
  · rintro ⟨⟨hfP, hfint⟩, ⟨⟨_, hAd, hsv⟩, ⟨_, hAd', htot⟩⟩⟩
    obtain rfl := Option.some.inj hAd; obtain rfl := Option.some.inj hAd'
    obtain ⟨hfset, hfsub⟩ := Entity.mem_powerset_iff.1 hfP
    refine ⟨⟨hfset, fun p hp ↦ Entity.mem_prod_iff.1 (hfsub p hp),
      fun a b₁ b₂ hm1 hm2 ↦ ?_, fun a ha ↦ ?_⟩, hfint⟩
    · obtain ⟨ha, hb₁⟩ := Entity.kpair_mem_prod_iff.1 (hfsub _ hm1)
      obtain ⟨_, hb₂⟩ := Entity.kpair_mem_prod_iff.1 (hfsub _ hm2)
      obtain ⟨_, hB1, hb_all⟩ := hsv a ha; obtain rfl := Option.some.inj hB1
      obtain ⟨_, hB2, hc_all⟩ := hb_all b₁ hb₁; obtain rfl := Option.some.inj hB2
      obtain ⟨z, hz1, hz2⟩ := hc_all b₂ hb₂ ⟨
        ⟨Entity.kpair a b₁, f, by simp [starTerm_pair, evalUTerm_pair], by simp, hm1⟩,
        ⟨Entity.kpair a b₂, f, by simp [starTerm_pair, evalUTerm_pair], by simp, hm2⟩⟩
      exact (Option.some.inj (by simpa using hz1)).trans
        (Option.some.inj (by simpa using hz2)).symm
    · obtain ⟨_, hBd, b, hbB, p, f', hp, hf', hm⟩ := htot a ha
      obtain rfl := Option.some.inj hBd
      obtain rfl := Option.some.inj (by simpa using hf')
      have hpeq : Entity.kpair a b = p :=
        Option.some.inj (by simpa [starTerm_pair, evalUTerm_pair] using hp)
      exact ⟨b, hbB, hpeq ▸ hm⟩
  · rintro ⟨⟨hfset, hfprod, hfsv, hftot⟩, hfint⟩
    refine ⟨⟨Entity.mem_powerset_iff.2 ⟨hfset, fun p hp ↦ Entity.mem_prod_iff.2 (hfprod p hp)⟩,
      hfint⟩, ?_, ?_⟩
    · refine ⟨F.star A, rfl, fun a ha ↦ ⟨F.star B, rfl, fun b₁ hb₁ ↦
        ⟨F.star B, rfl, fun b₂ hb₂ ⟨⟨p1, f1, hp1, hf1, hm1⟩, ⟨p2, f2, hp2, hf2, hm2⟩⟩ ↦ ?_⟩⟩⟩
      obtain rfl := Option.some.inj (by simpa using hf1)
      obtain rfl := Option.some.inj (by simpa using hf2)
      have h1 : Entity.kpair a b₁ = p1 :=
        Option.some.inj (by simpa [starTerm_pair, evalUTerm_pair] using hp1)
      have h2 : Entity.kpair a b₂ = p2 :=
        Option.some.inj (by simpa [starTerm_pair, evalUTerm_pair] using hp2)
      have hbeq : b₁ = b₂ := hfsv a b₁ b₂ (h1 ▸ hm1) (h2 ▸ hm2)
      exact ⟨b₁, by simp, by simp [hbeq]⟩
    · refine ⟨F.star A, rfl, fun a ha ↦ ?_⟩
      obtain ⟨b, hbB, hp⟩ := hftot a ha
      exact ⟨F.star B, rfl, b, hbB, Entity.kpair a b, f,
        by simp [starTerm_pair, evalUTerm_pair], by simp, hp⟩

/-- Characteristic function `χ_B : A → {e₀, e₁}` mapping `x ∈ B` to `e₁` and `x ∈ A \ B` to `e₀`
(Goldblatt **Exercise 13.13(2)**, p. 176, taking `e₀ = 0, e₁ = 1` over `ℝ`). -/
def charFunEntity {X : Type*} (A B e₀ e₁ : Entity X) : Entity X :=
  open Classical in
  Entity.mkFuncEntity A (fun x ↦ if x ∈ B then e₁ else e₀)

/-- `charFunEntity A B e₀ e₁` belongs to `Entity.funSpace A (Entity.upair e₀ e₁)`. -/
theorem charFunEntity_mem_funSpace {X : Type*} (A B e₀ e₁ : Entity X) :
    charFunEntity A B e₀ e₁ ∈ Entity.funSpace A (Entity.upair e₀ e₁) := by
  classical
  rw [Entity.mem_funSpace_iff]
  refine Entity.isFuncFromTo_mkFuncEntity fun x _ ↦ ?_
  split_ifs
  · exact Entity.mem_upair_iff.2 (Or.inr rfl)
  · exact Entity.mem_upair_iff.2 (Or.inl rfl)

/-- Characteristic-function map `B ↦ χ_B` from `𝒫(A)` to `{e₀, e₁}^A`
(Goldblatt **Exercise 13.13(2)**, p. 176). -/
def powersetToCharFun {X : Type*} (A e₀ e₁ : Entity X) : Entity X :=
  Entity.mkFuncEntity (Entity.powerset A) (fun B ↦ charFunEntity A B e₀ e₁)

/-- Goldblatt **Exercise 13.13(2) (Part 1)** (p. 176): For any set `A : Entity X` and any two
distinct entities `e₀ ≠ e₁` (such as `0` and `1` in `Entity ℝ`), `𝒫(A)` is in bijective
correspondence with `{e₀, e₁}^A` (`Entity.funSpace A (Entity.upair e₀ e₁)`)! -/
theorem isBijectiveFromTo_powersetToCharFun {X : Type*} {A e₀ e₁ : Entity X}
    (hA : A.IsSet) (hne : e₀ ≠ e₁) :
    Entity.IsBijectiveFromTo (powersetToCharFun A e₀ e₁)
      (Entity.powerset A) (Entity.funSpace A (Entity.upair e₀ e₁)) := by
  classical
  have hgP : ∀ B ∈ Entity.powerset A,
      charFunEntity A B e₀ e₁ ∈ Entity.funSpace A (Entity.upair e₀ e₁) :=
    fun B _ ↦ charFunEntity_mem_funSpace A B e₀ e₁
  have hfunc : Entity.IsFuncFromTo (powersetToCharFun A e₀ e₁)
      (Entity.powerset A) (Entity.funSpace A (Entity.upair e₀ e₁)) :=
    Entity.isFuncFromTo_mkFuncEntity hgP
  have hval_char : ∀ B (x : Entity X), x ∈ A →
      Entity.funcApp (charFunEntity A B e₀ e₁) x = (if x ∈ B then e₁ else e₀) := by
    intro B x hxA
    have hv := Entity.funcApp_mkFuncEntity (B := Entity.upair e₀ e₁)
      (g := fun z ↦ if z ∈ B then e₁ else e₀)
      (fun z _ ↦ by split_ifs <;> simp [Entity.mem_upair_iff]) hxA
    simpa [charFunEntity] using hv
  refine ⟨⟨hfunc, fun f hf ↦ ?_⟩, ⟨hfunc.isFuncEntity, fun B₁ B₂ f hp1 hp2 ↦ ?_⟩⟩
  · have hfF := Entity.mem_funSpace_iff.1 hf
    let B : Entity X := Entity.setOfBounded {x : Entity X | x ∈ A ∧ Entity.funcApp f x = e₁}
    have hB_bdd : IsBoundedRank {x : Entity X | x ∈ A ∧ Entity.funcApp f x = e₁} :=
      A.isBoundedRank_extSet.subset fun _ h ↦ h.1
    have hBP : B ∈ Entity.powerset A :=
      Entity.mem_powerset_iff.2 ⟨Entity.isSet_setOfBounded _, fun x hx ↦
        ((Entity.mem_setOfBounded hB_bdd).1 hx).1⟩
    have hdomB : B ∈ Entity.relDom (powersetToCharFun A e₀ e₁) := by
      rw [hfunc.relDom_eq (Entity.isSet_powerset A)]; exact hBP
    have hfeq : charFunEntity A B e₀ e₁ = f := by
      have hcF := Entity.mem_funSpace_iff.1 (charFunEntity_mem_funSpace A B e₀ e₁)
      refine Entity.set_ext hcF.1 hfF.1 fun p ↦ ?_
      constructor
      · intro hp
        obtain ⟨x, hxA, y, _, rfl⟩ := hcF.2.1 p hp
        have hy : y = if x ∈ B then e₁ else e₀ :=
          (((Entity.kpair_mem_iff_funcApp_eq hcF.isFuncEntity).1 hp).2).symm.trans
            (hval_char B x hxA)
        have hxdom : x ∈ Entity.relDom f := by rw [hfF.relDom_eq hA]; exact hxA
        have hfy_mem : Entity.funcApp f x ∈ Entity.upair e₀ e₁ :=
          hfF.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨x, Entity.kpair_funcApp_mem hxdom⟩)
        have hfy_eq : Entity.funcApp f x = y := by
          rw [hy]
          by_cases hxB : x ∈ B
          · simp only [hxB, ↓reduceIte]
            exact ((Entity.mem_setOfBounded hB_bdd).1 hxB).2
          · simp only [hxB, ↓reduceIte]
            rcases Entity.mem_upair_iff.1 hfy_mem with h0 | h1
            · exact h0
            · exact absurd ((Entity.mem_setOfBounded hB_bdd).2 ⟨hxA, h1⟩) hxB
        exact hfy_eq ▸ Entity.kpair_funcApp_mem hxdom
      · intro hp
        obtain ⟨x, hxA, y, _, rfl⟩ := hfF.2.1 p hp
        have hy : Entity.funcApp f x = y :=
          ((Entity.kpair_mem_iff_funcApp_eq hfF.isFuncEntity).1 hp).2
        have hxdom : x ∈ Entity.relDom (charFunEntity A B e₀ e₁) := by
          rw [hcF.relDom_eq hA]; exact hxA
        have hcy : Entity.funcApp (charFunEntity A B e₀ e₁) x = y := by
          rw [hval_char B x hxA]
          by_cases hxB : x ∈ B
          · simp only [hxB, ↓reduceIte]
            exact (((Entity.mem_setOfBounded hB_bdd).1 hxB).2).symm.trans hy
          · simp only [hxB, ↓reduceIte]
            have hy_mem : y ∈ Entity.upair e₀ e₁ :=
              hfF.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨x, hp⟩)
            rcases Entity.mem_upair_iff.1 hy_mem with rfl | rfl
            · rfl
            · exact absurd ((Entity.mem_setOfBounded hB_bdd).2 ⟨hxA, hy⟩) hxB
        exact hcy ▸ Entity.kpair_funcApp_mem hxdom
    have happ : Entity.funcApp (powersetToCharFun A e₀ e₁) B = f := by
      have hv : Entity.funcApp (powersetToCharFun A e₀ e₁) B = charFunEntity A B e₀ e₁ := by
        simpa [powersetToCharFun] using Entity.funcApp_mkFuncEntity hgP hBP
      exact hv.trans hfeq
    exact ⟨B, hBP, happ ▸ Entity.kpair_funcApp_mem hdomB⟩
  · obtain ⟨B₁', hB₁P, _, _, heq1⟩ := hfunc.2.1 _ hp1
    obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 heq1
    obtain ⟨B₂', hB₂P, _, _, heq2⟩ := hfunc.2.1 _ hp2
    obtain ⟨rfl, _⟩ := Entity.kpair_inj.1 heq2
    obtain ⟨hB₁set, hB₁sub⟩ := Entity.mem_powerset_iff.1 hB₁P
    obtain ⟨hB₂set, hB₂sub⟩ := Entity.mem_powerset_iff.1 hB₂P
    have hf1 : charFunEntity A B₁ e₀ e₁ = f := by
      have hv : Entity.funcApp (powersetToCharFun A e₀ e₁) B₁ = charFunEntity A B₁ e₀ e₁ := by
        simpa [powersetToCharFun] using Entity.funcApp_mkFuncEntity hgP hB₁P
      exact hv.symm.trans (((Entity.kpair_mem_iff_funcApp_eq hfunc.isFuncEntity).1 hp1).2)
    have hf2 : charFunEntity A B₂ e₀ e₁ = f := by
      have hv : Entity.funcApp (powersetToCharFun A e₀ e₁) B₂ = charFunEntity A B₂ e₀ e₁ := by
        simpa [powersetToCharFun] using Entity.funcApp_mkFuncEntity hgP hB₂P
      exact hv.symm.trans (((Entity.kpair_mem_iff_funcApp_eq hfunc.isFuncEntity).1 hp2).2)
    have hc_eq : charFunEntity A B₁ e₀ e₁ = charFunEntity A B₂ e₀ e₁ := hf1.trans hf2.symm
    refine Entity.set_ext hB₁set hB₂set fun x ↦ ?_
    constructor
    · intro hx1
      have hv := hval_char B₁ x (hB₁sub x hx1)
      rw [hc_eq, hval_char B₂ x (hB₁sub x hx1)] at hv
      simp only [hx1, ↓reduceIte] at hv
      by_contra hx2
      simp only [hx2, ↓reduceIte] at hv
      exact hne hv
    · intro hx2
      have hv := hval_char B₂ x (hB₂sub x hx2)
      rw [← hc_eq, hval_char B₁ x (hB₂sub x hx2)] at hv
      simp only [hx2, ↓reduceIte] at hv
      by_contra hx1
      simp only [hx1, ↓reduceIte] at hv
      exact hne hv

/-- Goldblatt **Exercise 13.13(2) (Part 2)** (p. 176): Under any framework `F`, `*𝒫(A)` is in
internal bijective correspondence (via `F.star (powersetToCharFun A e₀ e₁)`) with
`*({e₀, e₁}^A)` — which by **Exercise 13.13(3)** is the exact set of all **internal** functions
`f : *A → {*e₀, *e₁}` (for `e₀ = 0, e₁ = 1` in `Entity ℝ`, all internal functions `*A → {0, 1}`)! -/
theorem Framework.star_powerset_bijective_internal_charFuns {X Y : Type*} (F : Framework X Y)
    {A e₀ e₁ : Entity X} (hA : A.IsSet) (hne : e₀ ≠ e₁) :
    Entity.IsBijectiveFromTo
      (F.star (powersetToCharFun A e₀ e₁))
      (F.star (Entity.powerset A))
      (F.star (Entity.funSpace A (Entity.upair e₀ e₁))) ∧
    ∀ f : Entity Y,
      f ∈ F.star (Entity.funSpace A (Entity.upair e₀ e₁)) ↔
        Entity.IsFuncFromTo f (F.star A) (Entity.upair (F.star e₀) (F.star e₁)) ∧
          F.IsInternalEntity f := by
  refine ⟨(F.isBijectiveFromTo_star_iff).2 (isBijectiveFromTo_powersetToCharFun hA hne),
    fun f ↦ ?_⟩
  rw [F.mem_star_funSpace_iff, F.star_upair]

/-! ## §13.14 External Images Are External (Theorem 13.14.1, Exercises 13.14.2–13.14.3) -/

/-- Entity representation of the external image `im A = {*a : a ∈ A} ⊆ *A` inside `Entity Y`
(`𝕌'`), well-defined because `F.sigmaImage A ⊆ (F.star A).extSet` has bounded rank
(Goldblatt §13.9 & §13.14, pp. 172, 176–177). -/
def Framework.imEntity {X Y : Type*} (F : Framework X Y) (A : Entity X) : Entity Y :=
  Entity.setOfBounded (F.sigmaImage A)

/-- `F.imEntity A` is a set entity in `Entity Y`. -/
@[simp]
theorem Framework.isSet_imEntity {X Y : Type*} (F : Framework X Y) (A : Entity X) :
    (F.imEntity A).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `F.imEntity A` is membership in `F.sigmaImage A` (`b ∈ im A ↔ ∃ a ∈ A, *a = b`). -/
@[simp]
theorem Framework.mem_imEntity_iff {X Y : Type*} (F : Framework X Y) {A : Entity X} {b : Entity Y} :
    b ∈ F.imEntity A ↔ b ∈ F.sigmaImage A :=
  Entity.mem_setOfBounded
    ((F.star A).isBoundedRank_extSet.subset fun _ hb ↦ by
      obtain ⟨a, ha, rfl⟩ := hb
      exact F.mem_star_iff.2 ha)

/-- Extension of `F.imEntity A` equals `F.sigmaImage A`. -/
@[simp]
theorem Framework.extSet_imEntity {X Y : Type*} (F : Framework X Y) (A : Entity X) :
    (F.imEntity A).extSet = F.sigmaImage A := by
  ext b; exact F.mem_imEntity_iff

/-- `F.imEntity A` always belongs to `Entity.powerset (F.star A)` (`im A ∈ 𝒫(*A)`;
Goldblatt §13.14, p. 177). -/
theorem Framework.imEntity_mem_powerset_star {X Y : Type*} (F : Framework X Y) (A : Entity X) :
    F.imEntity A ∈ Entity.powerset (F.star A) :=
  Entity.mem_powerset_iff.2 ⟨F.isSet_imEntity A, fun b hb ↦ by
    obtain ⟨a, ha, rfl⟩ := F.mem_imEntity_iff.1 hb
    exact F.mem_star_iff.2 ha⟩

/-- Goldblatt **Exercise 13.14.2** (p. 176): If `f : N₀ → A` is an injective function in `Entity X`
with `X₀ = ran f`, then the inverse image of `im X₀` under `*f` is `im N₀`:
`Entity.relPreimage (F.star f) (F.imEntity X₀) = F.imEntity N₀` (`(*f)⁻¹(im X₀) = im N₀`)! -/
theorem Framework.relPreimage_star_imEntity_relRan {X Y : Type*} (F : Framework X Y)
    {f N₀ A : Entity X} (hN₀ : N₀.IsSet) (hf : Entity.IsFuncFromTo f N₀ A)
    (hinj : f.IsInjectiveFunc) :
    Entity.relPreimage (F.star f) (F.imEntity (Entity.relRan f)) = F.imEntity N₀ := by
  have hinj_star : (F.star f).IsInjectiveFunc := (F.isInjectiveFunc_star_iff).2 hinj
  refine Entity.set_ext (Entity.isSet_relPreimage _ _) (F.isSet_imEntity N₀) fun y ↦ ?_
  rw [Entity.mem_relPreimage_iff, F.mem_imEntity_iff]
  constructor
  · rintro ⟨b, hbX, hp⟩
    obtain ⟨x, hxRan, rfl⟩ := F.mem_imEntity_iff.1 hbX
    obtain ⟨n, hnfx⟩ := Entity.mem_relRan_iff.1 hxRan
    obtain ⟨n', hn'N, _, _, heqn⟩ := hf.2.1 _ hnfx
    obtain ⟨rfl, _⟩ := Entity.kpair_inj.1 heqn
    have hp_std : Entity.kpair (F.star n) (F.star x) ∈ F.star f := by
      rw [← F.star_kpair]
      exact F.mem_star_iff.2 hnfx
    have hyeq : y = F.star n := hinj_star.2 y (F.star n) (F.star x) hp hp_std
    exact ⟨n, hn'N, hyeq.symm⟩
  · rintro ⟨n, hnN, rfl⟩
    have hndom : n ∈ Entity.relDom f := by rw [hf.relDom_eq hN₀]; exact hnN
    have hp : Entity.kpair n (Entity.funcApp f n) ∈ f := Entity.kpair_funcApp_mem hndom
    have hxRan : Entity.funcApp f n ∈ Entity.relRan f := Entity.mem_relRan_iff.2 ⟨n, hp⟩
    refine ⟨F.star (Entity.funcApp f n), F.mem_imEntity_iff.2 ⟨_, hxRan, rfl⟩, ?_⟩
    rw [← F.star_kpair]
    exact F.mem_star_iff.2 hp

/-- Goldblatt **Theorem 13.14.1** (pp. 176–177, General Framework Form): Suppose `N₀ : Entity X` is
a countably infinite set whose external image `F.imEntity N₀` is external. Then for **every**
infinite set `A : Entity X` (`A.extSet.Infinite`):
1. `F.IsExternalEntity (F.imEntity A)` (`im A` is external!),
2. `∃ b ∈ F.star A, F.IsNonstandard b` (`*A \ im A ≠ ∅`, so `*A` has nonstandard elements!),
3. `F.star (Entity.powerset A) ≠ Entity.powerset (F.star A)` (`*𝒫(A)` is a proper subset of `𝒫(*A)`). -/
theorem Framework.isExternalEntity_imEntity_of_infinite_general {X Y : Type*} (F : Framework X Y)
    {N₀ : Entity X} (hN₀set : N₀.IsSet) (hN₀count : Nonempty (ℕ ≃ N₀.extSet))
    (hN₀ext : F.IsExternalEntity (F.imEntity N₀))
    {A : Entity X} (hAinf : A.extSet.Infinite) :
    F.IsExternalEntity (F.imEntity A) ∧
    (∃ b ∈ F.star A, F.IsNonstandard b) ∧
    F.star (Entity.powerset A) ≠ Entity.powerset (F.star A) := by
  classical
  have h1 : F.IsExternalEntity (F.imEntity A) := by
    intro hAim_int
    let eN : ℕ ≃ N₀.extSet := Classical.choice hN₀count
    let eA : ℕ ↪ A.extSet := hAinf.natEmbedding
    let g : Entity X → Entity X := fun z ↦
      if hz : z ∈ N₀.extSet then (eA (eN.symm ⟨z, hz⟩)).1 else ∅
    have hgA : ∀ z ∈ N₀, g z ∈ A := by
      intro z hz
      have hz' : z ∈ N₀.extSet := hz
      simp only [g, hz', ↓reduceDIte]
      exact (eA (eN.symm ⟨z, hz'⟩)).2
    let f : Entity X := Entity.mkFuncEntity N₀ g
    have hf : Entity.IsFuncFromTo f N₀ A := Entity.isFuncFromTo_mkFuncEntity hgA
    have hinj : f.IsInjectiveFunc := by
      refine ⟨hf.isFuncEntity, fun z₁ z₂ b hp1 hp2 ↦ ?_⟩
      obtain ⟨_, hz₁N, _, _, heq1⟩ := hf.2.1 _ hp1
      obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 heq1
      obtain ⟨_, hz₂N, _, _, heq2⟩ := hf.2.1 _ hp2
      obtain ⟨rfl, _⟩ := Entity.kpair_inj.1 heq2
      have hv1 : g z₁ = b :=
        (Entity.funcApp_mkFuncEntity hgA hz₁N).symm.trans
          (((Entity.kpair_mem_iff_funcApp_eq hf.isFuncEntity).1 hp1).2)
      have hv2 : g z₂ = b :=
        (Entity.funcApp_mkFuncEntity hgA hz₂N).symm.trans
          (((Entity.kpair_mem_iff_funcApp_eq hf.isFuncEntity).1 hp2).2)
      have hz₁' : z₁ ∈ N₀.extSet := hz₁N
      have hz₂' : z₂ ∈ N₀.extSet := hz₂N
      simp only [g, hz₁', hz₂', ↓reduceDIte] at hv1 hv2
      have hsub_eq : eA (eN.symm ⟨z₁, hz₁'⟩) = eA (eN.symm ⟨z₂, hz₂'⟩) :=
        Subtype.ext (hv1.trans hv2.symm)
      have hsym_eq := eA.injective hsub_eq
      exact congrArg Subtype.val (eN.symm.injective hsym_eq)
    let X₀ : Entity X := Entity.relRan f
    have hX₀sub : ∀ x ∈ X₀, x ∈ A := fun x hx ↦ hf.mem_of_mem_relRan hx
    -- Goldblatt p. 176: `im A ∩ *X₀ = {*a : a ∈ A and *a ∈ *X₀} = {*a : a ∈ X₀} = im X₀`
    have hinter_eq : Entity.inter (F.imEntity A) (F.star X₀) = F.imEntity X₀ := by
      refine Entity.set_ext (Entity.isSet_inter _ _) (F.isSet_imEntity X₀) fun y ↦ ?_
      rw [Entity.mem_inter_iff, F.mem_imEntity_iff, F.mem_imEntity_iff]
      constructor
      · rintro ⟨⟨a, _, rfl⟩, hyX⟩
        exact ⟨a, (F.mem_star_iff).1 hyX, rfl⟩
      · rintro ⟨x, hxX, rfl⟩
        exact ⟨⟨x, hX₀sub x hxX, rfl⟩, F.mem_star_iff.2 hxX⟩
    have hX₀im_int : F.IsInternalEntity (F.imEntity X₀) :=
      hinter_eq ▸ F.isInternalEntity_inter hAim_int (F.isInternalEntity_star X₀)
    have hN₀im_int : F.IsInternalEntity (F.imEntity N₀) :=
      (F.relPreimage_star_imEntity_relRan hN₀set hf hinj) ▸
        F.isInternalEntity_relPreimage (F.isInternalEntity_star f) hX₀im_int
    exact hN₀ext hN₀im_int
  have h2 : ∃ b ∈ F.star A, F.IsNonstandard b := by
    by_contra hnone
    push Not at hnone
    have hAset : A.IsSet :=
      Entity.isSet_iff_eq_empty_or_nonempty.2 (Or.inr hAinf.nonempty)
    have hEq : F.imEntity A = F.star A := by
      refine Entity.set_ext (F.isSet_imEntity A) ((F.isSet_star_iff).2 hAset) fun b ↦ ?_
      rw [F.mem_imEntity_iff, F.mem_sigmaImage_iff]
      exact ⟨fun h ↦ h.1, fun hb ↦ ⟨hb, Classical.not_not.1 (hnone b hb)⟩⟩
    exact h1 (hEq ▸ F.isInternalEntity_star A)
  have h3 : F.star (Entity.powerset A) ≠ Entity.powerset (F.star A) := by
    intro hEq
    have hmemP : F.imEntity A ∈ F.star (Entity.powerset A) :=
      hEq.symm ▸ F.imEntity_mem_powerset_star A
    exact h1 (F.mem_star_powerset_iff.1 hmemP).2
  exact ⟨h1, h2, h3⟩

/-- Countable infinity of `posNatEntity = {1, 2, 3, …}` (`ℕ ≃ posNatEntity.extSet`). -/
def posNatEntityCountEquiv : ℕ ≃ posNatEntity.extSet :=
  Equiv.ofBijective
    (fun n : ℕ ↦ ⟨Entity.atom ((n + 1 : ℕ) : ℝ),
      atom_mem_mkAtomSet_iff.2 ⟨n + 1, by omega, rfl⟩⟩)
    ⟨fun m n hmn ↦ by
      have hat := Entity.atom_inj.1 (congrArg Subtype.val hmn)
      have hnat : m + 1 = n + 1 := by exact_mod_cast hat
      omega,
     fun z ↦ by
      obtain ⟨_, ⟨k, hk1, rfl⟩, hzeq⟩ := mem_mkAtomSet_iff.1 z.2
      refine ⟨k - 1, Subtype.ext ?_⟩
      dsimp only
      have hk : k - 1 + 1 = k := by omega
      rw [hk, hzeq]⟩

/-- Goldblatt **Theorem 13.14.1** over `ℝ` (pp. 176–177): In any framework `F : Framework ℝ Y` in
which `*ℕ` has a nonstandard element, for **every** infinite set `A : Entity ℝ` of arbitrary rank in
`𝕌(ℝ)`:
1. `im A` (`F.imEntity A`) is **external**,
2. `*A` has **nonstandard** elements (`*A \ im A ≠ ∅`), and
3. `*𝒫(A)` is a **proper subset** of `𝒫(*A)`. -/
theorem Framework.isExternalEntity_imEntity_of_infinite {Y : Type*} (F : Framework ℝ Y)
    (hns : ∃ ω ∈ F.star posNatEntity, F.IsNonstandard ω)
    {A : Entity ℝ} (hAinf : A.extSet.Infinite) :
    F.IsExternalEntity (F.imEntity A) ∧
    (∃ b ∈ F.star A, F.IsNonstandard b) ∧
    F.star (Entity.powerset A) ≠ Entity.powerset (F.star A) := by
  have hN₀ext : F.IsExternalEntity (F.imEntity posNatEntity) := fun hint ↦
    F.not_exists_internal_extSet_eq_sigmaImage_posNat hns
      ⟨F.imEntity posNatEntity, F.isSet_imEntity _, hint, F.extSet_imEntity _⟩
  exact F.isExternalEntity_imEntity_of_infinite_general
    (Entity.isSet_setOfBounded _) ⟨posNatEntityCountEquiv⟩ hN₀ext hAinf

/-- Unconditional **Theorem 13.14.1** in `hyperrealFramework` (Goldblatt §13.14, pp. 176–177): For
**every** infinite set `A : Entity ℝ` in the superstructure `𝕌(ℝ)`, `im A` is external, `*A`
contains nonstandard elements, and `*𝒫(A) ≠ 𝒫(*A)`. -/
theorem hyperrealFramework_isExternalEntity_imEntity_of_infinite {A : Entity ℝ}
    (hAinf : A.extSet.Infinite) :
    hyperrealFramework.IsExternalEntity (hyperrealFramework.imEntity A) ∧
    (∃ b ∈ hyperrealFramework.star A, hyperrealFramework.IsNonstandard b) ∧
    hyperrealFramework.star (Entity.powerset A) ≠ Entity.powerset (hyperrealFramework.star A) :=
  hyperrealFramework.isExternalEntity_imEntity_of_infinite
    hyperrealFramework_exists_nonstandard_posNat hAinf

/-- Goldblatt **Exercise 13.14.3** (p. 177): Whenever `A : Entity X` is a **finite** set,
`*𝒫(A) = 𝒫(*A)`! -/
theorem Framework.star_powerset_eq_powerset_star_of_finite {X Y : Type*} (F : Framework X Y)
    {A : Entity X} (hAset : A.IsSet) (hAfin : A.extSet.Finite) :
    F.star (Entity.powerset A) = Entity.powerset (F.star A) := by
  classical
  refine Entity.set_ext ((F.isSet_star_iff).2 (Entity.isSet_powerset A))
    (Entity.isSet_powerset (F.star A)) fun B ↦ ?_
  rw [F.mem_star_powerset_iff]
  refine ⟨fun h ↦ h.1, fun hBP ↦ ⟨hBP, ?_⟩⟩
  obtain ⟨hBset, hBsub⟩ := Entity.mem_powerset_iff.1 hBP
  have hstar_fin : (F.star A).extSet.Finite := by
    rw [F.star_extSet_eq_sigmaImage_of_finite hAset hAfin]
    exact hAfin.image F.star
  have hBfin : B.extSet.Finite := hstar_fin.subset hBsub
  have hBeq : B = Entity.finsetEntity hBfin.toFinset := by
    refine Entity.set_ext hBset (Entity.isSet_finsetEntity _) fun y ↦ ?_
    rw [Entity.mem_finsetEntity_iff, Set.Finite.mem_toFinset]
    rfl
  rw [hBeq]
  exact F.isInternalEntity_finsetEntity fun y hy ↦
    (F.isInternalEntity_star A).of_mem (hBsub y ((Set.Finite.mem_toFinset hBfin).1 hy))

/-! ## §13.15 Internal Set Definition Principle & §13.16 Internal Function Definition Principle -/

/-- Goldblatt §13.15 (p. 177): **Internal Set Definition Principle** — if `φ(x)` is an internal
`ℒ_{𝕌'}`-formula (`φ.AllConstsInternal F`, all constants internal) with `x` the only free variable
(`∀ v ∈ freeVarsUFormula φ, v = x`), then for any internal set `A : Entity Y`, the set
`{a ∈ A : φ(a)}` is internal! -/
theorem Framework.internal_set_definition_principle {X Y : Type*} (F : Framework X Y)
    {A : Entity Y} (hA : F.IsInternalEntity A) (x : ℕ) {φ : UFormula Y}
    (hvars : ∀ v ∈ freeVarsUFormula φ, v = x)
    (hconsts : φ.AllConstsInternal F) :
    F.IsInternalEntity
      (Entity.setOfBounded
        {a : Entity Y | a ∈ A ∧ Holds (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) x a) φ}) :=
  F.isInternalEntity_comprehension hA x hvars hconsts (fun _ ↦ ∅)

/-- Goldblatt §13.15 (p. 177, Second Formulation): If `B = {a ∈ 𝕌' : φ(a)}` is a subset of `𝕌'`
definable by an `ℒ_{𝕌'}`-formula `φ` with only internal constants and sole free variable `x`, then
for any internal set `A`, `A ∩ B` (`Entity.setOfBounded (A.extSet ∩ B)`) is internal! -/
theorem Framework.isInternalEntity_inter_definable {X Y : Type*} (F : Framework X Y)
    {A : Entity Y} (hA : F.IsInternalEntity A) {B : Set (Entity Y)}
    (x : ℕ) {φ : UFormula Y}
    (hvars : ∀ v ∈ freeVarsUFormula φ, v = x)
    (hconsts : φ.AllConstsInternal F)
    (hB : B = {a : Entity Y | Holds (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) x a) φ}) :
    F.IsInternalEntity (Entity.setOfBounded (A.extSet ∩ B)) := by
  subst hB
  exact F.internal_set_definition_principle hA x hvars hconsts

/-- Goldblatt §13.16 (p. 178): **Internal Function Definition Principle** — let `f : A → B` be a
function between internal sets `A` and `B` (`Entity.IsFuncFromTo f A B`), and suppose there is an
internal `ℒ_{𝕌'}`-term `τ(x)` (`τ.AllConstsInternal F`) with sole variable at most `x` such that
`f(a) = τ(a)` (`evalUTerm (Function.update (fun _ ↦ ∅) x a) τ = some (Entity.funcApp f a)`) for all
`a ∈ A`. Then `f` is an **internal** function! -/
theorem Framework.internal_function_definition_principle {X Y : Type*} (F : Framework X Y)
    {f A B : Entity Y} (hAset : A.IsSet)
    (hA : F.IsInternalEntity A) (hB : F.IsInternalEntity B)
    (hf : Entity.IsFuncFromTo f A B)
    (x : ℕ) {τ : UTerm Y}
    (hvars : ∀ v ∈ freeVarsUTerm τ, v = x)
    (hconsts : τ.AllConstsInternal F)
    (hval : ∀ a ∈ A,
      evalUTerm (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) x a) τ =
        some (Entity.funcApp f a)) :
    F.IsInternalEntity f := by
  -- Goldblatt p. 178: `f = {c ∈ A × B : (∃ x ∈ A) (∃ y ∈ B) (c = (x, y) ∧ y = τ(x))}`
  let yVar : ℕ := x + 1
  let cVar : ℕ := x + 2
  let ψ : UFormula Y :=
    .existsIn x (.const A)
      (.existsIn yVar (.const B)
        (.conj
          (.eq (.var cVar) (UTerm.pair (.var x) (.var yVar)))
          (.eq (.var yVar) τ)))
  have hψ_vars : ∀ v ∈ freeVarsUFormula ψ, v = cVar := by
    intro v hv
    simp only [ψ, freeVarsUFormula, freeVarsUTerm, freeVarsUTerm_pair, Finset.empty_union,
      Finset.mem_erase, Finset.mem_union, Finset.mem_singleton] at hv
    obtain ⟨hnx, hny, (rfl | (rfl | rfl)) | (rfl | hvτ)⟩ := hv
    · rfl
    · exact (hnx rfl).elim
    · exact (hny rfl).elim
    · exact (hny rfl).elim
    · exact (hnx (hvars v hvτ)).elim
  have hψ_consts : ψ.AllConstsInternal F := by
    simp [ψ, hA, hB, hconsts]
  have hcomp := F.internal_set_definition_principle
    (F.isInternalEntity_prod hA hB) cVar hψ_vars hψ_consts
  have hbdd : IsBoundedRank {c : Entity Y |
      c ∈ Entity.prod A B ∧ Holds (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) cVar c) ψ} :=
    (Entity.prod A B).isBoundedRank_extSet.subset fun _ h ↦ h.1
  have hfeq : f = Entity.setOfBounded {c : Entity Y |
      c ∈ Entity.prod A B ∧ Holds (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) cVar c) ψ} := by
    refine Entity.set_ext hf.1 (Entity.isSet_setOfBounded _) fun c ↦ ?_
    rw [Entity.mem_setOfBounded hbdd]
    constructor
    · intro hcf
      obtain ⟨a, haA, b, hbB, rfl⟩ := hf.2.1 c hcf
      have hfab : Entity.funcApp f a = b :=
        ((Entity.kpair_mem_iff_funcApp_eq hf.isFuncEntity).1 hcf).2
      let env₃ := Function.update (Function.update
        (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) cVar (Entity.kpair a b)) x a) yVar b
      have hτ_ev : evalUTerm env₃ τ = some b := by
        have hcongr : evalUTerm env₃ τ =
            evalUTerm (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) x a) τ :=
          evalUTerm_congr fun v hv ↦ by
            have hvx := hvars v hv; subst v
            have hne : x ≠ yVar := by omega
            simp [env₃, Function.update_of_ne hne]
        rw [hcongr, hval a haA, hfab]
      refine ⟨Entity.kpair_mem_prod_iff.2 ⟨haA, hbB⟩, A, rfl, a, haA, B, rfl, b, hbB, ?_, ?_⟩
      · have hcx : cVar ≠ x := by omega
        have hcy : cVar ≠ yVar := by omega
        have hxy : x ≠ yVar := by omega
        exact ⟨Entity.kpair a b,
          by simp [Function.update_of_ne hcy, Function.update_of_ne hcx],
          by simp [evalUTerm_pair, Function.update_of_ne hxy]⟩
      · exact ⟨b, by simp, hτ_ev⟩
    · rintro ⟨_, _, hAd, a, haA, _, hBd, b, _, ⟨q1, hq1a, hq1b⟩, ⟨q2, hq2a, hq2b⟩⟩
      obtain rfl := Option.some.inj hAd
      obtain rfl := Option.some.inj hBd
      have hcx : cVar ≠ x := by omega
      have hcy : cVar ≠ yVar := by omega
      have hxy : x ≠ yVar := by omega
      have hc_eq : c = q1 :=
        Option.some.inj (by simpa [Function.update_of_ne hcy, Function.update_of_ne hcx] using hq1a)
      have hab_eq : Entity.kpair a b = q1 :=
        Option.some.inj (by simpa [evalUTerm_pair, Function.update_of_ne hxy] using hq1b)
      have hb_eq : b = q2 := Option.some.inj (by simpa using hq2a)
      have hτ_congr :
          evalUTerm (Function.update (Function.update
            (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) cVar c) x a) yVar b) τ =
          evalUTerm (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) x a) τ :=
        evalUTerm_congr fun v hv ↦ by
          have hvx := hvars v hv; subst v
          have hne : x ≠ yVar := by omega
          simp [Function.update_of_ne hne]
      rw [hτ_congr, hval a haA] at hq2b
      have hfab : Entity.funcApp f a = b := (Option.some.inj hq2b).trans hb_eq.symm
      have hadom : a ∈ Entity.relDom f := by rw [hf.relDom_eq hAset]; exact haA
      rw [hc_eq.trans hab_eq.symm, ← hfab]
      exact Entity.kpair_funcApp_mem hadom
  exact hfeq ▸ hcomp

/-! ## §13.17 Hyperfiniteness and Internal Cardinality (Theorem 13.17.1) -/

/-- Goldblatt §13.17 (pp. 178–179): An entity `B : Entity Y` in `𝕌'` is **hyperfinite** if
`B ∈ *𝒫_F(A)` (`F.star (Entity.finPowerset A)`) for some standard entity `A : Entity X`. -/
def Framework.IsHyperfiniteSet {X Y : Type*} (F : Framework X Y) (B : Entity Y) : Prop :=
  ∃ A : Entity X, B ∈ F.star (Entity.finPowerset A)

/-- Goldblatt §13.17 (p. 178): `*𝒫_F(A) ⊆ *𝒫(A) ⊆ 𝒫(*A)` — every member of `*𝒫_F(A)` belongs to
`*𝒫(A)` (and hence is an internal subset of `*A`). -/
theorem Framework.mem_star_powerset_of_mem_star_finPowerset {X Y : Type*} (F : Framework X Y)
    {A : Entity X} {B : Entity Y} (hB : B ∈ F.star (Entity.finPowerset A)) :
    B ∈ F.star (Entity.powerset A) := by
  have hsub : ∀ Z ∈ Entity.finPowerset A, Z ∈ Entity.powerset A := fun Z hZ ↦ by
    obtain ⟨hZs, hZsub, _⟩ := Entity.mem_finPowerset_iff.1 hZ
    exact Entity.mem_powerset_iff.2 ⟨hZs, hZsub⟩
  exact (F.subset_star_iff.2 hsub) _ hB

/-- Every hyperfinite entity is an internal set (`B.IsSet ∧ F.IsInternalEntity B`;
Goldblatt §13.17, p. 178). -/
theorem Framework.IsHyperfiniteSet.isInternalAndSet {X Y : Type*} {F : Framework X Y}
    {B : Entity Y} (hB : F.IsHyperfiniteSet B) :
    B.IsSet ∧ F.IsInternalEntity B := by
  obtain ⟨A, hBA⟩ := hB
  obtain ⟨hBP, hBint⟩ := F.mem_star_powerset_iff.1
    (F.mem_star_powerset_of_mem_star_finPowerset hBA)
  exact ⟨(Entity.mem_powerset_iff.1 hBP).1, hBint⟩

/-- Every hyperfinite set is internal (`F.IsInternalEntity B`; Goldblatt §13.17, p. 178). -/
theorem Framework.IsHyperfiniteSet.isInternalEntity {X Y : Type*} {F : Framework X Y}
    {B : Entity Y} (hB : F.IsHyperfiniteSet B) : F.IsInternalEntity B :=
  hB.isInternalAndSet.2

/-- Every hyperfinite entity is a set (`B.IsSet`; Goldblatt §13.17, p. 178). -/
theorem Framework.IsHyperfiniteSet.isSet {X Y : Type*} {F : Framework X Y}
    {B : Entity Y} (hB : F.IsHyperfiniteSet B) : B.IsSet :=
  hB.isInternalAndSet.1

/-- `∅` is hyperfinite (`∅ ∈ *𝒫_F(∅)`; Goldblatt §13.17, p. 178). -/
@[simp]
theorem Framework.isHyperfiniteSet_empty {X Y : Type*} (F : Framework X Y) :
    F.IsHyperfiniteSet (∅ : Entity Y) := by
  refine ⟨∅, ?_⟩
  have h0 : (∅ : Entity X) ∈ Entity.finPowerset ∅ :=
    Entity.mem_finPowerset_iff.2 ⟨Entity.isSet_empty,
      fun z hz ↦ (Entity.not_mem_empty z hz).elim,
      Set.finite_empty.subset fun z hz ↦ (Entity.not_mem_empty z hz).elim⟩
  simpa [F.star_empty] using F.mem_star_iff.2 h0

/-- If `B` is hyperfinite and `B ⊆ *D`, then `B ∈ *𝒫_F(D)` (ambient-change lemma for hyperfinite
sets; Goldblatt §13.17, p. 179). -/
theorem Framework.mem_star_finPowerset_of_isHyperfiniteSet_of_subset {X Y : Type*}
    (F : Framework X Y) {B : Entity Y} {D : Entity X}
    (hB : F.IsHyperfiniteSet B) (hsub : ∀ x ∈ B, x ∈ F.star D) :
    B ∈ F.star (Entity.finPowerset D) := by
  obtain ⟨C, hBC⟩ := hB
  let φ : UFormula X :=
    .forallIn 0 (.const (Entity.finPowerset C))
      (.imp
        (.forallIn 1 (.var 0) (.mem (.var 1) (.const D)))
        (.mem (.var 0) (.const (Entity.finPowerset D))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm]
  have hstd : SentenceHolds φ := by
    refine ⟨Entity.finPowerset C, rfl, fun Z hZC ⟨_, hZ0, hallD⟩ ↦ ?_⟩
    obtain rfl := Option.some.inj (by simpa using hZ0)
    obtain ⟨hZs, _, hZfin⟩ := Entity.mem_finPowerset_iff.1 hZC
    refine ⟨Z, Entity.finPowerset D, by simp, rfl, Entity.mem_finPowerset_iff.2 ⟨hZs, fun x hxZ ↦ ?_, hZfin⟩⟩
    obtain ⟨x', D', hx', hD', hm⟩ := hallD x hxZ
    have h1 : x = x' := Option.some.inj (by simpa using hx')
    obtain rfl := Option.some.inj hD'
    exact h1 ▸ hm
  obtain ⟨_, hFC, hall⟩ := (F.transfer φ hsent).1 hstd
  obtain rfl := Option.some.inj hFC
  obtain ⟨B', FD', hB', hFD', hm⟩ := hall B hBC
    ⟨B, by simp, fun x hxB ↦ ⟨x, F.star D, by simp, rfl, hsub x hxB⟩⟩
  have h1 : B = B' := Option.some.inj (by simpa using hB')
  obtain rfl := Option.some.inj hFD'
  exact h1 ▸ hm

/-- Constant-free `ℒ_𝕌`-formula on variables `0` (`dom`), `1` (`cod`), `2` (`f`) asserting that `f`
is a set-theoretic function from `dom` to `cod` (Goldblatt §13.17, p. 179, clauses 3–5). -/
def funcBetweenFormula (Z : Type*) : UFormula Z :=
  .conj
    (.forallIn 3 (.var 2)
      (.existsIn 4 (.var 0)
        (.existsIn 5 (.var 1)
          (.eq (.var 3) (UTerm.pair (.var 4) (.var 5))))))
    (.conj
      (.forallIn 4 (.var 0)
        (.forallIn 5 (.var 1)
          (.forallIn 6 (.var 1)
            (.imp
              (.conj
                (.mem (UTerm.pair (.var 4) (.var 5)) (.var 2))
                (.mem (UTerm.pair (.var 4) (.var 6)) (.var 2)))
              (.eq (.var 5) (.var 6))))))
      (.forallIn 4 (.var 0)
        (.existsIn 5 (.var 1)
          (.mem (UTerm.pair (.var 4) (.var 5)) (.var 2)))))

/-- Constant-free `ℒ_𝕌`-formula on variables `0` (`dom`), `1` (`cod`), `2` (`f`) asserting
injectivity of `f : dom → cod` (Goldblatt §13.17, p. 179). -/
def injBetweenFormula (Z : Type*) : UFormula Z :=
  .conj (funcBetweenFormula Z)
    (.forallIn 4 (.var 0)
      (.forallIn 5 (.var 0)
        (.forallIn 6 (.var 1)
          (.imp
            (.conj
              (.mem (UTerm.pair (.var 4) (.var 6)) (.var 2))
              (.mem (UTerm.pair (.var 5) (.var 6)) (.var 2)))
            (.eq (.var 4) (.var 5))))))

/-- Constant-free `ℒ_𝕌`-formula on variables `0` (`dom`), `1` (`cod`), `2` (`f`) asserting
surjectivity of `f : dom → cod` (Goldblatt §13.17, p. 179). -/
def surjBetweenFormula (Z : Type*) : UFormula Z :=
  .conj (funcBetweenFormula Z)
    (.forallIn 5 (.var 1)
      (.existsIn 4 (.var 0)
        (.mem (UTerm.pair (.var 4) (.var 5)) (.var 2))))

/-- Constant-free `ℒ_𝕌`-formula on variables `0` (`dom`), `1` (`cod`), `2` (`f`) asserting that `f`
is a bijection from `dom` onto `cod` (Goldblatt §13.17, p. 179, clauses 3–7). -/
def bijBetweenFormula (Z : Type*) : UFormula Z :=
  .conj (surjBetweenFormula Z)
    (.forallIn 4 (.var 0)
      (.forallIn 5 (.var 0)
        (.forallIn 6 (.var 1)
          (.imp
            (.conj
              (.mem (UTerm.pair (.var 4) (.var 6)) (.var 2))
              (.mem (UTerm.pair (.var 5) (.var 6)) (.var 2)))
            (.eq (.var 4) (.var 5))))))

/-- `starFormula` preserves `funcBetweenFormula`, `injBetweenFormula`, `surjBetweenFormula`, and
`bijBetweenFormula` (since they contain no constants). -/
@[simp]
theorem starFormula_funcBetweenFormula {X Y : Type*} (star : Entity X → Entity Y) :
    starFormula star (funcBetweenFormula X) = funcBetweenFormula Y := by
  simp [funcBetweenFormula, starFormula, starTerm_pair, starTerm]

/-- `starFormula` preserves `injBetweenFormula`. -/
@[simp]
theorem starFormula_injBetweenFormula {X Y : Type*} (star : Entity X → Entity Y) :
    starFormula star (injBetweenFormula X) = injBetweenFormula Y := by
  simp [injBetweenFormula]

/-- `starFormula` preserves `surjBetweenFormula`. -/
@[simp]
theorem starFormula_surjBetweenFormula {X Y : Type*} (star : Entity X → Entity Y) :
    starFormula star (surjBetweenFormula X) = surjBetweenFormula Y := by
  simp [surjBetweenFormula]

/-- `starFormula` preserves `bijBetweenFormula`. -/
@[simp]
theorem starFormula_bijBetweenFormula {X Y : Type*} (star : Entity X → Entity Y) :
    starFormula star (bijBetweenFormula X) = bijBetweenFormula Y := by
  simp [bijBetweenFormula]

/-- Free variables of `funcBetweenFormula Z` lie in `{0, 1, 2}`. -/
theorem freeVars_funcBetweenFormula {Z : Type*} {v : ℕ}
    (hv : v ∈ freeVarsUFormula (funcBetweenFormula Z)) : v < 3 := by
  simp [funcBetweenFormula, freeVarsUFormula, freeVarsUTerm] at hv; omega

/-- Free variables of `injBetweenFormula Z` lie in `{0, 1, 2}`. -/
theorem freeVars_injBetweenFormula {Z : Type*} {v : ℕ}
    (hv : v ∈ freeVarsUFormula (injBetweenFormula Z)) : v < 3 := by
  simp [injBetweenFormula, funcBetweenFormula, freeVarsUFormula, freeVarsUTerm] at hv; omega

/-- Free variables of `surjBetweenFormula Z` lie in `{0, 1, 2}`. -/
theorem freeVars_surjBetweenFormula {Z : Type*} {v : ℕ}
    (hv : v ∈ freeVarsUFormula (surjBetweenFormula Z)) : v < 3 := by
  simp [surjBetweenFormula, funcBetweenFormula, freeVarsUFormula, freeVarsUTerm] at hv; omega

/-- Free variables of `bijBetweenFormula Z` lie in `{0, 1, 2}`. -/
theorem freeVars_bijBetweenFormula {Z : Type*} {v : ℕ}
    (hv : v ∈ freeVarsUFormula (bijBetweenFormula Z)) : v < 3 := by
  simp [bijBetweenFormula, surjBetweenFormula, funcBetweenFormula, freeVarsUFormula, freeVarsUTerm] at hv
  omega

/-- Semantic equivalence of `funcBetweenFormula Z` under any environment mapping `0 ↦ D`, `1 ↦ C`,
`2 ↦ f` when `f.IsSet`. -/
theorem holds_funcBetweenFormula_iff {Z : Type*} {env : ℕ → Entity Z} {D C f : Entity Z}
    (hfset : f.IsSet) (h0 : env 0 = D) (h1 : env 1 = C) (h2 : env 2 = f) :
    Holds env (funcBetweenFormula Z) ↔ Entity.IsFuncFromTo f D C := by
  constructor
  · rintro ⟨⟨_, hf0, hrel⟩, ⟨_, hD1, hsv⟩, ⟨_, hD2, htot⟩⟩
    obtain rfl := Option.some.inj (by simpa [h2] using hf0)
    obtain rfl := Option.some.inj (by simpa [h0] using hD1)
    obtain rfl := Option.some.inj (by simpa [h0] using hD2)
    have hprod : ∀ p ∈ f, ∃ a ∈ D, ∃ b ∈ C, p = Entity.kpair a b := by
      intro p hp
      obtain ⟨_, hd0, x, hxD, _, hc0, y, hyC, q, hq1, hq2⟩ := hrel p hp
      have hDeq : D = _ := Option.some.inj (by simpa [h0] using hd0)
      have hCeq : C = _ := Option.some.inj (by simpa [h1] using hc0)
      have hp1 : p = q := Option.some.inj (by simpa using hq1)
      have hp2 : Entity.kpair x y = q := Option.some.inj (by simpa [evalUTerm_pair] using hq2)
      exact ⟨x, hDeq ▸ hxD, y, hCeq ▸ hyC, hp1.trans hp2.symm⟩
    refine ⟨hfset, hprod, fun x y₁ y₂ hm1 hm2 ↦ ?_, fun x hxD ↦ ?_⟩
    · obtain ⟨_, ha₁, _, hb₁, he1⟩ := hprod _ hm1
      obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 he1
      obtain ⟨_, _, _, hb₂, he2⟩ := hprod _ hm2
      obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 he2
      obtain ⟨_, hc1, hy1all⟩ := hsv x ha₁
      have hC1 : C = _ := Option.some.inj (by simpa [h1] using hc1)
      obtain ⟨_, hc2, hy2all⟩ := hy1all y₁ (hC1 ▸ hb₁)
      have hC2 : C = _ := Option.some.inj (by simpa [h1] using hc2)
      obtain ⟨z, hz1, hz2⟩ := hy2all y₂ (hC2 ▸ hb₂) ⟨
        ⟨Entity.kpair x y₁, f, by simp [evalUTerm_pair], by simp [h2], hm1⟩,
        ⟨Entity.kpair x y₂, f, by simp [evalUTerm_pair], by simp [h2], hm2⟩⟩
      exact (Option.some.inj (by simpa using hz1)).trans
        (Option.some.inj (by simpa using hz2)).symm
    · obtain ⟨_, hc1, y, hyC, p, f', hp, hf', hm⟩ := htot x hxD
      have hC1 : C = _ := Option.some.inj (by simpa [h1] using hc1)
      have hf1 : f = f' := Option.some.inj (by simpa [h2] using hf')
      have hp1 : Entity.kpair x y = p := Option.some.inj (by simpa [evalUTerm_pair] using hp)
      exact ⟨y, hC1 ▸ hyC, hp1 ▸ hf1 ▸ hm⟩
  · rintro ⟨_, hprod, hsv, htot⟩
    refine ⟨⟨f, by simp [h2], fun p hp ↦ ?_⟩, ⟨D, by simp [h0], fun x hxD ↦ ?_⟩,
      ⟨D, by simp [h0], fun x hxD ↦ ?_⟩⟩
    · obtain ⟨a, haD, b, hbC, rfl⟩ := hprod p hp
      exact ⟨D, by simp [h0], a, haD, C, by simp [h1], b, hbC, Entity.kpair a b,
        by simp, by simp [evalUTerm_pair]⟩
    · refine ⟨C, by simp [h1], fun y₁ _ ↦ ⟨C, by simp [h1], fun y₂ _ ⟨⟨p1, f1, hp1, hf1, hm1⟩, ⟨p2, f2, hp2, hf2, hm2⟩⟩ ↦ ?_⟩⟩
      have hf1' : f = f1 := Option.some.inj (by simpa [h2] using hf1)
      have hf2' : f = f2 := Option.some.inj (by simpa [h2] using hf2)
      have hp1' : Entity.kpair x y₁ = p1 := Option.some.inj (by simpa [evalUTerm_pair] using hp1)
      have hp2' : Entity.kpair x y₂ = p2 := Option.some.inj (by simpa [evalUTerm_pair] using hp2)
      have hyeq : y₁ = y₂ := hsv x y₁ y₂ (hp1' ▸ hf1' ▸ hm1) (hp2' ▸ hf2' ▸ hm2)
      exact ⟨y₁, by simp, by simp [hyeq]⟩
    · obtain ⟨y, hyC, hp⟩ := htot x hxD
      exact ⟨C, by simp [h1], y, hyC, Entity.kpair x y, f,
        by simp [evalUTerm_pair], by simp [h2], hp⟩

/-- Semantic equivalence of `injBetweenFormula Z` when `f.IsSet`. -/
theorem holds_injBetweenFormula_iff {Z : Type*} {env : ℕ → Entity Z} {D C f : Entity Z}
    (hfset : f.IsSet) (h0 : env 0 = D) (h1 : env 1 = C) (h2 : env 2 = f) :
    Holds env (injBetweenFormula Z) ↔ Entity.IsFuncFromTo f D C ∧ f.IsInjectiveFunc := by
  rw [injBetweenFormula, Holds, holds_funcBetweenFormula_iff hfset h0 h1 h2]
  refine and_congr_right fun hfunc ↦ ?_
  constructor
  · rintro ⟨_, hD1, hall⟩
    have hDeq : D = _ := Option.some.inj (by simpa [h0] using hD1)
    refine ⟨hfunc.isFuncEntity, fun x₁ x₂ y hm1 hm2 ↦ ?_⟩
    obtain ⟨_, hx₁D, _, hyC, he1⟩ := hfunc.2.1 _ hm1
    obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 he1
    obtain ⟨_, hx₂D, _, _, he2⟩ := hfunc.2.1 _ hm2
    obtain ⟨rfl, _⟩ := Entity.kpair_inj.1 he2
    obtain ⟨_, hD2, hx2all⟩ := hall x₁ (hDeq ▸ hx₁D)
    have hD2eq : D = _ := Option.some.inj (by simpa [h0] using hD2)
    obtain ⟨_, hC1, hyall⟩ := hx2all x₂ (hD2eq ▸ hx₂D)
    have hC1eq : C = _ := Option.some.inj (by simpa [h1] using hC1)
    obtain ⟨z, hz1, hz2⟩ := hyall y (hC1eq ▸ hyC) ⟨
      ⟨Entity.kpair x₁ y, f, by simp [evalUTerm_pair], by simp [h2], hm1⟩,
      ⟨Entity.kpair x₂ y, f, by simp [evalUTerm_pair], by simp [h2], hm2⟩⟩
    exact (Option.some.inj (by simpa using hz1)).trans
      (Option.some.inj (by simpa using hz2)).symm
  · rintro ⟨_, hinj⟩
    refine ⟨D, by simp [h0], fun x₁ _ ↦ ⟨D, by simp [h0], fun x₂ _ ↦
      ⟨C, by simp [h1], fun y _ ⟨⟨p1, f1, hp1, hf1, hm1⟩, ⟨p2, f2, hp2, hf2, hm2⟩⟩ ↦ ?_⟩⟩⟩
    have hf1' : f = f1 := Option.some.inj (by simpa [h2] using hf1)
    have hf2' : f = f2 := Option.some.inj (by simpa [h2] using hf2)
    have hp1' : Entity.kpair x₁ y = p1 := Option.some.inj (by simpa [evalUTerm_pair] using hp1)
    have hp2' : Entity.kpair x₂ y = p2 := Option.some.inj (by simpa [evalUTerm_pair] using hp2)
    have hxeq : x₁ = x₂ := hinj x₁ x₂ y (hp1' ▸ hf1' ▸ hm1) (hp2' ▸ hf2' ▸ hm2)
    exact ⟨x₁, by simp, by simp [hxeq]⟩

/-- Semantic equivalence of `surjBetweenFormula Z` when `f.IsSet`. -/
theorem holds_surjBetweenFormula_iff {Z : Type*} {env : ℕ → Entity Z} {D C f : Entity Z}
    (hfset : f.IsSet) (h0 : env 0 = D) (h1 : env 1 = C) (h2 : env 2 = f) :
    Holds env (surjBetweenFormula Z) ↔ Entity.IsSurjectiveFromTo f D C := by
  rw [surjBetweenFormula, Holds, holds_funcBetweenFormula_iff hfset h0 h1 h2]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · rintro ⟨_, hC1, hall⟩ y hyC
    have hC1eq : C = _ := Option.some.inj (by simpa [h1] using hC1)
    obtain ⟨_, hD1, x, hxD, p, f', hp, hf', hm⟩ := hall y (hC1eq ▸ hyC)
    have hD1eq : D = _ := Option.some.inj (by simpa [h0] using hD1)
    have hf1 : f = f' := Option.some.inj (by simpa [h2] using hf')
    have hp1 : Entity.kpair x y = p := Option.some.inj (by simpa [evalUTerm_pair] using hp)
    exact ⟨x, hD1eq ▸ hxD, hp1 ▸ hf1 ▸ hm⟩
  · intro hsurj
    refine ⟨C, by simp [h1], fun y hyC ↦ ?_⟩
    obtain ⟨x, hxD, hp⟩ := hsurj y hyC
    exact ⟨D, by simp [h0], x, hxD, Entity.kpair x y, f,
      by simp [evalUTerm_pair], by simp [h2], hp⟩

/-- Semantic equivalence of `bijBetweenFormula Z` when `f.IsSet`. -/
theorem holds_bijBetweenFormula_iff {Z : Type*} {env : ℕ → Entity Z} {D C f : Entity Z}
    (hfset : f.IsSet) (h0 : env 0 = D) (h1 : env 1 = C) (h2 : env 2 = f) :
    Holds env (bijBetweenFormula Z) ↔ Entity.IsBijectiveFromTo f D C := by
  rw [bijBetweenFormula, Holds, holds_surjBetweenFormula_iff hfset h0 h1 h2]
  refine and_congr_right fun hsurj ↦ ?_
  have hinj_eq := holds_injBetweenFormula_iff hfset h0 h1 h2
  rw [injBetweenFormula, Holds, holds_funcBetweenFormula_iff hfset h0 h1 h2] at hinj_eq
  exact ⟨fun h ↦ (hinj_eq.1 ⟨hsurj.1, h⟩).2, fun h ↦ (hinj_eq.2 ⟨hsurj.1, h⟩).2⟩

/-- Standard cardinality function `Z ↦ |Z|` from `Entity.finPowerset A` to `nat0Entity`
(mapping nonempty finite subsets into `posNatEntity`; Goldblatt §13.17, p. 180). -/
def cardFun (A : Entity ℝ) : Entity ℝ :=
  open Classical in
  Entity.mkFuncEntity (Entity.finPowerset A) (fun Z ↦
    if h : Z.extSet.Finite then Entity.atom (h.toFinset.card : ℝ) else Entity.atom 0)

/-- `cardFun A` is a function `Entity.finPowerset A → nat0Entity`. -/
theorem isFuncFromTo_cardFun (A : Entity ℝ) :
    Entity.IsFuncFromTo (cardFun A) (Entity.finPowerset A) nat0Entity := by
  classical
  refine Entity.isFuncFromTo_mkFuncEntity fun Z hZ ↦ ?_
  obtain ⟨_, _, hfin⟩ := Entity.mem_finPowerset_iff.1 hZ
  simp only [hfin, ↓reduceDIte]
  exact atom_mem_mkAtomSet_iff.2 ⟨hfin.toFinset.card, rfl⟩

/-- Evaluation of `cardFun A` on `Z ∈ Entity.finPowerset A`. -/
theorem funcApp_cardFun {A Z : Entity ℝ} (hZ : Z ∈ Entity.finPowerset A) :
    Entity.funcApp (cardFun A) Z =
      Entity.atom ((open Classical in (Entity.mem_finPowerset_iff.1 hZ).2.2.toFinset.card) : ℝ) := by
  classical
  obtain ⟨_, _, hfin⟩ := Entity.mem_finPowerset_iff.1 hZ
  have hv := Entity.funcApp_mkFuncEntity (B := nat0Entity)
    (g := fun W ↦ if h : W.extSet.Finite then Entity.atom (h.toFinset.card : ℝ) else Entity.atom 0)
    (fun W hW ↦ by
      obtain ⟨_, _, hwfin⟩ := Entity.mem_finPowerset_iff.1 hW
      simp only [hwfin, ↓reduceDIte]
      exact atom_mem_mkAtomSet_iff.2 ⟨hwfin.toFinset.card, rfl⟩)
    hZ
  simpa [cardFun, hfin] using hv

/-- Every `Z ∈ Entity.finPowerset A` admits a bijection `f ∈ Entity.powerset (ℕ × A)` from
`initSegStd |Z|` onto `Z` (standard core of Theorem 13.17.1; Goldblatt §13.17, p. 179). -/
theorem std_exists_bijection_initSeg_cardFun {A Z : Entity ℝ}
    (hZ : Z ∈ Entity.finPowerset A) :
    ∃ f ∈ Entity.powerset (Entity.prod posNatEntity A),
      Entity.IsBijectiveFromTo f
        (Entity.funcApp initSegFun (Entity.funcApp (cardFun A) Z)) Z := by
  classical
  obtain ⟨hZset, hZsub, hZfin⟩ := Entity.mem_finPowerset_iff.1 hZ
  let m : ℕ := hZfin.toFinset.card
  have heq_card : Entity.funcApp (cardFun A) Z = Entity.atom (m : ℝ) := funcApp_cardFun hZ
  have hmN : Entity.atom (m : ℝ) ∈ nat0Entity := atom_mem_mkAtomSet_iff.2 ⟨m, rfl⟩
  have heq_seg : Entity.funcApp initSegFun (Entity.atom (m : ℝ)) = initSegStd (m : ℝ) := by
    have hv := Entity.funcApp_mkFuncEntity (B := Entity.finPowerset posNatEntity)
      (g := fun e ↦ initSegStd (Entity.atomVal 0 e))
      (fun e he ↦ by
        obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 he
        simpa using initSegStd_mem_finPowerset k)
      hmN
    simpa [initSegFun, Entity.atomVal] using hv
  rw [heq_card, heq_seg]
  let eqv : Fin m ≃ hZfin.toFinset := (Finset.equivFin hZfin.toFinset).symm
  let g : Entity ℝ → Entity ℝ := fun e ↦
    if hk : ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ e = Entity.atom (k : ℝ) then
      (eqv ⟨hk.choose - 1, by have := hk.choose_spec; omega⟩).1
    else ∅
  have hgZ : ∀ e ∈ initSegStd (m : ℝ), g e ∈ Z := by
    intro e he
    obtain ⟨_, ⟨k, hk1, hkle, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 he
    have hkm : k ≤ m := by exact_mod_cast hkle
    have hex : ∃ k' : ℕ, 1 ≤ k' ∧ k' ≤ m ∧ Entity.atom (k : ℝ) = Entity.atom (k' : ℝ) :=
      ⟨k, hk1, hkm, rfl⟩
    simp only [g, hex, ↓reduceDIte]
    exact (Set.Finite.mem_toFinset hZfin).1 (eqv _).2
  let f : Entity ℝ := Entity.mkFuncEntity (initSegStd (m : ℝ)) g
  have hfunc : Entity.IsFuncFromTo f (initSegStd (m : ℝ)) Z := Entity.isFuncFromTo_mkFuncEntity hgZ
  have hfP : f ∈ Entity.powerset (Entity.prod posNatEntity A) := by
    refine Entity.mem_powerset_iff.2 ⟨hfunc.1, fun p hp ↦ ?_⟩
    obtain ⟨e, he, z, hz, rfl⟩ := hfunc.2.1 p hp
    obtain ⟨_, ⟨k, hk1, _, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 he
    exact Entity.kpair_mem_prod_iff.2 ⟨atom_mem_mkAtomSet_iff.2 ⟨k, hk1, rfl⟩, hZsub z hz⟩
  refine ⟨f, hfP, ⟨hfunc, fun z hz ↦ ?_⟩, ⟨hfunc.isFuncEntity, fun e₁ e₂ z hp1 hp2 ↦ ?_⟩⟩
  · have hz_fin : z ∈ hZfin.toFinset := (Set.Finite.mem_toFinset hZfin).2 hz
    let j : Fin m := eqv.symm ⟨z, hz_fin⟩
    let k : ℕ := j.1 + 1
    have hk1 : 1 ≤ k := by omega
    have hkm : k ≤ m := by omega
    have he_mem : Entity.atom (k : ℝ) ∈ initSegStd (m : ℝ) :=
      atom_mem_mkAtomSet_iff.2 ⟨k, hk1, by exact_mod_cast hkm, rfl⟩
    have hex : ∃ k' : ℕ, 1 ≤ k' ∧ k' ≤ m ∧ Entity.atom (k : ℝ) = Entity.atom (k' : ℝ) :=
      ⟨k, hk1, hkm, rfl⟩
    have hk_eq : hex.choose = k := by
      have hat := Entity.atom_inj.1 hex.choose_spec.2.2
      exact_mod_cast hat.symm
    have hgk : g (Entity.atom (k : ℝ)) = z := by
      simp only [g, hex, ↓reduceDIte]
      have hidx : (⟨hex.choose - 1, by have := hex.choose_spec; omega⟩ : Fin m) = j := by
        ext; dsimp [j, k] at hk_eq ⊢; omega
      rw [hidx]
      exact congrArg Subtype.val (eqv.apply_symm_apply ⟨z, hz_fin⟩)
    have hdom : Entity.atom (k : ℝ) ∈ Entity.relDom f := by
      rw [hfunc.relDom_eq (Entity.isSet_setOfBounded _)]; exact he_mem
    have happ : Entity.funcApp f (Entity.atom (k : ℝ)) = z :=
      (Entity.funcApp_mkFuncEntity hgZ he_mem).trans hgk
    exact ⟨Entity.atom (k : ℝ), he_mem, happ ▸ Entity.kpair_funcApp_mem hdom⟩
  · obtain ⟨_, he₁, _, _, heq1⟩ := hfunc.2.1 _ hp1; obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 heq1
    obtain ⟨_, he₂, _, _, heq2⟩ := hfunc.2.1 _ hp2; obtain ⟨rfl, _⟩ := Entity.kpair_inj.1 heq2
    obtain ⟨_, ⟨k₁, hk₁1, hk₁le, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 he₁
    obtain ⟨_, ⟨k₂, hk₂1, hk₂le, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 he₂
    have hk₁m : k₁ ≤ m := by exact_mod_cast hk₁le
    have hk₂m : k₂ ≤ m := by exact_mod_cast hk₂le
    have hv1 : g (Entity.atom (k₁ : ℝ)) = z :=
      (Entity.funcApp_mkFuncEntity hgZ he₁).symm.trans
        (((Entity.kpair_mem_iff_funcApp_eq hfunc.isFuncEntity).1 hp1).2)
    have hv2 : g (Entity.atom (k₂ : ℝ)) = z :=
      (Entity.funcApp_mkFuncEntity hgZ he₂).symm.trans
        (((Entity.kpair_mem_iff_funcApp_eq hfunc.isFuncEntity).1 hp2).2)
    have hex₁ : ∃ k' : ℕ, 1 ≤ k' ∧ k' ≤ m ∧ Entity.atom (k₁ : ℝ) = Entity.atom (k' : ℝ) :=
      ⟨k₁, hk₁1, hk₁m, rfl⟩
    have hex₂ : ∃ k' : ℕ, 1 ≤ k' ∧ k' ≤ m ∧ Entity.atom (k₂ : ℝ) = Entity.atom (k' : ℝ) :=
      ⟨k₂, hk₂1, hk₂m, rfl⟩
    have hc₁ : hex₁.choose = k₁ := by exact_mod_cast (Entity.atom_inj.1 hex₁.choose_spec.2.2).symm
    have hc₂ : hex₂.choose = k₂ := by exact_mod_cast (Entity.atom_inj.1 hex₂.choose_spec.2.2).symm
    simp only [g, hex₁, hex₂, ↓reduceDIte] at hv1 hv2
    have heqv_eq := eqv.injective (Subtype.ext (hv1.trans hv2.symm))
    have hfin_eq : hex₁.choose - 1 = hex₂.choose - 1 := congrArg Fin.val heqv_eq
    have hkk : k₁ = k₂ := by omega
    rw [hkk]

/-- Goldblatt **Theorem 13.17.1** (pp. 179–180): A set `B : Entity Y` is **hyperfinite**
(`F.IsHyperfiniteSet B`) **if and only if** `B.IsSet` and there exist `n ∈ F.star nat0Entity` and
an **internal bijection** `f : F.initSeg n → B`! (Moreover, when `B` is nonempty,
`n ∈ F.star posNatEntity`, i.e., `n ∈ *ℕ`.) -/
theorem Framework.isHyperfiniteSet_iff_exists_internal_bijection {Y : Type*} (F : Framework ℝ Y)
    {B : Entity Y} :
    F.IsHyperfiniteSet B ↔
      B.IsSet ∧ ∃ n ∈ F.star nat0Entity, ∃ f : Entity Y,
        F.IsInternalEntity f ∧ Entity.IsBijectiveFromTo f (F.initSeg n) B := by
  constructor
  · rintro ⟨A, hBA⟩
    have hBset : B.IsSet := (F.mem_star_finPowerset_of_isHyperfiniteSet_of_subset ⟨A, hBA⟩
      (fun x hx ↦ (Entity.mem_powerset_iff.1 (F.mem_powerset_star_of_mem_star_powerset
        (F.mem_star_powerset_of_mem_star_finPowerset hBA))).2 x hx) |> fun h ↦
          (Entity.mem_powerset_iff.1 (F.mem_powerset_star_of_mem_star_powerset
            (F.mem_star_powerset_of_mem_star_finPowerset h))).1)
    let n : Entity Y := Entity.funcApp (F.star (cardFun A)) B
    have hf_card := (F.isFuncFromTo_star_iff).2 (isFuncFromTo_cardFun A)
    have hdomB : B ∈ Entity.relDom (F.star (cardFun A)) := by
      rw [hf_card.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_finPowerset A))]; exact hBA
    have hnN : n ∈ F.star nat0Entity :=
      hf_card.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨B, Entity.kpair_funcApp_mem hdomB⟩)
    -- Transfer `∀ Z ∈ 𝒫_F(A), ∃ f ∈ 𝒫(ℕ × A), ∃ V ∈ 𝒫_F(ℕ), V = initSeg(cardFun A Z) ∧ bij(V, Z, f)`
    let φ : UFormula ℝ :=
      .forallIn 1 (.const (Entity.finPowerset A))
        (.existsIn 2 (.const (Entity.powerset (Entity.prod posNatEntity A)))
          (.existsIn 0 (.const (Entity.finPowerset posNatEntity))
            (.conj
              (.eq (.var 0) (.app (.const initSegFun) (.app (.const (cardFun A)) (.var 1))))
              (bijBetweenFormula ℝ))))
    have hsent : IsSentence φ := by
      rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
      intro v hv
      simp only [φ, freeVarsUFormula, freeVarsUTerm, Finset.empty_union, Finset.mem_erase,
        Finset.mem_union, Finset.mem_singleton] at hv
      obtain ⟨hv1, hv2, hv0, (rfl | rfl) | hbij⟩ := hv
      · exact hv0 rfl
      · exact hv1 rfl
      · have := freeVars_bijBetweenFormula hbij; omega
    have hstd : SentenceHolds φ := by
      refine ⟨Entity.finPowerset A, rfl, fun Z hZ ↦ ?_⟩
      obtain ⟨f, hfP, hbij⟩ := std_exists_bijection_initSeg_cardFun hZ
      have hcZ_mem : Entity.funcApp (cardFun A) Z ∈ nat0Entity :=
        (isFuncFromTo_cardFun A).mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨Z,
          Entity.kpair_funcApp_mem (by
            rw [(isFuncFromTo_cardFun A).relDom_eq (Entity.isSet_finPowerset A)]; exact hZ)⟩)
      let V : Entity ℝ := Entity.funcApp initSegFun (Entity.funcApp (cardFun A) Z)
      have hV_mem : V ∈ Entity.finPowerset posNatEntity :=
        isFuncFromTo_initSegFun.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨_,
          Entity.kpair_funcApp_mem (by
            rw [isFuncFromTo_initSegFun.relDom_eq (Entity.isSet_setOfBounded _)]; exact hcZ_mem)⟩)
      let env₃ := Function.update (Function.update
        (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 1 Z) 2 f) 0 V
      have happ_ev : evalUTerm env₃
          (.app (.const initSegFun) (.app (.const (cardFun A)) (.var 1))) = some V := by
        rw [evalUTerm_app_eq_some_iff]
        refine ⟨initSegFun, Entity.funcApp (cardFun A) Z, rfl, ?_,
          isFuncFromTo_initSegFun.isFuncEntity, ?_, rfl⟩
        · rw [evalUTerm_app_eq_some_iff]
          refine ⟨cardFun A, Z, rfl, by simp [env₃], (isFuncFromTo_cardFun A).isFuncEntity, ?_, rfl⟩
          rw [(isFuncFromTo_cardFun A).relDom_eq (Entity.isSet_finPowerset A)]; exact hZ
        · rw [isFuncFromTo_initSegFun.relDom_eq (Entity.isSet_setOfBounded _)]; exact hcZ_mem
      dsimp only [env₃] at happ_ev
      refine ⟨_, rfl, f, hfP, _, rfl, V, hV_mem, ⟨V, by simp, happ_ev⟩, ?_⟩
      rw [holds_bijBetweenFormula_iff (D := V) (C := Z) (Entity.mem_powerset_iff.1 hfP).1
        (by simp) (by simp) (by simp)]
      exact hbij
    obtain ⟨_, hFd, hallZ⟩ := (F.transfer φ hsent).1 hstd
    obtain rfl := Option.some.inj hFd
    obtain ⟨_, hPd, f, hfP, _, hVd, V, _, ⟨qV, hq1, hq2⟩, hbij_hold⟩ := hallZ B hBA
    obtain rfl := Option.some.inj hPd; obtain rfl := Option.some.inj hVd
    have hV1 : V = qV := Option.some.inj (by simpa using hq1)
    have hf_seg := (F.isFuncFromTo_star_iff).2 isFuncFromTo_initSegFun
    have hdom_n : n ∈ Entity.relDom (F.star initSegFun) := by
      rw [hf_seg.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_setOfBounded _))]; exact hnN
    have happ_star : evalUTerm
        (Function.update (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 1 B) 2 f) 0 V)
        (starTerm F.star (.app (.const initSegFun) (.app (.const (cardFun A)) (.var 1)))) =
        some (F.initSeg n) := by
      simp only [starTerm]
      rw [evalUTerm_app_eq_some_iff]
      refine ⟨F.star initSegFun, n, rfl, ?_, hf_seg.isFuncEntity, hdom_n, rfl⟩
      rw [evalUTerm_app_eq_some_iff]
      exact ⟨F.star (cardFun A), B, rfl, by simp, hf_card.isFuncEntity, hdomB, rfl⟩
    have hV2 : F.initSeg n = qV := Option.some.inj (happ_star.symm.trans hq2)
    have hVeq : V = F.initSeg n := hV1.trans hV2.symm
    subst hVeq
    obtain ⟨hfP_sub, hf_int⟩ := F.mem_star_powerset_iff.1 hfP
    have hf_set : f.IsSet := (Entity.mem_powerset_iff.1 hfP_sub).1
    rw [starFormula_bijBetweenFormula, holds_bijBetweenFormula_iff (D := F.initSeg n) (C := B)
      hf_set (by simp) (by simp) (by simp)] at hbij_hold
    exact ⟨hBset, n, hnN, f, hf_int, hbij_hold⟩
  · rintro ⟨hBset, n, hnN, f, hf_int, hbij⟩
    -- Range of internal `f` is `B`, so `B` is internal!
    have hB_eq_ran : B = Entity.relRan f := by
      refine Entity.set_ext hBset (Entity.isSet_relRan f) fun y ↦ ?_
      rw [Entity.mem_relRan_iff]
      exact ⟨fun hyB ↦ let ⟨x, _, hp⟩ := hbij.1.2 y hyB; ⟨x, hp⟩,
        fun ⟨x, hp⟩ ↦ hbij.1.1.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨x, hp⟩)⟩
    have hB_int : F.IsInternalEntity B := hB_eq_ran ▸ F.isInternalEntity_relRan hf_int
    obtain ⟨A, _, hstarA, hBA⟩ := F.exists_mem_star_transitiveSet_of_isInternalEntity hB_int
    have hBP : B ∈ F.star (Entity.powerset A) :=
      F.mem_star_powerset_iff.2 ⟨Entity.mem_powerset_iff.2
        ⟨hBset, fun y hyB ↦ hstarA.2 B hBA y hyB⟩, hB_int⟩
    have hseg_sub : ∀ x ∈ F.initSeg n, x ∈ F.star posNatEntity :=
      fun x hx ↦ ((F.mem_initSeg_iff hnN).1 hx).1
    have hfP : f ∈ F.star (Entity.powerset (Entity.prod posNatEntity A)) := by
      rw [F.mem_star_powerset_iff, F.star_prod]
      refine ⟨Entity.mem_powerset_iff.2 ⟨hbij.1.1.1, fun p hp ↦ ?_⟩, hf_int⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := hbij.1.1.2.1 p hp
      exact Entity.kpair_mem_prod_iff.2 ⟨hseg_sub x hx, hstarA.2 B hBA y hy⟩
    -- Transfer converse: surjection from `initSeg(n)` onto `Z ∈ 𝒫(A)` implies `Z ∈ 𝒫_F(A)`
    let ψ : UFormula ℝ :=
      .forallIn 1 (.const (Entity.powerset A))
        (.imp
          (.existsIn 7 (.const nat0Entity)
            (.existsIn 2 (.const (Entity.powerset (Entity.prod posNatEntity A)))
              (.existsIn 0 (.const (Entity.finPowerset posNatEntity))
                (.conj
                  (.eq (.var 0) (.app (.const initSegFun) (.var 7)))
                  (surjBetweenFormula ℝ)))))
          (.mem (.var 1) (.const (Entity.finPowerset A))))
    have hsent : IsSentence ψ := by
      rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
      intro v hv
      simp only [ψ, freeVarsUFormula, freeVarsUTerm, Finset.empty_union, Finset.mem_erase,
        Finset.mem_union, Finset.mem_singleton] at hv
      rcases hv with ⟨hv1, ⟨hv7, hv2, hv0, (rfl | rfl) | hsurj⟩ | (rfl | hvF)⟩
      · exact hv0 rfl
      · exact hv7 rfl
      · have := freeVars_surjBetweenFormula hsurj; omega
      · exact hv1 rfl
      · simp at hvF
    have hstd : SentenceHolds ψ := by
      refine ⟨Entity.powerset A, rfl,
        fun Z hZP ⟨_, hNd, en, hen, _, hPd, g, hgP, _, hVd, V, hVF, ⟨qV, hq1, hq2⟩, hsurj_g⟩ ↦ ?_⟩
      obtain rfl := Option.some.inj hNd; obtain rfl := Option.some.inj hPd
      obtain rfl := Option.some.inj hVd
      obtain ⟨hZs, hZsub⟩ := Entity.mem_powerset_iff.1 hZP
      obtain ⟨_, _, hVfin⟩ := Entity.mem_finPowerset_iff.1 hVF
      have hg_set : g.IsSet := (Entity.mem_powerset_iff.1 hgP).1
      rw [holds_surjBetweenFormula_iff (D := V) (C := Z) hg_set
        (by simp) (by simp) (by simp)] at hsurj_g
      have hZ_sub_img : Z.extSet ⊆ Entity.funcApp g '' V.extSet := by
        intro z hz
        obtain ⟨x, hxV, hp⟩ := hsurj_g.2 z hz
        exact ⟨x, hxV, ((Entity.kpair_mem_iff_funcApp_eq hsurj_g.1.isFuncEntity).1 hp).2⟩
      exact ⟨Z, Entity.finPowerset A, by simp, rfl,
        Entity.mem_finPowerset_iff.2 ⟨hZs, hZsub, (hVfin.image _).subset hZ_sub_img⟩⟩
    obtain ⟨_, hPd, hallZ⟩ := (F.transfer ψ hsent).1 hstd
    obtain rfl := Option.some.inj hPd
    have hf_seg := (F.isFuncFromTo_star_iff).2 isFuncFromTo_initSegFun
    have hdom_n : n ∈ Entity.relDom (F.star initSegFun) := by
      rw [hf_seg.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_setOfBounded _))]; exact hnN
    have hseg_hold :
        Holds (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 1 B)
          (starFormula F.star (.existsIn 7 (.const nat0Entity)
            (.existsIn 2 (.const (Entity.powerset (Entity.prod posNatEntity A)))
              (.existsIn 0 (.const (Entity.finPowerset posNatEntity))
                (.conj (.eq (.var 0) (.app (.const initSegFun) (.var 7)))
                  (surjBetweenFormula ℝ)))))) := by
      refine ⟨F.star nat0Entity, rfl, n, hnN, _, rfl, f, hfP, _, rfl,
        F.initSeg n, F.initSeg_mem_star_finPowerset hnN,
        ⟨F.initSeg n, by simp, ?_⟩, ?_⟩
      · rw [starTerm, evalUTerm_app_eq_some_iff]
        exact ⟨F.star initSegFun, n, rfl, by simp, hf_seg.isFuncEntity, hdom_n, rfl⟩
      · rw [starFormula_surjBetweenFormula,
          holds_surjBetweenFormula_iff (D := F.initSeg n) (C := B) hbij.1.1.1
            (by simp) (by simp) (by simp)]
        exact hbij.1
    obtain ⟨B', FA', hB', hFA', hm⟩ := hallZ B hBP hseg_hold
    have h1 : B = B' := Option.some.inj (by simpa using hB')
    obtain rfl := Option.some.inj hFA'
    exact ⟨A, h1 ▸ hm⟩

/-! ## §13.18 Exercises on Hyperfinite Sets and Sizes (Part 1: Exercises 1–3) -/

/-- Goldblatt **Exercise 13.18(1) (Part 1)** (p. 180): If `n, m ∈ F.star nat0Entity` and there is an
internal injection `f : F.initSeg n → F.initSeg m`, then `(n, m) ∈ F.star realLeRel` (`n ≤ m`)! -/
theorem Framework.le_of_internal_injection_initSeg {Y : Type*} (F : Framework ℝ Y)
    {n m f : Entity Y} (hn : n ∈ F.star nat0Entity) (hm : m ∈ F.star nat0Entity)
    (hf_int : F.IsInternalEntity f)
    (hfunc : Entity.IsFuncFromTo f (F.initSeg n) (F.initSeg m))
    (hinj : f.IsInjectiveFunc) :
    Entity.kpair n m ∈ F.star realLeRel := by
  have hfP : f ∈ F.star (Entity.powerset (Entity.prod posNatEntity posNatEntity)) := by
    rw [F.mem_star_powerset_iff, F.star_prod]
    refine ⟨Entity.mem_powerset_iff.2 ⟨hfunc.1, fun p hp ↦ ?_⟩, hf_int⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := hfunc.2.1 p hp
    exact Entity.kpair_mem_prod_iff.2
      ⟨((F.mem_initSeg_iff hn).1 hx).1, ((F.mem_initSeg_iff hm).1 hy).1⟩
  let φ : UFormula ℝ :=
    .forallIn 7 (.const nat0Entity)
      (.forallIn 8 (.const nat0Entity)
        (.imp
          (.existsIn 2 (.const (Entity.powerset (Entity.prod posNatEntity posNatEntity)))
            (.existsIn 0 (.const (Entity.finPowerset posNatEntity))
              (.existsIn 1 (.const (Entity.finPowerset posNatEntity))
                (.conj
                  (.conj
                    (.eq (.var 0) (.app (.const initSegFun) (.var 7)))
                    (.eq (.var 1) (.app (.const initSegFun) (.var 8))))
                  (injBetweenFormula ℝ)))))
          (.mem (UTerm.pair (.var 7) (.var 8)) (.const realLeRel))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v hv
    simp only [φ, freeVarsUFormula, freeVarsUTerm_pair, freeVarsUTerm, Finset.empty_union,
      Finset.mem_erase, Finset.mem_union, Finset.mem_singleton] at hv
    rcases hv with ⟨hv7, hv8, ⟨hv2, hv0, hv1, ((rfl | rfl) | (rfl | rfl)) | hinj_v⟩ | ((rfl | rfl) | hF)⟩
    · exact hv0 rfl
    · exact hv7 rfl
    · exact hv1 rfl
    · exact hv8 rfl
    · have := freeVars_injBetweenFormula hinj_v; omega
    · exact hv7 rfl
    · exact hv8 rfl
    · simp at hF
  have hstd : SentenceHolds φ := by
    refine ⟨nat0Entity, rfl, fun en hen ↦ ⟨nat0Entity, rfl, fun em hem
      ⟨_, hPd, g, hgP, _, hV0, V₀, _, _, hV1, V₁, _, ⟨⟨⟨q0, hq0a, hq0b⟩, ⟨q1, hq1a, hq1b⟩⟩, hinj_g⟩⟩ ↦ ?_⟩⟩
    obtain rfl := Option.some.inj hPd
    obtain ⟨_, ⟨kn, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 hen
    obtain ⟨_, ⟨km, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 hem
    have hseg_ev : ∀ k : ℕ, Entity.funcApp initSegFun (Entity.atom (k : ℝ)) = initSegStd (k : ℝ) := by
      intro k
      have hk_mem : Entity.atom (k : ℝ) ∈ nat0Entity := atom_mem_mkAtomSet_iff.2 ⟨k, rfl⟩
      have hv := Entity.funcApp_mkFuncEntity (B := Entity.finPowerset posNatEntity)
        (g := fun e ↦ initSegStd (Entity.atomVal 0 e))
        (fun e he ↦ by obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 he; simpa using initSegStd_mem_finPowerset j)
        hk_mem
      simpa [initSegFun, Entity.atomVal] using hv
    have hV0_eq : V₀ = initSegStd (kn : ℝ) := by
      have h1 : V₀ = q0 := Option.some.inj (by simpa using hq0a)
      obtain ⟨_, a0, hc0, ha0, _, _, hq0_eq⟩ := evalUTerm_app_eq_some_iff.1 hq0b
      obtain rfl := Option.some.inj hc0
      obtain rfl := Option.some.inj (by simpa using ha0)
      exact h1.trans (hq0_eq.symm.trans (hseg_ev kn))
    have hV1_eq : V₁ = initSegStd (km : ℝ) := by
      have h1 : V₁ = q1 := Option.some.inj (by simpa using hq1a)
      obtain ⟨_, a1, hc1, ha1, _, _, hq1_eq⟩ := evalUTerm_app_eq_some_iff.1 hq1b
      obtain rfl := Option.some.inj hc1
      obtain rfl := Option.some.inj (by simpa using ha1)
      exact h1.trans (hq1_eq.symm.trans (hseg_ev km))
    subst hV0_eq; subst hV1_eq
    rw [holds_injBetweenFormula_iff (D := initSegStd (kn : ℝ)) (C := initSegStd (km : ℝ))
      (Entity.mem_powerset_iff.1 hgP).1 (by simp) (by simp) (by simp)] at hinj_g
    obtain ⟨hg_fn, hg_inj⟩ := hinj_g
    -- Pigeonhole on `Finset.Icc 1 kn → Finset.Icc 1 km`
    have hinj_on : Set.InjOn (fun k : ℕ ↦ Entity.funcApp g (Entity.atom (k : ℝ)))
        (Finset.Icc 1 kn : Set ℕ) := by
      intro i hi j hj hij
      obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 (Finset.mem_coe.1 hi)
      obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 (Finset.mem_coe.1 hj)
      have hi_mem : Entity.atom (i : ℝ) ∈ initSegStd (kn : ℝ) :=
        atom_mem_mkAtomSet_iff.2 ⟨i, hi1, by exact_mod_cast hik, rfl⟩
      have hj_mem : Entity.atom (j : ℝ) ∈ initSegStd (kn : ℝ) :=
        atom_mem_mkAtomSet_iff.2 ⟨j, hj1, by exact_mod_cast hjk, rfl⟩
      have hidom : Entity.atom (i : ℝ) ∈ Entity.relDom g := by
        rw [hg_fn.relDom_eq (Entity.isSet_setOfBounded _)]; exact hi_mem
      have hjdom : Entity.atom (j : ℝ) ∈ Entity.relDom g := by
        rw [hg_fn.relDom_eq (Entity.isSet_setOfBounded _)]; exact hj_mem
      have hp1 := Entity.kpair_funcApp_mem hidom
      dsimp only at hij
      have hp2 : Entity.kpair (Entity.atom (j : ℝ)) (Entity.funcApp g (Entity.atom (i : ℝ))) ∈ g :=
        hij ▸ Entity.kpair_funcApp_mem hjdom
      have hat := hg_inj.2 _ _ _ hp1 hp2
      exact_mod_cast Entity.atom_inj.1 hat
    have himg_sub : (Finset.Icc 1 kn).image (fun k : ℕ ↦ Entity.funcApp g (Entity.atom (k : ℝ))) ⊆
        (Finset.Icc 1 km).image (fun k : ℕ ↦ Entity.atom (k : ℝ)) := by
      classical
      intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
      obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
      have hi_mem : Entity.atom (i : ℝ) ∈ initSegStd (kn : ℝ) :=
        atom_mem_mkAtomSet_iff.2 ⟨i, hi1, by exact_mod_cast hik, rfl⟩
      have hidom : Entity.atom (i : ℝ) ∈ Entity.relDom g := by
        rw [hg_fn.relDom_eq (Entity.isSet_setOfBounded _)]; exact hi_mem
      have hgi_mem : Entity.funcApp g (Entity.atom (i : ℝ)) ∈ initSegStd (km : ℝ) :=
        hg_fn.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hidom⟩)
      obtain ⟨_, ⟨j, hj1, hjle, rfl⟩, hjeq⟩ := mem_mkAtomSet_iff.1 hgi_mem
      have hjm : j ≤ km := by exact_mod_cast hjle
      exact Finset.mem_image.2 ⟨j, Finset.mem_Icc.2 ⟨hj1, hjm⟩, hjeq.symm⟩
    have hcard_le : kn ≤ km := by
      classical
      have hc1 : ((Finset.Icc 1 kn).image (fun k : ℕ ↦ Entity.funcApp g (Entity.atom (k : ℝ)))).card = kn := by
        rw [Finset.card_image_of_injOn hinj_on, Nat.card_Icc]; omega
      have hc2 : ((Finset.Icc 1 km).image (fun k : ℕ ↦ Entity.atom (k : ℝ))).card ≤ km :=
        (Finset.card_image_le).trans (by rw [Nat.card_Icc]; omega)
      exact hc1 ▸ (Finset.card_le_card himg_sub).trans hc2
    exact ⟨Entity.kpair (Entity.atom (kn : ℝ)) (Entity.atom (km : ℝ)), realLeRel,
      by simp [evalUTerm_pair], rfl, kpair_atom_mem_realLeRel_iff.2 (by exact_mod_cast hcard_le)⟩
  obtain ⟨_, hN1, hall1⟩ := (F.transfer φ hsent).1 hstd; obtain rfl := Option.some.inj hN1
  obtain ⟨_, hN2, hall2⟩ := hall1 n hn; obtain rfl := Option.some.inj hN2
  have hf_seg := (F.isFuncFromTo_star_iff).2 isFuncFromTo_initSegFun
  have hdn : n ∈ Entity.relDom (F.star initSegFun) := by
    rw [hf_seg.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_setOfBounded _))]; exact hn
  have hdm : m ∈ Entity.relDom (F.star initSegFun) := by
    rw [hf_seg.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_setOfBounded _))]; exact hm
  obtain ⟨p, R', hp, hR', hle⟩ := hall2 m hm
    ⟨_, rfl, f, hfP, _, rfl, F.initSeg n, F.initSeg_mem_star_finPowerset hn,
     _, rfl, F.initSeg m, F.initSeg_mem_star_finPowerset hm,
     ⟨⟨⟨F.initSeg n, by simp, by
         rw [starTerm, evalUTerm_app_eq_some_iff]
         exact ⟨F.star initSegFun, n, rfl, by simp, hf_seg.isFuncEntity, hdn, rfl⟩⟩,
       ⟨F.initSeg m, by simp, by
         rw [starTerm, evalUTerm_app_eq_some_iff]
         exact ⟨F.star initSegFun, m, rfl, by simp, hf_seg.isFuncEntity, hdm, rfl⟩⟩⟩,
      by
        rw [starFormula_injBetweenFormula,
          holds_injBetweenFormula_iff (D := F.initSeg n) (C := F.initSeg m)
            hfunc.1 (by simp) (by simp) (by simp)]
        exact ⟨hfunc, hinj⟩⟩⟩
  obtain rfl := Option.some.inj hR'
  have hpeq : Entity.kpair n m = p :=
    Option.some.inj (by simpa [starTerm_pair, evalUTerm_pair] using hp)
  exact hpeq ▸ hle

/-- Antisymmetry of `F.star realLeRel` on `F.star realEntity` (helper for Exercise 13.18(1)). -/
theorem Framework.eq_of_star_realLeRel_symm {Y : Type*} (F : Framework ℝ Y) {a b : Entity Y}
    (ha : a ∈ F.star realEntity) (hb : b ∈ F.star realEntity)
    (hab : Entity.kpair a b ∈ F.star realLeRel) (hba : Entity.kpair b a ∈ F.star realLeRel) :
    a = b := by
  let φ : UFormula ℝ :=
    .forallIn 0 (.const realEntity)
      (.forallIn 1 (.const realEntity)
        (.imp
          (.conj
            (.mem (UTerm.pair (.var 0) (.var 1)) (.const realLeRel))
            (.mem (UTerm.pair (.var 1) (.var 0)) (.const realLeRel)))
          (.eq (.var 0) (.var 1))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm]; tauto
  have hstd : SentenceHolds φ := by
    refine ⟨realEntity, rfl, fun ea hea ↦ ⟨realEntity, rfl, fun eb heb ⟨⟨p1, R1, hp1, hR1, h1⟩, ⟨p2, R2, hp2, hR2, h2⟩⟩ ↦ ?_⟩⟩
    obtain ⟨ra, rfl⟩ := mem_baseSet_iff.1 hea
    obtain ⟨rb, rfl⟩ := mem_baseSet_iff.1 heb
    obtain rfl := Option.some.inj hR1; obtain rfl := Option.some.inj hR2
    have he1 : Entity.kpair (Entity.atom ra) (Entity.atom rb) = p1 :=
      Option.some.inj (by simpa [evalUTerm_pair] using hp1)
    have he2 : Entity.kpair (Entity.atom rb) (Entity.atom ra) = p2 :=
      Option.some.inj (by simpa [evalUTerm_pair] using hp2)
    have hr_eq : ra = rb := le_antisymm
      (kpair_atom_mem_realLeRel_iff.1 (he1 ▸ h1))
      (kpair_atom_mem_realLeRel_iff.1 (he2 ▸ h2))
    exact ⟨Entity.atom ra, by simp, by simp [hr_eq]⟩
  obtain ⟨_, hR1, hall1⟩ := (F.transfer φ hsent).1 hstd; obtain rfl := Option.some.inj hR1
  obtain ⟨_, hR2, hall2⟩ := hall1 a ha; obtain rfl := Option.some.inj hR2
  obtain ⟨z, hz1, hz2⟩ := hall2 b hb ⟨
    ⟨Entity.kpair a b, F.star realLeRel, by simp [starTerm_pair, evalUTerm_pair], rfl, hab⟩,
    ⟨Entity.kpair b a, F.star realLeRel, by simp [starTerm_pair, evalUTerm_pair], rfl, hba⟩⟩
  exact (Option.some.inj (by simpa using hz1)).trans (Option.some.inj (by simpa using hz2)).symm

/-- Goldblatt **Exercise 13.18(1) (Part 2)** (p. 180): If `n, m ∈ F.star nat0Entity` and there is an
internal bijection `f : F.initSeg n → F.initSeg m`, then `n = m`! -/
theorem Framework.eq_of_internal_bijection_initSeg {Y : Type*} (F : Framework ℝ Y)
    {n m f : Entity Y} (hn : n ∈ F.star nat0Entity) (hm : m ∈ F.star nat0Entity)
    (hf_int : F.IsInternalEntity f)
    (hbij : Entity.IsBijectiveFromTo f (F.initSeg n) (F.initSeg m)) :
    n = m := by
  have hle1 : Entity.kpair n m ∈ F.star realLeRel :=
    F.le_of_internal_injection_initSeg hn hm hf_int hbij.1.1 hbij.2
  have hinv_fn : Entity.IsFuncFromTo (Entity.relInv f) (F.initSeg m) (F.initSeg n) := by
    refine ⟨Entity.isSet_relInv f, fun p hp ↦ ?_, fun y x₁ x₂ h1 h2 ↦ ?_, fun y hy ↦ ?_⟩
    · obtain ⟨a, b, hp_f, rfl⟩ := Entity.mem_relInv_iff.1 hp
      obtain ⟨_, ha, _, hb, heq⟩ := hbij.1.1.2.1 _ hp_f
      obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 heq
      exact ⟨b, hb, a, ha, rfl⟩
    · exact hbij.2.2 x₁ x₂ y (Entity.kpair_mem_relInv_iff.1 h1) (Entity.kpair_mem_relInv_iff.1 h2)
    · obtain ⟨x, hx, hp⟩ := hbij.1.2 y hy
      exact ⟨x, hx, Entity.kpair_mem_relInv_iff.2 hp⟩
  have hinv_inj : (Entity.relInv f).IsInjectiveFunc :=
    ⟨hinv_fn.isFuncEntity, fun y₁ y₂ x h1 h2 ↦
      hbij.1.1.2.2.1 x y₁ y₂ (Entity.kpair_mem_relInv_iff.1 h1) (Entity.kpair_mem_relInv_iff.1 h2)⟩
  have hle2 : Entity.kpair m n ∈ F.star realLeRel :=
    F.le_of_internal_injection_initSeg hm hn (F.isInternalEntity_relInv hf_int) hinv_fn hinv_inj
  have hsubR : ∀ z ∈ nat0Entity, z ∈ realEntity := fun z hz ↦ by
    obtain ⟨r, _, rfl⟩ := mem_mkAtomSet_iff.1 hz; exact mem_baseSet_iff.2 ⟨r, rfl⟩
  exact F.eq_of_star_realLeRel_symm ((F.subset_star_iff.2 hsubR) _ hn)
    ((F.subset_star_iff.2 hsubR) _ hm) hle1 hle2

/-- Goldblatt §13.17 (p. 180): **Internal Cardinality** `|B|` (`F.hyperCard B`) of a hyperfinite
set `B` — the unique `n ∈ *ℕ₀` admitting an internal bijection `F.initSeg n → B` (defaulting to `∅`
when `B` is not hyperfinite). -/
def Framework.hyperCard {Y : Type*} (F : Framework ℝ Y) (B : Entity Y) : Entity Y :=
  open Classical in
  if h : F.IsHyperfiniteSet B then
    ((F.isHyperfiniteSet_iff_exists_internal_bijection.1 h).2).choose
  else ∅

/-- Characterization and uniqueness of `F.hyperCard B`: for any hyperfinite `B`, `F.hyperCard B`
belongs to `F.star nat0Entity`, admits an internal bijection `F.initSeg (F.hyperCard B) → B`, and
equals ANY `n ∈ F.star nat0Entity` admitting an internal bijection `F.initSeg n → B` (in particular,
`F.hyperCard B = Entity.funcApp (F.star (cardFun A)) B` whenever `B ∈ *𝒫_F(A)`;
Goldblatt §13.17, p. 180). -/
theorem Framework.hyperCard_spec {Y : Type*} (F : Framework ℝ Y) {B : Entity Y}
    (hB : F.IsHyperfiniteSet B) :
    F.hyperCard B ∈ F.star nat0Entity ∧
    (∃ f : Entity Y, F.IsInternalEntity f ∧
      Entity.IsBijectiveFromTo f (F.initSeg (F.hyperCard B)) B) ∧
    (∀ n ∈ F.star nat0Entity,
      (∃ g : Entity Y, F.IsInternalEntity g ∧ Entity.IsBijectiveFromTo g (F.initSeg n) B) →
        n = F.hyperCard B) := by
  classical
  have hspec := ((F.isHyperfiniteSet_iff_exists_internal_bijection.1 hB).2).choose_spec
  have heq : F.hyperCard B = ((F.isHyperfiniteSet_iff_exists_internal_bijection.1 hB).2).choose := by
    simp [Framework.hyperCard, hB]
  rw [← heq] at hspec
  refine ⟨hspec.1, hspec.2, fun n hn ⟨g, hg_int, hg_bij⟩ ↦ ?_⟩
  obtain ⟨f, hf_int, hf_bij⟩ := hspec.2
  -- Compose `g : initSeg n → B` with `f⁻¹ : B → initSeg (hyperCard B)`
  let h := Entity.relComp g (Entity.relInv f)
  have hh_int : F.IsInternalEntity h :=
    F.isInternalEntity_relComp hg_int (F.isInternalEntity_relInv hf_int)
  have hh_bij : Entity.IsBijectiveFromTo h (F.initSeg n) (F.initSeg (F.hyperCard B)) := by
    have hfn : Entity.IsFuncFromTo h (F.initSeg n) (F.initSeg (F.hyperCard B)) := by
      refine ⟨Entity.isSet_relComp _ _, fun p hp ↦ ?_, fun x y₁ y₂ hm1 hm2 ↦ ?_, fun x hx ↦ ?_⟩
      · obtain ⟨a, b, c, hpg, hpf, rfl⟩ := Entity.mem_relComp_iff.1 hp
        obtain ⟨_, ha, _, _, he1⟩ := hg_bij.1.1.2.1 _ hpg; obtain ⟨rfl, _⟩ := Entity.kpair_inj.1 he1
        obtain ⟨_, hc, _, _, he2⟩ := hf_bij.1.1.2.1 _ (Entity.kpair_mem_relInv_iff.1 hpf)
        obtain ⟨rfl, _⟩ := Entity.kpair_inj.1 he2
        exact ⟨a, ha, c, hc, rfl⟩
      · obtain ⟨b₁, hgb₁, hfb₁⟩ := Entity.kpair_mem_relComp_iff.1 hm1
        obtain ⟨b₂, hgb₂, hfb₂⟩ := Entity.kpair_mem_relComp_iff.1 hm2
        have hbeq : b₁ = b₂ := hg_bij.1.1.2.2.1 x b₁ b₂ hgb₁ hgb₂
        subst hbeq
        exact hf_bij.2.2 y₁ y₂ b₁
          (Entity.kpair_mem_relInv_iff.1 hfb₁) (Entity.kpair_mem_relInv_iff.1 hfb₂)
      · obtain ⟨b, hbB, hgb⟩ := hg_bij.1.1.2.2.2 x hx
        obtain ⟨c, hc, hfc⟩ := hf_bij.1.2 b hbB
        exact ⟨c, hc, Entity.kpair_mem_relComp_iff.2 ⟨b, hgb, Entity.kpair_mem_relInv_iff.2 hfc⟩⟩
    refine ⟨⟨hfn, fun c hc ↦ ?_⟩, ⟨hfn.isFuncEntity, fun x₁ x₂ c hm1 hm2 ↦ ?_⟩⟩
    · obtain ⟨b, hbB, hfc⟩ := hf_bij.1.1.2.2.2 c hc
      obtain ⟨a, ha, hga⟩ := hg_bij.1.2 b hbB
      exact ⟨a, ha, Entity.kpair_mem_relComp_iff.2 ⟨b, hga, Entity.kpair_mem_relInv_iff.2 hfc⟩⟩
    · obtain ⟨b₁, hgb₁, hfb₁⟩ := Entity.kpair_mem_relComp_iff.1 hm1
      obtain ⟨b₂, hgb₂, hfb₂⟩ := Entity.kpair_mem_relComp_iff.1 hm2
      have hbeq : b₁ = b₂ := hf_bij.1.1.2.2.1 c b₁ b₂
        (Entity.kpair_mem_relInv_iff.1 hfb₁) (Entity.kpair_mem_relInv_iff.1 hfb₂)
      subst hbeq
      exact hg_bij.2.2 x₁ x₂ b₁ hgb₁ hgb₂
  exact F.eq_of_internal_bijection_initSeg hn hspec.1 hh_int hh_bij

/-- For every `B ∈ F.star (Entity.finPowerset A)`, `F.hyperCard B` agrees with the transferred
standard cardinality function `Entity.funcApp (F.star (cardFun A)) B`
(Goldblatt §13.17, p. 180). -/
theorem Framework.hyperCard_eq_funcApp_star_cardFun {Y : Type*} (F : Framework ℝ Y)
    {A : Entity ℝ} {B : Entity Y} (hBA : B ∈ F.star (Entity.finPowerset A)) :
    F.hyperCard B = Entity.funcApp (F.star (cardFun A)) B := by
  -- Transfer existence of bijection from `initSeg(cardFun A B)` to `B`, then apply `hyperCard_spec`
  have hf_card := (F.isFuncFromTo_star_iff).2 (isFuncFromTo_cardFun A)
  have hdomB : B ∈ Entity.relDom (F.star (cardFun A)) := by
    rw [hf_card.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_finPowerset A))]; exact hBA
  let n := Entity.funcApp (F.star (cardFun A)) B
  have hnN : n ∈ F.star nat0Entity :=
    hf_card.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨B, Entity.kpair_funcApp_mem hdomB⟩)
  let φ : UFormula ℝ :=
    .forallIn 1 (.const (Entity.finPowerset A))
      (.existsIn 2 (.const (Entity.powerset (Entity.prod posNatEntity A)))
        (.existsIn 0 (.const (Entity.finPowerset posNatEntity))
          (.conj
            (.eq (.var 0) (.app (.const initSegFun) (.app (.const (cardFun A)) (.var 1))))
            (bijBetweenFormula ℝ))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v hv
    simp only [φ, freeVarsUFormula, freeVarsUTerm, Finset.empty_union, Finset.mem_erase,
      Finset.mem_union, Finset.mem_singleton] at hv
    obtain ⟨hv1, hv2, hv0, (rfl | rfl) | hbij⟩ := hv
    · exact hv0 rfl
    · exact hv1 rfl
    · have := freeVars_bijBetweenFormula hbij; omega
  have hstd : SentenceHolds φ := by
    refine ⟨Entity.finPowerset A, rfl, fun Z hZ ↦ ?_⟩
    obtain ⟨f, hfP, hbij⟩ := std_exists_bijection_initSeg_cardFun hZ
    have hcZ_mem : Entity.funcApp (cardFun A) Z ∈ nat0Entity :=
      (isFuncFromTo_cardFun A).mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨Z,
        Entity.kpair_funcApp_mem (by
          rw [(isFuncFromTo_cardFun A).relDom_eq (Entity.isSet_finPowerset A)]; exact hZ)⟩)
    let V : Entity ℝ := Entity.funcApp initSegFun (Entity.funcApp (cardFun A) Z)
    have hV_mem : V ∈ Entity.finPowerset posNatEntity :=
      isFuncFromTo_initSegFun.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨_,
        Entity.kpair_funcApp_mem (by
          rw [isFuncFromTo_initSegFun.relDom_eq (Entity.isSet_setOfBounded _)]; exact hcZ_mem)⟩)
    let env₃ := Function.update (Function.update
      (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 1 Z) 2 f) 0 V
    have happ_ev : evalUTerm env₃
        (.app (.const initSegFun) (.app (.const (cardFun A)) (.var 1))) = some V := by
      rw [evalUTerm_app_eq_some_iff]
      refine ⟨initSegFun, Entity.funcApp (cardFun A) Z, rfl, ?_,
        isFuncFromTo_initSegFun.isFuncEntity, ?_, rfl⟩
      · rw [evalUTerm_app_eq_some_iff]
        refine ⟨cardFun A, Z, rfl, by simp [env₃], (isFuncFromTo_cardFun A).isFuncEntity, ?_, rfl⟩
        rw [(isFuncFromTo_cardFun A).relDom_eq (Entity.isSet_finPowerset A)]; exact hZ
      · rw [isFuncFromTo_initSegFun.relDom_eq (Entity.isSet_setOfBounded _)]; exact hcZ_mem
    dsimp only [env₃] at happ_ev
    refine ⟨_, rfl, f, hfP, _, rfl, V, hV_mem, ⟨V, by simp, happ_ev⟩, ?_⟩
    rw [holds_bijBetweenFormula_iff (D := V) (C := Z) (Entity.mem_powerset_iff.1 hfP).1
      (by simp) (by simp) (by simp)]
    exact hbij
  obtain ⟨_, hFd, hallZ⟩ := (F.transfer φ hsent).1 hstd
  obtain rfl := Option.some.inj hFd
  obtain ⟨_, hPd, f, hfP, _, hVd, V, _, ⟨qV, hq1, hq2⟩, hbij_hold⟩ := hallZ B hBA
  obtain rfl := Option.some.inj hPd; obtain rfl := Option.some.inj hVd
  have hf_seg := (F.isFuncFromTo_star_iff).2 isFuncFromTo_initSegFun
  have hdom_n : n ∈ Entity.relDom (F.star initSegFun) := by
    rw [hf_seg.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_setOfBounded _))]; exact hnN
  have happ_star : evalUTerm
      (Function.update (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 1 B) 2 f) 0 V)
      (starTerm F.star (.app (.const initSegFun) (.app (.const (cardFun A)) (.var 1)))) =
      some (F.initSeg n) := by
    simp only [starTerm]; rw [evalUTerm_app_eq_some_iff]
    refine ⟨F.star initSegFun, n, rfl, ?_, hf_seg.isFuncEntity, hdom_n, rfl⟩
    rw [evalUTerm_app_eq_some_iff]
    exact ⟨F.star (cardFun A), B, rfl, by simp, hf_card.isFuncEntity, hdomB, rfl⟩
  have hVeq : V = F.initSeg n :=
    (Option.some.inj (by simpa using hq1)).trans (Option.some.inj (happ_star.symm.trans hq2)).symm
  subst hVeq
  obtain ⟨hfP_sub, hf_int⟩ := F.mem_star_powerset_iff.1 hfP
  rw [starFormula_bijBetweenFormula, holds_bijBetweenFormula_iff (D := F.initSeg n) (C := B)
    (Entity.mem_powerset_iff.1 hfP_sub).1 (by simp) (by simp) (by simp)] at hbij_hold
  exact ((F.hyperCard_spec ⟨A, hBA⟩).2.2 n hnN ⟨f, hf_int, hbij_hold⟩).symm

/-- Goldblatt **Exercise 13.18(2)** (p. 180): Any internal subset `B ⊆ A` of a hyperfinite set `A`
is also hyperfinite, and has `(|B|, |A|) ∈ F.star realLeRel` (`|B| ≤ |A|`)! -/
theorem Framework.isHyperfiniteSet_and_hyperCard_le_of_subset {Y : Type*} (F : Framework ℝ Y)
    {A B : Entity Y} (hA : F.IsHyperfiniteSet A)
    (hBset : B.IsSet) (hBsub : ∀ x ∈ B, x ∈ A) (hBint : F.IsInternalEntity B) :
    F.IsHyperfiniteSet B ∧ Entity.kpair (F.hyperCard B) (F.hyperCard A) ∈ F.star realLeRel := by
  obtain ⟨C, hAC⟩ := hA
  have hAsubC : ∀ x ∈ A, x ∈ F.star C :=
    (Entity.mem_powerset_iff.1 (F.mem_powerset_star_of_mem_star_powerset
      (F.mem_star_powerset_of_mem_star_finPowerset hAC))).2
  have hBP : B ∈ F.star (Entity.powerset C) :=
    F.mem_star_powerset_iff.2 ⟨Entity.mem_powerset_iff.2
      ⟨hBset, fun x hxB ↦ hAsubC x (hBsub x hxB)⟩, hBint⟩
  let φ : UFormula ℝ :=
    .forallIn 0 (.const (Entity.finPowerset C))
      (.forallIn 1 (.const (Entity.powerset C))
        (.imp
          (.forallIn 2 (.var 1) (.mem (.var 2) (.var 0)))
          (.conj
            (.mem (.var 1) (.const (Entity.finPowerset C)))
            (.mem (UTerm.pair (.app (.const (cardFun C)) (.var 1))
                              (.app (.const (cardFun C)) (.var 0))) (.const realLeRel)))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm]
  have hstd : SentenceHolds φ := by
    refine ⟨Entity.finPowerset C, rfl, fun ZA hZA ↦ ⟨Entity.powerset C, rfl, fun ZB hZB ⟨_, hZB0, hsub_ev⟩ ↦ ?_⟩⟩
    obtain rfl := Option.some.inj (by simpa using hZB0)
    obtain ⟨_, _, hZAfin⟩ := Entity.mem_finPowerset_iff.1 hZA
    obtain ⟨hZBs, hZBsubC⟩ := Entity.mem_powerset_iff.1 hZB
    have hBA_sub : ZB.extSet ⊆ ZA.extSet := fun x hxB ↦ by
      obtain ⟨x', ZA', hx', hZA', hm⟩ := hsub_ev x hxB
      have h1 : x = x' := Option.some.inj (by simpa using hx')
      have h2 : ZA = ZA' := Option.some.inj (by simpa using hZA')
      exact h1 ▸ h2 ▸ hm
    have hZBfin : ZB.extSet.Finite := hZAfin.subset hBA_sub
    have hZB_finP : ZB ∈ Entity.finPowerset C :=
      Entity.mem_finPowerset_iff.2 ⟨hZBs, hZBsubC, hZBfin⟩
    refine ⟨⟨ZB, Entity.finPowerset C, by simp, rfl, hZB_finP⟩, ?_⟩
    classical
    have hcard_le : hZBfin.toFinset.card ≤ hZAfin.toFinset.card :=
      Finset.card_le_card fun x hx ↦ (Set.Finite.mem_toFinset hZAfin).2
        (hBA_sub ((Set.Finite.mem_toFinset hZBfin).1 hx))
    have hcA := funcApp_cardFun hZA
    have hcB := funcApp_cardFun hZB_finP
    have hdA : ZA ∈ Entity.relDom (cardFun C) := by
      rw [(isFuncFromTo_cardFun C).relDom_eq (Entity.isSet_finPowerset C)]; exact hZA
    have hdB : ZB ∈ Entity.relDom (cardFun C) := by
      rw [(isFuncFromTo_cardFun C).relDom_eq (Entity.isSet_finPowerset C)]; exact hZB_finP
    let env₂ := Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0 ZA) 1 ZB
    have hevA : evalUTerm env₂ (.app (.const (cardFun C)) (.var 0)) =
        some (Entity.funcApp (cardFun C) ZA) :=
      evalUTerm_app_eq_some_iff.2 ⟨cardFun C, ZA, rfl, by simp [env₂],
        (isFuncFromTo_cardFun C).isFuncEntity, hdA, rfl⟩
    have hevB : evalUTerm env₂ (.app (.const (cardFun C)) (.var 1)) =
        some (Entity.funcApp (cardFun C) ZB) :=
      evalUTerm_app_eq_some_iff.2 ⟨cardFun C, ZB, rfl, by simp [env₂],
        (isFuncFromTo_cardFun C).isFuncEntity, hdB, rfl⟩
    dsimp only [env₂] at hevA hevB
    refine ⟨Entity.kpair (Entity.funcApp (cardFun C) ZB) (Entity.funcApp (cardFun C) ZA),
      realLeRel, by simp [evalUTerm_pair, hevA, hevB], rfl, ?_⟩
    rw [hcA, hcB]
    exact kpair_atom_mem_realLeRel_iff.2 (by exact_mod_cast hcard_le)
  obtain ⟨_, hFC, hallA⟩ := (F.transfer φ hsent).1 hstd; obtain rfl := Option.some.inj hFC
  obtain ⟨_, hPC, hallB⟩ := hallA A hAC; obtain rfl := Option.some.inj hPC
  obtain ⟨⟨B', FC', hB', hFC', hBC⟩, ⟨p, R', hp, hR', hle⟩⟩ := hallB B hBP
    ⟨B, by simp, fun x hxB ↦ ⟨x, A, by simp, by simp, hBsub x hxB⟩⟩
  have hBeq : B = B' := Option.some.inj (by simpa using hB')
  obtain rfl := Option.some.inj hFC'
  have hBC' : B ∈ F.star (Entity.finPowerset C) := hBeq ▸ hBC
  obtain rfl := Option.some.inj hR'
  have hf_card := (F.isFuncFromTo_star_iff).2 (isFuncFromTo_cardFun C)
  have hdA : A ∈ Entity.relDom (F.star (cardFun C)) := by
    rw [hf_card.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_finPowerset C))]; exact hAC
  have hdB : B ∈ Entity.relDom (F.star (cardFun C)) := by
    rw [hf_card.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_finPowerset C))]; exact hBC'
  let envY := Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 A) 1 B
  have hevA : evalUTerm envY (starTerm F.star (.app (.const (cardFun C)) (.var 0))) =
      some (Entity.funcApp (F.star (cardFun C)) A) := by
    rw [starTerm, evalUTerm_app_eq_some_iff]
    exact ⟨F.star (cardFun C), A, rfl, by simp [envY], hf_card.isFuncEntity, hdA, rfl⟩
  have hevB : evalUTerm envY (starTerm F.star (.app (.const (cardFun C)) (.var 1))) =
      some (Entity.funcApp (F.star (cardFun C)) B) := by
    rw [starTerm, evalUTerm_app_eq_some_iff]
    exact ⟨F.star (cardFun C), B, rfl, by simp [envY], hf_card.isFuncEntity, hdB, rfl⟩
  dsimp only [envY, starTerm] at hevA hevB
  have hpeq : Entity.kpair (Entity.funcApp (F.star (cardFun C)) B)
      (Entity.funcApp (F.star (cardFun C)) A) = p :=
    Option.some.inj (by simpa [starTerm_pair, evalUTerm_pair, hevA, hevB] using hp)
  rw [F.hyperCard_eq_funcApp_star_cardFun hBC', F.hyperCard_eq_funcApp_star_cardFun hAC]
  exact ⟨⟨C, hBC'⟩, hpeq ▸ hle⟩

/-- Goldblatt **Exercise 13.18(3)** (p. 180): Any nonempty hyperfinite subset `B` of `*ℝ` has a
**least** element and a **greatest** element with respect to `F.star realLeRel`! -/
theorem Framework.exists_least_and_greatest_of_hyperfinite_real {Y : Type*} (F : Framework ℝ Y)
    {B : Entity Y} (hB : F.IsHyperfiniteSet B)
    (hBsub : ∀ x ∈ B, x ∈ F.star realEntity) (hne : ∃ x : Entity Y, x ∈ B) :
    (∃ m ∈ B, ∀ x ∈ B, Entity.kpair m x ∈ F.star realLeRel) ∧
    (∃ M ∈ B, ∀ x ∈ B, Entity.kpair x M ∈ F.star realLeRel) := by
  have hBF : B ∈ F.star (Entity.finPowerset realEntity) :=
    F.mem_star_finPowerset_of_isHyperfiniteSet_of_subset hB hBsub
  let φ : UFormula ℝ :=
    .forallIn 0 (.const (Entity.finPowerset realEntity))
      (.imp
        (.existsIn 1 (.var 0) (.eq (.var 1) (.var 1)))
        (.conj
          (.existsIn 1 (.var 0)
            (.forallIn 2 (.var 0) (.mem (UTerm.pair (.var 1) (.var 2)) (.const realLeRel))))
          (.existsIn 1 (.var 0)
            (.forallIn 2 (.var 0) (.mem (UTerm.pair (.var 2) (.var 1)) (.const realLeRel))))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm]; tauto
  have hstd : SentenceHolds φ := by
    refine ⟨Entity.finPowerset realEntity, rfl, fun Z hZ ⟨_, hZ0, ex₀, hex₀, _⟩ ↦ ?_⟩
    obtain rfl := Option.some.inj (by simpa using hZ0)
    obtain ⟨_, hZsubR, hZfin⟩ := Entity.mem_finPowerset_iff.1 hZ
    obtain ⟨r₀, rfl⟩ := mem_baseSet_iff.1 (hZsubR ex₀ hex₀)
    classical
    let S : Finset ℝ := hZfin.toFinset.image (Entity.atomVal 0)
    have hS_ne : S.Nonempty := ⟨r₀, Finset.mem_image.2
      ⟨Entity.atom r₀, (Set.Finite.mem_toFinset hZfin).2 hex₀, by simp [Entity.atomVal]⟩⟩
    have hmin_mem : Entity.atom (S.min' hS_ne) ∈ Z := by
      obtain ⟨ez, hez, hval⟩ := Finset.mem_image.1 (Finset.min'_mem S hS_ne)
      have hezZ := (Set.Finite.mem_toFinset hZfin).1 hez
      obtain ⟨rz, rfl⟩ := mem_baseSet_iff.1 (hZsubR ez hezZ)
      rw [Entity.atomVal_atom] at hval
      exact hval ▸ hezZ
    have hmax_mem : Entity.atom (S.max' hS_ne) ∈ Z := by
      obtain ⟨ez, hez, hval⟩ := Finset.mem_image.1 (Finset.max'_mem S hS_ne)
      have hezZ := (Set.Finite.mem_toFinset hZfin).1 hez
      obtain ⟨rz, rfl⟩ := mem_baseSet_iff.1 (hZsubR ez hezZ)
      rw [Entity.atomVal_atom] at hval
      exact hval ▸ hezZ
    refine ⟨⟨Z, by simp, Entity.atom (S.min' hS_ne), hmin_mem, Z, by simp, fun ex hex ↦ ?_⟩,
      ⟨Z, by simp, Entity.atom (S.max' hS_ne), hmax_mem, Z, by simp, fun ex hex ↦ ?_⟩⟩
    · obtain ⟨rx, rfl⟩ := mem_baseSet_iff.1 (hZsubR ex hex)
      have hrxS : rx ∈ S := Finset.mem_image.2
        ⟨Entity.atom rx, (Set.Finite.mem_toFinset hZfin).2 hex, by simp [Entity.atomVal]⟩
      exact ⟨Entity.kpair (Entity.atom (S.min' hS_ne)) (Entity.atom rx), realLeRel,
        by simp [evalUTerm_pair], rfl, kpair_atom_mem_realLeRel_iff.2 (Finset.min'_le S rx hrxS)⟩
    · obtain ⟨rx, rfl⟩ := mem_baseSet_iff.1 (hZsubR ex hex)
      have hrxS : rx ∈ S := Finset.mem_image.2
        ⟨Entity.atom rx, (Set.Finite.mem_toFinset hZfin).2 hex, by simp [Entity.atomVal]⟩
      exact ⟨Entity.kpair (Entity.atom rx) (Entity.atom (S.max' hS_ne)), realLeRel,
        by simp [evalUTerm_pair], rfl, kpair_atom_mem_realLeRel_iff.2 (Finset.le_max' S rx hrxS)⟩
  obtain ⟨_, hFR, hallB⟩ := (F.transfer φ hsent).1 hstd; obtain rfl := Option.some.inj hFR
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨⟨_, hB1, m, hmB, _, hB2, hm_le⟩, ⟨_, hB3, M, hMB, _, hB4, hM_ge⟩⟩ :=
    hallB B hBF ⟨B, by simp, x₀, hx₀, x₀, by simp, by simp⟩
  obtain rfl := Option.some.inj (by simpa using hB1)
  obtain rfl := Option.some.inj (by simpa using hB2)
  obtain rfl := Option.some.inj (by simpa using hB3)
  obtain rfl := Option.some.inj (by simpa using hB4)
  refine ⟨⟨m, hmB, fun x hxB ↦ ?_⟩, ⟨M, hMB, fun x hxB ↦ ?_⟩⟩
  · obtain ⟨p, R', hp, hR', hle⟩ := hm_le x hxB
    obtain rfl := Option.some.inj hR'
    have hpeq : Entity.kpair m x = p :=
      Option.some.inj (by simpa [starTerm_pair, evalUTerm_pair] using hp)
    exact hpeq ▸ hle
  · obtain ⟨p, R', hp, hR', hle⟩ := hM_ge x hxB
    obtain rfl := Option.some.inj hR'
    have hpeq : Entity.kpair x M = p :=
      Option.some.inj (by simpa [starTerm_pair, evalUTerm_pair] using hp)
    exact hpeq ▸ hle

/-! ## §13.18 Exercises on Hyperfinite Sets and Sizes (Part 2: Exercises 4–6) -/

/-- Goldblatt **Exercise 13.18(4)** (p. 180): The **internal power set**
`𝒫_I(A) = 𝒫(A) ∩ *𝕌 = {B ⊆ A : B is internal}` (`F.internalPowerset A`). -/
def Framework.internalPowerset {X Y : Type*} (F : Framework X Y) (A : Entity Y) : Entity Y :=
  Entity.setOfBounded {B : Entity Y | B ∈ Entity.powerset A ∧ F.IsInternalEntity B}

/-- `F.internalPowerset A` is a set entity. -/
@[simp]
theorem Framework.isSet_internalPowerset {X Y : Type*} (F : Framework X Y) (A : Entity Y) :
    (F.internalPowerset A).IsSet :=
  Entity.isSet_setOfBounded _

/-- Membership in `F.internalPowerset A`: `B ∈ 𝒫_I(A) ↔ B ∈ 𝒫(A) ∧ F.IsInternalEntity B`
(Goldblatt §13.18, Exercise 4, p. 180). -/
@[simp]
theorem Framework.mem_internalPowerset_iff {X Y : Type*} (F : Framework X Y) {A B : Entity Y} :
    B ∈ F.internalPowerset A ↔ B ∈ Entity.powerset A ∧ F.IsInternalEntity B := by
  have hbdd : IsBoundedRank {Z : Entity Y | Z ∈ Entity.powerset A ∧ F.IsInternalEntity Z} :=
    (Entity.isBoundedRank_extSet (Entity.powerset A)).subset fun _ h ↦ h.1
  rw [Framework.internalPowerset, Entity.mem_setOfBounded hbdd]
  rfl

/-- By Theorem 13.12.1, `𝒫_I(*C) = *𝒫(C)` for every standard set `*C` (`C : Entity X`). -/
@[simp]
theorem Framework.internalPowerset_star {X Y : Type*} (F : Framework X Y) (C : Entity X) :
    F.internalPowerset (F.star C) = F.star (Entity.powerset C) := by
  refine Entity.set_ext (F.isSet_internalPowerset _)
    ((F.isSet_star_iff).2 (Entity.isSet_powerset C)) fun B ↦ ?_
  rw [F.mem_internalPowerset_iff, F.mem_star_powerset_iff]

/-- Standard base-2 exponential function `n ↦ 2^n` from `nat0Entity` to `posNatEntity`
(Goldblatt §13.18, Exercise 4, p. 180). -/
def pow2Fun : Entity ℝ :=
  Entity.mkFuncEntity nat0Entity
    (fun e ↦ Entity.atom (((2 ^ Nat.floor (Entity.atomVal 0 e) : ℕ) : ℝ)))

/-- `pow2Fun` is a set-theoretic function `nat0Entity → posNatEntity`. -/
theorem isFuncFromTo_pow2Fun : Entity.IsFuncFromTo pow2Fun nat0Entity posNatEntity := by
  refine Entity.isFuncFromTo_mkFuncEntity fun e _ ↦ ?_
  exact atom_mem_mkAtomSet_iff.2 ⟨2 ^ Nat.floor (Entity.atomVal 0 e), Nat.one_le_two_pow, rfl⟩

/-- Evaluation of `pow2Fun` on `Entity.atom (n : ℝ)` (`n : ℕ`) yields `Entity.atom ((2^n : ℕ) : ℝ)`. -/
@[simp]
theorem funcApp_pow2Fun (n : ℕ) :
    Entity.funcApp pow2Fun (Entity.atom (n : ℝ)) = Entity.atom (((2 ^ n : ℕ) : ℝ)) := by
  have hn : Entity.atom (n : ℝ) ∈ nat0Entity := atom_mem_mkAtomSet_iff.2 ⟨n, rfl⟩
  have hv := Entity.funcApp_mkFuncEntity (B := posNatEntity)
    (g := fun e ↦ Entity.atom (((2 ^ Nat.floor (Entity.atomVal 0 e) : ℕ) : ℝ)))
    (fun e _ ↦ atom_mem_mkAtomSet_iff.2 ⟨_, Nat.one_le_two_pow, rfl⟩) hn
  simpa [pow2Fun, Entity.atomVal_atom] using hv

/-- Standard finite-powerset map `Z ↦ 𝒫(Z)` from `Entity.finPowerset C` to
`Entity.finPowerset (Entity.powerset C)` (helper for Exercise 13.18(4)). -/
def finPowersetMap (C : Entity ℝ) : Entity ℝ :=
  Entity.mkFuncEntity (Entity.finPowerset C) Entity.powerset

/-- Every finite subset `Z ∈ Entity.finPowerset C` has `Entity.powerset Z ∈ Entity.finPowerset (Entity.powerset C)`
with cardinality `2 ^ |Z|`. -/
theorem powerset_mem_finPowerset_and_card {C Z : Entity ℝ} (hZ : Z ∈ Entity.finPowerset C) :
    Entity.powerset Z ∈ Entity.finPowerset (Entity.powerset C) ∧
      Entity.funcApp (cardFun (Entity.powerset C)) (Entity.powerset Z) =
        Entity.funcApp pow2Fun (Entity.funcApp (cardFun C) Z) := by
  classical
  obtain ⟨hZs, hZsub, hZfin⟩ := Entity.mem_finPowerset_iff.1 hZ
  let FZ : Finset (Entity ℝ) := hZfin.toFinset
  let FP : Finset (Entity ℝ) := FZ.powerset.image Entity.finsetEntity
  have hPZ_eq : (Entity.powerset Z).extSet = (FP : Set (Entity ℝ)) := by
    ext B
    simp only [Entity.extSet, Set.mem_ofPred_eq, Entity.mem_powerset_iff, FP, Finset.mem_coe,
      Finset.mem_image, Finset.mem_powerset]
    constructor
    · rintro ⟨hBs, hBsubZ⟩
      have hBfin : B.extSet.Finite := hZfin.subset hBsubZ
      refine ⟨hBfin.toFinset, fun x hx ↦ (Set.Finite.mem_toFinset hZfin).2
        (hBsubZ x ((Set.Finite.mem_toFinset hBfin).1 hx)), ?_⟩
      refine Entity.set_ext (Entity.isSet_finsetEntity _) hBs fun x ↦ ?_
      rw [Entity.mem_finsetEntity_iff, Set.Finite.mem_toFinset]
      rfl
    · rintro ⟨s, hsFZ, rfl⟩
      refine ⟨Entity.isSet_finsetEntity s, fun x hx ↦ ?_⟩
      exact (Set.Finite.mem_toFinset hZfin).1 (hsFZ (Entity.mem_finsetEntity_iff.1 hx))
  have hPZ_fin : (Entity.powerset Z).extSet.Finite := by
    rw [hPZ_eq]; exact FP.finite_toSet
  have hPZ_mem : Entity.powerset Z ∈ Entity.finPowerset (Entity.powerset C) := by
    refine Entity.mem_finPowerset_iff.2 ⟨Entity.isSet_powerset Z, fun B hB ↦ ?_, hPZ_fin⟩
    obtain ⟨hBs, hBsubZ⟩ := Entity.mem_powerset_iff.1 hB
    exact Entity.mem_powerset_iff.2 ⟨hBs, fun x hx ↦ hZsub x (hBsubZ x hx)⟩
  refine ⟨hPZ_mem, ?_⟩
  have hinj : Set.InjOn (Entity.finsetEntity : Finset (Entity ℝ) → Entity ℝ)
      (FZ.powerset : Set (Finset (Entity ℝ))) := by
    intro s₁ _ s₂ _ heq
    ext x
    simpa [Entity.mem_finsetEntity_iff] using congrArg (fun E ↦ x ∈ E) heq
  have htoFin : hPZ_fin.toFinset = FP := by
    ext B
    rw [Set.Finite.mem_toFinset, hPZ_eq, Finset.mem_coe]
  have hcard_FP : FP.card = 2 ^ FZ.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_powerset]
  rw [funcApp_cardFun hPZ_mem, funcApp_cardFun hZ, funcApp_pow2Fun]
  exact congrArg Entity.atom (by exact_mod_cast (congrArg Finset.card htoFin).trans hcard_FP)

/-- `finPowersetMap C` is a set-theoretic function `Entity.finPowerset C → Entity.finPowerset (Entity.powerset C)`. -/
theorem isFuncFromTo_finPowersetMap (C : Entity ℝ) :
    Entity.IsFuncFromTo (finPowersetMap C)
      (Entity.finPowerset C) (Entity.finPowerset (Entity.powerset C)) :=
  Entity.isFuncFromTo_mkFuncEntity fun _ hZ ↦ (powerset_mem_finPowerset_and_card hZ).1

/-- Evaluation of `finPowersetMap C` on `Z ∈ Entity.finPowerset C` gives `Entity.powerset Z`. -/
theorem funcApp_finPowersetMap {C Z : Entity ℝ} (hZ : Z ∈ Entity.finPowerset C) :
    Entity.funcApp (finPowersetMap C) Z = Entity.powerset Z :=
  Entity.funcApp_mkFuncEntity (fun _ hW ↦ (powerset_mem_finPowerset_and_card hW).1) hZ

/-- Goldblatt **Exercise 13.18(4)** (p. 180): If `A` is hyperfinite (`F.IsHyperfiniteSet A`), then
its **internal power set** `𝒫_I(A) = 𝒫(A) ∩ *𝕌` (`F.internalPowerset A`) is also **hyperfinite**,
and its internal cardinality satisfies `|𝒫_I(A)| = 2 ^ |A|`
(`F.hyperCard (F.internalPowerset A) = Entity.funcApp (F.star pow2Fun) (F.hyperCard A)`)! -/
theorem Framework.isHyperfiniteSet_internalPowerset_and_hyperCard {Y : Type*}
    (F : Framework ℝ Y) {A : Entity Y} (hA : F.IsHyperfiniteSet A) :
    F.IsHyperfiniteSet (F.internalPowerset A) ∧
      F.hyperCard (F.internalPowerset A) =
        Entity.funcApp (F.star pow2Fun) (F.hyperCard A) := by
  obtain ⟨C, hAC⟩ := hA
  have hAsubC : ∀ x ∈ A, x ∈ F.star C :=
    (Entity.mem_powerset_iff.1 (F.mem_powerset_star_of_mem_star_powerset
      (F.mem_star_powerset_of_mem_star_finPowerset hAC))).2
  have hf_pm := (F.isFuncFromTo_star_iff).2 (isFuncFromTo_finPowersetMap C)
  have hdA_pm : A ∈ Entity.relDom (F.star (finPowersetMap C)) := by
    rw [hf_pm.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_finPowerset C))]; exact hAC
  let W := Entity.funcApp (F.star (finPowersetMap C)) A
  have hW_finP : W ∈ F.star (Entity.finPowerset (Entity.powerset C)) :=
    hf_pm.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨A, Entity.kpair_funcApp_mem hdA_pm⟩)
  have hW_set : W.IsSet :=
    (Entity.mem_powerset_iff.1 (F.mem_powerset_star_of_mem_star_powerset
      (F.mem_star_powerset_of_mem_star_finPowerset hW_finP))).1
  have hW_sub_starPC : ∀ B ∈ W, B ∈ F.star (Entity.powerset C) :=
    (Entity.mem_powerset_iff.1 (F.mem_powerset_star_of_mem_star_powerset
      (F.mem_star_powerset_of_mem_star_finPowerset hW_finP))).2
  -- Transfer Sentence 1: `∀ Z ∈ 𝒫_F(C), ∀ B ∈ 𝒫(C), B ∈ finPowersetMap C Z ↔ ∀ x ∈ B, x ∈ Z`
  -- and Sentence 2: `cardFun (𝒫(C)) (finPowersetMap C Z) = pow2Fun (cardFun C Z)` together!
  let φ : UFormula ℝ :=
    .forallIn 0 (.const (Entity.finPowerset C))
      (.conj
        (.forallIn 1 (.const (Entity.powerset C))
          (.iff
            (.mem (.var 1) (.app (.const (finPowersetMap C)) (.var 0)))
            (.forallIn 2 (.var 1) (.mem (.var 2) (.var 0)))))
        (.eq
          (.app (.const (cardFun (Entity.powerset C))) (.app (.const (finPowersetMap C)) (.var 0)))
          (.app (.const pow2Fun) (.app (.const (cardFun C)) (.var 0)))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm]
  have hstd : SentenceHolds φ := by
    refine ⟨Entity.finPowerset C, rfl, fun Z hZ ↦ ⟨⟨Entity.powerset C, rfl, fun B hB ↦ ?_⟩, ?_⟩⟩
    · have hdomZ : Z ∈ Entity.relDom (finPowersetMap C) := by
        rw [(isFuncFromTo_finPowersetMap C).relDom_eq (Entity.isSet_finPowerset C)]; exact hZ
      have hev_pm : evalUTerm (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0 Z) 1 B)
          (.app (.const (finPowersetMap C)) (.var 0)) = some (Entity.powerset Z) :=
        evalUTerm_app_eq_some_iff.2 ⟨finPowersetMap C, Z, rfl, by simp,
          (isFuncFromTo_finPowersetMap C).isFuncEntity, hdomZ, funcApp_finPowersetMap hZ⟩
      obtain ⟨hBs, _⟩ := Entity.mem_powerset_iff.1 hB
      constructor
      · rintro ⟨B', P', hB', hP', hm⟩
        have hBeq : B = B' := Option.some.inj (by simpa using hB')
        have hPeq : Entity.powerset Z = P' := Option.some.inj (hev_pm.symm.trans hP')
        have hsub := (Entity.mem_powerset_iff.1 (hBeq ▸ hPeq ▸ hm)).2
        exact ⟨B, by simp, fun x hxB ↦ ⟨x, Z, by simp, by simp, hsub x hxB⟩⟩
      · rintro ⟨_, hB0, hallx⟩
        obtain rfl := Option.some.inj (by simpa using hB0)
        have hBPZ : B ∈ Entity.powerset Z := Entity.mem_powerset_iff.2 ⟨hBs, fun x hxB ↦ by
          obtain ⟨x', Z', hx', hZ', hm⟩ := hallx x hxB
          have h1 : x = x' := Option.some.inj (by simpa using hx')
          have h2 : Z = Z' := Option.some.inj (by simpa using hZ')
          exact h1 ▸ h2 ▸ hm⟩
        exact ⟨B, Entity.powerset Z, by simp, hev_pm, hBPZ⟩
    · obtain ⟨hPZ_mem, hcard_eq⟩ := powerset_mem_finPowerset_and_card hZ
      have hdZ_pm : Z ∈ Entity.relDom (finPowersetMap C) := by
        rw [(isFuncFromTo_finPowersetMap C).relDom_eq (Entity.isSet_finPowerset C)]; exact hZ
      have hdPZ_c : Entity.powerset Z ∈ Entity.relDom (cardFun (Entity.powerset C)) := by
        rw [(isFuncFromTo_cardFun _).relDom_eq (Entity.isSet_finPowerset _)]; exact hPZ_mem
      have hdZ_c : Z ∈ Entity.relDom (cardFun C) := by
        rw [(isFuncFromTo_cardFun C).relDom_eq (Entity.isSet_finPowerset C)]; exact hZ
      have hcZ_mem : Entity.funcApp (cardFun C) Z ∈ nat0Entity :=
        (isFuncFromTo_cardFun C).mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨Z, Entity.kpair_funcApp_mem hdZ_c⟩)
      have hd_p2 : Entity.funcApp (cardFun C) Z ∈ Entity.relDom pow2Fun := by
        rw [isFuncFromTo_pow2Fun.relDom_eq (Entity.isSet_setOfBounded _)]; exact hcZ_mem
      let env₁ := Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0 Z
      have hev1 : evalUTerm env₁
          (.app (.const (cardFun (Entity.powerset C))) (.app (.const (finPowersetMap C)) (.var 0))) =
          some (Entity.funcApp (cardFun (Entity.powerset C)) (Entity.powerset Z)) := by
        rw [evalUTerm_app_eq_some_iff]
        refine ⟨_, Entity.powerset Z, rfl, ?_, (isFuncFromTo_cardFun _).isFuncEntity, hdPZ_c, rfl⟩
        exact evalUTerm_app_eq_some_iff.2 ⟨_, Z, rfl, by simp [env₁],
          (isFuncFromTo_finPowersetMap C).isFuncEntity, hdZ_pm, funcApp_finPowersetMap hZ⟩
      have hev2 : evalUTerm env₁ (.app (.const pow2Fun) (.app (.const (cardFun C)) (.var 0))) =
          some (Entity.funcApp pow2Fun (Entity.funcApp (cardFun C) Z)) := by
        rw [evalUTerm_app_eq_some_iff]
        refine ⟨pow2Fun, Entity.funcApp (cardFun C) Z, rfl, ?_,
          isFuncFromTo_pow2Fun.isFuncEntity, hd_p2, rfl⟩
        exact evalUTerm_app_eq_some_iff.2 ⟨cardFun C, Z, rfl, by simp [env₁],
          (isFuncFromTo_cardFun C).isFuncEntity, hdZ_c, rfl⟩
      dsimp only [env₁] at hev1 hev2
      exact ⟨_, hev1, hcard_eq ▸ hev2⟩
  obtain ⟨_, hFC, hallA⟩ := (F.transfer φ hsent).1 hstd; obtain rfl := Option.some.inj hFC
  obtain ⟨⟨_, hPC, hallB⟩, ⟨q, hq1, hq2⟩⟩ := hallA A hAC; obtain rfl := Option.some.inj hPC
  have hPA_eq_W : F.internalPowerset A = W := by
    refine Entity.set_ext (F.isSet_internalPowerset A) hW_set fun B ↦ ?_
    have hev_W : ∀ B₀ : Entity Y,
        evalUTerm (Function.update (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 A) 1 B₀)
          (starTerm F.star (.app (.const (finPowersetMap C)) (.var 0))) = some W := fun B₀ ↦ by
      rw [starTerm, evalUTerm_app_eq_some_iff]
      exact ⟨F.star (finPowersetMap C), A, rfl, by simp, hf_pm.isFuncEntity, hdA_pm, rfl⟩
    constructor
    · intro hB_in
      obtain ⟨hBPA, hBint⟩ := F.mem_internalPowerset_iff.1 hB_in
      obtain ⟨hBs, hBsubA⟩ := Entity.mem_powerset_iff.1 hBPA
      have hB_starPC : B ∈ F.star (Entity.powerset C) :=
        F.mem_star_powerset_iff.2 ⟨Entity.mem_powerset_iff.2
          ⟨hBs, fun x hxB ↦ hAsubC x (hBsubA x hxB)⟩, hBint⟩
      obtain ⟨B', W', hB', hW', hm⟩ := (hallB B hB_starPC).2
        ⟨B, by simp, fun x hxB ↦ ⟨x, A, by simp, by simp, hBsubA x hxB⟩⟩
      have hBeq : B = B' := Option.some.inj (by simpa using hB')
      have hWeq : W = W' := Option.some.inj ((hev_W B).symm.trans hW')
      exact hBeq ▸ hWeq ▸ hm
    · intro hBW
      have hB_starPC : B ∈ F.star (Entity.powerset C) := hW_sub_starPC B hBW
      obtain ⟨hBPC, hBint⟩ := F.mem_star_powerset_iff.1 hB_starPC
      obtain ⟨hBs, _⟩ := Entity.mem_powerset_iff.1 hBPC
      obtain ⟨_, hB0, hallx⟩ := (hallB B hB_starPC).1 ⟨B, W, by simp, hev_W B, hBW⟩
      obtain rfl := Option.some.inj (by simpa using hB0)
      refine F.mem_internalPowerset_iff.2 ⟨Entity.mem_powerset_iff.2 ⟨hBs, fun x hxB ↦ ?_⟩, hBint⟩
      obtain ⟨x', A', hx', hA', hm⟩ := hallx x hxB
      have h1 : x = x' := Option.some.inj (by simpa using hx')
      have h2 : A = A' := Option.some.inj (by simpa using hA')
      exact h1 ▸ h2 ▸ hm
  have hPA_finP : F.internalPowerset A ∈ F.star (Entity.finPowerset (Entity.powerset C)) :=
    hPA_eq_W ▸ hW_finP
  refine ⟨⟨Entity.powerset C, hPA_finP⟩, ?_⟩
  have hf_cPC := (F.isFuncFromTo_star_iff).2 (isFuncFromTo_cardFun (Entity.powerset C))
  have hf_cC := (F.isFuncFromTo_star_iff).2 (isFuncFromTo_cardFun C)
  have hf_p2 := (F.isFuncFromTo_star_iff).2 isFuncFromTo_pow2Fun
  have hdW_c : W ∈ Entity.relDom (F.star (cardFun (Entity.powerset C))) := by
    rw [hf_cPC.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_finPowerset _))]; exact hW_finP
  have hdA_c : A ∈ Entity.relDom (F.star (cardFun C)) := by
    rw [hf_cC.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_finPowerset C))]; exact hAC
  have hcA_mem : Entity.funcApp (F.star (cardFun C)) A ∈ F.star nat0Entity :=
    hf_cC.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨A, Entity.kpair_funcApp_mem hdA_c⟩)
  have hd_p2 : Entity.funcApp (F.star (cardFun C)) A ∈ Entity.relDom (F.star pow2Fun) := by
    rw [hf_p2.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_setOfBounded _))]; exact hcA_mem
  have hevY1 : evalUTerm (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 A)
      (starTerm F.star (.app (.const (cardFun (Entity.powerset C))) (.app (.const (finPowersetMap C)) (.var 0)))) =
      some (Entity.funcApp (F.star (cardFun (Entity.powerset C))) W) := by
    simp only [starTerm]; rw [evalUTerm_app_eq_some_iff]
    refine ⟨_, W, rfl, ?_, hf_cPC.isFuncEntity, hdW_c, rfl⟩
    exact evalUTerm_app_eq_some_iff.2 ⟨_, A, rfl, by simp, hf_pm.isFuncEntity, hdA_pm, rfl⟩
  have hevY2 : evalUTerm (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 A)
      (starTerm F.star (.app (.const pow2Fun) (.app (.const (cardFun C)) (.var 0)))) =
      some (Entity.funcApp (F.star pow2Fun) (Entity.funcApp (F.star (cardFun C)) A)) := by
    simp only [starTerm]; rw [evalUTerm_app_eq_some_iff]
    refine ⟨_, Entity.funcApp (F.star (cardFun C)) A, rfl, ?_, hf_p2.isFuncEntity, hd_p2, rfl⟩
    exact evalUTerm_app_eq_some_iff.2 ⟨_, A, rfl, by simp, hf_cC.isFuncEntity, hdA_c, rfl⟩
  have hcardY_eq : Entity.funcApp (F.star (cardFun (Entity.powerset C))) W =
      Entity.funcApp (F.star pow2Fun) (Entity.funcApp (F.star (cardFun C)) A) :=
    (Option.some.inj (hevY1.symm.trans hq1)).trans (Option.some.inj (hevY2.symm.trans hq2)).symm
  rw [hPA_eq_W, F.hyperCard_eq_funcApp_star_cardFun hW_finP,
    F.hyperCard_eq_funcApp_star_cardFun hAC]
  exact hcardY_eq

/-- Goldblatt **Exercise 13.18(5)** (p. 180): A set `B : Entity Y` is **hyperfinite**
(`F.IsHyperfiniteSet B`) **if and only if** `B.IsSet` and there exist `n ∈ F.star nat0Entity` and
an **internal surjection** `f : F.initSeg n → B`! -/
theorem Framework.isHyperfiniteSet_iff_exists_internal_surjection {Y : Type*} (F : Framework ℝ Y)
    {B : Entity Y} :
    F.IsHyperfiniteSet B ↔
      B.IsSet ∧ ∃ n ∈ F.star nat0Entity, ∃ f : Entity Y,
        F.IsInternalEntity f ∧ Entity.IsSurjectiveFromTo f (F.initSeg n) B := by
  constructor
  · intro hB
    obtain ⟨hBs, n, hnN, f, hf_int, hbij⟩ := F.isHyperfiniteSet_iff_exists_internal_bijection.1 hB
    exact ⟨hBs, n, hnN, f, hf_int, hbij.1⟩
  · rintro ⟨hBset, n, hnN, f, hf_int, hsurj⟩
    have hB_eq_ran : B = Entity.relRan f := by
      refine Entity.set_ext hBset (Entity.isSet_relRan f) fun y ↦ ?_
      rw [Entity.mem_relRan_iff]
      exact ⟨fun hyB ↦ let ⟨x, _, hp⟩ := hsurj.2 y hyB; ⟨x, hp⟩,
        fun ⟨x, hp⟩ ↦ hsurj.1.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨x, hp⟩)⟩
    have hB_int : F.IsInternalEntity B := hB_eq_ran ▸ F.isInternalEntity_relRan hf_int
    obtain ⟨A, _, hstarA, hBA⟩ := F.exists_mem_star_transitiveSet_of_isInternalEntity hB_int
    have hBP : B ∈ F.star (Entity.powerset A) :=
      F.mem_star_powerset_iff.2 ⟨Entity.mem_powerset_iff.2
        ⟨hBset, fun y hyB ↦ hstarA.2 B hBA y hyB⟩, hB_int⟩
    have hseg_sub : ∀ x ∈ F.initSeg n, x ∈ F.star posNatEntity :=
      fun x hx ↦ ((F.mem_initSeg_iff hnN).1 hx).1
    have hfP : f ∈ F.star (Entity.powerset (Entity.prod posNatEntity A)) := by
      rw [F.mem_star_powerset_iff, F.star_prod]
      refine ⟨Entity.mem_powerset_iff.2 ⟨hsurj.1.1, fun p hp ↦ ?_⟩, hf_int⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := hsurj.1.2.1 p hp
      exact Entity.kpair_mem_prod_iff.2 ⟨hseg_sub x hx, hstarA.2 B hBA y hy⟩
    let ψ : UFormula ℝ :=
      .forallIn 1 (.const (Entity.powerset A))
        (.imp
          (.existsIn 7 (.const nat0Entity)
            (.existsIn 2 (.const (Entity.powerset (Entity.prod posNatEntity A)))
              (.existsIn 0 (.const (Entity.finPowerset posNatEntity))
                (.conj
                  (.eq (.var 0) (.app (.const initSegFun) (.var 7)))
                  (surjBetweenFormula ℝ)))))
          (.mem (.var 1) (.const (Entity.finPowerset A))))
    have hsent : IsSentence ψ := by
      rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
      intro v hv
      simp only [ψ, freeVarsUFormula, freeVarsUTerm, Finset.empty_union, Finset.mem_erase,
        Finset.mem_union, Finset.mem_singleton] at hv
      rcases hv with ⟨hv1, ⟨hv7, hv2, hv0, (rfl | rfl) | hs⟩ | (rfl | hvF)⟩
      · exact hv0 rfl
      · exact hv7 rfl
      · have := freeVars_surjBetweenFormula hs; omega
      · exact hv1 rfl
      · simp at hvF
    have hstd : SentenceHolds ψ := by
      refine ⟨Entity.powerset A, rfl,
        fun Z hZP ⟨_, hNd, en, _, _, hPd, g, hgP, _, hVd, V, hVF, _, hsurj_g⟩ ↦ ?_⟩
      obtain rfl := Option.some.inj hNd; obtain rfl := Option.some.inj hPd
      obtain rfl := Option.some.inj hVd
      obtain ⟨hZs, hZsub⟩ := Entity.mem_powerset_iff.1 hZP
      obtain ⟨_, _, hVfin⟩ := Entity.mem_finPowerset_iff.1 hVF
      have hg_set : g.IsSet := (Entity.mem_powerset_iff.1 hgP).1
      rw [holds_surjBetweenFormula_iff (D := V) (C := Z) hg_set
        (by simp) (by simp) (by simp)] at hsurj_g
      have hZ_sub_img : Z.extSet ⊆ Entity.funcApp g '' V.extSet := by
        intro z hz
        obtain ⟨x, hxV, hp⟩ := hsurj_g.2 z hz
        exact ⟨x, hxV, ((Entity.kpair_mem_iff_funcApp_eq hsurj_g.1.isFuncEntity).1 hp).2⟩
      exact ⟨Z, Entity.finPowerset A, by simp, rfl,
        Entity.mem_finPowerset_iff.2 ⟨hZs, hZsub, (hVfin.image _).subset hZ_sub_img⟩⟩
    obtain ⟨_, hPd, hallZ⟩ := (F.transfer ψ hsent).1 hstd
    obtain rfl := Option.some.inj hPd
    have hf_seg := (F.isFuncFromTo_star_iff).2 isFuncFromTo_initSegFun
    have hdom_n : n ∈ Entity.relDom (F.star initSegFun) := by
      rw [hf_seg.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_setOfBounded _))]; exact hnN
    have hseg_hold :
        Holds (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 1 B)
          (starFormula F.star (.existsIn 7 (.const nat0Entity)
            (.existsIn 2 (.const (Entity.powerset (Entity.prod posNatEntity A)))
              (.existsIn 0 (.const (Entity.finPowerset posNatEntity))
                (.conj (.eq (.var 0) (.app (.const initSegFun) (.var 7)))
                  (surjBetweenFormula ℝ)))))) := by
      refine ⟨F.star nat0Entity, rfl, n, hnN, _, rfl, f, hfP, _, rfl,
        F.initSeg n, F.initSeg_mem_star_finPowerset hnN,
        ⟨F.initSeg n, by simp, ?_⟩, ?_⟩
      · rw [starTerm, evalUTerm_app_eq_some_iff]
        exact ⟨F.star initSegFun, n, rfl, by simp, hf_seg.isFuncEntity, hdom_n, rfl⟩
      · rw [starFormula_surjBetweenFormula,
          holds_surjBetweenFormula_iff (D := F.initSeg n) (C := B) hsurj.1.1
            (by simp) (by simp) (by simp)]
        exact hsurj
    obtain ⟨B', FA', hB', hFA', hm⟩ := hallZ B hBP hseg_hold
    have h1 : B = B' := Option.some.inj (by simpa using hB')
    obtain rfl := Option.some.inj hFA'
    exact ⟨A, h1 ▸ hm⟩

/-- Nonempty form of Goldblatt **Exercise 13.18(5)** (p. 180): for any nonempty set `B`, `B` is
hyperfinite **if and only if** there exist `n ∈ F.star posNatEntity` (`n ∈ *ℕ`) and an internal
surjection `f : F.initSeg n → B`! -/
theorem Framework.isHyperfiniteSet_iff_exists_internal_surjection_posNat {Y : Type*}
    (F : Framework ℝ Y) {B : Entity Y} (hBs : B.IsSet) (hne : ∃ y : Entity Y, y ∈ B) :
    F.IsHyperfiniteSet B ↔
      ∃ n ∈ F.star posNatEntity, ∃ f : Entity Y,
        F.IsInternalEntity f ∧ Entity.IsSurjectiveFromTo f (F.initSeg n) B := by
  have hsubN : ∀ z ∈ posNatEntity, z ∈ nat0Entity := fun z hz ↦ by
    obtain ⟨_, ⟨k, _, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 hz
    exact atom_mem_mkAtomSet_iff.2 ⟨k, rfl⟩
  rw [F.isHyperfiniteSet_iff_exists_internal_surjection]
  constructor
  · rintro ⟨_, n, hn0, f, hf_int, hsurj⟩
    obtain ⟨y₀, hy₀⟩ := hne
    obtain ⟨x₀, hx₀, _⟩ := hsurj.2 y₀ hy₀
    obtain ⟨hx₀N, hx₀le⟩ := (F.mem_initSeg_iff hn0).1 hx₀
    -- Transfer `∀ m ∈ ℕ₀, (∃ k ∈ ℕ, k ≤ m) → m ∈ ℕ`
    let φ : UFormula ℝ :=
      .forallIn 0 (.const nat0Entity)
        (.imp
          (.existsIn 1 (.const posNatEntity)
            (.mem (UTerm.pair (.var 1) (.var 0)) (.const realLeRel)))
          (.mem (.var 0) (.const posNatEntity)))
    have hsent : IsSentence φ := by
      rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
      intro v; simp [φ, freeVarsUFormula, freeVarsUTerm_pair, freeVarsUTerm]
    have hstd : SentenceHolds φ := by
      refine ⟨nat0Entity, rfl, fun em hem ⟨_, hPd, ek, hek, p, R', hp, hR', hle⟩ ↦ ?_⟩
      obtain rfl := Option.some.inj hPd; obtain rfl := Option.some.inj hR'
      obtain ⟨_, ⟨m, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 hem
      obtain ⟨_, ⟨k, hk1, rfl⟩, rfl⟩ := mem_mkAtomSet_iff.1 hek
      have hp_eq : Entity.kpair (Entity.atom (k : ℝ)) (Entity.atom (m : ℝ)) = p :=
        Option.some.inj (by simpa [evalUTerm_pair] using hp)
      have hkm : k ≤ m := by exact_mod_cast kpair_atom_mem_realLeRel_iff.1 (hp_eq ▸ hle)
      exact ⟨Entity.atom (m : ℝ), posNatEntity, by simp, rfl,
        atom_mem_mkAtomSet_iff.2 ⟨m, le_trans hk1 hkm, rfl⟩⟩
    obtain ⟨_, hN0, hall⟩ := (F.transfer φ hsent).1 hstd; obtain rfl := Option.some.inj hN0
    obtain ⟨n', PN', hn', hPN', hnP⟩ := hall n hn0
      ⟨F.star posNatEntity, rfl, x₀, hx₀N, Entity.kpair x₀ n, F.star realLeRel,
        by simp [starTerm_pair, evalUTerm_pair], rfl, hx₀le⟩
    have hneq : n = n' := Option.some.inj (by simpa using hn')
    obtain rfl := Option.some.inj hPN'
    exact ⟨n, hneq ▸ hnP, f, hf_int, hsurj⟩
  · rintro ⟨n, hnP, f, hf_int, hsurj⟩
    exact ⟨hBs, n, (F.subset_star_iff.2 hsubN) n hnP, f, hf_int, hsurj⟩

/-- Goldblatt **Exercise 13.18(6)** (p. 180): **Internal images of hyperfinite sets are hyperfinite**:
if `f` is an internal function (`f.IsFuncEntity ∧ F.IsInternalEntity f`) and `B` is hyperfinite
(`F.IsHyperfiniteSet B`), then the image `f(B)` (`Entity.relImage f B`) is hyperfinite! -/
theorem Framework.isHyperfiniteSet_relImage {Y : Type*} (F : Framework ℝ Y)
    {f B : Entity Y} (hf_fn : f.IsFuncEntity) (hf_int : F.IsInternalEntity f)
    (hB : F.IsHyperfiniteSet B) :
    F.IsHyperfiniteSet (Entity.relImage f B) := by
  let B' := Entity.inter B (Entity.relDom f)
  have hB'_int : F.IsInternalEntity B' :=
    F.isInternalEntity_inter hB.isInternalEntity (F.isInternalEntity_relDom hf_int)
  have hB'_hf : F.IsHyperfiniteSet B' :=
    (F.isHyperfiniteSet_and_hyperCard_le_of_subset hB (Entity.isSet_inter _ _)
      (fun x hx ↦ (Entity.mem_inter_iff.1 hx).1) hB'_int).1
  obtain ⟨_, n, hnN, g, hg_int, hg_bij⟩ := F.isHyperfiniteSet_iff_exists_internal_bijection.1 hB'_hf
  let h := Entity.relComp g f
  have hh_int : F.IsInternalEntity h := F.isInternalEntity_relComp hg_int hf_int
  have hh_surj : Entity.IsSurjectiveFromTo h (F.initSeg n) (Entity.relImage f B) := by
    refine ⟨⟨Entity.isSet_relComp g f, fun p hp ↦ ?_, fun x y₁ y₂ hm1 hm2 ↦ ?_, fun x hx ↦ ?_⟩,
      fun y hy ↦ ?_⟩
    · obtain ⟨a, b, c, hpg, hpf, rfl⟩ := Entity.mem_relComp_iff.1 hp
      obtain ⟨_, ha, _, hb, heq⟩ := hg_bij.1.1.2.1 _ hpg
      obtain ⟨rfl, rfl⟩ := Entity.kpair_inj.1 heq
      exact ⟨a, ha, c, Entity.mem_relImage_iff.2 ⟨b, (Entity.mem_inter_iff.1 hb).1, hpf⟩, rfl⟩
    · obtain ⟨b₁, hgb₁, hfb₁⟩ := Entity.kpair_mem_relComp_iff.1 hm1
      obtain ⟨b₂, hgb₂, hfb₂⟩ := Entity.kpair_mem_relComp_iff.1 hm2
      have hbeq : b₁ = b₂ := hg_bij.1.1.2.2.1 x b₁ b₂ hgb₁ hgb₂
      subst hbeq
      exact hf_fn.2 b₁ y₁ y₂ hfb₁ hfb₂
    · obtain ⟨b, hbB', hgb⟩ := hg_bij.1.1.2.2.2 x hx
      obtain ⟨hbB, hbdom⟩ := Entity.mem_inter_iff.1 hbB'
      obtain ⟨c, hbc⟩ := Entity.mem_relDom_iff.1 hbdom
      exact ⟨c, Entity.mem_relImage_iff.2 ⟨b, hbB, hbc⟩,
        Entity.kpair_mem_relComp_iff.2 ⟨b, hgb, hbc⟩⟩
    · obtain ⟨b, hbB, hbc⟩ := Entity.mem_relImage_iff.1 hy
      have hbB' : b ∈ B' := Entity.mem_inter_iff.2 ⟨hbB, Entity.mem_relDom_iff.2 ⟨y, hbc⟩⟩
      obtain ⟨a, ha, hgb⟩ := hg_bij.1.2 b hbB'
      exact ⟨a, ha, Entity.kpair_mem_relComp_iff.2 ⟨b, hgb, hbc⟩⟩
  exact F.isHyperfiniteSet_iff_exists_internal_surjection.2
    ⟨Entity.isSet_relImage f B, n, hnN, h, hh_int, hh_surj⟩

/-! ## §13.19–13.20 Hyperfinite Summation and Exercises -/

/-- Standard real addition `(x, y) ↦ x + y` as a set-theoretic function
`Entity.prod realEntity realEntity → realEntity` (Goldblatt §13.19–13.20, pp. 180–181). -/
def realAddFun : Entity ℝ :=
  Entity.mkFuncEntity (Entity.prod realEntity realEntity)
    (fun p ↦ Entity.atom (Entity.atomVal 0 (Entity.pairFirst p) +
      Entity.atomVal 0 (Entity.pairSecond p)))

/-- `realAddFun` is a function `ℝ × ℝ → ℝ`. -/
theorem isFuncFromTo_realAddFun :
    Entity.IsFuncFromTo realAddFun (Entity.prod realEntity realEntity) realEntity :=
  Entity.isFuncFromTo_mkFuncEntity fun _ _ ↦ mem_baseSet_iff.2 ⟨_, rfl⟩

/-- Evaluation of `realAddFun` on `(atom a, atom b)`. -/
@[simp]
theorem funcApp_realAddFun (a b : ℝ) :
    Entity.funcApp realAddFun (Entity.kpair (Entity.atom a) (Entity.atom b)) =
      Entity.atom (a + b) := by
  have hp : Entity.kpair (Entity.atom a) (Entity.atom b) ∈ Entity.prod realEntity realEntity :=
    Entity.kpair_mem_prod_iff.2 ⟨mem_baseSet_iff.2 ⟨a, rfl⟩, mem_baseSet_iff.2 ⟨b, rfl⟩⟩
  have hv := Entity.funcApp_mkFuncEntity (B := realEntity)
    (g := fun p ↦ Entity.atom (Entity.atomVal 0 (Entity.pairFirst p) +
      Entity.atomVal 0 (Entity.pairSecond p)))
    (fun _ _ ↦ mem_baseSet_iff.2 ⟨_, rfl⟩) hp
  simpa [realAddFun] using hv

/-- Standard real multiplication `(x, y) ↦ x * y` as a set-theoretic function
`Entity.prod realEntity realEntity → realEntity` (Goldblatt §13.20, p. 181). -/
def realMulFun : Entity ℝ :=
  Entity.mkFuncEntity (Entity.prod realEntity realEntity)
    (fun p ↦ Entity.atom (Entity.atomVal 0 (Entity.pairFirst p) *
      Entity.atomVal 0 (Entity.pairSecond p)))

/-- `realMulFun` is a function `ℝ × ℝ → ℝ`. -/
theorem isFuncFromTo_realMulFun :
    Entity.IsFuncFromTo realMulFun (Entity.prod realEntity realEntity) realEntity :=
  Entity.isFuncFromTo_mkFuncEntity fun _ _ ↦ mem_baseSet_iff.2 ⟨_, rfl⟩

/-- Evaluation of `realMulFun` on `(atom a, atom b)`. -/
@[simp]
theorem funcApp_realMulFun (a b : ℝ) :
    Entity.funcApp realMulFun (Entity.kpair (Entity.atom a) (Entity.atom b)) =
      Entity.atom (a * b) := by
  have hp : Entity.kpair (Entity.atom a) (Entity.atom b) ∈ Entity.prod realEntity realEntity :=
    Entity.kpair_mem_prod_iff.2 ⟨mem_baseSet_iff.2 ⟨a, rfl⟩, mem_baseSet_iff.2 ⟨b, rfl⟩⟩
  have hv := Entity.funcApp_mkFuncEntity (B := realEntity)
    (g := fun p ↦ Entity.atom (Entity.atomVal 0 (Entity.pairFirst p) *
      Entity.atomVal 0 (Entity.pairSecond p)))
    (fun _ _ ↦ mem_baseSet_iff.2 ⟨_, rfl⟩) hp
  simpa [realMulFun] using hv

/-- Transferred addition `x + y` on `F.star realEntity` in a framework `F : Framework ℝ Y`. -/
def Framework.starAdd {Y : Type*} (F : Framework ℝ Y) (x y : Entity Y) : Entity Y :=
  Entity.funcApp (F.star realAddFun) (Entity.kpair x y)

/-- Transferred multiplication `x * y` on `F.star realEntity` in a framework `F : Framework ℝ Y`. -/
def Framework.starMul {Y : Type*} (F : Framework ℝ Y) (x y : Entity Y) : Entity Y :=
  Entity.funcApp (F.star realMulFun) (Entity.kpair x y)

/-- Closure of `F.starAdd` on `F.star realEntity`. -/
theorem Framework.starAdd_mem {Y : Type*} (F : Framework ℝ Y) {x y : Entity Y}
    (hx : x ∈ F.star realEntity) (hy : y ∈ F.star realEntity) :
    F.starAdd x y ∈ F.star realEntity := by
  have hf := (F.isFuncFromTo_star_iff).2 isFuncFromTo_realAddFun
  have hdom : Entity.kpair x y ∈ Entity.relDom (F.star realAddFun) := by
    rw [hf.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hx, hy⟩
  exact hf.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hdom⟩)

/-- Closure of `F.starMul` on `F.star realEntity`. -/
theorem Framework.starMul_mem {Y : Type*} (F : Framework ℝ Y) {x y : Entity Y}
    (hx : x ∈ F.star realEntity) (hy : y ∈ F.star realEntity) :
    F.starMul x y ∈ F.star realEntity := by
  have hf := (F.isFuncFromTo_star_iff).2 isFuncFromTo_realMulFun
  have hdom : Entity.kpair x y ∈ Entity.relDom (F.star realMulFun) := by
    rw [hf.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hx, hy⟩
  exact hf.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hdom⟩)

/-- Goldblatt §13.19 (pp. 180–181): Standard finite-set summation map `B ↦ Σ B` from
`Entity.finPowerset realEntity` to `realEntity`. -/
def realSetSumFun : Entity ℝ :=
  open Classical in
  Entity.mkFuncEntity (Entity.finPowerset realEntity) (fun Z ↦
    if h : Z.extSet.Finite then Entity.atom (∑ x ∈ h.toFinset, Entity.atomVal 0 x)
    else Entity.atom 0)

/-- `realSetSumFun` is a set-theoretic function `𝒫_F(ℝ) → ℝ`. -/
theorem isFuncFromTo_realSetSumFun :
    Entity.IsFuncFromTo realSetSumFun (Entity.finPowerset realEntity) realEntity := by
  classical
  refine Entity.isFuncFromTo_mkFuncEntity fun Z hZ ↦ ?_
  obtain ⟨_, _, hfin⟩ := Entity.mem_finPowerset_iff.1 hZ
  simp only [hfin, ↓reduceDIte]
  exact mem_baseSet_iff.2 ⟨_, rfl⟩

/-- Evaluation of `realSetSumFun` on `Z ∈ Entity.finPowerset realEntity`. -/
theorem funcApp_realSetSumFun {Z : Entity ℝ} (hZ : Z ∈ Entity.finPowerset realEntity) :
    Entity.funcApp realSetSumFun Z =
      Entity.atom (open Classical in ∑ x ∈ (Entity.mem_finPowerset_iff.1 hZ).2.2.toFinset,
        Entity.atomVal 0 x) := by
  classical
  obtain ⟨_, _, hfin⟩ := Entity.mem_finPowerset_iff.1 hZ
  have hv := Entity.funcApp_mkFuncEntity (B := realEntity)
    (g := fun W ↦ if h : W.extSet.Finite then Entity.atom (∑ x ∈ h.toFinset, Entity.atomVal 0 x)
      else Entity.atom 0)
    (fun W hW ↦ by
      obtain ⟨_, _, hw⟩ := Entity.mem_finPowerset_iff.1 hW
      simp only [hw, ↓reduceDIte]; exact mem_baseSet_iff.2 ⟨_, rfl⟩) hZ
  simpa [realSetSumFun, hfin] using hv

/-- Goldblatt §13.19 (p. 181): **Hyperfinite Set Sum** `Σ B` (`F.hyperSetSum B`) of a hyperfinite
subset `B ⊆ *ℝ`, obtained by applying `*realSetSumFun` to `B`. -/
def Framework.hyperSetSum {Y : Type*} (F : Framework ℝ Y) (B : Entity Y) : Entity Y :=
  Entity.funcApp (F.star realSetSumFun) B

/-- For any hyperfinite subset `B ⊆ F.star realEntity`, `F.hyperSetSum B ∈ F.star realEntity`
(Goldblatt §13.19, p. 181). -/
theorem Framework.hyperSetSum_mem_star_realEntity {Y : Type*} (F : Framework ℝ Y)
    {B : Entity Y} (hB : F.IsHyperfiniteSet B) (hsub : ∀ x ∈ B, x ∈ F.star realEntity) :
    F.hyperSetSum B ∈ F.star realEntity := by
  have hBF := F.mem_star_finPowerset_of_isHyperfiniteSet_of_subset hB hsub
  have hf := (F.isFuncFromTo_star_iff).2 isFuncFromTo_realSetSumFun
  have hdom : B ∈ Entity.relDom (F.star realSetSumFun) := by
    rw [hf.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_finPowerset _))]; exact hBF
  exact hf.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨B, Entity.kpair_funcApp_mem hdom⟩)

/-- Standard indexed finite-function summation map `(Z, f) ↦ ∑_{x ∈ Z} f(x)` from
`Entity.prod (Entity.finPowerset A) (Entity.powerset (Entity.prod A realEntity))` to `realEntity`
(accounting properly for multiplicities as in §12.7 so that Exercise 13.20(1)–(2) hold unconditionally;
when `f` is injective on `Z`, this agrees with `realSetSumFun (Entity.relImage f Z)`;
Goldblatt §13.19–13.20, pp. 180–181). -/
def realFunSumFun (A : Entity ℝ) : Entity ℝ :=
  open Classical in
  Entity.mkFuncEntity
    (Entity.prod (Entity.finPowerset A) (Entity.powerset (Entity.prod A realEntity)))
    (fun p ↦
      if h : (Entity.pairFirst p).extSet.Finite then
        Entity.atom (∑ x ∈ h.toFinset,
          Entity.atomVal 0 (Entity.funcApp (Entity.pairSecond p) x))
      else Entity.atom 0)

/-- `realFunSumFun A` is a set-theoretic function `𝒫_F(A) × 𝒫(A × ℝ) → ℝ`. -/
theorem isFuncFromTo_realFunSumFun (A : Entity ℝ) :
    Entity.IsFuncFromTo (realFunSumFun A)
      (Entity.prod (Entity.finPowerset A) (Entity.powerset (Entity.prod A realEntity)))
      realEntity := by
  classical
  refine Entity.isFuncFromTo_mkFuncEntity fun p hp ↦ ?_
  obtain ⟨Z, hZ, f, _, rfl⟩ := Entity.mem_prod_iff.1 hp
  obtain ⟨_, _, hfin⟩ := Entity.mem_finPowerset_iff.1 hZ
  simp only [Entity.pairFirst_kpair, hfin, ↓reduceDIte]
  exact mem_baseSet_iff.2 ⟨_, rfl⟩

/-- Evaluation of `realFunSumFun A` on `(Z, f)` for `Z ∈ 𝒫_F(A)` and `f ∈ 𝒫(A × ℝ)`. -/
theorem funcApp_realFunSumFun {A Z f : Entity ℝ}
    (hZ : Z ∈ Entity.finPowerset A) (hf : f ∈ Entity.powerset (Entity.prod A realEntity)) :
    Entity.funcApp (realFunSumFun A) (Entity.kpair Z f) =
      Entity.atom (open Classical in ∑ x ∈ (Entity.mem_finPowerset_iff.1 hZ).2.2.toFinset,
        Entity.atomVal 0 (Entity.funcApp f x)) := by
  classical
  obtain ⟨_, _, hfin⟩ := Entity.mem_finPowerset_iff.1 hZ
  have hp : Entity.kpair Z f ∈
      Entity.prod (Entity.finPowerset A) (Entity.powerset (Entity.prod A realEntity)) :=
    Entity.kpair_mem_prod_iff.2 ⟨hZ, hf⟩
  have hv := Entity.funcApp_mkFuncEntity (B := realEntity)
    (g := fun q ↦ if h : (Entity.pairFirst q).extSet.Finite then
      Entity.atom (∑ x ∈ h.toFinset, Entity.atomVal 0 (Entity.funcApp (Entity.pairSecond q) x))
      else Entity.atom 0)
    (fun q hq ↦ by
      obtain ⟨W, hW, _, _, rfl⟩ := Entity.mem_prod_iff.1 hq
      obtain ⟨_, _, hw⟩ := Entity.mem_finPowerset_iff.1 hW
      simp only [Entity.pairFirst_kpair, hw, ↓reduceDIte]; exact mem_baseSet_iff.2 ⟨_, rfl⟩) hp
  simpa [realFunSumFun, hfin] using hv

/-- Goldblatt §13.19 (pp. 180–181): **Hyperfinite Sum** `∑_{x ∈ B} f(x)` (`F.hyperSum B f`) of an
internal `*ℝ`-valued function `f` over a hyperfinite set `B`, defined via the transferred standard
summation operator `F.star (realFunSumFun A)` applied to `(B, f ∩ (B × *ℝ))` (and shown below to be
independent of the ambient standard set `A`). -/
def Framework.hyperSum {Y : Type*} (F : Framework ℝ Y) (B f : Entity Y) : Entity Y :=
  open Classical in
  if hB : F.IsHyperfiniteSet B then
    Entity.funcApp (F.star (realFunSumFun hB.choose))
      (Entity.kpair B (Entity.inter f (Entity.prod B (F.star realEntity))))
  else F.star (Entity.atom 0)

/-- Predicate `F.IsInternalRealFunOn f B` asserting that `f` is an internal function whose domain
includes `B` and which takes values in `*ℝ` on `B` (Goldblatt §13.19, p. 181). -/
def Framework.IsInternalRealFunOn {Y : Type*} (F : Framework ℝ Y) (f B : Entity Y) : Prop :=
  f.IsFuncEntity ∧ F.IsInternalEntity f ∧
    ∀ x ∈ B, x ∈ Entity.relDom f ∧ Entity.funcApp f x ∈ F.star realEntity

/-- Helper: restricting an internal `*ℝ`-valued function `f` on `B ∈ *𝒫_F(A)` to `B × *ℝ` produces
an internal function `fB ∈ *𝒫(A × ℝ)` agreeing with `f` on `B`. -/
theorem Framework.inter_prod_mem_star_powerset_and_eqOn {Y : Type*} (F : Framework ℝ Y)
    {A : Entity ℝ} {B f : Entity Y} (hBA : B ∈ F.star (Entity.finPowerset A))
    (hf : F.IsInternalRealFunOn f B) :
    let fB := Entity.inter f (Entity.prod B (F.star realEntity))
    fB ∈ F.star (Entity.powerset (Entity.prod A realEntity)) ∧
      fB.IsFuncEntity ∧
      ∀ x ∈ B, x ∈ Entity.relDom fB ∧ Entity.funcApp fB x = Entity.funcApp f x := by
  have hBsubA : ∀ x ∈ B, x ∈ F.star A :=
    (Entity.mem_powerset_iff.1 (F.mem_powerset_star_of_mem_star_powerset
      (F.mem_star_powerset_of_mem_star_finPowerset hBA))).2
  have hBint : F.IsInternalEntity B := (Framework.IsHyperfiniteSet.isInternalEntity ⟨A, hBA⟩)
  let fB := Entity.inter f (Entity.prod B (F.star realEntity))
  have hfB_int : F.IsInternalEntity fB :=
    F.isInternalEntity_inter hf.2.1
      (F.isInternalEntity_prod hBint (F.isStandard_star realEntity).isInternalEntity)
  have hfB_P : fB ∈ F.star (Entity.powerset (Entity.prod A realEntity)) := by
    rw [F.mem_star_powerset_iff, F.star_prod]
    refine ⟨Entity.mem_powerset_iff.2 ⟨Entity.isSet_inter _ _, fun p hp ↦ ?_⟩, hfB_int⟩
    obtain ⟨_, hp_prod⟩ := Entity.mem_inter_iff.1 hp
    obtain ⟨x, hxB, y, hyR, rfl⟩ := Entity.mem_prod_iff.1 hp_prod
    exact Entity.kpair_mem_prod_iff.2 ⟨hBsubA x hxB, hyR⟩
  have hfB_fn : fB.IsFuncEntity :=
    ⟨⟨Entity.isSet_inter _ _, fun p hp ↦ hf.1.1.2 p (Entity.mem_inter_iff.1 hp).1⟩,
      fun a b c h1 h2 ↦ hf.1.2 a b c (Entity.mem_inter_iff.1 h1).1 (Entity.mem_inter_iff.1 h2).1⟩
  refine ⟨hfB_P, hfB_fn, fun x hxB ↦ ?_⟩
  obtain ⟨hxdom, hfxR⟩ := hf.2.2 x hxB
  have hmem : Entity.kpair x (Entity.funcApp f x) ∈ fB :=
    Entity.mem_inter_iff.2 ⟨Entity.kpair_funcApp_mem hxdom,
      Entity.kpair_mem_prod_iff.2 ⟨hxB, hfxR⟩⟩
  exact ((Entity.kpair_mem_iff_funcApp_eq hfB_fn).1 hmem)

/-- Ambient-independence and extensionality of `F.hyperSum B f`: for ANY `A : Entity ℝ` with
`B ∈ F.star (Entity.finPowerset A)` and ANY `h ∈ F.star (Entity.powerset (Entity.prod A realEntity))`
that is functional and agrees with `f` on `B`,
`F.hyperSum B f = Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B h)`. -/
theorem Framework.hyperSum_eq_funcApp_of_mem_star_powerset {Y : Type*} (F : Framework ℝ Y)
    {A : Entity ℝ} {B f h : Entity Y}
    (hBA : B ∈ F.star (Entity.finPowerset A))
    (hf : F.IsInternalRealFunOn f B)
    (hhP : h ∈ F.star (Entity.powerset (Entity.prod A realEntity)))
    (hh_fn : h.IsFuncEntity)
    (hh_eq : ∀ x ∈ B, x ∈ Entity.relDom h ∧ Entity.funcApp h x = Entity.funcApp f x) :
    F.hyperSum B f = Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B h) := by
  classical
  have hB : F.IsHyperfiniteSet B := ⟨A, hBA⟩
  let A₀ := hB.choose
  have hBA₀ : B ∈ F.star (Entity.finPowerset A₀) := hB.choose_spec
  have hdef : F.hyperSum B f =
      Entity.funcApp (F.star (realFunSumFun A₀))
        (Entity.kpair B (Entity.inter f (Entity.prod B (F.star realEntity)))) := by
    simp [Framework.hyperSum, hB, A₀]
  rw [hdef]
  let fB := Entity.inter f (Entity.prod B (F.star realEntity))
  obtain ⟨hfB_P₀, hfB_fn, hfB_eq⟩ := F.inter_prod_mem_star_powerset_and_eqOn hBA₀ hf
  let D := Entity.union A₀ A
  have hBD : B ∈ F.star (Entity.finPowerset D) := by
    refine F.mem_star_finPowerset_of_isHyperfiniteSet_of_subset hB fun x hxB ↦ ?_
    have hxA : x ∈ F.star A :=
      (Entity.mem_powerset_iff.1 (F.mem_powerset_star_of_mem_star_powerset
        (F.mem_star_powerset_of_mem_star_finPowerset hBA))).2 x hxB
    rw [F.star_union]; exact Entity.mem_union_iff.2 (Or.inr hxA)
  -- Transfer: for `Z ∈ 𝒫_F(A₀) ∩ 𝒫_F(A)`, `g₁ ∈ 𝒫(A₀ × ℝ)`, `g₂ ∈ 𝒫(A × ℝ)`,
  -- if `∀ x ∈ Z, g₁(x) = g₂(x)` then `realFunSumFun A₀ (Z, g₁) = realFunSumFun A (Z, g₂)`!
  let φ : UFormula ℝ :=
    .forallIn 0 (.const (Entity.finPowerset D))
      (.forallIn 1 (.const (Entity.powerset (Entity.prod A₀ realEntity)))
        (.forallIn 2 (.const (Entity.powerset (Entity.prod A realEntity)))
          (.imp
            (.conj
              (.conj
                (.mem (.var 0) (.const (Entity.finPowerset A₀)))
                (.mem (.var 0) (.const (Entity.finPowerset A))))
              (.forallIn 3 (.var 0) (.eq (.app (.var 1) (.var 3)) (.app (.var 2) (.var 3)))))
            (.eq (.app (.const (realFunSumFun A₀)) (UTerm.pair (.var 0) (.var 1)))
                 (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 2)))))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm_pair, freeVarsUTerm]; tauto
  have hstd : SentenceHolds φ := by
    refine ⟨_, rfl, fun Z _ ↦ ⟨_, rfl, fun g₁ hg₁ ↦ ⟨_, rfl, fun g₂ hg₂ ⟨⟨⟨_, _, hZA₀_m⟩, ⟨_, _, hZA_m⟩⟩, _, hZ0, heq_on⟩ ↦ ?_⟩⟩⟩
    obtain rfl := Option.some.inj (by simpa using hZ0)
    have hZA₀ : Z ∈ Entity.finPowerset A₀ := by
      rcases hZA₀_m with ⟨h1, h2, h3⟩
      have he1 : Z = _ := Option.some.inj (by simpa using h1)
      have he2 : Entity.finPowerset A₀ = _ := Option.some.inj h2
      exact he1 ▸ he2 ▸ h3
    have hZA : Z ∈ Entity.finPowerset A := by
      rcases hZA_m with ⟨h1, h2, h3⟩
      have he1 : Z = _ := Option.some.inj (by simpa using h1)
      have he2 : Entity.finPowerset A = _ := Option.some.inj h2
      exact he1 ▸ he2 ▸ h3
    have hsum_eq : Entity.funcApp (realFunSumFun A₀) (Entity.kpair Z g₁) =
        Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₂) := by
      rw [funcApp_realFunSumFun hZA₀ hg₁, funcApp_realFunSumFun hZA hg₂]
      congr 1
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      have hxZ : x ∈ Z := (Set.Finite.mem_toFinset (Entity.mem_finPowerset_iff.1 hZA₀).2.2).1 hx
      obtain ⟨y, hy1, hy2⟩ := heq_on x hxZ
      obtain ⟨g₁', x₁, hg₁', hx₁, _, _, hv1⟩ := evalUTerm_app_eq_some_iff.1 hy1
      obtain ⟨g₂', x₂, hg₂', hx₂, _, _, hv2⟩ := evalUTerm_app_eq_some_iff.1 hy2
      have e1 : g₁ = g₁' := Option.some.inj (by simpa using hg₁')
      have e2 : x = x₁ := Option.some.inj (by simpa using hx₁)
      have e3 : g₂ = g₂' := Option.some.inj (by simpa using hg₂')
      have e4 : x = x₂ := Option.some.inj (by simpa using hx₂)
      subst e1; subst e2; subst e3; subst e4
      rw [hv1, hv2]
    have hd1 : Entity.kpair Z g₁ ∈ Entity.relDom (realFunSumFun A₀) := by
      rw [(isFuncFromTo_realFunSumFun A₀).relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hZA₀, hg₁⟩
    have hd2 : Entity.kpair Z g₂ ∈ Entity.relDom (realFunSumFun A) := by
      rw [(isFuncFromTo_realFunSumFun A).relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hZA, hg₂⟩
    let env₃ := Function.update (Function.update
      (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0 Z) 1 g₁) 2 g₂
    have hev1 : evalUTerm env₃ (.app (.const (realFunSumFun A₀)) (UTerm.pair (.var 0) (.var 1))) =
        some (Entity.funcApp (realFunSumFun A₀) (Entity.kpair Z g₁)) :=
      evalUTerm_app_eq_some_iff.2 ⟨_, Entity.kpair Z g₁, rfl,
        by simp [env₃, evalUTerm_pair], (isFuncFromTo_realFunSumFun A₀).isFuncEntity, hd1, rfl⟩
    have hev2 : evalUTerm env₃ (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 2))) =
        some (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₂)) :=
      evalUTerm_app_eq_some_iff.2 ⟨_, Entity.kpair Z g₂, rfl,
        by simp [env₃, evalUTerm_pair], (isFuncFromTo_realFunSumFun A).isFuncEntity, hd2, rfl⟩
    dsimp only [env₃] at hev1 hev2
    exact ⟨_, hev1, hsum_eq ▸ hev2⟩
  obtain ⟨_, hFD, hallZ⟩ := (F.transfer φ hsent).1 hstd; obtain rfl := Option.some.inj hFD
  obtain ⟨_, hP0, hall1⟩ := hallZ B hBD; obtain rfl := Option.some.inj hP0
  obtain ⟨_, hPA, hall2⟩ := hall1 fB hfB_P₀; obtain rfl := Option.some.inj hPA
  obtain ⟨q, hq1, hq2⟩ := hall2 h hhP ⟨⟨
    ⟨B, _, by simp, rfl, hBA₀⟩,
    ⟨B, _, by simp, rfl, hBA⟩⟩,
    ⟨B, by simp, fun x hxB ↦ by
      obtain ⟨hd_fB, hv_fB⟩ := hfB_eq x hxB
      obtain ⟨hd_h, hv_h⟩ := hh_eq x hxB
      refine ⟨Entity.funcApp f x, ?_, ?_⟩
      · rw [starTerm, evalUTerm_app_eq_some_iff]
        exact ⟨fB, x, by simp, by simp, hfB_fn, hd_fB, hv_fB⟩
      · rw [starTerm, evalUTerm_app_eq_some_iff]
        exact ⟨h, x, by simp, by simp, hh_fn, hd_h, hv_h⟩⟩⟩
  have hf1 := (F.isFuncFromTo_star_iff).2 (isFuncFromTo_realFunSumFun A₀)
  have hf2 := (F.isFuncFromTo_star_iff).2 (isFuncFromTo_realFunSumFun A)
  have hdY1 : Entity.kpair B fB ∈ Entity.relDom (F.star (realFunSumFun A₀)) := by
    rw [hf1.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hBA₀, hfB_P₀⟩
  have hdY2 : Entity.kpair B h ∈ Entity.relDom (F.star (realFunSumFun A)) := by
    rw [hf2.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hBA, hhP⟩
  let envY := Function.update (Function.update
    (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 B) 1 fB) 2 h
  have hevY1 : evalUTerm envY
      (starTerm F.star (.app (.const (realFunSumFun A₀)) (UTerm.pair (.var 0) (.var 1)))) =
      some (Entity.funcApp (F.star (realFunSumFun A₀)) (Entity.kpair B fB)) := by
    simp only [starTerm]; rw [evalUTerm_app_eq_some_iff]
    exact ⟨_, Entity.kpair B fB, rfl, by simp [envY, starTerm_pair, evalUTerm_pair],
      hf1.isFuncEntity, hdY1, rfl⟩
  have hevY2 : evalUTerm envY
      (starTerm F.star (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 2)))) =
      some (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B h)) := by
    simp only [starTerm]; rw [evalUTerm_app_eq_some_iff]
    exact ⟨_, Entity.kpair B h, rfl, by simp [envY, starTerm_pair, evalUTerm_pair],
      hf2.isFuncEntity, hdY2, rfl⟩
  dsimp only [envY] at hevY1 hevY2
  exact (Option.some.inj (hevY1.symm.trans hq1)).trans (Option.some.inj (hevY2.symm.trans hq2)).symm

/-- Every hyperfinite sum `F.hyperSum B f` of an internal `*ℝ`-valued function `f` over a
hyperfinite set `B` belongs to `F.star realEntity` (`*ℝ`; Goldblatt §13.19, p. 181). -/
theorem Framework.hyperSum_mem_star_realEntity {Y : Type*} (F : Framework ℝ Y)
    {B f : Entity Y} (hB : F.IsHyperfiniteSet B) (hf : F.IsInternalRealFunOn f B) :
    F.hyperSum B f ∈ F.star realEntity := by
  obtain ⟨A, hBA⟩ := hB
  obtain ⟨hfB_P, hfB_fn, hfB_eq⟩ := F.inter_prod_mem_star_powerset_and_eqOn hBA hf
  rw [F.hyperSum_eq_funcApp_of_mem_star_powerset hBA hf hfB_P hfB_fn hfB_eq]
  have hfs := (F.isFuncFromTo_star_iff).2 (isFuncFromTo_realFunSumFun A)
  have hdom : Entity.kpair B (Entity.inter f (Entity.prod B (F.star realEntity))) ∈
      Entity.relDom (F.star (realFunSumFun A)) := by
    rw [hfs.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hBA, hfB_P⟩
  exact hfs.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hdom⟩)

/-- Goldblatt §13.19 (p. 181): When `f` is injective on `B`, the indexed hyperfinite sum
`F.hyperSum B f` (`∑_{x ∈ B} f(x)`) agrees with the hyperfinite set sum
`F.hyperSetSum (Entity.relImage f B)` (`Σ f(B)`). -/
theorem Framework.hyperSum_eq_hyperSetSum_relImage_of_injOn {Y : Type*} (F : Framework ℝ Y)
    {B f : Entity Y} (hB : F.IsHyperfiniteSet B) (hf : F.IsInternalRealFunOn f B)
    (hinj : ∀ x₁ ∈ B, ∀ x₂ ∈ B, Entity.funcApp f x₁ = Entity.funcApp f x₂ → x₁ = x₂) :
    F.hyperSum B f = F.hyperSetSum (Entity.relImage f B) := by
  obtain ⟨A, hBA⟩ := hB
  let fB := Entity.inter f (Entity.prod B (F.star realEntity))
  obtain ⟨hfB_P, hfB_fn, hfB_eq⟩ := F.inter_prod_mem_star_powerset_and_eqOn hBA hf
  rw [F.hyperSum_eq_funcApp_of_mem_star_powerset hBA hf hfB_P hfB_fn hfB_eq]
  have himg_sub : ∀ y ∈ Entity.relImage f B, y ∈ F.star realEntity := by
    intro y hy
    obtain ⟨x, hxB, hxy⟩ := Entity.mem_relImage_iff.1 hy
    have heq := ((Entity.kpair_mem_iff_funcApp_eq hf.1).1 hxy).2
    exact heq ▸ (hf.2.2 x hxB).2
  have himg_F : Entity.relImage f B ∈ F.star (Entity.finPowerset realEntity) :=
    F.mem_star_finPowerset_of_isHyperfiniteSet_of_subset
      (F.isHyperfiniteSet_relImage hf.1 hf.2.1 ⟨A, hBA⟩) himg_sub
  let φ : UFormula ℝ :=
    .forallIn 0 (.const (Entity.finPowerset A))
      (.forallIn 1 (.const (Entity.powerset (Entity.prod A realEntity)))
        (.forallIn 2 (.const (Entity.finPowerset realEntity))
          (.imp
            (.conj
              (.conj
                (.forallIn 3 (.var 2)
                  (.existsIn 4 (.var 0) (.eq (.var 3) (.app (.var 1) (.var 4)))))
                (.forallIn 4 (.var 0) (.mem (.app (.var 1) (.var 4)) (.var 2))))
              (.forallIn 4 (.var 0)
                (.forallIn 5 (.var 0)
                  (.imp (.eq (.app (.var 1) (.var 4)) (.app (.var 1) (.var 5)))
                        (.eq (.var 4) (.var 5))))))
            (.eq (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 1)))
                 (.app (.const realSetSumFun) (.var 2))))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm_pair, freeVarsUTerm]; tauto
  have hstd : SentenceHolds φ := by
    refine ⟨_, rfl, fun Z hZ ↦ ⟨_, rfl, fun g hg ↦ ⟨_, rfl, fun W hW ⟨⟨⟨_, hW0, hsurj⟩, ⟨_, hZ0, hinto⟩⟩, ⟨_, hZ1, hinjZ⟩⟩ ↦ ?_⟩⟩⟩
    obtain rfl := Option.some.inj (by simpa using hW0)
    obtain rfl := Option.some.inj (by simpa using hZ0)
    obtain rfl := Option.some.inj (by simpa using hZ1)
    classical
    obtain ⟨_, _, hZfin⟩ := Entity.mem_finPowerset_iff.1 hZ
    obtain ⟨_, _, hWfin⟩ := Entity.mem_finPowerset_iff.1 hW
    have hW_eq_img : hWfin.toFinset = hZfin.toFinset.image (Entity.funcApp g) := by
      ext y
      rw [Set.Finite.mem_toFinset, Finset.mem_image]
      constructor
      · intro hyW
        obtain ⟨_, hZ', x, hxZ, q, hq1, hq2⟩ := hsurj y hyW
        have hZeq : Z = _ := Option.some.inj (by simpa using hZ')
        obtain ⟨g', x', hg', hx', _, _, hv⟩ := evalUTerm_app_eq_some_iff.1 hq2
        have ey : y = q := Option.some.inj (by simpa using hq1)
        have eg : g = g' := Option.some.inj (by simpa using hg')
        have ex : x = x' := Option.some.inj (by simpa using hx')
        exact ⟨x, (Set.Finite.mem_toFinset hZfin).2 (hZeq ▸ hxZ), (ey.trans (eg ▸ ex ▸ hv).symm).symm⟩
      · rintro ⟨x, hxF, rfl⟩
        have hxZ := (Set.Finite.mem_toFinset hZfin).1 hxF
        obtain ⟨y', W', hy', hW', hm⟩ := hinto x hxZ
        obtain ⟨g', x', hg', hx', _, _, hv⟩ := evalUTerm_app_eq_some_iff.1 hy'
        have eg : g = g' := Option.some.inj (by simpa using hg')
        have ex : x = x' := Option.some.inj (by simpa using hx')
        have eW : W = W' := Option.some.inj (by simpa using hW')
        have ey : Entity.funcApp g x = y' := eg ▸ ex ▸ hv
        exact ey ▸ eW ▸ hm
    have hinj_on : Set.InjOn (Entity.funcApp g) (hZfin.toFinset : Set (Entity ℝ)) := by
      intro x₁ hx₁ x₂ hx₂ heq
      have hx₁Z := (Set.Finite.mem_toFinset hZfin).1 hx₁
      have hx₂Z := (Set.Finite.mem_toFinset hZfin).1 hx₂
      obtain ⟨_, hZ2, hall2⟩ := hinjZ x₁ hx₁Z
      have eZ2 : Z = _ := Option.some.inj (by simpa using hZ2)
      obtain ⟨y₁, W₁, hy₁, _, _⟩ := hinto x₁ hx₁Z
      obtain ⟨g₁, a₁, hg₁, ha₁, hfn₁, hdom₁, _⟩ := evalUTerm_app_eq_some_iff.1 hy₁
      have eg₁ : g = g₁ := Option.some.inj (by simpa using hg₁)
      have ea₁ : x₁ = a₁ := Option.some.inj (by simpa using ha₁)
      obtain ⟨y₂, W₂, hy₂, _, _⟩ := hinto x₂ hx₂Z
      obtain ⟨g₂, a₂, hg₂, ha₂, _, hdom₂, _⟩ := evalUTerm_app_eq_some_iff.1 hy₂
      have eg₂ : g = g₂ := Option.some.inj (by simpa using hg₂)
      have ea₂ : x₂ = a₂ := Option.some.inj (by simpa using ha₂)
      obtain ⟨q, hq1, hq2⟩ := hall2 x₂ (eZ2 ▸ hx₂Z) ⟨Entity.funcApp g x₁,
        evalUTerm_app_eq_some_iff.2 ⟨g, x₁, by simp, by simp, eg₁ ▸ hfn₁, eg₁ ▸ ea₁ ▸ hdom₁, rfl⟩,
        evalUTerm_app_eq_some_iff.2 ⟨g, x₂, by simp, by simp, eg₁ ▸ hfn₁, eg₂ ▸ ea₂ ▸ hdom₂, heq.symm⟩⟩
      exact (Option.some.inj (by simpa using hq1)).trans (Option.some.inj (by simpa using hq2)).symm
    have hsum_eq : Entity.funcApp (realFunSumFun A) (Entity.kpair Z g) =
        Entity.funcApp realSetSumFun W := by
      rw [funcApp_realFunSumFun hZ hg, funcApp_realSetSumFun hW]
      exact congrArg Entity.atom ((Finset.sum_image hinj_on).symm.trans
        (by rw [← hW_eq_img]))
    have hd1 : Entity.kpair Z g ∈ Entity.relDom (realFunSumFun A) := by
      rw [(isFuncFromTo_realFunSumFun A).relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hZ, hg⟩
    have hd2 : W ∈ Entity.relDom realSetSumFun := by
      rw [isFuncFromTo_realSetSumFun.relDom_eq (Entity.isSet_finPowerset _)]; exact hW
    let env₃ := Function.update (Function.update
      (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0 Z) 1 g) 2 W
    have hev1 : evalUTerm env₃ (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 1))) =
        some (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g)) :=
      evalUTerm_app_eq_some_iff.2 ⟨_, Entity.kpair Z g, rfl, by simp [env₃, evalUTerm_pair],
        (isFuncFromTo_realFunSumFun A).isFuncEntity, hd1, rfl⟩
    have hev2 : evalUTerm env₃ (.app (.const realSetSumFun) (.var 2)) =
        some (Entity.funcApp realSetSumFun W) :=
      evalUTerm_app_eq_some_iff.2 ⟨_, W, rfl, by simp [env₃],
        isFuncFromTo_realSetSumFun.isFuncEntity, hd2, rfl⟩
    dsimp only [env₃] at hev1 hev2
    exact ⟨_, hev1, hsum_eq ▸ hev2⟩
  obtain ⟨_, hFA, hall0⟩ := (F.transfer φ hsent).1 hstd; obtain rfl := Option.some.inj hFA
  obtain ⟨_, hPA, hall1⟩ := hall0 B hBA; obtain rfl := Option.some.inj hPA
  obtain ⟨_, hFR, hall2⟩ := hall1 fB hfB_P; obtain rfl := Option.some.inj hFR
  let W := Entity.relImage f B
  obtain ⟨q, hq1, hq2⟩ := hall2 W himg_F ⟨⟨
    ⟨W, by simp, fun y hyW ↦ by
      obtain ⟨x, hxB, hxy⟩ := Entity.mem_relImage_iff.1 hyW
      have hy_eq := ((Entity.kpair_mem_iff_funcApp_eq hf.1).1 hxy).2
      obtain ⟨hd_fB, hv_fB⟩ := hfB_eq x hxB
      refine ⟨B, by simp, x, hxB, y, by simp, ?_⟩
      rw [starTerm, evalUTerm_app_eq_some_iff]
      exact ⟨fB, x, by simp, by simp, hfB_fn, hd_fB, hv_fB.trans hy_eq⟩⟩,
    ⟨B, by simp, fun x hxB ↦ by
      obtain ⟨hd_fB, hv_fB⟩ := hfB_eq x hxB
      have hmemW : Entity.funcApp f x ∈ W :=
        Entity.mem_relImage_iff.2 ⟨x, hxB, Entity.kpair_funcApp_mem (hf.2.2 x hxB).1⟩
      refine ⟨Entity.funcApp f x, W, ?_, by simp, hmemW⟩
      rw [starTerm, evalUTerm_app_eq_some_iff]
      exact ⟨fB, x, by simp, by simp, hfB_fn, hd_fB, hv_fB⟩⟩⟩,
    ⟨B, by simp, fun x₁ hx₁ ↦ ⟨B, by simp, fun x₂ hx₂ ⟨y, hy1, hy2⟩ ↦ by
      obtain ⟨g₁, a₁, hg₁, ha₁, _, _, hv1⟩ := evalUTerm_app_eq_some_iff.1 (by simpa [starTerm] using hy1)
      obtain ⟨g₂, a₂, hg₂, ha₂, _, _, hv2⟩ := evalUTerm_app_eq_some_iff.1 (by simpa [starTerm] using hy2)
      have eg₁ : fB = g₁ := Option.some.inj (by simpa using hg₁)
      have ea₁ : x₁ = a₁ := Option.some.inj (by simpa using ha₁)
      have eg₂ : fB = g₂ := Option.some.inj (by simpa using hg₂)
      have ea₂ : x₂ = a₂ := Option.some.inj (by simpa using ha₂)
      have heq_f : Entity.funcApp f x₁ = Entity.funcApp f x₂ :=
        (hfB_eq x₁ hx₁).2.symm.trans ((eg₁ ▸ ea₁ ▸ hv1).trans ((eg₂ ▸ ea₂ ▸ hv2).symm.trans (hfB_eq x₂ hx₂).2))
      exact ⟨x₁, by simp, by simp [hinj x₁ hx₁ x₂ hx₂ heq_f]⟩⟩⟩⟩
  have hf1 := (F.isFuncFromTo_star_iff).2 (isFuncFromTo_realFunSumFun A)
  have hf2 := (F.isFuncFromTo_star_iff).2 isFuncFromTo_realSetSumFun
  have hdY1 : Entity.kpair B fB ∈ Entity.relDom (F.star (realFunSumFun A)) := by
    rw [hf1.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hBA, hfB_P⟩
  have hdY2 : W ∈ Entity.relDom (F.star realSetSumFun) := by
    rw [hf2.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_finPowerset _))]; exact himg_F
  let envY := Function.update (Function.update
    (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 B) 1 fB) 2 W
  have hevY1 : evalUTerm envY
      (starTerm F.star (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 1)))) =
      some (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B fB)) := by
    simp only [starTerm]; rw [evalUTerm_app_eq_some_iff]
    exact ⟨_, Entity.kpair B fB, rfl, by simp [envY, starTerm_pair, evalUTerm_pair],
      hf1.isFuncEntity, hdY1, rfl⟩
  have hevY2 : evalUTerm envY (starTerm F.star (.app (.const realSetSumFun) (.var 2))) =
      some (F.hyperSetSum W) := by
    simp only [starTerm]; rw [evalUTerm_app_eq_some_iff]
    exact ⟨_, W, rfl, by simp [envY], hf2.isFuncEntity, hdY2, rfl⟩
  dsimp only [envY] at hevY1 hevY2
  exact (Option.some.inj (hevY1.symm.trans hq1)).trans (Option.some.inj (hevY2.symm.trans hq2)).symm

/-- Pointwise scalar multiple `x ↦ c * f(x)` on a set `B`, constructed via `Entity.mkFuncEntity`
and shown internal below by the **Internal Function Definition Principle** (§13.16;
Goldblatt §13.20, Exercise 1, p. 181). -/
def Framework.internalSmulOn {Y : Type*} (F : Framework ℝ Y) (B c f : Entity Y) : Entity Y :=
  Entity.mkFuncEntity B (fun x ↦ F.starMul c (Entity.funcApp f x))

/-- By the **Internal Function Definition Principle** (§13.16), if `B` is an internal set,
`c ∈ F.star realEntity`, and `F.IsInternalRealFunOn f B`, then `F.internalSmulOn B c f` satisfies
`F.IsInternalRealFunOn (F.internalSmulOn B c f) B` with `(internalSmulOn B c f)(x) = c * f(x)`. -/
theorem Framework.isInternalRealFunOn_internalSmulOn {Y : Type*} (F : Framework ℝ Y)
    {B c f : Entity Y} (hBs : B.IsSet) (hBint : F.IsInternalEntity B)
    (hc : c ∈ F.star realEntity) (hf : F.IsInternalRealFunOn f B) :
    F.IsInternalRealFunOn (F.internalSmulOn B c f) B ∧
      ∀ x ∈ B, Entity.funcApp (F.internalSmulOn B c f) x = F.starMul c (Entity.funcApp f x) := by
  have hgR : ∀ x ∈ B, F.starMul c (Entity.funcApp f x) ∈ F.star realEntity :=
    fun x hx ↦ F.starMul_mem hc (hf.2.2 x hx).2
  have hfn : Entity.IsFuncFromTo (F.internalSmulOn B c f) B (F.star realEntity) :=
    Entity.isFuncFromTo_mkFuncEntity hgR
  have happ : ∀ x ∈ B, Entity.funcApp (F.internalSmulOn B c f) x =
      F.starMul c (Entity.funcApp f x) :=
    fun x hx ↦ Entity.funcApp_mkFuncEntity hgR hx
  let τ : UTerm Y :=
    .app (.const (F.star realMulFun)) (UTerm.pair (.const c) (.app (.const f) (.var 0)))
  have hc_int : F.IsInternalEntity c := ⟨realEntity, hc⟩
  have hmul_int : F.IsInternalEntity (F.star realMulFun) := (F.isStandard_star _).isInternalEntity
  have hFR_int : F.IsInternalEntity (F.star realEntity) := (F.isStandard_star _).isInternalEntity
  have h_int : F.IsInternalEntity (F.internalSmulOn B c f) := by
    refine F.internal_function_definition_principle hBs hBint hFR_int hfn 0 (τ := τ)
      (fun v hv ↦ by simp [τ, freeVarsUTerm_pair, freeVarsUTerm] at hv; exact hv)
      ?_ (fun x hxB ↦ ?_)
    · intro d hd
      simp only [τ, UTerm.pair, constsUTerm, List.mem_append, List.mem_singleton,
        List.mem_flatMap, List.mem_finRange, true_and] at hd
      rcases hd with rfl | ⟨⟨i, hi⟩, hdi⟩
      · exact hmul_int
      · interval_cases i
        · simp [constsUTerm] at hdi; exact hdi ▸ hc_int
        · simp [constsUTerm] at hdi; exact hdi ▸ hf.2.1
    · have hf_mul := (F.isFuncFromTo_star_iff).2 isFuncFromTo_realMulFun
      have hd_mul : Entity.kpair c (Entity.funcApp f x) ∈ Entity.relDom (F.star realMulFun) := by
        rw [hf_mul.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
        exact Entity.kpair_mem_prod_iff.2 ⟨hc, (hf.2.2 x hxB).2⟩
      rw [happ x hxB, evalUTerm_app_eq_some_iff]
      refine ⟨F.star realMulFun, Entity.kpair c (Entity.funcApp f x), rfl, ?_,
        hf_mul.isFuncEntity, hd_mul, rfl⟩
      rw [evalUTerm_pair]
      have hevf : evalUTerm (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 x)
          (.app (.const f) (.var 0)) = some (Entity.funcApp f x) :=
        evalUTerm_app_eq_some_iff.2 ⟨f, x, rfl, by simp, hf.1, (hf.2.2 x hxB).1, rfl⟩
      simp [hevf]
  refine ⟨⟨hfn.isFuncEntity, h_int, fun x hxB ↦ ⟨?_, (happ x hxB).symm ▸ hgR x hxB⟩⟩, happ⟩
  rw [hfn.relDom_eq hBs]; exact hxB

/-- Pointwise sum `x ↦ f(x) + g(x)` on a set `B`, constructed via `Entity.mkFuncEntity`
and shown internal below by the **Internal Function Definition Principle** (§13.16;
Goldblatt §13.20, Exercise 1, p. 181). -/
def Framework.internalAddOn {Y : Type*} (F : Framework ℝ Y) (B f g : Entity Y) : Entity Y :=
  Entity.mkFuncEntity B (fun x ↦ F.starAdd (Entity.funcApp f x) (Entity.funcApp g x))

/-- By the **Internal Function Definition Principle** (§13.16), if `B` is an internal set and
`F.IsInternalRealFunOn f B`, `F.IsInternalRealFunOn g B`, then `F.internalAddOn B f g` satisfies
`F.IsInternalRealFunOn (F.internalAddOn B f g) B` with `(internalAddOn B f g)(x) = f(x) + g(x)`. -/
theorem Framework.isInternalRealFunOn_internalAddOn {Y : Type*} (F : Framework ℝ Y)
    {B f g : Entity Y} (hBs : B.IsSet) (hBint : F.IsInternalEntity B)
    (hf : F.IsInternalRealFunOn f B) (hg : F.IsInternalRealFunOn g B) :
    F.IsInternalRealFunOn (F.internalAddOn B f g) B ∧
      ∀ x ∈ B, Entity.funcApp (F.internalAddOn B f g) x =
        F.starAdd (Entity.funcApp f x) (Entity.funcApp g x) := by
  have hgR : ∀ x ∈ B, F.starAdd (Entity.funcApp f x) (Entity.funcApp g x) ∈ F.star realEntity :=
    fun x hx ↦ F.starAdd_mem (hf.2.2 x hx).2 (hg.2.2 x hx).2
  have hfn : Entity.IsFuncFromTo (F.internalAddOn B f g) B (F.star realEntity) :=
    Entity.isFuncFromTo_mkFuncEntity hgR
  have happ : ∀ x ∈ B, Entity.funcApp (F.internalAddOn B f g) x =
      F.starAdd (Entity.funcApp f x) (Entity.funcApp g x) :=
    fun x hx ↦ Entity.funcApp_mkFuncEntity hgR hx
  let τ : UTerm Y :=
    .app (.const (F.star realAddFun))
      (UTerm.pair (.app (.const f) (.var 0)) (.app (.const g) (.var 0)))
  have hadd_int : F.IsInternalEntity (F.star realAddFun) := (F.isStandard_star _).isInternalEntity
  have hFR_int : F.IsInternalEntity (F.star realEntity) := (F.isStandard_star _).isInternalEntity
  have h_int : F.IsInternalEntity (F.internalAddOn B f g) := by
    refine F.internal_function_definition_principle hBs hBint hFR_int hfn 0 (τ := τ)
      (fun v hv ↦ by simp [τ, freeVarsUTerm_pair, freeVarsUTerm] at hv; omega)
      ?_ (fun x hxB ↦ ?_)
    · intro d hd
      simp only [τ, UTerm.pair, constsUTerm, List.mem_append, List.mem_singleton,
        List.mem_flatMap, List.mem_finRange, true_and] at hd
      rcases hd with rfl | ⟨⟨i, hi⟩, hdi⟩
      · exact hadd_int
      · interval_cases i
        · simp [constsUTerm] at hdi; exact hdi ▸ hf.2.1
        · simp [constsUTerm] at hdi; exact hdi ▸ hg.2.1
    · have hf_add := (F.isFuncFromTo_star_iff).2 isFuncFromTo_realAddFun
      have hd_add : Entity.kpair (Entity.funcApp f x) (Entity.funcApp g x) ∈
          Entity.relDom (F.star realAddFun) := by
        rw [hf_add.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
        exact Entity.kpair_mem_prod_iff.2 ⟨(hf.2.2 x hxB).2, (hg.2.2 x hxB).2⟩
      rw [happ x hxB, evalUTerm_app_eq_some_iff]
      refine ⟨F.star realAddFun, Entity.kpair (Entity.funcApp f x) (Entity.funcApp g x), rfl, ?_,
        hf_add.isFuncEntity, hd_add, rfl⟩
      rw [evalUTerm_pair]
      have hevf : evalUTerm (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 x)
          (.app (.const f) (.var 0)) = some (Entity.funcApp f x) :=
        evalUTerm_app_eq_some_iff.2 ⟨f, x, rfl, by simp, hf.1, (hf.2.2 x hxB).1, rfl⟩
      have hevg : evalUTerm (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 x)
          (.app (.const g) (.var 0)) = some (Entity.funcApp g x) :=
        evalUTerm_app_eq_some_iff.2 ⟨g, x, rfl, by simp, hg.1, (hg.2.2 x hxB).1, rfl⟩
      simp [hevf, hevg]
  refine ⟨⟨hfn.isFuncEntity, h_int, fun x hxB ↦ ⟨?_, (happ x hxB).symm ▸ hgR x hxB⟩⟩, happ⟩
  rw [hfn.relDom_eq hBs]; exact hxB

/-- Goldblatt **Exercise 13.20(1), Property 1 (Scalar Linearity)** (p. 181):
`∑_{x ∈ B} c f(x) = c (∑_{x ∈ B} f(x))` for any hyperfinite set `B`, `c ∈ *ℝ`, and internal
`*ℝ`-valued functions `f, cf` on `B` with `cf(x) = c * f(x)` on `B`. -/
theorem Framework.hyperSum_smul {Y : Type*} (F : Framework ℝ Y)
    {B c f cf : Entity Y} (hB : F.IsHyperfiniteSet B) (hc : c ∈ F.star realEntity)
    (hf : F.IsInternalRealFunOn f B) (hcf : F.IsInternalRealFunOn cf B)
    (heq : ∀ x ∈ B, Entity.funcApp cf x = F.starMul c (Entity.funcApp f x)) :
    F.hyperSum B cf = F.starMul c (F.hyperSum B f) := by
  obtain ⟨A, hBA⟩ := hB
  let fB := Entity.inter f (Entity.prod B (F.star realEntity))
  let cfB := Entity.inter cf (Entity.prod B (F.star realEntity))
  obtain ⟨hfB_P, hfB_fn, hfB_eq⟩ := F.inter_prod_mem_star_powerset_and_eqOn hBA hf
  obtain ⟨hcfB_P, hcfB_fn, hcfB_eq⟩ := F.inter_prod_mem_star_powerset_and_eqOn hBA hcf
  rw [F.hyperSum_eq_funcApp_of_mem_star_powerset hBA hcf hcfB_P hcfB_fn hcfB_eq,
      F.hyperSum_eq_funcApp_of_mem_star_powerset hBA hf hfB_P hfB_fn hfB_eq]
  let φ : UFormula ℝ :=
    .forallIn 0 (.const (Entity.finPowerset A))
      (.forallIn 1 (.const realEntity)
        (.forallIn 2 (.const (Entity.powerset (Entity.prod A realEntity)))
          (.forallIn 3 (.const (Entity.powerset (Entity.prod A realEntity)))
            (.imp
              (.forallIn 4 (.var 0)
                (.eq (.app (.var 3) (.var 4))
                     (.app (.const realMulFun) (UTerm.pair (.var 1) (.app (.var 2) (.var 4))))))
              (.eq (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 3)))
                   (.app (.const realMulFun)
                     (UTerm.pair (.var 1)
                       (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 2))))))))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm_pair, freeVarsUTerm]; tauto
  have hstd : SentenceHolds φ := by
    refine ⟨_, rfl, fun Z hZ ↦ ⟨_, rfl, fun ec hec ↦ ⟨_, rfl, fun g₁ hg₁ ↦ ⟨_, rfl, fun g₂ hg₂ ⟨_, hZ0, hpt⟩ ↦ ?_⟩⟩⟩⟩
    obtain rfl := Option.some.inj (by simpa using hZ0)
    obtain ⟨rc, rfl⟩ := mem_baseSet_iff.1 hec
    have hsum_eq : Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₂) =
        Entity.funcApp realMulFun
          (Entity.kpair (Entity.atom rc) (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₁))) := by
      rw [funcApp_realFunSumFun hZ hg₂, funcApp_realFunSumFun hZ hg₁, funcApp_realMulFun]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      have hxZ : x ∈ Z := (Set.Finite.mem_toFinset (Entity.mem_finPowerset_iff.1 hZ).2.2).1 hx
      obtain ⟨y, hy1, hy2⟩ := hpt x hxZ
      obtain ⟨g₂', x₂, hg₂', hx₂, _, _, hv₂⟩ := evalUTerm_app_eq_some_iff.1 hy1
      have eg₂ : g₂ = g₂' := Option.some.inj (by simpa using hg₂')
      have ex₂ : x = x₂ := Option.some.inj (by simpa using hx₂)
      subst eg₂; subst ex₂
      obtain ⟨mF, pq, hmF, hpq, _, hdom_m, hvm⟩ := evalUTerm_app_eq_some_iff.1 hy2
      obtain rfl := Option.some.inj hmF
      obtain ⟨c', v₁, hc_ev, hg1_ev, rfl⟩ := evalUTerm_pair_eq_some_iff.1 hpq
      have ec' : Entity.atom rc = c' := Option.some.inj (by simpa using hc_ev)
      obtain ⟨g₁', x₁, hg₁', hx₁, _, _, hv₁⟩ := evalUTerm_app_eq_some_iff.1 hg1_ev
      have eg₁ : g₁ = g₁' := Option.some.inj (by simpa using hg₁')
      have ex₁ : x = x₁ := Option.some.inj (by simpa using hx₁)
      subst ec'; subst eg₁; subst ex₁; subst hv₁; subst hv₂
      rw [isFuncFromTo_realMulFun.relDom_eq (Entity.isSet_prod _ _)] at hdom_m
      obtain ⟨_, hv₁R⟩ := Entity.kpair_mem_prod_iff.1 hdom_m
      obtain ⟨rv, hrv⟩ := mem_baseSet_iff.1 hv₁R
      rw [← hvm, hrv, funcApp_realMulFun, Entity.atomVal_atom, Entity.atomVal_atom]
    have hd1 : Entity.kpair Z g₁ ∈ Entity.relDom (realFunSumFun A) := by
      rw [(isFuncFromTo_realFunSumFun A).relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hZ, hg₁⟩
    have hd2 : Entity.kpair Z g₂ ∈ Entity.relDom (realFunSumFun A) := by
      rw [(isFuncFromTo_realFunSumFun A).relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hZ, hg₂⟩
    have hs1R : Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₁) ∈ realEntity :=
      (isFuncFromTo_realFunSumFun A).mem_of_mem_relRan
        (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hd1⟩)
    have hdm : Entity.kpair (Entity.atom rc) (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₁)) ∈
        Entity.relDom realMulFun := by
      rw [isFuncFromTo_realMulFun.relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hec, hs1R⟩
    let env₄ := Function.update (Function.update (Function.update
      (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0 Z) 1 (Entity.atom rc)) 2 g₁) 3 g₂
    have hevL : evalUTerm env₄ (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 3))) =
        some (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₂)) :=
      evalUTerm_app_eq_some_iff.2 ⟨_, _, rfl, by simp [env₄, evalUTerm_pair],
        (isFuncFromTo_realFunSumFun A).isFuncEntity, hd2, rfl⟩
    have hevR : evalUTerm env₄
        (.app (.const realMulFun) (UTerm.pair (.var 1)
          (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 2))))) =
        some (Entity.funcApp realMulFun
          (Entity.kpair (Entity.atom rc) (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₁)))) := by
      rw [evalUTerm_app_eq_some_iff]
      refine ⟨realMulFun, _, rfl, ?_, isFuncFromTo_realMulFun.isFuncEntity, hdm, rfl⟩
      have hevS : evalUTerm env₄ (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 2))) =
          some (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₁)) :=
        evalUTerm_app_eq_some_iff.2 ⟨_, _, rfl, by simp [env₄, evalUTerm_pair],
          (isFuncFromTo_realFunSumFun A).isFuncEntity, hd1, rfl⟩
      simp [env₄, evalUTerm_pair, hevS]
    dsimp only [env₄] at hevL hevR
    exact ⟨_, hevL, hsum_eq ▸ hevR⟩
  obtain ⟨_, hFA, hall0⟩ := (F.transfer φ hsent).1 hstd; obtain rfl := Option.some.inj hFA
  obtain ⟨_, hFR, hall1⟩ := hall0 B hBA; obtain rfl := Option.some.inj hFR
  obtain ⟨_, hP1, hall2⟩ := hall1 c hc; obtain rfl := Option.some.inj hP1
  obtain ⟨_, hP2, hall3⟩ := hall2 fB hfB_P; obtain rfl := Option.some.inj hP2
  have hf_mul := (F.isFuncFromTo_star_iff).2 isFuncFromTo_realMulFun
  have hf_sum := (F.isFuncFromTo_star_iff).2 (isFuncFromTo_realFunSumFun A)
  obtain ⟨q, hq1, hq2⟩ := hall3 cfB hcfB_P ⟨B, by simp, fun x hxB ↦ by
    obtain ⟨hd_fB, hv_fB⟩ := hfB_eq x hxB
    obtain ⟨hd_cfB, hv_cfB⟩ := hcfB_eq x hxB
    have hd_m : Entity.kpair c (Entity.funcApp f x) ∈ Entity.relDom (F.star realMulFun) := by
      rw [hf_mul.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
      exact Entity.kpair_mem_prod_iff.2 ⟨hc, (hf.2.2 x hxB).2⟩
    refine ⟨Entity.funcApp cf x, ?_, ?_⟩
    · rw [starTerm, evalUTerm_app_eq_some_iff]
      exact ⟨cfB, x, by simp, by simp, hcfB_fn, hd_cfB, hv_cfB⟩
    · simp only [starTerm, starTerm_pair]
      rw [evalUTerm_app_eq_some_iff]
      refine ⟨F.star realMulFun, Entity.kpair c (Entity.funcApp f x), rfl, ?_,
        hf_mul.isFuncEntity, hd_m, (heq x hxB).symm⟩
      have hevf : evalUTerm
          (Function.update (Function.update (Function.update (Function.update
            (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 B) 1 c) 2 fB) 3 cfB) 4 x)
          (.app (.var 2) (.var 4)) = some (Entity.funcApp f x) :=
        evalUTerm_app_eq_some_iff.2 ⟨fB, x, by simp, by simp, hfB_fn, hd_fB, hv_fB⟩
      simp [evalUTerm_pair, hevf]⟩
  have hdY1 : Entity.kpair B fB ∈ Entity.relDom (F.star (realFunSumFun A)) := by
    rw [hf_sum.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hBA, hfB_P⟩
  have hdY2 : Entity.kpair B cfB ∈ Entity.relDom (F.star (realFunSumFun A)) := by
    rw [hf_sum.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hBA, hcfB_P⟩
  have hs1R : Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B fB) ∈ F.star realEntity :=
    hf_sum.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hdY1⟩)
  have hdmY : Entity.kpair c (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B fB)) ∈
      Entity.relDom (F.star realMulFun) := by
    rw [hf_mul.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hc, hs1R⟩
  let envY := Function.update (Function.update (Function.update
    (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 B) 1 c) 2 fB) 3 cfB
  have hevYL : evalUTerm envY
      (starTerm F.star (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 3)))) =
      some (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B cfB)) := by
    simp only [starTerm]; rw [evalUTerm_app_eq_some_iff]
    exact ⟨_, _, rfl, by simp [envY, starTerm_pair, evalUTerm_pair], hf_sum.isFuncEntity, hdY2, rfl⟩
  have hevYR : evalUTerm envY
      (starTerm F.star (.app (.const realMulFun) (UTerm.pair (.var 1)
        (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 2)))))) =
      some (F.starMul c (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B fB))) := by
    simp only [starTerm, starTerm_pair]; rw [evalUTerm_app_eq_some_iff]
    refine ⟨F.star realMulFun, _, rfl, ?_, hf_mul.isFuncEntity, hdmY, rfl⟩
    have hevS : evalUTerm envY (.app (.const (F.star (realFunSumFun A))) (UTerm.pair (.var 0) (.var 2))) =
        some (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B fB)) :=
      evalUTerm_app_eq_some_iff.2 ⟨_, _, rfl, by simp [envY, evalUTerm_pair],
        hf_sum.isFuncEntity, hdY1, rfl⟩
    simp [envY, evalUTerm_pair, hevS]
  dsimp only [envY] at hevYL hevYR
  exact (Option.some.inj (hevYL.symm.trans hq1)).trans (Option.some.inj (hevYR.symm.trans hq2)).symm

/-- Direct specialization of `hyperSum_smul` to `F.internalSmulOn B c f`:
`∑_{x ∈ B} (c * f(x)) = c * ∑_{x ∈ B} f(x)` (Goldblatt §13.20, Exercise 1, p. 181). -/
@[simp]
theorem Framework.hyperSum_internalSmulOn {Y : Type*} (F : Framework ℝ Y)
    {B c f : Entity Y} (hB : F.IsHyperfiniteSet B) (hc : c ∈ F.star realEntity)
    (hf : F.IsInternalRealFunOn f B) :
    F.hyperSum B (F.internalSmulOn B c f) = F.starMul c (F.hyperSum B f) := by
  obtain ⟨hcf, heq⟩ := F.isInternalRealFunOn_internalSmulOn hB.isSet hB.isInternalEntity hc hf
  exact F.hyperSum_smul hB hc hf hcf heq

/-- Goldblatt **Exercise 13.20(1), Property 2 (Additivity)** (p. 181):
`∑_{x ∈ B} (f(x) + g(x)) = ∑_{x ∈ B} f(x) + ∑_{x ∈ B} g(x)` for any hyperfinite set `B` and
internal `*ℝ`-valued functions `f, g, fg` on `B` with `fg(x) = f(x) + g(x)` on `B`. -/
theorem Framework.hyperSum_add {Y : Type*} (F : Framework ℝ Y)
    {B f g fg : Entity Y} (hB : F.IsHyperfiniteSet B)
    (hf : F.IsInternalRealFunOn f B) (hg : F.IsInternalRealFunOn g B)
    (hfg : F.IsInternalRealFunOn fg B)
    (heq : ∀ x ∈ B, Entity.funcApp fg x =
      F.starAdd (Entity.funcApp f x) (Entity.funcApp g x)) :
    F.hyperSum B fg = F.starAdd (F.hyperSum B f) (F.hyperSum B g) := by
  obtain ⟨A, hBA⟩ := hB
  let fB := Entity.inter f (Entity.prod B (F.star realEntity))
  let gB := Entity.inter g (Entity.prod B (F.star realEntity))
  let fgB := Entity.inter fg (Entity.prod B (F.star realEntity))
  obtain ⟨hfB_P, hfB_fn, hfB_eq⟩ := F.inter_prod_mem_star_powerset_and_eqOn hBA hf
  obtain ⟨hgB_P, hgB_fn, hgB_eq⟩ := F.inter_prod_mem_star_powerset_and_eqOn hBA hg
  obtain ⟨hfgB_P, hfgB_fn, hfgB_eq⟩ := F.inter_prod_mem_star_powerset_and_eqOn hBA hfg
  rw [F.hyperSum_eq_funcApp_of_mem_star_powerset hBA hfg hfgB_P hfgB_fn hfgB_eq,
      F.hyperSum_eq_funcApp_of_mem_star_powerset hBA hf hfB_P hfB_fn hfB_eq,
      F.hyperSum_eq_funcApp_of_mem_star_powerset hBA hg hgB_P hgB_fn hgB_eq]
  let φ : UFormula ℝ :=
    .forallIn 0 (.const (Entity.finPowerset A))
      (.forallIn 1 (.const (Entity.powerset (Entity.prod A realEntity)))
        (.forallIn 2 (.const (Entity.powerset (Entity.prod A realEntity)))
          (.forallIn 3 (.const (Entity.powerset (Entity.prod A realEntity)))
            (.imp
              (.forallIn 4 (.var 0)
                (.eq (.app (.var 3) (.var 4))
                     (.app (.const realAddFun)
                       (UTerm.pair (.app (.var 1) (.var 4)) (.app (.var 2) (.var 4))))))
              (.eq (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 3)))
                   (.app (.const realAddFun)
                     (UTerm.pair
                       (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 1)))
                       (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 2))))))))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm_pair, freeVarsUTerm]; tauto
  have hstd : SentenceHolds φ := by
    refine ⟨_, rfl, fun Z hZ ↦ ⟨_, rfl, fun g₁ hg₁ ↦ ⟨_, rfl, fun g₂ hg₂ ↦ ⟨_, rfl, fun g₃ hg₃ ⟨_, hZ0, hpt⟩ ↦ ?_⟩⟩⟩⟩
    obtain rfl := Option.some.inj (by simpa using hZ0)
    have hsum_eq : Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₃) =
        Entity.funcApp realAddFun
          (Entity.kpair (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₁))
                        (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₂))) := by
      rw [funcApp_realFunSumFun hZ hg₃, funcApp_realFunSumFun hZ hg₁,
          funcApp_realFunSumFun hZ hg₂, funcApp_realAddFun]
      congr 1
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      have hxZ : x ∈ Z := (Set.Finite.mem_toFinset (Entity.mem_finPowerset_iff.1 hZ).2.2).1 hx
      obtain ⟨y, hy1, hy2⟩ := hpt x hxZ
      obtain ⟨g₃', x₃, hg₃', hx₃, _, _, hv₃⟩ := evalUTerm_app_eq_some_iff.1 hy1
      have eg₃ : g₃ = g₃' := Option.some.inj (by simpa using hg₃')
      have ex₃ : x = x₃ := Option.some.inj (by simpa using hx₃)
      subst eg₃; subst ex₃
      obtain ⟨aF, pq, haF, hpq, _, hdom_a, hva⟩ := evalUTerm_app_eq_some_iff.1 hy2
      obtain rfl := Option.some.inj haF
      obtain ⟨v₁, v₂, h1_ev, h2_ev, rfl⟩ := evalUTerm_pair_eq_some_iff.1 hpq
      obtain ⟨g₁', x₁, hg₁', hx₁, _, _, hv₁⟩ := evalUTerm_app_eq_some_iff.1 h1_ev
      obtain ⟨g₂', x₂, hg₂', hx₂, _, _, hv₂⟩ := evalUTerm_app_eq_some_iff.1 h2_ev
      have eg₁ : g₁ = g₁' := Option.some.inj (by simpa using hg₁')
      have ex₁ : x = x₁ := Option.some.inj (by simpa using hx₁)
      have eg₂ : g₂ = g₂' := Option.some.inj (by simpa using hg₂')
      have ex₂ : x = x₂ := Option.some.inj (by simpa using hx₂)
      subst eg₁; subst ex₁; subst eg₂; subst ex₂; subst hv₁; subst hv₂; subst hv₃
      rw [isFuncFromTo_realAddFun.relDom_eq (Entity.isSet_prod _ _)] at hdom_a
      obtain ⟨hv₁R, hv₂R⟩ := Entity.kpair_mem_prod_iff.1 hdom_a
      obtain ⟨r₁, hr₁⟩ := mem_baseSet_iff.1 hv₁R
      obtain ⟨r₂, hr₂⟩ := mem_baseSet_iff.1 hv₂R
      rw [← hva, hr₁, hr₂, funcApp_realAddFun,
        Entity.atomVal_atom, Entity.atomVal_atom, Entity.atomVal_atom]
    have hd1 : Entity.kpair Z g₁ ∈ Entity.relDom (realFunSumFun A) := by
      rw [(isFuncFromTo_realFunSumFun A).relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hZ, hg₁⟩
    have hd2 : Entity.kpair Z g₂ ∈ Entity.relDom (realFunSumFun A) := by
      rw [(isFuncFromTo_realFunSumFun A).relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hZ, hg₂⟩
    have hd3 : Entity.kpair Z g₃ ∈ Entity.relDom (realFunSumFun A) := by
      rw [(isFuncFromTo_realFunSumFun A).relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hZ, hg₃⟩
    have hs1R := (isFuncFromTo_realFunSumFun A).mem_of_mem_relRan
      (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hd1⟩)
    have hs2R := (isFuncFromTo_realFunSumFun A).mem_of_mem_relRan
      (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hd2⟩)
    have hda : Entity.kpair (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₁))
        (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₂)) ∈ Entity.relDom realAddFun := by
      rw [isFuncFromTo_realAddFun.relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hs1R, hs2R⟩
    let env₄ := Function.update (Function.update (Function.update
      (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0 Z) 1 g₁) 2 g₂) 3 g₃
    have hevL : evalUTerm env₄ (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 3))) =
        some (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₃)) :=
      evalUTerm_app_eq_some_iff.2 ⟨_, _, rfl, by simp [env₄, evalUTerm_pair],
        (isFuncFromTo_realFunSumFun A).isFuncEntity, hd3, rfl⟩
    have hevR : evalUTerm env₄
        (.app (.const realAddFun) (UTerm.pair
          (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 1)))
          (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 2))))) =
        some (Entity.funcApp realAddFun
          (Entity.kpair (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₁))
                        (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₂)))) := by
      rw [evalUTerm_app_eq_some_iff]
      refine ⟨realAddFun, _, rfl, ?_, isFuncFromTo_realAddFun.isFuncEntity, hda, rfl⟩
      have hev1 : evalUTerm env₄ (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 1))) =
          some (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₁)) :=
        evalUTerm_app_eq_some_iff.2 ⟨_, _, rfl, by simp [env₄, evalUTerm_pair],
          (isFuncFromTo_realFunSumFun A).isFuncEntity, hd1, rfl⟩
      have hev2 : evalUTerm env₄ (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 2))) =
          some (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₂)) :=
        evalUTerm_app_eq_some_iff.2 ⟨_, _, rfl, by simp [env₄, evalUTerm_pair],
          (isFuncFromTo_realFunSumFun A).isFuncEntity, hd2, rfl⟩
      simp [evalUTerm_pair, hev1, hev2]
    dsimp only [env₄] at hevL hevR
    exact ⟨_, hevL, hsum_eq ▸ hevR⟩
  obtain ⟨_, hFA, hall0⟩ := (F.transfer φ hsent).1 hstd; obtain rfl := Option.some.inj hFA
  obtain ⟨_, hP1, hall1⟩ := hall0 B hBA; obtain rfl := Option.some.inj hP1
  obtain ⟨_, hP2, hall2⟩ := hall1 fB hfB_P; obtain rfl := Option.some.inj hP2
  obtain ⟨_, hP3, hall3⟩ := hall2 gB hgB_P; obtain rfl := Option.some.inj hP3
  have hf_add := (F.isFuncFromTo_star_iff).2 isFuncFromTo_realAddFun
  have hf_sum := (F.isFuncFromTo_star_iff).2 (isFuncFromTo_realFunSumFun A)
  obtain ⟨q, hq1, hq2⟩ := hall3 fgB hfgB_P ⟨B, by simp, fun x hxB ↦ by
    obtain ⟨hd_fB, hv_fB⟩ := hfB_eq x hxB
    obtain ⟨hd_gB, hv_gB⟩ := hgB_eq x hxB
    obtain ⟨hd_fgB, hv_fgB⟩ := hfgB_eq x hxB
    have hd_a : Entity.kpair (Entity.funcApp f x) (Entity.funcApp g x) ∈
        Entity.relDom (F.star realAddFun) := by
      rw [hf_add.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
      exact Entity.kpair_mem_prod_iff.2 ⟨(hf.2.2 x hxB).2, (hg.2.2 x hxB).2⟩
    refine ⟨Entity.funcApp fg x, ?_, ?_⟩
    · rw [starTerm, evalUTerm_app_eq_some_iff]
      exact ⟨fgB, x, by simp, by simp, hfgB_fn, hd_fgB, hv_fgB⟩
    · simp only [starTerm, starTerm_pair]
      rw [evalUTerm_app_eq_some_iff]
      refine ⟨F.star realAddFun, _, rfl, ?_, hf_add.isFuncEntity, hd_a, (heq x hxB).symm⟩
      let env₅ := Function.update (Function.update (Function.update (Function.update
        (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 B) 1 fB) 2 gB) 3 fgB) 4 x
      have hev1 : evalUTerm env₅ (.app (.var 1) (.var 4)) = some (Entity.funcApp f x) :=
        evalUTerm_app_eq_some_iff.2 ⟨fB, x, by simp [env₅], by simp [env₅], hfB_fn, hd_fB, hv_fB⟩
      have hev2 : evalUTerm env₅ (.app (.var 2) (.var 4)) = some (Entity.funcApp g x) :=
        evalUTerm_app_eq_some_iff.2 ⟨gB, x, by simp [env₅], by simp [env₅], hgB_fn, hd_gB, hv_gB⟩
      dsimp only [env₅] at hev1 hev2
      simp [evalUTerm_pair, hev1, hev2]⟩
  have hdY1 : Entity.kpair B fB ∈ Entity.relDom (F.star (realFunSumFun A)) := by
    rw [hf_sum.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hBA, hfB_P⟩
  have hdY2 : Entity.kpair B gB ∈ Entity.relDom (F.star (realFunSumFun A)) := by
    rw [hf_sum.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hBA, hgB_P⟩
  have hdY3 : Entity.kpair B fgB ∈ Entity.relDom (F.star (realFunSumFun A)) := by
    rw [hf_sum.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hBA, hfgB_P⟩
  have hs1R := hf_sum.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hdY1⟩)
  have hs2R := hf_sum.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hdY2⟩)
  have hdaY : Entity.kpair (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B fB))
      (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B gB)) ∈
      Entity.relDom (F.star realAddFun) := by
    rw [hf_add.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hs1R, hs2R⟩
  let envY := Function.update (Function.update (Function.update
    (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 B) 1 fB) 2 gB) 3 fgB
  have hevYL : evalUTerm envY
      (starTerm F.star (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 3)))) =
      some (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B fgB)) := by
    simp only [starTerm]; rw [evalUTerm_app_eq_some_iff]
    exact ⟨_, _, rfl, by simp [envY, starTerm_pair, evalUTerm_pair], hf_sum.isFuncEntity, hdY3, rfl⟩
  have hevYR : evalUTerm envY
      (starTerm F.star (.app (.const realAddFun) (UTerm.pair
        (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 1)))
        (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 2)))))) =
      some (F.starAdd (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B fB))
                      (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B gB))) := by
    simp only [starTerm, starTerm_pair]; rw [evalUTerm_app_eq_some_iff]
    refine ⟨F.star realAddFun, _, rfl, ?_, hf_add.isFuncEntity, hdaY, rfl⟩
    have hev1 : evalUTerm envY (.app (.const (F.star (realFunSumFun A))) (UTerm.pair (.var 0) (.var 1))) =
        some (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B fB)) :=
      evalUTerm_app_eq_some_iff.2 ⟨_, _, rfl, by simp [envY, evalUTerm_pair],
        hf_sum.isFuncEntity, hdY1, rfl⟩
    have hev2 : evalUTerm envY (.app (.const (F.star (realFunSumFun A))) (UTerm.pair (.var 0) (.var 2))) =
        some (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B gB)) :=
      evalUTerm_app_eq_some_iff.2 ⟨_, _, rfl, by simp [envY, evalUTerm_pair],
        hf_sum.isFuncEntity, hdY2, rfl⟩
    simp [evalUTerm_pair, hev1, hev2]
  dsimp only [envY] at hevYL hevYR
  exact (Option.some.inj (hevYL.symm.trans hq1)).trans (Option.some.inj (hevYR.symm.trans hq2)).symm

/-- Direct specialization of `hyperSum_add` to `F.internalAddOn B f g`:
`∑_{x ∈ B} (f(x) + g(x)) = ∑_{x ∈ B} f(x) + ∑_{x ∈ B} g(x)`
(Goldblatt §13.20, Exercise 1, p. 181). -/
@[simp]
theorem Framework.hyperSum_internalAddOn {Y : Type*} (F : Framework ℝ Y)
    {B f g : Entity Y} (hB : F.IsHyperfiniteSet B)
    (hf : F.IsInternalRealFunOn f B) (hg : F.IsInternalRealFunOn g B) :
    F.hyperSum B (F.internalAddOn B f g) =
      F.starAdd (F.hyperSum B f) (F.hyperSum B g) := by
  obtain ⟨hfg, heq⟩ := F.isInternalRealFunOn_internalAddOn hB.isSet hB.isInternalEntity hf hg
  exact F.hyperSum_add hB hf hg hfg heq

/-- Binary union of two hyperfinite sets is hyperfinite (Goldblatt §13.20, Exercise 1, p. 181). -/
theorem Framework.isHyperfiniteSet_union {X Y : Type*} (F : Framework X Y)
    {B C : Entity Y} (hB : F.IsHyperfiniteSet B) (hC : F.IsHyperfiniteSet C) :
    F.IsHyperfiniteSet (Entity.union B C) := by
  obtain ⟨A₁, hBA₁⟩ := hB
  obtain ⟨A₂, hCA₂⟩ := hC
  let A := Entity.union A₁ A₂
  have hBsub : ∀ x ∈ B, x ∈ F.star A := fun x hx ↦ by
    rw [F.star_union]; exact Entity.mem_union_iff.2 (Or.inl
      ((Entity.mem_powerset_iff.1 (F.mem_powerset_star_of_mem_star_powerset
        (F.mem_star_powerset_of_mem_star_finPowerset hBA₁))).2 x hx))
  have hCsub : ∀ x ∈ C, x ∈ F.star A := fun x hx ↦ by
    rw [F.star_union]; exact Entity.mem_union_iff.2 (Or.inr
      ((Entity.mem_powerset_iff.1 (F.mem_powerset_star_of_mem_star_powerset
        (F.mem_star_powerset_of_mem_star_finPowerset hCA₂))).2 x hx))
  have hBA : B ∈ F.star (Entity.finPowerset A) :=
    F.mem_star_finPowerset_of_isHyperfiniteSet_of_subset ⟨A₁, hBA₁⟩ hBsub
  have hCA : C ∈ F.star (Entity.finPowerset A) :=
    F.mem_star_finPowerset_of_isHyperfiniteSet_of_subset ⟨A₂, hCA₂⟩ hCsub
  have hU_int : F.IsInternalEntity (Entity.union B C) :=
    F.isInternalEntity_union (Framework.IsHyperfiniteSet.isInternalEntity ⟨A₁, hBA₁⟩)
      (Framework.IsHyperfiniteSet.isInternalEntity ⟨A₂, hCA₂⟩)
  have hU_P : Entity.union B C ∈ F.star (Entity.powerset A) := by
    refine F.mem_star_powerset_iff.2 ⟨Entity.mem_powerset_iff.2 ⟨Entity.isSet_union _ _, fun x hx ↦ ?_⟩, hU_int⟩
    rcases Entity.mem_union_iff.1 hx with hxB | hxC
    · exact hBsub x hxB
    · exact hCsub x hxC
  let φ : UFormula X :=
    .forallIn 0 (.const (Entity.finPowerset A))
      (.forallIn 1 (.const (Entity.finPowerset A))
        (.forallIn 2 (.const (Entity.powerset A))
          (.imp
            (.forallIn 3 (.var 2)
              (.disj (.mem (.var 3) (.var 0)) (.mem (.var 3) (.var 1))))
            (.mem (.var 2) (.const (Entity.finPowerset A))))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm]; tauto
  have hstd : SentenceHolds φ := by
    refine ⟨_, rfl, fun Z₁ hZ₁ ↦ ⟨_, rfl, fun Z₂ hZ₂ ↦ ⟨_, rfl, fun W hW ⟨_, hW0, hsub⟩ ↦ ?_⟩⟩⟩
    obtain rfl := Option.some.inj (by simpa using hW0)
    obtain ⟨_, _, hfin₁⟩ := Entity.mem_finPowerset_iff.1 hZ₁
    obtain ⟨_, _, hfin₂⟩ := Entity.mem_finPowerset_iff.1 hZ₂
    obtain ⟨hWs, hWsubA⟩ := Entity.mem_powerset_iff.1 hW
    have hW_sub_u : W.extSet ⊆ Z₁.extSet ∪ Z₂.extSet := fun x hxW ↦ by
      rcases hsub x hxW with ⟨x', Z₁', hx', hZ₁', hm⟩ | ⟨x', Z₂', hx', hZ₂', hm⟩
      · have e1 : x = x' := Option.some.inj (by simpa using hx')
        have e2 : Z₁ = Z₁' := Option.some.inj (by simpa using hZ₁')
        exact Or.inl (e1 ▸ e2 ▸ hm)
      · have e1 : x = x' := Option.some.inj (by simpa using hx')
        have e2 : Z₂ = Z₂' := Option.some.inj (by simpa using hZ₂')
        exact Or.inr (e1 ▸ e2 ▸ hm)
    exact ⟨W, _, by simp, rfl,
      Entity.mem_finPowerset_iff.2 ⟨hWs, hWsubA, (hfin₁.union hfin₂).subset hW_sub_u⟩⟩
  obtain ⟨_, hFA0, hall0⟩ := (F.transfer φ hsent).1 hstd; obtain rfl := Option.some.inj hFA0
  obtain ⟨_, hFA1, hall1⟩ := hall0 B hBA; obtain rfl := Option.some.inj hFA1
  obtain ⟨_, hPA, hall2⟩ := hall1 C hCA; obtain rfl := Option.some.inj hPA
  obtain ⟨U', FA', hU', hFA', hm⟩ := hall2 (Entity.union B C) hU_P ⟨Entity.union B C, by simp, fun x hx ↦ by
    rcases Entity.mem_union_iff.1 hx with hxB | hxC
    · exact Or.inl ⟨x, B, by simp, by simp, hxB⟩
    · exact Or.inr ⟨x, C, by simp, by simp, hxC⟩⟩
  have eU : Entity.union B C = U' := Option.some.inj (by simpa using hU')
  obtain rfl := Option.some.inj hFA'
  exact ⟨A, eU ▸ hm⟩

/-- Goldblatt **Exercise 13.20(1), Property 3 (Disjoint Additivity)** (p. 181):
If `B, C` are disjoint hyperfinite sets (`Entity.inter B C = ∅`) and `f` is an internal
`*ℝ`-valued function on `Entity.union B C`, then
`∑_{x ∈ B ∪ C} f(x) = ∑_{x ∈ B} f(x) + ∑_{x ∈ C} f(x)`. -/
theorem Framework.hyperSum_union_disjoint {Y : Type*} (F : Framework ℝ Y)
    {B C f : Entity Y} (hB : F.IsHyperfiniteSet B) (hC : F.IsHyperfiniteSet C)
    (hdisj : Entity.inter B C = ∅)
    (hf : F.IsInternalRealFunOn f (Entity.union B C)) :
    F.hyperSum (Entity.union B C) f = F.starAdd (F.hyperSum B f) (F.hyperSum C f) := by
  let U := Entity.union B C
  obtain ⟨A, hUA⟩ := F.isHyperfiniteSet_union hB hC
  have hUsub : ∀ x ∈ U, x ∈ F.star A :=
    (Entity.mem_powerset_iff.1 (F.mem_powerset_star_of_mem_star_powerset
      (F.mem_star_powerset_of_mem_star_finPowerset hUA))).2
  have hBA : B ∈ F.star (Entity.finPowerset A) :=
    F.mem_star_finPowerset_of_isHyperfiniteSet_of_subset hB
      (fun x hx ↦ hUsub x (Entity.mem_union_iff.2 (Or.inl hx)))
  have hCA : C ∈ F.star (Entity.finPowerset A) :=
    F.mem_star_finPowerset_of_isHyperfiniteSet_of_subset hC
      (fun x hx ↦ hUsub x (Entity.mem_union_iff.2 (Or.inr hx)))
  have hfB : F.IsInternalRealFunOn f B :=
    ⟨hf.1, hf.2.1, fun x hx ↦ hf.2.2 x (Entity.mem_union_iff.2 (Or.inl hx))⟩
  have hfC : F.IsInternalRealFunOn f C :=
    ⟨hf.1, hf.2.1, fun x hx ↦ hf.2.2 x (Entity.mem_union_iff.2 (Or.inr hx))⟩
  let fU := Entity.inter f (Entity.prod U (F.star realEntity))
  obtain ⟨hfU_P, hfU_fn, hfU_eq⟩ := F.inter_prod_mem_star_powerset_and_eqOn hUA hf
  rw [F.hyperSum_eq_funcApp_of_mem_star_powerset hUA hf hfU_P hfU_fn hfU_eq,
      F.hyperSum_eq_funcApp_of_mem_star_powerset hBA hfB hfU_P hfU_fn
        (fun x hx ↦ hfU_eq x (Entity.mem_union_iff.2 (Or.inl hx))),
      F.hyperSum_eq_funcApp_of_mem_star_powerset hCA hfC hfU_P hfU_fn
        (fun x hx ↦ hfU_eq x (Entity.mem_union_iff.2 (Or.inr hx)))]
  let φ : UFormula ℝ :=
    .forallIn 0 (.const (Entity.finPowerset A))
      (.forallIn 1 (.const (Entity.finPowerset A))
        (.forallIn 2 (.const (Entity.finPowerset A))
          (.forallIn 3 (.const (Entity.powerset (Entity.prod A realEntity)))
            (.imp
              (.conj
                (.conj
                  (.forallIn 4 (.var 2) (.disj (.mem (.var 4) (.var 0)) (.mem (.var 4) (.var 1))))
                  (.conj
                    (.forallIn 4 (.var 0) (.mem (.var 4) (.var 2)))
                    (.forallIn 4 (.var 1) (.mem (.var 4) (.var 2)))))
                (.forallIn 4 (.var 0) (.neg (.mem (.var 4) (.var 1)))))
              (.eq (.app (.const (realFunSumFun A)) (UTerm.pair (.var 2) (.var 3)))
                   (.app (.const realAddFun)
                     (UTerm.pair
                       (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 3)))
                       (.app (.const (realFunSumFun A)) (UTerm.pair (.var 1) (.var 3))))))))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm_pair, freeVarsUTerm]; tauto
  have hstd : SentenceHolds φ := by
    refine ⟨_, rfl, fun Z₁ hZ₁ ↦ ⟨_, rfl, fun Z₂ hZ₂ ↦ ⟨_, rfl, fun W hW ↦ ⟨_, rfl,
      fun g hg ⟨⟨⟨_, hW0, hcov⟩, ⟨_, hZ₁0, hsub₁⟩, ⟨_, hZ₂0, hsub₂⟩⟩, ⟨_, hZ₁1, hdis⟩⟩ ↦ ?_⟩⟩⟩⟩
    obtain rfl := Option.some.inj (by simpa using hW0)
    obtain rfl := Option.some.inj (by simpa using hZ₁0)
    obtain rfl := Option.some.inj (by simpa using hZ₂0)
    obtain rfl := Option.some.inj (by simpa using hZ₁1)
    classical
    obtain ⟨_, _, hfin₁⟩ := Entity.mem_finPowerset_iff.1 hZ₁
    obtain ⟨_, _, hfin₂⟩ := Entity.mem_finPowerset_iff.1 hZ₂
    obtain ⟨_, _, hfinW⟩ := Entity.mem_finPowerset_iff.1 hW
    have htoFin_eq : hfinW.toFinset = hfin₁.toFinset ∪ hfin₂.toFinset := by
      ext x
      rw [Set.Finite.mem_toFinset, Finset.mem_union,
          Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      constructor
      · intro hxW
        rcases hcov x hxW with ⟨x', Z₁', hx', hZ₁', hm⟩ | ⟨x', Z₂', hx', hZ₂', hm⟩
        · have e1 : x = x' := Option.some.inj (by simpa using hx')
          have e2 : Z₁ = Z₁' := Option.some.inj (by simpa using hZ₁')
          exact Or.inl (e1 ▸ e2 ▸ hm)
        · have e1 : x = x' := Option.some.inj (by simpa using hx')
          have e2 : Z₂ = Z₂' := Option.some.inj (by simpa using hZ₂')
          exact Or.inr (e1 ▸ e2 ▸ hm)
      · rintro (hx₁ | hx₂)
        · obtain ⟨x', W', hx', hW', hm⟩ := hsub₁ x hx₁
          have e1 : x = x' := Option.some.inj (by simpa using hx')
          have e2 : W = W' := Option.some.inj (by simpa using hW')
          exact e1 ▸ e2 ▸ hm
        · obtain ⟨x', W', hx', hW', hm⟩ := hsub₂ x hx₂
          have e1 : x = x' := Option.some.inj (by simpa using hx')
          have e2 : W = W' := Option.some.inj (by simpa using hW')
          exact e1 ▸ e2 ▸ hm
    have hdisj_fin : Disjoint hfin₁.toFinset hfin₂.toFinset := by
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      exact hdis x ((Set.Finite.mem_toFinset hfin₁).1 hx₁)
        ⟨x, Z₂, by simp, by simp, (Set.Finite.mem_toFinset hfin₂).1 hx₂⟩
    have hsum_eq : Entity.funcApp (realFunSumFun A) (Entity.kpair W g) =
        Entity.funcApp realAddFun
          (Entity.kpair (Entity.funcApp (realFunSumFun A) (Entity.kpair Z₁ g))
                        (Entity.funcApp (realFunSumFun A) (Entity.kpair Z₂ g))) := by
      rw [funcApp_realFunSumFun hW hg, funcApp_realFunSumFun hZ₁ hg,
          funcApp_realFunSumFun hZ₂ hg, funcApp_realAddFun]
      exact congrArg Entity.atom (by rw [htoFin_eq, Finset.sum_union hdisj_fin])
    have hdW : Entity.kpair W g ∈ Entity.relDom (realFunSumFun A) := by
      rw [(isFuncFromTo_realFunSumFun A).relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hW, hg⟩
    have hd1 : Entity.kpair Z₁ g ∈ Entity.relDom (realFunSumFun A) := by
      rw [(isFuncFromTo_realFunSumFun A).relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hZ₁, hg⟩
    have hd2 : Entity.kpair Z₂ g ∈ Entity.relDom (realFunSumFun A) := by
      rw [(isFuncFromTo_realFunSumFun A).relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hZ₂, hg⟩
    have hs1R := (isFuncFromTo_realFunSumFun A).mem_of_mem_relRan
      (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hd1⟩)
    have hs2R := (isFuncFromTo_realFunSumFun A).mem_of_mem_relRan
      (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hd2⟩)
    have hda : Entity.kpair (Entity.funcApp (realFunSumFun A) (Entity.kpair Z₁ g))
        (Entity.funcApp (realFunSumFun A) (Entity.kpair Z₂ g)) ∈ Entity.relDom realAddFun := by
      rw [isFuncFromTo_realAddFun.relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hs1R, hs2R⟩
    let env₄ := Function.update (Function.update (Function.update
      (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0 Z₁) 1 Z₂) 2 W) 3 g
    have hevL : evalUTerm env₄ (.app (.const (realFunSumFun A)) (UTerm.pair (.var 2) (.var 3))) =
        some (Entity.funcApp (realFunSumFun A) (Entity.kpair W g)) :=
      evalUTerm_app_eq_some_iff.2 ⟨_, _, rfl, by simp [env₄, evalUTerm_pair],
        (isFuncFromTo_realFunSumFun A).isFuncEntity, hdW, rfl⟩
    have hevR : evalUTerm env₄
        (.app (.const realAddFun) (UTerm.pair
          (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 3)))
          (.app (.const (realFunSumFun A)) (UTerm.pair (.var 1) (.var 3))))) =
        some (Entity.funcApp realAddFun
          (Entity.kpair (Entity.funcApp (realFunSumFun A) (Entity.kpair Z₁ g))
                        (Entity.funcApp (realFunSumFun A) (Entity.kpair Z₂ g)))) := by
      rw [evalUTerm_app_eq_some_iff]
      refine ⟨realAddFun, _, rfl, ?_, isFuncFromTo_realAddFun.isFuncEntity, hda, rfl⟩
      have hev1 : evalUTerm env₄ (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 3))) =
          some (Entity.funcApp (realFunSumFun A) (Entity.kpair Z₁ g)) :=
        evalUTerm_app_eq_some_iff.2 ⟨_, _, rfl, by simp [env₄, evalUTerm_pair],
          (isFuncFromTo_realFunSumFun A).isFuncEntity, hd1, rfl⟩
      have hev2 : evalUTerm env₄ (.app (.const (realFunSumFun A)) (UTerm.pair (.var 1) (.var 3))) =
          some (Entity.funcApp (realFunSumFun A) (Entity.kpair Z₂ g)) :=
        evalUTerm_app_eq_some_iff.2 ⟨_, _, rfl, by simp [env₄, evalUTerm_pair],
          (isFuncFromTo_realFunSumFun A).isFuncEntity, hd2, rfl⟩
      simp [evalUTerm_pair, hev1, hev2]
    dsimp only [env₄] at hevL hevR
    exact ⟨_, hevL, hsum_eq ▸ hevR⟩
  obtain ⟨_, hFA0, hall0⟩ := (F.transfer φ hsent).1 hstd; obtain rfl := Option.some.inj hFA0
  obtain ⟨_, hFA1, hall1⟩ := hall0 B hBA; obtain rfl := Option.some.inj hFA1
  obtain ⟨_, hFA2, hall2⟩ := hall1 C hCA; obtain rfl := Option.some.inj hFA2
  obtain ⟨_, hPA, hall3⟩ := hall2 U hUA; obtain rfl := Option.some.inj hPA
  obtain ⟨q, hq1, hq2⟩ := hall3 fU hfU_P ⟨⟨
    ⟨U, by simp, fun x hxU ↦ by
      rcases Entity.mem_union_iff.1 hxU with hxB | hxC
      · exact Or.inl ⟨x, B, by simp, by simp, hxB⟩
      · exact Or.inr ⟨x, C, by simp, by simp, hxC⟩⟩,
    ⟨B, by simp, fun x hxB ↦ ⟨x, U, by simp, by simp, Entity.mem_union_iff.2 (Or.inl hxB)⟩⟩,
    ⟨C, by simp, fun x hxC ↦ ⟨x, U, by simp, by simp, Entity.mem_union_iff.2 (Or.inr hxC)⟩⟩⟩,
    ⟨B, by simp, fun x hxB ⟨x', C', hx', hC', hxC⟩ ↦ by
      have e1 : x = x' := Option.some.inj (by simpa using hx')
      have e2 : C = C' := Option.some.inj (by simpa using hC')
      have hmem0 : x ∈ (∅ : Entity Y) := hdisj ▸ Entity.mem_inter_iff.2 ⟨hxB, e1 ▸ e2 ▸ hxC⟩
      exact Entity.not_mem_empty x hmem0⟩⟩
  have hf_add := (F.isFuncFromTo_star_iff).2 isFuncFromTo_realAddFun
  have hf_sum := (F.isFuncFromTo_star_iff).2 (isFuncFromTo_realFunSumFun A)
  have hdW : Entity.kpair U fU ∈ Entity.relDom (F.star (realFunSumFun A)) := by
    rw [hf_sum.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hUA, hfU_P⟩
  have hd1 : Entity.kpair B fU ∈ Entity.relDom (F.star (realFunSumFun A)) := by
    rw [hf_sum.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hBA, hfU_P⟩
  have hd2 : Entity.kpair C fU ∈ Entity.relDom (F.star (realFunSumFun A)) := by
    rw [hf_sum.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hCA, hfU_P⟩
  have hs1R := hf_sum.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hd1⟩)
  have hs2R := hf_sum.mem_of_mem_relRan (Entity.mem_relRan_iff.2 ⟨_, Entity.kpair_funcApp_mem hd2⟩)
  have hdaY : Entity.kpair (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B fU))
      (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair C fU)) ∈
      Entity.relDom (F.star realAddFun) := by
    rw [hf_add.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hs1R, hs2R⟩
  let envY := Function.update (Function.update (Function.update
    (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 B) 1 C) 2 U) 3 fU
  have hevYL : evalUTerm envY
      (starTerm F.star (.app (.const (realFunSumFun A)) (UTerm.pair (.var 2) (.var 3)))) =
      some (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair U fU)) := by
    simp only [starTerm]; rw [evalUTerm_app_eq_some_iff]
    exact ⟨_, _, rfl, by simp [envY, starTerm_pair, evalUTerm_pair], hf_sum.isFuncEntity, hdW, rfl⟩
  have hevYR : evalUTerm envY
      (starTerm F.star (.app (.const realAddFun) (UTerm.pair
        (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 3)))
        (.app (.const (realFunSumFun A)) (UTerm.pair (.var 1) (.var 3)))))) =
      some (F.starAdd (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B fU))
                      (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair C fU))) := by
    simp only [starTerm, starTerm_pair]; rw [evalUTerm_app_eq_some_iff]
    refine ⟨F.star realAddFun, _, rfl, ?_, hf_add.isFuncEntity, hdaY, rfl⟩
    have hev1 : evalUTerm envY (.app (.const (F.star (realFunSumFun A))) (UTerm.pair (.var 0) (.var 3))) =
        some (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B fU)) :=
      evalUTerm_app_eq_some_iff.2 ⟨_, _, rfl, by simp [envY, evalUTerm_pair],
        hf_sum.isFuncEntity, hd1, rfl⟩
    have hev2 : evalUTerm envY (.app (.const (F.star (realFunSumFun A))) (UTerm.pair (.var 1) (.var 3))) =
        some (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair C fU)) :=
      evalUTerm_app_eq_some_iff.2 ⟨_, _, rfl, by simp [envY, evalUTerm_pair],
        hf_sum.isFuncEntity, hd2, rfl⟩
    simp [evalUTerm_pair, hev1, hev2]
  dsimp only [envY] at hevYL hevYR
  exact (Option.some.inj (hevYL.symm.trans hq1)).trans (Option.some.inj (hevYR.symm.trans hq2)).symm

/-- Goldblatt **Exercise 13.20(1), Property 4 (Order Monotonicity)** (p. 181):
`∑_{x ∈ B} f(x) ≤ ∑_{x ∈ B} g(x)` whenever `f(x) ≤ g(x)` on `B`! -/
theorem Framework.hyperSum_mono {Y : Type*} (F : Framework ℝ Y)
    {B f g : Entity Y} (hB : F.IsHyperfiniteSet B)
    (hf : F.IsInternalRealFunOn f B) (hg : F.IsInternalRealFunOn g B)
    (hle : ∀ x ∈ B, Entity.kpair (Entity.funcApp f x) (Entity.funcApp g x) ∈ F.star realLeRel) :
    Entity.kpair (F.hyperSum B f) (F.hyperSum B g) ∈ F.star realLeRel := by
  obtain ⟨A, hBA⟩ := hB
  let fB := Entity.inter f (Entity.prod B (F.star realEntity))
  let gB := Entity.inter g (Entity.prod B (F.star realEntity))
  obtain ⟨hfB_P, hfB_fn, hfB_eq⟩ := F.inter_prod_mem_star_powerset_and_eqOn hBA hf
  obtain ⟨hgB_P, hgB_fn, hgB_eq⟩ := F.inter_prod_mem_star_powerset_and_eqOn hBA hg
  rw [F.hyperSum_eq_funcApp_of_mem_star_powerset hBA hf hfB_P hfB_fn hfB_eq,
      F.hyperSum_eq_funcApp_of_mem_star_powerset hBA hg hgB_P hgB_fn hgB_eq]
  let φ : UFormula ℝ :=
    .forallIn 0 (.const (Entity.finPowerset A))
      (.forallIn 1 (.const (Entity.powerset (Entity.prod A realEntity)))
        (.forallIn 2 (.const (Entity.powerset (Entity.prod A realEntity)))
          (.imp
            (.forallIn 3 (.var 0)
              (.mem (UTerm.pair (.app (.var 1) (.var 3)) (.app (.var 2) (.var 3)))
                    (.const realLeRel)))
            (.mem (UTerm.pair
                    (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 1)))
                    (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 2))))
                  (.const realLeRel)))))
  have hsent : IsSentence φ := by
    rw [IsSentence, Finset.eq_empty_iff_forall_notMem]
    intro v; simp [φ, freeVarsUFormula, freeVarsUTerm_pair, freeVarsUTerm]; tauto
  have hstd : SentenceHolds φ := by
    refine ⟨_, rfl, fun Z hZ ↦ ⟨_, rfl, fun g₁ hg₁ ↦ ⟨_, rfl, fun g₂ hg₂ ⟨_, hZ0, hpt⟩ ↦ ?_⟩⟩⟩
    obtain rfl := Option.some.inj (by simpa using hZ0)
    have hsum_le : Entity.kpair
        (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₁))
        (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₂)) ∈ realLeRel := by
      rw [funcApp_realFunSumFun hZ hg₁, funcApp_realFunSumFun hZ hg₂, kpair_atom_mem_realLeRel_iff]
      refine Finset.sum_le_sum fun x hx ↦ ?_
      have hxZ : x ∈ Z := (Set.Finite.mem_toFinset (Entity.mem_finPowerset_iff.1 hZ).2.2).1 hx
      obtain ⟨pq, R', hpq, hR', hm⟩ := hpt x hxZ
      obtain rfl := Option.some.inj hR'
      obtain ⟨v₁, v₂, h1_ev, h2_ev, rfl⟩ := evalUTerm_pair_eq_some_iff.1 hpq
      obtain ⟨g₁', x₁, hg₁', hx₁, _, _, hv₁⟩ := evalUTerm_app_eq_some_iff.1 h1_ev
      obtain ⟨g₂', x₂, hg₂', hx₂, _, _, hv₂⟩ := evalUTerm_app_eq_some_iff.1 h2_ev
      have eg₁ : g₁ = g₁' := Option.some.inj (by simpa using hg₁')
      have ex₁ : x = x₁ := Option.some.inj (by simpa using hx₁)
      have eg₂ : g₂ = g₂' := Option.some.inj (by simpa using hg₂')
      have ex₂ : x = x₂ := Option.some.inj (by simpa using hx₂)
      subst eg₁; subst ex₁; subst eg₂; subst ex₂; subst hv₁; subst hv₂
      have hbdd : IsBoundedRank {p : Entity ℝ |
          ∃ a b : ℝ, a ≤ b ∧ p = Entity.kpair (Entity.atom a) (Entity.atom b)} :=
        (Entity.isBoundedRank_prod realEntity realEntity).subset fun _ ⟨a, b, _, hp⟩ ↦
          ⟨Entity.atom a, mem_baseSet_iff.2 ⟨a, rfl⟩, Entity.atom b, mem_baseSet_iff.2 ⟨b, rfl⟩, hp⟩
      rw [realLeRel, Entity.mem_setOfBounded hbdd] at hm
      obtain ⟨ra, rb, hrab, heqp⟩ := hm
      obtain ⟨ha, hb⟩ := Entity.kpair_inj.1 heqp
      rw [ha, hb, Entity.atomVal_atom, Entity.atomVal_atom]
      exact hrab
    have hd1 : Entity.kpair Z g₁ ∈ Entity.relDom (realFunSumFun A) := by
      rw [(isFuncFromTo_realFunSumFun A).relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hZ, hg₁⟩
    have hd2 : Entity.kpair Z g₂ ∈ Entity.relDom (realFunSumFun A) := by
      rw [(isFuncFromTo_realFunSumFun A).relDom_eq (Entity.isSet_prod _ _)]
      exact Entity.kpair_mem_prod_iff.2 ⟨hZ, hg₂⟩
    let env₃ := Function.update (Function.update
      (Function.update (fun _ : ℕ ↦ (∅ : Entity ℝ)) 0 Z) 1 g₁) 2 g₂
    have hev1 : evalUTerm env₃ (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 1))) =
        some (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₁)) :=
      evalUTerm_app_eq_some_iff.2 ⟨_, _, rfl, by simp [env₃, evalUTerm_pair],
        (isFuncFromTo_realFunSumFun A).isFuncEntity, hd1, rfl⟩
    have hev2 : evalUTerm env₃ (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 2))) =
        some (Entity.funcApp (realFunSumFun A) (Entity.kpair Z g₂)) :=
      evalUTerm_app_eq_some_iff.2 ⟨_, _, rfl, by simp [env₃, evalUTerm_pair],
        (isFuncFromTo_realFunSumFun A).isFuncEntity, hd2, rfl⟩
    dsimp only [env₃] at hev1 hev2
    exact ⟨_, realLeRel, by simp [evalUTerm_pair, hev1, hev2], rfl, hsum_le⟩
  obtain ⟨_, hFA, hall0⟩ := (F.transfer φ hsent).1 hstd; obtain rfl := Option.some.inj hFA
  obtain ⟨_, hP1, hall1⟩ := hall0 B hBA; obtain rfl := Option.some.inj hP1
  obtain ⟨_, hP2, hall2⟩ := hall1 fB hfB_P; obtain rfl := Option.some.inj hP2
  obtain ⟨p, R', hp, hR', hm⟩ := hall2 gB hgB_P ⟨B, by simp, fun x hxB ↦ by
    obtain ⟨hd_fB, hv_fB⟩ := hfB_eq x hxB
    obtain ⟨hd_gB, hv_gB⟩ := hgB_eq x hxB
    let env₄ := Function.update (Function.update (Function.update
      (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 B) 1 fB) 2 gB) 3 x
    have hev1 : evalUTerm env₄ (.app (.var 1) (.var 3)) = some (Entity.funcApp f x) :=
      evalUTerm_app_eq_some_iff.2 ⟨fB, x, by simp [env₄], by simp [env₄], hfB_fn, hd_fB, hv_fB⟩
    have hev2 : evalUTerm env₄ (.app (.var 2) (.var 3)) = some (Entity.funcApp g x) :=
      evalUTerm_app_eq_some_iff.2 ⟨gB, x, by simp [env₄], by simp [env₄], hgB_fn, hd_gB, hv_gB⟩
    dsimp only [env₄] at hev1 hev2
    exact ⟨Entity.kpair (Entity.funcApp f x) (Entity.funcApp g x), F.star realLeRel,
      by simp [starTerm_pair, starTerm, evalUTerm_pair, hev1, hev2], rfl, hle x hxB⟩⟩
  obtain rfl := Option.some.inj hR'
  have hf_sum := (F.isFuncFromTo_star_iff).2 (isFuncFromTo_realFunSumFun A)
  have hd1 : Entity.kpair B fB ∈ Entity.relDom (F.star (realFunSumFun A)) := by
    rw [hf_sum.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hBA, hfB_P⟩
  have hd2 : Entity.kpair B gB ∈ Entity.relDom (F.star (realFunSumFun A)) := by
    rw [hf_sum.relDom_eq ((F.isSet_star_iff).2 (Entity.isSet_prod _ _)), F.star_prod]
    exact Entity.kpair_mem_prod_iff.2 ⟨hBA, hgB_P⟩
  let envY := Function.update (Function.update
    (Function.update (fun _ : ℕ ↦ (∅ : Entity Y)) 0 B) 1 fB) 2 gB
  have hev1 : evalUTerm envY
      (starTerm F.star (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 1)))) =
      some (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B fB)) := by
    simp only [starTerm]; rw [evalUTerm_app_eq_some_iff]
    exact ⟨_, _, rfl, by simp [envY, starTerm_pair, evalUTerm_pair], hf_sum.isFuncEntity, hd1, rfl⟩
  have hev2 : evalUTerm envY
      (starTerm F.star (.app (.const (realFunSumFun A)) (UTerm.pair (.var 0) (.var 2)))) =
      some (Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B gB)) := by
    simp only [starTerm]; rw [evalUTerm_app_eq_some_iff]
    exact ⟨_, _, rfl, by simp [envY, starTerm_pair, evalUTerm_pair], hf_sum.isFuncEntity, hd2, rfl⟩
  dsimp only [envY] at hev1 hev2
  rw [starTerm_pair] at hp
  obtain ⟨s₁, s₂, hs₁, hs₂, rfl⟩ := evalUTerm_pair_eq_some_iff.1 hp
  have es₁ : Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B fB) = s₁ :=
    Option.some.inj (hev1.symm.trans hs₁)
  have es₂ : Entity.funcApp (F.star (realFunSumFun A)) (Entity.kpair B gB) = s₂ :=
    Option.some.inj (hev2.symm.trans hs₂)
  exact es₁ ▸ es₂ ▸ hm

/-- Goldblatt **Exercise 13.20(2)** (p. 181): **Indexed Hyperfinite Sums** `∑_{i=1}^n x_i`
(`F.hyperIndexedSum n x`) with `n ∈ *ℕ₀` (in particular, **unlimited** `n ∈ *ℕ \ im ℕ`).
Since `F.initSeg n = {i ∈ *ℕ : 1 ≤ i ≤ n}` belongs to `*𝒫_F(ℕ)` for every `n ∈ *ℕ₀` (even when `n`
is unlimited), the indexed sum `∑_{i=1}^n x_i` is well-defined as `F.hyperSum (F.initSeg n) x`
whenever the sequence `i ↦ x_i` is an **internal** `*ℝ`-valued function whose domain contains
`{1, …, n}` (`F.IsInternalRealFunOn x (F.initSeg n)` — whereas an *external* sequence cannot in
general be summed over an unlimited initial segment). -/
def Framework.hyperIndexedSum {Y : Type*} (F : Framework ℝ Y) (n x : Entity Y) : Entity Y :=
  F.hyperSum (F.initSeg n) x

/-- Every indexed hyperfinite sum `∑_{i=1}^n x_i` (`n ∈ F.star nat0Entity`, including unlimited
`n ∈ *ℕ \ im ℕ`) of an internal `*ℝ`-valued sequence `x` belongs to `F.star realEntity` (`*ℝ`;
Goldblatt §13.20, Exercise 2, p. 181). -/
theorem Framework.hyperIndexedSum_mem_star_realEntity {Y : Type*} (F : Framework ℝ Y)
    {n x : Entity Y} (hn : n ∈ F.star nat0Entity)
    (hx : F.IsInternalRealFunOn x (F.initSeg n)) :
    F.hyperIndexedSum n x ∈ F.star realEntity :=
  F.hyperSum_mem_star_realEntity ⟨posNatEntity, F.initSeg_mem_star_finPowerset hn⟩ hx

/-- Scalar linearity of indexed hyperfinite sums `∑_{i=1}^n (c * x_i) = c * ∑_{i=1}^n x_i`
for any `n ∈ F.star nat0Entity` (including unlimited `n`; Goldblatt §13.20, Exercises 1–2, p. 181). -/
theorem Framework.hyperIndexedSum_smul {Y : Type*} (F : Framework ℝ Y)
    {n c x cx : Entity Y} (hn : n ∈ F.star nat0Entity) (hc : c ∈ F.star realEntity)
    (hx : F.IsInternalRealFunOn x (F.initSeg n))
    (hcx : F.IsInternalRealFunOn cx (F.initSeg n))
    (heq : ∀ i ∈ F.initSeg n, Entity.funcApp cx i = F.starMul c (Entity.funcApp x i)) :
    F.hyperIndexedSum n cx = F.starMul c (F.hyperIndexedSum n x) :=
  F.hyperSum_smul ⟨posNatEntity, F.initSeg_mem_star_finPowerset hn⟩ hc hx hcx heq

/-- Additivity of indexed hyperfinite sums `∑_{i=1}^n (x_i + y_i) = ∑_{i=1}^n x_i + ∑_{i=1}^n y_i`
for any `n ∈ F.star nat0Entity` (including unlimited `n`; Goldblatt §13.20, Exercises 1–2, p. 181). -/
theorem Framework.hyperIndexedSum_add {Y : Type*} (F : Framework ℝ Y)
    {n x y xy : Entity Y} (hn : n ∈ F.star nat0Entity)
    (hx : F.IsInternalRealFunOn x (F.initSeg n))
    (hy : F.IsInternalRealFunOn y (F.initSeg n))
    (hxy : F.IsInternalRealFunOn xy (F.initSeg n))
    (heq : ∀ i ∈ F.initSeg n, Entity.funcApp xy i =
      F.starAdd (Entity.funcApp x i) (Entity.funcApp y i)) :
    F.hyperIndexedSum n xy = F.starAdd (F.hyperIndexedSum n x) (F.hyperIndexedSum n y) :=
  F.hyperSum_add ⟨posNatEntity, F.initSeg_mem_star_finPowerset hn⟩ hx hy hxy heq

/-- Order monotonicity of indexed hyperfinite sums `∑_{i=1}^n x_i ≤ ∑_{i=1}^n y_i` for any
`n ∈ F.star nat0Entity` (including unlimited `n`; Goldblatt §13.20, Exercises 1–2, p. 181). -/
theorem Framework.hyperIndexedSum_mono {Y : Type*} (F : Framework ℝ Y)
    {n x y : Entity Y} (hn : n ∈ F.star nat0Entity)
    (hx : F.IsInternalRealFunOn x (F.initSeg n))
    (hy : F.IsInternalRealFunOn y (F.initSeg n))
    (hle : ∀ i ∈ F.initSeg n,
      Entity.kpair (Entity.funcApp x i) (Entity.funcApp y i) ∈ F.star realLeRel) :
    Entity.kpair (F.hyperIndexedSum n x) (F.hyperIndexedSum n y) ∈ F.star realLeRel :=
  F.hyperSum_mono ⟨posNatEntity, F.initSeg_mem_star_finPowerset hn⟩ hx hy hle

/-! ## §13.21 Unification Bridges to Chapters 11 and 12 (`hyperrealFramework`) -/

/-- Helper over any `U : Ultrafilter I`: members of `(ultrapowerFramework U X).star (baseSet X)`
are precisely the atoms `Entity.atom x` (`x : Germ (U : Filter I) X`). -/
theorem mem_ultrapowerStar_baseSet_iff {I X : Type*} (U : Ultrafilter I)
    {y : Entity (Germ (U : Filter I) X)} :
    y ∈ (ultrapowerFramework U X).star (baseSet X) ↔
      ∃ x : Germ (U : Filter I) X, y = Entity.atom x := by
  let rRaw : RawStage X 1 := Sum.inr Set.univ
  have hr_eq : baseSet X = Entity.ofRaw rRaw := by
    refine Entity.set_ext (Entity.isSet_setOfBounded _) (Entity.isSet_ofRaw_inr _) fun e ↦ ?_
    rw [mem_baseSet_iff, Entity.mem_ofRaw_inr]
    exact ⟨fun ⟨r, he⟩ ↦ ⟨r, trivial, he⟩, fun ⟨r, _, he⟩ ↦ ⟨r, he⟩⟩
  change y ∈ ultrapowerStar U (baseSet X) ↔ _
  rw [hr_eq, ultrapowerStar_ofRaw,
    mem_collapseStage_of_eventually_inr U (Filter.Eventually.of_forall fun _ ↦ rfl)]
  constructor
  · rintro ⟨u, rfl, _⟩
    exact ⟨((show I → X from u) : Germ (U : Filter I) X), rfl⟩
  · rintro ⟨x, rfl⟩
    refine Germ.inductionOn x fun u ↦ ?_
    exact ⟨show I → RawStage X 0 from u, rfl, Filter.Eventually.of_forall fun _ ↦ trivial⟩

/-- Membership in `hyperrealFramework.star realEntity`: its members are precisely the hyperreal
atoms `Entity.atom x` (`x : ℝ*`; Goldblatt §13.8–13.9, pp. 168–171). -/
@[simp]
theorem mem_hyperrealFramework_star_realEntity_iff {y : Entity ℝ*} :
    y ∈ hyperrealFramework.star realEntity ↔ ∃ x : ℝ*, y = Entity.atom x :=
  mem_ultrapowerStar_baseSet_iff (hyperfilter ℕ)

/-- Extract the underlying subset `{x : ℝ* | Entity.atom x ∈ B} ⊆ ℝ*` from an entity `B : Entity ℝ*`. -/
def entityToHyperrealSet (B : Entity ℝ*) : Set ℝ* :=
  {x : ℝ* | Entity.atom x ∈ B}

/-- Round-trip identity `entityToHyperrealSet (mkAtomSet X) = X` for any `X : Set ℝ*`. -/
@[simp]
theorem entityToHyperrealSet_mkAtomSet (X : Set ℝ*) :
    entityToHyperrealSet (mkAtomSet X) = X := by
  ext x; simp [entityToHyperrealSet]

/-- General ultrapower set bridge over any `U : Ultrafilter I`: `mkAtomSet S` belongs to
`(ultrapowerFramework U X).star (Entity.powerset (baseSet X))` iff `S` is of the form
`{x : Germ U X | Germ.LiftRel (· ∈ ·) x ↑A}` for some `A : I → Set X`. -/
theorem mkAtomSet_mem_ultrapowerStar_powerset_iff {I X : Type*} (U : Ultrafilter I)
    (S : Set (Germ (U : Filter I) X)) :
    mkAtomSet S ∈ (ultrapowerFramework U X).star (Entity.powerset (baseSet X)) ↔
      ∃ A : I → Set X, S =
        {x : Germ (U : Filter I) X | Germ.LiftRel (· ∈ ·) x (A : Germ (U : Filter I) (Set X))} := by
  rw [(ultrapowerFramework U X).mem_star_powerset_iff]
  have hsub : mkAtomSet S ∈ Entity.powerset ((ultrapowerFramework U X).star (baseSet X)) := by
    refine Entity.mem_powerset_iff.2 ⟨Entity.isSet_setOfBounded _, fun y hy ↦ ?_⟩
    obtain ⟨x, _, rfl⟩ := mem_mkAtomSet_iff.1 hy
    exact (mem_ultrapowerStar_baseSet_iff U).2 ⟨x, rfl⟩
  simp only [hsub, true_and]
  constructor
  · intro hInt
    obtain ⟨m, g, hEq⟩ :=
      (exists_mem_ultrapowerStar_iff_exists_collapseStage U (mkAtomSet S)).1 hInt
    let A : I → Set X := fun i ↦ {r : X | Entity.atom r ∈ Entity.ofRaw (g i)}
    refine ⟨A, ?_⟩
    ext x
    refine Germ.inductionOn x fun r ↦ ?_
    change (r : Germ (U : Filter I) X) ∈ S ↔
      Germ.LiftRel (· ∈ ·) (r : Germ (U : Filter I) X) (A : Germ (U : Filter I) (Set X))
    rw [Germ.liftRel_coe, ← atom_mem_mkAtomSet_iff, hEq]
    exact collapseStage_coe_mem_iff U (m := 0) r g
  · rintro ⟨A, rfl⟩
    let g : I → RawStage X 1 := fun i ↦ Sum.inr (A i)
    have hg_inr : ∀ᶠ i in (U : Filter I), g i = Sum.inr (A i) :=
      Filter.Eventually.of_forall fun _ ↦ rfl
    let B := collapseStage U 1 (g : Germ (U : Filter I) (RawStage X 1))
    have hB_int : (ultrapowerFramework U X).IsInternalEntity B :=
      (exists_mem_ultrapowerStar_iff_exists_collapseStage U B).2 ⟨1, g, rfl⟩
    have hEq : mkAtomSet {x : Germ (U : Filter I) X |
        Germ.LiftRel (· ∈ ·) x (A : Germ (U : Filter I) (Set X))} = B := by
      refine Entity.set_ext (Entity.isSet_setOfBounded _)
        (isSet_collapseStage_of_eventually_inr U hg_inr) fun y ↦ ?_
      rw [mem_collapseStage_of_eventually_inr U hg_inr]
      constructor
      · intro hy
        obtain ⟨x, hxA, rfl⟩ := mem_mkAtomSet_iff.1 hy
        refine Germ.inductionOn x (fun r hxr ↦ ?_) hxA
        exact ⟨show I → RawStage X 0 from r, rfl, Germ.liftRel_coe.1 hxr⟩
      · rintro ⟨u, rfl, hu⟩
        change Entity.atom ((show I → X from u) : Germ (U : Filter I) X) ∈ _
        exact atom_mem_mkAtomSet_iff.2
          (Germ.liftRel_coe.2 (hu : ∀ᶠ i in (U : Filter I), (show I → X from u) i ∈ A i))
    exact hEq ▸ hB_int

/-- **Chapter 11 ↔ Chapter 13 Bridge (`Goldblatt.IsInternal`)**:
A subset `X : Set ℝ*` is internal in the ultrapower sense of Chapter 11 (`Goldblatt.IsInternal X`,
i.e., `X = [A_n]`) **if and only if** its superstructure entity `mkAtomSet X : Entity ℝ*` belongs to
`hyperrealFramework.star (Entity.powerset realEntity)` (Goldblatt §11.1 & §13.10–13.12,
pp. 125, 172–176). -/
theorem isInternal_iff_mkAtomSet_mem_star_powerset (X : Set ℝ*) :
    Goldblatt.IsInternal X ↔
      mkAtomSet X ∈ hyperrealFramework.star (Entity.powerset realEntity) :=
  (mkAtomSet_mem_ultrapowerStar_powerset_iff (hyperfilter ℕ) X).symm

/-- General ultrapower hyperfiniteness bridge over any `U : Ultrafilter I`: `mkAtomSet S` belongs
to `(ultrapowerFramework U X).star (Entity.finPowerset (baseSet X))` iff `S` is of the form
`{x : Germ U X | Germ.LiftRel (· ∈ ·) x ↑A}` with `∀ᶠ i in U, (A i).Finite`. -/
theorem mkAtomSet_mem_ultrapowerStar_finPowerset_iff {I X : Type*} (U : Ultrafilter I)
    (S : Set (Germ (U : Filter I) X)) :
    mkAtomSet S ∈ (ultrapowerFramework U X).star (Entity.finPowerset (baseSet X)) ↔
      ∃ A : I → Set X,
        S = {x : Germ (U : Filter I) X |
          Germ.LiftRel (· ∈ ·) x (A : Germ (U : Filter I) (Set X))} ∧
        ∀ᶠ i in (U : Filter I), (A i).Finite := by
  obtain ⟨⟨mF, rawF⟩, hrawF⟩ := Quotient.exists_rep (Entity.finPowerset (baseSet X))
  have hstarF : (ultrapowerFramework U X).star (Entity.finPowerset (baseSet X)) =
      collapseStage U mF ((fun _ : I ↦ rawF) : Germ (U : Filter I) (RawStage X mF)) := by
    change ultrapowerStar U (Entity.finPowerset (baseSet X)) = _
    rw [← hrawF]
    exact ultrapowerStar_ofRaw U rawF
  have hofRawF : Entity.ofRaw rawF = Entity.finPowerset (baseSet X) := hrawF
  constructor
  · intro hmem
    have hInt : (ultrapowerFramework U X).IsInternalEntity (mkAtomSet S) :=
      ⟨Entity.finPowerset (baseSet X), hmem⟩
    obtain ⟨m, g, hEq⟩ :=
      (exists_mem_ultrapowerStar_iff_exists_collapseStage U (mkAtomSet S)).1 hInt
    let A : I → Set X := fun i ↦ {r : X | Entity.atom r ∈ Entity.ofRaw (g i)}
    have hS_eq : S = {x : Germ (U : Filter I) X |
        Germ.LiftRel (· ∈ ·) x (A : Germ (U : Filter I) (Set X))} := by
      ext x
      refine Germ.inductionOn x fun r ↦ ?_
      change (r : Germ (U : Filter I) X) ∈ S ↔
        Germ.LiftRel (· ∈ ·) (r : Germ (U : Filter I) X) (A : Germ (U : Filter I) (Set X))
      rw [Germ.liftRel_coe, ← atom_mem_mkAtomSet_iff, hEq]
      exact collapseStage_coe_mem_iff U (m := 0) r g
    rw [hEq, hstarF] at hmem
    have hev := (collapseStage_coe_mem_iff U g (fun _ : I ↦ rawF)).1 hmem
    refine ⟨A, hS_eq, hev.mono fun i hi ↦ ?_⟩
    rw [hofRawF] at hi
    obtain ⟨_, _, hfin⟩ := Entity.mem_finPowerset_iff.1 hi
    exact hfin.preimage fun _ _ _ _ h ↦ Entity.atom_inj.1 h
  · rintro ⟨A, rfl, hev_fin⟩
    let A' : I → Set X := fun i ↦ if (A i).Finite then A i else ∅
    have hev_eq : ∀ᶠ i in (U : Filter I), A' i = A i :=
      hev_fin.mono fun i hi ↦ by simp [A', hi]
    have hS_eq : {x : Germ (U : Filter I) X |
        Germ.LiftRel (· ∈ ·) x (A : Germ (U : Filter I) (Set X))} =
        {x : Germ (U : Filter I) X |
          Germ.LiftRel (· ∈ ·) x (A' : Germ (U : Filter I) (Set X))} := by
      rw [Germ.coe_eq.2 hev_eq]
    rw [hS_eq, hstarF]
    let g : I → RawStage X 1 := fun i ↦ Sum.inr (A' i)
    have hg_inr : ∀ᶠ i in (U : Filter I), g i = Sum.inr (A' i) :=
      Filter.Eventually.of_forall fun _ ↦ rfl
    have hEq : mkAtomSet {x : Germ (U : Filter I) X |
        Germ.LiftRel (· ∈ ·) x (A' : Germ (U : Filter I) (Set X))} =
        collapseStage U 1 (g : Germ (U : Filter I) (RawStage X 1)) := by
      refine Entity.set_ext (Entity.isSet_setOfBounded _)
        (isSet_collapseStage_of_eventually_inr U hg_inr) fun y ↦ ?_
      rw [mem_collapseStage_of_eventually_inr U hg_inr]
      constructor
      · intro hy
        obtain ⟨x, hxA, rfl⟩ := mem_mkAtomSet_iff.1 hy
        refine Germ.inductionOn x (fun r hxr ↦ ?_) hxA
        exact ⟨show I → RawStage X 0 from r, rfl, Germ.liftRel_coe.1 hxr⟩
      · rintro ⟨u, rfl, hu⟩
        change Entity.atom ((show I → X from u) : Germ (U : Filter I) X) ∈ _
        exact atom_mem_mkAtomSet_iff.2
          (Germ.liftRel_coe.2 (hu : ∀ᶠ i in (U : Filter I), (show I → X from u) i ∈ A' i))
    rw [hEq]
    refine (collapseStage_coe_mem_iff U g (fun _ : I ↦ rawF)).2
      (Filter.Eventually.of_forall fun i ↦ ?_)
    rw [hofRawF]
    have hfinA' : (A' i).Finite := by
      by_cases h : (A i).Finite <;> simp [A', h]
    refine Entity.mem_finPowerset_iff.2 ⟨Entity.isSet_ofRaw_inr _, fun e he ↦ ?_, ?_⟩
    · obtain ⟨r, _, rfl⟩ := Entity.mem_ofRaw_inr.1 he
      exact mem_baseSet_iff.2 ⟨r, rfl⟩
    · refine (hfinA'.image Entity.atom).subset fun e he ↦ ?_
      obtain ⟨r, hr, rfl⟩ := Entity.mem_ofRaw_inr.1 he
      exact ⟨r, hr, rfl⟩

/-- **Chapter 12 ↔ Chapter 13 Bridge (`Goldblatt.IsHyperfinite`)**:
A subset `X : Set ℝ*` is hyperfinite in the ultrapower sense of Chapter 12
(`Goldblatt.IsHyperfinite X`, i.e., `X = [A_n]` with `A_n` almost everywhere finite) **if and only if**
`mkAtomSet X ∈ hyperrealFramework.star (Entity.finPowerset realEntity)`
(Goldblatt §12.3 & §13.17, pp. 149, 178). -/
theorem isHyperfinite_iff_mkAtomSet_mem_star_finPowerset (X : Set ℝ*) :
    Goldblatt.IsHyperfinite X ↔
      mkAtomSet X ∈ hyperrealFramework.star (Entity.finPowerset realEntity) :=
  (mkAtomSet_mem_ultrapowerStar_finPowerset_iff (hyperfilter ℕ) X).symm

/-- Embed a partial map `(D, fn)` on a type `Z` (with fallback value `d₀ : Z`) as a set-theoretic
function entity in `Entity Z`. -/
def partialMapToEntity {Z : Type*} (d₀ : Z) (D : Set Z) (fn : Z → Z) : Entity Z :=
  Entity.mkFuncEntity (mkAtomSet D) (fun e ↦ Entity.atom (fn (Entity.atomVal d₀ e)))

/-- Membership of ordered atom pairs in `partialMapToEntity d₀ D fn`. -/
@[simp]
theorem kpair_atom_mem_partialMapToEntity_iff {Z : Type*} {d₀ : Z} {D : Set Z} {fn : Z → Z}
    {x y : Z} :
    Entity.kpair (Entity.atom x) (Entity.atom y) ∈ partialMapToEntity d₀ D fn ↔
      x ∈ D ∧ y = fn x := by
  have hfn : Entity.IsFuncFromTo (partialMapToEntity d₀ D fn) (mkAtomSet D) (baseSet Z) :=
    Entity.isFuncFromTo_mkFuncEntity fun _ _ ↦ mem_baseSet_iff.2 ⟨_, rfl⟩
  rw [Entity.kpair_mem_iff_funcApp_eq hfn.isFuncEntity,
      hfn.relDom_eq (Entity.isSet_setOfBounded _), atom_mem_mkAtomSet_iff]
  refine and_congr_right fun hx ↦ ?_
  have hv := Entity.funcApp_mkFuncEntity (B := baseSet Z)
    (g := fun e ↦ Entity.atom (fn (Entity.atomVal d₀ e)))
    (fun _ _ ↦ mem_baseSet_iff.2 ⟨_, rfl⟩) (atom_mem_mkAtomSet_iff.2 hx)
  rw [partialMapToEntity, hv, Entity.atomVal_atom, Entity.atom_inj, eq_comm]

/-- Embed a `Goldblatt.RealPartialFun` as a rank-`3` function entity in `Entity ℝ`
(Goldblatt §12.1 & §13.3, pp. 147, 160). -/
def realPartialFunToEntity (f : Goldblatt.RealPartialFun) : Entity ℝ :=
  partialMapToEntity 0 f.dom f.apply

/-- Embed a `Goldblatt.InternalPartialFun` as a set-theoretic function entity in `Entity ℝ*`
(Goldblatt §12.1 & §13.3, pp. 147, 160). -/
def partialFunToEntity (F : Goldblatt.InternalPartialFun) : Entity ℝ* :=
  partialMapToEntity 0 F.dom F.apply

/-- Membership of ordered atom pairs in `realPartialFunToEntity f`. -/
@[simp]
theorem kpair_atom_mem_realPartialFunToEntity_iff {f : Goldblatt.RealPartialFun} {r s : ℝ} :
    Entity.kpair (Entity.atom r) (Entity.atom s) ∈ realPartialFunToEntity f ↔
      r ∈ f.dom ∧ s = f.apply r :=
  kpair_atom_mem_partialMapToEntity_iff

/-- Membership of ordered atom pairs in `partialFunToEntity F`. -/
@[simp]
theorem kpair_atom_mem_partialFunToEntity_iff {F : Goldblatt.InternalPartialFun} {x y : ℝ*} :
    Entity.kpair (Entity.atom x) (Entity.atom y) ∈ partialFunToEntity F ↔
      x ∈ F.dom ∧ y = F.apply x :=
  kpair_atom_mem_partialMapToEntity_iff

/-- General ultrapower partial-function internality bridge over any `U : Ultrafilter ℕ`:
`partialMapToEntity d₀ D fn` is internal in `ultrapowerFramework U ℝ` iff `(D, fn)` arises from a
sequence `f : ℕ → Goldblatt.RealPartialFun` via `Germ.LiftRel` and `Germ.map₂`. -/
theorem isInternalEntity_partialMapToEntity_iff (U : Ultrafilter ℕ)
    (d₀ : Germ (U : Filter ℕ) ℝ) (D : Set (Germ (U : Filter ℕ) ℝ))
    (fn : Germ (U : Filter ℕ) ℝ → Germ (U : Filter ℕ) ℝ) :
    (ultrapowerFramework U ℝ).IsInternalEntity (partialMapToEntity d₀ D fn) ↔
      ∃ f : ℕ → Goldblatt.RealPartialFun,
        D = {x : Germ (U : Filter ℕ) ℝ |
          Germ.LiftRel (· ∈ ·) x ((fun n ↦ (f n).dom) : Germ (U : Filter ℕ) (Set ℝ))} ∧
        ∀ x ∈ D, fn x =
          Germ.map₂ Goldblatt.RealPartialFun.apply
            (f : Germ (U : Filter ℕ) Goldblatt.RealPartialFun) x := by
  constructor
  · intro hInt
    obtain ⟨N, g, hEq⟩ :=
      (exists_mem_ultrapowerStar_iff_exists_collapseStage U (partialMapToEntity d₀ D fn)).1 hInt
    have hF_fn : Entity.IsFuncFromTo (partialMapToEntity d₀ D fn)
        (mkAtomSet D) (baseSet (Germ (U : Filter ℕ) ℝ)) :=
      Entity.isFuncFromTo_mkFuncEntity fun _ _ ↦ mem_baseSet_iff.2 ⟨_, rfl⟩
    have hev_fn : ∀ᶠ n in (U : Filter ℕ), (Entity.ofRaw (g n)).IsFuncEntity :=
      (collapseStage_isFuncEntity_iff U g).1 (hEq ▸ hF_fn.isFuncEntity)
    let f : ℕ → Goldblatt.RealPartialFun := fun n ↦
      Goldblatt.RealPartialFun.mkPartial
        {r : ℝ | ∃ s : ℝ, Entity.kpair (Entity.atom r) (Entity.atom s) ∈ Entity.ofRaw (g n)}
        (fun r ↦ Entity.atomVal 0 (Entity.funcApp (Entity.ofRaw (g n)) (Entity.atom r)))
    refine ⟨f, ?_, ?_⟩
    · ext x
      refine Germ.inductionOn x fun r ↦ ?_
      change (r : Germ (U : Filter ℕ) ℝ) ∈ D ↔
        Germ.LiftRel (· ∈ ·) (r : Germ (U : Filter ℕ) ℝ)
          ((fun n ↦ (f n).dom) : Germ (U : Filter ℕ) (Set ℝ))
      rw [Germ.liftRel_coe]
      constructor
      · intro hxr
        obtain ⟨s, hs_eq⟩ : ∃ s : ℕ → ℝ,
            (s : Germ (U : Filter ℕ) ℝ) = fn (r : Germ (U : Filter ℕ) ℝ) :=
          Germ.inductionOn (fn (r : Germ (U : Filter ℕ) ℝ)) fun s ↦ ⟨s, rfl⟩
        have hp : Entity.kpair
            (Entity.atom (r : Germ (U : Filter ℕ) ℝ))
            (Entity.atom (s : Germ (U : Filter ℕ) ℝ)) ∈ partialMapToEntity d₀ D fn :=
          kpair_atom_mem_partialMapToEntity_iff.2 ⟨hxr, hs_eq⟩
        rw [hEq] at hp
        have hev :=
          (kpair_collapseStage_mem_iff U (X := ℝ) (ma := 0) (mb := 0) r s g).1 hp
        exact hev.mono fun n hn ↦ ⟨s n, hn⟩
      · intro hev
        let s : ℕ → ℝ := fun n ↦
          if h : ∃ s' : ℝ,
              Entity.kpair (Entity.atom (r n)) (Entity.atom s') ∈ Entity.ofRaw (g n) then
            h.choose
          else 0
        have hev_p : ∀ᶠ n in (U : Filter ℕ),
            Entity.kpair (Entity.atom (r n)) (Entity.atom (s n)) ∈ Entity.ofRaw (g n) :=
          hev.mono fun n hn ↦ by
            have hn' : ∃ s' : ℝ,
                Entity.kpair (Entity.atom (r n)) (Entity.atom s') ∈ Entity.ofRaw (g n) := hn
            simp only [s, hn', ↓reduceDIte]
            exact hn'.choose_spec
        have hp : Entity.kpair
            (Entity.atom (r : Germ (U : Filter ℕ) ℝ))
            (Entity.atom (s : Germ (U : Filter ℕ) ℝ)) ∈ partialMapToEntity d₀ D fn := by
          rw [hEq]
          exact (kpair_collapseStage_mem_iff U (X := ℝ) (ma := 0) (mb := 0) r s g).2 hev_p
        exact (kpair_atom_mem_partialMapToEntity_iff.1 hp).1
    · intro x hx
      obtain ⟨r, rfl⟩ : ∃ r : ℕ → ℝ, (r : Germ (U : Filter ℕ) ℝ) = x :=
        Germ.inductionOn x fun r ↦ ⟨r, rfl⟩
      obtain ⟨s, hs_eq⟩ : ∃ s : ℕ → ℝ,
          (s : Germ (U : Filter ℕ) ℝ) = fn (r : Germ (U : Filter ℕ) ℝ) :=
        Germ.inductionOn (fn (r : Germ (U : Filter ℕ) ℝ)) fun s ↦ ⟨s, rfl⟩
      rw [← hs_eq]
      have hp : Entity.kpair
          (Entity.atom (r : Germ (U : Filter ℕ) ℝ))
          (Entity.atom (s : Germ (U : Filter ℕ) ℝ)) ∈ partialMapToEntity d₀ D fn :=
        kpair_atom_mem_partialMapToEntity_iff.2 ⟨hx, hs_eq⟩
      rw [hEq] at hp
      have hev :=
        (kpair_collapseStage_mem_iff U (X := ℝ) (ma := 0) (mb := 0) r s g).1 hp
      refine Germ.coe_eq.2 ((hev.and hev_fn).mono fun n ⟨hn, hfni⟩ ↦ ?_)
      have hr_dom : r n ∈ {r' : ℝ |
          ∃ s' : ℝ, Entity.kpair (Entity.atom r') (Entity.atom s') ∈ Entity.ofRaw (g n)} :=
        ⟨s n, hn⟩
      change s n = (f n).apply (r n)
      rw [Goldblatt.RealPartialFun.mkPartial_apply_of_mem hr_dom]
      have happ : Entity.funcApp (Entity.ofRaw (g n)) (Entity.atom (r n)) = Entity.atom (s n) :=
        ((Entity.kpair_mem_iff_funcApp_eq hfni).1 hn).2
      rw [happ, Entity.atomVal_atom]
  · rintro ⟨f, hD_eq, hfn_eq⟩
    have hfn_n : ∀ n : ℕ,
        Entity.IsFuncFromTo (realPartialFunToEntity (f n)) (mkAtomSet (f n).dom) realEntity :=
      fun n ↦ Entity.isFuncFromTo_mkFuncEntity fun _ _ ↦ mem_baseSet_iff.2 ⟨_, rfl⟩
    have hf_sub : ∀ n : ℕ, (realPartialFunToEntity (f n)).extSet ⊆
        (Entity.prod realEntity realEntity).extSet := fun n p hp ↦ by
      obtain ⟨a, ha, b, hb, rfl⟩ := (hfn_n n).2.1 p hp
      obtain ⟨r, _, rfl⟩ := mem_mkAtomSet_iff.1 ha
      exact Entity.mem_prod_iff.2 ⟨Entity.atom r, mem_baseSet_iff.2 ⟨r, rfl⟩, b, hb, rfl⟩
    have hf_mem : ∀ n : ℕ, realPartialFunToEntity (f n) ∈ VStage ℝ 3 := fun n ↦
      subset_prod_mem_vStage_add_two (isSet_vStageEntity ℝ 0) (isSet_vStageEntity ℝ 0)
        (vStageEntity_mem_vStage_succ ℝ 0) (vStageEntity_mem_vStage_succ ℝ 0)
        (hfn_n n).1 (hf_sub n)
    let g : ℕ → RawStage ℝ 3 := fun n ↦ (realPartialFunToEntity (f n)).toRawAt 2
    have hg_raw : ∀ n : ℕ, Entity.ofRaw (g n) = realPartialFunToEntity (f n) :=
      fun n ↦ Entity.ofRaw_toRawAt (hf_mem n)
    let G := collapseStage U 3 (g : Germ (U : Filter ℕ) (RawStage ℝ 3))
    have hG_int : (ultrapowerFramework U ℝ).IsInternalEntity G :=
      (exists_mem_ultrapowerStar_iff_exists_collapseStage U G).2 ⟨3, g, rfl⟩
    obtain ⟨⟨mP, rawP⟩, hrawP⟩ :=
      Quotient.exists_rep (Entity.powerset (Entity.prod realEntity realEntity))
    have hG_P : G ∈ (ultrapowerFramework U ℝ).star
        (Entity.powerset (Entity.prod realEntity realEntity)) := by
      have hstarP : (ultrapowerFramework U ℝ).star
          (Entity.powerset (Entity.prod realEntity realEntity)) =
          collapseStage U mP ((fun _ : ℕ ↦ rawP) : Germ (U : Filter ℕ) (RawStage ℝ mP)) := by
        change ultrapowerStar U (Entity.powerset (Entity.prod realEntity realEntity)) = _
        rw [← hrawP]
        exact ultrapowerStar_ofRaw U rawP
      rw [hstarP]
      refine (collapseStage_coe_mem_iff U g (fun _ : ℕ ↦ rawP)).2
        (Filter.Eventually.of_forall fun n ↦ ?_)
      rw [hg_raw n, show Entity.ofRaw rawP =
        Entity.powerset (Entity.prod realEntity realEntity) from hrawP]
      exact Entity.mem_powerset_iff.2 ⟨(hfn_n n).1, fun p hp ↦ hf_sub n hp⟩
    obtain ⟨hG_sub, _⟩ := (ultrapowerFramework U ℝ).mem_star_powerset_iff.1 hG_P
    rw [(ultrapowerFramework U ℝ).star_prod] at hG_sub
    obtain ⟨hG_set, hG_prod⟩ := Entity.mem_powerset_iff.1 hG_sub
    have hF_fn : Entity.IsFuncFromTo (partialMapToEntity d₀ D fn)
        (mkAtomSet D) (baseSet (Germ (U : Filter ℕ) ℝ)) :=
      Entity.isFuncFromTo_mkFuncEntity fun _ _ ↦ mem_baseSet_iff.2 ⟨_, rfl⟩
    have hEq : partialMapToEntity d₀ D fn = G := by
      refine Entity.set_ext hF_fn.1 hG_set fun p ↦ ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
      · obtain ⟨a, ha, b, hb, rfl⟩ := hF_fn.2.1 p hp
        obtain ⟨x, _, rfl⟩ := mem_mkAtomSet_iff.1 ha
        obtain ⟨y, rfl⟩ := mem_baseSet_iff.1 hb
        obtain ⟨hx_dom, rfl⟩ := kpair_atom_mem_partialMapToEntity_iff.1 hp
        rw [hfn_eq x hx_dom]
        have hx_lift : Germ.LiftRel (· ∈ ·) x
            ((fun n ↦ (f n).dom) : Germ (U : Filter ℕ) (Set ℝ)) := by
          rw [hD_eq] at hx_dom; exact hx_dom
        refine Germ.inductionOn x (fun r hxr ↦ ?_) hx_lift
        have hev_dom : ∀ᶠ n in (U : Filter ℕ), r n ∈ (f n).dom := Germ.liftRel_coe.1 hxr
        refine (kpair_collapseStage_mem_iff U (X := ℝ) (ma := 0) (mb := 0)
          r (fun n ↦ (f n).apply (r n)) g).2 ?_
        refine hev_dom.mono fun n hn ↦ ?_
        rw [hg_raw n]
        exact kpair_atom_mem_realPartialFunToEntity_iff.2 ⟨hn, rfl⟩
      · obtain ⟨a, ha, b, hb, rfl⟩ := Entity.mem_prod_iff.1 (hG_prod p hp)
        obtain ⟨x, rfl⟩ := (mem_ultrapowerStar_baseSet_iff U).1 ha
        obtain ⟨y, rfl⟩ := (mem_ultrapowerStar_baseSet_iff U).1 hb
        refine Germ.inductionOn x (fun r hpr ↦ ?_) hp
        refine Germ.inductionOn y (fun s hprs ↦ ?_) hpr
        have hev :=
          (kpair_collapseStage_mem_iff U (X := ℝ) (ma := 0) (mb := 0) r s g).1 hprs
        have hev' : ∀ᶠ n in (U : Filter ℕ), r n ∈ (f n).dom ∧ s n = (f n).apply (r n) :=
          hev.mono fun n hn ↦ by
            rw [hg_raw n] at hn
            exact kpair_atom_mem_realPartialFunToEntity_iff.1 hn
        obtain ⟨hev_d, hev_s⟩ := Filter.eventually_and.1 hev'
        have hx_dom : (r : Germ (U : Filter ℕ) ℝ) ∈ D := by
          rw [hD_eq]; exact Germ.liftRel_coe.2 hev_d
        refine kpair_atom_mem_partialMapToEntity_iff.2 ⟨hx_dom, ?_⟩
        rw [hfn_eq _ hx_dom]
        exact Germ.coe_eq.2 hev_s
    exact hEq ▸ hG_int

/-- **Chapter 12 ↔ Chapter 13 Bridge (`Goldblatt.IsInternalFun`)**:
A partial hyperreal function `F : Goldblatt.InternalPartialFun` is internal in the ultrapower sense
of Chapter 12 (`Goldblatt.IsInternalFun F`, i.e., `F = [f_n]`) **if and only if** its graph entity
`partialFunToEntity F` is an internal entity of `hyperrealFramework`
(Goldblatt §12.1 & §13.10–13.13, pp. 147, 172–176). -/
theorem isInternalFun_iff_isInternalEntity_partialFunToEntity (F : Goldblatt.InternalPartialFun) :
    Goldblatt.IsInternalFun F ↔
      hyperrealFramework.IsInternalEntity (partialFunToEntity F) :=
  (exists_congr fun _ ↦ Goldblatt.InternalPartialFun.eq_iff_dom_and_eqOn).trans
    (isInternalEntity_partialMapToEntity_iff (hyperfilter ℕ) (0 : ℝ*) F.dom F.apply).symm

/-- Helper over any `U : Ultrafilter ℕ`: when `D = Set.univ`, `partialMapToEntity d₀ D fn` belongs
to `(ultrapowerFramework U ℝ).star (Entity.funSpace realEntity realEntity)` iff it is internal. -/
theorem partialMapToEntity_mem_ultrapowerStar_funSpace_iff_of_univ (U : Ultrafilter ℕ)
    (d₀ : Germ (U : Filter ℕ) ℝ) {D : Set (Germ (U : Filter ℕ) ℝ)}
    (hD : D = Set.univ) (fn : Germ (U : Filter ℕ) ℝ → Germ (U : Filter ℕ) ℝ) :
    partialMapToEntity d₀ D fn ∈
      (ultrapowerFramework U ℝ).star (Entity.funSpace realEntity realEntity) ↔
      (ultrapowerFramework U ℝ).IsInternalEntity (partialMapToEntity d₀ D fn) := by
  rw [(ultrapowerFramework U ℝ).mem_star_funSpace_iff]
  have hdom_eq : mkAtomSet D = (ultrapowerFramework U ℝ).star realEntity := by
    refine Entity.set_ext (Entity.isSet_setOfBounded _)
      ((ultrapowerFramework U ℝ).isSet_star_iff.2 (isSet_vStageEntity ℝ 0)) fun y ↦ ?_
    rw [mem_mkAtomSet_iff, realEntity, mem_ultrapowerStar_baseSet_iff U, hD]
    exact ⟨fun ⟨x, _, hy⟩ ↦ ⟨x, hy⟩, fun ⟨x, hy⟩ ↦ ⟨x, Set.mem_univ x, hy⟩⟩
  have hfn : Entity.IsFuncFromTo (partialMapToEntity d₀ D fn)
      (mkAtomSet D) ((ultrapowerFramework U ℝ).star realEntity) :=
    Entity.isFuncFromTo_mkFuncEntity fun _ _ ↦ by
      rw [realEntity, mem_ultrapowerStar_baseSet_iff U]
      exact ⟨_, rfl⟩
  rw [hdom_eq] at hfn
  exact ⟨And.right, fun hInt ↦ ⟨hfn, hInt⟩⟩

/-- **Chapter 12 ↔ Chapter 13 Bridge for Total Functions (`*(ℝ^ℝ)`)**:
A total hyperreal function `F : Goldblatt.InternalPartialFun` (`F.dom = Set.univ`) is internal in
the ultrapower sense of Chapter 12 (`Goldblatt.IsInternalFun F`) **if and only if** its graph entity
`partialFunToEntity F` belongs to `hyperrealFramework.star (Entity.funSpace realEntity realEntity)`
(Goldblatt §12.1 & Exercise 13.13(3), pp. 147, 176). -/
theorem isInternalFun_total_iff_mem_star_funSpace {F : Goldblatt.InternalPartialFun}
    (hdom : F.dom = Set.univ) :
    Goldblatt.IsInternalFun F ↔
      partialFunToEntity F ∈ hyperrealFramework.star (Entity.funSpace realEntity realEntity) :=
  (isInternalFun_iff_isInternalEntity_partialFunToEntity F).trans
    (partialMapToEntity_mem_ultrapowerStar_funSpace_iff_of_univ
      (hyperfilter ℕ) (0 : ℝ*) hdom F.apply).symm

end Goldblatt.Ch13
end


