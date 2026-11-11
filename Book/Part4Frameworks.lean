import VersoManual
import Book.Meta
import LecturesOnTheHyperreals.Ch13_UniversesFrameworks
import LecturesOnTheHyperreals.Ch14_Enlargements
import LecturesOnTheHyperreals.Ch15_PermanenceSaturation

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 400000
set_option linter.verso.markup.emph false

#doc (Manual) "Part IV — Nonstandard Frameworks, Enlargements & Saturation" =>
%%%
tag := "part-4-frameworks"
file := "part-4-frameworks"
%%%

Parts I–III focused on real numbers, subsets of $`\mathbb{R}`, and functions $`\mathbb{R} \to \mathbb{R}`. But modern mathematics also quantifies over **topologies** (sets of sets of points), **measures** (functions from sets of sets to $`\mathbb{R}`), **Banach spaces** and their **dual spaces**, **Boolean algebras**, and **infinite graphs**. How do we extend *all* higher-order structures over any base set $`X` simultaneously with a single `*-transform`?

Part IV answers this with Abraham Robinson and Elias Zakon's **Superstructure Framework**, constructs **Enlargements** via fine ultrafilters over finite subsets, and proves the equivalence between **Saturation**, **Permanence**, and **Comprehensiveness**.

```spatial3d (model := "superstructure_cone") (title := "3D Stage IV · Zakon Cumulative Superstructure V(ℝ) → V(*ℝ)")
Left: stacked golden ranks <code>V₀(ℝ) ⊂ V₁(ℝ) ⊂ V₂(ℝ) ⊂ V₃(ℝ)</code> of standard mathematics. Right: the nonstandard superstructure <code>V(*ℝ)</code> splits into the sapphire internal sub-cone <code>*V(ℝ)</code>—linked by luminous golden <code>*-transfer</code> arches—and the violet outer cage of external entities (<code>ℝ</code>, <code>ℕ</code>, <code>𝕃</code>, <code>𝕀</code>, and Loeb measurable sets).
```

# Chapter 13: Zakon Superstructures & $`\Delta_0` Transfer
%%%
tag := "ch13-superstructures"
file := "ch13-superstructures"
%%%

Given a base set $`X` of *individuals* (urelements), the **cumulative superstructure** $`V(X)` builds every finite-rank set-theoretic object over $`X`:

$$`V_0(X) = X, \qquad V_{n+1}(X) = V_n(X) \cup \mathcal{P}\bigl(V_n(X)\bigr), \qquad V(X) = \bigcup_{n \in \mathbb{N}} V_n(X).`

Using Kuratowski ordered pairs $`(a, b) = \{\{a\}, \{a, b\}\}`, relations and functions on $`V_n(X)` reside cleanly inside $`V_{n+3}(X)`. A **Nonstandard Framework** for $`X` consists of a map $`a \mapsto {}^*a` from $`V(X)` into $`V({}^*X)` satisfying **Łoś / Zakon Bounded-Quantifier ($`\Delta_0`) Transfer**: every formula whose quantifiers are bounded to entities $`\forall x \in A` or $`\exists x \in A` holds in $`V(X)` **iff** its `*-transform` holds in $`V({}^*X)`!

```svgCard (src := "static/diagrams/ch13_superstructure_transfer.svg") (alt := "Zakon Cumulative Superstructures and Bounded-Quantifier Transfer")
<strong>Figure IV.1 — Ranks of the Superstructure.</strong> Points live at rank 0, subsets at rank 1, relations and functions at rank 2–3, and topologies, σ-algebras, and dual spaces at rank 3–4. An element <code>B ∈ V(*X)</code> is <em>internal</em> iff <code>B ∈ *A</code> for some standard <code>A ∈ V(X)</code>; internal sets are closed under every definable <code>Δ₀</code> comprehension operation.
```

In [`Ch13_UniversesFrameworks.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch13_UniversesFrameworks.lean) (our largest module at **12,047 lines**), we formalize the full quotient construction of `Entity X` from `RawStage X m`, Kuratowski pairs and $`n`-tuples, internal set comprehension, the Zakon collapsed ultrapower framework, and the exact bridge proving that our Chapter 11–12 internal sets and partial functions coincide with internal entities in $`V(\mathbb{R}^*)`!

```lean
section
open Goldblatt.Ch13

-- Superstructure entities and agreement between Ch12 internal functions and V(ℝ*):
#check Entity
#check @isInternalFun_iff_isInternalEntity_partialFunToEntity
#check @isInternalFun_total_iff_mem_star_funSpace
end
```

# Chapter 14: Concurrent Relations & Enlargements
%%%
tag := "ch14-enlargements"
file := "ch14-enlargements"
%%%

Countable ultrapowers over $`\mathbb{N}` create unlimited numbers and infinitesimals for *countable* families of constraints—but what if $`X` is an uncountable topological space, a vast group, or an infinite-dimensional normed space?

A binary relation $`R` is **concurrent** (or *finitely satisfiable*) if for every finite collection $`x_1, \dots, x_k \in \mathrm{dom}(R)`, there exists some $`y` simultaneously satisfying $`R(x_1, y) \land \cdots \land R(x_k, y)`. A nonstandard framework is an **Enlargement** if for *every* concurrent relation $`R`, there exists a single nonstandard witness $`b` satisfying $`{}^*R({}^*x, b)` for **all** standard $`x \in \mathrm{dom}(R)` at once!

Look at what one enlargement witness $`b` gives immediately:

* Take $`R(x, F) :\iff x \in F \land F \text{ is finite}` on an infinite set $`A`: enlargement produces a **hyperfinite set** $`F^+ \subseteq {}^*A` containing $`{}^*x` for **every** standard element $`x \in A`!
* Take $`R(U, y) :\iff y \in U` on the open neighbourhoods $`U` of a point $`p` in any topological space: enlargement produces a point inside the **monad** $`\mu(p) = \bigcap_{U \in \mathcal{N}(p)} {}^*U`!

In [`Ch14_Enlargements.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch14_Enlargements.lean) (2,187 lines), we prove **Goldblatt's Theorem 14.3.1** by constructing a *fine ultrafilter* on the directed set $`I = \mathrm{Finset}(\mathcal{C})` of finite constraint sets (extending all upper cones $`\{i \in I : i_0 \subseteq i\}` via Zorn's Lemma), proving unconditionally that **every mathematical universe admits an enlargement** (`exists_enlargement`)!

```lean
section
open Goldblatt.Ch14

-- Fine ultrafilters and Goldblatt's Theorem 14.3.1 (Existence of Enlargements):
#check @isConcurrent_iff_hasFIP_slices
#check @theorem_14_3_1_single_concurrent
#check @theorem_14_3_1_hyperfinite_approx
#check @universalUltrapowerEnlargement_isEnlargement
#check @exists_enlargement
end
```

# Chapter 15: Permanence, Robinson's Lemma & $`\kappa`-Saturation
%%%
tag := "ch15-permanence-saturation"
file := "ch15-permanence-saturation"
%%%

While *Enlargement* simultaneously solves families of constraints over *standard* entities, many advanced constructions—especially Peter Loeb's measure theory (Ch. 16) and Banach nonstandard hulls (Ch. 18)—require solving families of constraints over **already-constructed internal entities**.

A framework is **$`\kappa`-saturated** if every family $`\mathcal{A}` of internal sets with the Finite Intersection Property and cardinality $`|\mathcal{A}| < \kappa` has nonempty intersection $`\bigcap \mathcal{A} \neq \emptyset`. In [`Ch15_PermanenceSaturation.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch15_PermanenceSaturation.lean) (3,156 lines), we prove:

* **Permanence Principles** (overflow and underflow across $`\mathbb{N}`, $`\mathbb{I}_+`, and $`\mathbb{L}`) and **Robinson's Sequential Lemma**: if an internal hypersequence $`(x_N)` satisfies $`x_n \approx_h 0` for every finite $`n \in \mathbb{N}`, then there exists an unlimited $`\nu \in \mathbb{N}^*_\infty` such that $`x_N \approx_h 0` for *all* $`N \le \nu`!
* **Saturation $`\iff` Comprehensiveness**: Countable ($`\aleph_1`-) saturation is equivalent to **countable comprehensiveness**—every sequence $`f : \mathbb{N} \to B` into an internal set $`B` extends to an *internal* function $`F : {}^*\mathbb{N} \to B` satisfying $`F(n) = f(n)` for all $`n \in \mathbb{N}`.
* **Exact Cardinalities**: Every infinite internal subset of $`\mathbb{R}^*` has cardinality at least $`\aleph_1` (in fact $`2^{\aleph_0}`), $`|\mathbb{R}^*| = 2^{\aleph_0}` equals the continuum, and therefore $`\mathbb{R}^*` is $`\aleph_1`-saturated while *not* $`(2^{\aleph_0})^+`-saturated!

```lean
section
open Goldblatt.Ch15

#check @permanence_posInfinitesimal_underflow
#check @countable_saturation_hyperreal_iff_concurrent_internalRel₂
#check @card_infinite_internal_hyperreal_ge_aleph_one
#check @card_hyperreal_eq_continuum
#check @not_succ_continuum_saturated_hyperreal
end
```
