import VersoManual
import Book.Meta
import LecturesOnTheHyperreals.Ch01_WhatAreTheHyperreals
import LecturesOnTheHyperreals.Ch02_LargeSets
import LecturesOnTheHyperreals.Ch03_UltrapowerConstruction
import LecturesOnTheHyperreals.Ch04_TransferPrinciple
import LecturesOnTheHyperreals.Ch05_HyperrealsGreatAndSmall

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 400000
set_option linter.verso.markup.emph false

#doc (Manual) "Part I — Foundations of the Hyperreal Line" =>
%%%
tag := "part-1-foundations"
file := "part-1-foundations"
%%%

Part I constructs the hyperreal ordered field $`\mathbb{R}^*` from scratch using sequences of real numbers modulo a nonprincipal ultrafilter on $`\mathbb{N}`, proves Łoś's bounded-quantifier Transfer Principle, and maps out the geometric anatomy of halos, galaxies, and the standard-part (*shadow*) homomorphism.

```svgCard (src := "static/diagrams/ch01_microscope_telescope.svg") (alt := "Anatomy of the Hyperreal Line: Galaxies, Halos, and the Shadow Quotient")
<strong>Figure I.1 — The Infinitesimal Microscope &amp; Infinite Telescope.</strong> Inside the principal galaxy <code>𝕃</code> of limited hyperreals, every real number <code>r</code> is surrounded by a cloud of infinitesimally close neighbours <code>hal(r) = r + 𝕀</code>. Beyond <code>𝕃</code> float disjoint galaxies <code>gal(±ω)</code> of unlimited hyperreals.
```

# Chapter 1: What Are the Hyperreals?
%%%
tag := "ch01-what-are-the-hyperreals"
file := "ch01-what-are-the-hyperreals"
%%%

When Gottfried Wilhelm Leibniz introduced differential calculus in 1684, he computed the slope of $`y = x^2` by adding a nonzero increment $`dx`, expanding

$$`\frac{(x + dx)^2 - x^2}{dx} = \frac{2x\,dx + (dx)^2}{dx} = 2x + dx,`

and then discarding $`dx` as “incomparably small” compared to $`2x`. George Berkeley famously mocked $`dx` in *The Analyst* (1734) as “the ghost of a departed quantity”: how can $`dx \neq 0` when we divide by it, yet $`dx = 0` at the end of the calculation?

Abraham Robinson resolved Berkeley's paradox in 1960 by embedding $`\mathbb{R}` into a genuine ordered field $`\mathbb{R}^*` that contains nonzero **infinitesimals**—elements $`\varepsilon` satisfying $`|\varepsilon| < r` for every positive real $`r \in \mathbb{R}`—while replacing the contradictory equality $`2x + dx = 2x` with **infinitesimal proximity** $`2x + dx \approx 2x`, from which a canonical ring homomorphism (`shadow`) extracts the unique real value $`2x`.

## Field-Agnostic Infinitesimal Arithmetic

In [`Ch01_WhatAreTheHyperreals.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch01_WhatAreTheHyperreals.lean), we first develop Goldblatt's §1.2–§1.4 axiomatic laws inside *any* strict ordered field extending $`\mathbb{R}` (`[Field F] [LinearOrder F] [IsStrictOrderedRing F]`). Even before constructing $`\mathbb{R}^*`, the order axioms alone force:

* $`0` is the **only** real number that is infinitesimal; if a subfield contains a nonzero infinitesimal $`\varepsilon`, its reciprocal $`\varepsilon^{-1}` is **infinite** (exceeding every standard real in absolute value), and the field cannot be Archimedean.
* Infinitesimals form an additive group closed under multiplication by any *limited* element, whereas $`\infty - \infty` and $`\varepsilon / \delta` remain genuinely indeterminate—for example, $`\varepsilon^2 / \varepsilon = \varepsilon \approx 0`, $`\varepsilon / \varepsilon = 1`, and $`\varepsilon / \varepsilon^2 = \varepsilon^{-1}` is unlimited.

Hover or tap any identifier in the live-elaborated Lean 4 block below to inspect its exact kernel type and proof state:

```lean
section
open Goldblatt.Ch01

-- Every nonzero infinitesimal has an infinite reciprocal, and vice versa:
#check @isNonzeroInfinitesimalIn_iff_inv_isInfiniteIn

-- Sums of infinitesimals remain infinitesimal in any ordered field:
example {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {ε δ : F} (hε : IsInfinitesimalIn ε) (hδ : IsInfinitesimalIn δ) :
    IsInfinitesimalIn (ε + δ) :=
  hε.add hδ
end
```

# Chapters 2 & 3: Large Sets, Ultrafilters & the Ultrapower $`\mathbb{R}^*`
%%%
tag := "ch02-03-ultrapower"
file := "ch02-03-ultrapower"
%%%

How do we actually build $`\mathbb{R}^*` without hand-waving? A natural first try is the ring of all real sequences $`\mathbb{R}^{\mathbb{N}}` under termwise addition and multiplication: the sequence $`\varepsilon = (1, \tfrac{1}{2}, \tfrac{1}{3}, \dots)` shrinks faster than every positive constant sequence $`(r, r, r, \dots)`, while $`\omega = (1, 2, 3, \dots)` outgrows every constant sequence.

Unfortunately, raw $`\mathbb{R}^{\mathbb{N}}` is **not a field**! The interlacing indicator sequences

$$`e = (1, 0, 1, 0, \dots) \quad\text{and}\quad o = (0, 1, 0, 1, \dots)`

are both nonzero, yet their product is $`e \cdot o = (0, 0, 0, \dots)`. To quotient out zero divisors while making the order total, we must decide for *every* subset $`A \subseteq \mathbb{N}` whether $`A` or its complement $`A^c` counts as “large.”

```spatial3d (model := "ultrapower_germs") (title := "3D Stage II · Ultrapower Sequence-to-Germ Collapse (ℝ^ℕ / ℱ)")
Three real sequences over <code>ℕ</code> funnel through the golden nonprincipal ultrafilter lens <code>ℱ</code> onto hyperreal germs on the vertical <code>ℝ*</code> axis: the cyan harmonic spiral <code>1/(n+1)</code> enters the translucent zero halo <code>hal(0)</code>, the coral sequence <code>n</code> shoots upward to the unlimited point <code>ω</code>, and the emerald alternating sequence <code>(1,0,1,0,…)</code> resolves cleanly without zero divisors.
```

## From Fréchet's Cofinite Filter to a Free Ultrafilter

In [`Ch02_LargeSets.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch02_LargeSets.lean) and [`Ch03_UltrapowerConstruction.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch03_UltrapowerConstruction.lean), we formalize Goldblatt's filter hierarchy:

1. **Cofinite (Fréchet) filter**: $`A \subseteq \mathbb{N}` is cofinite iff $`A^c` is finite. Cofinite sets are closed under finite intersections and supersets, and exclude all finite sets so finite-index accidents are ignored.
2. **Finite Intersection Property & Zorn's Lemma**: Any family with the FIP generates a proper filter, and Zorn's Lemma extends the cofinite filter to a maximal proper filter—a **free (nonprincipal) ultrafilter** $`\mathcal{F}` satisfying $`A \in \mathcal{F} \iff A^c \notin \mathcal{F}` for every $`A \subseteq \mathbb{N}`.
3. **Ultrapower Quotient**: Identifying two sequences $`r \sim s` iff $`\{n \in \mathbb{N} : r_n = s_n\} \in \mathcal{F}` produces the hyperreal ordered field $`\mathbb{R}^*` (aligned seamlessly with Mathlib's `Hyperreal := Germ (hyperfilter ℕ : Filter ℕ) ℝ`).

```svgCard (src := "static/diagrams/ch03_ultrapower_filter.svg") (alt := "Ultrapower Construction and Los Index-wise Transfer")
<strong>Figure I.2 — Voting by Free Ultrafilter.</strong> For any two sequences <code>r</code> and <code>s</code>, the index set divides into <code>{r_n &lt; s_n} ⊔ {r_n = s_n} ⊔ {r_n &gt; s_n}</code>. Finite-additivity and maximality of <code>ℱ</code> force <em>exactly one</em> of those three pieces to belong to <code>ℱ</code>, giving trichotomy and multiplicative inverses in one stroke.
```

```lean
section
open Goldblatt

-- Raw sequence rings have zero divisors (1,0,1,0,...) * (0,1,0,1,...) = 0:
#check seqEvenOne_mul_seqOddOne
#check seq_has_zero_divisors

-- Modulo any filter F, index-wise agreement is an equivalence congruence:
#check seqEquiv_equivalence
#check seqEquiv_add_mul
end
```

# Chapter 4: Relational Structures & Łoś's Transfer Principle
%%%
tag := "ch04-transfer-principle"
file := "ch04-transfer-principle"
%%%

Computing directly with equivalence classes of sequences for every theorem of calculus would be exhausting. Chapter 4 builds the logical engine that makes ultrafilter indices disappear once and for all: **Łoś's Theorem** and the **Transfer Principle**.

In [`Ch04_TransferPrinciple.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch04_TransferPrinciple.lean) (2,754 lines), we construct deep embeddings of first-order terms (`LTerm S`) with *partial* function symbols (`PartialFun S m`, so division $`x / y` and $`\sqrt{x}` carry explicit domains!) and bounded-quantifier formulas (`LFormula S`, supporting `∀ x ∈ A, φ` and `∃ x ∈ A, φ`). Every standard relation $`P \subseteq S^k` and partial function $`f` lifts index-by-index to $`{}^*P` and $`{}^*f`, and structural induction proves:

* **Łoś's Theorem**: $`{}^*\varphi([r_1], \dots, [r_m])` holds in $`{}^*S` iff $`\{n \in \mathbb{N} : \varphi(r_1(n), \dots, r_m(n))\} \in \mathcal{F}`.
* **Transfer Principle**: Every first-order bounded sentence $`\varphi` is true over $`\mathbb{R}` **if and only if** its `*-transform` $`{}^*\varphi` is true over $`\mathbb{R}^*`!

Consequently, identities like $`\sin^2 x + \cos^2 x = 1`, the discreetness of hyperintegers (there is no $`N \in \mathbb{N}^*` strictly between $`n` and $`n + 1`), and universal algebraic laws transfer automatically from $`\mathbb{R}` to $`\mathbb{R}^*`.

```lean
section
open Goldblatt.Ch04

-- Deeply embedded first-order terms, bounded formulas, and complex transfer:
#check LTerm
#check PartialFun.IsTotal
#check hypernat_discrete_between_nat
#check exists_unlimited_mem_starSet_iff_unbounded
#check complex_transfer_principle
end
```

# Chapter 5: Hyperreals Great & Small — Shadows, Quotients & Infinite Primes
%%%
tag := "ch05-shadows-and-primes"
file := "ch05-shadows-and-primes"
%%%

Chapter 5 harvests the geometric payoff of Part I inside [`Ch05_HyperrealsGreatAndSmall.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch05_HyperrealsGreatAndSmall.lean):

* **Halos & Galaxies**: Two hyperreals lie in the same **halo** ($`x \approx_h y`) when $`x - y \in \mathbb{I}` is infinitesimal, and in the same **galaxy** when $`x - y \in \mathbb{L}` is limited.
* **The Standard Part (`shadow`)**: For every limited $`b \in \mathbb{L}`, the cut $`\{r \in \mathbb{R} : (r : \mathbb{R}^*) < b\}` is nonempty and bounded above in $`\mathbb{R}`. By Dedekind completeness of $`\mathbb{R}`, its supremum $`\mathrm{sh}(b) \in \mathbb{R}` exists and is the **unique** real number infinitesimally close to $`b`!
* **Valuation Ring Isomorphism**: Limited hyperreals form a subring $`\mathbb{L} \subseteq \mathbb{R}^*`, infinitesimals form a maximal ideal $`\mathbb{I} \triangleleft \mathbb{L}`, and `shadowRingHom` induces a canonical ring isomorphism $`\mathbb{L} / \mathbb{I} \simeq_{+\,*} \mathbb{R}`!
* **Euclid's Infinitude of Primes via Hypernaturals**: Pick an unlimited hypernatural $`N \in \mathbb{N}^* \setminus \mathbb{N}`. By Transfer of prime factorization, $`N! + 1` has a hyperprime divisor $`P \in {}^*\mathrm{Prime}`. Since $`P` divides $`N! + 1`, $`P` cannot divide $`N!`, so $`P > n` for every standard $`n \in \mathbb{N}`. By backward existential transfer, the set of standard primes is unbounded!

```lean
section
open Goldblatt

-- Every limited hyperreal is infinitesimally close to its unique real shadow:
#check @infClose_shadow
#check @shadow_add
#check @shadow_mul
#check @ker_shadowRingHom

-- Euclid's theorem proved via a hyperprime dividing N! + 1 for unlimited N:
#check nonstandard_euclid_infinite_primes
end
```
