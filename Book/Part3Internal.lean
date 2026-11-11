import VersoManual
import Book.Meta
import LecturesOnTheHyperreals.Ch11_InternalSets
import LecturesOnTheHyperreals.Ch12_InternalFunctions

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 400000
set_option linter.verso.markup.emph false

#doc (Manual) "Part III — Internal & External Entities" =>
%%%
tag := "part-3-internal"
file := "part-3-internal"
%%%

Why doesn't the Dedekind completeness axiom of $`\mathbb{R}`—*“every nonempty bounded-above subset has a least upper bound”*—transfer directly to prove that the set of infinitesimals $`\mathbb{I} \subseteq \mathbb{R}^*` has a least upper bound $`s \in \mathbb{R}^*`? (Notice such an $`s` is impossible: if $`s \in \mathbb{I}` then $`2s \in \mathbb{I}` exceeds $`s`, while if $`s \notin \mathbb{I}` then $`s/2` is already a smaller upper bound!)

Part III answers this fundamental question with razor precision: quantifier transfer over subsets of $`\mathbb{R}^*` applies **precisely to internal sets**—those assembled index-by-index from sequences of subsets $`(A_n)_{n \in \mathbb{N}}` of $`\mathbb{R}`! Sets like $`\mathbb{I}`, $`\mathbb{L}`, $`\mathbb{N}`, and $`\mathbb{R}` are **external**: invisible to internal first-order comprehension, yet extraordinarily fertile as boundary markers that force internal sets to *overflow* and *underflow*.

```svgCard (src := "static/diagrams/ch11_internal_overflow.svg") (alt := "Internal vs External Sets, Overflow, Underflow, and Countable Saturation")
<strong>Figure III.1 — Overflow, Countable Saturation &amp; Hyperfinite Sets.</strong> Because no internal set can stop cleanly at the external boundary between finite <code>ℕ</code> and unlimited <code>*ℕ_∞</code>, any internal set containing all standard naturals automatically spills out to cover an initial hyperfinite segment <code>{0, …, K}</code> for some unlimited <code>K</code>.
```

# Chapter 11: Internal Sets, Overflow & Countable Saturation
%%%
tag := "ch11-internal-sets"
file := "ch11-internal-sets"
%%%

In [`Ch11_InternalSets.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch11_InternalSets.lean) (2,245 lines), a subset $`X \subseteq \mathbb{R}^*` is **internal** (`IsInternal X`) iff there exists a sequence of standard sets $`A : \mathbb{N} \to \mathrm{Set}\;\mathbb{R}` such that

$$`[r] \in [A_n] \iff \{n \in \mathbb{N} : r_n \in A_n\} \in \mathcal{F}.`

Constant sequences $`A_n = A` give the *standard* sets $`{}^*A`, whereas varying sequences such as $`A_n = [0, 1/(n+1)]` produce genuinely new internal subsets like the infinitesimal closed interval $`[0, \varepsilon]`. Transfer of Dedekind completeness now says: **every nonempty bounded-above *internal* subset of $`\mathbb{R}^*` has a least upper bound in $`\mathbb{R}^*`**! Flipping that theorem on its head immediately yields:

1. **External Sets**: $`\mathbb{I}`, $`\mathbb{L}`, $`\mathbb{R}`, $`\mathbb{N}`, and $`\mathbb{N}^*_\infty` are all *external* because they are bounded without suprema/infima.
2. **Overflow & Underflow**:
   * *Overflow*: If an internal set $`A \subseteq \mathbb{N}^*` contains arbitrarily large finite naturals (or contains all of $`\mathbb{N}`), then $`A` contains an unlimited hypernatural $`K \in \mathbb{N}^*_\infty`!
   * *Underflow*: If an internal set $`A \subseteq \mathbb{N}^*` contains every unlimited hypernatural, it must already contain $`\{m \in \mathbb{N}^* : m \ge k_0\}` for some *finite* $`k_0 \in \mathbb{N}`!
3. **Countable ($`\aleph_1`-) Saturation**: Any decreasing chain $`A_0 \supseteq A_1 \supseteq A_2 \supseteq \cdots` of nonempty internal sets in the ultrapower $`\mathbb{R}^*` has **nonempty intersection** $`\bigcap_{k \in \mathbb{N}} A_k \neq \emptyset`! The proof is a gem of diagonalization: pick a witness $`x^{(k)} \in A_k` at each step and define the diagonal sequence $`y_n = x^{(n)}_n`—for every fixed $`k`, $`y_n` agrees with $`x^{(n)}_n \in A_k(n)` on all indices $`n \ge k` (a cofinite set, hence in $`\mathcal{F}`)!
4. **Closedness of Shadows**: Using countable saturation, for *any* internal set $`X \subseteq \mathbb{R}^*`, its standard shadow image $`\mathrm{sh}(X \cap \mathbb{L}) \subseteq \mathbb{R}` is **automatically closed** in $`\mathbb{R}`!

```lean
section
open Goldblatt

-- Internal sets, star sets, and the internal S-open / hyper-open characterization:
#check @ofSeq_mem_internalSet
#check @isInternal_starSet
#check @isIntervalOpen_iff_isHyperOpen_of_isInternal
#check @isSOpen_iff_forall_halo_subset_of_isInternal
end
```

# Chapter 12: Internal Functions, Hyperfinite Sets & Pigeonhole
%%%
tag := "ch12-internal-functions"
file := "ch12-internal-functions"
%%%

Just as sequences of subsets $`(A_n)` assemble internal sets, sequences of partial real functions $`(f_n : A_n \to \mathbb{R})` assemble **internal functions** $`[f_n] : [A_n] \to \mathbb{R}^*` in [`Ch12_InternalFunctions.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch12_InternalFunctions.lean) (1,679 lines).

The superstar class of internal sets is the **hyperfinite sets**: internal sets $`A = [A_n]` arising from sequences of *finite* sets $`A_n \subseteq \mathbb{R}`. Even though a hyperfinite set with unlimited internal cardinality $`|A| = [|A_n|] = N \in \mathbb{N}^*_\infty` is uncountably infinite from the outside, **from the inside it behaves exactly like a finite set**:

* Every nonempty hyperfinite subset of $`\mathbb{R}^*` attains an **exact maximum and minimum** element!
* **Hyperfinite Pigeonhole Principle**: No internal injection can map a hyperfinite set $`A` into a proper internal subset $`B \subsetneq A`!
* **Hyperfinite Summation (`hypersum`)**: Any internal function $`F` can be summed over any hyperfinite set $`S = [S_n]` via $`\sum_{x \in S} F(x) := \bigl[\sum_{x \in S_n} f_n(x)\bigr]`, obeying linearity, monotonicity, and disjoint-union additivity—providing the exact foundation for hyperfinite Riemann integration (Ch. 9) and Loeb probability spaces (Ch. 16).

```lean
section
open Goldblatt

-- Hyperfinite summation linearity, disjoint additivity, and step partitions:
#check @hypersum_add
#check @hypersum_union_disjoint
#check @hypersum_mono
#check @hyperStepPartition_eq_and_hypercard
end
```
