import VersoManual
import Book.Meta
import LecturesOnTheHyperreals.Ch16_LoebMeasure
import LecturesOnTheHyperreals.Ch17_RamseyTheory
import LecturesOnTheHyperreals.Ch18_Completion
import LecturesOnTheHyperreals.Ch19_HyperfiniteApproximation

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 400000
set_option linter.verso.markup.emph false

#doc (Manual) "Part V — Landmark Applications & Reading Guide" =>
%%%
tag := "part-5-applications"
file := "part-5-applications"
%%%

In Part V, the machinery of hyperfinite sets, enlargements, and countable saturation pays off across four seemingly distant branches of mathematics: **measure and probability theory** (Ch. 16), **infinitary and finitary Ramsey combinatorics** (Ch. 17), **metric, Banach, $`p`-adic, and power-series completions** (Ch. 18), and **functional analysis and Stone duality** (Ch. 19), followed by Chapter 20's historical reading guide.

```spatial3d (model := "padic_stone_hull") (title := "3D Stage V · 3-adic Valuation Tree, Nonstandard Hull & Hahn–Banach Plane")
Inside the translucent Nonstandard Hull unit ball <code>M̂ = M_fin / ≈</code> rises a 3-level 3-adic branching tree (<code>1 → 3 → 9 → 27</code> ultrametric coset balls), while a golden hyperfinite Hahn–Banach hyperplane touches the sphere tangentially along its normal functional vector.
```

# Chapter 16: Loeb Measure & Lebesgue Measure from Hyperfinite Counting
%%%
tag := "ch16-loeb-measure"
file := "ch16-loeb-measure"
%%%

For decades after Robinson's 1960 discovery, mathematicians believed nonstandard analysis could never help measure theory or stochastic processes because **an internal algebra $`\mathcal{A}` of subsets cannot be a $`\sigma`-algebra** (unless finite): countable unions of internal sets are almost always external!

In 1975, **Peter A. Loeb** turned this apparent obstacle into one of the most celebrated theorems of nonstandard analysis. Start with *any* internal algebra $`\mathcal{A}` of subsets of $`\Omega` and an internal finitely additive measure $`\nu : \mathcal{A} \to {}^*\mathbb{R}_{\ge 0}` (for example, uniform hyperfinite counting $`\nu(A) = |A|/N` on a grid of size $`N \in \mathbb{N}^*_\infty`). Define the standard real pre-measure

$$`\mu_0(A) := \mathrm{sh}\bigl(\nu(A)\bigr) \in [0, \infty].`

Why is $`\mu_0` countably additive on $`\mathcal{A}` whenever $`\Omega` lives in an $`\aleph_1`-saturated universe? Suppose $`A \in \mathcal{A}` is a disjoint union $`A = \bigsqcup_{k=0}^\infty A_k` with every $`A_k \in \mathcal{A}`. Then the decreasing internal remainders $`B_m = A \setminus \bigcup_{k=0}^m A_k` satisfy $`\bigcap_{m=0}^\infty B_m = \emptyset`. By **countable saturation**, some finite stage $`B_M` is *already empty*, so $`A_k = \emptyset` for all $`k > M`—the infinite disjoint union was secretly finite all along! Carathéodory's extension theorem then extends $`\mu_0` uniquely to a complete standard $`\sigma`-additive measure $`\mu_L` on the **Loeb $`\sigma`-algebra** $`L(\mathcal{A})`.

```svgCard (src := "static/diagrams/ch16_loeb_measure.svg") (alt := "Peter Loeb Measure Construction and Lebesgue Measure from Hyperfinite Counting")
<strong>Figure V.1 — The Loeb Measure Pipeline.</strong> Pushing uniform hyperfinite counting <code>|A|/N</code> down from a grid <code>Ω</code> via <code>st⁻¹</code> recovers classical Lebesgue measure on <code>ℝ</code> directly from discrete combinatorics!
```

In [`Ch16_LoebMeasure.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch16_LoebMeasure.lean) (4,160 lines), we formalize set rings, Carathéodory outer measures, Loeb's theorem with inner/outer internal approximation characterizations, and prove that a subset $`B \subseteq \mathbb{R}` is **Lebesgue measurable** iff its inverse shadow $`\mathrm{st}^{-1}(B)` is Loeb measurable on the hyperfinite line grid!

```lean
section
open Goldblatt.Ch16

#check IsSetRing
#check IsSigmaAlgebra
#check @M_line_starInterval_measure
#check @M_line_borel_measure
#check @nullMeasurableSet_iff_isLoebMeasurable_invShadow_omega
end
```

# Chapter 17: Ramsey Theory & the Paris–Harrington Theorem
%%%
tag := "ch17-ramsey"
file := "ch17-ramsey"
%%%

Chapter 17 ([`Ch17_RamseyTheory.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch17_RamseyTheory.lean), 2,064 lines) showcases how ultrafilters and nonstandard transfer streamline Ramsey combinatorics:

1. **Infinite Ramsey Theorem**: Given a $`k`-coloring $`c : [\mathbb{N}]^r \to \{0, \dots, k-1\}` of $`r`-element subsets of $`\mathbb{N}`, evaluate $`{}^*c` at an unlimited point $`\omega \in \mathbb{N}^*_\infty` to induce a $`k`-coloring $`c'(s) := {}^*c(s \cup \{\omega\})` on $`(r-1)`-subsets! Inducting on $`r` and stepping through standard witnesses via Transfer constructs an infinite monochromatic subset $`H \subseteq \mathbb{N}` cleanly.
2. **Compactness Transfer to Finite Ramsey**: Suppose for contradiction that for every $`n \in \mathbb{N}` there existed a “bad” $`k`-coloring $`c_n` of $`\{1, \dots, n\}` with no monochromatic $`m`-subset. In the ultrapower, the sequence $`(c_n)` assembles into an internal coloring on $`\{1, \dots, N\}` ($`N` unlimited), whose restriction to $`\mathbb{N}` violates Infinite Ramsey!
3. **Paris–Harrington Theorem (1977)**: Replacing fixed size $`|H| \ge m` with **relatively large** finite sets ($`|H| \ge m` *and* $`|H| \ge \min(H)`) follows in a dozen lines from Infinite Ramsey by the exact same compactness-transfer argument—remarkably proving in `ZFC` a combinatorial principle famously independent of first-order Peano Arithmetic (`PA`)!

```lean
section
open Goldblatt.Ch17

#check @ramsey_three_three_six
#check @infinite_ramsey
#check @infinite_poset_chain_or_antichain_via_ramsey
#check @finite_ramsey
#check @paris_harrington_ramsey
end
```

# Chapter 18: Completion by Enlargement — Hulls, $`p`-adics & Power Series
%%%
tag := "ch18-completion"
file := "ch18-completion"
%%%

```svgCard (src := "static/diagrams/ch17_19_applications_quartet.svg") (alt := "Part V Panorama: Ramsey, Completions, Stone Duality, and Hahn-Banach")
<strong>Figure V.2 — Four Jewels of Part V.</strong> One quotient template—<em>finite elements modulo infinitesimal proximity</em>—builds Cauchy completions of metric and normed spaces, the ring of <em>p</em>-adic integers <code>ℤ_p</code>, the field <code>ℚ_p</code>, and formal power series!
```

In Chapter 5 we saw $`\mathbb{L} / \mathbb{I} \simeq \mathbb{R}`, and starting from hyperrationals $`\mathbb{Q}^*` instead of $`\mathbb{R}^*` constructs $`\mathbb{R} \simeq \mathbb{Q}^*_{\mathrm{fin}} / \mathbb{Q}^*_{\mathrm{inf}}` without ever mentioning Cauchy equivalence classes or Dedekind cuts! In [`Ch18_Completion.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch18_Completion.lean) (5,078 lines), we execute this universal **Nonstandard Hull** recipe across four settings:

* **Metric & Banach Nonstandard Hulls**: For any metric or normed space $`M` in an $`\aleph_1`-saturated enlargement, let $`M_{\mathrm{fin}} = \{x \in {}^*M : {}^*d(x, {}^*x_0) \in \mathbb{L}\}` and identify $`x \approx y \iff {}^*d(x, y) \in \mathbb{I}`. Countable saturation guarantees that the quotient $`\widehat{M} = M_{\mathrm{fin}} / {\approx}` with distance $`\hat{d}([x], [y]) = \mathrm{sh}({}^*d(x, y))` is **automatically Cauchy complete** (a complete metric space / Banach space into which $`M` embeds isometrically as a dense subspace)!
* **$`p`-adic Integers $`\mathbb{Z}_p` & Field $`\mathbb{Q}_p`**: Equipping $`\mathbb{Z}` and $`\mathbb{Q}` with the $`p`-adic valuation $`|x|_p = p^{-\mathrm{ord}_p(x)}`, two hyperintegers $`z, w \in {}^*\mathbb{Z}` are $`p`-adically infinitesimally close iff $`p^n \mid (z - w)` for *every* standard $`n \in \mathbb{N}`. Quotienting $`{}^*\mathbb{Z}` by $`\bigcap_{n \in \mathbb{N}} p^n\,{}^*\mathbb{Z}` produces $`\mathbb{Z}_p`, where every $`p`-adic integer is represented literally by the base-$`p` digits of a single hypernatural!
* **Formal Power Series $`R⟦X⟧`**: Quotienting hyperpolynomials of unlimited degree modulo $`(X^\omega)` recovers formal power series via finite-degree truncations.

```lean
section
open Goldblatt.Ch18

#check @hyperratQuotient_isField
#check @padicInfClose_hypernat_iff_eq_basePDigits
#check @exists_pos_hypernat_baseP_expansion_of_padicInt
end
```

# Chapter 19: Hyperfinite Approximation — Coloring, Stone Duality & Hahn–Banach
%%%
tag := "ch19-hyperfinite-approximation"
file := "ch19-hyperfinite-approximation"
%%%

Chapter 19 ([`Ch19_HyperfiniteApproximation.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch19_HyperfiniteApproximation.lean), 4,489 lines) demonstrates the **Hyperfinite Approximation** paradigm: embed an arbitrary infinite structure $`S` into a *hyperfinite* substructure $`S^+ \subseteq {}^*S`, apply a finite theorem to $`S^+` by Transfer, and restrict or take `shadow` back to $`S`!

1. **De Bruijn–Erdős Graph Coloring Theorem**: If every finite subgraph of an infinite graph $`G = (V, E)` is $`k`-colorable, let $`V^+ \subseteq {}^*V` be a hyperfinite vertex set containing $`{}^*v` for every $`v \in V`. By Transfer of finite $`k`-colorability, the hyperfinite induced subgraph on $`V^+` has an internal $`k`-coloring $`c : V^+ \to {}^*\{0, \dots, k-1\} = \{0, \dots, k-1\}`. Restricting $`x \mapsto c({}^*x)` colors all of $`G`!
2. **Boolean Algebras & Stone's Representation Theorem**: Every finite Boolean algebra is atomic and isomorphic to the power set of its atoms. Embedding any Boolean algebra $`B` into a hyperfinite subalgebra $`B^+ \subseteq {}^*B` maps each $`b \in B` to the set of internal atoms of $`B^+` below $`{}^*b`, immediately yielding Stone's clopen set representation!
3. **Hyperfinite Hahn–Banach Extension Theorem**: Given a sublinear functional $`p : E \to \mathbb{R}` and a linear functional $`f : U \to \mathbb{R}` dominated by $`p` on a subspace $`U \subseteq E`, finite-dimensional one-step extension transfers to extend $`{}^*f` across a hyperfinite-dimensional span $`E^+ \supseteq E`, and taking the standard part $`F(v) := \mathrm{sh}\bigl(\Phi({}^*v)\bigr)` produces a global $`p`-dominated linear extension on $`E`—along with norm-preserving Banach extensions and separating dual functionals!

```lean
section
open Goldblatt.Ch19

#check @stoneHyperfiniteRep_injective
#check @isClopen_stoneClopenSet
#check @hahn_banach_extension
#check @hahn_banach_norm_preserving
#check @separating_dual_of_ne
end
```

# Chapter 20: Historical Notes, Further Reading & Coverage Map
%%%
tag := "ch20-notes-and-bibliography"
file := "ch20-notes-and-bibliography"
%%%

Goldblatt closes *Lectures on the Hyperreals* with Chapter 20 (*Notes on Topics and Literature*), tracing nonstandard analysis from Leibniz, Euler, and Cauchy through Hewitt's 1948 hyperreal rings $`C(X)/M`, Łoś's 1955 ultraproduct theorem, Robinson's 1960 breakthrough and 1966 monograph *Non-standard Analysis*, Luxemburg's 1962 Caltech lectures, Keisler's undergraduate calculus textbook, Loeb's 1975 measure theory, Nelson's 1977 Internal Set Theory, and applications to mathematical physics, economics, and stochastic differential equations.

The complete 41-entry annotated bibliography and theorem-by-theorem mapping between Goldblatt's 20 chapters and our 21 Lean 4 modules (**59,556 lines**, **0 `sorry`s**, **0 custom axioms**) are documented in [`COVERAGE.md`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/COVERAGE.md) and [`README.md`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/README.md).
