import VersoManual
import Book.Meta
import LecturesOnTheHyperreals.Ch06_Convergence
import LecturesOnTheHyperreals.Ch07_ContinuousFunctions
import LecturesOnTheHyperreals.Ch08_Differentiation
import LecturesOnTheHyperreals.Ch09_RiemannIntegral
import LecturesOnTheHyperreals.Ch10_Topology

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 400000
set_option linter.verso.markup.emph false

#doc (Manual) "Part II — Elementary Analysis via Infinitesimals" =>
%%%
tag := "part-2-analysis"
file := "part-2-analysis"
%%%

Classical real analysis buries intuitive geometric ideas beneath nested quantifier alternations ($`\forall \varepsilon > 0,\; \exists \delta > 0,\; \forall x \dots`). Part II replaces those $`\varepsilon`–$`\delta` games with direct algebraic statements about unlimited hypernatural indices $`N \in \mathbb{N}^*_\infty` and infinitesimal increments $`\Delta x \in \mathbb{I}`.

```spatial3d (model := "hyperfinite_riemann_loeb") (title := "3D Stage III · Hyperfinite Step Partition & Shadow Integral")
Twenty-eight hyperfinite Riemann columns of width <code>dx = 1/N</code> support the coral curve <code>y = f(x)</code> over <code>[0, 1]</code>, while the translucent golden shell shows how <code>shadow</code> collapses the hyperfinite sum onto the exact definite integral—and the front emerald nodes preview Loeb's uniform counting grid.
```

# Chapter 6: Sequences, Series & Robinson's Tail Criterion
%%%
tag := "ch06-convergence"
file := "ch06-convergence"
%%%

Every real sequence $`s : \mathbb{N} \to \mathbb{R}` extends canonically to a **hypersequence** $`{}^*s : \mathbb{N}^* \to \mathbb{R}^*`. In [`Ch06_Convergence.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch06_Convergence.lean) (2,580 lines), the three pillars of classical sequence theory become one-line halo statements at unlimited indices $`N \in \mathbb{N}^* \setminus \mathbb{N}`:

* **Convergence**: $`\lim_{n \to \infty} s_n = L` **iff** $`{}^*s_N \approx_h L` for *every* unlimited $`N \in \mathbb{N}^*_\infty`.
* **Monotone Convergence**: If $`s` is monotone increasing and bounded above by $`M \in \mathbb{R}`, then for any fixed unlimited $`\omega`, $`{}^*s_\omega` is limited, so $`L = \mathrm{sh}({}^*s_\omega)` is the limit!
* **Bolzano–Weierstrass & Cauchy Completeness**: If $`s` is bounded, then for any unlimited $`\omega`, $`{}^*s_\omega` is limited and its shadow $`L = \mathrm{sh}({}^*s_\omega)` is a cluster point; if $`s` is Cauchy, $`{}^*s_M \approx_h {}^*s_N` for all unlimited $`M, N`, forcing every unlimited index into the *same* halo $`\mathrm{hal}(L)`.

```lean
section
open Goldblatt
open Goldblatt.Ch06

-- Hypersequences preserve monotonicity, bounds, and algebraic operations:
#check @starSeq_mono
#check @starSeq_le_coe_of_forall_le
#check @isUnlimitedNat_add_right
end
```

# Chapter 7: Microcontinuity, Heine–Cantor & Cauchy's 1821 Sum Theorem
%%%
tag := "ch07-continuity"
file := "ch07-continuity"
%%%

A function $`f : A \to \mathbb{R}` is continuous at $`c \in A` **if and only if** its nonstandard extension $`{}^*f` maps the halo of $`c` into the halo of $`f(c)`:

$$`\forall x \in {}^*A,\quad x \approx_h c \implies {}^*f(x) \approx_h f(c).`

Notice the difference between **pointwise continuity** and **uniform continuity**:

1. In *ordinary continuity*, $`c \in A` is fixed to be a *standard* real first, and $`x \in {}^*A` varies near $`c`.
2. In *uniform continuity* on $`A`, **both** $`x, y \in {}^*A` range freely over *all* hyperreals in $`{}^*A`: $`x \approx_h y \implies {}^*f(x) \approx_h {}^*f(y)`.

Why does $`f(x) = x^2` fail uniform continuity on $`\mathbb{R}`? Take an unlimited $`\omega` and $`\varepsilon = 1/\omega \approx 0`: then $`\omega + \varepsilon \approx_h \omega`, yet $`(\omega + \varepsilon)^2 - \omega^2 = 2 + \varepsilon^2 \not\approx_h 0`!

And why is every continuous function on a compact interval $`[a, b]` automatically **uniformly continuous** (Heine–Cantor)? Let $`x, y \in {}^*[a, b]` satisfy $`x \approx_h y`. Since $`a \le x \le b`, $`x` is limited, so $`c = \mathrm{sh}(x)` lies in $`[a, b]`! Then $`x \approx_h c \approx_h y`, and continuity at the single real point $`c` yields

$$`{}^*f(x) \approx_h f(c) \approx_h {}^*f(y).`

The entire Heine–Cantor proof is six lines long! In [`Ch07_ContinuousFunctions.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch07_ContinuousFunctions.lean) (2,847 lines), we also formalize Thomae's popcorn function, the Intermediate and Extreme Value Theorems via hyperfinite grids, and **Augustin-Louis Cauchy's famous 1821 controversy** over infinite series of continuous functions—pinpointing the missing hypothesis of *micro-uniform convergence* at unlimited indices.

```lean
section
open Goldblatt.Ch07

-- Thomae's function, nonstandard IVT/EVT, and Cauchy's 1821 series theorem:
#check @continuousAt_thomaeFunction_iff
#check @intermediate_value_Icc_nonstandard
#check @extreme_value_Icc_nonstandard
#check @cauchySeries_counterexample
#check @cauchy_sum_theorem_nonstandard
end
```

# Chapters 8 & 9: The Incremental Equation & Hyperfinite Riemann Integrals
%%%
tag := "ch08-09-calculus"
file := "ch08-09-calculus"
%%%

```svgCard (src := "static/diagrams/ch08_incremental_calculus.svg") (alt := "Incremental Equation and Hyperfinite Riemann Sums")
<strong>Figure II.1 — Exact Linearization &amp; Hyperfinite Integration.</strong> Left: differentiating <code>f</code> at <code>x</code> decomposes <code>Δf = f'(x)Δx + ηΔx</code> with <code>η ≈ 0</code>, turning the Chain Rule into literal algebra. Right: definite integrals arise by taking <code>shadow</code> of a hyperfinite step sum of width <code>dx ≈ 0⁺</code>.
```

In [`Ch08_Differentiation.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch08_Differentiation.lean) (3,319 lines), $`f` has derivative $`f'(x)` at $`x \in \mathbb{R}` iff for every nonzero infinitesimal $`\Delta x \in \mathbb{I} \setminus \{0\}`,

$$`\frac{{}^*f(x + \Delta x) - f(x)}{\Delta x} \approx_h f'(x), \quad\text{equivalently}\quad \Delta f = f'(x)\Delta x + \eta\,\Delta x \;\;(\eta \approx_h 0).`

With this **Incremental Equation**, the tricky glitch where an inner function $`g(x + \Delta x) - g(x)` might hit zero infinitely often vanishes completely: substituting $`\Delta g` into $`\Delta f = f'(g(x))\Delta g + \zeta\,\Delta g` proves the **Chain Rule** by two lines of ring arithmetic! Even better, Chapter 8 proves that $`f'` is *continuous* on $`(a, b)` iff the incremental equation holds at *every* hyperreal $`x` well inside $`{}^*(a, b)`—illustrated by the classical pathology $`f(x) = x^2 \sin(1/x)`, whose derivative exists at $`0` yet oscillates wildly at infinitesimal $`x = 1/(2\pi N)`.

In [`Ch09_RiemannIntegral.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch09_RiemannIntegral.lean) (2,991 lines), partitioning $`[a, b]` into $`N` subintervals of infinitesimal width $`dx = (b - a)/N` turns the **Fundamental Theorem of Calculus** into a telescoping hyperfinite sum:

$$`G(b) - G(a) = \sum_{k=0}^{N-1} \bigl({}^*G(x_{k+1}) - {}^*G(x_k)\bigr) = \sum_{k=0}^{N-1} {}^*f(x_k)\,dx + \sum_{k=0}^{N-1} \eta_k\,dx \approx_h \int_a^b f(x)\,dx.`

```lean
section
open Goldblatt.Ch08
open Goldblatt.Ch09

-- Equivalence with Mathlib's HasDerivWithinAt, continuous-deriv characterization, and x² sin(1/x):
#check @hasDerivWithinAt_iff_hasNSCDerivWithinAt
#check @continuousOn_deriv_iff_wellInside_incremental_eq
#check @sqMulSinInv_deriv_exists_and_not_continuousAt_zero

-- FTC Part 2 via hyperfinite telescoping and hyperfinite sample averages:
#check @ftc_part2_via_hyperfinite_telescoping
#check @hyperSampleAverage_infClose_average_integral
end
```

# Chapter 10: Robinson's Nonstandard Topology & the S-Topology
%%%
tag := "ch10-topology"
file := "ch10-topology"
%%%

Chapter 10 ([`Ch10_Topology.lean`](https://github.com/alok/lectures-on-the-hyperreals/blob/main/LecturesOnTheHyperreals/Ch10_Topology.lean), 2,681 lines) recasts metric and general topology on $`\mathbb{R}` (and on $`\mathbb{R}^*` itself!) in terms of halos:

```svgCard (src := "static/diagrams/ch10_halo_topology.svg") (alt := "Robinson Nonstandard Topology: Open, Closed, and Compact Sets via Halos")
<strong>Figure II.2 — Open, Closed &amp; Compact via Halos.</strong> A set <code>K ⊆ ℝ</code> is compact iff every point of <code>*K</code> is near-standard in <code>K</code>. Non-compactness becomes a single concrete witness: <code>(0, 1]</code> fails compactness because <code>ε ∈ *(0, 1]</code> has shadow <code>0 ∉ (0, 1]</code>; <code>ℝ</code> fails because <code>ω ∈ *ℝ</code> has no shadow at all!
```

We also formalize the two natural topologies on $`\mathbb{R}^*` itself: the fine **interval (order) topology** (generated by hyperreal intervals $`(a, b)` of arbitrarily tiny infinitesimal radius, making $`\mathbb{R}^*` totally disconnected!) versus the coarser **S-topology** (generated by standard-radius balls $`\{x \in \mathbb{R}^* : |x - b| < r\}` for $`0 < r \in \mathbb{R}`), proving that $`\bigcap_{r > 0} B_S(b, r) = \mathrm{hal}(b)`.

```lean
section
open Goldblatt.Ch10

#check @biInter_realRadiusNhds_eq_halo
#check @generateFrom_realRadiusNhds_eq_intervalTopology
#check @isIntervalOpen_starSet_of_isOpen
end
```
