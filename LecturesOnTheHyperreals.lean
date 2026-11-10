import LecturesOnTheHyperreals.Ch01_WhatAreTheHyperreals
import LecturesOnTheHyperreals.Ch02_LargeSets
import LecturesOnTheHyperreals.Ch03_UltrapowerConstruction
import LecturesOnTheHyperreals.Ch04_TransferPrinciple
import LecturesOnTheHyperreals.Ch05_HyperrealsGreatAndSmall
import LecturesOnTheHyperreals.Ch06_Convergence
import LecturesOnTheHyperreals.Ch07_ContinuousFunctions
import LecturesOnTheHyperreals.Ch08_Differentiation
import LecturesOnTheHyperreals.Ch09_RiemannIntegral
import LecturesOnTheHyperreals.Ch10_Topology
import LecturesOnTheHyperreals.Ch11_InternalSets
import LecturesOnTheHyperreals.Ch12_InternalFunctions
import LecturesOnTheHyperreals.Ch13_UniversesFrameworks
import LecturesOnTheHyperreals.Ch14_Enlargements
import LecturesOnTheHyperreals.Ch15_PermanenceSaturation
import LecturesOnTheHyperreals.Ch16_LoebMeasure
import LecturesOnTheHyperreals.Ch17_RamseyTheory
import LecturesOnTheHyperreals.Ch18_Completion
import LecturesOnTheHyperreals.Ch19_HyperfiniteApproximation

/-!
# Lectures on the Hyperreals — Complete Lean 4 Formalization

Complete, `sorry`-free, custom-`axiom`-free Lean 4 formalization of Robert Goldblatt's
*Lectures on the Hyperreals: An Introduction to Nonstandard Analysis*
(Graduate Texts in Mathematics, vol. 188, Springer-Verlag, New York, 1998):

* **Part I — Foundations (Chapters 1–5)**
  * `Ch01_WhatAreTheHyperreals`: Historical foundations, Leibniz/Euler infinitesimals, ordered
    fields, Archimedean vs. non-Archimedean extensions, and hyperreal preview.
  * `Ch02_LargeSets`: Filters, Fréchet cofinite filter, finite intersection property, Zorn's Lemma,
    and free ultrafilters (`hyperfilter`).
  * `Ch03_UltrapowerConstruction`: Ultrapower construction of `ℝ*`, `ℕ*`, `ℤ*`, `ℚ*`, `omegaNat`,
    `starSet`, `starFun`, `starFun₂`, `starFunN`, `starSeq`, `starRel`, and `|ℝ*| = 2^𝔠`.
  * `Ch04_TransferPrinciple`: Relational structures, terms with partial functions, bounded-quantifier
    formulas, `*-transforms`, Łoś's Theorem, Transfer Principle, and `Hypercomplex`.
  * `Ch05_HyperrealsGreatAndSmall`: Limited, unlimited, infinitesimal, and appreciable hyperreals;
    halos, galaxies, and the shadow homomorphism `𝕃 ⧸ 𝕀 ≃+* ℝ`; Dedekind & Cauchy completeness via
    `shadow`; `*ℕ` galaxies, hyperfactorials, and nonstandard proof of Euclid's theorem.

* **Part II — Elementary Analysis (Chapters 6–10)**
  * `Ch06_Convergence`: Hypersequences, underflow/overspill, nonstandard convergence, monotone
    convergence, Cauchy criterion, Bolzano–Weierstrass, `limsup`/`liminf`, and infinite series tests.
  * `Ch07_ContinuousFunctions`: Microcontinuity, functional limits, Thomae's ruler function, IVT,
    EVT, Heine–Cantor uniform continuity, Banach Contraction Theorem, Robinson's sequential lemma,
    uniform convergence, and Cauchy's 1821 sum theorem.
  * `Ch08_Differentiation`: Nonstandard derivatives, increments & differentials, Incremental
    Equation, chain & inverse function theorems, multivariable total derivatives, Taylor series,
    and well-inside incremental approximation.
  * `Ch09_RiemannIntegral`: Darboux & step-size Riemann sums, shadow integral, Fundamental Theorem
    of Calculus (Parts 1 & 2), and Mean Value Theorems for integrals.
  * `Ch10_Topology`: Halo characterizations of open/closed/interior/closure/frontier, Kuratowski
    axioms, Robinson's Compactness Criterion, Heine–Borel, S-topology, and interval topology on `ℝ*`.

* **Part III — Internal and External Entities (Chapters 11–12)**
  * `Ch11_InternalSets`: `[A_n]` internal sets, internal least-number & induction principles,
    overflow & underflow, internal completeness, external sets, Internal Set Definition Principle,
    halo permanence, countable saturation, uncountability of infinite internal sets, closed shadows,
    and hyper-open sets.
  * `Ch12_InternalFunctions`: `[f_n]` internal partial functions, internal algebra/bijections/inverses,
    hyperfinite sets & internal cardinality `|A| ∈ ℕ*`, Hyperfinite Pigeonhole Principle, hyperfinite
    summation, and Riemann integrals as shadows of hyperfinite sums.

* **Part IV — Nonstandard Frameworks (Chapters 13–15)**
  * `Ch13_UniversesFrameworks`: Cumulative superstructures `Entity X`, Kuratowski tuples/relations/
    functions, language `ℒ_𝕌`, `Δ₀` transfer frameworks, Zakon ultrapower collapse, standard/internal/
    external entities, `*𝒫(A)`, Internal Set & Function Definition Principles, general hyperfinite
    sets & sums, and unification bridges to Chapters 11–12.
  * `Ch14_Enlargements`: Concurrent relations, FIP, hyperfinite approximation, Theorem 14.2.1
    equivalence, fine ultrafilters on `Finset I`, and Theorem 14.3.1 (Existence of Enlargements).
  * `Ch15_PermanenceSaturation`: Permanence principles, Robinson's Sequential Lemma, comprehensiveness,
    `κ`-saturation, `ℵ₁`-saturation, and Equivalence of Countable Saturation & Countable
    Comprehensiveness.

* **Part V — Applications (Chapters 16–19)**
  * `Ch16_LoebMeasure`: Set rings/algebras, Carathéodory extension, Peter Loeb's Theorem, single-set
    internal approximability, and Lebesgue measure on `[0, 1]` and `ℝ` via hyperfinite counting
    Loeb measure.
  * `Ch17_RamseyTheory`: Party problem `R(3, 3) = 6`, nonstandard cofinality on `ℕ*`, Infinite
    Ramsey's Theorem, Finite Ramsey's Theorem via ultrapower transfer, and Paris–Harrington
    relatively large Ramsey theorem.
  * `Ch18_Completion`: `ℚ_𝕃 ⧸ ℚ_𝕀 ≃+*o ℝ`, Metric & Banach Nonstandard Hulls, $p$-adic integers
    `ℤ* ⧸ I_p ≃+* ℤ_[p]` & numbers `ℚ_[p]`, formal power series `R⟦X⟧` via hyperpolynomials, and
    hyperfinite base-$p$ expansions.
  * `Ch19_HyperfiniteApproximation`: De Bruijn–Erdős `k`-colouring theorem, formula Boolean algebras,
    hyperfinite Boolean algebra `B⁺`, nonstandard Boolean Ultrafilter & Stone Representation
    Theorems (`B ≃o Clopens (StoneSpace B)`), distributive lattice prime filter theorem, hyperfinite
    vector spaces `V⁺`, and nonstandard proofs of the Hahn–Banach Extension Theorem.
-/
