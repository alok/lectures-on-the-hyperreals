# Complete Book-to-Lean Coverage Map

**Book**: Robert Goldblatt, *Lectures on the Hyperreals: An Introduction to Nonstandard Analysis*, Graduate Texts in Mathematics, vol. 188, Springer-Verlag, New York, 1998 (xi + 289 pp.).

Every mathematical chapter (Chapters 1–19, Parts I–V) is formalized in Lean 4 (`v4.35.0` / Mathlib `v4.35.0`) with **zero `sorry`s** and **zero custom axioms** (`propext`, `Classical.choice`, `Quot.sound` only). Chapter 20 (*Books on Nonstandard Analysis*, pp. 279–282) is an annotated bibliography of 41 monographs, catalogued in full below with cross-references to the formalized chapters.

---

## Summary Table

| Ch. | Title (Book Pages) | Lean Module | Namespace | Lines | Thms/Lemmas | Defs/Types | Total Decls |
|---:|---|---|---|---:|---:|---:|---:|
| **1** | What Are the Hyperreals? (pp. 3–14) | `LecturesOnTheHyperreals/Ch01_WhatAreTheHyperreals.lean` | `Goldblatt` | 1,215 | 70 | 18 | 88 |
| **2** | Large Sets (pp. 15–22) | `LecturesOnTheHyperreals/Ch02_LargeSets.lean` | `Goldblatt` | 1,492 | 112 | 32 | 144 |
| **3** | Ultrapower Construction of the Hyperreals (pp. 23–34) | `LecturesOnTheHyperreals/Ch03_UltrapowerConstruction.lean` | `Goldblatt` | 868 | 81 | 28 | 109 |
| **4** | The Transfer Principle (pp. 35–48) | `LecturesOnTheHyperreals/Ch04_TransferPrinciple.lean` | `Goldblatt.Ch04` | 2,754 | 149 | 50 | 199 |
| **5** | Hyperreals Great and Small (pp. 49–62) | `LecturesOnTheHyperreals/Ch05_HyperrealsGreatAndSmall.lean` | `Goldblatt` | 1,562 | 109 | 29 | 138 |
| **6** | Convergence of Sequences and Series (pp. 63–74) | `LecturesOnTheHyperreals/Ch06_Convergence.lean` | `Goldblatt.Ch06` | 2,580 | 164 | 19 | 183 |
| **7** | Continuous Functions (pp. 75–90) | `LecturesOnTheHyperreals/Ch07_ContinuousFunctions.lean` | `Goldblatt.Ch07` | 2,847 | 134 | 23 | 157 |
| **8** | Differentiation (pp. 91–104) | `LecturesOnTheHyperreals/Ch08_Differentiation.lean` | `Goldblatt.Ch08` | 3,319 | 125 | 22 | 147 |
| **9** | The Riemann Integral (pp. 105–112) | `LecturesOnTheHyperreals/Ch09_RiemannIntegral.lean` | `Goldblatt.Ch09` | 2,991 | 118 | 27 | 145 |
| **10** | Topology of the Reals (pp. 113–128) | `LecturesOnTheHyperreals/Ch10_Topology.lean` | `Goldblatt.Ch10` | 2,681 | 140 | 11 | 151 |
| **11** | Internal and External Sets (pp. 129–146) | `LecturesOnTheHyperreals/Ch11_InternalSets.lean` | `Goldblatt` | 2,245 | 125 | 13 | 138 |
| **12** | Internal Functions and Hyperfinite Sets (pp. 147–156) | `LecturesOnTheHyperreals/Ch12_InternalFunctions.lean` | `Goldblatt` | 1,679 | 69 | 29 | 98 |
| **13** | Universes and Frameworks (pp. 157–182) | `LecturesOnTheHyperreals/Ch13_UniversesFrameworks.lean` | `Goldblatt.Ch13` | 12,047 | 461 | 148 | 609 |
| **14** | The Existence of Nonstandard Entities (pp. 183–190) | `LecturesOnTheHyperreals/Ch14_Enlargements.lean` | `Goldblatt.Ch14` | 2,187 | 113 | 49 | 162 |
| **15** | Permanence, Comprehensiveness, and Saturation (pp. 191–202) | `LecturesOnTheHyperreals/Ch15_PermanenceSaturation.lean` | `Goldblatt.Ch15` | 3,156 | 118 | 33 | 151 |
| **16** | Loeb Measure (pp. 203–220) | `LecturesOnTheHyperreals/Ch16_LoebMeasure.lean` | `Goldblatt.Ch16` | 4,160 | 115 | 44 | 159 |
| **17** | Ramsey Theory (pp. 221–230) | `LecturesOnTheHyperreals/Ch17_RamseyTheory.lean` | `Goldblatt.Ch17` | 2,064 | 79 | 21 | 100 |
| **18** | Completion by Enlargement (pp. 231–258) | `LecturesOnTheHyperreals/Ch18_Completion.lean` | `Goldblatt.Ch18` | 5,078 | 207 | 119 | 326 |
| **19** | Hyperfinite Approximation (pp. 259–278) | `LecturesOnTheHyperreals/Ch19_HyperfiniteApproximation.lean` | `Goldblatt.Ch19` | 4,489 | 192 | 95 | 287 |
| **Root** | Umbrella Import & Audit (`LecturesOnTheHyperreals.lean` + `scripts/verify_axioms.lean`) | `LecturesOnTheHyperreals.lean` | — | 142 | — | — | — |
| **Total** | **All 19 Mathematical Chapters + Root/Audit** | **21 Lean files** | **`Goldblatt`** | **59,556** | **2,681** | **810** | **3,491** *(4,248 in kernel)* |

---

## Detailed Section-by-Section Coverage

### Part I — Foundations (Chapters 1–5)

#### Chapter 1: What Are the Hyperreals? (`Ch01_WhatAreTheHyperreals.lean`, pp. 3–14)
- **§1.1 Infinitely Small and Large**: `IsInfinitesimalIn`, `IsNonzeroInfinitesimalIn`, `IsPositiveInfinitesimalIn`, `IsInfiniteIn`, reciprocal duality (`isNonzeroInfinitesimalIn_iff_inv_isInfiniteIn`), equivalence of the Archimedean property with absence of nonzero infinitesimals (`not_real_isNonzeroInfinitesimalIn`, `not_real_isInfiniteIn`).
- **§1.2 Historical Background**: Archimedes' polygon/exhaustion identities and parabola quadrature `∑ k < n, (k/n)²(1/n) → 1/3`; Leibniz product increment `(x + dx)(y + dy) - xy = x dy + y dx + dx dy` with `(dx * dy) / dx` infinitesimal; Euler's infinite-exponent binomial product `(∏ k < n, (j - k)/j) - 1` and `(1 + z/n)^n → exp z`; Weierstrass `ε`-`δ` limit equivalence (`WeierstrassLimit`) and Robinson's finite-satisfiability theorem (`robinson_finite_satisfiability_in_real`).
- **§1.3 What Is a Real Number?**: Base-10 decimal truncations `decimalTrunc`, Dedekind completeness (`IsDedekindComplete`, `orderRingIsoRealOfIsDedekindComplete`, `not_isDedekindComplete_of_exists_nonzeroInfinitesimal`), Dedekind cuts `DedekindCutQ ≃o ℝ`, and Cantor's rational Cauchy sequence completion.

#### Chapter 2: Large Sets (`Ch02_LargeSets.lean`, pp. 15–22)
- **§2.1–2.2 Variable Quantities & Largeness**: Agreement sets `agreementSet`, comparison sets `lessThanSet`, alternating sequences `altEven` and `altOdd`.
- **§2.3–2.5 Filters and Ultrafilters**: `SetFilter`, `SetFilter.IsProper`, `SetFilter.IsUltrafilter`, `SetUltrafilter`, order/type equivalences with Mathlib's `Filter` and `Ultrafilter`, `principalFilter`, `cofiniteSetFilter`, `generatedSetFilter`, `chainUnionFilter`, `HasFIP`, and all 8 filter facts of §2.5.
- **§2.6–2.7 Zorn's Lemma & Exercises**: Theorem 2.6.1 (`exists_ultrafilter_extending_fip`), Corollary 2.6.2 (`exists_nonprincipal_ultrafilter`), and Exercises 2.7(1)–(5) (including distinct free ultrafilters on `ℕ` separating even and odd naturals).

#### Chapter 3: Ultrapower Construction of the Hyperreals (`Ch03_UltrapowerConstruction.lean`, pp. 23–34)
- **§3.1–3.4 Equivalence Modulo `𝓕` & Ordered Field `ℝ*`**: Ultrapower construction of `ℝ*`, `ℕ*`, `ℤ*`, `ℚ*` over `hyperfilter ℕ`; canonical unlimited hypernatural `omegaNat = [(0, 1, 2, …)]`, positive infinitesimal `1 / omegaNat`, ordered field laws, and non-Archimedean witnesses.
- **§3.5–3.9 Enlarging Sets, Functions, Partial Functions, Sequences & Relations**: `starSet` (`*A`), Boolean/interval preservation, `starFun`, `starFun₂`, `starFunN`, `starPartialFun`, `starSeq`, `starRel`, `starRel₂`, trigonometric identity transfers, and cardinality `|ℝ*| = 2^𝔠` (`card_hyperreal_eq_continuum` / `#(Ultrafilter ℕ) = 2^𝔠`).

#### Chapter 4: The Transfer Principle (`Ch04_TransferPrinciple.lean`, pp. 35–48)
- **§4.1–4.3 Relational Structures, Partial-Function Terms, and Bounded Formulas**: `PartialFun`, `RelStructure`, `LTerm` (with definedness guards for partial functions such as `1/x` and `tan x`), `LFormula` (atomic, connectives, bounded quantifiers `(∀ x ∈ A)` / `(∃ x ∈ A)`), and Goldblatt's `tan(-x) = -tan(x)` worked formalization.
- **§4.4–4.5 `*-Transforms`, Łoś's Theorem, and Transfer**: Parametric ultrapower `RelStructure` over any `Germ (U : Filter I) S` and over `ℝ*`, full Łoś's Theorem for `LFormula`, **Transfer Principle** (universal/existential transfer, preservation of identities, strict order, field axioms, trigonometric & algebraic laws), `Hypercomplex` (`*ℂ ≃+* ℝ* × ℝ*`), and all §4.1 & §4.5 exercises.

#### Chapter 5: Hyperreals Great and Small (`Ch05_HyperrealsGreatAndSmall.lean`, pp. 49–62)
- **§5.1–5.4 Limited, Unlimited, Infinitesimal, Appreciable, Halos & Galaxies**: `IsLimited` (`𝕃`), `IsUnlimited`, `IsPosUnlimited`, `IsNegUnlimited`, `IsInfinitesimal` (`𝕀`), `IsAppreciable`, `LimitedSubring`, `InfinitesimalIdeal` (maximal ideal of `𝕃`), `InfClose` (`≈ₕ`), `LimDist` (`∼ₗ`), `halo`, `galaxy`.
- **§5.5–5.7 Shadow (Standard Part) & Completeness of `ℝ`**: `shadow : ℝ* → ℝ` (`sh(x) = sSup {r : ℝ | (r : ℝ*) ≤ x}`), ring/order homomorphism laws on `𝕃`, isomorphism `(LimitedSubring ⧸ InfinitesimalIdeal) ≃+* ℝ`, rational-ultrapower quotient `(*ℚ ∩ 𝕃) ⧸ (*ℚ ∩ 𝕀) ≃+* ℝ`, trigonometric infinitesimals (`sin ε / ε ≈ₕ 1`, `(1 - cos ε) / ε ≈ₕ 0`), and nonstandard proofs of Dedekind and Cauchy completeness of `ℝ`.
- **§5.8–5.10 Hypernaturals `*ℕ`, Galaxies, Factorials & Primes**: `IsUnlimitedNat`, galaxy decomposition of `ℕ*` into copies of `ℕ` and `ℤ`, `hyperFactorial`, `IsStarPrime`, and Goldblatt's nonstandard proof of Euclid's Theorem (`N! + 1` has a `*`-prime factor `p > N`, forcing infinitely many standard primes).

---

### Part II — Elementary Analysis (Chapters 6–10)

#### Chapter 6: Convergence of Sequences and Series (`Ch06_Convergence.lean`, pp. 63–74)
- **§6.1–6.4 Hypersequences & Nonstandard Convergence**: `starSeq`, underflow/overspill on `ℕ*`, `Tendsto s atTop (𝓝 L) ↔ ∀ N, IsUnlimitedNat N → starSeq s N ≈ₕ L`, uniqueness & algebra of limits, squeeze theorem, boundedness, monotone convergence, and divergence to `±∞`.
- **§6.5–6.7 Subsequences, Cluster Points, Cauchy Criterion, `limsup`/`liminf`**: Nonstandard characterization of cluster points (`∃ N unlimited, starSeq s N ≈ₕ c`), **Bolzano–Weierstrass Theorem**, **Cauchy Criterion** (`∀ M N unlimited, starSeq s M ≈ₕ starSeq s N`), `seqLimsup`/`seqLiminf` & `erealSeqLimsup` as maximum/minimum of unlimited shadows.
- **§6.8–6.10 Infinite Series**: Tail criterion `∑_{k=M}^N a_k ≈ₕ 0` for unlimited `M ≤ N`, Oresme's divergence of the harmonic series, geometric series, comparison & limit comparison tests, D'Alembert's ratio test, Cauchy's root test, and Leibniz's alternating series test.

#### Chapter 7: Continuous Functions (`Ch07_ContinuousFunctions.lean`, pp. 75–90)
- **§7.1–7.4 Microcontinuity & Functional Limits**: Theorem 7.1.1 (`continuousAt_iff_infClose`, `*f(hal(c)) ⊆ hal(f(c))`), Theorem 7.1.3 (`continuousWithinAt_iff_infClose`), nonstandard continuity of `sin` and `cos`, all 7 one-sided/punctured/infinite limit characterizations, and Exercise 7.4(3) (`sin(1/x)`, `x sin(1/x)`, Dirichlet's `1_ℚ`, `±x`, and **Thomae's ruler function** `continuousAt_thomaeFunction_iff`).
- **§7.5–7.9 IVT, EVT, Uniform Continuity & Contraction Fixed Points**: Hyperfinite-grid nonstandard proofs of the **Intermediate Value Theorem** (`intermediate_value_Icc_nonstandard`), **Extreme Value Theorem** (`extreme_value_Icc_nonstandard`), **Heine–Cantor Theorem** (`uniformContinuousOn_Icc_of_continuousOn`), Exercises 7.8(1)–(4), and **Banach's Contraction Mapping Theorem** (`contractionOn_isClosed_existsUnique_fixedPoint`).
- **§7.10–7.15 Permanence, Uniform Convergence & Cauchy's Sum Theorem**: `cauchy_permanence_principle`, `robinson_sequential_lemma`, Exercises 7.11(1)–(3), extended function hypersequences `starFunSeq`, Robinson's Uniform Convergence Criterion (`tendstoUniformlyOn_iff_starFunSeq_infClose`), `xⁿ` counterexample on `[0, 1]`, Theorem 7.13.1 & Theorem 7.14.1, and **Cauchy's 1821 Sum Theorem** (`cauchy_sum_theorem_nonstandard`).

#### Chapter 8: Differentiation (`Ch08_Differentiation.lean`, pp. 91–104)
- **§8.1–8.4 Infinitesimal Derivatives, Differentials & Chain Rule**: `HasNSCDerivAt`, Theorem 8.1.1 (`hasDerivAt_iff_hasNSCDerivAt`), Exercise 8.1.2 (`sin' = cos`, `cos' = -sin`), non-differentiability of `|x|` at `0`, Theorem 8.2.1 (microcontinuity), **Theorem 8.2.2 (Incremental Equation)** (`hasNSCDerivAt_iff_incremental_eq`), Leibniz product/quotient rules, and nonstandard Chain Rule (`HasNSCDerivAt.comp`).
- **§8.5–8.6 Critical Point, Rolle, MVT & Inverse Function Theorem**: `rolle_nsc`, `mvt_nsc`, `cauchy_mvt_nsc`, monotonicity tests, and Goldblatt's nonstandard proof of the **Inverse Function Theorem** (`HasNSCDerivAt.invFunOn_Ioo`).
- **§8.7–8.12 Partial Derivatives, Taylor Series & Well-Inside Incremental Equation**: Theorem 8.7.1 (`IsNSCSmoothAt.hasNSCTotalDerivAt`), multivariable chain rule, Exercises 8.8(1)–(2), Lagrange & Peano Taylor remainders (`taylor_incremental_of_cont_iterDeriv`, Exercise 8.10.2 `taylor_incremental_peano`), Maclaurin series for `cos` & `exp` (Exercise 8.9.1), second-derivative extremum test, **Theorem 8.11.1** (`continuousOn_deriv_iff_wellInside_incremental_eq`), and Exercises 8.12(1)–(2) (`x² sin(1/x)`).

#### Chapter 9: The Riemann Integral (`Ch09_RiemannIntegral.lean`, pp. 105–112)
- **§9.1–9.3 Step-Size Riemann Sums & Shadow Integral**: `IntervalPartition`, Darboux upper/lower sums, `stepPartition`, `hyperStepSum`, **Theorem 9.1.1** (`hyperStepLowerSum_infClose_hyperStepUpperSum`), Exercise 9.1.2 (monotonic functions), `hyperIntegral f a b = shadow (hyperStepSum f a b ε)`, full Darboux equivalence (`exists_isDarbouxIntegrableOn_iff_infClose`), Exercise 9.2.1 (equal subdivisions `N ∈ ℕ*` + `∫_0^b x = b²/2` & `∫_0^b x² = b³/3`), and Chasles' relation (Exercise 9.3.1).
- **§9.4–9.5 Fundamental Theorem of Calculus & Integral Mean Value Theorems**: **Theorem 9.4.1 (FTC Part 1)** (`hasDerivWithinAt_areaFun_Icc`, `hasDerivAt_areaFun_and_intervalIntegral`), **Theorem 9.4.2 (FTC Part 2)** (both `G - F` proof and direct hyperfinite telescoping proof `ftc_part2_via_hyperfinite_telescoping`), sample averages `hyperSampleAverage`, and First & Weighted Mean Value Theorems for Integrals.

#### Chapter 10: Topology of the Reals (`Ch10_Topology.lean`, pp. 113–128)
- **§10.1–10.2 Open/Closed Sets, Interior, Closure & Frontier via Halos**: `isOpen_iff_forall_halo_subset`, `isClosed_iff_forall_infClose_mem`, nonstandard `nsaInterior`/`nsaClosure`/`nsaFrontier`/`nsaDerivedSet`, Kuratowski closure axioms, and **Theorem 10.2.2** (`halo (r : ℝ*) = ⋂_{A open, r ∈ A} *A`).
- **§10.3 Compactness**: **Robinson's Nonstandard Compactness Criterion** (`isCompact_iff_forall_mem_starSet_exists_infClose` — proved directly without Heine–Borel!), **Theorem 10.3.1 (Heine–Borel Theorem)** (`isCompact_iff_isClosed_and_isBounded`), topological EVT, and Heine–Cantor.
- **§10.4–10.5 Topologies on `ℝ*` (S-Topology & Interval Topology)**: `realRadiusNhds`, `sNhds`, Robinson's `sTopology` (non-Hausdorff, clopen `𝕃` and galaxies), `intervalTopology = Preorder.topology ℝ*` (Hausdorff, clopen `𝕀`, halos, galaxies, `ℝ* \ ℝ`, total disconnectedness), and Exercises 10.5.1–10.5.2.

---

### Part III — Internal and External Entities (Chapters 11–12)

#### Chapter 11: Internal and External Sets (`Ch11_InternalSets.lean`, pp. 129–146)
- **§11.1–11.6 Internal Sets, Least Number, Overflow & Internal Completeness**: `internalSet`, `IsInternal`, `IsExternal`, `internalNatSet`, `IsInternalNat`, Boolean closure, finite sets (`isInternal_of_finite`), Internal Least Number & Induction Principles, **Overflow** (`overflow_nat`), and **Internal Order Completeness** (`IsInternal.exists_isLUB`, `IsInternal.exists_isGLB`).
- **§11.7–11.10 External Sets, Internal Set Definition Principle & Underflow**: External proofs for `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℝ₊`, `𝕃`, `𝕀`, halos, galaxies; `isInternal_real_set_iff_finite`; Internal Set Definition Principle (`isInternal_sep_lt`, quantifier projections); **Underflow** (`underflow_nat`) and **Halo Permanence** (`exists_real_ball_subset_of_halo_subset`).
- **§11.11–11.14 Saturation, Uncountability, Closed Shadows & Hyper-Open Sets**: **Countable Saturation** (`countable_saturation_decreasing`, `countable_saturation_fip`, `isInternal_iUnion_implies_finite`), **Uncountability of Infinite Internal Sets** (`IsInternal.not_countable_of_infinite`), **Closedness of Shadows of Internal Sets** (`IsInternal.isClosed_shadowSet` + alternative overflow proof), and `IsHyperOpen` (`isIntervalOpen_iff_isHyperOpen_of_isInternal`).

#### Chapter 12: Internal Functions and Hyperfinite Sets (`Ch12_InternalFunctions.lean`, pp. 147–156)
- **§12.1–12.2 Internal Partial Functions**: `RealPartialFun`, `InternalPartialFun`, `internalFun`, `IsInternalFun`, `starInternalFun`, **Theorem 12.1.1** (`internalFun_eq_iff`), and Exercises 12.2(1)–(8) (restriction, image, preimage, composition, injectivity, inverse, `F + G`, `F * G`, `c • F`, infinitesimal LUB of infinitesimal-valued internal functions).
- **§12.3–12.6 Hyperfinite Sets, Counting & Pigeonhole Principle**: `IsHyperfinite`, `HasHypercard`, `hasHypercard_Icc_one`, `exists_hyperfinite_approx_of_countable`, `hasHypercard_uniformPartition`, Exercises 12.4(1)–(3), **Theorem 12.5.1** (`hasHypercard_iff_exists_internal_bijection`), **Theorem 12.6.1 (Hyperfinite Pigeonhole Principle)** (`isHyperfinite_iff_pigeonhole`), and non-internality of `doubleStandardMap`.
- **§12.7 Integrals as Hyperfinite Sums**: `hypersum`, 4 algebraic/monotonicity laws, Exercise 12.7.1 (`hyperStepPartition_eq_and_hypercard`), and **Riemann Integral as Shadow of a Hyperfinite Sum** (`integral_eq_shadow_hypersum`).

---

### Part IV — Nonstandard Frameworks (Chapters 13–15)

#### Chapter 13: Universes and Frameworks (`Ch13_UniversesFrameworks.lean`, pp. 157–182)
- **§13.1–13.6 Superstructures & Universes**: Cumulative quotient superstructure `Entity X : Type u` over any base type `X`, atoms vs. sets, Kuratowski pairs/tuples (`kpair_injective`, `ktuple_injective`), relations, functions, function spaces `B^A`, dependent products `∏_{i ∈ I} A_i`, transitive/strongly transitive sets, `VStage X n`, `Entity.rank`, Exercise 13.6.1, and explicit rank bounds for topologies (`V_3`), measures (`V_5`), metrics (`V_6`), and Riemann integrals (`V_6`).
- **§13.7–13.12 Language `ℒ_𝕌`, `Δ₀` Transfer Frameworks & Ultrapower Models**: `UTerm`, `UFormula`, `Framework X Y`, Exercises 13.8.1–13.8.2, Zakon bounded-rank collapse `collapseStage`, Łoś's Theorems (`los_uterm`, `los_uformula`), `ultrapowerFramework U X`, `hyperrealFramework`, `sigmaImage` (**Theorem 13.9.2**), `internalUniverse` (**Theorem 13.10.1**), 18 internal closure laws (§13.11), and **Theorem 13.12.1** (`*𝒫(A)` = internal subsets of `*A`).
- **§13.13–13.20 Comprehension, General Hyperfinite Sets, Hyperfinite Sums & Ch. 11–12 Bridges**: Internal induction & completeness, **Theorem 13.14.1** (external image `im A` of infinite `A`), **Internal Set & Function Definition Principles** (§13.15–13.16), `IsHyperfiniteSet`, **Theorem 13.17.1**, `hyperCard`, Exercises 13.18(1)–(6) (including `|𝒫_I(A)| = 2^{|A|}`), `hyperSum` & `hyperIndexedSum` (Exercises 13.20(1)–(2)), and exact equivalence bridges to `Goldblatt.IsInternal`, `Goldblatt.IsHyperfinite`, and `Goldblatt.IsInternalFun`.

#### Chapter 14: The Existence of Nonstandard Entities (`Ch14_Enlargements.lean`, pp. 183–190)
- **§14.1–14.2 Concurrent Relations & Enlargements**: `IsConcurrent`, `NonstandardExtension`, all 6 concrete motivating concurrent relations (nonstandard elements, unlimited hypernaturals, positive infinitesimals, hyperfinite supersets of standard sets, topological monads `monad`, and FIP/Robinson compactness `isCompact_iff_forall_mem_starSet_exists_monad`), **Theorem 14.2.1** (`enlargement_tfae`: FIP ↔ Concurrence ↔ Hyperfinite Approximation), and countable concurrence vs. uncountable failure in `ℝ*`.
- **§14.3–14.4 Fine Ultrafilters & Theorem 14.3.1**: `hatSet`, `IsFineFilter`, `fineUltrafilter I`, `FineUltrapower`, Exercises 14.4(1)–(3), **Theorem 14.3.1** (`theorem_14_3_1_single_concurrent`, `theorem_14_3_1_family_concurrent`, `theorem_14_3_1_hyperfinite_approx`), and the global **Enlargement Existence Theorem** (`exists_enlargement`).

#### Chapter 15: Permanence, Comprehensiveness, and Saturation (`Ch15_PermanenceSaturation.lean`, pp. 191–202)
- **§15.1–15.3 Permanence & Robinson's Sequential Lemma**: Theorem 15.1.1(1)–(5) (including ray overflow and the `{ε}ᶜ` nonstandard-parameter counterexample), Exercise 15.1.2, **Lemma 15.2.1 (Robinson's Sequential Lemma)**, Exercise 15.2.2, **Theorem 15.2.3**, and §15.3 uniform convergence applications (Exercise 15.3.1).
- **§15.4–15.6 Comprehensiveness & `κ`-Saturation**: `ultrapower_comprehensive`, Exercises 15.4.1(1)–(2), `countable_comprehensiveness_seq`, **Theorem 15.4.3** & Exercise 15.4.4, `UniverseEmbedding`, **Theorem 15.4.2** (`countableComprehensiveness_iff_countableSaturation`), `ℵ₁`-saturation of `ℝ*`, Exercise 15.5.1 (`isKappaSaturated_iff_concurrent`), `#Y ≥ κ` for infinite internal sets, and failure of `(2^ℵ₀)⁺`-saturation for `ℝ*`.

---

### Part V — Applications (Chapters 16–19)

#### Chapter 16: Loeb Measure (`Ch16_LoebMeasure.lean`, pp. 203–220)
- **§16.1–16.4 Set Rings/Algebras, Carathéodory Extension & Lebesgue Facts**: `IsSetRing`, `IsSetAlgebra`, `IsSigmaRing`, `IsSigmaAlgebra`, Examples 16.1(1)–(6) (`S(𝒞_ℝ) = borel ℝ`, `internalSubsetAlgebra`), `IsFinitelyAdditiveMeasure`, `IsCountablyAdditiveMeasure`, `caratheodoryOuter`, `caratheodoryExtensionMeasure` (including `σ`-finite uniqueness and `𝒜_σ`/`𝒜_δ` characterization), and §16.4 Lebesgue regularity/uniqueness lemmas.
- **§16.5–16.7 Peter Loeb's Theorem & Single-Set Approximability**: `InternalMeasureAlgebra`, `loebPremeasure`, **Peter Loeb's Theorem** (`loebPremeasure_isCountablyAdditive`, `loebMeasure_properties`), Lemmas 16.5.1–16.5.2, `IsMuApproximable`, **Lemmas 16.6.1–16.6.4** (`isLoebMeasurable_iff_isMuApproximable_of_lt_top`), and **Theorem 16.7.1**.
- **§16.8 Lebesgue Measure via Hyperfinite Counting Loeb Measure**: Both the `[0, 1]` uniform grid (`M_unit`, `map_unitSt_loebMeasure_eq_volume`, `nullMeasurableSet_iff_isLoebMeasurable_unitSt`) and Goldblatt's full real-line grid `S = {k/N : |k| ≤ N²}` (`M_line`, **Theorem 16.8.1**, `*ℚ` counterexample `M_line_starRat_counterexample`, **Lemma 16.8.3**, and **Theorem 16.8.2** `nullMeasurableSet_iff_isLoebMeasurable_invShadow`).

#### Chapter 17: Ramsey Theory (`Ch17_RamseyTheory.lean`, pp. 221–230)
- **§17.1–17.2 Colourings, Poset Chains/Antichains & Nonstandard Cofinality**: `rSubsets`, `IsMonochromatic`, Party Problem **`R(3, 3) = 6`** (`ramsey_number_three_three`), nonstandard cofinality of `omegaNat ∈ ℕ*`, `starNatFinFun`, and direct nonstandard proof of **Theorem 17.1.1** (`infinite_poset_chain_or_antichain_nonstandard`).
- **§17.3–17.5 Infinite Ramsey, Finite Ramsey & Paris–Harrington**: Exercise 17.3.1 (`[*A]^r = *([A]^r)`), **Theorem 17.3.1 (Infinite Ramsey's Theorem)** (`infinite_ramsey`), Erdős–Szekeres & Bolzano–Weierstrass corollaries, **Theorem 17.4.1 (Finite Ramsey's Theorem via Ultrapower Transfer)** (`finite_ramsey`) + Exercise 17.4.1, and **§17.5 Paris–Harrington Partition Theorem** for relatively large finite sets (`paris_harrington_ramsey_exact`).

#### Chapter 18: Completion by Enlargement (`Ch18_Completion.lean`, pp. 231–258)
- **§18.1–18.3 Rational, Metric & Banach Nonstandard Hulls**: Intrinsic `(HyperratLimited ⧸ HyperratInfinitesimal) ≃+*o ℝ`; **Theorem 18.3.1** (`CompleteSpace (MetricHull M p)`), **Theorem 18.3.2** (`MetricCompletion M ≃ᵢ UniformSpace.Completion M`), Corollary 18.3.3 & Exercise 18.3.4; Banach nonstandard hull `NormedHull E` and `BanachCompletion E ≃ₗᵢ[ℝ] UniformSpace.Completion E`.
- **§18.4–18.5 $p$-adic Integers $\mathbb{Z}_p$ & Numbers $\mathbb{Q}_p$**: **Theorem 18.4.1**, `(ℤ* ⧸ PadicInfinitesimalIdealZ p) ≃+* ℤ_[p]`, `MetricHull (PadicZ p) ⟨0⟩ ≃ᵢ ℤ_[p]`; **Theorems 18.5.1–18.5.2**, `(PadicLimitedSubringQ p ⧸ PadicInfinitesimalIdealQ p) ≃+* ℚ_[p]`, `MetricHull (PadicQ p) ⟨0⟩ ≃ᵢ ℚ_[p]`.
- **§18.6–18.8 Formal Power Series `R⟦X⟧` & Hyperfinite Base-$p$ Expansions**: **Theorems 18.6.1–18.6.2**, Corollary 18.6.3, Exercise 18.6.4, `(HyperPoly R ⧸ XAdicIdeal R) ≃+* PowerSeries (StarRing R)`, `(ApproachableHyperPoly R ⧸ ApproachableInfinitesimalIdeal R) ≃+* PowerSeries R`, `(LimitedCoeffHyperPoly ⧸ InfinitesimalCoeffHyperPoly) ≃+* PowerSeries ℝ`, `MetricCompletion (AdicPoly R) ≃ᵢ AdicPowerSeries R`; `StarSeqP p ≃ ℕ*`, **Theorem 18.7.1**, and **Exercises 18.8(1)–(2)**.

#### Chapter 19: Hyperfinite Approximation (`Ch19_HyperfiniteApproximation.lean`, pp. 259–278)
- **§19.1 Graph Colouring**: Exercise 19.1.1 and nonstandard hyperfinite-approximation proof of the **De Bruijn–Erdős `k`-Colouring Theorem** (`deBruijn_erdos_colorable_iff`, `chromaticNumber_eq_iSup_finset`).
- **§19.2–19.7 Boolean Algebras & Stone Duality**: Propositional formula algebra `FormulaAlgebra Sym` (`|B_Π| = 2^(2^|Π|)`, Exercise 19.2.1, atomless for infinite `Π`), `finiteBooleanAlgebra_orderIso_powerset_atoms`, minterm local finiteness & Exercise 19.5(2), hyperfinite approximating subalgebra `B⁺` (Exercise 19.5(1)), nonstandard Boolean Ultrafilter Theorem, **Stone's Representation Theorem** (`stoneFieldOfSetsOrderIso`), full topological Stone duality **`B ≃o Clopens (StoneSpace B)`** (`stoneClopenIso`), and Exercises 19.7(1)–(4) (including Birkhoff/Stone distributive lattice prime filter representation).
- **§19.8–19.11 Hyperfinite Vector Spaces & Hahn–Banach Theorem**: Exercise 19.8.1, **Theorem 19.8.2** (`hyperfiniteApproxSubspace E` `V⁺`), Exercises 19.9(1)–(3) (transcendence over `ℝ` & infinite dimensionality of `ℝ*` and `𝕃`), Lemma 19.10.1, Exercises 19.11(1)–(2), **Goldblatt's `V⁺` Nonstandard Proof of Hahn–Banach** (`hahn_banach_extension`), **Luxemburg's FIP Proof** (Exercise 19.11(3), `exercise_19_11_3_c_hahn_banach_luxemburg`), and normed-space corollaries (`hahn_banach_norm_preserving`, `separating_dual_of_ne`) — proved without importing Mathlib's `HahnBanach`.

---

## Chapter 20: Books on Nonstandard Analysis (pp. 279–282)

Chapter 20 of Goldblatt's monograph contains no theorems or definitions; instead, it curates 41 foundational monographs and edited volumes on nonstandard analysis published between 1966 and 1998. All 41 references are preserved below alongside connections to the formalized Lean modules:

1. **S. Albeverio, J. E. Fenstad, R. Høegh-Krohn, T. Lindstrøm**, *Nonstandard Methods in Stochastic Analysis and Mathematical Physics*, Academic Press, 1986. *(Connects to `Ch16_LoebMeasure`, `Ch19_HyperfiniteApproximation`.)*
2. **S. A. Albeverio, W. A. J. Luxemburg, M. P. H. Wolff (eds.)**, *Advances in Analysis, Probability, and Mathematical Physics: Contributions of Nonstandard Analysis*, Kluwer, 1995.
3. **L. O. Arkeryd, N. J. Cutland, C. W. Henson (eds.)**, *Nonstandard Analysis: Theory and Applications*, Kluwer, 1997.
4. **D. Ballard**, *Foundational Aspects of "Non"standard Mathematics*, AMS, 1994. *(Connects to `Ch13_UniversesFrameworks`.)*
5. **M. Capiński, N. J. Cutland**, *Nonstandard Methods for Stochastic Fluid Mechanics*, World Scientific, 1995. *(Loeb-space applications building on `Ch16_LoebMeasure`.)*
6. **N. J. Cutland (ed.)**, *Nonstandard Analysis and its Applications*, LMS Student Texts 10, Cambridge University Press, 1988/1998.
7. **N. J. Cutland, V. Neves, F. Oliveira, J. Sousa-Pinto (eds.)**, *Developments in Nonstandard Mathematics*, Pitman Research Notes 336, Longman, 1995.
8. **J. W. Dauben**, *Abraham Robinson: The Creation of Nonstandard Analysis — A Personal and Mathematical Odyssey*, Princeton University Press, 1995. *(Historical context formalized in `Ch01_WhatAreTheHyperreals`.)*
9. **M. Davis**, *Applied Nonstandard Analysis*, Wiley, 1977. *(Superstructure frameworks, Loeb measure, and Hilbert/Banach hulls: `Ch13`, `Ch16`, `Ch18`.)*
10. **F. Diener, M. Diener (eds.)**, *Nonstandard Analysis in Practice*, Springer, 1995.
11. **F. Diener, G. Reeb**, *Analyse Non Standard*, Hermann, Paris, 1989.
12. **M. Diener, G. Wallet (eds.)**, *Mathématiques Finitaires et Analyse Non Standard* (2 vols.), Université Paris VII, 1989.
13. **E. I. Gordon**, *Nonstandard Methods in Commutative Harmonic Analysis*, Translations of Mathematical Monographs 164, AMS, 1997. *(Hyperfinite approximation of groups/algebras: `Ch19`.)*
14. **J. M. Henle, E. M. Kleinberg**, *Infinitesimal Calculus*, MIT Press, 1979. *(Elementary calculus via infinitesimals: `Ch05`–`Ch09`.)*
15. **R. F. Hoskins**, *Standard and Nonstandard Analysis*, Ellis Horwood, 1990.
16. **A. E. Hurd (ed.)**, *Nonstandard Analysis — Recent Developments*, LNM 983, Springer, 1983.
17. **A. E. Hurd, P. A. Loeb (eds.)**, *Victoria Symposium on Nonstandard Analysis*, LNM 369, Springer, 1974.
18. **A. E. Hurd, P. A. Loeb**, *An Introduction to Nonstandard Real Analysis*, Academic Press, 1985. *(Direct precursor to Part II–V, especially `Ch13`–`Ch16`.)*
19. **D. S. Jones**, *Introduction to Asymptotics: A Treatment Using Nonstandard Analysis*, World Scientific, 1997.
20. **V. Kanovei**, *A Course on Foundations of Nonstandard Analysis*, IPM, Tehran, 1994.
21. **H. J. Keisler**, *Elementary Calculus: An Infinitesimal Approach*, Prindle, Weber & Schmidt, 1976. *(Increment equation & shadow calculus: `Ch07`–`Ch09`.)*
22. **H. J. Keisler**, *Foundations of Infinitesimal Calculus*, Prindle, Weber & Schmidt, 1976. *(Ultrapowers, transfer, and saturation: `Ch03`–`Ch05`, `Ch15`.)*
23. **H. J. Keisler**, *An Infinitesimal Approach to Stochastic Analysis*, Memoirs of the AMS 297, 1984. *(Loeb probability spaces: `Ch16`.)*
24. **F. Koudjeti**, *Elements of External Calculus; with an Application to Mathematical Finance*, Ph.D. thesis, Rijksuniversiteit Groningen / Labyrint Publication, 1995.
25. **A. G. Kusraev, S. S. Kutateladze**, *Nonstandard Methods of Analysis*, Kluwer, 1994. *(Boolean-valued and nonstandard functional analysis: `Ch18`, `Ch19`.)*
26. **A. H. Lightstone, A. Robinson**, *Nonarchimedean Fields and Asymptotic Expansions*, North-Holland, 1975. *(Connects to `Ch05`, `Ch18`.)*
27. **R. Lutz, M. Goze**, *Nonstandard Analysis: A Practical Guide with Applications*, LNM 881, Springer, 1981.
28. **W. A. J. Luxemburg (ed.)**, *Applications of Model Theory to Algebra, Analysis, and Probability*, Holt, Rinehart and Winston, 1969. *(Ultrapowers, Zakon superstructures, Luxemburg's Hahn–Banach proof: `Ch13`, `Ch18`, `Ch19`.)*
29. **W. A. J. Luxemburg, A. Robinson (eds.)**, *Contributions to Non-Standard Analysis*, Studies in Logic 69, North-Holland, 1972.
30. **M. Machover, J. Hirshfeld**, *Lectures on Non-Standard Analysis*, LNM 94, Springer, 1969. *(Enlargements & concurrence: `Ch14`.)*
31. **E. Nelson**, *Radically Elementary Probability Theory*, Princeton University Press, 1987. *(Hyperfinite probability & counting measures: `Ch12`, `Ch16`.)*
32. **S. Rashid**, *Economies With Many Agents: An Approach Using Nonstandard Analysis*, Johns Hopkins University Press, 1987.
33. **A. Robert**, *Nonstandard Analysis*, Wiley, 1988.
34. **A. Robinson**, *Non-standard Analysis*, North-Holland, 1966; revised edition, Princeton University Press, 1996. *(The founding monograph; compactness, Cauchy's sum theorem, topological monads, and enlargements: `Ch01`, `Ch07`, `Ch10`, `Ch14`.)*
35. **A. Robinson**, *Selected Papers, Volume 2: Nonstandard Analysis and Philosophy*, ed. H. J. Keisler et al., North-Holland, 1979.
36. **J. E. Rubio**, *Optimisation and Nonstandard Analysis*, Dekker, 1994.
37. **K. D. Stroyan, J. M. Bayod**, *Foundations of Infinitesimal Stochastic Analysis*, Studies in Logic 119, North-Holland, 1986.
38. **K. D. Stroyan, W. A. J. Luxemburg**, *Introduction to the Theory of Infinitesimals*, Academic Press, 1976. *(Superstructures, saturation, nonstandard hulls, and Stone/Hahn–Banach: `Ch13`–`Ch19`.)*
39. **C. Tuckey**, *Nonstandard Methods in the Calculus of Variations*, Pitman Research Notes 297, Longman, 1993.
40. **I. van den Berg**, *Nonstandard Asymptotic Analysis*, LNM 1249, Springer, 1987. *(Permanence principles & underflow/overflow: `Ch11`, `Ch15`.)*
41. **K. R. Wicks**, *Fractals and Hyperspaces*, LNM 1492, Springer, 1991.
