# Errata and proof clarifications in the cited literature

These findings concern the mathematical sources used in the formalization.
**Open** means that the cited text requires the stated correction or additional
justification. The correction column describes the argument used here; it does
not assert that the source has been amended.

The Lean certificate column identifies a counterexample or a formalized repair
when available. Typographical corrections do not have separate Lean assertions.
All locations use the numbering of the cited source. FHX refers to the paper in
[`paper/`](paper/).

## Boucksom–Jonsson

Source: S. Boucksom and M. Jonsson, *Global pluripotential theory over a trivially
valued field* (BJ22), and the addendum *Addendum to “Global pluripotential theory
over a trivially valued field”*.

### EP-1.1. Lemma 4.6: decreasing limits with minus-infinite values

- **Location:** BJ22, Lemma 4.6 and the use of (4.5) in its proof.
- **Issue:** at a common minus-infinite point, (4.5) asks for
  `−∞ < −∞`. The exponential difference has limit zero rather than a strictly
  negative limit. Weakening the inequality does not repair the directedness
  argument. The lemma itself is false, including for nontrivial limits:
  logarithmic wells on `K = [0,1]` give a function in the iterated decreasing
  closure but not in the first decreasing closure.
- **Status:** Open.
- **Correction:** do not use this closure lemma for families admitting
  minus-infinite values. The decreasing-limit results needed for the envelope
  theorem follow from homogeneous majorants or from the envelope property.
- **Lean certificates:** `EnvelopeProperty.not_bj22Lemma46` ([source](EnvelopeProperty/Global/Lemma46Counterexample.lean)); `EnvelopeProperty.MultiModel.isPSH_of_antitone_of_homMajorant` ([source](EnvelopeProperty/Global/PSH2HomogeneousMajorant.lean)).

### EP-4.1. Theorem 6.21: monotonicity in the homogeneous Siu argument

- **Location:** BJ22, Theorem 6.21; FHX, Remark 7.3.
- **Issue:** on `ℙ¹`, take `ℓ = e_E`, `ψ_n = (1 − 1/(2n))ℓ` and
  `t_n = 1 − 1/n`. Although `ψ_n` decreases to `ℓ`, the difference
  `ψ_n − t_nℓ = ℓ/(2n)` increases where `ℓ` is finite and negative.
  This refutes the monotonicity step, not the statement of the theorem.
- **Status:** Open.
- **Correction:** use fixed-coefficient division, as in FHX §7.
- **Lean certificate:** `EnvelopeProperty.ProjBerk.bj621_counterexample` ([source](EnvelopeProperty/Projective/Remark73ProjectiveLine.lean)).

### BJ-Add-1. Lemma 1.3: approximation by PL obstacles

- **Location:** the addendum, Lemma 1.3, implication (iii) ⇒ (i).
- **Issue:** uniformly approximating each term of a decreasing net does not
  preserve monotonicity of the net.
- **Status:** Open.
- **Correction:** index by rational PL majorants of the continuous obstacle;
  this family is directed under finite minima. FHX Proposition 2.5(1) uses
  this construction.
- **Lean certificate:** `EnvelopeProperty.ProjBerk.exists_antitone_isRatPL_net` ([source](EnvelopeProperty/Projective/PLDensity.lean)).

### BJ-Convex-1. Corollary 4.10: the value at minus infinity

- **Location:** BJ22, Corollary 4.10.
- **Issue:** `χ : (−∞,0] → ℝ` is applied to `φ − ψ`, which can equal `−∞`.
- **Status:** Open.
- **Correction:** extend by `χ(−∞) = lim_{t→−∞} χ(t)` and use finite maxima
  of affine functions with slopes in `[0,1]` in the approximation.
- **Lean certificate:** no separate certificate in this library.

## Wu

Source: L. Wu, *On the local theory of non-archimedean psh functions*.
The following corrections are also recorded in FHX §5.

### Wu-Principal. Lemma 5.11 and Proposition 5.10

- **Location:** Lemma 5.11, used in the proof of Proposition 5.10.
- **Issue:** the ideal-theoretic claim used to prove the principal-open hull
  inequality is incorrect.
- **Status:** Open.
- **Correction:** for `x ∈ K̂ ∩ Y_f^an`, extend `v + c log|f|` by `−∞`,
  apply the hull inequality on `Y`, and let positive rational `c` decrease to
  zero. This is the direct proof of FHX Lemma 5.17.
- **Lean certificate:** `EnvelopeProperty.le_iSup_of_mem_hull_awayExtend` ([source](EnvelopeProperty/Local/PrincipalExtension.lean)).

| Location | Issue and correction | Status | Lean certificate |
|---|---|---|---|
| Definition 3.1(3) | Require the supporting affine function to touch the graph: `u(x) = l(x)` and `u ≥ l` near `x`. | Open | No separate Lean assertion. |
| Definition 3.15(2) | State logarithmic growth as `u ≤ g + O(1)` for `g ∈ FS(Y)`. | Open | No separate Lean assertion. |
| Lemma 3.16, proof | Use `log‖f‖ ≤ max_α log‖a_α z^α‖`; for a monic equation use `log‖f‖ ≤ max_{i<m} (m−i)⁻¹ log‖b_i‖`. | Open | No separate Lean assertion. |
| Proposition 3.17(2) | The displayed sections generate the module; they need not form a basis. | Open | No separate Lean assertion. |
| Corollary 3.18 and Proposition 3.17(1) | The limit is `g + φ`; replace `0` in the maximum by `−C_j` and add dominated generator terms. | Open | No separate Lean assertion. |
| Lemma 3.24, proof of (3) | On the complement of `P_i`, the formula is `ch + C_i`, in agreement with `w′_i = max{w_i, ch + C_i}`. | Open | No separate Lean assertion. |
| Lemma 3.25(1) | Compactness of the collar suffices; continuity of the limit is unnecessary. | Open | No separate Lean assertion. |
| Proposition 3.30, proof | Use `g_ε = max{g, −ε log‖f‖}`, `ε = c/3`, and retain the index-dependent constant in `u_j ≤ 2g_ε + C_j`. | Open | No separate Lean assertion. |
| §5, Proposition 5.4 and following | Use strict polynomial inequalities; `int{g ≤ t} = {g < t}` does not hold in general. | Open | No separate Lean assertion. |
| Proposition 5.7 and Lemma 5.8 | The fibre-radius formula is `−log d_{W_j} = max{−j, M_j}`. | Open | No separate Lean assertion. |
| Lemma 6.8 and Corollary 6.9 | Assume local regularizability of `u`; regularizability of `u + cρ` alone does not justify `u + cρ′ + εv`. Use the barrier `v = max_i log‖f_i‖` with positive rational `ε`. | Open | No separate Lean assertion. |
| Lemma 6.16, proof | Take `U = r⁻¹(S)`; use a local projection and generic étaleness in positive characteristic. | Open | No separate Lean assertion. |

## The Stacks Project

### Stacks-1. Intermediate subalgebras of a universal homeomorphism

- **Location:** Tags `0CNF` and `0CND`, using Tags `0CNC` and `0CNB`.
- **Issue:** applying the auxiliary result to `B′ ⊆ B` requires checking
  that `Spec B → Spec B′` is a universal homeomorphism.
- **Status:** Open.
- **Correction:** use integrality, lying over and universal injectivity,
  which passes to this factor.
- **Lean certificate:** `EnvelopeProperty.Algebra.IsRadicialIntegral.over_subalgebra` ([source](EnvelopeProperty/Algebra/RadicialStructure.lean)).

### Stacks-2. Clearing denominators

- **Location:** Tag `0CN9`.
- **Issue:** the denominator-clearing argument is omitted.
- **Status:** Open.
- **Correction:** clear a common denominator outside the given prime before
  applying the additive-power argument.
- **Lean certificate:** `EnvelopeProperty.exists_mul_not_mem_and_mul_pow_mem` ([source](EnvelopeProperty/Algebra/RadicialStructure.lean)).

## Roberts–Singh

### Roberts–Singh-1. Theorem 4.17: the ambient ring in the conclusion

- **Location:** Roberts–Singh, *Subintegrality, invertible modules and the
  Picard group*, Compositio Mathematica 85 (1993), p. 267, proof of (i) ⇒ (ii).
- **Issue:** “If `p = 0` then `bⁿ ∈ B` for `n ≫ 0`” names the wrong ring.
- **Status:** Open.
- **Correction:** read `bⁿ ∈ A`.
- **Lean certificate:** no separate Lean assertion for this misprint.

## Temkin

Source: M. Temkin, *Stable modification of relative curves*,
Journal of Algebraic Geometry 19 (2010). An omitted justification is listed as
a proof clarification; it does not refute the associated statement.

| Finding | Location | Issue | Correction | Status | Lean certificate |
|---|---|---|---|---|---|
| T1 | Proposition 3.2.1, converse | "by the same argument" needs the open `U` qcqs, i.e. quasi-separatedness of `S`, which is what is being proved | apply the argument to a finite affine cover of `U` | Open | No separate Lean assertion. |
| T2 | Lemma 3.2.9 (end of §3.2) | stated without proof | continuity of the center map for separated quasi-compact `S` by a patch-compactness argument | Open | No separate Lean assertion. |
| T3 | Lemma 2.1.2 | `B_E ⊂ \|l^×\|` should be lifts `b ∈ l^×` of a ℚ-basis | Choose elements of the valued field lifting the basis of the quotient value group. | Open | No separate Lean assertion. |
| T4 | Lemma 2.1.2 | orthogonality of monomials "easy to see", not proved | residue part (max-coefficient formula) + value part (distinct values) | Open | No separate Lean assertion. |
| T5 | Corollary 2.1.3(i) | omits height ≤ rational rank and rat. rank of `v(F^×)` ≤ 1 for the prime field | Use height at most rational rank and the bound of one on the rational rank of the prime-field value group. | Open | No separate Lean assertion. |
| T9 | Lemma 6.2.9(ii), proof | reducing the `w^{pi}` terms cannot remove the constant term (the step `c = b̄₀^{1/p}` does not lower index `i = 0`), yet `B` is written without constant term | Remove the constant term using its membership in `℘₁(l)` over an algebraically closed residue field; alternatively use the Hasse–Cauchy argument. | Open | No separate Lean assertion. |
| T11 | Lemma 4.4.2 (also 4.4.6) | “since `V` is closed in `C̄`” needs `R` strictly henselian (closures of non-closed points finite over `R/𝔭`, hence local); some henselianity is necessary: over `ℤ₍₅₎` the closure of `(x² + 1)` in `ℙ¹` meets the closed fibre at `x = ±2` | proved when every `Frac(V/𝔭)` is separably closed (`Alterations.StableModification.BlowDown.isClosed_of_forall_specializes`, `Alterations.StableModification.BlowDown.specializes_of_specializes_of_isAlgebraicAt`) | Open | `Alterations.StableModification.BlowDown.isClosed_of_forall_specializes` ([source](EnvelopeProperty/Alterations/StableModification/BlowDown/ClosedLocus.lean)); `Alterations.StableModification.BlowDown.specializes_of_specializes_of_isAlgebraicAt` ([source](EnvelopeProperty/Alterations/StableModification/BlowDown/ClosedLocus.lean)) |
| T16 | §2.1, extension of valuations | valuation rings over `k°` = localizations of the integral closure at maximal ideals, stated without proof | proved (`Alterations.StableModification.Valuation.isLocalization_integralClosure`, `Alterations.StableModification.Valuation.exists_valuationSubring_of_isMaximal`) | Open | `Alterations.StableModification.Valuation.isLocalization_integralClosure` ([source](EnvelopeProperty/Alterations/StableModification/Valuation/Unramified.lean)); `Alterations.StableModification.Valuation.exists_valuationSubring_of_isMaximal` ([source](EnvelopeProperty/Alterations/StableModification/Valuation/Unramified.lean)) |
| T18 | Lemma 6.2.6 proof | filtration of `F/F^p` written as balls of radius `< n`, but `U_n` has elements of norm `n`; must be `≤ n` | Use the filtration `{ν ≤ n}`. | Open | No separate Lean assertion. |
| T19 | Lemma 6.2.6 proof | the element lying in `F^{p^i}` and constant is the remainder `f − f₀ − … − f_{i−1}`, not `f_i` (slip) | Apply the constant-field argument to `f − f₀ − … − f_{i−1}`. | Open | No separate Lean assertion. |
| T21 | Proposition 3.2.6 proof | reduction to affine pieces omits that the morphisms from the opens glue to a proper morphism | same centre argument as the covering statement | Open | No separate Lean assertion. |
| T22 | §3.2, generic étaleness of modifications | `K^s`-modifications are generically étale alterations needs generic freeness (EGA IV 6.9.2) for non-Noetherian `S` | Use generic freeness for the locally Noetherian base in the alteration theorem. | Open | No separate Lean assertion. |
| T23 | Lemma B.3 proof | **false step**: "if neither of two meeting exceptional trees contains the other, some double point joins `Y₁∖Y₂` to `Y₂∖Y₁`"; counterexample: components `a,b,c` with double points `a∩b`, `a∩c`, `Y₁ = a∪b`, `Y₂ = a∪c`. The derived bound `\|∂(Y₁∪Y₂)\| ≤ \|∂Y₁\|+\|∂Y₂\|−2` still holds | Use `∂(A∪B) + ∂(A∩B) + 2·cross(A,B) = ∂A + ∂B` and the boundary lower bound for the intersection. | Open | `Alterations.StableModification.CurvesField.IncidenceGraph.IsExceptionalTree.exists_isExceptional` ([source](EnvelopeProperty/Alterations/StableModification/CurvesField/Trees.lean)) |
| T25 | Lemma B.3, proof | "hence the stable blow down factors through `C̄′`" needs that a maximal exceptional tree is contracted by any blow-down without exceptional components | Apply the handshake identity and the bound on the total number of incident edges. | Open | `Alterations.StableModification.CurvesField.IncidenceGraph.sum_star_le` ([source](EnvelopeProperty/Alterations/StableModification/CurvesField/Trees.lean)) |
| T26 | Proposition 6.2.4, types 2/3 (statement, proof) | stated for any critical coset, but the reduction subtracts `a_{ij}u^{p^i} − a·a_{ij}^{1/p}u^{p^{i−1}}`, which stays in `Span(B)` only for `a ∈ k`; for `a ∈ L∖k` the induction does not close. Only special cosets (`a ∈ {0,1}`) are used later (Theorem 6.3.1) | State the induction for special cosets, where the parameter lies in the ground field; these are the cosets used in Theorem 6.3.1. | Open | No separate Lean assertion. |
| T27 | Proposition 2.2.1 proof | "`f_i` has a root in `m F̂°_i = F̂°°_i`": `m` undefined; if `K°°` the equality fails for ramified `F̂_i/K̂`; "all roots small" silently uses equal absolute values of conjugates over `K̂` | Use small roots in an algebraic closure of the completion, without the asserted ideal equality. | Open | No separate Lean assertion. |
| T28 | Proposition 2.2.1 proof | choosing `z ∈ K°°` with `x = x₀+zy` primitive and `zy ∈ m₁⋯mₙ` needs `y` integral over `K°`, but `y` is any primitive element | use `c·y`, `0 ≠ c ∈ K°` | Open | No separate Lean assertion. |
| T31 | Theorem 6.3.1, proof | "admits only immediate algebraic extensions; in particular any finite extension splits into a tower of p-extensions" asserted without argument | Use the trace argument to identify the finite ramification group as a p-group, then split the extension into degree-p steps. | Open | No separate Lean assertion. |
| T33 | Proposition 4.3.1 | "we will build these blow ups so that `x` is the only closed point of the modification locus; this allows to work locally at `x` since each such blow up extends trivially": extending a blow-up of a neighbourhood `U` by the identity needs its locus closed in `C`, which does not follow. Counterexample (reading "closed" as closed in `C`): `R` with primes `0 ⊊ 𝔭 ⊊ 𝔪`, `0 ≠ c ∈ 𝔭`, `π ∈ 𝔪∖𝔭`, `C = 𝔸¹_R`, `y` = point `T=0` of the closed fibre, `U = C∖{y}`; the blow-up of `U` along `(T,c)(T−1,π)` has locus `{z, x}` (`z`: `T=0` over `𝔭`; `x`: `T=1` over `𝔪`), closed in `U`, `x` its only point closed in `C`, but `y ∈ cl{z}`, so it does not extend by the identity. Related to T11. Also "semi-stable": the charts give strictly semi-stable | Over a strictly henselian base, separate the relevant closed component of the modification locus before extending the blow-up. | Open | `Alterations.StableModification.Blowups.isClosed_range_of_isProper_comp` ([source](EnvelopeProperty/Alterations/StableModification/Blowups/Extension.lean)) |
| T34 | Proposition 4.2.3 proof | "Lemma 4.2.2 implies `Γ(C′) ⊆ Γ(C″)`" needs `Γ(C′) = gen(Γ₀(C′)) ∪ Γ(C)` for `C′`, but Lemma 4.2.2 assumes `C′` normal (its bijection `Γ(C′) ≅ (C′/S)⁰` uses normality) and Proposition 4.2.3 does not | `Alterations.StableModification.ValCurves.gammaSet_eq_union` holds for every modification (composite valuation, Lemma 2.1.4, and a contraction lemma) | Open | `Alterations.StableModification.ValCurves.gammaSet_eq_union` ([source](EnvelopeProperty/Alterations/StableModification/ValCurves/ModificationsGamma.lean)) |
| T35 | Lemma 4.2.2 proof | "obviously the sets `Γ(C′)` and `Γ₀(C′)` are finite" needs the strict inequality of fibre transcendence degrees under proper specialization within a fibre (Abhyankar), besides the standing finite-height assumption | `Alterations.StableModification.ValCurves.one_add_fiberTrdeg_le_of_specializes`, `Alterations.StableModification.ValCurves.finite_gammaSet` | Open | `Alterations.StableModification.ValCurves.one_add_fiberTrdeg_le_of_specializes` ([source](EnvelopeProperty/Alterations/StableModification/ValCurves/ModificationsFiniteness.lean)); `Alterations.StableModification.ValCurves.finite_gammaSet` ([source](EnvelopeProperty/Alterations/StableModification/ValCurves/ModificationsFiniteness.lean)) |
| T37 | Lemma 6.3.3 | the hypothesis `\|α(x) − β(x)\| < ε\|x\|` for any `x ∈ K` fails at `x = 0`; completeness of the images is used implicitly | `≤` (or `x ≠ 0`) with complete `K`, `E`: `Alterations.StableModification.Valuation.Analytic.finrank_le_of_forall_exists_norm_sub_le` | Open | `Alterations.StableModification.Valuation.Analytic.finrank_le_of_forall_exists_norm_sub_le` ([source](EnvelopeProperty/Alterations/StableModification/Valuation/Analytic/Continuity.lean)) |
| T38 | Lemma 6.3.2 | the applications of the lemma use that the image of the embedding is `cl k(z′)`, which the lemma does not state and which needs `L` complete | stated and proved under `CompleteSpace L` (`Alterations.StableModification.Valuation.Analytic.exists_algHom_closureAdjoin`) | Open | `Alterations.StableModification.Valuation.Analytic.exists_algHom_closureAdjoin` ([source](EnvelopeProperty/Alterations/StableModification/Valuation/Analytic/Continuity.lean)) |
| T39 | Corollary 6.3.4 | finiteness of `l` over `cl k(x′)` is used without justification | transcendence exchange (`Alterations.StableModification.Valuation.Analytic.isAlgebraic_adjoin_of_isAlgebraic_adjoin`, `Alterations.StableModification.Valuation.Analytic.finiteDimensional_closureAdjoin`) | Open | `Alterations.StableModification.Valuation.Analytic.isAlgebraic_adjoin_of_isAlgebraic_adjoin` ([source](EnvelopeProperty/Alterations/StableModification/Valuation/Analytic/Continuity.lean)); `Alterations.StableModification.Valuation.Analytic.finiteDimensional_closureAdjoin` ([source](EnvelopeProperty/Alterations/StableModification/Valuation/Analytic/Continuity.lean)) |
| T40 | Theorem 6.3.1 proof | "no immediate extensions of degree `p`, hence stable" silently uses that a non-immediate degree-`p` step is Cartesian (defect theory) | For the degree-p steps in the argument, prove the alternatives for ramification and residue degrees and the Cartesian property of a non-immediate step. | Open | No separate Lean assertion. |
| T41 | Proposition 4.3.1 proof | the reduction applies the claim to the finite set `Γ₀(C′)` and then Proposition 4.2.3, but `Γ₀(C′)` is known finite only for normal `C′` (Lemma 4.2.2); Lemma 4.3.2 applies `cofinprop` to a possibly non-normal blow-up | Prove finiteness of `Γ₀` for every modification of a flat quasi-compact locally finite-type relative curve over a finite-height valuation ring; normality is unnecessary. | Open | `Alterations.StableModification.LocalUniformization.exists_dominates_of_isNormalScheme` ([source](EnvelopeProperty/Alterations/StableModification/LocalUniformization/Reduction.lean)); `Alterations.StableModification.Gluing.finite_gammaZeroSet_of_flat` ([source](EnvelopeProperty/Alterations/StableModification/Gluing/GammaFinite.lean)) |
| T42 | Proposition 4.3.1 stage 2 | "we can find `a ∈ K` and `π_a ∈ R`" with transcendental residue of `(T − a)/π_a`: `a ∈ R` is derived only afterwards and the case `\|a\| > 1` is not excluded explicitly (minor) | for `\|a\| > 1` the residue is that of `−a/π_a ∈ K`, algebraic (`Alterations.StableModification.LocalUniformization.exists_transcendental_residue_sub`) | Open | `Alterations.StableModification.LocalUniformization.exists_transcendental_residue_sub` ([source](EnvelopeProperty/Alterations/StableModification/LocalUniformization/ModelValuation.lean)) |
| T43 | Proposition 4.3.1 stage 2 | the perturbation `f + ωT` needs `\|T\| ≤ 1` and some `0 ≠ ω` with `\|ω\| < \|π\|` (nontrivial `v_K`); `f + ωT` is separable but may be reducible and must be factored again (imprecise wording, no counterexample) | `Alterations.StableModification.LocalUniformization.residue_mem_linearResidueField` (induction on degree) | Open | `Alterations.StableModification.LocalUniformization.residue_mem_linearResidueField` ([source](EnvelopeProperty/Alterations/StableModification/LocalUniformization/ModelValuation.lean)) |
| T44 | Proposition 4.3.1, with ("`C` is not assumed `S`-proper or even `S`-separated") | extends T33: even with the strict-henselian shrinking, a local blow-up need not extend when `C` is not separated. Counterexample: `A` with primes `0 ⊊ 𝔭 ⊊ 𝔪`, `0 ≠ π ∈ 𝔭`; `C` = two copies of `𝔸¹_A` glued off the closed origin, `x` = origin of copy 1, `Bl_{(π,T)}`: the locus `{z, x}` with `z = (T, 𝔭)` has `cl{z}` containing the origin of copy 2, and every neighbourhood of `x` contains `z` | Use separatedness of the relative curve when extending the local blow-up. | Open | `Alterations.StableModification.Blowups.exists_transport` ([source](EnvelopeProperty/Alterations/StableModification/Blowups/Transport.lean)) |
| T45 | Lemma 5.1(i) proof | "the semi-stable locus of `C′ → S` is open (e.g. use the local description from [dJ, 2.23])": de Jong 2.23 describes only completed local rings `Ô_{X,x} ≅ A′[[u,v]]/(Q − h)`, which gives no Zariski neighbourhood with nodal fibres (gap in the justification, not a false claim) | present the curve near a node as a quotient of a standard étale `R[X₀,X₁]`-algebra, show the kernel is principal `(g)` with invertible Hessian, classify nearby geometric points by Taylor expansion (`Alterations.StableModification.Curves.SemistableOpen.exists_isNodalCurve_nbhd`, `nodalLocus`) | Open | `Alterations.StableModification.Curves.SemistableOpen.exists_isNodalCurve_nbhd` ([source](EnvelopeProperty/Alterations/StableModification/Curves/SemistableOpen.lean)) |
| T46 | Theorem 2.1.8 proof ("`k₁` and `K₁` … the induced valuations of height one"), and Proposition 4.3.3 (Lemma 2.1.1 needs `O ∩ K(T)` of finite height) | finiteness of the height of the valuation of `L` (resp. `K(T)`) is used but not justified when only `O ∩ K` has finite height (in Temkin it would come from the reduction in Theorem 2.1.8). The height of `O` can exceed that of `O ∩ K`: `v(K^×) = ℤ × {0}`, `L = K(t)`, `v(t) = (0,1)` in lexicographic `ℤ²` gives `ht O = 2`, `ht(O ∩ K) = 1` | for `trdeg ≤ 1` no three overrings have the same trace on `K` (Abhyankar on residue fields), so `ht V ≤ 2·ht(V ∩ K) + 1` (`Alterations.StableModification.Valuation.MainUniformization.finite_primeSpectrum_of_trdeg_le_one`); induct on the height of the base | Open | `Alterations.StableModification.Valuation.MainUniformization.finite_primeSpectrum_of_trdeg_le_one` ([source](EnvelopeProperty/Alterations/StableModification/Valuation/MainUniformizationHeight.lean)) |
| T48 | Proposition 4.3.1 ("we can replace `R` with its localization beneath `x`" and "extends trivially") | extends T33 to a global base: a closed point of `C` can lie over a non-closed prime `𝔭` (e.g. `(πT − 1)` in `𝔸¹` over a DVR, residue field `Frac R`), so the blow-up lives over `R_𝔭` and its locus, closed in `C_𝔭`, need not be closed in `C`; counterexample for a point not closed in `C`: `R` with primes `0 ⊊ 𝔭 ⊊ 𝔪`, `z = 𝔭R[T] + (T)`: `{z}` is closed in `𝔸¹_{R_𝔭}` but its closure in `𝔸¹_R` contains `𝔪R[T] + (T)` | closedness from `x` closed in `C`, finiteness of the locus and a coarsening of the valuation at `O ∖ 𝔭` (`Alterations.StableModification.LocalUniformization.isClosed_of_finite_of_unique`) | Open | `Alterations.StableModification.LocalUniformization.isClosed_of_finite_of_unique` ([source](EnvelopeProperty/Alterations/StableModification/LocalUniformization/GlobalClosed.lean)) |
| T49 | Proposition 4.3.1 stage 2 ("we can actually assume that `C = Spec(A)`") | the reduction replaces `L` by `K(T)`; keeping a residue transcendental over `K̃` needs `L/K(T)` algebraic and Abhyankar for `L/K(T)`, and "centred at the generic point of `Z`" must be checked on `C` through the étale map (imprecision); also the smooth-generic-fibre hypothesis of 4.3.1 is not needed for the cofinality, and normality of strictly semistable curves (used via Proposition 3.5.2) is elementary over any normal base | Check transcendence after the residue extension and the centre condition through the étale map; use normality of strictly semistable curves over a normal base. | Open | `Alterations.StableModification.LocalUniformization.exists_transcendental_residue_comap` ([source](EnvelopeProperty/Alterations/StableModification/LocalUniformization/GlobalStageTools.lean)); `Alterations.StableModification.LocalUniformization.exists_smoothStep` ([source](EnvelopeProperty/Alterations/StableModification/LocalUniformization/GlobalSmoothStage.lean)); `Alterations.StableModification.LocalUniformization.isNormalScheme_of_isStrictlySemistable` ([source](EnvelopeProperty/Alterations/StableModification/LocalUniformization/GlobalNormal.lean)); `Alterations.StableModification.Curves.SemistableNormal.isNormalScheme_of_isNodalCurve` ([source](EnvelopeProperty/Alterations/StableModification/Curves/SemistableNormalScheme.lean)) |
| T50 | Appendix B | "`g(x)` is the geometric genus `h¹(𝒪)` of its irreducible component": it is `h¹` of the structure sheaf of the normalization of the component, not of the component (wording); Lemma B.1's `p_a = h¹` uses `h⁰(𝒪_C) = 1`, covered by the standing hypotheses | `p_a := 1 − χ`; `Alterations.StableModification.CurvesField.Genus.arithmeticGenus_eq_normalization` | Open | `Alterations.StableModification.CurvesField.Genus.arithmeticGenus_eq_normalization` ([source](EnvelopeProperty/Alterations/StableModification/CurvesField/GenusNormalization.lean)) |
| T51 | Proposition 4.3.1 proof (also Proposition 3.5.2) | "normality of semi-stable `S`-curves with smooth generic fiber" is used without proof or reference here (gap; the claim is true). Smooth generic fibre is necessary: `R[u,v]/(uv)` over a DVR is nodal with non-domain local ring at the origin | étale-local form `uv − c` of a node (Stacks 0CBY with a Morse lemma in families, no Artin approximation) plus normality of `O[u,v]/(uv − c)` for `c ≠ 0` and faithfully flat descent, over any integral normal base (no Noetherian hypothesis): `Alterations.StableModification.Curves.SemistableNormal.isNormalScheme_of_isNodalCurve` | Open | `Alterations.StableModification.Curves.SemistableNormal.isNormalScheme_of_isNodalCurve` ([source](EnvelopeProperty/Alterations/StableModification/Curves/SemistableNormalScheme.lean)) |
| T52 | Theorem 2.1.8 proof | "for any uniformizer `x` at `z`, … `x` induces an étale morphism from a neighborhood of `z` to `𝔸¹_k`" is false at smooth closed points with inseparable residue field (possible when `k` is separably closed but imperfect). Counterexample: `𝔸¹_k` at the point `T^p − c`, `c ∉ k^p`: smooth, residue field `k(c^{1/p}) ≠ k`, uniformizer `x = T^p − c` with `dx = 0`. An étale coordinate (`T`) exists but is not a uniformizer | Use an étale coordinate rather than an arbitrary uniformizer. In the algebraically closed case, the places used in the construction are rational. | Open | No separate Lean assertion. |
| T53 | Proposition 4.3.3 proof | "`Ā = k[T]`": the base ring is meant (`R′[T]`), not the field `k` (typo) | Read `Ā = R′[T]`. | Open | No separate Lean assertion. |
| T54 | Lemma 4.4.2 proof | Zariski connectedness over a non-Noetherian `S` justified by "`C′` comes from a curve defined over a noetherian base": the hypothesis of EGA III 4.3.2 (`π_*O = O`, or geometric connectedness of the generic fibre) must hold on the Noetherian model, and normality does not descend (gap; the statement is true) | Use direct connectedness arguments over finite-height valuation rings. The birational repair is proved for height one and in the stated projective higher-height setting. | Open | `Alterations.StableModification.Cohomology.Connected.isConnected_fiber_of_isProjectiveOver` ([source](EnvelopeProperty/Alterations/StableModification/Cohomology/Connected.lean)); `Alterations.StableModification.Cohomology.ConnectedBirational.isConnected_preimage_singleton_of_heightOne` ([source](EnvelopeProperty/Alterations/StableModification/Cohomology/ConnectedBirational.lean)); `Alterations.StableModification.Cohomology.ConnectedBirational.isConnected_preimage_singleton_of_generizations` ([source](EnvelopeProperty/Alterations/StableModification/Cohomology/ConnectedBirational.lean)); `Alterations.StableModification.Cohomology.ConnectedBirationalHeight.isConnected_preimage_singleton_of_isProjectiveOver` ([source](EnvelopeProperty/Alterations/StableModification/Cohomology/ConnectedBirationalHeight.lean)) |
| T55 | Corollary B.2 proof | uses without saying so that the normalization of `C` is the normalization of `C′` with the components of `Z` removed | Use the finite outer normalization in the generic points outside the contracted subcurve; no identification with a larger normalization is assumed. | Open | `Alterations.StableModification.CurvesField.Genus.isFinite_outerNormalization` ([source](EnvelopeProperty/Alterations/StableModification/CurvesField/StableDownScheme.lean)) |
| T57 | Lemma 4.4.4 proof | **false step**: "if `t` is a specialization of `s` then any irreducible component `Z′ ⊂ C′_t` lying in the Zariski closure of `Z` is exceptional". Counterexample: `V` of height 2, `0 ⊊ 𝔭 ⊊ 𝔪`, `s = 𝔭`, `t = 𝔪`, `C = C_k ×_k V`, `a ∈ 𝔭 ∖ 0`, `b ∈ 𝔪 ∖ 𝔭`; blow up `(u, a)` at a `k`-point (rational tails `E_s`, `E_t`, `E_t` in the closure of `E_s`), then `(v − c_j, b)` at three points of `E_t`: `C′` is semistable, `E_s` is exceptional, but `E_t ≅ ℙ¹` in its closure is contracted with 4 double points, not exceptional. The lemma itself is not refuted | The special fibre meets the closure in an exceptional tree, which contains an exceptional component; an individual component need not remain exceptional. | Open | `Alterations.StableModification.CurvesField.IncidenceGraph.IsExceptionalTree.exists_isExceptional` ([source](EnvelopeProperty/Alterations/StableModification/CurvesField/Trees.lean)) |
| T58 | §1, property (b) of `ω_{C/S}` | Rosenlicht's condition is written `Res_{x_i}(ν) = Res_{y_i}(ν)`; it should be `Res_{x_i}(ν) + Res_{y_i}(ν) = 0` (at `uv = 0` the generator `du/u = −dv/v` has residues `1` and `−1`). Sign error; the degree computation is unaffected | Require opposite residues on the two branches: their sum is zero. | Open | No separate Lean assertion. |
| T61 | Lemma 4.4.2 proof | "any finite, connected and dominant `S`-scheme maps bijectively onto `S`" is false unless the scheme is integral. Counterexample: `c ∈ 𝔪∖0`, `A = {(a,b) ∈ K°×K° : a ≡ b mod c}`: finite (generated by `(1,1)`, `(0,c)`), local, dominant, but `A[1/c] = K×K` has two points over `η` | Apply the assertion to an integral finite scheme, as provided by the Stein factorization of the integral source. | Open | No separate Lean assertion. |
| T62 | Proposition 4.5.1 proof | "Applying to them first Proposition [cofinprop]": the modifications `C′_i → C_i` from Proposition 3.2.6 are not normal in general, while the proof of Proposition 4.3.1 needs `Γ₀(C′_i)` finite, which Lemma 4.2.2 gives only for normal `C′` (extends T41 to §4.5; gap, not a false statement) | Use the finiteness result of T41 for the refinement modifications, without imposing normality. | Open | `Alterations.StableModification.Gluing.finite_gammaZeroSet_of_flat` ([source](EnvelopeProperty/Alterations/StableModification/Gluing/GammaFinite.lean)); `Alterations.StableModification.Gluing.exists_dominates_isStrictlySemistable_of_isModification` ([source](EnvelopeProperty/Alterations/StableModification/Gluing/GammaFinite.lean)) |
| T63 | Corollary 4.4.3 proof ("the stability criterion and the stable blow-down lemma imply …") | Applying Lemma B.3 (uniqueness of the stable blow-down over a field) needs two unstated facts: the fibres of `h′` and `h` must be read in one incidence graph, which must be anchored (true since `C_s` is a curve of pure dimension one), and stability of `C_st` must make the fibres of `h` a stable family, i.e. the description of the components of `(C_st)_s` by stars (stated there without proof). These are implicit steps in the proof | Read both contractions in one anchored incidence graph and prove stability of the fibres before applying the domination criterion. | Open | `Alterations.StableModification.BlowDown.Domination.fibresStable_of_fibreStable` ([source](EnvelopeProperty/Alterations/StableModification/BlowDown/DominationStable.lean)); `Alterations.StableModification.BlowDown.Domination.dominates_of_fibreStable` ([source](EnvelopeProperty/Alterations/StableModification/BlowDown/DominationStable.lean)) |
| T64 | Lemma 4.4.5 proof | The proof uses the openness of the semi-stable locus (Lemma 5.1(i)), which assumes geometric fibres of pure dimension one; this property of the blow-down `C″` is not established at that point (gap) | Prove purity of the one-dimensional fibres using proper surjectivity and the lower bound on component dimension. | Open | `Alterations.StableModification.BlowDown.pureOneDimensionalFibres_of_isNodalCurve_comp` ([source](EnvelopeProperty/Alterations/StableModification/BlowDown/ContractionDimension.lean)) |
| T65 | Lemma 4.4.5 proof (marks paragraph) | The stability criterion gives "at most one mark on `Z`, and `x` smooth if there is one", but not that `D″` is étale at `x` (that `D′ → C″` is a closed immersion there) (gap) | Over the henselian base, the marked component is a section; separatedness gives a closed immersion of its image. | Open | `Alterations.StableModification.BlowDown.isSemistablePair_blowDown` ([source](EnvelopeProperty/Alterations/StableModification/BlowDown/ContractionMarks.lean)) |
| T67 | Lemma 4.3.2 | "a semi-stable blow up whose center is contained in `D`" via `Bl_{(π,u)}`: the centre `V(u, π)` is a curve, not contained in `D`; the ideal `(u, π)` is invertible but not trivial off the node (it is `(π)` on `D(v)`), so the trivial extension is a modification but not visibly a blow-up of `C` | Blow up `(u,v,π)`, with `π` of minimal valuation among the coordinates of the sections through the node. The centre is supported at the node and all lifts land in the `π`-chart. | Open | `Alterations.StableModification.Gluing.SeparationProjective.exists_node_step_projective` ([source](EnvelopeProperty/Alterations/StableModification/Gluing/SeparationProjective.lean)); `Alterations.StableModification.Gluing.SeparationProjective.exists_separation_marks_projective` ([source](EnvelopeProperty/Alterations/StableModification/Gluing/SeparationProjective.lean)) |
| T68 | Lemma 5.1(ii) proof | The proof uses the incidence graph with genera of the contracted locus `Z_s̄`, which records neither where contracted components meet non-contracted ones nor the marks; both are needed to recognise an exceptional component (at most two special points) (minor gap) | Retain the marks and the incidence with noncontracted components when testing exceptional vertices; the openness argument then uses the full marked-curve data. | Open | No separate Lean assertion. |

## de Jong

Source: A. J. de Jong, *Smoothness, semi-stability and alterations*,
Publications Mathématiques de l’IHÉS 83 (1996).

| Finding | Location | Issue and correction | Status | Lean certificate |
|---|---|---|---|---|
| J1 | §2.20 | Read `U ⊂ S`, not `U ⊂ X`. | Open | No separate Lean assertion. |
| J3 | §4.18(e) | Read `sm(X/S)`, not `sm(X/Y)`. | Open | No separate Lean assertion. |
| J4 | §4.20 | The point `t_α` belongs to `T`, not `Z`. | Open | No separate Lean assertion. |
| J5 | §4.22 | The inverse image `ψ⁻¹(D)` lies on `Y′`, not `Y`. | Open | No separate Lean assertion. |
| J6 | §4.27, chart `t₁ ≠ 0` | The boundary product ends in `t_r`, not `t_s`. | Open | No separate Lean assertion. |
| J8 | §3.3 | The `t_i` form part of a regular system of parameters; they form the whole system only at the generic point of the intersection of the corresponding boundary components. | Open | No separate Lean assertion. |
| J9 | §3.3 | Justify `V(h) ⊆ V(∏ t_i) ⇒ h = ε ∏ t_i^{n_i}` using the principal ideal theorem and divisibility. | Open | No separate Lean assertion. |
| J10 | §3.4(ii) | Read “smooth over `S ∖ D`”, not `X ∖ D`. | Open | No separate Lean assertion. |
| J11 | §4.4 | Read “restraints”, not “restaints”. | Open | No separate Lean assertion. |
| J12 | §6.13 | The incidence construction uses `X ×_S ℙ_S^{d−1}`, not `S ×_S ℙ_S^{d−1}`; the ambient object is an `S`-variety. | Open | No separate Lean assertion. |
| J13 | §7.11 | The cardinality is taken after forming the union of the special-point and marked-point sets. | Open | No separate Lean assertion. |
| J2 | §2.20 | Equality of dimensions under an alteration needs justification in the stated setting. Use the dimension theorem for varieties over a field. | Open | `Alterations.StableModification.DeJong.topologicalKrullDim_eq_of_isAlteration` ([source](EnvelopeProperty/Alterations/StableModification/DeJong/Dimension.lean)) |
| J14 | §3.4 | Constancy of the local integer is asserted without proof. Use global colon ideals and stabilization on a finite affine cover. | Open | `Alterations.StableModification.Resolution.Global.exists_colonIter_stable` ([source](EnvelopeProperty/Alterations/StableModification/Resolution/GlobalInitial.lean)) |
| J15 | §3.4 | Compatibility of completion and blowing up is not made explicit. Describe the blow-up stalk as a localization of a chart and give generators of its completed maximal ideal. | Open | `Alterations.StableModification.Resolution.Global.exists_chart_maximalIdeal` ([source](EnvelopeProperty/Alterations/StableModification/Resolution/GlobalChart.lean)) |

## Complex-analytic sources

### Analytic-1. Włodarczyk: typographical slips in the analytic-resolution text

- **Location:** §5.5, Lemma 5.5.1(4) and Lemma 5.5.3(5).
- **Issue:** misplaced iteration exponents and an unbalanced parenthesis in
  the displayed transformed-ideal expressions.
- **Status:** Open.
- **Correction:** distinguish the iteration index from the exponent and use
  the transformed homogenized ideal with matching parentheses.
- **Lean certificate:** no separate Lean assertion for these misprints.

### Analytic-2. Darvas–Xia: the variable after the trace theorem

- **Location:** Darvas–Xia, *The trace operator of quasi-plurisubharmonic
  functions on compact Kähler manifolds*, the paragraph following Theorem 3.16.
- **Issue:** the display uses `φ`, whereas the theorem names the function `u`.
- **Status:** Open.
- **Correction:** use the same variable `u` in the display.
- **Lean certificate:** no separate Lean assertion for this variable mismatch.
