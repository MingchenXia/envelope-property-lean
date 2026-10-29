import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.KahlerCurrentRegularizationInterface
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.KahlerCurrentRegularizationAlgebraicApproximation

set_option autoImplicit false

/-!
# Demailly regularization of Kähler currents

Source: Demailly, *Regularization of closed positive currents and intersection
theory* (1992), Theorem 1.1 and Proposition 3.7; Boucksom, *Divisorial Zariski
decompositions*, Theorem 2.4 and the proof of Theorem 3.17; CT22, Section 2
("By Demailly's regularization, big classes contain Kähler currents with
analytic singularities").

Let `T = θ + ddᶜφ ≥ ω₀` be a Kähler current on a compact Kähler manifold.
Demailly's Bergman-kernel regularization produces quasi-psh functions
`φ_m = (1/2m) log ∑ |σ_{m,j}|² + O(1)` with `θ + ddᶜφ_m ≥ ω₀ - ε_m ω`,
`ε_m → 0`, analytic singularities along the multiplier ideal `𝓘(mφ)`, and
`ν(φ, x) - n/m ≤ ν(φ_m, x) ≤ ν(φ, x)`.  For `m` large `θ + ddᶜφ_m` is again a
Kähler current, and a point where `φ_m = -∞` has `ν(φ_m, x) > 0`, hence
`ν(φ, x) > 0`.

The singularities are asserted in two compatible forms: a rational coefficient with a bounded remainder along a
coherent ideal (`HasAnalyticSingularities`) and the separately proved fact that
the potential is smooth off its polar set
(`HasManifoldAnalyticSingularitiesSmoothOffPole`).  The latter is sufficient
for the admissible restricted-current presentations, whose definition uses the
same smooth-off-pole convention.  No claim is made that a bounded logarithmic
remainder extends smoothly across the poles.

**The classical input.**  Following Boucksom, the theorem below is
derived from Demailly's approximation theorem as one named classical input,
`KahlerCurrentRegularizationAlgebraicApproximation.demailly1992_exists_algebraicApproximation_analyticSingularities`
(Boucksom, *On the volume of a line bundle*, Theorem 2.6, with `γ = 0` and clause (i) in both conventions).  The
deduction —
the shift by the Kähler lower bound, the choice of an index with `δ_k < 1`, the
reconstruction of a Kähler current in the same class, and the two Lelong steps —
is proved there.

This module also imports `KahlerCurrentRegularizationInterface`, which records the ordered regularized-max Bergman
construction of `AnalyticGeometry.DemaillyRegularizedMaxBergmanDataInterface` (Bergman kernels of
weighted `L²` spaces on coordinate balls, Ohsawa--Takegoshi at the needed
generality, Nadel coherence, Skoda-type Lelong comparison, and the global
gluing); the theorem below does not depend on it.  `exists_kahlerCurrent_poleSet_eq_nonKahlerLocus` is proved
from the theorem below together with `AnalyticGeometry.AnalyticNoetherProperty`
and `AnalyticGeometry.KahlerCurrentMax`.
-/

open Set

namespace ComplexGeometry.AnalyticGeometry.KahlerCurrentRegularization

open Pluripotential Pluripotential.PositiveClasses Pluripotential.NonKahlerLocus
  Pluripotential.NumericalRestrictedVolumeScaffold Pluripotential.GlobalAnalyticSingularities

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Source-interface wrapper** (Demailly regularization, Kähler-current form).
Every Kähler current in a class on a compact complex manifold is dominated by a
Kähler current in the same class with analytic singularities whose polar set lies
in the set where the original current has positive Lelong number.  The
regularized potential is smooth away from that polar set. -/
theorem exists_kahlerCurrent_poleSet_subset_lelongNumber_pos [CompactSpace M]
    {alpha : RealBottChern n M} (T : KahlerCurrent alpha) :
    ∃ S : KahlerCurrent alpha,
      HasAnalyticSingularities (n := n) S.potential ∧
        HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) S.potential ∧
        poleSet S.potential ⊆ {x | 0 < lelongNumber (n := n) T.potential x} :=
  KahlerCurrentRegularizationAlgebraicApproximation.exists_kahlerCurrent_poleSet_subset_lelongNumber_pos T

end

end ComplexGeometry.AnalyticGeometry.KahlerCurrentRegularization
