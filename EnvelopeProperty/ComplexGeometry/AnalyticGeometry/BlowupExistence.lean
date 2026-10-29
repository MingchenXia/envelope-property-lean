import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.BlowupUniqueness
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.BlowupMonomialCharts
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.BlowupSpaceUniversal

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Existence of the blowup along a smooth centre

Source: Griffiths--Harris, Chapter 4 §6; Voisin I, §3.3; the construction follows Demailly,
*Complex Analytic and Differential Geometry*, Chapter VII §12.

`exists_isBlowupAlong` below: the blowup `IsBlowupAlong n C π` along a nowhere-dense closed
complex submanifold exists, and the witness is Demailly's blowup
`AnalyticGeometry.BlowupConstruction.blowupProj : BlowupSpace n C → X`, built in

* `AnalyticGeometry.BlowupSpaceTangent` -- the tangent space `T_yC` of the centre (common kernel of the
  differentials of the germs of `𝓘_C`);
* `AnalyticGeometry.BlowupSpace` -- the point set `(X \ C) ⊔ P(N_C)` and Demailly's monomial charts `τ̃ⱼ`;
* `AnalyticGeometry.BlowupSpaceRatio` -- the quotients `(f/τⱼ)~` are holomorphic in the charts;
* `AnalyticGeometry.BlowupSpaceAtlas`, `AnalyticGeometry.BlowupSpaceManifold` -- the atlas is holomorphic, the space
  is a Hausdorff, second countable complex manifold and `π` is holomorphic;
* `AnalyticGeometry.BlowupSpaceUniversal` -- `π*𝓘_C` is invertible and every holomorphic `g : Z → X` with
  `g*𝓘_C` invertible (test manifolds `Z` of every dimension) lifts uniquely and holomorphically
  (`isBlowupAlong_blowupProj`).

`AnalyticGeometry.BlowupUniqueness` shows the object is unique up to a unique isomorphism over `X`, so any
other construction may be compared with this one.
-/

open Set
open scoped Manifold ContDiff

universe u

namespace ComplexGeometry.AnalyticGeometry.BlowupExistence

open Pluripotential Pluripotential.HolomorphicIdealSheaves Pluripotential.BlowupSequences

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **The blowup of a complex manifold along a nowhere-dense closed complex submanifold
exists**: the witness is Demailly's blowup
`BlowupConstruction.blowupProj : BlowupSpace n C → X`, by
`BlowupConstruction.isBlowupAlong_blowupProj`. -/
theorem exists_isBlowupAlong (C : Set X) (hC : IsClosedSubmanifold n C)
    (hCint : interior C = ∅) :
    ∃ (Z : Type u) (_ : TopologicalSpace Z) (_ : ChartedSpace (ComplexModel n) Z)
      (_ : IsComplexManifold n Z) (π : Z → X), IsBlowupAlong n C π := by
  have : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
  exact ⟨BlowupConstruction.BlowupSpace n C, inferInstance, inferInstance, inferInstance,
    BlowupConstruction.blowupProj n C, BlowupConstruction.isBlowupAlong_blowupProj hCint⟩

end

end ComplexGeometry.AnalyticGeometry.BlowupExistence
