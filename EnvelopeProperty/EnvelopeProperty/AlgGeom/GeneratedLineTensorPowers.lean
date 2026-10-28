import EnvelopeProperty.AlgGeom.GeneratedLineProjectiveTwist
import EnvelopeProperty.AlgGeom.PositivePowerProjectiveGeneration

/-! # EVERY actual tensor power of a genuine original finite globally generated line -/
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.GeneratedLineTensorPowers
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- EVERY actual original tensor power has genuine finite original global
generators, constructed from the SAME original generated-line morphism. -/
theorem exists_generatingSections_tensorPower {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of R)) (B : X.Modules)
    (hB : IsInvertible B) (G : B.GeneratingSections) (hG : G.IsFiniteType) (r : ℕ) :
    ∃ H : (CanonicalGeometry.bundleTensorPower B r).GeneratingSections, H.IsFiniteType := by
  obtain ⟨n, f, _c, e, _hf, _hc⟩ := GeneratedLineProjectiveTwist.exists_projective_morphism p hB G hG
  let P := coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) (r : ℤ)
  let Q := coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) 1
  let E : (Scheme.Modules.pullback f).obj P ≅ CanonicalGeometry.bundleTensorPower B r :=
    (Scheme.Modules.pullback f).mapIso
      (PositivePowerProjectiveGeneration.twistPowerIso (0 : Fin (n + 1)) r).symm ≪≫
        BundleTensorPowerPullback.pullbackIso f Q r ≪≫ BundleTensorPowerPullback.powerIso e r
  let F := ProjectiveTwistGlobalGeneration.generatingSections (R := R) (0 : Fin (n + 1)) r
  let : F.IsFiniteType := ProjectiveTwistGlobalGeneration.generatingSections_isFiniteType _ _
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections f F
  let : H.IsFiniteType := ClosedProjectiveGlobalGeneration.pullback_generatingSections_isFiniteType f F
  exact ⟨H.ofEpi E.hom, inferInstance⟩
end EnvelopeProperty.GeneratedLineTensorPowers
