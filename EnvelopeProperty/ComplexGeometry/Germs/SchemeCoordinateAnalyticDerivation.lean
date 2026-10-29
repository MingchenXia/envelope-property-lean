import EnvelopeProperty.ComplexGeometry.Germs.SchemeCoordinateModelTransport
import EnvelopeProperty.ComplexGeometry.Germs.SchemeCoordinateEtale
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.HolomorphicGermCoordinateDerivation

/-!
# Actual analytic derivatives of every original smooth affine function

The same original regular germ map is a complex algebra map into the existing
Euclidean holomorphic model. Restricting actual analytic differentiation gives
derivations on the original affine algebra, with whole representative readback
and internally proved coordinate values. No derivative comparison is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace HolomorphicGerms

open CategoryTheory AlgebraicGeometry ComplexSchemes Filter
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HironakaHolomorphicJetMonomialSpan HolomorphicGermCoordinateDerivation
open scoped Topology

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f)

local instance analyticDerivationAffineAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- The same original affine regular map in the actual Euclidean model, with its scalar law. -/
def schemeCoordinateModelRegularAlgHom :
    SchemeCoordinateAffineRing f n p →ₐ[ℂ] HolGerm (ComplexModel n) where
  toRingHom := (schemeCoordinateModelGermEquiv n).toRingHom.comp (schemeCoordinateRegularGerm f n p)
  commutes' c := by
    change schemeCoordinateModelGermEquiv n
      (schemeCoordinateRegularGerm f n p (algebraMap ℂ _ c)) = _
    rw [schemeCoordinateRegularGerm_scalar, schemeCoordinateModelGermEquiv_const]
    rfl

/-- Actual original free generators have literal translated coordinate germs. -/
theorem schemeCoordinateModelRegularAlgHom_freeGenerator (i : Fin n) :
    schemeCoordinateModelRegularAlgHom f n p (standardSmoothComplexChartFreeGenerator f n p i) =
      coordinateGerm i + HolGerm.constHom
        (standardSmoothComplexAlgebraPoint f n p (standardSmoothComplexChartFreeGenerator f n p i)) := by
  have h := congrArg (schemeCoordinateModelGermEquiv n)
    (schemeCoordinateCenteredFreeGenerator_germ f n p i)
  rw [schemeCoordinateCenteredFreeGenerator, map_sub, schemeCoordinateRegularGerm_scalar,
    map_sub, schemeCoordinateModelGermEquiv_const, schemeCoordinateModelGermEquiv_coordinate] at h
  exact sub_eq_iff_eq_add.mp h

/-- Actual analytic differentiation restricted to the original affine algebra and its original action. -/
def schemeCoordinateAnalyticDerivation (j : Fin n) :
    letI := (schemeCoordinateModelRegularAlgHom f n p).toAlgebra
    Derivation ℂ (SchemeCoordinateAffineRing f n p) (HolGerm (ComplexModel n)) :=
  along (schemeCoordinateModelRegularAlgHom f n p) j

/-- The actual original free coordinates internally derive the Kronecker derivative matrix. -/
theorem schemeCoordinateAnalyticDerivation_freeGenerator (i j : Fin n) :
    schemeCoordinateAnalyticDerivation f n p j (standardSmoothComplexChartFreeGenerator f n p i) =
      if i = j then 1 else 0 :=
  along_coordinate (schemeCoordinateModelRegularAlgHom f n p)
    (standardSmoothComplexChartFreeGenerator f n p)
    (fun i => standardSmoothComplexAlgebraPoint f n p (standardSmoothComplexChartFreeGenerator f n p i))
    (schemeCoordinateModelRegularAlgHom_freeGenerator f n p) i j

/-- WHOLE derivative-germ readback is the derivative of the same actual inverse-chart evaluation. -/
theorem schemeCoordinateAnalyticDerivation_source (j : Fin n)
    (a : SchemeCoordinateAffineRing f n p) :
    ((schemeCoordinateAnalyticDerivation f n p j a : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) =
        (fun z : ComplexModel n => fderiv ℂ
          (fun w : ComplexModel n =>
            schemeCoordinateRegularRepresentative f n p a (schemeCoordinateModelEquiv n w)) z
          (EuclideanSpace.single j 1)) := by
  change ((coordinatePartial j (schemeCoordinateModelGermEquiv n
    (HolGerm.mk (schemeCoordinateRegularRepresentative f n p a)
      (schemeCoordinateRegularRepresentative_holomorphic f n p a))) :
        HolGerm (ComplexModel n)) : Germ (𝓝 (0 : ComplexModel n)) ℂ) = _
  rw [schemeCoordinateModelGermEquiv, HolGerm.comapEquiv_mk, coordinatePartial_mk]
  rfl

end HolomorphicGerms
