import EnvelopeProperty.Char0.AnalyticEtaleJacobian
import EnvelopeProperty.ComplexGeometry.Germs.SchemeCoordinateAnalyticDerivation
import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAnalyticOverlapAlgebra

/-!
# The same original affine scheme morphism has the whole analytic Jacobian ideal

Every coefficient map and holomorphic representative is manufactured from the
actual original scheme morphism and existing preferred coordinates. The generic
whole-germ differential comparison is applied to this SAME native regular map.
No analytic map, derivative, unit determinant or ideal comparison is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace EnvelopeProperty.Char0.NativeSchemeJacobian

open CategoryTheory AlgebraicGeometry ComplexSchemes Filter
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HolomorphicGerms AnalyticEtaleJacobian
open scoped Topology

variable {R : Type} [CommRing R] {Y : Scheme}
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Y ⟶ Spec (.of R)) (n : ℕ)
  [SmoothOfRelativeDimension n (π ≫ f)] (p : SchemeComplexPoint (π ≫ f))

local instance nativeJacobianAffineAlgebra :
    Algebra ℂ (SchemeCoordinateAffineRing (π ≫ f) n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart (π ≫ f) n p).val.map ≫ (π ≫ f))

/-- The actual original source coefficient map into the actual preferred affine chart. -/
def sourceAlgebraMap :
    letI := affinePointFieldAlgebra f
    R →ₐ[ℂ] SchemeCoordinateAffineRing (π ≫ f) n p := by
  let := affinePointFieldAlgebra f
  exact affineSchemeOverAlgebraMap f
    ((standardSmoothComplexAffineChart (π ≫ f) n p).val.map ≫ (π ≫ f))
    ((standardSmoothComplexAffineChart (π ≫ f) n p).val.map ≫ π) (Category.assoc _ _ _)

local instance nativeJacobianOriginalSourceAction :
    Algebra R (SchemeCoordinateAffineRing (π ≫ f) n p) :=
  (sourceAlgebraMap f π n p).toAlgebra

/-- Every original affine function has exactly its original algebraic coordinate partial as an analytic germ. -/
theorem partial_eq_etale (j : Fin n) (a : SchemeCoordinateAffineRing (π ≫ f) n p) :
    schemeCoordinateAnalyticDerivation (π ≫ f) n p j a =
      schemeCoordinateModelRegularAlgHom (π ≫ f) n p
        (etalePartialDeriv (standardSmoothComplexChartFreeGenerator (π ≫ f) n p)
          (schemeCoordinatePolynomialMap_etale (π ≫ f) n p) j a) :=
  partial_apply_normalized (schemeCoordinateModelRegularAlgHom (π ≫ f) n p)
    (standardSmoothComplexChartFreeGenerator (π ≫ f) n p)
    (schemeCoordinatePolynomialMap_etale (π ≫ f) n p)
    (fun i => standardSmoothComplexAlgebraPoint (π ≫ f) n p
      (standardSmoothComplexChartFreeGenerator (π ≫ f) n p i))
    (schemeCoordinateModelRegularAlgHom_freeGenerator (π ≫ f) n p) j a

/-- Every genuine etale coordinate change has an internally derived actual analytic unit Jacobian. -/
theorem coordinateJacobian_isUnit (v : Fin n → SchemeCoordinateAffineRing (π ≫ f) n p)
    (hv : (MvPolynomial.aeval (R := ℂ) v).toRingHom.Etale) :
    IsUnit (Matrix.of fun i j =>
      schemeCoordinateAnalyticDerivation (π ≫ f) n p j (v i)).det :=
  AnalyticEtaleJacobian.coordinateJacobian_isUnit
    (schemeCoordinateModelRegularAlgHom (π ≫ f) n p)
    (standardSmoothComplexChartFreeGenerator (π ≫ f) n p)
    (schemeCoordinatePolynomialMap_etale (π ≫ f) n p)
    (fun i => standardSmoothComplexAlgebraPoint (π ≫ f) n p
      (standardSmoothComplexChartFreeGenerator (π ≫ f) n p i))
    (schemeCoordinateModelRegularAlgHom_freeGenerator (π ≫ f) n p) v hv

/-- The WHOLE native analytic Jacobian ideal of the SAME original morphism is the extended algebraic ideal. -/
theorem jacobianIdeal_eq_map (v : Fin n → SchemeCoordinateAffineRing (π ≫ f) n p)
    (hv : (MvPolynomial.aeval (R := ℂ) v).toRingHom.Etale) :
    analyticSourceJacobianIdeal (R := R) (schemeCoordinateModelRegularAlgHom (π ≫ f) n p) =
      (affineRelativeJacobianIdeal (R := R) (etaleDifferentialBasis v hv)).map
        (schemeCoordinateModelRegularAlgHom (π ≫ f) n p).toRingHom :=
  analyticSourceJacobianIdeal_eq_map (schemeCoordinateModelRegularAlgHom (π ≫ f) n p)
    (standardSmoothComplexChartFreeGenerator (π ≫ f) n p)
    (schemeCoordinatePolynomialMap_etale (π ≫ f) n p)
    (fun i => standardSmoothComplexAlgebraPoint (π ≫ f) n p
      (standardSmoothComplexChartFreeGenerator (π ≫ f) n p i))
    (schemeCoordinateModelRegularAlgHom_freeGenerator (π ≫ f) n p) v hv

/-- The literal centered inverse-chart evaluation of an original source coefficient. -/
def sourceFunctionRepresentative (r : R) (z : ComplexModel n) : ℂ :=
  schemeCoordinateRegularRepresentative (π ≫ f) n p (sourceAlgebraMap f π n p r)
    (schemeCoordinateModelEquiv n z)

/-- The entire actual determinant reads the derivative matrix of the SAME original morphism's coefficients. -/
theorem jacobian_representative (w : Fin n → R) :
    ((analyticSourceJacobian (schemeCoordinateModelRegularAlgHom (π ≫ f) n p) w :
      HolGerm (ComplexModel n)) : Germ (𝓝 (0 : ComplexModel n)) ℂ) =
        (fun z : ComplexModel n => (Matrix.of fun i j =>
          fderiv ℂ (sourceFunctionRepresentative f π n p (w i)) z
            (EuclideanSpace.single j 1)).det) := by
  let hF (i : Fin n) : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (sourceFunctionRepresentative f π n p (w i)) z :=
    eventually_differentiableAt_comp_clm (schemeCoordinateModelEquiv n).toContinuousLinearMap
      (schemeCoordinateRegularRepresentative_holomorphic (π ≫ f) n p
        (sourceAlgebraMap f π n p (w i)))
  apply analyticSourceJacobian_representative _ w
    (fun i => sourceFunctionRepresentative f π n p (w i)) hF
  intro i
  change schemeCoordinateModelGermEquiv n
    (HolGerm.mk (schemeCoordinateRegularRepresentative (π ≫ f) n p (sourceAlgebraMap f π n p (w i)))
      (schemeCoordinateRegularRepresentative_holomorphic (π ≫ f) n p
        (sourceAlgebraMap f π n p (w i)))) = _
  rw [schemeCoordinateModelGermEquiv, HolGerm.comapEquiv_mk]
  rfl

end EnvelopeProperty.Char0.NativeSchemeJacobian
