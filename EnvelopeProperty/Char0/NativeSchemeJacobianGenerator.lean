import EnvelopeProperty.Char0.NativeSchemeJacobian
import EnvelopeProperty.Char0.AffineOpenChartMaps
import EnvelopeProperty.Char0.AnalyticJacobianGenerator
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# A genuine coordinate Jacobian generator for the original scheme morphism

The vector representative is assembled from the literal original coefficient
evaluations in the actual centered inverse source chart. Actual target etale
coordinates make its complex-Jacobian germ generate the whole Jacobian ideal.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace EnvelopeProperty.Char0.NativeSchemeJacobianGenerator

open CategoryTheory AlgebraicGeometry ComplexSchemes Filter
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HolomorphicGerms AnalyticEtaleJacobian AnalyticJacobianGenerator
open NativeSchemeJacobian HolomorphicGermJacobian
open scoped Topology

variable {R : Type} [CommRing R] {Y : Scheme}
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Y ⟶ Spec (.of R)) (n : ℕ)
  [SmoothOfRelativeDimension n (π ≫ f)] (p : SchemeComplexPoint (π ≫ f))

local instance nativeCoordinateJacobianAffineAlgebra :
    Algebra ℂ (SchemeCoordinateAffineRing (π ≫ f) n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart (π ≫ f) n p).val.map ≫ (π ≫ f))

local instance nativeCoordinateJacobianOriginalSourceAction :
    Algebra R (SchemeCoordinateAffineRing (π ≫ f) n p) :=
  (sourceAlgebraMap f π n p).toAlgebra

/-- The actual original target-coordinate functions after the actual morphism and inverse source chart. -/
def sourceCoordinateRepresentative (t : Fin n → R) (z : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 (fun i => sourceFunctionRepresentative f π n p (t i) z)

/-- Actual holomorphy of that literal vector representative, manufactured from the original regular functions. -/
theorem sourceCoordinateRepresentative_holomorphic (t : Fin n → R) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (sourceCoordinateRepresentative f π n p t) z := by
  have hi (i : Fin n) : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (sourceFunctionRepresentative f π n p (t i)) z :=
    eventually_differentiableAt_comp_clm (schemeCoordinateModelEquiv n).toContinuousLinearMap
      (schemeCoordinateRegularRepresentative_holomorphic (π ≫ f) n p
        (sourceAlgebraMap f π n p (t i)))
  filter_upwards [Filter.eventually_all.mpr hi] with z hz
  exact (differentiableAt_piLp 2).mpr hz

/-- The existing actual complex-Jacobian germ of the literal original coordinate representative. -/
def sourceCoordinateJacobian (t : Fin n → R) : HolGerm (ComplexModel n) :=
  jacobianGerm (sourceCoordinateRepresentative f π n p t)
    (sourceCoordinateRepresentative_holomorphic f π n p t)

/-- Exact whole-germ comparison with the actual determinant of the original coefficient derivatives. -/
theorem sourceCoordinateJacobian_eq (t : Fin n → R) :
    sourceCoordinateJacobian f π n p t =
      analyticSourceJacobian (schemeCoordinateModelRegularAlgHom (π ≫ f) n p) t := by
  symm
  apply analyticSourceJacobian_eq_jacobianGerm
  intro i
  change ((schemeCoordinateModelGermEquiv n
    (HolGerm.mk (schemeCoordinateRegularRepresentative (π ≫ f) n p (sourceAlgebraMap f π n p (t i)))
      (schemeCoordinateRegularRepresentative_holomorphic (π ≫ f) n p
        (sourceAlgebraMap f π n p (t i)))) : HolGerm (ComplexModel n)) :
        Germ (𝓝 (0 : ComplexModel n)) ℂ) = _
  rw [schemeCoordinateModelGermEquiv, HolGerm.comapEquiv_mk]
  rfl

/-- The ENTIRE generator reads back the actual existing complexJacobian of the literal original map. -/
theorem sourceCoordinateJacobian_source (t : Fin n → R) :
    ((sourceCoordinateJacobian f π n p t : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) =
        (DivisorialChangeOfVariables.complexJacobian (sourceCoordinateRepresentative f π n p t) :
          Germ (𝓝 (0 : ComplexModel n)) ℂ) :=
  jacobianGerm_source _ _

/-- Actual original target etale coordinates make the WHOLE native analytic ideal principal. -/
theorem jacobianIdeal_eq_span_sourceCoordinateJacobian (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) :
    analyticSourceJacobianIdeal (R := R) (schemeCoordinateModelRegularAlgHom (π ≫ f) n p) =
      Ideal.span {sourceCoordinateJacobian f π n p t} := by
  let := affinePointFieldAlgebra f
  let : IsScalarTower ℂ R (SchemeCoordinateAffineRing (π ≫ f) n p) :=
    IsScalarTower.of_algebraMap_eq fun c => ((sourceAlgebraMap f π n p).commutes c).symm
  rw [sourceCoordinateJacobian_eq]
  exact analyticSourceJacobianIdeal_eq_span (schemeCoordinateModelRegularAlgHom (π ≫ f) n p)
    (standardSmoothComplexChartFreeGenerator (π ≫ f) n p)
    (schemeCoordinatePolynomialMap_etale (π ≫ f) n p)
    (fun i => standardSmoothComplexAlgebraPoint (π ≫ f) n p
      (standardSmoothComplexChartFreeGenerator (π ≫ f) n p i))
    (schemeCoordinateModelRegularAlgHom_freeGenerator (π ≫ f) n p) t ht

/-- Actual etale geometry produces the actual analytic unit; no determinant certificate is supplied. -/
theorem sourceCoordinateJacobian_isUnit [Etale π] (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) :
    IsUnit (sourceCoordinateJacobian f π n p t) := by
  let := affinePointFieldAlgebra f
  let : IsScalarTower ℂ R (SchemeCoordinateAffineRing (π ≫ f) n p) :=
    IsScalarTower.of_algebraMap_eq fun c => ((sourceAlgebraMap f π n p).commutes c).symm
  have hs : Spec.map (CommRingCat.ofHom
      (algebraMap R (SchemeCoordinateAffineRing (π ≫ f) n p))) =
      (standardSmoothComplexAffineChart (π ≫ f) n p).val.map ≫ π :=
    affineSchemeOverAlgebraMap_spec _ _ _ (Category.assoc _ _ _)
  have hA : (algebraMap R (SchemeCoordinateAffineRing (π ≫ f) n p)).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)
      (φ := CommRingCat.ofHom (algebraMap R (SchemeCoordinateAffineRing (π ≫ f) n p)))).mp
        (by rw [hs]; infer_instance)
  rw [sourceCoordinateJacobian_eq]
  exact NativeSchemeJacobian.coordinateJacobian_isUnit f π n p _
    (etale_aeval_algebraMap t ht hA)

end EnvelopeProperty.Char0.NativeSchemeJacobianGenerator
