import EnvelopeProperty.AlgGeom.FiniteSchemeNormalization
import EnvelopeProperty.AlgGeom.NormalSchemeNormalization
import EnvelopeProperty.AlgGeom.IntegralSchemeDimension
import EnvelopeProperty.AlgGeom.CurveDenominatorCartier
import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv

/-! # Genuine smoothness of SAME actual normal curves and native curve normalizations -/
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.NormalCurveSmooth

/-- True original normal curve stalks and actual finite-type perfect-field
geometry internally derive smoothness of the SAME original structure map. -/
theorem smooth_of_normal_curve {F : Type u} [Field F] [PerfectField F]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of F)) [LocallyOfFiniteType f]
    (hNorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : topologicalKrullDim X ≤ 1) : Smooth f := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  apply (AlgebraicGeometry.Scheme.smooth_iff_isRegular f).mpr
  constructor
  intro x
  let := CurveDenominatorCartier.stalk_isPrincipalIdealRing hdim hNorm x
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing (X.presheaf.stalk x)

/-- The SAME actual native normalization of an original integral finite-type
curve is smooth over the original perfect field, with no supplied normality/regularity. -/
theorem normalization_smooth {F : Type u} [Field F] [PerfectField F]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of F)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) :
    Smooth (IntegralSchemeNormalization.projection X ≫ f) := by
  let Z := IntegralSchemeNormalization.normalization X
  let ν := IntegralSchemeNormalization.projection X
  let : IsIntegral Z := inferInstanceAs (IsIntegral (IntegralSchemeNormalization.genericMap X).normalization)
  let : IsFinite ν := IntegralSchemeNormalization.projection_isFinite F X f
  let : IsIntegralHom ν := IntegralSchemeNormalization.projection_isIntegralHom X
  apply smooth_of_normal_curve (ν ≫ f)
  · exact IntegralSchemeNormalization.stalk_isIntegrallyClosed X
  · exact IntegralSchemeDimension.topologicalKrullDim_le_of_isIntegralHom ν 1 hdim

end EnvelopeProperty.NormalCurveSmooth
