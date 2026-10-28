import EnvelopeProperty.Local.PLIdealNormalizedModels
import EnvelopeProperty.AlgGeom.NativeProjectiveVarietyComparison
import EnvelopeProperty.AlgGeom.ProjectiveBlowupSequence
import EnvelopeProperty.AlgGeom.CurveFiniteMapDegrees
import EnvelopeProperty.Projective.FactorizationBaseChange

/-! # Genuine polynomial projectivity of SAME normalized PL models over ANY original field -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Polynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint IntegralSchemeNormalization
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The SAME original native variety-product map has a true finite polynomial
projective embedding over the SAME original k[t]. -/
theorem nativeProductStructure_isProjectiveFactorization : IsProjectiveFactorization X.nativeProductStructure := by
  have h := ProjectiveFactorizationBaseChange.baseChange (S := Polynomial k)
    X.nativeStructure X.originalNativeStructure_isProjectiveFactorization
  have hi := h.comp_isClosedImmersion X.nativeProductModelIso.hom inferInstance
  change IsProjectiveFactorization (X.nativeProductModelIso.hom ≫
    pullback.snd X.nativeStructure (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) at hi
  rwa [X.nativeProductModelIso_over_base] at hi

/-- The SAME actual original simultaneous blowup remains polynomially
projective over its original parameter base. -/
theorem simultaneousIdealBlowupStructure_isProjectiveFactorization
    (I J : X.NativeProductModel.IdealSheafData) :
    IsProjectiveFactorization (X.simultaneousIdealBlowupStructure I J) :=
  ProjectiveBlowupSequence.blowup_isProjectiveFactorization (I * J) X.nativeProductStructure
    X.nativeProductStructure_isProjectiveFactorization

variable (I J : X.NativeProductModel.IdealSheafData)
  (hfin : ∀ w : X.an,
    modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
    modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)

/-- Actual finite normalization of the SAME original blowup, over ANY field;
no perfectness or finite-normalization certificate is assumed. -/
theorem normalizedSimultaneousIdealBlowupProjection_isFinite_anyField :
    IsFinite (X.normalizedSimultaneousIdealBlowupProjection I J hfin) := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) :=
    X.simultaneousIdealBlowup_isIntegral_of_finiteLogs I J X.triv (hfin X.triv).1 (hfin X.triv).2
  let : LocallyOfFiniteType (X.simultaneousIdealBlowupFieldStructure I J) :=
    X.simultaneousIdealBlowupFieldStructure_locallyOfFiniteType I J
  exact IntegralSchemeNormalization.projection_isFinite k (X.simultaneousIdealBlowup I J)
    (X.simultaneousIdealBlowupFieldStructure I J)

/-- The SAME actual normalized original PL model has an internally constructed
finite polynomial projective factorization over SAME k[t], over ANY original field. -/
theorem normalizedSimultaneousIdealBlowupStructure_isProjectiveFactorization :
    IsProjectiveFactorization (X.normalizedSimultaneousIdealBlowupStructure I J hfin) := by
  let := X.normalizedSimultaneousIdealBlowupProjection_isFinite_anyField I J hfin
  exact CurveFiniteMapDegrees.finite_comp_projectiveFactorization
    (X.simultaneousIdealBlowupStructure I J) (X.simultaneousIdealBlowupStructure_isProjectiveFactorization I J)
    (X.normalizedSimultaneousIdealBlowupProjection I J hfin)

/-- The SAME actual original normalized model is proper over the SAME
polynomial base over ANY original field, without perfectness. -/
theorem normalizedSimultaneousIdealBlowupStructure_isProper_anyField :
    IsProper (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
  (X.normalizedSimultaneousIdealBlowupStructure_isProjectiveFactorization I J hfin).isProper

end EnvelopeProperty.ProjSubvariety
