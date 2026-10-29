import EnvelopeProperty.AlgGeom.ProjectiveLineFunctionField
import EnvelopeProperty.AlgGeom.SpecifiedFieldNormalizationFunctionField
import EnvelopeProperty.AlgGeom.IntegralSchemeDimension

/-! # An ACTUAL normal proper residual curve for the SAME finite rational field extension -/

open AlgebraicGeometry CategoryTheory TopologicalSpace Alterations
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.ResidualFunctionFieldCurve
variable (k L : Type u) [Field k] [Field L] [Algebra (RatFunc k) L]

/-- The SAME  specified rational-field embedding, through the actual native P1 function field. -/
abbrev functionFieldAlgebra : Algebra (projectiveSpace k 1).functionField L :=
  ((algebraMap (RatFunc k) L).comp (ProjectiveLineFunctionField.functionFieldEquiv k).toRingHom).toAlgebra

/-- Original finiteness transfers across the genuine original P1 function-field equivalence. -/
theorem functionField_finite [FiniteDimensional (RatFunc k) L] :
    letI := functionFieldAlgebra k L
    FiniteDimensional (projectiveSpace k 1).functionField L := by
  let := functionFieldAlgebra k L
  apply RingHom.finite_algebraMap.mp
  exact (RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite (RatFunc k) L)).comp
    (RingHom.Finite.of_surjective (ProjectiveLineFunctionField.functionFieldEquiv k).toRingHom (ProjectiveLineFunctionField.functionFieldEquiv k).surjective)

/-- The ACTUAL normalization of the original projective line inside the SAME specified field L. -/
abbrev model : Scheme.{u} :=
  letI := functionFieldAlgebra k L
  SpecifiedFieldSchemeNormalization.normalization (projectiveSpace k 1) L

/-- The original native P1 projection of the SAME actual residual-field model. -/
def projection : model k L ⟶ projectiveSpace k 1 :=
  letI := functionFieldAlgebra k L
  SpecifiedFieldSchemeNormalization.projection (projectiveSpace k 1) L

/-- The SAME original coefficient-field structure morphism of the ACTUAL residual model. -/
def baseMap : model k L ⟶ Spec (.of k) := projection k L ≫ projectiveSpaceStructure k 1

/-- The ACTUAL whole original residual-field model is integral. -/
instance model_isIntegral : IsIntegral (model k L) := by
  let := functionFieldAlgebra k L
  exact SpecifiedFieldSchemeNormalization.normalization_isIntegral (projectiveSpace k 1) L

/-- Every original actual residual-model stalk is normal, with no separability or perfectness premise. -/
theorem stalk_isIntegrallyClosed [FiniteDimensional (RatFunc k) L] (x : model k L) :
    IsIntegrallyClosed ((model k L).presheaf.stalk x) := by
  let := functionFieldAlgebra k L
  let := functionField_finite k L
  exact SpecifiedFieldSchemeNormalization.stalk_isIntegrallyClosed (projectiveSpace k 1) L x

/-- Original finite rational-field degree gives a TRUE finite projection of the SAME model to native P1. -/
theorem projection_isFinite [FiniteDimensional (RatFunc k) L] : IsFinite (projection k L) := by
  let := functionFieldAlgebra k L
  let := functionField_finite k L
  exact SpecifiedFieldSchemeNormalization.projection_isFinite (projectiveSpace k 1) L (projectiveSpaceStructure k 1)

/-- The ACTUAL original residual-model structure is genuinely proper over the SAME coefficient field. -/
theorem structure_isProper [FiniteDimensional (RatFunc k) L] : IsProper (baseMap k L) := by
  let := projection_isFinite k L
  unfold baseMap
  infer_instance

/-- Actual finite-integral dimension comparison derives the whole original residual-model curve bound. -/
theorem dimension_le [FiniteDimensional (RatFunc k) L] : topologicalKrullDim (model k L) ≤ 1 := by
  let := projection_isFinite k L
  exact IntegralSchemeDimension.topologicalKrullDim_le_of_isIntegralHom (projection k L) 1
    (IntegralSchemeDimension.projectiveLine_dimension_le k)

/-- The SAME actual model's whole original native canonical function field is the original specified L. -/
def fieldEquiv [FiniteDimensional (RatFunc k) L] : (model k L).functionField ≃+* L := by
  let := functionFieldAlgebra k L
  let := functionField_finite k L
  exact SpecifiedFieldSchemeNormalization.functionFieldEquiv (projectiveSpace k 1) L
    (Alterations.Geometry.Segre.coordinateChartInclusion (R := k) (0 : Fin 2)).opensRange
    (isAffineOpen_opensRange _)

/-- EVERY original polynomial on the native P1 chart is retained by the actual projection
and the SAME specified rational-function-field embedding. -/
theorem fieldEquiv_projection_polynomial [FiniteDimensional (RatFunc k) L] (p : k[X]) :
    letI := functionFieldAlgebra k L
    let U := (Alterations.Geometry.Segre.coordinateChartInclusion (R := k) (0 : Fin 2)).opensRange
    letI : Nonempty (projection k L ⁻¹ᵁ U) :=
      SpecifiedFieldSchemeNormalization.affinePreimage_nonempty (projectiveSpace k 1) L U
    fieldEquiv k L ((model k L).germToFunctionField (projection k L ⁻¹ᵁ U)
      ((projection k L).app U ((ProjectiveLineFunctionField.chartRingEquiv k).symm p))) =
      algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) p) := by
  let := functionFieldAlgebra k L
  let := functionField_finite k L
  let U := (Alterations.Geometry.Segre.coordinateChartInclusion (R := k) (0 : Fin 2)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  let : Nonempty (projection k L ⁻¹ᵁ U) :=
    SpecifiedFieldSchemeNormalization.affinePreimage_nonempty (projectiveSpace k 1) L U
  have hn := SpecifiedFieldSchemeNormalization.functionFieldEquiv_projection_section
    (projectiveSpace k 1) L U hU ((ProjectiveLineFunctionField.chartRingEquiv k).symm p)
  refine hn.trans ?_
  change algebraMap (RatFunc k) L
    (ProjectiveLineFunctionField.functionFieldEquiv k ((projectiveSpace k 1).germToFunctionField U
      ((ProjectiveLineFunctionField.chartRingEquiv k).symm p))) = _
  exact congrArg (algebraMap (RatFunc k) L)
    (ProjectiveLineFunctionField.functionFieldEquiv_polynomial k p)

/-- The original nonzero finite rational extension gives a TRUE dimension-one model,
using actual original affine prime chains, not a supplied curve-dimension hypothesis. -/
theorem dimension_eq_one [FiniteDimensional (RatFunc k) L] :
    topologicalKrullDim (model k L) = 1 := by
  apply le_antisymm (dimension_le k L)
  let X := projectiveSpace k 1
  let U := (Alterations.Geometry.Segre.coordinateChartInclusion (R := k) (0 : Fin 2)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  let := functionFieldAlgebra k L
  let := SpecifiedFieldSchemeNormalization.sectionExtensionAlgebra X L U
  let := SpecifiedFieldSchemeNormalization.sectionExtensionAlgebra_isScalarTower X L U
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let V := projection k L ⁻¹ᵁ U
  have hV : IsAffineOpen V := SpecifiedFieldSchemeNormalization.affinePreimage_isAffineOpen X L U hU
  have hinj : Function.Injective (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)) := by
    intro a b hab
    apply IsFractionRing.injective Γ(X, U) X.functionField
    apply (algebraMap X.functionField L).injective
    exact congrArg Subtype.val hab
  have hA : ringKrullDim Γ(X, U) = 1 :=
    (ringKrullDim_eq_of_ringEquiv (ProjectiveLineFunctionField.chartRingEquiv k)).trans
      (by simp [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field])
  have hC : 1 ≤ ringKrullDim (integralClosure Γ(X, U) L) := by
    rw [← hA]
    exact IntegralSchemeDimension.ringKrullDim_le_of_isIntegral_of_injective _
      (algebraMap_isIntegral_iff.mpr inferInstance) hinj
  have hB : 1 ≤ ringKrullDim Γ(model k L, V) :=
    hC.trans_eq (ringKrullDim_eq_of_ringEquiv
      (SpecifiedFieldSchemeNormalization.affineSectionIso X L U hU).commRingCatIsoToRingEquiv).symm
  have hle : ringKrullDim Γ(model k L, V) ≤ topologicalKrullDim (model k L) := by
    have h := hV.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    change topologicalKrullDim (PrimeSpectrum Γ(model k L, V)) ≤ topologicalKrullDim (model k L) at h
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
  exact hB.trans hle

/-- The SAME specified original coefficient action is retained by the ACTUAL model function field. -/
def fieldAlgEquiv [FiniteDimensional (RatFunc k) L] [Algebra k L] [IsScalarTower k (RatFunc k) L] :
    letI := (baseMap k L).stalkAlgebra (genericPoint (model k L))
    (model k L).functionField ≃ₐ[k] L := by
  let := functionFieldAlgebra k L
  let := functionField_finite k L
  let := (projectiveSpaceStructure k 1).stalkAlgebra (genericPoint (projectiveSpace k 1))
  let := (baseMap k L).stalkAlgebra (genericPoint (model k L))
  let U := (Alterations.Geometry.Segre.coordinateChartInclusion (R := k) (0 : Fin 2)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  refine { fieldEquiv k L with commutes' := ?_ }
  intro c
  have hn : fieldEquiv k L (algebraMap k (model k L).functionField c) =
      algebraMap (projectiveSpace k 1).functionField L
        (algebraMap k (projectiveSpace k 1).functionField c) := by
    let := SpecifiedFieldSchemeNormalization.coefficientExtensionAlgebra
      (projectiveSpace k 1) L (projectiveSpaceStructure k 1)
    exact (SpecifiedFieldSchemeNormalization.functionFieldAlgEquiv
      (projectiveSpace k 1) L (projectiveSpaceStructure k 1) U hU).commutes c
  refine hn.trans ?_
  change algebraMap (RatFunc k) L
    (ProjectiveLineFunctionField.functionFieldEquiv k
      (algebraMap k (projectiveSpace k 1).functionField c)) = _
  have he : ProjectiveLineFunctionField.functionFieldEquiv k
      (algebraMap k (projectiveSpace k 1).functionField c) = algebraMap k (RatFunc k) c :=
    (ProjectiveLineFunctionField.functionFieldAlgEquiv k).commutes c
  exact (congrArg (algebraMap (RatFunc k) L) he).trans
    (IsScalarTower.algebraMap_apply k (RatFunc k) L c).symm

end EnvelopeProperty.ResidualFunctionFieldCurve
