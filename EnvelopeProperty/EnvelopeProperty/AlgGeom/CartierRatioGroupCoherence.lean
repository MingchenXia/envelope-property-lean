/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierEvaluationRatio
import EnvelopeProperty.AlgGeom.CartierGroupLinearization

/-! # Genuine whole group unit and cocycle of original Cartier ratios -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CartesianMonoidalCategory
open scoped MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty
open AlgebraicGeometry.Scheme.Modules
variable {k : Type u} [Field k]
variable (G B : Over (Spec (CommRingCat.of k))) [GrpObj G] [ModObj G B]
attribute [local instance] flat_groupAction_over_field
variable (I J : B.left.IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible)
variable (hinvI : I.comap (cartierActionMap G B) = I.comap (cartierProjectionMap G B))
variable (hinvJ : J.comap (cartierActionMap G B) = J.comap (cartierProjectionMap G B))

/-- The genuine whole group comparison on the SAME original tensor-dual
ratio, using actual inclusion-preserving Cartier factors and evaluation. -/
def cartierRatioGroupLinearization :
    (Scheme.Modules.pullback (cartierActionMap G B)).obj (I.ratioModule J) ≅
      (Scheme.Modules.pullback (cartierProjectionMap G B)).obj (I.ratioModule J) :=
  evaluationRatioComparison hJ.isInvertibleModule_toModules
    (cartierActionMap G B) (cartierProjectionMap G B)
    (cartierGroupLinearization G B I hI hinvI)
    (cartierGroupLinearization G B J hJ hinvJ)

/-- The actual whole original ratio group comparison has its true unit
law, with the native comparison on the original identity composites. -/
theorem cartierRatioGroupLinearization_unit :
    pullbackIsoAlong (cartierActionMap G B) (cartierProjectionMap G B)
        (cartierRatioGroupLinearization G B I J hI hJ hinvI hinvJ) (cartierUnitMap G B) =
      (Scheme.Modules.pullbackCongr
        ((cartierUnitMap_action G B).trans (cartierUnitMap_projection G B).symm)).app
          (I.ratioModule J) := by
  have hi : pullbackIsoAlong (cartierActionMap G B) (cartierProjectionMap G B)
      (cartierGroupLinearization G B I hI hinvI) (cartierUnitMap G B) = _ :=
    cartierGroupLinearization_unit G B I hI hinvI
  have hj : pullbackIsoAlong (cartierActionMap G B) (cartierProjectionMap G B)
      (cartierGroupLinearization G B J hJ hinvJ) (cartierUnitMap G B) = _ :=
    cartierGroupLinearization_unit G B J hJ hinvJ
  rw [cartierRatioGroupLinearization, evaluationRatioComparison_baseChange, hi, hj,
    evaluationRatioComparison_congr]
  rfl

/-- The SAME actual original ratio comparison satisfies the true whole
group cocycle on the entire original triple product, with no supplied law. -/
theorem cartierRatioGroupLinearization_cocycle :
    (Scheme.Modules.pullbackCongr (cartierMultiplyMap_action G B)).app (I.ratioModule J) ≪≫
      pullbackIsoAlong (cartierActionMap G B) (cartierProjectionMap G B)
        (cartierRatioGroupLinearization G B I J hI hJ hinvI hinvJ) (cartierInnerActionMap G B) ≪≫
      (Scheme.Modules.pullbackCongr (cartierInnerActionMap_projection G B)).app (I.ratioModule J) ≪≫
      pullbackIsoAlong (cartierActionMap G B) (cartierProjectionMap G B)
        (cartierRatioGroupLinearization G B I J hI hJ hinvI hinvJ) (cartierTailMap G B) ≪≫
      (Scheme.Modules.pullbackCongr (cartierMultiplyMap_projection G B).symm).app (I.ratioModule J) =
    pullbackIsoAlong (cartierActionMap G B) (cartierProjectionMap G B)
      (cartierRatioGroupLinearization G B I J hI hJ hinvI hinvJ) (cartierMultiplyMap G B) := by
  let eI := cartierGroupLinearization G B I hI hinvI
  let eJ := cartierGroupLinearization G B J hJ hinvJ
  let h₁ := cartierMultiplyMap_action G B
  let h₂ := cartierInnerActionMap_projection G B
  let h₃ := (cartierMultiplyMap_projection G B).symm
  have hi : (Scheme.Modules.pullbackCongr h₁).app I.toModules ≪≫
      pullbackIsoAlong (cartierActionMap G B) (cartierProjectionMap G B) eI (cartierInnerActionMap G B) ≪≫
      (Scheme.Modules.pullbackCongr h₂).app I.toModules ≪≫
      pullbackIsoAlong (cartierActionMap G B) (cartierProjectionMap G B) eI (cartierTailMap G B) ≪≫
      (Scheme.Modules.pullbackCongr h₃).app I.toModules =
    pullbackIsoAlong (cartierActionMap G B) (cartierProjectionMap G B) eI (cartierMultiplyMap G B) :=
    cartierGroupLinearization_cocycle G B I hI hinvI
  have hj : (Scheme.Modules.pullbackCongr h₁).app J.toModules ≪≫
      pullbackIsoAlong (cartierActionMap G B) (cartierProjectionMap G B) eJ (cartierInnerActionMap G B) ≪≫
      (Scheme.Modules.pullbackCongr h₂).app J.toModules ≪≫
      pullbackIsoAlong (cartierActionMap G B) (cartierProjectionMap G B) eJ (cartierTailMap G B) ≪≫
      (Scheme.Modules.pullbackCongr h₃).app J.toModules =
    pullbackIsoAlong (cartierActionMap G B) (cartierProjectionMap G B) eJ (cartierMultiplyMap G B) :=
    cartierGroupLinearization_cocycle G B J hJ hinvJ
  simp only [Scheme.IdealSheafData.ratioModule]
  rw [← evaluationRatioComparison_congr hJ.isInvertibleModule_toModules _ _ h₁,
    ← evaluationRatioComparison_congr hJ.isInvertibleModule_toModules _ _ h₂,
    ← evaluationRatioComparison_congr hJ.isInvertibleModule_toModules _ _ h₃]
  simp only [cartierRatioGroupLinearization, evaluationRatioComparison_baseChange,
    evaluationRatioComparison_trans]
  rw [hi, hj]

end EnvelopeProperty
