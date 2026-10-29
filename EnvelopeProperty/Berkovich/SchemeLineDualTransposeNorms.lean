/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLineModelTensorHomNorms
import EnvelopeProperty.Berkovich.CartierModelInclusionNorm
import EnvelopeProperty.AlgGeom.InvertibleDualTranspose

/-! # Genuine original dual transposes preserve actual model morphism norms -/

open scoped NNReal ENNReal
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance schemeDualTransposeNormMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
variable [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)

/-- The ACTUAL canonical original dual transpose has EXACTLY the true
model norm of its original functional, derived from actual evaluation. -/
theorem modelHomNorm_dualTranspose {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (α : M ⟶ Scheme.Modules.unitObj X) :
    modelHomNorm hb y (Scheme.Modules.isInvertible_unit (X := X)) hM.dual (hM.dualTranspose α) =
      modelHomNorm hb y hM (Scheme.Modules.isInvertible_unit (X := X)) α := by
  let hO := Scheme.Modules.isInvertible_unit (X := X)
  let σ := hM.dualTranspose α
  let P := ModularCurves.monoidalTensorObjIso M (Scheme.Modules.dualObj M) ≪≫ hM.evaluationIso
  have hp := hM.dualTranspose_pairing α
  have he := congrArg (modelHomNorm hb y (hM.monoidalTensor hO) hO) hp
  change modelHomNorm hb y (hM.monoidalTensor hO) hO (M ◁ σ ≫ P.hom) =
    modelHomNorm hb y (hM.monoidalTensor hO) hO ((Scheme.Modules.originalRightUnitIso M).hom ≫ α) at he
  rw [modelHomNorm_comp hb y (hM.monoidalTensor hO) (hM.monoidalTensor hM.dual) hO (M ◁ σ) P.hom,
    modelHomNorm_iso hb y (hM.monoidalTensor hM.dual) hO P, mul_one,
    modelHomNorm_comp hb y (hM.monoidalTensor hO) hM hO (Scheme.Modules.originalRightUnitIso M).hom α,
    modelHomNorm_iso hb y (hM.monoidalTensor hO) hM (Scheme.Modules.originalRightUnitIso M), one_mul] at he
  have ht := modelHomNorm_tensorHom hb y hM hM hO hM.dual (𝟙 M) σ
  simp only [MonoidalCategory.tensorHom_def, id_whiskerRight, Category.id_comp] at ht
  rw [modelHomNorm_id, one_mul] at ht
  exact ht.symm.trans he

/-- The ACTUAL canonical dual Cartier inclusion section has EXACTLY
its intrinsic original ideal norm, without a dual metric certificate. -/
theorem modelHomNorm_dualCartierInclusion (I : X.IdealSheafData) (hI : I.IsInvertible) :
    (modelHomNorm hb y (Scheme.Modules.isInvertible_unit (X := X))
      hI.isInvertibleModule_toModules.dual
      (hI.isInvertibleModule_toModules.dualTranspose I.toModulesInclusion) : ℝ≥0∞) =
      modelIdealNorm I hb y := by
  rw [modelHomNorm_dualTranspose]
  exact modelHomNorm_idealInclusion I hI hb y

/-- The true logarithmic potential of the ACTUAL canonical dual Cartier
section is the intrinsic original ideal logarithm, including zero norms. -/
theorem modelHomNorm_dualCartierInclusion_log (I : X.IdealSheafData) (hI : I.IsInvertible) :
    ENNReal.log (modelHomNorm hb y (Scheme.Modules.isInvertible_unit (X := X))
      hI.isInvertibleModule_toModules.dual
      (hI.isInvertibleModule_toModules.dualTranspose I.toModulesInclusion) : ℝ≥0∞) =
      modelIdealLog I hb y :=
  congrArg ENNReal.log (modelHomNorm_dualCartierInclusion hb y I hI)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
