/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierDualEvaluation

/-! # Actual original dual transposes from genuine canonical evaluation -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance invertibleTransposeMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance invertibleTransposeSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}} {M : X.Modules}

/-- TRUE original right-unit comparison using the ACTUAL structure module. -/
def originalRightUnitIso (M : X.Modules) : M ⊗ unitObj X ≅ M :=
  whiskerLeftIso M (ModularCurves.monoidalUnitObjIso X).symm ≪≫ ρ_ M

private def originalTransposeTensorFullyFaithful (hM : IsInvertible M) :
    (tensorLeft M).FullyFaithful :=
  hM.tensorRightFullyFaithful.ofIso (BraidedCategory.tensorLeftIsoTensorRight M).symm

/-- The ACTUAL transpose of an ACTUAL whole original linear functional,
constructed in the ORIGINAL sheaf dual by genuine tensor full faithfulness. -/
def IsInvertible.dualTranspose (hM : IsInvertible M) (α : M ⟶ unitObj X) :
    unitObj X ⟶ dualObj M :=
  (originalTransposeTensorFullyFaithful hM).preimage
    ((originalRightUnitIso M).hom ≫ α ≫
      (ModularCurves.monoidalTensorObjIso M (dualObj M) ≪≫ hM.evaluationIso).inv)

/-- The TRUE whole original transpose preserves the ORIGINAL canonical
sheaf evaluation, without a supplied pairing compatibility hypothesis. -/
theorem IsInvertible.dualTranspose_pairing (hM : IsInvertible M) (α : M ⟶ unitObj X) :
    M ◁ hM.dualTranspose α ≫ ModularCurves.dualPairing M =
      (originalRightUnitIso M).hom ≫ α := by
  have h := (originalTransposeTensorFullyFaithful hM).map_preimage
    ((originalRightUnitIso M).hom ≫ α ≫
      (ModularCurves.monoidalTensorObjIso M (dualObj M) ≪≫ hM.evaluationIso).inv)
  change M ◁ hM.dualTranspose α = _ at h
  rw [h]
  change (originalRightUnitIso M).hom ≫ α ≫
      (ModularCurves.monoidalTensorObjIso M (dualObj M) ≪≫ hM.evaluationIso).inv ≫
        (ModularCurves.monoidalTensorObjIso M (dualObj M) ≪≫ hM.evaluationIso).hom = _
  simp only [Iso.inv_hom_id, Category.comp_id]

/-- TRUE original canonical evaluation uniquely determines the actual
transpose among ALL morphisms of the ORIGINAL structure and dual modules. -/
theorem IsInvertible.dualTranspose_unique (hM : IsInvertible M) (α : M ⟶ unitObj X)
    (σ : unitObj X ⟶ dualObj M)
    (hσ : M ◁ σ ≫ ModularCurves.dualPairing M = (originalRightUnitIso M).hom ≫ α) :
    σ = hM.dualTranspose α := by
  apply (originalTransposeTensorFullyFaithful hM).map_injective
  have : IsIso (ModularCurves.dualPairing M) := by
    change IsIso (ModularCurves.monoidalTensorObjIso M (dualObj M) ≪≫ hM.evaluationIso).hom
    infer_instance
  apply (cancel_mono (ModularCurves.dualPairing M)).mp
  exact hσ.trans (hM.dualTranspose_pairing α).symm

end AlgebraicGeometry.Scheme.Modules
