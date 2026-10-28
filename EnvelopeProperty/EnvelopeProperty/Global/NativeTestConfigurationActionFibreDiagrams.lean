import EnvelopeProperty.Global.NativeTestConfigurationFibreOneCompatibility

/-! # Whole original action/fibre diagrams deriving source line trivialization -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped Polynomial CategoryTheory.MonObj
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : TestConfiguration k X)

private local instance originalAction : ModObj (ProjBerk.nativeMultiplicativeGroup k)
    (totalOver k C.projection) := C.action

/-- The genuine original group times the SAME original parameter-one fibre inclusion. -/
def unitFibreActionInclusion :
    ProjBerk.nativeMultiplicativeGroup k ⊗ fibreOneOver k C.projection ⟶
      ProjBerk.nativeMultiplicativeGroup k ⊗ totalOver k C.projection :=
  ProjBerk.nativeMultiplicativeGroup k ◁ C.fibreOneInclusion

/-- The actual whole original action-product inclusion retains the entire original last projection. -/
@[reassoc (attr := simp)]
theorem unitFibreActionInclusion_projection : C.unitFibreActionInclusion ≫
    snd (ProjBerk.nativeMultiplicativeGroup k) (totalOver k C.projection) =
      snd (ProjBerk.nativeMultiplicativeGroup k) (fibreOneOver k C.projection) ≫ C.fibreOneInclusion :=
  whiskerLeft_snd _ _

/-- The original action on the whole group-times-fibre is EXACTLY the original inverse
whole fibre trivialization followed by the original total-space projection. -/
theorem unitFibreActionInclusion_action : C.unitFibreActionInclusion ≫
    ModObj.smul (M := ProjBerk.nativeMultiplicativeGroup k) (X := totalOver k C.projection) =
      C.groupPullbackFibreIso.inv ≫ C.groupPullbackProjection := by
  let := C.groupPullbackModObj
  let : IsModHom (ProjBerk.nativeMultiplicativeGroup k) C.groupPullbackProjection :=
    C.groupPullbackProjection_isModHom
  change _ = ((fst (ProjBerk.nativeMultiplicativeGroup k) (fibreOneOver k C.projection)) •
    (snd (ProjBerk.nativeMultiplicativeGroup k) (fibreOneOver k C.projection) ≫
      C.fibreOneGroupLift)) ≫ C.groupPullbackProjection
  rw [IsModHom.map_smul, Category.assoc, fibreOneGroupLift_projection, Hom.smul_def]
  congr 1

/-- The WHOLE original unit open lifts canonically into the SAME original group-action product. -/
def unitOpenActionLift : C.unitOpenOver ⟶
    ProjBerk.nativeMultiplicativeGroup k ⊗ totalOver k C.projection :=
  C.unitOpenFibreIso.hom ≫ C.unitFibreActionInclusion

/-- The original action composite of the SAME entire original lift is the ORIGINAL open inclusion. -/
@[reassoc (attr := simp)]
theorem unitOpenActionLift_action : C.unitOpenActionLift ≫
    ModObj.smul (M := ProjBerk.nativeMultiplicativeGroup k) (X := totalOver k C.projection) =
      C.unitOpenInclusion := by
  rw [unitOpenActionLift, Category.assoc, unitFibreActionInclusion_action]
  simp only [unitOpenFibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, groupPullbackOpenIso_inv_projection]

/-- The projection composite of the WHOLE original lift factors through the SAME original fibre ONE. -/
@[reassoc (attr := simp)]
theorem unitOpenActionLift_projection : C.unitOpenActionLift ≫
    snd (ProjBerk.nativeMultiplicativeGroup k) (totalOver k C.projection) =
      C.unitOpenFibreIso.hom ≫
        snd (ProjBerk.nativeMultiplicativeGroup k) (fibreOneOver k C.projection) ≫ C.fibreOneInclusion := by
  rw [unitOpenActionLift, Category.assoc, unitFibreActionInclusion_projection]

/-- The entire original X projection of the genuine original product trivialization. -/
def unitOpenOriginalProjection : C.unitOpenOver ⟶ X :=
  C.unitOpenIso.hom ≫ fst X (ProjBerk.nativeMultiplicativeGroup k)

/-- The WHOLE original X projection is precisely its SAME native fibre factor followed by
its ORIGINAL source fibre-one identification, retaining the entire original source X. -/
theorem unitOpenOriginalProjection_eq : C.unitOpenOriginalProjection =
    C.unitOpenFibreIso.hom ≫
      snd (ProjBerk.nativeMultiplicativeGroup k) (fibreOneOver k C.projection) ≫ C.fibreOneIso.hom := by
  simp only [unitOpenOriginalProjection, unitOpenIso, Iso.trans_hom, Category.assoc,
    braiding_hom_fst, whiskerLeftIso_hom, whiskerLeft_snd]

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
