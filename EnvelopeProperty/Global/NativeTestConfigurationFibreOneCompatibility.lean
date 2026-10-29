/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.NativeTestConfigurationUnitFibre
import EnvelopeProperty.AlgGeom.EquivariantGroupFibreInclusion

/-!
# The literal original fibre-one identification is retained by the WHOLE trivialization

The exact source fibre-one isomorphism, original entire native fibre
inclusion, original group unit, and both actual full inverse maps commute.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped Polynomial CategoryTheory.MonObj
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : TestConfiguration k X)

/-- The whole ORIGINAL native fibre-one inclusion into the SAME original unit open. -/
def fibreOneUnitOpenInclusion : fibreOneOver k C.projection ⟶ C.unitOpenOver :=
  C.fibreOneGroupLift ≫ C.groupPullbackOpenIso.hom

/-- The same actual unit-open fibre map retains the ENTIRE original total-space fibre inclusion. -/
@[reassoc (attr := simp)]
theorem fibreOneUnitOpenInclusion_inclusion : C.fibreOneUnitOpenInclusion ≫ C.unitOpenInclusion =
    C.fibreOneInclusion := by
  rw [fibreOneUnitOpenInclusion, Category.assoc, groupPullbackOpenIso_inclusion,
    fibreOneGroupLift_projection]

private theorem fibreOneGroupLift_iso : C.fibreOneGroupLift ≫ C.groupPullbackFibreIso.hom =
    lift (toUnit _ ≫ η[ProjBerk.nativeMultiplicativeGroup k]) (𝟙 (fibreOneOver k C.projection)) := by
  let := C.groupPullbackModObj
  let : ModObj (ProjBerk.nativeMultiplicativeGroup k) (ProjBerk.nativeMultiplicativeGroup k) :=
    ModObj.regular _
  let : IsModHom (ProjBerk.nativeMultiplicativeGroup k) C.groupPullbackParameter :=
    C.groupPullbackParameter_isModHom
  exact EquivariantGroupFibreInclusion.inclusion_iso (ProjBerk.nativeMultiplicativeGroup k)
    C.groupPullbackParameter C.fibreOneGroupSquare

/-- The ENTIRE original unit-open trivialization restricts to EXACTLY the source
fibre-one identification and the ORIGINAL group unit, with no fibre-compatibility certificate. -/
theorem fibreOneUnitOpenInclusion_trivialization : C.fibreOneUnitOpenInclusion ≫ C.unitOpenIso.hom =
    lift C.fibreOneIso.hom (toUnit _ ≫ η[ProjBerk.nativeMultiplicativeGroup k]) := by
  simp only [fibreOneUnitOpenInclusion, unitOpenIso, unitOpenFibreIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc C.fibreOneGroupLift, C.fibreOneGroupLift_iso]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, braiding_hom_fst, whiskerLeftIso_hom, whiskerLeft_snd,
      lift_snd_assoc, Category.id_comp, lift_fst]
  · simp only [Category.assoc, braiding_hom_snd, whiskerLeftIso_hom, whiskerLeft_fst,
      lift_fst, lift_snd]

/-- The WHOLE inverse original unit-open trivialization restricts to the exact
original source fibre-one inclusion, with the SAME original source identification. -/
theorem fibreOneUnitOpenInclusion_inverse :
    lift C.fibreOneIso.hom (toUnit _ ≫ η[ProjBerk.nativeMultiplicativeGroup k]) ≫ C.unitOpenIso.inv =
      C.fibreOneUnitOpenInclusion := by
  rw [← fibreOneUnitOpenInclusion_trivialization C, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
