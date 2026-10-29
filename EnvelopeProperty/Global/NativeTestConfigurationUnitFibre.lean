/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.NativeTestConfigurationUnitOpen
import EnvelopeProperty.AlgGeom.EquivariantGroupFibreTrivialization

/-!
# The literal original fibre-one trivialization of the WHOLE original unit open

The SAME original fibre at ONE is proved Cartesian over the actual Laurent
parameter. The original source action then gives the entire product iso;
no fibre comparison or unit-open trivialization certificate is supplied.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped Polynomial CategoryTheory.MonObj
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : TestConfiguration k X)

/-- The whole original actual fibre-one inclusion into the original total model. -/
def fibreOneInclusion : fibreOneOver k C.projection ⟶ totalOver k C.projection :=
  SchemeEquivariantPullback.firstProjection (structureOver k C.projection) (pointOne k)

private theorem parameterGroupUnit_inclusion :
    η[ProjBerk.nativeMultiplicativeGroup k] ≫ ProjBerk.nativeParameterGroupInclusion k = pointOne k := by
  let := ProjBerk.nativeParameterLineMonObj k
  let : IsMonHom (ProjBerk.nativeParameterGroupInclusion k) :=
    ProjBerk.nativeParameterGroupInclusion_isMonHom k
  exact IsMonHom.one_hom (ProjBerk.nativeParameterGroupInclusion k)

private theorem fibreOneOuterSquare : IsPullback C.fibreOneInclusion
    (toUnit (fibreOneOver k C.projection)) (structureOver k C.projection)
    (η[ProjBerk.nativeMultiplicativeGroup k] ≫ ProjBerk.nativeParameterGroupInclusion k) := by
  rw [parameterGroupUnit_inclusion (k := k)]
  have he : toUnit (fibreOneOver k C.projection) =
      SchemeEquivariantPullback.secondProjection (structureOver k C.projection) (pointOne k) :=
    toUnit_unique _ _
  rw [he]
  exact SchemeEquivariantPullback.square (structureOver k C.projection) (pointOne k)

private theorem groupPullbackSquare : IsPullback C.groupPullbackProjection
    C.groupPullbackParameter (structureOver k C.projection) (ProjBerk.nativeParameterGroupInclusion k) :=
  SchemeEquivariantPullback.square (structureOver k C.projection) (ProjBerk.nativeParameterGroupInclusion k)

/-- The entire original actual fibre-one inclusion into the SAME original Laurent pullback. -/
def fibreOneGroupLift : fibreOneOver k C.projection ⟶ C.groupPullback :=
  C.groupPullbackSquare.lift C.fibreOneInclusion
    (toUnit _ ≫ η[ProjBerk.nativeMultiplicativeGroup k]) (by
      rw [C.fibreOneOuterSquare.w, Category.assoc])

/-- The WHOLE original fibre-one lift retains its ORIGINAL total-space inclusion. -/
@[reassoc (attr := simp)]
theorem fibreOneGroupLift_projection : C.fibreOneGroupLift ≫ C.groupPullbackProjection =
    C.fibreOneInclusion := C.groupPullbackSquare.lift_fst _ _ _

/-- The WHOLE original fibre-one lift has exactly the original group-unit parameter. -/
@[reassoc (attr := simp)]
theorem fibreOneGroupLift_parameter : C.fibreOneGroupLift ≫ C.groupPullbackParameter =
    toUnit _ ≫ η[ProjBerk.nativeMultiplicativeGroup k] := C.groupPullbackSquare.lift_snd _ _ _

/-- The SAME original native fibre over polynomial parameter ONE is genuinely
Cartesian over the actual Laurent group parameter and its original unit. -/
theorem fibreOneGroupSquare : IsPullback C.fibreOneGroupLift
    (toUnit (fibreOneOver k C.projection)) C.groupPullbackParameter η[ProjBerk.nativeMultiplicativeGroup k] :=
  C.fibreOneOuterSquare.of_right' C.groupPullbackSquare

/-- Original source TC equivariance derives a genuine whole product isomorphism
using the SAME native original fibre ONE and SAME original Laurent parameter. -/
def groupPullbackFibreIso : C.groupPullback ≅
    ProjBerk.nativeMultiplicativeGroup k ⊗ fibreOneOver k C.projection := by
  let := C.groupPullbackModObj
  let : ModObj (ProjBerk.nativeMultiplicativeGroup k) (ProjBerk.nativeMultiplicativeGroup k) :=
    ModObj.regular _
  let : IsModHom (ProjBerk.nativeMultiplicativeGroup k) C.groupPullbackParameter :=
    C.groupPullbackParameter_isModHom
  exact EquivariantGroupFibreTrivialization.iso (ProjBerk.nativeMultiplicativeGroup k)
    C.groupPullbackParameter C.fibreOneGroupSquare

/-- The whole original Laurent parameter is EXACTLY the first product projection. -/
@[reassoc (attr := simp)]
theorem groupPullbackFibreIso_fst : C.groupPullbackFibreIso.hom ≫
    fst (ProjBerk.nativeMultiplicativeGroup k) (fibreOneOver k C.projection) = C.groupPullbackParameter := by
  let := C.groupPullbackModObj
  let : ModObj (ProjBerk.nativeMultiplicativeGroup k) (ProjBerk.nativeMultiplicativeGroup k) :=
    ModObj.regular _
  let : IsModHom (ProjBerk.nativeMultiplicativeGroup k) C.groupPullbackParameter :=
    C.groupPullbackParameter_isModHom
  exact EquivariantGroupFibreTrivialization.iso_hom_fst _ _ _

/-- The literal original WHOLE noncentral open is a genuine product with its SAME original native fibre ONE. -/
def unitOpenFibreIso : C.unitOpenOver ≅
    ProjBerk.nativeMultiplicativeGroup k ⊗ fibreOneOver k C.projection :=
  C.groupPullbackOpenIso.symm ≪≫ C.groupPullbackFibreIso

/-- The WHOLE original unit-open product iso retains its original Laurent parameter map. -/
@[reassoc (attr := simp)]
theorem unitOpenFibreIso_fst : C.unitOpenFibreIso.hom ≫
    fst (ProjBerk.nativeMultiplicativeGroup k) (fibreOneOver k C.projection) =
      C.groupPullbackOpenIso.inv ≫ C.groupPullbackParameter := by
  rw [unitOpenFibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, groupPullbackFibreIso_fst]

/-- The literal original WHOLE noncentral open is isomorphic to the ORIGINAL X times
its original multiplicative group, from ONLY source fibre-one datum and true action. -/
def unitOpenIso : C.unitOpenOver ≅ X ⊗ ProjBerk.nativeMultiplicativeGroup k :=
  C.unitOpenFibreIso ≪≫ whiskerLeftIso (ProjBerk.nativeMultiplicativeGroup k) C.fibreOneIso ≪≫
    β_ (ProjBerk.nativeMultiplicativeGroup k) X

/-- The entire original standard product parameter is EXACTLY the original Laurent parameter. -/
@[reassoc (attr := simp)]
theorem unitOpenIso_parameter : C.unitOpenIso.hom ≫ snd X (ProjBerk.nativeMultiplicativeGroup k) =
    C.groupPullbackOpenIso.inv ≫ C.groupPullbackParameter := by
  simp only [unitOpenIso, Iso.trans_hom, Category.assoc, braiding_hom_snd,
    whiskerLeftIso_hom, whiskerLeft_fst, unitOpenFibreIso_fst]

/-- The WHOLE native original unit-open trivialization lies over the ORIGINAL A1
parameter map, not merely over its generic point or on underlying points. -/
theorem unitOpenIso_structure : C.unitOpenIso.hom ≫ snd X (ProjBerk.nativeMultiplicativeGroup k) ≫
    ProjBerk.nativeParameterGroupInclusion k = C.unitOpenInclusion ≫ structureOver k C.projection := by
  rw [← Category.assoc, unitOpenIso_parameter, Category.assoc,
    ← C.groupPullbackSquare.w, ← Category.assoc, groupPullbackOpenIso_inv_projection]

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
