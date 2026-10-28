/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.NativeTestConfigurationData

/-!
# The SAME original unit open as a genuine equivariant Laurent pullback

Source TC (i)--(iii) and the genuine original group inclusion derive the
whole native product-open comparison and its true group action. No supplied
unit-open trivialization, action, integrality or normality is used.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped Polynomial CategoryTheory.MonObj
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : TestConfiguration k X)

/-- The SAME native Laurent-base pullback of the original parameter projection. -/
def groupPullback : Over (Spec (CommRingCat.of k)) :=
  SchemeEquivariantPullback.object (structureOver k C.projection) (ProjBerk.nativeParameterGroupInclusion k)

/-- The whole original projection from this SAME native Laurent pullback to the total model. -/
def groupPullbackProjection : C.groupPullback ⟶ totalOver k C.projection :=
  SchemeEquivariantPullback.firstProjection (structureOver k C.projection)
    (ProjBerk.nativeParameterGroupInclusion k)

/-- The whole original Laurent parameter of the SAME native pullback. -/
def groupPullbackParameter : C.groupPullback ⟶ ProjBerk.nativeMultiplicativeGroup k :=
  SchemeEquivariantPullback.secondProjection (structureOver k C.projection)
    (ProjBerk.nativeParameterGroupInclusion k)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual Laurent-pullback projection is a genuine open immersion. -/
theorem groupPullbackProjection_isOpenImmersion : IsOpenImmersion C.groupPullbackProjection.left := by
  let : IsOpenImmersion (ProjBerk.nativeParameterGroupInclusion k).left :=
    ProjBerk.nativeParameterGroupInclusion_isOpenImmersion k
  change IsOpenImmersion (pullback.fst C.projection (ProjBerk.nativeParameterGroupInclusion k).left)
  infer_instance

private local instance projectionOpen : IsOpenImmersion C.groupPullbackProjection.left :=
  C.groupPullbackProjection_isOpenImmersion

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole actual Laurent-pullback projection has EXACTLY the original noncentral open as its image. -/
theorem groupPullbackProjection_opensRange : C.groupPullbackProjection.left.opensRange = C.unitOpen := by
  let : IsOpenImmersion (ProjBerk.nativeParameterGroupInclusion k).left :=
    ProjBerk.nativeParameterGroupInclusion_isOpenImmersion k
  change (pullback.fst C.projection (ProjBerk.nativeParameterGroupInclusion k).left).opensRange = _
  rw [Scheme.Hom.opensRange_pullbackFst, ProjBerk.nativeParameterGroupInclusion_opensRange]
  rfl

/-- The SAME original whole noncentral open over the original coefficient field. -/
def unitOpenOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (C.unitOpen.ι ≫ (totalOver k C.projection).hom)

/-- The SAME actual unit-open inclusion over the original field. -/
def unitOpenInclusion : C.unitOpenOver ⟶ totalOver k C.projection := Over.homMk C.unitOpen.ι rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def groupPullbackOpenNativeIso : C.groupPullback.left ≅ C.unitOpen.toScheme :=
  IsOpenImmersion.isoOfRangeEq C.groupPullbackProjection.left C.unitOpen.ι (by
    rw [Scheme.Opens.range_ι]
    exact congrArg (fun U : C.total.Opens => U.carrier) C.groupPullbackProjection_opensRange)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole native Laurent pullback is the SAME original noncentral open, over the SAME original field. -/
def groupPullbackOpenIso : C.groupPullback ≅ C.unitOpenOver :=
  Over.isoMk C.groupPullbackOpenNativeIso (by
    change C.groupPullbackOpenNativeIso.hom ≫
      (C.unitOpen.ι ≫ (totalOver k C.projection).hom) = _
    rw [← Category.assoc]
    unfold groupPullbackOpenNativeIso
    rw [IsOpenImmersion.isoOfRangeEq_hom_fac]
    exact C.groupPullbackProjection.w)

set_option backward.isDefEq.respectTransparency false in
/-- The ENTIRE original open inclusion diagram of the native Laurent comparison. -/
@[reassoc (attr := simp)]
theorem groupPullbackOpenIso_inclusion : C.groupPullbackOpenIso.hom ≫ C.unitOpenInclusion =
    C.groupPullbackProjection := by
  apply Over.OverMorphism.ext
  change C.groupPullbackOpenNativeIso.hom ≫ C.unitOpen.ι = C.groupPullbackProjection.left
  unfold groupPullbackOpenNativeIso
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The ENTIRE original inverse open inclusion diagram of the native Laurent comparison. -/
@[reassoc (attr := simp)]
theorem groupPullbackOpenIso_inv_projection : C.groupPullbackOpenIso.inv ≫ C.groupPullbackProjection =
    C.unitOpenInclusion := by
  rw [← C.groupPullbackOpenIso_inclusion, Iso.inv_hom_id_assoc]

/-- The genuine internally derived group action on the SAME native Laurent pullback. -/
@[instance_reducible]
def groupPullbackModObj : ModObj (ProjBerk.nativeMultiplicativeGroup k) C.groupPullback := by
  let := ProjBerk.nativeParameterLineModObj k
  let := C.action
  let : ModObj (ProjBerk.nativeMultiplicativeGroup k) (ProjBerk.nativeMultiplicativeGroup k) :=
    ModObj.regular _
  let : IsModHom (ProjBerk.nativeMultiplicativeGroup k) (structureOver k C.projection) := C.equivariant
  let : IsModHom (ProjBerk.nativeMultiplicativeGroup k) (ProjBerk.nativeParameterGroupInclusion k) :=
    ProjBerk.nativeParameterGroupInclusion_isModHom k
  exact SchemeEquivariantPullback.modObj (structureOver k C.projection)
    (ProjBerk.nativeParameterGroupInclusion k) (ProjBerk.nativeMultiplicativeGroup k)

/-- The WHOLE original projection from the SAME Laurent pullback is equivariant. -/
theorem groupPullbackProjection_isModHom : letI := C.groupPullbackModObj
    letI := C.action
    IsModHom (ProjBerk.nativeMultiplicativeGroup k) C.groupPullbackProjection := by
  let := ProjBerk.nativeParameterLineModObj k
  let := C.action
  let : ModObj (ProjBerk.nativeMultiplicativeGroup k) (ProjBerk.nativeMultiplicativeGroup k) :=
    ModObj.regular _
  let : IsModHom (ProjBerk.nativeMultiplicativeGroup k) (structureOver k C.projection) := C.equivariant
  let : IsModHom (ProjBerk.nativeMultiplicativeGroup k) (ProjBerk.nativeParameterGroupInclusion k) :=
    ProjBerk.nativeParameterGroupInclusion_isModHom k
  exact SchemeEquivariantPullback.firstProjection_isModHom (structureOver k C.projection)
    (ProjBerk.nativeParameterGroupInclusion k) (ProjBerk.nativeMultiplicativeGroup k)

/-- The WHOLE original Laurent parameter map is equivariant for the original REGULAR group action. -/
theorem groupPullbackParameter_isModHom : letI := C.groupPullbackModObj
    letI : ModObj (ProjBerk.nativeMultiplicativeGroup k) (ProjBerk.nativeMultiplicativeGroup k) :=
      ModObj.regular _
    IsModHom (ProjBerk.nativeMultiplicativeGroup k) C.groupPullbackParameter := by
  let := ProjBerk.nativeParameterLineModObj k
  let := C.action
  let : ModObj (ProjBerk.nativeMultiplicativeGroup k) (ProjBerk.nativeMultiplicativeGroup k) :=
    ModObj.regular _
  let : IsModHom (ProjBerk.nativeMultiplicativeGroup k) (structureOver k C.projection) := C.equivariant
  let : IsModHom (ProjBerk.nativeMultiplicativeGroup k) (ProjBerk.nativeParameterGroupInclusion k) :=
    ProjBerk.nativeParameterGroupInclusion_isModHom k
  exact SchemeEquivariantPullback.secondProjection_isModHom (structureOver k C.projection)
    (ProjBerk.nativeParameterGroupInclusion k) (ProjBerk.nativeMultiplicativeGroup k)

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
