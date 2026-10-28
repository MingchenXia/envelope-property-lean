/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.NativeTestConfigurationUnitFibre
import EnvelopeProperty.Projective.NativeMultiplicativeProductReduced

/-!
# Actual reducedness of every literal original test configuration of a reduced X

The ORIGINAL fibre-one identification derives proper/Noetherian geometry of
the SAME original X. Actual entire unit-open trivialization and original
flatness then derive reducedness of the WHOLE original total model. No
irreducibility, normality or perfectness hypothesis is introduced.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : TestConfiguration k X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem fibreOne_coefficient :
    pullback.snd C.projection (pointOne k).left = (fibreOneOver k C.projection).hom := by
  have h := (SchemeEquivariantPullback.secondProjection (structureOver k C.projection) (pointOne k)).w
  exact (Category.comp_id (pullback.snd C.projection (pointOne k).left)).symm.trans h

include C in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Properness of the SAME original X follows from the genuine original parameter-one fibre datum. -/
theorem original_isProper : IsProper X.hom := by
  let : IsProper C.projection := C.projection_isProper
  let : IsProper (fibreOneOver k C.projection).hom := by
    rw [← C.fibreOne_coefficient]
    infer_instance
  let : IsIso C.fibreOneIso.inv.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (CommRingCat.of k))).map C.fibreOneIso.inv))
  have h : IsProper (C.fibreOneIso.inv.left ≫ (fibreOneOver k C.projection).hom) := inferInstance
  rwa [C.fibreOneIso.inv.w] at h

include C in
/-- Local Noetherianity of the SAME original X is derived, not supplied as an extra premise. -/
theorem original_isLocallyNoetherian : IsLocallyNoetherian X.left := by
  let : IsProper X.hom := C.original_isProper
  exact LocallyOfFiniteType.isLocallyNoetherian X.hom

include C in
/-- Noetherianity of the SAME original X is derived from the actual original TC source data. -/
theorem original_isNoetherian : AlgebraicGeometry.IsNoetherian X.left := by
  let : IsProper X.hom := C.original_isProper
  let : IsLocallyNoetherian X.left := C.original_isLocallyNoetherian
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact ⟨⟩

set_option backward.isDefEq.respectTransparency false in
/-- Reducedness of the SAME original X gives reducedness of the ENTIRE actual original unit open. -/
theorem unitOpen_isReduced [IsReduced X.left] : IsReduced C.unitOpen.toScheme := by
  let : IsLocallyNoetherian X.left := C.original_isLocallyNoetherian
  let : IsReduced (pullback (ProjBerk.nativeMultiplicativeGroup k).hom X.hom) :=
    ProjBerk.nativeMultiplicativeGroup_pullback_isReduced k X.hom
  let : IsReduced (X ⊗ ProjBerk.nativeMultiplicativeGroup k).left :=
    isReduced_of_isOpenImmersion (pullbackSymmetry X.hom (ProjBerk.nativeMultiplicativeGroup k).hom).hom
  let : IsIso C.unitOpenIso.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (CommRingCat.of k))).map C.unitOpenIso.hom))
  exact isReduced_of_isOpenImmersion C.unitOpenIso.hom.left

set_option backward.isDefEq.respectTransparency false in
/-- Every literal original test configuration of a reduced ORIGINAL X has a
reduced ENTIRE original total model, as in the source; no irreducibility/normality/perfectness premise. -/
theorem total_isReduced [IsReduced X.left] : IsReduced C.total := by
  let : Flat C.projection := C.flat
  let : IsReduced (C.projection ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : k[X])).toScheme :=
    C.unitOpen_isReduced
  exact FlatParameterOpen.isReduced_of_parameterOpen C.projection (Polynomial.X : k[X])
    (mem_nonZeroDivisors_iff_ne_zero.mpr Polynomial.X_ne_zero)

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
