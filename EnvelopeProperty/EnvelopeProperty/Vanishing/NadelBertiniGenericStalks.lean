import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv

/-! # Actual generic-fibre regularity from the original local rings

The flat-preimmersion and generic-point flatness proofs adapt the corresponding
native proofs in `DeJongAlterations.Geometry.GenericFiberIntegral` from the
workspace DJA source; no unvendored module is imported. Every comparison here
is the stalk map of the original native scheme-theoretic fibre.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniGenericStalks
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}}

/-- A flat preimmersion's actual original local-ring map is an isomorphism. -/
theorem stalkMap_isIso_of_flat_preimmersion (f : X ⟶ Y)
    [Flat f] [IsPreimmersion f] (x : X) : IsIso (f.stalkMap x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨?_, f.stalkMap_surjective x⟩
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat (f.stalkMap x).hom›.injective

/-- The actual residue-field point at the original generic point is flat. -/
theorem fromSpecResidueField_flat (Y : Scheme.{u}) [IsIntegral Y] :
    Flat (Y.fromSpecResidueField (genericPoint Y)) := by
  apply (Flat.iff_flat_stalkMap _).mpr
  intro x
  have hfield : IsField
      (Y.presheaf.stalk ((Y.fromSpecResidueField (genericPoint Y)) x)) := by
    rw [Scheme.fromSpecResidueField_apply]
    exact Field.toIsField Y.functionField
  let : Field (Y.presheaf.stalk ((Y.fromSpecResidueField (genericPoint Y)) x)) :=
    hfield.toField
  algebraize [((Y.fromSpecResidueField (genericPoint Y)).stalkMap x).hom]
  change Module.Flat _ _
  infer_instance

/-- Regularity transfers through the actual stalk isomorphisms, point by point. -/
theorem isRegular_of_flat_preimmersion (f : X ⟶ Y)
    [Flat f] [IsPreimmersion f] [IsRegular Y] : IsRegular X := by
  constructor
  intro x
  let : IsRegularLocalRing (Y.presheaf.stalk (f x)) := IsRegular.isRegularAt (f x)
  let : IsIso (f.stalkMap x) := stalkMap_isIso_of_flat_preimmersion f x
  exact IsRegularLocalRing.of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

/-- The whole actual generic fibre is regular; neither dominance nor source
integrality nor nonemptiness of the fibre is required. -/
theorem genericFiber_isRegular (f : X ⟶ Y) [IsRegular X] [IsIntegral Y] :
    IsRegular (f.fiber (genericPoint Y)) := by
  let : Flat (Y.fromSpecResidueField (genericPoint Y)) := fromSpecResidueField_flat Y
  let : Flat (f.fiberι (genericPoint Y)) := by
    change Flat (CategoryTheory.Limits.pullback.fst _ _)
    infer_instance
  exact isRegular_of_flat_preimmersion (f.fiberι (genericPoint Y))

end EnvelopeProperty.Vanishing.NadelBertiniGenericStalks
