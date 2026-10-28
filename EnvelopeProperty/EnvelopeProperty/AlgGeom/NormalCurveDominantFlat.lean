import EnvelopeProperty.AlgGeom.CurveDenominatorCartier
import EnvelopeProperty.AlgGeom.DominantFunctionFieldMaps
import EnvelopeProperty.AlgGeom.CartierModuleFlatPullback
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Genuine flatness of actual dominant morphisms to the original normal curve -/
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.NormalCurveDominantFlat
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsDominant f]
    (hdim : topologicalKrullDim Y ≤ 1)
    (hNormal : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

include hdim hNormal

/-- Every SAME actual dominant stalk map is flat, with torsionfreeness/PID all internally derived. -/
theorem stalkMap_flat (x : X) : (f.stalkMap x).hom.Flat := by
  let := (f.stalkMap x).hom.toAlgebra
  let := CurveDenominatorCartier.stalk_isPrincipalIdealRing hdim hNormal (f x)
  let : Module.IsTorsionFree (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (DominantFunctionFieldMaps.stalkMap_injective f x)
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The entire SAME dominant morphism to the original normal curve is genuinely flat. -/
theorem flat : Flat f := Flat.of_stalkMap f (stalkMap_flat f hdim hNormal)

/-- Every SAME original Cartier ideal pulls to a genuine original Cartier ideal along the actual map. -/
theorem comap_isInvertible (I : Y.IdealSheafData) (hI : I.IsInvertible) :
    (I.comap f).IsInvertible := by
  let := flat f hdim hNormal
  exact hI.comap_of_flat f

end EnvelopeProperty.NormalCurveDominantFlat
