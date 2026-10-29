import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Genuine dominant maps retain the whole original native stalk and field maps -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.DominantFunctionFieldMaps
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Y) [IsDominant p]

/-- Actual dominance sends the SAME original generic points to one another. -/
theorem genericPoint_map : p (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  simpa only [Set.image_univ, p.denseRange.closure_range] using
    (genericPoint_spec X).image p.continuous

/-- The genuine original generic-stalk field embedding, with only actual dominance. -/
def functionFieldMap : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (specializes_of_eq (genericPoint_map p)) ≫
    p.stalkMap (genericPoint X)

/-- The ENTIRE original stalk coefficient square follows actual specialization naturality. -/
theorem stalk_coefficients (x : X) :
    CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (p x)) Y.functionField) ≫
      functionFieldMap p =
    p.stalkMap x ≫ CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) := by
  dsimp only [functionFieldMap]
  change Y.presheaf.stalkSpecializes (genericPoint_specializes (p x)) ≫
    Y.presheaf.stalkSpecializes (specializes_of_eq (genericPoint_map p)) ≫
      p.stalkMap (genericPoint X) = p.stalkMap x ≫
      X.presheaf.stalkSpecializes (genericPoint_specializes x)
  rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  exact p.stalkSpecializes_stalkMap (genericPoint X) x (genericPoint_specializes x)

/-- Every SAME original native stalk map is genuinely injective. -/
theorem stalkMap_injective (x : X) : Function.Injective (p.stalkMap x) := by
  intro a b hab
  apply IsFractionRing.injective (Y.presheaf.stalk (p x)) Y.functionField
  apply (functionFieldMap p).hom.injective
  have h := congrArg (fun f : Y.presheaf.stalk (p x) ⟶ X.functionField => f a)
    (stalk_coefficients p x)
  have h' := congrArg (fun f : Y.presheaf.stalk (p x) ⟶ X.functionField => f b)
    (stalk_coefficients p x)
  exact h.trans ((congrArg (algebraMap (X.presheaf.stalk x) X.functionField) hab).trans h'.symm)

/-- EVERY whole original section retains its original generic germ under actual pullback. -/
theorem functionFieldMap_section (U : Y.Opens) [Nonempty U] [Nonempty (p ⁻¹ᵁ U)]
    (s : Γ(Y, U)) :
    functionFieldMap p (Y.germToFunctionField U s) =
      X.germToFunctionField (p ⁻¹ᵁ U) (p.app U s) := by
  let x := genericPoint X
  have hx : p x ∈ U := by
    rw [show p x = genericPoint Y from genericPoint_map p]
    exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hn : Y.germToFunctionField U ≫ functionFieldMap p =
      p.app U ≫ X.germToFunctionField (p ⁻¹ᵁ U) := by
    change Y.presheaf.germ U (genericPoint Y) _ ≫
      (Y.presheaf.stalkSpecializes (specializes_of_eq (genericPoint_map p)) ≫
        p.stalkMap (genericPoint X)) = p.app U ≫ X.germToFunctionField (p ⁻¹ᵁ U)
    rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
    exact p.germ_stalkMap U (genericPoint X) hx
  exact congrArg (fun f : Γ(Y, U) ⟶ X.functionField => f s) hn

end EnvelopeProperty.DominantFunctionFieldMaps
