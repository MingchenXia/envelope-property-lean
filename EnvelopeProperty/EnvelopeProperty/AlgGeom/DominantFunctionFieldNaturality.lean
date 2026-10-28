import EnvelopeProperty.AlgGeom.DominantFunctionFieldMaps
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Native original function-field functoriality and actual open-square degrees -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.DominantFunctionFieldNaturality
open DominantFunctionFieldMaps
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME original native dominant generic-stalk maps compose contravariantly. -/
theorem functionFieldMap_comp {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g] :
    functionFieldMap g ≫ functionFieldMap f = functionFieldMap (f ≫ g) := by
  unfold functionFieldMap
  rw [Scheme.Hom.stalkMap_comp]
  have hn := g.stalkSpecializes_stalkMap (f (genericPoint X)) (genericPoint Y)
    (specializes_of_eq (genericPoint_map f))
  change (Z.presheaf.stalkSpecializes (specializes_of_eq (genericPoint_map g)) ≫
    g.stalkMap (genericPoint Y)) ≫
      (Y.presheaf.stalkSpecializes (specializes_of_eq (genericPoint_map f)) ≫
        f.stalkMap (genericPoint X)) =
    Z.presheaf.stalkSpecializes (specializes_of_eq (genericPoint_map (f ≫ g))) ≫
      (g.stalkMap (f (genericPoint X)) ≫ f.stalkMap (genericPoint X))
  rw [Category.assoc, ← Category.assoc (g.stalkMap (genericPoint Y)), ← hn,
    ← Category.assoc, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  rfl

/-- An actual original dominant open immersion induces a genuine SAME native function-field isomorphism. -/
theorem functionFieldMap_isIso {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsOpenImmersion f] : IsIso (functionFieldMap f) := by
  change IsIso ((Y.presheaf.stalkCongr (.of_eq (genericPoint_map f).symm)).hom ≫ f.stalkMap (genericPoint X))
  infer_instance

private theorem functionFieldMap_congr {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f g : X ⟶ Y) [IsDominant f] [IsDominant g] (h : f = g) :
    functionFieldMap f = functionFieldMap g := by
  subst g
  rfl

/-- The TRUE native function-field degree of the SAME original dominant map
is preserved by an ACTUAL whole original open-immersion square. -/
theorem finrank_eq_of_open_square {X Y X' Y' : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral X'] [IsIntegral Y']
    (f : X ⟶ Y) (f' : X' ⟶ Y') (iX : X' ⟶ X) (iY : Y' ⟶ Y)
    [IsDominant f] [IsDominant f'] [IsDominant iX] [IsDominant iY]
    [IsOpenImmersion iX] [IsOpenImmersion iY] (h : iX ≫ f = f' ≫ iY) :
    letI := (functionFieldMap f).hom.toAlgebra
    letI := (functionFieldMap f').hom.toAlgebra
    Module.finrank Y.functionField X.functionField = Module.finrank Y'.functionField X'.functionField := by
  let := (functionFieldMap f).hom.toAlgebra
  let := (functionFieldMap f').hom.toAlgebra
  let : IsIso (functionFieldMap iX) := functionFieldMap_isIso iX
  let : IsIso (functionFieldMap iY) := functionFieldMap_isIso iY
  apply Algebra.finrank_eq_of_equiv_equiv
    (asIso (functionFieldMap iY)).commRingCatIsoToRingEquiv
    (asIso (functionFieldMap iX)).commRingCatIsoToRingEquiv
  have he : functionFieldMap iY ≫ functionFieldMap f' = functionFieldMap f ≫ functionFieldMap iX := by
    rw [functionFieldMap_comp, functionFieldMap_comp]
    exact functionFieldMap_congr _ _ h.symm
  exact congrArg CommRingCat.Hom.hom he

end EnvelopeProperty.DominantFunctionFieldNaturality
