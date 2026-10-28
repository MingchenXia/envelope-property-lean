import EnvelopeProperty.AlgGeom.SchemeFunctionFieldSubalgebras
import EnvelopeProperty.Berkovich.SchemeValuedPoints

/-! # Genuine generic-germ relations retain original native values on actual common opens -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped NNReal
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeValuedPoint
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A literal original product relation in SAME native K(X) gives the actual value
relation at EVERY common native point, including those with nongeneric support. -/
theorem eval_mul_of_genericGerm_mul {X : Scheme.{u}} [IsIntegral X]
    (U V : X.Opens) [Nonempty U] [Nonempty V] (y : SchemeValuedPoint X)
    (hyU : y.point ∈ U) (hyV : y.point ∈ V) (s : Γ(X,U)) (t u : Γ(X,V))
    (h : X.germToFunctionField U s * X.germToFunctionField V t = X.germToFunctionField V u) :
    eval y U hyU s * eval y V hyV t = eval y V hyV u := by
  let W := U ⊓ V
  have hyW : y.point ∈ W := ⟨hyU,hyV⟩
  let : Nonempty W := ⟨⟨y.point,hyW⟩⟩
  let rU := X.presheaf.map (homOfLE (show W ≤ U from inf_le_left)).op
  let rV := X.presheaf.map (homOfLE (show W ≤ V from inf_le_right)).op
  have hs : X.germToFunctionField W (rU s) = X.germToFunctionField U s := by
    exact X.presheaf.germ_res_apply (homOfLE (show W ≤ U from inf_le_left)) (genericPoint X)
      (((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using (inferInstance : Nonempty W))) s
  have ht (a : Γ(X,V)) : X.germToFunctionField W (rV a) = X.germToFunctionField V a := by
    exact X.presheaf.germ_res_apply (homOfLE (show W ≤ V from inf_le_right)) (genericPoint X)
      (((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using (inferInstance : Nonempty W))) a
  have he : rU s * rV t = rV u := by
    apply X.germToFunctionField_injective W
    rw [map_mul,hs,ht,ht]
    exact h
  have hv := congrArg (eval y W hyW) he
  simpa only [eval_mul,rU,rV,eval_restrict] using hv

end EnvelopeProperty.Berkovich.SchemeValuedPoint
