import EnvelopeProperty.AlgGeom.AffineFunctionFieldGeneration

/-! # Literal original scalar compatibility of original section pullbacks and native generic germs -/

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
noncomputable section
universe u
namespace EnvelopeProperty.SchemeFunctionFieldPullbackCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ Spec (.of k))

/-- The SAME original section map is linear over the literal original composite coefficient map. -/
def sectionMap (V : Y.Opens) :
    letI := q.sectionsAlgebra V
    letI := (f ≫ q).sectionsAlgebra (f ⁻¹ᵁ V)
    Γ(Y, V) →ₐ[k] Γ(X, f ⁻¹ᵁ V) := by
  letI := q.sectionsAlgebra V
  letI := (f ≫ q).sectionsAlgebra (f ⁻¹ᵁ V)
  refine { (f.app V).hom with commutes' := ?_ }
  intro a
  rw [Scheme.Hom.algebraMap_sectionsAlgebra, Scheme.Hom.algebraMap_sectionsAlgebra]
  have hc := Scheme.Hom.appLE_comp_appLE f q ⊤ V (f ⁻¹ᵁ V) le_top le_rfl
  have hf : f.appLE V (f ⁻¹ᵁ V) le_rfl = f.app V := by
    simp only [Scheme.Hom.appLE, homOfLE_refl, op_id]
    rw [X.presheaf.map_id, Category.comp_id]
  rw [hf] at hc
  exact congrArg (fun z => ((Scheme.ΓSpecIso (.of k)).inv ≫ z).hom a) hc

variable [IsIntegral X]

/-- The TRUE original pullback followed by the actual generic germ, with SAME original k scalars. -/
def genericMap (V : Y.Opens) [Nonempty (f ⁻¹ᵁ V)] :
    letI := q.sectionsAlgebra V
    letI := (f ≫ q).stalkAlgebra (genericPoint X)
    Γ(Y, V) →ₐ[k] X.functionField := by
  letI := q.sectionsAlgebra V
  letI := (f ≫ q).sectionsAlgebra (f ⁻¹ᵁ V)
  letI := (f ≫ q).stalkAlgebra (genericPoint X)
  exact ((f ≫ q).sectionsFunctionFieldAlgHom (f ⁻¹ᵁ V)).comp (sectionMap f q V)

/-- Every SAME original section retains its literal original pulled generic coefficient. -/
theorem genericMap_apply (V : Y.Opens) [Nonempty (f ⁻¹ᵁ V)] (a : Γ(Y, V)) :
    letI := q.sectionsAlgebra V
    letI := (f ≫ q).stalkAlgebra (genericPoint X)
    genericMap f q V a = X.germToFunctionField (f ⁻¹ᵁ V) (f.app V a) := rfl

end EnvelopeProperty.SchemeFunctionFieldPullbackCoefficients
