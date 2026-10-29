import EnvelopeProperty.AlgGeom.SchemeFunctionFieldSubalgebras
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Genuine affine-chart generators of the ENTIRE actual native function field -/

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.AffineFunctionFieldGeneration
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (p : X ⟶ Spec (.of k))

/-- The SAME original nonempty affine section germs generate ALL of the actual K(X). -/
theorem adjoin_sectionGerms_eq_top (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    letI := p.stalkAlgebra (genericPoint X)
    IntermediateField.adjoin k (Set.range fun a : Γ(X, U) => X.germToFunctionField U a) = ⊤ := by
  let := p.stalkAlgebra (genericPoint X)
  let : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  apply top_unique
  intro z _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) z
  exact IntermediateField.div_mem _ (IntermediateField.subset_adjoin k _ ⟨a, rfl⟩)
    (IntermediateField.subset_adjoin k _ ⟨b, rfl⟩)

/-- Actual local finite type INTERNALLY produces finitely many original affine sections
whose SAME actual native germs generate the ENTIRE original K(X). -/
theorem exists_finite_sectionGerms [LocallyOfFiniteType p]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    letI := p.stalkAlgebra (genericPoint X)
    ∃ s : Finset Γ(X, U), IntermediateField.adjoin k
      ((fun a : Γ(X, U) => X.germToFunctionField U a) '' (s : Set Γ(X, U))) = ⊤ := by
  classical
  let := p.stalkAlgebra (genericPoint X)
  let := p.sectionsAlgebra U
  let : Algebra.FiniteType k Γ(X, U) := p.finiteType_sectionsAlgebra hU
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k Γ(X, U)).FG)
  let F := IntermediateField.adjoin k
    ((fun a : Γ(X, U) => X.germToFunctionField U a) '' (s : Set Γ(X, U)))
  refine ⟨s, ?_⟩
  have hall : ∀ a : Γ(X, U), X.germToFunctionField U a ∈ F := by
    intro a
    have ha : a ∈ Algebra.adjoin k (s : Set Γ(X, U)) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem a ha => exact IntermediateField.subset_adjoin k _ ⟨a, ha, rfl⟩
    | algebraMap a =>
      change (p.sectionsFunctionFieldAlgHom U) (algebraMap k Γ(X, U) a) ∈ F
      rw [AlgHom.commutes]
      exact F.algebraMap_mem a
    | add a b _ _ ha hb => rw [map_add]; exact F.add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact F.mul_mem ha hb
  apply top_unique
  rw [← adjoin_sectionGerms_eq_top p U hU, IntermediateField.adjoin_le_iff]
  rintro _ ⟨a, rfl⟩
  exact hall a

/-- A true original closed embedding DERIVES all-field generation from the SAME original
ambient affine functions, through their actual original pullback and actual generic germs. -/
theorem closedImmersion_adjoin_eq_top {Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty (f ⁻¹ᵁ V)] :
    letI := p.stalkAlgebra (genericPoint X)
    IntermediateField.adjoin k (Set.range fun a : Γ(Y, V) =>
      X.germToFunctionField (f ⁻¹ᵁ V) (f.app V a)) = ⊤ := by
  let := p.stalkAlgebra (genericPoint X)
  apply top_unique
  rw [← adjoin_sectionGerms_eq_top p (f ⁻¹ᵁ V) (hV.preimage f), IntermediateField.adjoin_le_iff]
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, rfl⟩ := f.app_surjective V hV a
  exact IntermediateField.subset_adjoin k _ ⟨b, rfl⟩

end EnvelopeProperty.AffineFunctionFieldGeneration
