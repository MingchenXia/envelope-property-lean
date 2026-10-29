import EnvelopeProperty.AlgGeom.SchemeInvertibleHomSection
import EnvelopeProperty.AlgGeom.SchemeTensorObjMorphisms

/-! # Entire-map naturality of the original invertible Hom-section correspondence -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace EnvelopeProperty.SchemeInvertibleHomSection

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}
noncomputable local instance : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

/-- Composition of the ENTIRE original map corresponds to the SAME
actual explicit tensor map on its genuine original tensor-dual section. -/
theorem equiv_comp (A : X.Modules) (hA : Scheme.Modules.IsInvertible A)
    {B C : X.Modules} (φ : A ⟶ B) (ψ : B ⟶ C) :
    equiv A hA C (φ ≫ ψ) =
      equiv A hA B φ ≫ SchemeTensorObjMorphisms.tensorObjMap ψ (𝟙 (Scheme.Modules.dualObj A)) := by
  let E := SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA
  let adj := E.toAdjunction
  let eB := ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A)
  let eC := ModularCurves.monoidalTensorObjIso C (Scheme.Modules.dualObj A)
  have hn := adj.homEquiv_naturality_right ((λ_ A).hom ≫ φ) ψ
  have ht := SchemeTensorObjMorphisms.tensorObjMap_monoidal ψ (𝟙 (Scheme.Modules.dualObj A))
  have hc : eB.hom ≫ SchemeTensorObjMorphisms.tensorObjMap ψ (𝟙 (Scheme.Modules.dualObj A)) =
      (ψ ▷ Scheme.Modules.dualObj A) ≫ eC.hom := by
    apply (cancel_mono eC.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [ht, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
      MonoidalCategory.tensorHom_id]
  change (ModularCurves.monoidalUnitObjIso X).inv ≫
      adj.homEquiv _ _ ((λ_ A).hom ≫ (φ ≫ ψ)) ≫ eC.hom =
    ((ModularCurves.monoidalUnitObjIso X).inv ≫ adj.homEquiv _ _ ((λ_ A).hom ≫ φ) ≫ eB.hom) ≫
      SchemeTensorObjMorphisms.tensorObjMap ψ (𝟙 (Scheme.Modules.dualObj A))
  rw [← Category.assoc (λ_ A).hom φ ψ, hn]
  have heInv : E.inverse.map ψ = ψ ▷ Scheme.Modules.dualObj A := rfl
  rw [heInv]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ (ModularCurves.monoidalUnitObjIso X).inv ≫ adj.homEquiv _ _ ((λ_ A).hom ≫ φ) ≫ z)
    hc.symm

/-- An actual lift of the SAME original tensor-dual section along the
SAME original tensor map is equivalent to an actual factorization of
the ENTIRE original map. Neither lift nor factorization is postulated. -/
theorem equiv_lift_iff (A : X.Modules) (hA : Scheme.Modules.IsInvertible A)
    {B C : X.Modules} (φ : A ⟶ C) (ψ : B ⟶ C) :
    (∃ s : Scheme.Modules.unitObj X ⟶
        Scheme.Modules.tensorObj B (Scheme.Modules.dualObj A),
      s ≫ SchemeTensorObjMorphisms.tensorObjMap ψ (𝟙 (Scheme.Modules.dualObj A)) = equiv A hA C φ) ↔
      ∃ θ : A ⟶ B, θ ≫ ψ = φ := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨(equiv A hA B).symm s, ?_⟩
    apply (equiv A hA C).injective
    rw [equiv_comp, Equiv.apply_symm_apply]
    exact hs
  · rintro ⟨θ, rfl⟩
    exact ⟨equiv A hA B θ, (equiv_comp A hA θ ψ).symm⟩

end
end EnvelopeProperty.SchemeInvertibleHomSection
