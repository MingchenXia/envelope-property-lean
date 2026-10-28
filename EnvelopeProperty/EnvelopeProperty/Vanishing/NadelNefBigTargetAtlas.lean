import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigTargetAtlas

/-- An actual whole source chart which is the exact target inverse open
transfers its immersion property to the actual target restriction. -/
theorem restrict_isImmersion_of_exact_chart {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (j : T ⟶ X) [IsOpenImmersion j] [IsImmersion (j ≫ f)]
    (U : Y.Opens) (h : f ⁻¹ᵁ U = j.opensRange) : IsImmersion (f ∣_ U) := by
  let e : T ≅ (f ⁻¹ᵁ U).toScheme := j.isoOpensRange ≪≫ X.isoOfEq h.symm
  have he : e.hom ≫ (f ⁻¹ᵁ U).ι = j := by
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.isoOpensRange_hom_ι]
  have ht : (e.hom ≫ (f ∣_ U)) ≫ U.ι = j ≫ f := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, he]
  have hc : IsImmersion ((e.hom ≫ (f ∣_ U)) ≫ U.ι) := ht.symm ▸ inferInstance
  let := hc
  have hi : IsImmersion (e.hom ≫ (f ∣_ U)) := IsImmersion.of_comp _ U.ι
  let := hi
  have hc' : IsImmersion (e.inv ≫ (e.hom ≫ (f ∣_ U))) := inferInstance
  exact e.inv_hom_id_assoc (f ∣_ U) ▸ hc'

theorem restrict_isImmersion_of_empty_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (h : f ⁻¹ᵁ U = ⊥) : IsImmersion (f ∣_ U) := by
  let : IsEmpty (f ⁻¹ᵁ U).toScheme := ⟨fun x => by
    have hx : x.1 ∈ (f ⁻¹ᵁ U) := x.2
    exact (congrArg (fun V : X.Opens => (x.1 : X) ∈ V) h).mp hx⟩
  infer_instance

end EnvelopeProperty.Vanishing.NadelNefBigTargetAtlas
