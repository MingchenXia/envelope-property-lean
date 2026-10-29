import EnvelopeProperty.InfinitesimalIdempotents
import EnvelopeProperty.SchemeGlobalIdempotents

/-! # Actual infinitesimal compatible idempotents detect closed-fibre connectedness -/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.FibreCompatibleConnectedness

open InfinitesimalSchemes InfinitesimalIdempotents
variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- Actual positive-order idempotent lifting detects nontriviality of the
WHOLE original order-one global-section ring, including all nilpotents. -/
theorem modelOne_globalSections_nontrivial [Nontrivial (compatibleSections I f)] :
    Nontrivial Γ(model I f 1, ⊤) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have he : (familyEquiv I f).symm ⟨0, .zero⟩ =
      (familyEquiv I f).symm ⟨1, .one⟩ := by
    apply Subtype.ext
    exact h
  have hf := (familyEquiv I f).symm.injective he
  exact zero_ne_one (congrArg Subtype.val hf)

/-- A local actual whole compatible-section ring gives connectedness of the
ENTIRE actual order-one scheme; its global ring need not equal the residue field. -/
theorem modelOne_connectedSpace [IsLocalRing (compatibleSections I f)] :
    ConnectedSpace (model I f 1) := by
  let : Nontrivial Γ(model I f 1, ⊤) := modelOne_globalSections_nontrivial I f
  apply (SchemeGlobalIdempotents.connectedSpace_iff_idempotents (model I f 1)).mpr
  refine ⟨SchemeGlobalIdempotents.nonempty_of_nontrivial_globalSections _, ?_⟩
  intro e he
  let z := familyEquiv I f ⟨e, he⟩
  have hz : z.1 = 0 ∨ z.1 = 1 := by
    obtain hu | hu := IsLocalRing.isUnit_or_isUnit_one_sub_self z.1
    · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp z.2)
    · left
      have hh := (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp z.2.one_sub
      have hh' := congrArg (fun t : compatibleSections I f => 1-t) hh
      simpa using hh'
  have hzero : z.1.1 0 = e := congrArg Subtype.val ((familyEquiv I f).symm_apply_apply ⟨e, he⟩)
  rcases hz with hz | hz
  · left
    exact hzero.symm.trans (congrArg (fun t : compatibleSections I f => t.1 0) hz)
  · right
    exact hzero.symm.trans (congrArg (fun t : compatibleSections I f => t.1 0) hz)

end EnvelopeProperty.FibreCompatibleConnectedness
