/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.SchemeGlobalIdempotents
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Genuine original idempotent restrictions along closed scheme surjections -/
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.SchemeIdempotentRestriction
variable {X Y Z : Scheme.{u}}

/-- The ORIGINAL whole section RingHom on genuine original idempotents. -/
def map (j : Y ⟶ X) : {e : Γ(X,⊤) // IsIdempotentElem e} →
    {e : Γ(Y,⊤) // IsIdempotentElem e} := fun e =>
  ⟨j.appTop e.1,e.2.map j.appTop.hom⟩

/-- Whole ORIGINAL section restriction retains the true scheme identity. -/
theorem map_id : map (𝟙 X) = id := by
  funext e
  apply Subtype.ext
  simp [map]

/-- Whole ORIGINAL section restriction retains genuine contravariant composition. -/
theorem map_comp (i : Z ⟶ Y) (j : Y ⟶ X) : map (i ≫ j) = map i ∘ map j := by
  funext e
  apply Subtype.ext
  simp only [map,Function.comp_apply,Scheme.Hom.comp_appTop,CommRingCat.comp_apply]

/-- Actual closedness and scheme surjectivity DERIVE bijectivity ONLY on original global idempotents. -/
theorem map_bijective_of_closed_surjective (j : Y ⟶ X) [IsClosedImmersion j] [Surjective j] :
    Function.Bijective (map j) := by
  have hhomeo : IsHomeomorph j :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨j.isClosedEmbedding.isEmbedding,j.surjective⟩
  let E : Y ≃ₜ X := hhomeo.homeomorph
  constructor
  · intro e f h
    apply Subtype.ext
    apply SchemeGlobalIdempotents.eq_of_basicOpen_eq X e.2 f.2
    have hD : Y.basicOpen (j.appTop e.1)=Y.basicOpen (j.appTop f.1) :=
      congrArg (fun t : {e : Γ(Y,⊤) // IsIdempotentElem e} => Y.basicOpen t.1) h
    rw [← j.preimage_basicOpen_top,← j.preimage_basicOpen_top] at hD
    ext x
    obtain ⟨y,rfl⟩ := j.surjective x
    exact iff_of_eq (congrArg (fun V : Y.Opens => y ∈ V) hD)
  · intro e
    let V : X.Opens := ⟨E.symm ⁻¹' (Y.basicOpen e.1),(Y.basicOpen e.1).isOpen.preimage E.symm.continuous⟩
    have hV : IsClosed (V : Set X) :=
      (SchemeGlobalIdempotents.isClopen_basicOpen Y e.1 e.2).isClosed.preimage E.symm.continuous
    obtain ⟨f,hf,hfV⟩ := SchemeGlobalIdempotents.exists_idempotent_basicOpen_eq X V hV
    refine ⟨⟨f,hf⟩,?_⟩
    apply Subtype.ext
    apply SchemeGlobalIdempotents.eq_of_basicOpen_eq Y (hf.map j.appTop.hom) e.2
    rw [← j.preimage_basicOpen_top,hfV]
    ext y
    change E.symm (E y) ∈ Y.basicOpen e.1 ↔ y ∈ Y.basicOpen e.1
    rw [E.symm_apply_apply]

end EnvelopeProperty.SchemeIdempotentRestriction
