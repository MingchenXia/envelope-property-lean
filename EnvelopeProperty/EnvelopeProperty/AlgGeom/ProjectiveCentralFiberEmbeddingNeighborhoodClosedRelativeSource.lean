import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedPartial

/-! # The actual source of the same partial map over an original base open -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRelativeSource
variable {R : Type u} [CommRing R] {Y Z : Scheme.{u}}

private theorem partialRestriction_isPullback
    (p : Y ⟶ Spec (CommRingCat.of R)) (q : Z ⟶ Spec (CommRingCat.of R))
    (U : Y.Opens) (f : U.toScheme ⟶ Z) (hf : f ≫ q = U.ι ≫ p)
    (B : (Spec (CommRingCat.of R)).Opens) (hB : p ⁻¹ᵁ B ≤ U) :
    IsPullback ((f ∣_ (q ⁻¹ᵁ B)) ≫ (q ∣_ B))
      ((f ⁻¹ᵁ (q ⁻¹ᵁ B)).ι ≫ U.ι) B.ι p := by
  let V := q ⁻¹ᵁ B
  let W := f ⁻¹ᵁ V
  let i : W.toScheme ⟶ Y := W.ι ≫ U.ι
  let r : W.toScheme ⟶ B.toScheme := (f ∣_ V) ≫ (q ∣_ B)
  have hcomm : i ≫ p = r ≫ B.ι := by
    calc
      i ≫ p = W.ι ≫ (U.ι ≫ p) := by dsimp only [i]; rw [Category.assoc]
      _ = W.ι ≫ (f ≫ q) := by rw [hf]
      _ = ((f ∣_ V) ≫ V.ι) ≫ q := by rw [morphismRestrict_ι, Category.assoc]
      _ = r ≫ B.ι := by
        dsimp only [r, V]
        simpa only [Category.assoc] using
          congrArg (fun a => (f ∣_ (q ⁻¹ᵁ B)) ≫ a) (morphismRestrict_ι q B).symm
  have hrange : p ⁻¹ᵁ B.ι.opensRange = i.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    ext y
    change p y ∈ B ↔ y ∈ Set.range i
    constructor
    · intro hy
      let x : U.toScheme := ⟨y, hB hy⟩
      have hx : f x ∈ V := by
        change q (f x) ∈ B
        have he : q (f x) = p (U.ι x) := congrArg (fun a => a x) hf
        rw [he]
        exact hy
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      have he : q (f x.1) = p (U.ι x.1) := congrArg (fun a => a x.1) hf
      exact he ▸ x.2
  exact IsOpenImmersion.isPullback r i B.ι p hcomm hrange

/-- The ACTUAL original whole inverse-image source is canonically isomorphic
to the source of the SAME actual partial target restriction. The actual two
pullback squares and their comparison are internally constructed. -/
def baseOpenSourceIso
    (p : Y ⟶ Spec (CommRingCat.of R)) (q : Z ⟶ Spec (CommRingCat.of R))
    (U : Y.Opens) (f : U.toScheme ⟶ Z) (hf : f ≫ q = U.ι ≫ p)
    (B : (Spec (CommRingCat.of R)).Opens) (hB : p ⁻¹ᵁ B ≤ U) :
    (p ⁻¹ᵁ B).toScheme ≅ (f ⁻¹ᵁ (q ⁻¹ᵁ B)).toScheme :=
  (isPullback_morphismRestrict p B).isoPullback ≪≫
    (partialRestriction_isPullback p q U f hf B hB).isoPullback.symm

/-- The WHOLE actual source comparison retains exactly the SAME original
open factor, not merely a pointwise or reduced-source comparison. -/
theorem baseOpenSourceIso_inclusion
    (p : Y ⟶ Spec (CommRingCat.of R)) (q : Z ⟶ Spec (CommRingCat.of R))
    (U : Y.Opens) (f : U.toScheme ⟶ Z) (hf : f ≫ q = U.ι ≫ p)
    (B : (Spec (CommRingCat.of R)).Opens) (hB : p ⁻¹ᵁ B ≤ U) :
    (baseOpenSourceIso p q U f hf B hB).hom ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ B)).ι =
      Y.homOfLE hB := by
  let hnew := isPullback_morphismRestrict p B
  let hold := partialRestriction_isPullback p q U f hf B hB
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, Scheme.homOfLE_ι]
  change hnew.isoPullback.hom ≫
      (hold.isoPullback.inv ≫ ((f ⁻¹ᵁ (q ⁻¹ᵁ B)).ι ≫ U.ι)) = (p ⁻¹ᵁ B).ι
  rw [hold.isoPullback_inv_snd]
  exact hnew.isoPullback_hom_snd

/-- The SAME actual factor from a WHOLE inverse image of an affine base open
to the original source open is affine. Its affineness is derived from the
actual original restriction square and separatedness of the original inclusion. -/
theorem baseOpenSourceFactor_isAffine
    (p : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens)
    (B : (Spec (CommRingCat.of R)).Opens) [IsAffine B.toScheme]
    (hB : p ⁻¹ᵁ B ≤ U) : IsAffineHom (Y.homOfLE hB) := by
  let : IsAffineHom B.ι := inferInstance
  let : IsAffineHom (p ⁻¹ᵁ B).ι :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_morphismRestrict p B) (inferInstance : IsAffineHom B.ι)
  let : IsAffineHom (Y.homOfLE hB ≫ U.ι) :=
    (Scheme.homOfLE_ι Y hB).symm ▸ (inferInstance : IsAffineHom (p ⁻¹ᵁ B).ι)
  exact IsAffineHom.of_comp (Y.homOfLE hB) U.ι

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRelativeSource
