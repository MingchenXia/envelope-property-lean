import EnvelopeProperty.AlgGeom.ProjectiveSectionFamilyImage

/-! # Actual finite original evaluation epimorphisms onto the whole base ideal -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveBaseIdealEpimorphism
open Scheme.Modules InvertibleSheafBaseIdeal InvertibleSectionFamilyImage
attribute [local instance] Scheme.Modules.monoidalCategory

/-- Transport the SAME original image factor along an equality of actual ideals. -/
def imageFactorOfEq {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
    (α : M ⟶ unitObj X) (I : X.IdealSheafData)
    (h : QuasicoherentImageIdeal.imageIdeal M α = I) : M ⟶ I.toModules :=
  QuasicoherentImageModule.imageFactor α ≫
    eqToHom (congrArg (fun J : X.IdealSheafData => J.toModules) h)

/-- The original whole source-to-image factor stays epimorphic under target transport. -/
theorem imageFactorOfEq_epi {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
    (α : M ⟶ unitObj X) (I : X.IdealSheafData)
    (h : QuasicoherentImageIdeal.imageIdeal M α = I) : Epi (imageFactorOfEq α I h) := by
  let : Epi (QuasicoherentImageModule.imageFactor α) :=
    QuasicoherentImageModule.imageFactor_epi α
  unfold imageFactorOfEq
  infer_instance

/-- The transported factor has EXACTLY the original whole evaluation composite. -/
theorem imageFactorOfEq_inclusion {X : Scheme.{u}} {M : X.Modules}
    [M.IsQuasicoherent] (α : M ⟶ unitObj X) (I : X.IdealSheafData)
    (h : QuasicoherentImageIdeal.imageIdeal M α = I) :
    imageFactorOfEq α I h ≫ I.toModulesInclusion = α := by
  subst I
  simpa only [imageFactorOfEq, eqToHom_refl, Category.comp_id] using
    QuasicoherentImageModule.imageFactor_inclusion α

/-- The actual original projective geometry yields a finite original section
family and a TRUE whole base-ideal epimorphism with its original composite. -/
theorem exists_finite_original_baseIdeal_epi {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (hf : IsProjectiveFactorization f)
    (L : X.Modules) (hL : IsInvertible L) :
    ∃ (G : Finset Γ(L, ⊤))
      (p : (tensorRight (C := X.Modules) (dualObj L)).obj
        (SheafOfModules.free (R := X.ringCatSheaf) G) ⟶ (baseIdeal hL).toModules),
      Epi p ∧ p ≫ (baseIdeal hL).toModulesInclusion =
        familyEvaluation hL (fun s : G => s.1) := by
  obtain ⟨G, hG⟩ := exists_projective_finite_imageIdeal f hf L hL
  let : ((tensorRight (C := X.Modules) (dualObj L)).obj
    (SheafOfModules.free (R := X.ringCatSheaf) G)).IsQuasicoherent :=
    freeTensorDual_isQuasicoherent hL G
  let α := familyEvaluation hL (fun s : G => s.1)
  exact ⟨G, imageFactorOfEq α (baseIdeal hL) hG,
    imageFactorOfEq_epi α _ hG, imageFactorOfEq_inclusion α _ hG⟩

end EnvelopeProperty.ProjectiveBaseIdealEpimorphism
