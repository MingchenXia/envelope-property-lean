import EnvelopeProperty.AlgGeom.InvertibleSectionFamilyImage
import EnvelopeProperty.AlgGeom.ProjectiveLineBaseIdealGenerators

/-! # Actual all-section and finite projective tensor evaluation images -/
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.InvertibleSectionFamilyImage
open Scheme.Modules InvertibleSheafBaseIdeal
attribute [local instance] Scheme.Modules.monoidalCategory

/-- Taking ALL original global sections recovers the SAME whole original base ideal. -/
theorem allSections_imageIdeal {X : Scheme.{u}} {L : X.Modules}
    (hL : IsInvertible L) :
    let : ((tensorRight (C := X.Modules) (dualObj L)).obj
      (SheafOfModules.free (R := X.ringCatSheaf) Γ(L, ⊤))).IsQuasicoherent :=
      freeTensorDual_isQuasicoherent hL Γ(L, ⊤)
    QuasicoherentImageIdeal.imageIdeal _ (familyEvaluation hL (fun s : Γ(L, ⊤) => s)) =
      baseIdeal hL :=
  familyEvaluation_imageIdeal hL (fun s : Γ(L, ⊤) => s)

/-- The original projective geometry internally produces one finite original
family whose actual tensor evaluation has the WHOLE all-global-section image ideal. -/
theorem exists_projective_finite_imageIdeal {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (hf : IsProjectiveFactorization f)
    (L : X.Modules) (hL : IsInvertible L) :
    ∃ G : Finset Γ(L, ⊤),
      let : ((tensorRight (C := X.Modules) (dualObj L)).obj
        (SheafOfModules.free (R := X.ringCatSheaf) G)).IsQuasicoherent :=
        freeTensorDual_isQuasicoherent hL G
      QuasicoherentImageIdeal.imageIdeal _
        (familyEvaluation hL (fun s : G => s.1)) = baseIdeal hL := by
  obtain ⟨G, hG⟩ := ProjectiveLineBaseIdealGenerators.exists_finite_global_generators f hf L hL
  refine ⟨G, (familyEvaluation_imageIdeal hL (fun s : G => s.1)).trans ?_⟩
  rw [iSup_subtype]
  exact hG.symm

end EnvelopeProperty.InvertibleSectionFamilyImage
