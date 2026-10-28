import EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomialMaps

/-! # Actual Laurent reconstruction returns the original coordinate-index polynomials -/

open MvPolynomial
noncomputable section
universe u

namespace EnvelopeProperty.Char0.RelativeHomogeneousSectionLift
open DeJongAlterations.Geometry.ProperSteinProjectiveCech

variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The SAME original polynomial embeds injectively into the Laurent algebra
on the genuine universe-lifted original coordinates, over the SAME ring. -/
theorem originalPolynomialToLaurent_injective :
    Function.Injective
      (RelativeProjectiveSectionPolynomial.originalPolynomialToLaurent (R := R) (σ := σ)) :=
  polynomialToProjectiveLaurent_injective.comp
    (MvPolynomial.rename_injective ULift.up (fun _ _ h => congrArg ULift.down h))

/-- Every original empty-intersection Laurent element reconstructs an actual
homogeneous polynomial on the SAME original coordinate index set. -/
theorem exists_original_polynomial_of_empty_laurent [Fintype σ] [LinearOrder σ]
    (e : ℕ) (l : subsetHomogeneousLaurentModule (K := R) (I := ULift.{u} σ) (e : ℤ) ∅) :
    ∃ F : MvPolynomial σ R, ∃ _ : F.IsHomogeneous e,
      RelativeProjectiveSectionPolynomial.originalPolynomialToLaurent F = l.val := by
  obtain ⟨G, hG, hGl⟩ :=
    RelativeProjectiveSectionPolynomial.exists_polynomial_of_empty_laurent e l
  let F := MvPolynomial.rename ULift.down G
  have hF : F.IsHomogeneous e := hG.rename_isHomogeneous
  have hFG : MvPolynomial.rename ULift.up F = G := by
    change MvPolynomial.rename ULift.up (MvPolynomial.rename ULift.down G) = G
    rw [MvPolynomial.rename_rename]
    have hcomp : (ULift.up : σ → ULift.{u} σ) ∘ ULift.down = id := by
      funext x
      cases x
      rfl
    rw [hcomp, MvPolynomial.rename_id_apply]
  refine ⟨F, hF, ?_⟩
  change polynomialToProjectiveLaurent (K := R) (I := ULift.{u} σ)
    (MvPolynomial.rename ULift.up F) = l.val
  rw [hFG]
  exact hGl

/-- The SAME original native ordinary localization maps injectively to the
SAME Laurent algebra whenever its original denominator has unit image. -/
theorem originalLocalizationToLaurent_injective (f : MvPolynomial σ R)
    (hf : IsUnit (RelativeProjectiveSectionPolynomial.originalPolynomialToLaurent f)) :
    Function.Injective (RelativeProjectiveSectionPolynomial.originalLocalizationToLaurent f hf) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers f)
    (RelativeProjectiveSectionPolynomial.originalLocalizationToLaurent f hf).toRingHom).mpr
  intro x y
  constructor
  · exact congrArg (RelativeProjectiveSectionPolynomial.originalLocalizationToLaurent f hf)
  · intro h
    change RelativeProjectiveSectionPolynomial.originalLocalizationToLaurent f hf
      (algebraMap (MvPolynomial σ R) (Localization.Away f) x) =
      RelativeProjectiveSectionPolynomial.originalLocalizationToLaurent f hf
        (algebraMap (MvPolynomial σ R) (Localization.Away f) y) at h
    rw [RelativeProjectiveSectionPolynomial.originalLocalizationToLaurent_algebraMap,
      RelativeProjectiveSectionPolynomial.originalLocalizationToLaurent_algebraMap] at h
    exact congrArg (algebraMap (MvPolynomial σ R) (Localization.Away f))
      (originalPolynomialToLaurent_injective h)

/-- The SAME original native homogeneous degree-zero localization retains
EVERY original fraction under the actual original Laurent map. -/
theorem originalAwayToLaurent_injective (f : MvPolynomial σ R)
    (hf : IsUnit (RelativeProjectiveSectionPolynomial.originalPolynomialToLaurent f)) :
    Function.Injective (RelativeProjectiveSectionPolynomial.originalAwayToLaurent f hf) :=
  (originalLocalizationToLaurent_injective f hf).comp
    (show Function.Injective
      (algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule σ R) f)
        (Localization.Away f)) from HomogeneousLocalization.val_injective _)

end EnvelopeProperty.Char0.RelativeHomogeneousSectionLift
