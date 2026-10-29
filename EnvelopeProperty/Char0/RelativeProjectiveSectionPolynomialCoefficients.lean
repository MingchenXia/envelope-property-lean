import EnvelopeProperty.AlgGeom.ProjectiveHomogeneousSections

/-! # The SAME whole native projective section retains its actual coordinate transitions

The coefficients use the original coordinate-hyperplane frames. Native over-site
restriction and the proved original frame transition derive their whole overlap
formula; no desired polynomial lifting or coefficient compatibility is an input.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Original frame coefficients commute with a genuine original open-frame transition. -/
theorem coefficient_transition_of_open_transition {X : Scheme.{u}} (M : X.Modules)
    (U V W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V)
    (a : M.restrict U.ι ≅ unitObj U.toScheme)
    (b : M.restrict V.ι ≅ unitObj V.toScheme) (r : Γ(X, W))
    (hab : (restrictOpenTrivialization hWU a).hom =
      (restrictOpenTrivialization hWV b).hom ≫
        ModularCurves.unitEndomorphismOfTopSection (openTopSection W r))
    (s : Γ(M, ⊤)) :
    X.presheaf.map (homOfLE hWU).op
      (ModularCurves.overTrivializationCoefficient M U (overTrivializationOfRestrictIso M U a) s) =
    X.presheaf.map (homOfLE hWV).op
      (ModularCurves.overTrivializationCoefficient M V (overTrivializationOfRestrictIso M V b) s) * r := by
  have h := ModularCurves.overTrivializationCoefficient_eq_mul_of_transition M W
    (overTrivializationOfRestrictIso M W (restrictOpenTrivialization hWU a))
    (overTrivializationOfRestrictIso M W (restrictOpenTrivialization hWV b)) r
    (ModularCurves.overTrivializationOfRestrictIso_hom_eq_comp_scalar M W _ _ r hab) s
  rw [overTrivializationOfRestrictOpenTrivialization,
    overTrivializationOfRestrictOpenTrivialization,
    ModularCurves.overTrivializationCoefficient_restrict,
    ModularCurves.overTrivializationCoefficient_restrict] at h
  exact h

private theorem openTopSection_pow {X : Scheme.{u}} (U : X.Opens) (r : Γ(X, U)) (e : ℕ) :
    openTopSection U (r ^ e) = openTopSection U r ^ e := by
  let f : Γ(X, U) →+* Γ(U.toScheme, ⊤) :=
    (U.ι.appIso ⊤).hom.hom.comp (X.presheaf.map (eqToHom U.ι_image_top).op).hom
  exact f.map_pow r e

variable {R : Type u} [CommRing R] {σ : Type}

/-- The actual coefficient of an original whole section in its original O(e) frame. -/
def nativeCoefficient (i j : σ) (e : ℕ)
    (s : Γ(coordinateHyperplaneTwist (R := R) j (e : ℤ), ⊤)) :
    Γ(Proj (homogeneousSubmodule σ R), coordinateOpen (R := R) i) :=
  ModularCurves.overTrivializationCoefficient
    (coordinateHyperplanePoleSheafPower (R := R) j e) (coordinateOpen (R := R) i)
    (overTrivializationOfRestrictIso
      (coordinateHyperplanePoleSheafPower (R := R) j e) (coordinateOpen (R := R) i)
      (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j e)) s

/-- EVERY original global section satisfies the genuine original coordinate transition, on the WHOLE original overlap. -/
theorem nativeCoefficient_overlap (i k j : σ) (e : ℕ)
    (s : Γ(coordinateHyperplaneTwist (R := R) j (e : ℤ), ⊤)) :
    (Proj (homogeneousSubmodule σ R)).presheaf.map
      (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op (nativeCoefficient i j e s) =
    (Proj (homogeneousSubmodule σ R)).presheaf.map
      (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op (nativeCoefficient k j e s) *
      (coordinateOpenTransitionUnit (R := R) i k :
        Γ(Proj (homogeneousSubmodule σ R), coordinateOpenOverlap (R := R) i k)) ^ e := by
  apply coefficient_transition_of_open_transition
    (coordinateHyperplanePoleSheafPower (R := R) j e)
    (coordinateOpen (R := R) i) (coordinateOpen (R := R) k)
    (coordinateOpenOverlap (R := R) i k)
    (coordinateOpenOverlap_le_left (R := R) i k)
    (coordinateOpenOverlap_le_right (R := R) i k)
    (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j e)
    (coordinateHyperplanePoleSheafPowerTrivialization (R := R) k j e) _ ?_ s
  exact (coordinateHyperplanePoleSheafPowerTrivialization_restrict_transition (R := R) i k j e).trans
    (congrArg (fun a => (restrictOpenTrivialization (coordinateOpenOverlap_le_right (R := R) i k)
      (coordinateHyperplanePoleSheafPowerTrivialization (R := R) k j e)).hom ≫
        ModularCurves.unitEndomorphismOfTopSection a)
      (openTopSection_pow _ _ e).symm)

/-- The same original coefficients detect equality of ENTIRE original global sections. -/
theorem nativeCoefficient_ext (j : σ) (e : ℕ)
    (s t : Γ(coordinateHyperplaneTwist (R := R) j (e : ℤ), ⊤))
    (h : ∀ i, nativeCoefficient i j e s = nativeCoefficient i j e t) : s = t := by
  let M := coordinateHyperplanePoleSheafPower (R := R) j e
  apply TopCat.Presheaf.IsSheaf.section_ext (F := M.presheaf) M.isSheaf
  intro x hx
  have hcover := iSup_coordinateOpen_eq_top (R := R) (σ := σ)
  have hx' : x ∈ ⨆ i, coordinateOpen (R := R) i := by simpa only [hcover] using hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
  exact ⟨coordinateOpen (R := R) i, le_top, hi,
    ModularCurves.restrict_eq_of_overTrivializationCoefficient_eq M _ _ s t (h i)⟩

/-- The actual native coefficient of the original homogeneous section is the SAME original polynomial fraction. -/
theorem nativeCoefficient_homogeneousSection (i j : σ) (e : ℕ)
    (F : MvPolynomial σ R) (hF : F.IsHomogeneous e) :
    nativeCoefficient i j e (ProjectiveHomogeneousSections.homogeneousSection j e F hF) =
      ProjectiveHomogeneousSections.coefficient i e F hF :=
  ProjectiveHomogeneousSections.section_coefficient i j e F hF

end EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomial
