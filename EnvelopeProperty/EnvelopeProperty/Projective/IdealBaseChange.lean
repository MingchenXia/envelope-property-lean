/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeBaseChange
import EnvelopeProperty.Projective.NativeQuotient
import EnvelopeProperty.Berkovich.SchemeIdealPullback

/-!
# Whole homogeneous quotient ideal sheaves under actual coefficient base change

Entire genuine affine section squares and actual geometric ideal-image formulas
identify the whole original projective ideal pullback. No coefficient flatness,
injectivity, reducedness, finite-generation or sheaf-comparison certificate is
assumed, and no radical replacement is made.
-/

open scoped Classical
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}

/-- The true whole projective quotient-kernel ideal sheaf has exactly its original homogeneous-ideal coefficient base change. -/
theorem homogeneousQuotientIdealSheaf_comap_coefficientMap
    (φ : R →+* S) (J : HomogeneousIdeal (ProjectiveGrading R n)) :
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap (nativeCoefficientMap φ) =
      GradedQuotient.quotientIdealSheaf (ProjectiveGrading S n) (J.map (coefficientGradedMap φ)) := by
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun j : Fin (n + 1) => ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩)
    iSup_nativeCoordinateOpen_eq_top
  intro j
  let Ur : (NativeProjectiveScheme R n).affineOpens :=
    ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩
  let Us : (NativeProjectiveScheme S n).affineOpens :=
    ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩
  have hp : Us.1 ≤ nativeCoefficientMap φ ⁻¹ᵁ Ur.1 := by
    rw [nativeCoefficientMap_preimage_coordinateOpen]
  let eR := (nativeCoordinateSectionsIso (R := R) j).hom.hom
  let eS := (nativeCoordinateSectionsIso (R := S) j).hom.hom
  let a := (nativeCoefficientMap φ).appLE Ur.1 Us.1 hp
  let m : CoordinateRing R j →+* CoordinateRing S j := MvPolynomial.map φ
  have hc : a.hom.comp eR = eS.comp m := by
    exact congrArg CommRingCat.Hom.hom (nativeCoefficientMap_coordinateSections φ j)
  have ht (L : Ideal Γ(NativeProjectiveScheme R n, Ur)) :
      (L.map a.hom).comap eS = (L.comap eR).map m := by
    conv_lhs => rw [← Ideal.map_comap_of_surjective eR
      (ConcreteCategory.bijective_of_isIso (nativeCoordinateSectionsIso (R := R) j).hom).surjective L]
    rw [Ideal.map_map, hc, ← Ideal.map_map,
      Ideal.comap_map_of_bijective eS
        (ConcreteCategory.bijective_of_isIso (nativeCoordinateSectionsIso (R := S) j).hom)]
  apply Ideal.comap_injective_of_surjective eS
    (ConcreteCategory.bijective_of_isIso (nativeCoordinateSectionsIso (R := S) j).hom).surjective
  rw [Scheme.IdealSheafData.comap_ideal_of_affine_opens _ _ Us Ur hp, ht,
    homogeneousQuotient_coordinateSectionIdeal,
    homogeneousQuotient_coordinateSectionIdeal]
  change (J.toIdeal.map (coordinateDehom j).toRingHom).map (MvPolynomial.map φ) =
    (J.toIdeal.map (MvPolynomial.map φ)).map (coordinateDehom j).toRingHom
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro F
  exact (coordinateDehom_map φ j F).symm

end EnvelopeProperty.ProjBerk
