/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeParameterProduct

/-!
# Actual parameter families on genuine original closed subschemes

The whole original defining ideal gives the actual restricted family.  Its
source is identified with the whole geometric coefficient product through
actual closed-immersion and native-Proj pullback squares.  Nothing is inferred
from pointwise preservation of a support or equality of Gauss functions.
-/

open scoped Classical Polynomial LaurentPolynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}

/-- The whole actual original base homogeneous ideal extended by the parameter. -/
def nativeConstantIdeal (J : HomogeneousIdeal (ProjectiveGrading R n)) :
    (NativeProjectiveScheme R[X] n).IdealSheafData :=
  nativeHomogeneousIdealSheaf (J.map (coefficientGradedMap Polynomial.C))

/-- The actual parameter family pulls the whole original constant ideal back
to its actual coefficient-extended constant ideal, with no invariance input. -/
theorem nativeConstantIdeal_comap_parameterFamily
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (f : R →+* S) (u : Sˣ) :
    (nativeConstantIdeal J).comap (nativeParameterFamilyMap f u) =
      nativeConstantIdeal (J.map (coefficientGradedMap f)) := by
  change (GradedQuotient.quotientIdealSheaf _ _).comap
    (nativeCoefficientMap (parameterUnitBaseChangeHom f u)) = _
  rw [homogeneousQuotientIdealSheaf_comap_coefficientMap]
  congr 1
  apply HomogeneousIdeal.toIdeal_injective
  change (J.toIdeal.map (MvPolynomial.map Polynomial.C)).map
    (MvPolynomial.map (parameterUnitBaseChangeHom f u)) =
      (J.toIdeal.map (MvPolynomial.map f)).map (MvPolynomial.map Polynomial.C)
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro F
  change MvPolynomial.map (parameterUnitBaseChangeHom f u) (MvPolynomial.map Polynomial.C F) =
    MvPolynomial.map Polynomial.C (MvPolynomial.map f F)
  rw [MvPolynomial.map_map, MvPolynomial.map_map]
  have hc : (parameterUnitBaseChangeHom f u).comp Polynomial.C = Polynomial.C.comp f := by
    apply RingHom.ext
    intro r
    exact parameterUnitBaseChangeHom_C f u r
  rw [hc]

/-- The genuine original closed family has its actual parameter-family map. -/
def nativeClosedParameterFamilyMap (J : HomogeneousIdeal (ProjectiveGrading R n))
    (f : R →+* S) (u : Sˣ) :
    (nativeConstantIdeal (J.map (coefficientGradedMap f))).subscheme ⟶
      (nativeConstantIdeal J).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ (nativeParameterFamilyMap f u)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (nativeConstantIdeal_comap_parameterFamily J f u).le)

/-- The restricted entire family retains its exact whole ambient triangle. -/
@[reassoc]
theorem nativeClosedParameterFamilyMap_ι (J : HomogeneousIdeal (ProjectiveGrading R n))
    (f : R →+* S) (u : Sˣ) :
    nativeClosedParameterFamilyMap J f u ≫ (nativeConstantIdeal J).subschemeι =
      (nativeConstantIdeal (J.map (coefficientGradedMap f))).subschemeι ≫
        nativeParameterFamilyMap f u :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (nativeConstantIdeal_comap_parameterFamily J f u).le)

/-- The whole original closed-family coefficient square is genuinely cartesian. -/
theorem isPullback_nativeClosedParameterProduct
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (f : R →+* S) :
    IsPullback (nativeClosedParameterFamilyMap J f 1)
      ((nativeConstantIdeal (J.map (coefficientGradedMap f))).subschemeι ≫
        nativeStructureMap ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : S →+* S[X])))
      ((nativeConstantIdeal J).subschemeι ≫
        nativeStructureMap ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))
      (Spec.map (CommRingCat.ofHom f)) := by
  have h : (nativeConstantIdeal J).comap (nativeParameterFamilyMap f 1) =
      nativeConstantIdeal (J.map (coefficientGradedMap f)) :=
    nativeConstantIdeal_comap_parameterFamily J f 1
  have hs := (isPullback_of_isClosedImmersion
    (nativeConstantIdeal (J.map (coefficientGradedMap f))).subschemeι
    (nativeConstantIdeal J).subschemeι (nativeClosedParameterFamilyMap J f 1)
    (nativeParameterFamilyMap f 1) (nativeClosedParameterFamilyMap_ι J f 1).symm
    (by simpa only [Scheme.IdealSheafData.ker_subschemeι] using h)).flip
  have ha : nativeParameterFamilyMap (n := n) f 1 =
      nativeCoefficientMap (Polynomial.mapRingHom f) := by
    unfold nativeParameterFamilyMap
    rw [parameterUnitBaseChangeHom_one]
  simpa only [ha, Category.assoc] using
    hs.paste_vert (ha.symm ▸ isPullback_nativeParameterProduct (n := n) f)

/-- The true whole closed-family geometric coefficient-product isomorphism. -/
def nativeClosedParameterProductIso
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (f : R →+* S) :
    (nativeConstantIdeal (J.map (coefficientGradedMap f))).subscheme ≅
      pullback ((nativeConstantIdeal J).subschemeι ≫ nativeStructureMap ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))
        (Spec.map (CommRingCat.ofHom f)) :=
  (isPullback_nativeClosedParameterProduct J f).isoPullback

/-- The actual original closed-family product comparison preserves projection. -/
@[reassoc]
theorem nativeClosedParameterProductIso_hom_fst
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (f : R →+* S) :
    (nativeClosedParameterProductIso J f).hom ≫ pullback.fst _ _ =
      nativeClosedParameterFamilyMap J f 1 :=
  (isPullback_nativeClosedParameterProduct J f).isoPullback_hom_fst

/-- A single actual morphism on the whole multiplicative-group product of the
genuine original closed native parameter family. -/
def nativeClosedParameterLaurentActionMorphism
    (J : HomogeneousIdeal (ProjectiveGrading R n)) :
    pullback ((nativeConstantIdeal J).subschemeι ≫ nativeStructureMap ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* R[T;T⁻¹]))) ⟶
        (nativeConstantIdeal J).subscheme :=
  (nativeClosedParameterProductIso J LaurentPolynomial.C).inv ≫
    nativeClosedParameterFamilyMap J LaurentPolynomial.C (parameterLaurentUnit R)

/-- Whole coefficient-extended unit invariance of the original ring ideal
proves equality of actual sheaf pullbacks along the entire family and projection. -/
theorem nativeHomogeneousIdealSheaf_comap_parameterFamily_eq
    (I : HomogeneousIdeal (ProjectiveGrading R[X] n)) (f : R →+* S) (u : Sˣ)
    (hI : (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
      (MvPolynomial.map (parameterScaleHom (u : S))) =
        I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))) :
    (nativeHomogeneousIdealSheaf I).comap (nativeParameterFamilyMap f u) =
      (nativeHomogeneousIdealSheaf I).comap (nativeParameterFamilyMap f 1) := by
  change (GradedQuotient.quotientIdealSheaf _ I).comap
    (nativeCoefficientMap (parameterUnitBaseChangeHom f u)) =
      (GradedQuotient.quotientIdealSheaf _ I).comap
        (nativeCoefficientMap (parameterUnitBaseChangeHom f 1))
  rw [homogeneousQuotientIdealSheaf_comap_coefficientMap,
    homogeneousQuotientIdealSheaf_comap_coefficientMap, parameterUnitBaseChangeHom_one]
  congr 1
  apply HomogeneousIdeal.toIdeal_injective
  change I.toIdeal.map (MvPolynomial.map
      ((parameterScaleHom (u : S)).comp (Polynomial.mapRingHom f))) = _
  have hc : MvPolynomial.map (σ := Fin (n + 1))
      ((parameterScaleHom (u : S)).comp (Polynomial.mapRingHom f)) =
      (MvPolynomial.map (parameterScaleHom (u : S))).comp
        (MvPolynomial.map (Polynomial.mapRingHom f)) := by
    apply RingHom.ext
    intro F
    exact (MvPolynomial.map_map _ _ _).symm
  rw [hc, ← Ideal.map_map]
  exact hI

/-- The whole original restricted ideal is preserved by the entire genuine
closed-family parameter map, with equality to its actual unscaled projection. -/
theorem nativeClosedIdeal_comap_parameterFamily_eq
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (I : HomogeneousIdeal (ProjectiveGrading R[X] n)) (f : R →+* S) (u : Sˣ)
    (hI : (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
      (MvPolynomial.map (parameterScaleHom (u : S))) =
        I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))) :
    ((nativeHomogeneousIdealSheaf I).comap (nativeConstantIdeal J).subschemeι).comap
        (nativeClosedParameterFamilyMap J f u) =
      ((nativeHomogeneousIdealSheaf I).comap (nativeConstantIdeal J).subschemeι).comap
        (nativeClosedParameterFamilyMap J f 1) := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    nativeClosedParameterFamilyMap_ι, nativeClosedParameterFamilyMap_ι,
    Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
    nativeHomogeneousIdealSheaf_comap_parameterFamily_eq I f u hI]

end EnvelopeProperty.ProjBerk
