/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeParameterClosedFamily

/-!
# Whole parameter maps between prescribed original closed families

Exact coefficient-ideal images supply the genuine native closed maps needed
for universal unit sections and multiplication diagrams. Their identity and
composition laws are equalities of entire scheme morphisms.
-/

open scoped Classical Polynomial LaurentPolynomial
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {n : ℕ}

/-- Whole homogeneous coefficient-image ideals preserve actual composition. -/
theorem homogeneousIdeal_coefficient_map_map (J : HomogeneousIdeal (ProjectiveGrading R n))
    (f : R →+* S) (g : S →+* T) :
    (J.map (coefficientGradedMap f)).map (coefficientGradedMap g) =
      J.map (coefficientGradedMap (g.comp f)) := by
  apply HomogeneousIdeal.toIdeal_injective
  change (J.toIdeal.map (MvPolynomial.map f)).map (MvPolynomial.map g) =
    J.toIdeal.map (MvPolynomial.map (g.comp f))
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro F
  exact MvPolynomial.map_map f g F

/-- Whole homogeneous coefficient-image ideals preserve actual identity. -/
theorem homogeneousIdeal_coefficient_map_id (J : HomogeneousIdeal (ProjectiveGrading R n)) :
    J.map (coefficientGradedMap (RingHom.id R)) = J := by
  apply HomogeneousIdeal.toIdeal_injective
  change J.toIdeal.map (MvPolynomial.map (RingHom.id R)) = J.toIdeal
  have h : MvPolynomial.map (σ := Fin (n + 1)) (RingHom.id R) = RingHom.id _ := by
    apply RingHom.ext
    exact MvPolynomial.map_id
  rw [h, Ideal.map_id]

/-- The whole original-coefficient structure of the genuine closed parameter family. -/
def nativeClosedBaseStructure (J : HomogeneousIdeal (ProjectiveGrading R n)) :
    (nativeConstantIdeal J).subscheme ⟶ Spec (CommRingCat.of R) :=
  (nativeConstantIdeal J).subschemeι ≫ nativeStructureMap ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))

/-- An actual coefficient map with its whole actual ideal-image identity
constructs the genuine parameter map between the prescribed original closed families. -/
def nativeClosedParameterMapOfIdealMap
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (K : HomogeneousIdeal (ProjectiveGrading S n)) (f : R →+* S)
    (h : J.map (coefficientGradedMap f) = K) (u : Sˣ) :
    (nativeConstantIdeal K).subscheme ⟶ (nativeConstantIdeal J).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ (nativeParameterFamilyMap f u)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr (by
      rw [nativeConstantIdeal_comap_parameterFamily, h]))

/-- The entire prescribed closed-family map has its exact ambient triangle. -/
@[reassoc]
theorem nativeClosedParameterMapOfIdealMap_ι
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (K : HomogeneousIdeal (ProjectiveGrading S n)) (f : R →+* S)
    (h : J.map (coefficientGradedMap f) = K) (u : Sˣ) :
    nativeClosedParameterMapOfIdealMap J K f h u ≫ (nativeConstantIdeal J).subschemeι =
      (nativeConstantIdeal K).subschemeι ≫ nativeParameterFamilyMap f u := by
  apply Scheme.IdealSheafData.subschemeMap_subschemeι

/-- The actual entire prescribed closed-family morphism has its true original
coefficient-base triangle. -/
@[reassoc]
theorem nativeClosedParameterMapOfIdealMap_base
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (K : HomogeneousIdeal (ProjectiveGrading S n)) (f : R →+* S)
    (h : J.map (coefficientGradedMap f) = K) (u : Sˣ) :
    nativeClosedParameterMapOfIdealMap J K f h u ≫ nativeClosedBaseStructure J =
      nativeClosedBaseStructure K ≫ Spec.map (CommRingCat.ofHom f) := by
  have hc : (parameterUnitBaseChangeHom f u).comp Polynomial.C = Polynomial.C.comp f := by
    apply RingHom.ext
    intro r
    exact parameterUnitBaseChangeHom_C f u r
  dsimp only [nativeClosedBaseStructure]
  rw [nativeClosedParameterMapOfIdealMap_ι_assoc]
  unfold nativeParameterFamilyMap
  rw [← Category.assoc (nativeCoefficientMap (n := n) (parameterUnitBaseChangeHom f u))
      nativeStructureMap _, nativeCoefficientMap_over_base, Category.assoc, ← Spec.map_comp]
  change _ ≫ nativeStructureMap ≫ Spec.map (CommRingCat.ofHom
      ((parameterUnitBaseChangeHom f u).comp Polynomial.C)) = _
  rw [hc]
  change _ ≫ nativeStructureMap ≫
    (Spec.map (CommRingCat.ofHom f ≫ CommRingCat.ofHom Polynomial.C)) = _
  simp only [Spec.map_comp, Category.assoc]

/-- For the very actual coefficient-image ideal this is exactly the original
family morphism; no family-comparison certificate is needed. -/
theorem nativeClosedParameterMapOfIdealMap_eq_family
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (f : R →+* S) (u : Sˣ) :
    nativeClosedParameterMapOfIdealMap J (J.map (coefficientGradedMap f)) f rfl u =
      nativeClosedParameterFamilyMap J f u := rfl

/-- The actual prescribed original closed-family identity law. -/
theorem nativeClosedParameterMapOfIdealMap_id
    (J : HomogeneousIdeal (ProjectiveGrading R n)) :
    nativeClosedParameterMapOfIdealMap J J (RingHom.id R)
      (homogeneousIdeal_coefficient_map_id J) 1 = 𝟙 _ := by
  apply (cancel_mono (nativeConstantIdeal J).subschemeι).mp
  rw [nativeClosedParameterMapOfIdealMap_ι, nativeParameterFamilyMap_id,
    Category.comp_id, Category.id_comp]

/-- Entire prescribed closed-family maps compose by the genuine unit product. -/
theorem nativeClosedParameterMapOfIdealMap_comp
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (K : HomogeneousIdeal (ProjectiveGrading S n))
    (L : HomogeneousIdeal (ProjectiveGrading T n))
    (f : R →+* S) (g : S →+* T)
    (hf : J.map (coefficientGradedMap f) = K)
    (hg : K.map (coefficientGradedMap g) = L) (u : Sˣ) (v : Tˣ) :
    nativeClosedParameterMapOfIdealMap J L (g.comp f)
        (by rw [← homogeneousIdeal_coefficient_map_map, hf, hg])
        (v * Units.map g.toMonoidHom u) =
      nativeClosedParameterMapOfIdealMap K L g hg v ≫
        nativeClosedParameterMapOfIdealMap J K f hf u := by
  apply (cancel_mono (nativeConstantIdeal J).subschemeι).mp
  simp only [Category.assoc, nativeClosedParameterMapOfIdealMap_ι,
    nativeClosedParameterMapOfIdealMap_ι_assoc, nativeParameterFamilyMap_comp]

end EnvelopeProperty.ProjBerk
