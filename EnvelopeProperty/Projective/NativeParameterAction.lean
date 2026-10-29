/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealParameterScaling
import EnvelopeProperty.Projective.IdealBaseChange

/-!
# Genuine native scheme maps of parameter substitutions

Coefficient functoriality gives actual whole scheme automorphisms from unit
parameter substitutions over any coefficient ring.  These are intermediate
producers toward the Laurent-family algebraic multiplicative-group action.
-/

open scoped Classical Polynomial
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {Y Z : Scheme.{u}}

/-- An actual scheme isomorphism identifying the whole ideals induces the
actual isomorphism of their closed subschemes. -/
def subschemeIsoOfComap (I : Y.IdealSheafData) (J : Z.IdealSheafData)
    (e : Y ≅ Z) (h : J.comap e.hom = I) : I.subscheme ≅ J.subscheme := by
  have hi : I.comap e.inv = J := by
    rw [← h, ← comap_comp, e.inv_hom_id, comap_id]
  exact {
    hom := I.subschemeMap J e.hom (le_map_iff_comap_le.mpr h.le)
    inv := J.subschemeMap I e.inv (le_map_iff_comap_le.mpr hi.le)
    hom_inv_id := by
      apply (cancel_mono I.subschemeι).mp
      rw [Category.assoc, subschemeMap_subschemeι, ← Category.assoc,
        subschemeMap_subschemeι, Category.assoc, e.hom_inv_id,
        Category.comp_id, Category.id_comp]
    inv_hom_id := by
      apply (cancel_mono J.subschemeι).mp
      rw [Category.assoc, subschemeMap_subschemeι, ← Category.assoc,
        subschemeMap_subschemeι, Category.assoc, e.inv_hom_id,
        Category.comp_id, Category.id_comp] }

/-- The induced actual closed-subscheme isomorphism has its original ambient
isomorphism as the exact inclusion triangle. -/
@[reassoc]
theorem subschemeIsoOfComap_hom_ι (I : Y.IdealSheafData) (J : Z.IdealSheafData)
    (e : Y ≅ Z) (h : J.comap e.hom = I) :
    (I.subschemeIsoOfComap J e h).hom ≫ J.subschemeι = I.subschemeι ≫ e.hom :=
  subschemeMap_subschemeι I J e.hom (le_map_iff_comap_le.mpr h.le)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace EnvelopeProperty
variable {R : Type u} [CommRing R]

/-- The actual coefficient polynomial automorphism t ↦ u t. -/
def parameterScaleEquiv (u : Rˣ) : R[X] ≃+* R[X] where
  __ := parameterScaleHom (u : R)
  invFun := parameterScaleHom (↑u⁻¹ : R)
  left_inv p := by
    change ((parameterScaleHom (↑u⁻¹ : R)).comp (parameterScaleHom (u : R))) p = p
    rw [parameterScaleHom_comp, Units.inv_mul, parameterScaleHom_one]
    rfl
  right_inv p := by
    change ((parameterScaleHom (u : R)).comp (parameterScaleHom (↑u⁻¹ : R))) p = p
    rw [parameterScaleHom_comp, Units.mul_inv, parameterScaleHom_one]
    rfl

namespace ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {S T : Type u} [CommRing S] [CommRing T] {n : ℕ}

/-- Genuine native coefficient morphisms compose contravariantly on the whole
actual projective schemes. -/
theorem nativeCoefficientMap_comp (φ : R →+* S) (ψ : S →+* T) :
    nativeCoefficientMap (n := n) (ψ.comp φ) =
      nativeCoefficientMap ψ ≫ nativeCoefficientMap φ := by
  have h : coefficientGradedMap (n := n) (ψ.comp φ) =
      (coefficientGradedMap ψ).comp (coefficientGradedMap φ) := by
    apply GradedRingHom.ext
    intro F
    exact (MvPolynomial.map_map φ ψ F).symm
  change Proj.map _ _ = Proj.map _ _ ≫ Proj.map _ _
  simpa only [h] using Proj.map_comp (coefficientGradedMap φ) (coefficientGradedMap ψ)
    (coefficientGradedMap_irrelevant_le φ) (coefficientGradedMap_irrelevant_le ψ)

/-- The identity coefficient map is the identity of the actual projective scheme. -/
theorem nativeCoefficientMap_id :
    nativeCoefficientMap (n := n) (RingHom.id R) = 𝟙 (NativeProjectiveScheme R n) := by
  have h : coefficientGradedMap (n := n) (RingHom.id R) =
      GradedRingHom.id (ProjectiveGrading R n) := by
    apply GradedRingHom.ext
    intro F
    exact MvPolynomial.map_id F
  change Proj.map _ _ = 𝟙 _
  simpa only [h] using Proj.map_id (𝒜 := ProjectiveGrading R n)

/-- An actual coefficient-ring isomorphism induces the actual contravariant
native projective-scheme isomorphism. -/
def nativeCoefficientIso (e : R ≃+* S) :
    NativeProjectiveScheme S n ≅ NativeProjectiveScheme R n where
  hom := nativeCoefficientMap e.toRingHom
  inv := nativeCoefficientMap e.symm.toRingHom
  hom_inv_id := by
    rw [← nativeCoefficientMap_comp]
    have h : e.toRingHom.comp e.symm.toRingHom = RingHom.id S := by
      ext r
      exact e.apply_symm_apply r
    rw [h, nativeCoefficientMap_id]
  inv_hom_id := by
    rw [← nativeCoefficientMap_comp]
    have h : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
      ext r
      exact e.symm_apply_apply r
    rw [h, nativeCoefficientMap_id]

/-- The genuine whole polynomial-Proj parameter-unit automorphism. -/
def nativeParameterScaleIso (u : Rˣ) :
    NativeProjectiveScheme R[X] n ≅ NativeProjectiveScheme R[X] n :=
  nativeCoefficientIso (parameterScaleEquiv u)

/-- Whole original homogeneous-ideal invariance gives equality of the actual
native ideal sheaves under the genuine parameter-scaling scheme map. -/
theorem nativeHomogeneousIdealSheaf_comap_parameterScale
    (J : HomogeneousIdeal (ProjectiveGrading R[X] n)) (u : Rˣ)
    (hJ : J.toIdeal.map (MvPolynomial.map (parameterScaleHom (u : R))) = J.toIdeal) :
    (nativeHomogeneousIdealSheaf J).comap (nativeParameterScaleIso (n := n) u).hom =
      nativeHomogeneousIdealSheaf J := by
  change (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R[X] n) J).comap
    (nativeCoefficientMap (parameterScaleHom (u : R))) = _
  rw [homogeneousQuotientIdealSheaf_comap_coefficientMap]
  congr 1
  apply HomogeneousIdeal.toIdeal_injective
  exact hJ

/-- The whole genuine ideal sheaf of every base homogeneous ideal extended by
the parameter is fixed by actual parameter-unit scaling. -/
theorem nativeConstantIdeal_comap_parameterScale
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (u : Rˣ) :
    (nativeHomogeneousIdealSheaf (J.map (coefficientGradedMap Polynomial.C))).comap
      (nativeParameterScaleIso (n := n) u).hom =
      nativeHomogeneousIdealSheaf (J.map (coefficientGradedMap Polynomial.C)) := by
  apply nativeHomogeneousIdealSheaf_comap_parameterScale
  change (J.toIdeal.map (MvPolynomial.map Polynomial.C)).map
    (MvPolynomial.map (parameterScaleHom (u : R))) =
      J.toIdeal.map (MvPolynomial.map Polynomial.C)
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro F
  exact parameterScale_map_base (u : R) F

/-- The actual parameter-unit automorphism of the genuine native closed
polynomial family of an arbitrary original homogeneous base ideal. -/
def nativeClosedParameterScaleIso (J : HomogeneousIdeal (ProjectiveGrading R n)) (u : Rˣ) :
    (nativeHomogeneousIdealSheaf (J.map (coefficientGradedMap Polynomial.C))).subscheme ≅
      (nativeHomogeneousIdealSheaf (J.map (coefficientGradedMap Polynomial.C))).subscheme :=
  Scheme.IdealSheafData.subschemeIsoOfComap _ _ (nativeParameterScaleIso u)
    (nativeConstantIdeal_comap_parameterScale J u)

/-- The actual closed-family parameter automorphism preserves the original
native inclusion triangle. -/
@[reassoc]
theorem nativeClosedParameterScaleIso_hom_ι
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (u : Rˣ) :
    (nativeClosedParameterScaleIso J u).hom ≫
        (nativeHomogeneousIdealSheaf (J.map (coefficientGradedMap Polynomial.C))).subschemeι =
      (nativeHomogeneousIdealSheaf (J.map (coefficientGradedMap Polynomial.C))).subschemeι ≫
        (nativeParameterScaleIso (n := n) u).hom :=
  Scheme.IdealSheafData.subschemeIsoOfComap_hom_ι _ _ _ _

end ProjBerk
end EnvelopeProperty
