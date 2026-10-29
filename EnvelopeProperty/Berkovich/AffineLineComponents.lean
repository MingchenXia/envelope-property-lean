/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AffineDimension
import EnvelopeProperty.Berkovich.AffineLineEquations
import EnvelopeProperty.Berkovich.OpenAffineLine
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Genuine domination of actual affine-line inverse-image components

The original transverse equations describe the actual open-line inverse image.
For an actual finite injective homomorphism from a nonempty polynomial
principal open to a domain, each actual minimal prime of their entire image
has a constructed whole finite injective line algebra homomorphism. Its true
quotient dimension is one and the actual scheme map is finite and surjective.
Every original localized coefficient and the whole scheme square is preserved.

Ambient domain is explicit. Domain preservation under field scalar extension,
finite normalization and its smoothness or flatness are separate producers;
no desired component, normalization or curve-potential witness is an input.
No infinite/algebraically closed field or characteristic assumption is used.
-/

open CategoryTheory
open scoped Classical Polynomial AlgebraicGeometry
noncomputable section
namespace EnvelopeProperty.AffineLine
variable {F σ : Type*} [Field F]

/-- The original dimension of any actual finite faithful domain algebra over a nonempty polynomial principal open is exactly its coordinate count. -/
theorem ringKrullDim_finite_over_principalOpen [Fintype σ]
    (g : MvPolynomial σ F) (hg : g ≠ 0)
    (B : Type*) [CommRing B] [IsDomain B] [Algebra F B]
    [Algebra (Localization.Away g) B] [IsScalarTower F (Localization.Away g) B]
    [Module.Finite (Localization.Away g) B] [FaithfulSMul (Localization.Away g) B] :
    ringKrullDim B = (Fintype.card σ : ℕ) := by
  let R := Localization.Away g
  have : IsDomain R := IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := Submonoid.powers g) R
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hg))
  have : Algebra.FinitePresentation (MvPolynomial σ F) R :=
    IsLocalization.Away.finitePresentation g
  have : Algebra.FiniteType F R := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F (MvPolynomial σ F))
    (inferInstance : Algebra.FiniteType (MvPolynomial σ F) R)
  have : Algebra.FiniteType F B := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F R) (inferInstance : Algebra.FiniteType R B)
  have : IsIntegrallyClosed R := isIntegrallyClosed_of_isLocalization
    (S := R) (Submonoid.powers g)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hg))
  rw [ringKrullDim_eq_of_normal_integral_finiteType_domain F R B,
    ringKrullDim_localizationAway_of_finiteType_domain F (MvPolynomial σ F) g hg,
    MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp only [ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card]

/-- Every actual minimal component of a transverse-line inverse image in a sufficiently dimensional affine domain is genuinely positive-dimensional. -/
theorem positive_dim_quotient_of_minimalPrime_lineIdeal [Fintype σ]
    (a b : σ → F) (j : σ) {B : Type*} [CommRing B] [IsDomain B]
    [Algebra F B] [Algebra.FiniteType F B]
    (φ : MvPolynomial σ F →+* B) (P : Ideal B)
    (hP : P ∈ ((lineIdeal a b j).map φ).minimalPrimes)
    (hB : (Fintype.card σ : ℕ) ≤ ringKrullDim B) :
    0 < ringKrullDim (B ⧸ P) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing F B
  have : P.IsPrime := hP.isPrime
  apply positive_dim_quotient_of_height_lt_of_finiteType_domain F B P
  have hh := height_map_lineIdeal_le a b j φ P hP
  have hc : Fintype.card σ - 1 < Fintype.card σ :=
    Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨j⟩) (by decide)
  have hh' : (P.height : WithBot ℕ∞) ≤ (Fintype.card σ - 1 : ℕ) := by
    simpa only [WithBot.coe_natCast] using (WithBot.coe_le_coe.mpr hh)
  have hc' : ((Fintype.card σ - 1 : ℕ) : WithBot ℕ∞) < (Fintype.card σ : ℕ) := by
    exact_mod_cast hc
  exact lt_of_le_of_lt hh' (lt_of_lt_of_le hc' hB)

/-- The genuine localized line-map kernel is the localization of the original transverse equation ideal. -/
theorem ker_principalLineHom (a b : σ → F) (j : σ) (g : MvPolynomial σ F)
    (hb : b j ≠ 0) :
    RingHom.ker (principalLineHom a b g).toRingHom =
      (lineIdeal a b j).map (algebraMap _ (Localization.Away g)) := by
  have hk := IsLocalization.ker_map (S := Localization.Away g)
    (OpenLineRing (subst a b g)) (subst a b).toRingHom
    (Submonoid.map_powers (subst a b).toRingHom g)
  rw [ker_subst_eq_lineIdeal a b j hb] at hk
  simpa only [principalLineHom, IsLocalization.Away.mapₐ, IsLocalization.Away.map] using hk

/-- The actual line inverse-image support is exactly the zero locus of the original entire transverse-equation image. -/
theorem principalLine_preimage_range (a b : σ → F) (j : σ) (g : MvPolynomial σ F)
    (hb : b j ≠ 0) {B : Type*} [CommRing B] [Algebra F B]
    (φ : Localization.Away g →ₐ[F] B) :
    PrimeSpectrum.comap φ.toRingHom ⁻¹'
        Set.range (PrimeSpectrum.comap (principalLineHom a b g).toRingHom) =
      PrimeSpectrum.zeroLocus ((lineIdeal a b j).map
        (φ.toRingHom.comp (algebraMap _ (Localization.Away g)))) := by
  rw [range_comap_of_surjective _ _
    (principalLineHom_surjective a b g (by intro hz; exact hb (congrFun hz j)))]
  ext x
  change RingHom.ker (principalLineHom a b g).toRingHom ≤ x.asIdeal.comap φ.toRingHom ↔ _
  rw [ker_principalLineHom a b j g hb, ← Ideal.map_le_iff_le_comap, Ideal.map_map]
  rfl

section Component
variable (a b : σ → F) (j : σ) (g : MvPolynomial σ F) (hb : b j ≠ 0)
variable {B : Type*} [CommRing B] [Algebra F B]
variable (φ : Localization.Away g →ₐ[F] B) (P : Ideal B)
variable (hP : P ∈ ((lineIdeal a b j).map
  (φ.toRingHom.comp (algebraMap _ (Localization.Away g)))).minimalPrimes)

include hb hP in
/-- The entire localized line ideal maps to zero in the actual original component quotient. -/
theorem componentLine_ker_le :
    RingHom.ker (principalLineHom a b g).toRingHom ≤
      RingHom.ker ((Ideal.Quotient.mkₐ F P).comp φ).toRingHom := by
  rw [ker_principalLineHom a b j g hb]
  change (lineIdeal a b j).map (algebraMap _ (Localization.Away g)) ≤
    RingHom.ker ((Ideal.Quotient.mk P).comp φ.toRingHom)
  rw [← RingHom.comap_ker, Ideal.mk_ker]
  have hle := hP.1.2
  rw [← Ideal.map_map] at hle
  exact Ideal.map_le_iff_le_comap.mp hle

/-- The actual whole open-line homomorphism to an original minimal component quotient. -/
def componentLineHom : OpenLineRing (subst a b g) →ₐ[F] (B ⧸ P) :=
  AlgHom.liftOfSurjective (principalLineHom a b g)
    (principalLineHom_surjective a b g (by intro hz; exact hb (congrFun hz j)))
    ((Ideal.Quotient.mkₐ F P).comp φ) (componentLine_ker_le a b j g hb φ P hP)

/-- Every original localized ambient element agrees under the entire component-line factorization. -/
theorem componentLineHom_comp :
    (componentLineHom a b j g hb φ P hP).comp (principalLineHom a b g) =
      (Ideal.Quotient.mkₐ F P).comp φ :=
  AlgHom.liftOfSurjective_comp _ _ _ _

/-- This is the whole localized coefficient diagram, with no generator-value substitute. -/
theorem componentLineHom_principalLineHom (r : Localization.Away g) :
    componentLineHom a b j g hb φ P hP (principalLineHom a b g r) =
      Ideal.Quotient.mk P (φ r) := by
  exact congrArg (fun f : Localization.Away g →ₐ[F] (B ⧸ P) => f r)
    (componentLineHom_comp a b j g hb φ P hP)

/-- The actual component-line ring map is finite whenever the original entire ambient ring map is finite. -/
theorem componentLineHom_finite (hφ : φ.toRingHom.Finite) :
    (componentLineHom a b j g hb φ P hP).toRingHom.Finite := by
  let R := Localization.Away g
  let C := OpenLineRing (subst a b g)
  let D := B ⧸ P
  let : Algebra R B := φ.toRingHom.toAlgebra
  let : Algebra R C := (principalLineHom a b g).toRingHom.toAlgebra
  let : Algebra C D := (componentLineHom a b j g hb φ P hP).toRingHom.toAlgebra
  have : Module.Finite R B := hφ
  have : IsScalarTower R C D := IsScalarTower.of_algebraMap_eq fun r =>
    (componentLineHom_principalLineHom a b j g hb φ P hP r).symm
  exact Module.Finite.of_restrictScalars_finite R C D

/-- True finite ambient dimension and actual transverse equations force the constructed component map to be injective. -/
theorem componentLineHom_injective [Fintype σ] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    Function.Injective (componentLineHom a b j g hb φ P hP) := by
  let R := Localization.Away g
  let C := OpenLineRing (subst a b g)
  let D := B ⧸ P
  let : Algebra R B := φ.toRingHom.toAlgebra
  have : IsScalarTower F R B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have : Module.Finite R B := hφ
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr hiφ
  have : P.IsPrime := hP.isPrime
  have : IsDomain C := openLineRing_isDomain _ hline
  have : IsDedekindDomain C := openLineRing_isDedekindDomain _ hline
  let : Algebra C D := (componentLineHom a b j g hb φ P hP).toRingHom.toAlgebra
  have : Module.Finite C D := componentLineHom_finite a b j g hb φ P hP hφ
  have : Algebra.FinitePresentation (MvPolynomial σ F) R :=
    IsLocalization.Away.finitePresentation g
  have : Algebra.FiniteType F R := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F (MvPolynomial σ F))
    (inferInstance : Algebra.FiniteType (MvPolynomial σ F) R)
  have : Algebra.FiniteType F B := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F R) (inferInstance : Algebra.FiniteType R B)
  apply injective_algebraMap_of_isIntegral_of_positive_dim (C := C) (D := D)
  apply positive_dim_quotient_of_minimalPrime_lineIdeal a b j _ P hP
  exact (ringKrullDim_finite_over_principalOpen g hg B).symm.le

/-- Every actual minimal component genuinely surjects onto the entire original principal-open line. -/
theorem componentLineHom_comap_surjective [Fintype σ] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    Function.Surjective (PrimeSpectrum.comap
      (componentLineHom a b j g hb φ P hP).toRingHom) := by
  let C := OpenLineRing (subst a b g)
  let D := B ⧸ P
  let : Algebra C D := (componentLineHom a b j g hb φ P hP).toRingHom.toAlgebra
  have : Module.Finite C D := componentLineHom_finite a b j g hb φ P hP hφ
  have : FaithfulSMul C D := (faithfulSMul_iff_algebraMap_injective C D).mpr
    (componentLineHom_injective a b j g hb φ P hP hg hline hφ hiφ)
  exact Algebra.IsIntegral.comap_surjective C D

include hb hP in
/-- The original minimal component really has dimension one, not merely a supplied curve witness. -/
theorem component_quotient_ringKrullDim_eq_one [Fintype σ] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    ringKrullDim (B ⧸ P) = 1 := by
  let R := Localization.Away g
  let C := OpenLineRing (subst a b g)
  let D := B ⧸ P
  let : Algebra R B := φ.toRingHom.toAlgebra
  have : IsScalarTower F R B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have : Module.Finite R B := hφ
  have : Algebra.FinitePresentation (MvPolynomial σ F) R :=
    IsLocalization.Away.finitePresentation g
  have : Algebra.FiniteType F R := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F (MvPolynomial σ F))
    (inferInstance : Algebra.FiniteType (MvPolynomial σ F) R)
  have : Algebra.FiniteType F B := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F R) (inferInstance : Algebra.FiniteType R B)
  have : P.IsPrime := hP.isPrime
  have : IsDomain C := openLineRing_isDomain _ hline
  have : IsIntegrallyClosed C := openLineRing_isIntegrallyClosed _ hline
  have : Algebra.FiniteType F C := openLineRing_finiteType _
  let : Algebra C D := (componentLineHom a b j g hb φ P hP).toRingHom.toAlgebra
  have : Module.Finite C D := componentLineHom_finite a b j g hb φ P hP hφ
  have : FaithfulSMul C D := (faithfulSMul_iff_algebraMap_injective C D).mpr
    (componentLineHom_injective a b j g hb φ P hP hg hline hφ hiφ)
  rw [ringKrullDim_eq_of_normal_integral_finiteType_domain F C D,
    ringKrullDim_localizationAway_of_finiteType_domain F F[X] _ hline,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

end Component
end EnvelopeProperty.AffineLine

universe u
namespace EnvelopeProperty.AffineLine
variable {F σ B : Type u} [Field F] [CommRing B] [Algebra F B]
variable (a b : σ → F) (j : σ) (g : MvPolynomial σ F) (hb : b j ≠ 0)
variable (φ : Localization.Away g →ₐ[F] B) (P : Ideal B)
variable (hP : P ∈ ((lineIdeal a b j).map
  (φ.toRingHom.comp (algebraMap _ (Localization.Away g)))).minimalPrimes)

/-- The actual morphism from the original minimal component scheme to the original open line. -/
def componentLineSchemeMap :
    AlgebraicGeometry.Spec (CommRingCat.of (B ⧸ P)) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of (OpenLineRing (subst a b g))) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    (componentLineHom a b j g hb φ P hP).toRingHom)

/-- Genuine ring finiteness supplies finiteness of the actual component scheme morphism. -/
theorem componentLineSchemeMap_isFinite (hφ : φ.toRingHom.Finite) :
    AlgebraicGeometry.IsFinite (componentLineSchemeMap a b j g hb φ P hP) := by
  apply (AlgebraicGeometry.IsFinite.SpecMap_iff _).mpr
  exact componentLineHom_finite a b j g hb φ P hP hφ

/-- Every actual minimal component maps onto the entire open-line scheme. -/
theorem componentLineSchemeMap_surjective [Fintype σ] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    AlgebraicGeometry.Surjective (componentLineSchemeMap a b j g hb φ P hP) := by
  constructor
  exact componentLineHom_comap_surjective a b j g hb φ P hP hg hline hφ hiφ


/-- The whole original component inclusion and ambient finite map commute with the constructed line map. -/
theorem componentLineSchemeMap_square :
    componentLineSchemeMap a b j g hb φ P hP ≫ principalLineSchemeMap a b g =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  rw [componentLineSchemeMap, principalLineSchemeMap, ← AlgebraicGeometry.Spec.map_comp,
    ← AlgebraicGeometry.Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (componentLineHom_principalLineHom a b j g hb φ P hP)

/-- The actual principal-open line square is a genuine scheme pullback, including empty-open cases. -/
theorem principalLineSchemeMap_isPullback (a b : σ → F) (g : MvPolynomial σ F) :
    CategoryTheory.IsPullback (principalLineSchemeMap a b g) (openLineInclusion (subst a b g))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away g))))
      (schemeMap a b) := by
  have : AlgebraicGeometry.IsOpenImmersion (openLineInclusion (subst a b g)) :=
    openLineInclusion_isOpenImmersion _
  apply AlgebraicGeometry.IsOpenImmersion.isPullback
  · exact (principalLineSchemeMap_square a b g).symm
  · change schemeMap a b ⁻¹ᵁ
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap _ (Localization.Away g)))).opensRange =
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap F[X] (Localization.Away (subst a b g))))).opensRange
    erw [AlgebraicGeometry.Scheme.Hom.opensRange_localizationAway
      (R := CommRingCat.of (MvPolynomial σ F)) g,
      AlgebraicGeometry.Scheme.Hom.opensRange_localizationAway
        (R := CommRingCat.of F[X]) (subst a b g)]
    ext x
    rfl

end EnvelopeProperty.AffineLine
