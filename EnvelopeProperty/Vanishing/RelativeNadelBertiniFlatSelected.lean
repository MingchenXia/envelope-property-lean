import EnvelopeProperty.Vanishing.RelativeNadelBertiniGenericOpen
import EnvelopeProperty.Vanishing.NadelBertiniSncFlatSelected

/-! # Actual selected Cartier equations in a nonproper family

Only the genuine coefficient good open is used.  Localized quotient
flatness follows from actual smoothness on that open, so no properness
of the parameter map enters the original selected-equation argument.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct
universe u
namespace EnvelopeProperty.Vanishing.RelativeNadelBertiniFlatSelected
open NadelBertiniSncFlatAffine NadelBertiniSncFlatBaseChange NadelBertiniSncFlatFibre
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B]

/-- The actual incidence quotient is flat on any original principal
parameter neighbourhood contained in the nonproper smooth good open. -/
theorem localizedQuotient_flat_of_goodOpen {Y : Scheme.{u}}
    (F : Y ⟶ Spec (.of A)) [LocallyOfFinitePresentation F]
    (h : B) (ν : Spec (.of (B ⧸ Ideal.span {h})) ⟶ Y) [IsOpenImmersion ν]
    (hν : ν ≫ F = quotientStructure A h) (g : A)
    (hg : PrimeSpectrum.basicOpen g ≤ RelativeNadelBertiniGenericOpen.goodOpen F) :
    Module.Flat (Localization.Away g) (localizedQuotient A g h) := by
  have hfp : LocallyOfFinitePresentation (quotientStructure A h) :=
    hν ▸ (inferInstanceAs (LocallyOfFinitePresentation (ν ≫ F)))
  have hpre : (quotientStructure A h) ⁻¹ᵁ PrimeSpectrum.basicOpen g ≤
      (quotientStructure A h).smoothLocus := by
    intro x hx
    have hxF : F (ν x) ∈ RelativeNadelBertiniGenericOpen.goodOpen F := by
      have he := congrArg (fun f => f x) hν
      change F (ν x) = quotientStructure A h x at he
      rw [he]
      exact hg hx
    have hloc : ν x ∈ F.smoothLocus :=
      RelativeNadelBertiniGenericOpen.goodOpen_preimage_le F hxF
    have he : ν ⁻¹ᵁ F.smoothLocus = (quotientStructure A h).smoothLocus := by
      simpa only [hν] using Scheme.Hom.preimage_smoothLocus_eq ν F
    rw [← he]
    exact hloc
  let : Smooth ((quotientStructure A h) ∣_ PrimeSpectrum.basicOpen g) :=
    NadelBertiniGenericOpen.smooth_morphismRestrict_of_preimage_le_smoothLocus _ _ hpre
  exact localizedQuotient_flat_of_smooth_basicOpen A g h

/-- The actual good parameter internally supplies localized quotient
flatness and regularity of the SAME original equation in its whole fibre. -/
theorem tensor_regular_of_goodOpen {Y : Scheme.{u}} {K : Type u} [Field K]
    (F : Y ⟶ Spec (.of A)) [LocallyOfFinitePresentation F]
    (h : B) (hh : IsSMulRegular B h)
    (ν : Spec (.of (B ⧸ Ideal.span {h})) ⟶ Y) [IsOpenImmersion ν]
    (hν : ν ≫ F = quotientStructure A h) (φ : A →+* K)
    (hφ : Spec.map (CommRingCat.ofHom φ) (⊥ : PrimeSpectrum K) ∈
      RelativeNadelBertiniGenericOpen.goodOpen F) :
    letI : Algebra A K := φ.toAlgebra
    IsSMulRegular (K ⊗[A] B) ((1 : K) ⊗ₜ[A] h) := by
  obtain ⟨g, hg, hsub⟩ := exists_unit_basicOpen_neighbourhood A φ _ hφ
  let : Module.Flat (Localization.Away g) (localizedQuotient A g h) :=
    localizedQuotient_flat_of_goodOpen A F h ν hν g hsub
  exact tensor_regular_of_localized_flat A g h hh φ hg

/-- The whole original selected local coefficient is a nonzerodivisor,
proved from the actual universal quotient chart and its original parameter
triangle.  The family need not be proper over the original field. -/
theorem selectedEquation_regular_of_goodOpen
    {k C : Type u} [Field k] [CommRing C] [Algebra k C]
    {S : Type} [Fintype S] [DecidableEq S] {Y : Scheme.{u}}
    (F : Y ⟶ Spec (.of (MvPolynomial S k))) [LocallyOfFinitePresentation F]
    (c : S → C) (j : S) (hj : c j = 1) (a : S → k)
    (ν : Spec (.of (MvPolynomial S C ⧸ Ideal.span
      {NadelBertiniLinearSmooth.linearForm c})) ⟶ Y) [IsOpenImmersion ν]
    (hν : ν ≫ F = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {NadelBertiniLinearSmooth.linearForm c})).comp
        (NadelBertiniSncFlatPolynomial.coefficientMap (k := k) (C := C)))))
    (ha : Spec.map (CommRingCat.ofHom (MvPolynomial.eval a)) (⊥ : PrimeSpectrum k) ∈
      RelativeNadelBertiniGenericOpen.goodOpen F) :
    IsSMulRegular C (∑ i, algebraMap k C (a i) * c i) := by
  let : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
    (NadelBertiniSncFlatPolynomial.coefficientMap (k := k) (C := C)).toAlgebra
  let : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
  have hν' : ν ≫ F = quotientStructure (MvPolynomial S k)
      (NadelBertiniLinearSmooth.linearForm c) := hν
  have hreg : IsSMulRegular (k ⊗[MvPolynomial S k] MvPolynomial S C)
      ((1 : k) ⊗ₜ[MvPolynomial S k] NadelBertiniLinearSmooth.linearForm c) :=
    tensor_regular_of_goodOpen (MvPolynomial S k) F
      (NadelBertiniLinearSmooth.linearForm c)
      (NadelBertiniSncLinearRegular.linearForm_regular c j hj) ν hν'
      (MvPolynomial.eval a) ha
  let e := NadelBertiniSncFlatPolynomial.fibreEvaluationIso (C := C) a
  have he : e ((1 : k) ⊗ₜ[MvPolynomial S k] NadelBertiniLinearSmooth.linearForm c) =
      ∑ i, algebraMap k C (a i) * c i :=
    NadelBertiniSncFlatPolynomial.fibreEvaluationIso_linearForm a c
  change Function.Injective (fun z : C => (∑ i, algebraMap k C (a i) * c i) * z)
  intro z z' hzz'
  apply e.symm.injective
  apply hreg
  apply e.injective
  simpa only [smul_eq_mul, map_mul, he, e.apply_symm_apply] using hzz'

end EnvelopeProperty.Vanishing.RelativeNadelBertiniFlatSelected
