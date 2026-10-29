import EnvelopeProperty.AlgGeom.PrimitiveMonogenicSubalgebra
import EnvelopeProperty.AlgGeom.SeparableGoodLocus

/-!
# The actual monogenic birational presentation on a constructed good locus

The primitive singleton adjoin is presented by its actual minimal polynomial.
Transporting its constructed common open through this quotient presentation
retains every original coefficient and the prescribed actual generator.
-/

open scoped Polynomial Classical
noncomputable section

namespace EnvelopeProperty.FcMonogenicBirationalPresentation

open FcPrimitiveMonogenicSubalgebra

theorem exists_minpoly_presentation_commonOpen
    (R A K L : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra A L] [IsFractionRing A L] [Algebra R L] [Algebra K L]
    [IsScalarTower R A L] [IsScalarTower R K L]
    (b : A) (hprim : IntermediateField.adjoin K {algebraMap A L b} = ⊤) :
    let P := minpoly R b
    ∃ δ : AdjoinRoot P →ₐ[R] A, P.Monic ∧ Irreducible P ∧ Function.Injective δ ∧
      δ (AdjoinRoot.root P) = b ∧
      ∃ (h : AdjoinRoot P) (g : R), h ≠ 0 ∧ g ≠ 0 ∧ h ∣ algebraMap R (AdjoinRoot P) g ∧
        ∃ e : Localization.Away h ≃+* Localization.Away (δ h),
          ∀ c : AdjoinRoot P, e (algebraMap _ (Localization.Away h) c) =
            algebraMap A (Localization.Away (δ h)) (δ c) := by
  let P := minpoly R b
  let C := Algebra.adjoin R ({b} : Set A)
  obtain ⟨hPm, hPi, eP, hb⟩ := monic_irreducible_minpoly_presentation R A b
  let δ : AdjoinRoot P →ₐ[R] A := C.val.comp eP.toAlgHom
  have hiδ : Function.Injective δ := Subtype.val_injective.comp eP.injective
  have hδb : δ (AdjoinRoot.root P) = b := hb
  obtain ⟨hC, g, hhC, hg, hdiv, eC, heC⟩ :=
    exists_commonOpen_of_primitive_adjoin R A K L b hprim
  obtain ⟨h, rfl⟩ := eP.surjective hC
  have hh : h ≠ 0 := by
    intro hz
    apply hhC
    rw [hz, map_zero]
  have hdiv' : h ∣ algebraMap R (AdjoinRoot P) g := by
    obtain ⟨q, hq⟩ := hdiv
    refine ⟨eP.symm q, ?_⟩
    apply eP.injective
    rw [eP.commutes, map_mul, eP.apply_symm_apply]
    exact hq
  have H : (Submonoid.powers h).map eP.toRingEquiv.toMonoidHom =
      Submonoid.powers (eP h) := by
    rw [Submonoid.map_powers]
    rfl
  let eLoc : Localization.Away h ≃+* Localization.Away (eP h) :=
    IsLocalization.ringEquivOfRingEquiv _ _ eP.toRingEquiv H
  let e : Localization.Away h ≃+* Localization.Away (δ h) := eLoc.trans eC
  refine ⟨δ, hPm, hPi, hiδ, hδb, h, g, hh, hg, hdiv', e, ?_⟩
  intro c
  change eC (eLoc (algebraMap (AdjoinRoot P) (Localization.Away h) c)) =
    algebraMap A (Localization.Away (δ h)) (δ c)
  rw [show eLoc (algebraMap (AdjoinRoot P) (Localization.Away h) c) =
      algebraMap C (Localization.Away (eP h)) (eP c) from
        IsLocalization.ringEquivOfRingEquiv_eq
          (S := Localization.Away h) (Q := Localization.Away (eP h)) H c]
  exact heC (eP c)

/-- The actual minimal-polynomial presentation and its whole common open share
one constructed nonzero base locus on which every specialized polynomial is
separable. No presentation, common-open isomorphism, or good locus is supplied. -/
theorem exists_minpoly_presentation_goodLocus
    (R A K L : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra A L] [IsFractionRing A L] [Algebra R L] [Algebra K L]
    [IsScalarTower R A L] [IsScalarTower R K L] [Algebra.FormallyEtale K L]
    (b : A) (hprim : IntermediateField.adjoin K {algebraMap A L b} = ⊤) :
    let P := minpoly R b
    ∃ δ : AdjoinRoot P →ₐ[R] A, P.Monic ∧ Irreducible P ∧ Function.Injective δ ∧
      δ (AdjoinRoot.root P) = b ∧
      ∃ (h : AdjoinRoot P) (g : R), h ≠ 0 ∧ g ≠ 0 ∧ h ∣ algebraMap R (AdjoinRoot P) g ∧
        ∃ e : Localization.Away h ≃+* Localization.Away (δ h),
          (∀ c : AdjoinRoot P, e (algebraMap _ (Localization.Away h) c) =
            algebraMap A (Localization.Away (δ h)) (δ c)) ∧
          ∀ (E : Type*) [Field E] (w : R →+* E), w g ≠ 0 → (P.map w).Separable := by
  let P := minpoly R b
  obtain ⟨δ, hPm, hPi, hiδ, hδb, h, g₀, hh, hg₀, hdiv, e, he⟩ :=
    exists_minpoly_presentation_commonOpen R A K L b hprim
  have : Algebra.EssFiniteType A L := .of_isLocalization L (nonZeroDivisors A)
  have : Algebra.EssFiniteType R L := .comp R A L
  have : Algebra.EssFiniteType K L := .of_comp R K L
  have : Algebra.IsSeparable K L := Algebra.FormallyUnramified.isSeparable K L
  have hmin := minpoly.isIntegrallyClosed_eq_field_fractions K L
    (Algebra.IsIntegral.isIntegral b : IsIntegral R b)
  have hsep : (P.map (algebraMap R K)).Separable := by
    rw [← hmin]
    exact Algebra.IsSeparable.isSeparable K _
  obtain ⟨g₁, hg₁, hgood⟩ := FcSeparableGoodLocus.exists_separable_principal_locus P hsep
  have hdiv' : h ∣ algebraMap R (AdjoinRoot P) (g₀ * g₁) := by
    obtain ⟨c, hc⟩ := hdiv
    refine ⟨c * algebraMap R (AdjoinRoot P) g₁, ?_⟩
    rw [map_mul, hc, mul_assoc]
  refine ⟨δ, hPm, hPi, hiδ, hδb, h, g₀ * g₁, hh, mul_ne_zero hg₀ hg₁, hdiv', e, he, ?_⟩
  intro E _ w hw
  apply hgood E w
  intro hz
  apply hw
  rw [map_mul, hz, mul_zero]

/-- Every original finite-type domain over a perfect field has an ACTUAL global
finite normalization, monic irreducible polynomial, map from its genuine quotient,
and common principal open over one constructed nonzero separable base locus.
All presentation and good-locus data are conclusions. -/
theorem exists_global_monic_presentation_goodLocus
    (F A : Type*) [Field F] [PerfectField F] [CommRing A] [IsDomain A]
    [Algebra F A] [Algebra.FiniteType F A] :
    ∃ (n : ℕ) (φ : MvPolynomial (Fin n) F →ₐ[F] A)
      (P : (MvPolynomial (Fin n) F)[X]) (δ : AdjoinRoot P →ₐ[F] A)
      (h : AdjoinRoot P) (g : MvPolynomial (Fin n) F),
      Function.Injective φ ∧ φ.toRingHom.Finite ∧ P.Monic ∧ Irreducible P ∧
      Function.Injective δ ∧ δ.comp (AdjoinRoot.ofAlgHom F P) = φ ∧
      h ≠ 0 ∧ g ≠ 0 ∧ h ∣ algebraMap _ (AdjoinRoot P) g ∧
      ∃ e : Localization.Away h ≃ₐ[F] Localization.Away (δ h),
        (∀ c : AdjoinRoot P, e (algebraMap _ (Localization.Away h) c) =
          algebraMap A (Localization.Away (δ h)) (δ c)) ∧
        ∀ w : MvPolynomial (Fin n) F →ₐ[F] F, w g ≠ 0 → (P.map w.toRingHom).Separable := by
  obtain ⟨n, φ, ψ, b, hiφ, hfin, _het, hcompat, hsep, hprim⟩ :=
    FcPrimitiveIntegralGenerator.exists_global_normalization_with_integral_primitive_element F A
  let R := MvPolynomial (Fin n) F
  let K := FractionRing R
  let L := FractionRing A
  let : Algebra R A := φ.toRingHom.toAlgebra
  have : Module.Finite R A := hfin
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hiφ
  have : IsScalarTower F R A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have : IsScalarTower R A L := inferInstance
  let : Algebra K L := ψ.toAlgebra
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun p => by
    rw [IsScalarTower.algebraMap_apply R A L]
    exact (hcompat p).symm
  have : Algebra.FormallyEtale K L := hsep
  let P := minpoly R b
  obtain ⟨δR, hPm, hPi, hiδR, _hroot, h, g, hh, hg, hdiv, eRing, heRing, hgood⟩ :=
    exists_minpoly_presentation_goodLocus R A K L b hprim
  let δ : AdjoinRoot P →ₐ[F] A := δR.restrictScalars F
  have hδcomp : δ.comp (AdjoinRoot.ofAlgHom F P) = φ := by
    apply AlgHom.ext
    intro r
    exact δR.commutes r
  let e := commonOpenAlgEquiv_of_ringEquiv δ h eRing heRing
  refine ⟨n, φ, P, δ, h, g, hiφ, hfin, hPm, hPi, hiδR, hδcomp, hh, hg, hdiv, e, ?_, ?_⟩
  · exact heRing
  · intro w hw
    exact hgood F w.toRingHom hw

end EnvelopeProperty.FcMonogenicBirationalPresentation
