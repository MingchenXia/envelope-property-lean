import EnvelopeProperty.Char0.FieldTensorDomainCoverDescent
import EnvelopeProperty.Char0.FractionFieldModel
import EnvelopeProperty.Char0.ValuativeTensorOpen
import EnvelopeProperty.Char0.ComplexValuativeSubadditivity

/-! # Full intrinsic multiplier subadditivity over countable characteristic-zero fields -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace EnvelopeProperty.Char0

private theorem countable_product_ne_bot {R : Type} [CommRing R] [IsDomain R]
    (I J : Ideal R) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : I * J ≠ ⊥ := by
  intro h
  exact (not_or.mpr ⟨hI, hJ⟩) (Ideal.mul_eq_bot.mp h)

private theorem multiplierProduct_le_after_tensorOpen
    {F K M : Type} [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F ℂ] [Algebra ℂ M] [CharZero F]
    (C : Subalgebra F K) [IsFractionRing C K]
    (D : Subalgebra ℂ M) [IsFractionRing D M]
    (φ : (ℂ ⊗[F] C) →ₐ[ℂ] D)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))]
    (n : ℕ) (z : Fin n → C) (hz : (MvPolynomial.aeval (R := F) z).toRingHom.Etale)
    (I J : Ideal C) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (q : ℚ) :
    (valuativeMultiplierIdeal C (I * J) (countable_product_ne_bot I J hI hJ) q).map
        (tensorOpenCoefficientMap φ) ≤
      (valuativeMultiplierIdeal C I hI q).map (tensorOpenCoefficientMap φ) *
        (valuativeMultiplierIdeal C J hJ q).map (tensorOpenCoefficientMap φ) := by
  let B := ℂ ⊗[F] C
  let : Algebra B D := φ.toAlgebra
  let : IsScalarTower ℂ B D := IsScalarTower.of_algebraMap_eq (R := ℂ) (S := B) (A := D)
    fun a => (φ.commutes a).symm
  let zB := fieldTensorCoordinates (k := F) (L := ℂ) z
  let hzB := etale_fieldTensorCoordinates (k := F) (L := ℂ) z hz
  let zD := fun a => φ (zB a)
  let hzD := SourceOpenPushedKernel.etale_coordinates (.of B) (.of D) zB hzB
  let a := tensorOpenCoefficientMap φ
  have hID : I.map a ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (tensorOpenCoefficientMap_injective φ)).mp.mt hI
  have hJD : J.map a ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (tensorOpenCoefficientMap_injective φ)).mp.mt hJ
  have hP := valuativeMultiplierIdeal_tensorOpen C D φ z hz (I * J)
    (countable_product_ne_bot I J hI hJ) q
  have hMI := valuativeMultiplierIdeal_tensorOpen C D φ z hz I hI q
  have hMJ := valuativeMultiplierIdeal_tensorOpen C D φ z hz J hJ q
  have hcomplex := ComplexValuativeSubadditivity.valuativeMultiplierIdeal_mul_le
    D n zD hzD (I.map a) (J.map a) hID hJD q
  rw [hP, hMI, hMJ]
  simpa only [Ideal.map_mul] using hcomplex

private theorem multiplierProduct_le_after_domainOpen
    {F K R : Type} [Field F] [Field K] [CommRing R] [IsDomain R]
    [Algebra F K] [Algebra F ℂ] [Algebra ℂ R] [CharZero F]
    (C : Subalgebra F K) [IsFractionRing C K]
    (φ₀ : (ℂ ⊗[F] C) →ₐ[ℂ] R)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ₀.toRingHom))]
    (n : ℕ) (z : Fin n → C) (hz : (MvPolynomial.aeval (R := F) z).toRingHom.Etale)
    (I J : Ideal C) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (q : ℚ) :
    (valuativeMultiplierIdeal C (I * J) (countable_product_ne_bot I J hI hJ) q).map
        (tensorOpenCoefficientMap φ₀) ≤
      (valuativeMultiplierIdeal C I hI q).map (tensorOpenCoefficientMap φ₀) *
        (valuativeMultiplierIdeal C J hJ q).map (tensorOpenCoefficientMap φ₀) := by
  let B := ℂ ⊗[F] C
  let : Field (FractionRing R) := inferInstance
  let D := AffineFractionFieldModel.subalgebra ℂ R
  let e := AffineFractionFieldModel.equiv ℂ R
  let : IsDomain D := Function.Injective.isDomain e.symm.toRingHom e.symm.injective
  let : IsFractionRing D (FractionRing R) := AffineFractionFieldModel.isFractionRing ℂ R
  let φ : B →ₐ[ℂ] D := e.toAlgHom.comp φ₀
  let : IsIso (CommRingCat.ofHom e.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr e.bijective
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
    change IsOpenImmersion (Spec.map
      (CommRingCat.ofHom φ₀.toRingHom ≫ CommRingCat.ofHom e.toRingHom))
    rw [Spec.map_comp]
    infer_instance
  have hD := multiplierProduct_le_after_tensorOpen C D φ n z hz I J hI hJ q
  have hread : e.symm.toRingHom.comp (tensorOpenCoefficientMap φ) = tensorOpenCoefficientMap φ₀ := by
    ext x
    change e.symm (e (φ₀ (1 ⊗ₜ[F] x))) = φ₀ (1 ⊗ₜ[F] x)
    exact AlgEquiv.symm_apply_apply e _
  have hR := Ideal.map_mono (f := e.symm.toRingHom) hD
  simpa only [Ideal.map_mul, Ideal.map_map, hread] using hR

private theorem tensorLocalizationCoefficientMap
    {F L A : Type} [Field F] [Field L] [CommRing A] [Algebra F L] [Algebra F A]
    (g : L ⊗[F] A) :
    tensorOpenCoefficientMap (IsScalarTower.toAlgHom L (L ⊗[F] A) (Localization.Away g)) =
      SmoothAffineDomainCover.componentCoefficientMap (F := F) (L := L) (A₀ := A) g := by
  ext x
  rfl

/-- Countable characteristic-zero coefficients suffice for the FULL original all-DVR
multiplier ideal subadditivity. The actual complex tensor may split. -/
theorem valuativeMultiplierIdeal_mul_le_of_countable
    {F K : Type} [Field F] [Field K] [Algebra F K] [CharZero F] [Countable F]
    (C : Subalgebra F K) [IsFractionRing C K] (n : ℕ) (z : Fin n → C)
    (hz : (MvPolynomial.aeval (R := F) z).toRingHom.Etale)
    (I J : Ideal C) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (q : ℚ) :
    valuativeMultiplierIdeal C (I * J) (countable_product_ne_bot I J hI hJ) q ≤
      valuativeMultiplierIdeal C I hI q * valuativeMultiplierIdeal C J hJ q := by
  let : SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap F C))) :=
    smoothOfRelativeDimension_of_etale_coordinates z hz
  let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap F C))) :=
    SmoothOfRelativeDimension.smooth n _
  let : Algebra.Smooth F C := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap F C))).mp inferInstance)
  obtain ⟨ι⟩ := CountableComplexModel.nonempty_complex_embedding F
  let : Algebra F ℂ := ι.toAlgebra
  let B := ℂ ⊗[F] C
  obtain ⟨N, g, hg, hdomain, _hcover⟩ :=
    SmoothAffineDomainCover.exists_fieldTensor_principal_domain_cover (F := F) (L := ℂ) (A₀ := C)
  apply (FieldTensorDomainCoverDescent.ideal_le_mul_iff_componentMaps g hg
    (valuativeMultiplierIdeal C (I * J) (countable_product_ne_bot I J hI hJ) q)
    (valuativeMultiplierIdeal C I hI q) (valuativeMultiplierIdeal C J hJ q)).mpr
  intro i
  let R := Localization.Away (g i)
  let : IsDomain R := (hdomain i).1
  let φ : B →ₐ[ℂ] R := IsScalarTower.toAlgHom ℂ B R
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B R)))
    infer_instance
  have h := multiplierProduct_le_after_domainOpen C φ n z hz I J hI hJ q
  have hread := tensorLocalizationCoefficientMap (F := F) (L := ℂ) (A := C) (g i)
  dsimp only [φ, B, R] at h
  simpa only [hread] using h

end EnvelopeProperty.Char0
