import EnvelopeProperty.Char0.CountableMultiplierSubadditivity
import EnvelopeProperty.Char0.CountableAffineModel
import EnvelopeProperty.Char0.FieldCoordinateDescent
import EnvelopeProperty.Char0.ValuativeSourceEquivalence
import EnvelopeProperty.Char0.ValuativeFieldTensor
import EnvelopeProperty.Char0.SmoothSourceReesCover
import EnvelopeProperty.Char0.MultiplierAwayLocalization
import EnvelopeProperty.Char0.SchemeMultiplierIdealSheaf
import Hironaka.Scheme.IdealSheaf.StalkLe

/-! # Full original multiplier ideal sheaf subadditivity over the arbitrary original char-zero field

The original field need not embed in C. The original objects may lie in any
common universe. Both the actual countable field and model are canonically
shrunk, and their whole multiplier ideals return through the proved actual
source-equivalence formula before extension to the original field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct Classical
namespace EnvelopeProperty.Char0
universe u

private theorem charZero_product_ne_bot {R : Type u} [CommRing R] [IsDomain R]
    (I J : Ideal R) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : I * J ≠ ⊥ := by
  intro h
  exact (not_or.mpr ⟨hI, hJ⟩) (Ideal.mul_eq_bot.mp h)

private theorem countableFractionModel_mul_le
    {F A : Type u} [Field F] [CharZero F] [Countable F]
    [CommRing A] [IsDomain A] [Algebra F A] [Countable A]
    {n : ℕ} (z : Fin n → A) (hz : (MvPolynomial.aeval (R := F) z).toRingHom.Etale)
    (I J : Ideal (AffineFractionFieldModel.subalgebra F A))
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (q : ℚ) :
    valuativeMultiplierIdeal _ (I * J) (charZero_product_ne_bot I J hI hJ) q ≤
      valuativeMultiplierIdeal _ I hI q * valuativeMultiplierIdeal _ J hJ q := by
  let Fs := CountableSmallCoefficientModel.Field0 F
  let As := CountableSmallCoefficientModel.Model0 A
  let : IsDomain As := CountableSmallCoefficientModel.model_isDomain A
  let Cs := AffineFractionFieldModel.subalgebra Fs As
  let es := AffineFractionFieldModel.equiv Fs As
  let eC := ((es.symm.toRingEquiv.trans
    (CountableSmallCoefficientModel.modelEquiv F A).toRingEquiv).trans
      (AffineFractionFieldModel.equiv F A).toRingEquiv)
  let Is := I.map eC.symm.toRingHom
  let Js := J.map eC.symm.toRingHom
  have hIs : Is ≠ ⊥ := (Ideal.map_eq_bot_iff_of_injective eC.symm.injective).mp.mt hI
  have hJs : Js ≠ ⊥ := (Ideal.map_eq_bot_iff_of_injective eC.symm.injective).mp.mt hJ
  let zs : Fin n → As := fun i => (CountableSmallCoefficientModel.modelEquiv F A).symm (z i)
  have hzs : (MvPolynomial.aeval (R := Fs) zs).toRingHom.Etale :=
    FieldCoordinateDescent.etale_smallModelCoordinates F A z hz
  let zCs : Fin n → Cs := fun i => es (zs i)
  have hzCs := etale_coordinates_sourceAlgEquiv es zs hzs
  have hsmall := valuativeMultiplierIdeal_mul_le_of_countable Cs n zCs hzCs Is Js hIs hJs q
  have hP := ValuativeSourceEquivalence.valuativeMultiplierIdeal_fractionModel_equiv
    (CountableSmallCoefficientModel.fieldEquiv F)
    (CountableSmallCoefficientModel.modelEquiv F A).toRingEquiv
    (CountableSmallCoefficientModel.coefficient_square F A)
    (Is * Js) (charZero_product_ne_bot Is Js hIs hJs) q
  have hMI := ValuativeSourceEquivalence.valuativeMultiplierIdeal_fractionModel_equiv
    (CountableSmallCoefficientModel.fieldEquiv F)
    (CountableSmallCoefficientModel.modelEquiv F A).toRingEquiv
    (CountableSmallCoefficientModel.coefficient_square F A) Is hIs q
  have hMJ := ValuativeSourceEquivalence.valuativeMultiplierIdeal_fractionModel_equiv
    (CountableSmallCoefficientModel.fieldEquiv F)
    (CountableSmallCoefficientModel.modelEquiv F A).toRingEquiv
    (CountableSmallCoefficientModel.coefficient_square F A) Js hJs q
  have hIsmap : Is.map eC.toRingHom = I := by
    change (I.map eC.symm.toRingHom).map eC.toRingHom = I
    rw [Ideal.map_map]
    simp
  have hJsmap : Js.map eC.toRingHom = J := by
    change (J.map eC.symm.toRingHom).map eC.toRingHom = J
    rw [Ideal.map_map]
    simp
  have hMapped := Ideal.map_mono (f := eC.toRingHom) hsmall
  rw [Ideal.map_mul, hP, hMI, hMJ] at hMapped
  change valuativeMultiplierIdeal _ ((Is * Js).map eC.toRingHom) _ q ≤
    valuativeMultiplierIdeal _ (Is.map eC.toRingHom) _ q *
      valuativeMultiplierIdeal _ (Js.map eC.toRingHom) _ q at hMapped
  simpa only [Ideal.map_mul, hIsmap, hJsmap] using hMapped

private theorem multiplier_mul_le_of_actual_countable_model
    {F k K A : Type u} [Field F] [CharZero F] [Countable F]
    [Field k] [Field K] [Algebra k K] [CharZero k] [Algebra F k]
    [CommRing A] [IsDomain A] [Algebra F A] [Countable A]
    (C : Subalgebra k K) [IsFractionRing C K]
    (E : (k ⊗[F] A) ≃ₐ[k] C) {n : ℕ} (z : Fin n → A)
    (hz : (MvPolynomial.aeval (R := F) z).toRingHom.Etale)
    (I₀ J₀ : Ideal A) (I J : Ideal C) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hImap : I₀.map (E.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) = I)
    (hJmap : J₀.map (E.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) = J)
    (q : ℚ) :
    valuativeMultiplierIdeal C (I * J) (charZero_product_ne_bot I J hI hJ) q ≤
      valuativeMultiplierIdeal C I hI q * valuativeMultiplierIdeal C J hJ q := by
  let C₀ := AffineFractionFieldModel.subalgebra F A
  let e₀ := AffineFractionFieldModel.equiv F A
  let : IsDomain C₀ := Function.Injective.isDomain e₀.symm.toRingHom e₀.symm.injective
  let : Algebra F C := ((algebraMap k C).comp (algebraMap F k)).toAlgebra
  let : IsScalarTower F k C := IsScalarTower.of_algebraMap_eq (R := F) (S := k) (A := C)
    fun _ => rfl
  let E₀ : (k ⊗[F] C₀) ≃ₐ[k] C :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) e₀.symm).trans E
  let α := FieldTensorModelEquivalence.coefficientMap (A := .of C₀) (D := .of C) E₀
  have hsquare : α.toRingHom.comp e₀.toRingHom =
      E.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom := by
    apply RingHom.ext
    intro x
    change E ((Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) e₀.symm)
      (1 ⊗ₜ[F] e₀ x)) = E (1 ⊗ₜ[F] x)
    simp
  let I' := I₀.map e₀.toRingHom
  let J' := J₀.map e₀.toRingHom
  have hI' : I'.map α.toRingHom = I := by rw [Ideal.map_map, hsquare]; exact hImap
  have hJ' : J'.map α.toRingHom = J := by rw [Ideal.map_map, hsquare]; exact hJmap
  have hI'0 : I' ≠ ⊥ := by intro h; apply hI; rw [← hI', h, Ideal.map_bot]
  have hJ'0 : J' ≠ ⊥ := by intro h; apply hJ; rw [← hJ', h, Ideal.map_bot]
  let zC₀ : Fin n → C₀ := fun i => e₀ (z i)
  have hzC₀ := etale_coordinates_sourceAlgEquiv e₀ z hz
  have hsmall := countableFractionModel_mul_le z hz I' J' hI'0 hJ'0 q
  have hP := valuativeMultiplierIdeal_fieldTensorEquiv C₀ C E₀ zC₀ hzC₀ (I' * J')
    (charZero_product_ne_bot I' J' hI'0 hJ'0) q
  have hMI := valuativeMultiplierIdeal_fieldTensorEquiv C₀ C E₀ zC₀ hzC₀ I' hI'0 q
  have hMJ := valuativeMultiplierIdeal_fieldTensorEquiv C₀ C E₀ zC₀ hzC₀ J' hJ'0 q
  have hMapped := Ideal.map_mono (f := α.toRingHom) hsmall
  rw [Ideal.map_mul, hP, hMI, hMJ] at hMapped
  change valuativeMultiplierIdeal C ((I' * J').map α.toRingHom) _ q ≤
    valuativeMultiplierIdeal C (I'.map α.toRingHom) _ q *
      valuativeMultiplierIdeal C (J'.map α.toRingHom) _ q at hMapped
  simpa only [Ideal.map_mul, hI', hJ'] using hMapped

private theorem multiplier_mul_le_of_actual_countable_family
    {F k K A : Type u} [Field F] [CharZero F] [Countable F]
    [Field k] [Field K] [Algebra k K] [CharZero k] [Algebra F k]
    [CommRing A] [IsDomain A] [Algebra F A] [Countable A]
    (C : Subalgebra k K) [IsFractionRing C K]
    (E : (k ⊗[F] A) ≃ₐ[k] C) {n m l : ℕ}
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (I J : Ideal C) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (a : Fin m → C) (ha : Ideal.span (Set.range a) = I)
    (b : Fin l → C) (hb : Ideal.span (Set.range b) = J)
    (c₀ : Fin n ⊕ (Fin m ⊕ Fin l) → A)
    (hc₀ : ∀ i, E (1 ⊗ₜ[F] c₀ i) = Sum.elim z (Sum.elim a b) i)
    (q : ℚ) :
    valuativeMultiplierIdeal C (I * J) (charZero_product_ne_bot I J hI hJ) q ≤
      valuativeMultiplierIdeal C I hI q * valuativeMultiplierIdeal C J hJ q := by
  let z₀ : Fin n → A := fun i => c₀ (.inl i)
  have hread : (fun i => E (1 ⊗ₜ[F] z₀ i)) = z := funext fun i => hc₀ (.inl i)
  have hz₀ : (MvPolynomial.aeval (R := F) z₀).toRingHom.Etale :=
    FieldCoordinateDescent.etale_of_tensorEquiv_coordinates E z₀ (by rw [hread]; exact hz)
  let a₀ : Fin m → A := fun i => c₀ (.inr (.inl i))
  let b₀ : Fin l → A := fun i => c₀ (.inr (.inr i))
  let I₀ := Ideal.span (Set.range a₀)
  let J₀ := Ideal.span (Set.range b₀)
  let δ := E.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
  have hI₀map : I₀.map δ = I := by
    rw [Ideal.map_span, ← Set.range_comp]
    calc
      Ideal.span (Set.range (fun i => δ (a₀ i))) = Ideal.span (Set.range a) := by
        apply congrArg Ideal.span
        apply congrArg Set.range
        funext i
        exact hc₀ (.inr (.inl i))
      _ = I := ha
  have hJ₀map : J₀.map δ = J := by
    rw [Ideal.map_span, ← Set.range_comp]
    calc
      Ideal.span (Set.range (fun i => δ (b₀ i))) = Ideal.span (Set.range b) := by
        apply congrArg Ideal.span
        apply congrArg Set.range
        funext i
        exact hc₀ (.inr (.inr i))
      _ = J := hb
  exact multiplier_mul_le_of_actual_countable_model C E z₀ hz₀ I₀ J₀ I J hI hJ hI₀map hJ₀map q

/-- Full original all-DVR subadditivity on an original etale affine chart over
ANY original characteristic-zero field, without embedding that field in C. -/
theorem valuativeMultiplierIdeal_mul_le_of_etale
    {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
    (C : Subalgebra k K) [IsFractionRing C K] (n : ℕ) (z : Fin n → C)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (I J : Ideal C) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (q : ℚ) :
    valuativeMultiplierIdeal C (I * J) (charZero_product_ne_bot I J hI hJ) q ≤
      valuativeMultiplierIdeal C I hI q * valuativeMultiplierIdeal C J hJ q := by
  let : SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap k C))) :=
    smoothOfRelativeDimension_of_etale_coordinates z hz
  let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C))) :=
    SmoothOfRelativeDimension.smooth n _
  let : Algebra.Smooth k C := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap k C))).mp inferInstance)
  let : Algebra.FiniteType k C := finiteType_of_etale_coordinates z hz
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  obtain ⟨m, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I)
  obtain ⟨l, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian J)
  let c : Fin n ⊕ (Fin m ⊕ Fin l) → C := Sum.elim z (Sum.elim a b)
  obtain ⟨F, hF, m₀, r₀, Q, c₀, E, hc₀, _hspan, _hFP, _hcount, _hsm, hdomain⟩ :=
    CountableAffineModel.exists_countable_smooth_domain_model (K := k) (A := C) c
  let : Countable F := hF
  let A₀ := MvPolynomial (Fin m₀) F ⧸ Ideal.span (Set.range Q)
  let : IsDomain A₀ := hdomain
  let : Countable A₀ := _hcount
  exact multiplier_mul_le_of_actual_countable_family C E z hz I J hI hJ a ha b hb c₀ hc₀ q

/-- Full original multiplier subadditivity for arbitrary smooth original affine
subalgebras, with the actual etale cover constructed internally. -/
theorem valuativeMultiplierIdeal_mul_le
    {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
    (C : Subalgebra k K) [IsFractionRing C K]
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (I J : Ideal C) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (q : ℚ) :
    valuativeMultiplierIdeal C (I * J) (charZero_product_ne_bot I J hI hJ) q ≤
      valuativeMultiplierIdeal C I hI q * valuativeMultiplierIdeal C J hJ q := by
  obtain ⟨n, m, g, hg, _, hcoord⟩ := exists_smooth_source_unit_rees_etale_cover C
  intro a ha
  let B := valuativeMultiplierIdeal C I hI q * valuativeMultiplierIdeal C J hJ q
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem B (Set.range g) hg a
  rintro ⟨s, i, rfl⟩
  by_cases hi : g i = 0
  · exact ⟨1, by simp [hi]⟩
  · let D := reesTreeChart C g i
    let hCD := le_reesTreeChart C g i
    let φ := (Subalgebra.inclusion hCD).toRingHom
    let : Algebra C D := φ.toAlgebra
    let : IsFractionRing D K := isFractionRing_intermediate_subalgebra C D hCD
    have hlocal : IsLocalization.Away (g i) D := isLocalization_principalReesChart C g hg i hi
    let : IsLocalization.Away (g i) D := hlocal
    have hID : I.map φ ≠ ⊥ :=
      (Ideal.map_eq_bot_iff_of_injective (Subalgebra.inclusion_injective hCD)).mp.mt hI
    have hJD : J.map φ ≠ ⊥ :=
      (Ideal.map_eq_bot_iff_of_injective (Subalgebra.inclusion_injective hCD)).mp.mt hJ
    obtain ⟨z, hz⟩ := hcoord ⟨i, hi⟩
    have hbaseP := map_valuativeMultiplierIdeal_source_away C D hCD (g i) hlocal
      (I * J) (charZero_product_ne_bot I J hI hJ) q
    have hbaseI := map_valuativeMultiplierIdeal_source_away C D hCD (g i) hlocal I hI q
    have hbaseJ := map_valuativeMultiplierIdeal_source_away C D hCD (g i) hlocal J hJ q
    have hle : (valuativeMultiplierIdeal C (I * J) (charZero_product_ne_bot I J hI hJ) q).map φ ≤
        B.map φ := by
      dsimp only [B]
      rw [hbaseP]
      simp only [Ideal.map_mul]
      rw [hbaseI, hbaseJ]
      exact valuativeMultiplierIdeal_mul_le_of_etale D n z hz (I.map φ) (J.map φ) hID hJD q
    have hcoeff : algebraMap C D a ∈ B.map (algebraMap C D) :=
      hle (Ideal.mem_map_of_mem φ ha)
    obtain ⟨s, hs, hmem⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers (g i)) D B a).mp hcoeff
    obtain ⟨N, rfl⟩ := hs
    exact ⟨N, hmem⟩

private theorem scheme_product_generic_ne_bot {X : Scheme.{u}} [IsIntegral X]
    (I J : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (hJ : J.stalkIdeal (genericPoint X) ≠ ⊥) : (I * J).stalkIdeal (genericPoint X) ≠ ⊥ := by
  rw [Scheme.IdealSheafData.stalkIdeal_mul]
  exact charZero_product_ne_bot _ _ hI hJ

/-- Subadditivity of the SAME original smooth scheme multiplier ideal sheaves.
The original field is arbitrary; original generic nonzero ideals and all rational levels are retained. -/
theorem schemeMultiplierIdealSheaf_mul_le
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (I J : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (hJ : J.stalkIdeal (genericPoint X) ≠ ⊥) (q : ℚ) :
    schemeMultiplierIdealSheaf f (I * J) (scheme_product_generic_ne_bot I J hI hJ) q ≤
      schemeMultiplierIdealSheaf f I hI q * schemeMultiplierIdealSheaf f J hJ q := by
  intro U
  change schemeMultiplierAffineIdeal f (I * J) (scheme_product_generic_ne_bot I J hI hJ) q U ≤
    schemeMultiplierAffineIdeal f I hI q U * schemeMultiplierAffineIdeal f J hJ q U
  by_cases hU : Nonempty U.1
  · let _ := hU
    let _ := f.stalkAlgebra (genericPoint X)
    let _ := f.sectionsAlgebra U.1
    let C := f.sectionsFunctionFieldSubalgebra U.1
    let e := f.sectionsFunctionFieldEquiv U.1
    let : IsFractionRing C X.functionField := f.sectionsFunctionFieldSubalgebra_isFractionRing U.1 U.2
    let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C))) :=
      f.smooth_sectionsFunctionFieldSubalgebra U.1 U.2
    have hIC : (I.ideal U).map e.toRingHom ≠ ⊥ :=
      (Ideal.map_eq_bot_iff_of_injective e.injective).mp.mt
        (affineIdeal_ne_bot_of_generic_stalk_ne_bot I hI U)
    have hJC : (J.ideal U).map e.toRingHom ≠ ⊥ :=
      (Ideal.map_eq_bot_iff_of_injective e.injective).mp.mt
        (affineIdeal_ne_bot_of_generic_stalk_ne_bot J hJ U)
    have h := valuativeMultiplierIdeal_mul_le C ((I.ideal U).map e.toRingHom)
      ((J.ideal U).map e.toRingHom) hIC hJC q
    simp only [schemeMultiplierAffineIdeal, dif_pos hU]
    change (valuativeMultiplierIdeal C (((I * J).ideal U).map e.toRingHom) _ q).comap e.toRingHom ≤
      (valuativeMultiplierIdeal C ((I.ideal U).map e.toRingHom) _ q).comap e.toRingHom *
        (valuativeMultiplierIdeal C ((J.ideal U).map e.toRingHom) _ q).comap e.toRingHom
    have hprod : ((I * J).ideal U).map e.toRingHom =
        (I.ideal U).map e.toRingHom * (J.ideal U).map e.toRingHom := Ideal.map_mul _ _ _
    have hcomap (A B : Ideal C) : (A * B).comap e.toRingHom =
        A.comap e.toRingHom * B.comap e.toRingHom := by
      have he (L : Ideal C) : L.comap e.toRingHom = L.map e.symm.toRingHom :=
        (Ideal.map_comap_of_equiv e.toRingEquiv.symm).symm
      rw [he, Ideal.map_mul, he, he]
    have h' := Ideal.comap_mono (f := e.toRingHom) h
    rw [hcomap] at h'
    simpa only [hprod] using h'
  · simp only [schemeMultiplierAffineIdeal, dif_neg hU, Ideal.top_mul, le_refl]

end EnvelopeProperty.Char0
