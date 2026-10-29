import EnvelopeProperty.AlgGeom.GaussRegularSurfaceValuationOrders
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Actual native eventual orders on the SAME original fraction field

All original localization, residue and fraction-field maps are constructed
internally. No valuation family, leading-residue comparison or slope pair
is supplied as an input.
-/

noncomputable section
open IsLocalRing IsDiscreteValuationRing
open scoped Classical nonZeroDivisors WithZero

universe u
namespace EnvelopeProperty.GaussRegularSurfaceValuationFractions

variable {S : Type u} [CommRing S] [IsDomain S]

local notation "T(" π "," hπ ")" => GaussRegularSurfaceValuationOrders.verticalRing π hπ

/-- The actual original vertical localization embeds in the SAME FractionRing S. -/
def verticalFractionEmbedding (π : S) (hπ : Prime π) : T(π,hπ) →+* FractionRing S := by
  let : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  exact (Localization.mapToFractionRing (FractionRing S) (Ideal.span {π}).primeCompl T(π,hπ)
    (Ideal.span {π}).primeCompl_le_nonZeroDivisors).toRingHom

/-- The actual original map is injective by the genuine localization kernel. -/
theorem verticalFractionEmbedding_injective (π : S) (hπ : Prime π) :
    Function.Injective (verticalFractionEmbedding π hπ) := by
  let : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  have hM := (Ideal.span {π}).primeCompl_le_nonZeroDivisors
  change Function.Injective (IsLocalization.lift (Localization.map_isUnit_of_le
    (FractionRing S) (Ideal.span {π}).primeCompl hM) : T(π,hπ) →+* FractionRing S)
  apply (IsLocalization.lift_injective_iff _).mpr
  intro a b
  exact ⟨fun h => congrArg _ (IsLocalization.injective T(π,hπ) hM h),
    fun h => congrArg _ (IsFractionRing.injective S (FractionRing S) h)⟩

/-- EVERY original coefficient keeps its literal original fraction-field value. -/
theorem verticalFractionEmbedding_coefficient (π : S) (hπ : Prime π) (s : S) :
    verticalFractionEmbedding π hπ (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ s) =
      algebraMap S (FractionRing S) s := by
  let : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  exact (Localization.mapToFractionRing (FractionRing S) (Ideal.span {π}).primeCompl T(π,hπ)
    (Ideal.span {π}).primeCompl_le_nonZeroDivisors).commutes s

/-- This SAME actual embedding makes the ORIGINAL field the fraction ring
of the ORIGINAL vertical localization. -/
theorem verticalFractionRing (π : S) (hπ : Prime π) :
    letI : Algebra T(π,hπ) (FractionRing S) := (verticalFractionEmbedding π hπ).toAlgebra
    IsFractionRing T(π,hπ) (FractionRing S) := by
  let : Algebra T(π,hπ) (FractionRing S) := (verticalFractionEmbedding π hπ).toAlgebra
  let : FaithfulSMul T(π,hπ) (FractionRing S) :=
    (faithfulSMul_iff_algebraMap_injective T(π,hπ) _).mpr (verticalFractionEmbedding_injective π hπ)
  apply IsFractionRing.of_field T(π,hπ) (FractionRing S)
  intro f
  obtain ⟨s,t,_,h⟩ := IsFractionRing.div_surjective S f
  refine ⟨GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ s,
    GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ t,?_⟩
  change f = verticalFractionEmbedding π hπ _ / verticalFractionEmbedding π hπ _
  rw [verticalFractionEmbedding_coefficient,verticalFractionEmbedding_coefficient]
  exact h.symm

/-- The canonical ORIGINAL vertical residue field equals the fraction field
of the actual original prime quotient; no residue identification is input. -/
def verticalResidueEquiv [IsLocalRing S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) :
    ResidueField T(π,hπ) ≃+* FractionRing (GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm) := by
  let : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  exact (FractionRing.algEquiv (A := GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm)
    (ResidueField T(π,hπ))).symm.toRingEquiv

omit [IsDomain S] in
/-- The canonical field map retains the actual residue of EVERY original coefficient. -/
theorem verticalResidueEquiv_coefficient [IsLocalRing S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (s : S) :
    verticalResidueEquiv π z hπ hz hm
        (residue T(π,hπ) (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ s)) =
      algebraMap (GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm) _
        (GaussRegularSurfaceValuationOrders.residualCoefficientMap π z hπ hz hm s) := by
  let : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  let R := GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm
  have hc : algebraMap R (ResidueField T(π,hπ))
      (GaussRegularSurfaceValuationOrders.residualCoefficientMap π z hπ hz hm s) =
      residue T(π,hπ) (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ s) := by
    dsimp only [R,GaussRegularSurfaceValuationOrders.residualCoefficientMap]
    erw [Ideal.algebraMap_quotient_residueField_mk]
  rw [← hc]
  exact (FractionRing.algEquiv (A := R) (ResidueField T(π,hπ))).symm.commutes _

variable [IsNoetherianRing S]

/-- The actual native order on the SAME original field, using its actual
original vertical DVR and the original embedding just constructed. -/
def verticalOrder (π : S) (hπ : Prime π) : FractionRing S →*₀ ℤᵐ⁰ := by
  let : Algebra T(π,hπ) (FractionRing S) := (verticalFractionEmbedding π hπ).toAlgebra
  let : IsFractionRing T(π,hπ) (FractionRing S) := verticalFractionRing π hπ
  exact Ring.ordFrac T(π,hπ)

/-- The ACTUAL weighted native order on that SAME original FractionRing S. -/
def weightedOrder [IsLocalRing S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (N : ℕ) (hN : 0 < N) : FractionRing S →*₀ ℤᵐ⁰ := by
  let V := GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN
  let : Algebra V (FractionRing S) := (GaussRegularSurfaceValuations.fractionEmbedding π z hπ hz N hm hN).toAlgebra
  let : IsFractionRing V (FractionRing S) := GaussRegularSurfaceValuations.localFractionRing π z hπ hz N hm hN
  exact Ring.ordFrac V

/-- The actual residual fraction-field order of the SAME original quotient DVR. -/
def residualOrder [IsLocalRing S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) :
    FractionRing (GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm) →*₀ ℤᵐ⁰ :=
  Ring.ordFrac (GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm)

private theorem nativeOrder_of_addVal {A K : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (x : A) (n : ℕ) (h : addVal A x = n) :
    Ring.ordFrac A (algebraMap A K x) = WithZero.exp (n : ℤ) := by
  rw [Ring.ordFrac_eq_valuation_inv,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal,h,inv_inv]
  rfl

private theorem verticalOrder_coefficient (π : S) (hπ : Prime π) (s : S) (n : ℕ)
    (h : addVal T(π,hπ) (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ s) = n) :
    verticalOrder π hπ (algebraMap S (FractionRing S) s) = WithZero.exp (n : ℤ) := by
  let : Algebra T(π,hπ) (FractionRing S) := (verticalFractionEmbedding π hπ).toAlgebra
  let : IsFractionRing T(π,hπ) (FractionRing S) := verticalFractionRing π hπ
  change Ring.ordFrac T(π,hπ) _ = _
  rw [← verticalFractionEmbedding_coefficient π hπ s]
  exact nativeOrder_of_addVal _ n h

private theorem weightedOrder_coefficient [IsLocalRing S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (N : ℕ) (hN : 0 < N) (s : S) (n : ℕ)
    (h : addVal (GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN)
      (GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN s) = n) :
    weightedOrder π z hπ hz hm N hN (algebraMap S (FractionRing S) s) = WithZero.exp (n : ℤ) := by
  let V := GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN
  let : Algebra V (FractionRing S) := (GaussRegularSurfaceValuations.fractionEmbedding π z hπ hz N hm hN).toAlgebra
  let : IsFractionRing V (FractionRing S) := GaussRegularSurfaceValuations.localFractionRing π z hπ hz N hm hN
  change Ring.ordFrac V _ = _
  rw [← GaussRegularSurfaceValuations.fractionEmbedding_coefficient π z hπ hz N hm hN s]
  exact nativeOrder_of_addVal _ n h

omit [IsDomain S] in
private theorem residualOrder_coefficient [IsLocalRing S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (s : S) (n : ℕ)
    (h : addVal (GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm)
      (GaussRegularSurfaceValuationOrders.residualCoefficientMap π z hπ hz hm s) = n) :
    residualOrder π z hπ hz hm
      (algebraMap (GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm) _
        (GaussRegularSurfaceValuationOrders.residualCoefficientMap π z hπ hz hm s)) = WithZero.exp (n : ℤ) :=
  nativeOrder_of_addVal _ n h

section Leading
variable [IsLocalRing S]

private theorem weighted_addVal_of_leading (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (f f' u g : S) (a b : ℕ)
    (hf : f = π ^ a * f') (he : f' = z ^ b * u + π * g) (hu : IsUnit u)
    (N : ℕ) (hN : 0 < N) (hb : b < N) :
    addVal (GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN)
      (GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN f) = a * N + b := by
  let V := GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN
  let j := GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN
  have hzv : addVal V (j z) = 1 := GaussRegularSurfaceValuations.parameter_addVal π z hπ hz N hm hN
  have hpv : addVal V (j π) = N := GaussRegularSurfaceValuations.vertical_addVal π z hπ hz N hm hN
  have huv : addVal V (j u) = 0 := addVal_eq_zero_iff.mpr (hu.map j)
  have hsmall : addVal V (j (z ^ b * u)) = b := by
    rw [map_mul,map_pow,addVal_mul,addVal_pow,hzv,huv,add_zero,nsmul_one]
  have hbig : (N : ℕ∞) ≤ addVal V (j (π * g)) := by
    rw [map_mul,addVal_mul,hpv]
    exact le_self_add
  have hlt : addVal V (j (z ^ b * u)) < addVal V (j (π * g)) := by
    rw [hsmall]
    exact lt_of_lt_of_le (by exact_mod_cast hb) hbig
  have hfv : addVal V (j f') = b := by rw [he,map_add,(addVal V).map_add_eq_of_lt_left hlt,hsmall]
  change addVal V (j f) = _
  rw [hf,map_mul,map_pow,addVal_mul,addVal_pow,hpv,hfv,nsmul_eq_mul]

private theorem leading_eventual (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (f : S) (hf : f ≠ 0) :
    ∃ (a b : ℕ) (f' : S), f = π ^ a * f' ∧ ¬ π ∣ f' ∧
      verticalOrder π hπ (algebraMap S (FractionRing S) f) = WithZero.exp (a : ℤ) ∧
      residualOrder π z hπ hz hm
        (algebraMap (GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm) _
          (GaussRegularSurfaceValuationOrders.residualCoefficientMap π z hπ hz hm f')) = WithZero.exp (b : ℤ) ∧
      ∀ (N : ℕ) (hN : 0 < N), b < N →
        weightedOrder π z hπ hz hm N hN (algebraMap S (FractionRing S) f) =
          WithZero.exp ((a : ℤ) * (N : ℤ) + (b : ℤ)) := by
  obtain ⟨a,b,f',u,g,hfactor,hlead,hu,hnd,hva,hrb⟩ :=
    GaussRegularSurfaceValuationOrders.exists_leadingExpansion π z hπ hz hm f hf
  obtain ⟨a',b',hva',hord⟩ := GaussRegularSurfaceValuationOrders.exists_eventual_addVal π z hπ hz hm f hf
  have haa : a' = a := by exact_mod_cast hva'.symm.trans hva
  subst a'
  have hbb : b' = b := by
    let n := max b b' + 1
    have hn : 0 < n := Nat.succ_pos _
    have hb : b < n := Nat.lt_succ_of_le (le_max_left _ _)
    have hb' : b' < n := Nat.lt_succ_of_le (le_max_right _ _)
    have hc := weighted_addVal_of_leading π z hπ hz hm f f' u g a b hfactor hlead hu n hn hb
    have heq : a * n + b' = a * n + b := by exact_mod_cast (hord n hn hb').symm.trans hc
    exact Nat.add_left_cancel heq
  subst b'
  refine ⟨a,b,f',hfactor,hnd,verticalOrder_coefficient π hπ f a hva,
    residualOrder_coefficient π z hπ hz hm f' b hrb,?_⟩
  intro N hN hb
  simpa only [Nat.cast_mul,Nat.cast_add] using weightedOrder_coefficient π z hπ hz hm N hN f (a * N + b)
    (by simpa only [Nat.cast_mul,Nat.cast_add] using hord N hN hb)

omit [IsDomain S] [IsNoetherianRing S] [IsLocalRing S] in
private theorem vertical_unit_of_not_div (π : S) (hπ : Prime π) (s : S) (hs : ¬ π ∣ s) :
    IsUnit (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ s) := by
  let : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  apply (IsLocalization.AtPrime.isUnit_to_map_iff _ (Ideal.span {π}) _).mpr
  change s ∉ Ideal.span {π}
  simpa only [Ideal.mem_span_singleton] using hs

/-- Every nonzero fraction INTERNALLY gives a true vertical unit and its
genuine intrinsic leading-residue order, with exact eventual weighted orders
in the SAME original FractionRing S. No field/order/slope pair is input. -/
theorem exists_eventual_fieldOrder (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (f : FractionRing S) (hf : f ≠ 0) :
    ∃ (a b : ℤ) (u : T(π,hπ)ˣ), f = verticalFractionEmbedding π hπ (u : T(π,hπ)) *
        (algebraMap S (FractionRing S) π) ^ a ∧
      verticalOrder π hπ f = WithZero.exp a ∧
      residualOrder π z hπ hz hm (verticalResidueEquiv π z hπ hz hm (residue T(π,hπ) (u : T(π,hπ)))) = WithZero.exp b ∧
      ∃ M : ℕ, ∀ (N : ℕ) (hN : 0 < N), M < N →
        weightedOrder π z hπ hz hm N hN f = WithZero.exp (a * (N : ℤ) + b) := by
  obtain ⟨s,t,ht,heq⟩ := IsFractionRing.div_surjective S f
  have hs : s ≠ 0 := by
    intro hs
    apply hf
    rw [← heq,hs,map_zero,zero_div]
  have ht0 : t ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp ht
  obtain ⟨as,bs,s',hfs,hns,hvs,hrs,hes⟩ := leading_eventual π z hπ hz hm s hs
  obtain ⟨aT,bt,t',hft,hnt,hvt,hrt,het⟩ := leading_eventual π z hπ hz hm t ht0
  have hus := vertical_unit_of_not_div π hπ s' hns
  have hut := vertical_unit_of_not_div π hπ t' hnt
  let us : T(π,hπ)ˣ := hus.unit
  let ut : T(π,hπ)ˣ := hut.unit
  let u := us / ut
  have hsval : (us : T(π,hπ)) = GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ s' := hus.unit_spec
  have htval : (ut : T(π,hπ)) = GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ t' := hut.unit_spec
  have hue : verticalFractionEmbedding π hπ (u : T(π,hπ)) =
      verticalFractionEmbedding π hπ (us : T(π,hπ)) / verticalFractionEmbedding π hπ (ut : T(π,hπ)) := by
    change verticalFractionEmbedding π hπ ((us : T(π,hπ)) * (↑ut⁻¹ : T(π,hπ))) = _
    rw [map_mul,map_units_inv,div_eq_mul_inv]
  have hπK : algebraMap S (FractionRing S) π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr hπ.ne_zero
  refine ⟨(as : ℤ) - (aT : ℤ),(bs : ℤ) - (bt : ℤ),u,?_,?_,?_,?_⟩
  · rw [← heq,hfs,hft]
    simp only [map_mul,map_pow]
    rw [hue,hsval,htval,verticalFractionEmbedding_coefficient,verticalFractionEmbedding_coefficient,
      zpow_sub₀ hπK,zpow_natCast,zpow_natCast,div_mul_div_comm]
    congr 1 <;> ring
  · rw [← heq,map_div₀,hvs,hvt,← WithZero.exp_sub]
  · let er : T(π,hπ) →+* FractionRing (GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm) :=
      (verticalResidueEquiv π z hπ hz hm).toRingHom.comp (residue T(π,hπ))
    have her : verticalResidueEquiv π z hπ hz hm (residue T(π,hπ) (u : T(π,hπ))) =
        algebraMap (GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm) _
          (GaussRegularSurfaceValuationOrders.residualCoefficientMap π z hπ hz hm s') /
        algebraMap (GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm) _
          (GaussRegularSurfaceValuationOrders.residualCoefficientMap π z hπ hz hm t') := by
      calc
        _ = er (u : T(π,hπ)) := rfl
        _ = er (us : T(π,hπ)) / er (ut : T(π,hπ)) := by
          change er ((us : T(π,hπ)) * (↑ut⁻¹ : T(π,hπ))) = _
          rw [map_mul,map_units_inv,div_eq_mul_inv]
        _ = _ := by
          change verticalResidueEquiv π z hπ hz hm (residue T(π,hπ) (us : T(π,hπ))) /
            verticalResidueEquiv π z hπ hz hm (residue T(π,hπ) (ut : T(π,hπ))) = _
          rw [hsval,htval,verticalResidueEquiv_coefficient,verticalResidueEquiv_coefficient]
    rw [her,map_div₀,hrs,hrt,← WithZero.exp_sub]
  · refine ⟨max bs bt,?_⟩
    intro N hN hmax
    rw [← heq,map_div₀,hes N hN (lt_of_le_of_lt (le_max_left _ _) hmax),
      het N hN (lt_of_le_of_lt (le_max_right _ _) hmax),← WithZero.exp_sub]
    congr 1
    ring

end Leading
end EnvelopeProperty.GaussRegularSurfaceValuationFractions
