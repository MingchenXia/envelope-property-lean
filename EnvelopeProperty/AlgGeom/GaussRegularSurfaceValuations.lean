import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! # Actual original weighted surface charts and their DVR localizations

The original quotient uses genuine parameters. No valuation family, normalized
chart or desired order comparison is supplied. The first algebraic step is
prime-parameter saturation, without a GCD/UFD or normalization hypothesis.
-/

noncomputable section
open Polynomial IsLocalRing
open scoped Classical Polynomial nonZeroDivisors

universe u
namespace EnvelopeProperty.GaussRegularSurfaceValuations

variable {S : Type u} [CommRing S]

/-- The literal original weighted linear relation. -/
def relation (π z : S) (N : ℕ) : S[X] := C π * X - C (z ^ N)

/-- The actual original polynomial quotient, before any localization. -/
abbrev chart (π z : S) (N : ℕ) := AdjoinRoot (relation π z N)

/-- The same original coefficient map into that literal quotient. -/
def coefficientMap (π z : S) (N : ℕ) : S →+* chart π z N :=
  AdjoinRoot.of (relation π z N)

/-- The actual image of the original polynomial variable. -/
def chartParameter (π z : S) (N : ℕ) : chart π z N :=
  AdjoinRoot.root (relation π z N)

/-- A genuine prime coefficient and nonzero original residue make the
actual linear relation saturated under multiplication by that coefficient. -/
theorem relation_saturated [IsDomain S] (π c : S) (hπ : Prime π)
    (hc : ¬ π ∣ c) (P : S[X]) :
    C π * X - C c ∣ C π * P → C π * X - C c ∣ P := by
  let I : Ideal S := Ideal.span {π}
  let : I.IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  let ρ : S →+* S ⧸ I := Ideal.Quotient.mk I
  have hρπ : ρ π = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl π))
  have hρc : ρ c ≠ 0 := by
    intro he
    exact hc (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he))
  rintro ⟨Q,hQ⟩
  have he := congrArg (Polynomial.map ρ) hQ
  simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_C,Polynomial.map_X,
    hρπ,map_zero,zero_mul,zero_sub] at he
  have hQzero : Q.map ρ = 0 := by
    exact (mul_eq_zero.mp he.symm).resolve_left (neg_ne_zero.mpr (C_ne_zero.mpr hρc))
  have hQmem : Q ∈ I.map (C : S →+* S[X]) := by
    apply Ideal.mem_map_C_iff.mpr
    intro n
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hn := congrArg (fun p : (S ⧸ I)[X] => p.coeff n) hQzero
    simpa only [coeff_map,coeff_zero] using hn
  have hmap : I.map (C : S →+* S[X]) = Ideal.span {C π} := by
    dsimp only [I]
    rw [Ideal.map_span,Set.image_singleton]
  obtain ⟨Q₁,hQ₁⟩ := Ideal.mem_span_singleton.mp (hmap ▸ hQmem)
  refine ⟨Q₁,?_⟩
  apply mul_left_cancel₀ (C_ne_zero.mpr hπ.ne_zero)
  rw [hQ,hQ₁]
  ring


private def awayRoot (π c : S) : Localization.Away π :=
  algebraMap S (Localization.Away π) c * IsLocalization.Away.invSelf π

private theorem awayRoot_relation (π c : S) :
    algebraMap S (Localization.Away π) π * awayRoot π c =
      algebraMap S (Localization.Away π) c := by
  dsimp only [awayRoot]
  rw [mul_left_comm,IsLocalization.Away.mul_invSelf,mul_one]

private theorem away_eval_kernel [IsDomain S] (π c : S) (hπ : Prime π)
    (hc : ¬ π ∣ c) :
    RingHom.ker (eval₂RingHom (algebraMap S (Localization.Away π)) (awayRoot π c)) =
      Ideal.span {C π * X - C c} := by
  let A := Localization.Away π
  let φ : S →+* A := algebraMap S A
  let τ : A := awayRoot π c
  let F : S[X] := C π * X - C c
  let q : Ideal S[X] := Ideal.span {F}
  let MP : Submonoid S[X] := (Submonoid.powers π).map C
  let : Algebra S[X] A[X] := Polynomial.algebra S A
  let : IsLocalization MP A[X] := Polynomial.isLocalization (Submonoid.powers π) A
  have hπτ : φ π * τ = φ c := awayRoot_relation π c
  have hF : F.map φ = C (φ π) * (X - C τ) := by
    dsimp only [F]
    rw [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,Polynomial.map_C,
      mul_sub,← Polynomial.C_mul,hπτ]
  have hπu : IsUnit (C (φ π) : A[X]) :=
    (IsLocalization.map_units A (⟨π,Submonoid.mem_powers π⟩ : Submonoid.powers π)).map C
  have hq : q.map (algebraMap S[X] A[X]) = Ideal.span {X - C τ} := by
    dsimp only [q]
    rw [Ideal.map_span,Set.image_singleton]
    change Ideal.span {F.map φ} = _
    rw [hF,Ideal.span_singleton_mul_left_unit hπu]
  change RingHom.ker (eval₂RingHom φ τ) = q
  apply le_antisymm
  · intro P hP
    have he : (P.map φ).eval τ = 0 := by
      simpa only [RingHom.mem_ker,coe_eval₂RingHom,eval₂_eq_eval_map] using hP
    have hmem : algebraMap S[X] A[X] P ∈ q.map (algebraMap S[X] A[X]) := by
      rw [hq,← Polynomial.ker_evalRingHom τ]
      change (P.map φ).eval τ = 0
      exact he
    obtain ⟨d,hd,hdP⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff MP A[X] q P).mp hmem
    obtain ⟨a,ha,hda⟩ := hd
    obtain ⟨n,hn⟩ := ha
    have hpow : (C π) ^ n * P ∈ q := by
      rw [← hda,← hn,map_pow] at hdP
      exact hdP
    have hs : ∀ n : ℕ, (C π) ^ n * P ∈ q → P ∈ q := by
      intro n
      induction n with
      | zero => simpa only [pow_zero,one_mul] using (fun h => h)
      | succ n ih =>
        intro h
        apply ih
        apply Ideal.mem_span_singleton.mpr
        apply relation_saturated π c hπ hc ((C π) ^ n * P)
        apply Ideal.mem_span_singleton.mp
        simpa only [pow_succ',mul_assoc] using h
    exact hs n hpow
  · apply Ideal.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    change (C π * X - C c).eval₂ φ τ = 0
    simp only [eval₂_sub,eval₂_mul,eval₂_C,eval₂_X,hπτ,sub_self]

private def chartAwayMap (π z : S) (N : ℕ) : chart π z N →+* Localization.Away π := by
  let A := Localization.Away π
  let φ : S →+* A := algebraMap S A
  let τ : A := awayRoot π (z ^ N)
  have he : (relation π z N).eval₂ φ τ = 0 := by
    change (C π * X - C (z ^ N)).eval₂ φ τ = 0
    simp only [eval₂_sub,eval₂_mul,eval₂_C,eval₂_X]
    exact sub_eq_zero.mpr (awayRoot_relation π (z ^ N))
  exact AdjoinRoot.lift φ τ he

private theorem chartAwayMap_injective [IsDomain S] (π z : S) (hπ : Prime π)
    (hz : ¬ π ∣ z) (N : ℕ) : Function.Injective (chartAwayMap π z N) := by
  have hc : ¬ π ∣ z ^ N := fun h => hz (hπ.dvd_of_dvd_pow h)
  apply (injective_iff_map_eq_zero (chartAwayMap π z N)).mpr
  intro b hb
  induction b using AdjoinRoot.induction_on with
  | ih P =>
    apply AdjoinRoot.mk_eq_zero.mpr
    apply Ideal.mem_span_singleton.mp
    change P ∈ Ideal.span {C π * X - C (z ^ N)}
    rw [← away_eval_kernel π (z ^ N) hπ hc]
    change P.eval₂ (algebraMap S (Localization.Away π)) (awayRoot π (z ^ N)) = 0
    simpa only [chartAwayMap,AdjoinRoot.lift_mk] using hb

private theorem chartAwayMap_coefficient (π z : S) (N : ℕ) (s : S) :
    chartAwayMap π z N (coefficientMap π z N s) = algebraMap S (Localization.Away π) s := by
  dsimp only [chartAwayMap,coefficientMap]
  exact AdjoinRoot.lift_of _

/-- The original literal weighted chart is a domain, derived from the prime
parameter and its original nonzero second-parameter residue. -/
theorem chart_isDomain [IsDomain S] (π z : S) (hπ : Prime π)
    (hz : ¬ π ∣ z) (N : ℕ) : IsDomain (chart π z N) := by
  let : IsDomain (Localization.Away π) := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero)
  exact (chartAwayMap_injective π z hπ hz N).isDomain

private def chartFractionMap [IsDomain S] (π z : S) (hπ : Prime π) (N : ℕ) :
    chart π z N →+* FractionRing S :=
  (Localization.mapToFractionRing (FractionRing S) (Submonoid.powers π) (Localization.Away π)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero)).toRingHom.comp (chartAwayMap π z N)

private theorem chartFractionMap_injective [IsDomain S] (π z : S) (hπ : Prime π)
    (hz : ¬ π ∣ z) (N : ℕ) : Function.Injective (chartFractionMap π z hπ N) := by
  have hM := powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero
  have hi : Function.Injective (Localization.mapToFractionRing (FractionRing S)
      (Submonoid.powers π) (Localization.Away π) hM) := by
    change Function.Injective (IsLocalization.lift (Localization.map_isUnit_of_le
      (FractionRing S) (Submonoid.powers π) hM) : Localization.Away π →+* FractionRing S)
    apply (IsLocalization.lift_injective_iff _).mpr
    intro a b
    exact ⟨fun h => congrArg _ (IsLocalization.injective (Localization.Away π) hM h),
      fun h => congrArg _ (IsFractionRing.injective S (FractionRing S) h)⟩
  exact hi.comp (chartAwayMap_injective π z hπ hz N)

private theorem chartFractionMap_coefficient [IsDomain S] (π z : S) (hπ : Prime π)
    (N : ℕ) (s : S) : chartFractionMap π z hπ N (coefficientMap π z N s) =
      algebraMap S (FractionRing S) s := by
  dsimp only [chartFractionMap,RingHom.comp_apply,AlgHom.toRingHom_eq_coe]
  rw [chartAwayMap_coefficient]
  exact (Localization.mapToFractionRing (FractionRing S) (Submonoid.powers π) (Localization.Away π)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero)).commutes s


section ClosedCentre
variable [IsLocalRing S]

/-- The actual ideal extended from the same original local maximal ideal. -/
def closedPrime (π z : S) (N : ℕ) : Ideal (chart π z N) :=
  (maximalIdeal S).map (coefficientMap π z N)

private theorem relation_mod_maximal (π z : S) (N : ℕ)
    (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    (relation π z N).map (Ideal.Quotient.mk (maximalIdeal S)) = 0 := by
  have hp : π ∈ maximalIdeal S := hm.symm ▸ Ideal.subset_span (by simp)
  have hz : z ∈ maximalIdeal S := hm.symm ▸ Ideal.subset_span (by simp)
  have hp0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have hz0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
  have hzN0 : Ideal.Quotient.mk (maximalIdeal S) (z ^ N) = 0 := by
    rw [map_pow,hz0,zero_pow hN.ne']
  simp only [relation,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_X,hp0,hzN0,map_zero,zero_mul,sub_zero]

/-- The actual SAME chart residue quotient is the original residue polynomial
ring, with no chosen prime or residue isomorphism as input. -/
def chart_residueIso (π z : S) (N : ℕ)
    (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    chart π z N ⧸ closedPrime π z N ≃+* (ResidueField S)[X] :=
  (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal S) (relation π z N)).trans
    ((Ideal.quotEquivOfEq (show Ideal.span
      {(relation π z N).map (Ideal.Quotient.mk (maximalIdeal S))} = ⊥ by
        rw [relation_mod_maximal π z N hm hN,Ideal.span_singleton_zero])).trans
      (RingEquiv.quotientBot _))

/-- The original maximal-ideal extension is a genuine prime of the same chart. -/
theorem closedPrime_isPrime [IsDomain S] (π z : S) (N : ℕ)
    (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    (closedPrime π z N).IsPrime := by
  apply (Ideal.Quotient.isDomain_iff_prime (closedPrime π z N)).mp
  exact (chart_residueIso π z N hm hN).injective.isDomain

private theorem chart_residueIso_parameter (π z : S) (N : ℕ)
    (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    chart_residueIso π z N hm hN
      (Ideal.Quotient.mk (closedPrime π z N) (chartParameter π z N)) = X := by
  change chart_residueIso π z N hm hN
    (Ideal.Quotient.mk (closedPrime π z N) (AdjoinRoot.mk (relation π z N) X)) = X
  dsimp only [chart_residueIso]
  erw [RingEquiv.trans_apply,
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of]
  simp only [Polynomial.map_X]
  erw [RingEquiv.trans_apply,Ideal.quotEquivOfEq_mk,RingEquiv.quotientBot_mk]
  rfl

private theorem chartParameter_notMem_closedPrime [IsDomain S] (π z : S) (N : ℕ)
    (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    chartParameter π z N ∉ closedPrime π z N := by
  intro h
  have he := congrArg (chart_residueIso π z N hm hN)
    (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  rw [chart_residueIso_parameter,map_zero] at he
  exact Polynomial.X_ne_zero he

omit [IsLocalRing S] in
private theorem chart_relation (π z : S) (N : ℕ) :
    coefficientMap π z N π * chartParameter π z N = coefficientMap π z N (z ^ N) := by
  apply sub_eq_zero.mp
  have he := AdjoinRoot.eval₂_root (relation π z N)
  change (C π * X - C (z ^ N)).eval₂ (coefficientMap π z N) (chartParameter π z N) = 0 at he
  simpa only [eval₂_sub,eval₂_mul,eval₂_C,eval₂_X] using he

/-- The actual localization at the original closed-centre prime. The prime
and domain data in this type are derived from the original parameters. -/
abbrev localRing [IsDomain S] (π z : S) (_hπ : Prime π) (_hz : ¬ π ∣ z) (N : ℕ)
    (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :=
  letI : (closedPrime π z N).IsPrime := closedPrime_isPrime π z N hm hN
  Localization.AtPrime (closedPrime π z N)

private instance localRing_domain [IsDomain S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    IsDomain (localRing π z hπ hz N hm hN) := by
  let : IsDomain (chart π z N) := chart_isDomain π z hπ hz N
  let : (closedPrime π z N).IsPrime := closedPrime_isPrime π z N hm hN
  exact IsLocalization.isDomain_of_atPrime _ (closedPrime π z N)

/-- The literal original coefficient map into the constructed local ring. -/
def localCoefficientMap [IsDomain S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    S →+* localRing π z hπ hz N hm hN :=
  (algebraMap (chart π z N) _).comp (coefficientMap π z N)

/-- The original second parameter in the actual constructed local ring. -/
def localParameter [IsDomain S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    localRing π z hπ hz N hm hN := localCoefficientMap π z hπ hz N hm hN z

private theorem localRoot_unit [IsDomain S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    IsUnit (algebraMap (chart π z N) (localRing π z hπ hz N hm hN) (chartParameter π z N)) := by
  let : (closedPrime π z N).IsPrime := closedPrime_isPrime π z N hm hN
  apply (IsLocalization.AtPrime.isUnit_to_map_iff _ (closedPrime π z N) _).mpr
  exact chartParameter_notMem_closedPrime π z N hm hN

private theorem local_relation [IsDomain S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    localCoefficientMap π z hπ hz N hm hN π *
        algebraMap (chart π z N) (localRing π z hπ hz N hm hN) (chartParameter π z N) =
      localParameter π z hπ hz N hm hN ^ N := by
  dsimp only [localParameter,localCoefficientMap,RingHom.comp_apply]
  rw [← map_mul,chart_relation,map_pow,map_pow]

/-- The SAME original second parameter generates the genuine maximal ideal. -/
theorem local_maximalIdeal [IsDomain S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    maximalIdeal (localRing π z hπ hz N hm hN) =
      Ideal.span {localParameter π z hπ hz N hm hN} := by
  let V := localRing π z hπ hz N hm hN
  let : (closedPrime π z N).IsPrime := closedPrime_isPrime π z N hm hN
  have hd : localParameter π z hπ hz N hm hN ∣ localCoefficientMap π z hπ hz N hm hN π := by
    apply (localRoot_unit π z hπ hz N hm hN).dvd_mul_right.mp
    rw [local_relation]
    exact dvd_pow_self _ hN.ne'
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (closedPrime π z N) V]
  dsimp only [closedPrime]
  rw [hm,Ideal.map_span,Set.image_pair,Ideal.map_span,Set.image_pair]
  exact Ideal.span_pair_eq_span_right_iff_dvd.mpr hd

omit [IsLocalRing S] in
private theorem coefficientMap_injective [IsDomain S] (π z : S) (hπ : Prime π) (N : ℕ) :
    Function.Injective (coefficientMap π z N) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  have hd : (C π * X : S[X]).degree = 1 := degree_C_mul_X hπ.ne_zero
  dsimp only [relation]
  rw [degree_sub_C (by rw [hd]; exact zero_lt_one),hd]
  exact one_ne_zero

private theorem localParameter_ne_zero [IsDomain S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    localParameter π z hπ hz N hm hN ≠ 0 := by
  let : IsDomain (chart π z N) := chart_isDomain π z hπ hz N
  let : (closedPrime π z N).IsPrime := closedPrime_isPrime π z N hm hN
  have hinj := (IsLocalization.injective (localRing π z hπ hz N hm hN)
    (closedPrime π z N).primeCompl_le_nonZeroDivisors).comp (coefficientMap_injective π z hπ N)
  exact fun he => hz (by
    have hzero : algebraMap (chart π z N) (localRing π z hπ hz N hm hN)
        (coefficientMap π z N 0) = 0 := by simp only [map_zero]
    have hz0 : z = 0 := hinj (he.trans hzero.symm)
    rw [hz0]
    exact dvd_zero π)

/-- No DVR certificate is an input: actual Noetherianity and the internally
proved original principal maximal ideal construct the discrete valuation ring. -/
theorem localRing_isDVR [IsDomain S] [IsNoetherianRing S] (π z : S) (hπ : Prime π)
    (hz : ¬ π ∣ z) (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    IsDiscreteValuationRing (localRing π z hπ hz N hm hN) := by
  let V := localRing π z hπ hz N hm hN
  have hnot : ¬ IsField V := by
    intro h
    have he := IsLocalRing.isField_iff_maximalIdeal_eq.mp h
    rw [local_maximalIdeal π z hπ hz N hm hN,Ideal.span_singleton_eq_bot] at he
    exact localParameter_ne_zero π z hπ hz N hm hN he
  apply ((IsDiscreteValuationRing.TFAE V hnot).out 0 4).mpr
  exact ⟨localParameter π z hπ hz N hm hN,local_maximalIdeal π z hπ hz N hm hN⟩

private instance localRing_dvr [IsDomain S] [IsNoetherianRing S] (π z : S) (hπ : Prime π)
    (hz : ¬ π ∣ z) (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    IsDiscreteValuationRing (localRing π z hπ hz N hm hN) := localRing_isDVR π z hπ hz N hm hN

/-- The SAME original parameter is a true uniformizer of the constructed DVR. -/
theorem localParameter_irreducible [IsDomain S] [IsNoetherianRing S] (π z : S) (hπ : Prime π)
    (hz : ¬ π ∣ z) (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    Irreducible (localParameter π z hπ hz N hm hN) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr (local_maximalIdeal π z hπ hz N hm hN)

/-- The native additive valuation of this actual DVR gives the original
second parameter order one. -/
theorem parameter_addVal [IsDomain S] [IsNoetherianRing S] (π z : S) (hπ : Prime π)
    (hz : ¬ π ∣ z) (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    IsDiscreteValuationRing.addVal (localRing π z hπ hz N hm hN)
      (localParameter π z hπ hz N hm hN) = 1 :=
  IsDiscreteValuationRing.addVal_uniformizer (localParameter_irreducible π z hπ hz N hm hN)

/-- The literal original chart relation internally forces vertical order N. -/
theorem vertical_addVal [IsDomain S] [IsNoetherianRing S] (π z : S) (hπ : Prime π)
    (hz : ¬ π ∣ z) (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    IsDiscreteValuationRing.addVal (localRing π z hπ hz N hm hN)
      (localCoefficientMap π z hπ hz N hm hN π) = N := by
  have he := congrArg (IsDiscreteValuationRing.addVal (localRing π z hπ hz N hm hN))
    (local_relation π z hπ hz N hm hN)
  rw [IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (localRoot_unit π z hπ hz N hm hN),
    add_zero,IsDiscreteValuationRing.addVal_pow,parameter_addVal,nsmul_one] at he
  exact he

/-- The actual coefficient map has exactly the original closed centre. -/
theorem localCenter [IsDomain S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    (maximalIdeal (localRing π z hπ hz N hm hN)).comap
      (localCoefficientMap π z hπ hz N hm hN) = maximalIdeal S := by
  let : (closedPrime π z N).IsPrime := closedPrime_isPrime π z N hm hN
  ext x
  change localCoefficientMap π z hπ hz N hm hN x ∈ maximalIdeal _ ↔ x ∈ maximalIdeal S
  constructor
  · intro hx
    by_contra h
    exact IsLocalRing.notMem_maximalIdeal.mpr
      ((IsLocalRing.notMem_maximalIdeal.mp h).map
        (localCoefficientMap π z hπ hz N hm hN)) hx
  · intro hx
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (closedPrime π z N) _).mpr
      (Ideal.mem_map_of_mem (coefficientMap π z N) hx)

/-- The actual constructed local ring embeds into the SAME original fraction
field, by the original quotient evaluation and genuine localization lift. -/
def fractionEmbedding [IsDomain S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    localRing π z hπ hz N hm hN →+* FractionRing S := by
  let : (closedPrime π z N).IsPrime := closedPrime_isPrime π z N hm hN
  apply IsLocalization.lift (M := (closedPrime π z N).primeCompl)
    (g := chartFractionMap π z hπ N)
  intro y
  apply isUnit_iff_ne_zero.mpr
  apply (map_ne_zero_iff _ (chartFractionMap_injective π z hπ hz N)).mpr
  intro hy
  exact y.property (hy ▸ (closedPrime π z N).zero_mem)

/-- The actual fraction embedding is injective, without a comparison certificate. -/
theorem fractionEmbedding_injective [IsDomain S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    Function.Injective (fractionEmbedding π z hπ hz N hm hN) := by
  let : IsDomain (chart π z N) := chart_isDomain π z hπ hz N
  let : (closedPrime π z N).IsPrime := closedPrime_isPrime π z N hm hN
  dsimp only [fractionEmbedding]
  apply (IsLocalization.lift_injective_iff _).mpr
  intro a b
  exact ⟨fun h => congrArg _ (IsLocalization.injective (localRing π z hπ hz N hm hN)
      (closedPrime π z N).primeCompl_le_nonZeroDivisors h),
    fun h => congrArg _ (chartFractionMap_injective π z hπ hz N h)⟩

/-- EVERY original coefficient retains its literal original fraction-field value. -/
theorem fractionEmbedding_coefficient [IsDomain S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) (s : S) :
    fractionEmbedding π z hπ hz N hm hN (localCoefficientMap π z hπ hz N hm hN s) =
      algebraMap S (FractionRing S) s := by
  dsimp only [localCoefficientMap,RingHom.comp_apply,fractionEmbedding]
  rw [IsLocalization.lift_eq]
  exact chartFractionMap_coefficient π z hπ N s

/-- The same actual map makes the ORIGINAL fraction field the fraction ring
of the internally constructed DVR. -/
theorem localFractionRing [IsDomain S] (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (N : ℕ) (hm : maximalIdeal S = Ideal.span {π,z}) (hN : 0 < N) :
    letI : Algebra (localRing π z hπ hz N hm hN) (FractionRing S) :=
      (fractionEmbedding π z hπ hz N hm hN).toAlgebra
    IsFractionRing (localRing π z hπ hz N hm hN) (FractionRing S) := by
  let V := localRing π z hπ hz N hm hN
  let : Algebra V (FractionRing S) := (fractionEmbedding π z hπ hz N hm hN).toAlgebra
  let : FaithfulSMul V (FractionRing S) := (faithfulSMul_iff_algebraMap_injective V _).mpr
    (fractionEmbedding_injective π z hπ hz N hm hN)
  apply IsFractionRing.of_field V (FractionRing S)
  intro x
  obtain ⟨a,b,_,he⟩ := IsFractionRing.div_surjective S x
  refine ⟨localCoefficientMap π z hπ hz N hm hN a,localCoefficientMap π z hπ hz N hm hN b,?_⟩
  change x = fractionEmbedding π z hπ hz N hm hN (localCoefficientMap π z hπ hz N hm hN a) /
    fractionEmbedding π z hπ hz N hm hN (localCoefficientMap π z hπ hz N hm hN b)
  rw [fractionEmbedding_coefficient,fractionEmbedding_coefficient]
  exact he.symm

end ClosedCentre

end EnvelopeProperty.GaussRegularSurfaceValuations
