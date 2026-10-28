/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.NormFormGeneral
import EnvelopeProperty.Berkovich.ArtinianLocalFactors
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Genuine finite-algebra local multiplicities under field extension

The actual Artinian local-factor idempotents isolate a factor through the
entire determinant polynomial of T e + U(1-e). Coefficient base change and
polynomial degree prove conservation of each full local dimension under
arbitrary field extension, retaining nilpotents and inseparability.
Arbitrary commutative-monoid function products regroup by actual contraction.
No valuation, completeness or assumed product decomposition is required.
-/

open scoped TensorProduct
open MvPolynomial Classical
noncomputable section
namespace EnvelopeProperty

theorem normForm_algebraMap {R E σ : Type*} [CommRing R] [CommRing E] [Algebra R E]
    [Module.Free R E] [Module.Finite R E] [Fintype σ] (b : σ → R) :
    normForm R (fun j => algebraMap R E (b j)) =
      (∑ j, C (b j) * X j) ^ Module.finrank R E := by
  classical
  nontriviality R
  let P := MvPolynomial σ R
  have h : (∑ j, (X j : P) ⊗ₜ[R] algebraMap R E (b j)) =
      algebraMap P (P ⊗[R] E) (∑ j, C (b j) * X j) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (X j : P) ⊗ₜ[R] algebraMap R E (b j) =
      (C (b j) * X j) ⊗ₜ[R] (1 : E)
    rw [Algebra.algebraMap_eq_smul_one, ← smul_eq_C_mul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rw [normForm, h, Algebra.norm_algebraMap, Module.finrank_baseChange]

variable (H E : Type*) [Field H] [CommRing E] [Algebra H E] [FiniteDimensional H E]

def finiteAlgebraIdempotent (m : MaximalSpectrum E) : E := by
  classical
  exact (finiteAlgebraLocalizationEquiv H E).symm (Pi.single m 1)

theorem finiteAlgebraIdempotent_algebraMap (m p : MaximalSpectrum E) :
    algebraMap E (Localization.AtPrime p.asIdeal) (finiteAlgebraIdempotent H E m) =
      if p = m then 1 else 0 := by
  classical
  rw [← finiteAlgebraLocalizationEquiv_apply H E _ p]
  change finiteAlgebraLocalizationEquiv H E
    ((finiteAlgebraLocalizationEquiv H E).symm (Pi.single m 1)) p = _
  rw [AlgEquiv.apply_symm_apply]
  by_cases hp : p = m
  · subst p
    simp
  · simp [hp]

theorem finiteAlgebraIdempotent_isIdempotent (m : MaximalSpectrum E) :
    IsIdempotentElem (finiteAlgebraIdempotent H E m) := by
  classical
  change finiteAlgebraIdempotent H E m * finiteAlgebraIdempotent H E m = _
  apply (finiteAlgebraLocalizationEquiv H E).injective
  ext p
  simp [finiteAlgebraLocalizationEquiv_apply,
    finiteAlgebraIdempotent_algebraMap]

theorem finiteAlgebraIdempotent_mem_iff (m p : MaximalSpectrum E) :
    finiteAlgebraIdempotent H E m ∈ p.asIdeal ↔ p ≠ m := by
  classical
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime p.asIdeal) p.asIdeal]
  rw [finiteAlgebraIdempotent_algebraMap]
  by_cases hp : p = m <;> simp [hp]

theorem localization_idempotent_algebraMap {R : Type*} [CommRing R]
    (a : R) (ha : IsIdempotentElem a) (p : MaximalSpectrum R) :
    algebraMap R (Localization.AtPrime p.asIdeal) a = if a ∉ p.asIdeal then 1 else 0 := by
  classical
  let b := algebraMap R (Localization.AtPrime p.asIdeal) a
  have hb : b * b = b := by
    rw [← map_mul]
    exact congrArg (algebraMap R (Localization.AtPrime p.asIdeal)) ha
  by_cases hp : a ∉ p.asIdeal
  · rw [if_pos hp]
    have hu : IsUnit b := (IsLocalization.AtPrime.isUnit_to_map_iff
      (Localization.AtPrime p.asIdeal) p.asIdeal a).2 hp
    exact hu.mul_left_cancel (by simpa using hb)
  · rw [if_neg hp]
    have hn : ¬IsUnit b := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff
        (Localization.AtPrime p.asIdeal) p.asIdeal a]
      exact hp
    have hu : IsUnit (1 - b) :=
      (IsLocalRing.isUnit_or_isUnit_one_sub_self b).resolve_left hn
    have hzero : b * (1 - b) = 0 * (1 - b) := by
      simp only [mul_sub, mul_one, zero_mul, hb, sub_self]
    exact hu.mul_right_cancel hzero

theorem normForm_idempotent {H E : Type*} [Field H] [CommRing E] [Algebra H E]
    [FiniteDimensional H E] (a : E) (ha : IsIdempotentElem a) :
    normForm H (fun j : Bool => if j then a else 1 - a) =
      ∏ m ∈ (finiteAlgebraMaximalSpectrumFinite H E).toFinset,
        (if a ∉ m.asIdeal then (X true : MvPolynomial Bool H) else X false) ^
          Module.finrank H (Localization.AtPrime m.asIdeal) := by
  classical
  let : IsArtinianRing E := IsArtinianRing.of_finite H E
  let : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  have hf : (finiteAlgebraMaximalSpectrumFinite H E).toFinset = Finset.univ := by
    ext m
    simp
  rw [hf, normForm_eq_prod_of_algEquiv (finiteAlgebraLocalizationEquiv H E)]
  apply Finset.prod_congr rfl
  intro m _
  have h := localization_idempotent_algebraMap a ha m
  have hb : (fun j : Bool => finiteAlgebraLocalizationEquiv H E (if j then a else 1 - a) m) =
      fun j => algebraMap H (Localization.AtPrime m.asIdeal)
        (if j then (if a ∉ m.asIdeal then 1 else 0) else
          1 - (if a ∉ m.asIdeal then 1 else 0)) := by
    funext j
    cases j <;> simp [finiteAlgebraLocalizationEquiv_apply, h]
  rw [hb, normForm_algebraMap]
  by_cases hp : a ∉ m.asIdeal <;> simp [hp]

theorem degreeOf_map_normForm_idempotent {H K E : Type*} [Field H] [Field K]
    [Algebra H K] [CommRing E] [Algebra H E] [FiniteDimensional H E]
    (a : E) (ha : IsIdempotentElem a) :
    degreeOf true (map (algebraMap H K)
      (normForm H (fun j : Bool => if j then a else 1 - a))) =
      ∑ m ∈ (finiteAlgebraMaximalSpectrumFinite H E).toFinset,
        if a ∉ m.asIdeal then Module.finrank H (Localization.AtPrime m.asIdeal) else 0 := by
  classical
  rw [normForm_idempotent (H := H) a ha, map_prod]
  simp only [map_pow]
  have hpoly (m : MaximalSpectrum E) :
      map (algebraMap H K) (if a ∉ m.asIdeal then (X true : MvPolynomial Bool H) else X false) =
        if a ∉ m.asIdeal then (X true : MvPolynomial Bool K) else X false := by
    split_ifs <;> simp
  simp_rw [hpoly]
  rw [degreeOf_prod_eq]
  · apply Finset.sum_congr rfl
    intro m _
    by_cases hm : a ∉ m.asIdeal <;>
      simp [hm, degreeOf_pow_eq, X_ne_zero, degreeOf_X]
  · intro m _
    split_ifs <;> exact pow_ne_zero _ (X_ne_zero _)

theorem degreeOf_normForm_idempotent {H E : Type*} [Field H]
    [CommRing E] [Algebra H E] [FiniteDimensional H E]
    (a : E) (ha : IsIdempotentElem a) :
    degreeOf true (normForm H (fun j : Bool => if j then a else 1 - a)) =
      ∑ m ∈ (finiteAlgebraMaximalSpectrumFinite H E).toFinset,
        if a ∉ m.asIdeal then Module.finrank H (Localization.AtPrime m.asIdeal) else 0 := by
  simpa only [Algebra.algebraMap_self, MvPolynomial.map_id] using
    degreeOf_map_normForm_idempotent (H := H) (K := H) a ha

def finiteAlgebraMaximalComap {H K E : Type*} [Field H] [Field K]
    [Algebra H K] [CommRing E] [Algebra H E] [FiniteDimensional H E]
    (p : MaximalSpectrum (K ⊗[H] E)) : MaximalSpectrum E := by
  let : IsArtinianRing E := IsArtinianRing.of_finite H E
  exact ⟨Ideal.comap (Algebra.TensorProduct.includeRight : E →ₐ[H] K ⊗[H] E) p.asIdeal,
    IsArtinianRing.isMaximal_of_isPrime _⟩

theorem finiteAlgebraIdempotent_baseChange_not_mem_iff {H K E : Type*} [Field H] [Field K]
    [Algebra H K] [CommRing E] [Algebra H E] [FiniteDimensional H E]
    (m : MaximalSpectrum E) (p : MaximalSpectrum (K ⊗[H] E)) :
    (1 : K) ⊗ₜ[H] finiteAlgebraIdempotent H E m ∉ p.asIdeal ↔
      finiteAlgebraMaximalComap p = m := by
  change finiteAlgebraIdempotent H E m ∉ (finiteAlgebraMaximalComap p).asIdeal ↔ _
  simp only [finiteAlgebraIdempotent_mem_iff, not_not]

theorem sum_localFinrank_baseChange {H K E : Type*} [Field H] [Field K]
    [Algebra H K] [CommRing E] [Algebra H E] [FiniteDimensional H E]
    (m : MaximalSpectrum E) :
    (∑ p ∈ (finiteAlgebraMaximalSpectrumFinite K (K ⊗[H] E)).toFinset,
      if finiteAlgebraMaximalComap p = m then
        Module.finrank K (Localization.AtPrime p.asIdeal) else 0) =
      Module.finrank H (Localization.AtPrime m.asIdeal) := by
  classical
  let a := finiteAlgebraIdempotent H E m
  have ha : IsIdempotentElem a := finiteAlgebraIdempotent_isIdempotent H E m
  have ha' : IsIdempotentElem ((1 : K) ⊗ₜ[H] a) := by
    change ((Algebra.TensorProduct.includeRight : E →ₐ[H] K ⊗[H] E) a) *
      ((Algebra.TensorProduct.includeRight : E →ₐ[H] K ⊗[H] E) a) = _
    rw [← map_mul]
    exact congrArg (Algebra.TensorProduct.includeRight : E →ₐ[H] K ⊗[H] E) ha
  have hb : (fun j : Bool => (1 : K) ⊗ₜ[H] (if j then a else 1 - a)) =
      fun j => if j then (1 : K) ⊗ₜ[H] a else 1 - (1 : K) ⊗ₜ[H] a := by
    funext j
    cases j <;> simp [TensorProduct.tmul_sub, ← Algebra.TensorProduct.one_def]
  have h := congrArg (degreeOf true) (map_normForm_baseChange
    (B := H) (K := K) (fun j : Bool => if j then a else 1 - a))
  rw [degreeOf_map_normForm_idempotent (H := H) (K := K) a ha, hb,
    degreeOf_normForm_idempotent (H := K) _ ha'] at h
  simp only [a, finiteAlgebraIdempotent_baseChange_not_mem_iff] at h
  rw [← h]
  simp only [a, finiteAlgebraIdempotent_mem_iff, not_not]
  simp

theorem finiteAlgebraWeightedProduct_baseChange {H K E M : Type*} [Field H] [Field K]
    [Algebra H K] [CommRing E] [Algebra H E] [FiniteDimensional H E]
    [CommMonoid M] (f : MaximalSpectrum E → M) :
    (∏ p ∈ (finiteAlgebraMaximalSpectrumFinite K (K ⊗[H] E)).toFinset,
      f (finiteAlgebraMaximalComap p) ^ Module.finrank K (Localization.AtPrime p.asIdeal)) =
    ∏ m ∈ (finiteAlgebraMaximalSpectrumFinite H E).toFinset,
      f m ^ Module.finrank H (Localization.AtPrime m.asIdeal) := by
  classical
  let : IsArtinianRing E := IsArtinianRing.of_finite H E
  let : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  let s := (finiteAlgebraMaximalSpectrumFinite K (K ⊗[H] E)).toFinset
  have hf : (finiteAlgebraMaximalSpectrumFinite H E).toFinset = Finset.univ := by
    ext m
    simp
  rw [hf, ← Finset.prod_fiberwise s (fun p => finiteAlgebraMaximalComap p)]
  apply Finset.prod_congr rfl
  intro m _
  have hp : (∏ p ∈ s.filter (fun p => finiteAlgebraMaximalComap p = m),
      f (finiteAlgebraMaximalComap p) ^ Module.finrank K (Localization.AtPrime p.asIdeal)) =
    ∏ p ∈ s.filter (fun p => finiteAlgebraMaximalComap p = m),
      f m ^ Module.finrank K (Localization.AtPrime p.asIdeal) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  rw [hp, Finset.prod_pow_eq_pow_sum]
  congr 1
  simpa only [Finset.sum_filter] using sum_localFinrank_baseChange (K := K) m

def maximalSpectrumAlgEquiv {R E F : Type*} [CommRing R] [CommRing E] [CommRing F]
    [Algebra R E] [Algebra R F] (e : E ≃ₐ[R] F) : MaximalSpectrum F ≃ MaximalSpectrum E where
  toFun p := ⟨p.asIdeal.comap e.toRingHom, p.isMaximal.comap_bijective e e.bijective⟩
  invFun m := ⟨m.asIdeal.comap e.symm.toRingHom, m.isMaximal.comap_bijective e.symm e.symm.bijective⟩
  left_inv p := by
    ext a
    simp [Ideal.mem_comap]
  right_inv m := by
    ext a
    simp [Ideal.mem_comap]

def maximalLocalizationAlgEquiv {R E F : Type*} [CommRing R] [CommRing E] [CommRing F]
    [Algebra R E] [Algebra R F] (e : E ≃ₐ[R] F) (p : MaximalSpectrum F) :
    Localization.AtPrime (maximalSpectrumAlgEquiv e p).asIdeal ≃ₐ[R]
      Localization.AtPrime p.asIdeal := by
  have h : Submonoid.map e.toMonoidHom (maximalSpectrumAlgEquiv e p).asIdeal.primeCompl =
      p.asIdeal.primeCompl := by
    ext f
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hf
      refine ⟨e.symm f, ?_, e.apply_symm_apply f⟩
      change e (e.symm f) ∉ p.asIdeal
      simpa using hf
  exact IsLocalization.algEquivOfAlgEquiv _ _ e h

theorem finrank_maximalLocalizationAlgEquiv {H E F : Type*} [Field H]
    [CommRing E] [CommRing F] [Algebra H E] [Algebra H F]
    (e : E ≃ₐ[H] F) (p : MaximalSpectrum F) :
    Module.finrank H (Localization.AtPrime p.asIdeal) =
      Module.finrank H (Localization.AtPrime (maximalSpectrumAlgEquiv e p).asIdeal) :=
  (maximalLocalizationAlgEquiv e p).toLinearEquiv.finrank_eq.symm

end EnvelopeProperty
