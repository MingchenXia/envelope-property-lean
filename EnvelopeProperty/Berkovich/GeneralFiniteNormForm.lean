/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.ArtinianLocalFactors
import EnvelopeProperty.Berkovich.LocalNormForm
import EnvelopeProperty.Berkovich.ValuationAlgebraNorm

/-!
# Weighted determinant norm forms for arbitrary finite algebras

The decomposition of a finite algebra into its Artinian localizations, after base change to an
algebraic closure, keeps track of the lengths of the local factors and of the inseparable residue
degrees. Equality of determinant polynomials, followed by uniqueness of the extension of the norm
of a complete field, gives the weighted norm identities without separability or infinitude
assumptions. The local splitting hypothesis of
`wgaussValuation_normForm_local_of_algClosureSplit` is supplied by the localization product.
-/

open scoped NNReal TensorProduct
open MvPolynomial
noncomputable section
namespace EnvelopeProperty

/-- A splitting into local factors over an algebraic closure gives the weighted norm form of a
finite local algebra over a complete field. -/
theorem wgaussValuation_normForm_local_of_algClosureSplit {H E σ ι : Type*}
    [NormedField H] [CompleteSpace H] [IsUltrametricDist H] [CommRing E] [Algebra H E]
    [FiniteDimensional H E] [IsLocalRing E] [Fintype σ] [Fintype ι]
    {L : ι → Type*} [∀ i, CommRing (L i)] [∀ i, Algebra (AlgebraicClosure H) (L i)]
    [∀ i, FiniteDimensional (AlgebraicClosure H) (L i)] [∀ i, IsLocalRing (L i)]
    (e : (AlgebraicClosure H ⊗[H] E) ≃ₐ[AlgebraicClosure H] ∀ i, L i)
    (w : Valuation (IsLocalRing.ResidueField E) ℝ≥0)
    (hw : ∀ c : H, w (algebraMap H (IsLocalRing.ResidueField E) c) = ‖c‖₊)
    (b : σ → E) (r : σ → ℝ≥0) :
    wgaussValuation NormedField.valuation r (normForm H b) =
      (Finset.univ.sup fun j => w (IsLocalRing.residue E (b j)) * r j) ^
        ((Module.length E E).toNat * Module.finrank H (IsLocalRing.ResidueField E)) := by
  classical
  let Ω := AlgebraicClosure H
  have : IsArtinianRing E := IsArtinianRing.of_finite H E
  obtain ⟨wΩ, hwΩ⟩ := Valuation.exists_extends_norm (K := H) (L := Ω)
  let φ : ∀ i, E →+* Ω := fun i =>
    (localResidueScalar (K := Ω) (E := L i)).toRingHom.comp
      (((Pi.evalRingHom L i).comp e.toRingHom).comp
        (Algebra.TensorProduct.includeRight : E →ₐ[H] Ω ⊗[H] E).toRingHom)
  have hφ : ∀ i (c : H), φ i (algebraMap H E c) = algebraMap H Ω c := by
    intro i c
    change localResidueScalar (e (Algebra.TensorProduct.includeRight (algebraMap H E c)) i) = _
    rw [Algebra.TensorProduct.includeRight.commutes,
      IsScalarTower.algebraMap_apply H Ω (Ω ⊗[H] E), e.commutes]
    change localResidueScalar (algebraMap Ω (L i) (algebraMap H Ω c)) = algebraMap H Ω c
    rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  have hker : ∀ i, RingHom.ker (φ i) = IsLocalRing.maximalIdeal E := fun i =>
    IsLocalRing.eq_maximalIdeal ((IsArtinianRing.isPrime_iff_isMaximal _).mp
      (RingHom.ker_isPrime (φ i)))
  let ψ : ∀ i, IsLocalRing.ResidueField E →+* Ω := fun i =>
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal E) (φ i) (fun a ha => by
      rw [← hker i, RingHom.mem_ker] at ha
      exact ha)
  have hψ : ∀ i a, ψ i (IsLocalRing.residue E a) = φ i a := fun _ _ => rfl
  have hψc : ∀ i (c : H), ψ i (algebraMap H (IsLocalRing.ResidueField E) c) = algebraMap H Ω c := by
    intro i c
    rw [IsScalarTower.algebraMap_apply H E (IsLocalRing.ResidueField E),
      IsLocalRing.ResidueField.algebraMap_eq, hψ, hφ]
  have hval : ∀ i a, wΩ (φ i a) = w (IsLocalRing.residue E a) := by
    intro i a
    have heq := Valuation.eq_of_extends_norm
      (v := wΩ.comap (ψ i)) (w := w)
      (fun c => by rw [Valuation.comap_apply, hψc, hwΩ]) hw
    have h := congrArg (fun v : Valuation (IsLocalRing.ResidueField E) ℝ≥0 =>
      v (IsLocalRing.residue E a)) heq
    simpa only [Valuation.comap_apply, hψ] using h
  have hdeg : ∑ i, (Module.length (L i) (L i)).toNat = Module.finrank H E := by
    simp only [← finrank_eq_localLength (K := Ω)]
    rw [← Module.finrank_pi_fintype, ← e.toLinearEquiv.finrank_eq, Module.finrank_baseChange]
  rw [← wgaussValuation_map NormedField.valuation r (algebraMap H Ω) wΩ
    (fun c => by rw [hwΩ, NormedField.valuation_apply]), map_normForm_baseChange,
    normForm_eq_prod_of_algEquiv e, map_prod]
  calc
    (∏ i, wgaussValuation wΩ r (normForm Ω
      (fun j => e ((1 : Ω) ⊗ₜ[H] b j) i))) =
        ∏ i, (Finset.univ.sup fun j => w (IsLocalRing.residue E (b j)) * r j) ^
          (Module.length (L i) (L i)).toNat := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [wgaussValuation_normForm_of_local_algClosed]
      congr 1
      refine Finset.sup_congr rfl fun j _ => ?_
      exact congrArg (fun v : ℝ≥0 => v * r j) (hval i (b j))
    _ = (Finset.univ.sup fun j => w (IsLocalRing.residue E (b j)) * r j) ^
        ((Module.length E E).toNat * Module.finrank H (IsLocalRing.ResidueField E)) := by
      rw [Finset.prod_pow_eq_pow_sum, hdeg, finrank_eq_length_mul_residue_finrank]

/-- The weighted norm form of a finite local algebra over a complete ultrametric field, with
exponent the length times the residue degree. -/
theorem wgaussValuation_normForm_of_local {H E σ : Type*} [NormedField H]
    [CompleteSpace H] [IsUltrametricDist H] [CommRing E] [Algebra H E]
    [FiniteDimensional H E] [IsLocalRing E] [Fintype σ]
    (w : Valuation (IsLocalRing.ResidueField E) ℝ≥0)
    (hw : ∀ c : H, w (algebraMap H (IsLocalRing.ResidueField E) c) = ‖c‖₊)
    (b : σ → E) (r : σ → ℝ≥0) :
    wgaussValuation NormedField.valuation r (normForm H b) =
      (Finset.univ.sup fun j => w (IsLocalRing.residue E (b j)) * r j) ^
        ((Module.length E E).toNat * Module.finrank H (IsLocalRing.ResidueField E)) := by
  classical
  let Ω := AlgebraicClosure H
  let T := Ω ⊗[H] E
  have : IsArtinianRing T := IsArtinianRing.of_finite Ω _
  let : Fintype (MaximalSpectrum T) := Fintype.ofFinite _
  exact wgaussValuation_normForm_local_of_algClosureSplit
    (finiteAlgebraLocalizationEquiv Ω T) w hw b r

/-- The weighted norm form of a finite product of finite local algebras, with the length and
residue degree of each factor as exponents. -/
theorem wgaussValuation_normForm_of_localAlgEquiv {H E σ ι : Type*} [NormedField H]
    [CompleteSpace H] [IsUltrametricDist H] [CommRing E] [Algebra H E]
    [Fintype σ] [Fintype ι] {L : ι → Type*} [∀ i, CommRing (L i)] [∀ i, Algebra H (L i)]
    [∀ i, FiniteDimensional H (L i)] [∀ i, IsLocalRing (L i)]
    (e : E ≃ₐ[H] ∀ i, L i) (w : ∀ i, Valuation (IsLocalRing.ResidueField (L i)) ℝ≥0)
    (hw : ∀ i (c : H), w i (algebraMap H (IsLocalRing.ResidueField (L i)) c) = ‖c‖₊)
    (b : σ → E) (r : σ → ℝ≥0) :
    wgaussValuation NormedField.valuation r (normForm H b) =
      ∏ i, (Finset.univ.sup fun j => w i (IsLocalRing.residue (L i) (e (b j) i)) * r j) ^
        ((Module.length (L i) (L i)).toNat * Module.finrank H (IsLocalRing.ResidueField (L i))) := by
  rw [normForm_eq_prod_of_algEquiv e, map_prod]
  exact Finset.prod_congr rfl fun i _ => wgaussValuation_normForm_of_local (w i) (hw i) _ r

/-- The weighted norm form of a finite algebra over a complete ultrametric field, from its
decomposition into localizations at maximal ideals; no étaleness is assumed. -/
theorem wgaussValuation_normForm_of_finite {H E σ : Type*} [NormedField H]
    [CompleteSpace H] [IsUltrametricDist H] [CommRing E] [Algebra H E]
    [FiniteDimensional H E] [Fintype σ]
    (w : ∀ m : MaximalSpectrum E, Valuation m.asIdeal.ResidueField ℝ≥0)
    (hw : ∀ m (c : H), w m (algebraMap H m.asIdeal.ResidueField c) = ‖c‖₊)
    (b : σ → E) (r : σ → ℝ≥0) :
    wgaussValuation NormedField.valuation r (normForm H b) =
      ∏ m ∈ (finiteAlgebraMaximalSpectrumFinite H E).toFinset,
        (Finset.univ.sup fun j => w m (algebraMap E m.asIdeal.ResidueField (b j)) * r j) ^
          ((Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal)).toNat *
            Module.finrank H m.asIdeal.ResidueField) := by
  classical
  have : IsArtinianRing E := IsArtinianRing.of_finite H E
  let : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  have hf : (finiteAlgebraMaximalSpectrumFinite H E).toFinset = Finset.univ := by
    ext m
    simp
  rw [hf, wgaussValuation_normForm_of_localAlgEquiv (finiteAlgebraLocalizationEquiv H E) w hw]
  refine Finset.prod_congr rfl fun m _ => ?_
  simp only [finiteAlgebraLocalizationEquiv_apply]
  rfl

end EnvelopeProperty
