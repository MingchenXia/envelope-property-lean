/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.NormForm
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Genuine norm-form identities over finite and infinite coefficient fields

Coefficient base change, algebra equivalences and product decomposition preserve
entire determinant norm polynomials. The weighted identity over a complete
ultrametric field uses the actual splitting algebra over its algebraic closure.
Only that algebraic closure is used for polynomial interpolation, so the complete
base field may be finite and trivially normed.
-/

open scoped NNReal TensorProduct
open MvPolynomial
noncomputable section
namespace EnvelopeProperty

/-- The actual determinant norm form commutes with coefficient base change. -/
theorem map_normForm_baseChange {B A K σ : Type*} [CommRing B] [CommRing A]
    [Algebra B A] [Module.Free B A] [Module.Finite B A] [CommRing K] [Algebra B K]
    [Fintype σ] (b : σ → A) :
    map (algebraMap B K) (normForm B b) =
      normForm K (fun j => (1 : K) ⊗ₜ[B] b j) := by
  classical
  let e := Module.Free.chooseBasis B A
  let P := Algebra.TensorProduct.basis (MvPolynomial σ B) e
  let Q := Algebra.TensorProduct.basis K e
  let S := Algebra.TensorProduct.basis (MvPolynomial σ K) Q
  rw [normForm, normForm, Algebra.norm_eq_matrix_det P, Algebra.norm_eq_matrix_det S,
    RingHom.map_det]
  congr 1
  ext a c
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
    Finset.sum_mul, Finset.sum_mul]
  simp [Algebra.TensorProduct.tmul_mul_tmul, P, Q, S, map_sum]

/-- Actual norm forms respect algebra equivalences over arbitrary coefficient rings. -/
theorem normForm_algEquiv {R E F σ : Type*} [CommRing R] [CommRing E] [CommRing F]
    [Algebra R E] [Algebra R F] [Fintype σ] (e : E ≃ₐ[R] F) (b : σ → E) :
    normForm R (fun j => e (b j)) = normForm R b := by
  classical
  let g : (MvPolynomial σ R ⊗[R] E) ≃ₐ[MvPolynomial σ R]
      (MvPolynomial σ R ⊗[R] F) := Algebra.TensorProduct.congr .refl e
  have h : g (∑ j, (X j : MvPolynomial σ R) ⊗ₜ[R] b j) =
      ∑ j, (X j : MvPolynomial σ R) ⊗ₜ[R] e (b j) := by
    simp [g]
  rw [normForm, ← h, Algebra.norm_eq_of_algEquiv g]
  rfl

/-- A genuine product decomposition factors the entire determinant norm polynomial. -/
theorem normForm_eq_prod_of_algEquiv {R E σ ι : Type*} [CommRing R] [CommRing E]
    [Algebra R E] [Fintype σ] [Fintype ι] {L : ι → Type*}
    [∀ i, CommRing (L i)] [∀ i, Algebra R (L i)]
    [∀ i, Module.Free R (L i)] [∀ i, Module.Finite R (L i)]
    (e : E ≃ₐ[R] ∀ i, L i) (b : σ → E) :
    normForm R b = ∏ i, normForm R (fun j => e (b j) i) := by
  classical
  rw [← normForm_algEquiv e]
  let g := Algebra.TensorProduct.piRight R (MvPolynomial σ R) (MvPolynomial σ R) L
  rw [normForm, ← Algebra.norm_eq_of_algEquiv g, algebraNorm_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_sum, Finset.sum_apply]
  rfl

/-- Without requiring the ground field to be infinite, the actual norm form of a
finite separable field extension has its usual weighted coefficient norm. -/
theorem wgaussValuation_normForm_field {H L σ : Type*} [NormedField H]
    [CompleteSpace H] [IsUltrametricDist H] [Field L] [Algebra H L]
    [FiniteDimensional H L] [Algebra.IsSeparable H L] [Fintype σ]
    (w : Valuation L ℝ≥0) (hw : ∀ c : H, w (algebraMap H L c) = ‖c‖₊)
    (b : σ → L) (r : σ → ℝ≥0) :
    wgaussValuation NormedField.valuation r (normForm H b) =
      (Finset.univ.sup fun j => w (b j) * r j) ^ Module.finrank H L := by
  classical
  let Ω := AlgebraicClosure H
  let : Algebra.FormallyEtale H L := Algebra.FormallyEtale.of_isSeparable H L
  have : IsArtinianRing (Ω ⊗[H] L) := IsArtinianRing.of_finite Ω _
  let : Fintype (PrimeSpectrum (Ω ⊗[H] L)) := Fintype.ofFinite _
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω (Ω ⊗[H] L)
  obtain ⟨wΩ, hwΩ⟩ := Valuation.exists_extends_norm (K := H) (L := Ω)
  let τ : PrimeSpectrum (Ω ⊗[H] L) → L →ₐ[H] Ω := fun m =>
    (((Pi.evalAlgHom Ω (fun _ : PrimeSpectrum (Ω ⊗[H] L) => Ω) m).comp e.toAlgHom).restrictScalars H).comp Algebra.TensorProduct.includeRight
  have hτ : ∀ m a, wΩ (τ m a) = w a := by
    intro m a
    have he := Valuation.eq_of_extends_norm (K := H)
      (v := wΩ.comap (τ m).toRingHom) (w := w)
      (fun c => by
        change wΩ (τ m (algebraMap H L c)) = ‖c‖₊
        rw [AlgHom.commutes, hwΩ]) hw
    exact congrArg (fun v : Valuation L ℝ≥0 => v a) he
  have hmap : map (algebraMap H Ω) (normForm H b) =
      ∏ m : PrimeSpectrum (Ω ⊗[H] L), ∑ j, C (τ m (b j)) * X j := by
    apply MvPolynomial.funext
    intro t
    rw [eval_map_normForm, ← Algebra.norm_eq_of_algEquiv e, algebraNorm_pi, map_prod]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [map_sum, Finset.sum_apply, Algebra.norm_self]
    simp only [MonoidHom.id_apply, map_sum, map_mul, eval_C, eval_X]
    refine Finset.sum_congr rfl fun j _ => ?_
    change e (t j • ((1 : Ω) ⊗ₜ[H] b j)) m = e ((1 : Ω) ⊗ₜ[H] b j) m * t j
    rw [map_smul, Pi.smul_apply, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  have hcard : Fintype.card (PrimeSpectrum (Ω ⊗[H] L)) = Module.finrank H L := by
    rw [← Module.finrank_baseChange (R := Ω), e.toLinearEquiv.finrank_eq,
      Module.finrank_pi_fintype]
    simp
  rw [← wgaussValuation_map NormedField.valuation r (algebraMap H Ω) wΩ
    (fun c => by rw [hwΩ, NormedField.valuation_apply]), hmap, map_prod]
  calc
    (∏ m : PrimeSpectrum (Ω ⊗[H] L),
      wgaussValuation wΩ r (∑ j, C (τ m (b j)) * X j)) =
        ∏ _m : PrimeSpectrum (Ω ⊗[H] L), Finset.univ.sup fun j => w (b j) * r j := by
      refine Finset.prod_congr rfl fun m _ => ?_
      rw [wgaussValuation_linear]
      simp only [hτ]
    _ = (Finset.univ.sup fun j => w (b j) * r j) ^ Module.finrank H L := by
      rw [Finset.prod_const, Finset.card_univ, hcard]

/-- The complete weighted norm-form identity for a finite product of separable
fields; no infinitude of H is needed for this actual determinant polynomial. -/
theorem wgaussValuation_normForm_of_algEquiv {H E σ ι : Type*} [NormedField H]
    [CompleteSpace H] [IsUltrametricDist H] [CommRing E] [Algebra H E]
    [Fintype σ] [Fintype ι] {L : ι → Type*} [∀ i, Field (L i)]
    [∀ i, Algebra H (L i)] [∀ i, FiniteDimensional H (L i)]
    [∀ i, Algebra.IsSeparable H (L i)] (e : E ≃ₐ[H] ∀ i, L i)
    (w : ∀ i, Valuation (L i) ℝ≥0)
    (hw : ∀ i (c : H), w i (algebraMap H (L i) c) = ‖c‖₊)
    (b : σ → E) (r : σ → ℝ≥0) :
    wgaussValuation NormedField.valuation r (normForm H b) =
      ∏ i, (Finset.univ.sup fun j => w i (e (b j) i) * r j) ^ Module.finrank H (L i) := by
  rw [normForm_eq_prod_of_algEquiv e, map_prod]
  exact Finset.prod_congr rfl fun i _ => wgaussValuation_normForm_field (w i) (hw i) _ r

end EnvelopeProperty
