/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.NormIdentity

/-!
# Norm forms and their genuine base-change identities

Norm forms and scalar algebra norms commute with base change for any finite
free algebra over a commutative ring. The statements and proofs of normForm
and eval_map_normForm are extracted unchanged from the paper interface.
-/

open scoped NNReal Topology TensorProduct
open MvPolynomial
noncomputable section
namespace EnvelopeProperty

/-! ### The norm form of a linear form -/

section NormForm

variable (B : Type*) {A : Type*} [CommRing B] [CommRing A] [Algebra B A] {σ : Type*} [Fintype σ]

/-- The **norm form** of the linear form `∑_j X_j b_j`, for `b_j ∈ A` (`j ∈ σ`): the norm of
`∑_j X_j ⊗ b_j` in `B[X] ⊗_B A` over `B[X] = B[X_j : j ∈ σ]`. For `A` free of rank `d` over `B`
it is a form of degree `d` with coefficients in `B` (FHX, proof of `lem:finite-flat-norm`). -/
def normForm (b : σ → A) : MvPolynomial σ B :=
  Algebra.norm (MvPolynomial σ B) (∑ j, (X j : MvPolynomial σ B) ⊗ₜ[B] b j)

variable {B}

/-- **The norm form commutes with base change.** For `A` finite free over `B` and any
`B`-algebra `K`, the image of the norm form in `K[X]` evaluates at `t ∈ K^σ` to the norm of
`∑_j t_j (1 ⊗ b_j)` in `K ⊗_B A` over `K`. -/
theorem eval_map_normForm [Module.Free B A] [Module.Finite B A] {K : Type*} [CommRing K]
    [Algebra B K] (b : σ → A) (t : σ → K) :
    eval t (map (algebraMap B K) (normForm B b)) =
      Algebra.norm K (∑ j, t j • ((1 : K) ⊗ₜ[B] b j)) := by
  classical
  let e := Module.Free.chooseBasis B A
  let P := Algebra.TensorProduct.basis (MvPolynomial σ B) e
  let Q := Algebra.TensorProduct.basis K e
  rw [normForm, Algebra.norm_eq_matrix_det P, Algebra.norm_eq_matrix_det Q, eval_map,
    ← coe_eval₂Hom, RingHom.map_det]
  congr 1
  ext a c
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.basis_apply, Finset.sum_mul, Finset.sum_mul]
  simp [Algebra.TensorProduct.tmul_mul_tmul, P, Q, Algebra.smul_def]

end NormForm

theorem algebraNorm_baseChange_tmul {A B K : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Free A B] [Module.Finite A B] [CommRing K] [Algebra A K] (b : B) :
    algebraMap A K (Algebra.norm A b) = Algebra.norm K ((1 : K) ⊗ₜ[A] b) := by
  classical
  let e := Module.Free.chooseBasis A B
  let Q := Algebra.TensorProduct.basis K e
  rw [Algebra.norm_eq_matrix_det e, Algebra.norm_eq_matrix_det Q, RingHom.map_det]
  congr 1
  ext a c
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply]
  simp [Algebra.TensorProduct.tmul_mul_tmul, Q]

theorem valuation_algebraNorm_eq_pow {H L : Type*} [NormedField H] [CompleteSpace H]
    [IsUltrametricDist H] [Field L] [Algebra H L] [FiniteDimensional H L]
    [Algebra.IsSeparable H L] (w : Valuation L ℝ≥0)
    (hw : ∀ c : H, w (algebraMap H L c) = ‖c‖₊) (b : L) :
    (NormedField.valuation (K := H)) (Algebra.norm H b) = w b ^ Module.finrank H L := by
  obtain ⟨wΩ, hwΩ⟩ := Valuation.exists_extends_norm (K := H) (L := AlgebraicClosure H)
  have hτ : ∀ (τ : L →ₐ[H] AlgebraicClosure H), wΩ (τ b) = w b := by
    intro τ
    have he := Valuation.eq_of_extends_norm (K := H)
      (v := wΩ.comap τ.toRingHom) (w := w)
      (fun c => by
        change wΩ (τ (algebraMap H L c)) = ‖c‖₊
        rw [AlgHom.commutes, hwΩ]) hw
    exact congrArg (fun u : Valuation L ℝ≥0 => u b) he
  change ‖Algebra.norm H b‖₊ = _
  rw [← hwΩ (Algebra.norm H b), Algebra.norm_eq_prod_embeddings, map_prod]
  simp only [hτ, Finset.prod_const, Finset.card_univ, AlgHom.card]

/-- Scalar norms in a product of finite separable fields obey the corresponding product formula. -/
theorem valuation_algebraNorm_eq_prod_of_algEquiv {H E : Type*} [NormedField H]
    [CompleteSpace H] [IsUltrametricDist H] [CommRing E] [Algebra H E]
    {ι : Type*} [Fintype ι] {L : ι → Type*} [∀ i, Field (L i)]
    [∀ i, Algebra H (L i)] [∀ i, FiniteDimensional H (L i)] [∀ i, Algebra.IsSeparable H (L i)]
    (e : E ≃ₐ[H] ∀ i, L i) (w : ∀ i, Valuation (L i) ℝ≥0)
    (hw : ∀ i (c : H), w i (algebraMap H (L i) c) = ‖c‖₊) (b : E) :
    (NormedField.valuation (K := H)) (Algebra.norm H b) =
      ∏ i, w i (e b i) ^ Module.finrank H (L i) := by
  rw [← Algebra.norm_eq_of_algEquiv e, algebraNorm_pi, map_prod]
  exact Finset.prod_congr rfl fun i _ => valuation_algebraNorm_eq_pow (w i) (hw i) (e b i)

end EnvelopeProperty
