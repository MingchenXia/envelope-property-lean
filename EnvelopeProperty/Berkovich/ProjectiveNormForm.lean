/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.ProjectiveDeterminant
import EnvelopeProperty.Berkovich.NormForm
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Intrinsic norms and whole norm forms of finite projective algebras

Left multiplication and the intrinsic finite projective determinant define
an actual multiplicative algebra norm. Applying it to the polynomial tensor
algebra defines the entire norm form. Actual tensor comparisons prove scalar
and whole polynomial coefficient base change; finite free agreement connects
these constructions to the existing norm and norm-form APIs.

The base ring and commutative algebra are arbitrary. Local ranks may vary,
and rank-zero components contribute one. Global constant-degree homogeneity
and transport of decreasing function limits are separate producers.
-/

open scoped Classical TensorProduct
noncomputable section
namespace EnvelopeProperty

/-- Intrinsic multiplicative norm for an actual finite projective algebra. -/
def projectiveNorm (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A] : A →* R :=
  (projectiveDet R A).comp (Algebra.lmul R A).toRingHom.toMonoidHom

@[simp]
theorem projectiveNorm_apply {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A] (a : A) :
    projectiveNorm R A a = projectiveDet R A (Algebra.lmul R A a) := rfl

theorem projectiveNorm_eq_norm_of_free {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    [Module.Finite R A] [Module.Free R A] (a : A) :
    projectiveNorm R A a = Algebra.norm R a :=
  projectiveDet_eq_det_of_free _

/-- Whole multiplication endomorphisms commute with actual coefficient base change. -/
theorem lmul_one_tmul_eq_baseChange {R A S : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [CommRing S] [Algebra R S] (a : A) :
    Algebra.lmul S (S ⊗[R] A) ((1 : S) ⊗ₜ[R] a) = (Algebra.lmul R A a).baseChange S := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul s b =>
    change ((1 : S) ⊗ₜ[R] a) * (s ⊗ₜ[R] b) = s ⊗ₜ[R] (a * b)
    simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- Scalar intrinsic projective norm commutes with actual tensor coefficient base change. -/
theorem projectiveNorm_baseChange {R A S : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [Module.Projective R A]
    [CommRing S] [Algebra R S] (a : A) :
    projectiveNorm S (S ⊗[R] A) ((1 : S) ⊗ₜ[R] a) =
      algebraMap R S (projectiveNorm R A a) := by
  simp only [projectiveNorm_apply, lmul_one_tmul_eq_baseChange, projectiveDet_baseChange]

/-- The intrinsic norm respects genuine algebra equivalences. -/
theorem projectiveNorm_algEquiv {R A B : Type*} [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R B] [Module.Projective R B] (e : A ≃ₐ[R] B) (a : A) :
    projectiveNorm R B (e a) = projectiveNorm R A a := by
  have h : Algebra.lmul R B (e a) = e.toLinearEquiv.toLinearMap.comp
      ((Algebra.lmul R A a).comp e.symm.toLinearEquiv.toLinearMap) := by
    ext b
    change e a * b = e (a * e.symm b)
    rw [map_mul, e.apply_symm_apply]
  rw [projectiveNorm_apply, projectiveNorm_apply, h]
  exact projectiveDet_conj e.toLinearEquiv (Algebra.lmul R A a)

/-- The genuine whole norm polynomial of a finite projective algebra. -/
def projectiveNormForm (R : Type*) {A σ : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A] [Fintype σ] (b : σ → A) : MvPolynomial σ R :=
  projectiveNorm (MvPolynomial σ R) (MvPolynomial σ R ⊗[R] A)
    (∑ j, (MvPolynomial.X j : MvPolynomial σ R) ⊗ₜ[R] b j)

theorem projectiveNormForm_eq_normForm_of_free {R A σ : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [Module.Free R A] [Fintype σ] (b : σ → A) :
    projectiveNormForm R b = normForm R b := by
  exact projectiveNorm_eq_norm_of_free _



section ProjectiveNormFormBaseChange
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {R A S σ : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A] [CommRing S] [Algebra R S] [Fintype σ]

/-- Whole projective norm polynomials commute with genuine tensor coefficient base change. -/
theorem map_projectiveNormForm_baseChange (b : σ → A) :
    MvPolynomial.map (algebraMap R S) (projectiveNormForm R b) =
      projectiveNormForm S (fun j => (1 : S) ⊗ₜ[R] b j) := by
  let PR := MvPolynomial σ R
  let PS := MvPolynomial σ S
  let e₁ := Algebra.TensorProduct.cancelBaseChange R PR PS PS A
  let e₂ := Algebra.TensorProduct.cancelBaseChange R S PS PS A
  let e := e₁.trans e₂.symm
  have h (j : σ) : e ((1 : PS) ⊗ₜ[PR] ((MvPolynomial.X j : PR) ⊗ₜ[R] b j)) =
      (MvPolynomial.X j : PS) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] b j) := by
    simp [e, e₁, e₂, Algebra.smul_def, PR, PS]
  change algebraMap PR PS (projectiveNorm PR (PR ⊗[R] A)
    (∑ j, (MvPolynomial.X j : PR) ⊗ₜ[R] b j)) = _
  rw [← projectiveNorm_baseChange, ← projectiveNorm_algEquiv e]
  change projectiveNorm PS (PS ⊗[S] (S ⊗[R] A))
    (e ((1 : PS) ⊗ₜ[PR] (∑ j, (MvPolynomial.X j : PR) ⊗ₜ[R] b j))) = _
  congr 1
  rw [TensorProduct.tmul_sum, map_sum]
  exact Finset.sum_congr rfl (fun j _ => h j)

end ProjectiveNormFormBaseChange


end EnvelopeProperty
