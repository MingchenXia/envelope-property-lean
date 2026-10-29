/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.NormFormGeneral
import EnvelopeProperty.Berkovich.LocalAlgebraNorm
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.LinearAlgebra.Eigenspace.Zero
/-!
# Whole norm polynomials of local algebras over algebraically closed fields

A finite local algebra has an actual residual scalar homomorphism to the
algebraically closed ground field. A linear form differs from its residual
scalar polynomial by a nilpotent element of the actual polynomial tensor
algebra. Its exact determinant norm is therefore the residual linear form
raised to the genuine local module length. No scalar-point interpolation is
used, and nilpotent layers are retained in the entire polynomial identity.
-/

open scoped NNReal TensorProduct
open MvPolynomial
noncomputable section
namespace EnvelopeProperty
/-- The exact norm of a nilpotent perturbation of a scalar, over any integral domain. -/
theorem algebraNorm_eq_pow_of_isNilpotent_sub {R E : Type*} [CommRing R] [IsDomain R]
    [CommRing E] [Algebra R E] [Module.Free R E] [Module.Finite R E] (b : E) (c : R)
    (h : IsNilpotent (b - algebraMap R E c)) :
    Algebra.norm R b = c ^ Module.finrank R E := by
  let f : Module.End R E := Algebra.lmul R E (b - algebraMap R E c)
  have hf : IsNilpotent f := h.map (Algebra.lmul R E)
  have hb : Algebra.lmul R E b = f - (-c) • 1 := by
    ext x
    simp [f, Algebra.coe_lmul_eq_mul, Algebra.smul_def]
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, hb,
    LinearMap.charpoly_sub_smul, hf.charpoly_eq_X_pow_finrank]
  simp [Polynomial.coeff_zero_eq_eval_zero, ← mul_pow]
section AlgebraicallyClosedLocal

variable {K E : Type*} [Field K] [IsAlgClosed K] [CommRing E]
    [Algebra K E] [FiniteDimensional K E] [IsLocalRing E]

/-- The canonical residue scalar of a finite local algebra over an algebraically
closed field, obtained by the actual residue-field isomorphism. -/
def localResidueScalar : E →ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K (IsLocalRing.ResidueField E))
    IsAlgClosed.algebraMap_bijective_of_isIntegral).symm.toAlgHom.comp
      (IsScalarTower.toAlgHom K E (IsLocalRing.ResidueField E))

theorem localResidueScalar_residue (b : E) :
    algebraMap K (IsLocalRing.ResidueField E) (localResidueScalar b) = IsLocalRing.residue E b := by
  exact (AlgEquiv.ofBijective (Algebra.ofId K (IsLocalRing.ResidueField E))
    IsAlgClosed.algebraMap_bijective_of_isIntegral).apply_symm_apply _

/-- The actual residual scalar differs from its original element by a nilpotent,
using nilradical=maximalIdeal of the finite local algebra. -/
theorem isNilpotent_sub_localResidueScalar (b : E) :
    IsNilpotent (b - algebraMap K E (localResidueScalar b)) := by
  have : IsArtinianRing E := IsArtinianRing.of_finite K E
  rw [← mem_nilradical]
  change b - algebraMap K E (localResidueScalar b) ∈ (⊥ : Ideal E).radical
  rw [← IsArtinianRing.jacobson_eq_radical,
    IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  change algebraMap E (IsLocalRing.ResidueField E)
    (b - algebraMap K E (localResidueScalar b)) = 0
  rw [map_sub, ← IsScalarTower.algebraMap_apply, localResidueScalar_residue]
  exact sub_self _

/-- Local length equals vector-space dimension when the residual field is the
algebraically closed ground field. -/
theorem finrank_eq_localLength : Module.finrank K E = (Module.length E E).toNat := by
  let e := AlgEquiv.ofBijective (Algebra.ofId K (IsLocalRing.ResidueField E))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hd : Module.finrank K (IsLocalRing.ResidueField E) = 1 := by
    rw [← e.toLinearEquiv.finrank_eq]
    simp
  rw [finrank_eq_length_mul_residue_finrank (K := K), hd, mul_one]

/-- Whole determinant norm polynomial of a finite local algebra over an
algebraically closed field. Nilpotent layers give its genuine local-length exponent. -/
theorem normForm_eq_localResidueScalar_pow {σ : Type*} [Fintype σ] (b : σ → E) :
    normForm K b = (∑ j, C (localResidueScalar (b j)) * X j) ^ (Module.length E E).toNat := by
  classical
  let P := MvPolynomial σ K
  let z : P ⊗[K] E := ∑ j, (X j : P) ⊗ₜ[K] b j
  let c : P := ∑ j, C (localResidueScalar (b j)) * X j
  have hn : IsNilpotent (z - algebraMap P (P ⊗[K] E) c) := by
    have hz : z - algebraMap P (P ⊗[K] E) c =
        ∑ j, ((X j : P) ⊗ₜ[K] (1 : E)) *
          ((1 : P) ⊗ₜ[K] (b j - algebraMap K E (localResidueScalar (b j)))) := by
      simp only [z, c, map_sum, map_mul]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hc : (1 : P) ⊗ₜ[K] algebraMap K E (localResidueScalar (b j)) =
          (C (localResidueScalar (b j)) : P) ⊗ₜ[K] (1 : E) :=
        Algebra.TensorProduct.includeRight.commutes _
      rw [TensorProduct.tmul_sub, mul_sub, hc]
      simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.algebraMap_apply, P, mul_comm]
    rw [hz]
    rw [← mem_nilradical]
    apply (nilradical (P ⊗[K] E)).sum_mem
    intro j _
    apply (nilradical (P ⊗[K] E)).mul_mem_left
    exact mem_nilradical.mpr ((isNilpotent_sub_localResidueScalar (b j)).map
      (Algebra.TensorProduct.includeRight : E →ₐ[K] P ⊗[K] E))
  change Algebra.norm P z = _
  rw [algebraNorm_eq_pow_of_isNilpotent_sub z c hn, Module.finrank_baseChange,
    finrank_eq_localLength (K := K)]

/-- The weighted whole norm form of a finite local algebra over an algebraically
closed field, with actual nilpotent local length. -/
theorem wgaussValuation_normForm_of_local_algClosed {σ : Type*} [Fintype σ]
    (v : Valuation K ℝ≥0) (b : σ → E) (r : σ → ℝ≥0) :
    wgaussValuation v r (normForm K b) =
      (Finset.univ.sup fun j => v (localResidueScalar (b j)) * r j) ^ (Module.length E E).toNat := by
  rw [normForm_eq_localResidueScalar_pow, map_pow, wgaussValuation_linear]

end AlgebraicallyClosedLocal

end EnvelopeProperty
