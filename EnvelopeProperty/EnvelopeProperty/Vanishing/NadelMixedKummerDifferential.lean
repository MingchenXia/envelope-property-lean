import EnvelopeProperty.Char0.EtaleDifferentials
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Actual variable-unit differentials of mixed Kummer root equations

The coefficient derivations are genuine derivations on the actual entire
polynomial presentation. In particular the differential of a branch coefficient
u*x retains x*du. No unit coefficient is treated as constant.
-/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelMixedKummer
open Algebra Module
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]

private def coefficientLinearMap {q : ℕ} (δ : Derivation k R R) :
    MvPolynomial (Fin q) R →ₗ[k] MvPolynomial (Fin q) R where
  toFun p := AddMonoidAlgebra.ofCoeff (Finsupp.mapRange δ δ.map_zero (AddMonoidAlgebra.coeff p))
  map_add' p q := by
    ext m
    exact δ.map_add (p.coeff m) (q.coeff m)
  map_smul' a p := by
    ext m
    exact δ.map_smul a (p.coeff m)

private theorem coefficientLinearMap_monomial {q : ℕ} (δ : Derivation k R R)
    (m : Fin q →₀ ℕ) (a : R) :
    coefficientLinearMap δ (MvPolynomial.monomial m a) = MvPolynomial.monomial m (δ a) := by
  exact congrArg AddMonoidAlgebra.ofCoeff Finsupp.mapRange_single

/-- Extend an actual original coefficient derivation, fixing the root variables. -/
def coefficientDerivation {q : ℕ} (δ : Derivation k R R) :
    Derivation k (MvPolynomial (Fin q) R) (MvPolynomial (Fin q) R) where
  toLinearMap := coefficientLinearMap δ
  map_one_eq_zero' := by
    change coefficientLinearMap δ (MvPolynomial.monomial 0 1) = 0
    rw [coefficientLinearMap_monomial]
    simp
  leibniz' p q := by
    change coefficientLinearMap δ (p * q) =
      p * coefficientLinearMap δ q + q * coefficientLinearMap δ p
    induction p using MvPolynomial.induction_on' with
    | add p₁ p₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂, mul_add]; ring
    | monomial m a =>
        induction q using MvPolynomial.induction_on' with
        | add q₁ q₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂, add_mul]; ring
        | monomial n b =>
            simp only [MvPolynomial.monomial_mul, coefficientLinearMap_monomial,
              Derivation.leibniz, smul_eq_mul]
            rw [add_comm n m, ← map_add]

/-- The genuine coefficient extension acts on each actual monomial coefficient. -/
theorem coefficientDerivation_monomial {q : ℕ} (δ : Derivation k R R)
    (m : Fin q →₀ ℕ) (a : R) :
    coefficientDerivation δ (MvPolynomial.monomial m a) = MvPolynomial.monomial m (δ a) :=
  coefficientLinearMap_monomial δ m a

/-- Original coefficients retain their actual original derivatives. -/
theorem coefficientDerivation_C {q : ℕ} (δ : Derivation k R R) (a : R) :
    coefficientDerivation (q := q) δ (MvPolynomial.C a) = MvPolynomial.C (δ a) :=
  coefficientDerivation_monomial δ 0 a

/-- Every original root variable is fixed by this genuine coefficient derivation. -/
theorem coefficientDerivation_X {q : ℕ} (δ : Derivation k R R) (i : Fin q) :
    coefficientDerivation δ (MvPolynomial.X i) = 0 := by
  change coefficientLinearMap δ (MvPolynomial.monomial (Finsupp.single i 1) 1) = 0
  rw [coefficientLinearMap_monomial]
  simp

variable {n q : ℕ} (x : Fin n → R)
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)

/-- The actual root equations in the WHOLE original polynomial presentation. -/
def relation (N : Fin q → ℕ) (c : Fin q → R) (i : Fin q) : MvPolynomial (Fin q) R :=
  MvPolynomial.X i ^ N i - MvPolynomial.C (c i)

/-- The actual old-coordinate derivative of an original Kummer relation. -/
theorem coefficientDerivation_relation (N : Fin q → ℕ) (c : Fin q → R)
    (i : Fin q) (j : Fin n) :
    coefficientDerivation (Char0.etalePartialDeriv x hx j) (relation N c i) =
      -MvPolynomial.C (Char0.etalePartialDeriv x hx j (c i)) := by
  rw [relation, map_sub, Derivation.leibniz_pow, coefficientDerivation_X,
    smul_zero, nsmul_zero, zero_sub, coefficientDerivation_C]

/-- The actual original root-coordinate derivative, with its actual root degree. -/
theorem rootDerivation_relation (N : Fin q → ℕ) (c : Fin q → R)
    (i j : Fin q) :
    MvPolynomial.pderiv j (relation N c i) =
      if i = j then (N i : MvPolynomial (Fin q) R) * MvPolynomial.X i ^ (N i - 1) else 0 := by
  classical
  rw [relation, map_sub, Derivation.leibniz_pow, MvPolynomial.pderiv_C, sub_zero,
    MvPolynomial.pderiv_X]
  split_ifs with h
  · simp [h, smul_eq_mul, nsmul_eq_mul]
  · simp [h, smul_eq_mul]

/-- The exact derivative of a branch coefficient includes the variable-unit term. -/
theorem branch_coefficient_derivative (u : Rˣ) (i j : Fin n) :
    Char0.etalePartialDeriv x hx j ((u : R) * x i) =
      x i * Char0.etalePartialDeriv x hx j (u : R) +
        (u : R) * (if i = j then 1 else 0) := by
  rw [Derivation.leibniz, Char0.etalePartialDeriv_apply]
  simp only [smul_eq_mul]
  ring

end EnvelopeProperty.Vanishing.NadelMixedKummer
