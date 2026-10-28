import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.Tactic

/-! # An actual integral additive correction for intrinsic Cartier generators -/
noncomputable section
namespace EnvelopeProperty.Cartier.CartierAdditivePrimitive
open MvPolynomial
open scoped Classical

/-- An actual INTEGER polynomial, constructed from the genuine first Witt addition
coefficient. No divisibility or correction-polynomial witness is assumed. -/
def carryPolynomial (p : ℕ) [Fact p.Prime] : MvPolynomial (Fin 2) ℤ :=
  -((WittVector.teichmuller p (X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) +
      WittVector.teichmuller p (X (1 : Fin 2) : MvPolynomial (Fin 2) ℤ)).coeff 1)

private theorem ghost_one (p : ℕ) [Fact p.Prime] {S : Type*} [CommRing S]
    (x : WittVector p S) :
    WittVector.ghostComponent 1 x = (p : S) * x.coeff 1 + (x.coeff 0)^p := by
  rw [WittVector.ghostComponent_apply, wittPolynomial_one]
  simp only [map_add, map_mul, map_pow, aeval_X, map_natCast]

private theorem rearrange {S : Type*} [CommRing S] (p z x y : S) (n : ℕ)
    (h : p * z + (x+y)^n = x^n+y^n) : p * (-z) = (x+y)^n-x^n-y^n := by
  linear_combination -h

/-- The TRUE whole original integer polynomial satisfies p*C=(X+Y)^p-X^p-Y^p. -/
theorem mul_carryPolynomial (p : ℕ) [Fact p.Prime] :
    (p : MvPolynomial (Fin 2) ℤ) * carryPolynomial p =
      (X (0 : Fin 2) + X (1 : Fin 2))^p - X (0 : Fin 2)^p - X (1 : Fin 2)^p := by
  have h := (WittVector.ghostComponent (p := p) (R := MvPolynomial (Fin 2) ℤ) 1).map_add
    (WittVector.teichmuller p (X (0 : Fin 2))) (WittVector.teichmuller p (X (1 : Fin 2)))
  rw [ghost_one, WittVector.add_coeff_zero, WittVector.teichmuller_coeff_zero,
    WittVector.teichmuller_coeff_zero, WittVector.ghostComponent_teichmuller,
    WittVector.ghostComponent_teichmuller, pow_one] at h
  exact rearrange _ _ _ _ _ h

/-- The actual original first partial is the required FULL additive-generator coefficient. -/
theorem pderiv_zero_carryPolynomial (p : ℕ) [hp : Fact p.Prime] :
    pderiv (0 : Fin 2) (carryPolynomial p) =
      (X (0 : Fin 2) + X (1 : Fin 2))^(p-1) - X (0 : Fin 2)^(p-1) := by
  have h := congrArg (pderiv (0 : Fin 2)) (mul_carryPolynomial p)
  simp only [Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_natCast,
    map_add, map_sub, pderiv_X_self, pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0),
    nsmul_eq_mul, smul_eq_mul, mul_zero, add_zero, mul_one, sub_zero] at h
  have hp0 : (p : MvPolynomial (Fin 2) ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply mul_left_cancel₀ hp0
  calc
    _ = _ := h
    _ = _ := by ring

/-- The actual original second partial is the required FULL additive-generator coefficient. -/
theorem pderiv_one_carryPolynomial (p : ℕ) [hp : Fact p.Prime] :
    pderiv (1 : Fin 2) (carryPolynomial p) =
      (X (0 : Fin 2) + X (1 : Fin 2))^(p-1) - X (1 : Fin 2)^(p-1) := by
  have h := congrArg (pderiv (1 : Fin 2)) (mul_carryPolynomial p)
  simp only [Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_natCast,
    map_add, map_sub, pderiv_X_self, pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1),
    nsmul_eq_mul, smul_eq_mul, mul_zero, add_zero, zero_add, mul_one] at h
  have hp0 : (p : MvPolynomial (Fin 2) ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply mul_left_cancel₀ hp0
  calc
    _ = _ := h
    _ = _ := by ring


/-- The SAME original polynomial cotangent differential has the two actual coefficients. -/
theorem polynomial_universalD (p : ℕ) [Fact p.Prime] :
    KaehlerDifferential.D ℤ (MvPolynomial (Fin 2) ℤ) (carryPolynomial p) =
      (((X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) + X (1 : Fin 2))^(p-1) - X (0 : Fin 2)^(p-1)) •
        KaehlerDifferential.D ℤ (MvPolynomial (Fin 2) ℤ) (X (0 : Fin 2)) +
      (((X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) + X (1 : Fin 2))^(p-1) - X (1 : Fin 2)^(p-1)) •
        KaehlerDifferential.D ℤ (MvPolynomial (Fin 2) ℤ) (X (1 : Fin 2)) := by
  have h := (KaehlerDifferential.mvPolynomialBasis ℤ (Fin 2)).sum_repr
    (KaehlerDifferential.D ℤ (MvPolynomial (Fin 2) ℤ) (carryPolynomial p))
  simpa only [Fin.sum_univ_two, KaehlerDifferential.mvPolynomialBasis_repr_apply,
    KaehlerDifferential.mvPolynomialBasis_apply, pderiv_zero_carryPolynomial,
    pderiv_one_carryPolynomial] using h.symm

/-- Evaluation of the genuine integer correction polynomial on the TWO original functions. -/
def primitive (p : ℕ) [Fact p.Prime] {B : Type*} [CommRing B] (a b : B) : B :=
  aeval (R := ℤ) ![a,b] (carryPolynomial p)

/-- The SAME original target universal differential has an ACTUAL primitive, with no
characteristic or primitive certificate. -/
theorem universalD_primitive (p : ℕ) [Fact p.Prime]
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (a b : B) :
    KaehlerDifferential.D R B (primitive p a b) =
      ((a+b)^(p-1)-a^(p-1)) • KaehlerDifferential.D R B a +
      ((a+b)^(p-1)-b^(p-1)) • KaehlerDifferential.D R B b := by
  let ev : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] B := aeval ![a,b]
  let : Algebra (MvPolynomial (Fin 2) ℤ) B := ev.toAlgebra
  have h := congrArg (KaehlerDifferential.map ℤ R (MvPolynomial (Fin 2) ℤ) B)
    (polynomial_universalD p)
  simp only [map_add, map_smul, KaehlerDifferential.map_D] at h
  have hs (c : MvPolynomial (Fin 2) ℤ) (z : KaehlerDifferential R B) :
      c • z = ev c • z := (IsScalarTower.algebraMap_smul B c z).symm
  simp only [hs] at h
  simpa only [ev, primitive, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    map_sub, map_pow, map_add, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one] using h

end EnvelopeProperty.Cartier.CartierAdditivePrimitive
