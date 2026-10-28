/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Berkovich.IdempotentNormBaseChange
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Tactic.FinCases

/-! # Original binary norm polynomials and genuine idempotent characteristic factors -/

open scoped TensorProduct Matrix
open Polynomial
noncomputable section
namespace EnvelopeProperty

/-- The WHOLE original binary norm polynomial at (Z,1) is the ordinary characteristic
polynomial of original left multiplication, over any commutative coefficient ring. -/
theorem normForm_eval_one_neg_eq_charpoly {R E : Type*} [CommRing R] [CommRing E]
    [Algebra R E] [Module.Free R E] [Module.Finite R E] (b : E) :
    MvPolynomial.eval₂Hom (Polynomial.C : R →+* R[X]) ![Polynomial.X, 1]
      (normForm R ![(1 : E), -b]) = (Algebra.lmul R E b).charpoly := by
  classical
  let e := Module.Free.chooseBasis R E
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex R E)
  let P := Algebra.TensorProduct.basis R[X] e
  have hn := eval_map_normForm (B := R) (K := R[X]) ![(1 : E), -b] ![Polynomial.X, 1]
  rw [MvPolynomial.eval_map] at hn
  change MvPolynomial.eval₂Hom (Polynomial.C : R →+* R[X]) ![Polynomial.X, 1]
      (normForm R ![(1 : E), -b]) = _ at hn
  rw [hn]
  have hs : (∑ j : Fin 2, (![(Polynomial.X : R[X]), 1] j) •
      ((1 : R[X]) ⊗ₜ[R] (![(1 : E), -b] j))) =
        (Polynomial.X : R[X]) ⊗ₜ[R] (1 : E) - (1 : R[X]) ⊗ₜ[R] b := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul]
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.tmul_neg, sub_eq_add_neg]
  rw [hs, Algebra.norm_eq_matrix_det P, ← LinearMap.charpoly_toMatrix (Algebra.lmul R E b) e]
  change _ = (Matrix.charmatrix (LinearMap.toMatrix e e (Algebra.lmul R E b))).det
  congr 1
  ext i j : 1
  simp [Algebra.leftMulMatrix_eq_repr_mul, P, Algebra.TensorProduct.basis_apply,
    sub_mul, Algebra.TensorProduct.tmul_mul_tmul, Matrix.charmatrix,
    RingHom.mapMatrix_apply, Finsupp.single_apply, Matrix.diagonal, eq_comm]
  exact Algebra.toMatrix_lmul' e b i j

namespace IdempotentSummand

variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E]
  [Module.Finite R E] [Module.Projective R E]
attribute [local instance] finite

/-- The actual selected characteristic factor is the EXISTING whole intrinsic quotient
norm polynomial under the genuine binary substitution (Z,1), even at variable rank. -/
def characteristicFactor {e : E} (he : IsIdempotentElem e) (b : E) : R[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C : R →+* R[X]) ![Polynomial.X, 1]
    (normForm (R := R) he ![(1 : E), -b])

/-- EVERY original coefficient of the actual factor respects arbitrary genuine base change;
no free quotient, flat scalar extension or constant rank is an input. -/
theorem map_characteristicFactor {S : Type*} [CommRing S] [Algebra R S]
    {e : E} (he : IsIdempotentElem e) (b : E) :
    Polynomial.map (algebraMap R S) (characteristicFactor (R := R) he b) =
      characteristicFactor
        (he.map (Algebra.TensorProduct.includeRight : E →ₐ[R] S ⊗[R] E))
        ((1 : S) ⊗ₜ[R] b) := by
  classical
  have hvec : (fun j : Fin 2 => (1 : S) ⊗ₜ[R] (![(1 : E), -b] j)) =
      ![(1 : S ⊗[R] E), -((1 : S) ⊗ₜ[R] b)] := by
    funext j
    fin_cases j
    · rfl
    · exact TensorProduct.tmul_neg (1 : S) b
  have hf := map_normForm_baseChange (R := R) (S := S) he ![(1 : E), -b]
  rw [hvec] at hf
  have hc : (Polynomial.mapRingHom (algebraMap R S)).comp Polynomial.C =
      Polynomial.C.comp (algebraMap R S) := by
    ext a
    simp
  have hx : (fun j : Fin 2 => (Polynomial.mapRingHom (algebraMap R S))
      (![(Polynomial.X : R[X]), 1] j)) = ![(Polynomial.X : S[X]), 1] := by
    funext j
    fin_cases j <;> simp
  change (Polynomial.mapRingHom (algebraMap R S))
    (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1] (normForm he ![1, -b])) = _
  rw [MvPolynomial.map_eval₂Hom, hc, hx,
    ← MvPolynomial.eval₂Hom_map_hom (algebraMap R S) ![(Polynomial.X : S[X]), 1]
      Polynomial.C (normForm he ![1, -b]), hf]
  rfl

private theorem characteristicPidSummandFree [IsDomain R] [IsPrincipalIdealRing R]
    {e : E} (he : IsIdempotentElem e) : Module.Free R (Summand e) := by
  let : Module.Projective R (Summand e) := projective he
  infer_instance

/-- Actual PID geometry DERIVES the quotient free structure, identifying the SAME existing
norm factor with its ordinary charpoly, monicity and true original rank degree. -/
theorem characteristicFactor_eq_charpoly [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Free R E] {e : E} (he : IsIdempotentElem e) (b : E) :
    let : Module.Free R (Summand e) := characteristicPidSummandFree (R := R) he
    characteristicFactor (R := R) he b = (Algebra.lmul R (Summand e) (quotient (R := R) e b)).charpoly ∧
      (characteristicFactor (R := R) he b).Monic ∧
        (characteristicFactor (R := R) he b).natDegree = Module.finrank R (Summand e) := by
  classical
  let : Module.Projective R (Summand e) := projective he
  let : Module.Free R (Summand e) := characteristicPidSummandFree (R := R) he
  have hvec : (fun j : Fin 2 => quotient (R := R) e (![(1 : E), -b] j)) =
      ![(1 : Summand e), -(quotient (R := R) e b)] := by
    funext j
    fin_cases j <;> simp
  have hh : characteristicFactor (R := R) he b =
      (Algebra.lmul R (Summand e) (quotient (R := R) e b)).charpoly := by
    unfold characteristicFactor normForm
    rw [projectiveNormForm_eq_normForm_of_free, hvec, normForm_eval_one_neg_eq_charpoly]
  refine ⟨hh, hh.symm ▸ LinearMap.charpoly_monic _, ?_⟩
  rw [hh]
  exact LinearMap.charpoly_natDegree _

/-- The two actual complementary quotient factors multiply to the WHOLE original
characteristic polynomial, retaining both original quotient actions. -/
theorem characteristicFactor_mul_one_sub [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Free R E] {e : E} (he : IsIdempotentElem e) (b : E) :
    characteristicFactor (R := R) he b * characteristicFactor (R := R) he.one_sub b =
      (Algebra.lmul R E b).charpoly := by
  classical
  let : Module.Free R (Summand e) := characteristicPidSummandFree (R := R) he
  let : Module.Free R (Summand (1-e)) := characteristicPidSummandFree (R := R) he.one_sub
  let c : (E ⧸ Ideal.span ({e} : Set E)) ≃ₐ[R] Summand (1-e) :=
    Ideal.quotientEquivAlgOfEq R (by simp only [sub_sub_cancel])
  let p : E ≃ₐ[R] Summand e × Summand (1-e) :=
    (productEquiv (R := R) he).trans (AlgEquiv.prodCongr (AlgEquiv.refl : Summand e ≃ₐ[R] Summand e) c)
  have hp (a : E) : p a = (quotient (R := R) e a, quotient (R := R) (1-e) a) := by
    rfl
  have hm : p.toLinearEquiv.conj (Algebra.lmul R E b) =
      (Algebra.lmul R (Summand e) (quotient (R := R) e b)).prodMap
        (Algebra.lmul R (Summand (1-e)) (quotient (R := R) (1-e) b)) := by
    apply LinearMap.ext
    intro a
    rw [LinearEquiv.conj_apply_apply]
    change p (b * p.symm a) = _
    rw [map_mul, p.apply_symm_apply, hp]
    rfl
  rw [(characteristicFactor_eq_charpoly (R := R) he b).1,
    (characteristicFactor_eq_charpoly (R := R) he.one_sub b).1,
    ← LinearMap.charpoly_prodMap, ← hm, LinearEquiv.charpoly_conj]

end IdempotentSummand
end EnvelopeProperty
