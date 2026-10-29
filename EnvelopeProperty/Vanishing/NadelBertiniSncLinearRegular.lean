import EnvelopeProperty.Vanishing.NadelBertiniLinearSmooth
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Monic

/-! # The actual original unit-pivot universal equation is regular

The entire original linear form is monic in its actual pivot variable after
the genuine variable algebra equivalence. No nontriviality or domain hypothesis
on the original chart ring is needed; regularity is produced internally.
-/
noncomputable section
open MvPolynomial
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniSncLinearRegular
open NadelBertiniLinearSmooth
variable {B : Type u} [CommRing B] {S : Type}

/-- The actual original variable algebra equivalence isolating the original pivot. -/
def pivotEquiv (j : S) : MvPolynomial S B ≃ₐ[B]
    Polynomial (MvPolynomial {i : S // i ≠ j} B) := by
  classical
  exact (MvPolynomial.renameEquiv B (Equiv.optionSubtypeNe j).symm).trans
    (MvPolynomial.optionEquivLeft B _)

private theorem pivotEquiv_C (j : S) (b : B) :
    pivotEquiv j (C b) = Polynomial.C (C b) := by
  classical
  simp [pivotEquiv]

private theorem pivotEquiv_X_self (j : S) :
    (pivotEquiv (B := B) j) (X j) = Polynomial.X := by
  classical
  simp [pivotEquiv]

private theorem pivotEquiv_X_other (j : S) (i : {i : S // i ≠ j}) :
    (pivotEquiv (B := B) j) (X i.1) = Polynomial.C (X i) := by
  classical
  simp [pivotEquiv, Equiv.optionSubtypeNe_symm_of_ne i.2]

variable [Fintype S] [DecidableEq S]

/-- The WHOLE original linear equation becomes the actual monic pivot polynomial,
retaining every original nonpivot frame coefficient and original variable. -/
theorem pivotEquiv_linearForm (c : S → B) (j : S) (hj : c j = 1) :
    pivotEquiv j (linearForm c) = Polynomial.X +
      Polynomial.C (linearForm (fun i : {i : S // i ≠ j} => c i.1)) := by
  classical
  rw [linearForm, map_sum]
  let e : Option {i : S // i ≠ j} ≃ S := Equiv.optionSubtypeNe j
  rw [← e.sum_comp (fun i => pivotEquiv j (C (c i) * X i)), Fintype.sum_option]
  simp only [e, Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some, map_mul,
    pivotEquiv_C, pivotEquiv_X_self, pivotEquiv_X_other, hj, map_one, one_mul]
  rw [linearForm, map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => (map_mul Polynomial.C _ _).symm)

/-- The actual original unit-pivot universal equation is a nonzerodivisor,
internally from its genuine monic polynomial image. -/
theorem linearForm_regular (c : S → B) (j : S) (hj : c j = 1) :
    IsSMulRegular (MvPolynomial S B) (linearForm c) := by
  have hmonic : Polynomial.Monic (pivotEquiv j (linearForm c)) := by
    rw [pivotEquiv_linearForm c j hj]
    exact Polynomial.monic_X_add_C _
  change Function.Injective (fun b : MvPolynomial S B => linearForm c * b)
  intro b b' hbb'
  apply (pivotEquiv j).injective
  apply hmonic.isRegular.left
  simpa only [map_mul] using congrArg (pivotEquiv j) hbb'

end EnvelopeProperty.Vanishing.NadelBertiniSncLinearRegular
