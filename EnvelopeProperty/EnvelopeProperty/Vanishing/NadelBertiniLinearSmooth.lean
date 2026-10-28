import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Ideal.Quotient.Operations
/-! # Actual arbitrary-pivot linear quotients have a genuine submersive presentation -/
noncomputable section
open MvPolynomial
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniLinearSmooth
variable {B : Type u} [CommRing B] {S : Type} [Fintype S]
def linearForm (c : S → B) : MvPolynomial S B := ∑ a, C (c a) * X a
def linearIdeal (c : S → B) : Ideal (MvPolynomial S B) := Ideal.span {linearForm c}
theorem linearForm_pderiv (c : S → B) (j : S) :
    (linearForm c).pderiv j = C (c j) := by
  classical
  simp [linearForm, MvPolynomial.pderiv_X, Pi.single_apply]
theorem linear_smooth (c : S → B) (j : S) (hj : c j = 1) :
    Algebra.Smooth B (MvPolynomial S B ⧸ linearIdeal c) := by
  classical
  let v : Fin 1 → MvPolynomial S B := fun _ => linearForm c
  let P := Algebra.PreSubmersivePresentation.naive (v := v) (fun _ => j)
    (fun a b _ => Subsingleton.elim a b)
  have hd : (linearForm c).pderiv j = 1 := by rw [linearForm_pderiv, hj, map_one]
  have hm : P.jacobiMatrix = (1 : Matrix (Fin 1) (Fin 1) (MvPolynomial S B)) := by
    ext a b : 1
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst a
    subst b
    simpa only [P, v, hd, Matrix.one_apply_eq] using
      (Algebra.PreSubmersivePresentation.jacobiMatrix_naive (v := v) (fun _ => j)
        (fun a b _ => Subsingleton.elim a b)
        (Function.surjInv Ideal.Quotient.mk_surjective) (by apply Function.surjInv_eq) 0 0)
  have hJ : P.jacobian = 1 := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hm, Matrix.det_one, map_one]
  let Q : Algebra.SubmersivePresentation B
      (MvPolynomial S B ⧸ Ideal.span (Set.range v)) S (Fin 1) :=
    { P with jacobian_isUnit := hJ.symm ▸ isUnit_one }
  let : Algebra.IsStandardSmooth B (MvPolynomial S B ⧸ Ideal.span (Set.range v)) :=
    Q.isStandardSmooth
  have hI : Ideal.span (Set.range v) = linearIdeal c := by
    simp only [v, Set.range_const, linearIdeal]
  exact Algebra.Smooth.of_equiv (Ideal.quotientEquivAlgOfEq B hI)
end EnvelopeProperty.Vanishing.NadelBertiniLinearSmooth
