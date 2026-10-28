import Hironaka.Scheme.BlowUp.CoordinateSubspace.Charts
import EnvelopeProperty.AlgGeom.Canonical.AffineCanonicalModule
import Mathlib.LinearAlgebra.Matrix.Block

/-! # The Jacobian of the actual original coordinate blowup substitution -/

open AlgebraicGeometry MvPolynomial CategoryTheory
open scoped BigOperators

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalJacobian
open CoordinateSubspace affineBlowUpAlgebra CanonicalGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] {n r : ℕ}

/-- The actual native original chart substitution, not a supplied Jacobian. -/
def jacobianMatrix (j : Fin n) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) A) :=
  fun i k => pderiv k (chartSubst A (center n r) j (X i))

theorem pivot_row (j : Fin n) (k : Fin n) :
    jacobianMatrix (A := A) (r := r) j j k = if j = k then 1 else 0 := by
  rw [jacobianMatrix, chartSubst_X]
  simp only [ne_eq, not_true_eq_false, and_false, ite_false]
  by_cases h : j = k
  · subst h
    simp
  · simp [pderiv_X_of_ne h, h]

theorem complementary_block (j : Fin n) :
    (jacobianMatrix (A := A) (r := r) j).toSquareBlockProp (fun i => ¬ i = j) =
      Matrix.diagonal (fun i : {i : Fin n // ¬ i = j} =>
        if i.1.val < r then X j else 1) := by
  apply Matrix.ext
  intro i k
  change pderiv k.1 (chartSubst A (center n r) j (X i.1)) = _
  rw [chartSubst_X]
  by_cases h : i = k
  · subst h
    by_cases hi : i.1.val < r
    · simp [hi, i.2, pderiv_X_of_ne (Ne.symm i.2)]
    · simp [hi]
  · have hik : i.1 ≠ k.1 := fun he => h (Subtype.ext he)
    by_cases hi : i.1.val < r
    · simp [hi, i.2, pderiv_X_of_ne hik,
        pderiv_X_of_ne (Ne.symm k.2), h]
    · simp [hi, pderiv_X_of_ne hik, h]

private theorem coordinate_count (j : Fin n) (hj : j.val < r) (hrn : r ≤ n) :
    Fintype.card {i : Fin n // i.val < r ∧ i ≠ j} = r - 1 := by
  let e : {i : Fin n // i.val < r ∧ i ≠ j} ≃
      {i : Fin r // i ≠ ⟨j.val, hj⟩} :=
    { toFun := fun i => ⟨⟨i.1.val, i.2.1⟩, fun h =>
        i.2.2 (Fin.ext (congrArg (fun z : Fin r => z.val) h))⟩
      invFun := fun i => ⟨⟨i.1.val, lt_of_lt_of_le i.1.isLt hrn⟩, i.1.isLt,
        fun h => i.2 (Fin.ext (congrArg (fun z : Fin n => z.val) h))⟩
      left_inv := fun _ => Subtype.ext (Fin.ext rfl)
      right_inv := fun _ => Subtype.ext (Fin.ext rfl) }
  rw [Fintype.card_congr e, Fintype.card_subtype, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

/-- The genuine original chart Jacobian is exactly the expected exceptional
equation to the original codimension minus one, over any commutative ring. -/
theorem determinant (j : Fin n) (hj : j.val < r) (hrn : r ≤ n) :
    (jacobianMatrix (A := A) (r := r) j).det = (X j) ^ (r - 1) := by
  classical
  let : Fintype {i : Fin n // i = j} := @Subtype.fintype (Fin n) (fun i => i = j) _ _
  have hblock := Matrix.twoBlockTriangular_det'
    (jacobianMatrix (A := A) (r := r) j) (fun i => i = j) (fun i hi k hk => by
      subst hi
      rw [pivot_row, if_neg (Ne.symm hk)])
  have hone : ((jacobianMatrix (A := A) (r := r) j).toSquareBlockProp
      (fun i => i = j)).det = 1 := by
    refine (Matrix.det_eq_elem_of_card_eq_one ?_ ⟨j, rfl⟩).trans ?_
    · exact Fintype.card_eq_one_iff.mpr ⟨⟨j, rfl⟩, fun i => Subtype.ext i.2⟩
    · exact (pivot_row j j).trans (if_pos rfl)
  rw [hblock, hone, one_mul, complementary_block, Matrix.det_diagonal]
  have hcount : (Finset.univ.filter (fun i : {i : Fin n // ¬ i = j} =>
      i.1.val < r)).card = r - 1 := by
    rw [← Fintype.card_subtype]
    calc
      _ = Fintype.card {i : Fin n // i.val < r ∧ i ≠ j} := Fintype.card_congr
        { toFun := fun i => ⟨i.1.1, i.2, i.1.2⟩
          invFun := fun i => ⟨⟨i.1, i.2.2⟩, i.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      _ = r - 1 := coordinate_count j hj hrn
  simp [Finset.prod_ite, hcount]

/-- The actual top relative Kähler wedge retains the exact original
coordinate ordering and computes the original chart's canonical Jacobian. -/
theorem top_wedge (j : Fin n) (hj : j.val < r) (hrn : r ≤ n) :
    exteriorPower.ιMulti (MvPolynomial (Fin n) A) n
        (fun i => KaehlerDifferential.D A (MvPolynomial (Fin n) A)
          (chartSubst A (center n r) j (X i))) =
      (X j : MvPolynomial (Fin n) A) ^ (r - 1) • exteriorPower.ιMulti (MvPolynomial (Fin n) A) n
        (fun i => KaehlerDifferential.D A (MvPolynomial (Fin n) A) (X i)) := by
  let b := KaehlerDifferential.mvPolynomialBasis A (Fin n)
  have hb : (fun i => KaehlerDifferential.D A (MvPolynomial (Fin n) A) (X i)) = b := by
    funext i
    exact (KaehlerDifferential.mvPolynomialBasis_apply A (Fin n) i).symm
  rw [hb, ← affineCanonicalGenerator_eq_wedge b]
  calc
    _ = affineCanonicalTrivialization b _ • affineCanonicalGenerator b :=
      affineCanonical_eq_smul_generator b _
    _ = _ := by
      rw [affineCanonicalTrivialization_apply_wedge]
      have hM : (Matrix.of fun i k => b.coord k
          (KaehlerDifferential.D A (MvPolynomial (Fin n) A)
            (chartSubst A (center n r) j (X i)))) = jacobianMatrix (A := A) (r := r) j := by
        apply Matrix.ext
        intro i k
        exact KaehlerDifferential.mvPolynomialBasis_repr_apply A (Fin n) _ k
      rw [hM, determinant j hj hrn]

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalJacobian
