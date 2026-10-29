import Mathlib.Analysis.Normed.Unbundled.SeminormFromBounded
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.LinearAlgebra.Basis.Bilinear

/-! # Actual finite structure constants construct a genuine algebra ring norm -/

open scoped NNReal BigOperators
noncomputable section

namespace Module.Basis

variable {R E ι : Type*} [NormedCommRing R] [CommRing E] [Algebra R E] [Fintype ι]
variable (b : Basis ι R E)

/-- The actual finite-product norm of the original basis coefficients. -/
def fcCoefficientNorm (x : E) : ℝ := ‖b.equivFun x‖

theorem fcCoefficientNorm_nonneg (x : E) : 0 ≤ b.fcCoefficientNorm x := norm_nonneg _

theorem fcCoefficientNorm_eq_zero_iff (x : E) : b.fcCoefficientNorm x = 0 ↔ x = 0 := by
  rw [fcCoefficientNorm,norm_eq_zero]
  constructor
  · intro h
    apply b.equivFun.injective
    simpa only [map_zero] using h
  · intro h
    subst x
    exact map_zero _

theorem fcCoefficientNorm_add_le (x y : E) :
    b.fcCoefficientNorm (x+y) ≤ b.fcCoefficientNorm x+b.fcCoefficientNorm y := by
  unfold fcCoefficientNorm
  rw [map_add]
  exact norm_add_le _ _

theorem fcCoefficientNorm_neg (x : E) : b.fcCoefficientNorm (-x) = b.fcCoefficientNorm x := by
  simp only [fcCoefficientNorm,map_neg,norm_neg]

theorem norm_equivFun_le_fcCoefficientNorm (x : E) (i : ι) :
    ‖b.equivFun x i‖ ≤ b.fcCoefficientNorm x := norm_le_pi_norm _ i

/-- A positive constant constructed from the ENTIRE original finite multiplication table. -/
def fcMultiplicationBound : ℝ := 1+∑ i : ι, ∑ j : ι, ∑ k : ι, ‖b.equivFun (b i*b j) k‖

theorem fcMultiplicationBound_pos : 0 < b.fcMultiplicationBound := by
  unfold fcMultiplicationBound
  exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => norm_nonneg _)

private theorem fc_product_equivFun (x y : E) (k : ι) :
    b.equivFun (x*y) k =
      ∑ i : ι, ∑ j : ι, (b.equivFun x i*b.equivFun y j)*b.equivFun (b i*b j) k := by
  have he : x*y = ∑ i : ι, ∑ j : ι, (b.equivFun x i*b.equivFun y j) • (b i*b j) := by
    conv_lhs => rw [← b.sum_repr x,← b.sum_repr y]
    simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,Basis.equivFun_apply]
    simp_rw [Finset.smul_sum,smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  rw [he]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

/-- No multiplicativity of the basis norm is assumed: the actual structure constants bound it. -/
theorem fcCoefficientNorm_mul_le (x y : E) :
    b.fcCoefficientNorm (x*y) ≤ b.fcMultiplicationBound*b.fcCoefficientNorm x*b.fcCoefficientNorm y := by
  classical
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg
    (mul_nonneg b.fcMultiplicationBound_pos.le (b.fcCoefficientNorm_nonneg x))
    (b.fcCoefficientNorm_nonneg y))).mpr
  intro k
  rw [b.fc_product_equivFun x y k]
  let S := ∑ i : ι, ∑ j : ι, ∑ l : ι, ‖b.equivFun (b i*b j) l‖
  have hS : (∑ i : ι, ∑ j : ι, ‖b.equivFun (b i*b j) k‖) ≤ S := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact Finset.single_le_sum (fun l _ => norm_nonneg _) (Finset.mem_univ k)
  have hSC : S ≤ b.fcMultiplicationBound := by
    change S ≤ 1+S
    linarith
  calc
    _ ≤ ∑ i : ι, ‖∑ j : ι, (b.equivFun x i*b.equivFun y j)*b.equivFun (b i*b j) k‖ := norm_sum_le _ _
    _ ≤ ∑ i : ι, ∑ j : ι, b.fcCoefficientNorm x*b.fcCoefficientNorm y*‖b.equivFun (b i*b j) k‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ‖b.equivFun x i*b.equivFun y j‖*‖b.equivFun (b i*b j) k‖ := norm_mul_le _ _
        _ ≤ (‖b.equivFun x i‖*‖b.equivFun y j‖)*‖b.equivFun (b i*b j) k‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul (b.norm_equivFun_le_fcCoefficientNorm x i)
            (b.norm_equivFun_le_fcCoefficientNorm y j) (norm_nonneg _) (b.fcCoefficientNorm_nonneg x))
          (norm_nonneg _)
    _ = (b.fcCoefficientNorm x*b.fcCoefficientNorm y)*
        (∑ i : ι, ∑ j : ι, ‖b.equivFun (b i*b j) k‖) := by simp only [Finset.mul_sum]
    _ ≤ (b.fcCoefficientNorm x*b.fcCoefficientNorm y)*S :=
      mul_le_mul_of_nonneg_left hS (mul_nonneg (b.fcCoefficientNorm_nonneg x) (b.fcCoefficientNorm_nonneg y))
    _ ≤ (b.fcCoefficientNorm x*b.fcCoefficientNorm y)*b.fcMultiplicationBound :=
      mul_le_mul_of_nonneg_left hSC (mul_nonneg (b.fcCoefficientNorm_nonneg x) (b.fcCoefficientNorm_nonneg y))
    _ = _ := by ring

/-- The original coefficients construct the normalized operator ring norm, rather than postulating it. -/
def fcCoefficientRingNorm : RingNorm E :=
  normFromBounded (by simp only [fcCoefficientNorm,map_zero,norm_zero])
    b.fcCoefficientNorm_nonneg b.fcCoefficientNorm_mul_le b.fcCoefficientNorm_add_le b.fcCoefficientNorm_neg
    (by ext x; exact b.fcCoefficientNorm_eq_zero_iff x)

theorem fcCoefficientRingNorm_le (x : E) :
    b.fcCoefficientRingNorm x ≤ b.fcMultiplicationBound*b.fcCoefficientNorm x :=
  seminormFromBounded_le b.fcCoefficientNorm_nonneg b.fcCoefficientNorm_mul_le x

theorem fcCoefficientNorm_le (x : E) :
    b.fcCoefficientNorm x ≤ b.fcCoefficientNorm 1*b.fcCoefficientRingNorm x :=
  seminormFromBounded_ge b.fcCoefficientNorm_nonneg b.fcCoefficientNorm_mul_le x

theorem fcCoefficientRingNorm_one [Nontrivial E] : b.fcCoefficientRingNorm 1 = 1 := by
  apply seminormFromBounded_one _ b.fcCoefficientNorm_nonneg b.fcCoefficientNorm_mul_le
  intro hf
  have hzero : b.fcCoefficientNorm 1 = 0 := congrFun hf 1
  exact one_ne_zero ((b.fcCoefficientNorm_eq_zero_iff 1).mp hzero)

variable [IsUltrametricDist R]

theorem fcCoefficientNorm_isNonarchimedean : IsNonarchimedean b.fcCoefficientNorm := by
  intro x y
  unfold fcCoefficientNorm
  rw [map_add]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem fcCoefficientRingNorm_isNonarchimedean : IsNonarchimedean b.fcCoefficientRingNorm :=
  seminormFromBounded_isNonarchimedean b.fcCoefficientNorm_nonneg b.fcCoefficientNorm_mul_le
    b.fcCoefficientNorm_isNonarchimedean

end Module.Basis
