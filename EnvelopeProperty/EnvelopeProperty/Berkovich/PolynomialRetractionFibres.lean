/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.PolynomialSpectrumHomotopy

open scoped Polynomial NNReal Topology
open Polynomial Topology unitInterval
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {v : Valuation R ℝ≥0}

private theorem openDiscRetraction_time_le_one (θ : I) : Real.toNNReal (θ : ℝ) ≤ 1 := by
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal (θ : ℝ) θ.2.1]
  exact θ.2.2

private theorem deformation_radius_le (θ : I) (x : RelativeSpectrum v A[X]) :
    val (polynomialGaussDeformation (θ, x)) X ≤ val x X := by
  change val (polynomialGaussInflation x (Real.toNNReal (θ : ℝ) * val x X)) X ≤ val x X
  rw [polynomialGaussInflation_val_X]
  apply max_le le_rfl
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (openDiscRetraction_time_le_one θ) bot_le

private theorem contraction_radius_le (θ : I) (x : RelativeSpectrum v A[X]) :
    val (polynomialGaussContraction (θ, x)) X ≤ val x X := by
  change val (gauss (proj x) ((1 - Real.toNNReal (θ : ℝ)) * val x X)) X ≤ val x X
  rw [gauss_val_X]
  calc
    _ ≤ 1 * val x X := mul_le_mul_of_nonneg_right (tsub_le_self) bot_le
    _ = _ := one_mul _

/-- Every time of the actual polynomial retraction preserves the entire original coefficient point. -/
theorem proj_polynomialRetraction (θ : I) (x : RelativeSpectrum v A[X]) :
    proj (polynomialRetraction (θ, x)) = proj x := by
  change proj ((polynomialGaussDeformation.trans polynomialGaussContraction) (θ, x)) = proj x
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact proj_polynomialGaussInflation _ _
  · exact proj_gauss _ _

/-- Every time of the same actual polynomial retraction weakly decreases the original radius. -/
theorem val_polynomialRetraction_X_le (θ : I) (x : RelativeSpectrum v A[X]) :
    val (polynomialRetraction (θ, x)) X ≤ val x X := by
  change val ((polynomialGaussDeformation.trans polynomialGaussContraction) (θ, x)) X ≤ val x X
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact deformation_radius_le _ x
  · exact contraction_radius_le _ x

/-- The actual strict coordinate disc in the whole original prescribed coefficient fibre. -/
abbrev FibreOpenDisc (y : RelativeSpectrum v A) (r : ℝ≥0) :=
  {x : RelativeSpectrum v A[X] // proj x = y ∧ val x X < r}

namespace FibreOpenDisc
variable (y : RelativeSpectrum v A) (r : ℝ≥0)

/-- Restrict the original whole polynomial homotopy to a genuine strict fibre disc. -/
def contraction (hr : 0 < r) : (ContinuousMap.id (FibreOpenDisc y r)).Homotopy
    (ContinuousMap.const _
      (⟨gauss y 0, proj_gauss y 0, by rw [gauss_val_X]; exact hr⟩ : FibreOpenDisc y r)) where
  toFun p := ⟨polynomialRetraction (p.1, p.2.1),
    (proj_polynomialRetraction p.1 p.2.1).trans p.2.2.1,
    (val_polynomialRetraction_X_le p.1 p.2.1).trans_lt p.2.2.2⟩
  continuous_toFun := (polynomialRetraction.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    exact polynomialRetraction.map_zero_left x.1
  map_one_left x := by
    apply Subtype.ext
    change polynomialRetraction (1, x.1) = gauss y 0
    exact (polynomialRetraction.map_one_left x.1).trans (by
      change gauss (proj x.1) 0 = gauss y 0
      rw [x.2.1])

/-- Every positive-radius actual strict fibre disc is contractible, without coefficient hypotheses. -/
theorem contractibleSpace (hr : 0 < r) : ContractibleSpace (FibreOpenDisc y r) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨⟨gauss y 0, proj_gauss y 0, by rw [gauss_val_X]; exact hr⟩, ⟨contraction y r hr⟩⟩

end FibreOpenDisc
end EnvelopeProperty.Berkovich.RelativeSpectrum
