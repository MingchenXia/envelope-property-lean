import EnvelopeProperty.Potential.LineSeparatedAffinoid

/-! # The constructed strict core is connected and approaches every separated boundary -/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

theorem inflation_mem_strictCore {x : RelativeSpectrum w K[X]} (hx : x ∈ U.strictCore)
    {s : ℝ≥0} (hs : s < U.radius) : fcCenteredInflation U.center x s ∈ U.strictCore := by
  constructor
  · rw [fcCenteredInflation_val_X_sub_C]
    exact max_lt hx.1 hs
  · intro j
    rw [fcCenteredInflation_val_X_sub_C]
    exact (hx.2 j).trans_le (le_max_left _ _)

theorem joinedIn_strictCore {x y : RelativeSpectrum w K[X]}
    (hx : x ∈ U.strictCore) (hy : y ∈ U.strictCore) : JoinedIn U.strictCore x y := by
  let s := max (val x (X-C U.center)) (val y (X-C U.center))
  have hs : s < U.radius := max_lt hx.1 hy.1
  have hpath (z : RelativeSpectrum w K[X]) (hz : z ∈ U.strictCore)
      (hzs : val z (X-C U.center) ≤ s) :
      JoinedIn U.strictCore z (centeredGauss (self w) U.center s) := by
    let p : Path z (centeredGauss (self w) U.center s) := {
      toFun t := fcCenteredInflation U.center z (s*Real.toNNReal (t : ℝ))
      continuous_toFun := (continuous_fcCenteredInflation U.center z).comp (by fun_prop)
      source' := by simp
      target' := by
        simpa only [show ((1 : unitInterval) : ℝ) = 1 from rfl,
          Real.toNNReal_one,mul_one] using fcCenteredInflation_eq_gauss U.center z s hzs }
    refine ⟨p,fun t => U.inflation_mem_strictCore hz ?_⟩
    have ht : Real.toNNReal (t : ℝ) ≤ 1 := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal (t : ℝ) t.2.1]
      exact t.2.2
    exact ((mul_le_mul_of_nonneg_left ht (show 0 ≤ s from zero_le)).trans_eq (mul_one _)).trans_lt hs
  exact (hpath x hx (le_max_left _ _)).trans (hpath y hy (le_max_right _ _)).symm

theorem isPathConnected_strictCore (hne : U.strictCore.Nonempty) : IsPathConnected U.strictCore := by
  obtain ⟨x,hx⟩ := hne
  exact ⟨x,hx,fun y hy => U.joinedIn_strictCore hx hy⟩

theorem radius_pos_of_strictCore_nonempty (hne : U.strictCore.Nonempty) : 0 < U.radius := by
  obtain ⟨x,hx⟩ := hne
  exact (show 0 ≤ val x (X-C U.center) from zero_le).trans_lt hx.1

theorem holeRadius_lt_outer_of_separated_core (hsep : U.IsSeparated)
    (hne : U.strictCore.Nonempty) (j : Fin m) : U.holeRadius j < U.radius := by
  obtain ⟨x,hx⟩ := hne
  have hd : w (U.center-U.holeCenter j) < U.radius := by
    rw [show U.center-U.holeCenter j = -(U.holeCenter j-U.center) by ring,Valuation.map_neg]
    exact hsep.holeCenter_lt j
  exact (hx.2 j).trans ((fc_linear_bound x U.center (U.holeCenter j)).trans_lt (max_lt hx.1 hd))

/-- The outer actual Gauss boundary is approached from the actual strict core. -/
theorem outerGauss_mem_closure_strictCore (hne : U.strictCore.Nonempty) (hsep : U.IsSeparated) :
    U.outerGauss ∈ closure U.strictCore := by
  classical
  let L : ℝ≥0 := Finset.univ.sup U.holeRadius
  have hLR : L < U.radius := (Finset.sup_lt_iff (U.radius_pos_of_strictCore_nonempty hne)).mpr
    (fun j _ => U.holeRadius_lt_outer_of_separated_core hsep hne j)
  have hR : U.radius ∈ closure (Set.Ioo L U.radius) := by
    rw [closure_Ioo hLR.ne]
    exact ⟨hLR.le,le_rfl⟩
  apply closure_mono (s := (centeredGauss (self w) U.center) '' Set.Ioo L U.radius) ?_
    (mem_closure_image (continuous_centeredGauss (self w) U.center).continuousAt hR)
  rintro y ⟨t,ht,rfl⟩
  constructor
  · simpa only [fc_centeredGauss_val_X_sub_C,sub_self,map_zero,zero_max] using ht.2
  · intro j
    rw [fc_centeredGauss_val_X_sub_C]
    exact ((Finset.le_sup (Finset.mem_univ j)).trans_lt ht.1).trans_le (le_max_right _ _)

/-- Each separated inner boundary is approached by its actual outward Gauss segment in the strict core. -/
theorem holeBoundaryPoint_mem_closure_strictCore (hsep : U.IsSeparated)
    (hne : U.strictCore.Nonempty) (j : Fin m) :
    U.holeBoundaryPoint j ∈ closure U.strictCore := by
  have hR := U.holeRadius_lt_outer_of_separated_core hsep hne j
  have hj : U.holeRadius j ∈ closure (Set.Ioo (U.holeRadius j) U.radius) := by
    rw [closure_Ioo hR.ne]
    exact ⟨le_rfl,hR.le⟩
  apply closure_mono
    (s := (centeredGauss (self w) (U.holeCenter j)) '' Set.Ioo (U.holeRadius j) U.radius) ?_
    (mem_closure_image (continuous_centeredGauss (self w) (U.holeCenter j)).continuousAt hj)
  rintro y ⟨t,ht,rfl⟩
  constructor
  · rw [fc_centeredGauss_val_X_sub_C]
    exact max_lt (hsep.holeCenter_lt j) ht.2
  · intro i
    rw [fc_centeredGauss_val_X_sub_C]
    by_cases hij : i = j
    · subst i
      simpa only [sub_self,map_zero,zero_max] using ht.1
    · have hi : U.holeRadius i < w (U.holeCenter j-U.holeCenter i) := by
        rw [show U.holeCenter j-U.holeCenter i = -(U.holeCenter i-U.holeCenter j) by ring,
          Valuation.map_neg]
        exact hsep.holeRadius_lt_distance i j hij
      exact hi.trans_le (le_max_left _ _)

theorem boundary_subset_closure_strictCore (hsep : U.IsSeparated) (hne : U.strictCore.Nonempty) :
    U.boundary ⊆ closure U.strictCore := by
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | ⟨j,rfl⟩
  · exact U.outerGauss_mem_closure_strictCore hne hsep
  · exact U.holeBoundaryPoint_mem_closure_strictCore hsep hne j

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
