import EnvelopeProperty.Potential.LineFiniteHoleDomains

/-! # Exact original radius and strict-centre tests for actual open-hole containment -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}

/-- WHOLE actual open-disc containment forces the ORIGINAL radius order, for arbitrary real radii. -/
theorem fc_openLinearDisc_radius_le_of_subset (a b : K) (r s : ℝ≥0)
    (hsub : fcOpenLinearDisc (w := w) a r ⊆ fcOpenLinearDisc b s) : r ≤ s := by
  apply le_of_not_gt
  intro hsr
  obtain ⟨ρ,hsρ,hρr⟩ := exists_between hsr
  let z := centeredGauss (self w) a ρ
  have hz : z ∈ fcOpenLinearDisc a r := by
    simpa only [z,fcOpenLinearDisc,Set.mem_ofPred_eq,fc_centeredGauss_val_X_sub_C,sub_self,map_zero,max_eq_right zero_le]
      using hρr
  have hzb := hsub hz
  have hlarge : ρ ≤ val z (X-C b) := by
    rw [show z = centeredGauss (self w) a ρ from rfl,fc_centeredGauss_val_X_sub_C]
    exact le_max_right _ _
  exact not_lt_of_ge (hsρ.le.trans hlarge) hzb

/-- For EVERY positive ORIGINAL source hole, whole actual containment is EXACTLY radius order and strict original centre distance. -/
theorem fc_openLinearDisc_subset_iff (a b : K) (r s : ℝ≥0) (hr : 0 < r) :
    fcOpenLinearDisc (w := w) a r ⊆ fcOpenLinearDisc b s ↔ r ≤ s ∧ w (a-b) < s := by
  constructor
  · intro hsub
    refine ⟨fc_openLinearDisc_radius_le_of_subset a b r s hsub,?_⟩
    have hz : centeredGauss (self w) a 0 ∈ fcOpenLinearDisc a r := by
      simpa only [fcOpenLinearDisc,Set.mem_ofPred_eq,fc_centeredGauss_val_X_sub_C,sub_self,map_zero,max_self] using hr
    have h := hsub hz
    simpa only [fcOpenLinearDisc,Set.mem_ofPred_eq,fc_centeredGauss_val_X_sub_C,max_zero] using h
  · rintro ⟨hrs,hab⟩ y hy
    exact (fc_linear_bound y a b).trans_lt (max_lt (hy.trans_le hrs) hab)

/-- An ACTUAL common point plus original radius order implies WHOLE actual open-hole containment. -/
theorem fc_openLinearDisc_subset_of_common (a b : K) (r s : ℝ≥0)
    (x : RelativeSpectrum w K[X]) (hx : x ∈ fcOpenLinearDisc a r) (hy : x ∈ fcOpenLinearDisc b s)
    (hrs : r ≤ s) : fcOpenLinearDisc (w := w) a r ⊆ fcOpenLinearDisc b s := by
  have hab : w (a-b) < s :=
    (fc_center_distance_bound x a b).trans_lt (max_lt (hx.trans_le hrs) hy)
  intro y hy'
  exact (fc_linear_bound y a b).trans_lt (max_lt (hy'.trans_le hrs) hab)
end EnvelopeProperty.Berkovich.RelativeSpectrum
