import EnvelopeProperty.Potential.LineOpenHoleContainment
import EnvelopeProperty.Potential.LineAffinoidUnions

/-! # Exact surviving ORIGINAL Gauss boundaries on actual intersections -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m n : ℕ}
variable (V : FCStandardAffinoid w n)

/-- ORIGINAL positive-radius Gauss membership is EXACTLY outer bounds and absence of a STRICTLY larger containing actual hole. -/
theorem centeredGauss_mem_iff_no_larger_hole (a : K) (r : ℝ≥0) (hr : 0 < r) :
    centeredGauss (self w) a r ∈ V.carrier ↔
      w (a-V.center) ≤ V.radius ∧ r ≤ V.radius ∧
        ∀ j, ¬(fcOpenLinearDisc (w := w) a r ⊆ V.holeOpenDisc j ∧ r < V.holeRadius j) := by
  constructor
  · intro hx
    have hout := hx.1
    rw [fc_centeredGauss_val_X_sub_C] at hout
    refine ⟨(max_le_iff.mp hout).1,(max_le_iff.mp hout).2,fun j hj => ?_⟩
    have hsub := (fc_openLinearDisc_subset_iff a (V.holeCenter j) r (V.holeRadius j) hr).mp hj.1
    have hval := hx.2 j
    rw [fc_centeredGauss_val_X_sub_C] at hval
    exact not_lt_of_ge hval (max_lt hsub.2 hj.2)
  · rintro ⟨hc,hR,hn⟩
    refine ⟨?_,fun j => ?_⟩
    · rw [fc_centeredGauss_val_X_sub_C]
      exact max_le hc hR
    · rw [fc_centeredGauss_val_X_sub_C]
      apply le_of_not_gt
      intro hbad
      have hd := max_lt_iff.mp hbad
      exact hn j ⟨(fc_openLinearDisc_subset_iff a (V.holeCenter j) r (V.holeRadius j) hr).mpr
        ⟨hd.2.le,hd.1⟩,hd.2⟩

variable (U : FCStandardAffinoid w m)

/-- EVERY ORIGINAL source-hole Gauss boundary survives the ACTUAL intersection iff no STRICTLY larger original opposite hole contains it. -/
theorem holeGauss_mem_intersection_iff_no_larger_hole (hR : U.radius ≤ V.radius)
    (x : RelativeSpectrum w K[X]) (hxU : x ∈ U.carrier) (hxV : x ∈ V.carrier) (i : Fin m) :
    centeredGauss (self w) (U.holeCenter i) (U.holeRadius i) ∈ U.carrier ∩ V.carrier ↔
      ∀ j, ¬(U.holeOpenDisc i ⊆ V.holeOpenDisc j ∧ U.holeRadius i < V.holeRadius j) := by
  have hUV : w (U.center-V.center) ≤ V.radius :=
    (fc_center_distance_bound x U.center V.center).trans (max_le (hxU.1.trans hR) hxV.1)
  have hc : w (U.holeCenter i-V.center) ≤ V.radius := by
    have he : U.holeCenter i-V.center = (U.holeCenter i-U.center)+(U.center-V.center) := by ring
    rw [he]
    exact (w.map_add _ _).trans (max_le ((U.holeCenter_le i).trans hR) hUV)
  constructor
  · intro h
    exact ((V.centeredGauss_mem_iff_no_larger_hole _ _ (U.holeRadius_pos i)).mp h.2).2.2
  · intro h
    exact ⟨U.holeGauss_mem i,(V.centeredGauss_mem_iff_no_larger_hole _ _ (U.holeRadius_pos i)).mpr
      ⟨hc,(U.holeRadius_le i).trans hR,h⟩⟩
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
