import EnvelopeProperty.Potential.LineSeparatedAffinoid
import EnvelopeProperty.Potential.LineRigidDensity

/-! # Actual rigid closed-disc neighbourhoods and appended separated holes -/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}

theorem fc_exists_positive_radius_lt_finite {m : ℕ} (R : ℝ≥0) (hR : 0 < R)
    (d : Fin m → ℝ≥0) (hd : ∀ j, 0 < d j) :
    ∃ r : ℝ≥0, 0 < r ∧ r < R ∧ ∀ j, r < d j := by
  classical
  let B : Finset ℝ≥0 := insert R (Finset.univ.image d)
  have hB : B.Nonempty := Finset.insert_nonempty _ _
  let q := B.min' hB
  have hq : 0 < q := (Finset.lt_min'_iff B hB).mpr (by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hR
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
      exact hd j)
  obtain ⟨r,hr,hrq⟩ := exists_between hq
  refine ⟨r,hr,hrq.trans_le (Finset.min'_le B _ (Finset.mem_insert_self _ _)),?_⟩
  intro j
  exact hrq.trans_le (Finset.min'_le B _ (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (Finset.mem_univ j))))

private theorem fc_disjoint_openDiscs_of_strict_distance (a b : K) (r s : ℝ≥0)
    (hr : r < w (a-b)) (hs : s < w (a-b)) :
    Disjoint {x : RelativeSpectrum w K[X] | val x (X-C a) < r}
      {x | val x (X-C b) < s} := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact not_lt_of_ge (fc_center_distance_bound x a b) (max_lt (hx.trans hr) (hy.trans hs))

namespace FCStandardAffinoid

variable {m : ℕ} (U : FCStandardAffinoid w m)

private theorem fc_rigid_core_values (a : K) (ha : fcRigidPoint (w := w) a ∈ U.strictCore) :
    w (a-U.center) < U.radius ∧ ∀ j, U.holeRadius j < w (a-U.holeCenter j) := by
  simpa only [strictCore,Set.mem_ofPred_eq,fcRigidPoint,fc_centeredGauss_val_X_sub_C,max_zero] using ha

/-- The literal original affinoid with one additional actual open hole. -/
def puncture (a : K) (r : ℝ≥0) (hr : 0 < r)
    (ha : fcRigidPoint (w := w) a ∈ U.strictCore)
    (hR : r < U.radius) (hd : ∀ j, r < w (a-U.holeCenter j)) : FCStandardAffinoid w (m+1) where
  center := U.center
  radius := U.radius
  holeCenter := Fin.cases a U.holeCenter
  holeRadius := Fin.cases r U.holeRadius
  holeRadius_pos := Fin.cases hr U.holeRadius_pos
  holeRadius_le := Fin.cases hR.le U.holeRadius_le
  holeCenter_le := Fin.cases (U.fc_rigid_core_values a ha).1.le U.holeCenter_le
  holes_disjoint := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro h00
        exact False.elim (h00 rfl)
      · intro _
        exact fc_disjoint_openDiscs_of_strict_distance a (U.holeCenter j) r (U.holeRadius j)
          (hd j) ((U.fc_rigid_core_values a ha).2 j)
    · intro i j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro _
        exact (fc_disjoint_openDiscs_of_strict_distance a (U.holeCenter i) r (U.holeRadius i)
          (hd i) ((U.fc_rigid_core_values a ha).2 i)).symm
      · intro hij
        exact U.holes_disjoint (fun he => hij (congrArg Fin.succ he))

theorem puncture_carrier (a : K) (r : ℝ≥0) (hr : 0 < r)
    (ha : fcRigidPoint (w := w) a ∈ U.strictCore)
    (hR : r < U.radius) (hd : ∀ j, r < w (a-U.holeCenter j)) :
    (U.puncture a r hr ha hR hd).carrier =
      U.carrier ∩ {x | r ≤ val x (X-C a)} := by
  ext x
  simp only [carrier,puncture,Set.mem_ofPred_eq,Set.mem_inter_iff,Fin.forall_fin_succ,
    Fin.cases_zero,Fin.cases_succ]
  tauto

theorem puncture_strictCore (a : K) (r : ℝ≥0) (hr : 0 < r)
    (ha : fcRigidPoint (w := w) a ∈ U.strictCore)
    (hR : r < U.radius) (hd : ∀ j, r < w (a-U.holeCenter j)) :
    (U.puncture a r hr ha hR hd).strictCore =
      U.strictCore ∩ {x | r < val x (X-C a)} := by
  ext x
  simp only [strictCore,puncture,Set.mem_ofPred_eq,Set.mem_inter_iff,Fin.forall_fin_succ,
    Fin.cases_zero,Fin.cases_succ]
  tauto

theorem puncture_boundary (a : K) (r : ℝ≥0) (hr : 0 < r)
    (ha : fcRigidPoint (w := w) a ∈ U.strictCore)
    (hR : r < U.radius) (hd : ∀ j, r < w (a-U.holeCenter j)) :
    (U.puncture a r hr ha hR hd).boundary = insert (centeredGauss (self w) a r) U.boundary := by
  ext x
  simp only [boundary,outerGauss,puncture,Set.mem_insert_iff,Set.mem_range,Fin.exists_fin_succ,
    Fin.cases_zero,Fin.cases_succ]
  tauto

theorem IsSeparated.puncture (hsep : U.IsSeparated)
    (a : K) (r : ℝ≥0) (hr : 0 < r)
    (ha : fcRigidPoint (w := w) a ∈ U.strictCore)
    (hR : r < U.radius) (hd : ∀ j, r < w (a-U.holeCenter j)) :
    (U.puncture a r hr ha hR hd).IsSeparated := by
  constructor
  · exact Fin.cases (U.fc_rigid_core_values a ha).1 hsep.holeCenter_lt
  · intro i
    refine Fin.cases ?_ ?_ i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro h00
        exact False.elim (h00 rfl)
      · intro _
        exact hd j
    · intro i j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro _
        change U.holeRadius i < w (U.holeCenter i-a)
        rw [show U.holeCenter i-a = -(a-U.holeCenter i) by ring,Valuation.map_neg]
        exact (U.fc_rigid_core_values a ha).2 i
      · intro hij
        exact hsep.holeRadius_lt_distance i j (fun he => hij (congrArg Fin.succ he))

end FCStandardAffinoid

variable [IsAlgClosed K]

/-- Whole actual positive-radius closed discs form a neighbourhood basis at each original rigid point. -/
theorem fc_exists_closedDisc_rigid_nhds (a : K) {N : Set (RelativeSpectrum w K[X])}
    (hN : N ∈ 𝓝 (fcRigidPoint (w := w) a)) :
    ∃ r : ℝ≥0, 0 < r ∧ {x : RelativeSpectrum w K[X] | val x (X-C a) ≤ r} ⊆ N := by
  obtain ⟨m,U,_,ha,hUN⟩ := fc_exists_separated_standardAffinoid_nhds (fcRigidPoint a) hN
  have hav := U.fc_rigid_core_values a ha
  obtain ⟨r,hr,hrR,hrd⟩ := fc_exists_positive_radius_lt_finite U.radius
    ((show 0 ≤ w (a-U.center) from zero_le).trans_lt hav.1)
    (fun j => w (a-U.holeCenter j))
    (fun j => (U.holeRadius_pos j).trans (hav.2 j))
  refine ⟨r,hr,fun x hx => hUN ?_⟩
  constructor
  · exact (fc_linear_bound x a U.center).trans (max_le (hx.trans hrR.le) hav.1.le)
  · intro j
    rw [fc_linear_value_eq_max x a (U.holeCenter j) (ne_of_lt (hx.trans_lt (hrd j))),
      max_eq_right (hx.trans (hrd j).le)]
    exact (hav.2 j).le

end EnvelopeProperty.Berkovich.RelativeSpectrum
