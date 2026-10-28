import EnvelopeProperty.Potential.LineStandardAffinoid

/-!
# The actual radial skeleton retraction of a standard affinoid

The capped minimum of the hole-coordinate values gives an explicit continuous
retraction onto the finite union of actual Gauss-radius intervals.
-/

open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}

section AlgebraicallyClosed

variable [IsAlgClosed K]

/-- Inflation is independent of its auxiliary centre on the algebraically closed line. -/
theorem fcCenteredInflation_center_independent (a b : K)
    (x : RelativeSpectrum w K[X]) (s : ℝ≥0) :
    fcCenteredInflation a x s = fcCenteredInflation b x s := by
  apply fc_ext_linear
  intro c
  simp only [fcCenteredInflation_val_X_sub_C]

/-- Inflating a Gauss point by a smaller radius fixes the original point. -/
theorem fcCenteredInflation_fix_gauss (a b : K) (r s : ℝ≥0) (hs : s ≤ r) :
    fcCenteredInflation a (centeredGauss (self w) b r) s = centeredGauss (self w) b r := by
  apply fc_ext_linear
  intro c
  simp only [fcCenteredInflation_val_X_sub_C, fc_centeredGauss_val_X_sub_C]
  rw [max_assoc, max_eq_left hs]

end AlgebraicallyClosed

namespace FCStandardAffinoid

variable {m : ℕ} (U : FCStandardAffinoid w m)

/-- The actual finite union of Gauss-radius intervals from the holes to the outer boundary. -/
def radialSkeleton : Set (RelativeSpectrum w K[X]) :=
  insert U.outerGauss (⋃ j, (fun s => centeredGauss (self w) (U.holeCenter j) s) ''
    Set.Icc (U.holeRadius j) U.radius)

/-- The cap guarantees a nonempty finite minimum, also for an affinoid without holes. -/
def skeletonRadius (x : RelativeSpectrum w K[X]) : ℝ≥0 :=
  Finset.univ.inf' (by simp)
    (Fin.cases U.radius (fun j => val x (X-C (U.holeCenter j))))

theorem skeletonRadius_le_outer (x : RelativeSpectrum w K[X]) :
    U.skeletonRadius x ≤ U.radius :=
  Finset.inf'_le _ (Finset.mem_univ (0 : Fin (m+1)))

theorem skeletonRadius_le_hole (x : RelativeSpectrum w K[X]) (j : Fin m) :
    U.skeletonRadius x ≤ val x (X-C (U.holeCenter j)) :=
  Finset.inf'_le _ (Finset.mem_univ j.succ)

theorem le_skeletonRadius (x : RelativeSpectrum w K[X]) (s : ℝ≥0)
    (hc : s ≤ U.radius) (hh : ∀ j, s ≤ val x (X-C (U.holeCenter j))) :
    s ≤ U.skeletonRadius x := by
  apply Finset.le_inf'
  intro i _
  exact Fin.cases hc hh i

theorem skeletonRadius_attained (x : RelativeSpectrum w K[X]) :
    U.skeletonRadius x = U.radius ∨
      ∃ j, U.skeletonRadius x = val x (X-C (U.holeCenter j)) := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_inf'
    (by simp : (Finset.univ : Finset (Fin (m+1))).Nonempty)
    (Fin.cases U.radius (fun j => val x (X-C (U.holeCenter j))))
  cases i using Fin.cases with
  | zero => exact Or.inl hi
  | succ j => exact Or.inr ⟨j,hi⟩

theorem continuous_skeletonRadius : Continuous U.skeletonRadius := by
  apply Continuous.finset_inf'_apply
  intro i _
  exact Fin.cases continuous_const (fun j => continuous_val_apply (X-C (U.holeCenter j))) i

theorem radialSegment_mem (j : Fin m) (s : ℝ≥0)
    (hlo : U.holeRadius j ≤ s) (hhi : s ≤ U.radius) :
    centeredGauss (self w) (U.holeCenter j) s ∈ U.carrier := by
  constructor
  · rw [fc_centeredGauss_val_X_sub_C]
    exact max_le (U.holeCenter_le j) hhi
  · intro i
    have hi := (U.holeGauss_mem j).2 i
    rw [fc_centeredGauss_val_X_sub_C] at hi ⊢
    exact hi.trans (max_le_max_left _ hlo)

theorem radialSkeleton_subset : U.radialSkeleton ⊆ U.carrier := by
  intro x hx
  rcases Set.mem_insert_iff.mp hx with h | h
  · exact h ▸ U.outerGauss_mem
  · obtain ⟨j,s,hs,rfl⟩ := Set.mem_iUnion.mp h
    exact U.radialSegment_mem j s hs.1 hs.2

theorem skeletonRadius_outer : U.skeletonRadius U.outerGauss = U.radius := by
  apply le_antisymm (U.skeletonRadius_le_outer _)
  apply U.le_skeletonRadius _ _ le_rfl
  intro j
  rw [outerGauss,fc_centeredGauss_val_X_sub_C]
  exact le_max_right _ _

theorem skeletonRadius_segment (j : Fin m) (s : ℝ≥0) (hhi : s ≤ U.radius) :
    U.skeletonRadius (centeredGauss (self w) (U.holeCenter j) s) = s := by
  apply le_antisymm
  · simpa only [fc_centeredGauss_val_X_sub_C, sub_self, map_zero, zero_max] using
      U.skeletonRadius_le_hole (centeredGauss (self w) (U.holeCenter j) s) j
  · apply U.le_skeletonRadius _ _ hhi
    intro i
    rw [fc_centeredGauss_val_X_sub_C]
    exact le_max_right _ _

/-- The actual polynomial-spectrum formula for the skeleton projection. -/
def skeletonProjection (x : RelativeSpectrum w K[X]) : RelativeSpectrum w K[X] :=
  fcCenteredInflation U.center x (U.skeletonRadius x)

variable [IsAlgClosed K]

theorem continuous_skeletonProjection : Continuous U.skeletonProjection := by
  rw [fc_continuous_iff_linear]
  intro b
  change Continuous fun x : RelativeSpectrum w K[X] =>
    val (fcCenteredInflation U.center x (U.skeletonRadius x)) (X-C b)
  simp only [fcCenteredInflation_val_X_sub_C]
  exact (continuous_val_apply _).max U.continuous_skeletonRadius

theorem skeletonProjection_mem {x : RelativeSpectrum w K[X]} (hx : x ∈ U.carrier) :
    U.skeletonProjection x ∈ U.radialSkeleton := by
  rcases U.skeletonRadius_attained x with h | ⟨j,h⟩
  · apply Set.mem_insert_iff.mpr
    apply Or.inl
    change fcCenteredInflation U.center x (U.skeletonRadius x) = U.outerGauss
    rw [h]
    exact fcCenteredInflation_eq_gauss U.center x U.radius hx.1
  · apply Set.mem_insert_of_mem
    apply Set.mem_iUnion.mpr
    refine ⟨j,U.skeletonRadius x,⟨?_,U.skeletonRadius_le_outer x⟩,?_⟩
    · rw [h]
      exact hx.2 j
    · change centeredGauss (self w) (U.holeCenter j) (U.skeletonRadius x) =
        fcCenteredInflation U.center x (U.skeletonRadius x)
      rw [fcCenteredInflation_center_independent U.center (U.holeCenter j)]
      exact (fcCenteredInflation_eq_gauss (U.holeCenter j) x _ h.ge).symm

theorem skeletonProjection_eq_self {x : RelativeSpectrum w K[X]}
    (hx : x ∈ U.radialSkeleton) : U.skeletonProjection x = x := by
  rcases Set.mem_insert_iff.mp hx with h | h
  · subst x
    change fcCenteredInflation U.center U.outerGauss (U.skeletonRadius U.outerGauss) =
      U.outerGauss
    rw [U.skeletonRadius_outer]
    exact fcCenteredInflation_fix_gauss _ _ _ _ le_rfl
  · obtain ⟨j,s,hs,rfl⟩ := Set.mem_iUnion.mp h
    change fcCenteredInflation U.center (centeredGauss (self w) (U.holeCenter j) s)
      (U.skeletonRadius (centeredGauss (self w) (U.holeCenter j) s)) = _
    rw [U.skeletonRadius_segment j s hs.2]
    exact fcCenteredInflation_fix_gauss _ _ _ _ le_rfl

/-- A genuine continuous map to the subspace skeleton, defined on the actual affinoid. -/
def radialRetraction : C(U.carrier, U.radialSkeleton) where
  toFun x := ⟨U.skeletonProjection x.1,U.skeletonProjection_mem x.2⟩
  continuous_toFun := (U.continuous_skeletonProjection.comp continuous_subtype_val).subtype_mk _

theorem radialRetraction_eq_self (x : U.radialSkeleton) :
    (U.radialRetraction ⟨x.1,U.radialSkeleton_subset x.2⟩).1 = x.1 :=
  U.skeletonProjection_eq_self x.2

end FCStandardAffinoid
end EnvelopeProperty.Berkovich.RelativeSpectrum
