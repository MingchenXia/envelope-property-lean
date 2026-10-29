import EnvelopeProperty.Potential.LineTopology
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Actual terminal annuli in every residue branch

Linear-coordinate convergence shows that every neighbourhood of an original
Gauss point contains a whole terminal annulus in each actual residue branch.
-/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}

private theorem fc_val_constant (x : RelativeSpectrum w K[X]) (c : K) :
    val x (C c) = w c := x.2 c

/-- Unequal linear and constant summand values give the actual ultrametric equality. -/
theorem fc_linear_value_eq_max (x : RelativeSpectrum w K[X]) (a b : K)
    (h : val x (X-C a) ≠ w (a-b)) :
    val x (X-C b) = max (val x (X-C a)) (w (a-b)) := by
  have he : (X-C b : K[X]) = (X-C a)+C (a-b) := by
    simp only [map_sub]
    ring
  rw [he]
  have hn : val x (X-C a) ≠ val x (C (a-b)) := by
    simpa only [fc_val_constant] using h
  simpa only [fc_val_constant] using (val x).map_add_of_distinct_val hn

variable [IsAlgClosed K]

/-- Convergence to the original line is determined by its original linear values. -/
theorem fc_tendsto_iff_linear {ι : Type*} {l : Filter ι}
    {g : ι → RelativeSpectrum w K[X]} {x : RelativeSpectrum w K[X]} :
    Tendsto g l (𝓝 x) ↔
      ∀ a : K, Tendsto (fun i => val (g i) (X-C a)) l (𝓝 (val x (X-C a))) := by
  constructor
  · intro hg a
    exact ((continuous_val_apply (X-C a)).tendsto x).comp hg
  · intro hg
    apply isClosedEmbedding_subtypeVal.tendsto_nhds_iff.mpr
    apply Spectrum.isInducing_toFun.tendsto_nhds_iff.mpr
    rw [tendsto_pi_nhds]
    intro p
    change Tendsto (fun i => val (g i) p) l (𝓝 (val x p))
    have hp : ∀ s : Multiset K,
        Tendsto (fun i => val (g i) ((s.map fun a => X-C a).prod)) l
          (𝓝 (val x ((s.map fun a => X-C a).prod))) := by
      intro s
      induction s using Multiset.induction_on with
      | empty =>
        simp only [Multiset.map_zero,Multiset.prod_zero,map_one]
        exact tendsto_const_nhds
      | @cons a s ih =>
        simp only [Multiset.map_cons,Multiset.prod_cons,map_mul]
        exact (hg a).mul ih
    rw [(IsAlgClosed.splits p).eq_prod_roots]
    simp only [map_mul,fc_val_constant]
    exact tendsto_const_nhds.mul (hp p.roots)

/-- The actual line filter where a branch coordinate tends to its outer radius from below. -/
def fcBranchEndFilter (b : K) (r : ℝ≥0) : Filter (RelativeSpectrum w K[X]) :=
  Filter.comap (fun y => val y (X-C b)) (𝓝[<] r)

/-- The whole actual branch end converges, without selecting paths or certificates. -/
theorem fc_tendsto_branchEnd (b : K) (r : ℝ≥0) :
    Tendsto id (fcBranchEndFilter (w := w) b r) (𝓝 (centeredGauss (self w) b r)) := by
  apply fc_tendsto_iff_linear.mpr
  intro c
  change Tendsto (fun y : RelativeSpectrum w K[X] => val y (X-C c))
    (fcBranchEndFilter b r) (𝓝 (val (centeredGauss (self w) b r) (X-C c)))
  rw [fc_centeredGauss_val_X_sub_C]
  have htWithin : Tendsto (fun y : RelativeSpectrum w K[X] => val y (X-C b))
      (fcBranchEndFilter b r) (𝓝[<] r) := tendsto_comap
  have ht : Tendsto (fun y : RelativeSpectrum w K[X] => val y (X-C b))
      (fcBranchEndFilter b r) (𝓝 r) := htWithin.mono_right nhdsWithin_le_nhds
  by_cases hd : w (b-c) < r
  · have hlt : ∀ᶠ y in fcBranchEndFilter (w := w) b r, w (b-c) < val y (X-C b) :=
      ht.eventually (eventually_gt_nhds hd)
    have he : (fun y : RelativeSpectrum w K[X] => val y (X-C c)) =ᶠ[fcBranchEndFilter b r]
        (fun y => val y (X-C b)) := hlt.mono fun y hy => by
      change val y (X-C c) = val y (X-C b)
      rw [fc_linear_value_eq_max y b c hy.ne',max_eq_left hy.le]
    rw [max_eq_right hd.le]
    exact ht.congr' he.symm
  · have hdr : r ≤ w (b-c) := le_of_not_gt hd
    have hlt : ∀ᶠ y in fcBranchEndFilter (w := w) b r, val y (X-C b) < r :=
      htWithin.eventually self_mem_nhdsWithin
    have he : (fun y : RelativeSpectrum w K[X] => val y (X-C c)) =ᶠ[fcBranchEndFilter b r]
        (fun _ => w (b-c)) := hlt.mono fun y hy => by
      change val y (X-C c) = w (b-c)
      rw [fc_linear_value_eq_max y b c (hy.trans_le hdr).ne,
        max_eq_right (hy.le.trans hdr)]
    rw [max_eq_left hdr]
    exact tendsto_const_nhds.congr' he.symm

/-- Every actual neighbourhood contains a terminal annulus in each original residue branch. -/
theorem fc_exists_annulus_subset_nhds (a b : K) (r : ℝ≥0) (hr : 0 < r)
    (hb : w (b-a) ≤ r) {V : Set (RelativeSpectrum w K[X])}
    (hV : V ∈ 𝓝 (centeredGauss (self w) a r)) :
    ∃ ρ : ℝ≥0, ρ < r ∧ {y : RelativeSpectrum w K[X] | ρ < val y (X-C b) ∧
      val y (X-C b) < r} ⊆ V := by
  have he : centeredGauss (self w) b r = centeredGauss (self w) a r :=
    fc_centeredGauss_eq_of_center_dist_le a b r hb
  have hVb : V ∈ 𝓝 (centeredGauss (self w) b r) := by rwa [he]
  have hEnd : V ∈ fcBranchEndFilter (w := w) b r :=
    (fc_tendsto_branchEnd b r).eventually hVb
  obtain ⟨ρ,hρ,hsub⟩ := ((nhdsLT_basis_of_exists_lt ⟨0,hr⟩).comap
    (fun y : RelativeSpectrum w K[X] => val y (X-C b))).mem_iff.mp hEnd
  exact ⟨ρ,hρ,hsub⟩

end EnvelopeProperty.Berkovich.RelativeSpectrum
