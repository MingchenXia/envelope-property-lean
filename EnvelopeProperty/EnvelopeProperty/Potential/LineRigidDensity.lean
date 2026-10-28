import EnvelopeProperty.Potential.LineClassification
import EnvelopeProperty.Potential.LineBranchEnds
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Density of actual evaluation points

Nontriviality and algebraic closure derive dense valuation range. Actual
evaluation points then approach every original Gauss point, and nested-disc
classification gives density in the entire original analytic line.
-/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}

/-- Algebraic closure and actual nontriviality derive dense value range; it is not an input. -/
theorem fc_denseRange_valuation (hne : ∃ t : K, 1 < w t) : DenseRange w := by
  let f : Kˣ →* (ℝ≥0)ˣ := Units.map w.toMonoidWithZeroHom.toMonoidHom
  let S : Subgroup (ℝ≥0)ˣ := f.range
  let _ : TopologicalSpace (ℝ≥0)ˣ := Preorder.topology (ℝ≥0)ˣ
  let _ : OrderTopology (ℝ≥0)ˣ := ⟨rfl⟩
  have hbot : S ≠ ⊥ := by
    obtain ⟨t,ht⟩ := hne
    have ht0 : t ≠ 0 := by
      intro hz
      rw [hz,map_zero] at ht
      exact not_lt_of_ge zero_le_one ht
    intro hS
    have hmem : f (Units.mk0 t ht0) ∈ S := ⟨Units.mk0 t ht0,rfl⟩
    rw [hS] at hmem
    have he := congrArg Units.val (Subgroup.mem_bot.mp hmem)
    change w t = 1 at he
    exact ht.ne' he
  have hnomin : ¬∃ u : (ℝ≥0)ˣ, IsLeast {g | g ∈ S ∧ 1 < g} u := by
    rintro ⟨u,hu,hmin⟩
    obtain ⟨t,ht⟩ := hu.1
    obtain ⟨a,ha⟩ := IsAlgClosed.exists_pow_nat_eq (t : K) zero_lt_two
    have ha0 : a ≠ 0 := by
      intro hz
      apply t.ne_zero
      rw [← ha,hz,zero_pow (by decide : (2 : ℕ) ≠ 0)]
    let z : (ℝ≥0)ˣ := f (Units.mk0 a ha0)
    have hsq : (w a)^2 = (u : ℝ≥0) := by
      rw [← map_pow,ha]
      exact congrArg Units.val ht
    have hu1 : (1 : ℝ≥0) < (u : ℝ≥0) := Units.val_lt_val.mpr hu.2
    have ha1 : 1 < w a := (one_lt_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp (hsq ▸ hu1)
    have hz1 : (1 : (ℝ≥0)ˣ) < z := by
      apply Units.val_lt_val.mp
      exact ha1
    have hzu : z < u := by
      apply Units.val_lt_val.mp
      change w a < (u : ℝ≥0)
      rw [← hsq,pow_two]
      exact lt_mul_of_one_lt_right (zero_lt_one.trans ha1) ha1
    exact not_le_of_gt hzu (hmin ⟨⟨Units.mk0 a ha0,rfl⟩,hz1⟩)
  have hd : Dense (S : Set (ℝ≥0)ˣ) := S.dense_of_no_min hbot hnomin
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨c,hac,hcb⟩ := exists_between hab
  have hc0 : c ≠ 0 := ne_of_gt (zero_le.trans_lt hac)
  have hb0 : b ≠ 0 := ne_of_gt (zero_le.trans_lt hab)
  have hcu : Units.mk0 c hc0 < Units.mk0 b hb0 := Units.val_lt_val.mp hcb
  obtain ⟨u,hu,hcu,hub⟩ := hd.exists_between hcu
  obtain ⟨t,ht⟩ := hu
  refine ⟨(u : ℝ≥0),⟨(t : K),?_⟩,hac.trans (Units.val_lt_val.mpr hcu),
    Units.val_lt_val.mpr hub⟩
  exact congrArg Units.val ht

/-- The original rigid evaluation point, represented by the already constructed radius-zero Gauss point. -/
def fcRigidPoint (a : K) : RelativeSpectrum w K[X] := centeredGauss (self w) a 0

/-- Every positive-radius actual Gauss point admits a sequence of original evaluation points. -/
theorem fc_exists_rigid_tendsto_gauss (hne : ∃ t : K, 1 < w t) (a : K) (r : ℝ≥0)
    (hr : 0 < r) :
    ∃ c : ℕ → K, Tendsto (fun n => fcRigidPoint (w := w) (c n)) atTop
      (𝓝 (centeredGauss (self w) a r)) := by
  obtain ⟨s,_,hs,hlim⟩ := Dense.exists_seq_strictMono_tendsto_of_lt
    (fc_denseRange_valuation hne) hr
  have hmem : ∀ n, ∃ c : K, w c = s n := fun n => (hs n).2
  choose c hc using hmem
  let g : ℕ → RelativeSpectrum w K[X] := fun n => fcRigidPoint (a+c n)
  have hcoord : (fun n => val (g n) (X-C a)) = s := by
    funext n
    change val (centeredGauss (self w) (a+c n) 0) (X-C a) = s n
    rw [fc_centeredGauss_val_X_sub_C,show a+c n-a = c n by ring,max_zero,hc n]
  have htWithin : Tendsto s atTop (𝓝[<] r) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim,Eventually.of_forall fun n => (hs n).1.2⟩
  have hg : Tendsto g atTop (fcBranchEndFilter (w := w) a r) := by
    apply tendsto_comap_iff.mpr
    change Tendsto (fun n => val (g n) (X-C a)) atTop (𝓝[<] r)
    rwa [hcoord]
  refine ⟨fun n => a+c n,?_⟩
  exact (fc_tendsto_branchEnd a r).comp hg

theorem fc_gauss_mem_closure_rigid (hne : ∃ t : K, 1 < w t) (a : K) (r : ℝ≥0) :
    centeredGauss (self w) a r ∈ closure (Set.range (fcRigidPoint (w := w))) := by
  by_cases hr : r = 0
  · subst r
    exact subset_closure ⟨a,rfl⟩
  · obtain ⟨c,hc⟩ := fc_exists_rigid_tendsto_gauss hne a r (pos_iff_ne_zero.mpr hr)
    exact isClosed_closure.mem_of_tendsto hc
      (Eventually.of_forall fun n => subset_closure ⟨c n,rfl⟩)

/-- Every actual analytic-line point is in the closure of the actual evaluation points. -/
theorem fc_denseRange_rigid (hne : ∃ t : K, 1 < w t) : DenseRange (fcRigidPoint (w := w)) := by
  intro x
  rcases fc_gauss_or_nested_discs x with ⟨a,r,rfl⟩ | ⟨a,r,_,_,_,_,_,_,hlim⟩
  · exact fc_gauss_mem_closure_rigid hne a r
  · exact isClosed_closure.mem_of_tendsto hlim
      (Eventually.of_forall fun n => fc_gauss_mem_closure_rigid hne (a n) (r n))

section NormedField

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [IsAlgClosed L]

/-- The source field convention supplies nontriviality without an additional density assumption. -/
theorem fc_denseRange_rigid_norm :
    DenseRange (fcRigidPoint (w := NormedField.valuation (K := L))) := by
  apply fc_denseRange_rigid
  obtain ⟨t,ht⟩ := NormedField.exists_lt_norm L 1
  refine ⟨t,?_⟩
  change (1 : ℝ≥0) < ‖t‖₊
  exact_mod_cast ht

end NormedField

end EnvelopeProperty.Berkovich.RelativeSpectrum
