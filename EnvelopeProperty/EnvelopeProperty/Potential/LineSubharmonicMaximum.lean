import EnvelopeProperty.Potential.LineSubharmonic
import EnvelopeProperty.Potential.LineSeparatedHarmonic
import EnvelopeProperty.Potential.LineAffinoidPuncture

/-! # The actual subharmonic strong maximum principle on the line -/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
variable {u : RelativeSpectrum w K[X] → EReal} {Ω : Set (RelativeSpectrum w K[X])}

/-- Every actual local maximum is constant on an actual neighbourhood, with all separating data derived. -/
theorem IsLineSubharmonicOn.eventually_eq_of_isLocalMax (hu : IsLineSubharmonicOn u Ω)
    (hnt : ∃ t : K, 1 < w t) (hΩ : IsOpen Ω) (x : RelativeSpectrum w K[X])
    (hx : x ∈ Ω) (hmax : IsLocalMax u x) : ∀ᶠ y in 𝓝 x, u y = u x := by
  classical
  by_cases hbot : u x = ⊥
  · exact hmax.mono fun y hy => le_antisymm hy (hbot ▸ bot_le)
  let R := (u x).toReal
  have hR : u x = (R : EReal) := (EReal.coe_toReal (hu.ne_top x hx) hbot).symm
  have hN : Ω ∩ {y | u y ≤ u x} ∈ 𝓝 x := Filter.inter_mem (hΩ.mem_nhds hx) hmax
  obtain ⟨m,U,hsep,hxU,hUN⟩ := fc_exists_separated_standardAffinoid_nhds x hN
  have hUΩ : U.carrier ⊆ Ω := fun y hy => (hUN hy).1
  have hupper : ∀ y ∈ U.carrier, u y ≤ (R : EReal) := by
    intro y hy
    rw [← hR]
    exact (hUN hy).2
  have hcore : ∀ y ∈ U.strictCore, u y = u x := by
    intro y hy
    by_contra hne
    have hyU := interior_subset (U.strictCore_subset_interior hy)
    have hylt : u y < u x := lt_of_le_of_ne (by rw [hR]; exact hupper y hyU) hne
    obtain ⟨b,hyb,hbR⟩ := EReal.lt_iff_exists_real_btwn.mp hylt
    have hbRreal : b < R := by rw [hR] at hbR; exact_mod_cast hbR
    obtain ⟨O,hOo,hOeq⟩ := upperSemicontinuousOn_iff_preimage_Iio.mp hu.upperSemicontinuousOn (b : EReal)
    have hyO : y ∈ O := by
      have hmem : y ∈ Ω ∩ u ⁻¹' Set.Iio (b : EReal) := ⟨hUΩ hyU,hyb⟩
      rw [hOeq] at hmem
      exact hmem.2
    obtain ⟨a,ha⟩ := (fc_denseRange_rigid hnt).exists_mem_open
      (U.isOpen_strictCore.inter hOo) ⟨y,hy,hyO⟩
    have haΩ : fcRigidPoint (w := w) a ∈ Ω :=
      hUΩ (interior_subset (U.strictCore_subset_interior ha.1))
    have hab : u (fcRigidPoint (w := w) a) < (b : EReal) := by
      have hmem : fcRigidPoint (w := w) a ∈ Ω ∩ O := ⟨haΩ,ha.2⟩
      rw [← hOeq] at hmem
      exact hmem.2
    obtain ⟨r₀,hr₀,hdisc⟩ := fc_exists_closedDisc_rigid_nhds a
      ((hΩ.inter hOo).mem_nhds ⟨haΩ,ha.2⟩)
    have hpx : 0 < val x (X-C a) := by
      apply pos_iff_ne_zero.mpr
      intro hz
      have he : x = fcRigidPoint (w := w) a := by
        simpa only [fcCenteredInflation_zero,fcRigidPoint] using
          fcCenteredInflation_eq_gauss a x 0 hz.le
      rw [he] at hbR
      exact (hab.trans hbR).false
    have had : ∀ j, U.holeRadius j < w (a-U.holeCenter j) := by
      intro j
      simpa only [fcRigidPoint,fc_centeredGauss_val_X_sub_C,max_zero] using ha.1.2 j
    obtain ⟨r,hr,hrcap,hrd⟩ := fc_exists_positive_radius_lt_finite
      (min r₀ U.radius) (lt_min hr₀ (U.radius_pos_of_strictCore_nonempty ⟨x,hxU⟩))
      (Fin.cases (val x (X-C a)) (fun j => w (a-U.holeCenter j)))
      (Fin.cases hpx (fun j => (U.holeRadius_pos j).trans (had j)))
    have hrr₀ : r < r₀ := hrcap.trans_le (min_le_left _ _)
    have hrR : r < U.radius := hrcap.trans_le (min_le_right _ _)
    have hrx : r < val x (X-C a) := by simpa only [Fin.cases_zero] using hrd 0
    have hrd' : ∀ j, r < w (a-U.holeCenter j) := by
      intro j
      simpa only [Fin.cases_succ] using hrd j.succ
    let V := U.puncture a r hr ha.1 hrR hrd'
    have hVsep : V.IsSeparated := hsep.puncture U a r hr ha.1 hrR hrd'
    have hVsub : V.carrier ⊆ U.carrier := by
      rw [show V.carrier = _ from U.puncture_carrier a r hr ha.1 hrR hrd']
      exact Set.inter_subset_left
    have hxV : x ∈ V.strictCore := by
      rw [show V.strictCore = _ from U.puncture_strictCore a r hr ha.1 hrR hrd']
      exact ⟨hxU,hrx⟩
    let z₀ := centeredGauss (self w) a r
    have hzB : z₀ ∈ V.boundary := by
      rw [show V.boundary = _ from U.puncture_boundary a r hr ha.1 hrR hrd']
      exact Set.mem_insert _ _
    have hzb : u z₀ ≤ (b : EReal) := by
      have hzD : val z₀ (X-C a) ≤ r₀ := by
        simpa only [z₀,fc_centeredGauss_val_X_sub_C,sub_self,map_zero,zero_max] using hrr₀.le
      have hzO := hdisc hzD
      rw [← hOeq] at hzO
      exact hzO.2.le
    let β : V.boundary → ℝ := fun z => if z.1 = z₀ then b else R
    obtain ⟨H,hH,hHB⟩ := V.exists_isHarmonic_boundary_values β
    have hHBupper : ∀ z : V.carrier, z.1 ∈ V.boundary → H z ≤ R := by
      intro z hz
      rw [hHB ⟨z.1,hz⟩]
      dsimp [β]
      split_ifs
      · exact hbRreal.le
      · exact le_rfl
    have hHBlow : ∃ z : V.carrier, z.1 ∈ V.boundary ∧ H z < R := by
      refine ⟨⟨z₀,V.boundary_subset hzB⟩,hzB,?_⟩
      rw [hHB ⟨z₀,hzB⟩]
      simpa only [β,if_pos rfl] using hbRreal
    let xV : V.carrier := ⟨x,interior_subset (V.strictCore_subset_interior hxV)⟩
    have hHx : H xV < R := hH.lt_of_boundary_le_of_exists_lt V hVsep R hHBupper hHBlow xV hxV
    have hcomp : u x ≤ (H xV : EReal) := hu.comparison V H
      (hVsub.trans hUΩ) hH (by
        intro z hz
        rw [hHB ⟨z.1,hz⟩]
        dsimp [β]
        split_ifs with he
        · simpa only [he] using hzb
        · exact hupper z.1 (hVsub z.2)) xV
    rw [hR] at hcomp
    have hle : R ≤ H xV := by exact_mod_cast hcomp
    exact not_le_of_gt hHx hle
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U.strictCore := U.isOpen_strictCore.mem_nhds hxU
  exact hnear.mono fun y hy => hcore y hy

section NormedField

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [IsAlgClosed L]
variable {v : RelativeSpectrum (NormedField.valuation (K := L)) L[X] → EReal}
variable {D : Set (RelativeSpectrum (NormedField.valuation (K := L)) L[X])}

/-- The source nontrivially normed field convention supplies the actual valuation nontriviality. -/
theorem IsLineSubharmonicOn.eventually_eq_of_isLocalMax_norm (hv : IsLineSubharmonicOn v D)
    (hD : IsOpen D) (x : RelativeSpectrum (NormedField.valuation (K := L)) L[X])
    (hx : x ∈ D) (hmax : IsLocalMax v x) : ∀ᶠ y in 𝓝 x, v y = v x := by
  apply hv.eventually_eq_of_isLocalMax _ hD x hx hmax
  obtain ⟨t,ht⟩ := NormedField.exists_lt_norm L 1
  refine ⟨t,?_⟩
  change (1 : ℝ≥0) < ‖t‖₊
  exact_mod_cast ht

end NormedField

end EnvelopeProperty.Berkovich.RelativeSpectrum
