import EnvelopeProperty.Potential.LineHarmonicRestriction
import EnvelopeProperty.Potential.LineSubharmonicMaximum

/-! # Actual upper-semicontinuous boundary comparison and subharmonic locality -/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}

namespace FCStandardAffinoid

/-- The topological boundary argument needs upper semicontinuity, including bottom values. -/
theorem le_zero_of_boundary_of_local_max_plateau_usc {m : ℕ} (U : FCStandardAffinoid w m)
    (f : RelativeSpectrum w K[X] → EReal) (hf : UpperSemicontinuousOn f U.carrier)
    (hB : ∀ z ∈ U.boundary, f z ≤ 0)
    (hplateau : ∀ x ∈ interior U.carrier, 0 < f x → IsLocalMax f x →
      ∀ᶠ y in 𝓝 x, f y = f x) :
    ∀ x ∈ U.carrier, f x ≤ 0 := by
  let _ : ConnectedSpace U.carrier := isConnected_iff_connectedSpace.mp U.isConnected_carrier
  let g : U.carrier → EReal := fun x => f x.1
  have hg : UpperSemicontinuous g := upperSemicontinuousOn_iff_restrict.mpr hf
  obtain ⟨x,hx,hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
    ⟨U.outerGauss,U.outerGauss_mem⟩ U.isCompact_carrier hf
  intro y hy
  by_contra hn
  have hpos : 0 < f x := (lt_of_not_ge hn).trans_le (hmax hy)
  let M : Set U.carrier := {z | f x ≤ g z}
  have hclosed : IsClosed M := hg.isClosed_preimage (f x)
  have hopen : IsOpen M := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hzeq : f z.1 = f x := le_antisymm (hmax z.2) hz
    have hzB : z.1 ∉ U.boundary := fun hzb =>
      (not_le_of_gt hpos) (hz.trans (hB z.1 hzb))
    have hzInt : z.1 ∈ interior U.carrier := by
      rw [U.interior_carrier]
      exact ⟨z.2,hzB⟩
    have hU : ∀ᶠ q in 𝓝 z.1, q ∈ interior U.carrier :=
      isOpen_interior.mem_nhds hzInt
    have hlocal : IsLocalMax f z.1 := hU.mono fun q hq =>
      (hmax (interior_subset hq)).trans_eq hzeq.symm
    have hzpos : 0 < f z.1 := by rw [hzeq]; exact hpos
    have he := hplateau z.1 hzInt hzpos hlocal
    have hs : Tendsto (fun q : U.carrier => q.1) (𝓝 z) (𝓝 z.1) :=
      continuous_subtype_val.tendsto z
    exact (hs.eventually he).mono fun q hq => (hq.trans hzeq).ge
  have hMuniv : M = Set.univ :=
    (show IsClopen M from ⟨hclosed,hopen⟩).eq_univ
      ⟨⟨x,hx⟩,show f x ≤ g ⟨x,hx⟩ from le_rfl⟩
  have houter : f x ≤ f U.outerGauss := by
    have hm : (⟨U.outerGauss,U.outerGauss_mem⟩ : U.carrier) ∈ M := by
      rw [hMuniv]
      exact Set.mem_univ _
    exact hm
  exact (not_le_of_gt hpos) (houter.trans (hB U.outerGauss (Set.mem_insert _ _)))

end FCStandardAffinoid

variable {u : RelativeSpectrum w K[X] → EReal} {Ω : Set (RelativeSpectrum w K[X])}

/-- The literal source comparison follows from actual local subharmonicity at every point. -/
theorem isLineSubharmonicOn_of_locally (hnt : ∃ t : K, 1 < w t)
    (hloc : ∀ x ∈ Ω, ∃ V : Set (RelativeSpectrum w K[X]),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ IsLineSubharmonicOn u V) :
    IsLineSubharmonicOn u Ω := by
  have husc : UpperSemicontinuousOn u Ω := by
    intro x hx
    obtain ⟨V,hVo,hxV,_,huV⟩ := hloc x hx
    have hc : UpperSemicontinuousAt u x := by
      intro b hb
      have he := huV.upperSemicontinuousOn x hxV b hb
      simpa only [nhdsWithin_eq_nhds.mpr (hVo.mem_nhds hxV)] using he
    exact hc.upperSemicontinuousWithinAt Ω
  refine ⟨husc,?_,?_⟩
  · intro x hx
    obtain ⟨V,_,hxV,_,huV⟩ := hloc x hx
    exact huV.ne_top x hxV
  · intro m U h hU hh hB x
    obtain ⟨c,γ,hγ⟩ := hh
    let F : RelativeSpectrum w K[X] → EReal :=
      fun y => u y + ((-U.harmonicExpression c γ y : ℝ) : EReal)
    have hE : ContinuousOn (U.harmonicExpression c γ) U.carrier :=
      continuousOn_iff_continuous_domRestrict.mpr (U.continuous_harmonicExpression c γ)
    have hF : UpperSemicontinuousOn F U.carrier :=
      (husc.mono hU).add'
        (continuous_coe_real_ereal.comp_continuousOn hE.neg).upperSemicontinuousOn
        (fun y _ => EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
          (Or.inr (EReal.coe_ne_top _)))
    have hFB : ∀ z ∈ U.boundary, F z ≤ 0 := by
      intro z hz
      have hb := hB ⟨z,U.boundary_subset hz⟩ hz
      rw [hγ] at hb
      calc
        F z ≤ (U.harmonicExpression c γ z : EReal)+
            ((-U.harmonicExpression c γ z : ℝ) : EReal) := add_le_add hb le_rfl
        _ = 0 := by rw [← EReal.coe_add,add_neg_cancel,EReal.coe_zero]
    have hbound : ∀ y ∈ U.carrier, F y ≤ 0 :=
      U.le_zero_of_boundary_of_local_max_plateau_usc F hF hFB (by
        intro y hy _ hmax
        obtain ⟨V,hVo,hyV,_,huV⟩ := hloc y (hU (interior_subset hy))
        let D := V ∩ interior U.carrier
        have hDo : IsOpen D := hVo.inter isOpen_interior
        have hDsub : D ⊆ U.carrier := fun _ hz => interior_subset hz.2
        have huD : IsLineSubharmonicOn u D := huV.mono Set.inter_subset_left
        have hhD : IsLineHarmonicOn (fun z => -U.harmonicExpression c γ z) D :=
          ((U.isLineHarmonicOn_harmonicExpression c γ).mono hDsub).neg
        have hFD : IsLineSubharmonicOn F D := huD.add_harmonic hhD hDo
        exact hFD.eventually_eq_of_isLocalMax hnt hDo y ⟨hyV,hy⟩ hmax)
    have he := (EReal.le_sub_iff_add_le
      (Or.inl (EReal.coe_ne_bot (-U.harmonicExpression c γ x.1)))
      (Or.inl (EReal.coe_ne_top (-U.harmonicExpression c γ x.1)))).mpr (hbound x.1 x.2)
    rw [hγ]
    simpa only [zero_sub,EReal.coe_neg,neg_neg] using he

theorem isLineSubharmonicOn_iff_locally (hnt : ∃ t : K, 1 < w t) (hΩ : IsOpen Ω) :
    IsLineSubharmonicOn u Ω ↔ ∀ x ∈ Ω, ∃ V : Set (RelativeSpectrum w K[X]),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ IsLineSubharmonicOn u V := by
  constructor
  · intro hu x hx
    exact ⟨Ω,hΩ,hx,Set.Subset.rfl,hu⟩
  · exact isLineSubharmonicOn_of_locally hnt

end EnvelopeProperty.Berkovich.RelativeSpectrum
