import EnvelopeProperty.Potential.LineStandardAffinoid
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.EReal.Lemmas

/-! # Compact connected comparison on an actual standard affinoid -/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}

/-- A general topological comparison lemma. Applications must derive the local plateau property. -/
theorem le_zero_of_boundary_of_local_max_plateau (U : FCStandardAffinoid w m)
    (f : RelativeSpectrum w K[X] → EReal) (hf : ContinuousOn f U.carrier)
    (hB : ∀ z ∈ U.boundary, f z ≤ 0)
    (hplateau : ∀ x ∈ interior U.carrier, 0 < f x → IsLocalMax f x →
      ∀ᶠ y in 𝓝 x, f y = f x) :
    ∀ x ∈ U.carrier, f x ≤ 0 := by
  let _ : CompactSpace U.carrier := isCompact_iff_compactSpace.mp U.isCompact_carrier
  let _ : ConnectedSpace U.carrier := isConnected_iff_connectedSpace.mp U.isConnected_carrier
  let g : U.carrier → EReal := fun x => f x.1
  have hg : Continuous g := continuousOn_iff_continuous_domRestrict.mp hf
  have hnonempty : (Set.univ : Set U.carrier).Nonempty :=
    ⟨⟨U.outerGauss,U.outerGauss_mem⟩,Set.mem_univ _⟩
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMaxOn hnonempty hg.continuousOn
  have hmax : ∀ y : U.carrier, g y ≤ g x := fun y => hx (Set.mem_univ y)
  intro y hy
  by_contra hn
  have hpos : 0 < g x := (lt_of_not_ge hn).trans_le (hmax ⟨y,hy⟩)
  let M : Set U.carrier := {z | g z = g x}
  have hclosed : IsClosed M := isClosed_eq hg continuous_const
  have hopen : IsOpen M := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    change g z = g x at hz
    have hzB : z.1 ∉ U.boundary := fun hzB => by
      have hb := hB z.1 hzB
      exact (not_le_of_gt hpos) (hz ▸ hb)
    have hzInt : z.1 ∈ interior U.carrier := by
      rw [U.interior_carrier]
      exact ⟨z.2,hzB⟩
    have hU : ∀ᶠ q in 𝓝 z.1, q ∈ interior U.carrier :=
      isOpen_interior.mem_nhds hzInt
    have hlocal : IsLocalMax f z.1 := hU.mono fun q hq =>
      (hmax ⟨q,interior_subset hq⟩).trans_eq hz.symm
    have hzpos : 0 < f z.1 := by
      change 0 < g z
      rw [hz]
      exact hpos
    have he := hplateau z.1 hzInt hzpos hlocal
    have hs : Tendsto (fun q : U.carrier => q.1) (𝓝 z) (𝓝 z.1) :=
      continuous_subtype_val.tendsto z
    exact (hs.eventually he).mono fun q hq => hq.trans hz
  have hMuniv : M = Set.univ := (show IsClopen M from ⟨hclosed,hopen⟩).eq_univ ⟨x,rfl⟩
  have houter : (⟨U.outerGauss,U.outerGauss_mem⟩ : U.carrier) ∈ M := by
    rw [hMuniv]
    exact Set.mem_univ _
  have hb := hB U.outerGauss (Set.mem_insert _ _)
  exact (not_le_of_gt hpos) (houter ▸ hb)

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
