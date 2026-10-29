import EnvelopeProperty.Potential.LineSubharmonic
import Mathlib.Data.Fintype.Order

/-! # Directed decreasing infima for actual subharmonic comparison -/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

private theorem fc_ereal_le_coe_of_pos_add {a : EReal} {b : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → a ≤ ((b+ε : ℝ) : EReal)) : a ≤ (b : EReal) := by
  by_contra hnot
  obtain ⟨c,hbc,hca⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hnot)
  have he : 0 < c-b := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hbc)
  have hc := h (c-b) he
  rw [show b+(c-b) = c by ring] at hc
  exact not_le_of_gt hca hc

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}
variable {Ω : Set (RelativeSpectrum w K[X])}

/-- Downward directedness is needed only on the actual source domain. -/
theorem IsLineSubharmonicOn.iInf_directed {ι : Type*} [Nonempty ι]
    (u : ι → RelativeSpectrum w K[X] → EReal)
    (hu : ∀ i, IsLineSubharmonicOn (u i) Ω)
    (hdir : Directed (· ≥ ·) (fun i (x : Ω) => u i x.1)) :
    IsLineSubharmonicOn (fun x => ⨅ i, u i x) Ω where
  upperSemicontinuousOn := upperSemicontinuousOn_iInf (fun i => (hu i).upperSemicontinuousOn)
  ne_top := by
    intro x hx
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ne_of_lt ((iInf_le (fun j => u j x) i).trans_lt
      (lt_top_iff_ne_top.mpr ((hu i).ne_top x hx)))
  comparison := by
    classical
    intro m U h hU hh hB x
    apply fc_ereal_le_coe_of_pos_add
    intro ε hε
    let _ : Fintype U.boundary := U.finite_boundary.fintype
    have hindex : ∀ z : U.boundary, ∃ i : ι,
        u i z.1 ≤ ((h ⟨z.1,U.boundary_subset z.2⟩+ε : ℝ) : EReal) := by
      intro z
      have hlt : (⨅ i, u i z.1) < ((h ⟨z.1,U.boundary_subset z.2⟩+ε : ℝ) : EReal) :=
        (hB ⟨z.1,U.boundary_subset z.2⟩ z.2).trans_lt (by
          exact_mod_cast lt_add_of_pos_right (h ⟨z.1,U.boundary_subset z.2⟩) hε)
      obtain ⟨i,hi⟩ := iInf_lt_iff.mp hlt
      exact ⟨i,hi.le⟩
    choose index hindex using hindex
    obtain ⟨k,hk⟩ := hdir.finite_le index
    have hhε : U.IsHarmonic (fun z => h z+ε) := by
      simpa only [Pi.add_def] using hh.add U (FCStandardAffinoid.IsHarmonic.const U ε)
    have hcomp : ∀ y : U.carrier, u k y.1 ≤ ((h y+ε : ℝ) : EReal) :=
      (hu k).comparison U _ hU hhε (by
        intro z hz
        let b : U.boundary := ⟨z.1,hz⟩
        have hkb : u k z.1 ≤ u (index b) z.1 := hk b ⟨z.1,hU z.2⟩
        have hb := hindex b
        change u (index b) z.1 ≤ ((h z+ε : ℝ) : EReal) at hb
        exact hkb.trans hb)
    exact (iInf_le (fun i => u i x.1) k).trans (hcomp x)

end EnvelopeProperty.Berkovich.RelativeSpectrum
