import EnvelopeProperty.Potential.LineSubharmonic
import EnvelopeProperty.Potential.LineAffinoidBasis

/-! # Actual harmonic functions on open domains and subharmonic addition -/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}

/-- The source local harmonic notion tests every actual standard affinoid. -/
structure IsLineHarmonicOn (h : RelativeSpectrum w K[X] → ℝ)
    (Ω : Set (RelativeSpectrum w K[X])) : Prop where
  isHarmonic : ∀ {m : ℕ} (U : FCStandardAffinoid w m), U.carrier ⊆ Ω →
    U.IsHarmonic (fun x => h x.1)

namespace IsLineHarmonicOn

variable {h : RelativeSpectrum w K[X] → ℝ} {Ω Ω' : Set (RelativeSpectrum w K[X])}

theorem mono (hh : IsLineHarmonicOn h Ω) (hΩ : Ω' ⊆ Ω) : IsLineHarmonicOn h Ω' where
  isHarmonic := fun U hU => hh.isHarmonic U (hU.trans hΩ)

theorem const (b : ℝ) (Ω : Set (RelativeSpectrum w K[X])) : IsLineHarmonicOn (fun _ => b) Ω where
  isHarmonic := fun U _ => FCStandardAffinoid.IsHarmonic.const U b

variable [IsAlgClosed K]

theorem continuousOn (hh : IsLineHarmonicOn h Ω) (hΩ : IsOpen Ω) : ContinuousOn h Ω := by
  intro x hx
  obtain ⟨m,U,hxU,hUΩ⟩ := fc_exists_standardAffinoid_nhds x (hΩ.mem_nhds hx)
  have hc : ContinuousOn h U.carrier := continuousOn_iff_continuous_domRestrict.mpr
    ((hh.isHarmonic U hUΩ).continuous U)
  have hn : U.carrier ∈ 𝓝 x :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hxU) interior_subset
  exact (hc.continuousAt hn).continuousWithinAt

end IsLineHarmonicOn

private theorem fc_ereal_add_coe_le_coe_iff (u : EReal) (a b : ℝ) :
    u+(a : EReal) ≤ (b : EReal) ↔ u ≤ ((b-a : ℝ) : EReal) := by
  rw [EReal.coe_sub]
  exact (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot a))
    (Or.inl (EReal.coe_ne_top a))).symm

namespace IsLineSubharmonicOn

variable {u : RelativeSpectrum w K[X] → EReal} {h : RelativeSpectrum w K[X] → ℝ}
variable {Ω : Set (RelativeSpectrum w K[X])}

theorem add_harmonic_of_continuousOn (hu : IsLineSubharmonicOn u Ω)
    (hh : IsLineHarmonicOn h Ω) (hc : ContinuousOn h Ω) :
    IsLineSubharmonicOn (fun x => u x+(h x : EReal)) Ω where
  upperSemicontinuousOn := hu.upperSemicontinuousOn.add'
    (continuous_coe_real_ereal.comp_continuousOn hc).upperSemicontinuousOn
    (fun x _ => EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot (h x)))
      (Or.inr (EReal.coe_ne_top (h x))))
  ne_top := fun x hx => EReal.add_ne_top (hu.ne_top x hx) (EReal.coe_ne_top (h x))
  comparison := by
    intro m U k hU hk hB x
    have hdiff : U.IsHarmonic (fun z => k z-h z.1) := by
      simpa only [Pi.sub_def] using hk.sub U (hh.isHarmonic U hU)
    apply (fc_ereal_add_coe_le_coe_iff _ _ _).mpr
    exact hu.comparison U _ hU hdiff
      (fun z hz => (fc_ereal_add_coe_le_coe_iff _ _ _).mp (hB z hz)) x

theorem add_const (hu : IsLineSubharmonicOn u Ω) (b : ℝ) :
    IsLineSubharmonicOn (fun x => u x+(b : EReal)) Ω :=
  hu.add_harmonic_of_continuousOn (IsLineHarmonicOn.const b Ω) continuousOn_const

variable [IsAlgClosed K]

theorem add_harmonic (hu : IsLineSubharmonicOn u Ω) (hh : IsLineHarmonicOn h Ω)
    (hΩ : IsOpen Ω) : IsLineSubharmonicOn (fun x => u x+(h x : EReal)) Ω :=
  hu.add_harmonic_of_continuousOn hh (hh.continuousOn hΩ)

end IsLineSubharmonicOn
end EnvelopeProperty.Berkovich.RelativeSpectrum
