import EnvelopeProperty.Potential.LineSubharmonicHarmonic
import EnvelopeProperty.Potential.LineDirichlet

/-! # Actual harmonicity is equivalent to harmonic comparison for both signs -/

open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}
variable {h : RelativeSpectrum w K[X] → ℝ} {Ω : Set (RelativeSpectrum w K[X])}

theorem IsLineHarmonicOn.neg (hh : IsLineHarmonicOn h Ω) :
    IsLineHarmonicOn (fun x => -h x) Ω where
  isHarmonic := fun U hU => by
    simpa only [Pi.neg_def] using (hh.isHarmonic U hU).neg U

variable [IsAlgClosed K]

theorem IsLineHarmonicOn.isLineSubharmonicOn (hh : IsLineHarmonicOn h Ω) (hΩ : IsOpen Ω) :
    IsLineSubharmonicOn (fun x => (h x : EReal)) Ω := by
  simpa only [EReal.coe_zero,zero_add] using
    (IsLineSubharmonicOn.const (w := w) 0 Ω).add_harmonic hh hΩ

theorem isLineHarmonicOn_of_both_subharmonic
    (hu : IsLineSubharmonicOn (fun x => (h x : EReal)) Ω)
    (hv : IsLineSubharmonicOn (fun x => ((-h x : ℝ) : EReal)) Ω) :
    IsLineHarmonicOn h Ω where
  isHarmonic := by
    intro m U hU
    obtain ⟨H,hH,hboundary⟩ := U.exists_isHarmonic_boundary_values (fun z => h z.1)
    have hfirst : ∀ x : U.carrier, (h x.1 : EReal) ≤ (H x : EReal) :=
      hu.comparison U H hU hH (by
        intro z hz
        exact_mod_cast (hboundary ⟨z.1,hz⟩).ge)
    have hneg : U.IsHarmonic (fun x => -H x) := by
      simpa only [Pi.neg_def] using hH.neg U
    have hsecond : ∀ x : U.carrier, ((-h x.1 : ℝ) : EReal) ≤ ((-H x : ℝ) : EReal) :=
      hv.comparison U _ hU hneg (by
        intro z hz
        exact_mod_cast (neg_le_neg (hboundary ⟨z.1,hz⟩).le))
    have heq : (fun x : U.carrier => h x.1) = H := by
      funext x
      have hf : h x.1 ≤ H x := by exact_mod_cast hfirst x
      have hs : -h x.1 ≤ -H x := by exact_mod_cast hsecond x
      exact le_antisymm hf (neg_le_neg_iff.mp hs)
    rw [heq]
    exact hH

theorem isLineHarmonicOn_iff_both_subharmonic (hΩ : IsOpen Ω) :
    IsLineHarmonicOn h Ω ↔
      IsLineSubharmonicOn (fun x => (h x : EReal)) Ω ∧
      IsLineSubharmonicOn (fun x => ((-h x : ℝ) : EReal)) Ω := by
  constructor
  · intro hh
    exact ⟨hh.isLineSubharmonicOn hΩ,hh.neg.isLineSubharmonicOn hΩ⟩
  · rintro ⟨hu,hv⟩
    exact isLineHarmonicOn_of_both_subharmonic hu hv

end EnvelopeProperty.Berkovich.RelativeSpectrum
