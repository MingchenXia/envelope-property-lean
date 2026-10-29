import EnvelopeProperty.Potential.LineSubharmonic
import EnvelopeProperty.Potential.LineDirichletExtension

/-! # Addition in actual harmonic comparison, including negative infinity -/

open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
variable {u v : RelativeSpectrum w K[X] → EReal} {Ω : Set (RelativeSpectrum w K[X])}

theorem IsLineSubharmonicOn.add (hu : IsLineSubharmonicOn u Ω) (hv : IsLineSubharmonicOn v Ω) :
    IsLineSubharmonicOn (fun x => u x+v x) Ω where
  upperSemicontinuousOn := hu.upperSemicontinuousOn.add' hv.upperSemicontinuousOn
    (fun x hx => EReal.continuousAt_add (Or.inl (hu.ne_top x hx)) (Or.inr (hv.ne_top x hx)))
  ne_top := fun x hx => EReal.add_ne_top (hu.ne_top x hx) (hv.ne_top x hx)
  comparison := by
    intro m U h hU hh hB x
    obtain ⟨H,hH,hbounds⟩ := U.exists_isHarmonic_boundary_split
      (fun z => u z.1) (fun z => v z.1)
      (fun z => h ⟨z.1,U.boundary_subset z.2⟩)
      (fun z => hu.ne_top z.1 (hU (U.boundary_subset z.2)))
      (fun z => hv.ne_top z.1 (hU (U.boundary_subset z.2)))
      (fun z => hB ⟨z.1,U.boundary_subset z.2⟩ z.2)
    have hfirst : ∀ y : U.carrier, u y.1 ≤ (H y : EReal) :=
      hu.comparison U H hU hH (by
        intro z hz
        exact (hbounds ⟨z.1,hz⟩).1)
    have hdiff : U.IsHarmonic (fun y => h y-H y) := by
      simpa only [Pi.sub_def] using hh.sub U hH
    have hsecond : ∀ y : U.carrier, v y.1 ≤ ((h y-H y : ℝ) : EReal) :=
      hv.comparison U _ hU hdiff (by
        intro z hz
        exact (hbounds ⟨z.1,hz⟩).2)
    calc
      u x.1+v x.1 ≤ (H x : EReal)+((h x-H x : ℝ) : EReal) :=
        add_le_add (hfirst x) (hsecond x)
      _ = (h x : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        ring

end EnvelopeProperty.Berkovich.RelativeSpectrum
