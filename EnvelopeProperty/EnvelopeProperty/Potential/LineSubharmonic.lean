import EnvelopeProperty.Potential.LineHarmonicAlgebra
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Actual subharmonic comparison on the analytic line

The source definition tests every actual standard affinoid and every actual
logarithmic harmonic function. Upper semicontinuity and exclusion of positive
infinity are included as the source range and regularity requirements.
-/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}

/-- The literal source comparison definition on actual standard affinoids. -/
structure IsLineSubharmonicOn (u : RelativeSpectrum w K[X] → EReal)
    (Ω : Set (RelativeSpectrum w K[X])) : Prop where
  upperSemicontinuousOn : UpperSemicontinuousOn u Ω
  ne_top : ∀ x ∈ Ω, u x ≠ ⊤
  comparison : ∀ {m : ℕ} (U : FCStandardAffinoid w m) (h : U.carrier → ℝ),
    U.carrier ⊆ Ω → U.IsHarmonic h →
      (∀ z : U.carrier, z.1 ∈ U.boundary → u z.1 ≤ (h z : EReal)) →
      ∀ x : U.carrier, u x.1 ≤ (h x : EReal)

namespace IsLineSubharmonicOn

variable {u v : RelativeSpectrum w K[X] → EReal} {Ω Ω' : Set (RelativeSpectrum w K[X])}

theorem mono (hu : IsLineSubharmonicOn u Ω) (hΩ : Ω' ⊆ Ω) : IsLineSubharmonicOn u Ω' where
  upperSemicontinuousOn := hu.upperSemicontinuousOn.mono hΩ
  ne_top := fun x hx => hu.ne_top x (hΩ hx)
  comparison := fun U h hU hh hB => hu.comparison U h (hU.trans hΩ) hh hB

theorem bot (Ω : Set (RelativeSpectrum w K[X])) :
    IsLineSubharmonicOn (fun _ => (⊥ : EReal)) Ω where
  upperSemicontinuousOn := upperSemicontinuousOn_const
  ne_top := by simp
  comparison := fun _ _ _ _ _ _ => bot_le

theorem sup (hu : IsLineSubharmonicOn u Ω) (hv : IsLineSubharmonicOn v Ω) :
    IsLineSubharmonicOn (fun x => u x ⊔ v x) Ω where
  upperSemicontinuousOn := hu.upperSemicontinuousOn.sup hv.upperSemicontinuousOn
  ne_top := by
    intro x hx
    exact (max_lt (lt_top_iff_ne_top.mpr (hu.ne_top x hx))
      (lt_top_iff_ne_top.mpr (hv.ne_top x hx))).ne
  comparison := by
    intro m U h hU hh hB x
    apply sup_le
    · exact hu.comparison U h hU hh
        (fun z hz => (le_sup_left : u z.1 ≤ u z.1 ⊔ v z.1).trans (hB z hz)) x
    · exact hv.comparison U h hU hh
        (fun z hz => (le_sup_right : v z.1 ≤ u z.1 ⊔ v z.1).trans (hB z hz)) x

variable [IsAlgClosed K]

theorem const (b : ℝ) (Ω : Set (RelativeSpectrum w K[X])) :
    IsLineSubharmonicOn (fun _ => (b : EReal)) Ω where
  upperSemicontinuousOn := upperSemicontinuousOn_const
  ne_top := by simp
  comparison := by
    intro m U h _ hh hB x
    obtain ⟨c,γ,hγ⟩ := hh
    have hdiff : ∀ y : RelativeSpectrum w K[X],
        U.harmonicExpression (b-c) (fun j => -γ j) y = b-U.harmonicExpression c γ y := by
      intro y
      simp only [FCStandardAffinoid.harmonicExpression,neg_mul,Finset.sum_neg_distrib]
      ring
    obtain ⟨z,hz,he⟩ := U.harmonicExpression_exists_boundary_ge (b-c) (fun j => -γ j) x.2
    have hb : b ≤ U.harmonicExpression c γ z := by
      have hhB := hB ⟨z,U.boundary_subset hz⟩ hz
      rw [hγ] at hhB
      exact_mod_cast hhB
    rw [hdiff,hdiff] at he
    rw [hγ]
    exact_mod_cast (show b ≤ U.harmonicExpression c γ x.1 by linarith)

end IsLineSubharmonicOn
end EnvelopeProperty.Berkovich.RelativeSpectrum
