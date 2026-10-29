import EnvelopeProperty.Potential.LineSeparatedCore
import EnvelopeProperty.Potential.LineDirichletExtension

/-! # Strict boundary comparison on the connected core of a constructed presentation -/

open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

/-- A genuinely lower actual boundary value lowers every point of the connected strict core. -/
theorem IsHarmonic.lt_of_boundary_le_of_exists_lt {H : U.carrier → ℝ} (hH : U.IsHarmonic H)
    (hsep : U.IsSeparated) (R : ℝ)
    (hB : ∀ z : U.carrier, z.1 ∈ U.boundary → H z ≤ R)
    (hlow : ∃ z : U.carrier, z.1 ∈ U.boundary ∧ H z < R)
    (x : U.carrier) (hx : x.1 ∈ U.strictCore) : H x < R := by
  have hupp : H ≤ fun _ => R :=
    hH.le_of_boundary_le U (IsHarmonic.const U R) hB
  apply lt_of_le_of_ne (hupp x)
  intro hxeq
  obtain ⟨c,γ,hγ⟩ := hH
  have hmax : ∀ y ∈ U.carrier, U.harmonicExpression c γ y ≤ U.harmonicExpression c γ x.1 := by
    intro y hy
    rw [← hγ ⟨y,hy⟩,← hγ x,hxeq]
    exact hupp ⟨y,hy⟩
  have hcomp := U.harmonicExpression_eq_on_interior_component c γ x.1
    (U.strictCore_subset_interior hx) hmax
  rw [← U.interior_carrier] at hcomp
  have hsub : U.strictCore ⊆ connectedComponentIn (interior U.carrier) x.1 :=
    (U.isPathConnected_strictCore ⟨x.1,hx⟩).isConnected.isPreconnected.subset_connectedComponentIn
      hx U.strictCore_subset_interior
  have hE : ContinuousOn (U.harmonicExpression c γ) U.carrier :=
    continuousOn_iff_continuous_domRestrict.mpr (U.continuous_harmonicExpression c γ)
  let M : Set (RelativeSpectrum w K[X]) :=
    U.carrier ∩ (U.harmonicExpression c γ) ⁻¹' {U.harmonicExpression c γ x.1}
  have hM : IsClosed M := hE.preimage_isClosed_of_isClosed U.isClosed_carrier isClosed_singleton
  have hcore : U.strictCore ⊆ M := fun y hy =>
    ⟨interior_subset (U.strictCore_subset_interior hy),hcomp y (hsub hy)⟩
  obtain ⟨z,hz,hzlt⟩ := hlow
  have hzM := (closure_minimal hcore hM) (U.boundary_subset_closure_strictCore hsep ⟨x.1,hx⟩ hz)
  have hzEq : H z = H x := (hγ z).trans (hzM.2.trans (hγ x).symm)
  exact hzlt.ne (hzEq.trans hxeq)

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
