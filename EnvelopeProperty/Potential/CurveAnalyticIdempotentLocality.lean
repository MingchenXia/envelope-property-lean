import EnvelopeProperty.Potential.CurveAnalyticIdempotent
import EnvelopeProperty.Potential.CurveAnalyticRestrictions

/-! # Genuine whole analytic idempotent lifts inside every prescribed neighbourhood -/

open scoped NNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
variable [CommRing B] [Algebra K[X] B] [Fintype ι]

/-- The ENTIRE original fibre idempotent lifts on an actual standard-affinoid carrier
inside ANY prescribed original neighbourhood. -/
theorem fc_exists_standardAffinoid_analytic_idempotent_nhds
    (x : RelativeSpectrum w K[X]) (basis : Module.Basis ι K[X] B)
    (e : FiniteFreeAnalyticCopy (basis.baseChange x.1.H)) (he : IsIdempotentElem e)
    (N : Set (RelativeSpectrum w K[X])) (hN : N ∈ 𝓝 x) :
    ∃ m : ℕ, ∃ U : FCStandardAffinoid w m, ∃ hx : x ∈ interior U.carrier,
      U.carrier ⊆ N ∧ ∃ a : U.CurveAnalyticAlgebra basis, IsIdempotentElem a ∧
        U.curveAnalyticNormedSpecialization basis ⟨x,interior_subset hx⟩ a = e := by
  obtain ⟨m,V,hxV,a,ha,hsp⟩ := fc_exists_standardAffinoid_analytic_idempotent x basis e he
  obtain ⟨n,U,hxU,hU⟩ := fc_exists_standardAffinoid_nhds x
    (Filter.inter_mem hN (isOpen_interior.mem_nhds hxV))
  let hUV : U.carrier ⊆ V.carrier := fun y hy => interior_subset (hU hy).2
  refine ⟨n,U,hxU,fun y hy => (hU hy).1,
    V.curveAnalyticNormedRestriction U hUV basis a,ha.map _,?_⟩
  rw [V.curveAnalyticNormedRestriction_specialization U hUV basis ⟨x,interior_subset hxU⟩ a]
  exact hsp

/-- Every ACTUAL fibre point has a genuinely constructed analytic idempotent in every
prescribed neighbourhood, with exact values at EVERY original fibre point. -/
theorem fc_exists_standardAffinoid_analytic_point_idempotent_nhds
    (x : RelativeSpectrum w K[X]) (basis : Module.Basis ι K[X] B) (y : Spectrum.Fibre (B := B) x.1)
    (N : Set (RelativeSpectrum w K[X])) (hN : N ∈ 𝓝 x) :
    ∃ m : ℕ, ∃ U : FCStandardAffinoid w m, ∃ hx : x ∈ interior U.carrier,
      U.carrier ⊆ N ∧ ∃ a : U.CurveAnalyticAlgebra basis, IsIdempotentElem a ∧
        ∀ z : Spectrum.Fibre (B := B) x.1,
          Spectrum.fibreHom z.2
            (U.curveAnalyticSpecialization ⟨x,interior_subset hx⟩ (U.curveAnalyticOriginalEquiv basis a)) =
              if z = y then 1 else 0 := by
  obtain ⟨e,he,heval⟩ := Spectrum.exists_completedFibre_point_idempotent x.1 basis y
  obtain ⟨m,U,hx,hUN,a,ha,hsp⟩ := fc_exists_standardAffinoid_analytic_idempotent_nhds x basis e he N hN
  refine ⟨m,U,hx,hUN,a,ha,?_⟩
  intro z
  have hraw := congrArg (FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.H)) hsp
  change (FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.H))
      ((FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.H)).symm
        (U.curveAnalyticSpecialization ⟨x,interior_subset hx⟩ (U.curveAnalyticOriginalEquiv basis a))) =
      (FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.H)) e at hraw
  rw [AlgEquiv.apply_symm_apply] at hraw
  rw [hraw]
  exact heval z

end EnvelopeProperty.Berkovich.RelativeSpectrum
