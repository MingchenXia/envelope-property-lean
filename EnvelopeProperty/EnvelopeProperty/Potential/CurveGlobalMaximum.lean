import EnvelopeProperty.Berkovich.IntegralCurveLocalMaximumAllValuations

/-! # Whole original maximum constancy, with actual analytic preconnectedness explicit -/

open scoped NNReal Topology Classical
open Topology Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum

universe u
variable {K B : Type u} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
variable [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B] [Ring.KrullDimLE 1 B]

/-- The actual topological preconnectedness input is explicit; native local psh
and an attained original global maximum DERIVE whole original constancy. -/
theorem IsLocallyPSHOn.eq_of_isMaxOn_univ_of_preconnected
    [PreconnectedSpace (RelativeSpectrum w B)]
    {u : RelativeSpectrum w B → EReal} (hu : IsLocallyPSHOn Set.univ u)
    (y : RelativeSpectrum w B)
    (hmax : IsMaxOn u Set.univ y) : ∀ z, u z = u y := by
  let M : Set (RelativeSpectrum w B) := {z | u y ≤ u z}
  have husc : UpperSemicontinuous u :=
    upperSemicontinuousOn_univ_iff.mp hu.upperSemicontinuousOn
  have hMc : IsClosed M := husc.isClosed_preimage (u y)
  have hMo : IsOpen M := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hzeq : u z = u y := le_antisymm (hmax (Set.mem_univ z)) hz
    have hzmax : IsLocalMax u z := Filter.Eventually.of_forall (fun q =>
      (hmax (Set.mem_univ q)).trans_eq hzeq.symm)
    have hflat := hu.eventually_eq_of_isLocalMax_integral_affineCurve_allValuations z (Set.mem_univ z) hzmax
    exact hflat.mono (fun q hq => (hq.trans hzeq).ge)
  have hMu : M = Set.univ :=
    (show IsClopen M from ⟨hMc,hMo⟩).eq_univ ⟨y,show u y ≤ u y from le_rfl⟩
  intro z
  have hz : z ∈ M := by rw [hMu]; exact Set.mem_univ z
  exact le_antisymm (hmax (Set.mem_univ z)) hz

end EnvelopeProperty.Berkovich.RelativeSpectrum
