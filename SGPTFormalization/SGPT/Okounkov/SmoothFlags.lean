import TranscendentalNakamaye.Pending.SubmanifoldChartedSpace
import Mathlib.Topology.Connected.TotallyDisconnected

noncomputable section

namespace SGPT.Okounkov

open Set
open scoped Manifold ContDiff
open TranscendentalNakamaye.FirstPass
open TranscendentalNakamaye.FirstPass.BlowupSequences

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Literal original smooth flag: actual connected closed complex submanifolds,
the original ambient level and decreasing ambient carriers. -/
def IsSmoothFlag (Y : Fin (n + 1) → Set X) : Prop :=
  Y 0 = univ ∧ Antitone Y ∧
    ∀ i, IsClosedConnectedSubmanifold n (Y i) (n - (i : ℕ))

omit [IsComplexManifold n X] in
/-- Actual flag levels are closed and genuinely nonempty. -/
theorem IsSmoothFlag.level_closed_connected {Y : Fin (n + 1) → Set X}
    (hY : IsSmoothFlag Y) (i : Fin (n + 1)) :
    IsClosed (Y i) ∧ IsConnected (Y i) :=
  ⟨(hY.2.2 i).1, (hY.2.2 i).2.1⟩

/-- Main's genuine flattened atlas produces the actual original complex
submanifold and holomorphic inclusion at every flag level. -/
theorem IsSmoothFlag.level_complex_structure {Y : Fin (n + 1) → Set X}
    (hY : IsSmoothFlag Y) (i : Fin (n + 1)) :
    ∃ cs : ChartedSpace (ComplexModel (n - (i : ℕ))) (Y i),
      @IsComplexManifold (n - (i : ℕ)) (Y i) _ cs ∧
      TranscendentalNakamaye.Pending.SubmanifoldChartedSpace.InclusionHolomorphicFor
        n (n - (i : ℕ)) (Y i) cs :=
  TranscendentalNakamaye.Pending.SubmanifoldChartedSpace.exists_submanifoldStructure_of_isClosedConnectedSubmanifold
    (hY.2.2 i)

omit [IsComplexManifold n X] in
/-- Compact original ambient space gives compactness of every true flag level. -/
theorem IsSmoothFlag.level_isCompact [CompactSpace X] {Y : Fin (n + 1) → Set X}
    (hY : IsSmoothFlag Y) (i : Fin (n + 1)) : IsCompact (Y i) :=
  (hY.level_closed_connected i).1.isCompact

/-- Actual zero-dimensional flag charts and connectedness produce a genuine
single endpoint, with no endpoint-cardinality premise. -/
theorem IsSmoothFlag.last_eq_singleton {Y : Fin (n + 1) → Set X}
    (hY : IsSmoothFlag Y) : ∃ x : X, Y (Fin.last n) = {x} := by
  let W := Y (Fin.last n)
  have hW : IsClosedConnectedSubmanifold n W 0 := by
    simpa only [Fin.val_last, Nat.sub_self] using hY.2.2 (Fin.last n)
  let : ChartedSpace (ComplexModel 0) W :=
    TranscendentalNakamaye.Pending.SubmanifoldChartedSpace.chartedSpace
      (Nat.zero_le n) hW.2.2
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : DiscreteTopology W := ChartedSpace.discreteTopology (ComplexModel 0) W
  have hsub : Subsingleton W := subsingleton_of_preconnected_totallyDisconnected
  obtain ⟨x, hx⟩ := hW.2.1.nonempty
  refine ⟨x, ?_⟩
  ext z
  constructor
  · intro hz
    have heq : (⟨z, hz⟩ : W) = ⟨x, hx⟩ := hsub.elim _ _
    exact mem_singleton_iff.mpr (congrArg Subtype.val heq)
  · intro hz
    exact mem_singleton_iff.mp hz ▸ hx

end SGPT.Okounkov
