import EnvelopeProperty.Vanishing.NadelGlobalNormalizationChart
import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingFrames

/-! # Genuine actual whole native normalized charts cover the whole normalization

Only invertibility of the SAME original finite list's lines is used to produce
common frames. Every actual normalized point is covered by its entire original
base-open preimage, retaining all disconnected factors.
-/

open AlgebraicGeometry CategoryTheory Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalNormalization
open NadelAuxiliaryMulticover NadelAdaptedChartMatching
variable {X : Scheme.{u}} [IsIntegral X] (D : List (AuxiliarySection X))
  (hL : ∀ i : Fin D.length, IsInvertible (D.get i).line)

include hL in
/-- Actual original local invertibility INTERNALLY supplies a genuine
whole native normalized chart at EVERY original normalized point. No chart,
normalization comparison or component-selection certificate is an input. -/
theorem exists_chart_at_point (z : normalizedScheme D) :
    ∃ U : X.affineOpens, ∃ hU : Nonempty U.1,
      ∃ e : NadelAuxiliaryMulticoverCharts.Frames U.1 D,
        let := hU
        letI := Chart.isOpenImmersion U D e
        z ∈ (Chart.map U D e).opensRange := by
  obtain ⟨U, hyU, _, ⟨e⟩⟩ := exists_common_frames_in (fun i => (D.get i).line) hL
    (normalizedToOriginal D z) ⊤ (by trivial)
  let hU : Nonempty U.1 := ⟨⟨normalizedToOriginal D z, hyU⟩⟩
  refine ⟨U, hU, e, ?_⟩
  let := hU
  dsimp only
  rw [Chart.opensRange_map]
  exact hyU

end EnvelopeProperty.Vanishing.NadelGlobalNormalization
