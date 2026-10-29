import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.HiepInduction

set_option autoImplicit false

/-!
# The Ohsawa–Takegoshi extension interface

`OhsawaTakegoshiHyperplane` states the extension theorem used by the proof
of strong openness for increasing sequences. Results in this module take
the extension statement as an explicit hypothesis. Its regular case is
established from Hörmander's `L²` estimate in
`AnalyticGeometry.OhsawaTakegoshiRegularProof`; the resulting strong-openness
statements are in `AnalyticGeometry.StrongOpennessRegularRoute`.

## The L² input

`OhsawaTakegoshiHyperplane` is the Ohsawa--Takegoshi extension theorem
(T. Ohsawa and K. Takegoshi, *On the extension of L² holomorphic functions*,
Math. Z. 195 (1987) 197--204) for the hyperplane `{z_m = 0}` of a convex
domain of `ℂ^{m+1}` that is bounded in the last coordinate. Convexity is used
only through pseudoconvexity, and is taken as the hypothesis here because
the interface uses convex domains. This is it is the one of Hiep (C. R. Acad. Sci. 2014), where the
L² extension is only ever applied on polydiscs and balls, and never Guan--Zhou's
own iteration over the sublevel sets of a plurisubharmonic exhaustion, which
are pseudoconvex but essentially never convex. Following that variant instead
would first require a pseudoconvexity predicate here.

The exponent `c > 0` is carried explicitly rather than normalized to `1`: the
general case is the special case applied to `c • φ`, which is again
plurisubharmonic, so stating it directly is no stronger and is compatible with plurisubharmonic scaling. The conclusion
asserts no `AEMeasurable`, so a `WeightedL2On` consumer must supply that
separately.

The constant depends only on the bound `R` for the last coordinate (`1620·R²`
classically, `π·R²` sharply), and is quantified existentially so that no
numeric normalization is asserted. It is quantified *before* the domain, the
weight and the function, so it is uniform over all of them; that is the
classical statement and not a weakening. The measurable-space instances are
the `borel _` ones, matching `IncreasingStrongOpenness`: mathlib's default
instance on `EuclideanSpace ℂ (Fin n)` is only propositionally equal to
`borel _`, so stating the interface without them would put its `volume` in a
different type from the consumer's.

Demailly, *Complex Analytic and Differential Geometry*, VIII-7.1 and VIII-7.5 (`demailly-cadg`), which is
the weaker 1982 extension theorem: it does not give the Ohsawa--Takegoshi
constant and cannot replace this interface.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace ComplexGeometry.AnalyticGeometry

noncomputable section

open Pluripotential

/-- The hyperplane `{z_m = 0} ≅ ℂ^m` of `ℂ^{m+1}`, as the linear isometric
embedding that appends a vanishing last coordinate. -/
def hyperplaneEmbedding (m : ℕ) (w : ComplexModel m) : ComplexModel (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => w i) 0)

@[simp] theorem hyperplaneEmbedding_last (m : ℕ) (w : ComplexModel m) :
    hyperplaneEmbedding m w (Fin.last m) = 0 := by
  simp [hyperplaneEmbedding]

@[simp] theorem hyperplaneEmbedding_castSucc (m : ℕ) (w : ComplexModel m)
    (i : Fin m) : hyperplaneEmbedding m w i.castSucc = w i := by
  simp [hyperplaneEmbedding]

/-- The Ohsawa--Takegoshi L² extension theorem from the hyperplane
`{z_m = 0}` of a convex domain `Ω ⊆ ℂ^{m+1}` whose last coordinate is bounded
by `R`: every holomorphic function on the slice which is `L²` for the weight
`e^{-φ}` extends to a holomorphic function on `Ω` which is `L²` for the same
weight, with a constant depending only on `R`. The exponent `c > 0` is carried
because `c • φ` is again plurisubharmonic, so the general case is the special
case applied to a rescaled weight; stating it directly spares the consumer a
plurisubharmonic-scaling lemma, and the constant is still independent of `c`.

This is an interface, an explicit hypothesis. -/
def OhsawaTakegoshiHyperplane : Prop := by
  exact ∀ m : ℕ, by
    letI : MeasurableSpace (ComplexModel m) := borel _
    letI : BorelSpace (ComplexModel m) := ⟨rfl⟩
    letI : MeasurableSpace (ComplexModel (m + 1)) := borel _
    letI : BorelSpace (ComplexModel (m + 1)) := ⟨rfl⟩
    exact ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ Ω : Set (ComplexModel (m + 1)), IsOpen Ω → Convex ℝ Ω →
        (∀ z ∈ Ω, ‖z (Fin.last m)‖ < R) →
        ∀ φ : ComplexModel (m + 1) → EReal, PlurisubharmonicOn φ Ω →
          ∀ c : ℝ, 0 < c →
          ∀ f : ComplexModel m → ℂ,
            DifferentiableOn ℂ f (hyperplaneEmbedding m ⁻¹' Ω) →
            ∃ F : ComplexModel (m + 1) → ℂ, DifferentiableOn ℂ F Ω ∧
              (∀ w ∈ hyperplaneEmbedding m ⁻¹' Ω,
                F (hyperplaneEmbedding m w) = f w) ∧
              (∫⁻ z in Ω, multiplierDensity φ c F z) ≤
                ENNReal.ofReal C *
                  ∫⁻ w in hyperplaneEmbedding m ⁻¹' Ω,
                    multiplierDensity (fun w => φ (hyperplaneEmbedding m w)) c f w

end

end ComplexGeometry.AnalyticGeometry
