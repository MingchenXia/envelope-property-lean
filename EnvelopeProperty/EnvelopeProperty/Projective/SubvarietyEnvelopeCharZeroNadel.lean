/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SmoothEPCharZeroImport
import EnvelopeProperty.Projective.SubvarietyMultiplierConeGenerators
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroChartRaw
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroChartTrivial

/-!
# The original characteristic-zero smooth envelope property from genuine Nadel vanishing

The sole theorem input is the actual relative ample ideal-power Nadel
vanishing proposition, proved in `Vanishing/RelativeNadelVanishing.lean`
(`Char0.relativeAmpleNadelVanishingInput`); the two are combined in
`Projective/SubvarietyEnvelopeCharZeroUnconditional.lean`. Actual original multiplier cone generators,
inclusions, subadditivity, chart estimates and the original trivial point
are all produced by proved theorems on the same original objects.

The final theorem constructs the existing `SmoothEnvelopeCharZero k`.
It introduces no global instance and assumes no envelope, generation,
approximation, native model, or valuation-comparison certificate.
-/

open scoped NNReal ENNReal Topology Polynomial

noncomputable section

namespace EnvelopeProperty

universe u

namespace ProjSubvariety

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {M : ℕ}

/-- The original envelope of every nonpositive PL obstacle in a positive
integral class is PSH, from only genuine relative ample Nadel vanishing
and the original smooth-chart hypothesis. -/
theorem isPSH_envelope_nat_of_relativeNadel
    (hNadel : Char0.RelativeAmpleNadelVanishingInput k)
    (X : ProjSubvariety k M) (hs : X.HasSmoothCharts) {d : ℕ} (hd : 0 < d)
    {φ : X.an → ℝ} (hφ : X.IsPL φ) (hφ0 : ∀ v, φ v ≤ 0) :
    X.IsPSH (d : ℝ) (X.envelope (d : ℝ) fun v => (φ v : EReal)) := by
  have hcont : Continuous φ := FSSystem.IsPL.continuous hφ
  obtain ⟨C₀, hC₀⟩ := FSSystem.exists_abs_le_of_continuous hcont
  have hC : ∀ v, -C₀ ≤ φ v := fun v => neg_le_of_abs_le (hC₀ v)
  obtain ⟨c, hgen⟩ := MultiplierConeGenerators.exists_uniform_bounded_polynomial_generators
    X hNadel hs
  exact isPSH_envelope_of_polynomialConeIdealOnlyChartEstimates
    (B := MultiplierBaseIdeals.originalMultiplierConeIdeal X hs d φ hC) (d := d) (c := c)
    (fun m _hm => hgen d φ (-C₀) hC m)
    (fun _m hm => MultiplierBaseIdeals.coneObstacleIdeal_le_originalMultiplierConeIdeal
      X hs d φ hC hm)
    (fun m l _hm _hl => MultiplierBaseIdeals.originalMultiplierConeIdeal_mul_le_saturation
      X hs d φ hC m l)
    (fun j V b hb htorus =>
      MultiplierBaseIdeals.exists_originalMultiplierConeIdeal_chart_le_obstacle
        X hs d φ hC j V b hb htorus)
    hd hφ hφ0

/-- The existing original integral/PL envelope criterion gives the original
envelope property in every real class from genuine relative ample Nadel
vanishing and the original smooth charts. -/
theorem hasEnvelopeProperty_of_relativeNadel
    (hNadel : Char0.RelativeAmpleNadelVanishingInput k)
    (X : ProjSubvariety k M) (hs : X.HasSmoothCharts) (θ : ℝ) :
    X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_forall_nat (separatesPoints_isPL X)
    (fun _d hd _φ hφ hφ0 => isPSH_envelope_nat_of_relativeNadel hNadel X hs hd hφ hφ0) θ

end ProjSubvariety

/-- The ORIGINAL `SmoothEnvelopeCharZero k` is constructed from the sole
explicit genuine relative ample Nadel input. Its original projective
subvariety, projective-normality, smooth-chart and nonnegative-class
quantifiers are exactly those of the existing target proposition. -/
theorem smoothEnvelopeCharZero_of_relativeNadel
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (hNadel : Char0.RelativeAmpleNadelVanishingInput k) : SmoothEnvelopeCharZero k := by
  constructor
  intro M X _hX hs θ _hθ
  exact ProjSubvariety.hasEnvelopeProperty_of_relativeNadel hNadel X hs θ

end EnvelopeProperty
