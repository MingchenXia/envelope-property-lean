/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SmoothEPCharZeroImport
import EnvelopeProperty.Projective.SubvarietyMultiplierConeGenerators
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroChartRaw
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroChartTrivial

/-!
# The smooth envelope property in characteristic zero from relative Nadel vanishing

Over an algebraically closed field `k` of characteristic `0`, relative ample Nadel vanishing for
powers of ideals (`Char0.RelativeAmpleNadelVanishingInput k`) implies the envelope property of
every projectively normal `X = V(I) ⊆ ℙᴹ` with smooth charts, in every real class, and hence
`SmoothEnvelopeCharZero k` (`smoothEnvelopeCharZero_of_relativeNadel`). The proof uses the uniform
generation of the multiplier cone ideals, their inclusions and subadditivity, and the chart
estimates. Relative Nadel vanishing is proved in `Vanishing/RelativeNadelVanishing.lean`
(`Char0.relativeAmpleNadelVanishingInput`); the two are combined in
`Projective/SubvarietyEnvelopeCharZeroUnconditional.lean`.
-/

open scoped NNReal ENNReal Topology Polynomial

noncomputable section

namespace EnvelopeProperty

universe u

namespace ProjSubvariety

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {M : ℕ}

/-- Under relative ample Nadel vanishing, for `X` with smooth charts the envelope of every
nonpositive PL obstacle in a positive integral class `d` is `d`-psh. -/
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

/-- Under relative ample Nadel vanishing, `X` with smooth charts has the envelope property in
every real class, by the criterion for integral classes and PL obstacles
(`hasEnvelopeProperty_of_forall_nat`). -/
theorem hasEnvelopeProperty_of_relativeNadel
    (hNadel : Char0.RelativeAmpleNadelVanishingInput k)
    (X : ProjSubvariety k M) (hs : X.HasSmoothCharts) (θ : ℝ) :
    X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_forall_nat (separatesPoints_isPL X)
    (fun _d hd _φ hφ hφ0 => isPSH_envelope_nat_of_relativeNadel hNadel X hs hd hφ hφ0) θ

end ProjSubvariety

/-- Relative ample Nadel vanishing over `k` implies `SmoothEnvelopeCharZero k`. -/
theorem smoothEnvelopeCharZero_of_relativeNadel
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (hNadel : Char0.RelativeAmpleNadelVanishingInput k) : SmoothEnvelopeCharZero k := by
  constructor
  intro M X _hX hs θ _hθ
  exact ProjSubvariety.hasEnvelopeProperty_of_relativeNadel hNadel X hs θ

end EnvelopeProperty
