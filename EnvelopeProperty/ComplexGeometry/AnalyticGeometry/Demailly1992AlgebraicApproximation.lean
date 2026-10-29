import EnvelopeProperty.ComplexGeometry.Pluripotential.NumericalRestrictedVolumeScaffold
import EnvelopeProperty.ComplexGeometry.Pluripotential.GlobalAnalyticSingularities
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.DemaillyApproximationSmoothOffPole

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Demailly's algebraic approximation theorem

Source: Demailly, *Regularization of closed positive currents and intersection
theory*, J. Algebraic Geom. **1** (1992), Theorem 1.1, as Boucksom quotes it
(`bou02-volume:2.6`, blueprint node demailly algebraic approximation):

> Let `T` be a closed almost positive `(1,1)`-current on a compact complex `X`
> with a Hermitian form `ω`. Write `T = α + ddᶜφ` with `α` smooth and `φ` almost
> psh, and suppose given a continuous real form `γ` with `T ≥ γ`. Then there is
> a sequence `φ_k` of almost psh functions such that
> (i) `φ_k` has algebraic singularities;
> (ii) `φ_k` decreases to `φ` everywhere;
> (iii) the Lelong numbers `ν(φ_k,x)` converge to `ν(φ,x)` uniformly in `x`;
> (iv) setting `T_k = α + ddᶜφ_k`, one has `T_k ≥ γ - ε_kω` with `ε_k ↓ 0`.

## Approximation and its projections

`demailly1992_exists_algebraicApproximation` gives a decreasing approximation
with algebraic singularities, both globally and in the bounded smooth-off-pole
sense. `exists_algebraicApproximation_smoothOffPole` is its chartwise projection.
The construction is the Bergman-kernel approximation in
`DemaillyApproximationSmoothOffPole`.

## What is specialized, and why every specialization WEAKENS the statement

* `γ = 0`: the current `α + ddᶜψ` is positive.
* Clause (i) is asked in two forms, both implied by "algebraic singularities":
  globally (`HasAnalyticSingularities`: a positive **rational** coefficient
  along a coherent ideal with a bounded remainder — Demailly's `φ_k` has
  coefficient `1/k` along the multiplier ideal `𝓘(kφ)`, coherent by Nadel), and
  chartwise in the bounded smooth-off-pole sense (`HasManifoldAnalyticSingularitiesSmoothOffPole`:
  bounded remainder, `C^∞` off the poles; Demailly's `φ_k` is smooth off its
  pole set, which is the zero set of the Bergman sections).
* Clause (ii) is `Antitone` together with `⨅ k, ψ_k x = ψ x`.
* Clause (iii) is OMITTED.
* Clause (iv) is `0 ≤ δ_k` with `δ_k → 0`, not "decreasing".

Degenerate cases: `ψ` is never identically `-∞`
(`IsThetaPshPotential` contains `LocallyNondegenerate`); on an empty `M` every
clause is vacuous; in dimension `0` every function is smooth and the constant
sequence works.

## Scope

The statement quantifies over an arbitrary closed real `(1,1)`-form, an arbitrary
`θ`-psh potential and an arbitrary Kähler background; it mentions no Kähler
current, class, Lelong number, pole set, subvariety or gluing datum. The applications (Boucksom 3.17; the CT22 4.3 collar construction; the
smoothing of bounded potentials) each add their own construction on top.
-/

open Set Filter
open scoped Topology

namespace ComplexGeometry.AnalyticGeometry.Demailly1992AlgebraicApproximation

open Pluripotential Pluripotential.PositiveClasses Pluripotential.NumericalRestrictedVolumeScaffold
  Pluripotential.GlobalAnalyticSingularities

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Demailly 1992 Theorem 1.1, in Boucksom's form `bou02-volume:2.6`, with `γ = 0` and
clause (i) in both conventions** (via
`DemaillyApproximationSmoothOffPole.exists_algebraicApproximation`, Demailly's explicit Bergman
kernel sequence on a fixed chart cover).
A positive current `α + ddᶜψ` on a compact Kähler manifold is approximated from
above by currents with algebraic singularities, at an asymptotically vanishing
loss of positivity.  -/
theorem demailly1992_exists_algebraicApproximation [CompactSpace M]
    (omega : KahlerBackground n M) (alpha : ClosedRealOneOneForm n M) (psi : M → EReal)
    (hpsi : IsThetaPshPotential alpha.val psi) :
    ∃ (psiSeq : ℕ → M → EReal) (delta : ℕ → ℝ),
      -- (i) analytic singularities, globally and in the bounded smooth-off-pole sense
      (∀ k, HasAnalyticSingularities (n := n) (psiSeq k)) ∧
      (∀ k, HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) (psiSeq k)) ∧
      -- (ii) decreasing to `psi` everywhere
      (∀ x, Antitone fun k => psiSeq k x) ∧ (∀ x, ⨅ k, psiSeq k x = psi x) ∧
      -- (iv) the curvature loss, with a vanishing constant
      (∀ k, 0 ≤ delta k) ∧ Tendsto delta atTop (𝓝 0) ∧
      ∀ k, IsThetaPshPotential (alpha + delta k • omega.form).val (psiSeq k) :=
  DemaillyApproximationSmoothOffPole.exists_algebraicApproximation omega alpha psi hpsi

/-- **The bounded smooth-off-pole form is a projection.**  Its statement is that of
`DemaillyAlgebraicApproximation.exists_algebraicApproximation`, character for
character, so that declaration can be proved as
`Demailly1992AlgebraicApproximation.exists_algebraicApproximation_smoothOffPole
omega alpha psi hpsi`. -/
theorem exists_algebraicApproximation_smoothOffPole [CompactSpace M]
    (omega : KahlerBackground n M) (alpha : ClosedRealOneOneForm n M) (psi : M → EReal)
    (hpsi : IsThetaPshPotential alpha.val psi) :
    ∃ (psiSeq : ℕ → M → EReal) (delta : ℕ → ℝ),
      -- (i) analytic singularities, in the bounded smooth-off-pole sense
      (∀ k, HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) (psiSeq k)) ∧
      -- (ii) decreasing to `psi` everywhere
      (∀ x, Antitone fun k => psiSeq k x) ∧ (∀ x, ⨅ k, psiSeq k x = psi x) ∧
      -- (iv) the curvature loss, with a vanishing constant
      (∀ k, 0 ≤ delta k) ∧ Tendsto delta atTop (𝓝 0) ∧
      ∀ k, IsThetaPshPotential (alpha + delta k • omega.form).val (psiSeq k) := by
  obtain ⟨psiSeq, delta, -, hsmooth, hanti, hinf, hdnn, hdlim, hpsh⟩ :=
    demailly1992_exists_algebraicApproximation omega alpha psi hpsi
  exact ⟨psiSeq, delta, hsmooth, hanti, hinf, hdnn, hdlim, hpsh⟩

end

end ComplexGeometry.AnalyticGeometry.Demailly1992AlgebraicApproximation
