import EnvelopeProperty.Char0.RelativeHomogeneousSectionLift
import EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomial

/-! # Actual original homogeneous polynomial lifts beyond one fixed bound -/

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open Scheme.Modules
noncomputable section
universe u

namespace EnvelopeProperty.Char0.RelativeHomogeneousSectionLift
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {N : ℕ} {Y : Scheme.{u}}

/-- Every section of every sufficiently large original pulled native twist
is the actual original pullback of an original homogeneous polynomial. -/
theorem exists_polynomial_lift_bound
    (i : Y ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) [IsClosedImmersion i] :
    ∃ b : ℕ, ∀ e : ℕ, b ≤ e →
      ∀ s : Γ((Scheme.Modules.pullback i).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (e : ℤ)), ⊤),
      ∃ F : MvPolynomial (Fin (N + 1)) R, ∃ hF : F.IsHomogeneous e,
        affinePullbackUnitTop i
          (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (e : ℤ))
          (ProjectiveHomogeneousSections.homogeneousSection (0 : Fin (N + 1)) e F hF) = s := by
  obtain ⟨b, hb⟩ := exists_section_lift_bound i
  refine ⟨b, fun e he s => ?_⟩
  obtain ⟨t, ht⟩ := hb e he s
  obtain ⟨F, hF, hpoly⟩ :=
    RelativeProjectiveSectionPolynomial.exists_homogeneous_polynomial (0 : Fin (N + 1)) e t
  refine ⟨F, hF, ?_⟩
  simpa only [hpoly] using ht

/-- The SAME original polynomial lift acts on powers of the SAME original H,
through the already-proved native whole hyperplane-power comparison. -/
theorem exists_power_polynomial_lift_bound
    (i : Y ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) [IsClosedImmersion i] :
    ∃ b : ℕ, ∀ e : ℕ, b ≤ e →
      ∀ s : Γ(CanonicalGeometry.bundleTensorPower (NadelClearedTwist.hyperplane i) e, ⊤),
      ∃ F : MvPolynomial (Fin (N + 1)) R, ∃ hF : F.IsHomogeneous e,
        (NadelClearedTwist.hyperplanePowerIso i e).inv.app ⊤
          (affinePullbackUnitTop i
            (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (e : ℤ))
            (ProjectiveHomogeneousSections.homogeneousSection (0 : Fin (N + 1)) e F hF)) = s := by
  obtain ⟨b, hb⟩ := exists_power_section_lift_bound i
  refine ⟨b, fun e he s => ?_⟩
  obtain ⟨t, ht⟩ := hb e he s
  obtain ⟨F, hF, hpoly⟩ :=
    RelativeProjectiveSectionPolynomial.exists_homogeneous_polynomial (0 : Fin (N + 1)) e t
  refine ⟨F, hF, ?_⟩
  simpa only [hpoly] using ht

end EnvelopeProperty.Char0.RelativeHomogeneousSectionLift
