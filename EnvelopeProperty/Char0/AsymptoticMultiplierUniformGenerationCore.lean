import EnvelopeProperty.Char0.SchemeAsymptoticMultiplierStabilization
import EnvelopeProperty.AlgGeom.Canonical.CanonicalLineSheaf
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness

/-! # Actual whole asymptotic adjoint modules, with internally produced constituent indices

The original global ideal-sheaf stabilization theorem is consumed, not assumed.
All natural multiplier indices, including zero, are retained. The actual whole
ideal module and original field structure occur in every conclusion.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.Char0.AsymptoticMultiplierUniformGeneration
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [Smooth p]

/-- The SAME original whole asymptotic ideal module with the original canonical twist. -/
def twistedModule (n : ℕ) (J : ℕ → X.IdealSheafData)
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥)
    (m : ℕ) (A : X.Modules) : X.Modules :=
  (canonicalLineSheaf p n ⊗ A) ⊗ (schemeAsymptoticMultiplierIdealSheaf p J hne m).toModules

/-- Actual gradedness internally produces whole-module attainment at EVERY sufficiently divisible
ORIGINAL index. No maximal constituent, stabilization index or module comparison is supplied. -/
theorem exists_divisible_twistedModule_eq [CompactSpace X]
    (n : ℕ) {J : ℕ → X.IdealSheafData} (hJ : ∀ a b, J a * J b ≤ J (a + b))
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥)
    (m : ℕ) (A : X.Modules) :
    ∃ q₀, 0 < q₀ ∧ ∀ q (hq : 0 < q), q₀ ∣ q →
      twistedModule p n J hne m A =
        (canonicalLineSheaf p n ⊗ A) ⊗
          (schemeMultiplierIdealSheaf p (J q) (hne q hq) ((m : ℚ) / q)).toModules := by
  obtain ⟨q₀, hq₀, he⟩ := exists_schemeAsymptoticMultiplierIdealSheaf_eq p hJ hne m
  exact ⟨q₀, hq₀, fun q hq hd =>
    congrArg (fun I : X.IdealSheafData => (canonicalLineSheaf p n ⊗ A) ⊗ I.toModules) (he q hq hd)⟩

/-- A positive ORIGINAL constituent realizing the entire original asymptotic twisted module is produced internally. -/
theorem exists_constituent_twistedModule_eq [CompactSpace X]
    (n : ℕ) {J : ℕ → X.IdealSheafData} (hJ : ∀ a b, J a * J b ≤ J (a + b))
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥)
    (m : ℕ) (A : X.Modules) :
    ∃ (q : ℕ) (hq : 0 < q),
      twistedModule p n J hne m A =
        (canonicalLineSheaf p n ⊗ A) ⊗
          (schemeMultiplierIdealSheaf p (J q) (hne q hq) ((m : ℚ) / q)).toModules := by
  obtain ⟨q, hq, he⟩ := exists_divisible_twistedModule_eq p n hJ hne m A
  exact ⟨q, hq, he q hq (dvd_refl q)⟩

/-- The original projective geometry DERIVES compactness and then a whole original constituent,
without a compactness, stabilization or module-comparison certificate input. -/
theorem exists_constituent_twistedModule_eq_of_projective {R : Type u} [CommRing R]
    (π : X ⟶ Spec (.of R)) (hp : IsProjectiveFactorization π)
    (n : ℕ) {J : ℕ → X.IdealSheafData} (hJ : ∀ a b, J a * J b ≤ J (a + b))
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥)
    (m : ℕ) (A : X.Modules) :
    ∃ (q : ℕ) (hq : 0 < q),
      twistedModule p n J hne m A =
        (canonicalLineSheaf p n ⊗ A) ⊗
          (schemeMultiplierIdealSheaf p (J q) (hne q hq) ((m : ℚ) / q)).toModules := by
  let : IsProper π := hp.isProper
  let : CompactSpace X := (quasiCompact_iff_compactSpace π).mp inferInstance
  exact exists_constituent_twistedModule_eq p n hJ hne m A

end EnvelopeProperty.Char0.AsymptoticMultiplierUniformGeneration
