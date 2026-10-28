import EnvelopeProperty.AlgGeom.SchemeLineAmpleness
import DeJongAlterations.Geometry.FiniteProjectivePreservation
/-! # Actual finite preservation supplies a very-ample line on the whole original source -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelFiniteAmplePullbackProjective

/-- The original ample datum and actual finite morphism internally construct
an actual very-ample line on the whole original source. -/
theorem exists_isVeryAmple_line {R : Type u} [CommRing R] {X W : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple p L)
    (π : W ⟶ X) [IsFinite π] :
    ∃ H : W.Modules, SchemeLineAmpleness.IsVeryAmple (π ≫ p) H := by
  obtain ⟨r, _hr, n, i, hi, hip, _e⟩ := hL.2
  have hp : DeJongAlterations.IsProjectiveOver p := ⟨n, i, hi, hip⟩
  obtain ⟨m, j, hj, hjp⟩ :=
    DeJongAlterations.Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite p hp π
  exact ⟨(pullback j).obj (coordinateHyperplaneTwist (R := R) (0 : Fin (m + 1)) 1),
    m, j, hj, hjp, ⟨Iso.refl _⟩⟩
end EnvelopeProperty.Vanishing.NadelFiniteAmplePullbackProjective
