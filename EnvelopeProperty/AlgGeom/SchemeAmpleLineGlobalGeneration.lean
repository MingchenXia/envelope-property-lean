import EnvelopeProperty.AlgGeom.PositivePowerProjectiveGeneration
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness

/-! # Eventual global generation of the original geometrically ample line -/
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.SchemeAmpleLineGlobalGeneration
open Scheme.Modules CanonicalGeometry

/-- The actual geometric ample criterion derives finite generation of EVERY
sufficiently large original tensor power. -/
theorem exists_eventual_generatingSections {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (L : X.Modules) (h : SchemeLineAmpleness.IsAmple p L) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ G : (bundleTensorPower L m).GeneratingSections, G.IsFiniteType := by
  obtain ⟨r, hr, n, i, hi, _hp, ⟨e⟩⟩ := h.2
  exact @PositivePowerProjectiveGeneration.exists_eventual_generatingSections
    R _ (Fin (n + 1)) _ X i hi L h.1 r hr (0 : Fin (n + 1)) e

end EnvelopeProperty.SchemeAmpleLineGlobalGeneration
