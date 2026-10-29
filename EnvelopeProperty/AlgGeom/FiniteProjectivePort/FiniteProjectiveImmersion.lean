import EnvelopeProperty.AlgGeom.FiniteProjectivePort.FiniteProjectiveMarkerOpen
import EnvelopeProperty.AlgGeom.FiniteProjectivePort.FiniteProjectiveAffineClosed
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import EnvelopeProperty.Alterations.Geometry.FiniteProjectiveImmersion

/-!
# Native finite-projectivity compatibility import

The original declarations are supplied by `Alterations.Geometry.FiniteProjectiveImmersion`.
Existing port imports are retained for compatibility.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Alterations.Geometry.FiniteProjective

universe u

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} {n : ℕ}

/-- An actual affine morphism into projective space and finite-type coefficient
structure internally produce an original-source projective immersion. -/
theorem exists_projectiveImmersion_of_affine_to_projective
    (p : Y ⟶ Spec (.of R)) [LocallyOfFiniteType p]
    (g : Y ⟶ projectiveSpace R n) [IsAffineHom g] :
    ∃ (m : ℕ) (e : Y ⟶ projectiveSpace R m), IsImmersion e ∧
      e ≫ projectiveSpaceStructure R m = p := by
  obtain ⟨T⟩ := exists_generatingTuple p g
  exact ⟨T.dimension, tupleProjectiveMap T, tupleProjectiveMap_isImmersion T,
    tupleProjectiveMap_structure T⟩

end Alterations.Geometry.FiniteProjective
