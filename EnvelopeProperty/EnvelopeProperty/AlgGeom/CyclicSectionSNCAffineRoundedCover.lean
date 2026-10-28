import EnvelopeProperty.AlgGeom.CyclicSectionSNCNormalizationRounded
import EnvelopeProperty.AlgGeom.CyclicSectionAffineCover

/-! # Actual affine geometry of the original SNC rounded algebra

The SAME rounded subalgebra in the original generic cyclic quotient has its
native finite flat surjective projection and its native finite comparison to
the original raw affine cover. No normality or normalization identification
is asserted, and no geometric certificate is an input.
-/

open CategoryTheory AlgebraicGeometry
open scoped BigOperators
noncomputable section
universe u v

namespace EnvelopeProperty.CyclicSectionSNCAffineRoundedCover
open CyclicSectionAlgebra CyclicSectionSNCNormalizationRounded
variable {R : Type u} [CommRing R] [IsDomain R]
variable {J : Type v} [Fintype J]

/-- The actual spectrum map of the SAME original rounded scalar inclusion. -/
def projection (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    Spec (.of (roundedAlgebra n α u f hn hf)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (roundedAlgebra n α u f hn hf)))

/-- The actual comparison is induced by the SAME original `rawToRounded`. -/
def rawComparison (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    Spec (.of (roundedAlgebra n α u f hn hf)) ⟶
      Spec (.of (RootRing n (u * ∏ j, f j ^ α j))) :=
  Spec.map (CommRingCat.ofHom (rawToRounded n α u f hn hf).toRingHom)

/-- The full original rounded/raw/base triangle commutes as actual scheme maps. -/
theorem rawComparison_projection (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    rawComparison n α u f hn hf ≫
      CyclicSectionAffineCover.structureMap n (u * ∏ j, f j ^ α j) =
        projection n α u f hn hf := by
  simp only [rawComparison, CyclicSectionAffineCover.structureMap, projection, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun r => (rawToRounded n α u f hn hf).commutes r)

/-- The actual original rounded basis produces freeness of the WHOLE same algebra. -/
theorem free (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    Module.Free R (roundedAlgebra n α u f hn hf) :=
  Module.Free.of_basis (basis n α u f hn hf)

/-- Positive rank of the SAME original rounded basis produces native faithful flatness. -/
theorem faithfullyFlat (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    Module.FaithfullyFlat R (roundedAlgebra n α u f hn hf) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Module.FaithfullyFlat.of_linearEquiv R (Fin n →₀ R)
    (basis n α u f hn hf).repr

/-- The actual rounded affine projection is finite over its SAME original base. -/
theorem isFinite_projection (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    IsFinite (projection n α u f hn hf) := by
  have := roundedAlgebra_finite n α u f hn hf
  apply (IsFinite.SpecMap_iff _).2
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- The actual rounded affine projection is flat by its produced original free basis. -/
theorem flat_projection (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    Flat (projection n α u f hn hf) := by
  have := free n α u f hn hf
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The actual rounded affine projection is surjective by its produced faithful flatness. -/
theorem surjective_projection (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    Surjective (projection n α u f hn hf) := by
  exact ((flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap R (roundedAlgebra n α u f hn hf)))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr (faithfullyFlat n α u f hn hf))).2

/-- Restriction of scalars in the actual R/raw/rounded tower makes the SAME map finite. -/
theorem rawToRounded_finite (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    (rawToRounded n α u f hn hf).toRingHom.Finite := by
  let := (rawToRounded n α u f hn hf).toAlgebra
  have : IsScalarTower R (RootRing n (u * ∏ j, f j ^ α j))
      (roundedAlgebra n α u f hn hf) :=
    IsScalarTower.of_algebraMap_eq (fun r => ((rawToRounded n α u f hn hf).commutes r).symm)
  have := roundedAlgebra_finite n α u f hn hf
  exact Module.Finite.of_restrictScalars_finite R
    (RootRing n (u * ∏ j, f j ^ α j)) (roundedAlgebra n α u f hn hf)

/-- The SAME actual spectrum comparison to the original raw cyclic cover is finite. -/
theorem isFinite_rawComparison (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    IsFinite (rawComparison n α u f hn hf) := by
  exact (IsFinite.SpecMap_iff _).mpr (rawToRounded_finite n α u f hn hf)

end EnvelopeProperty.CyclicSectionSNCAffineRoundedCover
