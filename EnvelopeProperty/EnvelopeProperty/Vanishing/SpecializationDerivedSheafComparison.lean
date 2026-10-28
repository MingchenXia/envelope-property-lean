import EnvelopeProperty.Vanishing.SpecializationDerivedScalarCoefficients
import EnvelopeProperty.AlgGeom.AffinePushforwardCohomology

/-! # Native sheaf cohomology and literal original scalar section homology -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.SpecializationDerivedSheafComparison

open SpecializationDerivedScalarCoefficients

/-- Native positive sheaf cohomology is exactly zero homology of the actual
ordered section complex with the literal original affine-base action. -/
theorem subsingleton_H_iff_restrict_ordered_zero
    {R : Type u} [CommRing R] {X : Scheme.{u}} [X.IsSeparated]
    (f : X ⟶ Spec (.of R)) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) ↔
      IsZero ((restrictComplex (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
        (orderedBaseCechComplex f M U)).homology (q + 1)) :=
  (AffinePushforwardCohomology.subsingleton_H_iff_ordered_zero f M U hU hUaff q).trans
    (restrictComplex_homology_isZero_iff
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
      (orderedBaseCechComplex f M U) (q + 1)).symm

end EnvelopeProperty.Vanishing.SpecializationDerivedSheafComparison
