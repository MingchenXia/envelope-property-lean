import EnvelopeProperty.Projective.NativeComparison

/-!
# Genuine native projective compactness over arbitrary prescribed seminorms

The fixed-base normalized spectrum is genuinely compact without any uniform
coefficient bound. Its actual native homeomorphism transports compactness and
the real zero-coordinate witness to native polynomial projective space.
-/

open scoped NNReal Topology
open Topology EnvelopeProperty.Berkovich
noncomputable section
namespace EnvelopeProperty.ProjBerk
variable {R : Type*} [CommRing R] (v : Valuation R ℝ≥0) (n : ℕ)

/-- The actual native fixed-base projective space is compact for every coefficient seminorm, including unbounded ones. -/
theorem compactSpace_nativeProjective :
    CompactSpace (RelativeSchemeValuedPoint v (nativeStructureMap (R := R) (n := n))) :=
  (RelativeNormalizedProjectiveSpectrum.nativeHomeomorph (n := n) v).compactSpace

/-- The actual whole fixed-base locus is a compact subset of the absolute native projective point space. -/
theorem isCompact_nativeProjective_relativeLocus :
    IsCompact (SchemeValuedPoint.relativeLocus v (nativeStructureMap (R := R) (n := n))) :=
  isCompact_iff_compactSpace.mpr (compactSpace_nativeProjective v n)

/-- A genuine zero-coordinate Gauss chart supplies a native projective point above every prescribed seminorm. -/
theorem nonempty_nativeProjective :
    Nonempty (RelativeSchemeValuedPoint v (nativeStructureMap (R := R) (n := n))) :=
  ⟨RelativeNormalizedProjectiveSpectrum.nativeHomeomorph v
    (RelativeNormalizedProjectiveSpectrum.zeroCoordinates (n := n) v)⟩
end EnvelopeProperty.ProjBerk
