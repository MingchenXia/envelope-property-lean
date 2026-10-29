/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeClosedImmersion
import EnvelopeProperty.Projective.NativeTopology

/-!
# Actual closed-projective native spaces and normalized graded points

For arbitrary coefficient rings and prescribed real seminorms, a true closed
immersion into actual polynomial Proj identifies its native fixed-base point
space with the closed normalized support locus. The entire original native map
and polynomial kernel are retained. Actual compactness and Hausdorffness follow
without any bound on coefficient values. Genuine ideal-sheaf-data closed
subschemes specialize this construction using their true scheme support.

No presentation certificate, nonempty closed subscheme, analytic structure sheaf
or coherent analytic ideal identification is assumed.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry EnvelopeProperty.Berkovich
universe u
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjBerk
variable {R : Type u} [CommRing R] (v : Valuation R ℝ≥0) {n : ℕ}
variable {X : Scheme.{u}} (g : X ⟶ NativeProjectiveScheme R n) [IsClosedImmersion g]

/-- The true normalized support locus of an actual closed-projective scheme immersion. -/
def normalizedClosedLocus : Set (RelativeNormalizedProjectiveSpectrum v n) :=
  {x | NormalizedProjectiveSpectrum.nativeSupport x.1 ∈ Set.range g}

/-- Genuine support continuity makes the actual closed-projective normalized locus closed. -/
theorem isClosed_normalizedClosedLocus : IsClosed (normalizedClosedLocus v g) :=
  g.isClosedEmbedding.isClosed_range.preimage
    (NormalizedProjectiveSpectrum.continuous_nativeSupport.comp continuous_subtype_val)

/-- A true closed-projective scheme immersion gives the actual normalized support-closed point-space comparison. -/
def nativeClosedProjectiveHomeomorph :
    RelativeSchemeValuedPoint v (g ≫ nativeStructureMap) ≃ₜ normalizedClosedLocus v g :=
  (RelativeSchemeValuedPoint.closedImmersionHomeomorph g rfl).trans
    ((RelativeNormalizedProjectiveSpectrum.nativeHomeomorph v).subtype (fun _ => Iff.rfl)).symm

/-- The closed-projective comparison preserves the entire original native image point. -/
theorem nativeClosedProjectiveHomeomorph_apply
    (x : RelativeSchemeValuedPoint v (g ≫ nativeStructureMap)) :
    RelativeNormalizedProjectiveSpectrum.nativeHomeomorph v (nativeClosedProjectiveHomeomorph v g x).1 =
      RelativeSchemeValuedPoint.map g rfl x := by
  let e : normalizedClosedLocus v g ≃ₜ
      {y : RelativeSchemeValuedPoint v (nativeStructureMap (R := R) (n := n)) //
        y.1.point ∈ Set.range g} :=
    (RelativeNormalizedProjectiveSpectrum.nativeHomeomorph v).subtype (fun _ => Iff.rfl)
  exact congrArg Subtype.val (e.apply_symm_apply
    (RelativeSchemeValuedPoint.closedImmersionHomeomorph g rfl x))

/-- The native image's entire homogeneous prime ideal is the resulting normalized seminorm kernel. -/
theorem nativeClosedProjectiveHomeomorph_support_toIdeal
    (x : RelativeSchemeValuedPoint v (g ≫ nativeStructureMap)) :
    (RelativeSchemeValuedPoint.map g rfl x).1.point.asHomogeneousIdeal.toIdeal =
      (nativeClosedProjectiveHomeomorph v g x).1.1.1.val.supp := by
  rw [← nativeClosedProjectiveHomeomorph_apply v g x]
  rfl

/-- Every actual closed-projective native fixed-base space is compact for arbitrary prescribed seminorms. -/
theorem compactSpace_nativeClosedProjective :
    CompactSpace (RelativeSchemeValuedPoint v (g ≫ nativeStructureMap)) := by
  let : CompactSpace (RelativeSchemeValuedPoint v (nativeStructureMap (R := R) (n := n))) :=
    compactSpace_nativeProjective v n
  exact (RelativeSchemeValuedPoint.isClosedEmbedding_map_of_isClosedImmersion g rfl).compactSpace

/-- The true closed-projective native space is Hausdorff through its actual normalized closed-locus embedding. -/
theorem t2Space_nativeClosedProjective :
    T2Space (RelativeSchemeValuedPoint v (g ≫ nativeStructureMap)) :=
  (nativeClosedProjectiveHomeomorph v g).isEmbedding.t2Space

/-- Its actual whole fixed-base locus is compact in the absolute native point topology. -/
theorem isCompact_nativeClosedProjective_relativeLocus :
    IsCompact (SchemeValuedPoint.relativeLocus v (g ≫ nativeStructureMap)) :=
  isCompact_iff_compactSpace.mpr (compactSpace_nativeClosedProjective v g)

/-- Actual ideal-sheaf-data closed projective subschemes are precisely the normalized points on their true scheme support. -/
def nativeProjectiveSubschemeHomeomorph (I : (NativeProjectiveScheme R n).IdealSheafData) :
    RelativeSchemeValuedPoint v (I.subschemeι ≫ nativeStructureMap) ≃ₜ
      {x : RelativeNormalizedProjectiveSpectrum v n |
        NormalizedProjectiveSpectrum.nativeSupport x.1 ∈ I.support} :=
  (nativeClosedProjectiveHomeomorph v I.subschemeι).trans
    (Homeomorph.setCongr (by
      ext x
      change NormalizedProjectiveSpectrum.nativeSupport x.1 ∈ Set.range I.subschemeι ↔
        NormalizedProjectiveSpectrum.nativeSupport x.1 ∈ I.support
      rw [I.range_subschemeι]
      rfl))

/-- The genuine projective closed-subscheme comparison retains the whole actual native inclusion point. -/
theorem nativeProjectiveSubschemeHomeomorph_apply
    (I : (NativeProjectiveScheme R n).IdealSheafData)
    (x : RelativeSchemeValuedPoint v (I.subschemeι ≫ nativeStructureMap)) :
    RelativeNormalizedProjectiveSpectrum.nativeHomeomorph v (nativeProjectiveSubschemeHomeomorph v I x).1 =
      RelativeSchemeValuedPoint.map I.subschemeι rfl x :=
  nativeClosedProjectiveHomeomorph_apply v I.subschemeι x

/-- The actual prescribed-base point space of every genuine projective ideal-sheaf-data closed subscheme is compact. -/
theorem compactSpace_nativeProjectiveSubscheme
    (I : (NativeProjectiveScheme R n).IdealSheafData) :
    CompactSpace (RelativeSchemeValuedPoint v (I.subschemeι ≫ nativeStructureMap)) :=
  compactSpace_nativeClosedProjective v I.subschemeι

end EnvelopeProperty.ProjBerk
