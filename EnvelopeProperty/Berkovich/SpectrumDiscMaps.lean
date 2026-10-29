/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumQuotient
import EnvelopeProperty.Berkovich.SchemeRelativeAtlas
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Genuine whole translated discs and their actual native polynomial square

Actual polynomial automorphisms restrict to real closed coordinate loci over
arbitrary coefficient rings and valuations. No field or norm bound is needed
for the translation homeomorphism; every original polynomial value is retained.
-/
open scoped NNReal Polynomial
open Polynomial CategoryTheory AlgebraicGeometry Topology
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (v : Valuation R ℝ≥0)

/-- The genuine whole fixed-base polynomial point locus with bounded original coordinate. -/
abbrev CoordinateDisc (r : ℝ≥0) := {x : RelativeSpectrum v A[X] // x.1.val X ≤ r}

/-- The genuine whole fixed-base polynomial point locus with bounded translated coordinate. -/
abbrev TranslatedDisc (a : A) (r : ℝ≥0) :=
  {x : RelativeSpectrum v A[X] // x.1.val (X - C a) ≤ r}

/-- The ACTUAL entire polynomial automorphism gives a genuine translated closed-disc homeomorphism. -/
def discTranslationHomeomorph (a : A) (r : ℝ≥0) :
    CoordinateDisc (A := A) v r ≃ₜ TranslatedDisc v a r :=
  (algEquivHomeomorph v ((Polynomial.algEquivAevalXAddC a).restrictScalars R)).subtype fun x => by
    change x.1.val X ≤ r ↔ x.1.val (Polynomial.algEquivAevalXAddC a (X - C a)) ≤ r
    have h : Polynomial.algEquivAevalXAddC a (X - C a) = X := by
      simp [Polynomial.algEquivAevalXAddC]
    rw [h]

@[simp]
theorem discTranslationHomeomorph_val_apply (a : A) (r : ℝ≥0)
    (x : CoordinateDisc (A := A) v r) (p : A[X]) :
    (discTranslationHomeomorph v a r x).1.1.val p =
      x.1.1.val (Polynomial.algEquivAevalXAddC a p) := rfl

/-- The actual translated disc is a CLOSED embedded whole point locus without compactness or separation assumptions. -/
theorem isClosedEmbedding_discTranslation (a : A) (r : ℝ≥0) :
    IsClosedEmbedding (fun x : CoordinateDisc (A := A) v r =>
      (discTranslationHomeomorph v a r x).1) := by
  have hc : IsClosed {x : RelativeSpectrum v A[X] | x.1.val (X - C a) ≤ r} :=
    isClosed_le ((Spectrum.continuous_val_apply _).comp continuous_subtype_val) continuous_const
  exact hc.isClosedEmbedding_subtypeVal.comp (discTranslationHomeomorph v a r).isClosedEmbedding

/-- The genuine entire translated point is the ACTUAL Spec polynomial automorphism on native points. -/
theorem discTranslationHomeomorph_native (a : A) (r : ℝ≥0)
    (x : CoordinateDisc (A := A) v r) :
    RelativeSchemeValuedPoint.affineSpectrumHomeomorph.symm (discTranslationHomeomorph v a r x).1 =
      RelativeSchemeValuedPoint.map
        (Spec.map (CommRingCat.ofHom
          ((Polynomial.algEquivAevalXAddC a).toAlgHom.restrictScalars R).toRingHom))
        (RelativeSchemeValuedPoint.affineStructureMap_commutes
          ((Polynomial.algEquivAevalXAddC a).toAlgHom.restrictScalars R))
        (RelativeSchemeValuedPoint.affineSpectrumHomeomorph.symm x.1) := by
  apply RelativeSchemeValuedPoint.affineSpectrumHomeomorph.injective
  rw [Homeomorph.apply_symm_apply, RelativeSchemeValuedPoint.affineSpectrumHomeomorph_map,
    Homeomorph.apply_symm_apply]
  rfl

end EnvelopeProperty.Berkovich.RelativeSpectrum
