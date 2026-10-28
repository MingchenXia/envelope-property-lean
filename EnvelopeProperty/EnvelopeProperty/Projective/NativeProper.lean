/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.Projective.NormalizedSpectrumProper
import EnvelopeProperty.Projective.NativeAbsolute
import EnvelopeProperty.Berkovich.SchemeClosedImmersion

/-!
# Actual native projective proper maps over arbitrary coefficient valuations

Whole original coefficient/basepoint comparison transports proved absolute
normalized-spectrum properness. Actual geometric closed immersions and exact
common prescribed-base restrictions retain this properness without bounds.
-/
open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry
open EnvelopeProperty.ProjBerk
universe u
noncomputable section
namespace EnvelopeProperty.Berkovich.NormalizedProjectiveSpectrum
variable {R : Type u} [CommRing R] {n : ℕ}

/-- The ENTIRE actual native structure map retains the whole ORIGINAL coefficient-restriction point. -/
theorem nativeAbsoluteHomeomorph_coefficientRestriction (x : NormalizedProjectiveSpectrum R n) :
    SchemeValuedPoint.spectrumHomeomorph
      (SchemeValuedPoint.map nativeStructureMap (nativeAbsoluteHomeomorph x)) =
      coefficientRestriction x := by
  have h := (nativeAbsoluteHomeomorph_mem_relativeLocus (coefficientRestriction x).val x).mpr
    (fun r => rfl)
  change SchemeValuedPoint.map nativeStructureMap (nativeAbsoluteHomeomorph x) =
    SchemeValuedPoint.basePoint (coefficientRestriction x).val at h
  rw [h, SchemeValuedPoint.basePoint, Homeomorph.apply_symm_apply]
  rfl

/-- The GENUINE original native polynomial projective structure map is proper, without bounded coefficients. -/
theorem isProperMap_map_nativeStructureMap :
    IsProperMap (SchemeValuedPoint.map (nativeStructureMap (R := R) (n := n))) := by
  have he : SchemeValuedPoint.map (nativeStructureMap (R := R) (n := n)) =
      SchemeValuedPoint.spectrumHomeomorph.symm ∘ coefficientRestriction ∘
        nativeAbsoluteHomeomorph.symm := by
    funext y
    apply SchemeValuedPoint.spectrumHomeomorph.injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    rw [← nativeAbsoluteHomeomorph_coefficientRestriction,
      Homeomorph.apply_symm_apply]
  rw [he]
  exact SchemeValuedPoint.spectrumHomeomorph.symm.isClosedEmbedding.isProperMap.comp
    (isProperMap_coefficientRestriction.comp nativeAbsoluteHomeomorph.symm.isClosedEmbedding.isProperMap)

/-- Actual native polynomial projective maps are closed over arbitrary commutative coefficients. -/
theorem isClosedMap_map_nativeStructureMap :
    IsClosedMap (SchemeValuedPoint.map (nativeStructureMap (R := R) (n := n))) :=
  isProperMap_map_nativeStructureMap.isClosedMap

/-- A TRUE geometric closed projective immersion gives native properness of the SAME entire original structure map. -/
theorem isProperMap_map_closedProjective {X : Scheme.{u}}
    (j : X ⟶ NativeProjectiveScheme R n) [IsClosedImmersion j] :
    IsProperMap (SchemeValuedPoint.map (j ≫ nativeStructureMap)) := by
  have hp := isProperMap_map_nativeStructureMap.comp
    (SchemeValuedPoint.isProperMap_map_of_isClosedImmersion j)
  have he : SchemeValuedPoint.map (j ≫ nativeStructureMap) =
      SchemeValuedPoint.map nativeStructureMap ∘ SchemeValuedPoint.map j :=
    funext (SchemeValuedPoint.map_comp j nativeStructureMap)
  rw [he]
  exact hp

/-- ANY exact common coefficient locus retains properness of the original closed-projective structure map. -/
theorem isProperMap_relativeMap_closedProjective {B : Type u} [CommRing B]
    (v : Valuation B ℝ≥0) {X : Scheme.{u}}
    (j : X ⟶ NativeProjectiveScheme R n) [IsClosedImmersion j]
    (f : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of B)) :
    IsProperMap (RelativeSchemeValuedPoint.map (v := v) (j ≫ nativeStructureMap)
      (fY := f) (fX := (j ≫ nativeStructureMap) ≫ f) rfl) := by
  have hcomp := (isProperMap_map_closedProjective j).comp
    (SchemeValuedPoint.isClosed_relativeLocus v ((j ≫ nativeStructureMap) ≫ f)).isClosedEmbedding_subtypeVal.isProperMap
  exact isProperMap_of_comp_of_inj
    (RelativeSchemeValuedPoint.continuous_map (j ≫ nativeStructureMap) rfl)
    continuous_subtype_val hcomp Subtype.val_injective

end EnvelopeProperty.Berkovich.NormalizedProjectiveSpectrum
