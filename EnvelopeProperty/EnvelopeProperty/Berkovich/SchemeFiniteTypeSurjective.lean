/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.FiniteTypeFieldPoint
import EnvelopeProperty.Berkovich.SchemeAtlas
import EnvelopeProperty.Berkovich.SchemeRelativeBaseChange
import EnvelopeProperty.Berkovich.SpectrumResidueField
import EnvelopeProperty.Berkovich.ValuationExtension

/-!
# Genuine native lifts under locally finite type scheme-surjections

An original point is recovered through its actual affine H(a), with every
original coefficient and the entire residue valuation preserved. Actual
finite field points of the true scheme fibre and real complete-field norm
extension then construct native lifts, without a native lifting certificate.
-/
open scoped NNReal Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
noncomputable section
namespace EnvelopeProperty.Berkovich.SchemeValuedPoint

/-- The ORIGINAL completed residue-field coefficient map recovers the ENTIRE original affine point. -/
theorem map_norm_basePoint_toH {A : Type u} [CommRing A] (a : Spectrum A) :
    map (Spec.map (CommRingCat.ofHom a.toH)) (basePoint (NormedField.valuation (K := Spectrum.H a))) =
      spectrumHomeomorph.symm a := by
  apply spectrumHomeomorph.injective
  rw [spectrumHomeomorph_map, basePoint, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]
  apply Spectrum.ext_val
  intro t
  exact Spectrum.nnnorm_toH a t

/-- A TRUE affine chart and the literal H(a) produce a whole original field-valued point, not a support lift. -/
theorem exists_complete_field_point {X : Scheme.{u}} (x : SchemeValuedPoint X) :
    ∃ (K : Type u) (_ : NormedField K) (_ : CompleteSpace K) (_ : IsUltrametricDist K)
      (q : Spec (CommRingCat.of K) ⟶ X), map q (basePoint (NormedField.valuation (K := K))) = x := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x.point ∈ (⊤ : X.Opens) from trivial)
  let a := affineOpenSpectrumHomeomorph hU ⟨x, hx⟩
  refine ⟨Spectrum.H a, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom a.toH) ≫ hU.fromSpec, ?_⟩
  rw [map_comp, map_norm_basePoint_toH]
  have he := congrArg Subtype.val ((affineOpenSpectrumHomeomorph hU).symm_apply_apply ⟨x, hx⟩)
  rw [affineOpenSpectrumHomeomorph_symm_coe] at he
  change map U.ι (map hU.isoSpec.inv (spectrumHomeomorph.symm a)) = x at he
  simpa only [IsAffineOpen.fromSpec, map_comp] using he

/-- Actual scheme-surjective LOCALLY finite type morphisms lift EVERY whole native point. -/
theorem map_surjective_of_locallyOfFiniteType {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : Function.Surjective f) :
    Function.Surjective (map f) := by
  intro x
  obtain ⟨K, hK, hcomplete, hultra, q, hq⟩ := exists_complete_field_point x
  let : Surjective f := ⟨hf⟩
  obtain ⟨L, hL, aL, hfinite, p, hp⟩ := FiniteTypePoint.exists_finite_field_lift f q
  let : Module.Finite K L := hfinite
  obtain ⟨w, hw⟩ := EnvelopeProperty.Valuation.exists_extends_norm (K := K) (L := L)
  refine ⟨map p (basePoint w), ?_⟩
  rw [← map_comp, hp, map_comp]
  have hr : map (Spec.map (CommRingCat.ofHom (algebraMap K L))) (basePoint w) =
      basePoint (NormedField.valuation (K := K)) := map_basePoint _ hw
  rw [hr]
  exact hq

end EnvelopeProperty.Berkovich.SchemeValuedPoint

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of R)}
  {fY : Y ⟶ Spec (CommRingCat.of R)}

/-- Actual locally finite type scheme-surjections lift EVERY exact common prescribed-base whole native point. -/
theorem map_surjective_of_locallyOfFiniteType (g : X ⟶ Y) (hg : g ≫ fY = fX)
    [LocallyOfFiniteType g] (hgs : Function.Surjective g) :
    Function.Surjective (map (v := v) g hg) := by
  intro y
  obtain ⟨x, hx⟩ := SchemeValuedPoint.map_surjective_of_locallyOfFiniteType g hgs y.1
  have hrel : x ∈ SchemeValuedPoint.relativeLocus v fX := by
    change SchemeValuedPoint.map fX x = SchemeValuedPoint.basePoint v
    rw [← hg, SchemeValuedPoint.map_comp, hx]
    exact y.2
  exact ⟨⟨x, hrel⟩, Subtype.ext hx⟩

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
