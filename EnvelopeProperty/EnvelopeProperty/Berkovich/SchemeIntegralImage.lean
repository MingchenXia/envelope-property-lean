/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeClosedImmersion
import EnvelopeProperty.Berkovich.SpectrumIntegralImage
import Mathlib.AlgebraicGeometry.Morphisms.Integral


/-!
# Actual native point lifting under integral scheme maps

An actual scheme preimage witness proves the precise section-kernel obstruction
through genuine residue evaluation and the injective residue-field map.
The constructed integral-spectrum lift and whole actual native affine chart
square then recover the original native point. Consequently native images are
exactly the support preimages of genuine integral scheme images, and a
scheme-surjective integral morphism is native-surjective. Exact whole same-base
membership is preserved. No coefficient bound, field, Noetherianity, completeness
or finite-type assumption is imposed. No lift at a specifically chosen source
support and no compatible different-coefficient prescribed-point surjectivity
is asserted.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite
universe u
noncomputable section
namespace EnvelopeProperty.Berkovich.SchemeValuedPoint
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]

/-- Native points on the genuine scheme image of an integral morphism admit actual whole-point lifts. -/
theorem exists_map_eq_of_point_mem_integralImage (y : SchemeValuedPoint Y)
    (hy : y.point ∈ Set.range f) : ∃ x : SchemeValuedPoint X, map f x = y := by
  rcases y with ⟨p, v⟩
  obtain ⟨x, hx⟩ := hy
  change f x = p at hx
  subst p
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (U := ⊤) (x := f x) trivial
  let z := affineOpenSpectrumHomeomorph hU ⟨⟨f x, v⟩, hxU⟩
  have hz : RingHom.ker (f.app U).hom ≤ z.val.supp := by
    intro a ha
    change z.val a = 0
    dsimp only [z]
    rw [affineOpenSpectrumHomeomorph_val_apply]
    change v (Y.evaluation U (f x) hxU a) = 0
    have he : Y.evaluation U (f x) hxU a = 0 := by
      apply (f.residueFieldMap x).hom.injective
      rw [map_zero, Scheme.evaluation_naturality_apply,
        RingHom.mem_ker.mp ha, map_zero]
    rw [he, map_zero]
  obtain ⟨t, ht⟩ := Spectrum.exists_comap_eq_of_isIntegral
    (f.app U).hom (f.isIntegral_app U hU) z hz
  let w := (affineOpenSpectrumHomeomorph (hU.preimage f)).symm t
  refine ⟨w.1, ?_⟩
  have he : affineOpenSpectrumHomeomorph hU ⟨map f w.1, w.2⟩ = z := by
    rw [affineOpenSpectrumHomeomorph_map]
    simpa only [w, Homeomorph.apply_symm_apply] using ht
  exact congrArg Subtype.val ((affineOpenSpectrumHomeomorph hU).injective he)

/-- The actual native image of an integral scheme morphism is exactly its genuine support-image locus. -/
theorem range_map_of_isIntegralHom :
    Set.range (map f) = (fun y : SchemeValuedPoint Y => y.point) ⁻¹' Set.range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.point, rfl⟩
  · exact exists_map_eq_of_point_mem_integralImage f y

/-- Every scheme-surjective integral morphism is surjective on actual native valued points. -/
theorem map_surjective_of_isIntegralHom (hf : Function.Surjective f) : Function.Surjective (map f) :=
  fun y => exists_map_eq_of_point_mem_integralImage f y (hf y.point)

end EnvelopeProperty.Berkovich.SchemeValuedPoint
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}
variable (g : X ⟶ Y) (hg : g ≫ fY = fX) [IsIntegralHom g]

/-- Whole native integral-image lifts automatically preserve an actual common prescribed base point. -/
theorem exists_map_eq_of_point_mem_integralImage (y : RelativeSchemeValuedPoint v fY)
    (hy : y.1.point ∈ Set.range g) : ∃ x : RelativeSchemeValuedPoint v fX, map g hg x = y := by
  obtain ⟨x, hx⟩ := SchemeValuedPoint.exists_map_eq_of_point_mem_integralImage g y.1 hy
  have hrel : x ∈ SchemeValuedPoint.relativeLocus v fX := by
    rw [relativeLocus_preimage_eq g hg]
    change SchemeValuedPoint.map g x ∈ SchemeValuedPoint.relativeLocus v fY
    rw [hx]
    exact y.2
  exact ⟨⟨x, hrel⟩, Subtype.ext hx⟩

/-- The true same-base prescribed native image of an integral morphism equals its support-image locus. -/
theorem range_map_of_isIntegralHom :
    Set.range (map (v := v) g hg) =
      (fun y : RelativeSchemeValuedPoint v fY => y.1.point) ⁻¹' Set.range g := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1.point, rfl⟩
  · exact exists_map_eq_of_point_mem_integralImage g hg y

/-- Scheme-surjective integral morphisms over a common base lift every actual prescribed-base native point. -/
theorem map_surjective_of_isIntegralHom (hgs : Function.Surjective g) :
    Function.Surjective (map (v := v) g hg) :=
  fun y => exists_map_eq_of_point_mem_integralImage g hg y (hgs y.1.point)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
