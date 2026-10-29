/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.ValuationPurelyInseparable
import EnvelopeProperty.Berkovich.SchemeIntegralImage
import EnvelopeProperty.Berkovich.SchemeIntegralMaps
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective


/-!
# Native invariance under genuine universal-homeomorphism conditions

Mathlib's actual universally injective scheme hypothesis gives scheme-point
injection and purely inseparable residue-field maps. The genuine power
valuation uniqueness theorem therefore proves whole native point injection.
For actual integral scheme-surjective morphisms, derived native closedness
and point lifting give a real homeomorphism, absolute and over any common
prescribed base seminorm. No native bijection or residue-comparison certificate,
coefficient bound, separatedness, completeness or finite-type hypothesis is
assumed. No normalization or cross-coefficient fixed-point extension is claimed.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite
universe u
noncomputable section
namespace EnvelopeProperty.Berkovich.SchemeValuedPoint
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversallyInjective f]

/-- Genuine universal injectivity supplies the actual purely inseparable residue-field maps. -/
theorem residueFieldMap_isPurelyInseparable_of_universallyInjective (x : X) :
    (f.residueFieldMap x).hom.IsPurelyInseparable := by
  have h : Function.Injective f ∧ ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable :=
    ((tfae_universallyInjective f).out 0 2).mp (inferInstance : UniversallyInjective f)
  exact h.2 x

/-- Scheme-point injection and genuine inseparable powers give injection of the entire native valued-point map. -/
theorem map_injective_of_universallyInjective : Function.Injective (map f) := by
  rintro ⟨x, v⟩ ⟨y, w⟩ h
  have hxy : x = y := f.injective (congrArg point h)
  subst y
  have hv : v.comap (f.residueFieldMap x).hom = w.comap (f.residueFieldMap x).hom := by
    simpa only [map, SchemeValuedPoint.mk.injEq, heq_eq_eq, true_and] using h
  have he := EnvelopeProperty.Valuation.comap_injective_of_isPurelyInseparable
    (f.residueFieldMap x).hom (residueFieldMap_isPurelyInseparable_of_universallyInjective f x) hv
  subst w
  rfl

/-- An actual integral, scheme-surjective, universally injective morphism is a native homeomorphism. -/
theorem isHomeomorph_map_of_integral_surjective_universallyInjective [IsIntegralHom f]
    (hf : Function.Surjective f) : IsHomeomorph (map f) :=
  isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨continuous_map f, isClosedMap_map_of_isIntegralHom f,
      map_injective_of_universallyInjective f, map_surjective_of_isIntegralHom f hf⟩

/-- The genuine native homeomorphism is built from actual algebraic universal-homeomorphism conditions. -/
def universalHomeomorph [IsIntegralHom f] (hf : Function.Surjective f) :
    SchemeValuedPoint X ≃ₜ SchemeValuedPoint Y :=
  (isHomeomorph_map_of_integral_surjective_universallyInjective f hf).homeomorph (map f)

/-- The true homeomorphism retains the original whole native point map. -/
@[simp]
theorem universalHomeomorph_apply [IsIntegralHom f] (hf : Function.Surjective f)
    (y : SchemeValuedPoint X) : universalHomeomorph f hf y = map f y := rfl

end EnvelopeProperty.Berkovich.SchemeValuedPoint
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}
variable (g : X ⟶ Y) (hg : g ≫ fY = fX) [UniversallyInjective g]

/-- Actual universal injectivity gives injection on every common prescribed whole base locus. -/
theorem map_injective_of_universallyInjective : Function.Injective (map (v := v) g hg) := by
  intro x y h
  apply Subtype.ext
  exact SchemeValuedPoint.map_injective_of_universallyInjective g (congrArg Subtype.val h)

/-- Genuine universal-homeomorphism conditions give a native homeomorphism above any common prescribed base point. -/
theorem isHomeomorph_map_of_integral_surjective_universallyInjective [IsIntegralHom g]
    (hgs : Function.Surjective g) : IsHomeomorph (map (v := v) g hg) :=
  isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨continuous_map g hg, isClosedMap_map_of_isIntegralHom g hg,
      map_injective_of_universallyInjective g hg, map_surjective_of_isIntegralHom g hg hgs⟩

/-- The actual common-base native homeomorphism of an integral, scheme-surjective, universally injective morphism. -/
def universalHomeomorph [IsIntegralHom g] (hgs : Function.Surjective g) :
    RelativeSchemeValuedPoint v fX ≃ₜ RelativeSchemeValuedPoint v fY :=
  (isHomeomorph_map_of_integral_surjective_universallyInjective g hg hgs).homeomorph (map g hg)

/-- The prescribed-base homeomorphism is exactly the original whole relative native map. -/
@[simp]
theorem universalHomeomorph_apply [IsIntegralHom g] (hgs : Function.Surjective g)
    (y : RelativeSchemeValuedPoint v fX) : universalHomeomorph g hg hgs y = map g hg y := rfl

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
