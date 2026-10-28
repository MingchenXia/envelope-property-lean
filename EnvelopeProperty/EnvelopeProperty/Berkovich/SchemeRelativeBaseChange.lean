/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeRelativeValuedPoints


/-!
# Native valued point maps across coefficient rings

Compatible prescribed real seminorms and an actual commuting structure
morphism diagram give a true continuous native point map between the fixed
base loci. The proof compares whole native affine base points using the
actual Spec seminorm homeomorphism. Arbitrary commutative rings are allowed;
no coefficient bound, properness or scalar-extension point existence is used.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite
universe u
noncomputable section
namespace EnvelopeProperty.Berkovich
namespace SchemeValuedPoint

/-- A compatible coefficient map sends the entire prescribed native point to the original prescribed point. -/
theorem map_basePoint {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}
    (hφ : ∀ r, w (φ r) = v r) :
    map (Spec.map (CommRingCat.ofHom φ)) (basePoint w) = basePoint v := by
  apply (spectrumHomeomorph (A := R)).injective
  rw [spectrumHomeomorph_map, basePoint, Homeomorph.apply_symm_apply,
    basePoint, Homeomorph.apply_symm_apply]
  exact Spectrum.ext_val hφ

end SchemeValuedPoint
namespace RelativeSchemeValuedPoint
variable {R S : Type u} [CommRing R] [CommRing S]
variable {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}
variable {X Y : Scheme.{u}}
variable {fX : X ⟶ Spec (CommRingCat.of S)} {fY : Y ⟶ Spec (CommRingCat.of R)}

/-- A genuine diagram over compatible coefficient rings preserves the entire prescribed native base points. -/
def mapOverBase (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r)
    (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (y : RelativeSchemeValuedPoint w fX) : RelativeSchemeValuedPoint v fY :=
  ⟨SchemeValuedPoint.map g y.1, by
    change SchemeValuedPoint.map fY (SchemeValuedPoint.map g y.1) = SchemeValuedPoint.basePoint v
    rw [← SchemeValuedPoint.map_comp, hg, SchemeValuedPoint.map_comp, y.2,
      SchemeValuedPoint.map_basePoint φ hφ]⟩

@[simp]
theorem mapOverBase_coe (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r)
    (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (y : RelativeSchemeValuedPoint w fX) :
    (mapOverBase φ hφ g hg y : SchemeValuedPoint Y) = SchemeValuedPoint.map g y.1 := rfl

@[fun_prop]
theorem continuous_mapOverBase (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r)
    (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ)) :
    Continuous (mapOverBase φ hφ g hg) :=
  ((SchemeValuedPoint.continuous_map g).comp continuous_subtype_val).subtype_mk _

/-- Identity coefficient change is the original commuting native relative point map. -/
theorem mapOverBase_id {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}
    (g : X ⟶ Y) (hg : g ≫ fY = fX) (y : RelativeSchemeValuedPoint v fX) :
    mapOverBase (RingHom.id R) (fun _ => rfl) g (by simpa using hg) y = map g hg y :=
  Subtype.ext rfl

end RelativeSchemeValuedPoint
end EnvelopeProperty.Berkovich
