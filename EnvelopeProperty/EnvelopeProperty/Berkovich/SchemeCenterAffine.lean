/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeProperCompact
import EnvelopeProperty.Berkovich.SchemeModelIdeals

/-!
# Genuine bounded affine criterion for proper centers

Actual section evaluation into the residue-field valuation ring constructs
a genuine affine valuative lift. Both whole scheme triangles and proper
uniqueness identify it with the true center lift. Consequently bounded
affine images equal actual center inverse images, preserving the distinction
between the original native kernel support and the proper model center.
-/


open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EnvelopeProperty.Berkovich.SchemeValuedPoint
variable {X : Scheme.{u}}

/-- The actual affine section evaluation gives the entire original native generic morphism. -/
theorem fromSpecResidueField_eq_affine {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    Spec.map (X.evaluation U x hx) ≫ hU.fromSpec = X.fromSpecResidueField x := by
  rw [Scheme.fromSpecResidueField, ← hU.fromSpecStalk_eq_fromSpecStalk hx, IsAffineOpen.fromSpecStalk,
    ← Spec.map_comp_assoc]
  rfl

/-- The actual affine chart's whole global-section pullback is genuine restriction. -/
theorem fromSpec_appTop_eq {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec.appTop = X.presheaf.map (homOfLE le_top).op ≫ (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appTop, hU.fromSpec_app_of_le ⊤ le_top]
  simp only [Scheme.Hom.preimage_top, homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The genuine section coefficient action presents the entire affine structure morphism. -/
theorem fromSpec_structureMap {R : Type u} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (sectionBaseMap f U)) := by
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (hU.fromSpec ≫ f).appTop =
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec.map (CommRingCat.ofHom (sectionBaseMap f U))).appTop
  rw [Scheme.Hom.comp_appTop, fromSpec_appTop_eq, ← Scheme.ΓSpecIso_inv_naturality]
  rfl
end EnvelopeProperty.Berkovich.SchemeValuedPoint

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- Actual bounded section evaluation takes every affine section into the genuine valuation ring. -/
def boundedAffineSectionMap (y : RelativeSchemeValuedPoint v f) (U : X.affineOpens)
    (hy : y.1.point ∈ U.1) (hbound : ∀ s : Γ(X, U), SchemeValuedPoint.eval y.1 U.1 hy s ≤ 1) :
    Γ(X, U) →+* CenterRing y :=
  (X.evaluation U.1 y.1.point hy).hom.codRestrict (CenterRing y).toSubring hbound

/-- The entire original coefficient map is preserved inside the genuine valuation ring. -/
theorem boundedAffineSectionMap_base (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (U : X.affineOpens) (hy : y.1.point ∈ U.1)
    (hbound : ∀ s : Γ(X, U), SchemeValuedPoint.eval y.1 U.1 hy s ≤ 1) :
    (boundedAffineSectionMap y U hy hbound).comp (SchemeValuedPoint.sectionBaseMap f U.1) =
      centerBaseMap hb y := by
  ext r
  change X.evaluation U.1 y.1.point hy (SchemeValuedPoint.sectionBaseMap f U.1 r) = residueBaseMap y r
  simp only [SchemeValuedPoint.sectionBaseMap_apply, residueBaseMap, RingHom.comp_apply,
    homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  exact congrArg (X.residue y.1.point)
    (X.presheaf.germ_res_apply (homOfLE (show U.1 ≤ ⊤ from le_top)) y.1.point hy
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)))

/-- The actual bounded affine section map constructs a whole valuation-ring lift into the affine neighborhood. -/
def boundedAffineLift (y : RelativeSchemeValuedPoint v f) (U : X.affineOpens)
    (hy : y.1.point ∈ U.1) (hbound : ∀ s : Γ(X, U), SchemeValuedPoint.eval y.1 U.1 hy s ≤ 1) :
    Spec (CommRingCat.of (CenterRing y)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (boundedAffineSectionMap y U hy hbound)) ≫ U.2.fromSpec

theorem boundedAffineLift_generic (y : RelativeSchemeValuedPoint v f) (U : X.affineOpens)
    (hy : y.1.point ∈ U.1) (hbound : ∀ s : Γ(X, U), SchemeValuedPoint.eval y.1 U.1 hy s ≤ 1) :
    Spec.map (CommRingCat.ofHom (algebraMap (CenterRing y) (X.residueField y.1.point))) ≫
      boundedAffineLift y U hy hbound = X.fromSpecResidueField y.1.point := by
  rw [boundedAffineLift, ← Spec.map_comp_assoc]
  exact SchemeValuedPoint.fromSpecResidueField_eq_affine U.2 y.1.point hy

theorem boundedAffineLift_base (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (U : X.affineOpens) (hy : y.1.point ∈ U.1)
    (hbound : ∀ s : Γ(X, U), SchemeValuedPoint.eval y.1 U.1 hy s ≤ 1) :
    boundedAffineLift y U hy hbound ≫ f = Spec.map (CommRingCat.ofHom (centerBaseMap hb y)) := by
  rw [boundedAffineLift, Category.assoc, SchemeValuedPoint.fromSpec_structureMap,
    ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (boundedAffineSectionMap_base hb y U hy hbound)

/-- Actual proper valuative uniqueness identifies the entire bounded affine lift with the true model lift. -/
theorem boundedAffineLift_eq_centerLift [IsProper f] (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (U : X.affineOpens) (hy : y.1.point ∈ U.1)
    (hbound : ∀ s : Γ(X, U), SchemeValuedPoint.eval y.1 U.1 hy s ≤ 1) :
    boundedAffineLift y U hy hbound = centerLift hb y :=
  centerLift_unique hb y _ (boundedAffineLift_generic y U hy hbound)
    (boundedAffineLift_base hb y U hy hbound)

/-- Boundedness on every genuine affine section forces the actual proper center into that affine open. -/
theorem center_mem_of_bounded_affine [IsProper f] (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (U : X.affineOpens) (hy : y.1.point ∈ U.1)
    (hbound : ∀ s : Γ(X, U), SchemeValuedPoint.eval y.1 U.1 hy s ≤ 1) : center hb y ∈ U.1 := by
  rw [center, ← boundedAffineLift_eq_centerLift hb y U hy hbound, boundedAffineLift, Scheme.Hom.comp_apply]
  exact U.2.range_fromSpec.le ⟨_, rfl⟩

/-- Every point of the genuine bounded affine image has its actual center in that affine open. -/
theorem center_mem_of_mem_boundedAffineImage [IsProper f] (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (U : X.affineOpens) (hy : y ∈ boundedAffineImage v f U) :
    center hb y ∈ U.1 := by
  let := SchemeValuedPoint.sectionBaseAlgebra f U.1
  change y ∈ (fun x : RelativeSpectrum v Γ(X, U) =>
    ((affineOpenSpectrumHomeomorph U.2).symm x : RelativeSchemeValuedPoint v f)) ''
      {x : RelativeSpectrum v Γ(X, U) | Spectrum.IsBounded x.1} at hy
  obtain ⟨x, hx, rfl⟩ := hy
  let z := (affineOpenSpectrumHomeomorph U.2).symm x
  apply center_mem_of_bounded_affine hb z.1 U z.2
  intro s
  have he := affineOpenSpectrumHomeomorph_val_apply U.2 z s
  change (affineOpenSpectrumHomeomorph U.2 ((affineOpenSpectrumHomeomorph U.2).symm x)).1.val s = _ at he
  rw [Homeomorph.apply_symm_apply] at he
  exact he ▸ hx s

/-- The genuine bounded affine image is exactly the true center-preimage, not the native support-preimage. -/
theorem mem_boundedAffineImage_iff_center_mem [IsProper f] (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (U : X.affineOpens) :
    y ∈ boundedAffineImage v f U ↔ center hb y ∈ U.1 :=
  ⟨center_mem_of_mem_boundedAffineImage hb y U, mem_boundedAffineImage_of_center_mem hb y U⟩

/-- The actual center inverse image of an affine open is the genuine compact bounded affine image. -/
theorem boundedAffineImage_eq_center_preimage [IsProper f] (hb : ∀ r, v r ≤ 1) (U : X.affineOpens) :
    boundedAffineImage v f U = (center hb) ⁻¹' (U.1 : Set X) := by
  ext y
  exact mem_boundedAffineImage_iff_center_mem hb y U
end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
