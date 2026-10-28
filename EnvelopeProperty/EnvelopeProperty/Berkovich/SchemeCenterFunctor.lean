/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeCenter

/-!
# Genuine functoriality of proper model centers

The actual native residue-field pullback restricts to a local valuation-ring
map and commutes with every genuine coefficient. Separated valuative
uniqueness identifies the entire proper lifts after a commuting model
morphism; evaluation at their actual closed points proves center naturality.
Both structure maps are proper over explicitly bounded prescribed
coefficients. No property of the intervening map beyond its commuting base
diagram, field base, Noetherian assumption or anti-continuity claim is used.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite

universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X Y : Scheme.{u}}
variable {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}

/-- Actual residue-field pullback restricts to the true valuation rings of commuting native points. -/
def centerRingMap (g : X ⟶ Y) (hg : g ≫ fY = fX) (y : RelativeSchemeValuedPoint v fX) :
    CenterRing (map g hg y) →+* CenterRing y :=
  ((g.residueFieldMap y.1.point).hom.comp (CenterRing (map g hg y)).toSubring.subtype).codRestrict
    (CenterRing y).toSubring (fun a => a.2)

/-- The actual field embedding preserves every valuation-ring element's original value. -/
@[simp]
theorem centerRingMap_val (g : X ⟶ Y) (hg : g ≫ fY = fX) (y : RelativeSchemeValuedPoint v fX)
    (a : CenterRing (map g hg y)) :
    y.1.residueVal (centerRingMap g hg y a : X.residueField y.1.point) =
      (map g hg y).1.residueVal (a : Y.residueField (map g hg y).1.point) := rfl

/-- Genuine field pullback contracts the valuation-ring maximal ideal exactly. -/
theorem centerRingMap_maximalIdeal_comap (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (y : RelativeSchemeValuedPoint v fX) :
    (IsLocalRing.maximalIdeal (CenterRing y)).comap (centerRingMap g hg y) =
      IsLocalRing.maximalIdeal (CenterRing (map g hg y)) := by
  ext a
  rw [Ideal.mem_comap, Valuation.mem_maximalIdeal_iff, Valuation.mem_maximalIdeal_iff]
  rfl

/-- The valuation-ring pullback is an actual local ring map. -/
theorem isLocalHom_centerRingMap (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (y : RelativeSchemeValuedPoint v fX) : IsLocalHom (centerRingMap g hg y) :=
  ((IsLocalRing.local_hom_TFAE _).out 4 0).mp (centerRingMap_maximalIdeal_comap g hg y)

/-- The actual generic inclusions and the residue-field embedding commute on every element. -/
theorem centerRingMap_fraction (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (y : RelativeSchemeValuedPoint v fX) :
    Spec.map (CommRingCat.ofHom (algebraMap (CenterRing y) (X.residueField y.1.point))) ≫
      Spec.map (CommRingCat.ofHom (centerRingMap g hg y)) =
        Spec.map (g.residueFieldMap y.1.point) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (CenterRing (map g hg y))
            (Y.residueField (map g hg y).1.point))) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- Actual structure-map coefficients commute with the genuine residue-field embedding. -/
theorem residueBaseMap_naturality (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (y : RelativeSchemeValuedPoint v fX) (r : R) :
    g.residueFieldMap y.1.point (residueBaseMap (map g hg y) r) = residueBaseMap y r := by
  have hcomp : fX.appTop = fY.appTop ≫ g.appTop := by
    rw [← Scheme.Hom.comp_appTop, hg]
  simp only [residueBaseMap, RingHom.comp_apply, SchemeValuedPoint.sectionBaseMap_apply,
    homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  change g.residueFieldMap y.1.point
    (Y.Γevaluation (g y.1.point) (fY.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))) =
      X.Γevaluation y.1.point (fX.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
  rw [Scheme.Γevaluation_naturality_apply, hcomp]
  rfl

/-- Bounded genuine base maps agree inside the valuation rings, not only in their norm values. -/
theorem centerRingMap_base (g : X ⟶ Y) (hg : g ≫ fY = fX) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v fX) (r : R) :
    centerRingMap g hg y (centerBaseMap hb (map g hg y) r) = centerBaseMap hb y r := by
  apply Subtype.ext
  exact residueBaseMap_naturality g hg y r

/-- Whole proper valuative lifts commute with every actual morphism between proper models over the base. -/
theorem centerLift_naturality [IsProper fX] [IsProper fY] (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v fX) :
    centerLift hb y ≫ g =
      Spec.map (CommRingCat.ofHom (centerRingMap g hg y)) ≫ centerLift hb (map g hg y) := by
  let S : ValuativeCommSq fY :=
    { R := CenterRing y
      K := X.residueField y.1.point
      i₁ := X.fromSpecResidueField y.1.point ≫ g
      i₂ := Spec.map (CommRingCat.ofHom (centerBaseMap hb y))
      commSq := ⟨by rw [Category.assoc, hg, center_commSq]⟩ }
  let : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion fY S
  let l₁ : S.commSq.LiftStruct :=
    { l := centerLift hb y ≫ g
      fac_left := by
        change _ ≫ (centerLift hb y ≫ g) = _
        rw [← Category.assoc, centerLift_generic]
      fac_right := by
        change (centerLift hb y ≫ g) ≫ fY = _
        rw [Category.assoc, hg, centerLift_base] }
  let l₂ : S.commSq.LiftStruct :=
    { l := Spec.map (CommRingCat.ofHom (centerRingMap g hg y)) ≫ centerLift hb (map g hg y)
      fac_left := by
        change _ ≫ (Spec.map (CommRingCat.ofHom (centerRingMap g hg y)) ≫ _) = _
        rw [← Category.assoc, centerRingMap_fraction, Category.assoc, centerLift_generic]
        exact g.SpecMap_residueFieldMap_fromSpecResidueField y.1.point
      fac_right := by
        change (Spec.map (CommRingCat.ofHom (centerRingMap g hg y)) ≫ _) ≫ fY = _
        rw [Category.assoc, centerLift_base, ← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        exact RingHom.ext (centerRingMap_base g hg hb y) }
  exact congrArg (fun z : S.commSq.LiftStruct => z.l) (Subsingleton.elim l₁ l₂)

/-- The actual valuation-ring map takes the genuine closed point to the genuine closed point. -/
theorem centerRingMap_closedPoint (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (y : RelativeSchemeValuedPoint v fX) :
    Spec.map (CommRingCat.ofHom (centerRingMap g hg y)) (IsLocalRing.closedPoint (CenterRing y)) =
      IsLocalRing.closedPoint (CenterRing (map g hg y)) := by
  let : IsLocalHom (centerRingMap g hg y) := isLocalHom_centerRingMap g hg y
  exact IsLocalRing.comap_closedPoint _

/-- Actual model centers are functorial for arbitrary commuting morphisms of proper models. -/
@[simp]
theorem center_map [IsProper fX] [IsProper fY] (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v fX) :
    g (center hb y) = center hb (map g hg y) := by
  have h := congrArg (fun q : Spec (CommRingCat.of (CenterRing y)) ⟶ Y =>
    q (IsLocalRing.closedPoint (CenterRing y))) (centerLift_naturality g hg hb y)
  simpa only [center, Scheme.Hom.comp_apply, centerRingMap_closedPoint] using h

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
