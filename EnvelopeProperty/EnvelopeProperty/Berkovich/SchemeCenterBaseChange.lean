/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeRelativeBaseChange
import EnvelopeProperty.Berkovich.SchemeCenter


/-!
# Genuine proper centers under coefficient change

For compatible real seminorms on R and S and explicitly bounded coefficients
in both rings, a commuting scheme morphism from a proper S-model to a proper
R-model preserves actual valuative lifts and centers. The genuine residue
field embedding restricts to a local valuation-ring map. Actual coefficient
equality forms the common target valuative square, and separated target
uniqueness compares the whole lifts. Source properness is only required over
S. No properness of the intervening morphism, Noetherianity, completeness or
anti-continuity hypothesis is assumed; native support and center stay distinct.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite

universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {R S : Type u} [CommRing R] [CommRing S]
variable {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}
variable (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r)
variable {X Y : Scheme.{u}}
variable {fX : X ⟶ Spec (CommRingCat.of S)} {fY : Y ⟶ Spec (CommRingCat.of R)}

/-- Actual residue-field pullback restricts to the true valuation rings of commuting native points. -/
def centerRingMap_overBase (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ)) (y : RelativeSchemeValuedPoint w fX) :
    CenterRing (mapOverBase φ hφ g hg y) →+* CenterRing y :=
  ((g.residueFieldMap y.1.point).hom.comp (CenterRing (mapOverBase φ hφ g hg y)).toSubring.subtype).codRestrict
    (CenterRing y).toSubring (fun a => a.2)

/-- The actual field embedding preserves every valuation-ring element's original value. -/
@[simp]
theorem centerRingMap_val_overBase (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ)) (y : RelativeSchemeValuedPoint w fX)
    (a : CenterRing (mapOverBase φ hφ g hg y)) :
    y.1.residueVal (centerRingMap_overBase φ hφ g hg y a : X.residueField y.1.point) =
      (mapOverBase φ hφ g hg y).1.residueVal (a : Y.residueField (mapOverBase φ hφ g hg y).1.point) := rfl

/-- Genuine field pullback contracts the valuation-ring maximal ideal exactly. -/
theorem centerRingMap_maximalIdeal_comap_overBase (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (y : RelativeSchemeValuedPoint w fX) :
    (IsLocalRing.maximalIdeal (CenterRing y)).comap (centerRingMap_overBase φ hφ g hg y) =
      IsLocalRing.maximalIdeal (CenterRing (mapOverBase φ hφ g hg y)) := by
  ext a
  rw [Ideal.mem_comap, Valuation.mem_maximalIdeal_iff, Valuation.mem_maximalIdeal_iff]
  rfl

/-- The valuation-ring pullback is an actual local ring map. -/
theorem isLocalHom_centerRingMap_overBase (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (y : RelativeSchemeValuedPoint w fX) : IsLocalHom (centerRingMap_overBase φ hφ g hg y) :=
  ((IsLocalRing.local_hom_TFAE _).out 4 0).mp (centerRingMap_maximalIdeal_comap_overBase φ hφ g hg y)

/-- The actual generic inclusions and the residue-field embedding commute on every element. -/
theorem centerRingMap_fraction_overBase (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (y : RelativeSchemeValuedPoint w fX) :
    Spec.map (CommRingCat.ofHom (algebraMap (CenterRing y) (X.residueField y.1.point))) ≫
      Spec.map (CommRingCat.ofHom (centerRingMap_overBase φ hφ g hg y)) =
        Spec.map (g.residueFieldMap y.1.point) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (CenterRing (mapOverBase φ hφ g hg y))
            (Y.residueField (mapOverBase φ hφ g hg y).1.point))) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- Actual structure-map coefficients commute with the genuine residue-field embedding. -/
theorem residueBaseMap_naturality_overBase (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (y : RelativeSchemeValuedPoint w fX) (r : R) :
    g.residueFieldMap y.1.point (residueBaseMap (mapOverBase φ hφ g hg y) r) = residueBaseMap y (φ r) := by
  have hcomp : fY.appTop ≫ g.appTop =
      (Spec.map (CommRingCat.ofHom φ)).appTop ≫ fX.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hg]
  simp only [residueBaseMap, RingHom.comp_apply, SchemeValuedPoint.sectionBaseMap_apply,
    homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  change g.residueFieldMap y.1.point
    (Y.Γevaluation (g y.1.point) (fY.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))) =
      X.Γevaluation y.1.point (fX.appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv (φ r)))
  rw [Scheme.Γevaluation_naturality_apply]
  have he := congrArg (fun a => a ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) hcomp
  change g.appTop (fY.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
    fX.appTop ((Spec.map (CommRingCat.ofHom φ)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) at he
  rw [he]
  have hi := congrArg (fun a => a r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  change (Scheme.ΓSpecIso (CommRingCat.of S)).inv (φ r) =
    (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) at hi
  rw [← hi]

/-- Bounded genuine base maps agree inside the valuation rings, not only in their norm values. -/
theorem centerRingMap_base_overBase (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ)) (hbR : ∀ r, v r ≤ 1) (hbS : ∀ s, w s ≤ 1)
    (y : RelativeSchemeValuedPoint w fX) (r : R) :
    centerRingMap_overBase φ hφ g hg y (centerBaseMap hbR (mapOverBase φ hφ g hg y) r) = centerBaseMap hbS y (φ r) := by
  apply Subtype.ext
  exact residueBaseMap_naturality_overBase φ hφ g hg y r

/-- Whole proper valuative lifts commute across the actual compatible coefficient diagram. -/
theorem centerLift_naturality_overBase [IsProper fX] [IsProper fY] (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (hbR : ∀ r, v r ≤ 1) (hbS : ∀ s, w s ≤ 1) (y : RelativeSchemeValuedPoint w fX) :
    centerLift hbS y ≫ g =
      Spec.map (CommRingCat.ofHom (centerRingMap_overBase φ hφ g hg y)) ≫ centerLift hbR (mapOverBase φ hφ g hg y) := by
  let S : ValuativeCommSq fY :=
    { R := CenterRing y
      K := X.residueField y.1.point
      i₁ := X.fromSpecResidueField y.1.point ≫ g
      i₂ := Spec.map (CommRingCat.ofHom ((centerBaseMap hbS y).comp φ))
      commSq := ⟨by rw [Category.assoc, hg, ← Category.assoc, center_commSq hbS y,
        Category.assoc, ← Spec.map_comp]; rfl⟩ }
  let : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion fY S
  let l₁ : S.commSq.LiftStruct :=
    { l := centerLift hbS y ≫ g
      fac_left := by
        change _ ≫ (centerLift hbS y ≫ g) = _
        rw [← Category.assoc, centerLift_generic]
      fac_right := by
        change (centerLift hbS y ≫ g) ≫ fY = _
        rw [Category.assoc, hg, ← Category.assoc, centerLift_base, ← Spec.map_comp]
        rfl }
  let l₂ : S.commSq.LiftStruct :=
    { l := Spec.map (CommRingCat.ofHom (centerRingMap_overBase φ hφ g hg y)) ≫ centerLift hbR (mapOverBase φ hφ g hg y)
      fac_left := by
        change _ ≫ (Spec.map (CommRingCat.ofHom (centerRingMap_overBase φ hφ g hg y)) ≫ _) = _
        rw [← Category.assoc, centerRingMap_fraction_overBase, Category.assoc, centerLift_generic]
        exact g.SpecMap_residueFieldMap_fromSpecResidueField y.1.point
      fac_right := by
        change (Spec.map (CommRingCat.ofHom (centerRingMap_overBase φ hφ g hg y)) ≫ _) ≫ fY = _
        rw [Category.assoc, centerLift_base, ← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        exact RingHom.ext (centerRingMap_base_overBase φ hφ g hg hbR hbS y) }
  exact congrArg (fun z : S.commSq.LiftStruct => z.l) (Subsingleton.elim l₁ l₂)

/-- The actual valuation-ring map takes the genuine closed point to the genuine closed point. -/
theorem centerRingMap_closedPoint_overBase (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (y : RelativeSchemeValuedPoint w fX) :
    Spec.map (CommRingCat.ofHom (centerRingMap_overBase φ hφ g hg y)) (IsLocalRing.closedPoint (CenterRing y)) =
      IsLocalRing.closedPoint (CenterRing (mapOverBase φ hφ g hg y)) := by
  let : IsLocalHom (centerRingMap_overBase φ hφ g hg y) := isLocalHom_centerRingMap_overBase φ hφ g hg y
  exact IsLocalRing.comap_closedPoint _

/-- Actual proper centers are preserved by commuting morphisms over compatible bounded bases. -/
@[simp]
theorem center_map_overBase [IsProper fX] [IsProper fY] (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (hbR : ∀ r, v r ≤ 1) (hbS : ∀ s, w s ≤ 1) (y : RelativeSchemeValuedPoint w fX) :
    g (center hbS y) = center hbR (mapOverBase φ hφ g hg y) := by
  have h := congrArg (fun q : Spec (CommRingCat.of (CenterRing y)) ⟶ Y =>
    q (IsLocalRing.closedPoint (CenterRing y))) (centerLift_naturality_overBase φ hφ g hg hbR hbS y)
  simpa only [center, Scheme.Hom.comp_apply, centerRingMap_closedPoint_overBase] using h

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
