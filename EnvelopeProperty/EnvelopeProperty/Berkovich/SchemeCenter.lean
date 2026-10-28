/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeRelativeValuedPoints
import EnvelopeProperty.Berkovich.SpectrumIdeals
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Actual valuative centers on proper schemes over bounded prescribed coefficients

A native point's actual residue-field valuation subring and bounded coefficient
map form a genuine valuative square. Properness produces an actual unique
scheme lift. Its closed-point image is the model center; the kernel support
specializes to it. Actual lift pullback evaluates all center-neighborhood
sections in the valuation ring, and the true center-stalk valuation is bounded
and detects its maximal ideal by values strictly smaller than one.

All prescribed coefficient values must be at most one. No field base,
triviality, completeness, Noetherian hypothesis or finite affine cover is
required. The ordinary native kernel support and the valuative center have
different definitions. No anti-continuity or analytic structure-sheaf claim
is supplied.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite

universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace EnvelopeProperty.Berkovich.SchemeValuedPoint

variable {X : Scheme.{u}}

/-- The genuine residue-field morphism preserves all actual global sections. -/
theorem fromSpecResidueField_appTop (x : X) :
    (X.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso (X.residueField x)).hom =
      X.Γevaluation x := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop,
    Category.assoc, Scheme.ΓSpecIso_naturality]
  rw [Scheme.fromSpecStalk_appTop]
  simp only [homOfLE_refl, op_id]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.comp_id, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- Every actual support neighborhood pulls back to the whole spectrum of its local stalk. -/
theorem fromSpecStalk_preimage_eq_top (x : X) (U : X.Opens) (hx : x ∈ U) :
    X.fromSpecStalk x ⁻¹ᵁ U = ⊤ :=
  Scheme.preimage_eq_top_of_closedPoint_mem _ (by simpa using hx)

/-- Pullback to all sections of the local stalk is the genuine germ map. -/
theorem fromSpecStalk_appLE_top (x : X) (U : X.Opens) (hx : x ∈ U)
    (h : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U) :
    (X.fromSpecStalk x).appLE U ⊤ h =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  rw [Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp]
  have hi : (homOfLE le_top).op ≫ (homOfLE h).op = 𝟙 (op (⊤ : (Spec (X.presheaf.stalk x)).Opens)) :=
    Subsingleton.elim _ _
  rw [hi, CategoryTheory.Functor.map_id, Category.comp_id]

/-- Every actual support neighborhood pulls back to the whole spectrum of its residue field. -/
theorem fromSpecResidueField_preimage_eq_top (x : X) (U : X.Opens) (hx : x ∈ U) :
    X.fromSpecResidueField x ⁻¹ᵁ U = ⊤ :=
  Scheme.preimage_eq_top_of_closedPoint_mem _ (by simpa using hx)

/-- Actual residue-field pullback evaluates every local section through the original residue map. -/
theorem fromSpecResidueField_appLE_top (x : X) (U : X.Opens) (hx : x ∈ U)
    (h : ⊤ ≤ X.fromSpecResidueField x ⁻¹ᵁ U) :
    (X.fromSpecResidueField x).appLE U ⊤ h ≫ (Scheme.ΓSpecIso (X.residueField x)).hom =
      X.evaluation U x hx := by
  have hSt : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by rw [fromSpecStalk_preimage_eq_top x U hx]
  have hRes : ⊤ ≤ Spec.map (X.residue x) ⁻¹ᵁ (⊤ : (Spec (X.presheaf.stalk x)).Opens) := le_top
  have he := Scheme.Hom.appLE_comp_appLE (Spec.map (X.residue x)) (X.fromSpecStalk x) U ⊤ ⊤ hSt hRes
  change (Spec.map (X.residue x) ≫ X.fromSpecStalk x).appLE U ⊤ h ≫ _ = _
  rw [← he, fromSpecStalk_appLE_top x U hx, Category.assoc]
  have ht : (Spec.map (X.residue x)).appLE ⊤ ⊤ hRes = (Spec.map (X.residue x)).appTop := by
    simp [Scheme.Hom.appLE]
  rw [ht, Scheme.ΓSpecIso_naturality]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

end EnvelopeProperty.Berkovich.SchemeValuedPoint

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- The actual coefficient residue map at a native point, derived from its genuine structure morphism. -/
def residueBaseMap (y : RelativeSchemeValuedPoint v f) : R →+* X.residueField y.1.point :=
  (X.Γevaluation y.1.point).hom.comp (SchemeValuedPoint.sectionBaseMap f ⊤)

@[simp]
theorem residueBaseMap_val (y : RelativeSchemeValuedPoint v f) (r : R) :
    y.1.residueVal (residueBaseMap y r) = v r := eval_sectionBaseMap y ⊤ trivial r

/-- The actual valuation subring of the native residue field; this concerns a model center rather than the kernel support. -/
abbrev CenterRing (y : RelativeSchemeValuedPoint v f) := y.1.residueVal.valuationSubring

/-- Bounded prescribed coefficients genuinely land in the native residue-field valuation ring. -/
def centerBaseMap (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) : R →+* CenterRing y :=
  (residueBaseMap y).codRestrict (CenterRing y).toSubring (fun r => by
    change y.1.residueVal (residueBaseMap y r) ≤ 1
    rw [residueBaseMap_val]
    exact hb r)

@[simp]
theorem centerBaseMap_coe (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) (r : R) :
    (centerBaseMap hb y r : X.residueField y.1.point) = residueBaseMap y r := rfl

/-- The top generic residue point and the bounded coefficient morphism form the actual whole valuative square. -/
theorem center_commSq (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    X.fromSpecResidueField y.1.point ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap (CenterRing y) (X.residueField y.1.point))) ≫
        Spec.map (CommRingCat.ofHom (centerBaseMap hb y)) := by
  rw [← Spec.map_comp]
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (X.fromSpecResidueField y.1.point ≫ f).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom (centerBaseMap hb y) ≫
          CommRingCat.ofHom (algebraMap (CenterRing y) (X.residueField y.1.point)))).appTop
  rw [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality]
  apply (cancel_mono (Scheme.ΓSpecIso (X.residueField y.1.point)).hom).mp
  simp only [Category.assoc, SchemeValuedPoint.fromSpecResidueField_appTop]
  have hi : (Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).inv ≫
      (Scheme.ΓSpecIso (X.residueField y.1.point)).hom = 𝟙 _ :=
    (Scheme.ΓSpecIso (X.residueField y.1.point)).inv_hom_id
  rw [hi, Category.comp_id]
  apply CommRingCat.hom_ext
  ext r
  change X.Γevaluation y.1.point (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
    algebraMap (CenterRing y) (X.residueField y.1.point) (centerBaseMap hb y r)
  change X.Γevaluation y.1.point (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
    residueBaseMap y r
  simp only [residueBaseMap, RingHom.comp_apply, SchemeValuedPoint.sectionBaseMap_apply,
    homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The whole actual valuative square formed from a bounded native prescribed-base point. -/
def centerSquare (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) : ValuativeCommSq f where
  R := CenterRing y
  K := X.residueField y.1.point
  i₁ := X.fromSpecResidueField y.1.point
  i₂ := Spec.map (CommRingCat.ofHom (centerBaseMap hb y))
  commSq := ⟨center_commSq hb y⟩

/-- Genuine properness produces the actual valuative lift, with both whole scheme triangles. -/
def centerLiftStruct [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    (centerSquare hb y).commSq.LiftStruct := by
  have h : IsProper f := inferInstance
  rw [IsProper.eq_valuativeCriterion] at h
  exact (Classical.choice (h.1.1.1 (centerSquare hb y))).default

/-- The actual morphism from the residue-field valuation ring to the proper scheme. -/
def centerLift [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    Spec (CommRingCat.of (CenterRing y)) ⟶ X := (centerLiftStruct hb y).l

@[reassoc]
theorem centerLift_generic [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    Spec.map (CommRingCat.ofHom (algebraMap (CenterRing y) (X.residueField y.1.point))) ≫
      centerLift hb y = X.fromSpecResidueField y.1.point :=
  (centerLiftStruct hb y).fac_left

@[reassoc]
theorem centerLift_base [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    centerLift hb y ≫ f = Spec.map (CommRingCat.ofHom (centerBaseMap hb y)) :=
  (centerLiftStruct hb y).fac_right

/-- Separatedness of the actual proper structure map makes its whole valuative lift unique. -/
theorem centerLift_unique [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (g : Spec (CommRingCat.of (CenterRing y)) ⟶ X)
    (hgeneric : Spec.map (CommRingCat.ofHom
      (algebraMap (CenterRing y) (X.residueField y.1.point))) ≫ g = X.fromSpecResidueField y.1.point)
    (hbase : g ≫ f = Spec.map (CommRingCat.ofHom (centerBaseMap hb y))) : g = centerLift hb y := by
  let : Subsingleton (centerSquare hb y).commSq.LiftStruct :=
    IsSeparated.valuativeCriterion f (centerSquare hb y)
  exact congrArg (fun z => z.l) (Subsingleton.elim
    (⟨g, hgeneric, hbase⟩ : (centerSquare hb y).commSq.LiftStruct) (centerLiftStruct hb y))

/-- The model center is the image of the actual closed point of the residue-field valuation ring. -/
def center [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) : X :=
  centerLift hb y (IsLocalRing.closedPoint (CenterRing y))

/-- The original native kernel support is a generization of its actual model center. -/
theorem support_specializes_center [IsProper f] (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) : y.1.point ⤳ center hb y := by
  have hgeneric : centerLift hb y
      (Spec.map (CommRingCat.ofHom (algebraMap (CenterRing y) (X.residueField y.1.point)))
        (IsLocalRing.closedPoint (X.residueField y.1.point))) = y.1.point := by
    rw [← Scheme.Hom.comp_apply, centerLift_generic]
    exact Scheme.fromSpecResidueField_apply y.1.point _
  rw [← hgeneric]
  exact (IsLocalRing.specializes_closedPoint _).map (centerLift hb y).continuous

/-- Every open neighborhood of the true center also contains the original native support. -/
theorem support_mem_of_center_mem [IsProper f] (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (U : X.Opens) (hc : center hb y ∈ U) : y.1.point ∈ U :=
  (support_specializes_center hb y).mem_open U.2 hc

/-- Every center neighborhood has a genuine section pullback to the actual residue-field valuation ring. -/
def centerSectionMap [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (U : X.Opens) (hc : center hb y ∈ U) : Γ(X, U) →+* CenterRing y :=
  ((centerLift hb y).appLE U ⊤ (by
    rw [Scheme.preimage_eq_top_of_closedPoint_mem (centerLift hb y) hc]) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (CenterRing y))).hom).hom

/-- The actual ring-valued center pullback evaluates to the original native residue-field value. -/
theorem centerSectionMap_coe [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (U : X.Opens) (hc : center hb y ∈ U) (s : Γ(X, U)) :
    (centerSectionMap hb y U hc s : X.residueField y.1.point) =
      X.evaluation U y.1.point (support_mem_of_center_mem hb y U hc) s := by
  let i := Spec.map (CommRingCat.ofHom (algebraMap (CenterRing y) (X.residueField y.1.point)))
  have hV : ⊤ ≤ centerLift hb y ⁻¹ᵁ U := by
    rw [Scheme.preimage_eq_top_of_closedPoint_mem (centerLift hb y) hc]
  have hK : ⊤ ≤ i ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of (CenterRing y))).Opens) := le_top
  have he := Scheme.Hom.appLE_comp_appLE i (centerLift hb y) U ⊤ ⊤ hV hK
  have ht : i.appLE ⊤ ⊤ hK = i.appTop := by simp [Scheme.Hom.appLE]
  have hfun : ∀ h : ⊤ ≤ (i ≫ centerLift hb y) ⁻¹ᵁ U,
      (i ≫ centerLift hb y).appLE U ⊤ h ≫
        (Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom =
      X.evaluation U y.1.point (support_mem_of_center_mem hb y U hc) := by
    dsimp only [i]
    rw [centerLift_generic]
    intro h
    exact SchemeValuedPoint.fromSpecResidueField_appLE_top _ _ _ _
  have hcomp :
      (centerLift hb y).appLE U ⊤ hV ≫
        (Scheme.ΓSpecIso (CommRingCat.of (CenterRing y))).hom ≫
          CommRingCat.ofHom (algebraMap (CenterRing y) (X.residueField y.1.point)) =
      X.evaluation U y.1.point (support_mem_of_center_mem hb y U hc) := by
    rw [← Scheme.ΓSpecIso_naturality, ← ht, ← Category.assoc, he]
    exact hfun _
  exact congrArg (fun g : Γ(X, U) ⟶ X.residueField y.1.point => g s) hcomp

/-- Every genuine local section near the actual model center has native value at most one. -/
theorem eval_le_one_of_center_mem [IsProper f] (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (U : X.Opens) (hc : center hb y ∈ U) (s : Γ(X, U)) :
    SchemeValuedPoint.eval y.1 U (support_mem_of_center_mem hb y U hc) s ≤ 1 := by
  rw [SchemeValuedPoint.eval, ← centerSectionMap_coe hb y U hc s]
  exact (centerSectionMap hb y U hc s).2

/-- The true local section spectrum is bounded on every actual center neighborhood. -/
theorem isBounded_sectionSpectrum_of_center_mem [IsProper f] (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (U : X.Opens) (hc : center hb y ∈ U) :
    Spectrum.IsBounded (sectionSpectrum y U (support_mem_of_center_mem hb y U hc)).1 := by
  intro s
  exact eval_le_one_of_center_mem hb y U hc s

/-- The genuine local scheme map from the center stalk into the actual valuation ring. -/
def centerStalkMap [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    X.presheaf.stalk (center hb y) →+* CenterRing y :=
  (Scheme.stalkClosedPointTo (centerLift hb y)).hom

/-- The actual center-stalk seminorm induced by the original native residue-field valuation. -/
def centerStalkVal [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    Valuation (X.presheaf.stalk (center hb y)) ℝ≥0 :=
  y.1.residueVal.comap ((CenterRing y).toSubring.subtype.comp (centerStalkMap hb y))

/-- Every actual model-stalk value is bounded by one, from its genuine valuation-ring image. -/
theorem centerStalkVal_le_one [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (a : X.presheaf.stalk (center hb y)) : centerStalkVal hb y a ≤ 1 :=
  (centerStalkMap hb y a).2

/-- Strictly smaller than one is the genuine maximal-ideal condition at the model center. -/
theorem centerStalkVal_lt_one_iff [IsProper f] (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (a : X.presheaf.stalk (center hb y)) :
    centerStalkVal hb y a < 1 ↔ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (center hb y)) := by
  let : IsLocalHom (centerStalkMap hb y) :=
    inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo (centerLift hb y)).hom)
  change y.1.residueVal (centerStalkMap hb y a) < 1 ↔ _
  rw [← Valuation.mem_maximalIdeal_iff]
  change a ∈ (IsLocalRing.maximalIdeal (CenterRing y)).comap (centerStalkMap hb y) ↔ _
  rw [IsLocalRing.maximalIdeal_comap]

/-- Germs of actual center-neighborhood sections have their genuine pulled-back valuation-ring values. -/
theorem centerStalkMap_germ [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (U : X.Opens) (hc : center hb y ∈ U) (s : Γ(X, U)) :
    centerStalkMap hb y (X.presheaf.germ U (center hb y) hc s) = centerSectionMap hb y U hc s := by
  have h := Scheme.germ_stalkClosedPointTo (centerLift hb y) U hc
  simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
    eqToIso.hom, Iso.op_hom] at h
  exact congrArg (fun g : Γ(X, U) ⟶ CommRingCat.of (CenterRing y) => g s) h

/-- The model-stalk germ seminorm agrees with every original native section value near its center. -/
theorem centerStalkVal_germ [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (U : X.Opens) (hc : center hb y ∈ U) (s : Γ(X, U)) :
    centerStalkVal hb y (X.presheaf.germ U (center hb y) hc s) =
      SchemeValuedPoint.eval y.1 U (support_mem_of_center_mem hb y U hc) s := by
  change y.1.residueVal (centerStalkMap hb y (X.presheaf.germ U (center hb y) hc s)) = _
  rw [centerStalkMap_germ]
  exact congrArg y.1.residueVal (centerSectionMap_coe hb y U hc s)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
