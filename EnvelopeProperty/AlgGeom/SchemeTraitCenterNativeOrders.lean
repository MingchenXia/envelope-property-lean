import EnvelopeProperty.Algebra.LocalFractionOrderTransport
import EnvelopeProperty.AlgGeom.SchemeTraitCenterOriginalRing
import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-! # Every native scheme order at the actual original trait center is the SAME original DVR fraction order -/
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Order
open scoped WithZero
noncomputable section
universe u
namespace EnvelopeProperty.SchemeTraitCenterNativeOrders
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original whole generic restriction DERIVES the actual entire original stalk coefficient square. -/
theorem original_coefficient_square {V K : Type u} [CommRing V] [IsLocalRing V] [Field K]
    [Algebra V K] {Y : Scheme.{u}} [IsIntegral Y]
    (q : Spec (.of V) ⟶ Y)
    [IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ q)] :
    (algebraMap V K).comp (Scheme.stalkClosedPointTo q).hom =
      (SchemeGenericFieldGraph.fieldHom
        (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ q)).hom.comp
          (algebraMap (Y.presheaf.stalk (q (closedPoint V))) Y.functionField) := by
  let c := q (closedPoint V)
  let j : Y.presheaf.stalk c ⟶ Y.functionField :=
    CommRingCat.ofHom (algebraMap (Y.presheaf.stalk c) Y.functionField)
  have hj : Spec.map j ≫ Y.fromSpecStalk c = Y.fromSpecStalk (genericPoint Y) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Y).specializes trivial)
  have hq : Spec.map (Scheme.stalkClosedPointTo q) ≫ Y.fromSpecStalk c = q :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk q
  have h : Scheme.stalkClosedPointTo q ≫ CommRingCat.ofHom (algebraMap V K) =
      j ≫ SchemeGenericFieldGraph.fieldHom
        (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ q) := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk c)).mp
    rw [Spec.map_comp, Spec.map_comp]
    simp only [Category.assoc, hq, hj, SchemeGenericFieldGraph.fieldHom_fromSpecStalk]
  exact congrArg CommRingCat.Hom.hom h

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Algebra V X.functionField] [IsFractionRing V X.functionField]
  (q : Spec (.of V) ⟶ Y)
  [IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q)]
  (p : Y ⟶ X)
  (hgen : (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q) ≫ p =
    X.fromSpecStalk (genericPoint X))
  [ValuationRing (Y.presheaf.stalk (q (closedPoint V)))]

/-- The actual native center is the SAME original DVR, by its original canonical local map. -/
def stalkRingEquiv : Y.presheaf.stalk (q (closedPoint V)) ≃+* V :=
  RingEquiv.ofBijective (Scheme.stalkClosedPointTo q).hom
    (SchemeTraitCenterOriginalRing.stalkClosedPointTo_bijective q p hgen)

/-- Every value is that of the SAME actual canonical local map. -/
theorem stalkRingEquiv_apply (a : Y.presheaf.stalk (q (closedPoint V))) :
    stalkRingEquiv q p hgen a = (Scheme.stalkClosedPointTo q) a := rfl

include hgen in
/-- The actual original center is genuinely codimension one; no codimension certificate is supplied. -/
theorem center_coheight : coheight (q (closedPoint V)) = 1 := by
  have hd : ringKrullDim (Y.presheaf.stalk (q (closedPoint V))) = 1 :=
    (ringKrullDim_eq_of_ringEquiv (stalkRingEquiv q p hgen)).trans
      (IsDiscreteValuationRing.ringKrullDim_eq_one V)
  rw [ringKrullDim_stalk_eq_coheight] at hd
  exact WithBot.coe_injective hd

variable [IsLocallyNoetherian Y]

/-- EVERY actual original native rational function retains its ENTIRE original fraction order on the SAME original V. -/
theorem ordHom_eq_original (f : Y.functionField) :
    Y.ordHom (q (closedPoint V)) (center_coheight q p hgen) f =
      Ring.ordFrac V ((SchemeGenericFieldGraph.fieldHom
        (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q)) f) := by
  let : Ring.KrullDimLE 1 (Y.presheaf.stalk (q (closedPoint V))) :=
    krullDimLE_of_coheight_le (center_coheight q p hgen).le
  let φ := (SchemeGenericFieldGraph.fieldHom
    (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q)).hom
  have hc (a : Y.presheaf.stalk (q (closedPoint V))) :
      φ (algebraMap (Y.presheaf.stalk (q (closedPoint V))) Y.functionField a) =
        algebraMap V X.functionField (stalkRingEquiv q p hgen a) := by
    rw [stalkRingEquiv_apply]
    exact (RingHom.congr_fun (original_coefficient_square q) a).symm
  exact (LocalFractionOrderTransport.ordFrac_ringEquiv
    (stalkRingEquiv q p hgen) φ hc f).symm

include hgen in
/-- The original maximal-ideal valuation of EVERY native nonzero rational function is the true exponential of its negative native scheme order. -/
theorem valuation_eq_exp_neg_ord (f : Y.functionField) (hf : f ≠ 0) :
    (IsDiscreteValuationRing.maximalIdeal V).valuation X.functionField
      ((SchemeGenericFieldGraph.fieldHom
        (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q)) f) =
      WithZero.exp (-Y.ord f (q (closedPoint V))) := by
  have ho := (Y.ord_eq_iff (center_coheight q p hgen) hf).mp rfl
  rw [ordHom_eq_original q p hgen, Ring.ordFrac_eq_valuation_inv] at ho
  change _ = WithZero.exp (Y.ord f (q (closedPoint V))) at ho
  simpa only [inv_inv, WithZero.exp_neg] using congrArg Inv.inv ho

end EnvelopeProperty.SchemeTraitCenterNativeOrders
