import EnvelopeProperty.AlgGeom.SchemeGenericFieldGraph
import Mathlib.RingTheory.Valuation.LocalSubring

/-! # The SAME actual original ring at a native birational valuation center -/
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeTraitCenterOriginalRing

/-- The actual native local map at a birational valuation center is the
WHOLE original ring; the unchanged generic triangle derives the comparison. -/
theorem stalkClosedPointTo_bijective
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {V : Type u} [CommRing V] [IsDomain V] [IsLocalRing V]
    [Algebra V X.functionField] [IsFractionRing V X.functionField]
    (q : Spec (.of V) ⟶ Y)
    [IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q)]
    (p : Y ⟶ X)
    (hgen : (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q) ≫ p =
      X.fromSpecStalk (genericPoint X))
    [ValuationRing (Y.presheaf.stalk (q (closedPoint V)))] :
    Function.Bijective (Scheme.stalkClosedPointTo q).hom := by
  let c := q (closedPoint V)
  let R := Y.presheaf.stalk c
  let g := Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q
  let e := SchemeGenericFieldGraph.functionFieldEquiv g p hgen
  let ρ := (Scheme.stalkClosedPointTo q).hom
  let j : R ⟶ Y.functionField := CommRingCat.ofHom (algebraMap R Y.functionField)
  have hj : Spec.map j ≫ Y.fromSpecStalk c = Y.fromSpecStalk (genericPoint Y) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Y).specializes trivial)
  have hq : Spec.map (Scheme.stalkClosedPointTo q) ≫ Y.fromSpecStalk c = q :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk q
  have hcoeff : Scheme.stalkClosedPointTo q ≫ CommRingCat.ofHom (algebraMap V X.functionField) =
      j ≫ SchemeGenericFieldGraph.fieldHom g := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk c)).mp
    rw [Spec.map_comp,Spec.map_comp]
    simp only [Category.assoc,hq,hj,
      SchemeGenericFieldGraph.fieldHom_fromSpecStalk]
    rfl
  let γ := e.symm.toRingHom.comp (algebraMap V X.functionField)
  have hγ : γ.comp ρ = algebraMap R Y.functionField := by
    ext a
    apply e.injective
    change e (e.symm (algebraMap V X.functionField (ρ a))) = e (algebraMap R Y.functionField a)
    rw [e.apply_symm_apply]
    exact congrArg (fun f : R ⟶ CommRingCat.of X.functionField => f a) hcoeff
  have hγinj : Function.Injective γ := e.symm.injective.comp (IsFractionRing.injective V X.functionField)
  have H := bijective_rangeRestrict_comp_of_valuationRing ρ γ hγ
  refine ⟨Function.Injective.of_comp (f := γ) ?_,?_⟩
  · rw [← RingHom.coe_comp,hγ]
    exact IsFractionRing.injective R Y.functionField
  · intro a
    obtain ⟨r,hr⟩ := H.2 (γ.rangeRestrict a)
    exact ⟨r,hγinj (congrArg Subtype.val hr)⟩

end EnvelopeProperty.SchemeTraitCenterOriginalRing
