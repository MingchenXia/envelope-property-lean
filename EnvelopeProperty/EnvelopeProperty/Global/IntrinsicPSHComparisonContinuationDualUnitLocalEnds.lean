import ModularCurves.Picard.DualPullback.Iso

/-!
# Actual source and target unit laws of the canonical local module comparison

Both genuine ends of the actual local comparison are proved before its
whole pullback-square assembly. No unit matching datum is input.
Route: owned `dual-unit-local-ends-route.tex`.
-/
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.OriginalDualPullbackCoherence
open Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The actual target restriction/over-site comparisons preserve the actual global pullback unit. -/
theorem localComparisonTarget_unit (U : X.Opens) :
    (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).inv.app ((pullback f).obj (unitObj X)) ≫
        (overFunctorEquiv (f ⁻¹ᵁ U)).inv.app ((pullback f).obj (unitObj X)) ≫
        (overEquiv (f ⁻¹ᵁ U)).functor.map ((pullbackUnitIso f).hom.over (f ⁻¹ᵁ U)) =
      (pullback (f ⁻¹ᵁ U).ι).map (pullbackUnitIso f).hom ≫
        (pullbackUnitIso (f ⁻¹ᵁ U).ι).hom := by
  let V := f ⁻¹ᵁ U
  let q := (pullbackUnitIso f).hom
  have heV : (overFunctorEquiv V).inv.app (unitObj Y) = (restrictUnitIso V.ι).hom :=
    congrArg Iso.inv (overFunctorEquiv_unitP V)
  have hov := (overFunctorEquiv V).inv.naturality q
  change (restrictFunctor V.ι).map q ≫ (overFunctorEquiv V).inv.app (unitObj Y) =
    (overFunctorEquiv V).inv.app ((pullback f).obj (unitObj X)) ≫
      (overEquiv V).functor.map (q.over V) at hov
  have hr := (restrictFunctorIsoPullback V.ι).inv.naturality q
  change (pullback V.ι).map q ≫ (restrictFunctorIsoPullback V.ι).inv.app (unitObj Y) =
    (restrictFunctorIsoPullback V.ι).inv.app ((pullback f).obj (unitObj X)) ≫
      (restrictFunctor V.ι).map q at hr
  change (restrictFunctorIsoPullback V.ι).inv.app ((pullback f).obj (unitObj X)) ≫
      (overFunctorEquiv V).inv.app ((pullback f).obj (unitObj X)) ≫
      (overEquiv V).functor.map (q.over V) = _
  rw [← hov, heV, ← Category.assoc, ← hr, Category.assoc,
    ModularCurves.restrictFunctorIsoPullback_inv_comp_restrictUnitIsoLow]

/-- The actual source over-site/restriction comparisons cancel against the actual open pullback unit. -/
theorem localComparisonSource_unit (U : X.Opens) :
    (pullback (f ∣_ U)).map ((overFunctorEquiv U).hom.app (unitObj X)) ≫
        (pullback (f ∣_ U)).map ((restrictFunctorIsoPullback U.ι).hom.app (unitObj X)) ≫
        (pullback (f ∣_ U)).map (pullbackUnitIso U.ι).hom =
      𝟙 ((pullback (f ∣_ U)).obj ((overEquiv U).functor.obj ((unitObj X).over U))) := by
  have heU : (overFunctorEquiv U).hom.app (unitObj X) = (restrictUnitIso U.ι).inv :=
    congrArg Iso.hom (overFunctorEquiv_unitP U)
  rw [← Functor.map_comp, ← Functor.map_comp]
  simp only [restrictFunctorIsoPullback_hom_comp_pullbackUnitIsoG, heU, Iso.inv_hom_id]
  exact (pullback (f ∣_ U)).map_id _

end EnvelopeProperty.OriginalDualPullbackCoherence

#check @EnvelopeProperty.OriginalDualPullbackCoherence.localComparisonTarget_unit
#print axioms EnvelopeProperty.OriginalDualPullbackCoherence.localComparisonTarget_unit
#check @EnvelopeProperty.OriginalDualPullbackCoherence.localComparisonSource_unit
#print axioms EnvelopeProperty.OriginalDualPullbackCoherence.localComparisonSource_unit
