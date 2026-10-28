import EnvelopeProperty.Berkovich.SchemeLineSectionEvaluation
import ModularCurves.Picard.DualPullback.UnitSquare

/-!
# Whole section pullback agrees with actual open restriction

The genuine restriction/pullback unit identity and actual whole naturality
are used before any section evaluation. No invertibility is required.
Route: owned `open-section-pullback-coherence-route.tex`.
-/
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGlobalSections
open Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual unit-normalized section pullback is its literal whole open restriction after the genuine comparison. -/
theorem pullbackSectionHom_comp_restrictComparison {Y Z : Scheme.{u}}
    (f : Z ⟶ Y) [IsOpenImmersion f] {L : Y.Modules} (α : unitObj Y ⟶ L) :
    SchemeLineSectionEvaluation.pullbackSectionHom f α ≫
        (restrictFunctorIsoPullback f).inv.app L =
      (restrictUnitIso f).inv ≫ (restrictFunctor f).map α := by
  let t := (restrictFunctorIsoPullback f).app (unitObj Y)
  let u := pullbackUnitIso f
  let r := restrictUnitIso f
  have ht : t.inv ≫ r.hom = u.hom :=
    ModularCurves.restrictFunctorIsoPullback_inv_comp_restrictUnitIsoLow f
  have hi : u.inv ≫ t.inv = r.inv := by
    apply (cancel_mono r.hom).mp
    calc
      (u.inv ≫ t.inv) ≫ r.hom = u.inv ≫ (t.inv ≫ r.hom) := Category.assoc _ _ _
      _ = u.inv ≫ u.hom := congrArg (fun a => u.inv ≫ a) ht
      _ = r.inv ≫ r.hom := u.inv_hom_id.trans r.inv_hom_id.symm
  have hn := (restrictFunctorIsoPullback f).inv.naturality α
  change (pullback f).map α ≫ (restrictFunctorIsoPullback f).inv.app L =
    t.inv ≫ (restrictFunctor f).map α at hn
  change (u.inv ≫ (pullback f).map α) ≫ (restrictFunctorIsoPullback f).inv.app L = _
  calc
    (u.inv ≫ (pullback f).map α) ≫ (restrictFunctorIsoPullback f).inv.app L =
        u.inv ≫ ((pullback f).map α ≫ (restrictFunctorIsoPullback f).inv.app L) := Category.assoc _ _ _
    _ = u.inv ≫ (t.inv ≫ (restrictFunctor f).map α) :=
      congrArg (fun a => u.inv ≫ a) hn
    _ = (u.inv ≫ t.inv) ≫ (restrictFunctor f).map α := (Category.assoc _ _ _).symm
    _ = r.inv ≫ (restrictFunctor f).map α :=
      congrArg (fun a => a ≫ (restrictFunctor f).map α) hi

end EnvelopeProperty.ClosedProjectiveGlobalSections

#check @EnvelopeProperty.ClosedProjectiveGlobalSections.pullbackSectionHom_comp_restrictComparison
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.pullbackSectionHom_comp_restrictComparison
