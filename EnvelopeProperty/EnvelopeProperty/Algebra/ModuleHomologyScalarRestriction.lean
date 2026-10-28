import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Actual native homology and every original cycle class under scalar restriction -/
noncomputable section
namespace EnvelopeProperty.ModuleHomologyScalarRestriction
open CategoryTheory
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
variable (f : A →+* B) (S : ShortComplex (ModuleCat B))

/-- Genuine native scalar restriction preserves the WHOLE actual native homology. -/
def homologyIso : (S.map (ModuleCat.restrictScalars f)).homology ≅
    (ModuleCat.restrictScalars f).obj S.homology :=
  S.mapHomologyIso (ModuleCat.restrictScalars f)

/-- The ENTIRE native homology projection commutes with the actual preservation comparison. -/
theorem homologyπ_comparison :
    (S.map (ModuleCat.restrictScalars f)).homologyπ ≫ (homologyIso f S).hom =
      (S.mapCyclesIso (ModuleCat.restrictScalars f)).hom ≫
        (ModuleCat.restrictScalars f).map S.homologyπ := by
  let F := ModuleCat.restrictScalars f
  let h := S.moduleCatLeftHomologyData
  change (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
    (S.mapCyclesIso F).hom ≫ F.map S.homologyπ
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  change (S.map F).homologyπ ≫ (h.map F).homologyIso.hom ≫ F.map h.homologyIso.inv =
    (h.map F).cyclesIso.hom ≫ F.map h.cyclesIso.inv ≫ F.map S.homologyπ
  have hπ := congrArg (fun k : (S.map F).cycles ⟶ F.obj h.H =>
    k ≫ F.map h.homologyIso.inv) (h.map F).homologyπ_comp_homologyIso_hom
  have hf : F.map h.π ≫ F.map h.homologyIso.inv =
      F.map h.cyclesIso.inv ≫ F.map S.homologyπ :=
    (F.map_comp h.π h.homologyIso.inv).symm.trans
      ((congrArg F.map h.π_comp_homologyIso_inv.symm).trans
        (F.map_comp h.cyclesIso.inv S.homologyπ))
  exact (Category.assoc _ _ _).symm.trans
    (hπ.trans ((Category.assoc _ _ _).trans
      (congrArg (fun k : F.obj h.K ⟶ F.obj S.homology => (h.map F).cyclesIso.hom ≫ k) hf)))

/-- EVERY actual original cycle class retains its SAME original form under genuine native
scalar restriction, without a quotient or cycle comparison certificate. -/
theorem cycleClass_comparison
    (z : LinearMap.ker (S.map (ModuleCat.restrictScalars f)).g.hom)
    (w : LinearMap.ker S.g.hom) (hzw : z.val = w.val) :
    (homologyIso f S).hom
      ((S.map (ModuleCat.restrictScalars f)).homologyπ
        ((S.map (ModuleCat.restrictScalars f)).moduleCatCyclesIso.inv z)) =
      S.homologyπ (S.moduleCatCyclesIso.inv w) := by
  let F := ModuleCat.restrictScalars f
  have hc : (S.mapCyclesIso F).hom ((S.map F).moduleCatCyclesIso.inv z) =
      S.moduleCatCyclesIso.inv w := by
    apply (ModuleCat.mono_iff_injective (F.map S.iCycles)).mp inferInstance
    have h := congrArg (fun t : (S.map F).cycles ⟶ F.obj S.X₂ =>
      t ((S.map F).moduleCatCyclesIso.inv z)) (S.mapCyclesIso_hom_iCycles F)
    change S.iCycles ((S.mapCyclesIso F).hom ((S.map F).moduleCatCyclesIso.inv z)) =
      (S.map F).iCycles ((S.map F).moduleCatCyclesIso.inv z) at h
    exact h.trans (((S.map F).moduleCatCyclesIso_inv_iCycles_apply z).trans
      (hzw.trans (S.moduleCatCyclesIso_inv_iCycles_apply w).symm))
  have h := congrArg (fun t : (S.map F).cycles ⟶ F.obj S.homology =>
    t ((S.map F).moduleCatCyclesIso.inv z)) (homologyπ_comparison f S)
  change (homologyIso f S).hom
    ((S.map F).homologyπ ((S.map F).moduleCatCyclesIso.inv z)) =
      S.homologyπ ((S.mapCyclesIso F).hom ((S.map F).moduleCatCyclesIso.inv z)) at h
  exact h.trans (congrArg S.homologyπ hc)

end EnvelopeProperty.ModuleHomologyScalarRestriction
