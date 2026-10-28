import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Category.ModuleCat.Descent

/-! # Every actual native cycle class under genuine flat scalar extension -/
noncomputable section
namespace EnvelopeProperty.FlatModuleHomologyCycleClasses
open CategoryTheory Limits
open scoped ChangeOfRings
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
variable (f : A →+* B) (hf : f.Flat) (S : ShortComplex (ModuleCat A))

/-- The SAME native scalar-extension homology comparison; exactness comes from actual flatness. -/
def homologyIso : (S.map (ModuleCat.extendScalars f)).homology ≅
    (ModuleCat.extendScalars f).obj S.homology := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact S.mapHomologyIso (ModuleCat.extendScalars f)

/-- The SAME native scalar-extension cycle comparison, with actual flatness-derived preservation. -/
def cyclesIso : (S.map (ModuleCat.extendScalars f)).cycles ≅
    (ModuleCat.extendScalars f).obj S.cycles := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact S.mapCyclesIso (ModuleCat.extendScalars f)

/-- The ENTIRE original native homology projection commutes with the SAME actual comparisons. -/
theorem homologyπ_comparison :
    (S.map (ModuleCat.extendScalars f)).homologyπ ≫ (homologyIso f hf S).hom =
      (cyclesIso f hf S).hom ≫ (ModuleCat.extendScalars f).map S.homologyπ := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let F := ModuleCat.extendScalars f
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

/-- EVERY actual pure tensor of EVERY original cycle retains its SAME original coefficient
and native class under actual flat homology base change. -/
theorem cycleClass_tmul
    (z : LinearMap.ker (S.map (ModuleCat.extendScalars f)).g.hom)
    (b : B) (w : LinearMap.ker S.g.hom) (hzw : z.val = b ⊗ₜ[A,f] w.val) :
    (homologyIso f hf S).hom
      ((S.map (ModuleCat.extendScalars f)).homologyπ
        ((S.map (ModuleCat.extendScalars f)).moduleCatCyclesIso.inv z)) =
      b ⊗ₜ[A,f] (S.homologyπ (S.moduleCatCyclesIso.inv w)) := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let F := ModuleCat.extendScalars f
  have hc : (cyclesIso f hf S).hom ((S.map F).moduleCatCyclesIso.inv z) =
      b ⊗ₜ[A,f] (S.moduleCatCyclesIso.inv w) := by
    apply (ModuleCat.mono_iff_injective (F.map S.iCycles)).mp inferInstance
    have h := congrArg (fun t : (S.map F).cycles ⟶ F.obj S.X₂ =>
      t ((S.map F).moduleCatCyclesIso.inv z)) (S.mapCyclesIso_hom_iCycles F)
    change F.map S.iCycles ((cyclesIso f hf S).hom ((S.map F).moduleCatCyclesIso.inv z)) =
      (S.map F).iCycles ((S.map F).moduleCatCyclesIso.inv z) at h
    exact h.trans (((S.map F).moduleCatCyclesIso_inv_iCycles_apply z).trans
      (hzw.trans ((congrArg (fun a : S.X₂ => b ⊗ₜ[A,f] a)
        (S.moduleCatCyclesIso_inv_iCycles_apply w).symm).trans
          (ModuleCat.ExtendScalars.map_tmul f S.iCycles b (S.moduleCatCyclesIso.inv w)).symm)))
  have h := congrArg (fun t : (S.map F).cycles ⟶ F.obj S.homology =>
    t ((S.map F).moduleCatCyclesIso.inv z)) (homologyπ_comparison f hf S)
  change (homologyIso f hf S).hom
    ((S.map F).homologyπ ((S.map F).moduleCatCyclesIso.inv z)) =
      F.map S.homologyπ ((cyclesIso f hf S).hom ((S.map F).moduleCatCyclesIso.inv z)) at h
  exact h.trans ((congrArg (F.map S.homologyπ) hc).trans
    (ModuleCat.ExtendScalars.map_tmul f S.homologyπ b (S.moduleCatCyclesIso.inv w)))

end EnvelopeProperty.FlatModuleHomologyCycleClasses
