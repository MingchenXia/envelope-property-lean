import EnvelopeProperty.AlgGeom.IdealModuleFunctorial
import ModularCurves.EllipticCurve.PoleSheaf

/-! # The whole geometric kernel ideal is the actual native module kernel -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.MorphismKernelIdealModuleComparison
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f]

/-- For the genuine geometric kernel of an actual quasi-compact morphism,
whole local ideal membership is exactly zero under the SAME section map. -/
theorem isLocallyMem_iff_app_eq_zero (W : X.Opens) (s : Γ(X, W)) :
    f.ker.IsLocallyMem W s ↔ (f.app W).hom s = 0 := by
  constructor
  · exact Scheme.IdealSheafData.ker_isLocallyMem_app_eq_zero f W s
  · intro hs V hVW
    rw [Scheme.Hom.ker_apply]
    change (f.app V).hom (X.presheaf.map (homOfLE hVW).op s) = 0
    rw [← ConcreteCategory.comp_apply,f.naturality,ConcreteCategory.comp_apply,hs,map_zero]

/-- The whole original geometric kernel inclusion vanishes under the SAME
original whole morphism section map. -/
theorem inclusion_quotient_zero :
    f.ker.toModulesInclusion ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext s
  exact (isLocallyMem_iff_app_eq_zero f W.unop s.1).mp s.2

private def kernelToGeometricIdeal : ModularCurves.idealModule f ⟶ f.ker.toModules where
  val :=
    { app W := ModuleCat.ofHom
        { toFun := fun s =>
            ⟨(ModularCurves.idealModuleToUnit f).val.app W s, by
              apply (isLocallyMem_iff_app_eq_zero f W.unop _).mpr
              have h := congrArg (fun q => q.val.app W s)
                (kernel.condition (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
              exact h⟩
          map_add' := fun a b => Subtype.ext (map_add _ a b)
          map_smul' := fun r s => Subtype.ext (map_smul _ r s) }
      naturality := fun {U V} g => by
        apply ModuleCat.hom_ext
        ext s
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply (ModularCurves.idealModuleToUnit f).val g s }

private theorem kernelToGeometricIdeal_inclusion :
    kernelToGeometricIdeal f ≫ f.ker.toModulesInclusion = ModularCurves.idealModuleToUnit f := rfl

private def geometricIdealToKernel : f.ker.toModules ⟶ ModularCurves.idealModule f :=
  kernel.lift (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
    (show f.ker.toModules ⟶ unitObj X from f.ker.toModulesInclusion) (inclusion_quotient_zero f)

private theorem geometricIdealToKernel_inclusion :
    geometricIdealToKernel f ≫ ModularCurves.idealModuleToUnit f = f.ker.toModulesInclusion :=
  kernel.lift_ι _ _ _

/-- The SAME whole geometric kernel ideal module is the actual native kernel
of the SAME whole original morphism. No closedness or Cartier premise is used. -/
def kernelIdealModuleIso : f.ker.toModules ≅ ModularCurves.idealModule f where
  hom := geometricIdealToKernel f
  inv := kernelToGeometricIdeal f
  hom_inv_id := by
    apply (cancel_mono f.ker.toModulesInclusion).mp
    rw [Category.assoc,kernelToGeometricIdeal_inclusion]
    simpa only [Category.id_comp] using geometricIdealToKernel_inclusion f
  inv_hom_id := by
    have : Mono (ModularCurves.idealModuleToUnit f) := by
      change Mono (kernel.ι (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
      infer_instance
    apply (cancel_mono (ModularCurves.idealModuleToUnit f)).mp
    rw [Category.assoc,geometricIdealToKernel_inclusion,kernelToGeometricIdeal_inclusion]
    simp

/-- The SAME original whole geometric inclusion is retained EXACTLY. -/
theorem kernelIdealModuleIso_hom_inclusion :
    (kernelIdealModuleIso f).hom ≫ ModularCurves.idealModuleToUnit f = f.ker.toModulesInclusion :=
  geometricIdealToKernel_inclusion f

end EnvelopeProperty.MorphismKernelIdealModuleComparison
