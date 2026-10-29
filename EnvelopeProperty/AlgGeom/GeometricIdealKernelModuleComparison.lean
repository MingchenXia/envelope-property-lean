import EnvelopeProperty.AlgGeom.IdealModuleFunctorial
import EnvelopeProperty.AlgGeom.FiniteClosedIdealEuler

/-! # Whole comparison of the SAME geometric ideal module and native closed kernel -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.GeometricIdealKernelModuleComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The original whole geometric ideal inclusion vanishes under the SAME
original closed-subscheme structure quotient. -/
theorem inclusion_quotient_zero :
    I.toModulesInclusion ≫ FiniteClosedIdealEuler.quotientMap I.subschemeι = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext s
  exact (I.isLocallyMem_iff_subscheme_app_eq_zero W.unop s.1).mp s.2

private def kernelToGeometricIdeal : ModularCurves.idealModule I.subschemeι ⟶ I.toModules where
  val :=
    { app W := ModuleCat.ofHom
        { toFun := fun s =>
            ⟨(ModularCurves.idealModuleToUnit I.subschemeι).val.app W s, by
              apply (I.isLocallyMem_iff_subscheme_app_eq_zero W.unop _).mpr
              have h := congrArg (fun q => q.val.app W s)
                (kernel.condition (FiniteClosedIdealEuler.quotientMap I.subschemeι))
              exact h⟩
          map_add' := fun a b => Subtype.ext (map_add _ a b)
          map_smul' := fun r s => Subtype.ext (map_smul _ r s) }
      naturality := fun {U V} f => by
        apply ModuleCat.hom_ext
        ext s
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply
          (ModularCurves.idealModuleToUnit I.subschemeι).val f s }

private theorem kernelToGeometricIdeal_inclusion :
    kernelToGeometricIdeal I ≫ I.toModulesInclusion =
      ModularCurves.idealModuleToUnit I.subschemeι := by
  rfl

private def geometricIdealToKernel : I.toModules ⟶ ModularCurves.idealModule I.subschemeι :=
  kernel.lift (FiniteClosedIdealEuler.quotientMap I.subschemeι)
    (show I.toModules ⟶ unitObj X from I.toModulesInclusion) (inclusion_quotient_zero I)

private theorem geometricIdealToKernel_inclusion :
    geometricIdealToKernel I ≫ ModularCurves.idealModuleToUnit I.subschemeι =
      I.toModulesInclusion := kernel.lift_ι _ _ _

/-- The SAME whole original geometric ideal module is the actual native
kernel of its ORIGINAL closed immersion, with no ideal comparison premise. -/
def toModulesKernelIso : I.toModules ≅ ModularCurves.idealModule I.subschemeι where
  hom := geometricIdealToKernel I
  inv := kernelToGeometricIdeal I
  hom_inv_id := by
    apply (cancel_mono I.toModulesInclusion).mp
    rw [Category.assoc, kernelToGeometricIdeal_inclusion]
    simpa only [Category.id_comp] using geometricIdealToKernel_inclusion I
  inv_hom_id := by
    have : Mono (ModularCurves.idealModuleToUnit I.subschemeι) := by
      change Mono (kernel.ι (FiniteClosedIdealEuler.quotientMap I.subschemeι))
      infer_instance
    apply (cancel_mono (ModularCurves.idealModuleToUnit I.subschemeι)).mp
    rw [Category.assoc, geometricIdealToKernel_inclusion, kernelToGeometricIdeal_inclusion]
    simp

/-- The whole original geometric inclusion is retained EXACTLY. -/
theorem toModulesKernelIso_hom_inclusion :
    (toModulesKernelIso I).hom ≫ ModularCurves.idealModuleToUnit I.subschemeι =
      I.toModulesInclusion := geometricIdealToKernel_inclusion I

end EnvelopeProperty.GeometricIdealKernelModuleComparison
