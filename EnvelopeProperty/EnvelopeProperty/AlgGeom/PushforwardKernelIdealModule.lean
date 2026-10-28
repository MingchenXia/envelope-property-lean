import EnvelopeProperty.AlgGeom.QuasiCompactKernelIdeal
import EnvelopeProperty.AlgGeom.IdealModuleFunctorial
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # The SAME entire geometric pushed-unit kernel ideal module is the actual native kernel -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace EnvelopeProperty.PushforwardKernelIdealModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalLocallyMemKernel_iff {X : Scheme.{u}} {M : X.Modules}
    (α : Scheme.Modules.unitObj X ⟶ M) (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, I.ideal U = Scheme.Modules.unitMapKernelIdeal α U)
    (W : X.Opens) (a : Γ(X, W)) :
    I.IsLocallyMem W a ↔ α.val.app (.op W) a = 0 := by
  constructor
  · intro ha
    apply TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) W
    intro x hx
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hx
    have hmem := ha ⟨V, hV⟩ hVW
    rw [hI] at hmem
    change α.val.app (.op V) (X.presheaf.map (homOfLE hVW).op a) = 0 at hmem
    have hres : M.presheaf.map (homOfLE hVW).op (α.val.app (.op W) a) = 0 :=
      (PresheafOfModules.naturality_apply α.val (homOfLE hVW).op a).symm.trans hmem
    have hg : M.presheaf.germ V x hxV
        (M.presheaf.map (homOfLE hVW).op (α.val.app (.op W) a)) = 0 :=
      (congrArg (M.presheaf.germ V x hxV) hres).trans (map_zero _)
    have hr := TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hVW) x hxV
      (α.val.app (.op W) a)
    exact hr.symm.trans (hg.trans (map_zero _).symm)
  · intro ha U hU
    rw [hI]
    change α.val.app (.op U.1) (X.presheaf.map (homOfLE hU).op a) = 0
    exact (PresheafOfModules.naturality_apply α.val (homOfLE hU).op a).trans
      ((congrArg (M.presheaf.map (homOfLE hU).op) ha).trans (map_zero _))

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [QuasiCompact g]
    (N : Y.Modules) [N.IsQuasicoherent]
    (α : Scheme.Modules.unitObj X ⟶ (Scheme.Modules.pushforward g).obj N)

/-- On EVERY actual original open, membership in the SAME entire pushed
kernel ideal module is exactly vanishing under the SAME original morphism. -/
theorem isLocallyMem_iff (W : X.Opens) (a : Γ(X, W)) :
    (Scheme.Modules.unitMapPushforwardKernelIdealSheaf g N α).IsLocallyMem W a ↔
      α.val.app (.op W) a = 0 :=
  originalLocallyMemKernel_iff α _ (fun _ => rfl) W a

/-- The SAME entire geometric ideal inclusion is annihilated by the original map. -/
theorem inclusion_comp_zero :
    (Scheme.Modules.unitMapPushforwardKernelIdealSheaf g N α).toModulesInclusion ≫ α = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext s
  exact (isLocallyMem_iff g N α W.unop s.1).mp s.2

private def originalKernelToIdeal : kernel α ⟶
    (Scheme.Modules.unitMapPushforwardKernelIdealSheaf g N α).toModules where
  val :=
    { app W := ModuleCat.ofHom
        { toFun := fun s => ⟨(kernel.ι α).val.app W s, by
            apply (isLocallyMem_iff g N α W.unop _).mpr
            exact congrArg (fun q => q.val.app W s) (kernel.condition α)⟩
          map_add' := fun a b => Subtype.ext (map_add _ a b)
          map_smul' := fun a s => Subtype.ext (map_smul _ a s) }
      naturality := fun {U V} i => by
        apply ModuleCat.hom_ext
        ext s
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply (kernel.ι α).val i s }

private def originalIdealToKernel :
    (Scheme.Modules.unitMapPushforwardKernelIdealSheaf g N α).toModules ⟶ kernel α :=
  kernel.lift α
    (Scheme.Modules.unitMapPushforwardKernelIdealSheaf g N α).toModulesInclusion
    (inclusion_comp_zero g N α)

/-- The SAME entire original geometric ideal MODULE is the actual native
categorical kernel, without any whole pushforward-quasicoherence premise. -/
def toModulesKernelIso :
    (Scheme.Modules.unitMapPushforwardKernelIdealSheaf g N α).toModules ≅ kernel α where
  hom := originalIdealToKernel g N α
  inv := originalKernelToIdeal g N α
  hom_inv_id := by
    apply (cancel_mono (Scheme.Modules.unitMapPushforwardKernelIdealSheaf g N α).toModulesInclusion).mp
    change originalIdealToKernel g N α ≫ kernel.ι α = _
    exact kernel.lift_ι α
      (Scheme.Modules.unitMapPushforwardKernelIdealSheaf g N α).toModulesInclusion
      (inclusion_comp_zero g N α)
  inv_hom_id := by
    apply (cancel_mono (kernel.ι α)).mp
    rw [Category.assoc]
    rw [show originalIdealToKernel g N α ≫ kernel.ι α =
        (Scheme.Modules.unitMapPushforwardKernelIdealSheaf g N α).toModulesInclusion from
      kernel.lift_ι _ _ _]
    rfl

/-- The comparison retains the SAME ENTIRE original ideal inclusion exactly. -/
theorem toModulesKernelIso_hom_inclusion :
    (toModulesKernelIso g N α).hom ≫ kernel.ι α =
      (Scheme.Modules.unitMapPushforwardKernelIdealSheaf g N α).toModulesInclusion :=
  kernel.lift_ι _ _ _

end EnvelopeProperty.PushforwardKernelIdealModule
