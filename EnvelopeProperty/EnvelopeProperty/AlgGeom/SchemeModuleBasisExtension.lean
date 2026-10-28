import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Actual original module morphisms extend from true original basis data -/
noncomputable section
namespace EnvelopeProperty.SchemeModuleBasisExtension
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} {ι : Type u} (B : ι → X.Opens)
variable (hB : Opens.IsBasis (Set.range B)) (M N : X.Modules)
variable (α : (inducedFunctor B).op ⋙ M.presheaf ⟶ (inducedFunctor B).op ⋙ N.presheaf)

/-- True native basis extension into SAME original additive sheaf. -/
def additiveExtension : M.presheaf ⟶ N.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom M.presheaf
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) hB α

/-- EVERY original basis component is the SAME original map. -/
theorem additiveExtension_app (i : ι) :
    (additiveExtension B hB M N α).app (op (B i)) = α.app (op i) :=
  TopCat.Sheaf.extend_hom_app M.presheaf
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) hB α i

variable (hα : ∀ (i : ι) (r : Γ(X, B i)) (x : Γ(M, B i)),
  α.app (op i) (r • x) = r • (show Γ(N, B i) from α.app (op i) x))

include hα in
/-- SAME whole original module linearity is DERIVED from genuine basis components. -/
theorem additiveExtension_smul (U : X.Opensᵒᵖ) (r : X.ringCatSheaf.obj.obj U)
    (x : M.val.obj U) :
    (additiveExtension B hB M N α).app U (r • x) =
      r • (show N.val.obj U from (additiveExtension B hB M N α).app U x) := by
  apply TopCat.Presheaf.IsSheaf.section_ext (Scheme.Modules.isSheaf N)
  intro z hz
  obtain ⟨V, ⟨i, rfl⟩, hzi, hi⟩ := Opens.isBasis_iff_nbhd.mp hB hz
  refine ⟨B i, hi, hzi, ?_⟩
  let j : B i ⟶ U.unop := homOfLE hi
  have h1 := ConcreteCategory.congr_hom
    ((additiveExtension B hB M N α).naturality j.op) (r • x)
  have h2 := ConcreteCategory.congr_hom
    ((additiveExtension B hB M N α).naturality j.op) x
  change (additiveExtension B hB M N α).app (op (B i)) (M.presheaf.map j.op (r • x)) =
    N.presheaf.map j.op ((additiveExtension B hB M N α).app U (r • x)) at h1
  change (additiveExtension B hB M N α).app (op (B i)) (M.presheaf.map j.op x) =
    N.presheaf.map j.op ((additiveExtension B hB M N α).app U x) at h2
  have hb := additiveExtension_app B hB M N α i
  change N.presheaf.map j.op ((additiveExtension B hB M N α).app U (r • x)) =
    N.presheaf.map j.op (r • (show N.val.obj U from (additiveExtension B hB M N α).app U x))
  have hn := Scheme.Modules.map_smul N j r
    (show Γ(N, U.unop) from (additiveExtension B hB M N α).app U x)
  have hm := Scheme.Modules.map_smul M j r x
  have hl (s : Γ(X, B i)) (y : Γ(M, B i)) :
      (additiveExtension B hB M N α).app (op (B i)) (s • y) =
        s • (show Γ(N, B i) from (additiveExtension B hB M N α).app (op (B i)) y) :=
    (ConcreteCategory.congr_hom hb (s • y)).trans
      ((hα i s y).trans
        (congrArg (fun z : Γ(N, B i) => s • z) (ConcreteCategory.congr_hom hb y)).symm)
  exact h1.symm.trans
    ((congrArg ((additiveExtension B hB M N α).app (op (B i))) hm).trans
      ((hl _ _).trans ((congrArg
        (fun y : Γ(N, B i) => X.presheaf.map j.op r • y) h2).trans hn.symm)))

/-- Actual ENTIRE original module-sheaf map, no supplied whole linearity/gluing certificate. -/
def extension : M ⟶ N :=
  ⟨PresheafOfModules.homMk (additiveExtension B hB M N α)
    (additiveExtension_smul B hB M N α hα)⟩

/-- EVERY original section on EVERY genuine basis open has its exact original image. -/
theorem extension_app (i : ι) (x : Γ(M, B i)) :
    (extension B hB M N α hα).val.app (op (B i)) x = α.app (op i) x :=
  ConcreteCategory.congr_hom (additiveExtension_app B hB M N α i) x

include hB in
/-- Actual whole original module morphisms are determined by EVERY original basis section. -/
theorem hom_ext {φ ψ : M ⟶ N}
    (h : ∀ (i : ι) (x : Γ(M, B i)), φ.val.app (op (B i)) x = ψ.val.app (op (B i)) x) :
    φ = ψ := by
  apply (Scheme.Modules.toPresheaf X).map_injective
  apply TopCat.Sheaf.hom_ext M.presheaf ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) hB
  intro i
  apply AddCommGrpCat.hom_ext
  ext x
  exact h i x

end EnvelopeProperty.SchemeModuleBasisExtension
