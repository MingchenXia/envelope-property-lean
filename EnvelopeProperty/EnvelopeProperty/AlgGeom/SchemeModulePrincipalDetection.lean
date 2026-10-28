import EnvelopeProperty.AlgGeom.GeneratedLineBaseIdealUnit
import EnvelopeProperty.AlgGeom.SchemeModulePrincipalLocalization

/-! # Genuine principal-open generation detects original quasicoherent maps -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModulePrincipalDetection
open Scheme.Modules

private theorem triple_comp_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B D E : C} (a : A ⟶ B) (b : B ⟶ D) : a ≫ b ≫ (0 : D ⟶ E) = 0 := by
  rw [comp_zero, comp_zero]

private theorem sectionHom_zero {X : Scheme.{u}} (M : X.Modules) :
    SchemeModuleGlobalSections.sectionHom M 0 = 0 := by
  apply M.unitHomEquiv.injective
  change M.unitHomEquiv (M.unitHomEquiv.symm (ModularCurves.moduleSectionsOfTop M 0)) = _
  rw [Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro U
  change M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op 0 = 0
  exact map_zero _

/-- Genuine original global generators detect the entire original module map. -/
theorem hom_eq_zero_of_generatingSections {X : Scheme.{u}} {M N : X.Modules}
    (G : M.GeneratingSections) (q : M ⟶ N)
    (hq : q.val.app (op ⊤) = 0) : q = 0 := by
  apply G.epi.left_cancellation
  apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan G.I)
  intro i
  change (SheafOfModules.ιFree i ≫ G.π) ≫ q = _
  have hs := congrArg (fun a => a ≫ q)
    (GeneratedLineBaseIdealUnit.sectionHom_topSection G i)
  have hc := SchemeModuleGlobalSections.sectionHom_comp
    (GeneratedLineBaseIdealUnit.topSection G i) q
  have hz : q.val.app (op ⊤) (GeneratedLineBaseIdealUnit.topSection G i) = 0 := by
    rw [hq]
    rfl
  have hz' := congrArg (SchemeModuleGlobalSections.sectionHom N) hz
  exact hs.symm.trans (hc.trans (hz'.trans ((sectionHom_zero N).trans (triple_comp_zero (SheafOfModules.ιFree i) G.π).symm)))

/-- The actual whole principal-open map vanishes if its original global map does. -/
theorem principalApp_eq_zero_of_top {X B : Scheme.{u}} (π : X ⟶ B)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    [CompactSpace X] [X.IsSeparated] (r : Γ(B, ⊤)) (q : M ⟶ N)
    (hq : q.val.app (op ⊤) = 0) :
    q.val.app (op (π ⁻¹ᵁ B.basicOpen r)) = 0 := by
  let P := π ⁻¹ᵁ B.basicOpen r
  let f := ((baseModulePresheaf π M).map (homOfLE (le_top : P ≤ ⊤)).op).hom
  let g := ((baseModulePresheaf π N).map (homOfLE (le_top : P ≤ ⊤)).op).hom
  let a := ((baseModulePresheafFunctor π).map q).app (op P)
  let := SchemeModulePrincipalLocalization.restriction_isLocalizedModule π M r
  let := SchemeModulePrincipalLocalization.restriction_isLocalizedModule π N r
  have hz : a.hom = 0 := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers r) f g
    ext s
    have hn := PresheafOfModules.naturality_apply q.val
      (homOfLE (le_top : P ≤ ⊤)).op s
    change q.val.app (op P) (M.presheaf.map _ s) = 0
    have hs : q.val.app (op ⊤) s = 0 := by
      rw [hq]
      rfl
    exact hn.trans ((congrArg (fun t => N.presheaf.map
      (homOfLE (le_top : P ≤ ⊤)).op t) hs).trans (map_zero _))
  ext s
  exact LinearMap.congr_fun hz s

private theorem appZero_congr {X : Scheme.{u}} {M N : X.Modules} (q : M ⟶ N)
    {U V : X.Opens} (h : U = V) (hq : q.val.app (op U) = 0) :
    q.val.app (op V) = 0 := by
  subst V
  exact hq

/-- Genuine generation on the original principal open detects the actual
restricted map, using whole original sections and their genuine restriction. -/
theorem restrict_eq_zero_of_generatingSections {X B : Scheme.{u}} (π : X ⟶ B)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    [CompactSpace X] [X.IsSeparated] (r : Γ(B, ⊤)) (q : M ⟶ N)
    (G : (M.restrict (π ⁻¹ᵁ B.basicOpen r).ι).GeneratingSections)
    (hq : q.val.app (op ⊤) = 0) :
    (restrictFunctor (π ⁻¹ᵁ B.basicOpen r).ι).map q = 0 := by
  let P := π ⁻¹ᵁ B.basicOpen r
  apply hom_eq_zero_of_generatingSections G
  have hp := principalApp_eq_zero_of_top π r q hq
  have hh := appZero_congr q P.ι_image_top.symm hp
  ext s
  exact congrArg (fun z => z s) hh

end EnvelopeProperty.SchemeModulePrincipalDetection
