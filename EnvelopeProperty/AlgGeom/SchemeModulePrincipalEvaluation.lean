import EnvelopeProperty.AlgGeom.SchemeModulePrincipalDetection
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

/-! # Whole original global evaluation on an actual generated principal open -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModulePrincipalEvaluation
open Scheme.Modules

/-- Evaluation of EVERY actual original top section in the original module. -/
def evaluation {X : Scheme.{u}} (M : X.Modules) :
    SheafOfModules.free (R := X.ringCatSheaf) Γ(M, ⊤) ⟶ M :=
  M.freeHomEquiv.symm (fun s => ModularCurves.moduleSectionsOfTop M s)

/-- Each original section is its own free basis inclusion followed by the
SAME entire original global evaluation. -/
theorem sectionHom_evaluation {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) :
    SchemeModuleGlobalSections.sectionHom M s = SheafOfModules.ιFree s ≫ evaluation M := by
  exact (congrArg M.unitHomEquiv.symm
    (congrFun (M.freeHomEquiv.apply_symm_apply
      (fun s => ModularCurves.moduleSectionsOfTop M s)).symm s)).trans
        (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply (evaluation M) s)

private theorem basis_cokernel {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasCokernels C] {A B D : C} (a : A ⟶ B) (e : B ⟶ D) :
    (a ≫ e) ≫ cokernel.π e = 0 := by
  rw [Category.assoc, cokernel.condition, comp_zero]

private theorem sectionHom_eq_zero_iff {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) :
    SchemeModuleGlobalSections.sectionHom M s = 0 → s = 0 := by
  intro h
  have h1 := congrArg
    (fun e => e.val.app (op (⊤ : X.Opens)) (show Γ(X, ⊤) from 1)) h
  change (1 : Γ(X, ⊤)) • M.presheaf.map
    (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op s = 0 at h1
  simpa using h1

/-- The actual original cokernel projection kills the ENTIRE original H0. -/
theorem cokernelProjection_top_eq_zero {X : Scheme.{u}} (M : X.Modules) :
    (cokernel.π (evaluation M)).val.app (op ⊤) = 0 := by
  ext s
  apply sectionHom_eq_zero_iff
  have hc := SchemeModuleGlobalSections.sectionHom_comp s (cokernel.π (evaluation M))
  have hb := congrArg (fun f => f ≫ cokernel.π (evaluation M)) (sectionHom_evaluation M s)
  exact hc.symm.trans (hb.trans (basis_cokernel (SheafOfModules.ιFree s) (evaluation M)))

private theorem epi_map_of_cokernel_zero {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {A B : C} (e : A ⟶ B) [PreservesColimit (parallelPair e 0) F]
    (h : F.map (cokernel.π e) = 0) : Epi (F.map e) := by
  apply Abelian.epi_of_cokernel_π_eq_zero
  exact (PreservesCokernel.π_iso_hom F e).symm.trans
    ((congrArg (fun a => a ≫ (PreservesCokernel.iso F e).hom) h).trans zero_comp)

/-- GENUINE original generation on the principal open DERIVES epimorphic
restriction of the ENTIRE original global evaluation, without a matching family. -/
theorem restrict_evaluation_epi {X B : Scheme.{u}} (π : X ⟶ B)
    (M : X.Modules) [M.IsQuasicoherent] [CompactSpace X] [X.IsSeparated]
    (r : Γ(B, ⊤)) (G : (M.restrict (π ⁻¹ᵁ B.basicOpen r).ι).GeneratingSections) :
    Epi ((restrictFunctor (π ⁻¹ᵁ B.basicOpen r).ι).map (evaluation M)) := by
  let F := restrictFunctor (π ⁻¹ᵁ B.basicOpen r).ι
  let : PreservesColimitsOfSize.{u,u} F :=
    (restrictAdjunction (π ⁻¹ᵁ B.basicOpen r).ι).leftAdjoint_preservesColimits
  let : (cokernel (evaluation M)).IsQuasicoherent := isQuasicoherent_cokernel (evaluation M)
  have hz := SchemeModulePrincipalDetection.restrict_eq_zero_of_generatingSections
    π r (cokernel.π (evaluation M)) G (cokernelProjection_top_eq_zero M)
  exact epi_map_of_cokernel_zero F (evaluation M) hz

end EnvelopeProperty.SchemeModulePrincipalEvaluation
