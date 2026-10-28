import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Genuine whole affine pushforward of the SAME original associated module sheaf -/
noncomputable section
namespace EnvelopeProperty.SpecPushforwardTilde
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

private def sectionsFirstIso :
    Scheme.Modules.pushforward (Spec.map f) ⋙ moduleSpecΓFunctor ≅
      (modulesSpecToSheaf ⋙
          TopCat.Sheaf.pushforward (ModuleCat S) (Spec.map f).base ⋙
            sheafCompose (Opens.grothendieckTopology (Spec R))
              (ModuleCat.restrictScalars f.hom)) ⋙
        TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
          (CategoryTheory.evaluation
            (TopologicalSpace.Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
            (op (⊤ : (Spec R).Opens)) := by
  let H := TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
    (CategoryTheory.evaluation
      (TopologicalSpace.Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
      (op (⊤ : (Spec R).Opens))
  exact (Functor.associator
      (Scheme.Modules.pushforward (Spec.map f)) modulesSpecToSheaf H).symm ≪≫
    Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso f) H

private theorem sectionsFirstIso_hom_apply (N : (Spec S).Modules)
    (x : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map f)).obj N)) :
    (sectionsFirstIso f).hom.app N x = x := rfl

/-- The actual whole global-section comparison retains EVERY SAME original section. -/
def sectionsIso (N : (Spec S).Modules) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map f)).obj N) ≅
      (ModuleCat.restrictScalars f.hom).obj (moduleSpecΓFunctor.obj N) := by
  have htop :
      (TopologicalSpace.Opens.map (Spec.map f).base).op.obj (op (⊤ : (Spec R).Opens)) =
        op (⊤ : (Spec S).Opens) := by simp
  exact (sectionsFirstIso f).app N ≪≫ (ModuleCat.restrictScalars f.hom).mapIso
    ((modulesSpecToSheaf.obj N).presheaf.mapIso (eqToIso htop))

/-- EVERY original section is unchanged by the actual native module comparison. -/
theorem sectionsIso_hom_apply (N : (Spec S).Modules)
    (x : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map f)).obj N)) :
    (sectionsIso f N).hom x = x := by
  change (modulesSpecToSheaf.obj N).presheaf.map
    (eqToHom (show (TopologicalSpace.Opens.map (Spec.map f).base).op.obj
      (op (⊤ : (Spec R).Opens)) = op (⊤ : (Spec S).Opens) by simp))
        ((sectionsFirstIso f).hom.app N x) = x
  rw [sectionsFirstIso_hom_apply]
  change (modulesSpecToSheaf.obj N).presheaf.map (𝟙 _) x = x
  exact congrArg (fun a : (modulesSpecToSheaf.obj N).presheaf.obj
      ((TopologicalSpace.Opens.map (Spec.map f).base).op.obj (op (⊤ : (Spec R).Opens))) ⟶
      (modulesSpecToSheaf.obj N).presheaf.obj
      ((TopologicalSpace.Opens.map (Spec.map f).base).op.obj (op (⊤ : (Spec R).Opens))) => a x)
    ((modulesSpecToSheaf.obj N).presheaf.map_id _)


/-- Genuine original affine pushforward of tilde M, with SAME native restricted coefficients. -/
def pushforwardTildeIso (M : ModuleCat S) :
    (Scheme.Modules.pushforward (Spec.map f)).obj (AlgebraicGeometry.tilde M) ≅
      AlgebraicGeometry.tilde ((ModuleCat.restrictScalars f.hom).obj M) := by
  let N := AlgebraicGeometry.tilde M
  let : IsIso N.fromTildeΓ := inferInstance
  let := isIso_fromTildeΓ_pushforward f N
  exact (asIso ((Scheme.Modules.pushforward (Spec.map f)).obj N).fromTildeΓ).symm ≪≫
    (tilde.functor R).mapIso (sectionsIso f N ≪≫
      (ModuleCat.restrictScalars f.hom).mapIso ((tilde.toTildeΓNatIso (R := S)).app M).symm)

end EnvelopeProperty.SpecPushforwardTilde
