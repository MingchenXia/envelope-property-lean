import EnvelopeProperty.Local.PLOriginalModelCompatibilityRatioSectionTransport

/-! # Actual canonical ratio sections are frames off both ideal supports -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.PLOriginalModelCompatibility.RatioSectionTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance ratioSectionFramesModulesMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance ratioSectionFramesModulesSymmetric (X : Scheme.{u}) :
    SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X
noncomputable local instance ratioSectionFramesPullbackMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
open SchemeLineSectionEvaluation SchemeTensorSectionHoms

/-- The actual original evaluation transpose becomes a frame whenever
its actual original pulled functional is a frame. -/
theorem pulledDualTranspose_isIso_of_functional_isIso {X Y : Scheme.{u}}
    {M : Y.Modules} (hM : IsInvertible M) (f : X ⟶ Y) (α : M ⟶ unitObj Y)
    [IsIso ((pullback f).map α ≫ (pullbackUnitIso f).hom)] :
    IsIso (pullbackSectionHom f (hM.dualTranspose α)) := by
  let σ := pullbackSectionHom f (hM.dualTranspose α)
  have : IsIso ((pullback f).obj M ◁ σ ≫ (hM.pulledEvaluationIso f).hom) := by
    change IsIso ((pullback f).obj M ◁
      pullbackSectionHom f (hM.dualTranspose α) ≫ (hM.pulledEvaluationIso f).hom)
    rw [pulledDualTranspose_pairing hM f α]
    infer_instance
  have : IsIso ((pullback f).obj M ◁ σ) :=
    IsIso.of_isIso_comp_right _ (hM.pulledEvaluationIso f).hom
  have : IsIso ((tensorLeft ((pullback f).obj M)).map σ) := by
    change IsIso ((pullback f).obj M ◁ σ)
    infer_instance
  let hf := (hM.pullback f).tensorRightFullyFaithful.ofIso
    (BraidedCategory.tensorLeftIsoTensorRight ((pullback f).obj M)).symm
  exact hf.isIso_of_isIso_map σ

/-- The SAME canonical ratio section is an actual whole frame whenever
BOTH original included factor modules are actual frames. -/
theorem canonicalPulledRatioSection_isIso {X Y : Scheme.{u}}
    (I J : Y.IdealSheafData) (hJ : J.IsInvertible) (f : X ⟶ Y)
    [IsIso (I.pullbackModuleInclusion f)] [IsIso (J.pullbackModuleInclusion f)] :
    IsIso (canonicalPulledRatioSection I J hJ f) := by
  have : IsIso ((pullback f).map J.toModulesInclusion ≫ (pullbackUnitIso f).hom) :=
    (inferInstance : IsIso (J.pullbackModuleInclusion f))
  have := pulledDualTranspose_isIso_of_functional_isIso
    hJ.isInvertibleModule_toModules f J.toModulesInclusion
  have := tensorSectionHom_isIso
    (asIso (I.pullbackModuleInclusion f)).inv
    (pullbackSectionHom f (hJ.isInvertibleModule_toModules.dualTranspose J.toModulesInclusion))
  unfold canonicalPulledRatioSection
  infer_instance

/-- The existing original local ratio section is a frame on the SAME
open disjoint from the TWO original ideal supports. -/
theorem localSection_isIso {N : Scheme.{u}} (I J : N.IdealSheafData)
    (hJ : J.IsInvertible) (U : N.Opens)
    (hUI : U ≤ I.support.compl) (hUJ : U ≤ J.support.compl) :
    IsIso (CartierRatioLocalRealization.localSection I J hJ U hUI) := by
  have := offSupportInclusion_isIso I U hUI
  have := offSupportInclusion_isIso J U hUJ
  rw [← canonicalPulledRatioSection_eq_localSection I J hJ U hUI]
  exact canonicalPulledRatioSection_isIso I J hJ U.ι

end EnvelopeProperty.PLOriginalModelCompatibility.RatioSectionTransport
