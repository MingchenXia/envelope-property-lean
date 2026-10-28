import EnvelopeProperty.AlgGeom.SchemeGlobalSectionModelNormIsometries
import EnvelopeProperty.AlgGeom.SchemeTensorSectionHoms
import EnvelopeProperty.AlgGeom.BundleTensorPowerPullback
import EnvelopeProperty.Berkovich.SchemeLineModelTensorHomNorms
import EnvelopeProperty.Berkovich.SchemeLineFibreSectionNorms

/-! # Actual entire original section powers and true proper-model norms -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
open scoped NNReal
noncomputable section
universe u
namespace EnvelopeProperty.SchemeGlobalSectionTensorPowerNorms
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CanonicalGeometry SchemeLineSectionEvaluation SchemeTensorSectionHoms
open SchemeGlobalSectionModelNormIsometries Berkovich RelativeSchemeValuedPoint
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem unitHomExtTop {X : Scheme.{u}} {M : X.Modules} (α β : unitObj X ⟶ M)
    (h : sectionAtOne α = sectionAtOne β) : α = β := by
  apply SheafOfModules.hom_ext
  ext V
  let a := (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
  have ha := PresheafOfModules.naturality_apply α.val a (1 : Γ(X,⊤))
  have hb := PresheafOfModules.naturality_apply β.val a (1 : Γ(X,⊤))
  change α.val.app V (X.presheaf.map a (1 : Γ(X,⊤))) = M.presheaf.map a (sectionAtOne α) at ha
  change β.val.app V (X.presheaf.map a (1 : Γ(X,⊤))) = M.presheaf.map a (sectionAtOne β) at hb
  rw [map_one] at ha hb
  exact ha.trans ((congrArg (M.presheaf.map a) h).trans hb.symm)

private theorem sectionHom_sectionAtOne {X : Scheme.{u}} {M : X.Modules} (α : unitObj X ⟶ M) :
    SchemeModuleGlobalSections.sectionHom M (sectionAtOne α) = α := by
  apply unitHomExtTop
  change sectionAtOne (topSectionHom M (sectionAtOne α)) = _
  exact topSectionHom_app_top_apply_one M (sectionAtOne α)

/-- The SAME actual original section-unit morphism raised to EVERY original explicit tensor power. -/
def powerSectionHom {X : Scheme.{u}} {M : X.Modules} (σ : unitObj X ⟶ M) :
    (n : ℕ) → unitObj X ⟶ bundleTensorPower M n
  | 0 => 𝟙 (unitObj X)
  | n + 1 => tensorSectionHom (powerSectionHom σ n) σ ≫
    (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).hom

/-- EVERY whole original global section has its genuine original tensor-power section. -/
def powerSection {X : Scheme.{u}} (M : X.Modules) (s : Γ(M,⊤)) (n : ℕ) :
    Γ(bundleTensorPower M n,⊤) :=
  sectionAtOne (powerSectionHom (SchemeModuleGlobalSections.sectionHom M s) n)

/-- The actual entire section power has EXACTLY its original recursively formed section-unit morphism. -/
theorem sectionHom_powerSection {X : Scheme.{u}} (M : X.Modules) (s : Γ(M,⊤)) (n : ℕ) :
    SchemeModuleGlobalSections.sectionHom (bundleTensorPower M n) (powerSection M s n) =
      powerSectionHom (SchemeModuleGlobalSections.sectionHom M s) n :=
  sectionHom_sectionAtOne _

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X : Scheme.{u}} {p : X ⟶ Spec (.of R)} [IsProper p]
  (hb : ∀ r,v r ≤ 1) (y : RelativeSchemeValuedPoint v p)

/-- True model morphism norms multiply on actual original tensor sections, including zero. -/
theorem modelHomNorm_tensorSectionHom {M N : X.Modules} (hM : IsInvertible M) (hN : IsInvertible N)
    (σ : unitObj X ⟶ M) (τ : unitObj X ⟶ N) :
    modelHomNorm hb y (isInvertible_unit (X := X)) (hM.monoidalTensor hN) (tensorSectionHom σ τ) =
      modelHomNorm hb y (isInvertible_unit (X := X)) hM σ *
        modelHomNorm hb y (isInvertible_unit (X := X)) hN τ := by
  have hu := modelHomNorm_iso hb y (isInvertible_unit (X := X))
    ((isInvertible_unit (X := X)).monoidalTensor (isInvertible_unit (X := X)))
    (ModularCurves.unitObjTensorIso X).symm
  simp only [Iso.symm_hom] at hu
  unfold tensorSectionHom
  rw [modelHomNorm_comp hb y (isInvertible_unit (X := X))
    ((isInvertible_unit (X := X)).monoidalTensor (isInvertible_unit (X := X)))
    (hM.monoidalTensor hN),hu,
    one_mul,modelHomNorm_tensorHom]

/-- Every true original section-unit morphism power has EXACTLY the original model norm to that power. -/
theorem modelHomNorm_powerSectionHom {M : X.Modules} (hM : IsInvertible M)
    (σ : unitObj X ⟶ M) (n : ℕ) :
    modelHomNorm hb y (isInvertible_unit (X := X))
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n) (powerSectionHom σ n) =
        modelHomNorm hb y (isInvertible_unit (X := X)) hM σ ^ n := by
  induction n with
  | zero => exact (modelHomNorm_id hb y (isInvertible_unit (X := X))).trans (pow_zero _).symm
  | succ n ih =>
    change modelHomNorm hb y (isInvertible_unit (X := X))
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM (n+1))
      (tensorSectionHom (powerSectionHom σ n) σ ≫
        (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).hom) = _
    rw [modelHomNorm_comp hb y (isInvertible_unit (X := X))
      ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n).monoidalTensor hM)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM (n+1)),
      modelHomNorm_iso hb y _ _ (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M),
      mul_one,modelHomNorm_tensorSectionHom hb y
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n) hM,ih,pow_succ]

/-- EVERY actual original whole global section power has its TRUE proper-model norm raised to that power. -/
theorem globalSectionNorm_powerSection (M : X.Modules) (hM : IsInvertible M) (s : Γ(M,⊤)) (n : ℕ) :
    globalSectionNorm hb y (bundleTensorPower M n)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n) (powerSection M s n) =
        globalSectionNorm hb y M hM s ^ n := by
  simp only [globalSectionNorm,sectionHom_powerSection,modelLineNorm_fibreSection]
  exact modelHomNorm_powerSectionHom hb y hM (SchemeModuleGlobalSections.sectionHom M s) n

/-- The ACTUAL original power of a section of M^d, in the SAME true original M^(d*r) module. -/
def blockPowerSection (M : X.Modules) (d : ℕ) (s : Γ(bundleTensorPower M d,⊤)) (r : ℕ) :
    Γ(bundleTensorPower M (d*r),⊤) :=
  SchemeModuleIsoGlobalSections.moduleIsoTopEquiv (BundleTensorPowerPullback.powerMulIso M d r)
    (powerSection (bundleTensorPower M d) s r)

/-- Actual original exponent-block section powers retain true norms at EVERY actual native point. -/
theorem globalSectionNorm_blockPowerSection (M : X.Modules) (hM : IsInvertible M)
    (d : ℕ) (s : Γ(bundleTensorPower M d,⊤)) (r : ℕ) :
    globalSectionNorm hb y (bundleTensorPower M (d*r))
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM (d*r)) (blockPowerSection M d s r) =
        globalSectionNorm hb y (bundleTensorPower M d)
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM d) s ^ r := by
  unfold blockPowerSection
  exact (globalSectionNorm_moduleIso hb y
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM d) r)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM (d*r))
    (BundleTensorPowerPullback.powerMulIso M d r) _).symm.trans
      (globalSectionNorm_powerSection hb y (bundleTensorPower M d)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM d) s r)

end EnvelopeProperty.SchemeGlobalSectionTensorPowerNorms
