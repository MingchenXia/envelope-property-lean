import EnvelopeProperty.AlgGeom.SchemeGlobalSectionTensorPowerNorms
import EnvelopeProperty.AlgGeom.SchemePulledPowerFrames

/-! # Original section powers and their actual frame and pullback laws -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.CyclicSectionGlobalCoverRootSectionPowers
open CanonicalGeometry SchemeTensorSectionHoms SchemeTensorPowerFrames
open SchemeGlobalSectionTensorPowerNorms SchemeLineSectionEvaluation
attribute [local instance] Scheme.Modules.monoidalCategory

/-- The whole original tensor section in two structure-unit coefficients is scalar multiplication. -/
theorem tensorSectionHom_scalars {X : Scheme.{u}} (a b : Γ(X, ⊤)) :
    tensorSectionHom (ModularCurves.unitEndomorphismOfTopSection a)
      (ModularCurves.unitEndomorphismOfTopSection b) ≫ (ModularCurves.unitObjTensorIso X).hom =
        ModularCurves.unitEndomorphismOfTopSection (a * b) := by
  have h := tensorSectionHom_precomp_scalars (𝟙 (unitObj X)) (𝟙 (unitObj X)) a b
  simp only [Category.comp_id] at h
  rw [h]
  simp only [tensorSectionHom, id_tensorHom_id, Category.comp_id,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The genuine section power has the original coefficient raised to the same power. -/
theorem powerSectionHom_frame {X : Scheme.{u}} {M : X.Modules}
    (τ : unitObj X ⟶ M) (e : M ≅ unitObj X) (a : Γ(X, ⊤))
    (ha : τ ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection a) (n : ℕ) :
    powerSectionHom τ n ≫ (powerFrame e n).hom =
      ModularCurves.unitEndomorphismOfTopSection (a ^ n) := by
  induction n with
  | zero =>
    change 𝟙 (unitObj X) ≫ 𝟙 (unitObj X) = _
    rw [pow_zero, ModularCurves.unitEndomorphismOfTopSection_one, Category.id_comp]
  | succ n ih =>
    change (tensorSectionHom (powerSectionHom τ n) τ ≫
      (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).hom) ≫
        ((ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).inv ≫
          (tensorFrame (powerFrame e n) e).hom) = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    change tensorSectionHom (powerSectionHom τ n) τ ≫
      ((powerFrame e n).hom ⊗ₘ e.hom) ≫ (ModularCurves.unitObjTensorIso X).hom = _
    rw [← Category.assoc, tensorSectionHom_comp, ih, ha, tensorSectionHom_scalars, pow_succ]

/-- Actual whole section morphisms commute with the SAME native pullback-power comparison. -/
theorem pullback_powerSectionHom {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules}
    (τ : unitObj X ⟶ M) (n : ℕ) :
    pullbackSectionHom f (powerSectionHom τ n) ≫
        (BundleTensorPowerPullback.pullbackIso f M n).hom =
      powerSectionHom (pullbackSectionHom f τ) n := by
  let : (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
  induction n with
  | zero =>
    change (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map (𝟙 (unitObj X)) ≫
      (pullbackUnitIso f).hom = 𝟙 _
    rw [(Scheme.Modules.pullback f).map_id, Category.id_comp, Iso.inv_hom_id]
  | succ n ih =>
    change pullbackSectionHom f (tensorSectionHom (powerSectionHom τ n) τ ≫
      (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).hom) ≫
        ((Scheme.Modules.pullback f).map
          (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).inv ≫
        (Functor.Monoidal.μIso (Scheme.Modules.pullback f) (bundleTensorPower M n) M).inv ≫
        ((BundleTensorPowerPullback.pullbackIso f M n).hom ⊗ₘ 𝟙 _) ≫
        (ModularCurves.monoidalTensorObjIso
          (bundleTensorPower ((Scheme.Modules.pullback f).obj M) n)
          ((Scheme.Modules.pullback f).obj M)).hom) = _
    unfold pullbackSectionHom at *
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc ((Scheme.Modules.pullback f).map
      (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).hom),
      ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    change (pullbackSectionHom f (tensorSectionHom (powerSectionHom τ n) τ) ≫
      (Functor.Monoidal.μIso (Scheme.Modules.pullback f) (bundleTensorPower M n) M).inv) ≫
      ((BundleTensorPowerPullback.pullbackIso f M n).hom ⊗ₘ 𝟙 _) ≫
        (ModularCurves.monoidalTensorObjIso
          (bundleTensorPower ((Scheme.Modules.pullback f).obj M) n)
          ((Scheme.Modules.pullback f).obj M)).hom = _
    change pullbackSectionHom f (powerSectionHom τ n) ≫
      (BundleTensorPowerPullback.pullbackIso f M n).hom =
        powerSectionHom (pullbackSectionHom f τ) n at ih
    rw [pullback_tensorSectionHom, ← Category.assoc, tensorSectionHom_comp, ih, Category.comp_id]
    rfl

end EnvelopeProperty.CyclicSectionGlobalCoverRootSectionPowers
