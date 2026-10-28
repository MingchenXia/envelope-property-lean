import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverRootSectionPowers
import EnvelopeProperty.AlgGeom.BundleTensorPowerPullbackCoherence

/-! # Original section powers through actual original factor comparisons -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.CyclicSectionGlobalCoverRootSectionPowerCoherence
open CanonicalGeometry SchemeTensorSectionHoms SchemeGlobalSectionTensorPowerNorms
open BundleTensorPowerPullback BundleTensorPowerPullbackCoherence
attribute [local instance] Scheme.Modules.monoidalCategory

/-- The actual whole section power is natural in every original module isomorphism. -/
theorem powerSectionHom_iso {X : Scheme.{u}} {M N : X.Modules}
    (τ : unitObj X ⟶ M) (e : M ≅ N) (n : ℕ) :
    powerSectionHom τ n ≫ (powerIso e n).hom = powerSectionHom (τ ≫ e.hom) n := by
  induction n with
  | zero => exact Category.id_comp _
  | succ n ih =>
    change (tensorSectionHom (powerSectionHom τ n) τ ≫
      (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).hom) ≫
        (bundleTensorIso (powerIso e n) e).hom = _
    have hn : (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).hom ≫
        (bundleTensorIso (powerIso e n) e).hom =
      ((powerIso e n).hom ⊗ₘ e.hom) ≫
        (ModularCurves.monoidalTensorObjIso (bundleTensorPower N n) N).hom :=
      ModularCurves.cartierMonoidalTensorObjIso_hom_natural (powerIso e n) e
    rw [Category.assoc, hn, ← Category.assoc, tensorSectionHom_comp, ih]
    rfl

/-- The whole original power comparison commutes with every actual structural factor triangle. -/
theorem pullbackIso_factor {X Y W : Scheme.{u}} (L : X.Modules)
    (i : W ⟶ Y) (b : Y ⟶ X) (g : W ⟶ X) (hi : i ≫ b = g) (n : ℕ) :
    (pullback i).mapIso (pullbackIso b L n) ≪≫ pullbackIso i ((pullback b).obj L) n ≪≫
        powerIso (frameFactorIso i b g hi L) n =
      frameFactorIso i b g hi (bundleTensorPower L n) ≪≫ pullbackIso g L n := by
  have hc := pullbackIso_comp i b L n
  have hg := pullbackIso_congr hi L n
  calc
    _ = ((pullback i).mapIso (pullbackIso b L n) ≪≫ pullbackIso i ((pullback b).obj L) n ≪≫
        powerIso ((pullbackComp i b).app L) n) ≪≫ powerIso ((pullbackCongr hi).app L) n := by
      rw [frameFactorIso, powerIso_trans]
      simp only [Iso.trans_assoc]
    _ = ((pullbackComp i b).app (bundleTensorPower L n) ≪≫ pullbackIso (i ≫ b) L n) ≪≫
        powerIso ((pullbackCongr hi).app L) n := congrArg (fun E => E ≪≫ _) hc
    _ = (pullbackComp i b).app (bundleTensorPower L n) ≪≫
        ((pullbackCongr hi).app (bundleTensorPower L n) ≪≫ pullbackIso g L n) := by
      rw [Iso.trans_assoc, ← hg]
    _ = _ := (Iso.trans_assoc _ _ _).symm

end EnvelopeProperty.CyclicSectionGlobalCoverRootSectionPowerCoherence
