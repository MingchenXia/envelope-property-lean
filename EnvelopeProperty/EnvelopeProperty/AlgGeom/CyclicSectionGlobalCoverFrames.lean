import EnvelopeProperty.AlgGeom.NativeLineTransitionCocycles
import EnvelopeProperty.AlgGeom.SchemePulledPowerFrames
import EnvelopeProperty.Berkovich.SchemeFramedSectionPullback

/-! # Original line frames and their actual section coefficients

All units and coefficient transformation laws are derived from original native
module isomorphisms and original tensor powers. No scalar transition certificate
or prescribed coefficient compatibility is an input.
-/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open Scheme.Modules
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.CyclicSectionGlobalCoverFrames
open CanonicalGeometry SchemeModuleFrameCoefficients SchemeTensorPowerFrames
open NativeLineTransitionCocycles SchemePulledPowerFrames SchemeLineSectionEvaluation
attribute [local instance] Scheme.Modules.monoidalCategory

/-- The SAME internally derived whole frame unit compares every original section. -/
theorem transitionUnit_coefficient {X : Scheme.{u}} {M : X.Modules}
    (e f : M ≅ unitObj X) (s : Γ(M, ⊤)) :
    coefficient f s = (transitionUnit e f : Γ(X, ⊤)) * coefficient e s := by
  have he := unitScalar_spec (e.symm ≪≫ f)
  have hh := congrArg (fun E => (e ≪≫ E).hom.app ⊤ s) he
  simp only [Iso.self_symm_id_assoc] at hh
  change coefficient f s =
    (ModularCurves.unitAutomorphismOfTopUnit (transitionUnit e f)).hom.app ⊤
      (coefficient e s) at hh
  refine hh.trans ?_
  change (ModularCurves.unitEndomorphismOfTopSection (transitionUnit e f : Γ(X, ⊤))).val.app
    (op ⊤) (coefficient e s) = _
  rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
  simp only [homOfLE_refl, op_id]
  erw [CategoryTheory.Functor.map_id]
  exact mul_comm (coefficient e s) (transitionUnit e f : Γ(X, ⊤))

/-- The derived whole frame unit is its actual inverse-frame section coefficient. -/
theorem transitionUnit_val {X : Scheme.{u}} {M : X.Modules}
    (e f : M ≅ unitObj X) :
    (transitionUnit e f : Γ(X, ⊤)) = coefficient f (unitSection e) := by
  rw [transitionUnit_coefficient, coefficient_unitSection, mul_one]

/-- A common original preceding isomorphism leaves the actual global frame unit unchanged. -/
theorem transitionUnit_precomp {X : Scheme.{u}} {M N : X.Modules} (a : M ≅ N)
    (e f : N ≅ unitObj X) : transitionUnit (a ≪≫ e) (a ≪≫ f) = transitionUnit e f := by
  unfold transitionUnit
  congr 1
  simp only [Iso.trans_symm, Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- Native whole tensor frames multiply their original global transition units. -/
theorem transitionUnit_tensorFrame {X : Scheme.{u}} {M N : X.Modules}
    (e f : M ≅ unitObj X) (d g : N ≅ unitObj X) :
    transitionUnit (tensorFrame e d) (tensorFrame f g) = transitionUnit e f * transitionUnit d g := by
  apply Units.ext
  rw [Units.val_mul, transitionUnit_val, tensorFrame_unitSection,
    tensorFrame_coefficient, ← transitionUnit_val, ← transitionUnit_val]

/-- Every original native power frame has precisely the original frame unit to that power. -/
theorem transitionUnit_powerFrame {X : Scheme.{u}} {M : X.Modules}
    (e f : M ≅ unitObj X) (n : ℕ) :
    transitionUnit (powerFrame e n) (powerFrame f n) = transitionUnit e f ^ n := by
  induction n with
  | zero =>
    apply Units.ext
    rw [transitionUnit_val]
    change coefficient (Iso.refl (unitObj X)) (unitSection (Iso.refl (unitObj X))) = _
    rw [coefficient_unitSection]
    simp
  | succ n ih =>
    change transitionUnit
      ((ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).symm ≪≫
        tensorFrame (powerFrame e n) e)
      ((ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).symm ≪≫
        tensorFrame (powerFrame f n) f) = _
    rw [transitionUnit_precomp, transitionUnit_tensorFrame, ih, pow_succ]

/-- Original pulled-power frames have exactly the original degree-one frame transition. -/
theorem transitionUnit_pullbackPowerFrame {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules}
    (e d : (pullback f).obj M ≅ unitObj Y) (n : ℕ) :
    transitionUnit (pullbackPowerFrame f e n) (pullbackPowerFrame f d n) = transitionUnit e d ^ n := by
  rw [pullbackPowerFrame, pullbackPowerFrame, transitionUnit_precomp, transitionUnit_powerFrame]

/-- The actual coefficient of the SAME original section in its induced line-power frame. -/
def sectionCoefficient {X Y : Scheme.{u}} (L : X.Modules) (n : ℕ)
    (s : unitObj X ⟶ bundleTensorPower L n) (f : Y ⟶ X)
    (e : (pullback f).obj L ≅ unitObj Y) : Γ(Y, ⊤) :=
  sectionAtOne (pullbackSectionHom f s ≫ (pullbackPowerFrame f e n).hom)

/-- The coefficient of the same original section changes by the actual original frame-unit power. -/
theorem sectionCoefficient_change {X Y : Scheme.{u}} (L : X.Modules) (n : ℕ)
    (s : unitObj X ⟶ bundleTensorPower L n) (f : Y ⟶ X)
    (e d : (pullback f).obj L ≅ unitObj Y) :
    sectionCoefficient L n s f d =
      (transitionUnit e d : Γ(Y, ⊤)) ^ n * sectionCoefficient L n s f e := by
  change coefficient (pullbackPowerFrame f d n) (sectionAtOne (pullbackSectionHom f s)) = _
  rw [transitionUnit_coefficient, transitionUnit_pullbackPowerFrame]
  rfl

/-- Actual restriction of an original section coefficient is its coefficient in the transported frame. -/
theorem sectionCoefficient_factor {X Y W : Scheme.{u}} (L : X.Modules) (n : ℕ)
    (s : unitObj X ⟶ bundleTensorPower L n) (f : Y ⟶ X)
    (e : (pullback f).obj L ≅ unitObj Y) (i : W ⟶ Y) (g : W ⟶ X) (hi : i ≫ f = g) :
    sectionCoefficient L n s g (frameViaFactor i f g hi e) =
      i.appTop (sectionCoefficient L n s f e) := by
  have hr := unitHom_eq_globalScalar (pullbackSectionHom f s ≫ (pullbackPowerFrame f e n).hom)
  have hh := frameViaFactor_sectionHom_scalar_apply i f g hi
    (pullbackPowerFrame f e n) s (sectionCoefficient L n s f e) hr
  rw [pullbackPowerFrame_factor] at hh
  exact hh

end EnvelopeProperty.CyclicSectionGlobalCoverFrames
