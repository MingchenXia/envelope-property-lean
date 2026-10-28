import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationUnitOpenPowers
import EnvelopeProperty.AlgGeom.CartierModuleFlatPullback

/-! # Genuine Cartier unit comparisons from original geometric ideal data

The native original ideal module and geometric comap ideal remain fixed.
Actual geometric triviality derives module triviality, with no supplied
module comparison. This does not identify an arbitrary TC polarization
with a newly constructed module.
-/

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules CanonicalGeometry

noncomputable local instance (Z : Scheme.{u}) : MonoidalCategory Z.Modules :=
  Scheme.Modules.monoidalCategory Z

/-- The actual top ideal module is the original structure module by its
literal original section inclusion; every original function has membership. -/
def originalTopIdealModuleIso (X : Scheme.{u}) :
    (⊤ : X.IdealSheafData).toModules ≅ unitObj X := by
  let i : (⊤ : X.IdealSheafData).toModules ⟶ unitObj X :=
    ⟨(⊤ : X.IdealSheafData).toSubmodule.ι⟩
  let r : unitObj X ⟶ (⊤ : X.IdealSheafData).toModules :=
    { val :=
        { app := fun W => ModuleCat.ofHom
            { toFun := fun a => ⟨a, by
                change (⊤ : X.IdealSheafData).IsLocallyMem W.unop a
                intro V hV
                simp⟩
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          naturality := by
            intro U V f
            ext
            rfl } }
  exact
    { hom := i
      inv := r
      hom_inv_id := by ext W a; rfl
      inv_hom_id := by ext W a; rfl }

/-- The constructed whole iso retains the literal original function at
EVERY original open, rather than merely giving an abstract free frame. -/
theorem originalTopIdealModuleIso_hom_apply (X : Scheme.{u}) (W : X.Opens)
    (s : Γ((⊤ : X.IdealSheafData).toModules, W)) :
    (originalTopIdealModuleIso X).hom.val.app (op W) s =
      (s : (⊤ : X.IdealSheafData).toSubmodule.obj (op W)).val := rfl

/-- Actual original Cartier flat pullback and original geometric ideal
triviality DERIVE this whole original module/unit comparison. -/
def originalCartierIdealPullbackUnitIso {Y Z : Scheme.{u}} (j : Z ⟶ Y) [Flat j]
    (I : Y.IdealSheafData) (hI : I.IsInvertible) (hIvert : I.comap j = ⊤) :
    (Scheme.Modules.pullback j).obj I.toModules ≅ unitObj Z :=
  hI.flatPullbackModuleIso j ≪≫
    eqToIso (congrArg (fun K : Z.IdealSheafData => K.toModules) hIvert) ≪≫
      originalTopIdealModuleIso Z

/-- The SAME original vertical Cartier tensor-dual ratio has its actual
unit pullback by true native tensor/dual comparisons, without an iso input. -/
def originalCartierRatioPullbackUnitIso {Y Z : Scheme.{u}} (j : Z ⟶ Y) [Flat j]
    (I J : Y.IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (hIvert : I.comap j = ⊤) (hJvert : J.comap j = ⊤) :
    (Scheme.Modules.pullback j).obj (I.ratioModule J) ≅ unitObj Z :=
  I.ratioPullbackIso J hJ j ≪≫
    tensorObjCongr (originalCartierIdealPullbackUnitIso j I hI hIvert)
      (dualIsoObj (originalCartierIdealPullbackUnitIso j J hJ hJvert).symm) ≪≫
    tensorObjCongr (Iso.refl _) (dualUnitObjIso (X := Z)) ≪≫
    (ModularCurves.monoidalTensorObjIso (unitObj Z) (unitObj Z)).symm ≪≫
    ModularCurves.unitObjTensorIso Z

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
