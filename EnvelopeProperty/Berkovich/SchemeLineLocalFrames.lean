/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLineModelMetric
import EnvelopeProperty.AlgGeom.LocalSpecIdealPullbackImage
import ModularCurves.Picard.DualPullback.Square
import ModularCurves.Picard.DualPullback.UnitComp

/-! # Actual original local frames and proper model-line norms -/

open scoped NNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.Modules

/-- Genuine pullback-composition comparison for an ACTUAL factorization. -/
def frameFactorIso {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) (M : D.Modules) :
    (pullback g).obj ((pullback b).obj M) ≅ (pullback f).obj M :=
  (pullbackComp g b).app M ≪≫ (pullbackCongr hg).app M

/-- An ACTUAL original unit frame transported through a genuine factor,
using only native original composition and structure-unit comparisons. -/
def frameViaFactor {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) {M : D.Modules}
    (e : (pullback b).obj M ≅ unitObj C) :
    (pullback f).obj M ≅ unitObj B :=
  (frameFactorIso g b f hg M).symm ≪≫ (pullback g).mapIso e ≪≫ pullbackUnitIso g

private theorem frameFactorIso_comp {A B C D : Scheme.{u}}
    (i : A ⟶ B) (g : B ⟶ C) (b : C ⟶ D) (f : B ⟶ D) (hg : g ≫ b = f)
    (w : A ⟶ D) (hi : i ≫ f = w) (M : D.Modules) :
    (pullback i).map (frameFactorIso g b f hg M).hom ≫
        (frameFactorIso i f w hi M).hom =
      (pullbackComp i g).hom.app ((pullback b).obj M) ≫
        (frameFactorIso (i ≫ g) b w (by rw [Category.assoc, hg]; exact hi) M).hom := by
  subst f
  have h := pullbackComp_three_congr_trans_app i g b (i ≫ g) rfl w
    (Category.assoc i g b).symm ((Category.assoc i g b).trans hi) M
  change (pullback i).map ((pullbackComp g b).hom.app M) ≫
      (pullbackComp i (g ≫ b)).hom.app M ≫ (pullbackCongr hi).hom.app M =
    (pullbackComp i g).hom.app ((pullback b).obj M) ≫
      (pullbackComp (i ≫ g) b).hom.app M ≫
        (pullbackCongr ((Category.assoc i g b).trans hi)).hom.app M
  simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.app_hom,
    show (pullbackCongr (rfl : i ≫ g = i ≫ g)).hom.app ((pullback b).obj M) = 𝟙 _ from rfl,
    Category.comp_id, Category.id_comp]
    using h

/-- ACTUAL transported local frames compose as WHOLE original isomorphisms,
with no supplied associativity or metric compatibility certificate. -/
theorem frameViaFactor_comp {A B C D : Scheme.{u}}
    (i : A ⟶ B) (g : B ⟶ C) (b : C ⟶ D) (f : B ⟶ D) (hg : g ≫ b = f)
    (w : A ⟶ D) (hi : i ≫ f = w) {M : D.Modules}
    (e : (pullback b).obj M ≅ unitObj C) :
    frameViaFactor i f w hi (frameViaFactor g b f hg e) =
      frameViaFactor (i ≫ g) b w (by rw [Category.assoc, hg]; exact hi) e := by
  let c := frameFactorIso g b f hg M
  let t := frameFactorIso i f w hi M
  let q := (pullbackComp i g).app ((pullback b).obj M)
  let l := frameFactorIso (i ≫ g) b w (by rw [Category.assoc, hg]; exact hi) M
  have hc : (pullback i).mapIso c ≪≫ t = q ≪≫ l := by
    apply Iso.ext
    exact frameFactorIso_comp i g b f hg w hi M
  have hcinv := congrArg (fun z => z.inv) hc
  change t.inv ≫ (pullback i).map c.inv = l.inv ≫ q.inv at hcinv
  have hn := (pullbackComp i g).inv.naturality e.hom
  simp only [Functor.comp_map] at hn
  have hu : (pullbackComp i g).inv.app (unitObj C) ≫
      (pullback i).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso i).hom =
      (pullbackUnitIso (i ≫ g)).hom := by
    rw [← ModularCurves.pullbackUnitIso_compLow i g]
    exact Iso.inv_hom_id_assoc ((pullbackComp i g).app (unitObj C)) _
  apply Iso.ext
  simp only [frameViaFactor, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  change t.inv ≫ (pullback i).map c.inv ≫
      (pullback i).map ((pullback g).map e.hom) ≫
      (pullback i).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso i).hom =
    l.inv ≫ (pullback (i ≫ g)).map e.hom ≫ (pullbackUnitIso (i ≫ g)).hom
  rw [← Category.assoc t.inv, hcinv]
  simp only [Category.assoc]
  dsimp only [q]
  simp only [Iso.app_inv]
  rw [← reassoc_of% hn, hu]

end AlgebraicGeometry.Scheme.Modules

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
variable [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)

/-- The ACTUAL proper valuative lift factors through EVERY original
open neighborhood of its true original closed-point center. -/
def centerOpenFactor (U : X.Opens) (hc : center hb y ∈ U) :
    Spec (CommRingCat.of (CenterRing y)) ⟶ U.toScheme :=
  Classical.choose (Scheme.exists_lift_open_of_closedPoint_mem (centerLift hb y) U hc)

/-- The derived original open factor has the true WHOLE scheme triangle. -/
theorem centerOpenFactor_comp (U : X.Opens) (hc : center hb y ∈ U) :
    centerOpenFactor hb y U hc ≫ U.ι = centerLift hb y :=
  Classical.choose_spec (Scheme.exists_lift_open_of_closedPoint_mem (centerLift hb y) U hc)

/-- Pulling an ACTUAL original local frame to the true proper center
gives a genuine entire original valuation-ring frame. -/
def centerLocalFrame {M : X.Modules} (U : X.Opens) (hc : center hb y ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme) :
    centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))) :=
  Scheme.Modules.frameViaFactor (centerOpenFactor hb y U hc) U.ι (centerLift hb y)
    (centerOpenFactor_comp hb y U hc) e

/-- The ACTUAL original residue-field morphism into the genuine local open. -/
def localGenericFactor (U : X.Opens) (hc : center hb y ∈ U) :
    Spec (CommRingCat.of (X.residueField y.1.point)) ⟶ U.toScheme :=
  centerGenericMap y ≫ centerOpenFactor hb y U hc

/-- The direct original local residue morphism has the true WHOLE generic triangle. -/
theorem localGenericFactor_comp (U : X.Opens) (hc : center hb y ∈ U) :
    localGenericFactor hb y U hc ≫ U.ι = X.fromSpecResidueField y.1.point := by
  rw [localGenericFactor, Category.assoc, centerOpenFactor_comp]
  exact centerLift_generic hb y

/-- The given ACTUAL original local frame pulled DIRECTLY to the SAME
original residue-field fiber by the true original local generic morphism. -/
def localFrameGenericIso {M : X.Modules} (U : X.Opens) (hc : center hb y ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme) :
    genericLineModule y M ≅ Scheme.Modules.unitObj
      (Spec (CommRingCat.of (X.residueField y.1.point))) :=
  Scheme.Modules.frameViaFactor (localGenericFactor hb y U hc) U.ι
    (X.fromSpecResidueField y.1.point) (localGenericFactor_comp hb y U hc) e

/-- The ACTUAL proper-center generic frame equals the DIRECT pullback
of the given ACTUAL local frame, as WHOLE original isomorphisms. -/
theorem centerFrameGenericIso_localFrame {M : X.Modules} (U : X.Opens)
    (hc : center hb y ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme) :
    centerFrameGenericIso hb y (centerLocalFrame hb y U hc e) =
      localFrameGenericIso hb y U hc e := by
  exact Scheme.Modules.frameViaFactor_comp (centerGenericMap y) (centerOpenFactor hb y U hc)
    U.ι (centerLift hb y) (centerOpenFactor_comp hb y U hc)
    (X.fromSpecResidueField y.1.point) (centerLift_generic hb y) e

/-- ANY ACTUAL original local frame at the true proper center computes
the genuine model norm on the SAME whole original generic-line module. -/
theorem modelLineNorm_eq_localFrame {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (U : X.Opens) (hc : center hb y ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (s : Γ(genericLineModule y M, ⊤)) :
    modelLineNorm hb y hM s =
      y.1.residueVal ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom
        (((localFrameGenericIso hb y U hc e).hom.val.app (op ⊤)).hom s)) := by
  rw [modelLineNorm_eq_frame hb y hM (centerLocalFrame hb y U hc e)]
  unfold centerFrameLineNorm centerFrameCoefficient
  rw [centerFrameGenericIso_localFrame]

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
