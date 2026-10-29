import EnvelopeProperty.Vanishing.FrobeniusLineComparison
import EnvelopeProperty.AlgGeom.BundleTensorPowerPullback
import EnvelopeProperty.AlgGeom.SchemeModuleFrameGluing
import ModularCurves.Picard.DualPullback.Square
import ModularCurves.Picard.DualPullback.UnitComp

/-! # Pure scheme frames for the original Frobenius line comparison

These are the actual scheme-module frame formulas and complete generic
proofs from the existing line-frame API, retained in a separate namespace.
This module uses native pullback, tensor, unit, and restriction comparisons;
it needs no valued-point metric or curve-degree imports.  The exact source
mapping is recorded in the Frobenius-line audit directory.  The scoped
transparency settings below are inherited from the migrated native proofs;
no kernel axiom or heartbeat/recursion budget is changed.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.FrobeniusLineCore
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) : (pullback f).Monoidal :=
  Scheme.Modules.pullbackMonoidal f

section UnitAutomorphisms
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- EVERY actual whole structure-module endomorphism is actual scalar
multiplication by its ORIGINAL top-open value on the original unit section. -/
theorem unitHom_eq_globalScalar (a : unitObj X ⟶ unitObj X) :
    a = ModularCurves.unitEndomorphismOfTopSection
      ((a.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) := by
  apply SheafOfModules.hom_ext
  ext U
  change (a.val.app U).hom (1 : Γ(X, U.unop)) =
    1 * X.presheaf.map (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op
      ((a.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))
  rw [one_mul]
  have hn := congrArg (fun q => q.hom (1 : Γ(X, ⊤)))
    (a.val.naturality (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op)
  change (a.val.app U).hom
      (X.presheaf.map (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op (1 : Γ(X, ⊤))) =
    X.presheaf.map (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op
      ((a.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) at hn
  simpa only [map_one] using hn

/-- EVERY actual original whole structure-module automorphism is the
actual scalar automorphism of a genuine ORIGINAL global unit. -/
theorem unitIso_eq_globalUnit (e : unitObj X ≅ unitObj X) :
    ∃ u : Γ(X, (⊤ : X.Opens))ˣ, e = ModularCurves.unitAutomorphismOfTopUnit u := by
  let r : Γ(X, ⊤) := (e.hom.val.app (op ⊤)).hom (1 : Γ(X, ⊤))
  have : IsIso (e.hom.val.app (op ⊤)) :=
    inferInstanceAs (IsIso ((SheafOfModules.evaluation _ (op ⊤)).map e.hom))
  have he := (ConcreteCategory.isIso_iff_bijective (e.hom.val.app (op ⊤))).mp inferInstance
  have hr : IsUnit r := by
    apply IsUnit.isUnit_iff_mulRight_bijective.mpr
    have hmul : (fun x : Γ(X, ⊤) => x * r) = (e.hom.val.app (op ⊤)).hom := by
      funext x
      have hx := ((e.hom.val.app (op ⊤)).hom).map_smul x (1 : Γ(X, ⊤))
      simpa only [smul_eq_mul, mul_one, r] using hx.symm
    rw [hmul]
    exact he
  obtain ⟨u, hu⟩ := hr
  refine ⟨u, ?_⟩
  apply Iso.ext
  rw [ModularCurves.unitAutomorphismOfTopUnit_hom, hu]
  simpa only [r] using unitHom_eq_globalScalar e.hom


end UnitAutomorphisms

/-- The genuine whole tensor frame, using the actual structure multiplication. -/
def tensorFrame {X : Scheme.{u}} {P Q : X.Modules}
    (e : P ≅ unitObj X) (d : Q ≅ unitObj X) : P ⊗ Q ≅ unitObj X :=
  (e ⊗ᵢ d) ≪≫ ModularCurves.unitObjTensorIso X


/-- Frames of the actual recursively sheafified tensor powers. -/
def powerFrame {X : Scheme.{u}} {P : X.Modules} (e : P ≅ unitObj X) :
    (n : ℕ) → bundleTensorPower P n ≅ unitObj X
  | 0 => Iso.refl _
  | n + 1 => (ModularCurves.monoidalTensorObjIso (bundleTensorPower P n) P).symm ≪≫
      tensorFrame (powerFrame e n) e


section FactorTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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


/-- Actual original frame transport commutes with the genuine native
pullback-composition comparison on the original module sheaf. -/
theorem frameViaFactor_pullbackComp {A B C D : Scheme.{u}}
    (i : A ⟶ B) (b : B ⟶ C) (f : A ⟶ C) (hi : i ≫ b = f)
    (g : C ⟶ D) {M : D.Modules}
    (e : (pullback (b ≫ g)).obj M ≅ unitObj B) :
    frameViaFactor i b f hi ((pullbackComp b g).app M ≪≫ e) =
      (pullbackComp f g).app M ≪≫
        frameViaFactor i (b ≫ g) (f ≫ g) (by rw [← Category.assoc,hi]) e := by
  subst f
  have hc : (pullbackComp i b).inv.app ((pullback g).obj M) ≫
      (pullback i).map ((pullbackComp b g).hom.app M) =
        (pullbackComp (i ≫ b) g).hom.app M ≫
          (pullbackComp i (b ≫ g)).inv.app M := by
    apply (cancel_epi ((pullbackComp i b).hom.app ((pullback g).obj M))).mp
    rw [Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc,← pullbackComp_assoc_app]
    simp only [Category.assoc,Iso.hom_inv_id_app]
    erw [Category.comp_id]
  apply Iso.ext
  simp only [frameViaFactor,frameFactorIso,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,
    Functor.mapIso_hom,Functor.map_comp,Category.assoc]
  change (pullbackComp i b).inv.app ((pullback g).obj M) ≫
    (pullback i).map ((pullbackComp b g).hom.app M) ≫
      (pullback i).map e.hom ≫ (pullbackUnitIso i).hom =
    (pullbackComp (i ≫ b) g).hom.app M ≫
      (pullbackComp i (b ≫ g)).inv.app M ≫
        (pullback i).map e.hom ≫ (pullbackUnitIso i).hom
  rw [← Category.assoc ((pullbackComp i b).inv.app ((pullback g).obj M)),hc]
  simp only [Category.assoc]


end FactorTransport

/-- Genuine original tensor frames are natural in both actual whole preceding isomorphisms. -/
theorem tensorFrame_naturality {X : Scheme.{u}} {P P' Q Q' : X.Modules}
    (a : P ≅ P') (b : Q ≅ Q') (e : P' ≅ unitObj X) (d : Q' ≅ unitObj X) :
    (a ⊗ᵢ b) ≪≫ tensorFrame e d = tensorFrame (a ≪≫ e) (b ≪≫ d) := by
  apply Iso.ext
  simp only [tensorFrame, Iso.trans_hom, tensorIso_hom]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun t => t ≫ (ModularCurves.unitObjTensorIso X).hom)
      (tensorHom_comp_tensorHom a.hom b.hom e.hom d.hom))


/-- An ACTUAL original frame of f*M induces an entire frame of the SAME f*(M^n). -/
def pullbackPowerFrame {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules}
    (e : (pullback f).obj M ≅ unitObj Y) (n : ℕ) : (pullback f).obj (bundleTensorPower M n) ≅ unitObj Y :=
  BundleTensorPowerPullback.pullbackIso f M n ≪≫ powerFrame e n

/-- Degree zero is the ACTUAL native structure-unit pullback comparison. -/
theorem pullbackPowerFrame_zero {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules}
    (e : (pullback f).obj M ≅ unitObj Y) : pullbackPowerFrame f e 0 = pullbackUnitIso f :=
  Iso.trans_refl _

/-- The genuine pulled-power frame has the actual native tensor recursion as a WHOLE original iso. -/
theorem pullbackPowerFrame_succ {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules}
    (e : (pullback f).obj M ≅ unitObj Y) (n : ℕ) :
    pullbackPowerFrame f e (n + 1) =
      (pullback f).mapIso (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).symm ≪≫
        (Functor.Monoidal.μIso (pullback f) (bundleTensorPower M n) M).symm ≪≫
          tensorFrame (pullbackPowerFrame f e n) e := by
  change ((pullback f).mapIso (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).symm ≪≫
    (Functor.Monoidal.μIso (pullback f) (bundleTensorPower M n) M).symm ≪≫
    (BundleTensorPowerPullback.pullbackIso f M n ⊗ᵢ Iso.refl ((pullback f).obj M)) ≪≫
    ModularCurves.monoidalTensorObjIso (bundleTensorPower ((pullback f).obj M) n) ((pullback f).obj M)) ≪≫
    (ModularCurves.monoidalTensorObjIso (bundleTensorPower ((pullback f).obj M) n) ((pullback f).obj M)).symm ≪≫
      tensorFrame (powerFrame e n) e = _
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
  have hn := tensorFrame_naturality (BundleTensorPowerPullback.pullbackIso f M n)
    (Iso.refl ((pullback f).obj M)) (powerFrame e n) e
  simp only [Iso.refl_trans] at hn
  exact congrArg (fun E =>
    (pullback f).mapIso (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).symm ≪≫
      (Functor.Monoidal.μIso (pullback f) (bundleTensorPower M n) M).symm ≪≫ E) hn

/-- Actual factor-frame transport is natural in EVERY original module iso. -/
theorem frameViaFactor_naturality {U Y X : Scheme.{u}} (i : U ⟶ Y) (b : Y ⟶ X)
    (g : U ⟶ X) (hi : i ≫ b = g) {M N : X.Modules} (a : M ≅ N)
    (e : (pullback b).obj N ≅ unitObj Y) :
    frameViaFactor i b g hi ((pullback b).mapIso a ≪≫ e) =
      (pullback g).mapIso a ≪≫ frameViaFactor i b g hi e := by
  let c : pullback b ⋙ pullback i ≅ pullback g := pullbackComp i b ≪≫ pullbackCongr hi
  have hc := c.inv.naturality a.hom
  simp only [Functor.comp_map] at hc
  apply Iso.ext
  simp only [frameViaFactor, frameFactorIso, Functor.mapIso_trans, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  have h := congrArg (fun q => q ≫ (pullback i).map e.hom ≫ (pullbackUnitIso i).hom) hc.symm
  simpa only [Category.assoc, c, Iso.trans_inv, NatTrans.comp_app, Iso.app_inv] using h

/-- Genuine native unit comparisons preserve the actual factor frame at degree zero. -/
theorem frameViaFactor_unit {U Y X : Scheme.{u}} (i : U ⟶ Y) (b : Y ⟶ X)
    (g : U ⟶ X) (hi : i ≫ b = g) :
    frameViaFactor i b g hi (pullbackUnitIso b) = pullbackUnitIso g := by
  apply Iso.ext
  apply (cancel_epi (frameFactorIso i b g hi (unitObj X)).hom).mp
  simp only [frameViaFactor, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.hom_inv_id_assoc]
  have hg := ModularCurves.pullbackUnitIso_congr hi
  have hc := ModularCurves.pullbackUnitIso_compLow i b
  change (pullback i).map (pullbackUnitIso b).hom ≫ (pullbackUnitIso i).hom =
    (pullbackComp i b).hom.app (unitObj X) ≫ (pullbackCongr hi).hom.app (unitObj X) ≫ (pullbackUnitIso g).hom
  have ht := congrArg (fun a => (pullbackComp i b).hom.app (unitObj X) ≫ a) hg
  exact hc.symm.trans ht.symm

private theorem pullbackCongr_hom_isMonoidal {Y X : Scheme.{u}} {a b : Y ⟶ X} (h : a = b) :
    (pullbackCongr h).hom.IsMonoidal := by
  subst b
  change NatTrans.IsMonoidal (𝟙 (pullback a))
  infer_instance

/-- Genuine monoidal native composition derives WHOLE factor transport of the actual pulled tensor frame. -/
theorem frameViaFactor_tensor {U Y X : Scheme.{u}} (i : U ⟶ Y) (b : Y ⟶ X)
    (g : U ⟶ X) (hi : i ≫ b = g) {M N : X.Modules}
    (e : (pullback b).obj M ≅ unitObj Y) (d : (pullback b).obj N ≅ unitObj Y) :
    frameViaFactor i b g hi ((Functor.Monoidal.μIso (pullback b) M N).symm ≪≫ tensorFrame e d) =
      (Functor.Monoidal.μIso (pullback g) M N).symm ≪≫
        tensorFrame (frameViaFactor i b g hi e) (frameViaFactor i b g hi d) := by
  let c : pullback b ⋙ pullback i ≅ pullback g := pullbackComp i b ≪≫ pullbackCongr hi
  have : (pullbackComp i b).hom.IsMonoidal := pullbackComp_hom_isMonoidal i b
  have : (pullbackCongr hi).hom.IsMonoidal := pullbackCongr_hom_isMonoidal hi
  have : c.hom.IsMonoidal := by dsimp only [c, Iso.trans_hom]; infer_instance
  exact (ModularCurves.pullbackComp_tensorTrivialization b i g c M N e d).symm

/-- The actual explicit tensor factor frame is preserved by the genuine native factor comparison. -/
theorem frameViaFactor_explicitTensor {U Y X : Scheme.{u}} (i : U ⟶ Y) (b : Y ⟶ X)
    (g : U ⟶ X) (hi : i ≫ b = g) {M N : X.Modules}
    (e : (pullback b).obj M ≅ unitObj Y) (d : (pullback b).obj N ≅ unitObj Y) :
    frameViaFactor i b g hi
        ((pullback b).mapIso (ModularCurves.monoidalTensorObjIso M N).symm ≪≫
          (Functor.Monoidal.μIso (pullback b) M N).symm ≪≫ tensorFrame e d) =
      (pullback g).mapIso (ModularCurves.monoidalTensorObjIso M N).symm ≪≫
        (Functor.Monoidal.μIso (pullback g) M N).symm ≪≫
          tensorFrame (frameViaFactor i b g hi e) (frameViaFactor i b g hi d) := by
  have hn := frameViaFactor_naturality i b g hi (ModularCurves.monoidalTensorObjIso M N).symm
    ((Functor.Monoidal.μIso (pullback b) M N).symm ≪≫ tensorFrame e d)
  have ht := congrArg (fun E => (pullback g).mapIso (ModularCurves.monoidalTensorObjIso M N).symm ≪≫ E)
    (frameViaFactor_tensor i b g hi e d)
  exact hn.trans ht

/-- Every ACTUAL original triangle derives WHOLE native factor compatibility for actual pulled power frames. -/
theorem pullbackPowerFrame_factor {U Y X : Scheme.{u}} (i : U ⟶ Y) (b : Y ⟶ X)
    (g : U ⟶ X) (hi : i ≫ b = g) {M : X.Modules}
    (e : (pullback b).obj M ≅ unitObj Y) (n : ℕ) :
    frameViaFactor i b g hi (pullbackPowerFrame b e n) =
      pullbackPowerFrame g (frameViaFactor i b g hi e) n := by
  induction n with
  | zero =>
    have hz := congrArg (fun E => frameViaFactor i b g hi E) (pullbackPowerFrame_zero b e)
    exact hz.trans ((frameViaFactor_unit i b g hi).trans (pullbackPowerFrame_zero g _).symm)
  | succ n ih =>
    have hr := congrArg (fun E => frameViaFactor i b g hi E) (pullbackPowerFrame_succ b e n)
    have ht := frameViaFactor_explicitTensor i b g hi (pullbackPowerFrame b e n) e
    have hp := congrArg (fun E =>
      (pullback g).mapIso (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).symm ≪≫
        (Functor.Monoidal.μIso (pullback g) (bundleTensorPower M n) M).symm ≪≫
          tensorFrame E (frameViaFactor i b g hi e)) ih
    exact hr.trans (ht.trans (hp.trans (pullbackPowerFrame_succ g _ n).symm))


theorem restrictTrivialization_eq_frameViaFactor {X : Scheme.{u}} {M : X.Modules}
    {U V : X.Opens} (h : V ≤ U) (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    restrictTrivialization h e = frameViaFactor (X.homOfLE h) U.ι V.ι (X.homOfLE_ι h) e := by
  exact pullbackCompositeTrivialization_eq (X.homOfLE h) U.ι V.ι (X.homOfLE_ι h) M e

theorem restrictIso_frameViaFactor {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (h : V ≤ U) (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    restrictOpenTrivialization h (restrictIsoOfPullbackIso M U e) =
      restrictIsoOfPullbackIso M V
        (frameViaFactor (X.homOfLE h) U.ι V.ι (X.homOfLE_ι h) e) := by
  rw [restrictOpenTrivialization_eq_pullback]
  unfold restrictOpenTrivializationPullback restrictIsoOfPullbackIso
  change (restrictFunctorIsoPullback V.ι).app M ≪≫
      restrictTrivialization h (((restrictFunctorIsoPullback U.ι).app M).symm ≪≫
        ((restrictFunctorIsoPullback U.ι).app M ≪≫ e)) =
    (restrictFunctorIsoPullback V.ι).app M ≪≫
      frameViaFactor (X.homOfLE h) U.ι V.ι (X.homOfLE_ι h) e
  rw [Iso.symm_self_id_assoc,restrictTrivialization_eq_frameViaFactor]


end EnvelopeProperty.Vanishing.FrobeniusLineCore
