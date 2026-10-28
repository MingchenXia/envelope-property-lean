import EnvelopeProperty.Berkovich.SchemeLinePowerFrameNorms

/-! # Actual whole native pullback-power frames and genuine factor triangles -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
open scoped NNReal
noncomputable section
universe u
namespace EnvelopeProperty.SchemePulledPowerFrames
open CanonicalGeometry SchemeTensorPowerFrames
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) : (pullback f).Monoidal :=
  Scheme.Modules.pullbackMonoidal f

private theorem cancelIsoSquare {C : Type*} [Category C] {W X Y Z : C}
    (k : W ≅ X) (l : Y ≅ Z) (t : X ≅ Z) (s : W ≅ Y)
    (h : k ≪≫ t = s ≪≫ l) : t ≪≫ l.symm = k.symm ≪≫ s := by
  have hh := congrArg (fun E => k.symm ≪≫ E ≪≫ l.symm) h
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id, Iso.trans_refl] using hh

/-- Genuine original tensor frames are natural in both actual whole preceding isomorphisms. -/
theorem tensorFrame_naturality {X : Scheme.{u}} {P P' Q Q' : X.Modules}
    (a : P ≅ P') (b : Q ≅ Q') (e : P' ≅ unitObj X) (d : Q' ≅ unitObj X) :
    (a ⊗ᵢ b) ≪≫ tensorFrame e d = tensorFrame (a ≪≫ e) (b ≪≫ d) := by
  apply Iso.ext
  simp only [tensorFrame, Iso.trans_hom, tensorIso_hom]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun t => t ≫ (ModularCurves.unitObjTensorIso X).hom)
      (tensorHom_comp_tensorHom a.hom b.hom e.hom d.hom))

/-- The actual original explicit tensor comparison commutes with actual whole factor isos. -/
theorem explicitTensorIso_naturality {X : Scheme.{u}} {P P' Q Q' : X.Modules}
    (a : P ≅ P') (b : Q ≅ Q') :
    bundleTensorIso a b ≪≫ (ModularCurves.monoidalTensorObjIso P' Q').symm =
      (ModularCurves.monoidalTensorObjIso P Q).symm ≪≫ (a ⊗ᵢ b) := by
  have hk : (ModularCurves.monoidalTensorObjIso P Q).hom ≫ (bundleTensorIso a b).hom =
      (a.hom ⊗ₘ b.hom) ≫ (ModularCurves.monoidalTensorObjIso P' Q').hom :=
    ModularCurves.cartierMonoidalTensorObjIso_hom_natural a b
  have hi : ModularCurves.monoidalTensorObjIso P Q ≪≫ bundleTensorIso a b =
      (a ⊗ᵢ b) ≪≫ ModularCurves.monoidalTensorObjIso P' Q' := Iso.ext hk
  exact cancelIsoSquare _ _ _ _ hi

/-- Actual whole original module isos preserve the genuine entire power-frame construction. -/
theorem powerFrame_naturality {X : Scheme.{u}} {P Q : X.Modules}
    (a : P ≅ Q) (e : Q ≅ unitObj X) (n : ℕ) :
    BundleTensorPowerPullback.powerIso a n ≪≫ powerFrame e n = powerFrame (a ≪≫ e) n := by
  induction n with
  | zero => exact Iso.refl_trans _
  | succ n ih =>
    have hn := explicitTensorIso_naturality (BundleTensorPowerPullback.powerIso a n) a
    have ht := tensorFrame_naturality (BundleTensorPowerPullback.powerIso a n) a (powerFrame e n) e
    have hc := congrArg (fun E => E ≪≫ tensorFrame (powerFrame e n) e) hn
    have ha := Iso.trans_assoc (ModularCurves.monoidalTensorObjIso (bundleTensorPower P n) P).symm
      (BundleTensorPowerPullback.powerIso a n ⊗ᵢ a) (tensorFrame (powerFrame e n) e)
    have hh := congrArg (fun E => (ModularCurves.monoidalTensorObjIso (bundleTensorPower P n) P).symm ≪≫ E) ht
    have hi := congrArg (fun E => (ModularCurves.monoidalTensorObjIso (bundleTensorPower P n) P).symm ≪≫
      tensorFrame E (a ≪≫ e)) ih
    exact (Iso.trans_assoc (bundleTensorIso (BundleTensorPowerPullback.powerIso a n) a)
      (ModularCurves.monoidalTensorObjIso (bundleTensorPower Q n) Q).symm
      (tensorFrame (powerFrame e n) e)).symm.trans (hc.trans (ha.trans (hh.trans hi)))

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

/-- On the ACTUAL original residue morphism these are exactly the genuine native generic power frames. -/
theorem pullbackPowerFrame_generic {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} {p : X ⟶ Spec (.of R)}
    (y : Berkovich.RelativeSchemeValuedPoint v p) {M : X.Modules}
    (e : Berkovich.RelativeSchemeValuedPoint.genericLineModule y M ≅ unitObj (Spec (X.residueField y.1.point)))
    (n : ℕ) :
    pullbackPowerFrame (X.fromSpecResidueField y.1.point) e n =
      Berkovich.SchemeLinePowerFrameNorms.genericPowerFrame y e n := by
  induction n with
  | zero => exact pullbackPowerFrame_zero _ _
  | succ n ih =>
    have hr := pullbackPowerFrame_succ (X.fromSpecResidueField y.1.point) e n
    have hp := congrArg (fun E =>
      (pullback (X.fromSpecResidueField y.1.point)).mapIso
        (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).symm ≪≫
          (Functor.Monoidal.μIso (pullback (X.fromSpecResidueField y.1.point)) (bundleTensorPower M n) M).symm ≪≫
            tensorFrame E e) ih
    exact hr.trans hp

end EnvelopeProperty.SchemePulledPowerFrames
