import EnvelopeProperty.AlgGeom.BundleTensorPowerPullbackCoherence
import EnvelopeProperty.Berkovich.SchemeFramedSectionPullback

/-! # Genuine induced native residue frames commute with actual original powers -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeInducedPowerFrames
open CanonicalGeometry BundleTensorPowerPullback BundleTensorPowerPullbackCoherence
open SchemePulledPowerFrames SchemeTensorPowerFrames SchemeFramedSectionPullback

private theorem attachSquareFrame {C : Type*} [Category C]
    {A B D E F : C} (a : A ≅ B) (b : B ≅ D) (p : A ≅ E) (d : E ≅ D)
    (e : D ≅ F) (f : E ≅ F) (h : a ≪≫ b = p ≪≫ d) (hf : d ≪≫ e = f) :
    a ≪≫ b ≪≫ e = p ≪≫ f := by
  exact (Iso.trans_assoc a b e).symm.trans
    ((congrArg (fun E => E ≪≫ e) h).trans
      ((Iso.trans_assoc p d e).trans (congrArg (fun E => p ≪≫ E) hf)))

private theorem cancelLeftFrame {C : Type*} [Category C]
    {A B D : C} (a : A ≅ B) (b : A ≅ D) (c : B ≅ D) (h : b = a ≪≫ c) :
    a.symm ≪≫ b = c := by
  have hh := congrArg (fun E => a.symm ≪≫ E) h
  simpa only [Iso.symm_self_id_assoc] using hh

/-- Any actual pulled-power frame is natural in the ENTIRE original preceding module iso. -/
theorem pullbackPowerFrame_naturality {X Y : Scheme.{u}} (t : Y ⟶ X)
    {M N : X.Modules} (a : M ≅ N) (e : (pullback t).obj N ≅ unitObj Y) (n : ℕ) :
    (pullback t).mapIso (powerIso a n) ≪≫ pullbackPowerFrame t e n =
      pullbackPowerFrame t ((pullback t).mapIso a ≪≫ e) n :=
  attachSquareFrame _ _ _ _ _ _ (pullbackIso_naturality t a n)
    (powerFrame_naturality ((pullback t).mapIso a) e n)

/-- Actual factor power frames retain the genuine native composition comparison as a WHOLE iso. -/
theorem factorPowerFrame_comp {W Y Z V : Scheme.{u}} (t : W ⟶ Y) (g : Y ⟶ Z)
    (q : W ⟶ V) (b : V ⟶ Z) (h : q ≫ b = t ≫ g) {M : Z.Modules}
    (e : (pullback b).obj M ≅ unitObj V) (n : ℕ) :
    (pullbackComp t g).app (bundleTensorPower M n) ≪≫
        frameViaFactor q b (t ≫ g) h (pullbackPowerFrame b e n) =
      (pullback t).mapIso (pullbackIso g M n) ≪≫
        pullbackPowerFrame t ((pullbackComp t g).app M ≪≫ frameViaFactor q b (t ≫ g) h e) n := by
  let E := frameViaFactor q b (t ≫ g) h e
  have hf := congrArg (fun F => (pullbackComp t g).app (bundleTensorPower M n) ≪≫ F)
    (pullbackPowerFrame_factor q b (t ≫ g) h e n)
  have hc := attachSquareFrame ((pullbackComp t g).app (bundleTensorPower M n))
    (pullbackIso (t ≫ g) M n)
    ((pullback t).mapIso (pullbackIso g M n) ≪≫ pullbackIso t ((pullback g).obj M) n)
    (powerIso ((pullbackComp t g).app M) n) (powerFrame E n) _
    (pullbackIso_comp t g M n).symm (powerFrame_naturality ((pullbackComp t g).app M) E n)
  exact hf.trans (hc.trans (Iso.trans_assoc _ _ _))

/-- Postcomposition of actual line isos gives the TRUE inverse native pullback on induced frames. -/
theorem inducedResidueFrame_postcomp {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    {M : Z.Modules} {N P : Y.Modules} (α : (pullback g).obj M ≅ N) (β : N ≅ P)
    (y : SchemeValuedPoint Y)
    (e : (pullback (Z.fromSpecResidueField (g y.point))).obj M ≅
      unitObj (Spec (.of (Z.residueField (g y.point))))) :
    inducedResidueFrame g (α ≪≫ β) y e =
      ((pullback (Y.fromSpecResidueField y.point)).mapIso β).symm ≪≫ inducedResidueFrame g α y e := by
  simp only [inducedResidueFrame, Functor.mapIso_trans, Iso.trans_symm, Iso.trans_assoc]

/-- The actual native residue-field square transports ALL canonical original power frames exactly. -/
theorem inducedResidueFrame_pullbackPower {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    {M : Z.Modules} (y : SchemeValuedPoint Y)
    (e : (pullback (Z.fromSpecResidueField (g y.point))).obj M ≅
      unitObj (Spec (.of (Z.residueField (g y.point))))) (n : ℕ) :
    inducedResidueFrame g (pullbackIso g M n) y
      (pullbackPowerFrame (Z.fromSpecResidueField (g y.point)) e n) =
        pullbackPowerFrame (Y.fromSpecResidueField y.point)
          (inducedResidueFrame g (Iso.refl ((pullback g).obj M)) y e) n := by
  let t := Y.fromSpecResidueField y.point
  let b := Z.fromSpecResidueField (g y.point)
  let q := Spec.map (g.residueFieldMap y.point)
  let h := g.SpecMap_residueFieldMap_fromSpecResidueField y.point
  let E := (pullbackComp t g).app M ≪≫ frameViaFactor q b (t ≫ g) h e
  have hf := factorPowerFrame_comp t g q b h e n
  have hc := cancelLeftFrame ((pullback t).mapIso (pullbackIso g M n)) _ _ hf
  have hn := inducedResidueFrame_eq g (pullbackIso g M n) y (pullbackPowerFrame b e n)
  have hb := inducedResidueFrame_eq g (Iso.refl ((pullback g).obj M)) y e
  have hb' : inducedResidueFrame g (Iso.refl ((pullback g).obj M)) y e = E := by
    simpa only [Functor.mapIso_refl, Iso.refl_symm, Iso.refl_trans] using hb
  have he := congrArg (fun F => pullbackPowerFrame t F n) hb'.symm
  exact hn.trans (hc.trans he)

/-- The induced ACTUAL native residue frame of a canonical original power is the SAME degree-one induced frame raised to that power. -/
theorem inducedResidueFrame_power {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    {M : Z.Modules} {N : Y.Modules} (α : (pullback g).obj M ≅ N) (y : SchemeValuedPoint Y)
    (e : (pullback (Z.fromSpecResidueField (g y.point))).obj M ≅
      unitObj (Spec (.of (Z.residueField (g y.point))))) (n : ℕ) :
    inducedResidueFrame g (pullbackIso g M n ≪≫ powerIso α n) y
      (pullbackPowerFrame (Z.fromSpecResidueField (g y.point)) e n) =
        pullbackPowerFrame (Y.fromSpecResidueField y.point) (inducedResidueFrame g α y e) n := by
  let t := Y.fromSpecResidueField y.point
  let E := inducedResidueFrame g (Iso.refl ((pullback g).obj M)) y e
  have hp := inducedResidueFrame_postcomp g (pullbackIso g M n) (powerIso α n) y
    (pullbackPowerFrame (Z.fromSpecResidueField (g y.point)) e n)
  have hn := congrArg (fun F => ((pullback t).mapIso (powerIso α n)).symm ≪≫ F)
    (inducedResidueFrame_pullbackPower g y e n)
  have hi := (congrArg (pullback t).mapIso (powerIso_symm α n)).trans
    ((pullback t).mapIso_symm (powerIso α n))
  have ht := congrArg (fun F => F ≪≫ pullbackPowerFrame t E n) hi.symm
  have hf := pullbackPowerFrame_naturality t α.symm E n
  have hb : (pullback t).mapIso α.symm ≪≫ E = inducedResidueFrame g α y e := by
    simp only [E, inducedResidueFrame, Functor.mapIso_refl, Iso.refl_symm, Iso.refl_trans,
      Functor.mapIso_symm]
    rfl
  have he := congrArg (fun F => pullbackPowerFrame t F n) hb
  exact hp.trans (hn.trans (ht.trans (hf.trans he)))

/-- Actual normalized target pullback powers retain the SAME canonical degree-one induced native frame. -/
theorem inducedResidueFrame_normalizedPower {Y Z X : Scheme.{u}} (g : Y ⟶ Z) (f : Y ⟶ X)
    {M : Z.Modules} {L : X.Modules} (α : (pullback g).obj M ≅ (pullback f).obj L)
    (y : SchemeValuedPoint Y)
    (e : (pullback (Z.fromSpecResidueField (g y.point))).obj M ≅
      unitObj (Spec (.of (Z.residueField (g y.point))))) (n : ℕ) :
    inducedResidueFrame g (pullbackIso g M n ≪≫ powerIso α n ≪≫ (pullbackIso f L n).symm) y
      (pullbackPowerFrame (Z.fromSpecResidueField (g y.point)) e n) =
        (pullback (Y.fromSpecResidueField y.point)).mapIso (pullbackIso f L n) ≪≫
          pullbackPowerFrame (Y.fromSpecResidueField y.point) (inducedResidueFrame g α y e) n := by
  have hp := inducedResidueFrame_postcomp g (pullbackIso g M n ≪≫ powerIso α n)
    (pullbackIso f L n).symm y (pullbackPowerFrame (Z.fromSpecResidueField (g y.point)) e n)
  have hn := congrArg (fun F => ((pullback (Y.fromSpecResidueField y.point)).mapIso (pullbackIso f L n).symm).symm ≪≫ F)
    (inducedResidueFrame_power g α y e n)
  have hi := congrArg (fun F => F.symm ≪≫ pullbackPowerFrame (Y.fromSpecResidueField y.point)
    (inducedResidueFrame g α y e) n)
    ((pullback (Y.fromSpecResidueField y.point)).mapIso_symm (pullbackIso f L n))
  have hleft := congrArg (fun F => inducedResidueFrame g F y
    (pullbackPowerFrame (Z.fromSpecResidueField (g y.point)) e n))
    (Iso.trans_assoc (pullbackIso g M n) (powerIso α n) (pullbackIso f L n).symm).symm
  exact hleft.trans (hp.trans (hn.trans hi))

end EnvelopeProperty.Berkovich.SchemeInducedPowerFrames
