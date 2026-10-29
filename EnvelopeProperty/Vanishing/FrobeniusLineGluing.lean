import EnvelopeProperty.Vanishing.FrobeniusLineFrameTransitions
import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormula

/-! # Local Frobenius line comparisons and their actual factor compatibility -/

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.FrobeniusLineComparison

open Cartier CanonicalGeometry FrobeniusLineCore
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]

/-- An original frame over a genuine scheme morphism gives a frame of
the original absolute-Frobenius pullback, via the actual naturality square. -/
def frobeniusFrame (s : Y ⟶ Spec (.of k)) (g : Y ⟶ X) {L : X.Modules}
    (e : (pullback g).obj L ≅ unitObj Y) :
    (pullback g).obj ((pullback (SchemeFrobenius.map f p)).obj L) ≅ unitObj Y :=
  (pullbackComp g (SchemeFrobenius.map f p)).app L ≪≫
    frameViaFactor (SchemeFrobenius.map s p) g (g ≫ SchemeFrobenius.map f p)
      (SchemeFrobenius.naturality s p f g) e

/-- The square prefix is independent of the frame; the remaining map is
the actual pulled whole frame on the source scheme. -/
theorem frobeniusFrame_eq (s : Y ⟶ Spec (.of k)) (g : Y ⟶ X) {L : X.Modules}
    (e : (pullback g).obj L ≅ unitObj Y) :
    frobeniusFrame f p s g e =
      (pullbackSquareIso g (SchemeFrobenius.map f p) (SchemeFrobenius.map s p) g
        (SchemeFrobenius.naturality s p f g).symm).app L ≪≫ pulledFrame s p e := by
  apply Iso.ext
  simp only [frobeniusFrame, frameViaFactor, frameFactorIso, pulledFrame,
    pullbackSquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Functor.mapIso_hom, NatTrans.comp_app, Iso.app_hom, Iso.app_inv, Category.assoc]
  have hc := congrArg (fun q => q.app L)
    (pullbackCongr_inv (SchemeFrobenius.naturality s p f g))
  simpa only [Iso.app_hom, Iso.app_inv] using
    congrArg (fun q => (pullbackComp g (SchemeFrobenius.map f p)).hom.app L ≫ q ≫
      (pullbackComp (SchemeFrobenius.map s p) g).inv.app L ≫
      (pullback (SchemeFrobenius.map s p)).map e.hom ≫
      (pullbackUnitIso (SchemeFrobenius.map s p)).hom) hc

/-- The actual Frobenius local frame is compatible with every genuine
factorization, including the original inclusions of overlapping opens. -/
theorem frobeniusFrame_factor (s : Y ⟶ Spec (.of k)) (t : Z ⟶ Spec (.of k))
    (j : Z ⟶ Y) (g : Y ⟶ X) (h : Z ⟶ X) (hj : j ≫ g = h)
    {L : X.Modules} (e : (pullback g).obj L ≅ unitObj Y) :
    frameViaFactor j g h hj (frobeniusFrame f p s g e) =
      frobeniusFrame f p t h (frameViaFactor j g h hj e) := by
  let FY := SchemeFrobenius.map s p
  let FZ := SchemeFrobenius.map t p
  let FX := SchemeFrobenius.map f p
  have hY : FY ≫ g = g ≫ FX := SchemeFrobenius.naturality s p f g
  have hZ : FZ ≫ h = h ≫ FX := SchemeFrobenius.naturality t p f h
  have hJ : FZ ≫ j = j ≫ FY := SchemeFrobenius.naturality t p s j
  have hjX : j ≫ (g ≫ FX) = h ≫ FX := by rw [← Category.assoc, hj]
  have hc := frameViaFactor_pullbackComp j g h hj FX
    (frameViaFactor FY g (g ≫ FX) hY e)
  change frameViaFactor j g h hj
      ((pullbackComp g FX).app L ≪≫ frameViaFactor FY g (g ≫ FX) hY e) = _
  rw [hc]
  have hleft := frameViaFactor_comp j FY g (g ≫ FX) hY (h ≫ FX) hjX e
  have hright := frameViaFactor_comp FZ j g h hj (h ≫ FX) hZ e
  have hmiddle :
      frameViaFactor (j ≫ FY) g (h ≫ FX)
        (by rw [Category.assoc, hY]; exact hjX) e =
      frameViaFactor (FZ ≫ j) g (h ≫ FX)
        (by rw [Category.assoc, hj]; exact hZ) e := by
    congr 1
    exact hJ.symm
  exact congrArg (fun E => (pullbackComp h FX).app L ≪≫ E)
    (hleft.trans (hmiddle.trans hright.symm))

/-- The actual local comparison at an original frame, with both original
whole pullback objects retained. -/
def localComparison (s : Y ⟶ Spec (.of k)) (g : Y ⟶ X) {L : X.Modules}
    (e : (pullback g).obj L ≅ unitObj Y) :
    (pullback g).obj ((pullback (SchemeFrobenius.map f p)).obj L) ≅
      (pullback g).obj (bundleTensorPower L p) :=
  frobeniusFrame f p s g e ≪≫ (pullbackPowerFrame g e p).symm

/-- Equality of the two derived pth-power transition functions makes the
local comparison independent of the original whole local frame. -/
theorem localComparison_eq (s : Y ⟶ Spec (.of k)) (g : Y ⟶ X) {L : X.Modules}
    (e e' : (pullback g).obj L ≅ unitObj Y) :
    localComparison f p s g e = localComparison f p s g e' := by
  simp only [localComparison, frobeniusFrame_eq, pullbackPowerFrame,
    Iso.trans_symm, Iso.trans_assoc]
  exact congrArg
    (fun E =>
      (pullbackSquareIso g (SchemeFrobenius.map f p) (SchemeFrobenius.map s p) g
        (SchemeFrobenius.naturality s p f g).symm).app L ≪≫ E ≪≫
        (BundleTensorPowerPullback.pullbackIso g L p).symm)
    (frameComparison_eq s p e e')

private theorem commonTransition_of_comparison_eq
    {C : Type*} [Category C] {A B T : C}
    (e e' : A ≅ T) (g g' : B ≅ T) (h : e ≪≫ g.symm = e' ≪≫ g'.symm) :
    ∃ c : T ⟶ T, e.hom = e'.hom ≫ c ∧ g.hom = g'.hom ≫ c := by
  refine ⟨e'.inv ≫ e.hom, by simp, ?_⟩
  have h' := congrArg (fun q : A ⟶ B => e'.inv ≫ q ≫ g.hom) (congrArg Iso.hom h)
  have hc : e'.inv ≫ e.hom = g'.inv ≫ g.hom := by
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc] using h'
  rw [hc]
  simp

/-- The actual Frobenius pullback of any original invertible module is its
original pth tensor power.  Whole original local comparisons are glued
after deriving both frame transitions and their restriction compatibility. -/
def absolutePowerIso (L : X.Modules) (hL : IsInvertible L) :
    (pullback (SchemeFrobenius.map f p)).obj L ≅ bundleTensorPower L p := by
  classical
  let I : Type u := Classical.choose hL
  let U : I → X.Opens := Classical.choose (Classical.choose_spec hL)
  have hU : TopologicalSpace.IsOpenCover U :=
    (Classical.choose_spec (Classical.choose_spec hL)).1
  let E (i : I) : (pullback (U i).ι).obj L ≅ unitObj (U i).toScheme :=
    Classical.choice ((Classical.choose_spec (Classical.choose_spec hL)).2 i)
  let M := (pullback (SchemeFrobenius.map f p)).obj L
  let N := bundleTensorPower L p
  let EM (i : I) := frobeniusFrame f p ((U i).ι ≫ f) (U i).ι (E i)
  let EN (i : I) := pullbackPowerFrame (U i).ι (E i) p
  have hcover : ∀ x : X, ∃ i, x ∈ U i := by
    intro x
    apply TopologicalSpace.Opens.mem_iSup.mp
    rw [show (⨆ i, U i) = ⊤ from hU]
    trivial
  refine SchemeModuleFrameGluing.glueOfFrames M N U hcover
    (fun i => restrictIsoOfPullbackIso M (U i) (EM i))
    (fun i => restrictIsoOfPullbackIso N (U i) (EN i)) ?_
  intro i j
  let W := U i ⊓ U j
  let a := X.homOfLE (inf_le_left : W ≤ U i)
  let b := X.homOfLE (inf_le_right : W ≤ U j)
  let Ei := frameViaFactor a (U i).ι W.ι (X.homOfLE_ι _) (E i)
  let Ej := frameViaFactor b (U j).ι W.ι (X.homOfLE_ι _) (E j)
  let Mi := frobeniusFrame f p (W.ι ≫ f) W.ι Ei
  let Mj := frobeniusFrame f p (W.ι ≫ f) W.ι Ej
  let Ni := pullbackPowerFrame W.ι Ei p
  let Nj := pullbackPowerFrame W.ι Ej p
  have hcomparison : Mi ≪≫ Ni.symm = Mj ≪≫ Nj.symm :=
    localComparison_eq f p (W.ι ≫ f) W.ι Ei Ej
  obtain ⟨c, hcM, hcN⟩ := commonTransition_of_comparison_eq Mi Mj Ni Nj hcomparison
  have hMi : restrictOpenTrivialization (inf_le_left : W ≤ U i)
      (restrictIsoOfPullbackIso M (U i) (EM i)) =
      restrictIsoOfPullbackIso M W Mi := by
    rw [FrobeniusLineCore.restrictIso_frameViaFactor]
    congr 1
    exact frobeniusFrame_factor f p ((U i).ι ≫ f) (W.ι ≫ f)
      a (U i).ι W.ι (X.homOfLE_ι _) (E i)
  have hMj : restrictOpenTrivialization (inf_le_right : W ≤ U j)
      (restrictIsoOfPullbackIso M (U j) (EM j)) =
      restrictIsoOfPullbackIso M W Mj := by
    rw [FrobeniusLineCore.restrictIso_frameViaFactor]
    congr 1
    exact frobeniusFrame_factor f p ((U j).ι ≫ f) (W.ι ≫ f)
      b (U j).ι W.ι (X.homOfLE_ι _) (E j)
  have hNi : restrictOpenTrivialization (inf_le_left : W ≤ U i)
      (restrictIsoOfPullbackIso N (U i) (EN i)) =
      restrictIsoOfPullbackIso N W Ni := by
    rw [FrobeniusLineCore.restrictIso_frameViaFactor]
    congr 1
    exact pullbackPowerFrame_factor a (U i).ι W.ι (X.homOfLE_ι _) (E i) p
  have hNj : restrictOpenTrivialization (inf_le_right : W ≤ U j)
      (restrictIsoOfPullbackIso N (U j) (EN j)) =
      restrictIsoOfPullbackIso N W Nj := by
    rw [FrobeniusLineCore.restrictIso_frameViaFactor]
    congr 1
    exact pullbackPowerFrame_factor b (U j).ι W.ι (X.homOfLE_ι _) (E j) p
  refine ⟨c, ?_, ?_⟩
  · rw [hMi, hMj]
    simpa only [restrictIsoOfPullbackIso, Iso.trans_hom, Category.assoc] using
      congrArg (fun q => ((restrictFunctorIsoPullback W.ι).app M).hom ≫ q) hcM
  · rw [hNi, hNj]
    simpa only [restrictIsoOfPullbackIso, Iso.trans_hom, Category.assoc] using
      congrArg (fun q => ((restrictFunctorIsoPullback W.ι).app N).hom ≫ q) hcN

/-- The original relative Frobenius and original twisted line satisfy
the genuine global pth-power comparison. -/
def relativePowerIso (L : X.Modules) (hL : IsInvertible L) :
    (pullback (SchemeRelativeFrobenius.map p f)).obj (twistedLine f p L) ≅
      bundleTensorPower L p :=
  relativePullbackIso f p L ≪≫ absolutePowerIso f p L hL

/-- Every original twisted tensor power pulls back to the actual amplified
power on the original scheme, with the product exponent retained. -/
def relativeTensorPowerIso (L : X.Modules) (hL : IsInvertible L) (m : ℕ) :
    (pullback (SchemeRelativeFrobenius.map p f)).obj
      (bundleTensorPower (twistedLine f p L) m) ≅ bundleTensorPower L (p * m) :=
  relativePullbackPowerIso f p L m ≪≫
    BundleTensorPowerPullback.powerIso (absolutePowerIso f p L hL) m ≪≫
      BundleTensorPowerPullback.powerMulIso L p m

/-- The genuine projection formula identifies each twisted pushed module
with the pushforward of the same original module at amplified exponent.
This is a termwise module statement; no arbitrary tensor differential on
the original de Rham complex is asserted. -/
def moduleProjectionIso (L : X.Modules) (hL : IsInvertible L)
    (M : X.Modules) (m : ℕ) :
    ((pushforward (SchemeRelativeFrobenius.map p f)).obj M ⊗
      bundleTensorPower (twistedLine f p L) m :
        (SchemeRelativeFrobenius.twist p f).Modules) ≅
      (pushforward (SchemeRelativeFrobenius.map p f)).obj
        (bundleTensorPower L (p * m) ⊗ M : X.Modules) := by
  have htwist : IsInvertible (twistedLine f p L) :=
    hL.pullback (Limits.pullback.fst f (SchemeRelativeFrobenius.baseMap (k := k) p))
  have hpower : IsInvertible (bundleTensorPower (twistedLine f p L) m) :=
    TensorPowerBaseIdealGrading.tensorPower_isInvertible htwist m
  exact SchemeLineProjectionFormula.lineProjectionFormulaObj
    (SchemeRelativeFrobenius.map p f) (bundleTensorPower (twistedLine f p L) m) hpower M ≪≫
      (pushforward (SchemeRelativeFrobenius.map p f)).mapIso
        ((Iso.refl M ⊗ᵢ relativeTensorPowerIso f p L hL m) ≪≫
          β_ M (bundleTensorPower L (p * m)))

end EnvelopeProperty.Vanishing.FrobeniusLineComparison
