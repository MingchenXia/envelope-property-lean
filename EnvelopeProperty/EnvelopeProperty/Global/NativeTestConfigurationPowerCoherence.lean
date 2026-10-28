import EnvelopeProperty.Global.NativeTestConfigurationLaurentSections
import EnvelopeProperty.AlgGeom.BundleTensorPowerPullbackCoherence

/-! # Actual original TC product line-power and pulled-frame coherence -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory CartesianMonoidalCategory
open Scheme.Modules
noncomputable section
universe u

namespace EnvelopeProperty.NativeTestConfigurationPowerCoherence
open CanonicalGeometry BundleTensorPowerPullback BundleTensorPowerPullbackCoherence

private theorem isoSquare_trans {C : Type*} [Category C]
    {A B D A' B' D' : C} (a : A ≅ B) (b : B ≅ D)
    (p : A ≅ A') (q : B ≅ B') (r : D ≅ D') (a' : A' ≅ B') (b' : B' ≅ D')
    (ha : a ≪≫ q = p ≪≫ a') (hb : b ≪≫ r = q ≪≫ b') :
    (a ≪≫ b) ≪≫ r = p ≪≫ (a' ≪≫ b') := by
  calc
    _ = a ≪≫ (b ≪≫ r) := Iso.trans_assoc _ _ _
    _ = a ≪≫ (q ≪≫ b') := by rw [hb]
    _ = (a ≪≫ q) ≪≫ b' := (Iso.trans_assoc _ _ _).symm
    _ = (p ≪≫ a') ≪≫ b' := by rw [ha]
    _ = _ := Iso.trans_assoc _ _ _

private theorem isoSquare_inverse {C : Type*} [Category C]
    {A B A' B' : C} (a : A ≅ B) (p : A ≅ A') (q : B ≅ B') (a' : A' ≅ B')
    (h : a ≪≫ q = p ≪≫ a') : a.symm ≪≫ p = q ≪≫ a'.symm := by
  have hh := congrArg (fun E => a.symm ≪≫ E ≪≫ a'.symm) h
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id, Iso.trans_refl] using hh.symm

private theorem cancelIsoRight {C : Type*} [Category C] {A B D : C}
    (a : A ≅ B) (b : B ≅ D) (c : A ≅ D) (h : a ≪≫ b = c) : a = c ≪≫ b.symm := by
  have hh := congrArg (fun E => E ≪≫ b.symm) h
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hh

private theorem mappedConjugateSquare {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B A' B' : C} {P Q : D}
    (a : A ≅ A') (e : A' ≅ B') (b : B ≅ B') (p : F.obj A' ≅ P) (q : F.obj B' ≅ Q)
    (v : P ≅ Q) (h : F.mapIso e ≪≫ q = p ≪≫ v) :
    F.mapIso (a ≪≫ e ≪≫ b.symm) ≪≫ (F.mapIso b ≪≫ q) = (F.mapIso a ≪≫ p) ≪≫ v := by
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [h]

private theorem composeIsoSquareWithFrame {C : Type*} [Category C]
    {A B D E F : C} (a : A ≅ B) (q : B ≅ D) (p : A ≅ E) (d : E ≅ D)
    (e : D ≅ F) (f : E ≅ F) (h : a ≪≫ q = p ≪≫ d) (hf : d ≪≫ e = f) :
    a ≪≫ q ≪≫ e = p ≪≫ f := by
  exact (Iso.trans_assoc a q e).symm.trans
    ((congrArg (fun E => E ≪≫ e) h).trans
      ((Iso.trans_assoc p d e).trans (congrArg (fun E => p ≪≫ E) hf)))

end EnvelopeProperty.NativeTestConfigurationPowerCoherence

namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open CanonicalGeometry BundleTensorPowerPullback BundleTensorPowerPullbackCoherence
open NativeTestConfigurationPowerCoherence
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : TestConfiguration k X) (M : C.total.Modules) (L : X.left.Modules)
    (α : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)

/-- Original action/fibre data give the actual WHOLE product line iso before taking powers. -/
def productTotalLineIso :
    (pullback C.productTotalMap).obj M ≅
      (pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).obj L :=
  ((pullbackComp C.unitOpenIso.inv.left C.unitOpenInclusion.left).app M).symm ≪≫
    (pullback C.unitOpenIso.inv.left).mapIso (C.unitOpenLineIso M L α e₁) ≪≫
      (pullbackComp C.unitOpenIso.inv.left C.unitOpenOriginalProjection.left).app L ≪≫
        (pullbackCongr C.unitOpenIso_inv_originalProjection).app L

/-- The LITERAL original product power iso is the canonical power of the ORIGINAL product line iso. -/
theorem productTotalLinePowerIso_coherence (n : ℕ) :
    C.productTotalLinePowerIso M L α e₁ n =
      pullbackIso C.productTotalMap M n ≪≫
        powerIso (C.productTotalLineIso M L α e₁) n ≪≫
          (pullbackIso (fst X (ProjBerk.nativeMultiplicativeGroup k)).left L n).symm := by
  let a := C.unitOpenIso.inv.left
  let b := C.unitOpenInclusion.left
  let c := C.unitOpenOriginalProjection.left
  let e := C.unitOpenLineIso M L α e₁
  let cm := (pullbackComp a b).app M
  let cl := (pullbackComp a c).app L
  let h := C.unitOpenIso_inv_originalProjection
  let d := (pullbackCongr h).app L
  let pm := (pullback a).mapIso (pullbackIso b M n) ≪≫ pullbackIso a ((pullback b).obj M) n
  let pl := (pullback a).mapIso (pullbackIso c L n) ≪≫ pullbackIso a ((pullback c).obj L) n
  have ha₀ := isoSquare_inverse ((pullbackComp a b).app (bundleTensorPower M n)) pm
    (pullbackIso (a ≫ b) M n) (powerIso cm n) (pullbackIso_comp a b M n).symm
  have ha := ha₀.trans (congrArg (fun E => pullbackIso (a ≫ b) M n ≪≫ E) (powerIso_symm cm n).symm)
  have hb := mappedConjugateSquare (pullback a) (pullbackIso b M n) (powerIso e n)
    (pullbackIso c L n) (pullbackIso a ((pullback b).obj M) n)
    (pullbackIso a ((pullback c).obj L) n) (powerIso ((pullback a).mapIso e) n)
    (pullbackIso_naturality a e n)
  have hc := (pullbackIso_comp a c L n).symm
  have hd := pullbackIso_congr h L n
  have hcd := isoSquare_trans ((pullbackComp a c).app (bundleTensorPower L n))
    ((pullbackCongr h).app (bundleTensorPower L n)) pl
    (pullbackIso (a ≫ c) L n) (pullbackIso (fst X (ProjBerk.nativeMultiplicativeGroup k)).left L n)
    (powerIso cl n) (powerIso d n) hc hd
  have hbcd := isoSquare_trans ((pullback a).mapIso (C.unitOpenLinePowerIso M L α e₁ n))
    (((pullbackComp a c).app (bundleTensorPower L n)) ≪≫ ((pullbackCongr h).app (bundleTensorPower L n)))
    pm pl (pullbackIso (fst X (ProjBerk.nativeMultiplicativeGroup k)).left L n)
    (powerIso ((pullback a).mapIso e) n) (powerIso cl n ≪≫ powerIso d n) hb hcd
  have habcd := isoSquare_trans (((pullbackComp a b).app (bundleTensorPower M n)).symm)
    (((pullback a).mapIso (C.unitOpenLinePowerIso M L α e₁ n)) ≪≫
      ((pullbackComp a c).app (bundleTensorPower L n)) ≪≫ ((pullbackCongr h).app (bundleTensorPower L n)))
    (pullbackIso (a ≫ b) M n) pm (pullbackIso (fst X (ProjBerk.nativeMultiplicativeGroup k)).left L n)
    (powerIso cm.symm n) (powerIso ((pullback a).mapIso e) n ≪≫ powerIso cl n ≪≫ powerIso d n) ha hbcd
  have hp₃ := powerIso_trans cl d n
  have hp₂ := (powerIso_trans ((pullback a).mapIso e) (cl ≪≫ d) n).trans
    (congrArg (fun E => powerIso ((pullback a).mapIso e) n ≪≫ E) hp₃)
  have hp₁ := (powerIso_trans cm.symm (((pullback a).mapIso e) ≪≫ cl ≪≫ d) n).trans
    (congrArg (fun E => powerIso cm.symm n ≪≫ E) hp₂)
  have hfinal := habcd.trans (congrArg (fun E => pullbackIso (a ≫ b) M n ≪≫ E) hp₁.symm)
  exact (cancelIsoRight _ _ _ hfinal).trans (Iso.trans_assoc _ _ _)

/-- On ANY actual pulled frame domain, literal original product powers preserve the derived WHOLE power frames. -/
theorem productTotalLinePowerIso_pulledFrame {W : Scheme.{u}}
    (t : W ⟶ (X ⊗ ProjBerk.nativeMultiplicativeGroup k).left)
    (e : (pullback t).obj ((pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).obj L) ≅ unitObj W)
    (n : ℕ) :
    (pullback t).mapIso (C.productTotalLinePowerIso M L α e₁ n) ≪≫
      (pullback t).mapIso (pullbackIso (fst X (ProjBerk.nativeMultiplicativeGroup k)).left L n) ≪≫
        SchemePulledPowerFrames.pullbackPowerFrame t e n =
      (pullback t).mapIso (pullbackIso C.productTotalMap M n) ≪≫
        SchemePulledPowerFrames.pullbackPowerFrame t
          ((pullback t).mapIso (C.productTotalLineIso M L α e₁) ≪≫ e) n := by
  have hn := pullbackIso_naturality t (C.productTotalLineIso M L α e₁) n
  have hs := mappedConjugateSquare (pullback t)
    (pullbackIso C.productTotalMap M n) (powerIso (C.productTotalLineIso M L α e₁) n)
    (pullbackIso (fst X (ProjBerk.nativeMultiplicativeGroup k)).left L n)
    (pullbackIso t ((pullback C.productTotalMap).obj M) n)
    (pullbackIso t ((pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).obj L) n)
    (powerIso ((pullback t).mapIso (C.productTotalLineIso M L α e₁)) n) hn
  have hc := congrArg (fun E => (pullback t).mapIso E ≪≫
    ((pullback t).mapIso (pullbackIso (fst X (ProjBerk.nativeMultiplicativeGroup k)).left L n) ≪≫
      pullbackIso t ((pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).obj L) n))
    (C.productTotalLinePowerIso_coherence M L α e₁ n)
  have h := composeIsoSquareWithFrame _ _ _ _ (SchemeTensorPowerFrames.powerFrame e n) _
    (hc.trans hs) (SchemePulledPowerFrames.powerFrame_naturality
      ((pullback t).mapIso (C.productTotalLineIso M L α e₁)) e n)
  simpa only [Iso.trans_assoc, SchemePulledPowerFrames.pullbackPowerFrame] using h

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
