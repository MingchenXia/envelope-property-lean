import EnvelopeProperty.AlgGeom.SchemePulledPowerFrames
import EnvelopeProperty.AlgGeom.CartierTensorPullbackNaturality

/-! # Canonical whole tensor-power pullback coherence -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.BundleTensorPowerPullbackCoherence
open CanonicalGeometry BundleTensorPowerPullback
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) : (pullback f).Monoidal :=
  Scheme.Modules.pullbackMonoidal f

private theorem tensorIso_trans {C : Type*} [Category C] [MonoidalCategory C]
    {A B C' D E F : C} (a : A ≅ B) (b : C' ≅ D) (c : B ≅ E) (d : D ≅ F) :
    (a ⊗ᵢ b) ≪≫ (c ⊗ᵢ d) = (a ≪≫ c) ⊗ᵢ (b ≪≫ d) := by
  apply Iso.ext
  exact tensorHom_comp_tensorHom _ _ _ _

private theorem tensorIso_refl {C : Type*} [Category C] [MonoidalCategory C] (A B : C) :
    (Iso.refl A ⊗ᵢ Iso.refl B) = Iso.refl (A ⊗ B) := by
  apply Iso.ext
  exact id_tensorHom_id A B

private theorem bundleTensorIso_trans {X : Scheme.{u}} {A B C D E F : X.Modules}
    (a : A ≅ B) (b : C ≅ D) (c : B ≅ E) (d : D ≅ F) :
    bundleTensorIso a b ≪≫ bundleTensorIso c d = bundleTensorIso (a ≪≫ c) (b ≪≫ d) := by
  let G := SheafOfModules.forget X.ringCatSheaf
  let H := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have hm := (H.mapIso_trans (G.mapIso a ⊗ᵢ G.mapIso b) (G.mapIso c ⊗ᵢ G.mapIso d)).symm
  have ht := congrArg H.mapIso (tensorIso_trans (G.mapIso a) (G.mapIso b) (G.mapIso c) (G.mapIso d))
  have he := congrArg (fun E => H.mapIso E) (congrArg₂ (fun E F => E ⊗ᵢ F)
    (G.mapIso_trans a c).symm (G.mapIso_trans b d).symm)
  exact hm.trans (ht.trans he)

private theorem bundleTensorIso_refl {X : Scheme.{u}} (M N : X.Modules) :
    bundleTensorIso (Iso.refl M) (Iso.refl N) = Iso.refl (Scheme.Modules.tensorObj M N) := by
  let G := SheafOfModules.forget X.ringCatSheaf
  let H := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have hg := congrArg₂ (fun E F => E ⊗ᵢ F) (G.mapIso_refl M) (G.mapIso_refl N)
  exact (congrArg H.mapIso (hg.trans (tensorIso_refl _ _))).trans (H.mapIso_refl _)

/-- The genuine whole explicit power of the identity is identity. -/
theorem powerIso_refl {X : Scheme.{u}} (M : X.Modules) (n : ℕ) :
    powerIso (Iso.refl M) n = Iso.refl (bundleTensorPower M n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change bundleTensorIso (powerIso (Iso.refl M) n) (Iso.refl M) = _
    exact (congrArg (fun E => bundleTensorIso E (Iso.refl M)) ih).trans (bundleTensorIso_refl _ _)

/-- Genuine entire power isomorphisms preserve actual composition. -/
theorem powerIso_trans {X : Scheme.{u}} {M N P : X.Modules} (a : M ≅ N) (b : N ≅ P) (n : ℕ) :
    powerIso (a ≪≫ b) n = powerIso a n ≪≫ powerIso b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change bundleTensorIso (powerIso (a ≪≫ b) n) (a ≪≫ b) = _
    exact (congrArg (fun E => bundleTensorIso E (a ≪≫ b)) ih).trans (bundleTensorIso_trans _ _ _ _).symm

/-- The actual power of an inverse is the inverse whole power isomorphism. -/
theorem powerIso_symm {X : Scheme.{u}} {M N : X.Modules} (a : M ≅ N) (n : ℕ) :
    powerIso a.symm n = (powerIso a n).symm := by
  have h := powerIso_trans a a.symm n
  rw [Iso.self_symm_id, powerIso_refl] at h
  have hc := congrArg (fun E => (powerIso a n).symm ≪≫ E) h
  simpa only [Iso.trans_refl, Iso.symm_self_id_assoc] using hc.symm

/-- The native power pullback recursion is the genuine canonical explicit tensor comparison. -/
theorem pullbackIso_succ {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) (n : ℕ) :
    pullbackIso f M (n + 1) =
      canonicalTensorPullbackIso f (bundleTensorPower M n) M ≪≫
        bundleTensorIso (pullbackIso f M n) (Iso.refl ((pullback f).obj M)) := by
  apply Iso.ext
  have hk := ModularCurves.cartierMonoidalTensorObjIso_hom_natural
    (pullbackIso f M n) (Iso.refl ((pullback f).obj M))
  have ht := congrArg (fun q =>
    ((pullback f).mapIso (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).symm).hom ≫
      (Functor.Monoidal.μIso (pullback f) (bundleTensorPower M n) M).inv ≫ q) hk
  exact ht.symm

/-- Genuine whole tensor-power pullback is natural in every actual original module isomorphism. -/
theorem pullbackIso_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} (a : M ≅ N) (n : ℕ) :
    (pullback f).mapIso (powerIso a n) ≪≫ pullbackIso f N n =
      pullbackIso f M n ≪≫ powerIso ((pullback f).mapIso a) n := by
  induction n with
  | zero =>
    change (pullback f).mapIso (Iso.refl _) ≪≫ pullbackUnitIso f = pullbackUnitIso f ≪≫ Iso.refl _
    rw [Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl]
  | succ n ih =>
    have hn := canonicalTensorPullbackIso_natural f (powerIso a n) a
    have ht := bundleTensorIso_trans ((pullback f).mapIso (powerIso a n)) ((pullback f).mapIso a)
      (pullbackIso f N n) (Iso.refl ((pullback f).obj N))
    have hu := bundleTensorIso_trans (pullbackIso f M n) (Iso.refl ((pullback f).obj M))
      (powerIso ((pullback f).mapIso a) n) ((pullback f).mapIso a)
    have hx : bundleTensorIso ((pullback f).mapIso (powerIso a n)) ((pullback f).mapIso a) ≪≫
        bundleTensorIso (pullbackIso f N n) (Iso.refl ((pullback f).obj N)) =
      bundleTensorIso (pullbackIso f M n) (Iso.refl ((pullback f).obj M)) ≪≫
        bundleTensorIso (powerIso ((pullback f).mapIso a) n) ((pullback f).mapIso a) := by
      have hv := congrArg₂ (fun E F => bundleTensorIso E F) ih (Iso.trans_refl ((pullback f).mapIso a))
      have hw := congrArg (fun E => bundleTensorIso (pullbackIso f M n ≪≫ powerIso ((pullback f).mapIso a) n) E)
        (Iso.refl_trans ((pullback f).mapIso a)).symm
      exact ht.trans (hv.trans (hw.trans hu.symm))
    have hleft := congrArg (fun E => (pullback f).mapIso (powerIso a (n + 1)) ≪≫ E)
      (pullbackIso_succ f N n)
    have hmid := congrArg (fun E => E ≪≫ bundleTensorIso (pullbackIso f N n) (Iso.refl ((pullback f).obj N))) hn
    have hright := congrArg (fun E => canonicalTensorPullbackIso f (bundleTensorPower M n) M ≪≫ E) hx
    have hend := congrArg (fun E => E ≪≫ powerIso ((pullback f).mapIso a) (n + 1)) (pullbackIso_succ f M n)
    exact hleft.trans (((Iso.trans_assoc _ _ _).symm.trans hmid).trans
      ((Iso.trans_assoc _ _ _).trans (hright.trans ((Iso.trans_assoc _ _ _).symm.trans hend.symm))))

private theorem isoThreeSquares {C : Type*} [Category C]
    {A B D E F G H I J : C} (a : A ≅ B) (b : B ≅ D) (c : D ≅ E)
    (d : E ≅ F) (e : F ≅ G) (t : B ≅ H) (q : H ≅ E)
    (r : H ≅ I) (s : I ≅ G) (v : A ≅ J) (w : J ≅ I)
    (h₁ : b ≪≫ c = t ≪≫ q) (h₂ : q ≪≫ d ≪≫ e = r ≪≫ s)
    (h₃ : a ≪≫ t ≪≫ r = v ≪≫ w) :
    a ≪≫ b ≪≫ c ≪≫ d ≪≫ e = v ≪≫ w ≪≫ s := by
  calc
    _ = a ≪≫ (b ≪≫ c) ≪≫ d ≪≫ e := by simp only [Iso.trans_assoc]
    _ = a ≪≫ (t ≪≫ q) ≪≫ d ≪≫ e := by rw [h₁]
    _ = a ≪≫ t ≪≫ (q ≪≫ d ≪≫ e) := by simp only [Iso.trans_assoc]
    _ = a ≪≫ t ≪≫ (r ≪≫ s) := by rw [h₂]
    _ = (a ≪≫ t ≪≫ r) ≪≫ s := by simp only [Iso.trans_assoc]
    _ = (v ≪≫ w) ≪≫ s := by rw [h₃]
    _ = _ := Iso.trans_assoc _ _ _

private theorem bundleTensorIso_three {X : Scheme.{u}} {A B C D E F G H : X.Modules}
    (a : A ≅ B) (b : C ≅ D) (c : B ≅ E) (d : D ≅ F) (e : E ≅ G) (f : F ≅ H) :
    bundleTensorIso a b ≪≫ bundleTensorIso c d ≪≫ bundleTensorIso e f =
      bundleTensorIso (a ≪≫ c ≪≫ e) (b ≪≫ d ≪≫ f) := by
  exact (congrArg (fun E => bundleTensorIso a b ≪≫ E) (bundleTensorIso_trans c d e f)).trans
    (bundleTensorIso_trans a b (c ≪≫ e) (d ≪≫ f))

/-- Actual whole power pullback commutes with the TRUE native composition comparison. -/
theorem pullbackIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (n : ℕ) :
    (pullback f).mapIso (pullbackIso g M n) ≪≫
        pullbackIso f ((pullback g).obj M) n ≪≫
        powerIso ((pullbackComp f g).app M) n =
      (pullbackComp f g).app (bundleTensorPower M n) ≪≫ pullbackIso (f ≫ g) M n := by
  induction n with
  | zero =>
    change (pullback f).mapIso (pullbackUnitIso g) ≪≫ pullbackUnitIso f ≪≫ Iso.refl _ =
      (pullbackComp f g).app (unitObj Z) ≪≫ pullbackUnitIso (f ≫ g)
    apply Iso.ext
    exact (Category.comp_id _).trans (ModularCurves.pullbackUnitIso_compLow f g).symm
  | succ n ih =>
    let cg := (pullbackComp f g).app M
    let cn := (pullbackComp f g).app (bundleTensorPower M n)
    have hn₀ := canonicalTensorPullbackIso_natural f (pullbackIso g M n)
      (Iso.refl ((pullback g).obj M))
    have hn₁ := congrArg (fun E => canonicalTensorPullbackIso f ((pullback g).obj (bundleTensorPower M n)) ((pullback g).obj M) ≪≫
      bundleTensorIso ((pullback f).mapIso (pullbackIso g M n)) E)
      ((pullback f).mapIso_refl ((pullback g).obj M))
    have hn := hn₀.trans hn₁
    have ht := bundleTensorIso_three ((pullback f).mapIso (pullbackIso g M n)) (Iso.refl _)
      (pullbackIso f ((pullback g).obj M) n) (Iso.refl _)
      (powerIso cg n) cg
    have hh := congrArg₂ (fun E F => bundleTensorIso E F) ih
      ((Iso.refl_trans (Iso.refl ((pullback f).obj ((pullback g).obj M)) ≪≫ cg)).trans (Iso.refl_trans cg))
    have hu := bundleTensorIso_trans cn cg (pullbackIso (f ≫ g) M n) (Iso.refl _)
    have hv := congrArg (fun E => bundleTensorIso (cn ≪≫ pullbackIso (f ≫ g) M n) E) (Iso.trans_refl cg)
    have h₂ := ht.trans (hh.trans (hv.symm.trans hu.symm))
    have hc := canonicalTensorPullbackIso_comp f g (bundleTensorPower M n) M
    have hthree := isoThreeSquares
      ((pullback f).mapIso (canonicalTensorPullbackIso g (bundleTensorPower M n) M))
      ((pullback f).mapIso (bundleTensorIso (pullbackIso g M n) (Iso.refl _)))
      (canonicalTensorPullbackIso f (bundleTensorPower ((pullback g).obj M) n) ((pullback g).obj M))
      (bundleTensorIso (pullbackIso f ((pullback g).obj M) n) (Iso.refl _))
      (bundleTensorIso (powerIso cg n) cg)
      (canonicalTensorPullbackIso f ((pullback g).obj (bundleTensorPower M n)) ((pullback g).obj M))
      (bundleTensorIso ((pullback f).mapIso (pullbackIso g M n)) (Iso.refl _))
      (bundleTensorIso cn cg)
      (bundleTensorIso (pullbackIso (f ≫ g) M n) (Iso.refl _))
      ((pullbackComp f g).app (bundleTensorPower M (n + 1)))
      (canonicalTensorPullbackIso (f ≫ g) (bundleTensorPower M n) M) hn h₂ hc
    have hg := (pullback f).mapIso_trans (canonicalTensorPullbackIso g (bundleTensorPower M n) M)
      (bundleTensorIso (pullbackIso g M n) (Iso.refl _))
    have hga := congrArg (pullback f).mapIso (pullbackIso_succ g M n)
    have hgb := hga.trans hg
    have hl₀ := congrArg (fun E => E ≪≫ pullbackIso f ((pullback g).obj M) (n + 1) ≪≫ powerIso cg (n + 1)) hgb
    have hl₁ := congrArg (fun E =>
      (((pullback f).mapIso (canonicalTensorPullbackIso g (bundleTensorPower M n) M)) ≪≫
        ((pullback f).mapIso (bundleTensorIso (pullbackIso g M n) (Iso.refl _)))) ≪≫ E ≪≫ powerIso cg (n + 1))
      (pullbackIso_succ f ((pullback g).obj M) n)
    have hl₂ := Iso.trans_assoc ((pullback f).mapIso (canonicalTensorPullbackIso g (bundleTensorPower M n) M))
      ((pullback f).mapIso (bundleTensorIso (pullbackIso g M n) (Iso.refl _)))
      ((canonicalTensorPullbackIso f (bundleTensorPower ((pullback g).obj M) n) ((pullback g).obj M) ≪≫
        bundleTensorIso (pullbackIso f ((pullback g).obj M) n) (Iso.refl _)) ≪≫ powerIso cg (n + 1))
    have hr := congrArg (fun E => (pullbackComp f g).app (bundleTensorPower M (n + 1)) ≪≫ E)
      (pullbackIso_succ (f ≫ g) M n)
    have hlast : ((canonicalTensorPullbackIso f (bundleTensorPower ((pullback g).obj M) n) ((pullback g).obj M) ≪≫
        bundleTensorIso (pullbackIso f ((pullback g).obj M) n) (Iso.refl _)) ≪≫ powerIso cg (n + 1)) =
      canonicalTensorPullbackIso f (bundleTensorPower ((pullback g).obj M) n) ((pullback g).obj M) ≪≫
        bundleTensorIso (pullbackIso f ((pullback g).obj M) n) (Iso.refl _) ≪≫
          bundleTensorIso (powerIso cg n) cg := Iso.trans_assoc _ _ _
    have hl₃ := congrArg (fun E =>
      (pullback f).mapIso (canonicalTensorPullbackIso g (bundleTensorPower M n) M) ≪≫
        (pullback f).mapIso (bundleTensorIso (pullbackIso g M n) (Iso.refl _)) ≪≫ E) hlast
    exact hl₀.trans (hl₁.trans (hl₂.trans (hl₃.trans (hthree.trans hr.symm))))

/-- Equal actual scheme maps give the genuine whole power comparison, without a compatibility input. -/
theorem pullbackIso_congr {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g)
    (M : X.Modules) (n : ℕ) :
    (pullbackCongr h).app (bundleTensorPower M n) ≪≫ pullbackIso g M n =
      pullbackIso f M n ≪≫ powerIso ((pullbackCongr h).app M) n := by
  subst g
  change Iso.refl _ ≪≫ pullbackIso f M n = pullbackIso f M n ≪≫ powerIso (Iso.refl _) n
  rw [powerIso_refl, Iso.refl_trans, Iso.trans_refl]

end EnvelopeProperty.BundleTensorPowerPullbackCoherence
