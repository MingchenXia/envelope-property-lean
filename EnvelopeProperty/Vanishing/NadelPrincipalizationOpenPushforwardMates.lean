import EnvelopeProperty.Vanishing.NadelPrincipalizationOpenPushforward

/-! # The actual open comparison as the canonical Cartesian mate -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationOpenPushforwardMates
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem mate_component {C D E F : Type*}
    [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) {G : C ⥤ E} {H : D ⥤ F}
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (d : D) :
    (mateEquiv a₁ a₂ (TwoSquare.mk G L₁ L₂ H α)).natTrans.app d =
      a₂.unit.app (G.obj (R₁.obj d)) ≫ R₂.map (α.app (R₁.obj d)) ≫
        R₂.map (H.map (a₁.counit.app d)) := by
  simp [mateEquiv]

private theorem unit_inverse {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R) (x : C) :
    a'.unit.app x ≫ R.map ((a.leftAdjointUniq a').inv.app x) = a.unit.app x := by
  rw [← Adjunction.unit_leftAdjointUniq_hom_app a a' x]
  rw [Category.assoc, ← R.map_comp]
  simp

/-- Passing from restriction adjunctions to their actual native pullback
adjunctions preserves the whole original Cartesian mate. -/
theorem mate_leftAdjointUniq {C D E F : Type*}
    [Category C] [Category D] [Category E] [Category F]
    {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₁' : L₁' ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₂' : L₂' ⊣ R₂)
    {G : C ⥤ E} {H : D ⥤ F} (α : G ⋙ L₂ ⟶ L₁ ⋙ H) :
    (mateEquiv a₁' a₂' (TwoSquare.mk G L₁' L₂' H
      (Functor.whiskerLeft G (a₂.leftAdjointUniq a₂').inv ≫ α ≫
        Functor.whiskerRight (a₁.leftAdjointUniq a₁').hom H))).natTrans =
      (mateEquiv a₁ a₂ (TwoSquare.mk G L₁ L₂ H α)).natTrans := by
  apply NatTrans.ext
  funext d
  rw [mate_component, mate_component]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp]
  have hunit := unit_inverse a₂ a₂' (G.obj (R₁.obj d))
  have hc := congrArg (fun m => R₂.map (H.map m))
    (Adjunction.leftAdjointUniq_hom_app_counit a₁ a₁' d)
  simp only [Functor.map_comp] at hc
  calc
    _ = (a₂'.unit.app (G.obj (R₁.obj d)) ≫
        R₂.map ((a₂.leftAdjointUniq a₂').inv.app (G.obj (R₁.obj d)))) ≫
        R₂.map (α.app (R₁.obj d)) ≫
        (R₂.map (H.map ((a₁.leftAdjointUniq a₁').hom.app (R₁.obj d))) ≫
          R₂.map (H.map (a₁'.counit.app d))) := by simp only [Category.assoc]
    _ = _ := by rw [hunit, hc]

variable {Y X Y' X' : Scheme.{u}} (p : Y ⟶ X) (p' : Y' ⟶ X')
    (h : Y' ⟶ Y) (g : X' ⟶ X) [IsOpenImmersion h] [IsOpenImmersion g]
    (H : IsPullback p' h g p)

/-- The SAME original whole pushforward square. -/
def pushIso : pushforward h ⋙ pushforward p ≅ pushforward p' ⋙ pushforward g :=
  pushforwardComp h p ≪≫ (pushforwardCongr H.w).symm ≪≫ (pushforwardComp p' g).symm

/-- The native Cartesian restriction isomorphism is the genuine mate of
the original whole pushforward-composition square. -/
theorem restrict_mate :
    (mateEquiv (restrictAdjunction h) (restrictAdjunction g)
      (TwoSquare.mk (pushforward p) (restrictFunctor h) (restrictFunctor g) (pushforward p')
        (restrictPushforwardIsoOfIsPullback p p' h g H).hom)).natTrans =
      (pushIso p p' h g H).hom := by
  apply NatTrans.ext
  funext M
  rw [mate_component]
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  simp only [Scheme.Modules.Hom.comp_app, pushforward_map_app,
    restrictAdjunction_unit_app_app, restrictAdjunction_counit_app_app,
    ]
  let x' : Γ(M, h ⁻¹ᵁ (p ⁻¹ᵁ U)) := x
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ x')) = M.presheaf.map _ x'
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  exact ConcreteCategory.congr_hom (M.presheaf.congr_map (Subsingleton.elim _ _)) x

/-- The whole original open-pullback isomorphism has precisely the original
Cartesian pushforward square as its native adjunction mate. -/
theorem open_mate :
    (mateEquiv (pullbackPushforwardAdjunction h) (pullbackPushforwardAdjunction g)
      (TwoSquare.mk (pushforward p) (pullback h) (pullback g) (pushforward p')
        (NadelPrincipalizationOpenPushforward.openNatIso p p' h g H).hom)).natTrans =
      (pushIso p p' h g H).hom :=
  (mate_leftAdjointUniq (restrictAdjunction h) (pullbackPushforwardAdjunction h)
    (restrictAdjunction g) (pullbackPushforwardAdjunction g)
    (restrictPushforwardIsoOfIsPullback p p' h g H).hom).trans
      (restrict_mate p p' h g H)

private def pullSquare (f : Y ⟶ X) (t : X' ⟶ X) :
    TwoSquare (pullback t) (pullback f)
      (pullback (CategoryTheory.Limits.pullback.snd f t))
      (pullback (CategoryTheory.Limits.pullback.fst f t)) :=
  TwoSquare.mk _ _ _ _
    ((pullbackComp (CategoryTheory.Limits.pullback.snd f t) t).hom ≫
      (pullbackCongr (CategoryTheory.Limits.pullback.condition.symm :
        CategoryTheory.Limits.pullback.snd f t ≫ t =
          CategoryTheory.Limits.pullback.fst f t ≫ f)).hom ≫
      (pullbackComp (CategoryTheory.Limits.pullback.fst f t) f).inv)

private theorem conjugateEquiv_pullbackComp_hom
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    conjugateEquiv
        (pullbackPushforwardAdjunction (a ≫ b))
        ((pullbackPushforwardAdjunction b).comp
          (pullbackPushforwardAdjunction a))
        (pullbackComp a b).hom =
      (pushforwardComp a b).inv := by
  let eL := pullbackComp a b
  let eR := pushforwardComp a b
  have h := conjugateEquiv_comm
    ((pullbackPushforwardAdjunction b).comp
      (pullbackPushforwardAdjunction a))
    (pullbackPushforwardAdjunction (a ≫ b))
    (α := eL.inv) (β := eL.hom) eL.hom_inv_id
  rw [conjugateEquiv_pullbackComp_inv] at h
  apply (cancel_epi eR.hom).1
  exact h.trans eR.hom_inv_id.symm

private theorem conjugateEquiv_pullbackCongr_hom
    {A B : Scheme.{u}} {a b : A ⟶ B} (h : a = b) :
    conjugateEquiv (pullbackPushforwardAdjunction b)
        (pullbackPushforwardAdjunction a) (pullbackCongr h).hom =
      (pushforwardCongr h).inv := by
  subst b
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom,
    conjugateEquiv_id]
  apply NatTrans.ext
  funext M
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change x = (((pushforwardCongr (rfl : a = a)).inv.app M).app U.unop) x
  rw [pushforwardCongr_inv_app_app]
  simp
  rfl

private theorem pullSquare_conjugate (f : Y ⟶ X) (t : X' ⟶ X) [IsOpenImmersion t] :
    conjugateEquiv
        ((pullbackPushforwardAdjunction f).comp
          (pullbackPushforwardAdjunction (CategoryTheory.Limits.pullback.fst f t)))
        ((pullbackPushforwardAdjunction t).comp
          (pullbackPushforwardAdjunction (CategoryTheory.Limits.pullback.snd f t)))
        (pullSquare f t) =
      (pushIso f (CategoryTheory.Limits.pullback.snd f t) (CategoryTheory.Limits.pullback.fst f t) t
        (IsPullback.of_hasPullback f t).flip).hom := by
  let q := CategoryTheory.Limits.pullback.snd f t
  let g := CategoryTheory.Limits.pullback.fst f t
  let h : q ≫ t = g ≫ f := CategoryTheory.Limits.pullback.condition.symm
  let adj₀ := (pullbackPushforwardAdjunction f).comp
    (pullbackPushforwardAdjunction g)
  let adj₁ := pullbackPushforwardAdjunction (g ≫ f)
  let adj₂ := pullbackPushforwardAdjunction (q ≫ t)
  let adj₃ := (pullbackPushforwardAdjunction t).comp
    (pullbackPushforwardAdjunction q)
  let A := (pullbackComp q t).hom
  let B := (pullbackCongr h).hom
  let C := (pullbackComp g f).inv
  have hA : conjugateEquiv adj₂ adj₃ A =
      (pushforwardComp q t).inv := by
    exact conjugateEquiv_pullbackComp_hom q t
  have hB : conjugateEquiv adj₁ adj₂ B =
      (pushforwardCongr h).inv := by
    exact conjugateEquiv_pullbackCongr_hom h
  have hC : conjugateEquiv adj₀ adj₁ C =
      (pushforwardComp g f).hom := by
    exact conjugateEquiv_pullbackComp_inv g f
  change conjugateEquiv adj₀ adj₃ (A ≫ B ≫ C) = _
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp adj₀ adj₁ adj₃, hC]
  rw [← conjugateEquiv_comp adj₁ adj₂ adj₃, hB, hA]
  rfl


private theorem native_first_mate (f : Y ⟶ X) (t : X' ⟶ X) :
    pullbackPushforwardBaseChange f t =
      (mateEquiv (pullbackPushforwardAdjunction f)
        (pullbackPushforwardAdjunction (CategoryTheory.Limits.pullback.snd f t))
        (pullSquare f t)).natTrans := rfl

/-- The separate native Cartesian base-change map has exactly the SAME
whole original pushforward square as its iterated adjunction mate. -/
theorem native_mate (f : Y ⟶ X) (t : X' ⟶ X) [IsOpenImmersion t] :
    (mateEquiv
      (pullbackPushforwardAdjunction (CategoryTheory.Limits.pullback.fst f t))
      (pullbackPushforwardAdjunction t)
      (TwoSquare.mk _ _ _ _ (pullbackPushforwardBaseChange f t))).natTrans =
      (pushIso f (CategoryTheory.Limits.pullback.snd f t)
        (CategoryTheory.Limits.pullback.fst f t) t (IsPullback.of_hasPullback f t).flip).hom := by
  rw [native_first_mate, iterated_mateEquiv_conjugateEquiv]
  exact pullSquare_conjugate f t

/-- For an actual open base map, the native canonical Cartesian mate is
exactly the internally constructed whole-module isomorphism. -/
theorem native_eq_openNatIso (f : Y ⟶ X) (t : X' ⟶ X) [IsOpenImmersion t] :
    pullbackPushforwardBaseChange f t =
      (NadelPrincipalizationOpenPushforward.openNatIso f
        (CategoryTheory.Limits.pullback.snd f t)
        (CategoryTheory.Limits.pullback.fst f t) t (IsPullback.of_hasPullback f t).flip).hom :=
  (mateEquiv
      (pullbackPushforwardAdjunction (CategoryTheory.Limits.pullback.fst f t))
      (pullbackPushforwardAdjunction t)).injective
    ((native_mate f t).trans
      (open_mate f (CategoryTheory.Limits.pullback.snd f t)
        (CategoryTheory.Limits.pullback.fst f t) t (IsPullback.of_hasPullback f t).flip).symm)

/-- Actual openness, with no comparison premise, proves that the SAME
native Cartesian pullback--pushforward mate is invertible. -/
theorem native_isIso (f : Y ⟶ X) (t : X' ⟶ X) [IsOpenImmersion t] :
    IsIso (pullbackPushforwardBaseChange f t) := by
  rw [native_eq_openNatIso f t]
  infer_instance

/-- The actual inverse to the SAME native canonical base-change mate. -/
def nativeIso (f : Y ⟶ X) (t : X' ⟶ X) [IsOpenImmersion t] :
    pushforward f ⋙ pullback t ≅
      pullback (CategoryTheory.Limits.pullback.fst f t) ⋙
        pushforward (CategoryTheory.Limits.pullback.snd f t) := by
  let := native_isIso f t
  exact asIso (pullbackPushforwardBaseChange f t)

/-- The forward morphism is literally the existing native canonical mate. -/
theorem nativeIso_hom (f : Y ⟶ X) (t : X' ⟶ X) [IsOpenImmersion t] :
    (nativeIso f t).hom = pullbackPushforwardBaseChange f t := rfl

/-- Its inverse is exactly the actual restriction--pullback Cartesian
inverse constructed from the original native open-square isomorphism. -/
theorem nativeIso_inv (f : Y ⟶ X) (t : X' ⟶ X) [IsOpenImmersion t] :
    (nativeIso f t).inv =
      (NadelPrincipalizationOpenPushforward.openNatIso f
        (CategoryTheory.Limits.pullback.snd f t)
        (CategoryTheory.Limits.pullback.fst f t) t (IsPullback.of_hasPullback f t).flip).inv :=
  congrArg Iso.inv (Iso.ext (native_eq_openNatIso f t))

/-- The SAME native canonical Cartesian mate carries the whole original
native-adjoint pushed section to the SAME pulled original section. -/
theorem native_section_triangle (f : Y ⟶ X) (t : X' ⟶ X) [IsOpenImmersion t]
    {M : Y.Modules} (δ : unitObj Y ⟶ M) :
    (pullbackUnitIso t).inv ≫
      (pullback t).map ((pullbackPushforwardAdjunction f).homEquiv _ _
        ((pullbackUnitIso f).hom ≫ δ)) ≫ (pullbackPushforwardBaseChange f t).app M =
    (pullbackPushforwardAdjunction (CategoryTheory.Limits.pullback.snd f t)).homEquiv _ _
      ((pullbackUnitIso (CategoryTheory.Limits.pullback.snd f t)).hom ≫
        (pullbackUnitIso (CategoryTheory.Limits.pullback.fst f t)).inv ≫
        (pullback (CategoryTheory.Limits.pullback.fst f t)).map δ) := by
  rw [native_eq_openNatIso f t]
  exact NadelPrincipalizationOpenPushforward.adjointSection_triangle f
    (CategoryTheory.Limits.pullback.snd f t) (CategoryTheory.Limits.pullback.fst f t) t
    (IsPullback.of_hasPullback f t).flip δ

end EnvelopeProperty.Vanishing.NadelPrincipalizationOpenPushforwardMates
