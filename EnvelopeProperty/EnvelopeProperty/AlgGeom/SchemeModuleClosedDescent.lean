module

public import EnvelopeProperty.AlgGeom.SchemeModuleStalkLinearity
public import ModularCurves.ForMathlib.AffineModuleBaseChange
public import Hironaka.Scheme.IdealSheaf.StalkIdeal
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Actual closed-immersion descent from ordinary original-stalk annihilation -/

@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct
open EnvelopeProperty.SchemeModuleStalkLinearity
universe u
namespace EnvelopeProperty.SchemeModuleClosedDescent

/-- An actual surjective ring map whose actual kernel annihilates the original
module has an invertible ACTUAL extension--restriction adjunction unit. -/
theorem isIso_extensionUnit_of_ker_annihilates
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{u} R)
    (hann : ∀ r : R, r ∈ RingHom.ker f → ∀ m : M, r • m = 0) :
    IsIso ((ModuleCat.extendRestrictScalarsAdj f).unit.app M) := by
  let := f.toAlgebra
  let fa : R →ₐ[R] S := Algebra.ofId R S
  let e : (R ⧸ RingHom.ker f) ≃ₐ[R] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := fa) hf
  have hp : (RingHom.ker f • (⊤ : Submodule R M)) = ⊥ := by
    apply le_antisymm _ bot_le
    exact Submodule.smul_le.mpr fun r hr m _ => (by simpa using hann r hr m)
  let E : S ⊗[R] M ≃ₗ[R] M :=
    (e.symm.toLinearEquiv.rTensor M) ≪≫ₗ
      TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker f) ≪≫ₗ
        (RingHom.ker f • (⊤ : Submodule R M)).quotEquivOfEqBot hp
  have hE (m : M) : E ((1 : S) ⊗ₜ[R] m) = m := by
    change (RingHom.ker f • (⊤ : Submodule R M)).quotEquivOfEqBot hp
      (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker f)
        (e.symm (1 : S) ⊗ₜ[R] m)) = m
    rw [map_one, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
    exact Submodule.quotEquivOfEqBot_apply_mk _ hp m
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (fun m : M => (1 : S) ⊗ₜ[R] m)
  constructor
  · intro m n h
    exact (hE m).symm.trans ((congrArg E h).trans (hE n))
  · intro t
    exact ⟨E t, E.injective (hE (E t))⟩

/-- Ordinary ORIGINAL-stalk annihilation kills actual ideal sections acting on
actual module sections; no section annihilation certificate is supplied. -/
theorem idealSections_smul_eq_zero {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules)
    (hann : ∀ (x : X) (r : X.presheaf.stalk x), r ∈ I.stalkIdeal x →
      ∀ m : M.presheaf.stalk x, r • m = 0)
    (U : X.affineOpens) (r : Γ(X, U.1)) (hr : r ∈ I.ideal U)
    (m : Γ(M, U.1)) : r • m = 0 := by
  refine TopCat.Presheaf.section_ext
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) U.1 (r • m) 0 ?_
  intro x hx
  have hrx : X.presheaf.germ U.1 x hx r ∈ I.stalkIdeal x :=
    I.map_germ_le_stalkIdeal U hx (Ideal.mem_map_of_mem _ hr)
  exact (PresheafOfModules.germ_smul (R := X.presheaf) M.val x U.1 hx r m).trans
    ((hann x _ hrx (M.presheaf.germ U.1 x hx m)).trans
      (M.presheaf.germ U.1 x hx).hom.map_zero.symm)

private theorem isIso_closedUnit_of_isAffine_sections {X : Scheme.{u}} [IsAffine X]
    (I : X.IdealSheafData) (M : X.Modules) [M.IsQuasicoherent]
    (hann : ∀ r : Γ(X, (⊤ : X.Opens)), r ∈ I.ideal ⟨⊤, isAffineOpen_top X⟩ →
      ∀ m : Γ(M, (⊤ : X.Opens)), r • m = 0) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app M) := by
  let : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have hsurj : Function.Surjective I.subschemeι.appTop.hom :=
    I.subschemeι_app_surjective U
  have hker : RingHom.ker I.subschemeι.appTop.hom = I.ideal U :=
    I.ker_subschemeι_app U
  let : IsIso ((ModuleCat.extendRestrictScalarsAdj I.subschemeι.appTop.hom).unit.app
      (ModuleCat.of Γ(X, (⊤ : X.Opens)) Γ(M, (⊤ : X.Opens)))) :=
    isIso_extensionUnit_of_ker_annihilates I.subschemeι.appTop.hom hsurj _
      (fun r hr m => hann r (hker ▸ hr) m)
  exact Scheme.Modules.isIso_pullbackPushforward_unit_of_isAffine_of_isIso_extendScalars_unit
    I.subschemeι M

/-- In the affine case, ordinary ORIGINAL-stalk annihilation makes the fixed
ACTUAL geometric pullback--pushforward unit invertible. -/
theorem isIso_closedUnit_of_isAffine {X : Scheme.{u}} [IsAffine X]
    (I : X.IdealSheafData) (M : X.Modules) [M.IsQuasicoherent]
    (hann : ∀ (x : X) (r : X.presheaf.stalk x), r ∈ I.stalkIdeal x →
      ∀ m : M.presheaf.stalk x, r • m = 0) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app M) :=
  isIso_closedUnit_of_isAffine_sections I M
    (fun r hr m => idealSections_smul_eq_zero I M hann ⟨⊤, isAffineOpen_top X⟩ r hr m)

/-- Every actual affine-open restriction has invertible SAME local closed unit,
proved from the ORIGINAL stalk input without a local annihilation certificate. -/
theorem isIso_closedUnit_restrictAffine {X U : Scheme.{u}} [IsAffine U]
    (I : X.IdealSheafData) (M : X.Modules) [M.IsQuasicoherent]
    (hann : ∀ (x : X) (r : X.presheaf.stalk x), r ∈ I.stalkIdeal x →
      ∀ m : M.presheaf.stalk x, r • m = 0)
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (I.comap j).subschemeι).unit.app
      (M.restrict j)) := by
  apply isIso_closedUnit_of_isAffine_sections
  intro r hr m
  let V : U.affineOpens := ⟨⊤, isAffineOpen_top U⟩
  let W : X.affineOpens := ⟨j ''ᵁ (⊤ : U.Opens),
    (isAffineOpen_top U).image_of_isOpenImmersion j⟩
  have hr' : (j.appIso (⊤ : U.Opens)).inv r ∈ I.ideal W := by
    change r ∈ (I.comap j).ideal V at hr
    rw [I.ideal_comap_of_isOpenImmersion j V] at hr
    exact hr
  exact idealSections_smul_eq_zero I M hann W
    ((j.appIso (⊤ : U.Opens)).inv r) hr' m

private def openPushforwardSquareIso {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    (H : IsPullback f' iU iV f) :
    Scheme.Modules.pushforward iU ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward iV :=
  Scheme.Modules.pushforwardComp iU f ≪≫
    Scheme.Modules.pushforwardCongr H.w.symm ≪≫
      (Scheme.Modules.pushforwardComp f' iV).symm

private def openBaseChangeMate {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor iV ⟶
      Scheme.Modules.restrictFunctor iU ⋙ Scheme.Modules.pushforward f' :=
  (mateEquiv (Scheme.Modules.restrictAdjunction iU)
    (Scheme.Modules.restrictAdjunction iV)).symm
      (openPushforwardSquareIso f f' iU iV H).hom

private theorem openBaseChangeMate_eq {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) :
    openBaseChangeMate f f' iU iV H =
      (Scheme.Modules.restrictPushforwardIsoOfIsPullback f f' iU iV H).hom := by
  apply NatTrans.ext
  funext M
  apply Scheme.Modules.hom_ext
  intro W
  ext m
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ m)) =
    M.presheaf.map _ m
  erw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  exact ConcreteCategory.congr_hom
    (M.presheaf.congr_map (Subsingleton.elim _ _)) m

private def openPullbackRestrictionMap {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) :
    Scheme.Modules.restrictFunctor iV ⋙ Scheme.Modules.pullback f' ⟶
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor iU :=
  (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f')).symm
      (openBaseChangeMate f f' iU iV H)

private theorem openPullbackRestrictionMap_isIso {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) :
    IsIso (openPullbackRestrictionMap f f' iU iV H) := by
  let a := (conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction iU))
    ((Scheme.Modules.restrictAdjunction iV).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f'))).symm
        (openPushforwardSquareIso f f' iU iV H).hom
  have ha : IsIso a := by dsimp only [a]; infer_instance
  have he : openPullbackRestrictionMap f f' iU iV H = a :=
    iterated_mateEquiv_conjugateEquiv_symm
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f')
      (Scheme.Modules.restrictAdjunction iV)
      (Scheme.Modules.restrictAdjunction iU)
      (openPushforwardSquareIso f f' iU iV H).hom
  exact he.symm ▸ ha

private theorem isIso_restrictUnit_of_localUnit {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) (M : Y.Modules)
    [IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f').unit.app (M.restrict iV))] :
    IsIso ((Scheme.Modules.restrictFunctor iV).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)) := by
  let b := openBaseChangeMate f f' iU iV H
  let : IsIso b := by
    dsimp only [b]
    rw [openBaseChangeMate_eq]
    infer_instance
  let a := openPullbackRestrictionMap f f' iU iV H
  let : IsIso a := openPullbackRestrictionMap_isIso f f' iU iV H
  have h := unit_mateEquiv_symm
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f') b M
  have hc : IsIso ((Scheme.Modules.restrictFunctor iV).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        b.app ((Scheme.Modules.pullback f).obj M)) := by
    rw [h]
    change IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f').unit.app (M.restrict iV) ≫
      (Scheme.Modules.pushforward f').map (a.app M))
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    ((Scheme.Modules.restrictFunctor iV).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M))
    (b.app ((Scheme.Modules.pullback f).obj M)) (inferInstance) hc

private def idealOpenLift {X U : Scheme.{u}} (I : X.IdealSheafData)
    (j : U ⟶ X) : (I.comap j).subscheme ⟶ I.subscheme :=
  (I.comapIso j).hom ≫ CategoryTheory.Limits.pullback.snd j I.subschemeι

private theorem idealOpen_isPullback {X U : Scheme.{u}} (I : X.IdealSheafData)
    (j : U ⟶ X) :
    IsPullback (I.comap j).subschemeι (idealOpenLift I j) j I.subschemeι := by
  apply isPullback_of_isClosedImmersion
  · simpa only [idealOpenLift, ← Category.assoc, I.comapIso_hom_fst] using
      congrArg (fun q => (I.comapIso j).hom ≫ q)
        (CategoryTheory.Limits.pullback.condition (f := j) (g := I.subschemeι))
  · simp

private theorem isIso_of_affineRestrictions {X : Scheme.{u}} {M N : X.Modules}
    (v : M ⟶ N)
    (hlocal : ∀ U : X.affineOpens,
      IsIso ((Scheme.Modules.restrictFunctor U.1.ι).map v)) : IsIso v := by
  have hxIso (x : X) : IsIso ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map v) := by
    obtain ⟨U, hx⟩ : ∃ U : X.affineOpens, x ∈ U.1 := by
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← iSup_affineOpens_eq_top X, Opens.mem_iSup] at hx
      exact hx
    let y : U.1.toScheme := ⟨x, hx⟩
    let e := Scheme.Modules.restrictStalkNatIso U.1.ι y
    let F := Scheme.Modules.restrictFunctor U.1.ι ⋙ Scheme.Modules.toPresheaf U.1.toScheme ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
    let G := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    let : IsIso ((Scheme.Modules.restrictFunctor U.1.ι).map v) := hlocal U
    have hf : IsIso (F.map v) := by
      dsimp only [F, Functor.comp_map]
      infer_instance
    have hc : IsIso (e.hom.app M ≫ G.map v) := by
      erw [← e.hom.naturality]
      change IsIso (F.map v ≫ e.hom.app N)
      infer_instance
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ (e.hom.app M) (G.map v)
      (inferInstance) hc
  apply (Scheme.Modules.Hom.isIso_iff_isIso_app (φ := v)).mpr
  intro U
  let : ∀ x : U, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map v).hom) := fun x => hxIso x.1
  exact TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso
    ((SheafOfModules.toSheaf X.ringCatSheaf).map v) U

/-- The SAME actual original closed pullback--pushforward unit is invertible
from only ordinary original-stalk annihilation, with no flatness or integrality. -/
theorem isIso_closedUnit {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules) [M.IsQuasicoherent]
    (hann : ∀ (x : X) (r : X.presheaf.stalk x), r ∈ I.stalkIdeal x →
      ∀ m : M.presheaf.stalk x, r • m = 0) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app M) := by
  apply isIso_of_affineRestrictions
  intro U
  let : IsAffine U.1.toScheme := U.2
  let j := U.1.ι
  let k := idealOpenLift I j
  let : IsOpenImmersion k := by dsimp only [k, idealOpenLift]; infer_instance
  let : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (I.comap j).subschemeι).unit.app (M.restrict j)) :=
    isIso_closedUnit_restrictAffine I M hann j
  exact isIso_restrictUnit_of_localUnit I.subschemeι (I.comap j).subschemeι k j
    (idealOpen_isPullback I j) M


/-- The fixed actual pullback of the original quasicoherent module through the
original closed subscheme is itself quasicoherent. -/
theorem isQuasicoherent_closedPullback {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback I.subschemeι).obj M).IsQuasicoherent := by
  let f := I.subschemeι
  let N := (Scheme.Modules.pullback f).obj M
  have hlocal (U : X.affineOpens) : (N.over (f ⁻¹ᵁ U.1)).IsQuasicoherent := by
    let V := f ⁻¹ᵁ U.1
    let g := f ∣_ U.1
    let : IsAffine U.1.toScheme := U.2
    let : IsAffine V.toScheme := U.2.preimage f
    let P := (Scheme.Modules.pullback g).obj (M.restrict U.1.ι)
    have hP : P.IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_pullback_of_isAffine g (M.restrict U.1.ι)
    let a := openPullbackRestrictionMap f g V.ι U.1.ι (isPullback_morphismRestrict f U.1)
    let : IsIso a :=
      openPullbackRestrictionMap_isIso f g V.ι U.1.ι (isPullback_morphismRestrict f U.1)
    let e : P ≅ N.restrict V.ι := asIso (a.app M)
    let : (N.restrict V.ι).IsQuasicoherent :=
      (Scheme.Modules.isQuasicoherent V.toScheme).prop_of_iso e hP
    exact Scheme.Modules.isQuasicoherent_over_of_restrict_of_isAffineOpen N V
  have hcover : (Opens.grothendieckTopology I.subscheme).CoversTop
      (fun U : X.affineOpens => f ⁻¹ᵁ U.1) := by
    rw [Opens.coversTop_iff, IsOpenCover]
    exact f.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ N _ (fun U : X.affineOpens => f ⁻¹ᵁ U.1) hcover hlocal

/-- The same actual closed pullback of the original finite-type quasicoherent
module has finite type, internally using original finite local generators. -/
theorem isFiniteType_closedPullback {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((Scheme.Modules.pullback I.subschemeι).obj M).IsFiniteType := by
  let f := I.subschemeι
  let N := (Scheme.Modules.pullback f).obj M
  have hG (U : X.affineOpens) :
      ∃ G : (N.restrict (f ⁻¹ᵁ U.1).ι).GeneratingSections, G.IsFiniteType := by
    let V := f ⁻¹ᵁ U.1
    let g := f ∣_ U.1
    let : IsAffine U.1.toScheme := U.2
    let : IsAffine V.toScheme := U.2.preimage f
    let MU := M.restrict U.1.ι
    let P := (Scheme.Modules.pullback g).obj MU
    let : P.IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_pullback_of_isAffine g MU
    obtain ⟨GMU, hGMU⟩ :=
      Scheme.Modules.exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen M U
    let : GMU.IsFiniteType := hGMU
    let : Module.Finite Γ(U.1.toScheme, ⊤) Γ(MU, ⊤) :=
      Scheme.Modules.globalSections_module_finite_of_generatingSections_of_isAffine MU GMU
    let := g.appTop.hom.toAlgebra
    let : Module.Finite Γ(V.toScheme, ⊤)
        (Γ(V.toScheme, ⊤) ⊗[Γ(U.1.toScheme, ⊤)] Γ(MU, ⊤)) := inferInstance
    let : Module.Finite Γ(V.toScheme, ⊤)
        ((ModuleCat.extendScalars g.appTop.hom).obj
          (ModuleCat.of Γ(U.1.toScheme, ⊤) Γ(MU, ⊤))) := by
      change Module.Finite Γ(V.toScheme, ⊤)
        (Γ(V.toScheme, ⊤) ⊗[Γ(U.1.toScheme, ⊤)] Γ(MU, ⊤))
      infer_instance
    let : Module.Finite Γ(V.toScheme, ⊤) Γ(P, ⊤) :=
      Module.Finite.equiv (Scheme.Modules.affinePullbackΓIso g MU).toLinearEquiv
    obtain ⟨G, hG⟩ :=
      Scheme.Modules.exists_generatingSections_of_globalSections_module_finite_of_isAffine P
    let a := openPullbackRestrictionMap f g V.ι U.1.ι (isPullback_morphismRestrict f U.1)
    let : IsIso a :=
      openPullbackRestrictionMap_isIso f g V.ι U.1.ι (isPullback_morphismRestrict f U.1)
    let e : P ≅ N.restrict V.ι := asIso (a.app M)
    let G' := SheafOfModules.GeneratingSections.equivOfIso e G
    have hG' : G'.IsFiniteType := ⟨by change Finite G.I; exact hG.finite⟩
    exact ⟨G', hG'⟩
  choose G hG using hG
  let q : N.LocalGeneratorsData :=
    { I := X.affineOpens
      X := fun U => f ⁻¹ᵁ U.1
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover]
        exact f.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)
      generators := fun U => Scheme.Modules.generatingSectionsOverOfRestrict N
        (f ⁻¹ᵁ U.1) (G U) }
  have hq : q.IsFiniteType := by
    constructor
    intro U
    let : (G U).IsFiniteType := hG U
    exact Scheme.Modules.generatingSectionsOverOfRestrict_isFiniteType N
      (f ⁻¹ᵁ U.1) (G U)
  have hqShrink : q.shrink.IsFiniteType := by
    constructor
    intro i
    dsimp [SheafOfModules.LocalGeneratorsData.shrink]
    exact hq.isFiniteType i.2.choose
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨q.shrink, hqShrink⟩

end EnvelopeProperty.SchemeModuleClosedDescent
