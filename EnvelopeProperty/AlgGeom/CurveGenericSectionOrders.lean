import EnvelopeProperty.AlgGeom.CurveLineSectionOrders
import EnvelopeProperty.AlgGeom.SchemeLineSectionUnitFrames
import EnvelopeProperty.Berkovich.SchemeGenericCenterCoefficients
import EnvelopeProperty.AlgGeom.ProjectiveGeneratedLineClasses
import EnvelopeProperty.AlgGeom.CurveRationalPrincipalBalance

/-! # Native local orders of arbitrary original generic line sections -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules CategoryTheory.MonoidalCategory
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
open scoped Classical
universe u
namespace EnvelopeProperty.CurveGenericSectionOrders
open SchemeLineSectionEvaluation
variable {X : Scheme.{u}} [IsIntegral X]

/-- The actual original residue-fibre module, named before its sections. -/
abbrev genericFibreModule (L : X.Modules) :
    (Spec (CommRingCat.of (X.residueField (genericPoint X)))).Modules :=
  (pullback (X.fromSpecResidueField (genericPoint X))).obj L

private def originalSection (L : X.Modules)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L, ⊤)) :
    Γ(genericFibreModule L, ⊤) := σ

private theorem generic_mem (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

private def genericFactor (U : X.Opens) [Nonempty U] :
    Spec (CommRingCat.of (X.residueField (genericPoint X))) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (X.fromSpecResidueField (genericPoint X)) (by
    rw [U.range_ι]
    rintro _ ⟨z,rfl⟩
    rw [Scheme.fromSpecResidueField_apply]
    exact generic_mem U)

private theorem genericFactor_comp (U : X.Opens) [Nonempty U] :
    genericFactor U ≫ U.ι = X.fromSpecResidueField (genericPoint X) :=
  IsOpenImmersion.lift_fac _ _ _

private def genericFrame (L : X.Modules) (U : X.Opens) [Nonempty U]
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    genericFibreModule L ≅
      unitObj (Spec (CommRingCat.of (X.residueField (genericPoint X)))) :=
  frameViaFactor (genericFactor U) U.ι (X.fromSpecResidueField (genericPoint X))
    (genericFactor_comp U) e

/-- The actual coefficient of the original generic section in the given ORIGINAL frame. -/
def genericCoefficient (L : X.Modules)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L, ⊤))
    (U : X.Opens) [Nonempty U]
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) : X.functionField :=
  (Berkovich.SchemeValuedPoint.genericResidueEquiv X (genericPoint X) rfl).symm
    ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).hom.hom
      (((genericFrame L U e).hom.val.app (op ⊤)).hom (originalSection L σ)))

private theorem iso_top_injective {B : Scheme.{u}} {M N : B.Modules} (e : M ≅ N) :
    Function.Injective ((e.hom.val.app (op ⊤)).hom) := by
  intro s t h
  have hs := Scheme.Modules.iso_hom_inv_app_applyT e (op ⊤) s
  have ht := Scheme.Modules.iso_hom_inv_app_applyT e (op ⊤) t
  exact hs.symm.trans ((congrArg ((e.inv.val.app (op ⊤)).hom) h).trans ht)

/-- Nonzero ORIGINAL generic sections have nonzero actual coefficients. -/
theorem genericCoefficient_ne_zero (L : X.Modules)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L, ⊤)) (hσ : σ ≠ 0)
    (U : X.Opens) [Nonempty U]
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    genericCoefficient L σ U e ≠ 0 := by
  intro hz
  let w := (Berkovich.SchemeValuedPoint.genericResidueEquiv X (genericPoint X) rfl).symm
  let g := (Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).hom.hom
  let E := genericFrame L U e
  have hw : g ((E.hom.val.app (op ⊤)).hom (originalSection L σ)) = 0 :=
    w.injective (hz.trans w.map_zero.symm)
  have hg : (E.hom.val.app (op ⊤)).hom (originalSection L σ) = 0 :=
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).hom).1
        (hw.trans g.map_zero.symm)
  exact hσ (iso_top_injective E (hg.trans (E.hom.val.app (op ⊤)).hom.map_zero.symm))

private theorem genericFrame_restrict (L : X.Modules) (U V : X.Opens)
    [Nonempty U] [Nonempty V] (hVU : V ≤ U)
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    genericFrame L V
      (frameViaFactor (X.homOfLE hVU) U.ι V.ι (X.homOfLE_ι hVU) e) = genericFrame L U e := by
  have hf : genericFactor V ≫ X.homOfLE hVU = genericFactor U := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc,X.homOfLE_ι,genericFactor_comp,genericFactor_comp]
  unfold genericFrame
  rw [frameViaFactor_comp]
  simp only [hf]

/-- Actual restriction of the ORIGINAL local frame preserves every original coefficient. -/
theorem genericCoefficient_restrict (L : X.Modules)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L, ⊤))
    (U V : X.Opens) [Nonempty U] [Nonempty V] (hVU : V ≤ U)
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    genericCoefficient L σ V
      (frameViaFactor (X.homOfLE hVU) U.ι V.ι (X.homOfLE_ι hVU) e) =
      genericCoefficient L σ U e := by
  unfold genericCoefficient
  rw [genericFrame_restrict]

omit [IsIntegral X] in
private theorem openTopSection_eq_appLE (U : X.Opens) (a : Γ(X,U)) :
    openTopSection U a = (U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom a := by
  rw [openTopSection,Scheme.Opens.ι_appIso,Scheme.Opens.ι_appLE]
  change (X.presheaf.map (eqToHom U.ι_image_top).op).hom a = _
  apply ConcreteCategory.congr_hom
  apply X.presheaf.congr_map
  exact Subsingleton.elim _ _

private theorem genericFactor_coefficient (U : X.Opens) [Nonempty U] (a : Γ(X,U)) :
    (Berkovich.SchemeValuedPoint.genericResidueEquiv X (genericPoint X) rfl).symm
      ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).hom.hom
        ((genericFactor U).appTop.hom (openTopSection U a))) = X.germToFunctionField U a := by
  apply (Berkovich.SchemeValuedPoint.genericResidueEquiv X (genericPoint X) rfl).injective
  rw [RingEquiv.apply_symm_apply,
    Berkovich.SchemeValuedPoint.genericResidueEquiv_germ X (genericPoint X) rfl U (generic_mem U)]
  rw [openTopSection_eq_appLE]
  let q := genericFactor U
  have ht : q.appLE ⊤ ⊤ (le_top : ⊤ ≤ q ⁻¹ᵁ ⊤) = q.appTop := by
    unfold Scheme.Hom.appLE
    change q.appTop ≫ (Spec (CommRingCat.of (X.residueField (genericPoint X)))).presheaf.map
      (𝟙 (op (⊤ : (Spec (CommRingCat.of (X.residueField (genericPoint X)))).Opens))) = q.appTop
    rw [(Spec (CommRingCat.of (X.residueField (genericPoint X)))).presheaf.map_id,Category.comp_id]
  have he := Scheme.Hom.appLE_comp_appLE q U.ι U ⊤ ⊤ U.ι_preimage_self.ge le_top
  have hfun : ∀ h : ⊤ ≤ (q ≫ U.ι) ⁻¹ᵁ U,
      (q ≫ U.ι).appLE U ⊤ h ≫
        (Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).hom =
          X.evaluation U (genericPoint X) (generic_mem U) := by
    dsimp only [q]
    rw [genericFactor_comp]
    intro h
    exact Berkovich.SchemeValuedPoint.fromSpecResidueField_appLE_top _ _ _ _
  have hall : U.ι.appLE U ⊤ U.ι_preimage_self.ge ≫ q.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).hom =
        X.evaluation U (genericPoint X) (generic_mem U) := by
    rw [← ht,← Category.assoc,he]
    exact hfun _
  exact congrArg (fun g : Γ(X,U) ⟶ X.residueField (genericPoint X) => g.hom a) hall

omit [IsIntegral X] in
private theorem scalar_top_apply {B : Scheme.{u}} (r a : Γ(B,⊤)) :
    ((ModularCurves.unitEndomorphismOfTopSection r).val.app (op ⊤)).hom a = a * r := by
  rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
  simp only [homOfLE_refl,op_id]
  change a * (B.presheaf.map (𝟙 (op (⊤ : B.Opens)))).hom r = a * r
  exact congrArg (fun q : Γ(B,⊤) ⟶ Γ(B,⊤) => a * q.hom r)
    (B.presheaf.map_id (op (⊤ : B.Opens)))

private theorem genericCoefficient_transition (L : X.Modules)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L, ⊤))
    (U : X.Opens) [Nonempty U]
    (e e' : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    ∃ a : Γ(X,U)ˣ, genericCoefficient L σ U e' =
      X.germToFunctionField U (a : Γ(X,U)) * genericCoefficient L σ U e := by
  obtain ⟨v,hv⟩ := unitIso_eq_globalUnit (e.symm ≪≫ e')
  have he : e'.hom = e.hom ≫ ModularCurves.unitEndomorphismOfTopSection (v : Γ(U.toScheme,⊤)) := by
    have h := congrArg (fun E : unitObj U.toScheme ≅ unitObj U.toScheme => e.hom ≫ E.hom) hv
    simpa only [Iso.trans_hom,Iso.symm_hom,Iso.hom_inv_id_assoc,
      ModularCurves.unitAutomorphismOfTopUnit_hom] using h
  let a : Γ(X,U)ˣ := Units.map U.topIso.hom.hom v
  have ha : openTopSection U (a : Γ(X,U)) = (v : Γ(U.toScheme,⊤)) := by
    change openTopSection U (U.topIso.hom.hom (v : Γ(U.toScheme,⊤))) = _
    rw [openTopSection,Scheme.Opens.ι_appIso]
    change U.topIso.inv.hom (U.topIso.hom.hom (v : Γ(U.toScheme,⊤))) = _
    exact ConcreteCategory.congr_hom U.topIso.hom_inv_id (v : Γ(U.toScheme,⊤))
  have hs : (pullback (genericFactor U)).map
      (ModularCurves.unitEndomorphismOfTopSection (v : Γ(U.toScheme,⊤))) ≫
        (pullbackUnitIso (genericFactor U)).hom =
      (pullbackUnitIso (genericFactor U)).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          ((genericFactor U).appTop.hom (v : Γ(U.toScheme,⊤))) := by
    have h := ModularCurves.pullback_unitEndomorphismOfTopSection
      (genericFactor U) (v : Γ(U.toScheme,⊤))
    have h' := congrArg (fun z => (pullbackUnitIso (genericFactor U)).hom ≫ z) h
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h'
  have hframe : (genericFrame L U e').hom = (genericFrame L U e).hom ≫
      ModularCurves.unitEndomorphismOfTopSection
        ((genericFactor U).appTop.hom (v : Γ(U.toScheme,⊤))) := by
    unfold genericFrame frameViaFactor
    simp only [Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom]
    rw [he,Functor.map_comp]
    simp only [Category.assoc]
    rw [hs]
  refine ⟨a,?_⟩
  unfold genericCoefficient
  rw [hframe]
  change (Berkovich.SchemeValuedPoint.genericResidueEquiv X (genericPoint X) rfl).symm
    ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).hom.hom
      (((ModularCurves.unitEndomorphismOfTopSection
        ((genericFactor U).appTop.hom (v : Γ(U.toScheme,⊤)))).val.app (op ⊤)).hom
          (((genericFrame L U e).hom.val.app (op ⊤)).hom (originalSection L σ)))) = _
  let w : Γ(Spec (CommRingCat.of (X.residueField (genericPoint X))),⊤) →+* X.functionField :=
    (Berkovich.SchemeValuedPoint.genericResidueEquiv X (genericPoint X) rfl).symm.toRingHom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).hom.hom
  let c : Γ(Spec (CommRingCat.of (X.residueField (genericPoint X))),⊤) :=
    ((genericFrame L U e).hom.val.app (op ⊤)).hom (originalSection L σ)
  have hval := congrArg w (scalar_top_apply
    ((genericFactor U).appTop.hom (v : Γ(U.toScheme,⊤))) c)
  have hmul := w.map_mul c ((genericFactor U).appTop.hom (v : Γ(U.toScheme,⊤)))
  have hval' := hval.trans hmul
  have hwa : w ((genericFactor U).appTop.hom (v : Γ(U.toScheme,⊤))) =
      X.germToFunctionField U (a : Γ(X,U)) := by
    rw [← ha]
    exact genericFactor_coefficient U _
  exact hval'.trans ((congrArg (fun t : X.functionField => w c * t) hwa).trans (mul_comm _ _))

private theorem genericCoefficient_injective (L : X.Modules) (U : X.Opens) [Nonempty U]
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    Function.Injective (fun σ => genericCoefficient L σ U e) := by
  intro σ τ h
  apply iso_top_injective (genericFrame L U e)
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).hom).1
  exact (Berkovich.SchemeValuedPoint.genericResidueEquiv X (genericPoint X) rfl).symm.injective h

private def genericScalar : X.functionField →+*
    Γ(Spec (CommRingCat.of (X.residueField (genericPoint X))),⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).inv.hom.comp
    (Berkovich.SchemeValuedPoint.genericResidueEquiv X (genericPoint X) rfl).toRingHom

/-- Scalar multiplication uses the ORIGINAL generic residue and section-ring action. -/
def scalarSection (L : X.Modules) (f : X.functionField)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L,⊤)) :
    Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L,⊤) :=
  genericScalar f • originalSection L σ

private theorem frame_scalar {B : Scheme.{u}} {M : B.Modules} (E : M ≅ unitObj B)
    (a : Γ(B,⊤)) (σ : Γ(M,⊤)) :
    (E.hom.val.app (op ⊤)).hom (a • σ) =
      a * (show Γ(B,⊤) from (E.hom.val.app (op ⊤)).hom σ) :=
  (E.hom.val.app (op ⊤)).hom.map_smul a σ

/-- EVERY actual generic frame retains the original whole-field scalar. -/
theorem genericCoefficient_scalarSection (L : X.Modules) (f : X.functionField)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L,⊤))
    (U : X.Opens) [Nonempty U]
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    genericCoefficient L (scalarSection L f σ) U e = f * genericCoefficient L σ U e := by
  let w : Γ(Spec (CommRingCat.of (X.residueField (genericPoint X))),⊤) →+* X.functionField :=
    (Berkovich.SchemeValuedPoint.genericResidueEquiv X (genericPoint X) rfl).symm.toRingHom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).hom.hom
  have hw : w (genericScalar f) = f := by
    change (Berkovich.SchemeValuedPoint.genericResidueEquiv X (genericPoint X) rfl).symm
      ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).inv.hom
          ((Berkovich.SchemeValuedPoint.genericResidueEquiv X (genericPoint X) rfl) f))) = f
    rw [Iso.inv_hom_id_apply,RingEquiv.symm_apply_apply]
  have h := congrArg w (frame_scalar (genericFrame L U e) (genericScalar f) (originalSection L σ))
  exact h.trans ((w.map_mul _ _).trans (congrArg (fun t : X.functionField =>
    t * genericCoefficient L σ U e) hw))

omit [IsIntegral X] in
private theorem exists_frame_at_integral (L : X.Modules) (hL : IsInvertible L) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty ((pullback U.ι).obj L ≅ unitObj U.toScheme) := by
  obtain ⟨ι,O,hO,hframe⟩ := hL
  have hx : x ∈ iSup O := by rw [hO]; trivial
  obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hx
  exact ⟨O j,hj,hframe j⟩

/-- ONE internally derived nonzero field scalar relates any two original nonzero generic sections. -/
theorem exists_scalarSection (L : X.Modules) (hL : IsInvertible L)
    (σ τ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L,⊤))
    (hσ : σ ≠ 0) (hτ : τ ≠ 0) :
    ∃ f : X.functionField, f ≠ 0 ∧ σ = scalarSection L f τ := by
  obtain ⟨U,hη,⟨e⟩⟩ := exists_frame_at_integral L hL (genericPoint X)
  let : Nonempty U := ⟨⟨genericPoint X,hη⟩⟩
  let a := genericCoefficient L σ U e
  let b := genericCoefficient L τ U e
  have ha : a ≠ 0 := genericCoefficient_ne_zero L σ hσ U e
  have hb : b ≠ 0 := genericCoefficient_ne_zero L τ hτ U e
  refine ⟨a / b,div_ne_zero ha hb,?_⟩
  apply genericCoefficient_injective L U e
  change genericCoefficient L σ U e = genericCoefficient L (scalarSection L (a / b) τ) U e
  rw [genericCoefficient_scalarSection]
  exact (div_mul_cancel₀ a hb).symm

private noncomputable instance pullback_monoidal {A B : Scheme.{u}} (f : A ⟶ B) :
    (pullback f).Monoidal := pullbackMonoidal f

/-- The actual pure generic tensor in the SAME original pulled tensor line. -/
def tensorSection (L T : X.Modules)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L,⊤))
    (τ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj T,⊤)) :
    Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj (L ⊗ T),⊤) :=
  (((Functor.Monoidal.μIso (pullback (X.fromSpecResidueField (genericPoint X))) L T).hom.val.app
    (op ⊤)).hom (ModularCurves.tensorSection _ _ ⊤ (originalSection L σ) (originalSection T τ)))

private def localTensorFrame (L T : X.Modules) (U : X.Opens)
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme)
    (d : (pullback U.ι).obj T ≅ unitObj U.toScheme) :
    (pullback U.ι).obj (L ⊗ T) ≅ unitObj U.toScheme :=
  (Functor.Monoidal.μIso (pullback U.ι) L T).symm ≪≫ (e ⊗ᵢ d) ≪≫
    ModularCurves.unitObjTensorIso U.toScheme

private theorem pullbackCongr_monoidal {A B : Scheme.{u}} {g h : A ⟶ B} (he : g = h) :
    (pullbackCongr he).hom.IsMonoidal := by
  subst h
  change NatTrans.IsMonoidal (𝟙 (pullback g))
  infer_instance

private theorem genericFrame_tensor (L T : X.Modules) (U : X.Opens) [Nonempty U]
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme)
    (d : (pullback U.ι).obj T ≅ unitObj U.toScheme) :
    genericFrame (L ⊗ T) U (localTensorFrame L T U e d) =
      (Functor.Monoidal.μIso (pullback (X.fromSpecResidueField (genericPoint X))) L T).symm ≪≫
        (genericFrame L U e ⊗ᵢ genericFrame T U d) ≪≫
          ModularCurves.unitObjTensorIso (Spec (CommRingCat.of (X.residueField (genericPoint X)))) := by
  let α : pullback U.ι ⋙ pullback (genericFactor U) ≅
      pullback (X.fromSpecResidueField (genericPoint X)) :=
    pullbackComp (genericFactor U) U.ι ≪≫ pullbackCongr (genericFactor_comp U)
  have : (pullbackComp (genericFactor U) U.ι).hom.IsMonoidal := pullbackComp_hom_isMonoidal _ _
  have : (pullbackCongr (genericFactor_comp U)).hom.IsMonoidal := pullbackCongr_monoidal _
  have : α.hom.IsMonoidal := by dsimp only [α,Iso.trans_hom]; infer_instance
  exact (ModularCurves.pullbackComp_tensorTrivialization U.ι (genericFactor U)
    (X.fromSpecResidueField (genericPoint X)) α L T e d).symm

private theorem tensor_frame_value {B : Scheme.{u}} {M N : B.Modules}
    (e : M ≅ unitObj B) (d : N ≅ unitObj B) (σ : Γ(M,⊤)) (τ : Γ(N,⊤)) :
    ((((e ⊗ᵢ d) ≪≫ ModularCurves.unitObjTensorIso B).hom.val.app (op ⊤)).hom
      (ModularCurves.tensorSection M N ⊤ σ τ)) =
        (show Γ(B,⊤) from (e.hom.val.app (op ⊤)).hom σ) *
          (show Γ(B,⊤) from (d.hom.val.app (op ⊤)).hom τ) := by
  have h := ModularCurves.tensorSection_map e.hom d.hom ⊤ σ τ
  exact (congrArg (fun z => (ModularCurves.unitObjTensorIso B).hom.val.app (op ⊤) z) h).trans
    (ModularCurves.unitObjTensorIso_hom_tensorSection B ⊤ _ _)

private theorem genericCoefficient_tensorSection (L T : X.Modules)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L,⊤))
    (τ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj T,⊤))
    (U : X.Opens) [Nonempty U]
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme)
    (d : (pullback U.ι).obj T ≅ unitObj U.toScheme) :
    genericCoefficient (L ⊗ T) (tensorSection L T σ τ) U (localTensorFrame L T U e d) =
      genericCoefficient L σ U e * genericCoefficient T τ U d := by
  let μ := Functor.Monoidal.μIso (pullback (X.fromSpecResidueField (genericPoint X))) L T
  let E := genericFrame L U e
  let D := genericFrame T U d
  have hi := congrArg (fun q => (q.val.app (op ⊤)).hom
      (ModularCurves.tensorSection _ _ ⊤ (originalSection L σ) (originalSection T τ)))
    (Iso.hom_inv_id_assoc μ ((E ⊗ᵢ D).hom ≫
      (ModularCurves.unitObjTensorIso (Spec (CommRingCat.of (X.residueField (genericPoint X))))).hom))
  have hc := hi.trans (tensor_frame_value E D (originalSection L σ) (originalSection T τ))
  have hf := genericFrame_tensor L T U e d
  have hc' : ((genericFrame (L ⊗ T) U (localTensorFrame L T U e d)).hom.val.app (op ⊤)).hom
      (originalSection (L ⊗ T) (tensorSection L T σ τ)) =
        (show Γ(Spec (CommRingCat.of (X.residueField (genericPoint X))),⊤) from
          (E.hom.val.app (op ⊤)).hom (originalSection L σ)) *
        (show Γ(Spec (CommRingCat.of (X.residueField (genericPoint X))),⊤) from
          (D.hom.val.app (op ⊤)).hom (originalSection T τ)) := by
    rw [hf]
    exact hc
  let w : Γ(Spec (CommRingCat.of (X.residueField (genericPoint X))),⊤) →+* X.functionField :=
    (Berkovich.SchemeValuedPoint.genericResidueEquiv X (genericPoint X) rfl).symm.toRingHom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).hom.hom
  exact (congrArg w hc').trans (w.map_mul _ _)

private theorem genericCoefficient_zero (L : X.Modules) (U : X.Opens) [Nonempty U]
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    genericCoefficient L 0 U e = 0 := by
  let w : Γ(Spec (CommRingCat.of (X.residueField (genericPoint X))),⊤) →+* X.functionField :=
    (Berkovich.SchemeValuedPoint.genericResidueEquiv X (genericPoint X) rfl).symm.toRingHom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).hom.hom
  have hz : ((genericFrame L U e).hom.val.app (op ⊤)).hom (originalSection L 0) = 0 :=
    ((genericFrame L U e).hom.val.app (op ⊤)).hom.map_zero
  exact (congrArg w hz).trans w.map_zero

private theorem scalarSection_ne_zero (L : X.Modules) (hL : IsInvertible L)
    (f : X.functionField) (hf : f ≠ 0)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L,⊤)) (hσ : σ ≠ 0) :
    scalarSection L f σ ≠ 0 := by
  obtain ⟨U,hη,⟨e⟩⟩ := exists_frame_at_integral L hL (genericPoint X)
  let : Nonempty U := ⟨⟨genericPoint X,hη⟩⟩
  intro hz
  have h := congrArg (fun τ => genericCoefficient L τ U e) hz
  have hc := (genericCoefficient_scalarSection L f σ U e).symm.trans
    (h.trans (genericCoefficient_zero L U e))
  exact mul_ne_zero hf (genericCoefficient_ne_zero L σ hσ U e) hc

private theorem tensorSection_ne_zero (L T : X.Modules) (hL : IsInvertible L) (hT : IsInvertible T)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L,⊤))
    (τ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj T,⊤))
    (hσ : σ ≠ 0) (hτ : τ ≠ 0) : tensorSection L T σ τ ≠ 0 := by
  obtain ⟨U,hU,⟨e⟩⟩ := exists_frame_at_integral L hL (genericPoint X)
  obtain ⟨V,hV,⟨d⟩⟩ := exists_frame_at_integral T hT (genericPoint X)
  let W := U ⊓ V
  let : Nonempty W := ⟨⟨genericPoint X,hU,hV⟩⟩
  let E := frameViaFactor (X.homOfLE (inf_le_left : W ≤ U)) U.ι W.ι (X.homOfLE_ι _) e
  let D := frameViaFactor (X.homOfLE (inf_le_right : W ≤ V)) V.ι W.ι (X.homOfLE_ι _) d
  intro hz
  have h := congrArg (fun ξ => genericCoefficient (L ⊗ T) ξ W (localTensorFrame L T W E D)) hz
  have hc := (genericCoefficient_tensorSection L T σ τ W E D).symm.trans
    (h.trans (genericCoefficient_zero (L ⊗ T) W (localTensorFrame L T W E D)))
  exact mul_ne_zero (genericCoefficient_ne_zero L σ hσ W E)
    (genericCoefficient_ne_zero T τ hτ W D) hc

/-- The SAME original whole section pulled to its actual original generic residue fibre. -/
def wholeSection (L : X.Modules) (s : unitObj X ⟶ L) :
    Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L,⊤) :=
  sectionAtOne (pullbackSectionHom (X.fromSpecResidueField (genericPoint X)) s)

omit [IsIntegral X] in
private theorem sectionHom_atOne (L : X.Modules) (s : unitObj X ⟶ L) :
    SchemeModuleGlobalSections.sectionHom L (sectionAtOne s) = s := by
  apply SheafOfModules.hom_ext
  ext U
  change (1 : Γ(X,U.unop)) • L.presheaf.map
    (homOfLE (le_top : U.unop ≤ ⊤)).op (sectionAtOne s) =
      s.val.app U (show Γ(X,U.unop) from 1)
  rw [one_smul]
  have h := PresheafOfModules.naturality_apply s.val
    (homOfLE (le_top : U.unop ≤ ⊤)).op (1 : Γ(X,⊤))
  change s.val.app U ((X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op).hom
    (1 : Γ(X,⊤))) = L.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op (sectionAtOne s) at h
  rw [map_one] at h
  exact h.symm

omit [IsIntegral X] in
private theorem affine_frame_at (L : X.Modules) (hL : IsInvertible L) (x : X) :
    ∃ (U : X.affineOpens), x ∈ U.1 ∧ Nonempty (L.restrict U.1.ι ≅ unitObj U.1.toScheme) := by
  obtain ⟨ι,O,hO,he⟩ := hL
  have hx : x ∈ iSup O := by rw [hO]; trivial
  obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hx
  obtain ⟨_,⟨U,hU,rfl⟩,hxU,hUO⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hj (O j).isOpen
  obtain ⟨e⟩ := he j
  exact ⟨⟨U,hU⟩,hxU,⟨restrictIsoOfPullbackIso L U (restrictTrivialization hUO e)⟩⟩

omit [IsIntegral X] in
private theorem original_coefficient_eq (L : X.Modules) (s : unitObj X ⟶ L)
    (U : X.affineOpens) (e : L.restrict U.1.ι ≅ unitObj U.1.toScheme) :
    CurveLineSectionOrders.frameCoefficient L s U (overTrivializationOfRestrictIso L U.1 e) =
      ModularCurves.localTrivializationCoefficient L U e (sectionAtOne s) := by
  have hres : s.val.app (op U.1) (show Γ(X,U.1) from 1) =
      L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (sectionAtOne s) := by
    have h := PresheafOfModules.naturality_apply s.val
      (homOfLE (le_top : U.1 ≤ ⊤)).op (1 : Γ(X,⊤))
    change s.val.app (op U.1) ((X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom
      (1 : Γ(X,⊤))) = L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (sectionAtOne s) at h
    rw [map_one] at h
    exact h
  change (overTrivializationOfRestrictIso L U.1 e).hom.val.app (op (Over.mk (𝟙 U.1)))
    (s.val.app (op U.1) (show Γ(X,U.1) from 1)) = _
  rw [hres]
  exact ModularCurves.overTrivializationCoefficient_overTrivializationOfRestrictIso L U e _

private theorem genericCoefficient_wholeSection (L : X.Modules) (s : unitObj X ⟶ L)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.restrict U.1.ι ≅ unitObj U.1.toScheme) :
    genericCoefficient L (wholeSection L s) U.1 (pullbackIsoOfRestrictIso L U.1 e) =
      X.germToFunctionField U.1 (ModularCurves.localTrivializationCoefficient L U e (sectionAtOne s)) := by
  let c := ModularCurves.localTrivializationCoefficient L U e (sectionAtOne s)
  have hs := SchemeLineSectionEvaluation.sectionHom_localScalar L U e (sectionAtOne s)
  rw [sectionHom_atOne] at hs
  have hv := SchemeLineSectionEvaluation.frameViaFactor_sectionHom_scalar_apply
    (genericFactor U.1) U.1.ι (X.fromSpecResidueField (genericPoint X)) (genericFactor_comp U.1)
    (pullbackIsoOfRestrictIso L U.1 e) s (openTopSection U.1 c) hs
  let w : Γ(Spec (CommRingCat.of (X.residueField (genericPoint X))),⊤) →+* X.functionField :=
    (Berkovich.SchemeValuedPoint.genericResidueEquiv X (genericPoint X) rfl).symm.toRingHom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (X.residueField (genericPoint X)))).hom.hom
  exact (congrArg w hv).trans (genericFactor_coefficient U.1 c)

/-- A nonzero ORIGINAL whole section remains nonzero in its ORIGINAL generic residue pullback. -/
theorem wholeSection_ne_zero (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (hs : s ≠ 0) : wholeSection L s ≠ 0 := by
  obtain ⟨U,hη,⟨e⟩⟩ := affine_frame_at L hL (genericPoint X)
  let : Nonempty U.1 := ⟨⟨genericPoint X,hη⟩⟩
  have hc : ModularCurves.localTrivializationCoefficient L U e (sectionAtOne s) ≠ 0 := by
    rw [← original_coefficient_eq L s U e]
    exact CurveLineSectionOrders.frameCoefficient_ne_zero L hL s hs U _
  have hcK : X.germToFunctionField U.1
      (ModularCurves.localTrivializationCoefficient L U e (sectionAtOne s)) ≠ 0 :=
    (map_ne_zero_iff _ (X.germToFunctionField_injective U.1)).mpr hc
  intro hz
  have h := congrArg (fun ξ => genericCoefficient L ξ U.1 (pullbackIsoOfRestrictIso L U.1 e)) hz
  exact hcK ((genericCoefficient_wholeSection L s U e).symm.trans
    (h.trans (genericCoefficient_zero L U.1 (pullbackIsoOfRestrictIso L U.1 e))))

variable [IsLocallyNoetherian X]

/-- ANY original open frame gives the SAME native local order of the SAME generic section. -/
theorem ord_genericCoefficient_eq (L : X.Modules)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L, ⊤)) (hσ : σ ≠ 0)
    (U V : X.Opens) (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme)
    (e' : (pullback V.ι).obj L ≅ unitObj V.toScheme) :
    letI : Nonempty U := ⟨⟨x,hxU⟩⟩
    letI : Nonempty V := ⟨⟨x,hxV⟩⟩
    X.ord (genericCoefficient L σ U e) x = X.ord (genericCoefficient L σ V e') x := by
  let : Nonempty U := ⟨⟨x,hxU⟩⟩
  let : Nonempty V := ⟨⟨x,hxV⟩⟩
  let W := U ⊓ V
  let : Nonempty W := ⟨⟨x,hxU,hxV⟩⟩
  let E := frameViaFactor (X.homOfLE (inf_le_left : W ≤ U)) U.ι W.ι
    (X.homOfLE_ι _) e
  let F := frameViaFactor (X.homOfLE (inf_le_right : W ≤ V)) V.ι W.ι
    (X.homOfLE_ι _) e'
  obtain ⟨a,ha⟩ := genericCoefficient_transition L σ W E F
  have haK : X.germToFunctionField W (a : Γ(X,W)) ≠ 0 :=
    (map_ne_zero_iff _ (X.germToFunctionField_injective W)).mpr a.isUnit.ne_zero
  have ho : X.ord (genericCoefficient L σ W F) x = X.ord (genericCoefficient L σ W E) x := by
    rw [ha,X.ord_mul haK (genericCoefficient_ne_zero L σ hσ W E),
      X.ord_of_isUnit a.isUnit (show x ∈ W from ⟨hxU,hxV⟩),zero_add]
  rw [genericCoefficient_restrict L σ U W inf_le_left e,
    genericCoefficient_restrict L σ V W inf_le_right e'] at ho
  exact ho.symm

omit [IsIntegral X] [IsLocallyNoetherian X] in
private theorem exists_frame_at (L : X.Modules) (hL : IsInvertible L) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ Nonempty ((pullback U.ι).obj L ≅ unitObj U.toScheme) := by
  obtain ⟨ι,O,hO,hframe⟩ := hL
  have hx : x ∈ iSup O := by rw [hO]; trivial
  obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hx
  exact ⟨O j,hj,hframe j⟩

/-- The native local order of the ORIGINAL arbitrary generic line section. -/
def order (L : X.Modules) (hL : IsInvertible L)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L, ⊤)) (x : X) : ℤ :=
  let U := (exists_frame_at L hL x).choose
  let hx := (exists_frame_at L hL x).choose_spec.1
  letI : Nonempty U := ⟨⟨x,hx⟩⟩
  X.ord (genericCoefficient L σ U (exists_frame_at L hL x).choose_spec.2.some) x

/-- EVERY given actual local frame computes the defined intrinsic order, without a certificate. -/
theorem order_eq_frameCoefficient (L : X.Modules) (hL : IsInvertible L)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L, ⊤)) (hσ : σ ≠ 0)
    (U : X.Opens) (x : X) (hx : x ∈ U)
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    letI : Nonempty U := ⟨⟨x,hx⟩⟩
    order L hL σ x = X.ord (genericCoefficient L σ U e) x :=
  ord_genericCoefficient_eq L σ hσ _ U x (exists_frame_at L hL x).choose_spec.1 hx
    (exists_frame_at L hL x).choose_spec.2.some e

/-- The actual original generic point has intrinsic section order zero. -/
theorem order_generic (L : X.Modules) (hL : IsInvertible L)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L, ⊤)) :
    order L hL σ (genericPoint X) = 0 := by
  unfold order
  apply X.ord_eq_zero_of_coheight_neq_one
  change Order.coheight (⊤ : X) ≠ 1
  simp


/-- The ORIGINAL scalar action adds the native rational-function order. -/
theorem order_scalarSection (L : X.Modules) (hL : IsInvertible L)
    (f : X.functionField) (hf : f ≠ 0)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L,⊤)) (hσ : σ ≠ 0)
    (x : X) : order L hL (scalarSection L f σ) x = X.ord f x + order L hL σ x := by
  obtain ⟨U,hx,⟨e⟩⟩ := exists_frame_at L hL x
  let : Nonempty U := ⟨⟨x,hx⟩⟩
  rw [order_eq_frameCoefficient L hL _ (scalarSection_ne_zero L hL f hf σ hσ) U x hx e,
    order_eq_frameCoefficient L hL σ hσ U x hx e,genericCoefficient_scalarSection,
    X.ord_mul hf (genericCoefficient_ne_zero L σ hσ U e)]

omit [IsIntegral X] [IsLocallyNoetherian X] in
private theorem tensor_invertible (L T : X.Modules) (hL : IsInvertible L) (hT : IsInvertible T) :
    IsInvertible (L ⊗ T) :=
  (hL.tensorObj hT).of_iso (ModularCurves.monoidalTensorObjIso L T)

/-- The actual original pure generic tensor has exactly the sum of the native factor orders. -/
theorem order_tensorSection (L T : X.Modules) (hL : IsInvertible L) (hT : IsInvertible T)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L,⊤))
    (τ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj T,⊤))
    (hσ : σ ≠ 0) (hτ : τ ≠ 0) (x : X) :
    order (L ⊗ T) (tensor_invertible L T hL hT) (tensorSection L T σ τ) x =
      order L hL σ x + order T hT τ x := by
  obtain ⟨U,hU,⟨e⟩⟩ := exists_frame_at L hL x
  obtain ⟨V,hV,⟨d⟩⟩ := exists_frame_at T hT x
  let W := U ⊓ V
  let : Nonempty W := ⟨⟨x,hU,hV⟩⟩
  let E := frameViaFactor (X.homOfLE (inf_le_left : W ≤ U)) U.ι W.ι (X.homOfLE_ι _) e
  let D := frameViaFactor (X.homOfLE (inf_le_right : W ≤ V)) V.ι W.ι (X.homOfLE_ι _) d
  have hxW : x ∈ W := ⟨hU,hV⟩
  rw [order_eq_frameCoefficient (L ⊗ T) _ _ (tensorSection_ne_zero L T hL hT σ τ hσ hτ)
      W x hxW (localTensorFrame L T W E D),
    order_eq_frameCoefficient L hL σ hσ W x hxW E,
    order_eq_frameCoefficient T hT τ hτ W x hxW D,
    genericCoefficient_tensorSection,
    X.ord_mul (genericCoefficient_ne_zero L σ hσ W E) (genericCoefficient_ne_zero T τ hτ W D)]

/-- The original generic pullback of a whole section has the SAME true original zero-ideal order. -/
theorem order_wholeSection (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (hs : s ≠ 0) (x : X) :
    order L hL (wholeSection L s) x = CurveCartierLocalOrders.localOrder
      (LineSectionZeroIdeal.zeroIdeal L hL s)
      (LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero L hL s hs) x := by
  obtain ⟨U,hx,⟨e⟩⟩ := affine_frame_at L hL x
  let : Nonempty U.1 := ⟨⟨x,hx⟩⟩
  rw [order_eq_frameCoefficient L hL _ (wholeSection_ne_zero L hL s hs) U.1 x hx
    (pullbackIsoOfRestrictIso L U.1 e),genericCoefficient_wholeSection]
  rw [CurveLineSectionOrders.localOrder_eq_frameCoefficient_order L hL s hs U
    (overTrivializationOfRestrictIso L U.1 e) x hx,original_coefficient_eq]

/-- Projective generation internally supplies TWO true whole zero divisors and ONE global field correction. -/
theorem exists_order_difference {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (hp : IsProjectiveFactorization p)
    (L : X.Modules) (hL : IsInvertible L)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L,⊤)) (hσ : σ ≠ 0) :
    ∃ (T : X.Modules) (hT : IsInvertible T)
      (s : unitObj X ⟶ L ⊗ T) (hs : s ≠ 0) (t : unitObj X ⟶ T) (ht : t ≠ 0)
      (f : X.functionField), f ≠ 0 ∧ ∀ x : X,
        order L hL σ x = X.ord f x +
          CurveCartierLocalOrders.localOrder (LineSectionZeroIdeal.zeroIdeal (L ⊗ T)
            (tensor_invertible L T hL hT) s)
            (LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero (L ⊗ T)
              (tensor_invertible L T hL hT) s hs) x -
          CurveCartierLocalOrders.localOrder (LineSectionZeroIdeal.zeroIdeal T hT t)
            (LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero T hT t ht) x := by
  obtain ⟨T,hT,H,_hH,hquot⟩ := ProjectiveGeneratedLineClasses.exists_simultaneous_generated_quotients
    p hp (fun _ : Unit => L) (fun _ => hL)
  obtain ⟨G,_hG,_he⟩ := hquot ()
  obtain ⟨t,ht⟩ := SchemeLineNonzeroGenerators.exists_section_ne_zero T hT H
  let hLT := tensor_invertible L T hL hT
  obtain ⟨s,hs⟩ := SchemeLineNonzeroGenerators.exists_section_ne_zero (L ⊗ T) hLT G
  obtain ⟨f,hf,hfsec⟩ := exists_scalarSection (L ⊗ T) hLT
    (tensorSection L T σ (wholeSection T t)) (wholeSection (L ⊗ T) s)
    (tensorSection_ne_zero L T hL hT σ _ hσ (wholeSection_ne_zero T hT t ht))
    (wholeSection_ne_zero (L ⊗ T) hLT s hs)
  refine ⟨T,hT,s,hs,t,ht,f,hf,fun x => ?_⟩
  have ho := congrArg (fun ξ => order (L ⊗ T) hLT ξ x) hfsec
  rw [order_tensorSection L T hL hT σ _ hσ (wholeSection_ne_zero T hT t ht),
    order_scalarSection (L ⊗ T) hLT f hf _ (wholeSection_ne_zero (L ⊗ T) hLT s hs),
    order_wholeSection T hT t ht,order_wholeSection (L ⊗ T) hLT s hs] at ho
  omega

omit [IsLocallyNoetherian X] in
private theorem finite_zero_order [hX : AlgebraicGeometry.IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I.IsInvertible) :
    letI : IsLocallyNoetherian X := hX.toIsLocallyNoetherian
    Function.HasFiniteSupport (CurveCartierLocalOrders.localOrder I hI) := by
  let : IsLocallyNoetherian X := hX.toIsLocallyNoetherian
  let : Finite I.subscheme := CurveFiniteClosedSubschemes.finite_subscheme hdim I
    (CurveCartierIdealDegrees.support_ne_top I hI)
  have hs : (I.support : Set X).Finite := by
    rw [← I.range_subschemeι]
    exact Set.finite_range I.subschemeι
  apply hs.subset
  intro x hx
  by_contra hnot
  exact hx (CurveCartierLocalOrders.localOrder_eq_zero_of_not_mem_support I hI x hnot)

omit [IsIntegral X] [IsLocallyNoetherian X] in
private theorem finite_weighted {α : Type u} (a : α → ℤ) (ha : Function.HasFiniteSupport a)
    (w : α → ℤ) : Function.HasFiniteSupport (fun x => a x * w x) := by
  apply ha.subset
  intro x hx
  by_contra hnot
  have hz : a x = 0 := by simpa only [Function.mem_support,not_not] using hnot
  exact hx (by change a x * w x = 0; rw [hz,zero_mul])

omit [IsLocallyNoetherian X] in
/-- ANY nonzero ORIGINAL generic section has finite-support actual native local order. -/
theorem hasFiniteSupport_order {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (L : X.Modules) (hL : IsInvertible L)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L,⊤)) (hσ : σ ≠ 0) :
    letI : IsProper p := hp.isProper
    letI : LocallyOfFiniteType p := inferInstance
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    Function.HasFiniteSupport (order L hL σ) := by
  let : IsProper p := hp.isProper
  let : LocallyOfFiniteType p := inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : AlgebraicGeometry.IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance,toCompactSpace := inferInstance }
  obtain ⟨T,hT,s,hs,t,ht,f,hf,ho⟩ := exists_order_difference p hp L hL σ hσ
  have he : order L hL σ = fun x => X.ord f x +
      CurveCartierLocalOrders.localOrder (LineSectionZeroIdeal.zeroIdeal (L ⊗ T)
        (tensor_invertible L T hL hT) s)
        (LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero (L ⊗ T)
          (tensor_invertible L T hL hT) s hs) x -
      CurveCartierLocalOrders.localOrder (LineSectionZeroIdeal.zeroIdeal T hT t)
        (LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero T hT t ht) x := funext ho
  rw [he]
  exact ((CurveRationalPrincipalBalance.hasFiniteSupport_ord hdim hNormal f hf).add
    (finite_zero_order hdim _ _)).sub (finite_zero_order hdim _ _)

omit [IsLocallyNoetherian X] in
/-- The SAME FULL Euler degree is the true residue-weighted order sum of ANY nonzero original generic section. -/
theorem degree_eq_finsum_order {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (L : X.Modules) (hL : IsInvertible L)
    (σ : Γ((pullback (X.fromSpecResidueField (genericPoint X))).obj L,⊤)) (hσ : σ ≠ 0) :
    letI : IsProper p := hp.isProper
    letI : LocallyOfFiniteType p := inferInstance
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    CurveLineDegrees.degree p L = ∑ᶠ x : X,
      letI := AffineSchemeLocalDegrees.residueAlgebra p x
      order L hL σ x * (Module.finrank k (X.residueField x) : ℤ) := by
  let : IsProper p := hp.isProper
  let : LocallyOfFiniteType p := inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : AlgebraicGeometry.IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance,toCompactSpace := inferInstance }
  obtain ⟨T,hT,s,hs,t,ht,f,hf,ho⟩ := exists_order_difference p hp L hL σ hσ
  let hLT := tensor_invertible L T hL hT
  let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ T) hLT s
  let hI := LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero (L ⊗ T) hLT s hs
  let J := LineSectionZeroIdeal.zeroIdeal T hT t
  let hJ := LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero T hT t ht
  let weight := fun x : X =>
    letI := AffineSchemeLocalDegrees.residueAlgebra p x
    (Module.finrank k (X.residueField x) : ℤ)
  let F := CurveRationalPrincipalBalance.weightedOrder p f
  let A := CurveCartierLocalOrders.weightedLocalOrder p I hI
  let B := CurveCartierLocalOrders.weightedLocalOrder p J hJ
  have hF : Function.HasFiniteSupport F :=
    CurveRationalPrincipalBalance.hasFiniteSupport_weightedOrder p hdim hNormal f hf
  have hA : Function.HasFiniteSupport A := finite_weighted _ (finite_zero_order hdim I hI) weight
  have hB : Function.HasFiniteSupport B := finite_weighted _ (finite_zero_order hdim J hJ) weight
  have hFzero : (∑ᶠ x : X,F x) = 0 :=
    CurveRationalPrincipalBalance.finsum_weightedOrder_eq_zero p hp hdim hNormal f hf
  have hpoint (x : X) : order L hL σ x * weight x = F x + A x - B x := by
    change order L hL σ x * weight x =
      X.ord f x * weight x + CurveCartierLocalOrders.localOrder I hI x * weight x -
        CurveCartierLocalOrders.localOrder J hJ x * weight x
    rw [ho x]
    ring
  have hN := CurveLineDegrees.degree_eq_zeroSection_orders p hp hdim (L ⊗ T) hLT s hs
  have hTdeg := CurveLineDegrees.degree_eq_zeroSection_orders p hp hdim T hT t ht
  have hTensor := CurveLineDegrees.degree_tensor p hp hdim L T hL hT
  have hdeg : CurveLineDegrees.degree p L = (∑ᶠ x : X,A x) - ∑ᶠ x : X,B x := by
    change CurveLineDegrees.degree p (L ⊗ T) = ∑ᶠ x : X,A x at hN
    change CurveLineDegrees.degree p T = ∑ᶠ x : X,B x at hTdeg
    change CurveLineDegrees.degree p (L ⊗ T) = CurveLineDegrees.degree p L + CurveLineDegrees.degree p T at hTensor
    omega
  change CurveLineDegrees.degree p L = ∑ᶠ x : X,order L hL σ x * weight x
  calc
    CurveLineDegrees.degree p L = (∑ᶠ x : X,A x) - ∑ᶠ x : X,B x := hdeg
    _ = ∑ᶠ x : X,(F x + A x - B x) := by
      have hsum : (∑ᶠ x : X,(F x + A x - B x)) =
          (∑ᶠ x : X,F x) + (∑ᶠ x : X,A x) - ∑ᶠ x : X,B x :=
        (finsum_sub_distrib (hF.add hA) hB).trans
          (congrArg (fun q : ℤ => q - ∑ᶠ x : X,B x) (finsum_add_distrib hF hA))
      rw [hFzero,zero_add] at hsum
      exact hsum.symm
    _ = ∑ᶠ x : X,order L hL σ x * weight x := finsum_congr (fun x => (hpoint x).symm)

end EnvelopeProperty.CurveGenericSectionOrders
