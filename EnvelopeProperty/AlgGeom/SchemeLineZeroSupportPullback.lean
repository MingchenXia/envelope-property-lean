import EnvelopeProperty.AlgGeom.SchemeClosedResidueSectionEvaluation
import EnvelopeProperty.AlgGeom.IntegralLineImageModules
import EnvelopeProperty.Berkovich.SchemeLinePullbackSections
/-! # Actual line-section zero support retains genuine scheme pullback -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeLineZeroSupportPullback

theorem mem_support_iff_coefficient_zero {X : Scheme.{u}} (M : X.Modules) (hM : IsInvertible M)
    (α : unitObj X ⟶ M) (U : X.Opens) (x : X) (hx : x ∈ U)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    x ∈ (LineSectionZeroIdeal.zeroIdeal M hM α).support ↔
      X.evaluation U x hx (e.hom.val.app (op (Over.mk (𝟙 U)))
        (α.val.app (op U) (1 : Γ(X,U)))) = 0 := by
  obtain ⟨W,hWa,hxW,hWU⟩ := exists_isAffineOpen_mem_and_subset hx
  let i : W ⟶ U := homOfLE hWU
  let eW := ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e (Over.mk i)
  rw [(LineSectionZeroIdeal.zeroIdeal M hM α).mem_support_iff_of_mem (U := ⟨W,hWa⟩) hxW,
    LineSectionZeroIdeal.zeroIdeal_ideal_of_frame M hM α ⟨W,hWa⟩ eW,
    X.zeroLocus_span, X.zeroLocus_singleton]
  change x ∉ X.basicOpen (eW.hom.val.app (op (Over.mk (𝟙 W))) (α.val.app (op W) (1 : Γ(X,W)))) ↔ _
  rw [← X.evaluation_eq_zero_iff_notMem_basicOpen x hxW]
  have hα := PresheafOfModules.naturality_apply α.val i.op (1 : Γ(X,U))
  change α.val.app (op W) (X.presheaf.map i.op (1 : Γ(X,U))) =
    M.val.map i.op (α.val.app (op U) (1 : Γ(X,U))) at hα
  rw [map_one] at hα
  have hn := PresheafOfModules.naturality_apply e.hom.val
    (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 U)).op
    (α.val.app (op U) (1 : Γ(X,U)))
  change e.hom.val.app (op (Over.mk i))
      (M.val.map i.op (α.val.app (op U) (1 : Γ(X,U)))) =
    X.presheaf.map i.op (e.hom.val.app (op (Over.mk (𝟙 U)))
      (α.val.app (op U) (1 : Γ(X,U)))) at hn
  have he : eW.hom.val.app (op (Over.mk (𝟙 W)))
      (α.val.app (op W) (1 : Γ(X,W))) =
    X.presheaf.map i.op (e.hom.val.app (op (Over.mk (𝟙 U)))
      (α.val.app (op U) (1 : Γ(X,U)))) := by
    change e.hom.val.app (op (Over.mk i)) _ = _
    rw [hα]
    exact hn
  rw [he]
  change X.residue x (X.presheaf.germ W x hxW (X.presheaf.map i.op _)) = 0 ↔ _
  rw [X.presheaf.germ_res_apply]
  rfl
private theorem restriction_section_one {X : Scheme.{u}} (M : X.Modules)
    (α : unitObj X ⟶ M) (U : X.Opens) :
    ((restrictAdjunction U.ι).unit.app M).val.app (op U)
      (α.val.app (op U) (1 : Γ(X,U))) =
    ((restrictUnitIso U.ι).inv ≫ (restrictFunctor U.ι).map α).val.app
      (op (U.ι ⁻¹ᵁ U)) (1 : Γ(U.toScheme,U.ι ⁻¹ᵁ U)) := by
  change _ = ((restrictFunctor U.ι).map α).val.app (op (U.ι ⁻¹ᵁ U))
    ((restrictUnitIso U.ι).inv.val.app (op (U.ι ⁻¹ᵁ U)) (1 : Γ(U.toScheme,U.ι ⁻¹ᵁ U)))
  have hu : (restrictUnitIso U.ι).inv.val.app (op (U.ι ⁻¹ᵁ U))
      (1 : Γ(U.toScheme,U.ι ⁻¹ᵁ U)) = (1 : Γ(X,U.ι ''ᵁ (U.ι ⁻¹ᵁ U))) := by
    change (U.ι.appIso (U.ι ⁻¹ᵁ U)).inv (1 : Γ(U.toScheme,U.ι ⁻¹ᵁ U)) = 1
    exact map_one _
  rw [hu]
  change M.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op
      (α.val.app (op U) (1 : Γ(X,U))) =
    α.val.app (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ U))) (1 : Γ(X,U.ι ''ᵁ (U.ι ⁻¹ᵁ U)))
  have h := PresheafOfModules.naturality_apply α.val
    (homOfLE (U.ι.image_preimage_le U)).op (1 : Γ(X,U))
  change α.val.app (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ U)))
    (X.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op (1 : Γ(X,U))) = _ at h
  rw [map_one] at h
  exact h.symm

private theorem coefficient_pullback_frame {X : Scheme.{u}} (M : X.Modules)
    (α : unitObj X ⟶ M) (U : X.Opens)
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    let eO := overTrivializationOfRestrictIso M U (restrictIsoOfPullbackIso M U e)
    eO.hom.val.app (op (Over.mk (𝟙 U))) (α.val.app (op U) (1 : Γ(X,U))) =
      U.topIso.hom (SchemeLineSectionEvaluation.sectionAtOne
        (SchemeLineSectionEvaluation.pullbackSectionHom U.ι α ≫ e.hom)) := by
  let eR := restrictIsoOfPullbackIso M U e
  let eO := overTrivializationOfRestrictIso M U eR
  let V := U.ι ⁻¹ᵁ U
  let a := ((overFunctorEquiv U).app M).hom
  let b := eR.hom
  let c := (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).inv
  let q := (overEquiv U).functor.map eO.hom
  have hq : q = a ≫ b ≫ c := by
    simp only [q,eO,overTrivializationOfRestrictIso,Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage,Iso.trans_hom]
    rfl
  have ha := overFunctorEquiv_hom_localModuleSection_preimageT M U
    (α.val.app (op U) (1 : Γ(X,U)))
  have hsec := restriction_section_one M α U
  have hr := SchemeLineSectionEvaluation.pullbackSectionHom_restrict M U α
  have hr' := congrArg (fun h => h ≫ (restrictFunctorIsoPullback U.ι).hom.app M ≫ e.hom) hr
  simp only [Category.assoc,Iso.inv_hom_id_app_assoc] at hr'
  change SchemeLineSectionEvaluation.pullbackSectionHom U.ι α ≫ e.hom =
    (restrictUnitIso U.ι).inv ≫ (restrictFunctor U.ι).map α ≫ b at hr'
  apply terminal_apply_eq_of_overEquivT M U eO.hom
  have hleft := congrArg (fun h => h.val.app (op V)
    (localModuleSection M U V (α.val.app (op U) (1 : Γ(X,U))))) hq
  erw [sheafOfModules_comp_app_apply,sheafOfModules_comp_app_apply] at hleft
  change q.val.app (op V) _ = c.val.app (op V) (b.val.app (op V) (a.val.app (op V) _)) at hleft
  change a.val.app (op V) _ = _ at ha
  rw [ha,hsec] at hleft
  have hb := congrArg (fun h => h.val.app (op V) (1 : Γ(U.toScheme,V))) hr'
  change _ = b.val.app (op V)
    (((restrictUnitIso U.ι).inv ≫ (restrictFunctor U.ι).map α).val.app (op V) (1 : Γ(U.toScheme,V))) at hb
  rw [← hb] at hleft
  dsimp only
  change q.val.app (op V) _ = _
  refine hleft.trans ?_
  let β := SchemeLineSectionEvaluation.pullbackSectionHom U.ι α ≫ e.hom
  let t := SchemeLineSectionEvaluation.sectionAtOne β
  change β.val.app (op V) (1 : Γ(U.toScheme,V)) = _
  have ht := unitHom_eq_globalScalar β
  have hv := congrArg (fun h => h.val.app (op V) (1 : Γ(U.toScheme,V))) ht
  rw [ModularCurves.unitEndomorphismOfTopSection_app_apply] at hv
  simp only [one_mul] at hv
  refine hv.trans ?_
  have hu : openTopSection U (U.topIso.hom t) = t := by
    rw [openTopSection,Scheme.Opens.ι_appIso]
    exact U.topIso.hom_inv_id_apply t
  change U.toScheme.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t = _
  have hrest := openTopSection_restrict U V (U.topIso.hom t)
  rw [hu] at hrest
  rw [← hrest]
  rw [Scheme.Opens.ι_appIso]
  change X.presheaf.map _ (U.topIso.hom t) = X.presheaf.map _ (U.topIso.hom t)
  exact ConcreteCategory.congr_hom (X.presheaf.congr_map (Subsingleton.elim _ _)) _
private theorem scalar_one {X : Scheme.{u}} (r : Γ(X,⊤)) :
    SchemeLineSectionEvaluation.sectionAtOne (ModularCurves.unitEndomorphismOfTopSection r) = r := by
  change (ModularCurves.unitEndomorphismOfTopSection r).val.app (op ⊤) (1 : Γ(X,⊤)) = r
  rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
  simp only [homOfLE_refl,op_id,one_mul]
  erw [CategoryTheory.Functor.map_id]
  rfl

theorem mem_support_iff_pullback_frame_zero {X : Scheme.{u}} (M : X.Modules) (hM : IsInvertible M)
    (α : unitObj X ⟶ M) (U : X.Opens) (x : X) (hx : x ∈ U)
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    x ∈ (LineSectionZeroIdeal.zeroIdeal M hM α).support ↔
      X.evaluation U x hx (U.topIso.hom (SchemeLineSectionEvaluation.sectionAtOne
        (SchemeLineSectionEvaluation.pullbackSectionHom U.ι α ≫ e.hom))) = 0 := by
  let eO := overTrivializationOfRestrictIso M U (restrictIsoOfPullbackIso M U e)
  have h := mem_support_iff_coefficient_zero M hM α U x hx eO
  have he := coefficient_pullback_frame M α U e
  change eO.hom.val.app (op (Over.mk (𝟙 U))) (α.val.app (op U) (1 : Γ(X,U))) = _ at he
  rw [he] at h
  exact h

theorem support_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) (hM : IsInvertible M)
    (α : unitObj X ⟶ M) :
    (LineSectionZeroIdeal.zeroIdeal ((pullback f).obj M) (hM.pullback f)
      (SchemeLineSectionEvaluation.pullbackSectionHom f α)).support =
        (LineSectionZeroIdeal.zeroIdeal M hM α).support.preimage f.continuous := by
  ext y
  have hMt := hM
  obtain ⟨ι,U,hU,hframe⟩ := hMt
  have hy : f y ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hy
  obtain ⟨e⟩ := hframe i
  let W := U i
  let V := f ⁻¹ᵁ W
  let ep := SchemeLineSectionEvaluation.localPullbackFrame f W e
  let c : Γ(X,W) := W.topIso.hom (SchemeLineSectionEvaluation.sectionAtOne
    (SchemeLineSectionEvaluation.pullbackSectionHom W.ι α ≫ e.hom))
  have hr : SchemeLineSectionEvaluation.pullbackSectionHom W.ι α ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection (openTopSection W c) := by
    have hc : openTopSection W c = SchemeLineSectionEvaluation.sectionAtOne
        (SchemeLineSectionEvaluation.pullbackSectionHom W.ι α ≫ e.hom) := by
      rw [openTopSection,Scheme.Opens.ι_appIso]
      exact W.topIso.hom_inv_id_apply _
    rw [hc]
    exact unitHom_eq_globalScalar _
  have hp := SchemeLineSectionEvaluation.localPullbackFrame_sectionHom_scalar f W e α c hr
  have hcoeff : V.topIso.hom (SchemeLineSectionEvaluation.sectionAtOne
      (SchemeLineSectionEvaluation.pullbackSectionHom V.ι
        (SchemeLineSectionEvaluation.pullbackSectionHom f α) ≫ ep.hom)) = (f.app W).hom c := by
    have hs := congrArg SchemeLineSectionEvaluation.sectionAtOne hp
    rw [scalar_one] at hs
    rw [hs,openTopSection,Scheme.Opens.ι_appIso]
    exact V.topIso.inv_hom_id_apply _
  change y ∈ (LineSectionZeroIdeal.zeroIdeal ((pullback f).obj M) (hM.pullback f)
    (SchemeLineSectionEvaluation.pullbackSectionHom f α)).support ↔
    f y ∈ (LineSectionZeroIdeal.zeroIdeal M hM α).support
  rw [mem_support_iff_pullback_frame_zero _ (hM.pullback f) _ V y hi ep,
    mem_support_iff_pullback_frame_zero M hM α W (f y) hi e,hcoeff]
  change Y.evaluation V y hi ((f.app W).hom c) = 0 ↔ X.evaluation W (f y) hi c = 0
  rw [← Scheme.evaluation_naturality_apply f y hi c]
  constructor
  · intro h
    apply (f.residueFieldMap y).hom.injective
    simpa only [map_zero] using h
  · intro h
    rw [h,map_zero]

end EnvelopeProperty.SchemeLineZeroSupportPullback
