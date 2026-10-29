import EnvelopeProperty.AlgGeom.SchemeLineZeroSupportPullback
import EnvelopeProperty.AlgGeom.CurveCartierLocalOrders
/-! # SAME native original frame coefficients retain ENTIRE actual zero ideals and genuine Cartier native orders -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeLineZeroIdealNativeFrameOrders
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

theorem overCoefficient_eq_nativeFrameCoefficient {X : Scheme.{u}} (M : X.Modules)
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

theorem zeroIdeal_ideal_of_pullback_frame {X : Scheme.{u}} (M : X.Modules) (hM : IsInvertible M)
    (α : unitObj X ⟶ M) (U : X.affineOpens)
    (e : (pullback U.1.ι).obj M ≅ unitObj U.1.toScheme) :
    (LineSectionZeroIdeal.zeroIdeal M hM α).ideal U =
      Ideal.span ({U.1.topIso.hom (SchemeLineSectionEvaluation.sectionAtOne
        (SchemeLineSectionEvaluation.pullbackSectionHom U.1.ι α ≫ e.hom))} : Set Γ(X,U.1)) := by
  let eO := overTrivializationOfRestrictIso M U.1 (restrictIsoOfPullbackIso M U.1 e)
  rw [LineSectionZeroIdeal.zeroIdeal_ideal_of_frame M hM α U eO]
  have he := overCoefficient_eq_nativeFrameCoefficient M α U.1 e
  change eO.hom.val.app (op (Over.mk (𝟙 U.1))) (α.val.app (op U.1) (1 : Γ(X,U.1))) = _ at he
  rw [he]

theorem localOrder_eq_native_frame {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (M : X.Modules) (hM : IsInvertible M) (α : unitObj X ⟶ M) (hα : α ≠ 0)
    (U : X.affineOpens) (e : (pullback U.1.ι).obj M ≅ unitObj U.1.toScheme)
    (x : X) (hx : x ∈ U.1) :
    letI : Nonempty U.1 := ⟨⟨x,hx⟩⟩
    let I := LineSectionZeroIdeal.zeroIdeal M hM α
    let hI := LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero M hM α hα
    let c := U.1.topIso.hom (SchemeLineSectionEvaluation.sectionAtOne
      (SchemeLineSectionEvaluation.pullbackSectionHom U.1.ι α ≫ e.hom))
    c ≠ 0 ∧ CurveCartierLocalOrders.localOrder I hI x = X.ord (X.germToFunctionField U.1 c) x := by
  let : Nonempty U.1 := ⟨⟨x,hx⟩⟩
  let I := LineSectionZeroIdeal.zeroIdeal M hM α
  let hI := LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero M hM α hα
  let c := U.1.topIso.hom (SchemeLineSectionEvaluation.sectionAtOne
    (SchemeLineSectionEvaluation.pullbackSectionHom U.1.ι α ≫ e.hom))
  have hspan : I.ideal U = Ideal.span ({c} : Set Γ(X,U.1)) :=
    zeroIdeal_ideal_of_pullback_frame M hM α U e
  have hc : c ≠ 0 := by
    intro hc0
    have hη : genericPoint X ∈ U.1 :=
      ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
        (by simpa using (inferInstance : Nonempty U.1))
    have hηI : genericPoint X ∈ I.support := by
      rw [I.mem_support_iff_of_mem hη,hspan,X.zeroLocus_span,X.zeroLocus_singleton,hc0,X.basicOpen_zero]
      simp
    exact CurveFiniteClosedSubschemes.genericPoint_not_mem I.support
      (CurveCartierIdealDegrees.support_ne_top I hI) hηI
  exact ⟨hc,CurveCartierLocalOrders.localOrder_eq_ord_of_local_equation I hI U c hc hspan x hx⟩
end EnvelopeProperty.SchemeLineZeroIdealNativeFrameOrders
