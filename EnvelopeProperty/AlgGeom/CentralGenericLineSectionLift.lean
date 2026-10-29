import EnvelopeProperty.AlgGeom.ClosedImmersionStalkQuotients
import EnvelopeProperty.AlgGeom.SchemeLineSectionUnitFrames
import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization
import EnvelopeProperty.Berkovich.SchemeGenericLinePullback
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Actual local lifts of prescribed central generic line sections -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.CentralGenericLineSectionLift
open SchemeLineSectionEvaluation

/-- Actual closed-immersion surjectivity and locality lift every nonzero
coefficient in the SAME central function field to an ambient stalk unit. -/
theorem exists_unit_lift {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) [IsClosedImmersion i] (b : C.functionField) (hb : b ≠ 0) :
    ∃ a : Y.presheaf.stalk (i (genericPoint C)),
      IsUnit a ∧ i.stalkMap (genericPoint C) a = b := by
  obtain ⟨a, ha⟩ := i.stalkMap_surjective (genericPoint C) b
  refine ⟨a, ?_, ha⟩
  apply isUnit_of_map_unit (i.stalkMap (genericPoint C)).hom a
  rw [ha]
  exact isUnit_iff_ne_zero.mpr hb

/-- A SAME actual center-stalk unit has an actual unit representative
on a genuine neighborhood inside any prescribed original neighborhood. -/
theorem exists_unit_neighborhood {Y : Scheme.{u}} (η : Y)
    (a : Y.presheaf.stalk η) (ha : IsUnit a) (U : Y.Opens) (hη : η ∈ U) :
    ∃ (V : Y.Opens) (_hVU : V ≤ U) (hηV : η ∈ V) (c : Γ(Y, V)ˣ),
      Y.presheaf.germ V η hηV (c : Γ(Y, V)) = a := by
  obtain ⟨W, hηW, s, hs⟩ := Y.presheaf.exists_germ_eq a
  let Z := W ⊓ U
  have hηZ : η ∈ Z := ⟨hηW, hη⟩
  let sZ : Γ(Y, Z) := Y.presheaf.map (homOfLE inf_le_left).op s
  have hg : Y.presheaf.germ Z η hηZ sZ = a :=
    (Y.presheaf.germ_res_apply (homOfLE inf_le_left) η hηZ s).trans hs
  obtain ⟨V, j, hηV, hc⟩ :=
    Y.toRingedSpace.isUnit_res_of_isUnit_germ Z sZ η hηZ (hg.symm ▸ ha)
  refine ⟨V, j.le.trans inf_le_right, hηV, hc.unit, ?_⟩
  rw [hc.unit_spec]
  exact (Y.presheaf.germ_res_apply j η hηV sZ).trans hg

private def residueOpenFactor {Y : Scheme.{u}} (y : Y) (U : Y.Opens) (hy : y ∈ U) :
    Spec (Y.residueField y) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (Y.fromSpecResidueField y) (by
    rw [U.range_ι]
    rintro _ ⟨z, rfl⟩
    change Y.fromSpecResidueField y z ∈ U
    rw [Scheme.fromSpecResidueField_apply]
    exact hy)

private theorem residueOpenFactor_comp {Y : Scheme.{u}} (y : Y)
    (U : Y.Opens) (hy : y ∈ U) :
    residueOpenFactor y U hy ≫ U.ι = Y.fromSpecResidueField y :=
  IsOpenImmersion.lift_fac _ _ _

private def closedOpenFactor {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (U : Y.Opens) (hη : i (genericPoint C) ∈ U) :
    Spec (C.residueField (genericPoint C)) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (C.fromSpecResidueField (genericPoint C) ≫ i) (by
    rw [U.range_ι]
    rintro _ ⟨z, rfl⟩
    change i (C.fromSpecResidueField (genericPoint C) z) ∈ U
    rw [Scheme.fromSpecResidueField_apply]
    exact hη)

private theorem closedOpenFactor_comp {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (U : Y.Opens) (hη : i (genericPoint C) ∈ U) :
    closedOpenFactor i U hη ≫ U.ι = C.fromSpecResidueField (genericPoint C) ≫ i :=
  IsOpenImmersion.lift_fac _ _ _

/-- The true generic restriction of the SAME local section, with actual
open-factor and native original pullback-composition comparisons. -/
def closedGenericSection {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (L : Y.Modules) (U : Y.Opens) (hη : i (genericPoint C) ∈ U)
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L) :
    Γ((pullback (C.fromSpecResidueField (genericPoint C))).obj ((pullback i).obj L), ⊤) :=
  sectionAtOne (pullbackSectionHom (closedOpenFactor i U hη) δ ≫
    (frameFactorIso (closedOpenFactor i U hη) U.ι
      (C.fromSpecResidueField (genericPoint C) ≫ i) (closedOpenFactor_comp i U hη) L).hom ≫
    ((pullbackComp (C.fromSpecResidueField (genericPoint C)) i).app L).inv)

private def closedGenericFrame {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) {L : Y.Modules} (U : Y.Opens) (hη : i (genericPoint C) ∈ U)
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    (pullback (C.fromSpecResidueField (genericPoint C))).obj ((pullback i).obj L) ≅
      unitObj (Spec (C.residueField (genericPoint C))) :=
  (pullbackComp (C.fromSpecResidueField (genericPoint C)) i).app L ≪≫
    frameViaFactor (closedOpenFactor i U hη) U.ι
      (C.fromSpecResidueField (genericPoint C) ≫ i) (closedOpenFactor_comp i U hη) e

private theorem iso_top_injective {B : Scheme.{u}} {M N : B.Modules} (e : M ≅ N) :
    Function.Injective ((e.hom.val.app (op ⊤)).hom) := by
  intro s t h
  have hs := Scheme.Modules.iso_hom_inv_app_applyT e (op ⊤) s
  have ht := Scheme.Modules.iso_hom_inv_app_applyT e (op ⊤) t
  exact hs.symm.trans ((congrArg ((e.inv.val.app (op ⊤)).hom) h).trans ht)

private theorem scalar_at_one {B : Scheme.{u}} (r : Γ(B, ⊤)) :
    sectionAtOne (ModularCurves.unitEndomorphismOfTopSection r) = r := by
  rw [sectionAtOne, ModularCurves.unitEndomorphismOfTopSection_app_apply]
  simp only [homOfLE_refl, op_id, one_mul]
  rw [B.presheaf.map_id]
  rfl

private theorem closedGenericSection_coefficient {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) {L : Y.Modules} (U : Y.Opens) (hη : i (genericPoint C) ∈ U)
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme)
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L) (r : Γ(U.toScheme, ⊤))
    (hr : δ ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection r) :
    (closedGenericFrame i U hη e).hom.val.app (op ⊤)
      (closedGenericSection i L U hη δ) = (closedOpenFactor i U hη).appTop.hom r := by
  have hs : SchemeLineSectionUnitFrames.frameScalar e δ = r := by
    unfold SchemeLineSectionUnitFrames.frameScalar
    rw [hr]
    exact scalar_at_one r
  have hf := SchemeLineSectionUnitFrames.pullback_frameScalar (closedOpenFactor i U hη) e δ
  rw [hs] at hf
  have hwhole : (pullbackSectionHom (closedOpenFactor i U hη) δ ≫
      (frameFactorIso (closedOpenFactor i U hη) U.ι
        (C.fromSpecResidueField (genericPoint C) ≫ i) (closedOpenFactor_comp i U hη) L).hom ≫
      ((pullbackComp (C.fromSpecResidueField (genericPoint C)) i).app L).inv) ≫
        (closedGenericFrame i U hη e).hom =
      ModularCurves.unitEndomorphismOfTopSection ((closedOpenFactor i U hη).appTop.hom r) := by
    simpa only [closedGenericFrame, frameViaFactor, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc] using hf
  have hv := congrArg sectionAtOne hwhole
  change (closedGenericFrame i U hη e).hom.val.app (op ⊤)
    (closedGenericSection i L U hη δ) =
      sectionAtOne (ModularCurves.unitEndomorphismOfTopSection
        ((closedOpenFactor i U hη).appTop.hom r)) at hv
  exact hv.trans (scalar_at_one _)

private theorem closedGenericFrame_restrict {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) {L : Y.Modules} (U V : Y.Opens) (hVU : V ≤ U)
    (hη : i (genericPoint C) ∈ V)
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    closedGenericFrame i V hη
      (frameViaFactor (Y.homOfLE hVU) U.ι V.ι (Y.homOfLE_ι hVU) e) =
        closedGenericFrame i U (hVU hη) e := by
  have hfactor : closedOpenFactor i V hη ≫ Y.homOfLE hVU =
      closedOpenFactor i U (hVU hη) := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, Y.homOfLE_ι, closedOpenFactor_comp, closedOpenFactor_comp]
  unfold closedGenericFrame
  rw [frameViaFactor_comp]
  simp only [hfactor]

private theorem openTopSection_eq_appLE {Y : Scheme.{u}} (U : Y.Opens) (c : Γ(Y, U)) :
    openTopSection U c = (U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom c := by
  rw [openTopSection, Scheme.Opens.ι_appIso, Scheme.Opens.ι_appLE]
  change (Y.presheaf.map (eqToHom U.ι_image_top).op).hom c = _
  apply ConcreteCategory.congr_hom
  apply Y.presheaf.congr_map
  exact Subsingleton.elim _ _

private theorem closedOpenFactor_coefficient {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (U : Y.Opens) (hη : i (genericPoint C) ∈ U) (c : Γ(Y, U)) :
    (Scheme.ΓSpecIso (C.residueField (genericPoint C))).hom.hom
      ((closedOpenFactor i U hη).appTop.hom (openTopSection U c)) =
        C.residue (genericPoint C)
          (i.stalkMap (genericPoint C) (Y.presheaf.germ U (i (genericPoint C)) hη c)) := by
  have hξ : genericPoint C ∈ i ⁻¹ᵁ U := by
    change i (genericPoint C) ∈ U
    exact hη
  let g := closedOpenFactor i U hη
  have htop : ⊤ ≤ g ⁻¹ᵁ (⊤ : U.toScheme.Opens) := le_top
  have he := Scheme.Hom.appLE_comp_appLE g U.ι U ⊤ ⊤ U.ι_preimage_self.ge htop
  have ht : g.appLE ⊤ ⊤ htop = g.appTop := by
    unfold Scheme.Hom.appLE
    change g.appTop ≫ (Spec (C.residueField (genericPoint C))).presheaf.map
      (𝟙 (op (⊤ : (Spec (C.residueField (genericPoint C))).Opens))) = g.appTop
    rw [(Spec (C.residueField (genericPoint C))).presheaf.map_id, Category.comp_id]
  have hpre : ⊤ ≤ C.fromSpecResidueField (genericPoint C) ⁻¹ᵁ (i ⁻¹ᵁ U) := by
    rw [Berkovich.SchemeValuedPoint.fromSpecResidueField_preimage_eq_top (genericPoint C)
      (i ⁻¹ᵁ U) hξ]
  have hcomp := Scheme.Hom.appLE_comp_appLE (C.fromSpecResidueField (genericPoint C))
    i U (i ⁻¹ᵁ U) ⊤ le_rfl hpre
  have hi : i.appLE U (i ⁻¹ᵁ U) le_rfl = i.app U := by
    unfold Scheme.Hom.appLE
    change i.app U ≫ C.presheaf.map (𝟙 (op (i ⁻¹ᵁ U))) = i.app U
    rw [C.presheaf.map_id, Category.comp_id]
  have hfun : ∀ h : ⊤ ≤ (g ≫ U.ι) ⁻¹ᵁ U,
      (g ≫ U.ι).appLE U ⊤ h ≫ (Scheme.ΓSpecIso (C.residueField (genericPoint C))).hom =
        i.app U ≫ C.evaluation (i ⁻¹ᵁ U) (genericPoint C) hξ := by
    dsimp only [g]
    rw [closedOpenFactor_comp]
    intro h
    rw [← hcomp, hi, Category.assoc]
    rw [Berkovich.SchemeValuedPoint.fromSpecResidueField_appLE_top]
  have hall : U.ι.appLE U ⊤ U.ι_preimage_self.ge ≫ g.appTop ≫
      (Scheme.ΓSpecIso (C.residueField (genericPoint C))).hom =
        i.app U ≫ C.evaluation (i ⁻¹ᵁ U) (genericPoint C) hξ := by
    rw [← ht, ← Category.assoc, he]
    exact hfun _
  rw [openTopSection_eq_appLE]
  have hv := congrArg (fun f : Γ(Y, U) ⟶ C.residueField (genericPoint C) => f.hom c) hall
  change _ = C.residue (genericPoint C)
    (C.presheaf.germ (i ⁻¹ᵁ U) (genericPoint C) hξ ((i.app U).hom c)) at hv
  exact hv.trans (congrArg (C.residue (genericPoint C))
    (i.germ_stalkMap_apply U (genericPoint C) hη c).symm)

/-- The SAME actual prescribed nonzero central generic section is the
exact original generic restriction of an actual ambient local section
isomorphism. All frames and unit lifts are produced internally. -/
theorem exists_local_section_lift {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) [IsClosedImmersion i] (L : Y.Modules) (hL : IsInvertible L)
    (σ : Γ((pullback (C.fromSpecResidueField (genericPoint C))).obj ((pullback i).obj L), ⊤))
    (hσ : σ ≠ 0) :
    ∃ (V : Y.Opens) (hηV : i (genericPoint C) ∈ V)
      (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L),
      IsIso δ ∧ closedGenericSection i L V hηV δ = σ := by
  obtain ⟨ι, O, hO, hframe⟩ := hL
  have hηO : i (genericPoint C) ∈ iSup O := by rw [hO]; trivial
  obtain ⟨j, hη⟩ := Opens.mem_iSup.mp hηO
  obtain ⟨e⟩ := hframe j
  let U := O j
  let E := closedGenericFrame i U hη e
  let b := (Scheme.ΓSpecIso (C.residueField (genericPoint C))).hom.hom
    ((E.hom.val.app (op ⊤)).hom σ)
  have hb : b ≠ 0 := by
    intro hb
    apply hσ
    apply iso_top_injective E
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (C.residueField (genericPoint C))).hom).1
    have hzero := (E.hom.val.app (op ⊤)).hom.map_zero
    calc
      (Scheme.ΓSpecIso (C.residueField (genericPoint C))).hom.hom
          ((E.hom.val.app (op ⊤)).hom σ) = 0 := hb
      _ = (Scheme.ΓSpecIso (C.residueField (genericPoint C))).hom.hom
          ((E.hom.val.app (op ⊤)).hom 0) :=
        ((congrArg (Scheme.ΓSpecIso (C.residueField (genericPoint C))).hom.hom hzero).trans
          (Scheme.ΓSpecIso (C.residueField (genericPoint C))).hom.hom.map_zero).symm
  obtain ⟨b₀, hb₀⟩ := C.residue_surjective (genericPoint C) b
  have hb₀ne : (b₀ : C.functionField) ≠ 0 := by
    intro hzero
    apply hb
    rw [← hb₀, hzero, map_zero]
  obtain ⟨a, ha, hab⟩ := exists_unit_lift i b₀ hb₀ne
  obtain ⟨V, hVU, hηV, c, hc⟩ := exists_unit_neighborhood (i (genericPoint C)) a ha U hη
  let eV := frameViaFactor (Y.homOfLE hVU) U.ι V.ι (Y.homOfLE_ι hVU) e
  let cv : Γ(V.toScheme, ⊤)ˣ :=
    Units.map (V.ι.appLE V ⊤ V.ι_preimage_self.ge).hom c
  let δ := (ModularCurves.unitAutomorphismOfTopUnit cv).hom ≫ eV.inv
  have hcv : (cv : Γ(V.toScheme, ⊤)) = openTopSection V (c : Γ(Y, V)) :=
    (openTopSection_eq_appLE V (c : Γ(Y, V))).symm
  have hδ : δ ≫ eV.hom =
      ModularCurves.unitEndomorphismOfTopSection (cv : Γ(V.toScheme, ⊤)) := by
    dsimp only [δ]
    rw [Category.assoc, eV.inv_hom_id, Category.comp_id]
    rfl
  have hE : closedGenericFrame i V hηV eV = E :=
    closedGenericFrame_restrict i U V hVU hηV e
  refine ⟨V, hηV, δ, inferInstance, ?_⟩
  apply iso_top_injective E
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (C.residueField (genericPoint C))).hom).1
  have hv : (E.hom.val.app (op ⊤)).hom (closedGenericSection i L V hηV δ) =
      (closedOpenFactor i V hηV).appTop.hom (cv : Γ(V.toScheme, ⊤)) := by
    rw [← hE]
    exact closedGenericSection_coefficient i V hηV eV δ _ hδ
  rw [hv]
  change (Scheme.ΓSpecIso (C.residueField (genericPoint C))).hom.hom
    ((closedOpenFactor i V hηV).appTop.hom (cv : Γ(V.toScheme, ⊤))) = b
  rw [hcv, closedOpenFactor_coefficient, hc, hab, hb₀]

private theorem generic_mem {Y : Scheme.{u}} [IsIntegral Y]
    (U : Y.Opens) [Nonempty U] : genericPoint Y ∈ U :=
  ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- The actual ambient rational section of the SAME line, obtained from
the SAME actual original local section by native generic pullback. -/
def genericSection {Y : Scheme.{u}} [IsIntegral Y]
    (L : Y.Modules) (U : Y.Opens) [Nonempty U]
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L) :
    Γ((pullback (Y.fromSpecResidueField (genericPoint Y))).obj L, ⊤) :=
  sectionAtOne (pullbackSectionHom (residueOpenFactor (genericPoint Y) U (generic_mem U)) δ ≫
    (frameFactorIso (residueOpenFactor (genericPoint Y) U (generic_mem U)) U.ι
      (Y.fromSpecResidueField (genericPoint Y))
      (residueOpenFactor_comp (genericPoint Y) U (generic_mem U)) L).hom)

private theorem genericSection_ne_zero {Y : Scheme.{u}} [IsIntegral Y]
    (L : Y.Modules) (U : Y.Opens) [Nonempty U]
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L) [IsIso δ] :
    genericSection L U δ ≠ 0 := by
  let α := pullbackSectionHom (residueOpenFactor (genericPoint Y) U (generic_mem U)) δ ≫
    (frameFactorIso (residueOpenFactor (genericPoint Y) U (generic_mem U)) U.ι
      (Y.fromSpecResidueField (genericPoint Y))
      (residueOpenFactor_comp (genericPoint Y) U (generic_mem U)) L).hom
  have hα : IsIso α := by
    dsimp only [α, pullbackSectionHom]
    infer_instance
  let := hα
  intro hz
  have hzero := (α.val.app (op ⊤)).hom.map_zero
  have he : (α.val.app (op ⊤)).hom
      (show Γ(Spec (Y.residueField (genericPoint Y)), ⊤) from 1) =
    (α.val.app (op ⊤)).hom
      (show Γ(Spec (Y.residueField (genericPoint Y)), ⊤) from 0) :=
    hz.trans hzero.symm
  have h := iso_top_injective (asIso α) he
  have hb := congrArg (Scheme.ΓSpecIso (Y.residueField (genericPoint Y))).hom.hom h
  rw [map_one, map_zero] at hb
  exact one_ne_zero hb

/-- The prescribed central section and the nonzero ambient generic ρ
come from the SAME produced actual local section isomorphism. -/
theorem exists_generic_section_lift {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    (i : C ⟶ Y) [IsClosedImmersion i] (L : Y.Modules) (hL : IsInvertible L)
    (σ : Γ((pullback (C.fromSpecResidueField (genericPoint C))).obj ((pullback i).obj L), ⊤))
    (hσ : σ ≠ 0) :
    ∃ (V : Y.Opens) (hηV : i (genericPoint C) ∈ V)
      (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L),
      IsIso δ ∧ closedGenericSection i L V hηV δ = σ ∧
      ∃ (hV : Nonempty V)
        (ρ : Γ((pullback (Y.fromSpecResidueField (genericPoint Y))).obj L, ⊤)),
        ρ = @genericSection Y _ L V hV δ ∧ ρ ≠ 0 := by
  obtain ⟨V, hηV, δ, hδ, he⟩ := exists_local_section_lift i L hL σ hσ
  let : IsIso δ := hδ
  let hV : Nonempty V := ⟨⟨i (genericPoint C), hηV⟩⟩
  exact ⟨V, hηV, δ, hδ, he, hV, genericSection L V δ, rfl, genericSection_ne_zero L V δ⟩

end EnvelopeProperty.CentralGenericLineSectionLift
