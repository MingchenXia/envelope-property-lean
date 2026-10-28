import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalSectionRegaugingGauge
import EnvelopeProperty.AlgGeom.CentralGenericLineSectionLift
import EnvelopeProperty.Local.PLGaussLeadingResidueNaturality

/-! # Actual two-frame line coefficients on the same ambient and central schemes -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Classical
universe u
namespace EnvelopeProperty.NumericalGaussCurveLineOrders
open Scheme.Modules SchemeLineSectionEvaluation SchemeLineSectionFactorization
open NumericalSectionRegauging NumericalSectionRegaugingOriginal NumericalSectionRegaugingGauge

private theorem pullbackSection_isIso {B C : Scheme.{u}} (g : B ⟶ C)
    {M : C.Modules} (δ : unitObj C ⟶ M) [IsIso δ] : IsIso (pullbackSectionHom g δ) := by
  dsimp only [pullbackSectionHom]
  infer_instance

private theorem restrictSection_isIso {Y : Scheme.{u}} (L : Y.Modules)
    (U : Y.Opens) (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L) [IsIso δ]
    (W : Y.Opens) (hWU : W ≤ U) : IsIso (restrictLocalSection L U δ W hWU) :=
  IsIso.comp_isIso' (pullbackSection_isIso (Y.homOfLE hWU) δ)
    (frameFactorIso (Y.homOfLE hWU) U.ι W.ι (Y.homOfLE_ι hWU) L).isIso_hom

private theorem twoFrames_transition {B : Scheme.{u}} {M : B.Modules}
    (δ ε : unitObj B ⟶ M) [IsIso δ] [IsIso ε] :
    ∃ a : Γ(B, ⊤)ˣ,
      δ = ModularCurves.unitEndomorphismOfTopSection (a : Γ(B, ⊤)) ≫ ε := by
  obtain ⟨a,ha⟩ := unitIso_eq_globalUnit ((asIso δ) ≪≫ (asIso ε).symm)
  have h := congrArg (fun E : unitObj B ≅ unitObj B => E.hom ≫ ε) ha
  change (δ ≫ inv ε) ≫ ε = ModularCurves.unitEndomorphismOfTopSection (a : Γ(B, ⊤)) ≫ ε at h
  exact ⟨a,by simpa only [Category.assoc,IsIso.inv_hom_id,Category.comp_id] using h⟩

private theorem exists_frame_at {Y : Scheme.{u}} (L : Y.Modules) (hL : IsInvertible L)
    (p : Y) :
    ∃ (V : Y.Opens) (_hp : p ∈ V)
      (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L), IsIso δ := by
  obtain ⟨ι,O,hO,hframe⟩ := hL
  have hp : p ∈ iSup O := by rw [hO]; trivial
  obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hp
  obtain ⟨e⟩ := hframe j
  exact ⟨O j,hj,e.inv,e.isIso_inv⟩


private theorem factorSection_comp {A B C D : Scheme.{u}}
    (i : A ⟶ B) (g : B ⟶ C) (b : C ⟶ D) (f : B ⟶ D) (hg : g ≫ b = f)
    (w : A ⟶ D) (hi : i ≫ f = w) {M : D.Modules}
    (δ : unitObj C ⟶ (pullback b).obj M) [IsIso δ] :
    pullbackSectionHom i (pullbackSectionHom g δ ≫ (frameFactorIso g b f hg M).hom) ≫
      (frameFactorIso i f w hi M).hom =
    pullbackSectionHom (i ≫ g) δ ≫
      (frameFactorIso (i ≫ g) b w (by rw [Category.assoc,hg]; exact hi) M).hom := by
  have h := congrArg (fun E : (pullback w).obj M ≅ unitObj A => E.inv)
    (frameViaFactor_comp i g b f hg w hi (asIso δ).symm)
  simpa only [frameViaFactor,Iso.trans_inv,Iso.symm_inv,Functor.mapIso_inv,
    show (asIso δ).hom = δ from rfl, pullbackSectionHom,Category.assoc] using h

private theorem factorSection_congr {A B C : Scheme.{u}}
    (g g' : A ⟶ B) (hg : g = g') (b : B ⟶ C) (p : A ⟶ C)
    (hp : g ≫ b = p) (hp' : g' ≫ b = p) {M : C.Modules}
    (δ : unitObj B ⟶ (pullback b).obj M) :
    pullbackSectionHom g δ ≫ (frameFactorIso g b p hp M).hom =
      pullbackSectionHom g' δ ≫ (frameFactorIso g' b p hp' M).hom := by
  subst g'
  rfl

private theorem sectionAtOne_scalar {B : Scheme.{u}} {M : B.Modules}
    (r : Γ(B, ⊤)) (β : unitObj B ⟶ M) :
    sectionAtOne (ModularCurves.unitEndomorphismOfTopSection r ≫ β) =
      r • sectionAtOne β := by
  have hr : sectionAtOne (ModularCurves.unitEndomorphismOfTopSection r) = r := by
    rw [sectionAtOne,ModularCurves.unitEndomorphismOfTopSection_app_apply]
    simp only [homOfLE_refl,op_id,one_mul]
    erw [CategoryTheory.Functor.map_id]
    rfl
  change β.val.app (op ⊤) (sectionAtOne (ModularCurves.unitEndomorphismOfTopSection r)) = _
  rw [hr]
  have h := (β.val.app (op ⊤)).hom.map_smul r
    (show Γ(unitObj B, ⊤) from (1 : Γ(B, ⊤)))
  have ho : r • (show Γ(unitObj B, ⊤) from (1 : Γ(B, ⊤))) =
      (show Γ(unitObj B, ⊤) from r) := by
    change (r : Γ(B, ⊤)) * (1 : Γ(B, ⊤)) = r
    exact mul_one r
  exact (congrArg (fun t => β.val.app (op ⊤) t) ho.symm).trans h


private def localValue {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) (L : D.Modules)
    (δ : unitObj C ⟶ (pullback b).obj L) : Γ((pullback f).obj L, ⊤) :=
  sectionAtOne (pullbackSectionHom g δ ≫ (frameFactorIso g b f hg L).hom)

private theorem localValue_scalar {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) (L : D.Modules)
    (r : Γ(C, ⊤)) (δ : unitObj C ⟶ (pullback b).obj L) :
    localValue g b f hg L (ModularCurves.unitEndomorphismOfTopSection r ≫ δ) =
      g.appTop.hom r • localValue g b f hg L δ := by
  dsimp only [localValue]
  rw [pullbackSectionHom_precomp_scalar,Category.assoc]
  exact sectionAtOne_scalar _ _

private theorem localValue_restrict {B Y : Scheme.{u}} (L : Y.Modules)
    (U : Y.Opens) (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L) [IsIso δ]
    (W : Y.Opens) (hWU : W ≤ U) (f : B ⟶ Y)
    (q : B ⟶ W.toScheme) (hq : q ≫ W.ι = f)
    (r : B ⟶ U.toScheme) (hr : r ≫ U.ι = f) :
    localValue q W.ι f hq L (restrictLocalSection L U δ W hWU) =
      localValue r U.ι f hr L δ := by
  have hqr : q ≫ Y.homOfLE hWU = r := by
    apply (cancel_mono U.ι).mp
    exact ((Category.assoc _ _ _).trans (congrArg (fun a => q ≫ a) (Y.homOfLE_ι hWU))).trans
      (hq.trans hr.symm)
  exact congrArg sectionAtOne
    ((factorSection_comp q (Y.homOfLE hWU) U.ι W.ι (Y.homOfLE_ι hWU) f hq δ).trans
      (factorSection_congr _ r hqr U.ι f _ hr δ))

private def genericFactor {Y : Scheme.{u}} (p : Y) (U : Y.Opens) (hp : p ∈ U) :
    Spec (Y.residueField p) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (Y.fromSpecResidueField p) (by
    rw [U.range_ι]
    rintro _ ⟨z,rfl⟩
    change Y.fromSpecResidueField p z ∈ U
    rw [Scheme.fromSpecResidueField_apply]
    exact hp)

private theorem genericFactor_comp {Y : Scheme.{u}} (p : Y)
    (U : Y.Opens) (hp : p ∈ U) :
    genericFactor p U hp ≫ U.ι = Y.fromSpecResidueField p := IsOpenImmersion.lift_fac _ _ _

private theorem genericSection_eq_localValue {Y : Scheme.{u}} [IsIntegral Y]
    (L : Y.Modules) (U : Y.Opens) [Nonempty U]
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L)
    (hη : genericPoint Y ∈ U) :
    CentralGenericLineSectionLift.genericSection L U δ =
      localValue (genericFactor (genericPoint Y) U hη) U.ι
        (Y.fromSpecResidueField (genericPoint Y))
        (genericFactor_comp (genericPoint Y) U hη) L δ := by
  rfl

private def closedFactor {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (U : Y.Opens) (hη : i (genericPoint C) ∈ U) :
    Spec (C.residueField (genericPoint C)) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (C.fromSpecResidueField (genericPoint C) ≫ i) (by
    rw [U.range_ι]
    rintro _ ⟨z,rfl⟩
    change i (C.fromSpecResidueField (genericPoint C) z) ∈ U
    rw [Scheme.fromSpecResidueField_apply]
    exact hη)

private theorem closedFactor_comp {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (U : Y.Opens) (hη : i (genericPoint C) ∈ U) :
    closedFactor i U hη ≫ U.ι = C.fromSpecResidueField (genericPoint C) ≫ i :=
  IsOpenImmersion.lift_fac _ _ _

private theorem closedGenericSection_eq_localValue {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (L : Y.Modules) (U : Y.Opens) (hη : i (genericPoint C) ∈ U)
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L) :
    CentralGenericLineSectionLift.closedGenericSection i L U hη δ =
      (((pullbackComp (C.fromSpecResidueField (genericPoint C)) i).app L).inv.val.app (op ⊤))
        (localValue (closedFactor i U hη) U.ι
          (C.fromSpecResidueField (genericPoint C) ≫ i) (closedFactor_comp i U hη) L δ) := by
  rfl


private theorem twoFrame_value {B Y : Scheme.{u}} (L : Y.Modules)
    (U V : Y.Opens) (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L)
    (ε : unitObj V.toScheme ⟶ (pullback V.ι).obj L) [IsIso δ] [IsIso ε]
    (W : Y.Opens) (hWU : W ≤ U) (hWV : W ≤ V)
    (a : Γ(W.toScheme, ⊤))
    (ha : restrictLocalSection L U δ W hWU = ModularCurves.unitEndomorphismOfTopSection a ≫
      restrictLocalSection L V ε W hWV)
    (f : B ⟶ Y) (q : B ⟶ W.toScheme) (hq : q ≫ W.ι = f)
    (rU : B ⟶ U.toScheme) (hU : rU ≫ U.ι = f)
    (rV : B ⟶ V.toScheme) (hV : rV ≫ V.ι = f) :
    localValue rU U.ι f hU L δ = q.appTop.hom a • localValue rV V.ι f hV L ε := by
  have hu := localValue_restrict L U δ W hWU f q hq rU hU
  have hv := localValue_restrict L V ε W hWV f q hq rV hV
  exact hu.symm.trans ((congrArg (localValue q W.ι f hq L) ha).trans
    ((localValue_scalar q W.ι f hq L a _).trans
      (congrArg (fun t => q.appTop.hom a • t) hv)))

private theorem openTopSection_eq_appLE {Y : Scheme.{u}} (U : Y.Opens) (c : Γ(Y, U)) :
    openTopSection U c = (U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom c := by
  rw [openTopSection, Scheme.Opens.ι_appIso, Scheme.Opens.ι_appLE]
  change (Y.presheaf.map (eqToHom U.ι_image_top).op).hom c = _
  apply ConcreteCategory.congr_hom
  apply Y.presheaf.congr_map
  exact Subsingleton.elim _ _

private theorem closedFactor_coefficient {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (U : Y.Opens) (hη : i (genericPoint C) ∈ U) (c : Γ(Y, U)) :
    (Scheme.ΓSpecIso (C.residueField (genericPoint C))).hom.hom
      ((closedFactor i U hη).appTop.hom (openTopSection U c)) =
        C.residue (genericPoint C)
          (i.stalkMap (genericPoint C) (Y.presheaf.germ U (i (genericPoint C)) hη c)) := by
  have hξ : genericPoint C ∈ i ⁻¹ᵁ U := by
    change i (genericPoint C) ∈ U
    exact hη
  let g := closedFactor i U hη
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
    rw [closedFactor_comp]
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


private theorem genericFactor_coefficient {Y : Scheme.{u}}
    (x : Y) (V : Y.Opens) (hx : x ∈ V) (c : Γ(Y,V)) :
    (Scheme.ΓSpecIso (Y.residueField x)).hom.hom
      ((genericFactor x V hx).appTop.hom (openTopSection V c)) =
        Y.evaluation V x hx c := by
  rw [openTopSection_eq_appLE]
  let g := genericFactor x V hx
  have htop : ⊤ ≤ g ⁻¹ᵁ (⊤ : V.toScheme.Opens) := le_top
  have he := Scheme.Hom.appLE_comp_appLE g V.ι V ⊤ ⊤ V.ι_preimage_self.ge htop
  have ht : g.appLE ⊤ ⊤ htop = g.appTop := by
    unfold Scheme.Hom.appLE
    change g.appTop ≫ (Spec (Y.residueField x)).presheaf.map
      (𝟙 (op (⊤ : (Spec (Y.residueField x)).Opens))) = g.appTop
    rw [(Spec (Y.residueField x)).presheaf.map_id, Category.comp_id]
  have hfun : ∀ h : ⊤ ≤ (g ≫ V.ι) ⁻¹ᵁ V,
      (g ≫ V.ι).appLE V ⊤ h ≫
        (Scheme.ΓSpecIso (Y.residueField x)).hom = Y.evaluation V x hx := by
    dsimp only [g]
    rw [genericFactor_comp]
    intro h
    exact Berkovich.SchemeValuedPoint.fromSpecResidueField_appLE_top _ _ _ _
  have hcomp : V.ι.appLE V ⊤ V.ι_preimage_self.ge ≫ g.appTop ≫
      (Scheme.ΓSpecIso (Y.residueField x)).hom = Y.evaluation V x hx := by
    rw [← ht, ← Category.assoc, he]
    exact hfun _
  exact congrArg (fun q : Γ(Y,V) ⟶ Y.residueField x => q.hom c) hcomp



private def genericScalar (X : Scheme.{u}) [IsIntegral X] (f : X.functionField) :
    Γ(Spec (X.residueField (genericPoint X)), ⊤) :=
  (Scheme.ΓSpecIso (X.residueField (genericPoint X))).inv.hom (X.residue (genericPoint X) f)

private theorem genericScalar_spec (X : Scheme.{u}) [IsIntegral X] (f : X.functionField) :
    (Scheme.ΓSpecIso (X.residueField (genericPoint X))).hom.hom (genericScalar X f) =
      X.residue (genericPoint X) f :=
  (Scheme.ΓSpecIso (X.residueField (genericPoint X))).commRingCatIsoToRingEquiv.apply_symm_apply _

private theorem genericScalar_germ {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (hη : genericPoint X ∈ U) (r : Γ(X,U)) :
    genericScalar X (X.germToFunctionField U r) =
      (genericFactor (genericPoint X) U hη).appTop.hom (openTopSection U r) := by
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (X.residueField (genericPoint X))).hom).1
  exact (genericScalar_spec X _).trans (genericFactor_coefficient (genericPoint X) U hη r).symm

private theorem genericSection_restrict {Y : Scheme.{u}} [IsIntegral Y]
    (L : Y.Modules) (U : Y.Opens) [Nonempty U]
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L) [IsIso δ]
    (W : Y.Opens) [Nonempty W] (hWU : W ≤ U) (hη : genericPoint Y ∈ W) :
    CentralGenericLineSectionLift.genericSection L W (restrictLocalSection L U δ W hWU) =
      CentralGenericLineSectionLift.genericSection L U δ :=
  (genericSection_eq_localValue L W _ hη).trans
    ((localValue_restrict L U δ W hWU (Y.fromSpecResidueField (genericPoint Y))
      (genericFactor (genericPoint Y) W hη) (genericFactor_comp _ _ _)
      (genericFactor (genericPoint Y) U (hWU hη)) (genericFactor_comp _ _ _)).trans
      (genericSection_eq_localValue L U δ (hWU hη)).symm)

private theorem closedGenericSection_restrict {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (L : Y.Modules) (U : Y.Opens)
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L) [IsIso δ]
    (W : Y.Opens) (hWU : W ≤ U) (hη : i (genericPoint C) ∈ W) :
    CentralGenericLineSectionLift.closedGenericSection i L W hη (restrictLocalSection L U δ W hWU) =
      CentralGenericLineSectionLift.closedGenericSection i L U (hWU hη) δ := by
  have h := localValue_restrict L U δ W hWU (C.fromSpecResidueField (genericPoint C) ≫ i)
    (closedFactor i W hη) (closedFactor_comp i W hη)
    (closedFactor i U (hWU hη)) (closedFactor_comp i U (hWU hη))
  have hv := congrArg
    (((pullbackComp (C.fromSpecResidueField (genericPoint C)) i).app L).inv.val.app (op ⊤)) h
  exact (closedGenericSection_eq_localValue i L W hη _).trans
    (hv.trans (closedGenericSection_eq_localValue i L U (hWU hη) δ).symm)


private theorem closedGenericSection_scalar {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (L : Y.Modules) (U : Y.Opens) (hη : i (genericPoint C) ∈ U)
    (a : Γ(U.toScheme, ⊤)) (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L) :
    CentralGenericLineSectionLift.closedGenericSection i L U hη
        (ModularCurves.unitEndomorphismOfTopSection a ≫ δ) =
      (closedFactor i U hη).appTop.hom a •
        CentralGenericLineSectionLift.closedGenericSection i L U hη δ := by
  let A := ((pullbackComp (C.fromSpecResidueField (genericPoint C)) i).app L).inv.val.app (op ⊤)
  exact (closedGenericSection_eq_localValue i L U hη _).trans
    ((congrArg A (localValue_scalar (closedFactor i U hη) U.ι
      (C.fromSpecResidueField (genericPoint C) ≫ i) (closedFactor_comp i U hη) L a δ)).trans
      ((A.hom.map_smul _ _).trans
        (congrArg (fun z => (closedFactor i U hη).appTop.hom a • z)
          (closedGenericSection_eq_localValue i L U hη δ).symm)))

/-- A single original generic section gives both actual coefficient squares for an
internally chosen frame at any point of the original central scheme. -/
theorem exists_twoFrame_coefficients {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    (i : C ⟶ Y) (L : Y.Modules) (hL : IsInvertible L)
    (U : Y.Opens) (hηU : i (genericPoint C) ∈ U)
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L) [IsIso δ] (x : C) :
    letI : Nonempty U := ⟨⟨i (genericPoint C), hηU⟩⟩
    ∃ (V : Y.Opens) (hpV : i x ∈ V) (hηV : i (genericPoint C) ∈ V)
      (ε : unitObj V.toScheme ⟶ (pullback V.ι).obj L) (_hε : IsIso ε)
      (W : Y.Opens) (hWU : W ≤ U) (hWV : W ≤ V) (hηW : i (genericPoint C) ∈ W)
      (r : Γ(Y,W)ˣ) (u : (Y.presheaf.stalk (i (genericPoint C)))ˣ)
      (f : Y.functionField) (b : C.functionField),
      restrictLocalSection L U δ W hWU =
        ModularCurves.unitEndomorphismOfTopSection (openTopSection W (r : Γ(Y,W))) ≫
          restrictLocalSection L V ε W hWV ∧
      (u : Y.presheaf.stalk (i (genericPoint C))) =
        Y.presheaf.germ W (i (genericPoint C)) hηW (r : Γ(Y,W)) ∧
      f = @Scheme.germToFunctionField Y _ W ⟨⟨i (genericPoint C),hηW⟩⟩ (r : Γ(Y,W)) ∧
      b = i.stalkMap (genericPoint C) (u : Y.presheaf.stalk (i (genericPoint C))) ∧
      f = algebraMap (Y.presheaf.stalk (i (genericPoint C))) Y.functionField u ∧
      f ≠ 0 ∧ b ≠ 0 ∧
      (letI : Nonempty V := ⟨⟨i x,hpV⟩⟩
       CentralGenericLineSectionLift.genericSection L U δ =
         (Scheme.ΓSpecIso (Y.residueField (genericPoint Y))).inv.hom
           (Y.residue (genericPoint Y) f) • CentralGenericLineSectionLift.genericSection L V ε) ∧
      CentralGenericLineSectionLift.closedGenericSection i L U hηU δ =
        (Scheme.ΓSpecIso (C.residueField (genericPoint C))).inv.hom
          (C.residue (genericPoint C) b) •
            CentralGenericLineSectionLift.closedGenericSection i L V hηV ε := by
  let : Nonempty U := ⟨⟨i (genericPoint C),hηU⟩⟩
  obtain ⟨V,hpV,ε,hε⟩ := exists_frame_at L hL (i x)
  let : IsIso ε := hε
  have hηV : i (genericPoint C) ∈ V :=
    ((genericPoint_spec C).specializes trivial).mem_open (i ⁻¹ᵁ V).isOpen hpV
  let W := U ⊓ V
  have hWU : W ≤ U := inf_le_left
  have hWV : W ≤ V := inf_le_right
  have hηW : i (genericPoint C) ∈ W := ⟨hηU,hηV⟩
  let : Nonempty W := ⟨⟨i (genericPoint C),hηW⟩⟩
  let : Nonempty V := ⟨⟨i x,hpV⟩⟩
  let := restrictSection_isIso L U δ W hWU
  let := restrictSection_isIso L V ε W hWV
  obtain ⟨a,ha⟩ := twoFrames_transition
    (restrictLocalSection L U δ W hWU) (restrictLocalSection L V ε W hWV)
  let r : Γ(Y,W)ˣ := Units.map W.topIso.hom.hom.toMonoidHom a
  have hr : openTopSection W (r : Γ(Y,W)) = (a : Γ(W.toScheme,⊤)) := by
    change openTopSection W (W.topIso.hom.hom (a : Γ(W.toScheme,⊤))) = _
    rw [openTopSection,Scheme.Opens.ι_appIso]
    change W.topIso.inv.hom (W.topIso.hom.hom (a : Γ(W.toScheme,⊤))) = _
    exact ConcreteCategory.congr_hom W.topIso.hom_inv_id (a : Γ(W.toScheme,⊤))
  have htrans : restrictLocalSection L U δ W hWU =
      ModularCurves.unitEndomorphismOfTopSection (openTopSection W (r : Γ(Y,W))) ≫
        restrictLocalSection L V ε W hWV :=
    ha.trans (congrArg (fun q => ModularCurves.unitEndomorphismOfTopSection q ≫
      restrictLocalSection L V ε W hWV) hr.symm)
  let u : (Y.presheaf.stalk (i (genericPoint C)))ˣ :=
    Units.map (Y.presheaf.germ W (i (genericPoint C)) hηW).hom.toMonoidHom r
  let f := Y.germToFunctionField W (r : Γ(Y,W))
  let b : C.functionField := i.stalkMap (genericPoint C) (u : Y.presheaf.stalk (i (genericPoint C)))
  have hf : f = algebraMap (Y.presheaf.stalk (i (genericPoint C))) Y.functionField u :=
    (Y.algebraMap_germ_eq_germToFunctionField hηW (r : Γ(Y,W))).symm
  have hf0 : f ≠ 0 := by
    rw [hf]
    exact (u.isUnit.map (algebraMap _ _)).ne_zero
  have hb0 : b ≠ 0 := (u.isUnit.map (i.stalkMap (genericPoint C)).hom).ne_zero
  have hGY := twoFrame_value L U V δ ε W hWU hWV _ htrans
    (Y.fromSpecResidueField (genericPoint Y))
    (genericFactor (genericPoint Y) W (CanonicalGeometry.genericPoint_mem_nonempty_open W))
    (genericFactor_comp _ _ _)
    (genericFactor (genericPoint Y) U (CanonicalGeometry.genericPoint_mem_nonempty_open U))
    (genericFactor_comp _ _ _)
    (genericFactor (genericPoint Y) V (CanonicalGeometry.genericPoint_mem_nonempty_open V))
    (genericFactor_comp _ _ _)
  have hGY' : CentralGenericLineSectionLift.genericSection L U δ =
      genericScalar Y f • CentralGenericLineSectionLift.genericSection L V ε :=
    (genericSection_eq_localValue L U δ _).trans
      (hGY.trans (congrArg₂ (fun q z => q • z)
        (genericScalar_germ W _ (r : Γ(Y,W))).symm
        (genericSection_eq_localValue L V ε _).symm))
  have hcb : (closedFactor i W hηW).appTop.hom (openTopSection W (r : Γ(Y,W))) =
      genericScalar C b := by
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (C.residueField (genericPoint C))).hom).1
    exact (closedFactor_coefficient i W hηW (r : Γ(Y,W))).trans (genericScalar_spec C b).symm
  have hGC := twoFrame_value L U V δ ε W hWU hWV _ htrans
    (C.fromSpecResidueField (genericPoint C) ≫ i)
    (closedFactor i W hηW) (closedFactor_comp i W hηW)
    (closedFactor i U hηU) (closedFactor_comp i U hηU)
    (closedFactor i V hηV) (closedFactor_comp i V hηV)
  let A := ((pullbackComp (C.fromSpecResidueField (genericPoint C)) i).app L).inv.val.app (op ⊤)
  have hGC' : CentralGenericLineSectionLift.closedGenericSection i L U hηU δ =
      genericScalar C b • CentralGenericLineSectionLift.closedGenericSection i L V hηV ε :=
    (closedGenericSection_eq_localValue i L U hηU δ).trans
      ((congrArg A hGC).trans ((A.hom.map_smul _ _).trans
        (congrArg₂ (fun q z => q • z) hcb
          (closedGenericSection_eq_localValue i L V hηV ε).symm)))
  exact ⟨V,hpV,hηV,ε,hε,W,hWU,hWV,hηW,r,u,f,b,htrans,rfl,rfl,rfl,hf,hf0,hb0,hGY',hGC'⟩


/-- The actual component-generic stalk unit has zero vertical order and the exact
original central-curve order in the SAME eventual weighted valuation family. -/
theorem unit_stalk_leading_order {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    (i : C ⟶ Y) [IsClosedImmersion i] (x : C)
    [IsNoetherianRing (Y.presheaf.stalk (i x))] [IsLocallyNoetherian C]
    (π z : Y.presheaf.stalk (i x)) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : IsLocalRing.maximalIdeal (Y.presheaf.stalk (i x)) = Ideal.span {π,z})
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π})
    (hdim : topologicalKrullDim C ≤ 1) (hx : x ≠ genericPoint C)
    (u : (Y.presheaf.stalk (i (genericPoint C)))ˣ) :
    let T := GaussRegularSurfaceValuationOrders.verticalRing π hπ
    let f := (FractionRing.algEquiv (A := Y.presheaf.stalk (i x)) Y.functionField).symm
      (algebraMap (Y.presheaf.stalk (i (genericPoint C))) Y.functionField u)
    let b : C.functionField := i.stalkMap (genericPoint C) u
    ∃ v : Tˣ,
      f = GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ (v : T) ∧
      GaussRegularSurfaceValuationFractions.verticalOrder π hπ f = WithZero.exp (0 : ℤ) ∧
      CentralCurveLeadingOrders.verticalResidueCurveFieldEquiv i x π z hπ hz hm hker
        (IsLocalRing.residue T (v : T)) = b ∧
      GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
        (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm
          (IsLocalRing.residue T (v : T))) = WithZero.exp (C.ord b x) ∧
      ∃ M : ℕ, ∀ (N : ℕ) (hN : 0 < N), M < N →
        GaussRegularSurfaceValuationFractions.weightedOrder π z hπ hz hm N hN f =
          WithZero.exp (C.ord b x) := by
  let D := Y.presheaf.stalk (i (genericPoint C))
  let T := GaussRegularSurfaceValuationOrders.verticalRing π hπ
  let J := FractionRing.algEquiv (A := Y.presheaf.stalk (i x)) Y.functionField
  let E := GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker
  let f := J.symm (algebraMap D Y.functionField u)
  let b : C.functionField := i.stalkMap (genericPoint C) u
  let v : Tˣ := Units.map E.symm.toMonoidHom u
  have hEu : E (v : T) = (u : D) := E.apply_symm_apply u
  have hF : f = GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ (v : T) := by
    apply J.injective
    exact (J.apply_symm_apply _).trans
      ((GaussLeadingResidueNaturality.componentStalk_fraction_apply i x π hπ hker v).trans
        (congrArg (algebraMap D Y.functionField) hEu)).symm
  let : IsDiscreteValuationRing D := GaussCommonVerticalStalks.componentStalk_isDVR i x π hπ hker
  have hzero : GaussRegularSurfaceValuationFractions.verticalOrder π hπ f = WithZero.exp (0 : ℤ) := by
    rw [GaussLeadingResidueNaturality.verticalOrder_genericField i x π hπ hker]
    change Ring.ordFrac D (J (J.symm (algebraMap D Y.functionField u))) = _
    rw [J.apply_symm_apply,Ring.ordFrac_of_isUnit u.isUnit]
    rfl
  have hres : CentralCurveLeadingOrders.verticalResidueCurveFieldEquiv i x π z hπ hz hm hker
      (IsLocalRing.residue T (v : T)) = b :=
    (GaussLeadingResidueNaturality.componentStalk_residual_apply i x π z hπ hz hm hker v).trans
      (congrArg (fun w : D => i.stalkMap (genericPoint C) w) hEu)
  have hord : GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
      (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm
        (IsLocalRing.residue T (v : T))) = WithZero.exp (C.ord b x) :=
    (CentralCurveLeadingOrders.leadingResidue_order_eq_curveOrd i x π z hπ hz hm hker hdim hx v).trans
      (congrArg (fun w : C.functionField => WithZero.exp (C.ord w x)) hres)
  have hf : f ≠ 0 :=
    (map_ne_zero_iff _ J.symm.injective).mpr ((u.isUnit.map (algebraMap D Y.functionField)).ne_zero)
  obtain ⟨a,w,hfac,hvert,M,hN⟩ :=
    CentralCurveLeadingOrders.exists_eventual_fieldOrder_curve i x π z hπ hz hm hker hdim hx f hf
  have ha : a = 0 := WithZero.exp_injective (hvert.symm.trans hzero)
  subst a
  have hfac' : GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ (w : T) = f := by
    simpa only [zpow_zero,mul_one] using hfac.symm
  have hw : (w : T) = (v : T) :=
    GaussRegularSurfaceValuationFractions.verticalFractionEmbedding_injective π hπ (hfac'.trans hF)
  refine ⟨v,hF,hzero,hres,hord,M,?_⟩
  intro N hNpos hMN
  have hn := hN N hNpos hMN
  rw [hw,hres,zero_mul,zero_add] at hn
  exact hn

end EnvelopeProperty.NumericalGaussCurveLineOrders
