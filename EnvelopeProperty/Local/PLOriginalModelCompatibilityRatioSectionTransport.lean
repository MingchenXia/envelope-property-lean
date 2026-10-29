import EnvelopeProperty.AlgGeom.CartierRatioGroupCoherence
import EnvelopeProperty.AlgGeom.InvertibleDualTranspose
import EnvelopeProperty.AlgGeom.SchemeTensorSectionHoms
import EnvelopeProperty.Berkovich.CartierRatioLocalRealization

/-! # Canonical Cartier ratio sections under the original action

The actual inclusion-preserving factor comparisons transport the inverse
numerator inclusion and the evaluation-defined denominator functional.
The resulting whole ratio-section equality precedes every norm comparison.
-/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped NNReal ENNReal
noncomputable section
universe u v w z

namespace EnvelopeProperty.PLOriginalModelCompatibility.RatioSectionTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance ratioSectionTransportModulesMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance ratioSectionTransportModulesSymmetric (X : Scheme.{u}) :
    SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X
noncomputable local instance ratioSectionTransportPullbackMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
open SchemeLineSectionEvaluation SchemeTensorSectionHoms

private theorem originalRightIdealFunctor
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    (B I : C) (i : I ⟶ 𝟙_ C) :
    Functor.LaxMonoidal.μ F B I ≫ F.map (B ◁ i ≫ (ρ_ B).hom) =
      F.obj B ◁ (F.map i ≫ (Functor.Monoidal.εIso F).inv) ≫ (ρ_ (F.obj B)).hom := by
  simp only [Functor.map_comp, whiskerLeft_comp, Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [Functor.LaxMonoidal.right_unitality F B]
  simp only [← Category.assoc, ← whiskerLeft_comp]
  simp only [← Functor.Monoidal.εIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem rightUnitFunctor
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    {UC : C} {UD : D} (uC : 𝟙_ C ≅ UC) (uD : 𝟙_ D ≅ UD)
    (uF : F.obj UC ≅ UD)
    (hu : uF.hom ≫ uD.inv = F.map uC.inv ≫ (Functor.Monoidal.εIso F).inv)
    (M : C) :
    F.obj M ◁ uF.inv ≫ Functor.LaxMonoidal.μ F M UC ≫
        F.map (M ◁ uC.inv ≫ (ρ_ M).hom) =
      F.obj M ◁ uD.inv ≫ (ρ_ (F.obj M)).hom := by
  rw [originalRightIdealFunctor]
  simp only [← whiskerLeft_comp_assoc]
  rw [← hu]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem pulledPairing
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    {UC : C} {UD : D} (uC : 𝟙_ C ≅ UC) (uD : 𝟙_ D ≅ UD)
    (uF : F.obj UC ≅ UD)
    (hu : uF.hom ≫ uD.inv = F.map uC.inv ≫ (Functor.Monoidal.εIso F).inv)
    (M N : C) (ev : M ⊗ N ⟶ 𝟙_ C) (σ : UC ⟶ N) (α : M ⟶ UC)
    (hσ : M ◁ σ ≫ ev = M ◁ uC.inv ≫ (ρ_ M).hom ≫ α ≫ uC.inv) :
    F.obj M ◁ (uF.inv ≫ F.map σ) ≫ Functor.LaxMonoidal.μ F M N ≫
        F.map ev ≫ (Functor.Monoidal.εIso F).inv =
      F.obj M ◁ uD.inv ≫ (ρ_ (F.obj M)).hom ≫
        F.map α ≫ uF.hom ≫ uD.inv := by
  simp only [whiskerLeft_comp, Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [← F.map_comp_assoc, hσ, hu]
  simpa only [F.map_comp, Category.assoc] using congrArg
    (fun q => q ≫ F.map α ≫ F.map uC.inv ≫ (Functor.Monoidal.εIso F).inv)
    (rightUnitFunctor F uC uD uF hu M)

private theorem transportedTranspose
    {C : Type u} [Category.{w} C] [MonoidalCategory C]
    {U Mf Mg Df Dg : C} (u : 𝟙_ C ≅ U)
    (evf : Mf ⊗ Df ≅ 𝟙_ C) (evg : Mg ⊗ Dg ≅ 𝟙_ C)
    (e : Mf ≅ Mg) (t : Df ⟶ Dg) [(tensorLeft Mg).Faithful]
    (sf : U ⟶ Df) (sg : U ⟶ Dg) (af : Mf ⟶ U) (ag : Mg ⟶ U)
    (hf : Mf ◁ sf ≫ evf.hom = Mf ◁ u.inv ≫ (ρ_ Mf).hom ≫ af ≫ u.inv)
    (hg : Mg ◁ sg ≫ evg.hom = Mg ◁ u.inv ≫ (ρ_ Mg).hom ≫ ag ≫ u.inv)
    (ht : Mg ◁ t ≫ evg.hom = e.inv ▷ Df ≫ evf.hom)
    (he : e.hom ≫ ag = af) :
    sf ≫ t = sg := by
  apply (tensorLeft Mg).map_injective
  change Mg ◁ (sf ≫ t) = Mg ◁ sg
  apply (cancel_mono evg.hom).mp
  rw [whiskerLeft_comp, Category.assoc, ht]
  rw [← Category.assoc, whisker_exchange, Category.assoc, hf, hg]
  rw [← whisker_exchange_assoc, rightUnitor_naturality_assoc]
  rw [← he]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem pullbackUnitSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackUnitIso f).hom ≫ (ModularCurves.monoidalUnitObjIso X).inv =
      (pullback f).map (ModularCurves.monoidalUnitObjIso Y).inv ≫
        (Functor.Monoidal.εIso (pullback f)).inv := by
  let F := pullback f
  let uY := ModularCurves.monoidalUnitObjIso Y
  let uX := ModularCurves.monoidalUnitObjIso X
  have h := congrArg Iso.hom (Scheme.Modules.pullback_monoidalUnitObjIso f)
  change (Functor.Monoidal.εIso F).inv ≫ uX.hom =
    F.map uY.hom ≫ (pullbackUnitIso f).hom at h
  apply (cancel_epi (F.map uY.hom)).mp
  change F.map uY.hom ≫ (pullbackUnitIso f).hom ≫ uX.inv =
    F.map uY.hom ≫ F.map uY.inv ≫ (Functor.Monoidal.εIso F).inv
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.id_comp]

/-- The actual pulled original transpose has the evaluation of the actual
pulled functional, with the native tensorator and structure-sheaf unit. -/
theorem pulledDualTranspose_pairing {X Y : Scheme.{u}} {M : Y.Modules}
    (hM : IsInvertible M) (f : X ⟶ Y) (α : M ⟶ unitObj Y) :
    (pullback f).obj M ◁ pullbackSectionHom f (hM.dualTranspose α) ≫
        (hM.pulledEvaluationIso f).hom =
      (originalRightUnitIso ((pullback f).obj M)).hom ≫
        ((pullback f).map α ≫ (pullbackUnitIso f).hom) ≫
          (ModularCurves.monoidalUnitObjIso X).inv := by
  have hσ : M ◁ hM.dualTranspose α ≫ hM.monoidalEvaluationIso.hom =
      M ◁ (ModularCurves.monoidalUnitObjIso Y).inv ≫ (ρ_ M).hom ≫
        α ≫ (ModularCurves.monoidalUnitObjIso Y).inv := by
    change M ◁ hM.dualTranspose α ≫
      (ModularCurves.dualPairing M ≫ (ModularCurves.monoidalUnitObjIso Y).inv) = _
    simpa only [originalRightUnitIso, Iso.trans_hom, whiskerLeftIso_hom,
      Iso.symm_hom, Category.assoc] using congrArg
        (fun q => q ≫ (ModularCurves.monoidalUnitObjIso Y).inv)
        (hM.dualTranspose_pairing α)
  simpa only [IsInvertible.pulledEvaluationIso, pullbackSectionHom,
    originalRightUnitIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.Monoidal.μIso_hom, whiskerLeftIso_hom, Category.assoc] using
      pulledPairing (pullback f) (ModularCurves.monoidalUnitObjIso Y)
        (ModularCurves.monoidalUnitObjIso X) (pullbackUnitIso f)
        (pullbackUnitSquare f) M (dualObj M) hM.monoidalEvaluationIso.hom
        (hM.dualTranspose α) α hσ

/-- Inclusion-preserving factor transport carries the SAME original
evaluation-defined functional section, before taking any fibre or norm. -/
theorem evaluationDualTransport_dualTranspose {X Y : Scheme.{u}} {M : Y.Modules}
    (hM : IsInvertible M) (f g : X ⟶ Y) (α : M ⟶ unitObj Y)
    (e : (pullback f).obj M ≅ (pullback g).obj M)
    (he : e.hom ≫ ((pullback g).map α ≫ (pullbackUnitIso g).hom) =
      (pullback f).map α ≫ (pullbackUnitIso f).hom) :
    pullbackSectionHom f (hM.dualTranspose α) ≫
        (hM.evaluationDualTransportIso f g e).hom =
      pullbackSectionHom g (hM.dualTranspose α) := by
  let ht := (hM.pullback g).tensorRightFullyFaithful.ofIso
    (BraidedCategory.tensorLeftIsoTensorRight ((pullback g).obj M)).symm
  let : (tensorLeft ((pullback g).obj M)).Faithful := ht.faithful
  exact transportedTranspose (ModularCurves.monoidalUnitObjIso X)
    (hM.pulledEvaluationIso f) (hM.pulledEvaluationIso g) e
    (hM.evaluationDualTransportIso f g e).hom
    (pullbackSectionHom f (hM.dualTranspose α))
    (pullbackSectionHom g (hM.dualTranspose α))
    ((pullback f).map α ≫ (pullbackUnitIso f).hom)
    ((pullback g).map α ≫ (pullbackUnitIso g).hom)
    (pulledDualTranspose_pairing hM f α) (pulledDualTranspose_pairing hM g α)
    (hM.evaluationDualTransportIso_pairing f g e) he

/-- Actual inversion of the included numerator module commutes with a
comparison that preserves its original structure-sheaf inclusion. -/
theorem inverseInclusion_transport {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f g : X ⟶ Y) [IsIso (I.pullbackModuleInclusion f)]
    [IsIso (I.pullbackModuleInclusion g)]
    (e : (pullback f).obj I.toModules ≅ (pullback g).obj I.toModules)
    (he : e.hom ≫ I.pullbackModuleInclusion g = I.pullbackModuleInclusion f) :
    (asIso (I.pullbackModuleInclusion f)).inv ≫ e.hom =
      (asIso (I.pullbackModuleInclusion g)).inv := by
  apply (cancel_mono (I.pullbackModuleInclusion g)).mp
  rw [Category.assoc, he]
  simp only [asIso_inv, IsIso.inv_hom_id]

/-- The actual ratio section uses the inverse numerator inclusion and
the original denominator inclusion's transpose, on these SAME modules. -/
def canonicalPulledRatioSection {X Y : Scheme.{u}} (I J : Y.IdealSheafData)
    (hJ : J.IsInvertible) (f : X ⟶ Y) [IsIso (I.pullbackModuleInclusion f)] :
    unitObj X ⟶ (pullback f).obj (I.ratioModule J) :=
  tensorSectionHom (asIso (I.pullbackModuleInclusion f)).inv
      (pullbackSectionHom f (hJ.isInvertibleModule_toModules.dualTranspose J.toModulesInclusion)) ≫
    (ModularCurves.monoidalTensorObjIso ((pullback f).obj I.toModules)
      ((pullback f).obj (dualObj J.toModules))).hom ≫
    (canonicalTensorPullbackIso f I.toModules (dualObj J.toModules)).inv

/-- The actual canonical ratio comparison transports the actual whole
ratio section; the hypotheses concern only the TWO original inclusions. -/
theorem evaluationRatioComparison_canonicalSection {X Y : Scheme.{u}}
    (I J : Y.IdealSheafData) (hJ : J.IsInvertible) (f g : X ⟶ Y)
    [IsIso (I.pullbackModuleInclusion f)] [IsIso (I.pullbackModuleInclusion g)]
    (eI : (pullback f).obj I.toModules ≅ (pullback g).obj I.toModules)
    (eJ : (pullback f).obj J.toModules ≅ (pullback g).obj J.toModules)
    (heI : eI.hom ≫ I.pullbackModuleInclusion g = I.pullbackModuleInclusion f)
    (heJ : eJ.hom ≫ J.pullbackModuleInclusion g = J.pullbackModuleInclusion f) :
    canonicalPulledRatioSection I J hJ f ≫
        (evaluationRatioComparison hJ.isInvertibleModule_toModules f g eI eJ).hom =
      canonicalPulledRatioSection I J hJ g := by
  have hi := inverseInclusion_transport I f g eI heI
  have hj := evaluationDualTransport_dualTranspose hJ.isInvertibleModule_toModules
    f g J.toModulesInclusion eJ heJ
  have hn := ModularCurves.cartierMonoidalTensorObjIso_hom_natural eI
    (hJ.isInvertibleModule_toModules.evaluationDualTransportIso f g eJ)
  unfold canonicalPulledRatioSection evaluationRatioComparison
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc _ (Scheme.Modules.tensorObjCongr eI _).hom, hn]
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc, tensorSectionHom_comp, hi, hj]
  simp only [Category.assoc]

/-- An actual whole inclusion identity remains the same inclusion identity
after arbitrary base change, including a residue-field morphism. -/
theorem pullbackIsoAlong_inclusion {X Y Z : Scheme.{u}} (I : Z.IdealSheafData)
    (f g : Y ⟶ Z) (e : (pullback f).obj I.toModules ≅ (pullback g).obj I.toModules)
    (he : e.hom ≫ I.pullbackModuleInclusion g = I.pullbackModuleInclusion f)
    (h : X ⟶ Y) :
    (pullbackIsoAlong f g e h).hom ≫ I.pullbackModuleInclusion (h ≫ g) =
      I.pullbackModuleInclusion (h ≫ f) := by
  apply (cancel_epi ((pullbackComp h f).hom.app I.toModules)).mp
  simp only [pullbackIsoAlong, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.app_inv, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [I.pullbackModuleInclusion_comp h g, ← Functor.map_comp_assoc, he,
    ← I.pullbackModuleInclusion_comp h f]

/-- The retained group ratio comparison preserves its original section on
EVERY base change where the numerator inclusion becomes invertible. -/
theorem cartierRatioGroupLinearization_canonicalSection
    {k : Type u} [Field k]
    (G B : Over (Spec (CommRingCat.of k))) [GrpObj G] [ModObj G B]
    (I J : B.left.IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (hinvI : I.comap (cartierActionMap G B) = I.comap (cartierProjectionMap G B))
    (hinvJ : J.comap (cartierActionMap G B) = J.comap (cartierProjectionMap G B))
    {T : Scheme.{u}} (q : T ⟶ (G ⊗ B).left)
    [IsIso (I.pullbackModuleInclusion (q ≫ cartierActionMap G B))]
    [IsIso (I.pullbackModuleInclusion (q ≫ cartierProjectionMap G B))] :
    canonicalPulledRatioSection I J hJ (q ≫ cartierActionMap G B) ≫
        (pullbackIsoAlong (cartierActionMap G B) (cartierProjectionMap G B)
          (cartierRatioGroupLinearization G B I J hI hJ hinvI hinvJ) q).hom =
      canonicalPulledRatioSection I J hJ (q ≫ cartierProjectionMap G B) := by
  change canonicalPulledRatioSection I J hJ (q ≫ cartierActionMap G B) ≫
    (pullbackIsoAlong _ _
      (evaluationRatioComparison hJ.isInvertibleModule_toModules _ _
        (cartierGroupLinearization G B I hI hinvI)
        (cartierGroupLinearization G B J hJ hinvJ)) q).hom = _
  rw [evaluationRatioComparison_baseChange]
  exact evaluationRatioComparison_canonicalSection I J hJ _ _ _ _
    (pullbackIsoAlong_inclusion I _ _ _ (cartierGroupLinearization_inclusion G B I hI hinvI) q)
    (pullbackIsoAlong_inclusion J _ _ _ (cartierGroupLinearization_inclusion G B J hJ hinvJ) q)

/-- The actual numerator inclusion is invertible on the SAME off-support
open; its frame is the canonical inclusion frame. -/
theorem offSupportInclusion_isIso {N : Scheme.{u}} (I : N.IdealSheafData)
    (U : N.Opens) (hU : U ≤ I.support.compl) :
    IsIso (I.pullbackModuleInclusion U.ι) := by
  change IsIso ((pullback U.ι).map I.toModulesInclusion ≫ (pullbackUnitIso U.ι).hom)
  rw [← CartierCanonicalOpenFrame.pullbackFrame_hom I U hU]
  infer_instance

private theorem unit_hom_ext {X : Scheme.{u}} {P : X.Modules} {a b : unitObj X ⟶ P}
    (h : sectionAtOne a = sectionAtOne b) : a = b := by
  apply SheafOfModules.hom_ext
  ext V
  let i := (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
  have ha := PresheafOfModules.naturality_apply a.val i (1 : Γ(X,⊤))
  have hb := PresheafOfModules.naturality_apply b.val i (1 : Γ(X,⊤))
  change a.val.app V (X.presheaf.map i (1 : Γ(X,⊤))) = P.presheaf.map i (sectionAtOne a) at ha
  change b.val.app V (X.presheaf.map i (1 : Γ(X,⊤))) = P.presheaf.map i (sectionAtOne b) at hb
  rw [map_one] at ha hb
  exact ha.trans ((congrArg (fun q => P.presheaf.map i q) h).trans hb.symm)

private theorem topSectionHom_sectionAtOne {X : Scheme.{u}} {P : X.Modules}
    (a : unitObj X ⟶ P) : topSectionHom P (sectionAtOne a) = a := by
  apply unit_hom_ext
  exact topSectionHom_app_top_apply_one P _

private theorem tensorRight_eq {X : Scheme.{u}} {M T : X.Modules}
    (a : unitObj X ⟶ M) (b : unitObj X ⟶ T) :
    SchemeSectionTensorDivision.tensorRight a b = tensorSectionHom a b := by
  have h := ModularCurves.topSectionHom_tensorSection M T (sectionAtOne a) (sectionAtOne b)
  rw [topSectionHom_sectionAtOne, topSectionHom_sectionAtOne] at h
  apply unit_hom_ext
  exact (SchemeSectionTensorDivision.sectionAtOne_tensorRight a b).trans
    ((topSectionHom_app_top_apply_one (M ⊗ T) _).symm.trans (congrArg sectionAtOne h))

/-- The whole canonical pulled ratio section is EXACTLY the existing
original local Cartier ratio section on the same off-support open. -/
theorem canonicalPulledRatioSection_eq_localSection {N : Scheme.{u}}
    (I J : N.IdealSheafData) (hJ : J.IsInvertible) (U : N.Opens)
    (hU : U ≤ I.support.compl) [IsIso (I.pullbackModuleInclusion U.ι)] :
    canonicalPulledRatioSection I J hJ U.ι =
      CartierRatioLocalRealization.localSection I J hJ U hU := by
  have he : asIso (I.pullbackModuleInclusion U.ι) =
      I.pullbackModuleIsoOfLeComplSupport U hU := by
    apply Iso.ext
    exact (CartierCanonicalOpenFrame.pullbackFrame_hom I U hU).symm
  unfold canonicalPulledRatioSection CartierRatioLocalRealization.localSection
  rw [he, tensorRight_eq]
  simp only [canonicalTensorPullbackIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Category.assoc, Iso.hom_inv_id_assoc]

private theorem offSupportFactor_inclusion {Y N : Scheme.{u}}
    (I : N.IdealSheafData) (U : N.Opens) (hU : U ≤ I.support.compl)
    (q : Y ⟶ U.toScheme) (p : Y ⟶ N) (hq : q ≫ U.ι = p) :
    (frameViaFactor q U.ι p hq (I.pullbackModuleIsoOfLeComplSupport U hU)).hom =
      I.pullbackModuleInclusion p := by
  let c : pullback U.ι ⋙ pullback q ≅ pullback p := pullbackComp q U.ι ≪≫ pullbackCongr hq
  have hn := (c.hom.naturality I.toModulesInclusion).symm
  have hn' : (frameFactorIso q U.ι p hq I.toModules).inv ≫
      (pullback q).map ((pullback U.ι).map I.toModulesInclusion) =
      (pullback p).map I.toModulesInclusion ≫
        (frameFactorIso q U.ι p hq (unitObj N)).inv := by
    apply (cancel_mono (frameFactorIso q U.ι p hq (unitObj N)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change (frameFactorIso q U.ι p hq I.toModules).hom ≫ (pullback p).map I.toModulesInclusion =
      (pullback q).map ((pullback U.ι).map I.toModulesInclusion) ≫
        (frameFactorIso q U.ι p hq (unitObj N)).hom at hn
    rw [← hn, Iso.inv_hom_id_assoc]
  have hu := congrArg Iso.hom (SchemePulledPowerFrames.frameViaFactor_unit q U.ι p hq)
  change (frameFactorIso q U.ι p hq (unitObj N)).inv ≫
    (pullback q).map (pullbackUnitIso U.ι).hom ≫ (pullbackUnitIso q).hom =
      (pullbackUnitIso p).hom at hu
  simp only [frameViaFactor, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    CartierCanonicalOpenFrame.pullbackFrame_hom, Functor.map_comp, Category.assoc,
    Scheme.IdealSheafData.pullbackModuleInclusion]
  rw [← Category.assoc ((frameFactorIso q U.ι p hq I.toModules).inv), hn']
  simpa only [Category.assoc] using congrArg
    (fun a => (pullback p).map I.toModulesInclusion ≫ a) hu

/-- Factoring through the SAME off-support open derives invertibility
of the actual pulled numerator inclusion, without any flatness hypothesis. -/
theorem offSupportFactorInclusion_isIso {Y N : Scheme.{u}}
    (I : N.IdealSheafData) (U : N.Opens) (hU : U ≤ I.support.compl)
    (q : Y ⟶ U.toScheme) (p : Y ⟶ N) (hq : q ≫ U.ι = p) :
    IsIso (I.pullbackModuleInclusion p) := by
  rw [← offSupportFactor_inclusion I U hU q p hq]
  infer_instance

private theorem sectionViaFactor_post {Y A N : Scheme.{u}} (q : Y ⟶ A) (j : A ⟶ N)
    (p : Y ⟶ N) (h : q ≫ j = p) {M L : N.Modules}
    (s : unitObj A ⟶ (pullback j).obj M) (a : M ⟶ L) :
    SchemeLocalSectionRatioPullback.sectionViaFactor q j p h (s ≫ (pullback j).map a) =
      SchemeLocalSectionRatioPullback.sectionViaFactor q j p h s ≫ (pullback p).map a := by
  let c : pullback j ⋙ pullback q ≅ pullback p := pullbackComp q j ≪≫ pullbackCongr h
  have hn := c.hom.naturality a
  unfold SchemeLocalSectionRatioPullback.sectionViaFactor pullbackSectionHom
  rw [Functor.map_comp]
  change (pullbackUnitIso q).inv ≫ (pullback q).map s ≫
    (pullback j ⋙ pullback q).map a ≫ c.hom.app L =
      (pullbackUnitIso q).inv ≫ (pullback q).map s ≫ c.hom.app M ≫ (pullback p).map a
  rw [hn]

/-- On EVERY factor through the original off-support open, the actual
whole pulled canonical section equals the actual local section transport. -/
theorem canonicalPulledRatioSection_eq_sectionViaFactor_localSection
    {Y N : Scheme.{u}} (I J : N.IdealSheafData) (hJ : J.IsInvertible)
    (U : N.Opens) (hU : U ≤ I.support.compl)
    (q : Y ⟶ U.toScheme) (p : Y ⟶ N) (hq : q ≫ U.ι = p)
    [IsIso (I.pullbackModuleInclusion p)] :
    canonicalPulledRatioSection I J hJ p =
      SchemeLocalSectionRatioPullback.sectionViaFactor q U.ι p hq
        (CartierRatioLocalRealization.localSection I J hJ U hU) := by
  let a := (I.pullbackModuleIsoOfLeComplSupport U hU).inv
  let b := pullbackSectionHom U.ι
    (hJ.isInvertibleModule_toModules.dualTranspose J.toModulesInclusion)
  have he : frameViaFactor q U.ι p hq (I.pullbackModuleIsoOfLeComplSupport U hU) =
      asIso (I.pullbackModuleInclusion p) := by
    apply Iso.ext
    exact offSupportFactor_inclusion I U hU q p hq
  have ha : SchemeLocalSectionRatioPullback.sectionViaFactor q U.ι p hq a =
      (asIso (I.pullbackModuleInclusion p)).inv := by
    simpa only [SchemeLocalSectionRatioPullback.sectionViaFactor, pullbackSectionHom,
      frameViaFactor, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, a]
      using congrArg Iso.inv he
  have ht := SchemeLocalSectionRatioPullback.sectionViaFactor_tensor q U.ι p hq a b
  have hs : SchemeLocalSectionRatioPullback.sectionViaFactor q U.ι p hq
      (SchemeSectionTensorDivision.tensorRight a b ≫
        (Functor.Monoidal.μIso (pullback U.ι) I.toModules (dualObj J.toModules)).hom) =
      SchemeSectionTensorDivision.tensorRight
        (SchemeLocalSectionRatioPullback.sectionViaFactor q U.ι p hq a)
        (SchemeLocalSectionRatioPullback.sectionViaFactor q U.ι p hq b) ≫
          (Functor.Monoidal.μIso (pullback p) I.toModules (dualObj J.toModules)).hom := by
    have h := congrArg (fun r => r ≫
      (Functor.Monoidal.μIso (pullback p) I.toModules (dualObj J.toModules)).hom) ht
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h.symm
  symm
  unfold CartierRatioLocalRealization.localSection
  rw [← Category.assoc, sectionViaFactor_post, hs, ha]
  rw [SchemeLocalSectionRatioPullback.sectionViaFactor_global]
  rw [tensorRight_eq]
  unfold canonicalPulledRatioSection
  simp only [canonicalTensorPullbackIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Category.assoc, Iso.hom_inv_id_assoc]

/-- The canonical original group ratio linearization carries the SAME
actual off-support local ratio section along its action and projection. -/
theorem cartierRatioGroupLinearization_localSection
    {k : Type u} [Field k]
    (G B : Over (Spec (CommRingCat.of k))) [GrpObj G] [ModObj G B]
    (I J : B.left.IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (hinvI : I.comap (cartierActionMap G B) = I.comap (cartierProjectionMap G B))
    (hinvJ : J.comap (cartierActionMap G B) = J.comap (cartierProjectionMap G B))
    {T : Scheme.{u}} (q : T ⟶ (G ⊗ B).left)
    (Ua Up : B.left.Opens) (hUa : Ua ≤ I.support.compl) (hUp : Up ≤ I.support.compl)
    (qa : T ⟶ Ua.toScheme) (qp : T ⟶ Up.toScheme)
    (hqa : qa ≫ Ua.ι = q ≫ cartierActionMap G B)
    (hqp : qp ≫ Up.ι = q ≫ cartierProjectionMap G B) :
    SchemeLocalSectionRatioPullback.sectionViaFactor qa Ua.ι
        (q ≫ cartierActionMap G B) hqa
        (CartierRatioLocalRealization.localSection I J hJ Ua hUa) ≫
      (pullbackIsoAlong (cartierActionMap G B) (cartierProjectionMap G B)
        (cartierRatioGroupLinearization G B I J hI hJ hinvI hinvJ) q).hom =
    SchemeLocalSectionRatioPullback.sectionViaFactor qp Up.ι
      (q ≫ cartierProjectionMap G B) hqp
      (CartierRatioLocalRealization.localSection I J hJ Up hUp) := by
  let := offSupportFactorInclusion_isIso I Ua hUa qa _ hqa
  let := offSupportFactorInclusion_isIso I Up hUp qp _ hqp
  have h := cartierRatioGroupLinearization_canonicalSection G B I J hI hJ hinvI hinvJ q
  rw [canonicalPulledRatioSection_eq_sectionViaFactor_localSection I J hJ Ua hUa qa _ hqa,
    canonicalPulledRatioSection_eq_sectionViaFactor_localSection I J hJ Up hUp qp _ hqp] at h
  exact h

end EnvelopeProperty.PLOriginalModelCompatibility.RatioSectionTransport
