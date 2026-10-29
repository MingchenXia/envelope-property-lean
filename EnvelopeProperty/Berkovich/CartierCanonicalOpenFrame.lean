import EnvelopeProperty.AlgGeom.IdealModuleOffSupport
import EnvelopeProperty.AlgGeom.SchemePulledPowerFrames
import EnvelopeProperty.Berkovich.CartierGenericUnitSection
import EnvelopeProperty.Berkovich.SchemeLocalSectionRatioPullback

/-! # The canonical native Cartier frame is its actual whole inclusion frame off support -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open scoped NNReal
universe u
namespace EnvelopeProperty.CartierCanonicalOpenFrame
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Scheme.Modules Berkovich.RelativeSchemeValuedPoint SchemeModuleFrameCoefficients

/-- The actual off-support whole frame is the SAME original inclusion pullback and true unit comparison. -/
theorem pullbackFrame_hom {N : Scheme.{u}} (I : N.IdealSheafData) (U : N.Opens)
    (hU : U ≤ I.support.compl) :
    (I.pullbackModuleIsoOfLeComplSupport U hU).hom =
      (pullback U.ι).map I.toModulesInclusion ≫ (pullbackUnitIso U.ι).hom := by
  let c := restrictFunctorIsoPullback U.ι
  have hn := c.inv.naturality I.toModulesInclusion
  simp only [Scheme.IdealSheafData.pullbackModuleIsoOfLeComplSupport,
    Scheme.IdealSheafData.restrictModuleIsoOfLeComplSupport,
    Iso.trans_hom,Iso.symm_hom,Iso.app_hom]
  change c.inv.app I.toModules ≫ (restrictFunctor U.ι).map I.toModulesInclusion ≫
    (restrictUnitIso U.ι).hom = _
  rw [← Category.assoc,← hn,Category.assoc]
  exact congrArg (fun a => (pullback U.ι).map I.toModulesInclusion ≫ a)
    (ModularCurves.restrictFunctorIsoPullback_inv_comp_restrictUnitIsoLow U.ι)

private theorem factor_inclusion {Y N : Scheme.{u}} (I : N.IdealSheafData) (U : N.Opens)
    (hU : U ≤ I.support.compl) (q : Y ⟶ U.toScheme) (p : Y ⟶ N) (hq : q ≫ U.ι = p) :
    (frameViaFactor q U.ι p hq (I.pullbackModuleIsoOfLeComplSupport U hU)).hom =
      (pullback p).map I.toModulesInclusion ≫ (pullbackUnitIso p).hom := by
  let c : pullback U.ι ⋙ pullback q ≅ pullback p := pullbackComp q U.ι ≪≫ pullbackCongr hq
  have hn := (c.hom.naturality I.toModulesInclusion).symm
  have hn' : (frameFactorIso q U.ι p hq I.toModules).inv ≫
      (pullback q).map ((pullback U.ι).map I.toModulesInclusion) =
      (pullback p).map I.toModulesInclusion ≫ (frameFactorIso q U.ι p hq (unitObj N)).inv := by
    apply (cancel_mono (frameFactorIso q U.ι p hq (unitObj N)).hom).mp
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    change (frameFactorIso q U.ι p hq I.toModules).hom ≫ (pullback p).map I.toModulesInclusion =
      (pullback q).map ((pullback U.ι).map I.toModulesInclusion) ≫
        (frameFactorIso q U.ι p hq (unitObj N)).hom at hn
    rw [← hn,Iso.inv_hom_id_assoc]

  have hu := congrArg Iso.hom (SchemePulledPowerFrames.frameViaFactor_unit q U.ι p hq)
  change (frameFactorIso q U.ι p hq (unitObj N)).inv ≫
    (pullback q).map (pullbackUnitIso U.ι).hom ≫ (pullbackUnitIso q).hom = (pullbackUnitIso p).hom at hu
  simp only [frameViaFactor,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,pullbackFrame_hom,
    Functor.map_comp,Category.assoc]
  rw [← Category.assoc ((frameFactorIso q U.ι p hq I.toModules).inv),hn']
  simpa only [Category.assoc] using congrArg (fun a => (pullback p).map I.toModulesInclusion ≫ a) hu

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {N : Scheme.{u}} {f : N ⟶ Spec (.of R)} [IsProper f]
    (hb : ∀ a, v a ≤ 1) (y : Berkovich.RelativeSchemeValuedPoint v f)
    (I : N.IdealSheafData) (hI : I.IsInvertible) (U : N.Opens) (hU : U ≤ I.support.compl)
    (q : Spec (N.residueField y.1.point) ⟶ U.toScheme)
    (hq : q ≫ U.ι = N.fromSpecResidueField y.1.point)
    (hn : modelIdealNorm I hb y ≠ 0)

/-- The actual original off-support whole inclusion frame becomes exactly the SAME canonical native Cartier inclusion frame. -/
theorem nativeFrame_eq :
    frameViaFactor q U.ι (N.fromSpecResidueField y.1.point) hq
      (I.pullbackModuleIsoOfLeComplSupport U hU) = genericIdealInclusionIso hb y I hI hn := by
  apply Iso.ext
  exact factor_inclusion I U hU q _ hq

/-- The SAME original whole inverse inclusion section pulls to the actual canonical generic Cartier unit, with no matching input. -/
theorem localUnitSection_native_eq :
    SchemeLineSectionEvaluation.sectionAtOne (SchemeLocalSectionRatioPullback.sectionViaFactor q U.ι
      (N.fromSpecResidueField y.1.point) hq (I.pullbackModuleIsoOfLeComplSupport U hU).inv) =
      genericIdealUnitSection hb y I hI hn := by
  have h := congrArg Iso.inv (nativeFrame_eq hb y I hI U hU q hq hn)
  have hs := congrArg (fun a => a.val.app (op ⊤) (1 : Γ(Spec (N.residueField y.1.point),⊤))) h
  exact hs

omit hn in
/-- The actual residue factor through the genuine off-support open derives its own native nonzero ideal norm and exact canonical whole-frame/section identifications. -/
theorem exists_nativeFrame :
    ∃ hn : modelIdealNorm I hb y ≠ 0,
      frameViaFactor q U.ι (N.fromSpecResidueField y.1.point) hq
        (I.pullbackModuleIsoOfLeComplSupport U hU) = genericIdealInclusionIso hb y I hI hn ∧
      SchemeLineSectionEvaluation.sectionAtOne (SchemeLocalSectionRatioPullback.sectionViaFactor q U.ι
        (N.fromSpecResidueField y.1.point) hq (I.pullbackModuleIsoOfLeComplSupport U hU).inv) =
        genericIdealUnitSection hb y I hI hn := by
  have hc : IsIso ((pullback (N.fromSpecResidueField y.1.point)).map I.toModulesInclusion ≫
      (pullbackUnitIso (N.fromSpecResidueField y.1.point)).hom) := by
    rw [← factor_inclusion I U hU q _ hq]
    infer_instance
  have hi : IsIso ((pullback (N.fromSpecResidueField y.1.point)).map I.toModulesInclusion) :=
    IsIso.of_isIso_comp_right _ (pullbackUnitIso (N.fromSpecResidueField y.1.point)).hom
  have hnorm := (modelIdealNorm_ne_zero_iff_isIso_genericInclusion hb y I hI).mpr hi
  exact ⟨hnorm,nativeFrame_eq hb y I hI U hU q hq hnorm,
    localUnitSection_native_eq hb y I hI U hU q hq hnorm⟩

end EnvelopeProperty.CartierCanonicalOpenFrame
