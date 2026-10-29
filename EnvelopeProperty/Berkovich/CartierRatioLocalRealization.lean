import EnvelopeProperty.Berkovich.CartierCanonicalOpenFrame
import EnvelopeProperty.Berkovich.CartierRatioGenericMetric

/-! # The actual original local Cartier ratio realizes its canonical native section -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
open scoped NNReal ENNReal
universe u
namespace EnvelopeProperty.CartierRatioLocalRealization
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) : (pullback f).Monoidal :=
  Scheme.Modules.pullbackMonoidal f
open SchemeLineSectionEvaluation SchemeSectionTensorDivision SchemeLocalSectionRatioPullback
open Berkovich.RelativeSchemeValuedPoint

private theorem sectionViaFactor_post {Y A N : Scheme.{u}} (q : Y ⟶ A) (j : A ⟶ N)
    (p : Y ⟶ N) (h : q ≫ j = p) {M L : N.Modules}
    (s : unitObj A ⟶ (pullback j).obj M) (a : M ⟶ L) :
    sectionViaFactor q j p h (s ≫ (pullback j).map a) =
      sectionViaFactor q j p h s ≫ (pullback p).map a := by
  let c : pullback j ⋙ pullback q ≅ pullback p := pullbackComp q j ≪≫ pullbackCongr h
  have hn := c.hom.naturality a
  unfold sectionViaFactor pullbackSectionHom
  rw [Functor.map_comp]
  change (pullbackUnitIso q).inv ≫ (pullback q).map s ≫
    (pullback j ⋙ pullback q).map a ≫ c.hom.app L =
      (pullbackUnitIso q).inv ≫ (pullback q).map s ≫ c.hom.app M ≫ (pullback p).map a
  rw [hn]

variable {N : Scheme.{u}} (I J : N.IdealSheafData) (hJ : J.IsInvertible)
    (U : N.Opens) (hU : U ≤ I.support.compl)

/-- The actual original whole local ratio section, through the original coherent/explicit tensor comparison. -/
def localSection : unitObj U.toScheme ⟶ (pullback U.ι).obj (I.ratioModule J) :=
  tensorRight (I.pullbackModuleIsoOfLeComplSupport U hU).inv
    (pullbackSectionHom U.ι (hJ.isInvertibleModule_toModules.dualTranspose J.toModulesInclusion)) ≫
      (Functor.Monoidal.μIso (pullback U.ι) I.toModules (dualObj J.toModules)).hom ≫
        (pullback U.ι).map (ModularCurves.monoidalTensorObjIso I.toModules (dualObj J.toModules)).hom

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {f : N ⟶ Spec (.of R)} [IsProper f] (hb : ∀ a, v a ≤ 1)
    (y : Berkovich.RelativeSchemeValuedPoint v f) (hI : I.IsInvertible)
    (q : Spec (N.residueField y.1.point) ⟶ U.toScheme)
    (hq : q ≫ U.ι = N.fromSpecResidueField y.1.point)
    (hn : modelIdealNorm I hb y ≠ 0)

/-- The SAME actual original local section pulls to the canonical native Cartier ratio, with all tensor identifications derived. -/
theorem native_eq :
    sectionAtOne (sectionViaFactor q U.ι (N.fromSpecResidueField y.1.point) hq
      (localSection I J hJ U hU)) = genericCartierRatioSection hb y I J hI hJ hn := by
  let p := N.fromSpecResidueField y.1.point
  let a := (I.pullbackModuleIsoOfLeComplSupport U hU).inv
  let b := pullbackSectionHom U.ι (hJ.isInvertibleModule_toModules.dualTranspose J.toModulesInclusion)
  have ht := sectionViaFactor_tensor q U.ι p hq a b
  have hs : sectionViaFactor q U.ι p hq
      (tensorRight a b ≫ (Functor.Monoidal.μIso (pullback U.ι) I.toModules (dualObj J.toModules)).hom) =
      tensorRight (sectionViaFactor q U.ι p hq a) (sectionViaFactor q U.ι p hq b) ≫
        (Functor.Monoidal.μIso (pullback p) I.toModules (dualObj J.toModules)).hom := by
    have h := congrArg (fun r => r ≫ (Functor.Monoidal.μIso (pullback p) I.toModules (dualObj J.toModules)).hom) ht
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using h.symm
  unfold localSection
  rw [← Category.assoc,sectionViaFactor_post,hs]
  change ((pullback p).map (ModularCurves.monoidalTensorObjIso I.toModules (dualObj J.toModules)).hom).val.app (op ⊤)
    ((Functor.Monoidal.μIso (pullback p) I.toModules (dualObj J.toModules)).hom.val.app (op ⊤)
      (sectionAtOne (tensorRight (sectionViaFactor q U.ι p hq a) (sectionViaFactor q U.ι p hq b)))) = _
  rw [sectionAtOne_tensorRight,sectionViaFactor_global]
  have ha := CartierCanonicalOpenFrame.localUnitSection_native_eq hb y I hI U hU q hq hn
  change sectionAtOne (sectionViaFactor q U.ι p hq a) = genericIdealUnitSection hb y I hI hn at ha
  rw [ha]
  rfl

omit hn in
/-- The actual residue factor derives its own true nonzero ideal norm before exact section identification. -/
theorem exists_native_eq :
    ∃ hn : modelIdealNorm I hb y ≠ 0,
      sectionAtOne (sectionViaFactor q U.ι (N.fromSpecResidueField y.1.point) hq
        (localSection I J hJ U hU)) = genericCartierRatioSection hb y I J hI hJ hn := by
  obtain ⟨hn,_,_⟩ := CartierCanonicalOpenFrame.exists_nativeFrame hb y I hI U hU q hq
  exact ⟨hn,native_eq I J hJ U hU hb y hI q hq hn⟩

omit hn in
/-- The SAME actual local section has its genuine original ideal potential as its true model weight. -/
theorem localSection_weight :
    -ENNReal.log (modelLineNorm hb y (hI.isInvertible_ratioModule hJ)
      (sectionAtOne (sectionViaFactor q U.ι (N.fromSpecResidueField y.1.point) hq
        (localSection I J hJ U hU))) : ℝ≥0∞) = modelIdealLog I hb y - modelIdealLog J hb y := by
  obtain ⟨hn,he⟩ := exists_native_eq I J hJ U hU hb y hI q hq
  rw [he]
  exact modelLineNorm_genericCartierRatioSection_weight hb y I J hI hJ hn

/-- The actual original local polarized section is the tensor of the SAME original global section and actual local Cartier ratio. -/
def localPolarizedSection {L : N.Modules} (τ : unitObj N ⟶ L) :
    unitObj U.toScheme ⟶ (pullback U.ι).obj (Scheme.Modules.tensorObj L (I.ratioModule J)) :=
  tensorRight (pullbackSectionHom U.ι τ) (localSection I J hJ U hU) ≫
    (Functor.Monoidal.μIso (pullback U.ι) L (I.ratioModule J)).hom ≫
      (pullback U.ι).map (ModularCurves.monoidalTensorObjIso L (I.ratioModule J)).hom

/-- The genuine whole local polarized section pulls to the SAME actual global-section/canonical-Cartier pure native tensor. -/
theorem localPolarizedSection_native_eq {L : N.Modules} (τ : unitObj N ⟶ L) :
    sectionAtOne (sectionViaFactor q U.ι (N.fromSpecResidueField y.1.point) hq
      (localPolarizedSection I J hJ U hU τ)) =
      genericTensorSection y (fibreSection y τ) (genericCartierRatioSection hb y I J hI hJ hn) := by
  let p := N.fromSpecResidueField y.1.point
  let a := pullbackSectionHom U.ι τ
  let b := localSection I J hJ U hU
  have ht := sectionViaFactor_tensor q U.ι p hq a b
  have hs : sectionViaFactor q U.ι p hq
      (tensorRight a b ≫ (Functor.Monoidal.μIso (pullback U.ι) L (I.ratioModule J)).hom) =
      tensorRight (sectionViaFactor q U.ι p hq a) (sectionViaFactor q U.ι p hq b) ≫
        (Functor.Monoidal.μIso (pullback p) L (I.ratioModule J)).hom := by
    have h := congrArg (fun r => r ≫ (Functor.Monoidal.μIso (pullback p) L (I.ratioModule J)).hom) ht
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using h.symm
  unfold localPolarizedSection
  rw [← Category.assoc,sectionViaFactor_post,hs]
  change ((pullback p).map (ModularCurves.monoidalTensorObjIso L (I.ratioModule J)).hom).val.app (op ⊤)
    ((Functor.Monoidal.μIso (pullback p) L (I.ratioModule J)).hom.val.app (op ⊤)
      (sectionAtOne (tensorRight (sectionViaFactor q U.ι p hq a) (sectionViaFactor q U.ι p hq b)))) = _
  rw [sectionAtOne_tensorRight,sectionViaFactor_global]
  have hb' := native_eq I J hJ U hU hb y hI q hq hn
  change sectionAtOne (sectionViaFactor q U.ι p hq b) = genericCartierRatioSection hb y I J hI hJ hn at hb'
  rw [hb']
  rfl

omit hn in
/-- The true local polarized section retains its genuine original model norm, including actual zeros. -/
theorem localPolarizedSection_norm {L : N.Modules} (hL : IsInvertible L) (τ : unitObj N ⟶ L) :
    (modelLineNorm hb y (hL.tensorObj (hI.isInvertible_ratioModule hJ))
      (sectionAtOne (sectionViaFactor q U.ι (N.fromSpecResidueField y.1.point) hq
        (localPolarizedSection I J hJ U hU τ))) : ℝ≥0∞) =
      (modelLineNorm hb y hL (fibreSection y τ) : ℝ≥0∞) *
        (modelIdealNorm I hb y)⁻¹ * modelIdealNorm J hb y := by
  obtain ⟨hn,_,_⟩ := CartierCanonicalOpenFrame.exists_nativeFrame hb y I hI U hU q hq
  rw [localPolarizedSection_native_eq I J hJ U hU hb y hI q hq hn,
    modelLineNorm_genericTensorSection hb y hL (hI.isInvertible_ratioModule hJ),
    ENNReal.coe_mul,modelLineNorm_genericCartierRatioSection]
  exact (mul_assoc _ _ _).symm

end EnvelopeProperty.CartierRatioLocalRealization
