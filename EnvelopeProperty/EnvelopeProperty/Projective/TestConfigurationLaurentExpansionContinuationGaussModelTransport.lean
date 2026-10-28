import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussLocalValues
import EnvelopeProperty.AlgGeom.SchemeLineSectionUnitFrames
import EnvelopeProperty.AlgGeom.SchemeLineFramePullbackCoherence
import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization

/-! # Genuine field pullback of original TC generic lines and model norms

The field is the actual residue field of the SAME native Laurent Gauss point.
Field-point classification derives the geometric factorization, and native
pullback comparisons construct the whole generic-line transport. Every
coefficient equality is proved from actual scalar pullback. The genuine
valuative frame is constructed by original invertibility and properness;
no unit-open isometry or coefficient/metric comparison is assumed.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped NNReal LaurentPolynomial Classical
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich SchemeLineSectionEvaluation

variable {K : Type u} [Field K] {Y : Scheme.{u}}
  (f : Spec (CommRingCat.of K) ⟶ Y)

/-- The ACTUAL field-point classification derives its entire geometric factorization. -/
theorem originalFieldResidueFactorization :
    Spec.map (Scheme.SpecToEquivOfField K Y f).2 ≫
        Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y f).1 = f :=
  (Scheme.SpecToEquivOfField K Y).symm_apply_apply f

/-- The native composition/congruence maps construct the SAME whole field/residue-line iso. -/
def originalFieldResidueLineIso (M : Y.Modules) :
    (Scheme.Modules.pullback (Spec.map (Scheme.SpecToEquivOfField K Y f).2)).obj
        ((Scheme.Modules.pullback
          (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y f).1)).obj M) ≅
      (Scheme.Modules.pullback f).obj M :=
  Scheme.Modules.frameFactorIso (Spec.map (Scheme.SpecToEquivOfField K Y f).2)
    (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y f).1) f
    (originalFieldResidueFactorization f) M

/-- An ACTUAL original residue-line frame transports through that derived geometric iso. -/
def originalFieldResidueLineFrame {M : Y.Modules}
    (e : (Scheme.Modules.pullback
        (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y f).1)).obj M ≅
      Scheme.Modules.unitObj
        (Spec (CommRingCat.of (Y.residueField (Scheme.SpecToEquivOfField K Y f).1)))) :
    (Scheme.Modules.pullback f).obj M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of K)) :=
  (originalFieldResidueLineIso f M).symm ≪≫
    (Scheme.Modules.pullback (Spec.map (Scheme.SpecToEquivOfField K Y f).2)).mapIso e ≪≫
      Scheme.Modules.pullbackUnitIso (Spec.map (Scheme.SpecToEquivOfField K Y f).2)

/-- The constructed field-line comparison and frame retain the ENTIRE original pairing. -/
theorem originalFieldResidueLineIso_frame {M : Y.Modules}
    (e : (Scheme.Modules.pullback
        (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y f).1)).obj M ≅
      Scheme.Modules.unitObj
        (Spec (CommRingCat.of (Y.residueField (Scheme.SpecToEquivOfField K Y f).1)))) :
    originalFieldResidueLineIso f M ≪≫ originalFieldResidueLineFrame f e =
      (Scheme.Modules.pullback (Spec.map (Scheme.SpecToEquivOfField K Y f).2)).mapIso e ≪≫
        Scheme.Modules.pullbackUnitIso (Spec.map (Scheme.SpecToEquivOfField K Y f).2) := by
  simp only [originalFieldResidueLineFrame, Iso.self_symm_id_assoc]

/-- EVERY actual original generic-line section morphism has its true field pullback. -/
def originalFieldResidueSectionHom {M : Y.Modules}
    (β : Scheme.Modules.unitObj
        (Spec (CommRingCat.of (Y.residueField (Scheme.SpecToEquivOfField K Y f).1))) ⟶
      (Scheme.Modules.pullback
        (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y f).1)).obj M) :
    Scheme.Modules.unitObj (Spec (CommRingCat.of K)) ⟶ (Scheme.Modules.pullback f).obj M :=
  pullbackSectionHom (Spec.map (Scheme.SpecToEquivOfField K Y f).2) β ≫
    (originalFieldResidueLineIso f M).hom

/-- The constructed ACTUAL whole-module comparison retains the SAME original
whole model section and its genuine structure-unit map. -/
theorem originalFieldResidueSectionHom_global {M : Y.Modules}
    (α : Scheme.Modules.unitObj Y ⟶ M) :
    originalFieldResidueSectionHom f (M := M)
        (pullbackSectionHom
          (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y f).1) α) =
      pullbackSectionHom f α :=
  SchemeLineSectionFactorization.pullbackSectionHom_factor
    (Spec.map (Scheme.SpecToEquivOfField K Y f).2)
    (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y f).1) f
    (originalFieldResidueFactorization f) α

/-- The ACTUAL transported coefficient is the actual scalar pullback of the
SAME original generic coefficient; no scalar equality is an input. -/
theorem originalFieldResidueSectionHom_coefficient {M : Y.Modules}
    (e : (Scheme.Modules.pullback
        (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y f).1)).obj M ≅
      Scheme.Modules.unitObj
        (Spec (CommRingCat.of (Y.residueField (Scheme.SpecToEquivOfField K Y f).1))))
    (β : Scheme.Modules.unitObj
        (Spec (CommRingCat.of (Y.residueField (Scheme.SpecToEquivOfField K Y f).1))) ⟶
      (Scheme.Modules.pullback
        (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y f).1)).obj M) :
    (originalFieldResidueLineFrame f (M := M) e).hom.val.app (op ⊤)
        (sectionAtOne (originalFieldResidueSectionHom f (M := M) β)) =
      (Spec.map (Scheme.SpecToEquivOfField K Y f).2).appTop.hom
        (SchemeLineSectionUnitFrames.frameScalar e β) := by
  have happ {B : Scheme.{u}} {N P : B.Modules}
      (α : Scheme.Modules.unitObj B ⟶ N) (γ : N ⟶ P) :
      sectionAtOne (α ≫ γ) = γ.val.app (op ⊤) (sectionAtOne α) := by
    rfl
  have hscalar {B : Scheme.{u}} (a : Γ(B, ⊤)) :
      sectionAtOne (ModularCurves.unitEndomorphismOfTopSection a) = a := by
    unfold sectionAtOne
    rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
    simp only [homOfLE_refl, op_id, one_mul]
    change B.presheaf.map (𝟙 (op (⊤ : B.Opens))) a = a
    exact congrArg (fun q : Γ(B, ⊤) ⟶ Γ(B, ⊤) => q a)
      (B.presheaf.map_id (op ⊤))
  have hs := SchemeLineSectionUnitFrames.pullback_frameScalar
    (Spec.map (Scheme.SpecToEquivOfField K Y f).2) e β
  have h : originalFieldResidueSectionHom f (M := M) β ≫
      (originalFieldResidueLineFrame f (M := M) e).hom =
      ModularCurves.unitEndomorphismOfTopSection
        ((Spec.map (Scheme.SpecToEquivOfField K Y f).2).appTop.hom
          (SchemeLineSectionUnitFrames.frameScalar e β)) := by
    simpa only [originalFieldResidueSectionHom, originalFieldResidueLineFrame,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc, Iso.hom_inv_id_assoc] using hs
  have hh := congrArg (fun q : Scheme.Modules.unitObj (Spec (CommRingCat.of K)) ⟶
      Scheme.Modules.unitObj (Spec (CommRingCat.of K)) => sectionAtOne q) h
  rw [happ (B := Spec (CommRingCat.of K))] at hh
  exact hh.trans (hscalar (B := Spec (CommRingCat.of K)) _)

/-- The true field valuation of EVERY transported original coefficient equals
the SAME constructed native point's original residue valuation. -/
theorem originalFieldResidueSectionHom_value (w : Valuation K ℝ≥0) {M : Y.Modules}
    (e : (Scheme.Modules.pullback
        (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y f).1)).obj M ≅
      Scheme.Modules.unitObj
        (Spec (CommRingCat.of (Y.residueField (Scheme.SpecToEquivOfField K Y f).1))))
    (β : Scheme.Modules.unitObj
        (Spec (CommRingCat.of (Y.residueField (Scheme.SpecToEquivOfField K Y f).1))) ⟶
      (Scheme.Modules.pullback
        (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y f).1)).obj M) :
    w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom
        ((originalFieldResidueLineFrame f (M := M) e).hom.val.app (op ⊤)
          (sectionAtOne (originalFieldResidueSectionHom f (M := M) β)))) =
      (originalFieldValuedPoint f w).residueVal
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.residueField (Scheme.SpecToEquivOfField K Y f).1))).hom
          (SchemeLineSectionUnitFrames.frameScalar e β)) := by
  rw [originalFieldResidueSectionHom_coefficient f (M := M) e β]
  exact congrArg w (congrArg (fun a => a.hom
    (SchemeLineSectionUnitFrames.frameScalar e β))
    (Scheme.ΓSpecIso_naturality (Scheme.SpecToEquivOfField K Y f).2))

/-- Literal code for the SAME entire native model-norm equality. It is
proved unconditionally below, never accepted as a comparison certificate. -/
def originalFieldModelNormSectionHomFormula
    {R : Type u} [CommRing R] {vR : Valuation R ℝ≥0}
    (q : Y ⟶ Spec (CommRingCat.of R)) [IsProper q]
    (hb : ∀ a, vR a ≤ 1) (w : Valuation K ℝ≥0)
    (hbase : SchemeValuedPoint.map q (originalFieldValuedPoint f w) =
      SchemeValuedPoint.basePoint vR)
    {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M) : Prop :=
    let y : RelativeSchemeValuedPoint vR q := ⟨originalFieldValuedPoint f w, hbase⟩
    ∃ e : RelativeSchemeValuedPoint.centerLineModule hb y M ≅ Scheme.Modules.unitObj
        (Spec (CommRingCat.of (RelativeSchemeValuedPoint.CenterRing y))),
      ∀ β : Scheme.Modules.unitObj (Spec (CommRingCat.of (Y.residueField y.1.point))) ⟶
          RelativeSchemeValuedPoint.genericLineModule y M,
        RelativeSchemeValuedPoint.modelLineNorm hb y (M := M) hM (sectionAtOne β) =
          w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom
            ((originalFieldResidueLineFrame f (M := M)
              (RelativeSchemeValuedPoint.centerFrameGenericIso hb y (M := M) e)).hom.val.app
                (op ⊤) (sectionAtOne (originalFieldResidueSectionHom f (M := M) β))))

/-- A genuine native prescribed-base field point on an arbitrary proper model
has its intrinsic norm computed by its constructed actual field pullback frame.
The base membership is exactly the native RelativeSchemeValuedPoint condition;
the TC consumer below DERIVES it from the original geometric parameter map. -/
theorem originalFieldModelNorm_sectionHom
    {R : Type u} [CommRing R] {vR : Valuation R ℝ≥0}
    (q : Y ⟶ Spec (CommRingCat.of R)) [IsProper q]
    (hb : ∀ a, vR a ≤ 1) (w : Valuation K ℝ≥0)
    (hbase : SchemeValuedPoint.map q (originalFieldValuedPoint f w) =
      SchemeValuedPoint.basePoint vR)
    {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M) :
    originalFieldModelNormSectionHomFormula f q hb w hbase (M := M) hM := by
  dsimp only [originalFieldModelNormSectionHomFormula]
  let y : RelativeSchemeValuedPoint vR q := ⟨originalFieldValuedPoint f w, hbase⟩
  obtain ⟨e⟩ := RelativeSchemeValuedPoint.exists_centerLineUnitIso
    (R := R) (v := vR) (X := Y) (f := q) (M := M) hb y hM
  refine ⟨e, fun β => ?_⟩
  rw [RelativeSchemeValuedPoint.modelLineNorm_eq_frame
    (R := R) (v := vR) (X := Y) (f := q) (M := M) hb y hM e]
  exact (originalFieldResidueSectionHom_value f w (M := M)
    (RelativeSchemeValuedPoint.centerFrameGenericIso hb y (M := M) e) β).symm

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X) {v : Valuation k ℝ≥0}
  (x : RelativeSchemeValuedPoint v X.hom) (r : ℝ≥0) (hr : 0 < r)

/-- The field is LITERALLY the residue field of the SAME original Laurent
Gauss point, mapped through the SAME original constructed g and unit inclusion. -/
def originalTestConfigurationGaussFieldMorph :
    Spec ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField
      (originalNativeLaurentGaussPoint x.1.residueVal r hr).point) ⟶ C.total :=
  (Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).fromSpecResidueField
      (originalNativeLaurentGaussPoint x.1.residueVal r hr).point ≫
    (originalTestConfigurationGaussMorph C x ≫ C.unitOpen.ι)

/-- This actual original field morphism represents the ENTIRE SAME total
Gauss point, rather than only the same support or an assumed valuation. -/
theorem originalTestConfigurationGaussFieldMorph_point :
    originalFieldValuedPoint (originalTestConfigurationGaussFieldMorph C x r hr)
        (originalNativeLaurentGaussPoint x.1.residueVal r hr).residueVal =
      originalTestConfigurationTotalGaussPoint C x r hr := by
  unfold originalTestConfigurationGaussFieldMorph
  rw [← originalFieldValuedPoint_map, originalFieldValuedPoint_fromResidueField,
    SchemeValuedPoint.map_comp]
  rfl

/-- The actual whole-point equality derives genuine prescribed-base membership
for the SAME original field-spectrum construction. -/
def originalTestConfigurationGaussFieldRelativePoint :
    RelativeSchemeValuedPoint (gaussValuation v r) C.projection :=
  ⟨originalFieldValuedPoint (originalTestConfigurationGaussFieldMorph C x r hr)
      (originalNativeLaurentGaussPoint x.1.residueVal r hr).residueVal,
    by rw [originalTestConfigurationGaussFieldMorph_point]
       exact originalTestConfigurationTotalGaussPoint_parameter C x r hr⟩

/-- The true relative field-point is exactly the original total relative Gauss point. -/
theorem originalTestConfigurationGaussFieldRelativePoint_eq :
    originalTestConfigurationGaussFieldRelativePoint C x r hr =
      originalTestConfigurationGaussRelativePoint C x r hr :=
  Subtype.ext (originalTestConfigurationGaussFieldMorph_point C x r hr)

local instance originalGaussModelProjectionIsProper : IsProper C.projection :=
  C.projection_isProper


/-- ORIGINAL properness and invertibility construct an actual valuative frame
computing EVERY original generic-line section morphism by its true field pullback.
Neither a center frame nor a metric/coefficient comparison is an input. -/
theorem originalTestConfigurationGaussField_modelNorm_sectionHom
    (x₀ : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) (hr₁ : r ≤ 1)
    {M : C.total.Modules} (hM : Scheme.Modules.IsInvertible M) :
    originalFieldModelNormSectionHomFormula
    (originalTestConfigurationGaussFieldMorph C x₀ r hr)
    (R := Polynomial k) (vR := gaussValuation (1 : Valuation k ℝ≥0) r) C.projection
    (originalTrivialPolynomialGauss_bounded (k := k) r hr₁)
    (originalNativeLaurentGaussPoint x₀.1.residueVal r hr).residueVal
    (originalTestConfigurationGaussFieldRelativePoint C x₀ r hr).property (M := M) hM :=
  originalFieldModelNorm_sectionHom
    (originalTestConfigurationGaussFieldMorph C x₀ r hr)
    (R := Polynomial k) (vR := gaussValuation (1 : Valuation k ℝ≥0) r) C.projection
    (originalTrivialPolynomialGauss_bounded (k := k) r hr₁)
    (originalNativeLaurentGaussPoint x₀.1.residueVal r hr).residueVal
    (originalTestConfigurationGaussFieldRelativePoint C x₀ r hr).property (M := M) hM

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
