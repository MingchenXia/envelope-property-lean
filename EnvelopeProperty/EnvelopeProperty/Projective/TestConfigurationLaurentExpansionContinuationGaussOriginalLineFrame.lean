import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussModelTransport

/-! # Actual original polarization frames on the same Laurent spectrum

The original full action-space linearization and fibre-one identification
DERIVE the unit-open polarization iso. The original Gauss projection square
constructs its actual Laurent-spectrum and actual Gauss-field frames. Every
section/unit and coefficient comparison below is proved through these actual
maps; no polarization comparison or norm equality is supplied.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped NNReal LaurentPolynomial Classical
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich SchemeLineSectionEvaluation Scheme.Modules

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X) {v : Valuation k ℝ≥0}
  (x : RelativeSchemeValuedPoint v X.hom)

/-- The SAME original Gauss projection square constructs the whole original
Laurent-spectrum frame from an actual original X residue-line frame. -/
def originalTestConfigurationGaussProjectionLineFrame (L : X.left.Modules)
    (e : (pullback (X.left.fromSpecResidueField x.1.point)).obj L ≅
      unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point)))) :
    (pullback (originalTestConfigurationGaussMorph C x ≫
      originalTestConfigurationUnitProjection C)).obj L ≅
        unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])) :=
  frameViaFactor
    (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : X.left.residueField x.1.point →+*
      (X.left.residueField x.1.point)[T;T⁻¹])))
    (X.left.fromSpecResidueField x.1.point)
    (originalTestConfigurationGaussMorph C x ≫ originalTestConfigurationUnitProjection C)
    (originalTestConfigurationGaussMorph_projection C x).symm e

variable (M : C.total.Modules) (L : X.left.Modules)
  (linearization :
    (pullback (originalTestConfigurationTotalAction C).left).obj M ≅
      (pullback
        (CartesianMonoidalCategory.snd (ProjBerk.nativeMultiplicativeGroup k)
          (NativeTestConfiguration.totalOver k C.projection)).left).obj M)
  (fibreOneIdentification :
    (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L)
  (e : (pullback (X.left.fromSpecResidueField x.1.point)).obj L ≅
    unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point))))

/-- ORIGINAL source linearization/fibre-one data DERIVE the actual whole
Laurent-spectrum frame on the SAME original total-model polarization. -/
def originalTestConfigurationGaussModelLineFrame :
    (pullback (originalTestConfigurationGaussMorph C x ≫ C.unitOpen.ι)).obj M ≅
      unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])) :=
  ((pullbackComp (originalTestConfigurationGaussMorph C x) C.unitOpen.ι).app M).symm ≪≫
    (pullback (originalTestConfigurationGaussMorph C x)).mapIso
      (originalTestConfigurationPolarizationUnitIso C M L linearization fibreOneIdentification) ≪≫
    (pullbackComp (originalTestConfigurationGaussMorph C x)
      (originalTestConfigurationUnitProjection C)).app L ≪≫
    originalTestConfigurationGaussProjectionLineFrame C x L e

/-- The actual constructed frame retains the ENTIRE genuine pullback pairing
with the SAME original DERIVED polarization comparison. -/
theorem originalTestConfigurationGaussModelLineFrame_pairing :
    (pullbackComp (originalTestConfigurationGaussMorph C x) C.unitOpen.ι).app M ≪≫
        originalTestConfigurationGaussModelLineFrame C x M L linearization
          fibreOneIdentification e =
      (pullback (originalTestConfigurationGaussMorph C x)).mapIso
          (originalTestConfigurationPolarizationUnitIso C M L linearization fibreOneIdentification) ≪≫
        (pullbackComp (originalTestConfigurationGaussMorph C x)
          (originalTestConfigurationUnitProjection C)).app L ≪≫
        originalTestConfigurationGaussProjectionLineFrame C x L e := by
  simp only [originalTestConfigurationGaussModelLineFrame, Iso.self_symm_id_assoc]

/-- EVERY original whole model section retains its actual structure-unit map
through the constructed original Laurent-spectrum polarization frame. -/
theorem originalTestConfigurationGaussModelLineFrame_sectionHom
    (α : unitObj C.total ⟶ M) :
    pullbackSectionHom (originalTestConfigurationGaussMorph C x ≫ C.unitOpen.ι) α ≫
        (originalTestConfigurationGaussModelLineFrame C x M L linearization
          fibreOneIdentification e).hom =
      pullbackSectionHom (originalTestConfigurationGaussMorph C x)
          (pullbackSectionHom C.unitOpen.ι α ≫
            (originalTestConfigurationPolarizationUnitIso C M L linearization
              fibreOneIdentification).hom) ≫
        ((pullbackComp (originalTestConfigurationGaussMorph C x)
          (originalTestConfigurationUnitProjection C)).app L ≪≫
          originalTestConfigurationGaussProjectionLineFrame C x L e).hom := by
  rw [← pullbackSectionHom_comp (originalTestConfigurationGaussMorph C x) C.unitOpen.ι α]
  simp only [originalTestConfigurationGaussModelLineFrame, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.app_inv, Iso.hom_inv_id_app_assoc, pullbackSectionHom,
    Functor.map_comp]

/-- EVERY original X section has its actual scalar pullback along the SAME
original constant inclusion, derived from the genuine geometric projection. -/
theorem originalTestConfigurationGaussProjectionLineFrame_sectionHom
    (α : unitObj X.left ⟶ L) :
    pullbackSectionHom (originalTestConfigurationGaussMorph C x ≫
        originalTestConfigurationUnitProjection C) α ≫
      (originalTestConfigurationGaussProjectionLineFrame C x L e).hom =
      ModularCurves.unitEndomorphismOfTopSection
        ((Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : X.left.residueField x.1.point →+*
          (X.left.residueField x.1.point)[T;T⁻¹]))).appTop.hom
          (SchemeLineSectionUnitFrames.frameScalar e
            (pullbackSectionHom (X.left.fromSpecResidueField x.1.point) α))) :=
  frameViaFactor_sectionHom_scalar _ _ _ _ e α _
    (SchemeLineSectionUnitFrames.frameScalar_identity e _)

/-- The ACTUAL whole Laurent scalar of every original X section is LITERALLY
the constant Laurent polynomial of its ORIGINAL residue-frame coefficient. -/
theorem originalTestConfigurationGaussProjectionLineFrame_coefficient
    (α : unitObj X.left ⟶ L) :
    (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom
        ((originalTestConfigurationGaussProjectionLineFrame C x L e).hom.val.app (op ⊤)
          (sectionAtOne (pullbackSectionHom (originalTestConfigurationGaussMorph C x ≫
            originalTestConfigurationUnitProjection C) α))) =
      LaurentPolynomial.C
        ((Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point))).hom
          (SchemeLineSectionUnitFrames.frameScalar e
            (pullbackSectionHom (X.left.fromSpecResidueField x.1.point) α))) := by
  have h := frameViaFactor_sectionHom_scalar_apply
    (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : X.left.residueField x.1.point →+*
      (X.left.residueField x.1.point)[T;T⁻¹])))
    (X.left.fromSpecResidueField x.1.point)
    (originalTestConfigurationGaussMorph C x ≫ originalTestConfigurationUnitProjection C)
    (originalTestConfigurationGaussMorph_projection C x).symm e α _
    (SchemeLineSectionUnitFrames.frameScalar_identity e _)
  have hh := congrArg
    (fun a => (Scheme.ΓSpecIso
      (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom a) h
  exact hh.trans (congrArg (fun a => a.hom
    (SchemeLineSectionUnitFrames.frameScalar e
      (pullbackSectionHom (X.left.fromSpecResidueField x.1.point) α)))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
      (LaurentPolynomial.C : X.left.residueField x.1.point →+*
        (X.left.residueField x.1.point)[T;T⁻¹]))))

variable (r : ℝ≥0) (hr : 0 < r)

/-- The SAME actual canonical Gauss residue morphism constructs the original
polarization frame over LITERALLY kappa(z), without center-in-unit assumptions. -/
def originalTestConfigurationGaussFieldPolarizationFrame :
    (pullback (originalTestConfigurationGaussFieldMorph C x r hr)).obj M ≅
      unitObj (Spec (CommRingCat.of
        ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).residueField
          (originalNativeLaurentGaussPoint x.1.residueVal r hr).point))) :=
  frameViaFactor
    ((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).fromSpecResidueField
      (originalNativeLaurentGaussPoint x.1.residueVal r hr).point)
    (originalTestConfigurationGaussMorph C x ≫ C.unitOpen.ι)
    (originalTestConfigurationGaussFieldMorph C x r hr) rfl
    (originalTestConfigurationGaussModelLineFrame C x M L linearization fibreOneIdentification e)

/-- EVERY SAME original whole model section has its actual coefficient scalar
transport through the constructed actual original Gauss-field frame. -/
theorem originalTestConfigurationGaussFieldPolarizationFrame_sectionHom
    (α : unitObj C.total ⟶ M) :
    pullbackSectionHom (originalTestConfigurationGaussFieldMorph C x r hr) α ≫
      (originalTestConfigurationGaussFieldPolarizationFrame C x M L linearization
        fibreOneIdentification e r hr).hom =
      ModularCurves.unitEndomorphismOfTopSection
        (((Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).fromSpecResidueField
          (originalNativeLaurentGaussPoint x.1.residueVal r hr).point).appTop.hom
          (SchemeLineSectionUnitFrames.frameScalar
            (originalTestConfigurationGaussModelLineFrame C x M L linearization
              fibreOneIdentification e)
            (pullbackSectionHom (originalTestConfigurationGaussMorph C x ≫ C.unitOpen.ι) α))) :=
  frameViaFactor_sectionHom_scalar _ _ _ _ _ α _
    (SchemeLineSectionUnitFrames.frameScalar_identity _ _)

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
