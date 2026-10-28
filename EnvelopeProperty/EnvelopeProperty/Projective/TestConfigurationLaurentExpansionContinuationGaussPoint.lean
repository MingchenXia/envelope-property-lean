import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationModelOpenSections
import EnvelopeProperty.Berkovich.SchemeCenter
import EnvelopeProperty.Berkovich.SpectrumLaurentGauss

/-! # Actual original residue-field points toward the original TC Gauss point

Genuine native Spec-to-point classification constructs native scheme valued
points from actual field spectra. The SAME original residue field recovers
the ENTIRE original valued point. No point, coefficient-value, or metric
comparison is supplied as a certificate.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped NNReal LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich

/-- A genuine actual field-spectrum map and actual field valuation construct
a native valued point by its true native residue-field embedding. -/
def originalFieldValuedPoint {K : Type u} [Field K] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of K) ⟶ Y) (v : Valuation K ℝ≥0) : SchemeValuedPoint Y :=
  let xf := Scheme.SpecToEquivOfField K Y f
  ⟨xf.1, v.comap xf.2.hom⟩

/-- The constructed actual native point retains the SAME geometric image. -/
theorem originalFieldValuedPoint_point {K : Type u} [Field K] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of K) ⟶ Y) (v : Valuation K ℝ≥0) :
    (originalFieldValuedPoint f v).point = f (IsLocalRing.closedPoint K) := rfl

/-- Actual composition retains the WHOLE original valued point, by genuine
native residue-field-map composition, without a value comparison input. -/
theorem originalFieldValuedPoint_map {K : Type u} [Field K] {Y Z : Scheme.{u}}
    (f : Spec (CommRingCat.of K) ⟶ Y) (g : Y ⟶ Z) (v : Valuation K ℝ≥0) :
    SchemeValuedPoint.map g (originalFieldValuedPoint f v) =
      originalFieldValuedPoint (f ≫ g) v := by
  change (⟨g (f (IsLocalRing.closedPoint K)),
    (v.comap (Y.descResidueField (Scheme.stalkClosedPointTo f)).hom).comap
      (g.residueFieldMap (f (IsLocalRing.closedPoint K))).hom⟩ : SchemeValuedPoint Z) =
    ⟨g (f (IsLocalRing.closedPoint K)),
      v.comap (Z.descResidueField (Scheme.stalkClosedPointTo (f ≫ g))).hom⟩
  rw [Scheme.descResidueField_stalkClosedPointTo_comp]
  rfl

/-- The actual original residue-field map and original residue valuation
recover the ENTIRE SAME original valued point, rather than merely support. -/
theorem originalFieldValuedPoint_fromResidueField {Y : Scheme.{u}} (y : SchemeValuedPoint Y) :
    originalFieldValuedPoint (Y.fromSpecResidueField y.point) y.residueVal = y := by
  let e := Scheme.SpecToEquivOfField (Y.residueField y.point) Y
  have hid : e.symm ⟨y.point, 𝟙 (Y.residueField y.point)⟩ =
      Y.fromSpecResidueField y.point := by
    change Spec.map (𝟙 (Y.residueField y.point)) ≫ Y.fromSpecResidueField y.point = _
    simp
  have hs := e.apply_symm_apply ⟨y.point, 𝟙 (Y.residueField y.point)⟩
  rw [hid] at hs
  unfold originalFieldValuedPoint
  change (⟨(e (Y.fromSpecResidueField y.point)).1,
    y.residueVal.comap (e (Y.fromSpecResidueField y.point)).2.hom⟩ : SchemeValuedPoint Y) = y
  rw [hs]
  cases y
  rfl

/-- The genuine field-spectrum factorization preserves the ENTIRE original
global section map, through its actual residue-field embedding. -/
theorem originalFieldValuedPoint_appTop {K : Type u} [Field K] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of K) ⟶ Y) :
    Y.Γevaluation (Scheme.SpecToEquivOfField K Y f).1 ≫
        (Scheme.SpecToEquivOfField K Y f).2 =
      f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
  let xf := Scheme.SpecToEquivOfField K Y f
  have hf : Spec.map xf.2 ≫ Y.fromSpecResidueField xf.1 = f :=
    (Scheme.SpecToEquivOfField K Y).symm_apply_apply f
  calc
    _ = ((Y.fromSpecResidueField xf.1).appTop ≫
        (Scheme.ΓSpecIso (Y.residueField xf.1)).hom) ≫ xf.2 := by
      rw [SchemeValuedPoint.fromSpecResidueField_appTop]
    _ = (Spec.map xf.2 ≫ Y.fromSpecResidueField xf.1).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
      simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
    _ = _ := congrArg (fun a : Spec (CommRingCat.of K) ⟶ Y =>
      a.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom) hf

/-- EVERY original whole section has its actual field-pullback value at the
constructed native point; no coefficient-value comparison is a premise. -/
theorem originalFieldValuedPoint_evalTop {K : Type u} [Field K] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of K) ⟶ Y) (v : Valuation K ℝ≥0) (s : Γ(Y, ⊤)) :
    SchemeValuedPoint.eval (originalFieldValuedPoint f v) ⊤ trivial s =
      v ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (f.appTop s)) := by
  change v ((Scheme.SpecToEquivOfField K Y f).2
    (Y.Γevaluation (Scheme.SpecToEquivOfField K Y f).1 s)) = _
  exact congrArg v (congrArg (fun a : Γ(Y, ⊤) ⟶ CommRingCat.of K => a s)
    (originalFieldValuedPoint_appTop f))

/-- On the SAME actual field spectrum the construction is the independently
defined native point of its actual valuation, on ALL original ring values. -/
theorem originalFieldValuedPoint_id {K : Type u} [Field K] (v : Valuation K ℝ≥0) :
    originalFieldValuedPoint (𝟙 (Spec (CommRingCat.of K))) v =
      SchemeValuedPoint.basePoint v := by
  apply (SchemeValuedPoint.spectrumHomeomorph (A := K)).injective
  rw [SchemeValuedPoint.basePoint, Homeomorph.apply_symm_apply]
  apply Spectrum.ext_val
  intro a
  rw [SchemeValuedPoint.spectrumHomeomorph_val_apply, originalFieldValuedPoint_evalTop]
  simp

/-- The actual native point of the ORIGINAL residue valuation maps to the
ENTIRE original valued point along its SAME canonical residue morphism. -/
theorem originalNativeResiduePoint_map {Y : Scheme.{u}} (y : SchemeValuedPoint Y) :
    SchemeValuedPoint.map (Y.fromSpecResidueField y.point)
      (SchemeValuedPoint.basePoint y.residueVal) = y := by
  rw [← originalFieldValuedPoint_id, originalFieldValuedPoint_map]
  simpa using originalFieldValuedPoint_fromResidueField y

/-- The actual original Laurent localization's native Gauss point, constructed
from the genuine polynomial Gauss valuation and its genuine localization. -/
def originalNativeLaurentGaussPoint {A : Type u} [CommRing A]
    (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint (Spec (CommRingCat.of A[T;T⁻¹])) :=
  SchemeValuedPoint.spectrumHomeomorph.symm (Spectrum.laurentGauss v r hr)

/-- EVERY literal Laurent section has its original localization Gauss value. -/
theorem originalNativeLaurentGaussPoint_eval {A : Type u} [CommRing A]
    (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r) (f : A[T;T⁻¹]) :
    SchemeValuedPoint.eval (originalNativeLaurentGaussPoint v r hr) ⊤ trivial
        ((Scheme.ΓSpecIso (CommRingCat.of A[T;T⁻¹])).inv f) =
      (Spectrum.laurentGauss v r hr).val f := by
  rw [← SchemeValuedPoint.spectrumHomeomorph_val_apply,
    originalNativeLaurentGaussPoint, Homeomorph.apply_symm_apply]

/-- Every SAME actual coefficient retains its ORIGINAL valuation. -/
theorem originalNativeLaurentGaussPoint_eval_C {A : Type u} [CommRing A]
    (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r) (a : A) :
    SchemeValuedPoint.eval (originalNativeLaurentGaussPoint v r hr) ⊤ trivial
        ((Scheme.ΓSpecIso (CommRingCat.of A[T;T⁻¹])).inv (LaurentPolynomial.C a)) = v a := by
  rw [originalNativeLaurentGaussPoint_eval, Spectrum.laurentGauss_val_C]

/-- Every integer power of the ORIGINAL Laurent coordinate has its true value. -/
theorem originalNativeLaurentGaussPoint_eval_T {A : Type u} [CommRing A]
    (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r) (n : ℤ) :
    SchemeValuedPoint.eval (originalNativeLaurentGaussPoint v r hr) ⊤ trivial
        ((Scheme.ΓSpecIso (CommRingCat.of A[T;T⁻¹])).inv (LaurentPolynomial.T n)) = r ^ n := by
  rw [originalNativeLaurentGaussPoint_eval, Spectrum.laurentGauss_val_T]

/-- EVERY original Laurent polynomial has exactly its ACTUAL finite-support
coefficient maximum; no Gauss/coefficient comparison is a hypothesis. -/
theorem originalNativeLaurentGaussPoint_eval_eq_sup {A : Type u} [CommRing A]
    (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r) (f : A[T;T⁻¹]) :
    SchemeValuedPoint.eval (originalNativeLaurentGaussPoint v r hr) ⊤ trivial
        ((Scheme.ΓSpecIso (CommRingCat.of A[T;T⁻¹])).inv f) =
      f.coeff.support.sup (fun n => v (f.coeff n) * r ^ n) := by
  rw [originalNativeLaurentGaussPoint_eval, Spectrum.laurentGauss_val_eq_sup]

/-- The true Laurent coefficient projection maps the ENTIRE constructed
Gauss point to the independently defined native original coefficient point. -/
theorem originalNativeLaurentGaussPoint_map_C {A : Type u} [CommRing A]
    (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : A →+* A[T;T⁻¹])))
        (originalNativeLaurentGaussPoint v r hr) = SchemeValuedPoint.basePoint v := by
  apply (SchemeValuedPoint.spectrumHomeomorph (A := A)).injective
  rw [SchemeValuedPoint.spectrumHomeomorph_map, originalNativeLaurentGaussPoint,
    Homeomorph.apply_symm_apply, SchemeValuedPoint.basePoint, Homeomorph.apply_symm_apply]
  exact Spectrum.ext_val (fun a => Spectrum.laurentGauss_val_C v r hr a)

/-- For the ORIGINAL residue field and original residue morphism, the actual
Laurent Gauss projection recovers the ENTIRE SAME original valued point. -/
theorem originalNativeResidueLaurentGaussPoint_map {Y : Scheme.{u}}
    (y : SchemeValuedPoint Y) (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint.map
        (Spec.map (CommRingCat.ofHom
          (LaurentPolynomial.C : Y.residueField y.point →+* (Y.residueField y.point)[T;T⁻¹])) ≫
          Y.fromSpecResidueField y.point)
        (originalNativeLaurentGaussPoint y.residueVal r hr) = y := by
  rw [SchemeValuedPoint.map_comp, originalNativeLaurentGaussPoint_map_C,
    originalNativeResiduePoint_map]

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
