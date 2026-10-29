/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.IdealRepresentationFinite
import EnvelopeProperty.Projective.NativeModelIdeals

/-!
# Actual arbitrary projective ideal sheaves and their whole homogeneous model functions

The homogeneous ideal is genuinely constructed from the original ideal sheaf,
not supplied as a representation hypothesis. Actual coordinate finite generation
and bounded model coefficients give global intrinsic norm and logarithm
continuity, including non-Noetherian coefficient rings. No locally Noetherian
assumption or analytic coherent-sheaf identification is asserted.
-/

open scoped Classical Polynomial NNReal ENNReal Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
variable {R : Type u} [CommRing R] (v : Valuation R ℝ≥0) {n : ℕ}
private local instance representationProjectiveProper :
    IsProper (ProjBerk.nativeStructureMap (R := R) (n := n)) := ProjBerk.nativeStructureMap_isProper

set_option backward.isDefEq.respectTransparency false in
/-- Every actual projective ideal-sheaf model norm is the whole norm of its genuinely constructed original homogeneous ideal. -/
theorem modelIdealNorm_eq_homogeneousRepresentative (hb : ∀ r, v r ≤ 1)
    (I : (ProjBerk.NativeProjectiveScheme R n).IdealSheafData)
    (x : RelativeNormalizedProjectiveSpectrum v n) :
    RelativeSchemeValuedPoint.modelIdealNorm I hb (nativeHomeomorph v x) =
      Spectrum.idealNorm (ProjBerk.nativeHomogeneousRepresentative I).toIdeal x.1.1 := by
  have h := modelIdealNorm_quotient_eq_idealNorm v hb (ProjBerk.nativeHomogeneousRepresentative I) x
  change RelativeSchemeValuedPoint.modelIdealNorm
    (f := ProjBerk.nativeStructureMap (R := R) (n := n))
    (GradedQuotient.quotientIdealSheaf (ProjBerk.ProjectiveGrading R n)
      (ProjBerk.nativeHomogeneousRepresentative I)) hb (nativeHomeomorph v x) = _ at h
  rwa [ProjBerk.nativeHomogeneousRepresentative_quotientIdealSheaf] at h

/-- Every actual projective ideal-sheaf logarithm is the whole logarithm of its genuinely constructed original homogeneous ideal. -/
theorem modelIdealLog_eq_homogeneousRepresentative (hb : ∀ r, v r ≤ 1)
    (I : (ProjBerk.NativeProjectiveScheme R n).IdealSheafData)
    (x : RelativeNormalizedProjectiveSpectrum v n) :
    RelativeSchemeValuedPoint.modelIdealLog I hb (nativeHomeomorph v x) =
      Spectrum.idealLog (ProjBerk.nativeHomogeneousRepresentative I).toIdeal x.1.1 :=
  congrArg ENNReal.log (modelIdealNorm_eq_homogeneousRepresentative v hb I x)


set_option backward.isDefEq.respectTransparency false in
/-- Actual chart finite generation yields continuity of the entire proper-center ideal norm over any bounded coefficient ring. -/
theorem continuous_modelIdealNorm_of_coordinate_fg (hb : ∀ r, v r ≤ 1)
    (I : (ProjBerk.NativeProjectiveScheme R n).IdealSheafData)
    (hfg : ∀ j : Fin (n + 1), (ProjBerk.nativeCoordinateIdeal I j).FG) :
    Continuous (RelativeSchemeValuedPoint.modelIdealNorm I hb :
      RelativeSchemeValuedPoint v (ProjBerk.nativeStructureMap (R := R) (n := n)) → ℝ≥0∞) := by
  obtain ⟨J, s, _hs, hspan, hJ⟩ :=
    ProjBerk.exists_finite_homogeneous_generators_quotientIdealSheaf_of_coordinate_fg I hfg
  have hcont : Continuous fun x : RelativeNormalizedProjectiveSpectrum v n =>
      ((s.sup fun F => x.1.1.val F : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.continuous_coe.comp (Continuous.finset_sup_apply fun F _ =>
      (Spectrum.continuous_val_apply F).comp
        (continuous_subtype_val.comp continuous_subtype_val))
  have he (x : RelativeNormalizedProjectiveSpectrum v n) :
      RelativeSchemeValuedPoint.modelIdealNorm I hb (nativeHomeomorph v x) =
        ((s.sup fun F => x.1.1.val F : ℝ≥0) : ℝ≥0∞) := by
    have h := modelIdealNorm_quotient_eq_idealNorm v hb J x
    change RelativeSchemeValuedPoint.modelIdealNorm
      (f := ProjBerk.nativeStructureMap (R := R) (n := n))
      (GradedQuotient.quotientIdealSheaf (ProjBerk.ProjectiveGrading R n) J)
        hb (nativeHomeomorph v x) = _ at h
    rw [hJ] at h
    rw [h, ← hspan, Spectrum.idealNorm_span_finset (isBounded_polynomial v hb x)]
  have hc : Continuous fun x : RelativeNormalizedProjectiveSpectrum v n =>
      RelativeSchemeValuedPoint.modelIdealNorm I hb (nativeHomeomorph v x) :=
    hcont.congr fun x => (he x).symm
  convert hc.comp (nativeHomeomorph v).symm.continuous using 1
  ext y
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply]

/-- Actual chart finite generation yields global true-center logarithmic continuity over any bounded coefficient ring, including negative infinity. -/
theorem continuous_modelIdealLog_of_coordinate_fg (hb : ∀ r, v r ≤ 1)
    (I : (ProjBerk.NativeProjectiveScheme R n).IdealSheafData)
    (hfg : ∀ j : Fin (n + 1), (ProjBerk.nativeCoordinateIdeal I j).FG) :
    Continuous (RelativeSchemeValuedPoint.modelIdealLog I hb :
      RelativeSchemeValuedPoint v (ProjBerk.nativeStructureMap (R := R) (n := n)) → EReal) :=
  ENNReal.continuous_log.comp (continuous_modelIdealNorm_of_coordinate_fg v hb I hfg)

end EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
