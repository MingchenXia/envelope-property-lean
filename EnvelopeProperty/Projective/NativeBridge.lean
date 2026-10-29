/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeComparison
import EnvelopeProperty.Projective.NormalizedSpectrum
import EnvelopeProperty.Projective.Charts
import EnvelopeProperty.Projective.Support

/-!
# The existing paper model and the actual native projective scheme

The old normalized graded `ProjBerk` interface over a trivially valued field is
canonically the arbitrary-base normalized projective spectrum over its trivial
coefficient seminorm. Its entire polynomial valuation and every affine ratio chart
are preserved. Composing with the actual native comparison identifies the old
point space and topology with native valued points of the genuine polynomial Proj
scheme, retaining its prime support and every actual chart polynomial section.

The native point uses the genuine degree-zero projective stalk residue field.
It does not identify that field with the affine-cone residue field. An analytic
structure sheaf and coherent sheaf model-ideal identification remain separate.
-/

open scoped Classical NNReal ENNReal Topology
open Topology EnvelopeProperty.Berkovich
noncomputable section
namespace EnvelopeProperty.ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type*} [Field k] {n : ℕ}

/-- The existing paper projective model is exactly the general normalized spectrum over the trivial base valuation. -/
def normalizedSpectrumHomeomorph : ProjBerk k n ≃ₜ
    RelativeNormalizedProjectiveSpectrum (1 : Valuation k ℝ≥0) n :=
  (Berk.relativeSpectrumHomeomorph.subtype (fun _ => Iff.rfl)).trans
    (RelativeNormalizedProjectiveSpectrum.coefficientHomeomorph (1 : Valuation k ℝ≥0)).symm

/-- The entire original polynomial valuation is preserved. -/
@[simp]
theorem normalizedSpectrumHomeomorph_val (x : ProjBerk k n) :
    (normalizedSpectrumHomeomorph x).1.1.val = x.1.val := rfl

/-- Every original polynomial value is preserved. -/
@[simp]
theorem normalizedSpectrumHomeomorph_val_apply (x : ProjBerk k n)
    (F : MvPolynomial (Fin (n + 1)) k) :
    (normalizedSpectrumHomeomorph x).1.1.val F = x.1.val F := rfl

/-- The genuine coordinate open is retained exactly. -/
@[simp]
theorem normalizedSpectrumHomeomorph_mem_chartOpen (x : ProjBerk k n) (j : Fin (n + 1)) :
    normalizedSpectrumHomeomorph x ∈
      RelativeNormalizedProjectiveSpectrum.chartOpen (1 : Valuation k ℝ≥0) j ↔ x ∈ chartOpen j := Iff.rfl

/-- The whole projective specialization restricts to each genuine coordinate open. -/
def normalizedSpectrumChartHomeomorph (j : Fin (n + 1)) : chartOpen (k := k) j ≃ₜ
    RelativeNormalizedProjectiveSpectrum.chartOpen (1 : Valuation k ℝ≥0) j :=
  normalizedSpectrumHomeomorph.subtype (fun _ => Iff.rfl)

/-- The entire affine ratio seminorm commutes with the genuine trivial-field specialization. -/
theorem normalizedSpectrumHomeomorph_coordinateChartMap (j : Fin (n + 1))
    (x : chartOpen (k := k) j) :
    RelativeNormalizedProjectiveSpectrum.coordinateChartHomeomorph (1 : Valuation k ℝ≥0) j
      (normalizedSpectrumChartHomeomorph j x) =
        Berk.relativeSpectrumHomeomorph (coordinateChartMap j x) := by
  apply Subtype.ext
  apply Spectrum.ext_val
  intro a
  rfl

/-- The existing paper model is genuinely the native valued-point space of actual polynomial Proj over the trivial field base. -/
def nativeHomeomorph : ProjBerk k n ≃ₜ
    RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) (nativeStructureMap (R := k) (n := n)) :=
  normalizedSpectrumHomeomorph.trans
    (RelativeNormalizedProjectiveSpectrum.nativeHomeomorph (1 : Valuation k ℝ≥0))

/-- The native map is the canonical genuine projective stalk-residue point construction. -/
@[simp]
theorem nativeHomeomorph_apply (x : ProjBerk k n) :
    nativeHomeomorph x = RelativeNormalizedProjectiveSpectrum.nativePoint
      (1 : Valuation k ℝ≥0) (normalizedSpectrumHomeomorph x) := rfl

/-- The actual native homogeneous prime support is the original whole polynomial valuation kernel. -/
@[simp]
theorem nativeHomeomorph_support_toIdeal (x : ProjBerk k n) :
    (nativeHomeomorph x).1.point.asHomogeneousIdeal.toIdeal = x.1.val.supp := rfl

/-- The actual native scheme point agrees with the existing paper homogeneous prime support. -/
@[simp]
theorem nativeHomeomorph_point (x : ProjBerk k n) :
    (nativeHomeomorph x).1.point = support x := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  rfl

/-- Every entire native coordinate chart agrees with the existing paper affine ratio seminorm. -/
theorem nativeHomeomorph_chart (j : Fin (n + 1)) (x : chartOpen (k := k) j) :
    nativeCoordinateSpectrumHomeomorph (1 : Valuation k ℝ≥0) j
      ⟨nativeHomeomorph x.1, x.2⟩ =
        Berk.relativeSpectrumHomeomorph (coordinateChartMap j x) := by
  calc
    nativeCoordinateSpectrumHomeomorph (1 : Valuation k ℝ≥0) j
      ⟨nativeHomeomorph x.1, x.2⟩ =
        RelativeNormalizedProjectiveSpectrum.coordinateChartHomeomorph (1 : Valuation k ℝ≥0) j
          (normalizedSpectrumChartHomeomorph j x) :=
      RelativeNormalizedProjectiveSpectrum.nativeHomeomorph_chart
        (1 : Valuation k ℝ≥0) j (normalizedSpectrumChartHomeomorph j x)
    _ = _ := normalizedSpectrumHomeomorph_coordinateChartMap j x

/-- Every actual polynomial section of a coordinate chart retains the existing paper chart value. -/
theorem nativeHomeomorph_val_apply (j : Fin (n + 1)) (x : chartOpen (k := k) j)
    (a : CoordinateRing k j) :
    SchemeValuedPoint.eval (nativeHomeomorph x.1).1 (nativeCoordinateOpen j) x.2
      ((nativeCoordinateSectionsIso j).hom a) = (coordinateChartMap j x).val a := by
  exact RelativeNormalizedProjectiveSpectrum.nativeHomeomorph_val_apply _ j
    (normalizedSpectrumChartHomeomorph j x) a

/-- The actual native homogeneous section has the original normalized form value whenever its chart coordinate has value one. -/
theorem nativeHomeomorph_eval_form_of_val_X_eq_one (x : ProjBerk k n) (j : Fin (n + 1))
    (hj : x.1.val (MvPolynomial.X j) = 1) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) k) (hF : F ∈ ProjectiveGrading k n (d • (1 : ℕ))) :
    SchemeValuedPoint.eval (nativeHomeomorph x).1 (nativeCoordinateOpen j)
      (show (nativeHomeomorph x).1.point ∈ nativeCoordinateOpen j from by
        change x.1.val (MvPolynomial.X j) ≠ 0
        rw [hj]
        exact one_ne_zero)
      ((nativeHomogeneousChartSectionsIso j).hom
        (HomogeneousLocalization.Away.mk (ProjectiveGrading k n)
          (MvPolynomial.isHomogeneous_X k j) d F hF)) = x.1.val F :=
  RelativeNormalizedProjectiveSpectrum.nativeHomeomorph_eval_form_of_val_X_eq_one _
    (normalizedSpectrumHomeomorph x) j hj d F hF

/-- The existing logarithmic form function is the actual native section logarithm in every value-one coordinate chart. -/
theorem nativeHomeomorph_log_form_of_val_X_eq_one (x : ProjBerk k n) (j : Fin (n + 1))
    (hj : x.1.val (MvPolynomial.X j) = 1) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) k) (hF : F ∈ ProjectiveGrading k n (d • (1 : ℕ))) :
    ENNReal.log (SchemeValuedPoint.eval (nativeHomeomorph x).1 (nativeCoordinateOpen j)
      (show (nativeHomeomorph x).1.point ∈ nativeCoordinateOpen j from by
        change x.1.val (MvPolynomial.X j) ≠ 0
        rw [hj]
        exact one_ne_zero)
      ((nativeHomogeneousChartSectionsIso j).hom
        (HomogeneousLocalization.Away.mk (ProjectiveGrading k n)
          (MvPolynomial.isHomogeneous_X k j) d F hF)) : ℝ≥0∞) = logAbs F x :=
  congrArg (fun a : ℝ≥0 => ENNReal.log (a : ℝ≥0∞))
    (nativeHomeomorph_eval_form_of_val_X_eq_one x j hj d F hF)

end EnvelopeProperty.ProjBerk
