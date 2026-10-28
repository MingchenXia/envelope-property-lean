/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumPolynomialGauss
import EnvelopeProperty.Berkovich.SpectrumFibre
import EnvelopeProperty.Berkovich.SpectrumBaseChange

/-!
# Actual scalar lifts to the original completed Gauss field

Gauss naturality gives an actual coefficient-preserving isometric embedding
of the original completed Gauss field into the completed field of the Gauss
point above every original point. Their genuine tensor evaluator constructs
actual scalar lifts preserving every whole original algebra value.
-/

open scoped Classical NNReal TensorProduct Polynomial
open Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (v : Valuation R ℝ≥0) (r : ℝ≥0)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual prescribed-coefficient Gauss point of the original base line. -/
def fcGaussBasePoint : RelativeSpectrum v R[X] := gauss (self v) r

/-- The original completed residue field of that actual Gauss point. -/
abbrev fcGaussField := H (fcGaussBasePoint v r)

instance fcGaussFieldAlgebra : Algebra R (fcGaussField v r) := inferInstance

/-- The true Gauss completed coefficient field retains every prescribed base value. -/
theorem fcGaussField_val_algebraMap (c : R) :
    NormedField.valuation (K := fcGaussField v r) (algebraMap R (fcGaussField v r) c) = v c :=
  nnnorm_algebraMap_H (fcGaussBasePoint v r) c

/-- Whole Gauss naturality preserves the actual original coefficient seminorm. -/
theorem fc_gauss_comap_base (x : RelativeSpectrum v A) :
    comap (Polynomial.mapAlgHom (Algebra.ofId R A)) (gauss x r) = fcGaussBasePoint v r := by
  apply Subtype.ext
  change Spectrum.comap (Polynomial.mapRingHom (algebraMap R A)) (Spectrum.gauss x.1 r) =
    Spectrum.gauss (Spectrum.ofValuation v) r
  rw [Spectrum.gauss_comap]
  exact congrArg (fun y => Spectrum.gauss y r) (Spectrum.ext_val x.2)

/-- A genuine coefficient-preserving embedding of the entire completed Gauss
field into the completed Gauss field of the original point. -/
def fcGaussScalarCoefficient (x : RelativeSpectrum v A) :
    fcGaussField v r →ₐ[R] H (gauss x r) :=
  H.map (Polynomial.mapAlgHom (Algebra.ofId R A)) (fc_gauss_comap_base v r x)

/-- The entire actual Gauss coefficient embedding is isometric. -/
theorem fcGaussScalarCoefficient_norm (x : RelativeSpectrum v A) (c : fcGaussField v r) :
    ‖fcGaussScalarCoefficient v r x c‖ = ‖c‖ :=
  H.norm_map _ (fc_gauss_comap_base v r x) c

/-- The genuine original-algebra evaluation into the Gauss completed field. -/
def fcGaussOriginalEvaluation (x : RelativeSpectrum v A) : A →ₐ[R] H (gauss x r) where
  __ := (Spectrum.toH (gauss x r).1).comp Polynomial.C
  commutes' _ := rfl

/-- The actual tensor evaluation combines the full Gauss coefficient field
with the entire original algebra, using their genuine original coefficient action. -/
def fcGaussScalarEval (x : RelativeSpectrum v A) : fcGaussField v r ⊗[R] A →+* H (gauss x r) :=
  (Algebra.TensorProduct.productMap (fcGaussScalarCoefficient v r x)
    (fcGaussOriginalEvaluation v r x)).toRingHom

/-- Every original tensor has its exact entire coefficient/evaluation product. -/
theorem fcGaussScalarEval_tmul (x : RelativeSpectrum v A) (c : fcGaussField v r) (a : A) :
    fcGaussScalarEval v r x (c ⊗ₜ[R] a) =
      fcGaussScalarCoefficient v r x c * Spectrum.toH (gauss x r).1 (Polynomial.C a) := rfl

/-- Pullback of the genuine completed Gauss norm constructs the actual lifted point. -/
def fcGaussScalarLift (x : RelativeSpectrum v A) :
    RelativeSpectrum (NormedField.valuation (K := fcGaussField v r)) (fcGaussField v r ⊗[R] A) :=
  ⟨Spectrum.ofValuation ((NormedField.valuation (K := H (gauss x r))).comap (fcGaussScalarEval v r x)), by
    intro c
    change ‖fcGaussScalarEval v r x (c ⊗ₜ[R] (1 : A))‖₊ = ‖c‖₊
    rw [fcGaussScalarEval_tmul, map_one, map_one, mul_one]
    exact NNReal.eq (fcGaussScalarCoefficient_norm v r x c)⟩

/-- The whole original point is recovered by the actual scalar restriction. -/
theorem fcGaussScalarLift_baseChangeRestriction (x : RelativeSpectrum v A) :
    baseChangeRestriction (fcGaussField_val_algebraMap v r) (fcGaussScalarLift v r x) = x := by
  apply Subtype.ext
  apply Spectrum.ext_val
  intro a
  change ‖fcGaussScalarEval v r x ((1 : fcGaussField v r) ⊗ₜ[R] a)‖₊ = x.1.val a
  rw [fcGaussScalarEval_tmul, map_one, one_mul, Spectrum.nnnorm_toH]
  exact Spectrum.gauss_val_C x.1 r a

/-- Scalar restriction from the actual original completed Gauss field is
surjective on all original algebra points, without a field or positive-radius
assumption. The point and entire evaluation map are constructed. -/
theorem fc_baseChangeRestriction_gauss_surjective :
    Function.Surjective (baseChangeRestriction (A := A) (fcGaussField_val_algebraMap v r)) :=
  fun x => ⟨fcGaussScalarLift v r x, fcGaussScalarLift_baseChangeRestriction v r x⟩

end EnvelopeProperty.Berkovich.RelativeSpectrum
