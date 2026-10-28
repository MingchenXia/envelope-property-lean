/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.ConnectedPathNonisolated
import EnvelopeProperty.Berkovich.LineGaussPaths
import Mathlib.Topology.Instances.NNReal.Lemmas

open scoped Polynomial NNReal Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {R : Type*} [CommRing R] {v : Valuation R ℝ≥0}

/-- The actual centered Gauss seminorm on the original polynomial coefficient ring, restricted to the genuine new polynomial variable. -/
def lineGaussInflation (x : RelativeSpectrum v R[X]) (r : ℝ≥0) :
    RelativeSpectrum v R[X] :=
  comap (Polynomial.mapAlgHom (Algebra.ofId R R[X])) (centeredGauss x (X : R[X]) r)

/-- EVERY original polynomial is evaluated by the genuine whole translated Gauss polynomial, with its original coefficient images. -/
theorem lineGaussInflation_val_apply (x : RelativeSpectrum v R[X]) (r : ℝ≥0) (p : R[X]) :
    val (lineGaussInflation x r) p =
      val (gauss x r) (Polynomial.algEquivAevalXAddC (X : R[X])
        (p.map (Polynomial.C : R →+* R[X]))) := rfl

/-- The whole original line inflation is continuous in its actual radius, including zero. -/
@[fun_prop]
theorem continuous_lineGaussInflation (x : RelativeSpectrum v R[X]) :
    Continuous (lineGaussInflation x) :=
  (continuous_comap _).comp (continuous_centeredGauss x (X : R[X]))

/-- Radius zero recovers the ENTIRE original point by the identity on every original polynomial. -/
theorem lineGaussInflation_zero (x : RelativeSpectrum v R[X]) : lineGaussInflation x 0 = x := by
  rw [lineGaussInflation, centeredGauss_zero, ← comap_comp]
  have he : ((Polynomial.aeval (X : R[X])).restrictScalars R).comp
      (Polynomial.mapAlgHom (Algebra.ofId R R[X])) = AlgHom.id R R[X] := by
    ext
    simp
  rw [he, comap_id]

/-- The actual translated variable has leading coefficient one, so its whole value bounds the original radius below. -/
theorem radius_le_lineGaussInflation_val_X (x : RelativeSpectrum v R[X]) (r : ℝ≥0) :
    r ≤ val (lineGaussInflation x r) (X : R[X]) := by
  rw [lineGaussInflation_val_apply]
  have he : Polynomial.algEquivAevalXAddC (X : R[X])
      ((X : R[X]).map (Polynomial.C : R →+* R[X])) =
      (X : R[X][X]) + C (X : R[X]) := by
    simp [Polynomial.algEquivAevalXAddC]
  rw [he]
  simpa using Spectrum.le_gauss_val x.1 r ((X : R[X][X]) + C (X : R[X])) 1

/-- Every actual prescribed line point is nonisolated, by a genuine nonconstant connected Gauss inflation, with no field or support hypothesis. -/
theorem not_isOpen_singleton_line (x : RelativeSpectrum v R[X]) :
    ¬ IsOpen ({x} : Set (RelativeSpectrum v R[X])) := by
  have hne : lineGaussInflation x (val x X + 1) ≠ lineGaussInflation x 0 := by
    intro he
    have h := radius_le_lineGaussInflation_val_X x (val x X + 1)
    rw [he, lineGaussInflation_zero] at h
    exact not_le_of_gt (lt_add_one (val x X)) h
  have hn := EnvelopeProperty.not_isOpen_singleton_of_continuous_connected
    (continuous_lineGaussInflation x) 0 (val x X + 1) hne
  simpa only [lineGaussInflation_zero] using hn

/-- Every actual prescribed line point has a nontrivial punctured neighborhood filter over any commutative ring. -/
theorem neBot_nhdsNE_line (x : RelativeSpectrum v R[X]) : Filter.NeBot (𝓝[≠] x) := by
  constructor
  intro h
  exact not_isOpen_singleton_line x ((isOpen_singleton_iff_punctured_nhds _).mpr h)

end EnvelopeProperty.Berkovich.RelativeSpectrum
