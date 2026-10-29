/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumLineInflation

open scoped Polynomial NNReal Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {v : Valuation R ℝ≥0}

private theorem translated_gauss_le (y : RelativeSpectrum v A) (a : A) (r : ℝ≥0)
    (ha : val y a ≤ r) (p : A[X]) :
    val (centeredGauss y a r) p ≤ val (gauss y r) p := by
  apply val_le_gauss_val (y := y)
  · apply ext_val
    intro c
    simp [centeredGauss_val_apply, Polynomial.algEquivAevalXAddC]
  · rw [centeredGauss_val_apply]
    have h : Polynomial.algEquivAevalXAddC a X = X + C a := by
      simp [Polynomial.algEquivAevalXAddC]
    rw [h]
    exact (val (gauss y r)).map_add _ _ |>.trans (by simpa using ha)

/-- Translation by a point inside the original Gauss disc fixes the WHOLE Gauss seminorm. -/
theorem centeredGauss_eq_gauss_of_val_le (y : RelativeSpectrum v A) (a : A) (r : ℝ≥0)
    (ha : val y a ≤ r) : centeredGauss y a r = gauss y r := by
  apply ext_val
  intro p
  apply le_antisymm (translated_gauss_le y a r ha p)
  let e := Polynomial.algEquivAevalXAddC a
  let z : RelativeSpectrum v A[X] := comap (e.symm.toAlgHom.restrictScalars R) (gauss y r)
  have hz : proj z = y := by
    apply ext_val
    intro c
    change val (gauss y r) (e.symm (C c)) = val y c
    have hc : e.symm (C c) = C c := e.symm.commutes c
    rw [hc, gauss_val_C]
  have hx : val z X ≤ r := by
    change val (gauss y r) (e.symm X) ≤ r
    have he : e.symm X = X - C a := by
      apply e.injective
      simp [e, Polynomial.algEquivAevalXAddC]
    rw [he]
    exact (val (gauss y r)).map_sub _ _ |>.trans (by simpa using ha)
  have hb := val_le_gauss_val hz hx (e p)
  change val (gauss y r) (e.symm (e p)) ≤ val (gauss y r) (e p) at hb
  rw [e.symm_apply_apply] at hb
  exact hb

/-- Whole translated Gauss inflation on an original polynomial algebra over any coefficient algebra. -/
def polynomialGaussInflation (x : RelativeSpectrum v A[X]) (r : ℝ≥0) :
    RelativeSpectrum v A[X] :=
  comap ((Polynomial.mapAlgHom (Algebra.ofId A A[X])).restrictScalars R)
    (centeredGauss x (X : A[X]) r)

/-- Inflation evaluates every original polynomial by the genuine translated Gauss polynomial. -/
theorem polynomialGaussInflation_val_apply (x : RelativeSpectrum v A[X]) (r : ℝ≥0)
    (p : A[X]) : val (polynomialGaussInflation x r) p =
      val (gauss x r) (Polynomial.algEquivAevalXAddC (X : A[X])
        (p.map (Polynomial.C : A →+* A[X]))) := rfl

/-- The whole original polynomial inflation depends jointly continuously on its point and radius. -/
@[fun_prop]
theorem continuous_polynomialGaussInflation_prod :
    Continuous fun p : RelativeSpectrum v A[X] × ℝ≥0 => polynomialGaussInflation p.1 p.2 :=
  (continuous_comap _).comp (continuous_centeredGauss_prod (X : A[X]))

/-- Radius zero recovers the entire original point, with all coefficient values. -/
@[simp]
theorem polynomialGaussInflation_zero (x : RelativeSpectrum v A[X]) :
    polynomialGaussInflation x 0 = x := by
  apply ext_val
  intro p
  change val (centeredGauss x (X : A[X]) 0)
    (p.map (Polynomial.C : A →+* A[X])) = val x p
  rw [centeredGauss_zero, comap_val_apply]
  congr 1
  change (p.map (Polynomial.C : A →+* A[X])).eval X = p
  rw [Polynomial.eval_map]
  simp

/-- Every original coefficient value is retained by the entire inflation. -/
@[simp]
theorem proj_polynomialGaussInflation (x : RelativeSpectrum v A[X]) (r : ℝ≥0) :
    proj (polynomialGaussInflation x r) = proj x := by
  apply ext_val
  intro c
  simp [polynomialGaussInflation_val_apply, Polynomial.algEquivAevalXAddC]

/-- The exact original coordinate value is the maximum of its original value and inflation radius. -/
theorem polynomialGaussInflation_val_X (x : RelativeSpectrum v A[X]) (r : ℝ≥0) :
    val (polynomialGaussInflation x r) X = max (val x X) r := by
  rw [polynomialGaussInflation_val_apply]
  have he : Polynomial.algEquivAevalXAddC (X : A[X])
      ((X : A[X]).map (Polynomial.C : A →+* A[X])) = X + C (X : A[X]) := by
    simp [Polynomial.algEquivAevalXAddC]
  rw [he]
  apply le_antisymm
  · exact (val (gauss x r)).map_add _ _ |>.trans (by simp [max_comm])
  · apply max_le
    · simpa using Spectrum.le_gauss_val x.1 r ((X : A[X][X]) + C (X : A[X])) 0
    · simpa using Spectrum.le_gauss_val x.1 r ((X : A[X][X]) + C (X : A[X])) 1

/-- Every whole original polynomial value increases along actual inflation. -/
theorem val_le_polynomialGaussInflation (x : RelativeSpectrum v A[X]) (r : ℝ≥0)
    (p : A[X]) : val x p ≤ val (polynomialGaussInflation x r) p := by
  have h := eval_val_le_centeredGauss x (X : A[X]) r
    (p.map (Polynomial.C : A →+* A[X]))
  have he : (p.map (Polynomial.C : A →+* A[X])).eval X = p := by
    rw [Polynomial.eval_map]
    simp
  rw [he] at h
  exact h

/-- When inflation reaches the original coordinate radius, it is the entire original Gauss point. -/
theorem polynomialGaussInflation_eq_gauss (x : RelativeSpectrum v A[X]) (r : ℝ≥0)
    (hx : val x X ≤ r) : polynomialGaussInflation x r = gauss (proj x) r := by
  apply ext_val
  intro p
  change val (centeredGauss x (X : A[X]) r)
    (p.map (Polynomial.C : A →+* A[X])) = val (gauss (proj x) r) p
  rw [centeredGauss_eq_gauss_of_val_le x X r hx]
  rw [gauss_val_apply, gauss_val_apply,
    Polynomial.support_map_of_injective p Polynomial.C_injective]
  apply Finset.sup_congr rfl
  intro i _
  rw [Polynomial.coeff_map]
  rfl

/-- Inflating an original Gauss point by a smaller radius fixes every original polynomial value. -/
theorem polynomialGaussInflation_gauss (y : RelativeSpectrum v A) (t s : ℝ≥0)
    (hst : s ≤ t) : polynomialGaussInflation (gauss y t) s = gauss y t := by
  apply ext_val
  intro p
  apply le_antisymm
  · apply val_le_gauss_val (y := y)
    · simp
    · rw [polynomialGaussInflation_val_X, gauss_val_X, max_eq_left hst]
  · exact val_le_polynomialGaussInflation (gauss y t) s p

end EnvelopeProperty.Berkovich.RelativeSpectrum
