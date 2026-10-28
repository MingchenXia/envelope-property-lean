/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumDiscBranches
import EnvelopeProperty.Berkovich.TranslatedFibreDiscs
import EnvelopeProperty.Berkovich.LineGaussPaths
import Mathlib.Data.Finset.Lattice.Fold

open scoped Polynomial NNReal Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
section GeneralTranslation
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {v : Valuation R ℝ≥0}

/-- Actual translation retains the precise value of EVERY original linear polynomial. -/
theorem polynomialTranslation_val_X_sub_C_eq (a b : A) (x : RelativeSpectrum v A[X]) :
    (polynomialTranslation a x).1.val (X - C b) = x.1.val (X - C (b-a)) := by
  rw [← val_apply, polynomialTranslation_val_apply]
  congr 1
  simp [Polynomial.algEquivAevalXAddC]
  ring
end GeneralTranslation

section AlgebraicallyClosed
variable {K : Type*} [Field K] [IsAlgClosed K] (v : Valuation K ℝ≥0)

/-- A genuine finite root minimum and the original branch cover derive either a WHOLE Gauss point
or an actual open strict-disc neighborhood on which EVERY original finite linear value is constant. -/
theorem exists_gauss_or_strictDisc_constant_linearValues (S : Finset K) (hS : S.Nonempty)
    (x : RelativeSpectrum v K[X]) (hpos : ∀ b ∈ S, 0 < x.1.val (X - C b)) :
    (∃ a ∈ S, ∃ t : ℝ≥0, 0 < t ∧ x = centeredGauss (self v) a t) ∨
      ∃ (c : K) (t : ℝ≥0), 0 < t ∧
        IsOpen {y : RelativeSpectrum v K[X] | y.1.val (X-C c) < t} ∧
        x.1.val (X-C c) < t ∧
        ∀ y : RelativeSpectrum v K[X], y.1.val (X-C c) < t →
          ∀ b ∈ S, y.1.val (X-C b) = x.1.val (X-C b) := by
  classical
  obtain ⟨a, ha, hmin⟩ := Finset.exists_mem_eq_inf' hS (fun b => x.1.val (X-C b))
  let t := x.1.val (X-C a)
  have ht : 0 < t := hpos a ha
  have htmin (b : K) (hb : b ∈ S) : t ≤ x.1.val (X-C b) := by
    calc
      t = S.inf' hS (fun c => x.1.val (X-C c)) := hmin.symm
      _ ≤ _ := Finset.inf'_le (fun c => x.1.val (X-C c)) hb
  let u := (polynomialTranslation (v := v) a).symm x
  have hu : polynomialTranslation a u = x := (polynomialTranslation a).apply_symm_apply x
  have hcoord : u.1.val X = t := by
    change ((polynomialTranslation a).symm x).1.val X = t
    rw [polynomialTranslation_symm_apply]
    simpa only [map_zero, sub_zero, zero_sub, neg_neg] using
      polynomialTranslation_val_X_sub_C_eq (v := v) (-a) 0 x
  let udisc : CoordinateDisc (A := K) v t := ⟨u, hcoord.le⟩
  by_cases hgauss : udisc = discGaussPoint v t
  · left
    refine ⟨a, ha, t, ht, ?_⟩
    have hg : u = gauss (self v) t := congrArg Subtype.val hgauss
    calc
      x = polynomialTranslation a u := hu.symm
      _ = polynomialTranslation a (gauss (self v) t) := congrArg (polynomialTranslation a) hg
      _ = centeredGauss (self v) a t := rfl
  · obtain ⟨c, _, hc⟩ := exists_mem_discBranch_of_ne_gauss (w := v) t udisc hgauss
    change u.1.val (X-C c) < t at hc
    let center := a+c
    have hxcenter : x.1.val (X-C center) < t := by
      have he := polynomialTranslation_val_X_sub_C_eq (v := v) a center u
      have he' : (polynomialTranslation a u).1.val (X-C center) = u.1.val (X-C c) := by
        simpa only [center, add_sub_cancel_left] using he
      rw [hu] at he'
      exact he'.trans_lt hc
    have hpoly (b : K) : (X-C b : K[X]) = (X-C center) - C (b-center) := by
      simp only [map_sub]
      ring
    have hsep (b : K) (hb : b ∈ S) : t ≤ v (b-center) := by
      by_contra h
      have hbv : v (b-center) < t := lt_of_not_ge h
      have hC : x.1.val (C (b-center)) = v (b-center) := x.2 (b-center)
      have hbad : x.1.val (X-C b) < t := by
        rw [hpoly]
        apply (x.1.val.map_sub _ _).trans_lt
        rw [hC]
        exact max_lt hxcenter hbv
      exact (not_lt_of_ge (htmin b hb)) hbad
    have hconstant (y : RelativeSpectrum v K[X]) (hy : y.1.val (X-C center) < t)
        (b : K) (hb : b ∈ S) : y.1.val (X-C b) = v (b-center) := by
      have hC : y.1.val (C (b-center)) = v (b-center) := y.2 (b-center)
      have hlt : y.1.val (X-C center) < y.1.val (C (b-center)) := by
        rw [hC]
        exact hy.trans_le (hsep b hb)
      rw [hpoly, y.1.val.map_sub_eq_of_lt_right hlt, hC]
    right
    refine ⟨center, t, ht, ?_, hxcenter, ?_⟩
    · exact isOpen_lt ((Spectrum.continuous_val_apply _).comp continuous_subtype_val) continuous_const
    · intro y hy b hb
      exact (hconstant y hy b hb).trans (hconstant x hxcenter b hb).symm
end AlgebraicallyClosed
end EnvelopeProperty.Berkovich.RelativeSpectrum
