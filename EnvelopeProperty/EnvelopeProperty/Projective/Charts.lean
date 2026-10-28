/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Basic
import EnvelopeProperty.Projective.ChartAlgebra
import EnvelopeProperty.Projective.ChartLocalization
import EnvelopeProperty.Berkovich.Localization

/-!
# Affine coordinate charts of the normalized projective seminorm model

For a coordinate `j`, the open set where `|X_j| ≠ 0` maps to the affine seminorm space in
the variables `U_i`, `i ≠ j`, by evaluating the ratios `X_i / X_j` in the principal localization.
The forward map is continuous and has the expected coordinate values.

The coordinate rings and substitutions in this module are explicit. The normalized projective
model remains the one of `Projective.Basic`; no identification with an arbitrary scheme's
analytification or coherent sheaf gluing is assumed.
-/

open scoped NNReal ENNReal Topology Polynomial
open Set Topology

noncomputable section

namespace EnvelopeProperty.ProjBerk

variable {k : Type*} [Field k] {n : ℕ}

/-- The coordinate open where `X_j` does not vanish. -/
def chartOpen (j : Fin (n + 1)) : Set (ProjBerk k n) :=
  {v | v.1.val (MvPolynomial.X j) ≠ 0}

theorem isOpen_chartOpen (j : Fin (n + 1)) : IsOpen (chartOpen (k := k) j) :=
  (Berk.isOpen_setOf_val_ne_zero (MvPolynomial.X j)).preimage continuous_val

/-- The normalized coordinate opens cover the projective model. -/
theorem exists_mem_chartOpen (v : ProjBerk k n) : ∃ j, v ∈ chartOpen j := by
  obtain ⟨j, hj⟩ := exists_val_X_eq_one v
  exact ⟨j, by simp only [chartOpen, Set.mem_ofPred_eq, hj, ne_eq, one_ne_zero, not_false_eq_true]⟩

/-- The forward affine chart map, defined on the full localized seminorm, not just its
values on individual coordinates. -/
def coordinateChartMap (j : Fin (n + 1)) (v : chartOpen (k := k) j) : Berk k (CoordinateRing k j) :=
  Berk.comap (chartRatioHom j) (Berk.awayLift (MvPolynomial.X j) v.1.1 v.2)

@[fun_prop]
theorem continuous_coordinateChartMap (j : Fin (n + 1)) : Continuous (coordinateChartMap (k := k) j) := by
  have hc : Continuous fun v : chartOpen (k := k) j => v.1.1 :=
    continuous_val.comp continuous_subtype_val
  exact (Berk.continuous_comap (chartRatioHom j)).comp
    ((Berk.continuous_awayLift (MvPolynomial.X j)).comp (hc.subtype_mk fun v => v.2))

/-- Evaluation on an affine chart coordinate is the ratio of its homogeneous coordinates. -/
theorem coordinateChartMap_val_X (j : Fin (n + 1)) (v : chartOpen (k := k) j) (i : ChartIndex j) :
    (coordinateChartMap j v).val (MvPolynomial.X i) =
      v.1.1.val (MvPolynomial.X i.1) / v.1.1.val (MvPolynomial.X j) := by
  simp only [coordinateChartMap, Berk.comap_val_apply, chartRatioHom, MvPolynomial.aeval_X]
  simpa only [pow_one] using
    Berk.awayLift_val_mk' (MvPolynomial.X j) v.1.1 v.2 (MvPolynomial.X i.1) 1

/-! ### The normalized Gauss point associated to an affine point -/

/-- The finite coordinate bound that normalizes the inverse chart. -/
def chartBound (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) : ℝ≥0 :=
  max 1 (Finset.univ.sup fun i : ChartIndex j => y.val (MvPolynomial.X i))

theorem one_le_chartBound (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) :
    1 ≤ chartBound j y := le_max_left _ _

theorem chartBound_pos (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) :
    0 < chartBound j y := zero_lt_one.trans_le (one_le_chartBound j y)

/-- The positive Gauss radius, inverse to the maximum coordinate norm. -/
def chartRadius (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) : ℝ≥0 := (chartBound j y)⁻¹

theorem chartRadius_pos (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) :
    0 < chartRadius j y := inv_pos.2 (chartBound_pos j y)

@[fun_prop]
theorem continuous_chartBound (j : Fin (n + 1)) : Continuous (chartBound (k := k) j) :=
  continuous_const.max (Continuous.finset_sup_apply fun i _ => Berk.continuous_abs (MvPolynomial.X i))

@[fun_prop]
theorem continuous_chartRadius (j : Fin (n + 1)) : Continuous (chartRadius (k := k) j) :=
  (continuous_chartBound j).inv₀ fun y => (chartBound_pos j y).ne'

/-- Pull back the Gauss seminorm under homogeneous substitution, with normalized radius. -/
def rawChartPoint (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) :
    Berk k (MvPolynomial (Fin (n + 1)) k) :=
  Berk.comap (chartHomogenize j) (Berk.gauss y (chartRadius j y))

@[fun_prop]
theorem continuous_rawChartPoint (j : Fin (n + 1)) : Continuous (rawChartPoint (k := k) j) :=
  (Berk.continuous_comap (chartHomogenize j)).comp
    (Berk.continuous_gauss_prod.comp (continuous_id.prodMk (continuous_chartRadius j)))

theorem rawChartPoint_val_X (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) (i : Fin (n + 1)) :
    (rawChartPoint j y).val (MvPolynomial.X i) = y.val (coordinateDehomCoord j i) * chartRadius j y := by
  simp only [rawChartPoint, Berk.comap_val_apply, chartHomogenize, MvPolynomial.aeval_X,
    map_mul, Berk.gauss_val_C, Berk.gauss_val_X]

@[simp]
theorem rawChartPoint_val_X_self (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) :
    (rawChartPoint j y).val (MvPolynomial.X j) = chartRadius j y := by
  rw [rawChartPoint_val_X, coordinateDehomCoord_self, map_one, one_mul]

/-- The affine coordinate bound is the maximum of all dehomogenized homogeneous coordinates. -/
theorem chartBound_eq_sup_dehom (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) :
    chartBound j y = Finset.univ.sup fun i : Fin (n + 1) => y.val (coordinateDehomCoord j i) := by
  apply le_antisymm
  · refine max_le ?_ (Finset.sup_le fun i _ => ?_)
    · simpa only [coordinateDehomCoord_self, map_one] using
        Finset.le_sup (f := fun i : Fin (n + 1) => y.val (coordinateDehomCoord j i)) (Finset.mem_univ j)
    · simpa only [coordinateDehomCoord_ne] using
        Finset.le_sup (f := fun i : Fin (n + 1) => y.val (coordinateDehomCoord j i)) (Finset.mem_univ i.1)
  · refine Finset.sup_le fun i _ => ?_
    by_cases hi : i = j
    · subst i
      simpa only [coordinateDehomCoord_self, map_one] using one_le_chartBound j y
    · have hi' : y.val (MvPolynomial.X (⟨i, hi⟩ : ChartIndex j)) ≤
          (Finset.univ.sup fun i : ChartIndex j => y.val (MvPolynomial.X i)) :=
        Finset.le_sup (f := fun i : ChartIndex j => y.val (MvPolynomial.X i))
          (Finset.mem_univ (⟨i, hi⟩ : ChartIndex j))
      simpa only [coordinateDehomCoord, dif_neg hi, chartBound] using hi'.trans (le_max_right 1 _)

/-- The pulled-back Gauss point has normalized homogeneous coordinates. -/
theorem rawChartPoint_normalized (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) :
    Finset.univ.sup (fun i : Fin (n + 1) => (rawChartPoint j y).val (MvPolynomial.X i)) = 1 := by
  calc Finset.univ.sup (fun i : Fin (n + 1) => (rawChartPoint j y).val (MvPolynomial.X i))
      = Finset.univ.sup (fun i : Fin (n + 1) => y.val (coordinateDehomCoord j i) * chartRadius j y) :=
        Finset.sup_congr rfl fun i _ => rawChartPoint_val_X j y i
    _ = (Finset.univ.sup fun i : Fin (n + 1) => y.val (coordinateDehomCoord j i)) * chartRadius j y :=
      (Finset.apply_sup_eq_sup_comp_of_linearOrder (fun a : ℝ≥0 => a * chartRadius j y)
        (fun _ _ h => mul_le_mul' h le_rfl) (zero_mul _)).symm
    _ = 1 := by
      rw [← chartBound_eq_sup_dehom]
      exact mul_inv_cancel₀ (chartBound_pos j y).ne'

/-- Homogeneous substitution has no `T`-coefficient above the original total degree. -/
theorem chartHomogenize_support_subset (j : Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) k) :
    (chartHomogenize j F).support ⊆ Finset.range (F.totalDegree + 1) := by
  intro d hd
  apply Finset.mem_range.2
  by_contra! hddeg
  have hc : (chartHomogenize j F).coeff d = 0 := by
    rw [chartHomogenize_coeff,
      MvPolynomial.homogeneousComponent_eq_zero d F (by omega), map_zero]
  exact (Polynomial.mem_support_iff.1 hd) hc

/-- The raw inverse point evaluates a homogeneous component by its dehomogenization. -/
theorem rawChartPoint_val_homogeneousComponent (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j))
    (F : MvPolynomial (Fin (n + 1)) k) (d : ℕ) :
    (rawChartPoint j y).val (MvPolynomial.homogeneousComponent d F) =
      y.val (coordinateDehom j (MvPolynomial.homogeneousComponent d F)) * chartRadius j y ^ d := by
  rw [rawChartPoint, Berk.comap_val_apply, chartHomogenize_homogeneousComponent,
    Berk.gauss_val_C_mul_X_pow]

/-- The coefficient formula proves gradedness of the Gauss construction for every polynomial. -/
theorem rawChartPoint_isGraded (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) :
    IsGraded (rawChartPoint j y) := by
  intro F
  calc (rawChartPoint j y).val F
      = (Finset.range (F.totalDegree + 1)).sup (fun d =>
          y.val (coordinateDehom j (MvPolynomial.homogeneousComponent d F)) * chartRadius j y ^ d) := by
        change (Berk.gauss y (chartRadius j y)).val (chartHomogenize j F) = _
        rw [Berk.gauss_val_eq_sup_of_subset y (chartRadius j y) (chartHomogenize j F)
          (chartHomogenize_support_subset j F)]
        exact Finset.sup_congr rfl fun d _ => by rw [chartHomogenize_coeff]
    _ = (Finset.range (F.totalDegree + 1)).sup (fun d =>
          (rawChartPoint j y).val (MvPolynomial.homogeneousComponent d F)) :=
        Finset.sup_congr rfl fun d _ => (rawChartPoint_val_homogeneousComponent j y F d).symm

/-- The normalized graded projective point constructed from an affine seminorm. -/
def coordinateChartInversePoint (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) : ProjBerk k n :=
  ⟨rawChartPoint j y, rawChartPoint_isGraded j y, rawChartPoint_normalized j y⟩

/-- The inverse chart construction lies in the coordinate open because its `j`-value is positive. -/
def coordinateChartInv (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) : chartOpen (k := k) j :=
  ⟨coordinateChartInversePoint j y, by
    change (rawChartPoint j y).val (MvPolynomial.X j) ≠ 0
    rw [rawChartPoint_val_X_self]
    exact (chartRadius_pos j y).ne'⟩

@[simp]
theorem coordinateChartInv_coe (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) :
    (coordinateChartInv j y).1.1 = rawChartPoint j y := rfl

@[fun_prop]
theorem continuous_coordinateChartInversePoint (j : Fin (n + 1)) : Continuous (coordinateChartInversePoint (k := k) j) :=
  (continuous_rawChartPoint j).subtype_mk _

@[fun_prop]
theorem continuous_coordinateChartInv (j : Fin (n + 1)) : Continuous (coordinateChartInv (k := k) j) :=
  (continuous_coordinateChartInversePoint j).subtype_mk _

/-! ### Reconstruction of a normalized point from its affine ratios -/

theorem coordinateChartMap_val_dehomCoord (j : Fin (n + 1)) (v : chartOpen (k := k) j) (i : Fin (n + 1)) :
    (coordinateChartMap j v).val (coordinateDehomCoord j i) =
      v.1.1.val (MvPolynomial.X i) / v.1.1.val (MvPolynomial.X j) := by
  by_cases hi : i = j
  · subst i
    rw [coordinateDehomCoord_self, map_one, div_self v.2]
  · simpa only [coordinateDehomCoord, dif_neg hi] using coordinateChartMap_val_X j v ⟨i, hi⟩

/-- Normalization determines the coordinate bound of an affine ratio chart. -/
theorem chartBound_coordinateChartMap (j : Fin (n + 1)) (v : chartOpen (k := k) j) :
    chartBound j (coordinateChartMap j v) = (v.1.1.val (MvPolynomial.X j))⁻¹ := by
  calc chartBound j (coordinateChartMap j v)
      = Finset.univ.sup (fun i : Fin (n + 1) => (coordinateChartMap j v).val (coordinateDehomCoord j i)) :=
        chartBound_eq_sup_dehom j _
    _ = Finset.univ.sup (fun i : Fin (n + 1) =>
          v.1.1.val (MvPolynomial.X i) / v.1.1.val (MvPolynomial.X j)) :=
        Finset.sup_congr rfl fun i _ => coordinateChartMap_val_dehomCoord j v i
    _ = (Finset.univ.sup fun i : Fin (n + 1) => v.1.1.val (MvPolynomial.X i)) /
          v.1.1.val (MvPolynomial.X j) :=
        (Finset.apply_sup_eq_sup_comp_of_linearOrder (fun a : ℝ≥0 => a / v.1.1.val (MvPolynomial.X j))
          (fun _ _ h => by simpa only [div_eq_mul_inv] using mul_le_mul' h le_rfl)
          (zero_div _)).symm
    _ = (v.1.1.val (MvPolynomial.X j))⁻¹ := by rw [sup_val_X v.1, one_div]

@[simp]
theorem chartRadius_coordinateChartMap (j : Fin (n + 1)) (v : chartOpen (k := k) j) :
    chartRadius j (coordinateChartMap j v) = v.1.1.val (MvPolynomial.X j) := by
  rw [chartRadius, chartBound_coordinateChartMap, inv_inv]

/-- Localized homogeneous reconstruction relates the whole dehomogenized polynomial to its form. -/
theorem coordinateChartMap_val_dehom_homogeneousComponent (j : Fin (n + 1)) (v : chartOpen (k := k) j)
    (F : MvPolynomial (Fin (n + 1)) k) (d : ℕ) :
    (coordinateChartMap j v).val (coordinateDehom j (MvPolynomial.homogeneousComponent d F)) *
      v.1.1.val (MvPolynomial.X j) ^ d = v.1.1.val (MvPolynomial.homogeneousComponent d F) := by
  have h := congrArg (fun a => (Berk.awayLift (MvPolynomial.X j) v.1.1 v.2).val a)
    (chartRatioHom_dehom_homogeneousComponent_mul_pow (R := k) j F d)
  simp only [map_mul, map_pow] at h
  rw [Berk.awayLift_val_algebraMap (MvPolynomial.X j) v.1.1 v.2 (MvPolynomial.X j),
    Berk.awayLift_val_algebraMap (MvPolynomial.X j) v.1.1 v.2
      (MvPolynomial.homogeneousComponent d F)] at h
  exact h

/-- Reconstruction agrees on every homogeneous component, hence on every polynomial by gradedness. -/
theorem rawChartPoint_coordinateChartMap_eq (j : Fin (n + 1)) (v : chartOpen (k := k) j) :
    rawChartPoint j (coordinateChartMap j v) = v.1.1 := by
  refine Berk.ext_val fun F => ?_
  rw [rawChartPoint_isGraded j (coordinateChartMap j v) F, isGraded v.1 F]
  refine Finset.sup_congr rfl fun d _ => ?_
  rw [rawChartPoint_val_homogeneousComponent, chartRadius_coordinateChartMap]
  exact coordinateChartMap_val_dehom_homogeneousComponent j v F d

@[simp]
theorem coordinateChartInv_coordinateChartMap (j : Fin (n + 1)) (v : chartOpen (k := k) j) :
    coordinateChartInv j (coordinateChartMap j v) = v :=
  Subtype.ext (Subtype.ext (rawChartPoint_coordinateChartMap_eq j v))

/-- Localizing homogeneous substitution and cancelling `T` recovers every affine polynomial. -/
@[simp]
theorem coordinateChartMap_coordinateChartInv (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) :
    coordinateChartMap j (coordinateChartInv j y) = y := by
  have hT : (Berk.gauss y (chartRadius j y)).val (Polynomial.X : (CoordinateRing k j)[X]) ≠ 0 := by
    rw [Berk.gauss_val_X]
    exact (chartRadius_pos j y).ne'
  let z := Berk.awayLift (Polynomial.X : (CoordinateRing k j)[X]) (Berk.gauss y (chartRadius j y)) hT
  have hraw : (rawChartPoint j y).val (MvPolynomial.X j) ≠ 0 := by
    rw [rawChartPoint_val_X_self]
    exact (chartRadius_pos j y).ne'
  have hlift : Berk.awayLift (MvPolynomial.X j) (rawChartPoint j y) hraw =
      Berk.comap (chartHomogenizeLocalization (R := k) j) z := by
    apply Berk.awayComap_injective (MvPolynomial.X j)
    rw [Berk.awayComap_awayLift]
    refine Berk.ext_val fun F => ?_
    change (Berk.gauss y (chartRadius j y)).val (chartHomogenize j F) =
      z.val (chartHomogenizeLocalization j
        (algebraMap _ (Localization.Away (MvPolynomial.X j)) F))
    rw [chartHomogenizeLocalization_algebraMap]
    exact (Berk.awayLift_val_algebraMap (Polynomial.X : (CoordinateRing k j)[X])
      (Berk.gauss y (chartRadius j y)) hT (chartHomogenize j F)).symm
  refine Berk.ext_val fun a => ?_
  change (Berk.awayLift (MvPolynomial.X j) (rawChartPoint j y) hraw).val
    (chartRatioHom j a) = y.val a
  rw [hlift, Berk.comap_val_apply, chartHomogenizeLocalization_chartRatioHom]
  exact (Berk.awayLift_val_algebraMap (Polynomial.X : (CoordinateRing k j)[X])
    (Berk.gauss y (chartRadius j y)) hT (Polynomial.C a)).trans (Berk.gauss_val_C y _ a)

/-- The coordinate open of the normalized projective model is an affine analytification. -/
def coordinateChartHomeomorph (j : Fin (n + 1)) : chartOpen (k := k) j ≃ₜ Berk k (CoordinateRing k j) where
  toFun := coordinateChartMap j
  invFun := coordinateChartInv j
  left_inv := coordinateChartInv_coordinateChartMap j
  right_inv := coordinateChartMap_coordinateChartInv j
  continuous_toFun := continuous_coordinateChartMap j
  continuous_invFun := continuous_coordinateChartInv j

@[simp]
theorem coordinateChartHomeomorph_apply (j : Fin (n + 1)) (v : chartOpen (k := k) j) :
    coordinateChartHomeomorph j v = coordinateChartMap j v := rfl

@[simp]
theorem coordinateChartHomeomorph_symm_apply (j : Fin (n + 1)) (y : Berk k (CoordinateRing k j)) :
    (coordinateChartHomeomorph j).symm y = coordinateChartInv j y := rfl

end EnvelopeProperty.ProjBerk
