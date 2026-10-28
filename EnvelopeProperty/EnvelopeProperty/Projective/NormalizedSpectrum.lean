/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumGrading
import EnvelopeProperty.Berkovich.SpectrumGauss
import EnvelopeProperty.Berkovich.SpectrumLocalization
import EnvelopeProperty.Berkovich.SpectrumFiniteType
import EnvelopeProperty.Projective.ChartLocalization

/-!
# Graded normalized projective spectra over arbitrary coefficient rings

The absolute normalized spectrum consists of actual real polynomial seminorms that
are graded on every homogeneous decomposition and whose maximum coordinate value is
one. Genuine Gauss seminorms and principal localization supply both whole coordinate
chart inverses over any commutative ring. Prescribing an arbitrary coefficient seminorm
then restricts the charts to actual relative spectra.

The fixed-base normalized spectrum is compact and Hausdorff: its coordinate polydisc
is compact using the prescribed, polynomial-dependent coefficient bounds. No global
bound on the coefficient seminorm is required. Only coordinate values are normalized;
global boundedness of every polynomial evaluation is not asserted. A genuine zero-
coordinate chart point supplies a witness over every prescribed seminorm.

These are point/topology producers. The actual native Proj comparison, coherent ideal
identification and analytic structure sheaf require separate constructions.
-/

open scoped Classical NNReal ENNReal Topology Polynomial
open Set Topology
open EnvelopeProperty.ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
namespace EnvelopeProperty.Berkovich
namespace Spectrum
variable {R : Type*} [CommRing R] {σ : Type*}

def IsPolynomialGraded (x : Spectrum (MvPolynomial σ R)) : Prop :=
  ∀ F, x.val F = (Finset.range (F.totalDegree + 1)).sup fun d =>
    x.val (MvPolynomial.homogeneousComponent d F)

theorem isPolynomialGraded_iff (x : Spectrum (MvPolynomial σ R)) :
    IsPolynomialGraded x ↔ ∀ F d, x.val (MvPolynomial.homogeneousComponent d F) ≤ x.val F := by
  constructor
  · intro h F d
    by_cases hd : d ≤ F.totalDegree
    · rw [h F]
      exact Finset.le_sup (f := fun d => x.val (MvPolynomial.homogeneousComponent d F))
        (Finset.mem_range.2 (Nat.lt_succ_of_le hd))
    · rw [MvPolynomial.homogeneousComponent_eq_zero d F (not_le.1 hd), map_zero]
      exact zero_le
  · intro h F
    refine le_antisymm ?_ (Finset.sup_le fun d _ => h F d)
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent F]
    exact x.val.map_sum_le fun d hd =>
      Finset.le_sup (f := fun d => x.val (MvPolynomial.homogeneousComponent d F)) hd

theorem isClosed_setOf_isPolynomialGraded :
    IsClosed {x : Spectrum (MvPolynomial σ R) | IsPolynomialGraded x} := by
  have he : {x : Spectrum (MvPolynomial σ R) | IsPolynomialGraded x} =
      ⋂ F : MvPolynomial σ R, {x | x.val F = (Finset.range (F.totalDegree + 1)).sup
        fun d => x.val (MvPolynomial.homogeneousComponent d F)} := by
    ext x
    simp [IsPolynomialGraded]
  rw [he]
  exact isClosed_iInter fun F => isClosed_eq (continuous_val_apply F)
    (Continuous.finset_sup_apply fun d _ => continuous_val_apply _)
theorem isPolynomialGraded_iff_isGraded (x : Spectrum (MvPolynomial σ R)) :
    IsPolynomialGraded x ↔ IsGraded (MvPolynomial.homogeneousSubmodule σ R) x := by
  rw [isPolynomialGraded_iff]
  change (∀ F d, x.val (MvPolynomial.homogeneousComponent d F) ≤ x.val F) ↔
    ∀ F d, x.val (MvPolynomial.decomposition.decompose' F d) ≤ x.val F
  simp only [MvPolynomial.decomposition.decompose'_apply]

end Spectrum

def NormalizedProjectiveSpectrum (R : Type*) [CommRing R] (n : ℕ) :=
  {x : Spectrum (MvPolynomial (Fin (n + 1)) R) // Spectrum.IsPolynomialGraded x ∧
    Finset.univ.sup (fun i => x.val (MvPolynomial.X i)) = 1}

namespace ChartPrimitives
variable {A : Type*} [CommRing A]
private theorem continuous_awayLift (f : A) :
    Continuous fun x : {x : Spectrum A // x.val f ≠ 0} => Spectrum.awayLift f x.1 x.2 :=
  Spectrum.Away.continuous_lift (Localization.Away f) f
private theorem awayLift_val_mk' (f : A) (x : Spectrum A) (hx : x.val f ≠ 0) (a : A) (d : ℕ) :
    (Spectrum.awayLift f x hx).val
      (IsLocalization.mk' (Localization.Away f) a (⟨f ^ d, d, rfl⟩ : Submonoid.powers f)) =
        x.val a / x.val f ^ d := Spectrum.Away.lift_val_mk' (Localization.Away f) f x hx a d
private theorem awayComap_injective (f : A) : Function.Injective (Spectrum.awayComap f) :=
  Spectrum.Away.comap_injective (Localization.Away f) f
private theorem awayComap_awayLift (f : A) (x : Spectrum A) (hx : x.val f ≠ 0) :
    Spectrum.awayComap f (Spectrum.awayLift f x hx) = x :=
  Spectrum.Away.comap_lift (Localization.Away f) f x hx
private theorem gauss_val_C_mul_X_pow (y : Spectrum A) (r : ℝ≥0) (a : A) (d : ℕ) :
    (Spectrum.gauss y r).val (Polynomial.C a * Polynomial.X ^ d) = y.val a * r ^ d := by
  simp only [map_mul, map_pow, Spectrum.gauss_val_C, Spectrum.gauss_val_X]
end ChartPrimitives

namespace NormalizedProjectiveSpectrum
variable {R : Type*} [CommRing R] {n : ℕ}
instance instTopologicalSpace : TopologicalSpace (NormalizedProjectiveSpectrum R n) := instTopologicalSpaceSubtype
instance instT2Space : T2Space (NormalizedProjectiveSpectrum R n) := inferInstanceAs (T2Space {_x : Spectrum _ // _})
@[fun_prop] theorem continuous_val :
    Continuous (Subtype.val : NormalizedProjectiveSpectrum R n → Spectrum (MvPolynomial (Fin (n + 1)) R)) :=
  continuous_subtype_val
theorem isGraded (x : NormalizedProjectiveSpectrum R n) : Spectrum.IsPolynomialGraded x.1 := x.2.1
theorem sup_val_X (x : NormalizedProjectiveSpectrum R n) :
    Finset.univ.sup (fun i => x.1.val (MvPolynomial.X i)) = 1 := x.2.2
theorem val_X_le_one (x : NormalizedProjectiveSpectrum R n) (i : Fin (n + 1)) :
    x.1.val (MvPolynomial.X i) ≤ 1 :=
  (Finset.le_sup (f := fun i => x.1.val (MvPolynomial.X i)) (Finset.mem_univ i)).trans (sup_val_X x).le

theorem continuous_iff {Y : Type*} [TopologicalSpace Y] {f : Y → NormalizedProjectiveSpectrum R n} :
    Continuous f ↔ ∀ F, Continuous fun y => (f y).1.val F := by
  refine ⟨fun h F => (Spectrum.continuous_val_apply F).comp (continuous_val.comp h), fun h => ?_⟩
  exact IsEmbedding.subtypeVal.continuous_iff.2 (Spectrum.continuous_iff.2 h)

theorem exists_val_X_eq_one (x : NormalizedProjectiveSpectrum R n) : ∃ j, x.1.val (MvPolynomial.X j) = 1 := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    fun i => x.1.val (MvPolynomial.X i)
  exact ⟨j, hj ▸ sup_val_X x⟩
variable {R : Type*} [CommRing R] {n : ℕ}

/-- The coordinate open where `X_j` does not vanish. -/
def chartOpen (j : Fin (n + 1)) : Set (NormalizedProjectiveSpectrum R n) :=
  {v | v.1.val (MvPolynomial.X j) ≠ 0}

theorem isOpen_chartOpen (j : Fin (n + 1)) : IsOpen (chartOpen (R := R) j) :=
  (Spectrum.isOpen_setOf_val_ne_zero (MvPolynomial.X j)).preimage continuous_val

/-- The normalized coordinate opens cover the projective model. -/
theorem exists_mem_chartOpen (v : NormalizedProjectiveSpectrum R n) : ∃ j, v ∈ chartOpen j := by
  obtain ⟨j, hj⟩ := exists_val_X_eq_one v
  exact ⟨j, by simp only [chartOpen, Set.mem_ofPred_eq, hj, ne_eq, one_ne_zero, not_false_eq_true]⟩

/-- The forward affine chart map, defined on the full localized seminorm, not just its
values on individual coordinates. -/
def coordinateChartMap (j : Fin (n + 1)) (v : chartOpen (R := R) j) : Spectrum (CoordinateRing R j) :=
  Spectrum.comap (chartRatioHom j).toRingHom (Spectrum.awayLift (MvPolynomial.X j) v.1.1 v.2)

@[fun_prop]
theorem continuous_coordinateChartMap (j : Fin (n + 1)) : Continuous (coordinateChartMap (R := R) j) := by
  have hc : Continuous fun v : chartOpen (R := R) j => v.1.1 :=
    continuous_val.comp continuous_subtype_val
  exact (Spectrum.continuous_comap (chartRatioHom j).toRingHom).comp
    ((ChartPrimitives.continuous_awayLift (MvPolynomial.X j)).comp (hc.subtype_mk fun v => v.2))

/-- Evaluation on an affine chart coordinate is the ratio of its homogeneous coordinates. -/
theorem coordinateChartMap_val_X (j : Fin (n + 1)) (v : chartOpen (R := R) j) (i : ChartIndex j) :
    (coordinateChartMap j v).val (MvPolynomial.X i) =
      v.1.1.val (MvPolynomial.X i.1) / v.1.1.val (MvPolynomial.X j) := by
  simp only [coordinateChartMap, Spectrum.comap_val_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, chartRatioHom, MvPolynomial.aeval_X]
  simpa only [pow_one] using
    ChartPrimitives.awayLift_val_mk' (MvPolynomial.X j) v.1.1 v.2 (MvPolynomial.X i.1) 1

/-! ### The normalized Gauss point associated to an affine point -/

/-- The finite coordinate bound that normalizes the inverse chart. -/
def chartBound (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) : ℝ≥0 :=
  max 1 (Finset.univ.sup fun i : ChartIndex j => y.val (MvPolynomial.X i))

theorem one_le_chartBound (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) :
    1 ≤ chartBound j y := le_max_left _ _

theorem chartBound_pos (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) :
    0 < chartBound j y := zero_lt_one.trans_le (one_le_chartBound j y)

/-- The positive Gauss radius, inverse to the maximum coordinate norm. -/
def chartRadius (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) : ℝ≥0 := (chartBound j y)⁻¹

theorem chartRadius_pos (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) :
    0 < chartRadius j y := inv_pos.2 (chartBound_pos j y)

@[fun_prop]
theorem continuous_chartBound (j : Fin (n + 1)) : Continuous (chartBound (R := R) j) :=
  continuous_const.max (Continuous.finset_sup_apply fun i _ => Spectrum.continuous_abs (MvPolynomial.X i))

@[fun_prop]
theorem continuous_chartRadius (j : Fin (n + 1)) : Continuous (chartRadius (R := R) j) :=
  (continuous_chartBound j).inv₀ fun y => (chartBound_pos j y).ne'

/-- Pull back the Gauss seminorm under homogeneous substitution, with normalized radius. -/
def rawChartPoint (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) :
    Spectrum (MvPolynomial (Fin (n + 1)) R) :=
  Spectrum.comap (chartHomogenize j).toRingHom (Spectrum.gauss y (chartRadius j y))

@[fun_prop]
theorem continuous_rawChartPoint (j : Fin (n + 1)) : Continuous (rawChartPoint (R := R) j) :=
  (Spectrum.continuous_comap (chartHomogenize j).toRingHom).comp
    (Spectrum.continuous_gauss_prod.comp (continuous_id.prodMk (continuous_chartRadius j)))

theorem rawChartPoint_val_X (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) (i : Fin (n + 1)) :
    (rawChartPoint j y).val (MvPolynomial.X i) = y.val (coordinateDehomCoord j i) * chartRadius j y := by
  simp only [rawChartPoint, Spectrum.comap_val_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, chartHomogenize, MvPolynomial.aeval_X,
    map_mul, Spectrum.gauss_val_C, Spectrum.gauss_val_X]

@[simp]
theorem rawChartPoint_val_X_self (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) :
    (rawChartPoint j y).val (MvPolynomial.X j) = chartRadius j y := by
  rw [rawChartPoint_val_X, coordinateDehomCoord_self, map_one, one_mul]

/-- The affine coordinate bound is the maximum of all dehomogenized homogeneous coordinates. -/
theorem chartBound_eq_sup_dehom (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) :
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
theorem rawChartPoint_normalized (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) :
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
    (F : MvPolynomial (Fin (n + 1)) R) :
    (chartHomogenize j F).support ⊆ Finset.range (F.totalDegree + 1) := by
  intro d hd
  apply Finset.mem_range.2
  by_contra! hddeg
  have hc : (chartHomogenize j F).coeff d = 0 := by
    rw [chartHomogenize_coeff,
      MvPolynomial.homogeneousComponent_eq_zero d F (by omega), map_zero]
  exact (Polynomial.mem_support_iff.1 hd) hc

/-- The raw inverse point evaluates a homogeneous component by its dehomogenization. -/
theorem rawChartPoint_val_homogeneousComponent (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j))
    (F : MvPolynomial (Fin (n + 1)) R) (d : ℕ) :
    (rawChartPoint j y).val (MvPolynomial.homogeneousComponent d F) =
      y.val (coordinateDehom j (MvPolynomial.homogeneousComponent d F)) * chartRadius j y ^ d := by
  rw [rawChartPoint, Spectrum.comap_val_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, chartHomogenize_homogeneousComponent,
    ChartPrimitives.gauss_val_C_mul_X_pow]

/-- The coefficient formula proves gradedness of the Gauss construction for every polynomial. -/
theorem rawChartPoint_isGraded (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) :
    Spectrum.IsPolynomialGraded (rawChartPoint j y) := by
  intro F
  calc (rawChartPoint j y).val F
      = (Finset.range (F.totalDegree + 1)).sup (fun d =>
          y.val (coordinateDehom j (MvPolynomial.homogeneousComponent d F)) * chartRadius j y ^ d) := by
        change (Spectrum.gauss y (chartRadius j y)).val (chartHomogenize j F) = _
        rw [Spectrum.gauss_val_eq_sup_of_subset y (chartRadius j y) (chartHomogenize j F)
          (chartHomogenize_support_subset j F)]
        exact Finset.sup_congr rfl fun d _ => by rw [chartHomogenize_coeff]
    _ = (Finset.range (F.totalDegree + 1)).sup (fun d =>
          (rawChartPoint j y).val (MvPolynomial.homogeneousComponent d F)) :=
        Finset.sup_congr rfl fun d _ => (rawChartPoint_val_homogeneousComponent j y F d).symm

/-- The normalized graded projective point constructed from an affine seminorm. -/
def coordinateChartInversePoint (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) : NormalizedProjectiveSpectrum R n :=
  ⟨rawChartPoint j y, rawChartPoint_isGraded j y, rawChartPoint_normalized j y⟩

/-- The inverse chart construction lies in the coordinate open because its `j`-value is positive. -/
def coordinateChartInv (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) : chartOpen (R := R) j :=
  ⟨coordinateChartInversePoint j y, by
    change (rawChartPoint j y).val (MvPolynomial.X j) ≠ 0
    rw [rawChartPoint_val_X_self]
    exact (chartRadius_pos j y).ne'⟩

@[simp]
theorem coordinateChartInv_coe (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) :
    (coordinateChartInv j y).1.1 = rawChartPoint j y := rfl

@[fun_prop]
theorem continuous_coordinateChartInversePoint (j : Fin (n + 1)) : Continuous (coordinateChartInversePoint (R := R) j) :=
  (continuous_rawChartPoint j).subtype_mk _

@[fun_prop]
theorem continuous_coordinateChartInv (j : Fin (n + 1)) : Continuous (coordinateChartInv (R := R) j) :=
  (continuous_coordinateChartInversePoint j).subtype_mk _

/-! ### Reconstruction of a normalized point from its affine ratios -/

theorem coordinateChartMap_val_dehomCoord (j : Fin (n + 1)) (v : chartOpen (R := R) j) (i : Fin (n + 1)) :
    (coordinateChartMap j v).val (coordinateDehomCoord j i) =
      v.1.1.val (MvPolynomial.X i) / v.1.1.val (MvPolynomial.X j) := by
  by_cases hi : i = j
  · subst i
    rw [coordinateDehomCoord_self, map_one, div_self v.2]
  · simpa only [coordinateDehomCoord, dif_neg hi] using coordinateChartMap_val_X j v ⟨i, hi⟩

/-- Normalization determines the coordinate bound of an affine ratio chart. -/
theorem chartBound_coordinateChartMap (j : Fin (n + 1)) (v : chartOpen (R := R) j) :
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
theorem chartRadius_coordinateChartMap (j : Fin (n + 1)) (v : chartOpen (R := R) j) :
    chartRadius j (coordinateChartMap j v) = v.1.1.val (MvPolynomial.X j) := by
  rw [chartRadius, chartBound_coordinateChartMap, inv_inv]

/-- Localized homogeneous reconstruction relates the whole dehomogenized polynomial to its form. -/
theorem coordinateChartMap_val_dehom_homogeneousComponent (j : Fin (n + 1)) (v : chartOpen (R := R) j)
    (F : MvPolynomial (Fin (n + 1)) R) (d : ℕ) :
    (coordinateChartMap j v).val (coordinateDehom j (MvPolynomial.homogeneousComponent d F)) *
      v.1.1.val (MvPolynomial.X j) ^ d = v.1.1.val (MvPolynomial.homogeneousComponent d F) := by
  have h := congrArg (fun a => (Spectrum.awayLift (MvPolynomial.X j) v.1.1 v.2).val a)
    (chartRatioHom_dehom_homogeneousComponent_mul_pow (R := R) j F d)
  simp only [map_mul, map_pow] at h
  rw [Spectrum.awayLift_val_algebraMap (MvPolynomial.X j) v.1.1 v.2 (MvPolynomial.X j),
    Spectrum.awayLift_val_algebraMap (MvPolynomial.X j) v.1.1 v.2
      (MvPolynomial.homogeneousComponent d F)] at h
  exact h

/-- Reconstruction agrees on every homogeneous component, hence on every polynomial by gradedness. -/
theorem rawChartPoint_coordinateChartMap_eq (j : Fin (n + 1)) (v : chartOpen (R := R) j) :
    rawChartPoint j (coordinateChartMap j v) = v.1.1 := by
  refine Spectrum.ext_val fun F => ?_
  rw [rawChartPoint_isGraded j (coordinateChartMap j v) F, isGraded v.1 F]
  refine Finset.sup_congr rfl fun d _ => ?_
  rw [rawChartPoint_val_homogeneousComponent, chartRadius_coordinateChartMap]
  exact coordinateChartMap_val_dehom_homogeneousComponent j v F d

@[simp]
theorem coordinateChartInv_coordinateChartMap (j : Fin (n + 1)) (v : chartOpen (R := R) j) :
    coordinateChartInv j (coordinateChartMap j v) = v :=
  Subtype.ext (Subtype.ext (rawChartPoint_coordinateChartMap_eq j v))

/-- Localizing homogeneous substitution and cancelling `T` recovers every affine polynomial. -/
@[simp]
theorem coordinateChartMap_coordinateChartInv (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) :
    coordinateChartMap j (coordinateChartInv j y) = y := by
  have hT : (Spectrum.gauss y (chartRadius j y)).val (Polynomial.X : (CoordinateRing R j)[X]) ≠ 0 := by
    rw [Spectrum.gauss_val_X]
    exact (chartRadius_pos j y).ne'
  let z := Spectrum.awayLift (Polynomial.X : (CoordinateRing R j)[X]) (Spectrum.gauss y (chartRadius j y)) hT
  have hraw : (rawChartPoint j y).val (MvPolynomial.X j) ≠ 0 := by
    rw [rawChartPoint_val_X_self]
    exact (chartRadius_pos j y).ne'
  have hlift : Spectrum.awayLift (MvPolynomial.X j) (rawChartPoint j y) hraw =
      Spectrum.comap (chartHomogenizeLocalization (R := R) j).toRingHom z := by
    apply ChartPrimitives.awayComap_injective (MvPolynomial.X j)
    rw [ChartPrimitives.awayComap_awayLift]
    refine Spectrum.ext_val fun F => ?_
    change (Spectrum.gauss y (chartRadius j y)).val (chartHomogenize j F) =
      z.val (chartHomogenizeLocalization j
        (algebraMap _ (Localization.Away (MvPolynomial.X j)) F))
    rw [chartHomogenizeLocalization_algebraMap]
    exact (Spectrum.awayLift_val_algebraMap (Polynomial.X : (CoordinateRing R j)[X])
      (Spectrum.gauss y (chartRadius j y)) hT (chartHomogenize j F)).symm
  refine Spectrum.ext_val fun a => ?_
  change (Spectrum.awayLift (MvPolynomial.X j) (rawChartPoint j y) hraw).val
    (chartRatioHom j a) = y.val a
  rw [hlift, Spectrum.comap_val_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, chartHomogenizeLocalization_chartRatioHom]
  exact (Spectrum.awayLift_val_algebraMap (Polynomial.X : (CoordinateRing R j)[X])
    (Spectrum.gauss y (chartRadius j y)) hT (Polynomial.C a)).trans (Spectrum.gauss_val_C y _ a)

/-- A coordinate open of the arbitrary-ring normalized model is the actual affine seminorm spectrum. -/
def coordinateChartHomeomorph (j : Fin (n + 1)) : chartOpen (R := R) j ≃ₜ Spectrum (CoordinateRing R j) where
  toFun := coordinateChartMap j
  invFun := coordinateChartInv j
  left_inv := coordinateChartInv_coordinateChartMap j
  right_inv := coordinateChartMap_coordinateChartInv j
  continuous_toFun := continuous_coordinateChartMap j
  continuous_invFun := continuous_coordinateChartInv j

@[simp]
theorem coordinateChartHomeomorph_apply (j : Fin (n + 1)) (v : chartOpen (R := R) j) :
    coordinateChartHomeomorph j v = coordinateChartMap j v := rfl

@[simp]
theorem coordinateChartHomeomorph_symm_apply (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) :
    (coordinateChartHomeomorph j).symm y = coordinateChartInv j y := rfl

theorem isClosed_carrier :
    IsClosed {x : Spectrum (MvPolynomial (Fin (n + 1)) R) | Spectrum.IsPolynomialGraded x ∧
      Finset.univ.sup (fun i => x.val (MvPolynomial.X i)) = 1} :=
  Spectrum.isClosed_setOf_isPolynomialGraded.inter
    (isClosed_eq (Continuous.finset_sup_apply fun _i _ => Spectrum.continuous_val_apply _) continuous_const)

theorem coordinateChartMap_val_C (j : Fin (n + 1)) (x : chartOpen (R := R) j) (r : R) :
    (coordinateChartMap j x).val (MvPolynomial.C r) = x.1.1.val (MvPolynomial.C r) := by
  change (Spectrum.awayLift (MvPolynomial.X j) x.1.1 x.2).val
    (chartRatioHom j (MvPolynomial.C r)) = _
  rw [show chartRatioHom j (MvPolynomial.C r) =
      algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away (MvPolynomial.X j))
        (MvPolynomial.C r) from (chartRatioHom (R := R) j).commutes r]
  exact Spectrum.awayLift_val_algebraMap _ _ _ _

theorem rawChartPoint_val_C (j : Fin (n + 1)) (y : Spectrum (CoordinateRing R j)) (r : R) :
    (rawChartPoint j y).val (MvPolynomial.C r) = y.val (MvPolynomial.C r) := by
  change (Spectrum.gauss y (chartRadius j y)).val (chartHomogenize j (MvPolynomial.C r)) = _
  rw [show chartHomogenize j (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) from
    (chartHomogenize (R := R) j).commutes r, Spectrum.gauss_val_C]

end NormalizedProjectiveSpectrum

def RelativeNormalizedProjectiveSpectrum {R : Type*} [CommRing R] (v : Valuation R ℝ≥0) (n : ℕ) :=
  {x : NormalizedProjectiveSpectrum R n // ∀ r, x.1.val (MvPolynomial.C r) = v r}

namespace RelativeNormalizedProjectiveSpectrum
variable {R : Type*} [CommRing R] (v : Valuation R ℝ≥0) {n : ℕ}
instance instTopologicalSpace : TopologicalSpace (RelativeNormalizedProjectiveSpectrum v n) := instTopologicalSpaceSubtype
instance instT2Space : T2Space (RelativeNormalizedProjectiveSpectrum v n) :=
  inferInstanceAs (T2Space {_x : NormalizedProjectiveSpectrum R n // _})

theorem isClosed_coefficientLocus :
    IsClosed {x : NormalizedProjectiveSpectrum R n | ∀ r, x.1.val (MvPolynomial.C r) = v r} := by
  have he : {x : NormalizedProjectiveSpectrum R n | ∀ r, x.1.val (MvPolynomial.C r) = v r} =
      ⋂ r : R, {x | x.1.val (MvPolynomial.C r) = v r} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [he]
  exact isClosed_iInter fun r => isClosed_eq
    ((Spectrum.continuous_val_apply (MvPolynomial.C r)).comp continuous_subtype_val) continuous_const

theorem isClosedEmbedding_val :
    IsClosedEmbedding (Subtype.val : RelativeNormalizedProjectiveSpectrum v n → NormalizedProjectiveSpectrum R n) :=
  (isClosed_coefficientLocus v).isClosedEmbedding_subtypeVal

def chartOpen (j : Fin (n + 1)) : Set (RelativeNormalizedProjectiveSpectrum v n) :=
  {x | x.1 ∈ NormalizedProjectiveSpectrum.chartOpen j}

theorem isOpen_chartOpen (j : Fin (n + 1)) : IsOpen (chartOpen v j) :=
  (NormalizedProjectiveSpectrum.isOpen_chartOpen j).preimage continuous_subtype_val

theorem exists_mem_chartOpen (x : RelativeNormalizedProjectiveSpectrum v n) :
    ∃ j, x ∈ chartOpen v j := NormalizedProjectiveSpectrum.exists_mem_chartOpen x.1

def chartSubtypeHomeomorph (j : Fin (n + 1)) :
    chartOpen v j ≃ₜ
      {x : NormalizedProjectiveSpectrum.chartOpen (R := R) j //
        ∀ r, x.1.1.val (MvPolynomial.C r) = v r} where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def coordinateChartHomeomorph (j : Fin (n + 1)) :
    chartOpen v j ≃ₜ RelativeSpectrum v (CoordinateRing R j) :=
  (chartSubtypeHomeomorph v j).trans
    ((NormalizedProjectiveSpectrum.coordinateChartHomeomorph (R := R) j).subtype (fun x => by
      change (∀ r, x.1.1.val (MvPolynomial.C r) = v r) ↔
        ∀ r, (NormalizedProjectiveSpectrum.coordinateChartMap j x).val (MvPolynomial.C r) = v r
      simp only [NormalizedProjectiveSpectrum.coordinateChartMap_val_C]))

@[simp]
theorem coordinateChartHomeomorph_val_apply (j : Fin (n + 1)) (x : chartOpen v j)
    (a : CoordinateRing R j) :
    (coordinateChartHomeomorph v j x).1.val a =
      (NormalizedProjectiveSpectrum.coordinateChartMap j ⟨x.1.1, x.2⟩).val a := rfl

theorem coordinateChartHomeomorph_val_X (j : Fin (n + 1)) (x : chartOpen v j) (i : ChartIndex j) :
    (coordinateChartHomeomorph v j x).1.val (MvPolynomial.X i) =
      x.1.1.1.val (MvPolynomial.X i.1) / x.1.1.1.val (MvPolynomial.X j) :=
  NormalizedProjectiveSpectrum.coordinateChartMap_val_X j ⟨x.1.1, x.2⟩ i

@[simp]
theorem coordinateChartHomeomorph_symm_coe (j : Fin (n + 1))
    (y : RelativeSpectrum v (CoordinateRing R j)) :
    ((coordinateChartHomeomorph v j).symm y).1.1.1 =
      NormalizedProjectiveSpectrum.rawChartPoint j y.1 := rfl

def coefficientHomeomorph : RelativeNormalizedProjectiveSpectrum v n ≃ₜ
    {x : RelativeSpectrum v (MvPolynomial (Fin (n + 1)) R) //
      Spectrum.IsPolynomialGraded x.1 ∧ Finset.univ.sup (fun i => x.1.val (MvPolynomial.X i)) = 1} where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem isClosed_carrier :
    IsClosed {x : RelativeSpectrum v (MvPolynomial (Fin (n + 1)) R) |
      Spectrum.IsPolynomialGraded x.1 ∧ Finset.univ.sup (fun i => x.1.val (MvPolynomial.X i)) = 1} :=
  NormalizedProjectiveSpectrum.isClosed_carrier.preimage continuous_subtype_val

theorem isCompact_carrier :
    IsCompact {x : RelativeSpectrum v (MvPolynomial (Fin (n + 1)) R) |
      Spectrum.IsPolynomialGraded x.1 ∧ Finset.univ.sup (fun i => x.1.val (MvPolynomial.X i)) = 1} := by
  refine (RelativeSpectrum.isCompact_setOf_forall_abs_le (v := v)
    (MvPolynomial.adjoin_range_X (R := R) (σ := Fin (n + 1))) 1).of_isClosed_subset
      (isClosed_carrier v) ?_
  intro x hx a ha
  obtain ⟨i, rfl⟩ := ha
  exact (Finset.le_sup (f := fun i : Fin (n + 1) => x.1.val (MvPolynomial.X i))
    (Finset.mem_univ i)).trans hx.2.le

instance instCompactSpace : CompactSpace (RelativeNormalizedProjectiveSpectrum v n) := by
  have hc : CompactSpace {x : RelativeSpectrum v (MvPolynomial (Fin (n + 1)) R) //
      Spectrum.IsPolynomialGraded x.1 ∧ Finset.univ.sup (fun i => x.1.val (MvPolynomial.X i)) = 1} :=
    isCompact_iff_compactSpace.1 (isCompact_carrier v)
  exact @Homeomorph.compactSpace _ _ _ _ hc (coefficientHomeomorph (n := n) v).symm

def zeroCoordinates : RelativeNormalizedProjectiveSpectrum v n :=
  ((coordinateChartHomeomorph v (0 : Fin (n + 1))).symm
    (RelativeSpectrum.comap (MvPolynomial.aeval fun _ : ChartIndex (0 : Fin (n + 1)) => (0 : R))
      (RelativeSpectrum.self v))).1

end RelativeNormalizedProjectiveSpectrum
end EnvelopeProperty.Berkovich
