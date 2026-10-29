/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.GaussValuation
import EnvelopeProperty.Berkovich.SpectrumTopology

/-!
# Gauss points over arbitrary seminorm spectra

For any commutative ring, the Gauss valuation gives a point of the polynomial
seminorm spectrum above a given point, at any nonnegative radius. The point is
maximal on the corresponding closed fibre disc, depends jointly continuously on
the base point and radius, and bounds every polynomial evaluation on the disc.
Consequently the disc is compact without any finite generation assumption.

The construction preserves any prescribed real-valued valuation on a commutative
base ring and supplies the same results in relative spectra. Radius zero is
evaluation at zero. No field or trivial valuation hypothesis is used.
-/

open scoped NNReal Topology Polynomial
open Polynomial Set Topology

noncomputable section

namespace EnvelopeProperty.Berkovich

namespace Spectrum

variable {A : Type*} [CommRing A]

/-- Restriction of a polynomial seminorm to its constant coefficients. -/
def proj : Spectrum A[X] → Spectrum A := comap (C : A →+* A[X])

@[simp]
theorem proj_val_apply (z : Spectrum A[X]) (a : A) : (proj z).val a = z.val (C a) := rfl

@[fun_prop]
theorem continuous_proj : Continuous (proj : Spectrum A[X] → Spectrum A) :=
  continuous_comap _

/-- The Gauss point above an arbitrary seminorm, including radius zero. -/
def gauss (y : Spectrum A) (r : ℝ≥0) : Spectrum A[X] := ⟨gaussValuation y.val r⟩

theorem gauss_val_apply (y : Spectrum A) (r : ℝ≥0) (F : A[X]) :
    (gauss y r).val F = F.support.sup fun i => y.val (F.coeff i) * r ^ i := rfl

theorem gauss_val_eq_sup_of_subset (y : Spectrum A) (r : ℝ≥0) (F : A[X])
    {s : Finset ℕ} (hs : F.support ⊆ s) :
    (gauss y r).val F = s.sup fun i => y.val (F.coeff i) * r ^ i :=
  gaussFun_eq_sup_of_subset y.val r F hs

theorem le_gauss_val (y : Spectrum A) (r : ℝ≥0) (F : A[X]) (i : ℕ) :
    y.val (F.coeff i) * r ^ i ≤ (gauss y r).val F := le_gaussFun y.val r F i

theorem gauss_val_le_iff (y : Spectrum A) (r : ℝ≥0) (F : A[X]) (M : ℝ≥0) :
    (gauss y r).val F ≤ M ↔ ∀ i, y.val (F.coeff i) * r ^ i ≤ M :=
  gaussFun_le_iff y.val r F M

@[simp]
theorem gauss_val_monomial (y : Spectrum A) (r : ℝ≥0) (i : ℕ) (a : A) :
    (gauss y r).val (monomial i a) = y.val a * r ^ i := gaussFun_monomial y.val r i a

@[simp]
theorem gauss_val_C (y : Spectrum A) (r : ℝ≥0) (a : A) :
    (gauss y r).val (C a) = y.val a := gaussFun_C y.val r a

@[simp]
theorem gauss_val_X (y : Spectrum A) (r : ℝ≥0) : (gauss y r).val (X : A[X]) = r :=
  gaussFun_X y.val r

@[simp]
theorem proj_gauss (y : Spectrum A) (r : ℝ≥0) : proj (gauss y r) = y :=
  ext_val fun a => gauss_val_C y r a

theorem gauss_zero_val_apply (y : Spectrum A) (F : A[X]) :
    (gauss y 0).val F = y.val (F.coeff 0) := by
  refine le_antisymm ((gauss_val_le_iff y 0 F _).2 fun i => ?_) ?_
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, mul_one]
    · rw [zero_pow hi.ne', mul_zero]; exact zero_le
  · simpa using le_gauss_val y 0 F 0

/-- Radius zero is the section of the projection given by evaluation at zero. -/
theorem gauss_zero_eq_comap (y : Spectrum A) :
    gauss y 0 = comap (Polynomial.evalRingHom (0 : A)) y := by
  refine ext_val fun F => ?_
  rw [gauss_zero_val_apply, comap_val_apply]
  change y.val (F.coeff 0) = y.val (Polynomial.eval 0 F)
  rw [coeff_zero_eq_eval_zero]

/-- The Gauss point bounds all polynomial evaluations on its closed fibre disc. -/
theorem val_le_gauss_val {z : Spectrum A[X]} {y : Spectrum A} {r : ℝ≥0}
    (hz : proj z = y) (hX : z.val X ≤ r) (F : A[X]) :
    z.val F ≤ (gauss y r).val F := by
  conv_lhs => rw [F.as_sum_support_C_mul_X_pow]
  refine z.val.map_sum_le fun i _ => ?_
  rw [z.val.map_mul, z.val.map_pow, ← proj_val_apply, hz]
  calc y.val (F.coeff i) * z.val X ^ i ≤ y.val (F.coeff i) * r ^ i := by gcongr
    _ ≤ (gauss y r).val F := le_gauss_val y r F i

theorem gauss_mem_fibreDisc (y : Spectrum A) (r : ℝ≥0) :
    proj (gauss y r) = y ∧ (gauss y r).val X ≤ r :=
  ⟨proj_gauss y r, (gauss_val_X y r).le⟩

/-- Joint continuity holds for all nonnegative radii, including zero. -/
@[fun_prop]
theorem continuous_gauss_prod : Continuous fun p : Spectrum A × ℝ≥0 => gauss p.1 p.2 := by
  rw [continuous_iff]
  intro F
  simp only [gauss_val_apply]
  exact Continuous.finset_sup_apply fun i _ =>
    ((continuous_val_apply (F.coeff i)).comp continuous_fst).mul (continuous_snd.pow i)

@[fun_prop]
theorem continuous_gauss (r : ℝ≥0) : Continuous fun y : Spectrum A => gauss y r :=
  continuous_gauss_prod.comp (continuous_id.prodMk continuous_const)

/-- Closed fibre discs are compact over arbitrary commutative rings, without finite type. -/
theorem isCompact_fibreDisc (y : Spectrum A) (r : ℝ≥0) :
    IsCompact {z : Spectrum A[X] | proj z = y ∧ z.val X ≤ r} := by
  refine (isCompact_setOf_forall_val_le fun F => (gauss y r).val F).of_isClosed_subset ?_ ?_
  · exact (isClosed_eq continuous_proj continuous_const).inter
      (isClosed_le (f := fun z : Spectrum A[X] => z.val X) (g := fun _ => r)
        (continuous_val_apply X) continuous_const)
  · intro z hz F
    exact val_le_gauss_val hz.1 hz.2 F

end Spectrum

namespace RelativeSpectrum

variable {R : Type*} [CommRing R] {v : Valuation R ℝ≥0}
  {A : Type*} [CommRing A] [Algebra R A]

/-- The polynomial projection with a prescribed base valuation. -/
def proj : RelativeSpectrum v A[X] → RelativeSpectrum v A :=
  comap (CAlgHom : A →ₐ[R] A[X])

@[simp]
theorem proj_val_apply (z : RelativeSpectrum v A[X]) (a : A) : val (proj z) a = val z (C a) :=
  rfl

@[fun_prop]
theorem continuous_proj : Continuous (proj : RelativeSpectrum v A[X] → RelativeSpectrum v A) :=
  continuous_comap _

/-- The Gauss extension retains each prescribed scalar value. -/
def gauss (y : RelativeSpectrum v A) (r : ℝ≥0) : RelativeSpectrum v A[X] :=
  ⟨Spectrum.gauss y.1 r, fun c => by
    rw [Polynomial.algebraMap_apply, Spectrum.gauss_val_C]
    exact y.2 c⟩

@[simp]
theorem gauss_coe (y : RelativeSpectrum v A) (r : ℝ≥0) :
    (gauss y r : Spectrum A[X]) = Spectrum.gauss y.1 r := rfl

theorem gauss_val_apply (y : RelativeSpectrum v A) (r : ℝ≥0) (F : A[X]) :
    val (gauss y r) F = F.support.sup fun i => val y (F.coeff i) * r ^ i := rfl

@[simp]
theorem gauss_val_C (y : RelativeSpectrum v A) (r : ℝ≥0) (a : A) :
    val (gauss y r) (C a) = val y a := Spectrum.gauss_val_C y.1 r a

@[simp]
theorem gauss_val_X (y : RelativeSpectrum v A) (r : ℝ≥0) : val (gauss y r) (X : A[X]) = r :=
  Spectrum.gauss_val_X y.1 r

@[simp]
theorem proj_gauss (y : RelativeSpectrum v A) (r : ℝ≥0) : proj (gauss y r) = y :=
  ext_val fun a => gauss_val_C y r a

theorem gauss_zero_val_apply (y : RelativeSpectrum v A) (F : A[X]) :
    val (gauss y 0) F = val y (F.coeff 0) := Spectrum.gauss_zero_val_apply y.1 F

theorem gauss_zero_eq_comap (y : RelativeSpectrum v A) :
    gauss y 0 = comap ((aeval (0 : A)).restrictScalars R : A[X] →ₐ[R] A) y := by
  refine ext_val fun F => ?_
  rw [gauss_zero_val_apply, comap_val_apply, AlgHom.restrictScalars_apply,
    coe_aeval_eq_eval, coeff_zero_eq_eval_zero]

theorem val_le_gauss_val {z : RelativeSpectrum v A[X]} {y : RelativeSpectrum v A} {r : ℝ≥0}
    (hz : proj z = y) (hX : val z X ≤ r) (F : A[X]) : val z F ≤ val (gauss y r) F :=
  Spectrum.val_le_gauss_val (congrArg Subtype.val hz) hX F

@[fun_prop]
theorem continuous_gauss_prod :
    Continuous fun p : RelativeSpectrum v A × ℝ≥0 => gauss p.1 p.2 := by
  rw [continuous_iff]
  intro F
  simp only [gauss_val_apply]
  exact Continuous.finset_sup_apply fun i _ =>
    ((continuous_val_apply (F.coeff i)).comp continuous_fst).mul (continuous_snd.pow i)

@[fun_prop]
theorem continuous_gauss (r : ℝ≥0) : Continuous fun y : RelativeSpectrum v A => gauss y r :=
  continuous_gauss_prod.comp (continuous_id.prodMk continuous_const)

theorem isCompact_fibreDisc (y : RelativeSpectrum v A) (r : ℝ≥0) :
    IsCompact {z : RelativeSpectrum v A[X] | proj z = y ∧ val z X ≤ r} := by
  refine (isCompact_setOf_forall_val_le fun F => val (gauss y r) F).of_isClosed_subset ?_ ?_
  · exact (isClosed_eq continuous_proj continuous_const).inter
      (isClosed_le (f := fun z : RelativeSpectrum v A[X] => val z X) (g := fun _ => r)
        (continuous_val_apply X) continuous_const)
  · intro z hz F
    exact val_le_gauss_val hz.1 hz.2 F

end RelativeSpectrum

end EnvelopeProperty.Berkovich
