import EnvelopeProperty.AlgGeom.NativeNumericalPSHComparisonContinuationGeneratedTwists
import EnvelopeProperty.AlgGeom.NativeNumericalFSContinuity
import EnvelopeProperty.AlgGeom.NativeLineFSPowerData
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The same FS function in arbitrarily small perturbations of its class

For a varying-line FS datum `D = (M, m, (sᵢ, wᵢ))` and `r > 0`, the datum
`FSData.powerDatum D r = (M^{⊗r}, m r, (sᵢ^{⊗r}, r wᵢ))` has the same function and the same
numerical class (the identity `bj22-trivval:equ:FSpower` following BJ22 Definition 2.18).
Combining it with the generated twist of
`EnvelopeProperty.AlgGeom.NativeNumericalPSHComparisonContinuationGeneratedTwists`:

* `FSData.exists_small_generatedPerturbations`: for a line `T` with finite global generators, the
  function of `D` is the function of nonzero data `E_j` of classes
  `[D] + (m (j+1))⁻¹ [T] → [D]`;
* `FSData.exists_small_ampleDirectionPerturbations`: for an ample line `A`, some `q > 0` (a power
  of `A` that is globally generated) gives data `E_j` with the same function and classes
  `[D] + q (m (j+1))⁻¹ [A] → [D]`.

These are the perturbations in an ample direction used in the proofs of BJ22 Lemma 4.9
(`bj22-trivval:lem:twopsh`) and Theorem 4.15 (i) (`bj22-trivval:thm:pshample`), for the
perturbation sizes `q / (m (j+1))`.  The lines of `E_j` are the actual tensor products
`M^{⊗(j+1)} ⊗ A^{⊗q}`; nothing is said about their ampleness.
-/

open AlgebraicGeometry CategoryTheory Scheme.Modules Filter Topology
open scoped Classical NNReal ENNReal Topology

noncomputable section

universe u

namespace EnvelopeProperty.NativeNumericalFubiniStudy

open Berkovich CanonicalGeometry SchemeGlobalSectionModelNormIsometries
open SchemeGlobalSectionTensorPowerNorms

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The `r`-th power of a varying-line FS datum: line `M^{⊗r}`, denominator `m r`, terms
`(s^{⊗r}, r w)`. -/
def FSData.powerDatum (D : FSData X) (r : ℕ) (hr : 0 < r) : FSData X where
  line := bundleTensorPower D.line r
  invertible := TensorPowerBaseIdealGrading.tensorPower_isInvertible D.invertible r
  m := D.m * r
  m_pos := Nat.mul_pos D.m_pos hr
  terms := D.terms.image fun q => (powerSection D.line q.1 r, (r : ℝ) * q.2)

private theorem nat_mul_cast_inv_mul (m r : ℕ) (hr : 0 < r) :
    ((m * r : ℕ) : ℝ)⁻¹ * (r : ℝ) = (m : ℝ)⁻¹ := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Nat.cast_mul, mul_inv, mul_assoc, inv_mul_cancel₀ hr', mul_one]

/-- The power datum has the same FS function. -/
theorem FSData.powerDatum_eval (D : FSData X) (r : ℕ) (hr : 0 < r)
    (p : X ⟶ Spec (.of k)) [IsProper p]
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
    (D.powerDatum r hr).eval p y = D.eval p y := by
  have hs : (D.terms.image fun q => (powerSection D.line q.1 r, (r : ℝ) * q.2)).sup
      (fun q => ENNReal.log
        (globalSectionNorm _root_.Valuation.one_apply_le_one y
          (bundleTensorPower D.line r)
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible D.invertible r) q.1 : ℝ≥0∞) +
          (q.2 : EReal)) =
      ((r : ℝ) : EReal) * D.terms.sup (fun q => ENNReal.log
        (globalSectionNorm _root_.Valuation.one_apply_le_one y D.line D.invertible q.1 : ℝ≥0∞) +
          (q.2 : EReal)) := by
    rw [Finset.sup_image,
      ProjBerk.ereal_coe_mul_finset_sup (c := (r : ℝ)) (by exact_mod_cast hr)]
    apply Finset.sup_congr rfl
    intro q _hq
    change ENNReal.log
        (globalSectionNorm _root_.Valuation.one_apply_le_one y (bundleTensorPower D.line r)
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible D.invertible r)
          (powerSection D.line q.1 r) : ℝ≥0∞) + (((r : ℝ) * q.2 : ℝ) : EReal) =
      ((r : ℝ) : EReal) * (ENNReal.log
        (globalSectionNorm _root_.Valuation.one_apply_le_one y D.line D.invertible q.1 : ℝ≥0∞) +
          (q.2 : EReal))
    rw [globalSectionNorm_powerSection _root_.Valuation.one_apply_le_one y D.line D.invertible,
      ENNReal.coe_pow, ENNReal.log_pow,
      ProjBerk.ereal_coe_mul_add (Nat.cast_nonneg r), EReal.coe_mul]
    rfl
  calc (D.powerDatum r hr).eval p y
      = ((((D.m * r : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * (((r : ℝ) : EReal) * D.terms.sup (fun q =>
          ENNReal.log (globalSectionNorm _root_.Valuation.one_apply_le_one y D.line D.invertible
            q.1 : ℝ≥0∞) + (q.2 : EReal))) :=
        congrArg (fun z : EReal => ((((D.m * r : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * z) hs
    _ = D.eval p y := by
        rw [ProjBerk.ereal_coe_mul_coe_mul, nat_mul_cast_inv_mul D.m r hr]
        rfl

/-- The power datum has the same numerical class. -/
theorem FSData.powerDatum_numericalClass (D : FSData X) (r : ℕ) (hr : 0 < r)
    (p : X ⟶ Spec (.of k)) [IsProjective p] :
    (D.powerDatum r hr).numericalClass p = D.numericalClass p := by
  change ((D.m * r : ℕ) : ℝ)⁻¹ • NativeRealNumericalClasses.lineClass p
    (bundleTensorPower D.line r)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible D.invertible r) = _
  rw [NativeRealNumericalClasses.lineClass_tensorPower p D.line D.invertible r, smul_smul,
    nat_mul_cast_inv_mul D.m r hr]
  rfl

/-- Powers preserve rationality of the weights. -/
theorem FSData.IsRational.powerDatum {D : FSData X} (hD : D.IsRational)
    (r : ℕ) (hr : 0 < r) : (D.powerDatum r hr).IsRational := by
  intro q hq
  have hq' : q ∈ D.terms.image fun q => (powerSection D.line q.1 r, (r : ℝ) * q.2) := hq
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
  obtain ⟨a, ha⟩ := hD t ht
  exact ⟨(r : ℚ) * a, by simp only [ha, Rat.cast_mul, Rat.cast_natCast]⟩

/-- On an integral scheme, powers preserve nonzeroness (by the function identity). -/
theorem FSData.Nonzero.powerDatum [IsIntegral X] {D : FSData X} (hD : D.Nonzero)
    (r : ℕ) (hr : 0 < r) (p : X ⟶ Spec (.of k)) [IsProper p] :
    (D.powerDatum r hr).Nonzero := by
  obtain ⟨y, hy⟩ := (D.nonzero_iff_exists_eval_ne_bot p).mp hD
  apply ((D.powerDatum r hr).nonzero_iff_exists_eval_ne_bot p).mpr
  exact ⟨y, by rw [D.powerDatum_eval r hr p y]; exact hy⟩

private local instance projectiveProper (p : X ⟶ Spec (.of k)) [IsProjective p] : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

private theorem original_class_perturbation_tendsto
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (m : ℕ) (x y : NativeRealNumericalClasses.Space p) :
    Tendsto (fun j : ℕ => x + (((m * (j + 1) : ℕ) : ℝ)⁻¹) • y)
      atTop (𝓝 x) := by
  have hs : Tendsto (fun j : ℕ => (((m * (j + 1) : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (m : ℝ)⁻¹
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv_rev, one_div, zero_mul] using h
  simpa only [zero_smul, add_zero] using tendsto_const_nhds.add (hs.smul_const y)

/-- For a line `T` with a finite generating family, the FS function of a nonzero datum `D` is
the function of nonzero data `E_j` whose classes `[D] + (m (j+1))⁻¹ [T]` tend to `[D]`. -/
theorem FSData.exists_small_generatedPerturbations [IsIntegral X]
    (D : FSData X) (hD : D.Nonzero)
    (T : X.Modules) (hT : IsInvertible T) (G : T.GeneratingSections) [Fintype G.I]
    (p : X ⟶ Spec (.of k)) [IsProjective p] :
    ∃ E : ℕ → FSData X,
      (∀ j, (E j).Nonzero) ∧
      (∀ j y, (E j).eval p y = D.eval p y) ∧
      (∀ j, (E j).numericalClass p = D.numericalClass p +
        (((D.m * (j + 1) : ℕ) : ℝ)⁻¹) • NativeRealNumericalClasses.lineClass p T hT) ∧
      Tendsto (fun j => (E j).numericalClass p) atTop (𝓝 (D.numericalClass p)) := by
  let E : ℕ → FSData X := fun j =>
    (D.powerDatum (j + 1) (Nat.zero_lt_succ j)).generatedTwist T hT G
  have hnonzero (j : ℕ) : (E j).Nonzero :=
    (hD.powerDatum (j + 1) (Nat.zero_lt_succ j) p).generatedTwist T hT G p
  have heval (j : ℕ) (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
      (E j).eval p y = D.eval p y :=
    ((D.powerDatum (j + 1) (Nat.zero_lt_succ j)).generatedTwist_eval T hT G p y).trans
      (D.powerDatum_eval (j + 1) (Nat.zero_lt_succ j) p y)
  have hclass (j : ℕ) : (E j).numericalClass p = D.numericalClass p +
      (((D.m * (j + 1) : ℕ) : ℝ)⁻¹) • NativeRealNumericalClasses.lineClass p T hT := by
    refine ((D.powerDatum (j + 1) (Nat.zero_lt_succ j)).generatedTwist_numericalClass
      T hT G p).trans ?_
    rw [FSData.powerDatum_numericalClass]
    rfl
  refine ⟨E, hnonzero, heval, hclass, ?_⟩
  exact Tendsto.congr (fun j => (hclass j).symm) (original_class_perturbation_tendsto p D.m _ _)

/-- For an ample line `A` there is `q > 0` such that the FS function of a nonzero datum `D` is
the function of nonzero data `E_j` whose classes `[D] + q (m (j+1))⁻¹ [A]` tend to `[D]`
(perturbation of the class in the ample direction `[A]`). -/
theorem FSData.exists_small_ampleDirectionPerturbations [IsIntegral X]
    (D : FSData X) (hD : D.Nonzero)
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (A : X.Modules) (hA : SchemeLineAmpleness.IsAmple p A) :
    ∃ q : ℕ, 0 < q ∧ ∃ E : ℕ → FSData X,
      (∀ j, (E j).Nonzero) ∧
      (∀ j y, (E j).eval p y = D.eval p y) ∧
      (∀ j, (E j).numericalClass p = D.numericalClass p +
        ((((D.m * (j + 1) : ℕ) : ℝ)⁻¹) * (q : ℝ)) •
          NativeRealNumericalClasses.lineClass p A hA.isInvertible) ∧
      Tendsto (fun j => (E j).numericalClass p) atTop (𝓝 (D.numericalClass p)) := by
  obtain ⟨N, hN⟩ := SchemeAmpleLineGlobalGeneration.exists_eventual_generatingSections p A hA
  obtain ⟨G, hG⟩ := hN (max N 1) (le_max_left N 1)
  have : Finite G.I := hG.finite
  let : Fintype G.I := Fintype.ofFinite G.I
  have hT := TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible (max N 1)
  obtain ⟨E, hE, heval, hclass, hconv⟩ :=
    D.exists_small_generatedPerturbations hD (bundleTensorPower A (max N 1)) hT G p
  refine ⟨max N 1, lt_of_lt_of_le Nat.one_pos (le_max_right N 1), E, hE, heval, ?_, hconv⟩
  intro j
  rw [hclass j, NativeRealNumericalClasses.lineClass_tensorPower p A hA.isInvertible (max N 1),
    smul_smul]

end EnvelopeProperty.NativeNumericalFubiniStudy
