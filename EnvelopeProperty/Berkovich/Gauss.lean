/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.Topology
import EnvelopeProperty.Berkovich.GaussValuation
import EnvelopeProperty.Berkovich.SpectrumGauss
import EnvelopeProperty.Berkovich.SpectrumBridge

/-!
# Gauss points over the affine line

Let `k` be a field with the trivial absolute value, `A` a commutative `k`-algebra, `Y = Spec A`
and `Ỹ = Y × 𝔸¹ = Spec A[w]`. We write `A[X]` for `A[w]`. This file constructs the Gauss points
`η_{y,r} ∈ Ỹ^an` of Fang–Han–Xia, *The envelope property for unibranch projective varieties*,
§5.3 (proof of `lem:hartogs`, "the Gauss norm on the closed fibre disc of radius `r`"), recorded
in the blueprint as `lem:gauss-point`.

For a point `y ∈ Y^an` and a radius `r ≥ 0` the Gauss point is
`|∑_ℓ a_ℓ w^ℓ|_{η_{y,r}} = max_ℓ |a_ℓ|_y r^ℓ`.

## Main definitions

* `EnvelopeProperty.gaussValuation v r`: the Gauss valuation `F ↦ max_ℓ v(F_ℓ) r^ℓ` on `A[X]`
  attached to a valuation `v : Valuation A ℝ≥0` (an ultrametric multiplicative seminorm, possibly
  with nonzero kernel) and `r : ℝ≥0`. Multiplicativity is Gauss's lemma; we prove it directly
  (minimal indices `i`, `j` realising the maxima for `F`, `G` give a unique dominant term in the
  coefficient of degree `i + j` of `F G`), so no reduction to `A ⧸ supp v` is needed.
* `EnvelopeProperty.Berk.proj : Berk k A[X] → Berk k A`: the projection `p : Ỹ^an → Y^an`.
* `EnvelopeProperty.Berk.gauss y r`: the Gauss point `η_{y,r}`.

## Main results

* `Berk.gauss_val_apply`: the defining formula; `Berk.proj_gauss`: `η_{y,r}` lies over `y`;
  `Berk.gauss_val_X`, `Berk.logAbs_X_gauss`: `|w|_{η_{y,r}} = r`.
* `Berk.val_le_gauss_val` (**maximality**): every `z` over `y` with `|w|_z ≤ r` satisfies
  `|F|_z ≤ |F|_{η_{y,r}}` for all `F`.
* `Berk.continuous_gauss`, `Berk.continuous_gauss_prod`: `η_{y,r}` depends continuously on `y`
  (and jointly on `(y, r)`).
* `Berk.gauss_val_lt_iff`, `Berk.logAbs_gauss_lt_iff`: strict polynomial inequalities at a Gauss
  point are coefficientwise: `log|F|(η_{y,r}) < c ↔ ∀ ℓ, log|a_ℓ|(y) + ℓ log r < c`. This is the
  computation `η_{y,r} ∈ W_j ↔ log r < -φ_j(y)` in the proof of `lem:hartogs`.
* `Berk.gauss_zero_val_apply`, `Berk.gauss_zero_eq_comap`: `η_{y,0}` is the point `(y, 0)`.
* `Berk.isCompact_fibreDisc`: closed fibre discs `{z | p z = y, |w|_z ≤ r}` are compact.
-/

open scoped NNReal ENNReal Topology Polynomial

open Polynomial Set Classical

noncomputable section

namespace EnvelopeProperty

namespace Berk

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-! ### The projection `Y × 𝔸¹ → Y` -/

/-- The projection `p : (Y × 𝔸¹)^an → Y^an`, induced by the inclusion `A → A[X]` of constant
polynomials. -/
def proj : Berk k A[X] → Berk k A :=
  comap (CAlgHom : A →ₐ[k] A[X])

@[simp]
theorem proj_val_apply (z : Berk k A[X]) (a : A) : (proj z).val a = z.val (C a) :=
  rfl

@[simp]
theorem logAbs_proj (a : A) (z : Berk k A[X]) : logAbs a (proj z) = logAbs (C a) z :=
  rfl

@[fun_prop]
theorem continuous_proj : Continuous (proj : Berk k A[X] → Berk k A) :=
  continuous_comap _

@[simp]
theorem relativeSpectrumHomeomorph_proj (z : Berk k A[X]) :
    relativeSpectrumHomeomorph (proj z) =
      Berkovich.RelativeSpectrum.proj (relativeSpectrumHomeomorph z) := rfl

/-! ### Gauss points -/

/-- The **Gauss point** `η_{y,r} ∈ (Y × 𝔸¹)^an` over `y ∈ Y^an` of radius `r ≥ 0`
(FHX `lem:hartogs`, blueprint `lem:gauss-point`): `|∑_ℓ a_ℓ w^ℓ| = max_ℓ |a_ℓ|_y r^ℓ`. -/
def gauss (y : Berk k A) (r : ℝ≥0) : Berk k A[X] where
  val := gaussValuation y.val r
  val_algebraMap c hc := by
    rw [Polynomial.algebraMap_apply]
    exact (gaussFun_C y.val r _).trans (y.val_algebraMap c hc)

@[simp]
theorem relativeSpectrumHomeomorph_gauss (y : Berk k A) (r : ℝ≥0) :
    relativeSpectrumHomeomorph (gauss y r) =
      Berkovich.RelativeSpectrum.gauss (relativeSpectrumHomeomorph y) r := rfl

variable (y : Berk k A) (r : ℝ≥0)

/-- The defining formula of the Gauss point. -/
theorem gauss_val_apply (F : A[X]) :
    (gauss y r).val F = F.support.sup fun ℓ => y.val (F.coeff ℓ) * r ^ ℓ :=
  rfl

/-- The Gauss norm may be computed as a maximum over any finite set of indices containing the
support. -/
theorem gauss_val_eq_sup_of_subset (F : A[X]) {s : Finset ℕ} (hs : F.support ⊆ s) :
    (gauss y r).val F = s.sup fun ℓ => y.val (F.coeff ℓ) * r ^ ℓ :=
  gaussFun_eq_sup_of_subset y.val r F hs

theorem gauss_val_eq_sup_range (F : A[X]) :
    (gauss y r).val F =
      (Finset.range (F.natDegree + 1)).sup fun ℓ => y.val (F.coeff ℓ) * r ^ ℓ :=
  gauss_val_eq_sup_of_subset y r F fun _ h => Finset.mem_range.2
    (Nat.lt_succ_of_le (le_natDegree_of_mem_supp _ h))

theorem le_gauss_val (F : A[X]) (ℓ : ℕ) : y.val (F.coeff ℓ) * r ^ ℓ ≤ (gauss y r).val F :=
  le_gaussFun y.val r F ℓ

theorem exists_gauss_val_eq (F : A[X]) : ∃ ℓ, (gauss y r).val F = y.val (F.coeff ℓ) * r ^ ℓ :=
  exists_eq_gaussFun y.val r F

theorem gauss_val_le_iff (F : A[X]) (R : ℝ≥0) :
    (gauss y r).val F ≤ R ↔ ∀ ℓ, y.val (F.coeff ℓ) * r ^ ℓ ≤ R :=
  gaussFun_le_iff y.val r F R

/-- **Strict polynomial inequalities** at a Gauss point are coefficientwise. -/
theorem gauss_val_lt_iff (F : A[X]) {R : ℝ≥0} (hR : 0 < R) :
    (gauss y r).val F < R ↔ ∀ ℓ, y.val (F.coeff ℓ) * r ^ ℓ < R := by
  refine ⟨fun h ℓ => (le_gauss_val y r F ℓ).trans_lt h, fun h => ?_⟩
  rw [gauss_val_apply]
  exact (Finset.sup_lt_iff (bot_eq_zero (α := ℝ≥0) ▸ hR)).2 fun ℓ _ => h ℓ

@[simp]
theorem gauss_val_monomial (n : ℕ) (a : A) : (gauss y r).val (monomial n a) = y.val a * r ^ n :=
  gaussFun_monomial y.val r n a

@[simp]
theorem gauss_val_C (a : A) : (gauss y r).val (C a) = y.val a :=
  gaussFun_C y.val r a

@[simp]
theorem gauss_val_C_mul_X_pow (a : A) (n : ℕ) :
    (gauss y r).val (C a * X ^ n) = y.val a * r ^ n := by
  rw [C_mul_X_pow_eq_monomial, gauss_val_monomial]

/-- `|w|_{η_{y,r}} = r`. -/
@[simp]
theorem gauss_val_X : (gauss y r).val (X : A[X]) = r :=
  gaussFun_X y.val r

/-- The Gauss point `η_{y,r}` lies over `y`. -/
@[simp]
theorem proj_gauss : proj (gauss y r) = y :=
  ext_val fun a => gauss_val_C y r a

/-- `log|w|(η_{y,r}) = log r`. -/
@[simp]
theorem logAbs_X_gauss : logAbs (X : A[X]) (gauss y r) = ENNReal.log (r : ℝ≥0∞) := by
  rw [logAbs, gauss_val_X]

theorem logAbs_X_gauss_of_ne_zero (hr : r ≠ 0) :
    logAbs (X : A[X]) (gauss y r) = (Real.log r : EReal) := by
  rw [logAbs_X_gauss, ENNReal.log_of_nnreal hr]

/-- The Gauss point of radius `0` is the point `(y, 0)`: `|F|_{η_{y,0}} = |F(0)|_y`. -/
theorem gauss_zero_val_apply (F : A[X]) : (gauss y 0).val F = y.val (F.coeff 0) := by
  refine le_antisymm ((gauss_val_le_iff y 0 F _).2 fun ℓ => ?_) ?_
  · rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
    · rw [pow_zero, mul_one]
    · rw [zero_pow hℓ.ne', mul_zero]; exact zero_le
  · simpa using le_gauss_val y 0 F 0

/-- The Gauss point of radius `0` is the image of `y` under the section `w = 0`. -/
theorem gauss_zero_eq_comap :
    gauss y 0 = comap ((aeval (0 : A)).restrictScalars k : A[X] →ₐ[k] A) y := by
  refine ext_val fun F => ?_
  rw [gauss_zero_val_apply, comap_val_apply, AlgHom.restrictScalars_apply, coe_aeval_eq_eval,
    coeff_zero_eq_eval_zero]

/-- **Maximality of the Gauss point**: if `z` lies over `y` and `|w|_z ≤ r`, then
`|F|_z ≤ |F|_{η_{y,r}}` for every `F`. This is the ultrametric inequality applied to
`F = ∑_ℓ a_ℓ w^ℓ`. -/
theorem val_le_gauss_val {z : Berk k A[X]} {y : Berk k A} {r : ℝ≥0} (hz : proj z = y)
    (hX : z.val X ≤ r) (F : A[X]) : z.val F ≤ (gauss y r).val F := by
  conv_lhs => rw [F.as_sum_support_C_mul_X_pow]
  refine z.val.map_sum_le fun ℓ _ => ?_
  rw [z.val.map_mul, z.val.map_pow, ← proj_val_apply, hz]
  calc y.val (F.coeff ℓ) * z.val X ^ ℓ ≤ y.val (F.coeff ℓ) * r ^ ℓ := by gcongr
    _ ≤ (gauss y r).val F := le_gauss_val y r F ℓ

theorem logAbs_le_logAbs_gauss {z : Berk k A[X]} {y : Berk k A} {r : ℝ≥0} (hz : proj z = y)
    (hX : z.val X ≤ r) (F : A[X]) : logAbs F z ≤ logAbs F (gauss y r) := by
  rw [logAbs, logAbs, ENNReal.log_le_log_iff, ENNReal.coe_le_coe]
  exact val_le_gauss_val hz hX F

/-- The Gauss point `η_{y,r}` lies in the closed fibre disc of radius `r` over `y`. -/
theorem gauss_mem_fibreDisc : proj (gauss y r) = y ∧ (gauss y r).val X ≤ r :=
  ⟨proj_gauss y r, (gauss_val_X y r).le⟩

/-- The Gauss norm is monotone in the radius. -/
theorem gauss_val_mono {r r' : ℝ≥0} (h : r ≤ r') (F : A[X]) :
    (gauss y r).val F ≤ (gauss y r').val F :=
  val_le_gauss_val (proj_gauss y r) ((gauss_val_X y r).le.trans h) F

/-! ### Continuity -/

/-- The Gauss point depends continuously on `(y, r)`. -/
theorem continuous_gauss_prod :
    Continuous fun p : Berk k A × ℝ≥0 => gauss p.1 p.2 := by
  have h : Continuous fun p : Berk k A × ℝ≥0 =>
      Berkovich.RelativeSpectrum.gauss (relativeSpectrumHomeomorph p.1) p.2 :=
    Berkovich.RelativeSpectrum.continuous_gauss_prod.comp
      ((relativeSpectrumHomeomorph.continuous.comp continuous_fst).prodMk continuous_snd)
  exact relativeSpectrumHomeomorph.symm.continuous.comp h

/-- The Gauss point `η_{y,r}` depends continuously on `y`. -/
@[fun_prop]
theorem continuous_gauss (r : ℝ≥0) : Continuous fun y : Berk k A => gauss y r :=
  continuous_gauss_prod.comp (continuous_id.prodMk continuous_const)

/-! ### Logarithmic form -/

/-- `log|F|(η_{y,r}) = max_ℓ (log|a_ℓ|(y) + ℓ log r)`. -/
theorem logAbs_gauss (F : A[X]) :
    logAbs F (gauss y r) =
      F.support.sup fun ℓ => logAbs (F.coeff ℓ) y + ℓ * ENNReal.log (r : ℝ≥0∞) := by
  rw [logAbs, gauss_val_apply, Finset.apply_sup_eq_sup_comp_of_linearOrder
    (fun t : ℝ≥0 => ENNReal.log (t : ℝ≥0∞)) (ENNReal.log_monotone.comp ENNReal.coe_mono)
    (by simp)]
  refine Finset.sup_congr rfl fun ℓ _ => ?_
  simp [logAbs, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.log_mul_add, ENNReal.log_pow]

theorem logAbs_coeff_add_le_logAbs_gauss (F : A[X]) (ℓ : ℕ) :
    logAbs (F.coeff ℓ) y + ℓ * ENNReal.log (r : ℝ≥0∞) ≤ logAbs F (gauss y r) := by
  have h := le_gauss_val y r F ℓ
  rw [logAbs, logAbs]
  rw [← ENNReal.log_pow, ← ENNReal.log_mul_add, ENNReal.log_le_log_iff]
  exact_mod_cast h

/-- `log|F|(η_{y,r}) ≤ c ↔ log|a_ℓ|(y) + ℓ log r ≤ c` for all `ℓ`. -/
theorem logAbs_gauss_le_iff (F : A[X]) (c : EReal) :
    logAbs F (gauss y r) ≤ c ↔ ∀ ℓ, logAbs (F.coeff ℓ) y + ℓ * ENNReal.log (r : ℝ≥0∞) ≤ c := by
  refine ⟨fun h ℓ => (logAbs_coeff_add_le_logAbs_gauss y r F ℓ).trans h, fun h => ?_⟩
  rw [logAbs_gauss]
  exact Finset.sup_le fun ℓ _ => h ℓ

/-- **Strict polynomial inequalities** at a Gauss point, logarithmic form:
`log|F|(η_{y,r}) < c ↔ log|a_ℓ|(y) + ℓ log r < c` for all `ℓ`. -/
theorem logAbs_gauss_lt_iff (F : A[X]) (c : EReal) :
    logAbs F (gauss y r) < c ↔ ∀ ℓ, logAbs (F.coeff ℓ) y + ℓ * ENNReal.log (r : ℝ≥0∞) < c := by
  refine ⟨fun h ℓ => (logAbs_coeff_add_le_logAbs_gauss y r F ℓ).trans_lt h, fun h => ?_⟩
  have hc : ⊥ < c := (bot_le.trans_lt (h 0))
  rw [logAbs_gauss]
  exact (Finset.sup_lt_iff hc).2 fun ℓ _ => h ℓ

/-- Strict polynomial inequalities at a Gauss point of positive radius, with real `log r`. -/
theorem logAbs_gauss_lt_iff_of_ne_zero (F : A[X]) (hr : r ≠ 0) (c : EReal) :
    logAbs F (gauss y r) < c ↔ ∀ ℓ, logAbs (F.coeff ℓ) y + ℓ * (Real.log r : EReal) < c := by
  rw [logAbs_gauss_lt_iff, ENNReal.log_of_nnreal hr]

/-! ### Compactness of closed fibre discs -/

/-- Closed fibre discs `{z | p z = y, |w|_z ≤ r}` are compact without finite generation:
transport the arbitrary relative-spectrum theorem through the specialization homeomorphism. -/
theorem isCompact_fibreDisc (y : Berk k A) (r : ℝ≥0) :
    IsCompact {z : Berk k A[X] | proj z = y ∧ z.val X ≤ r} := by
  let e := relativeSpectrumHomeomorph (k := k) (A := A[X])
  convert e.isCompact_preimage.mpr
    (Berkovich.RelativeSpectrum.isCompact_fibreDisc (relativeSpectrumHomeomorph y) r) using 1
  ext z
  change (proj z = y ∧ z.val X ≤ r) ↔
    (relativeSpectrumHomeomorph (proj z) = relativeSpectrumHomeomorph y ∧ z.val X ≤ r)
  exact and_congr relativeSpectrumHomeomorph.injective.eq_iff.symm Iff.rfl

end Berk

end EnvelopeProperty
