/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Finsupp.Weight

/-!
# Actual weighted polynomial ring seminorms

Coefficient norms may be nonseparated and merely submultiplicative. Every
polynomial has finite support, so any variable type is allowed. The exact
variable norm is norm(1) times its weight; unit normalization is not assumed.
-/
open scoped NNReal
noncomputable section
namespace EnvelopeProperty.WeightedPolynomial
variable {ι : Type*}

/-- The genuine finite-support multiplicative monomial weight. -/
def weight (w : ι → ℝ≥0) (m : ι →₀ ℕ) : ℝ≥0 := m.prod (fun i n => w i ^ n)

@[simp]
theorem weight_zero (w : ι → ℝ≥0) : weight w 0 = 1 := by simp [weight]

@[simp]
theorem weight_add (w : ι → ℝ≥0) (m n : ι →₀ ℕ) :
    weight w (m+n) = weight w m * weight w n := by
  exact Finsupp.prod_add_index' (fun i => pow_zero (w i)) (fun i a b => pow_add (w i) a b)

@[simp]
theorem weight_single (w : ι → ℝ≥0) (i : ι) (n : ℕ) :
    weight w (Finsupp.single i n) = w i ^ n := by simp [weight]

/-- Strict positivity is derived from the ACTUAL positive weights on finite support. -/
theorem weight_pos (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) (m : ι →₀ ℕ) : 0 < weight w m := by
  classical
  exact Finset.prod_pos fun i _ => pow_pos (hw i) _

variable {A : Type*} [SeminormedCommRing A]

/-- The actual finite coefficient maximum, with zero for the empty polynomial support. -/
def gauss (w : ι → ℝ≥0) (f : MvPolynomial ι A) : ℝ≥0 :=
  f.support.sup (fun m => ‖f.coeff m‖₊ * weight w m)

/-- Every ORIGINAL coefficient, including those outside support, obeys the full Gauss bound. -/
theorem le_gauss (w : ι → ℝ≥0) (f : MvPolynomial ι A) (m : ι →₀ ℕ) :
    ‖f.coeff m‖₊ * weight w m ≤ gauss w f := by
  classical
  by_cases hm : m ∈ f.support
  · exact Finset.le_sup (f := fun m => ‖f.coeff m‖₊ * weight w m) hm
  · rw [MvPolynomial.notMem_support_iff.mp hm, nnnorm_zero, zero_mul]
    exact zero_le

/-- The finite maximum bound is EXACTLY the family of all original coefficient bounds. -/
theorem gauss_le_iff (w : ι → ℝ≥0) (f : MvPolynomial ι A) (C : ℝ≥0) :
    gauss w f ≤ C ↔ ∀ m, ‖f.coeff m‖₊ * weight w m ≤ C := by
  constructor
  · intro h m
    exact (le_gauss w f m).trans h
  · intro h
    exact Finset.sup_le fun m _ => h m

@[simp]
theorem gauss_zero (w : ι → ℝ≥0) : gauss w (0 : MvPolynomial ι A) = 0 := by
  simp [gauss]

/-- EVERY original monomial retains its exact whole coefficient/weight value. -/
@[simp]
theorem gauss_monomial (w : ι → ℝ≥0) (m : ι →₀ ℕ) (a : A) :
    gauss w (MvPolynomial.monomial m a) = ‖a‖₊ * weight w m := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  · simp [gauss, MvPolynomial.support_monomial, ha]

@[simp]
theorem gauss_C (w : ι → ℝ≥0) (a : A) : gauss w (MvPolynomial.C a) = ‖a‖₊ := by
  change gauss w (MvPolynomial.monomial 0 a) = _
  rw [gauss_monomial, weight_zero, mul_one]

/-- Unit normalization is NOT assumed: this is the exact original variable norm. -/
@[simp]
theorem gauss_X (w : ι → ℝ≥0) (i : ι) :
    gauss w (MvPolynomial.X i : MvPolynomial ι A) = ‖(1 : A)‖₊ * w i := by
  change gauss w (MvPolynomial.monomial (Finsupp.single i 1) 1) = _
  rw [gauss_monomial, weight_single, pow_one]

@[simp]
theorem gauss_neg (w : ι → ℝ≥0) (f : MvPolynomial ι A) : gauss w (-f) = gauss w f := by
  classical
  apply le_antisymm
  · apply (gauss_le_iff w (-f) _).mpr
    intro m
    simpa only [MvPolynomial.coeff_neg, nnnorm_neg] using le_gauss w f m
  · apply (gauss_le_iff w f _).mpr
    intro m
    simpa only [MvPolynomial.coeff_neg, nnnorm_neg] using le_gauss w (-f) m

variable [IsUltrametricDist A]

/-- The full weighted maximum inherits the true original coefficient ultrametric inequality. -/
theorem gauss_add_le_max (w : ι → ℝ≥0) (f g : MvPolynomial ι A) :
    gauss w (f+g) ≤ max (gauss w f) (gauss w g) := by
  apply (gauss_le_iff w (f+g) _).mpr
  intro m
  rw [MvPolynomial.coeff_add]
  calc
    ‖f.coeff m + g.coeff m‖₊ * weight w m ≤
        max ‖f.coeff m‖₊ ‖g.coeff m‖₊ * weight w m :=
      mul_le_mul' (IsUltrametricDist.nnnorm_add_le_max _ _) le_rfl
    _ = max (‖f.coeff m‖₊ * weight w m) (‖g.coeff m‖₊ * weight w m) := max_mul _ _ _
    _ ≤ _ := max_le_max (le_gauss w f m) (le_gauss w g m)

/-- True finite coefficient convolution proves submultiplicativity without a multiplicative coefficient norm. -/
theorem gauss_mul_le (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) (f g : MvPolynomial ι A) :
    gauss w (f*g) ≤ gauss w f * gauss w g := by
  classical
  apply (gauss_le_iff w (f*g) _).mpr
  intro m
  have hW := weight_pos w hw m
  rw [MvPolynomial.coeff_mul]
  apply (le_div_iff₀ hW).mp
  apply IsUltrametricDist.nnnorm_sum_le_of_forall_le
  intro p hp
  apply (le_div_iff₀ hW).mpr
  have he : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
  rw [← he, weight_add]
  calc
    ‖f.coeff p.1 * g.coeff p.2‖₊ * (weight w p.1 * weight w p.2) ≤
        (‖f.coeff p.1‖₊ * ‖g.coeff p.2‖₊) * (weight w p.1 * weight w p.2) :=
      mul_le_mul' (nnnorm_mul_le _ _) le_rfl
    _ = (‖f.coeff p.1‖₊ * weight w p.1) * (‖g.coeff p.2‖₊ * weight w p.2) := by ring
    _ ≤ _ := mul_le_mul' (le_gauss w f p.1) (le_gauss w g p.2)

/-- The actual full polynomial Gauss function is a genuine ring seminorm. -/
def ringSeminorm (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) : RingSeminorm (MvPolynomial ι A) where
  toFun f := gauss w f
  map_zero' := by simp
  add_le' f g := by
    exact_mod_cast (gauss_add_le_max w f g).trans (max_le_add_of_nonneg zero_le zero_le)
  neg' f := congrArg ((↑) : ℝ≥0 → ℝ) (gauss_neg w f)
  mul_le' f g := by exact_mod_cast gauss_mul_le w hw f g

@[simp]
theorem ringSeminorm_apply (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) (f : MvPolynomial ι A) :
    ringSeminorm w hw f = (gauss w f : ℝ) := rfl

/-- Faithfulness is derived ONLY when the original coefficient ring norm is separated. -/
theorem gauss_eq_zero_iff {E : Type*} [NormedCommRing E]
    (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) (f : MvPolynomial ι E) :
    gauss w f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    apply MvPolynomial.ext
    intro m
    have hb := le_gauss w f m
    rw [hf] at hb
    have hz : ‖f.coeff m‖₊ * weight w m = 0 := le_antisymm hb zero_le
    exact nnnorm_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (weight_pos w hw m).ne')
  · rintro rfl
    exact gauss_zero w

end EnvelopeProperty.WeightedPolynomial
