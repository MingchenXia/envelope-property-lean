import EnvelopeProperty.AlgGeom.CyclicSectionBaseChange
import EnvelopeProperty.AlgGeom.CyclicSectionPowerBasis
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The actual rounded cyclic algebra inside the original generic quotient

These are the rounded root elements and their entire finite algebra on a
principal divisor. Normality and equality with the full integral closure are
separate statements.
-/

noncomputable section
universe v
namespace EnvelopeProperty.CyclicSectionNormalizationRounded
open CyclicSectionAlgebra Module
variable {R : Type v} [CommRing R] [IsDomain R]

/-- The SAME original root quotient after extension to the base fraction field. -/
abbrev GenericRootRing (n α : ℕ) (u f : R) :=
  RootRing n (algebraMap R (FractionRing R) (u * f ^ α))

/-- The actual rounded root power in the original generic cyclic quotient. -/
def roundedPower (n α : ℕ) (u f : R) (i : ℕ) : GenericRootRing n α u f :=
  algebraMap (FractionRing R) (GenericRootRing n α u f)
    (((algebraMap R (FractionRing R) f) ^ (i * α / n))⁻¹) *
    root n (algebraMap R (FractionRing R) (u * f ^ α)) ^ i

private theorem frac_ne_zero (f : R) (hf : f ≠ 0) :
    algebraMap R (FractionRing R) f ≠ 0 :=
  fun h => hf ((IsFractionRing.injective R (FractionRing R)) (by simpa using h))

/-- Every actual rounded root has the original explicit monic root equation. -/
theorem roundedPower_pow (n α : ℕ) (u f : R) (hf : f ≠ 0) (i : ℕ) :
    roundedPower n α u f i ^ n =
      algebraMap R (GenericRootRing n α u f) (u ^ i * f ^ (i * α % n)) := by
  have ht : (root n (algebraMap R (FractionRing R) (u * f ^ α)) ^ i) ^ n =
      algebraMap (FractionRing R) (GenericRootRing n α u f)
        ((algebraMap R (FractionRing R) (u * f ^ α)) ^ i) := by
    rw [pow_right_comm, root_pow, ← map_pow]
  rw [roundedPower, mul_pow, ← map_pow, ht, ← map_mul,
    IsScalarTower.algebraMap_apply R (FractionRing R) (GenericRootRing n α u f)]
  apply congrArg (algebraMap (FractionRing R) (GenericRootRing n α u f))
  simp only [map_mul, map_pow, mul_pow]
  have he : α * i = (i * α / n) * n + i * α % n := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod (i * α) n).symm
  simp only [← inv_pow, ← pow_mul]
  rw [he, pow_add]
  simp [frac_ne_zero f hf, mul_assoc, mul_comm]

/-- The SAME actual rounded element lies in the genuine original integral closure. -/
theorem roundedPower_integral (n α : ℕ) (u f : R) (hn : 0 < n) (hf : f ≠ 0) (i : ℕ) :
    IsIntegral R (roundedPower n α u f i) := by
  apply IsIntegral.of_pow hn
  rw [roundedPower_pow n α u f hf i]
  exact isIntegral_algebraMap

/-- Every original root power is recovered by multiplying its rounded element by
its SAME original denominator. -/
theorem root_pow_eq_denominator_mul (n α : ℕ) (u f : R) (hf : f ≠ 0) (i : ℕ) :
    root n (algebraMap R (FractionRing R) (u * f ^ α)) ^ i =
      algebraMap R (GenericRootRing n α u f) (f ^ (i * α / n)) *
        roundedPower n α u f i := by
  rw [roundedPower, IsScalarTower.algebraMap_apply R (FractionRing R)
    (GenericRootRing n α u f), ← mul_assoc, ← map_mul]
  simp [frac_ne_zero f hf]

private theorem div_carry (n α i j : ℕ) (hn : 0 < n) :
    α * ((i + j) / n) + (((i + j) % n) * α) / n =
      i * α / n + j * α / n + (if n ≤ i * α % n + j * α % n then 1 else 0) := by
  calc
    _ = ((i + j) * α) / n := by
      have h : (i + j) * α =
          n * (α * ((i + j) / n)) + ((i + j) % n) * α := by
        calc
          _ = (n * ((i + j) / n) + (i + j) % n) * α := by rw [Nat.div_add_mod]
          _ = _ := by ring
      rw [h, Nat.mul_add_div hn]
    _ = _ := by rw [Nat.add_mul, Nat.add_div hn]

private theorem fraction_coefficients_mul (n α : ℕ) (u f : R) (hn : 0 < n)
    (hf : f ≠ 0) (i j : ℕ) :
    ((algebraMap R (FractionRing R) f) ^ (i * α / n))⁻¹ *
        ((algebraMap R (FractionRing R) f) ^ (j * α / n))⁻¹ *
        ((algebraMap R (FractionRing R) (u * f ^ α)) ^ ((i + j) / n)) =
      algebraMap R (FractionRing R)
        (u ^ ((i + j) / n) * f ^ (if n ≤ i * α % n + j * α % n then 1 else 0)) *
        ((algebraMap R (FractionRing R) f) ^ ((((i + j) % n) * α) / n))⁻¹ := by
  simp only [map_mul, map_pow, mul_pow, ← pow_mul]
  have hh := div_carry n α i j hn
  field_simp [frac_ne_zero f hf]
  simp only [← pow_add]
  calc
    _ = (algebraMap R (FractionRing R) u) ^ ((i + j) / n) *
        ((algebraMap R (FractionRing R) f) ^ (α * ((i + j) / n)) *
          (algebraMap R (FractionRing R) f) ^ (((i + j) % n) * α / n)) := by ring
    _ = _ := by rw [← pow_add, hh, pow_add]; ring

/-- Original rounded generators multiply in the SAME generic quotient by actual
base coefficients, with the exact Euclidean carry. -/
theorem roundedPower_mul (n α : ℕ) (u f : R) (hn : 0 < n) (hf : f ≠ 0) (i j : ℕ) :
    roundedPower n α u f i * roundedPower n α u f j =
      algebraMap R (GenericRootRing n α u f)
        (u ^ ((i + j) / n) * f ^ (if n ≤ i * α % n + j * α % n then 1 else 0)) *
        roundedPower n α u f ((i + j) % n) := by
  have ht : root n (algebraMap R (FractionRing R) (u * f ^ α)) ^ (i + j) =
      algebraMap (FractionRing R) (GenericRootRing n α u f)
        ((algebraMap R (FractionRing R) (u * f ^ α)) ^ ((i + j) / n)) *
        root n (algebraMap R (FractionRing R) (u * f ^ α)) ^ ((i + j) % n) := by
    conv_lhs => rw [← Nat.div_add_mod (i + j) n]
    rw [pow_add, pow_mul, root_pow, map_pow]
  simp only [roundedPower]
  calc
    _ = (algebraMap (FractionRing R) (GenericRootRing n α u f)
        (((algebraMap R (FractionRing R) f) ^ (i * α / n))⁻¹ *
          ((algebraMap R (FractionRing R) f) ^ (j * α / n))⁻¹)) *
        root n (algebraMap R (FractionRing R) (u * f ^ α)) ^ (i + j) := by
      rw [map_mul (algebraMap (FractionRing R) (GenericRootRing n α u f)), pow_add]
      ring
    _ = _ := by
      rw [ht, ← mul_assoc, ← map_mul, fraction_coefficients_mul n α u f hn hf i j,
        map_mul (algebraMap (FractionRing R) (GenericRootRing n α u f)),
        ← IsScalarTower.algebraMap_apply R (FractionRing R)
          (GenericRootRing n α u f)]
      ring

/-- The literal original finite span of rounded root powers. -/
def roundedSpan (n α : ℕ) (u f : R) : Submodule R (GenericRootRing n α u f) :=
  Submodule.span R (Set.range (fun i : Fin n => roundedPower n α u f (i : ℕ)))

private theorem roundedPower_mem_span (n α : ℕ) (u f : R) (i : Fin n) :
    roundedPower n α u f (i : ℕ) ∈ roundedSpan n α u f :=
  Submodule.subset_span ⟨i, rfl⟩

/-- The entire original rounded span contains the actual unit element. -/
theorem one_mem_roundedSpan (n α : ℕ) (u f : R) (hn : 0 < n) :
    (1 : GenericRootRing n α u f) ∈ roundedSpan n α u f := by
  have h := roundedPower_mem_span n α u f ⟨0, hn⟩
  simpa [roundedPower] using h

/-- Every pair of elements of the whole original rounded span multiplies inside it. -/
theorem mul_mem_roundedSpan (n α : ℕ) (u f : R) (hn : 0 < n) (hf : f ≠ 0)
    (x y : GenericRootRing n α u f) (hx : x ∈ roundedSpan n α u f)
    (hy : y ∈ roundedSpan n α u f) : x * y ∈ roundedSpan n α u f := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [roundedPower_mul n α u f hn hf]
      rw [← Algebra.smul_def]
      exact (roundedSpan n α u f).smul_mem _
        (roundedPower_mem_span n α u f ⟨_, Nat.mod_lt _ hn⟩)
    | zero => simpa only [mul_zero] using (roundedSpan n α u f).zero_mem
    | add y z hy hz hiy hiz =>
      simpa only [mul_add] using (roundedSpan n α u f).add_mem hiy hiz
    | smul a y hy hiy =>
      simpa only [mul_smul_comm] using (roundedSpan n α u f).smul_mem a hiy
  | zero => simpa only [zero_mul] using (roundedSpan n α u f).zero_mem
  | add x z hx hz hix hiz =>
    simpa only [add_mul] using (roundedSpan n α u f).add_mem hix hiz
  | smul a x hx hix =>
    simpa only [smul_mul_assoc] using (roundedSpan n α u f).smul_mem a hix

/-- The actual rounded subalgebra has exactly the original rounded span as carrier. -/
def roundedAlgebra (n α : ℕ) (u f : R) (hn : 0 < n) (hf : f ≠ 0) :
    Subalgebra R (GenericRootRing n α u f) :=
  (roundedSpan n α u f).toSubalgebra (one_mem_roundedSpan n α u f hn)
    (mul_mem_roundedSpan n α u f hn hf)

/-- The original rounded subalgebra is finite over its SAME original base. -/
theorem roundedAlgebra_finite (n α : ℕ) (u f : R) (hn : 0 < n) (hf : f ≠ 0) :
    Module.Finite R (roundedAlgebra n α u f hn hf) :=
  Module.Finite.of_fg (Submodule.fg_span (Set.finite_range _))

/-- The WHOLE actual rounded algebra belongs to the original integral closure. -/
theorem roundedAlgebra_le_integralClosure (n α : ℕ) (u f : R) (hn : 0 < n) (hf : f ≠ 0) :
    roundedAlgebra n α u f hn hf ≤ integralClosure R (GenericRootRing n α u f) := by
  change roundedSpan n α u f ≤ (integralClosure R (GenericRootRing n α u f)).toSubmodule
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact roundedPower_integral n α u f hn hf (i : ℕ)

/-- The original raw coefficient map sends EVERY original quotient element into
its actual rounded span. -/
theorem coefficientMap_mem_roundedSpan (n α : ℕ) (u f : R) (hn : 0 < n) (hf : f ≠ 0)
    (x : RootRing n (u * f ^ α)) :
    CyclicSectionBaseChange.coefficientMap n (u * f ^ α)
      (algebraMap R (FractionRing R) (u * f ^ α)) rfl x ∈ roundedSpan n α u f := by
  rw [← (CyclicSectionPowerBasis.basis n (u * f ^ α) hn).sum_repr x]
  simp only [map_sum, map_smul]
  apply (roundedSpan n α u f).sum_mem
  intro i _
  apply (roundedSpan n α u f).smul_mem
  rw [CyclicSectionPowerBasis.basis_apply, map_pow,
    CyclicSectionBaseChange.coefficientMap_root, root_pow_eq_denominator_mul n α u f hf]
  rw [← Algebra.smul_def]
  exact (roundedSpan n α u f).smul_mem _ (roundedPower_mem_span n α u f i)

/-- The actual original raw algebra map factors through the SAME rounded subalgebra. -/
def rawToRounded (n α : ℕ) (u f : R) (hn : 0 < n) (hf : f ≠ 0) :
    RootRing n (u * f ^ α) →ₐ[R] roundedAlgebra n α u f hn hf :=
  (CyclicSectionBaseChange.coefficientMap n (u * f ^ α)
    (algebraMap R (FractionRing R) (u * f ^ α)) rfl).codRestrict
    (roundedAlgebra n α u f hn hf) (coefficientMap_mem_roundedSpan n α u f hn hf)

/-- Factoring preserves the WHOLE actual original coefficient-extension map. -/
theorem rawToRounded_comp_val (n α : ℕ) (u f : R) (hn : 0 < n) (hf : f ≠ 0) :
    (roundedAlgebra n α u f hn hf).val.comp (rawToRounded n α u f hn hf) =
      CyclicSectionBaseChange.coefficientMap n (u * f ^ α)
        (algebraMap R (FractionRing R) (u * f ^ α)) rfl := rfl

end EnvelopeProperty.CyclicSectionNormalizationRounded
