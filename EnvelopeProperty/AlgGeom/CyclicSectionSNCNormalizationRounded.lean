import EnvelopeProperty.AlgGeom.CyclicSectionNormalizationBasis
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # The actual rounded cyclic algebra for a finite branch family

All rounded generators lie in the same original quotient with coefficient
`u * ∏ j, f j ^ α j`. This constructs its actual finite integral rounded
subalgebra and bases, without a normality or SNC hypothesis.
-/
noncomputable section
universe v w
namespace EnvelopeProperty.CyclicSectionSNCNormalizationRounded
open CyclicSectionAlgebra Module
open scoped BigOperators
variable {R : Type v} [CommRing R] [IsDomain R]
variable {J : Type w} [Fintype J]

/-- The actual original generic quotient with the literal product branch coefficient. -/
abbrev GenericRootRing (n : ℕ) (α : J → ℕ) (u : R) (f : J → R) :=
  RootRing n (algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j))

/-- The literal product of original rounded branch denominators. -/
def denominator (n : ℕ) (α : J → ℕ) (f : J → R) (i : ℕ) : R :=
  ∏ j, f j ^ (i * α j / n)

/-- Every actual product denominator is nonzero in the SAME original domain. -/
theorem denominator_ne_zero (n : ℕ) (α : J → ℕ) (f : J → R)
    (hf : ∀ j, f j ≠ 0) (i : ℕ) : denominator n α f i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (hf j))

private theorem fraction_denominator_ne_zero (n : ℕ) (α : J → ℕ) (f : J → R)
    (hf : ∀ j, f j ≠ 0) (i : ℕ) :
    algebraMap R (FractionRing R) (denominator n α f i) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr
    (denominator_ne_zero n α f hf i)

/-- The original rounded element uses the actual inverse product denominator and SAME root. -/
def roundedPower (n : ℕ) (α : J → ℕ) (u : R) (f : J → R) (i : ℕ) :
    GenericRootRing n α u f :=
  algebraMap (FractionRing R) (GenericRootRing n α u f)
    ((algebraMap R (FractionRing R) (denominator n α f i))⁻¹) *
      root n (algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)) ^ i

omit [IsDomain R] in
/-- Euclidean division gives the exact whole original product coefficient identity. -/
theorem denominator_pow_mul_remainder (n : ℕ) (α : J → ℕ) (f : J → R) (i : ℕ) :
    denominator n α f i ^ n * (∏ j, f j ^ (i * α j % n)) = (∏ j, f j ^ α j) ^ i := by
  simp only [denominator, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← pow_mul, ← pow_add, ← pow_mul]
  congr 1
  simpa only [Nat.mul_comm] using Nat.div_add_mod (i * α j) n

/-- Every original rounded power has its exact original n-th power coefficient. -/
theorem roundedPower_pow (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hf : ∀ j, f j ≠ 0) (i : ℕ) :
    roundedPower n α u f i ^ n =
      algebraMap R (GenericRootRing n α u f) (u ^ i * ∏ j, f j ^ (i * α j % n)) := by
  have ht : (root n (algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)) ^ i) ^ n =
      algebraMap (FractionRing R) (GenericRootRing n α u f)
        ((algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)) ^ i) := by
    rw [pow_right_comm, root_pow, map_pow]
  rw [roundedPower, mul_pow,
    ← map_pow (algebraMap (FractionRing R) (GenericRootRing n α u f)), ht,
    ← map_mul (algebraMap (FractionRing R) (GenericRootRing n α u f)),
    IsScalarTower.algebraMap_apply R (FractionRing R) (GenericRootRing n α u f)]
  apply congrArg (algebraMap (FractionRing R) (GenericRootRing n α u f))
  have he := congrArg (algebraMap R (FractionRing R))
    (denominator_pow_mul_remainder n α f i).symm
  simp only [map_mul, map_pow] at he ⊢
  calc
    _ = (algebraMap R (FractionRing R) u) ^ i *
        (((algebraMap R (FractionRing R) (denominator n α f i)) ^ n)⁻¹ *
          (algebraMap R (FractionRing R) (∏ j, f j ^ α j)) ^ i) := by
      simp only [mul_pow, ← inv_pow]
      ring
    _ = (algebraMap R (FractionRing R) u) ^ i *
        (((algebraMap R (FractionRing R) (denominator n α f i)) ^ n)⁻¹ *
          ((algebraMap R (FractionRing R) (denominator n α f i)) ^ n *
            algebraMap R (FractionRing R) (∏ j, f j ^ (i * α j % n)))) := by rw [he]
    _ = _ := by simp [fraction_denominator_ne_zero n α f hf i]

/-- Every actual rounded generator is integral over the SAME original base. -/
theorem roundedPower_integral (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) (i : ℕ) : IsIntegral R (roundedPower n α u f i) := by
  apply IsIntegral.of_pow hn
  rw [roundedPower_pow n α u f hf i]
  exact isIntegral_algebraMap

/-- Every SAME original root power is recovered by its exact original product denominator. -/
theorem root_pow_eq_denominator_mul (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hf : ∀ j, f j ≠ 0) (i : ℕ) :
    root n (algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)) ^ i =
      algebraMap R (GenericRootRing n α u f) (denominator n α f i) * roundedPower n α u f i := by
  rw [roundedPower,
    IsScalarTower.algebraMap_apply R (FractionRing R) (GenericRootRing n α u f),
    ← mul_assoc, ← map_mul (algebraMap (FractionRing R) (GenericRootRing n α u f))]
  simp [fraction_denominator_ne_zero n α f hf i]

private theorem div_carry (n a i k : ℕ) (hn : 0 < n) :
    a * ((i + k) / n) + (((i + k) % n) * a) / n =
      i * a / n + k * a / n + (if n ≤ i * a % n + k * a % n then 1 else 0) := by
  calc
    _ = ((i + k) * a) / n := by
      have h : (i + k) * a = n * (a * ((i + k) / n)) + ((i + k) % n) * a := by
        calc
          _ = (n * ((i + k) / n) + (i + k) % n) * a := by rw [Nat.div_add_mod]
          _ = _ := by ring
      rw [h, Nat.mul_add_div hn]
    _ = _ := by rw [Nat.add_mul, Nat.add_div hn]

omit [IsDomain R] in
/-- The actual original product denominators have exactly the componentwise Euclidean carries. -/
theorem denominator_mul_carry (n : ℕ) (α : J → ℕ) (f : J → R) (hn : 0 < n) (i k : ℕ) :
    denominator n α f i * denominator n α f k *
        (∏ j, f j ^ (if n ≤ i * α j % n + k * α j % n then 1 else 0)) =
      (∏ j, f j ^ α j) ^ ((i + k) / n) * denominator n α f ((i + k) % n) := by
  simp only [denominator, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simp only [← pow_add, ← pow_mul]
  congr 1
  exact (div_carry n (α j) i k hn).symm

private theorem fraction_coefficients_mul (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) (i k : ℕ) :
    (algebraMap R (FractionRing R) (denominator n α f i))⁻¹ *
        (algebraMap R (FractionRing R) (denominator n α f k))⁻¹ *
        (algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)) ^ ((i + k) / n) =
      algebraMap R (FractionRing R)
        (u ^ ((i + k) / n) * ∏ j, f j ^ (if n ≤ i * α j % n + k * α j % n then 1 else 0)) *
        (algebraMap R (FractionRing R) (denominator n α f ((i + k) % n)))⁻¹ := by
  have he := congrArg (algebraMap R (FractionRing R)) (denominator_mul_carry n α f hn i k)
  simp only [map_mul, map_pow] at he ⊢
  rw [mul_pow]
  field_simp [fraction_denominator_ne_zero n α f hf i,
    fraction_denominator_ne_zero n α f hf k,
    fraction_denominator_ne_zero n α f hf ((i + k) % n)]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    congrArg (fun a : FractionRing R => (algebraMap R (FractionRing R) u) ^ ((i + k) / n) * a) he.symm

/-- SAME original rounded generators multiply by the literal original componentwise carry coefficient. -/
theorem roundedPower_mul (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) (i k : ℕ) :
    roundedPower n α u f i * roundedPower n α u f k =
      algebraMap R (GenericRootRing n α u f)
        (u ^ ((i + k) / n) * ∏ j, f j ^ (if n ≤ i * α j % n + k * α j % n then 1 else 0)) *
          roundedPower n α u f ((i + k) % n) := by
  have ht : root n (algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)) ^ (i + k) =
      algebraMap (FractionRing R) (GenericRootRing n α u f)
        ((algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)) ^ ((i + k) / n)) *
      root n (algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)) ^ ((i + k) % n) := by
    conv_lhs => rw [← Nat.div_add_mod (i + k) n]
    rw [pow_add, pow_mul, root_pow, map_pow]
  simp only [roundedPower]
  calc
    _ = algebraMap (FractionRing R) (GenericRootRing n α u f)
          ((algebraMap R (FractionRing R) (denominator n α f i))⁻¹ *
            (algebraMap R (FractionRing R) (denominator n α f k))⁻¹) *
        root n (algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)) ^ (i + k) := by
      rw [map_mul (algebraMap (FractionRing R) (GenericRootRing n α u f)), pow_add]
      ring
    _ = _ := by
      rw [ht, ← mul_assoc, ← map_mul (algebraMap (FractionRing R) (GenericRootRing n α u f)),
        fraction_coefficients_mul n α u f hn hf i k,
        map_mul (algebraMap (FractionRing R) (GenericRootRing n α u f)),
        ← IsScalarTower.algebraMap_apply R (FractionRing R) (GenericRootRing n α u f)]
      ring

/-- The literal original finite span of the SAME multicomponent rounded generators. -/
def roundedSpan (n : ℕ) (α : J → ℕ) (u : R) (f : J → R) :
    Submodule R (GenericRootRing n α u f) :=
  Submodule.span R (Set.range (fun i : Fin n => roundedPower n α u f (i : ℕ)))

private theorem roundedPower_mem_span (n : ℕ) (α : J → ℕ) (u : R) (f : J → R) (i : Fin n) :
    roundedPower n α u f (i : ℕ) ∈ roundedSpan n α u f :=
  Submodule.subset_span ⟨i, rfl⟩

/-- The whole original rounded span contains the SAME actual unit element. -/
theorem one_mem_roundedSpan (n : ℕ) (α : J → ℕ) (u : R) (f : J → R) (hn : 0 < n) :
    (1 : GenericRootRing n α u f) ∈ roundedSpan n α u f := by
  have h := roundedPower_mem_span n α u f ⟨0, hn⟩
  simpa [roundedPower, denominator] using h

/-- Multiplication of ALL elements preserves the SAME entire original rounded span. -/
theorem mul_mem_roundedSpan (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) (x y : GenericRootRing n α u f)
    (hx : x ∈ roundedSpan n α u f) (hy : y ∈ roundedSpan n α u f) :
    x * y ∈ roundedSpan n α u f := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
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

/-- The actual original rounded subalgebra has precisely the SAME finite rounded-span carrier. -/
def roundedAlgebra (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) : Subalgebra R (GenericRootRing n α u f) :=
  (roundedSpan n α u f).toSubalgebra (one_mem_roundedSpan n α u f hn)
    (mul_mem_roundedSpan n α u f hn hf)

/-- The WHOLE actual rounded algebra is finite over its SAME original base. -/
theorem roundedAlgebra_finite (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) : Module.Finite R (roundedAlgebra n α u f hn hf) :=
  Module.Finite.of_fg (Submodule.fg_span (Set.finite_range _))

/-- The WHOLE actual rounded algebra lies in the original integral closure. -/
theorem roundedAlgebra_le_integralClosure (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    roundedAlgebra n α u f hn hf ≤ integralClosure R (GenericRootRing n α u f) := by
  change roundedSpan n α u f ≤ (integralClosure R (GenericRootRing n α u f)).toSubmodule
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact roundedPower_integral n α u f hn hf (i : ℕ)

/-- EVERY original raw element maps into the SAME actual original rounded span. -/
theorem coefficientMap_mem_roundedSpan (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) (x : RootRing n (u * ∏ j, f j ^ α j)) :
    CyclicSectionBaseChange.coefficientMap n (u * ∏ j, f j ^ α j)
      (algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)) rfl x ∈ roundedSpan n α u f := by
  rw [← (CyclicSectionPowerBasis.basis n (u * ∏ j, f j ^ α j) hn).sum_repr x]
  simp only [map_sum, map_smul]
  apply (roundedSpan n α u f).sum_mem
  intro i _
  apply (roundedSpan n α u f).smul_mem
  rw [CyclicSectionPowerBasis.basis_apply, map_pow,
    CyclicSectionBaseChange.coefficientMap_root, root_pow_eq_denominator_mul n α u f hf]
  rw [← Algebra.smul_def]
  exact (roundedSpan n α u f).smul_mem _ (roundedPower_mem_span n α u f i)

/-- The WHOLE original raw quotient map factors through the SAME actual rounded algebra. -/
def rawToRounded (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    RootRing n (u * ∏ j, f j ^ α j) →ₐ[R] roundedAlgebra n α u f hn hf :=
  (CyclicSectionBaseChange.coefficientMap n (u * ∏ j, f j ^ α j)
    (algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)) rfl).codRestrict
    (roundedAlgebra n α u f hn hf) (coefficientMap_mem_roundedSpan n α u f hn hf)

/-- The factor preserves the ENTIRE SAME actual original coefficient-extension homomorphism. -/
theorem rawToRounded_comp_val (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    (roundedAlgebra n α u f hn hf).val.comp (rawToRounded n α u f hn hf) =
      CyclicSectionBaseChange.coefficientMap n (u * ∏ j, f j ^ α j)
        (algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)) rfl := rfl

/-- Actual nonzero product denominators diagonally rescale the SAME entire generic power basis. -/
def genericBasis (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    Basis (Fin n) (FractionRing R) (GenericRootRing n α u f) :=
  (CyclicSectionPowerBasis.basis n (algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)) hn).unitsSMul
    (fun i => (Units.mk0 (algebraMap R (FractionRing R) (denominator n α f (i : ℕ)))
      (fraction_denominator_ne_zero n α f hf _))⁻¹)

/-- Every actual generic basis vector is the literal SAME original multicomponent rounded power. -/
theorem genericBasis_apply (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) (i : Fin n) :
    genericBasis n α u f hn hf i = roundedPower n α u f (i : ℕ) := by
  rw [genericBasis, Basis.unitsSMul_apply, CyclicSectionPowerBasis.basis_apply]
  simp only [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, Algebra.smul_def, roundedPower]

/-- The SAME original rounded family is independent over the SAME original domain. -/
theorem roundedPower_linearIndependent (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    LinearIndependent R (fun i : Fin n => roundedPower n α u f (i : ℕ)) := by
  have h : LinearIndependent (FractionRing R) (fun i : Fin n => roundedPower n α u f (i : ℕ)) := by
    have he : (fun i : Fin n => roundedPower n α u f (i : ℕ)) =
        (genericBasis n α u f hn hf : Fin n → GenericRootRing n α u f) :=
      funext fun i => (genericBasis_apply n α u f hn hf i).symm
    rw [he]
    exact (genericBasis n α u f hn hf).linearIndependent
  exact h.restrict_scalars' R

/-- The SAME original rounded family is a basis of the WHOLE actual rounded subalgebra. -/
def basis (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) : Basis (Fin n) R (roundedAlgebra n α u f hn hf) :=
  Basis.span (roundedPower_linearIndependent n α u f hn hf)

/-- Each actual original algebra basis vector retains precisely its SAME literal rounded value. -/
theorem basis_apply (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) (i : Fin n) :
    (basis n α u f hn hf i : GenericRootRing n α u f) = roundedPower n α u f (i : ℕ) :=
  Basis.coe_span_apply _ i

end EnvelopeProperty.CyclicSectionSNCNormalizationRounded
