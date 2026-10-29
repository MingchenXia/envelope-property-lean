import EnvelopeProperty.AlgGeom.CyclicSectionSNCNormalizationRounded

/-! # Actual unit changes of the same indexed branch equations

The original index set and exponents are fixed. The adjusted coefficient is
computed internally so the literal defining product remains unchanged. Actual
unit diagonals prove whole rounded-algebra preservation and all coordinates.
-/

noncomputable section
universe v w
namespace EnvelopeProperty.CyclicSectionSNCBranchUnitGauge
open Polynomial Module CyclicSectionAlgebra CyclicSectionSNCNormalizationRounded
open scoped BigOperators
variable {R : Type v} [CommRing R]
variable {J : Type w} [Fintype J]

/-- The actual product of the original equation units with specified exponents. -/
def productUnit (e : J → ℕ) (ε : J → Rˣ) : Rˣ := ∏ j, ε j ^ e j

theorem productUnit_coe (e : J → ℕ) (ε : J → Rˣ) :
    (productUnit e ε : R) = ∏ j, (ε j : R) ^ e j := by simp [productUnit]

theorem productUnit_one (e : J → ℕ) : productUnit e (fun _ => (1 : Rˣ)) = 1 := by
  simp [productUnit]

theorem productUnit_mul (e : J → ℕ) (ε η : J → Rˣ) :
    productUnit e (fun j => η j * ε j) = productUnit e η * productUnit e ε := by
  simp only [productUnit, mul_pow, Finset.prod_mul_distrib]

/-- The SAME indexed branch equations, each multiplied by its actual original unit. -/
def branches (f : J → R) (ε : J → Rˣ) : J → R := fun j => (ε j : R) * f j

omit [Fintype J] in
theorem branches_one (f : J → R) : branches f (fun _ => (1 : Rˣ)) = f := by
  funext j
  simp [branches]

omit [Fintype J] in
theorem branches_mul (f : J → R) (ε η : J → Rˣ) :
    branches (branches f ε) η = branches f (fun j => η j * ε j) := by
  funext j
  simp only [branches, Units.val_mul, mul_assoc]

/-- The internally adjusted original coefficient for the same indexed branch gauge. -/
def coefficient (α : J → ℕ) (u : R) (ε : J → Rˣ) : R :=
  u * ((productUnit α ε)⁻¹ : Rˣ)

theorem coefficient_one (α : J → ℕ) (u : R) :
    coefficient α u (fun _ => (1 : Rˣ)) = u := by simp [coefficient, productUnit_one]

theorem coefficient_mul (α : J → ℕ) (u : R) (ε η : J → Rˣ) :
    coefficient α (coefficient α u ε) η = coefficient α u (fun j => η j * ε j) := by
  simp only [coefficient, productUnit_mul, mul_inv_rev, Units.val_mul]
  ring

/-- The actual complete defining product is unchanged, without an equality certificate. -/
theorem coefficient_eq (α : J → ℕ) (u : R) (f : J → R) (ε : J → Rˣ) :
    coefficient α u ε * ∏ j, branches f ε j ^ α j = u * ∏ j, f j ^ α j := by
  simp only [branches, mul_pow, Finset.prod_mul_distrib, ← productUnit_coe]
  change (u * ((productUnit α ε)⁻¹ : Rˣ)) *
    ((productUnit α ε : R) * ∏ j, f j ^ α j) = _
  rw [mul_assoc, ← mul_assoc (((productUnit α ε)⁻¹ : Rˣ) : R), Units.inv_mul, one_mul]

/-- Every actual rounded denominator has its literal original unit floor product. -/
theorem denominator_eq (n : ℕ) (α : J → ℕ) (f : J → R) (ε : J → Rˣ) (i : ℕ) :
    denominator n α (branches f ε) i =
      (productUnit (fun j => i * α j / n) ε : R) * denominator n α f i := by
  simp only [denominator, branches, mul_pow, Finset.prod_mul_distrib, productUnit_coe]

variable (n : ℕ) (α : J → ℕ) (u : R) (f : J → R) (ε : J → Rˣ)
local notation "Q" => GenericRootRing n α u f
local notation "Qε" => GenericRootRing n α (coefficient α u ε) (branches f ε)

/-- The actual raw quotient comparison to the original presentation fixes the root. -/
def rawEquiv : RootRing n (coefficient α u ε * ∏ j, branches f ε j ^ α j) ≃ₐ[R]
    RootRing n (u * ∏ j, f j ^ α j) :=
  AdjoinRoot.algEquivOfEq R
    (X ^ n - C (coefficient α u ε * ∏ j, branches f ε j ^ α j))
    (X ^ n - C (u * ∏ j, f j ^ α j)) (by rw [coefficient_eq])

theorem rawEquiv_root : rawEquiv n α u f ε
    (root n (coefficient α u ε * ∏ j, branches f ε j ^ α j)) =
      root n (u * ∏ j, f j ^ α j) := AdjoinRoot.algEquivOfEq_root _ _ _

/-- The SAME canonical actual generic quotient comparison over the original fraction ring. -/
def genericEquiv : Qε ≃ₐ[FractionRing R] Q :=
  AdjoinRoot.algEquivOfEq (FractionRing R)
    (X ^ n - C (algebraMap R (FractionRing R)
      (coefficient α u ε * ∏ j, branches f ε j ^ α j)))
    (X ^ n - C (algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)))
    (by rw [coefficient_eq])

theorem genericEquiv_root : genericEquiv n α u f ε
    (root n (algebraMap R (FractionRing R)
      (coefficient α u ε * ∏ j, branches f ε j ^ α j))) =
      root n (algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)) :=
  AdjoinRoot.algEquivOfEq_root _ _ _

/-- Actual comparisons of arbitrary equation gauges through the original raw quotient. -/
def rawBetween (ε η : J → Rˣ) :=
  (rawEquiv n α u f η).trans (rawEquiv n α u f ε).symm

theorem rawBetween_refl (ε : J → Rˣ) :
    rawBetween n α u f ε ε = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  exact (rawEquiv n α u f ε).symm_apply_apply x

theorem rawBetween_trans (ε η θ : J → Rˣ) :
    (rawBetween n α u f η θ).trans (rawBetween n α u f ε η) = rawBetween n α u f ε θ := by
  apply AlgEquiv.ext
  intro x
  simp only [rawBetween, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]

/-- Actual comparisons of arbitrary equation gauges through the original generic quotient. -/
def genericBetween (ε η : J → Rˣ) :=
  (genericEquiv n α u f η).trans (genericEquiv n α u f ε).symm

theorem genericBetween_root (ε η : J → Rˣ) : genericBetween n α u f ε η
    (root n (algebraMap R (FractionRing R)
      (coefficient α u η * ∏ j, branches f η j ^ α j))) =
      root n (algebraMap R (FractionRing R)
        (coefficient α u ε * ∏ j, branches f ε j ^ α j)) := by
  apply (genericEquiv n α u f ε).injective
  simp only [genericBetween, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, genericEquiv_root]

theorem genericBetween_refl (ε : J → Rˣ) :
    genericBetween n α u f ε ε = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  exact (genericEquiv n α u f ε).symm_apply_apply x

theorem genericBetween_trans (ε η θ : J → Rˣ) :
    (genericBetween n α u f η θ).trans (genericBetween n α u f ε η) =
      genericBetween n α u f ε θ := by
  apply AlgEquiv.ext
  intro x
  simp only [genericBetween, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]

private theorem equiv_comparison_trans {A B C D : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (eA : A ≃ₐ[R] D) (eB : B ≃ₐ[R] D) (eC : C ≃ₐ[R] D) :
    (eC.trans eB.symm).trans (eB.trans eA.symm) = eC.trans eA.symm := by
  apply AlgEquiv.ext
  intro x
  change eA.symm (eB (eB.symm (eC x))) = eA.symm (eC x)
  rw [AlgEquiv.apply_symm_apply]

variable [IsDomain R]

private theorem fraction_unit_inv_mul (v : Rˣ) (x : FractionRing R) :
    (algebraMap R (FractionRing R) (v : R) * x)⁻¹ =
      algebraMap R (FractionRing R) (v⁻¹ : Rˣ) * x⁻¹ := by
  have hv : (algebraMap R (FractionRing R) (v : R))⁻¹ =
      algebraMap R (FractionRing R) (v⁻¹ : Rˣ) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← map_mul]
    simp
  rw [mul_inv_rev, hv, mul_comm]

/-- EVERY actual gauged rounded vector has its exact inverse original unit floor product. -/
theorem genericEquiv_roundedPower (i : ℕ) :
    genericEquiv n α u f ε (roundedPower n α (coefficient α u ε) (branches f ε) i) =
      ((productUnit (fun j => i * α j / n) ε)⁻¹ : Rˣ) • roundedPower n α u f i := by
  have hd : (algebraMap R (FractionRing R) (denominator n α (branches f ε) i))⁻¹ =
      algebraMap R (FractionRing R) ((productUnit (fun j => i * α j / n) ε)⁻¹ : Rˣ) *
        (algebraMap R (FractionRing R) (denominator n α f i))⁻¹ := by
    rw [denominator_eq, map_mul, fraction_unit_inv_mul]
  simp only [roundedPower, map_mul (genericEquiv n α u f ε),
    map_pow (genericEquiv n α u f ε), AlgEquiv.commutes, genericEquiv_root]
  rw [hd, map_mul (algebraMap (FractionRing R) Q), Units.smul_def, Algebra.smul_def,
    IsScalarTower.algebraMap_apply R (FractionRing R) Q]
  ring

/-- Actual unit diagonals give equality of the ENTIRE actual rounded spans. -/
theorem genericEquiv_map_roundedSpan :
    (roundedSpan n α (coefficient α u ε) (branches f ε)).map
        ((genericEquiv n α u f ε).restrictScalars R).toLinearMap = roundedSpan n α u f := by
  rw [roundedSpan, Submodule.map_span, ← Set.range_comp]
  change Submodule.span R (Set.range (fun i : Fin n => genericEquiv n α u f ε
    (roundedPower n α (coefficient α u ε) (branches f ε) (i : ℕ)))) = _
  simp_rw [genericEquiv_roundedPower]
  rw [roundedSpan, Submodule.span_range_eq_iSup, Submodule.span_range_eq_iSup]
  apply iSup_congr
  intro i
  exact Submodule.span_singleton_group_smul_eq R
    ((productUnit (fun j => (i : ℕ) * α j / n) ε)⁻¹) _

omit [Fintype J] in
/-- Original nonzero equations remain nonzero under their actual original units. -/
theorem branches_nonzero (f : J → R) (ε : J → Rˣ) (hf : ∀ j, f j ≠ 0) :
    ∀ j, branches f ε j ≠ 0 := fun j => mul_ne_zero (ε j).ne_zero (hf j)

variable (hn : 0 < n) (hf : ∀ j, f j ≠ 0)
local notation "M" => roundedAlgebra n α u f hn hf
local notation "Mε" => roundedAlgebra n α (coefficient α u ε) (branches f ε) hn
  (branches_nonzero f ε hf)

/-- The WHOLE actual gauged rounded subalgebra maps to the original rounded subalgebra. -/
theorem genericEquiv_map_roundedAlgebra :
    (Mε).map ((genericEquiv n α u f ε).restrictScalars R).toAlgHom = M := by
  ext x
  rw [Subalgebra.mem_map]
  change (∃ y ∈ roundedSpan n α (coefficient α u ε) (branches f ε),
    genericEquiv n α u f ε y = x) ↔ x ∈ roundedSpan n α u f
  rw [← genericEquiv_map_roundedSpan n α u f ε]
  exact (Submodule.mem_map (f := ((genericEquiv n α u f ε).restrictScalars R).toLinearMap)
    (p := roundedSpan n α (coefficient α u ε) (branches f ε)) (x := x)).symm

/-- Genuine restriction of the actual generic comparison, with preservation proved internally. -/
def roundedAlgebraEquiv : Mε ≃ₐ[R] M :=
  (((genericEquiv n α u f ε).restrictScalars R).subalgebraMap Mε).trans
    (Subalgebra.equivOfEq _ _ (genericEquiv_map_roundedAlgebra n α u f ε hn hf))

theorem roundedAlgebraEquiv_coe (x : Mε) :
    (roundedAlgebraEquiv n α u f ε hn hf x : Q) = genericEquiv n α u f ε (x : Qε) := rfl

theorem roundedAlgebraEquiv_comp_val :
    (M).val.comp (roundedAlgebraEquiv n α u f ε hn hf).toAlgHom =
      ((genericEquiv n α u f ε).restrictScalars R).toAlgHom.comp (Mε).val := rfl

theorem roundedAlgebraEquiv_basis (i : Fin n) : roundedAlgebraEquiv n α u f ε hn hf
    (basis n α (coefficient α u ε) (branches f ε) hn (branches_nonzero f ε hf) i) =
      ((productUnit (fun j => (i : ℕ) * α j / n) ε)⁻¹ : Rˣ) • basis n α u f hn hf i := by
  apply Subtype.ext
  change genericEquiv n α u f ε
      (basis n α (coefficient α u ε) (branches f ε) hn (branches_nonzero f ε hf) i : Qε) =
    ((productUnit (fun j => (i : ℕ) * α j / n) ε)⁻¹ : Rˣ) • (basis n α u f hn hf i : Q)
  rw [basis_apply, basis_apply, genericEquiv_roundedPower]

/-- The actual original basis coordinates of EVERY actual gauged rounded element. -/
theorem roundedAlgebraEquiv_repr_apply (x : Mε) (i : Fin n) :
    (basis n α u f hn hf).repr (roundedAlgebraEquiv n α u f ε hn hf x) i =
      (((productUnit (fun j => (i : ℕ) * α j / n) ε)⁻¹ : Rˣ) : R) *
        (basis n α (coefficient α u ε) (branches f ε) hn (branches_nonzero f ε hf)).repr x i := by
  let ba := basis n α u f hn hf
  let bb := basis n α (coefficient α u ε) (branches f ε) hn (branches_nonzero f ε hf)
  have hsum : roundedAlgebraEquiv n α u f ε hn hf x = ∑ j : Fin n,
      ((((productUnit (fun k => (j : ℕ) * α k / n) ε)⁻¹ : Rˣ) : R) * bb.repr x j) • ba j := by
    calc
      _ = roundedAlgebraEquiv n α u f ε hn hf (∑ j : Fin n, bb.repr x j • bb j) :=
        congrArg (roundedAlgebraEquiv n α u f ε hn hf) (bb.sum_repr x).symm
      _ = _ := by
        simp only [map_sum, map_smul, ba, bb, roundedAlgebraEquiv_basis,
          Units.smul_def, smul_smul, mul_comm]
  change ba.repr (roundedAlgebraEquiv n α u f ε hn hf x) i = _
  rw [hsum]
  exact congrFun (ba.repr_sum_self (fun j =>
    (((productUnit (fun k => (j : ℕ) * α k / n) ε)⁻¹ : Rˣ) : R) * bb.repr x j)) i

/-- Whole actual rounded comparisons between arbitrary gauges of the same original presentation. -/
def roundedBetween (ε η : J → Rˣ) :
    roundedAlgebra n α (coefficient α u η) (branches f η) hn (branches_nonzero f η hf) ≃ₐ[R]
      roundedAlgebra n α (coefficient α u ε) (branches f ε) hn (branches_nonzero f ε hf) :=
  (roundedAlgebraEquiv n α u f η hn hf).trans (roundedAlgebraEquiv n α u f ε hn hf).symm

theorem roundedBetween_refl (ε : J → Rˣ) :
    roundedBetween n α u f hn hf ε ε = AlgEquiv.refl (R := R) :=
  (roundedAlgebraEquiv n α u f ε hn hf).self_trans_symm

theorem roundedBetween_trans (ε η θ : J → Rˣ) :
    (roundedBetween n α u f hn hf η θ).trans (roundedBetween n α u f hn hf ε η) =
      roundedBetween n α u f hn hf ε θ :=
  equiv_comparison_trans (roundedAlgebraEquiv n α u f ε hn hf)
    (roundedAlgebraEquiv n α u f η hn hf) (roundedAlgebraEquiv n α u f θ hn hf)

/-- The ENTIRE original raw-to-rounded gauge square commutes with the actual root maps. -/
theorem roundedAlgebraEquiv_comp_rawToRounded :
    (roundedAlgebraEquiv n α u f ε hn hf).toAlgHom.comp
        (rawToRounded n α (coefficient α u ε) (branches f ε) hn (branches_nonzero f ε hf)) =
      (rawToRounded n α u f hn hf).comp (rawEquiv n α u f ε).toAlgHom := by
  apply AdjoinRoot.algHom_ext
  apply Subtype.ext
  change genericEquiv n α u f ε
      (CyclicSectionBaseChange.coefficientMap n
        (coefficient α u ε * ∏ j, branches f ε j ^ α j)
        (algebraMap R (FractionRing R) (coefficient α u ε * ∏ j, branches f ε j ^ α j)) rfl
        (root n (coefficient α u ε * ∏ j, branches f ε j ^ α j))) =
    CyclicSectionBaseChange.coefficientMap n (u * ∏ j, f j ^ α j)
      (algebraMap R (FractionRing R) (u * ∏ j, f j ^ α j)) rfl
      (rawEquiv n α u f ε (root n (coefficient α u ε * ∏ j, branches f ε j ^ α j)))
  rw [CyclicSectionBaseChange.coefficientMap_root, genericEquiv_root, rawEquiv_root,
    CyclicSectionBaseChange.coefficientMap_root]

end EnvelopeProperty.CyclicSectionSNCBranchUnitGauge
