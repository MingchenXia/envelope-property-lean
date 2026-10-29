import EnvelopeProperty.DeligneIllusie.WittTwoModuleDivision

/-!
# Witt Two Residue

The actual original reduction quotient as the actual residue tensor product. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace EnvelopeProperty.DeligneIllusie.WittTwoResidue

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]

/-- The original Witt first-coordinate ring map supplies the residue algebra. -/
@[instance_reducible] def reductionAlgebra : Algebra (WittTwo.Ring p k) k :=
  (WittTwo.reduction p k).toAlgebra

attribute [local instance] reductionAlgebra

variable (M : Type*) [AddCommGroup M] [Module (WittTwo.Ring p k) M]

/-- Original projection to the actual tensor with the residue field. -/
def tensorReduction : M →ₗ[WittTwo.Ring p k] k ⊗[WittTwo.Ring p k] M :=
  TensorProduct.mk (WittTwo.Ring p k) k M 1

private abbrev scalarReduction : WittTwo.Ring p k →ₗ[WittTwo.Ring p k] k :=
  Algebra.linearMap (WittTwo.Ring p k) k

private theorem scalar_exact : Function.Exact
    (WittTwoFlat.primeSmul p k (WittTwo.Ring p k)) (scalarReduction p k) := by
  intro x
  change WittTwo.reduction p k x = 0 ↔ ∃ y, (p : WittTwo.Ring p k) * y = x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (WittTwo.exists_mul_prime_iff p k x).mpr hx
    exact ⟨y, (mul_comm _ _).trans hy.symm⟩
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

omit [CharP k p] [PerfectRing k p] in
private theorem tensor_reduction (z : WittTwo.Ring p k ⊗[WittTwo.Ring p k] M) :
    (scalarReduction p k).rTensor M z =
      tensorReduction p k M (TensorProduct.lid (WittTwo.Ring p k) M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    change (WittTwo.reduction p k a) ⊗ₜ m = 1 ⊗ₜ (a • m)
    rw [← TensorProduct.smul_tmul]
    congr 1
    change WittTwo.reduction p k a = WittTwo.reduction p k a * 1
    rw [mul_one]
  | add z w hz hw => simp [hz, hw]

omit [CharP k p] [PerfectRing k p] in
/-- The actual tensor reduction is onto, from original surjectivity of the same reduction. -/
theorem tensorReduction_surjective : Function.Surjective (tensorReduction p k M) := by
  intro t
  obtain ⟨z, hz⟩ := LinearMap.rTensor_surjective M
    (show Function.Surjective (scalarReduction p k) from WittTwo.reduction_surjective p k) t
  exact ⟨TensorProduct.lid (WittTwo.Ring p k) M z, (tensor_reduction p k M z).symm.trans hz⟩

variable [Module.Flat (WittTwo.Ring p k) M]

/-- Exactness concerns the SAME original prime multiplication and residue tensor map. -/
theorem tensorReduction_exact : Function.Exact (WittTwoFlat.primeSmul p k M)
    (tensorReduction p k M) := by
  have ht := Module.Flat.rTensor_exact M (scalar_exact p k)
  let e := TensorProduct.lid (WittTwo.Ring p k) M
  intro m
  constructor
  · intro hm
    have hz : (scalarReduction p k).rTensor M (e.symm m) = 0 := by
      rw [tensor_reduction, LinearEquiv.apply_symm_apply]
      exact hm
    obtain ⟨z, hz⟩ := (ht (e.symm m)).mp hz
    refine ⟨e z, ?_⟩
    have h : e ((WittTwoFlat.primeSmul p k (WittTwo.Ring p k)).rTensor M z) =
        (p : WittTwo.Ring p k) • e z := by
      clear hz
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a n => simp [e, WittTwoFlat.primeSmul]
      | add z w hz hw => simp [hz, hw, smul_add]
    change (p : WittTwo.Ring p k) • e z = m
    rw [← h, hz, LinearEquiv.apply_symm_apply]
  · rintro ⟨n, rfl⟩
    change (1 : k) ⊗ₜ ((p : WittTwo.Ring p k) • n) = 0
    rw [← TensorProduct.smul_tmul]
    have h : (p : WittTwo.Ring p k) • (1 : k) = 0 := by
      change WittTwo.reduction p k p * 1 = 0
      rw [map_natCast, CharP.cast_eq_zero, zero_mul]
    rw [h, TensorProduct.zero_tmul]

/-- The original module quotient is the actual tensor with the original residue field. -/
def reductionTensorEquiv : WittTwoModuleDivision.Reduction p k M ≃ₗ[WittTwo.Ring p k]
    k ⊗[WittTwo.Ring p k] M :=
  (Submodule.quotEquivOfEq _ _ (tensorReduction_exact p k M).linearMap_ker_eq.symm).trans
    ((tensorReduction p k M).quotKerEquivOfSurjective (tensorReduction_surjective p k M))

/-- Every original quotient class retains its original pure tensor value. -/
theorem reductionTensorEquiv_mk (m : M) :
    reductionTensorEquiv p k M ((WittTwoModuleDivision.primeSubmodule p k M).mkQ m) =
      (1 : k) ⊗ₜ m := by
  change (tensorReduction p k M).quotKerEquivOfSurjective
      (tensorReduction_surjective p k M) (Submodule.Quotient.mk m) = _
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- Actual canonical division takes values in the actual original residue tensor. -/
def dividePrimeTensorEquiv : WittTwoModuleDivision.primeSubmodule p k M ≃ₗ[WittTwo.Ring p k]
    k ⊗[WittTwo.Ring p k] M :=
  (WittTwoModuleDivision.dividePrimeEquiv p k M).trans (reductionTensorEquiv p k M)

/-- The same divided tensor map has the original value on every prime multiple. -/
theorem dividePrimeTensorEquiv_primeMultiple (m : M) :
    dividePrimeTensorEquiv p k M (WittTwoModuleDivision.primeMultiple p k M m) =
      (1 : k) ⊗ₜ m := by
  rw [dividePrimeTensorEquiv, LinearEquiv.trans_apply,
    WittTwoModuleDivision.dividePrime_primeMultiple, reductionTensorEquiv_mk]

end EnvelopeProperty.DeligneIllusie.WittTwoResidue
