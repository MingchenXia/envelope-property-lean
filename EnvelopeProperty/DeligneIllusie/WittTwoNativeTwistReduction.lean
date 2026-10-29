import EnvelopeProperty.DeligneIllusie.WittTwoNativeTwistResidue
import EnvelopeProperty.Cartier.FrobeniusLiftDifference

/-!
# Witt Two Native Twist Reduction

Actual prime reductions for the genuine left-copy Witt-two twist. -/

open scoped TensorProduct
noncomputable section
universe u

namespace EnvelopeProperty.DeligneIllusie.WittTwoNativeTwist

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  copyReductionAlgebra copyReductionModule sourceLeftAlgebra sourceLeftModule
  nativeCoefficientAlgebra

local instance copyReductionSMul : SMul (CoefficientCopy p k) k :=
  (copyReductionModule p k).toSMul

private def copyPrime : CoefficientCopy p k →ₗ[CoefficientCopy p k] CoefficientCopy p k :=
  LinearMap.mulLeft (CoefficientCopy p k) (p : CoefficientCopy p k)

private abbrev copyScalarReduction : CoefficientCopy p k →ₗ[CoefficientCopy p k] k :=
  Algebra.linearMap (CoefficientCopy p k) k

omit [CharP k p] in
private theorem copyScalarReduction_surjective :
    Function.Surjective (copyScalarReduction p k) := by
  intro d
  obtain ⟨w, hw⟩ := WittTwo.reduction_surjective p k d
  exact ⟨ULift.up w, hw⟩

private theorem copyScalar_exact [PerfectRing k p] :
    Function.Exact (copyPrime p k) (copyScalarReduction p k) := by
  intro x
  change WittTwo.reduction p k x.down = 0 ↔
    ∃ y : CoefficientCopy p k, (p : CoefficientCopy p k) * y = x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (WittTwo.exists_mul_prime_iff p k x.down).mpr hx
    refine ⟨ULift.up y, ?_⟩
    apply ULift.ext
    exact (mul_comm _ _).trans hy.symm
  · rintro ⟨y, rfl⟩
    change WittTwo.reduction p k ((p : WittTwo.Ring p k) * y.down) = 0
    rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]

local instance sourceLeftSMul : SMul (CoefficientCopy p k) (LiftSource p k A) :=
  (sourceLeftModule p k A).toSMul

private def sourcePrime : LiftSource p k A →ₗ[CoefficientCopy p k] LiftSource p k A :=
  LinearMap.mulLeft (CoefficientCopy p k) (p : LiftSource p k A)

/-- The ordinary residue projection of the genuine LEFT coefficient action. -/
def sourceTensorReduction : LiftSource p k A →ₗ[CoefficientCopy p k] SourceResidue p k A :=
  TensorProduct.mk (CoefficientCopy p k) k (LiftSource p k A) 1

private theorem copyTensor_reduction
    (z : CoefficientCopy p k ⊗[CoefficientCopy p k] LiftSource p k A) :
    (copyScalarReduction p k).rTensor (LiftSource p k A) z =
      sourceTensorReduction p k A (TensorProduct.lid (CoefficientCopy p k) (LiftSource p k A) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul w a =>
    change (copyReduction p k w) ⊗ₜ[CoefficientCopy p k] a =
      (1 : k) ⊗ₜ[CoefficientCopy p k] (w • a)
    rw [Algebra.smul_def]
    have ht := Algebra.TensorProduct.tmul_one_eq_one_tmul
      (R := CoefficientCopy p k) (A := k) (B := LiftSource p k A) w
    change (copyReduction p k w) ⊗ₜ[CoefficientCopy p k] (1 : LiftSource p k A) =
      (1 : k) ⊗ₜ[CoefficientCopy p k]
        (algebraMap (CoefficientCopy p k) (LiftSource p k A) w) at ht
    have hm := congrArg (fun z : SourceResidue p k A =>
      z * ((1 : k) ⊗ₜ[CoefficientCopy p k] a)) ht
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using hm
  | add z w hz hw => simp [hz, hw]

/-- Surjectivity is inherited from actual copied Witt reduction, without smoothness. -/
theorem sourceTensorReduction_surjective : Function.Surjective (sourceTensorReduction p k A) := by
  intro t
  obtain ⟨z, hz⟩ := LinearMap.rTensor_surjective (LiftSource p k A)
    (copyScalarReduction_surjective p k) t
  exact ⟨TensorProduct.lid (CoefficientCopy p k) (LiftSource p k A) z,
    (copyTensor_reduction p k A z).symm.trans hz⟩

/-- Canonical source reduction into the ACTUAL native pushout, not the old residue untwist. -/
def sourceReduction : LiftSource p k A →+* NativeTwist p k A :=
  (nativeResidueEquiv p k A).toRingHom.comp
    (Algebra.TensorProduct.includeRight : LiftSource p k A →ₐ[CoefficientCopy p k]
      SourceResidue p k A).toRingHom

theorem sourceReduction_tmul (w : CoefficientCopy p k) (a : A) :
    sourceReduction p k A (w ⊗ₜ[WittTwo.Ring p k] a) =
      nativeCoefficient p k A (copyReduction p k w) *
        nativeSource p k A (originalReduction p k A a) := by
  change nativeResidueEquiv p k A
    ((1 : k) ⊗ₜ[CoefficientCopy p k] (w ⊗ₜ[WittTwo.Ring p k] a)) = _
  rw [nativeResidueEquiv_tmul, one_mul]

theorem sourceReduction_coefficient (w : CoefficientCopy p k) :
    sourceReduction p k A (algebraMap (CoefficientCopy p k) (LiftSource p k A) w) =
      nativeCoefficient p k A (copyReduction p k w) := by
  change sourceReduction p k A (w ⊗ₜ[WittTwo.Ring p k] (1 : A)) = _
  rw [sourceReduction_tmul, map_one, map_one, mul_one]

theorem sourceReduction_surjective : Function.Surjective (sourceReduction p k A) :=
  (nativeResidueEquiv p k A).surjective.comp (sourceTensorReduction_surjective p k A)

variable [Algebra.Smooth (WittTwo.Ring p k) A]

/-- Smooth base change uses the actual genuine LEFT W' action. -/
theorem source_smooth : Algebra.Smooth (CoefficientCopy p k) (LiftSource p k A) :=
  inferInstanceAs (Algebra.Smooth (CoefficientCopy p k)
    (CoefficientCopy p k ⊗[WittTwo.Ring p k] A))

variable [PerfectRing k p]

private theorem sourceTensorReduction_exact :
    Function.Exact (sourcePrime p k A) (sourceTensorReduction p k A) := by
  let := source_smooth p k A
  have ht := Module.Flat.rTensor_exact (LiftSource p k A) (copyScalar_exact p k)
  let e := TensorProduct.lid (CoefficientCopy p k) (LiftSource p k A)
  intro x
  constructor
  · intro hx
    have hz : (copyScalarReduction p k).rTensor (LiftSource p k A) (e.symm x) = 0 := by
      rw [copyTensor_reduction, LinearEquiv.apply_symm_apply]
      exact hx
    obtain ⟨z, hz⟩ := (ht (e.symm x)).mp hz
    refine ⟨e z, ?_⟩
    have he : e ((copyPrime p k).rTensor (LiftSource p k A) z) =
        (p : LiftSource p k A) * e z := by
      clear hz
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul w a =>
        change ((p : CoefficientCopy p k) * w) • a =
          (p : LiftSource p k A) * (w • a)
        simp only [Algebra.smul_def, map_mul, map_natCast, mul_assoc]
      | add z w hz hw => simp [hz, hw, mul_add]
    change (p : LiftSource p k A) * e z = x
    rw [← he, hz, LinearEquiv.apply_symm_apply]
  · rintro ⟨y, rfl⟩
    change (Algebra.TensorProduct.includeRight : LiftSource p k A →ₐ[CoefficientCopy p k]
      SourceResidue p k A) ((p : LiftSource p k A) * y) = 0
    rw [map_mul, map_natCast]
    have hp : (p : SourceResidue p k A) = 0 := by
      rw [← map_natCast (algebraMap k (SourceResidue p k A)) p,
        CharP.cast_eq_zero, map_zero]
    rw [hp, zero_mul]

/-- The genuine left-coefficient smooth model reduces to the actual native twist. -/
def actualReduction : Cartier.FrobeniusLiftDifference.Reduction p
    (LiftSource p k A) (NativeTwist p k A) where
  map := sourceReduction p k A
  surjective := sourceReduction_surjective p k A
  kernel_iff x := by
    have hzero : sourceReduction p k A x = 0 ↔ sourceTensorReduction p k A x = 0 := by
      change nativeResidueEquiv p k A ((1 : k) ⊗ₜ[CoefficientCopy p k] x) = 0 ↔ _
      exact (nativeResidueEquiv p k A).map_eq_zero_iff
    rw [hzero, sourceTensorReduction_exact p k A x]
    change (∃ y : LiftSource p k A, (p : LiftSource p k A) * y = x) ↔
      ∃ y : LiftSource p k A, (p : LiftSource p k A) * y = x
    rfl

/-- The original smooth W-algebra has its actual flat prime reduction. -/
def actualFlatReduction : Cartier.FrobeniusLiftDifference.FlatReduction p A
    (ResidueAlgebra p k A) where
  map := originalReduction p k A
  surjective := WittTwoResidue.tensorReduction_surjective p k A
  kernel_iff a := by
    have h := WittTwoResidue.tensorReduction_exact p k A a
    change originalReduction p k A a = 0 ↔
      ∃ y : A, ((p : WittTwo.Ring p k) • (LinearMap.id : A →ₗ[WittTwo.Ring p k] A)) y = a at h
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at h
    simpa only [Algebra.smul_def, map_natCast] using h
  p_sq_zero := by
    have h := congrArg (algebraMap (WittTwo.Ring p k) A) (WittTwo.prime_square_zero p k)
    rw [map_pow, map_natCast, map_zero] at h
    simpa only [pow_two] using h
  flat a ha := by
    have hpa : (p : WittTwo.Ring p k) • a = 0 := by
      simpa only [Algebra.smul_def, map_natCast] using ha
    obtain ⟨b, hb⟩ := (WittTwoFlat.prime_smul_eq_zero_iff p k A a).mp hpa
    have hker := (WittTwoResidue.tensorReduction_exact p k A a).mpr ⟨b, hb.symm⟩
    exact hker

end EnvelopeProperty.DeligneIllusie.WittTwoNativeTwist
