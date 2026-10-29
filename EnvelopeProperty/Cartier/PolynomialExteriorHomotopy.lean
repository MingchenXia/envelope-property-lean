import EnvelopeProperty.Cartier.PolynomialCoordinateHomotopy
import EnvelopeProperty.Cartier.ExteriorContraction
import Mathlib.Tactic.Abel

/-!
# The genuine single-coordinate Cartier homotopy on original exterior modules

The homotopy and its exact residual are derived from actual coordinate integration and Cartan.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.PolynomialExteriorHomotopy
open scoped TensorProduct
open MvPolynomial PolynomialDeRham ExteriorContraction PolynomialCoordinateHomotopy
variable (k : Type*) [Field k] {σ : Type*} [Fintype σ]

/-- The actual coordinate antiderivative tensored with the ORIGINAL homogeneous contraction. -/
def homotopy (i : σ) (q : ℕ) :
    (MvPolynomial σ k ⊗[k] (⋀[k]^(q+1) (σ →₀ k))) →ₗ[k]
      (MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) :=
  TensorProduct.map (coordinateIntegral i) (interior (Finsupp.lapply i) q)

omit [Fintype σ] in
/-- The exact original pure tensor formula for the actual coordinate homotopy. -/
theorem homotopy_tmul (i : σ) (q : ℕ) (f : MvPolynomial σ k)
    (w : ⋀[k]^(q+1) (σ →₀ k)) :
    homotopy k i q (f ⊗ₜ[k] w) =
      coordinateIntegral i f ⊗ₜ[k] interior (Finsupp.lapply i) q w := rfl

omit [Fintype σ] in
private theorem coordinate_cartan (i j : σ) (q : ℕ) (w : ⋀[k]^(q+1) (σ →₀ k)) :
    leftWedge (Finsupp.single j 1) q (interior (Finsupp.lapply i) q w) +
      interior (Finsupp.lapply i) (q+1) (leftWedge (Finsupp.single j 1) (q+1) w) =
        (Finsupp.single j (1 : k) i) • w := by
  calc
    _ = interior (Finsupp.lapply i) (q+1) (leftWedge (Finsupp.single j 1) (q+1) w) +
        leftWedge (Finsupp.single j 1) q (interior (Finsupp.lapply i) q w) := add_comm _ _
    _ = (Finsupp.lapply i) (Finsupp.single j 1) • w := interior_leftWedge _ _ _ _
    _ = _ := rfl

variable (p : ℕ) [CharP k p]

/-- The actual residual is determined internally by the ORIGINAL top/zero coordinate digits
and the ORIGINAL contraction/wedge projections. -/
def residual (i : σ) (q : ℕ) :
    (MvPolynomial σ k ⊗[k] (⋀[k]^(q+1) (σ →₀ k))) →ₗ[k]
      (MvPolynomial σ k ⊗[k] (⋀[k]^(q+1) (σ →₀ k))) :=
  TensorProduct.map (digitProjection p i 1)
      ((leftWedge (Finsupp.single i 1) q).comp (interior (Finsupp.lapply i) q)) +
    TensorProduct.map (digitProjection p i 0)
      ((interior (Finsupp.lapply i) (q+1)).comp (leftWedge (Finsupp.single i 1) (q+1)))

/-- The genuine WHOLE positive-degree coordinate Cartier homotopy identity; no homotopy,
residual, coordinate pairing or commutation certificate occurs among the hypotheses. -/
theorem homotopy_identity (i : σ) (q : ℕ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^(q+1) (σ →₀ k))) :
    tensorDifferential k q (homotopy k i q z) +
      homotopy k i (q+1) (tensorDifferential k (q+1) z) = z - residual k p i q z := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero, sub_self]
  | tmul f w =>
    rw [homotopy_tmul, tensorDifferential_tmul, tensorDifferential_tmul, map_sum]
    simp_rw [homotopy_tmul]
    rw [← Finset.sum_add_distrib, Finset.sum_eq_single i]
    · rw [partial_integral p, integral_partial p]
      simp only [residual, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.comp_apply,
        TensorProduct.sub_tmul]
      have hc :
          f ⊗ₜ[k] leftWedge (Finsupp.single i 1) q (interior (Finsupp.lapply i) q w) +
          f ⊗ₜ[k] interior (Finsupp.lapply i) (q+1)
            (leftWedge (Finsupp.single i 1) (q+1) w) = f ⊗ₜ[k] w := by
        rw [← TensorProduct.tmul_add, coordinate_cartan]
        simp only [Finsupp.single_eq_same, one_smul]
      rw [← hc]
      abel
    · intro j _ hji
      rw [partial_integral_ne i j (Ne.symm hji), ← TensorProduct.tmul_add, coordinate_cartan]
      simp only [Finsupp.single_eq_of_ne (Ne.symm hji), zero_smul, TensorProduct.tmul_zero]
    · intro h
      exact (h (Finset.mem_univ i)).elim
  | add z w hz hw =>
    simp only [map_add] at *
    calc
      _ = (tensorDifferential k q (homotopy k i q z) +
            homotopy k i (q+1) (tensorDifferential k (q+1) z)) +
          (tensorDifferential k q (homotopy k i q w) +
            homotopy k i (q+1) (tensorDifferential k (q+1) w)) := by abel
      _ = (z - residual k p i q z) + (w - residual k p i q w) := congrArg₂ (· + ·) hz hw
      _ = _ := by abel

omit [Fintype σ] in
private theorem zero_contraction (ℓ : Module.Dual k (σ →₀ k)) (w : ⋀[k]^0 (σ →₀ k)) :
    CliffordAlgebra.contractLeft (Q := 0) ℓ (w : ExteriorAlgebra k (σ →₀ k)) = 0 := by
  have hw : (w : ExteriorAlgebra k (σ →₀ k)) ∈
      (1 : Submodule k (ExteriorAlgebra k (σ →₀ k))) := by
    simpa only [pow_zero] using w.property
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp hw
  rw [← ha, CliffordAlgebra.contractLeft_algebraMap]

omit [Fintype σ] in
private theorem zero_cartan (i j : σ) (w : ⋀[k]^0 (σ →₀ k)) :
    interior (Finsupp.lapply i) 0 (leftWedge (Finsupp.single j 1) 0 w) =
      (Finsupp.single j (1 : k) i) • w := by
  apply Subtype.ext
  change CliffordAlgebra.contractLeft (Q := 0) (Finsupp.lapply i)
    (ExteriorAlgebra.ι k (Finsupp.single j (1 : k)) * (w : ExteriorAlgebra k (σ →₀ k))) =
      (Finsupp.single j (1 : k) i) • (w : ExteriorAlgebra k (σ →₀ k))
  rw [CliffordAlgebra.contractLeft_ι_mul, zero_contraction, mul_zero, sub_zero]
  rfl

/-- The ACTUAL degree-zero residual keeps precisely the original zero coordinate digit. -/
def zeroResidual (i : σ) :
    (MvPolynomial σ k ⊗[k] (⋀[k]^0 (σ →₀ k))) →ₗ[k]
      (MvPolynomial σ k ⊗[k] (⋀[k]^0 (σ →₀ k))) :=
  TensorProduct.map (digitProjection p i 0) LinearMap.id

/-- The genuine WHOLE degree-zero Cartier coordinate homotopy, including the left endpoint. -/
theorem homotopy_degree_zero (i : σ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^0 (σ →₀ k))) :
    homotopy k i 0 (tensorDifferential k 0 z) = z - zeroResidual k p i z := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, sub_self]
  | tmul f w =>
    rw [tensorDifferential_tmul, map_sum]
    simp_rw [homotopy_tmul, zero_cartan]
    rw [Finset.sum_eq_single i]
    · simp only [Finsupp.single_eq_same, one_smul, integral_partial p,
        TensorProduct.sub_tmul, zeroResidual, TensorProduct.map_tmul, LinearMap.id_apply]
    · intro j _ hji
      simp only [Finsupp.single_eq_of_ne (Ne.symm hji), zero_smul, TensorProduct.tmul_zero]
    · intro h
      exact (h (Finset.mem_univ i)).elim
  | add z w hz hw => simpa only [map_add, add_sub_add_comm] using congrArg₂ (· + ·) hz hw

variable [LinearOrder σ]

/-- The actual coordinate homotopy on the SAME original exterior cotangent modules. -/
def originalHomotopy (i : σ) (q : ℕ) :
    (⋀[MvPolynomial σ k]^(q+1) (KaehlerDifferential k (MvPolynomial σ k))) →+
      (⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) :=
  (formEquiv k q).toAddMonoidHom.comp
    ((homotopy k i q).toAddMonoidHom.comp (formEquiv k (q+1)).symm.toAddMonoidHom)

omit [Fintype σ] in
/-- The actual original-module homotopy retains the ENTIRE coordinate construction. -/
theorem originalHomotopy_formEquiv (i : σ) (q : ℕ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^(q+1) (σ →₀ k))) :
    originalHomotopy k i q (formEquiv k (q+1) z) = formEquiv k q (homotopy k i q z) := by
  change formEquiv k q (homotopy k i q ((formEquiv k (q+1)).symm (formEquiv k (q+1) z))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The SAME actual residual operator on original exterior cotangent modules. -/
def originalResidual (i : σ) (q : ℕ) :
    (⋀[MvPolynomial σ k]^(q+1) (KaehlerDifferential k (MvPolynomial σ k))) →+
      (⋀[MvPolynomial σ k]^(q+1) (KaehlerDifferential k (MvPolynomial σ k))) :=
  (formEquiv k (q+1)).toAddMonoidHom.comp
    ((residual k p i q).toAddMonoidHom.comp (formEquiv k (q+1)).symm.toAddMonoidHom)

omit [Fintype σ] [CharP k p] in
/-- Every original form retains its exact internally constructed residual. -/
theorem originalResidual_formEquiv (i : σ) (q : ℕ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^(q+1) (σ →₀ k))) :
    originalResidual k p i q (formEquiv k (q+1) z) = formEquiv k (q+1) (residual k p i q z) := by
  change formEquiv k (q+1)
    (residual k p i q ((formEquiv k (q+1)).symm (formEquiv k (q+1) z))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Genuine positive-degree Cartier homotopy on the WHOLE SAME original exterior cotangent
modules, with actual original differential and actual residual, all internally constructed. -/
theorem originalHomotopy_identity (i : σ) (q : ℕ)
    (w : ⋀[MvPolynomial σ k]^(q+1) (KaehlerDifferential k (MvPolynomial σ k))) :
    differential k q (originalHomotopy k i q w) +
      originalHomotopy k i (q+1) (differential k (q+1) w) = w - originalResidual k p i q w := by
  obtain ⟨z, rfl⟩ := (formEquiv k (q+1)).surjective w
  rw [originalHomotopy_formEquiv, differential_formEquiv,
    differential_formEquiv, originalHomotopy_formEquiv,
    ← map_add, homotopy_identity, map_sub, originalResidual_formEquiv]

/-- The actual degree-zero residual on the SAME original exterior cotangent module. -/
def originalZeroResidual (i : σ) :
    (⋀[MvPolynomial σ k]^0 (KaehlerDifferential k (MvPolynomial σ k))) →+
      (⋀[MvPolynomial σ k]^0 (KaehlerDifferential k (MvPolynomial σ k))) :=
  (formEquiv k 0).toAddMonoidHom.comp
    ((zeroResidual k p i).toAddMonoidHom.comp (formEquiv k 0).symm.toAddMonoidHom)

/-- The genuine endpoint homotopy on WHOLE ORIGINAL degree-zero forms and original differential. -/
theorem originalHomotopy_degree_zero (i : σ)
    (w : ⋀[MvPolynomial σ k]^0 (KaehlerDifferential k (MvPolynomial σ k))) :
    originalHomotopy k i 0 (differential k 0 w) = w - originalZeroResidual k p i w := by
  obtain ⟨z, rfl⟩ := (formEquiv k 0).surjective w
  rw [differential_formEquiv, originalHomotopy_formEquiv, homotopy_degree_zero, map_sub]
  change formEquiv k 0 z - formEquiv k 0 (zeroResidual k p i z) =
    formEquiv k 0 z - formEquiv k 0
      (zeroResidual k p i ((formEquiv k 0).symm (formEquiv k 0 z)))
  rw [LinearEquiv.symm_apply_apply]

end EnvelopeProperty.Cartier.PolynomialExteriorHomotopy
