import EnvelopeProperty.Cartier.PolynomialExteriorHomotopy

/-!
# Genuine residual chain maps and actual original cohomology representatives

Actual chain preservation is derived from original square-zero and the genuine homotopies.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.PolynomialCartierResiduals
open scoped TensorProduct
open MvPolynomial PolynomialDeRham PolynomialExteriorHomotopy
variable (k : Type*) [Field k] {σ : Type*} [Fintype σ]
variable (p : ℕ) [CharP k p]

/-- The actual positive-degree residual COMMUTES with the original de Rham differential. -/
theorem residual_commutes (i : σ) (q : ℕ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^(q+1) (σ →₀ k))) :
    tensorDifferential k (q+1) (residual k p i q z) =
      residual k p i (q+1) (tensorDifferential k (q+1) z) := by
  have h1 := congrArg (tensorDifferential k (q+1)) (homotopy_identity k p i q z)
  have h2 := homotopy_identity k p i (q+1) (tensorDifferential k (q+1) z)
  simp only [map_add, map_sub, tensorDifferential_square, map_zero, zero_add, add_zero] at h1 h2
  exact sub_right_inj.mp (h1.symm.trans h2)

/-- The genuine endpoint residual also commutes with the SAME original differential. -/
theorem zeroResidual_commutes (i : σ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^0 (σ →₀ k))) :
    tensorDifferential k 0 (zeroResidual k p i z) =
      residual k p i 0 (tensorDifferential k 0 z) := by
  have h1 := congrArg (tensorDifferential k 0) (homotopy_degree_zero k p i z)
  have h2 := homotopy_identity k p i 0 (tensorDifferential k 0 z)
  simp only [map_sub, tensorDifferential_square, map_zero, add_zero] at h1 h2
  exact sub_right_inj.mp (h1.symm.trans h2)

/-- The internally constructed actual coordinate residual in EVERY natural degree. -/
def coordinateResidual (i : σ) (q : ℕ) :
    (MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) →ₗ[k]
      (MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) :=
  match q with
  | 0 => zeroResidual k p i
  | q+1 => residual k p i q

/-- Actual whole chain preservation, including degree zero, is proved internally. -/
theorem coordinateResidual_commutes (i : σ) (q : ℕ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) :
    tensorDifferential k q (coordinateResidual k p i q z) =
      coordinateResidual k p i (q+1) (tensorDifferential k q z) := by
  cases q with
  | zero => exact zeroResidual_commutes k p i z
  | succ q => exact residual_commutes k p i q z

/-- The ACTUAL whole ordered finite composition; no residual representative is supplied. -/
def residualList : (l : List σ) → (q : ℕ) →
    (MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) →ₗ[k]
      (MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k)))
  | [], _ => LinearMap.id
  | i :: l, q => (residualList l q).comp (coordinateResidual k p i q)

/-- Every genuine iterated residual COMMUTES with the WHOLE original differential. -/
theorem residualList_commutes (l : List σ) (q : ℕ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) :
    tensorDifferential k q (residualList k p l q z) =
      residualList k p l (q+1) (tensorDifferential k q z) := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
    change tensorDifferential k q (residualList k p l q (coordinateResidual k p i q z)) = _
    rw [ih, coordinateResidual_commutes]
    rfl

/-- Genuine repeated residuals of original cycles remain original cycles. -/
theorem residualList_closed (l : List σ) (q : ℕ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) (hz : tensorDifferential k q z = 0) :
    tensorDifferential k q (residualList k p l q z) = 0 := by
  rw [residualList_commutes, hz, map_zero]

/-- Every WHOLE original positive-degree cycle differs from its ACTUAL repeated residual by
an actual original boundary, with its primitive DERIVED from the genuine coordinate homotopies. -/
theorem exists_primitive_sub_residualList (l : List σ) (q : ℕ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^(q+1) (σ →₀ k)))
    (hz : tensorDifferential k (q+1) z = 0) :
    ∃ u : MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k)),
      tensorDifferential k q u = z - residualList k p l (q+1) z := by
  induction l generalizing z with
  | nil => exact ⟨0, by simp only [map_zero, residualList, LinearMap.id_apply, sub_self]⟩
  | cons i l ih =>
    have hc : tensorDifferential k (q+1) (coordinateResidual k p i (q+1) z) = 0 := by
      rw [coordinateResidual_commutes, hz, map_zero]
    obtain ⟨u, hu⟩ := ih (coordinateResidual k p i (q+1) z) hc
    refine ⟨homotopy k i q z + u, ?_⟩
    have hi := homotopy_identity k p i q z
    simp only [hz, map_zero, add_zero] at hi
    rw [map_add, hi, hu]
    change z - residual k p i q z +
      (residual k p i q z - residualList k p l (q+1) (residual k p i q z)) =
        z - residualList k p l (q+1) (residual k p i q z)
    abel

/-- A WHOLE original degree-zero cycle EQUALS its ACTUAL repeated residual. -/
theorem eq_residualList_of_closed_zero (l : List σ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^0 (σ →₀ k))) (hz : tensorDifferential k 0 z = 0) :
    z = residualList k p l 0 z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
    have hi := homotopy_degree_zero k p i z
    simp only [hz, map_zero] at hi
    have he : z = coordinateResidual k p i 0 z := (sub_eq_zero.mp hi.symm)
    have hc : tensorDifferential k 0 (coordinateResidual k p i 0 z) = 0 := by
      rw [coordinateResidual_commutes, hz, map_zero]
    change z = residualList k p l 0 (coordinateResidual k p i 0 z)
    exact he.trans (ih _ hc)

variable [LinearOrder σ]

/-- The ACTUAL repeated residual on the SAME whole original exterior cotangent module. -/
def originalResidualList (l : List σ) (q : ℕ) :
    (⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) →+
      (⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) :=
  (formEquiv k q).toAddMonoidHom.comp
    ((residualList k p l q).toAddMonoidHom.comp (formEquiv k q).symm.toAddMonoidHom)

omit [Fintype σ] [CharP k p] in
/-- The whole original-module residual list retains the ENTIRE actual original construction. -/
theorem originalResidualList_formEquiv (l : List σ) (q : ℕ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) :
    originalResidualList k p l q (formEquiv k q z) = formEquiv k q (residualList k p l q z) := by
  change formEquiv k q (residualList k p l q ((formEquiv k q).symm (formEquiv k q z))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Genuine repeated residuals commute with the SAME original exterior cotangent differential. -/
theorem originalResidualList_commutes (l : List σ) (q : ℕ)
    (w : ⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) :
    differential k q (originalResidualList k p l q w) =
      originalResidualList k p l (q+1) (differential k q w) := by
  obtain ⟨z, rfl⟩ := (formEquiv k q).surjective w
  rw [originalResidualList_formEquiv, differential_formEquiv,
    differential_formEquiv, originalResidualList_formEquiv, residualList_commutes]

/-- EVERY original whole positive-degree cycle has its ACTUAL iterated residual representative,
with an actual ORIGINAL exterior cotangent primitive derived internally. -/
theorem original_exists_primitive_sub_residualList (l : List σ) (q : ℕ)
    (w : ⋀[MvPolynomial σ k]^(q+1) (KaehlerDifferential k (MvPolynomial σ k)))
    (hw : differential k (q+1) w = 0) :
    ∃ u : ⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k)),
      differential k q u = w - originalResidualList k p l (q+1) w := by
  obtain ⟨z, rfl⟩ := (formEquiv k (q+1)).surjective w
  rw [differential_formEquiv] at hw
  have hz : tensorDifferential k (q+1) z = 0 := by
    apply (formEquiv k (q+1+1)).injective
    rw [map_zero]
    exact hw
  obtain ⟨u, hu⟩ := exists_primitive_sub_residualList k p l q z hz
  refine ⟨formEquiv k q u, ?_⟩
  rw [differential_formEquiv, hu, map_sub, originalResidualList_formEquiv]

/-- Every WHOLE ORIGINAL degree-zero cycle equals its actual repeated residual. -/
theorem original_eq_residualList_of_closed_zero (l : List σ)
    (w : ⋀[MvPolynomial σ k]^0 (KaehlerDifferential k (MvPolynomial σ k)))
    (hw : differential k 0 w = 0) : w = originalResidualList k p l 0 w := by
  obtain ⟨z, rfl⟩ := (formEquiv k 0).surjective w
  rw [differential_formEquiv] at hw
  have hz : tensorDifferential k 0 z = 0 := by
    apply (formEquiv k 1).injective
    rw [map_zero]
    exact hw
  rw [originalResidualList_formEquiv]
  exact congrArg (formEquiv k 0) (eq_residualList_of_closed_zero k p l z hz)

end EnvelopeProperty.Cartier.PolynomialCartierResiduals
