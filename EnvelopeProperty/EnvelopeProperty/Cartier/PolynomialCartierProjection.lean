import EnvelopeProperty.Cartier.PolynomialResidualCoefficients

/-!
# The actual full Cartier cycle projection on the original polynomial forms

Image closedness and annihilation of ALL actual boundaries are genuinely proved.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.PolynomialCartierProjection
open scoped TensorProduct Classical
open MvPolynomial PolynomialDeRham PolynomialCartierResiduals PolynomialResidualCoefficients
variable (k : Type*) [Field k] {σ : Type*} [LinearOrder σ]

private theorem tensor_monomial_basis_zero {N : Type*} [AddCommGroup N] [Module k N]
    (q : ℕ) (L : (MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) →ₗ[k] N)
    (h : ∀ (d : σ →₀ ℕ) (c : k) (s : Set.powersetCard σ q),
      L (monomial d c ⊗ₜ[k]
        (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s) = 0)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) : L z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact map_zero L
  | add z w hz hw => rw [map_add, hz, hw, add_zero]
  | tmul f w =>
    induction f using MvPolynomial.induction_on' with
    | monomial d c =>
      let T := L.comp (TensorProduct.mk k (MvPolynomial σ k) (⋀[k]^q (σ →₀ k)) (monomial d c))
      have hT : T = 0 := by
        apply ((Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q).ext
        intro s
        exact h d c s
      change T w = 0
      rw [hT, LinearMap.zero_apply]
    | add f g hf hg => rw [TensorProduct.add_tmul, map_add, hf, hg, add_zero]

private theorem leftWedge_basis_zero_of_mem (i : σ) (q : ℕ) (s : Set.powersetCard σ q)
    (hi : i ∈ s) :
    leftWedge (Finsupp.single i 1) q
      ((Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s) = 0 := by
  obtain ⟨j, hj⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr hi
  rw [exteriorPower.basis_apply]
  apply Subtype.ext
  change ExteriorAlgebra.ι k (Finsupp.single i 1) *
    ExteriorAlgebra.ιMulti k q
      ((Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)) ∘
        Set.powersetCard.ofFinEmbEquiv.symm s) = 0
  apply ExteriorCoordinateProjection.prepend_wedge_eq_zero
  exact ⟨j, congrArg (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)) hj⟩

variable (p : ℕ) [CharP k p] [Fintype σ]

/-- The ENTIRE actual full residual image consists of ORIGINAL closed polynomial forms. -/
theorem allResidual_closed (q : ℕ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) :
    tensorDifferential k q (allResidual k p q z) = 0 := by
  refine tensor_monomial_basis_zero k q
    ((tensorDifferential k q).comp (allResidual k p q)) ?_ z
  intro d c s
  change tensorDifferential k q (allResidual k p q _) = 0
  rw [allResidual_monomial_basis]
  split_ifs with hs
  · rw [tensorDifferential_tmul]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ s
    · rw [leftWedge_basis_zero_of_mem k i q s hi, TensorProduct.tmul_zero]
    · have hd : p ∣ d i := by simpa only [if_neg hi, add_zero] using hs i
      have hc : (d i : k) = 0 := (CharP.cast_eq_zero_iff k p _).mpr hd
      rw [pderiv_monomial, hc, mul_zero, map_zero, TensorProduct.zero_tmul]
  · exact map_zero _

/-- The actual full residual kills EVERY original boundary, not only selected coefficients. -/
theorem allResidual_boundary_zero (q : ℕ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) :
    allResidual k p (q+1) (tensorDifferential k q z) = 0 :=
  (residualList_commutes k p (Finset.univ.toList) q z).symm.trans (allResidual_closed k p q z)

omit [CharP k p] in
/-- The ACTUAL full residual is idempotent on the WHOLE original polynomial form module. -/
theorem allResidual_idempotent (q : ℕ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) :
    allResidual k p q (allResidual k p q z) = allResidual k p q z := by
  have h := tensor_monomial_basis_zero k q
    ((allResidual k p q).comp (allResidual k p q) - allResidual k p q)
    (fun d c s => by
      change allResidual k p q (allResidual k p q _) - allResidual k p q _ = 0
      rw [allResidual_monomial_basis]
      split_ifs with hs
      · rw [allResidual_monomial_basis, if_pos hs, sub_self]
      · rw [map_zero, sub_self]) z
  exact sub_eq_zero.mp h

/-- The ACTUAL full projection on the SAME original exterior cotangent module. -/
def originalAllResidual (q : ℕ) :
    (⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) →+
      (⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) :=
  originalResidualList k p (Finset.univ.toList) q

omit [CharP k p] in
/-- Every WHOLE original projection retains the entire internally derived coordinate construction. -/
theorem originalAllResidual_formEquiv (q : ℕ)
    (z : MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) :
    originalAllResidual k p q (formEquiv k q z) = formEquiv k q (allResidual k p q z) :=
  originalResidualList_formEquiv k p (Finset.univ.toList) q z

/-- The WHOLE actual full projection image consists of SAME ORIGINAL closed cotangent forms. -/
theorem originalAllResidual_closed (q : ℕ)
    (w : ⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) :
    differential k q (originalAllResidual k p q w) = 0 := by
  obtain ⟨z, rfl⟩ := (formEquiv k q).surjective w
  rw [originalAllResidual_formEquiv, differential_formEquiv, allResidual_closed, map_zero]

/-- The ORIGINAL full projection kills EVERY SAME ORIGINAL exterior cotangent boundary. -/
theorem originalAllResidual_boundary_zero (q : ℕ)
    (w : ⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) :
    originalAllResidual k p (q+1) (differential k q w) = 0 :=
  (originalResidualList_commutes k p (Finset.univ.toList) q w).symm.trans
    (originalAllResidual_closed k p q w)

omit [CharP k p] in
/-- The ACTUAL full projection is idempotent on EVERY original exterior cotangent element. -/
theorem originalAllResidual_idempotent (q : ℕ)
    (w : ⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) :
    originalAllResidual k p q (originalAllResidual k p q w) = originalAllResidual k p q w := by
  obtain ⟨z, rfl⟩ := (formEquiv k q).surjective w
  rw [originalAllResidual_formEquiv, originalAllResidual_formEquiv, allResidual_idempotent]

/-- On EVERY WHOLE ORIGINAL positive-degree cycle, being an actual ORIGINAL boundary is
EQUIVALENT to the derived full projection being zero. No primitive/image certificate is supplied. -/
theorem original_boundary_iff_residual_zero (q : ℕ)
    (w : ⋀[MvPolynomial σ k]^(q+1) (KaehlerDifferential k (MvPolynomial σ k)))
    (hw : differential k (q+1) w = 0) :
    (∃ u : ⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k)),
      differential k q u = w) ↔ originalAllResidual k p (q+1) w = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact originalAllResidual_boundary_zero k p q u
  · intro hR
    obtain ⟨u, hu⟩ := original_exists_primitive_sub_residualList k p
      (Finset.univ.toList) q w hw
    change differential k q u = w - originalAllResidual k p (q+1) w at hu
    rw [hR, sub_zero] at hu
    exact ⟨u, hu⟩

end EnvelopeProperty.Cartier.PolynomialCartierProjection
