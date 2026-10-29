import EnvelopeProperty.Cartier.PolynomialCartierResiduals
import EnvelopeProperty.Cartier.ExteriorCoordinateProjection

/-!
# The exact ORIGINAL coefficients of the full Cartier residual

The original exterior-basis support of the actual residual is DERIVED, not assumed.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.PolynomialResidualCoefficients
open scoped TensorProduct Classical
open MvPolynomial PolynomialDeRham ExteriorContraction PolynomialCoordinateHomotopy
open PolynomialExteriorHomotopy PolynomialCartierResiduals
variable (k : Type*) [Field k] {σ : Type*} [LinearOrder σ]

/-- Actual original L_i I_i selects precisely the original wedges containing i. -/
theorem leftWedge_interior_basis (i : σ) (q : ℕ) (s : Set.powersetCard σ (q+1)) :
    leftWedge (Finsupp.single i 1) q
      (interior (Finsupp.lapply i) q
        ((Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower (q+1) s)) =
    if i ∈ s then (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower (q+1) s else 0 := by
  have h := ExteriorCoordinateProjection.projection_wedge
    (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)) i (q+1) s
  simp only [exteriorPower.basis_apply]
  apply Subtype.ext
  split_ifs with hi
  · rw [if_pos hi] at h
    exact h
  · rw [if_neg hi] at h
    exact h

/-- The actual original complement I_i L_i selects the complementary original wedges. -/
theorem interior_leftWedge_basis (i : σ) (q : ℕ) (s : Set.powersetCard σ (q+1)) :
    interior (Finsupp.lapply i) (q+1)
      (leftWedge (Finsupp.single i 1) (q+1)
        ((Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower (q+1) s)) =
    if i ∈ s then 0 else (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower (q+1) s := by
  have h := ExteriorCoordinateProjection.complement_wedge
    (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)) i (q+1) s
  simp only [exteriorPower.basis_apply]
  apply Subtype.ext
  split_ifs with hi
  · rw [if_pos hi] at h
    exact h
  · rw [if_neg hi] at h
    exact h

variable (p : ℕ)

/-- The actual positive-degree residual preserves the SAME original exterior basis and applies
precisely its internally determined original coordinate residue projector to the whole coefficient. -/
theorem residual_basis (i : σ) (q : ℕ) (s : Set.powersetCard σ (q+1))
    (f : MvPolynomial σ k) :
    residual k p i q (f ⊗ₜ[k]
      (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower (q+1) s) =
    (if i ∈ s then digitProjection p i 1 f else digitProjection p i 0 f) ⊗ₜ[k]
      (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower (q+1) s := by
  simp only [residual, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.comp_apply,
    leftWedge_interior_basis, interior_leftWedge_basis]
  split_ifs with hi
  · rw [TensorProduct.tmul_zero, add_zero]
  · rw [TensorProduct.tmul_zero, zero_add]

/-- The exact WHOLE natural-degree residual formula includes its original degree-zero endpoint. -/
theorem coordinateResidual_basis (i : σ) (q : ℕ) (s : Set.powersetCard σ q)
    (f : MvPolynomial σ k) :
    coordinateResidual k p i q (f ⊗ₜ[k]
      (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s) =
    digitProjection p i (if i ∈ s then 1 else 0) f ⊗ₜ[k]
      (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s := by
  cases q with
  | zero =>
    have hi : i ∉ s := by
      intro h
      have he : s.val = ∅ := Finset.card_eq_zero.mp s.property
      change i ∈ s.val at h
      rw [he] at h
      exact Finset.notMem_empty i h
    rw [if_neg hi]
    rfl
  | succ q =>
    change residual k p i q _ = _
    rw [residual_basis]
    split_ifs <;> rfl

/-- The actual whole scalar residual list for the SAME fixed original exterior basis wedge. -/
def scalarResidualList (q : ℕ) (s : Set.powersetCard σ q) :
    List σ → (MvPolynomial σ k →ₗ[k] MvPolynomial σ k)
  | [] => LinearMap.id
  | i :: l => (scalarResidualList q s l).comp (digitProjection p i (if i ∈ s then 1 else 0))

/-- EVERY actual coordinate iteration retains the SAME original exterior basis and exactly the
internally derived original coefficient operator. -/
theorem residualList_basis (l : List σ) (q : ℕ) (s : Set.powersetCard σ q)
    (f : MvPolynomial σ k) :
    residualList k p l q (f ⊗ₜ[k]
      (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s) =
    scalarResidualList k p q s l f ⊗ₜ[k]
      (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    change residualList k p l q (coordinateResidual k p i q _) = _
    rw [coordinateResidual_basis, ih]
    rfl

omit [LinearOrder σ] in
/-- The actual scalar list retains an original monomial precisely when ALL its original
coordinate Cartier residue tests hold; its coefficient is unchanged. -/
theorem scalarResidualList_monomial (l : List σ) (q : ℕ) (s : Set.powersetCard σ q)
    (d : σ →₀ ℕ) (c : k) :
    scalarResidualList k p q s l (monomial d c) =
    if (∀ i ∈ l, p ∣ d i + if i ∈ s then 1 else 0) then monomial d c else 0 := by
  induction l with
  | nil => simp only [scalarResidualList, LinearMap.id_apply, List.not_mem_nil,
      false_implies, implies_true, if_true]
  | cons i l ih =>
    rw [scalarResidualList, LinearMap.comp_apply, digitProjection_monomial]
    by_cases hi : p ∣ d i + if i ∈ s then 1 else 0
    · rw [if_pos hi, ih]
      simp only [List.forall_mem_cons, hi, true_and]
    · rw [if_neg hi, map_zero]
      simp only [List.forall_mem_cons, hi, false_and, if_false]

/-- The exact original monomial/exterior-basis formula for EVERY actual coordinate list. -/
theorem residualList_monomial_basis (l : List σ) (q : ℕ) (s : Set.powersetCard σ q)
    (d : σ →₀ ℕ) (c : k) :
    residualList k p l q (monomial d c ⊗ₜ[k]
      (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s) =
    if (∀ i ∈ l, p ∣ d i + if i ∈ s then 1 else 0) then
      monomial d c ⊗ₜ[k]
        (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s else 0 := by
  rw [residualList_basis, scalarResidualList_monomial]
  split_ifs
  · rfl
  · simp only [TensorProduct.zero_tmul]

variable [Fintype σ]

/-- The ACTUAL full residual, enumerating ALL original coordinates internally. -/
def allResidual (q : ℕ) :
    (MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) →ₗ[k]
      (MvPolynomial σ k ⊗[k] (⋀[k]^q (σ →₀ k))) :=
  residualList k p (Finset.univ.toList) q

/-- The FULL original coefficient classification: ALL original coordinates are tested, not a
supplied subset or support certificate. The original monomial coefficient and basis are retained. -/
theorem allResidual_monomial_basis (q : ℕ) (s : Set.powersetCard σ q)
    (d : σ →₀ ℕ) (c : k) :
    allResidual k p q (monomial d c ⊗ₜ[k]
      (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s) =
    if (∀ i, p ∣ d i + if i ∈ s then 1 else 0) then
      monomial d c ⊗ₜ[k]
        (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s else 0 := by
  simpa only [allResidual, Finset.mem_toList, Finset.mem_univ, forall_const] using
    residualList_monomial_basis k p (Finset.univ.toList) q s d c

end EnvelopeProperty.Cartier.PolynomialResidualCoefficients
