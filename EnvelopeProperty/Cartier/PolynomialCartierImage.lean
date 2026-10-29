import EnvelopeProperty.Cartier.PolynomialCartierProjection
import EnvelopeProperty.Cartier.Polynomial
import EnvelopeProperty.Cartier.PolynomialFrobeniusDeRham

/-!
# The genuine Frobenius coefficients of the full original Cartier image

The coefficient roots and residue exponents are constructed on the original polynomial ring.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.PolynomialCartierImage
open scoped Classical TensorProduct
open MvPolynomial PolynomialDeRham PolynomialResidualCoefficients
variable (k : Type*) [Field k] {σ : Type*} [LinearOrder σ] [Fintype σ]
variable (p : ℕ) [hp : Fact p.Prime] [CharP k p] [PerfectRing k p]

/-- The actual Cartier digit belonging to the SAME original exterior basis wedge. -/
def residueDigit (q : ℕ) (s : Set.powersetCard σ q) : Box σ p :=
  fun i => if i ∈ s then ⟨p-1, Nat.sub_lt hp.out.pos (by decide)⟩ else 0

omit [LinearOrder σ] [Fintype σ] in
/-- The full original exponent is p-1 precisely on the original wedge factors. -/
theorem residueDigit_apply (q : ℕ) (s : Set.powersetCard σ q) (i : σ) :
    ((residueDigit (σ := σ) p q s i : Fin p) : ℕ) = if i ∈ s then p-1 else 0 := by
  unfold residueDigit
  split_ifs <;> rfl

omit [LinearOrder σ] in
private theorem residue_condition (q : ℕ) (s : Set.powersetCard σ q)
    (a : Box σ p) (c : σ →₀ ℕ) :
    (∀ i, p ∣ (p • c + a.toFinsupp) i + if i ∈ s then 1 else 0) ↔
      a = residueDigit p q s := by
  constructor
  · intro h
    funext i
    apply Fin.ext
    have ha := (a i).isLt
    have hd : p ∣ (a i : ℕ) + if i ∈ s then 1 else 0 := by
      have hi := h i
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
        Box.toFinsupp_apply, add_assoc] at hi
      exact (Nat.dvd_add_right (dvd_mul_right p (c i))).mp hi
    rw [residueDigit_apply]
    by_cases hi : i ∈ s
    · rw [if_pos hi] at hd ⊢
      have he : (a i : ℕ) + 1 = p :=
        Nat.eq_of_dvd_of_lt_two_mul (by omega) hd (by omega)
      omega
    · rw [if_neg hi, add_zero] at hd
      rw [if_neg hi]
      exact Nat.eq_zero_of_dvd_of_lt hd ha
  · rintro rfl i
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      Box.toFinsupp_apply, residueDigit_apply]
    by_cases hi : i ∈ s
    · rw [if_pos hi, if_pos hi, add_assoc, Nat.sub_add_cancel hp.out.one_le]
      exact dvd_add (dvd_mul_right p (c i)) (dvd_refl p)
    · rw [if_neg hi, if_neg hi, add_zero, add_zero]
      exact dvd_mul_right p (c i)

omit [LinearOrder σ] in
/-- Every original scalar residual is EXACTLY a p-th power times the internally derived
Cartier monomial. The original coefficient root is the genuine native rootPoly, not a witness. -/
theorem scalarResidualList_eq_rootPoly (q : ℕ) (s : Set.powersetCard σ q)
    (f : MvPolynomial σ k) :
    scalarResidualList k p q s Finset.univ.toList f =
      rootPoly p 1 (residueDigit p q s).toFinsupp f ^ p *
        monomial (residueDigit p q s).toFinsupp 1 := by
  induction f using MvPolynomial.induction_on' with
  | monomial d b =>
    obtain ⟨c, a, rfl⟩ := exists_box_smul_add p d
    rw [scalarResidualList_monomial]
    simp only [Finset.mem_toList, Finset.mem_univ, forall_const]
    simp only [residue_condition]
    by_cases ha : a = residueDigit p q s
    · subst a
      rw [if_pos rfl, rootPoly_one_monomial_smul_add, monomial_pow, monomial_mul,
        iterateFrobeniusEquiv_one_symm_pow, mul_one]
    · rw [if_neg ha, rootPoly_monomial_of_ne, zero_pow hp.out.ne_zero, zero_mul]
      intro c' hc
      rw [pow_one] at hc
      exact ha (box_eq_of_smul_add_eq p hc).symm
  | add f g hf hg =>
    rw [map_add, map_add, add_pow_char, add_mul, hf, hg]

/-- The ENTIRE original full residual on EVERY original scalar/basis form has its genuine
Frobenius Cartier coefficient and its SAME original wedge. -/
theorem allResidual_basis_eq_rootPoly (q : ℕ) (s : Set.powersetCard σ q)
    (f : MvPolynomial σ k) :
    allResidual k p q (f ⊗ₜ[k]
      (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s) =
    (rootPoly p 1 (residueDigit p q s).toFinsupp f ^ p *
      monomial (residueDigit p q s).toFinsupp 1) ⊗ₜ[k]
        (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s := by
  rw [allResidual, residualList_basis, scalarResidualList_eq_rootPoly]

/-- The SAME original exterior cotangent basis has exactly the derived Cartier coefficient. -/
theorem originalAllResidual_smul_basis (q : ℕ) (s : Set.powersetCard σ q)
    (f : MvPolynomial σ k) :
    PolynomialCartierProjection.originalAllResidual k p q
      (f • (KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q s) =
    (rootPoly p 1 (residueDigit p q s).toFinsupp f ^ p *
      monomial (residueDigit p q s).toFinsupp 1) •
        (KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q s := by
  rw [← formEquiv_tmul_basis, PolynomialCartierProjection.originalAllResidual_formEquiv,
    allResidual_basis_eq_rootPoly, formEquiv_tmul_basis]

/-- The ACTUAL Frobenius-linear Cartier representative on the original exterior cotangent
module. Its target is the original module with genuine native Frobenius-restricted scalars. -/
def representative (q : ℕ) :
    (⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) →ₗ[MvPolynomial σ k]
      frobeniusModule (σ := σ) k p q :=
  ((KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q).constr (MvPolynomial σ k)
    (fun s => formEquiv k q
      (monomial (residueDigit p q s).toFinsupp 1 ⊗ₜ[k]
        (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s))

omit [PerfectRing k p] in
/-- On EVERY original scalar/basis form the actual representative raises its original
coefficient to the p-th power, with the internally derived Cartier monomial. -/
theorem representative_smul_basis (q : ℕ) (s : Set.powersetCard σ q)
    (f : MvPolynomial σ k) :
    representative k p q
      (f • (KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q s) =
    (f^p * monomial (residueDigit p q s).toFinsupp 1) •
      (KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q s := by
  have hb : representative k p q
      ((KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q s) =
      formEquiv k q (monomial (residueDigit p q s).toFinsupp 1 ⊗ₜ[k]
        (Finsupp.basisSingleOne : Module.Basis σ k (σ →₀ k)).exteriorPower q s) := by
    unfold representative
    exact Module.Basis.constr_basis _ _ _ _
  rw [map_smul, hb]
  change f^p • formEquiv k q _ = _
  rw [formEquiv_tmul_basis, smul_smul]
  rfl

/-- The entire underlying representative is an actual additive map of the SAME original
exterior cotangent module; only its scalar action changed in the native linear target. -/
def originalRepresentative (q : ℕ) :
    (⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) →+
      (⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) where
  toFun := fun w => representative k p q w
  map_zero' := (representative k p q).map_zero
  map_add' := (representative k p q).map_add

omit [PerfectRing k p] in
/-- The entire underlying representative retains every ORIGINAL scalar/basis coefficient. -/
theorem originalRepresentative_smul_basis (q : ℕ) (s : Set.powersetCard σ q)
    (f : MvPolynomial σ k) :
    originalRepresentative k p q
      (f • (KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q s) =
    (f^p * monomial (residueDigit p q s).toFinsupp 1) •
      (KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q s :=
  representative_smul_basis k p q s f

/-- The actual whole coefficient-root operation on the SAME original exterior cotangent
module. Every coefficient is obtained from the original native basis coordinates. -/
def coefficient (q : ℕ) :
    (⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) →+
      (⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) where
  toFun w := ∑ s : Set.powersetCard σ q,
    rootPoly p 1 (residueDigit p q s).toFinsupp
      (((KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q).coord s w) •
        (KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q s
  map_zero' := by simp only [map_zero, zero_smul, Finset.sum_const_zero]
  map_add' w z := by
    simp only [map_add, add_smul, Finset.sum_add_distrib]

/-- Every actual coefficient-root operation retains the SAME original wedge. -/
theorem coefficient_smul_basis (q : ℕ) (s : Set.powersetCard σ q)
    (f : MvPolynomial σ k) :
    coefficient k p q (f • (KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q s) =
      rootPoly p 1 (residueDigit p q s).toFinsupp f •
        (KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q s := by
  change (∑ t : Set.powersetCard σ q, _) = _
  rw [Finset.sum_eq_single s]
  · simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro t _ ht
    simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne ht, smul_eq_mul, mul_zero, map_zero, zero_smul]
  · intro hs
    exact (hs (Finset.mem_univ s)).elim

/-- The whole coefficient construction is an actual left inverse to the original
Frobenius-linear Cartier representative. -/
theorem coefficient_representative (q : ℕ)
    (w : ⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) :
    coefficient k p q (originalRepresentative k p q w) = w := by
  let b := (KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q
  have hsum : ∑ s, b.coord s w • b s = w := b.sum_repr w
  calc
    coefficient k p q (originalRepresentative k p q w) =
        coefficient k p q (originalRepresentative k p q (∑ s, b.coord s w • b s)) := by
      rw [hsum]
    _ = ∑ s, b.coord s w • b s := by
      rw [map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro s _
      change coefficient k p q (originalRepresentative k p q
        (b.coord s w • (KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q s)) = _
      rw [originalRepresentative_smul_basis, coefficient_smul_basis,
        rootPoly_one_pow_mul p (fun i => (residueDigit p q s i).isLt),
        rootPoly_one_monomial_self, mul_one]
    _ = w := hsum

/-- The actual Frobenius-linear Cartier representative is injective on the WHOLE original
exterior cotangent module, including degree zero and all empty basis cases. -/
theorem representative_injective (q : ℕ) : Function.Injective (originalRepresentative (σ := σ) k p q) :=
  Function.LeftInverse.injective (coefficient_representative k p q)

/-- The entire actual Cartier representative of the constructed coefficient is the SAME
original full residual, on EVERY original exterior form. -/
theorem representative_coefficient (q : ℕ)
    (w : ⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) :
    originalRepresentative k p q (coefficient k p q w) =
      PolynomialCartierProjection.originalAllResidual k p q w := by
  change originalRepresentative k p q (∑ s : Set.powersetCard σ q, _) = _
  rw [map_sum]
  simp only [originalRepresentative_smul_basis]
  conv_rhs => rw [← ((KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q).sum_repr w]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact (originalAllResidual_smul_basis k p q s _).symm

/-- Every original Cartier representative is fixed by the ACTUAL full residual. -/
theorem originalRepresentative_fixed (q : ℕ)
    (w : ⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) :
    PolynomialCartierProjection.originalAllResidual k p q
      (originalRepresentative k p q w) = originalRepresentative k p q w := by
  rw [← representative_coefficient, coefficient_representative]

/-- Every ACTUAL Cartier representative is closed for the SAME original differential. -/
theorem originalRepresentative_closed (q : ℕ)
    (w : ⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) :
    differential k q (originalRepresentative k p q w) = 0 := by
  rw [← originalRepresentative_fixed k p q w]
  exact PolynomialCartierProjection.originalAllResidual_closed k p q _

/-- The genuine original Cartier coefficient kills EVERY actual original boundary. -/
theorem coefficient_boundary_zero (q : ℕ)
    (w : ⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) :
    coefficient k p (q+1) (differential k q w) = 0 := by
  apply representative_injective k p (q+1)
  rw [representative_coefficient, map_zero,
    PolynomialCartierProjection.originalAllResidual_boundary_zero]

/-- EVERY original positive-degree cycle has a UNIQUE original Cartier form modulo ACTUAL
original boundaries. Its coefficient and the required original primitive are derived internally. -/
theorem cycle_decomposition (q : ℕ)
    (w : ⋀[MvPolynomial σ k]^(q+1) (KaehlerDifferential k (MvPolynomial σ k)))
    (hw : differential k (q+1) w = 0) :
    ∃! v : ⋀[MvPolynomial σ k]^(q+1) (KaehlerDifferential k (MvPolynomial σ k)),
      ∃ u : ⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k)),
        differential k q u = w - originalRepresentative k p (q+1) v := by
  refine ⟨coefficient k p (q+1) w, ?_, ?_⟩
  · change ∃ u, differential k q u =
      w - originalRepresentative k p (q+1) (coefficient k p (q+1) w)
    rw [representative_coefficient]
    exact PolynomialCartierResiduals.original_exists_primitive_sub_residualList k p
      Finset.univ.toList q w hw
  · intro v hv
    obtain ⟨u, hu⟩ := hv
    have h := congrArg (coefficient k p (q+1)) hu
    rw [coefficient_boundary_zero, map_sub, coefficient_representative] at h
    exact (sub_eq_zero.mp h.symm).symm

/-- The actual degree-zero endpoint has NO incoming boundaries: every ORIGINAL closed
degree-zero form is exactly its genuine Cartier representative. -/
theorem cycle_zero_decomposition
    (w : ⋀[MvPolynomial σ k]^0 (KaehlerDifferential k (MvPolynomial σ k)))
    (hw : differential k 0 w = 0) :
    originalRepresentative k p 0 (coefficient k p 0 w) = w := by
  rw [representative_coefficient]
  exact (PolynomialCartierResiduals.original_eq_residualList_of_closed_zero k p
    Finset.univ.toList w hw).symm

end EnvelopeProperty.Cartier.PolynomialCartierImage
