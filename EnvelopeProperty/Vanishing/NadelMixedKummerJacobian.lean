import EnvelopeProperty.Vanishing.NadelMixedKummerResidue

/-! # An internally selected genuine unit minor for mixed SNC root equations

At the actual residue point, branch rows select distinct original coordinate
columns; all other rows select their own ORIGINAL root column. The x*du term
vanishes only after the ORIGINAL branch coordinate vanishes at that point.
-/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelMixedKummer
namespace MixedJacobian
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {n q : ℕ} (x : Fin n → R) (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
  (A : Set (Fin q)) (σ : A ↪ Fin n) (u : Fin q → Rˣ)
  {K : Type u} [Field K] (N : Fin q → ℕ)
  (φ : Ring N (mixedCoefficient x A σ u) →+* K)

local notation "c" => mixedCoefficient x A σ u

/-- The actual original coefficient vanishes at this SAME whole-source residue point. -/
def branch (i : Fin q) : Prop := baseResidue N c φ (c i) = 0

/-- A vanishing original coefficient is necessarily an active original branch;
entire unit-root factors cannot be branch rows. -/
theorem branch_mem (i : Fin q) (hi : branch x A σ u N φ i) : i ∈ A := by
  classical
  by_contra h
  have hu : baseResidue N c φ (u i : R) ≠ 0 :=
    ((u i).isUnit.map (baseResidue N c φ)).ne_zero
  apply hu
  simpa only [branch, mixedCoefficient, dif_neg h] using hi

/-- The ORIGINAL coordinate of a branch row actually vanishes at the residue point. -/
theorem branch_coordinate_zero (i : Fin q) (hi : branch x A σ u N φ i) :
    baseResidue N c φ (x (σ ⟨i, branch_mem x A σ u N φ i hi⟩)) = 0 := by
  have he : baseResidue N c φ ((u i : R) *
      x (σ ⟨i, branch_mem x A σ u N φ i hi⟩)) = 0 := by
    simpa only [branch, mixedCoefficient, dif_pos (branch_mem x A σ u N φ i hi)] using hi
  rw [map_mul] at he
  exact (mul_eq_zero.mp he).resolve_left (((u i).isUnit.map (baseResidue N c φ)).ne_zero)

/-- The variable-unit differential term vanishes for the proved geometric
reason x=0 at the SAME point; the actual unit's derivative is never discarded. -/
theorem branch_derivative (i : Fin q) (hi : branch x A σ u N φ i) (j : Fin n) :
    baseResidue N c φ (Char0.etalePartialDeriv x hx j (c i)) =
      baseResidue N c φ (u i : R) *
        (if σ ⟨i, branch_mem x A σ u N φ i hi⟩ = j then 1 else 0) := by
  rw [mixedCoefficient, dif_pos (branch_mem x A σ u N φ i hi),
    branch_coefficient_derivative x hx, map_add, map_mul,
    branch_coordinate_zero x A σ u N φ i hi, zero_mul, zero_add, map_mul]
  split_ifs <;> simp

/-- The actual pivot column is constructed from the original coefficient value. -/
def pivot (i : Fin q) : Fin n ⊕ Fin q := by
  classical
  exact if hi : branch x A σ u N φ i then .inl (σ ⟨i, branch_mem x A σ u N φ i hi⟩)
    else .inr i

/-- All selected columns are distinct, from the actual original SNC injection. -/
theorem pivot_injective : Function.Injective (pivot x A σ u N φ) := by
  classical
  intro i j h
  by_cases hi : branch x A σ u N φ i <;> by_cases hj : branch x A σ u N φ j
  · simp only [pivot, dif_pos hi, dif_pos hj, Sum.inl.injEq] at h
    exact congrArg Subtype.val (σ.injective h)
  · simp only [pivot, dif_pos hi, dif_neg hj, Sum.inl_ne_inr] at h
  · simp only [pivot, dif_neg hi, dif_pos hj, Sum.inr_ne_inl] at h
  · simpa only [pivot, dif_neg hi, dif_neg hj, Sum.inr.injEq] using h

/-- The selected q by q submatrix of the ACTUAL full relation Jacobian. -/
def minor : Matrix (Fin q) (Fin q) K :=
  (residueJacobian x hx N c φ).submatrix id (pivot x A σ u N φ)

/-- Every actual branch row of the selected minor is genuinely diagonal. -/
theorem minor_branch (i : Fin q) (hi : branch x A σ u N φ i) (j : Fin q) :
    minor x hx A σ u N φ i j = if i = j then -baseResidue N c φ (u i : R) else 0 := by
  classical
  by_cases hj : branch x A σ u N φ j
  · change residueJacobian x hx N c φ i (pivot x A σ u N φ j) = _
    rw [pivot, dif_pos hj, residueJacobian_inl, branch_derivative x hx A σ u N φ i hi]
    have he : σ ⟨i, branch_mem x A σ u N φ i hi⟩ =
        σ ⟨j, branch_mem x A σ u N φ j hj⟩ ↔ i = j := by
      constructor
      · intro h
        exact congrArg Subtype.val (σ.injective h)
      · intro h
        subst j
        rfl
    simp only [he]
    split_ifs <;> simp
  · change residueJacobian x hx N c φ i (pivot x A σ u N φ j) = _
    rw [pivot, dif_neg hj, residueJacobian_inr]
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp only [if_neg hij]

/-- Every nonbranch selected root column is the actual original root diagonal. -/
theorem minor_nonbranch_column (i j : Fin q) (hj : ¬branch x A σ u N φ j) :
    minor x hx A σ u N φ i j =
      if i = j then (N i : K) * rootResidue N c φ i ^ (N i - 1) else 0 := by
  change residueJacobian x hx N c φ i (pivot x A σ u N φ j) = _
  rw [pivot, dif_neg hj, residueJacobian_inr]

end MixedJacobian
end EnvelopeProperty.Vanishing.NadelMixedKummer
