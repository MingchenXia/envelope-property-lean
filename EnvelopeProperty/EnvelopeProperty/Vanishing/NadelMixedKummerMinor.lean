import EnvelopeProperty.Vanishing.NadelMixedKummerJacobian

/-! # The genuine mixed SNC root Jacobian has an actual unit minor

The entire original finite root family is used at every actual residue point.
The old-coordinate and original-root pivots are constructed internally.
-/

noncomputable section
universe u
open scoped Classical
namespace EnvelopeProperty.Vanishing.NadelMixedKummer.MixedJacobian
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {n q : ℕ} (x : Fin n → R) (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
  (A : Set (Fin q)) (σ : A ↪ Fin n) (u : Fin q → Rˣ)
  {K : Type u} [Field K] (N : Fin q → ℕ)
  (φ : Ring N (mixedCoefficient x A σ u) →+* K)

local notation "c" => mixedCoefficient x A σ u
local notation "b" => branch x A σ u N φ
local notation "M" => minor x hx A σ u N φ

/-- The ACTUAL selected minor has branch diagonal and nonbranch root diagonal
blocks; variable-unit derivatives remain in its genuine lower-left block. -/
theorem minor_blocks : (M).submatrix (Equiv.sumCompl b) (Equiv.sumCompl b) =
    Matrix.fromBlocks
      (Matrix.diagonal (fun i : {i // b i} => -baseResidue N c φ (u i : R))) 0
      (fun i : {i // ¬b i} => fun j : {j // b j} => minor x hx A σ u N φ i j)
      (Matrix.diagonal (fun i : {i // ¬b i} =>
        (N i : K) * rootResidue N c φ i ^ (N i - 1))) := by
  classical
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · change minor x hx A σ u N φ i j =
      if i = j then -baseResidue N c φ (u i : R) else 0
    simpa only [Subtype.ext_iff] using minor_branch x hx A σ u N φ i i.property j
  · change minor x hx A σ u N φ i j = 0
    exact (minor_branch x hx A σ u N φ i i.property j).trans
      (if_neg (show (i : Fin q) ≠ j from fun h => j.property (h ▸ i.property)))
  · rfl
  · change minor x hx A σ u N φ i j =
      if i = j then (N i : K) * rootResidue N c φ i ^ (N i - 1) else 0
    simpa only [Subtype.ext_iff] using minor_nonbranch_column x hx A σ u N φ i j j.property

/-- The determinant of the internally selected genuine minor is a unit,
using the ORIGINAL degree tameness and the ORIGINAL coordinate injection. -/
theorem minor_det_isUnit (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : R)) :
    IsUnit (M).det := by
  classical
  have he := Matrix.det_submatrix_equiv_self (Equiv.sumCompl b) M
  rw [minor_blocks x hx A σ u N φ] at he
  have hd := Matrix.det_fromBlocks_zero₁₂
    (Matrix.diagonal (fun i : {i // b i} => -baseResidue N c φ (u i : R)))
    (fun i : {i // ¬b i} => fun j : {j // b j} => minor x hx A σ u N φ i j)
    (Matrix.diagonal (fun i : {i // ¬b i} =>
      (N i : K) * rootResidue N c φ i ^ (N i - 1)))
  rw [Matrix.det_diagonal, Matrix.det_diagonal] at hd
  rw [← he, hd]
  apply IsUnit.mul
  · apply IsUnit.prod_univ_iff.mpr
    intro i
    exact ((u i).isUnit.map (baseResidue N c φ)).neg
  · apply IsUnit.prod_univ_iff.mpr
    intro i
    exact rootDiagonal_isUnit N c φ hN htame i i.property

/-- The ACTUAL full original relation Jacobian has a q-column unit minor.
Both the columns and their injectivity are internally produced. -/
theorem exists_unit_minor (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : R)) :
    ∃ p : Fin q ↪ (Fin n ⊕ Fin q),
      IsUnit ((residueJacobian x hx N c φ).submatrix id p).det :=
  ⟨⟨pivot x A σ u N φ, pivot_injective x A σ u N φ⟩,
    minor_det_isUnit x hx A σ u N φ hN htame⟩

end EnvelopeProperty.Vanishing.NadelMixedKummer.MixedJacobian
