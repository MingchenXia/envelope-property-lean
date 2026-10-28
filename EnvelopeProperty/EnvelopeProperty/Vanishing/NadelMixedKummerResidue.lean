import EnvelopeProperty.Vanishing.NadelMixedKummerPresentation

/-! # Genuine mixed Kummer residue Jacobians

Each matrix entry is the image of an ACTUAL derivation of an ACTUAL original
relation in the whole quotient. Arbitrary original variable units are retained.
-/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelMixedKummer
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {n q : ℕ} (x : Fin n → R) (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)

/-- The ORIGINAL mixed branch coefficients: distinct original coordinates
multiplied by actual original units, and entire original unit factors elsewhere. -/
def mixedCoefficient (A : Set (Fin q)) (σ : A ↪ Fin n) (u : Fin q → Rˣ) (i : Fin q) : R := by
  classical
  exact if hi : i ∈ A then (u i : R) * x (σ ⟨i, hi⟩) else (u i : R)

variable {K : Type u} [Field K] (N : Fin q → ℕ) (c : Fin q → R) (φ : Ring N c →+* K)

/-- The SAME original coefficient map to the actual residue field. -/
abbrev baseResidue : R →+* K := φ.comp (algebraMap R (Ring N c))

/-- Every actual original root at the SAME whole-quotient residue point. -/
abbrev rootResidue (i : Fin q) : K := φ (root N c i)

/-- The original whole quotient relation at the actual residue point. -/
theorem rootResidue_pow (i : Fin q) :
    rootResidue N c φ i ^ N i = baseResidue N c φ (c i) := by
  rw [← map_pow, root_pow]
  rfl

/-- The entire ACTUAL relation Jacobian, evaluated at the original residue
point, on old coordinate derivations and original root-coordinate derivations. -/
def residueJacobian : Matrix (Fin q) (Fin n ⊕ Fin q) K := fun i => Sum.elim
  (fun j => φ (Ideal.Quotient.mk _
    (coefficientDerivation (Char0.etalePartialDeriv x hx j) (relation N c i))))
  (fun j => φ (Ideal.Quotient.mk _ (MvPolynomial.pderiv j (relation N c i))))

/-- Every old-coordinate entry is the actual derivative of the original coefficient. -/
theorem residueJacobian_inl (i : Fin q) (j : Fin n) :
    residueJacobian x hx N c φ i (.inl j) =
      -baseResidue N c φ (Char0.etalePartialDeriv x hx j (c i)) := by
  simp only [residueJacobian, Sum.elim_inl, coefficientDerivation_relation, map_neg]
  rfl

/-- Every root-coordinate entry retains its original degree and original root. -/
theorem residueJacobian_inr (i j : Fin q) :
    residueJacobian x hx N c φ i (.inr j) =
      if i = j then (N i : K) * rootResidue N c φ i ^ (N i - 1) else 0 := by
  classical
  simp only [residueJacobian, Sum.elim_inr, rootDerivation_relation, apply_ite,
    map_mul, map_natCast, map_pow, map_zero]
  split_ifs <;> rfl

/-- A nonbranch original equation has a nonzero actual root at this SAME
residue point, using its positive ORIGINAL degree. -/
theorem rootResidue_ne_zero (hN : ∀ i, 0 < N i) (i : Fin q)
    (hi : baseResidue N c φ (c i) ≠ 0) : rootResidue N c φ i ≠ 0 := by
  intro h
  have he := rootResidue_pow N c φ i
  rw [h, zero_pow (Nat.ne_of_gt (hN i))] at he
  exact hi he.symm

/-- The original tame root-coordinate diagonal is a unit at every nonbranch row. -/
theorem rootDiagonal_isUnit (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : R))
    (i : Fin q) (hi : baseResidue N c φ (c i) ≠ 0) :
    IsUnit ((N i : K) * rootResidue N c φ i ^ (N i - 1)) := by
  apply IsUnit.mul
  · simpa only [map_natCast] using (htame i).map (baseResidue N c φ)
  · exact (isUnit_iff_ne_zero.mpr (rootResidue_ne_zero N c φ hN i hi)).pow _

end EnvelopeProperty.Vanishing.NadelMixedKummer
