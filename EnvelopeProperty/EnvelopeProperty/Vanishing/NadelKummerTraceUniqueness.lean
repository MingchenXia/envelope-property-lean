import EnvelopeProperty.Vanishing.NadelKummerTraceJacobian

/-! # Intrinsic trace normalization determines the actual polynomial counit

The original power-map coefficient action is retained on every functional.
No canonical trace, duality comparison, or vanishing is a supplied conclusion.
-/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelKummerTraceUniqueness

open NadelKummerCover NadelKummerCanonicalTrace NadelKummerTraceJacobian

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] {n : ℕ} (d : Fin n → ℕ)

/-- An actual nonzero base denominator for the original coordinate-power Jacobian. -/
def branchPolynomial : PolynomialRing R n :=
  ∏ j : Fin n, ((d j + 1 : ℕ) : PolynomialRing R n) * MvPolynomial.X j

/-- The product of the actual target coordinates, without selecting any component. -/
def coordinateProduct : PolynomialRing R n := ∏ j : Fin n, MvPolynomial.X j

/-- The actual Jacobian times the whole coordinate product comes from the base. -/
theorem jacobian_mul_coordinateProduct :
    jacobian R d * coordinateProduct R (n := n) = powerMap R d (branchPolynomial R d) := by
  unfold jacobian coordinateProduct branchPolynomial
  rw [← Finset.prod_mul_distrib, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  change (((d j + 1 : ℕ) : PolynomialRing R n) * MvPolynomial.X j ^ d j) *
      MvPolynomial.X j = powerMap R d (((d j + 1 : ℕ) : PolynomialRing R n) * MvPolynomial.X j)
  rw [map_mul, map_natCast]
  change _ = ((d j + 1 : ℕ) : PolynomialRing R n) *
    coordinatePowerHom R (fun i => d i + 1) (MvPolynomial.X j)
  rw [coordinatePowerHom_X, mul_assoc, pow_succ]

variable [IsDomain R] [CharZero R]

/-- The actual base denominator is regular in characteristic zero. -/
theorem branchPolynomial_ne_zero : branchPolynomial R d ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (d j)))
    (MvPolynomial.X_ne_zero j)

/-- The intrinsic trace normalization uniquely determines the whole
coefficient functional for the actual nonidentity scalar algebra. -/
theorem functional_ext_of_trace
    (ℓ₁ ℓ₂ : (ModuleCat.restrictScalars (powerMap R d)).obj
      (ModuleCat.of (PolynomialRing R n) (PolynomialRing R n)) →ₗ[PolynomialRing R n]
        PolynomialRing R n)
    (h₁ : ∀ b, ℓ₁ (jacobian R d * b) = powerTrace R d b)
    (h₂ : ∀ b, ℓ₂ (jacobian R d * b) = powerTrace R d b) : ℓ₁ = ℓ₂ := by
  apply LinearMap.ext
  intro b
  change PolynomialRing R n at b
  have hm₁ := ℓ₁.map_smul (branchPolynomial R d) b
  have hm₂ := ℓ₂.map_smul (branchPolynomial R d) b
  change ℓ₁ (powerMap R d (branchPolynomial R d) * b) = branchPolynomial R d * ℓ₁ b at hm₁
  change ℓ₂ (powerMap R d (branchPolynomial R d) * b) = branchPolynomial R d * ℓ₂ b at hm₂
  have he : ℓ₁ (powerMap R d (branchPolynomial R d) * b) =
      ℓ₂ (powerMap R d (branchPolynomial R d) * b) := by
    rw [← jacobian_mul_coordinateProduct]
    simpa only [mul_assoc] using
      (h₁ (coordinateProduct R (n := n) * b)).trans
        (h₂ (coordinateProduct R (n := n) * b)).symm
  exact mul_left_cancel₀ (branchPolynomial_ne_zero R d) (hm₁.symm.trans (he.trans hm₂))

/-- The unique intrinsic normalization is the actual produced native counit. -/
theorem eq_coefficientMap_of_trace
    (ℓ : (ModuleCat.restrictScalars (powerMap R d)).obj
      (ModuleCat.of (PolynomialRing R n) (PolynomialRing R n)) →ₗ[PolynomialRing R n]
        PolynomialRing R n)
    (h : ∀ b, ℓ (jacobian R d * b) = powerTrace R d b) : ℓ = coefficientMap R d :=
  functional_ext_of_trace R d ℓ (coefficientMap R d) h
    (fun b => (powerTrace_eq_coefficientMap_jacobian R d b).symm)

/-- Native adjunction frames also agree as whole target-algebra-linear maps. -/
theorem coextensionFrame_eq_of_trace
    (ℓ : (ModuleCat.restrictScalars (powerMap R d)).obj
      (ModuleCat.of (PolynomialRing R n) (PolynomialRing R n)) →ₗ[PolynomialRing R n]
        PolynomialRing R n)
    (h : ∀ b, ℓ (jacobian R d * b) = powerTrace R d b) :
    coextensionFrame (powerMap R d) ℓ = powerDualizingMap R d := by
  rw [eq_coefficientMap_of_trace R d ℓ h]
  rfl

end EnvelopeProperty.Vanishing.NadelKummerTraceUniqueness
