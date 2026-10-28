import EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniquenessCore
import EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChangeDifferentials
import EnvelopeProperty.Vanishing.NadelKummerTraceUniqueness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.RingHom.Flat

/-! # Intrinsic trace uniquely determines the actual flat-base-changed dual frame

The new coefficient ring may be disconnected or zero.  Its required
regularity is produced from actual flatness, never supplied as a certificate.
-/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniqueness

open CategoryTheory ModuleCat NadelKummerCanonicalTrace NadelKummerCanonicalBaseChange
open NadelKummerTraceJacobian NadelKummerTraceUniqueness NadelKummerCover
open scoped TensorProduct

section Coefficient
variable (R : Type u) [CommRing R] [Nontrivial R] {n : ℕ} (d : Fin n → ℕ)
    (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)

/-- The native trace for the actual left tensor inclusion, with its original scalar action. -/
def baseChangeTrace (c : powerBaseChangeRing R d S a) : S :=
  letI : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
  Algebra.trace S (powerBaseChangeRing R d S a) c

/-- The actual produced coefficient functional, with its native restricted scalar domain. -/
def coefficientFunctional :
    (restrictScalars (powerBaseChangeLeft R d S a)).obj
      (ModuleCat.of (powerBaseChangeRing R d S a) (powerBaseChangeRing R d S a)) →ₗ[S] S :=
  ((restrictScalars (powerBaseChangeLeft R d S a)).map (powerBaseChangeIso R d S a).hom ≫
    (restrictCoextendScalarsAdj (powerBaseChangeLeft R d S a)).counit.app
      (ModuleCat.of S S)).hom

/-- The native produced functional equals the frozen actual extended coefficient on every element. -/
theorem coefficientFunctional_apply (c : powerBaseChangeRing R d S a) :
    coefficientFunctional R d S a c = powerBaseChangeCoefficient R d S a c :=
  powerBaseChangeIso_counit R d S a c

/-- The native trace on every actual original pure tensor. -/
theorem baseChangeTrace_tensor (s : S) (b : PolynomialRing R n) :
    baseChangeTrace R d S a (powerBaseChangeTensor R d S a s b) =
      s * a (powerTrace R d b) := by
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
  let : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
  let : Module.Free (PolynomialRing R n) (PolynomialRing R n) := coordinatePowerHom_free R d
  let : Module.Finite (PolynomialRing R n) (PolynomialRing R n) := coordinatePowerHom_finite_of_basis R d
  unfold baseChangeTrace
  change @Algebra.trace S (S ⊗[PolynomialRing R n] PolynomialRing R n) _ _
    (algebraMap S (S ⊗[PolynomialRing R n] PolynomialRing R n)).toAlgebra (s ⊗ₜ[PolynomialRing R n] b) = _
  rw [toAlgebra_algebraMap]
  exact trace_tmul (A := PolynomialRing R n) s b

/-- The whole intrinsic trace is the actual coefficient functional evaluated against the actual Jacobian. -/
theorem baseChangeTrace_eq_coefficient_jacobian (c : powerBaseChangeRing R d S a) :
    baseChangeTrace R d S a c =
      coefficientFunctional R d S a (powerBaseChangeRight R d S a (jacobian R d) * c) := by
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
  let : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
  let : Module.Free (PolynomialRing R n) (PolynomialRing R n) := coordinatePowerHom_free R d
  let : Module.Finite (PolynomialRing R n) (PolynomialRing R n) := coordinatePowerHom_finite_of_basis R d
  rw [coefficientFunctional_apply]
  unfold baseChangeTrace
  change @Algebra.trace S (S ⊗[PolynomialRing R n] PolynomialRing R n) _ _
    (algebraMap S (S ⊗[PolynomialRing R n] PolynomialRing R n)).toAlgebra c = _
  rw [toAlgebra_algebraMap]
  exact trace_eq_extended_coefficient (polynomialCoefficient R d) (jacobian R d)
    (fun b => powerTrace_eq_coefficientMap_jacobian R d b) c

omit [Nontrivial R] in
/-- The actual Jacobian denominator identity in the actual tensor algebra. -/
theorem jacobian_mul_coordinateProduct_baseChange :
    powerBaseChangeRight R d S a (jacobian R d) *
        powerBaseChangeRight R d S a (coordinateProduct R (n := n)) =
      powerBaseChangeLeft R d S a (a (branchPolynomial R d)) := by
  rw [← map_mul, jacobian_mul_coordinateProduct]
  exact (RingHom.congr_fun (powerBaseChange_square R d S a) (branchPolynomial R d)).symm

end Coefficient

section Domain
variable (R : Type u) [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (d : Fin n → ℕ)
    (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)

/-- Actual flatness produces regularity over the whole new coefficient ring, even when disconnected. -/
theorem branchPolynomial_baseChange_regular (ha : a.Flat) :
    IsSMulRegular S (a (branchPolynomial R d)) := by
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : Module.Flat (PolynomialRing R n) S := ha
  exact (IsRegular.of_ne_zero (branchPolynomial_ne_zero R d)).left.isSMulRegular.of_flat

/-- Intrinsic native trace normalization determines the whole functional over the actual flat tensor algebra. -/
theorem functional_ext_of_trace (ha : a.Flat)
    (ℓ₁ ℓ₂ : (restrictScalars (powerBaseChangeLeft R d S a)).obj
      (ModuleCat.of (powerBaseChangeRing R d S a) (powerBaseChangeRing R d S a)) →ₗ[S] S)
    (h₁ : ∀ c, ℓ₁ (powerBaseChangeRight R d S a (jacobian R d) * c) =
      baseChangeTrace R d S a c)
    (h₂ : ∀ c, ℓ₂ (powerBaseChangeRight R d S a (jacobian R d) * c) =
      baseChangeTrace R d S a c) : ℓ₁ = ℓ₂ := by
  apply LinearMap.ext
  intro c
  change powerBaseChangeRing R d S a at c
  have hm₁ := ℓ₁.map_smul (a (branchPolynomial R d)) c
  have hm₂ := ℓ₂.map_smul (a (branchPolynomial R d)) c
  change ℓ₁ (powerBaseChangeLeft R d S a (a (branchPolynomial R d)) * c) =
    a (branchPolynomial R d) * ℓ₁ c at hm₁
  change ℓ₂ (powerBaseChangeLeft R d S a (a (branchPolynomial R d)) * c) =
    a (branchPolynomial R d) * ℓ₂ c at hm₂
  have he : ℓ₁ (powerBaseChangeLeft R d S a (a (branchPolynomial R d)) * c) =
      ℓ₂ (powerBaseChangeLeft R d S a (a (branchPolynomial R d)) * c) := by
    have he := (h₁ (powerBaseChangeRight R d S a (coordinateProduct R (n := n)) * c)).trans
      (h₂ (powerBaseChangeRight R d S a (coordinateProduct R (n := n)) * c)).symm
    have hm : powerBaseChangeLeft R d S a (a (branchPolynomial R d)) * c =
        powerBaseChangeRight R d S a (jacobian R d) *
          (powerBaseChangeRight R d S a (coordinateProduct R (n := n)) * c) := by
      rw [← jacobian_mul_coordinateProduct_baseChange, mul_assoc]
    exact (congrArg ℓ₁ hm).trans (he.trans (congrArg ℓ₂ hm).symm)
  exact branchPolynomial_baseChange_regular R d S a ha (hm₁.symm.trans (he.trans hm₂))

/-- The only intrinsically normalized functional is the actual produced coefficient functional. -/
theorem eq_coefficientFunctional_of_trace (ha : a.Flat)
    (ℓ : (restrictScalars (powerBaseChangeLeft R d S a)).obj
      (ModuleCat.of (powerBaseChangeRing R d S a) (powerBaseChangeRing R d S a)) →ₗ[S] S)
    (h : ∀ c, ℓ (powerBaseChangeRight R d S a (jacobian R d) * c) =
      baseChangeTrace R d S a c) : ℓ = coefficientFunctional R d S a :=
  functional_ext_of_trace R d S a ha ℓ (coefficientFunctional R d S a) h
    (fun c => (baseChangeTrace_eq_coefficient_jacobian R d S a c).symm)

/-- Uniqueness also identifies the whole final-algebra-linear native coextension frame. -/
theorem coextensionFrame_eq_of_trace (ha : a.Flat)
    (ℓ : (restrictScalars (powerBaseChangeLeft R d S a)).obj
      (ModuleCat.of (powerBaseChangeRing R d S a) (powerBaseChangeRing R d S a)) →ₗ[S] S)
    (h : ∀ c, ℓ (powerBaseChangeRight R d S a (jacobian R d) * c) =
      baseChangeTrace R d S a c) :
    coextensionFrame (powerBaseChangeLeft R d S a) ℓ = (powerBaseChangeIso R d S a).hom.hom := by
  rw [eq_coefficientFunctional_of_trace R d S a ha ℓ h]
  apply DFunLike.ext
  intro x
  apply (CoextendScalars.equiv (powerBaseChangeLeft R d S a) (ModuleCat.of S S)).injective
  apply LinearMap.ext
  intro y
  change powerBaseChangeRing R d S a at y
  change coextensionFrame (powerBaseChangeLeft R d S a) (coefficientFunctional R d S a) x y =
    (powerBaseChangeIso R d S a).hom x y
  exact (coextensionFrame_apply (powerBaseChangeLeft R d S a)
    (coefficientFunctional R d S a) x y).trans
      ((coefficientFunctional_apply R d S a (y * x)).trans
        (powerBaseChangeIso_apply R d S a x y).symm)

end Domain

end EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniqueness
