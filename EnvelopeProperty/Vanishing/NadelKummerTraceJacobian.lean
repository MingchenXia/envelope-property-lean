import EnvelopeProperty.Vanishing.NadelKummerTraceJacobianTower
import EnvelopeProperty.Vanishing.NadelKummerCanonicalTrace
import Mathlib.RingTheory.Trace.Basic

/-! # The whole native coordinate-power trace and its actual Jacobian

The scalar algebra for the trace is the literal coordinate-power map,
including when its source and target polynomial rings share a carrier.
-/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelKummerTraceJacobian

open CategoryTheory Module NadelKummerCover NadelFiniteDualityTower
open NadelKummerCanonicalTrace NadelKummerTraceJacobianTower

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] [Nontrivial R] {n : ℕ} (d : Fin n → ℕ)

/-- The original positive coordinate degrees N_j=d_j+1 give this actual
Jacobian product in the target polynomial coordinates. -/
def jacobian : PolynomialRing R n :=
  ∏ j : Fin n, ((d j + 1 : ℕ) : PolynomialRing R n) * MvPolynomial.X j ^ d j

/-- Native algebra trace with the ORIGINAL power-map scalar structure. -/
def powerTrace (b : PolynomialRing R n) : PolynomialRing R n :=
  letI : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
  Algebra.trace (PolynomialRing R n) (PolynomialRing R n) b

omit [Nontrivial R] in
/-- The original coordinate-power map has its actual native diagonal
Kähler differential, with the same positive degree N_j=d_j+1. -/
theorem differential_power_X (j : Fin n) :
    KaehlerDifferential.D R (PolynomialRing R n)
        (coordinatePowerHom R (fun i => d i + 1) (MvPolynomial.X j)) =
      (((d j + 1 : ℕ) : PolynomialRing R n) * MvPolynomial.X j ^ d j) •
        KaehlerDifferential.D R (PolynomialRing R n) (MvPolynomial.X j) := by
  rw [coordinatePowerHom_X, Derivation.leibniz_pow, Nat.add_sub_cancel]
  rw [← Nat.cast_smul_eq_nsmul (PolynomialRing R n), smul_smul]

omit [Nontrivial R] in
/-- The ordered native differential wedge of the original pulled coordinate
functions is the actual Jacobian times the original top generator. -/
theorem differential_power_wedge :
    exteriorPower.ιMulti (PolynomialRing R n) n
        (fun j => KaehlerDifferential.D R (PolynomialRing R n)
          (coordinatePowerHom R (fun i => d i + 1) (MvPolynomial.X j))) =
      jacobian R d • canonicalGenerator R n := by
  simp_rw [differential_power_X]
  rw [canonicalGenerator_eq_wedge]
  exact (exteriorPower.ιMulti (PolynomialRing R n) n).map_smul_univ _ _

omit [Nontrivial R] in
/-- The proved original tower map takes its whole Jacobian to the same
original positive-coordinate derivative product. -/
theorem coordinateTower_jacobian :
    coordinateTowerEquiv R d
        (towerJacobian (coordinateTowerDegree d) (coordinateTowerCoefficient R (n := n)) n) =
      jacobian R d := by
  change coordinateTowerToPolynomial R d _ = _
  unfold coordinateTowerToPolynomial
  rw [evaluation_jacobian]
  rw [← Fin.prod_univ_eq_prod_range
    (fun i => ((coordinateTowerDegree d i + 1 : ℕ) : PolynomialRing R n) *
      coordinateTowerCoefficient R (n := n) i ^ coordinateTowerDegree d i) n]
  apply Finset.prod_congr rfl
  intro j _
  simp only [coordinateTowerDegree, coordinateTowerCoefficient, dif_pos j.isLt]

/-- The native algebra trace on every original polynomial is the actual
whole top-coefficient counit evaluated against the original Jacobian. -/
theorem powerTrace_eq_coefficientMap_jacobian (b : PolynomialRing R n) :
    powerTrace R d b = coefficientMap R d (jacobian R d * b) := by
  let A := PolynomialRing R n
  let T := coordinateTowerRing R d
  let : Algebra A T := (coordinateTowerStructure R d).toAlgebra
  let : Algebra A A := (powerMap R d).toAlgebra
  let e : T ≃ₐ[A] A := coordinateTowerAlgEquiv R d
  have ht : powerTrace R d b = Algebra.trace A T ((coordinateTowerEquiv R d).symm b) := by
    have h := Algebra.trace_eq_of_algEquiv e ((coordinateTowerEquiv R d).symm b)
    change Algebra.trace A A
      (coordinateTowerEquiv R d ((coordinateTowerEquiv R d).symm b)) = _ at h
    rw [RingEquiv.apply_symm_apply] at h
    exact h
  rw [ht, NadelKummerTraceJacobianTower.trace_eq_topCoefficient_jacobian, coefficientMap_apply]
  apply congrArg (independentTopCoefficient (coordinateTowerDegree d)
    (coordinateTowerCoefficient R (n := n)) n)
  apply (coordinateTowerEquiv R d).injective
  rw [map_mul, coordinateTower_jacobian, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/-- The whole trace formula retains the original nonidentity power-map
coefficient action on every original polynomial. -/
theorem powerTrace_powerMap_mul (a b : PolynomialRing R n) :
    powerTrace R d (powerMap R d a * b) = a * powerTrace R d b := by
  rw [powerTrace_eq_coefficientMap_jacobian, powerTrace_eq_coefficientMap_jacobian]
  have h := (coefficientMap R d).map_smul a (jacobian R d * b)
  change coefficientMap R d (powerMap R d a * (jacobian R d * b)) =
    a * coefficientMap R d (jacobian R d * b) at h
  simpa only [mul_assoc, mul_left_comm] using h

/-- The actual canonical chart counit agrees with intrinsic algebra trace
on every original polynomial times the actual Jacobian top form. -/
theorem canonicalCounit_jacobian (b : PolynomialRing R n) :
    canonicalCounit R d ((jacobian R d * b) • canonicalGenerator R n) =
      powerTrace R d b • canonicalGenerator R n := by
  rw [canonicalCounit_generator, powerTrace_eq_coefficientMap_jacobian]

/-- On every coefficient times the actual pulled coordinate top form,
the original canonical counit is the intrinsic native algebra trace. -/
theorem canonicalCounit_pulledGenerator (b : PolynomialRing R n) :
    canonicalCounit R d
        (b • exteriorPower.ιMulti (PolynomialRing R n) n
          (fun j => KaehlerDifferential.D R (PolynomialRing R n)
            (coordinatePowerHom R (fun i => d i + 1) (MvPolynomial.X j)))) =
      powerTrace R d b • canonicalGenerator R n := by
  rw [differential_power_wedge, smul_smul, mul_comm b (jacobian R d)]
  exact canonicalCounit_jacobian R d b

end EnvelopeProperty.Vanishing.NadelKummerTraceJacobian
