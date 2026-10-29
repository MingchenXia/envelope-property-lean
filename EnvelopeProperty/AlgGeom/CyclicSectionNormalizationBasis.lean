import EnvelopeProperty.AlgGeom.CyclicSectionNormalizationRounded
import Mathlib.LinearAlgebra.Basis.SMul

/-! # Actual rounded cyclic bases over the original domain and its fraction field -/

noncomputable section
universe v
namespace EnvelopeProperty.CyclicSectionNormalizationBasis
open CyclicSectionAlgebra CyclicSectionNormalizationRounded Module
variable {R : Type v} [CommRing R] [IsDomain R]

private theorem fraction_pow_ne_zero (f : R) (hf : f ≠ 0) (q : ℕ) :
    (algebraMap R (FractionRing R) f) ^ q ≠ 0 := by
  apply pow_ne_zero
  intro h
  exact hf ((IsFractionRing.injective R (FractionRing R)) (by simpa using h))

/-- The actual generic rounded family is a basis of the SAME entire generic quotient. -/
def genericBasis (n α : ℕ) (u f : R) (hn : 0 < n) (hf : f ≠ 0) :
    Basis (Fin n) (FractionRing R) (GenericRootRing n α u f) :=
  (CyclicSectionPowerBasis.basis n (algebraMap R (FractionRing R) (u * f ^ α)) hn).unitsSMul
    (fun i => (Units.mk0 ((algebraMap R (FractionRing R) f) ^ ((i : ℕ) * α / n))
      (fraction_pow_ne_zero f hf _))⁻¹)

/-- Each generic basis vector is literally the SAME original rounded root power. -/
theorem genericBasis_apply (n α : ℕ) (u f : R) (hn : 0 < n) (hf : f ≠ 0) (i : Fin n) :
    genericBasis n α u f hn hf i = roundedPower n α u f (i : ℕ) := by
  rw [genericBasis, Basis.unitsSMul_apply, CyclicSectionPowerBasis.basis_apply]
  simp only [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, Algebra.smul_def,
    roundedPower]

/-- The SAME actual rounded family is independent over the original domain. -/
theorem roundedPower_linearIndependent (n α : ℕ) (u f : R) (hn : 0 < n) (hf : f ≠ 0) :
    LinearIndependent R (fun i : Fin n => roundedPower n α u f (i : ℕ)) := by
  have h : LinearIndependent (FractionRing R)
      (fun i : Fin n => roundedPower n α u f (i : ℕ)) := by
    have he : (fun i : Fin n => roundedPower n α u f (i : ℕ)) =
        (genericBasis n α u f hn hf : Fin n → GenericRootRing n α u f) :=
      funext fun i => (genericBasis_apply n α u f hn hf i).symm
    rw [he]
    exact (genericBasis n α u f hn hf).linearIndependent
  exact h.restrict_scalars' R

/-- The original rounded powers form an R-basis of the ACTUAL rounded subalgebra. -/
def basis (n α : ℕ) (u f : R) (hn : 0 < n) (hf : f ≠ 0) :
    Basis (Fin n) R (roundedAlgebra n α u f hn hf) :=
  Basis.span (roundedPower_linearIndependent n α u f hn hf)

/-- Every actual R-basis vector has its original rounded element as underlying value. -/
theorem basis_apply (n α : ℕ) (u f : R) (hn : 0 < n) (hf : f ≠ 0) (i : Fin n) :
    (basis n α u f hn hf i : GenericRootRing n α u f) = roundedPower n α u f (i : ℕ) :=
  Basis.coe_span_apply _ i

end EnvelopeProperty.CyclicSectionNormalizationBasis
