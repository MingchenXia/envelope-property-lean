import EnvelopeProperty.Vanishing.NadelFiniteDuality
import Mathlib.RingTheory.Trace.Defs

/-! # Native algebra trace of the original monic root algebra

The original positive-degree power basis and its proved reverse dual frame
compute every multiplication-matrix diagonal. No invertibility of the
degree or of the branch coordinate is required.
-/

open CategoryTheory Module
noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelKummerTraceJacobianRoot

open NadelFiniteDuality CyclicSectionAlgebra CyclicSectionPowerBasis

variable {R : Type u} [CommRing R] [Nontrivial R]

/-- The actual monic root relation has derivative N*y^(N-1), N=n+1. -/
def rootJacobian (n : ℕ) (a : R) : Root n a :=
  ((n + 1 : ℕ) : Root n a) * root (n + 1) a ^ n

/-- Every whole coefficient is the proved top-coefficient reverse pairing
for the original native root basis. -/
theorem rootBasis_coord (n : ℕ) (a : R) (z : Root n a) (i : Fin (n + 1)) :
    (basis (n + 1) a (Nat.succ_pos n)).repr z i =
      topCoefficient n a (root (n + 1) a ^ (i.rev : ℕ) * z) := by
  have h := congrArg (fun f : Module.Dual R (Root n a) => f z)
    (multiplicationPairing_reverse_basis n a i)
  rw [multiplicationPairing_apply, basis_apply, Module.Basis.dualBasis_apply] at h
  exact h.symm

/-- Every actual multiplication-matrix diagonal equals the same original
top coefficient, for arbitrary elements including the ramified locus. -/
theorem rootMulMatrix_diagonal (n : ℕ) (a : R) (x : Root n a) (i : Fin (n + 1)) :
    Algebra.leftMulMatrix (basis (n + 1) a (Nat.succ_pos n)) x i i =
      topCoefficient n a (root (n + 1) a ^ n * x) := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, rootBasis_coord, basis_apply]
  apply congrArg (topCoefficient n a)
  calc
    _ = (root (n + 1) a ^ (i : ℕ) * root (n + 1) a ^ (i.rev : ℕ)) * x := by ring
    _ = root (n + 1) a ^ ((i : ℕ) + (i.rev : ℕ)) * x :=
      congrArg (fun z : Root n a => z * x) (pow_add (root (n + 1) a) (i : ℕ) (i.rev : ℕ)).symm
    _ = _ := by rw [i.add_rev_cast]

/-- The native algebra trace is the actual top-coefficient counit
multiplied by the original monic Jacobian, on the whole root algebra. -/
theorem trace_eq_topCoefficient_jacobian (n : ℕ) (a : R) (x : Root n a) :
    Algebra.trace R (Root n a) x = topCoefficient n a (rootJacobian n a * x) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (basis (n + 1) a (Nat.succ_pos n)), Matrix.trace]
  simp_rw [Matrix.diag_apply, rootMulMatrix_diagonal]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [rootJacobian, ← map_nsmul]
  congr 1
  simp [nsmul_eq_mul, mul_assoc]

end EnvelopeProperty.Vanishing.NadelKummerTraceJacobianRoot
