import EnvelopeProperty.Vanishing.NadelKummerTraceJacobianRoot
import EnvelopeProperty.Vanishing.NadelKummerCoverTowerBasis

/-! # Native trace and the original Jacobian through independent root towers -/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelKummerTraceJacobianTower

open CategoryTheory Module NadelFiniteDuality NadelFiniteDualityTower
open NadelKummerTraceJacobianRoot CyclicSectionAlgebra CyclicSectionPowerBasis

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [Nontrivial R] (d : ℕ → ℕ) (c : ℕ → R)

/-- The original monic Jacobians multiplied through the actual coefficient tower. -/
def towerJacobian : ∀ k, independentRootRing d c k
  | 0 => 1
  | k + 1 => independentRootStep d c k (towerJacobian k) *
      (show independentRootRing d c (k + 1) from
        rootJacobian (d k) (independentRootStructure d c k (c k)))

/-- Native algebra trace equals the original composed top coefficient
against the actual whole tower Jacobian. -/
theorem trace_eq_topCoefficient_jacobian (k : ℕ) (x : independentRootRing d c k) :
    letI : Algebra R (independentRootRing d c k) := (independentRootStructure d c k).toAlgebra
    Algebra.trace R (independentRootRing d c k) x =
      independentTopCoefficient d c k (towerJacobian d c k * x) := by
  induction k with
  | zero =>
    change Algebra.trace R R (show R from x) = (1 : R) * (show R from x)
    rw [Algebra.trace_self_apply, one_mul]
  | succ k ih =>
    let B := independentRootRing d c k
    let C := independentRootRing d c (k + 1)
    let : Nontrivial B := independentRootRing_nontrivial d c k
    let : Algebra R B := (independentRootStructure d c k).toAlgebra
    let : Algebra B C := inferInstanceAs
      (Algebra B (Root (d k) (independentRootStructure d c k (c k))))
    let : Algebra R C := (independentRootStructure d c (k + 1)).toAlgebra
    let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
    let : Finite (NadelKummerCover.Tower.basisIndex d k) :=
      NadelKummerCover.Tower.basisIndex_finite d k
    have ht := Algebra.trace_trace_of_basis (R := R) (S := B) (T := C)
      (NadelKummerCover.Tower.basis d c k)
      (basis (d k + 1) (independentRootStructure d c k (c k)) (Nat.succ_pos _)) x
    have hr : Algebra.trace B C x =
        topCoefficient (d k) (independentRootStructure d c k (c k))
          (rootJacobian (d k) (independentRootStructure d c k (c k)) *
            (show Root (d k) (independentRootStructure d c k (c k)) from x)) :=
      NadelKummerTraceJacobianRoot.trace_eq_topCoefficient_jacobian (d k)
        (independentRootStructure d c k (c k)) _
    rw [← ht, hr, ih]
    change independentTopCoefficient d c k
        (towerJacobian d c k * topCoefficient (d k)
          (independentRootStructure d c k (c k))
          (rootJacobian (d k) (independentRootStructure d c k (c k)) *
            (show Root (d k) (independentRootStructure d c k (c k)) from x))) =
      independentTopCoefficient d c k
        (topCoefficient (d k) (independentRootStructure d c k (c k))
          ((algebraMap B (Root (d k) (independentRootStructure d c k (c k))) (towerJacobian d c k) *
            rootJacobian (d k) (independentRootStructure d c k (c k))) *
              (show Root (d k) (independentRootStructure d c k (c k)) from x)))
    apply congrArg (independentTopCoefficient d c k)
    have hl := (topCoefficient (d k) (independentRootStructure d c k (c k))).map_smul
      (towerJacobian d c k) (rootJacobian (d k) (independentRootStructure d c k (c k)) *
        (show Root (d k) (independentRootStructure d c k (c k)) from x))
    simpa only [Algebra.smul_def, Algebra.algebraMap_self_apply, mul_assoc] using hl.symm

variable {S : Type u} [CommRing S] (f : R →+* S) (r : ℕ → S)
    (hr : ∀ i, r i ^ (d i + 1) = f (c i))

omit [Nontrivial R] in
/-- Every actual universal evaluation sends the whole tower Jacobian to
the product of the original positive-degree coordinate derivatives. -/
theorem evaluation_jacobian (k : ℕ) :
    NadelKummerCover.Tower.evaluation d c f r hr k (towerJacobian d c k) =
      ∏ i ∈ Finset.range k, ((d i + 1 : ℕ) : S) * r i ^ d i := by
  induction k with
  | zero => simp [towerJacobian]
  | succ k ih =>
    rw [towerJacobian, map_mul]
    have hs := congrArg (fun h : independentRootRing d c k →+* S => h (towerJacobian d c k))
      (NadelKummerCover.Tower.evaluation_step d c f r hr k)
    rw [RingHom.comp_apply] at hs
    rw [hs, ih]
    change _ * NadelKummerCover.Tower.evaluation d c f r hr (k + 1)
      (((d k + 1 : ℕ) : independentRootRing d c (k + 1)) *
        (show independentRootRing d c (k + 1) from
          root (d k + 1) (independentRootStructure d c k (c k))) ^ d k) = _
    rw [map_mul, map_natCast, map_pow,
      NadelKummerCover.Tower.evaluation_root, Finset.prod_range_succ]

end EnvelopeProperty.Vanishing.NadelKummerTraceJacobianTower
