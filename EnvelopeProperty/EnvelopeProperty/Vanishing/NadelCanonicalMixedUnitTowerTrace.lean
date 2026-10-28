import EnvelopeProperty.Vanishing.NadelCanonicalMixedUnitCover
import EnvelopeProperty.Vanishing.NadelKummerTraceJacobianTower
import EnvelopeProperty.Vanishing.NadelCanonicalUnitRootDual

/-! # Actual whole variable-degree tame tower trace duality -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed

open CategoryTheory ModuleCat NadelFiniteDualityTower NadelAdaptedChartMatching
open NadelKummerTraceJacobianTower NadelKummerTraceJacobianRoot

variable {R : Type u} [CommRing R] [Nontrivial R] {q : ℕ}
    (N : Fin q → ℕ) (u : Fin q → Rˣ) (hN : ∀ i, 0 < N i)
    (htame : ∀ i, IsUnit (N i : R))

omit [Nontrivial R] in
include hN htame in
/-- The true entire original tower Jacobian is a unit at every actual finite unit-root stage. -/
theorem unitTowerJacobian_isUnit : ∀ (k : ℕ) (_ : k ≤ q),
    IsUnit (towerJacobian (VaryingFamily.degree N)
      (VaryingFamily.coefficient (fun i => (u i : R))) k) := by
  intro k
  induction k with
  | zero => intro _; exact isUnit_one
  | succ k ih =>
      intro hk
      let d := VaryingFamily.degree N
      let c := VaryingFamily.coefficient (fun i => (u i : R))
      let B := independentRootRing d c k
      let C := independentRootRing d c (k + 1)
      have hlt : k < q := Nat.lt_of_succ_le hk
      have hc : IsUnit (c k) := by
        simpa only [c, VaryingFamily.coefficient, dif_pos hlt] using (u ⟨k, hlt⟩).isUnit
      have hr : IsUnit (CyclicSectionAlgebra.root (d k + 1)
          (independentRootStructure d c k (c k))) := by
        apply (isUnit_pow_iff (Nat.succ_ne_zero (d k))).mp
        rw [CyclicSectionAlgebra.root_pow]
        exact (hc.map (independentRootStructure d c k)).map (independentRootStep d c k)
      have hd : IsUnit ((d k + 1 : ℕ) : C) := by
        have h := (htame ⟨k, hlt⟩).map (independentRootStructure d c (k + 1))
        simpa only [map_natCast, d, VaryingFamily.degree_eq N hN ⟨k, hlt⟩] using h
      change IsUnit ((independentRootStep d c k) (towerJacobian d c k) *
        (show C from rootJacobian (d k) (independentRootStructure d c k (c k))))
      exact ((ih (Nat.le_of_succ_le hk)).map (independentRootStep d c k)).mul
        (hd.mul (hr.pow (d k)))

/-- The actual whole final Jacobian as a true unit, with no component discarded. -/
def unitTowerJacobianUnit : (VaryingFamily.Ring N (fun i => (u i : R)))ˣ :=
  (unitTowerJacobian_isUnit N u hN htame q (Nat.le_refl q)).unit

omit [Nontrivial R] in
/-- The actual chosen unit retains the original literal complete tower Jacobian. -/
theorem unitTowerJacobianUnit_coe :
    (unitTowerJacobianUnit N u hN htame : VaryingFamily.Ring N (fun i => (u i : R))) =
      towerJacobian (VaryingFamily.degree N) (VaryingFamily.coefficient (fun i => (u i : R))) q :=
  (unitTowerJacobian_isUnit N u hN htame q (Nat.le_refl q)).unit_spec

/-- The native right-adjoint trace dual of the WHOLE original varying-degree unit tower. -/
def unitTowerTraceIso :
    ModuleCat.of (VaryingFamily.Ring N (fun i => (u i : R)))
        (VaryingFamily.Ring N (fun i => (u i : R))) ≅
      (coextendScalars (VaryingFamily.structureMap N (fun i => (u i : R)))).obj (ModuleCat.of R R) :=
  (LinearEquiv.smulOfUnit (M := VaryingFamily.Ring N (fun i => (u i : R)))
      (unitTowerJacobianUnit N u hN htame)).toModuleIso ≪≫
    independentRootIso (VaryingFamily.degree N) (VaryingFamily.coefficient (fun i => (u i : R))) q

/-- Every native functional value is actual whole-algebra trace multiplication, with the true original scalar action. -/
theorem unitTowerTraceIso_apply (x y : VaryingFamily.Ring N (fun i => (u i : R))) :
    (unitTowerTraceIso N u hN htame).hom x y =
      letI : Algebra R (VaryingFamily.Ring N (fun i => (u i : R))) :=
        (VaryingFamily.structureMap N (fun i => (u i : R))).toAlgebra
      Algebra.trace R (VaryingFamily.Ring N (fun i => (u i : R))) (y * x) := by
  rw [NadelKummerTraceJacobianTower.trace_eq_topCoefficient_jacobian]
  change (independentRootIso (VaryingFamily.degree N)
    (VaryingFamily.coefficient (fun i => (u i : R))) q).hom
      ((unitTowerJacobianUnit N u hN htame : VaryingFamily.Ring N (fun i => (u i : R))) * x) y = _
  rw [independentRootIso_hom_apply, unitTowerJacobianUnit_coe]
  congr 1
  ring

/-- The original native counit is trace on EVERY element of the entire varying-degree unit tower. -/
theorem unitTowerTraceIso_counit (x : VaryingFamily.Ring N (fun i => (u i : R))) :
    (restrictCoextendScalarsAdj (VaryingFamily.structureMap N (fun i => (u i : R)))).counit.app
      (ModuleCat.of R R) ((unitTowerTraceIso N u hN htame).hom x) =
      letI : Algebra R (VaryingFamily.Ring N (fun i => (u i : R))) :=
        (VaryingFamily.structureMap N (fun i => (u i : R))).toAlgebra
      Algebra.trace R (VaryingFamily.Ring N (fun i => (u i : R))) x := by
  change (unitTowerTraceIso N u hN htame).hom x
    (1 : VaryingFamily.Ring N (fun i => (u i : R))) = _
  rw [unitTowerTraceIso_apply, one_mul]

end EnvelopeProperty.Vanishing.NadelCanonicalMixed
