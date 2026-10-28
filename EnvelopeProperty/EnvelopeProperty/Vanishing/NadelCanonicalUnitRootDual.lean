import EnvelopeProperty.Vanishing.NadelKummerTraceJacobianRoot
import EnvelopeProperty.AlgGeom.KummerUnitRootCover

/-! # The true trace dual of the whole actual tame unit-root algebra

The entire original monic quotient is retained.  Its perfect top-coefficient
frame and actual unit Jacobian produce native trace duality without any
component choice or supplied trace/duality comparison.
-/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelCanonicalUnitRoot

open CategoryTheory ModuleCat NadelFiniteDuality NadelKummerTraceJacobianRoot
open CyclicSectionAlgebra

variable {A : Type u} [CommRing A] [Nontrivial A] (m : ℕ) (u : Aˣ)

omit [Nontrivial A] in
/-- The original whole unit-root quotient is étale for the actual tame degree-unit reason. -/
theorem root_etale (hN : IsUnit ((m + 1 : ℕ) : A)) : Algebra.Etale A (Root m (u : A)) :=
  KummerUnitRootCover.etale (m + 1) u (Nat.succ_pos m) hN

omit [Nontrivial A] in
/-- The actual original root is a unit in the whole algebra, without selecting any component. -/
theorem root_isUnit : IsUnit (root (m + 1) (u : A)) :=
  KummerUnitRootCover.root_isUnit (m + 1) u (Nat.succ_pos m)

omit [Nontrivial A] in
/-- The actual monic Jacobian is a unit on the entire tame unit-root algebra. -/
theorem jacobian_isUnit (hN : IsUnit ((m + 1 : ℕ) : A)) :
    IsUnit (rootJacobian m (u : A)) := by
  have h := (hN.map (algebraMap A (Root m (u : A)))).mul ((root_isUnit m u).pow m)
  simpa only [map_natCast, rootJacobian] using h

/-- The true original unit Jacobian, retaining its original element in the monic algebra. -/
def jacobianUnit (hN : IsUnit ((m + 1 : ℕ) : A)) : (Root m (u : A))ˣ :=
  (jacobian_isUnit m u hN).unit

omit [Nontrivial A] in
/-- The produced unit has the same actual original Jacobian coefficient. -/
theorem jacobianUnit_coe (hN : IsUnit ((m + 1 : ℕ) : A)) :
    (jacobianUnit m u hN : Root m (u : A)) = rootJacobian m (u : A) :=
  (jacobian_isUnit m u hN).unit_spec

/-- The native whole-algebra trace dual, produced from the actual monic perfect pairing. -/
def traceDualizingEquiv (hN : IsUnit ((m + 1 : ℕ) : A)) :
    Root m (u : A) ≃ₗ[Root m (u : A)] dualizingModule m (u : A) :=
  (LinearEquiv.smulOfUnit (M := Root m (u : A)) (jacobianUnit m u hN)).trans
    (dualizingEquiv m (u : A))

/-- The actual native dual equivalence is trace multiplication on every pair of original elements. -/
theorem traceDualizingEquiv_apply (hN : IsUnit ((m + 1 : ℕ) : A)) (x y : Root m (u : A)) :
    traceDualizingEquiv m u hN x y = Algebra.trace A (Root m (u : A)) (y * x) := by
  change dualizingEquiv m (u : A)
    (LinearEquiv.smulOfUnit (M := Root m (u : A)) (jacobianUnit m u hN) x) y = _
  rw [dualizingEquiv_apply]
  change topCoefficient m (u : A) (y * ((jacobianUnit m u hN : Root m (u : A)) * x)) = _
  rw [jacobianUnit_coe, trace_eq_topCoefficient_jacobian]
  congr 1
  ring

/-- The whole native trace-dual frame as an actual isomorphism of root-algebra modules. -/
def traceDualizingIso (hN : IsUnit ((m + 1 : ℕ) : A)) :
    ModuleCat.of (Root m (u : A)) (Root m (u : A)) ≅ dualizingModule m (u : A) :=
  LinearEquiv.toModuleIso (X₁ := ModuleCat.of (Root m (u : A)) (Root m (u : A)))
    (X₂ := dualizingModule m (u : A)) (traceDualizingEquiv m u hN)

/-- The native restriction/coextension counit of the actual trace frame is the whole original trace. -/
theorem traceDualizingIso_counit (hN : IsUnit ((m + 1 : ℕ) : A)) (x : Root m (u : A)) :
    (restrictCoextendScalarsAdj (algebraMap A (Root m (u : A)))).counit.app (ModuleCat.of A A)
      ((traceDualizingIso m u hN).hom x) = Algebra.trace A (Root m (u : A)) x := by
  change traceDualizingEquiv m u hN x (1 : Root m (u : A)) = _
  rw [traceDualizingEquiv_apply, one_mul]

end EnvelopeProperty.Vanishing.NadelCanonicalUnitRoot
