import EnvelopeProperty.Vanishing.NadelCanonicalMixedUnitTowerTrace
import EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChangeCore

/-! # Native whole simultaneous-unit trace duality, transported through the actual original quotient comparison -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed

open CategoryTheory ModuleCat NadelAdaptedChartMatching NadelKummerCanonicalTrace
open NadelKummerCanonicalBaseChange

variable {R : Type u} [CommRing R] [Nontrivial R] {q : ℕ}
    (N : Fin q → ℕ) (u : Fin q → Rˣ) (hN : ∀ i, 0 < N i)
    (htame : ∀ i, IsUnit (N i : R))

/-- The actual native right-adjoint dual module for the whole original simultaneous unit quotient. -/
abbrev unitCoverDual : ModuleCat (UnitCover N u) :=
  (coextendScalars (algebraMap R (UnitCover N u))).obj (ModuleCat.of R R)

/-- Native adjunction turns the actual whole trace into the original cover-linear multiplication pairing. -/
def unitCoverTraceMap : UnitCover N u →ₗ[UnitCover N u] unitCoverDual N u :=
  coextensionFrame (algebraMap R (UnitCover N u))
    ((Algebra.trace R (UnitCover N u)).comp (algebraRestrictionEquiv (A := R) (B := UnitCover N u)).toLinearMap)

omit [Nontrivial R] in
/-- The entire native pairing is actual whole-algebra trace multiplication on every original pair. -/
theorem unitCoverTraceMap_apply (x y : UnitCover N u) :
    unitCoverTraceMap N u x y = Algebra.trace R (UnitCover N u) (y * x) := rfl

/-- The actual whole quotient/tower comparison retains original restricted coefficient actions. -/
def unitCoverRestrictionEquiv :
    (restrictScalars (VaryingFamily.structureMap N (fun i => (u i : R)))).obj
        (ModuleCat.of (VaryingFamily.Ring N (fun i => (u i : R)))
          (VaryingFamily.Ring N (fun i => (u i : R)))) ≃ₗ[R]
      (restrictScalars (algebraMap R (UnitCover N u))).obj (ModuleCat.of (UnitCover N u) (UnitCover N u)) := by
  let : Algebra R (VaryingFamily.Ring N (fun i => (u i : R))) :=
    (VaryingFamily.structureMap N (fun i => (u i : R))).toAlgebra
  let e := (VaryingFinite.algEquiv N (fun i => (u i : R)) hN).symm
  exact {
    toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' r x := by
      change e (algebraMap R (VaryingFamily.Ring N (fun i => (u i : R))) r * (show VaryingFamily.Ring N (fun i => (u i : R)) from x)) =
        algebraMap R (UnitCover N u) r * e x
      rw [map_mul, e.commutes] }

/-- The actual native functional transport is precomposition with the complete original quotient/tower map. -/
def unitCoverFunctionalTransport : unitCoverDual N u ≃
    (coextendScalars (VaryingFamily.structureMap N (fun i => (u i : R)))).obj (ModuleCat.of R R) :=
  (CoextendScalars.equiv (algebraMap R (UnitCover N u)) (ModuleCat.of R R)).toEquiv |>.trans
    (((unitCoverRestrictionEquiv N u hN).symm.arrowCongr (LinearEquiv.refl R R)).toEquiv.trans
      (CoextendScalars.equiv (VaryingFamily.structureMap N (fun i => (u i : R)))
        (ModuleCat.of R R)).symm.toEquiv)

omit [Nontrivial R] in
/-- The actual entire functional comparison fixes the original evaluation values under the genuine whole algebra iso. -/
theorem unitCoverFunctionalTransport_apply (φ : unitCoverDual N u)
    (y : VaryingFamily.Ring N (fun i => (u i : R))) :
    unitCoverFunctionalTransport N u hN φ y = φ ((VaryingFinite.ringEquiv N (fun i => (u i : R)) hN).symm y) := rfl

/-- The actual whole native pairing comparison is proved by native trace invariance, not supplied as input. -/
theorem unitCoverFunctionalTransport_traceMap (x : UnitCover N u) :
    unitCoverFunctionalTransport N u hN (unitCoverTraceMap N u x) =
      (unitTowerTraceIso N u hN htame).hom ((VaryingFinite.ringEquiv N (fun i => (u i : R)) hN) x) := by
  let : Algebra R (VaryingFamily.Ring N (fun i => (u i : R))) :=
    (VaryingFamily.structureMap N (fun i => (u i : R))).toAlgebra
  let e := VaryingFinite.algEquiv N (fun i => (u i : R)) hN
  apply CoextendScalars.ext
  ext (y : VaryingFamily.Ring N (fun i => (u i : R)))
  rw [unitCoverFunctionalTransport_apply, unitCoverTraceMap_apply, unitTowerTraceIso_apply]
  change Algebra.trace R (UnitCover N u) ((e.symm y) * x) =
    Algebra.trace R (VaryingFamily.Ring N (fun i => (u i : R))) (y * e x)
  have h := Algebra.trace_eq_of_algEquiv e ((e.symm y) * x)
  simpa only [map_mul, AlgEquiv.apply_symm_apply] using h.symm

include hN htame in
/-- The actual whole trace pairing is bijective, internally from the original monic tower dual and unit Jacobian. -/
theorem unitCoverTraceMap_bijective : Function.Bijective (unitCoverTraceMap N u) := by
  let e := (VaryingFinite.ringEquiv N (fun i => (u i : R)) hN).toEquiv.trans
    ((unitTowerTraceIso N u hN htame).toLinearEquiv.toEquiv.trans
      (unitCoverFunctionalTransport N u hN).symm)
  have he : (unitCoverTraceMap N u : UnitCover N u → unitCoverDual N u) = e := by
    funext x
    apply (unitCoverFunctionalTransport N u hN).injective
    rw [unitCoverFunctionalTransport_traceMap N u hN htame]
    exact ((unitCoverFunctionalTransport N u hN).apply_symm_apply _).symm
  rw [he]
  exact e.bijective

/-- The original whole simultaneous-unit algebra is its actual cover-linear native trace dual. -/
def unitCoverTraceEquiv : UnitCover N u ≃ₗ[UnitCover N u] unitCoverDual N u :=
  LinearEquiv.ofBijective (unitCoverTraceMap N u) (unitCoverTraceMap_bijective N u hN htame)

/-- The produced isomorphism is an actual original-cover module isomorphism. -/
def unitCoverTraceIso : ModuleCat.of (UnitCover N u) (UnitCover N u) ≅ unitCoverDual N u :=
  (unitCoverTraceEquiv N u hN htame).toModuleIso

/-- The actual native whole-cover counit is the original whole trace. -/
theorem unitCoverTraceIso_counit (x : UnitCover N u) :
    (restrictCoextendScalarsAdj (algebraMap R (UnitCover N u))).counit.app (ModuleCat.of R R)
      ((unitCoverTraceIso N u hN htame).hom x) = Algebra.trace R (UnitCover N u) x := by
  change unitCoverTraceMap N u x (1 : UnitCover N u) = _
  rw [unitCoverTraceMap_apply, one_mul]

end EnvelopeProperty.Vanishing.NadelCanonicalMixed
