import EnvelopeProperty.Char0.NadelClearedTwistCore
import EnvelopeProperty.AlgGeom.ProjectiveTwistTensorAddition

/-! # The actual original hyperplane powers and negative projective twists

All comparisons use the original coordinate-hyperplane line and its proved
native transition-compatible tensor addition; no desired twist iso is input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules MvPolynomial
universe u
namespace EnvelopeProperty.Char0.NadelClearedTwist
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {N : ℕ} {X : Scheme.{u}}

/-- Genuine native positive projective twists are actual original tensor powers. -/
def coordinatePowerIso (a : Fin (N + 1)) : (r : ℕ) →
    bundleTensorPower (coordinateHyperplaneTwist (R := R) a 1) r ≅
      coordinateHyperplaneTwist (R := R) a (r : ℤ)
  | 0 => (ModularCurves.monoidalUnitObjIso _).symm
  | r + 1 =>
    (ModularCurves.monoidalTensorObjIso
      (bundleTensorPower (coordinateHyperplaneTwist (R := R) a 1) r)
      (coordinateHyperplaneTwist (R := R) a 1)).symm ≪≫
    (coordinatePowerIso a r ⊗ᵢ Iso.refl _) ≪≫
    ProjectiveTwistTensorAddition.tensorIso a a a (r : ℤ) 1 ≪≫
    eqToIso (congrArg (coordinateHyperplaneTwist (R := R) a) (by omega))

/-- The literal original coordinate-zero O(1) pulled by the actual embedding. -/
def hyperplane (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) : X.Modules :=
  (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) 1)

def hyperplanePowerIso (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) (r : ℕ) :
    bundleTensorPower (hyperplane i) r ≅
      (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (r : ℤ)) :=
  (BundleTensorPowerPullback.pullbackIso i _ r).symm ≪≫
    (Scheme.Modules.pullback i).mapIso (coordinatePowerIso (R := R) (0 : Fin (N + 1)) r)

/-- Actual native pullback monoidality and actual projective tensor addition. -/
def pulledTwistTensorIso (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R))
    (a : Fin (N + 1)) (s t : ℤ) :
    (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) a s) ⊗
        (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) a t) ≅
      (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) a (s + t)) := by
  letI : (Scheme.Modules.pullback i).Monoidal := Scheme.Modules.pullbackMonoidal i
  exact Functor.Monoidal.μIso (Scheme.Modules.pullback i) _ _ ≪≫
    (Scheme.Modules.pullback i).mapIso (ProjectiveTwistTensorAddition.tensorIso a a a s t)

/-- The ACTUAL original closed embedding itself proves very ampleness of H. -/
theorem hyperplane_isVeryAmple (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R))
    [IsClosedImmersion i] :
    SchemeLineAmpleness.IsVeryAmple (i ≫ homogeneousProjπ (R := R) (σ := Fin (N + 1))) (hyperplane i) := by
  have hi : IsClosedImmersion i := inferInstance
  refine ⟨N, i, ?_, ?_, ⟨Iso.refl _⟩⟩
  · change IsClosedImmersion i
    exact hi
  · rfl

theorem hyperplane_isAmple (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R))
    [IsClosedImmersion i] :
    SchemeLineAmpleness.IsAmple (i ≫ homogeneousProjπ (R := R) (σ := Fin (N + 1))) (hyperplane i) := by
  have h := hyperplane_isVeryAmple i
  refine ⟨h.isInvertible, 1, by omega, ?_⟩
  exact SchemeAmpleClosedRestriction.veryAmple_of_iso h (bundleTensorLeftUnitIso (hyperplane i)).symm

theorem hyperplane_isAmple_over (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R))
    [IsClosedImmersion i] (π : X ⟶ Spec (.of R))
    (hbase : i ≫ homogeneousProjπ (R := R) (σ := Fin (N + 1)) = π) :
    SchemeLineAmpleness.IsAmple π (hyperplane i) := by
  rw [← hbase]
  exact hyperplane_isAmple i

/-- The SAME actual negative projective twist leaves the exact original
positive natural power, including the endpoint q=N+1 for this iso. -/
def negativeHyperplaneIso (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R))
    (q : ℕ) (hq : q ≤ N + 1) :
    bundleTensorPower (hyperplane i) (N + 1) ⊗
        (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (-(q : ℤ))) ≅
      bundleTensorPower (hyperplane i) (N + 1 - q) := by
  have he : ((N + 1 : ℕ) : ℤ) + -(q : ℤ) = ((N + 1 - q : ℕ) : ℤ) := by omega
  exact (hyperplanePowerIso i (N + 1) ⊗ᵢ Iso.refl _) ≪≫
    pulledTwistTensorIso i (0 : Fin (N + 1)) ((N + 1 : ℕ) : ℤ) (-(q : ℤ)) ≪≫
    (Scheme.Modules.pullback i).mapIso (eqToIso
      (congrArg (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1))) he)) ≪≫
    (hyperplanePowerIso i (N + 1 - q)).symm

end EnvelopeProperty.Char0.NadelClearedTwist
