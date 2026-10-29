import EnvelopeProperty.ComplexGeometry.Germs.SchemeCoordinateFunctionField
import EnvelopeProperty.ComplexGeometry.Pluripotential.ComplexManifold

/-!
# Actual coordinate germs in the Euclidean model

The existing continuous complex-linear PiLp equivalence gives an actual germ
ring equivalence and its actual fraction-field equivalence. The genuine scheme
function-field embedding is transported through these equivalences, retaining
literal indexed coordinate readbacks without a model-type equality assumption.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace HolomorphicGerms

open CategoryTheory AlgebraicGeometry Algebra ComplexSchemes Filter
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry

/-- The actual continuous linear comparison of the two different normed models. -/
def schemeCoordinateModelEquiv (n : ℕ) : ComplexModel n ≃L[ℂ] (Fin n → ℂ) :=
  PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)

/-- Existing germ pullback through the actual continuous linear equivalence. -/
def schemeCoordinateModelGermEquiv (n : ℕ) :
    HolGerm (Fin n → ℂ) ≃+* HolGerm (ComplexModel n) :=
  HolGerm.comapEquiv (schemeCoordinateModelEquiv n)

/-- The actual original zero evaluation is preserved. -/
theorem schemeCoordinateModelGermEquiv_eval (n : ℕ) (g : HolGerm (Fin n → ℂ)) :
    HolGerm.eval (schemeCoordinateModelGermEquiv n g) = HolGerm.eval g :=
  HolGerm.eval_comapEquiv (schemeCoordinateModelEquiv n) g

/-- Actual complex scalar germs are preserved by the genuine pullback. -/
theorem schemeCoordinateModelGermEquiv_const (n : ℕ) (c : ℂ) :
    schemeCoordinateModelGermEquiv n (HolGerm.constHom c) = HolGerm.constHom c := by
  change HolGerm.comapEquiv (schemeCoordinateModelEquiv n) (HolGerm.constHom c) = _
  rw [HolGerm.constHom_apply, HolGerm.comapEquiv_mk, HolGerm.constHom_apply]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun _ => rfl

/-- Each literal coordinate germ remains the SAME indexed coordinate. -/
theorem schemeCoordinateModelGermEquiv_coordinate (n : ℕ) (i : Fin n) :
    schemeCoordinateModelGermEquiv n
      (HolGerm.mk (fun z : Fin n → ℂ => z i)
        (Eventually.of_forall fun _ =>
          (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).differentiableAt)) =
      HolGerm.mk (fun z : ComplexModel n => z i)
        (Eventually.of_forall fun _ =>
          (PiLp.proj 2 (fun _ : Fin n => ℂ) i : ComplexModel n →L[ℂ] ℂ).differentiableAt) := by
  change HolGerm.comapEquiv (schemeCoordinateModelEquiv n) _ = _
  rw [HolGerm.comapEquiv_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun _ => rfl

/-- Existing native fraction-ring extension of that exact germ equivalence. -/
def schemeCoordinateModelFractionEquiv (n : ℕ) :
    FractionRing (HolGerm (Fin n → ℂ)) ≃+* FractionRing (HolGerm (ComplexModel n)) :=
  IsFractionRing.ringEquivOfRingEquiv (schemeCoordinateModelGermEquiv n)

/-- Whole original germ-inclusion readback for the actual fraction equivalence. -/
theorem schemeCoordinateModelFractionEquiv_algebraMap (n : ℕ) (g : HolGerm (Fin n → ℂ)) :
    schemeCoordinateModelFractionEquiv n (algebraMap _ (FractionRing (HolGerm (Fin n → ℂ))) g) =
      algebraMap _ (FractionRing (HolGerm (ComplexModel n))) (schemeCoordinateModelGermEquiv n g) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (schemeCoordinateModelGermEquiv n) g

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) [IsIntegral X]

/-- The actual scheme function field maps to the actual the-model germ field. -/
def schemeCoordinateModelFunctionFieldGerm :
    X.functionField →+* FractionRing (HolGerm (ComplexModel n)) :=
  (schemeCoordinateModelFractionEquiv n).toRingHom.comp (schemeCoordinateFunctionFieldGerm f n p)

/-- The transported genuine global scheme function-field map is injective. -/
theorem schemeCoordinateModelFunctionFieldGerm_injective :
    Function.Injective (schemeCoordinateModelFunctionFieldGerm f n p) :=
  (schemeCoordinateModelFractionEquiv n).injective.comp
    (schemeCoordinateFunctionFieldGerm_injective f n p)

/-- Every actual original stalk element has its transported actual germ. -/
theorem schemeCoordinateModelFunctionFieldGerm_stalk
    (a : X.presheaf.stalk (schemeComplexPointImage f p)) :
    schemeCoordinateModelFunctionFieldGerm f n p (algebraMap _ X.functionField a) =
      algebraMap _ (FractionRing (HolGerm (ComplexModel n)))
        (schemeCoordinateModelGermEquiv n (schemeCoordinateStalkRegularGerm f n p a)) := by
  change schemeCoordinateModelFractionEquiv n
    (schemeCoordinateFunctionFieldGerm f n p (algebraMap _ X.functionField a)) = _
  rw [schemeCoordinateFunctionFieldGerm_stalk, schemeCoordinateModelFractionEquiv_algebraMap]

/-- Every actual affine regular element retains its original analytic germ. -/
theorem schemeCoordinateModelFunctionFieldGerm_regular (a : SchemeCoordinateAffineRing f n p) :
    schemeCoordinateModelFunctionFieldGerm f n p (schemeCoordinateRegularFunctionField f n p a) =
      algebraMap _ (FractionRing (HolGerm (ComplexModel n)))
        (schemeCoordinateModelGermEquiv n (schemeCoordinateRegularGerm f n p a)) := by
  change schemeCoordinateModelFractionEquiv n
    (schemeCoordinateFunctionFieldGerm f n p (schemeCoordinateRegularFunctionField f n p a)) = _
  rw [schemeCoordinateFunctionFieldGerm_regular, schemeCoordinateModelFractionEquiv_algebraMap]

/-- The actual centered rational functions map to literal the-model coordinates. -/
theorem schemeCoordinateModelFunctionFieldGerm_centered (i : Fin n) :
    schemeCoordinateModelFunctionFieldGerm f n p
      (schemeCoordinateRegularFunctionField f n p (schemeCoordinateCenteredFreeGenerator f n p i)) =
      algebraMap _ (FractionRing (HolGerm (ComplexModel n)))
        (HolGerm.mk (fun z : ComplexModel n => z i)
          (Eventually.of_forall fun _ =>
            (PiLp.proj 2 (fun _ : Fin n => ℂ) i : ComplexModel n →L[ℂ] ℂ).differentiableAt)) := by
  change schemeCoordinateModelFractionEquiv n
    (schemeCoordinateFunctionFieldGerm f n p (schemeCoordinateRegularFunctionField f n p
      (schemeCoordinateCenteredFreeGenerator f n p i))) = _
  rw [schemeCoordinateFunctionFieldGerm_centered, schemeCoordinateModelFractionEquiv_algebraMap,
    schemeCoordinateModelGermEquiv_coordinate]

end HolomorphicGerms
