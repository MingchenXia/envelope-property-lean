import EnvelopeProperty.Vanishing.NadelGlobalNormalizationGeneric
import Mathlib.RingTheory.TensorProduct.Maps

/-! # The SAME actual original global function field and whole raw generic algebra

The native original affine fraction-field theorem constructs the coefficient
comparison. Whole tensor functoriality fixes EVERY original raw element and
transports the entire actual raw integral closure, with all components retained.
-/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalNormalization.FunctionField
open NadelAuxiliaryMulticover NadelAdaptedChartMatching
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {X : Scheme.{u}} [IsIntegral X] (U : X.affineOpens) [Nonempty U.1]
  (D : List (AuxiliarySection X)) (e : NadelAuxiliaryMulticoverCharts.Frames U.1 D)

/-- The SAME native original germ action, explicit for the whole tensor comparison. -/
local instance coefficientAlgebra : Algebra Γ(X, U.1) X.functionField :=
  GenericChart.coefficientAlgebra U

/-- The ACTUAL native original affine function-field producer identifies the
literal fraction field with the SAME original global generic stalk. -/
def equiv : FractionRing Γ(X, U.1) ≃ₐ[Γ(X, U.1)] X.functionField := by
  let : IsFractionRing Γ(X, U.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  exact FractionRing.algEquiv Γ(X, U.1) X.functionField

/-- The original germ map is retained on EVERY actual original coefficient. -/
theorem equiv_coefficient (r : Γ(X, U.1)) :
    equiv U (algebraMap Γ(X, U.1) (FractionRing Γ(X, U.1)) r) = X.germToFunctionField U.1 r :=
  (equiv U).commutes r

/-- The WHOLE original raw generic tensor algebra comparison over the SAME
original raw ring, with no selected component or abstract field matching input. -/
def tensorEquiv : FractionRing Γ(X, U.1) ⊗[Γ(X, U.1)] WholeChart.Ring U D e ≃ₐ[WholeChart.Ring U D e]
    GenericChart.Ring U D e := by
  let t := Algebra.TensorProduct.congr (equiv U) (AlgEquiv.refl (R := Γ(X, U.1)) (A₁ := WholeChart.Ring U D e))
  exact {
    toRingEquiv := t.toRingEquiv
    commutes' := fun z => by
      change t ((1 : FractionRing Γ(X, U.1)) ⊗ₜ[Γ(X, U.1)] z) =
        (1 : X.functionField) ⊗ₜ[Γ(X, U.1)] z
      simp [t] }

/-- The WHOLE original raw element triangle, retaining ALL original roots. -/
theorem tensorEquiv_includeRight (z : WholeChart.Ring U D e) :
    tensorEquiv U D e (Algebra.TensorProduct.includeRight z) = Algebra.TensorProduct.includeRight z :=
  (tensorEquiv U D e).commutes z

/-- The ENTIRE integral closure transports to the actual original global
function-field tensor algebra through its proved whole original raw triangle. -/
def closureEquiv :
    integralClosure (WholeChart.Ring U D e)
      (FractionRing Γ(X, U.1) ⊗[Γ(X, U.1)] WholeChart.Ring U D e) ≃ₐ[WholeChart.Ring U D e]
      integralClosure (WholeChart.Ring U D e) (GenericChart.Ring U D e) :=
  (tensorEquiv U D e).mapIntegralClosure

end EnvelopeProperty.Vanishing.NadelGlobalNormalization.FunctionField
