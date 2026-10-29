import EnvelopeProperty.AlgGeom.InvertibleBaseIdealTransport
import EnvelopeProperty.AlgGeom.Canonical.LineBundleSections

/-! # The actual original tensor-power base ideals form a graded sequence -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
noncomputable section
universe u

namespace EnvelopeProperty.TensorPowerBaseIdealGrading
open Scheme.Modules ModularCurves InvertibleSheafBaseIdeal CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory

/-- Every actual original tensor power is invertible, with the original
structure-sheaf zeroth power and original sheafified successor powers. -/
theorem tensorPower_isInvertible {X : Scheme.{u}} {L : X.Modules}
    (hL : IsInvertible L) : ∀ n : ℕ, IsInvertible (bundleTensorPower L n)
  | 0 => isInvertible_unit
  | n + 1 => (tensorPower_isInvertible hL n).tensorObj hL

private def tensorComparison {X : Scheme.{u}} (L M : X.Modules) :
    L ⊗ M ≅ bundleTensor L M := monoidalTensorObjIso L M

/-- Canonical associators and unitors give addition of the SAME actual
original tensor powers. No tensor-power comparison is supplied as an input. -/
def tensorPowerAddIso {X : Scheme.{u}} (L : X.Modules) (m : ℕ) :
    (n : ℕ) → bundleTensorPower L m ⊗ bundleTensorPower L n ≅
      bundleTensorPower L (m + n)
  | 0 => whiskerLeftIso (bundleTensorPower L m) (monoidalUnitObjIso X).symm ≪≫
      ρ_ (bundleTensorPower L m)
  | n + 1 => whiskerLeftIso (bundleTensorPower L m)
      (tensorComparison (bundleTensorPower L n) L).symm ≪≫
    (α_ (bundleTensorPower L m) (bundleTensorPower L n) L).symm ≪≫
    (tensorPowerAddIso L m n ⊗ᵢ Iso.refl L) ≪≫
    tensorComparison (bundleTensorPower L (m + n)) L

/-- The whole base ideal of the SAME actual original tensor power, formed
using ALL original global sections rather than a chosen section family. -/
def powerBaseIdeal {X : Scheme.{u}} {L : X.Modules} (hL : IsInvertible L) (n : ℕ) :
    X.IdealSheafData := baseIdeal (tensorPower_isInvertible hL n)

/-- The WHOLE original tensor-power base ideals form a genuine graded sequence
on ANY original scheme for ANY original invertible sheaf. -/
theorem powerBaseIdeal_mul_le {X : Scheme.{u}} {L : X.Modules}
    (hL : IsInvertible L) (m n : ℕ) :
    powerBaseIdeal hL m * powerBaseIdeal hL n ≤ powerBaseIdeal hL (m + n) := by
  have hm := tensorPower_isInvertible hL m
  have hn := tensorPower_isInvertible hL n
  have hmul := InvertibleSheafBaseIdealMultiplication.baseIdeal_mul_le hm hn
  have hiso := InvertibleBaseIdealTransport.baseIdeal_eq_of_iso
    ((hm.tensorObj hn).of_iso
      (monoidalTensorObjIso (bundleTensorPower L m) (bundleTensorPower L n)))
    (tensorPower_isInvertible hL (m + n)) (tensorPowerAddIso L m n)
  exact hmul.trans_eq hiso

end EnvelopeProperty.TensorPowerBaseIdealGrading
