import EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSections
import EnvelopeProperty.Vanishing.NadelAuxiliaryMulticover
import EnvelopeProperty.AlgGeom.TensorPowerBaseIdealGrading
/-! # The original power line, degree and genuine inclusion section give actual auxiliary cyclic data -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsData
open NadelAuxiliaryBranchSections NadelAuxiliaryMulticover CanonicalGeometry
variable {X : Scheme.{u}}

abbrev auxiliarySection (L : X.Modules) (m : ℕ) (D : X.IdealSheafData)
    (α : unitObj X ⟶ tensorObj (bundleTensorPower L m) D.toModules) : AuxiliarySection X :=
  { line := L, degree := m, sectionHom := branchSection (bundleTensorPower L m) D α }

theorem auxiliarySection_branch (L : X.Modules) (hL : IsInvertible L) (m : ℕ)
    (D : X.IdealSheafData) (hD : D.IsInvertible)
    (α : unitObj X ⟶ tensorObj (bundleTensorPower L m) D.toModules) :
    LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L m)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m) (auxiliarySection L m D α).sectionHom =
      D * LineSectionZeroIdeal.zeroIdeal (tensorObj (bundleTensorPower L m) D.toModules)
        ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m).tensorObj hD.isInvertibleModule_toModules) α :=
  zeroIdeal_branch (bundleTensorPower L m) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m) D hD α

end EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsData
