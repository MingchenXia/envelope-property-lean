import EnvelopeProperty.AlgGeom.GeneratedLineProjectiveTwist
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Actual original generator coefficients in the SAME intrinsic function field -/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.GeneratedLineGenericCoordinates
open GeneratedLineProjectiveTwist GeneratedLineLocalCoefficients SchemeGeneratedLineCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} [IsIntegral X] {L : X.Modules}

/-- A genuine original generator-frame affine site, internally selected at the actual generic point. -/
def frameSite (hL : IsInvertible L) (G : L.GeneratingSections) : GeneratorAffineSite G :=
  Classical.choose (generatorCover hL G (genericPoint X))

/-- The SAME original generator which trivializes the original line on this actual affine open. -/
def pivot (hL : IsInvertible L) (G : L.GeneratingSections) : G.I :=
  (frameSite hL G).val.2

/-- The TRUE original generic coefficient, using the SAME original affine generator frame. -/
def coefficient (hL : IsInvertible L) (G : L.GeneratingSections) (i : G.I) : X.functionField := by
  let a := frameSite hL G
  letI : Nonempty a.val.1.1 := a.property.1
  exact X.germToFunctionField a.val.1.1
    (a.val.1.1.topIso.hom.hom (localCoefficient G a.val.1.1 (localFrame G a) i))

/-- The actual original pivot has generic coefficient EXACTLY one, derived from the original frame. -/
theorem coefficient_pivot (hL : IsInvertible L) (G : L.GeneratingSections) :
    coefficient hL G (pivot hL G) = 1 := by
  let a := frameSite hL G
  let : Nonempty a.val.1.1 := a.property.1
  change X.germToFunctionField a.val.1.1
    (a.val.1.1.topIso.hom.hom (localCoefficient G a.val.1.1 (localFrame G a) a.val.2)) = 1
  rw [show localCoefficient G a.val.1.1 (localFrame G a) a.val.2 = 1 from localFrame_coefficient G a,
    map_one, map_one]

/-- The literal original finite generic coefficient tuple with the SAME projective zero padding. -/
def paddedCoefficient (hL : IsInvertible L) (G : L.GeneratingSections) [Fintype G.I] :
    Fin (Fintype.card G.I + 1) → X.functionField :=
  paddedCoefficients (coefficient hL G)

/-- The finite tuple retains the SAME original nonzero pivot, with value one in K(X). -/
theorem paddedCoefficient_pivot (hL : IsInvertible L) (G : L.GeneratingSections) [Fintype G.I] :
    paddedCoefficient hL G (((Fintype.equivFin G.I) (pivot hL G)).succ) = 1 := by
  simp only [paddedCoefficient, paddedCoefficients, Fin.cases_succ, Equiv.symm_apply_apply,
    coefficient_pivot]

end EnvelopeProperty.GeneratedLineGenericCoordinates
