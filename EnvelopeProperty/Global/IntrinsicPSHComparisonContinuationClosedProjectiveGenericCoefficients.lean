import EnvelopeProperty.AlgGeom.OpenImmersionGenericCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Genuine original closed-projective polynomial coefficients in the original field

The original closed immersion supplies its ACTUAL surjective affine section
map; the ACTUAL generic germ of the original nonempty affine preimage then
has the SAME original X.functionField as its fraction field. Consequently
the original polynomial projective chart coefficients generate the ENTIRE
original field. No arbitrary section-subring fraction-field identification,
dominant ambient field map, base-algebra compatibility or M3 is assumed.
The precise scope is ring maps and whole field closure; actual k-algebra
compatibility, finite individual ratio generation and model construction
remain separate consumers.
Route: owned `closed-projective-generic-coefficients-route.tex`.
-/
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGenericCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} [IsIntegral X]

/-- The literal original affine-chart pullback followed by the original generic germ. -/
def closedChartGenericHom (i : X ⟶ Y) (U : Y.Opens) [Nonempty (i ⁻¹ᵁ U)] :
    Γ(Y, U) →+* X.functionField :=
  (X.germToFunctionField (i ⁻¹ᵁ U)).hom.comp (i.app U).hom

/-- Actual closed-immersion affine surjectivity gives the WHOLE original generic image. -/
theorem closedChartGenericHom_range (i : X ⟶ Y) [IsClosedImmersion i]
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty (i ⁻¹ᵁ U)] :
    Set.range (closedChartGenericHom i U) =
      Set.range (X.germToFunctionField (i ⁻¹ᵁ U)).hom := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨i.app U a, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := i.app_surjective U hU a
    exact ⟨b, rfl⟩

/-- The actual closed-chart coefficients generate the ENTIRE ORIGINAL function field. -/
theorem closedChartGenericHom_generates (i : X ⟶ Y) [IsClosedImmersion i]
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty (i ⁻¹ᵁ U)] :
    Subfield.closure (Set.range (closedChartGenericHom i U)) = ⊤ := by
  rw [closedChartGenericHom_range i U hU]
  let : IsFractionRing Γ(X, i ⁻¹ᵁ U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (i ⁻¹ᵁ U) (hU.preimage i)
  apply top_unique
  intro z _hz
  obtain ⟨a, b, _hb, hfrac⟩ := IsFractionRing.div_surjective Γ(X, i ⁻¹ᵁ U) z
  rw [← hfrac]
  exact (Subfield.closure _).div_mem (Subfield.subset_closure ⟨a, rfl⟩)
    (Subfield.subset_closure ⟨b, rfl⟩)

open Alterations Alterations.Geometry Alterations.Geometry.Segre
  Alterations.Geometry.ProjectiveIdeal

variable {k : Type u} [Field k] {n : ℕ}

/-- The literal ORIGINAL polynomial projective chart coefficients in the ORIGINAL function field. -/
def projectiveCoordinateGenericHom (i : X ⟶ projectiveSpace k n) (j : Fin (n + 1))
    [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)] :
    CoordinateRing k j →+* X.functionField :=
  (closedChartGenericHom i (coordinateChartInclusion (R := k) j).opensRange).comp
    (OpenImmersionGenericCoordinates.sectionRingEquiv
      (coordinateChartInclusion (R := k) j)).toRingHom

/-- EVERY original polynomial coefficient retains its actual original chart/pullback/generic germ. -/
theorem projectiveCoordinateGenericHom_apply (i : X ⟶ projectiveSpace k n) (j : Fin (n + 1))
    [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)] (a : CoordinateRing k j) :
    projectiveCoordinateGenericHom i j a =
      X.germToFunctionField (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)
        (i.app (coordinateChartInclusion (R := k) j).opensRange
          (OpenImmersionGenericCoordinates.sectionRingEquiv
            (coordinateChartInclusion (R := k) j) a)) := rfl

/-- A GENUINE original closed projective embedding makes these ACTUAL polynomial
coefficients generate the ENTIRE ORIGINAL field, without an assumed M3 certificate. -/
theorem projectiveCoordinateGenericHom_generates (i : X ⟶ projectiveSpace k n)
    [IsClosedImmersion i] (j : Fin (n + 1))
    [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)] :
    Subfield.closure (Set.range (projectiveCoordinateGenericHom i j)) = ⊤ := by
  have hr : Set.range (projectiveCoordinateGenericHom i j) =
      Set.range (closedChartGenericHom i (coordinateChartInclusion (R := k) j).opensRange) := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨OpenImmersionGenericCoordinates.sectionRingEquiv
        (coordinateChartInclusion (R := k) j) a, rfl⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, rfl⟩ := (OpenImmersionGenericCoordinates.sectionRingEquiv
        (coordinateChartInclusion (R := k) j)).surjective a
      exact ⟨b, rfl⟩
  rw [hr]
  exact closedChartGenericHom_generates i _
    (isAffineOpen_opensRange (coordinateChartInclusion (R := k) j))

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.closedChartGenericHom
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.closedChartGenericHom
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.closedChartGenericHom_range
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.closedChartGenericHom_range
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.closedChartGenericHom_generates
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.closedChartGenericHom_generates
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateGenericHom
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateGenericHom
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateGenericHom_apply
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateGenericHom_apply
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateGenericHom_generates
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateGenericHom_generates
