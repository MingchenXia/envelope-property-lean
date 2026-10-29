import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationOriginalAffineChartFactorSections

/-!
# Literal original generic projective coordinate values and cross-pivot identities

The actual original generic-point/chart factors are constructed once in the
compiled producer. This consumer derives the WHOLE original native section-map
triangle, then the literal coefficient values and actual overlap identities.
No ambient function-field map or supplied transition/frame match is used.
Route: owned `original-projective-generic-transitions-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Alterations Alterations.Geometry Alterations.Geometry.Segre
  Alterations.Geometry.ProjectiveIdeal
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGenericCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k] {n : ℕ}
variable (i : X ⟶ projectiveSpace k n) (j : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)]

/-- EVERY actual original polynomial pullback is its SAME literal original chart/pullback/generic germ. -/
theorem originalProjectiveGenericChartFactor_pullRingHom (a : CoordinateRing k j) :
    (Scheme.ΓSpecIso X.functionField).hom
      (pullRingHom (originalProjectiveGenericChartFactor i j) a) =
        projectiveCoordinateGenericHom i j a := by
  have ha := ConcreteCategory.congr_hom
    (originalProjectiveGenericChartFactor_sectionsTriangle i j) a
  have hv := congrArg (fun z : Γ(Spec X.functionField, ⊤) =>
    (Scheme.ΓSpecIso X.functionField).hom z) ha
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply,
    CommRingCat.hom_ofHom] at hv
  change (Scheme.ΓSpecIso X.functionField).hom
      (pullRingHom (originalProjectiveGenericChartFactor i j) a) =
    X.germToFunctionField (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)
      (i.app (coordinateChartInclusion (R := k) j).opensRange
        (OpenImmersionGenericCoordinates.sectionRingEquiv
          (coordinateChartInclusion (R := k) j) a)) at hv
  exact hv

variable (s : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)]

/-- A second genuinely nonempty ORIGINAL pivot gives an ACTUAL nonzero original coordinate value. -/
theorem originalProjectiveGenericCoordinate_pivot_ne_zero :
    projectiveCoordinateGenericHom i j (coordinateDehomCoord j s) ≠ 0 := by
  let l := originalProjectiveGenericChartFactor i j
  let m := originalProjectiveGenericChartFactor i s
  have hw : l ≫ coordinateChartInclusion j = m ≫ coordinateChartInclusion s :=
    (originalProjectiveGenericChartFactor_fac i j).trans
      (originalProjectiveGenericChartFactor_fac i s).symm
  have hu := ((coordinateChart_transition j s l m hw).1).map
    ((Scheme.ΓSpecIso X.functionField).hom.hom)
  rw [originalProjectiveGenericChartFactor_pullRingHom] at hu
  exact hu.ne_zero

/-- EVERY actual original coordinate retains the genuine cross-pivot identity in original K(X). -/
theorem originalProjectiveGenericCoordinate_cross (l : Fin (n + 1)) :
    projectiveCoordinateGenericHom i j (coordinateDehomCoord j l) =
      projectiveCoordinateGenericHom i s (coordinateDehomCoord s l) *
        projectiveCoordinateGenericHom i j (coordinateDehomCoord j s) := by
  let f := originalProjectiveGenericChartFactor i j
  let g := originalProjectiveGenericChartFactor i s
  have hw : f ≫ coordinateChartInclusion j = g ≫ coordinateChartInclusion s :=
    (originalProjectiveGenericChartFactor_fac i j).trans
      (originalProjectiveGenericChartFactor_fac i s).symm
  have hc := (coordinateChart_transition j s f g hw).2.2 l
  have hv := congrArg (fun z : Γ(Spec X.functionField, ⊤) =>
    (Scheme.ΓSpecIso X.functionField).hom z) hc
  dsimp only [f, g] at hv
  simp only [map_mul] at hv
  rw [originalProjectiveGenericChartFactor_pullRingHom i j (coordinateDehomCoord j l),
    originalProjectiveGenericChartFactor_pullRingHom i s (coordinateDehomCoord s l),
    originalProjectiveGenericChartFactor_pullRingHom i j (coordinateDehomCoord j s)] at hv
  exact hv

/-- Actual quotient coordinates on EVERY genuine original nonempty chart are the SAME original functions. -/
theorem originalProjectiveGenericCoordinate_quotient (l : Fin (n + 1)) :
    projectiveCoordinateGenericHom i j (coordinateDehomCoord j l) /
      projectiveCoordinateGenericHom i j (coordinateDehomCoord j s) =
        projectiveCoordinateGenericHom i s (coordinateDehomCoord s l) := by
  rw [originalProjectiveGenericCoordinate_cross i j s l]
  exact mul_div_cancel_right₀ _ (originalProjectiveGenericCoordinate_pivot_ne_zero i j s)

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalProjectiveGenericChartFactor_pullRingHom
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalProjectiveGenericChartFactor_pullRingHom

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalProjectiveGenericCoordinate_pivot_ne_zero
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalProjectiveGenericCoordinate_pivot_ne_zero

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalProjectiveGenericCoordinate_cross
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalProjectiveGenericCoordinate_cross

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalProjectiveGenericCoordinate_quotient
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalProjectiveGenericCoordinate_quotient
