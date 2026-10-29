import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveRankOneModel

/-!
# Actual original generic-point chart lifts

The original X need not dominate ambient projective space. We factor the
actual ORIGINAL Spec K(X)→X→projective space through genuine original charts,
retain the literal original generic-point section map and scheme triangle.
Their polynomial value law and cross-pivot identities are subsequent consumers.
No ambient function-field map or supplied coordinate transition is assumed.
Route: owned `original-projective-generic-factors-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Alterations Alterations.Geometry Alterations.Geometry.Segre
  Alterations.Geometry.ProjectiveIdeal
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGenericCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} [IsIntegral X]

/-- The original generic-point morphism's WHOLE chart pullback is the literal original generic germ. -/
theorem originalGenericPoint_appLE (U : X.Opens) [Nonempty U]
    (h : (⊤ : (Spec X.functionField).Opens) ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ U) :
    (X.fromSpecStalk (genericPoint X)).appLE U ⊤ h =
      X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv := by
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
      simpa using (inferInstance : Nonempty U))
  unfold Scheme.Hom.appLE
  rw [Scheme.fromSpecStalk_app hη]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [← Category.assoc]
  suffices (Spec X.functionField).presheaf.map
      ((homOfLE (show X.fromSpecStalk (genericPoint X) ⁻¹ᵁ U ≤ ⊤ from le_top)).op ≫
        (homOfLE h).op) = 𝟙 Γ(Spec X.functionField, ⊤) by
    rw [this, Category.comp_id]
  convert (Spec X.functionField).presheaf.map_id (Opposite.op ⊤) using 1
  congr 1

variable {k : Type u} [Field k] {n : ℕ}
variable (i : X ⟶ projectiveSpace k n) (j : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)]

/-- The ACTUAL original generic-point projective morphism genuinely factors through its same original chart. -/
def originalProjectiveGenericChartFactor :
    Spec X.functionField ⟶ Spec (.of (CoordinateRing k j)) :=
  IsOpenImmersion.lift (coordinateChartInclusion (R := k) j)
    (X.fromSpecStalk (genericPoint X) ≫ i) (by
      rintro _ ⟨t, rfl⟩
      let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange
      have hη : genericPoint X ∈ V :=
        ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by
          simpa using (inferInstance : Nonempty V))
      have hs : X.fromSpecStalk (genericPoint X) t ⤳ genericPoint X :=
        Scheme.range_fromSpecStalk.le ⟨t, rfl⟩
      exact hs.mem_open V.isOpen hη)

/-- Its entire ORIGINAL scheme triangle is internally produced. -/
theorem originalProjectiveGenericChartFactor_fac :
    originalProjectiveGenericChartFactor i j ≫ coordinateChartInclusion j =
      X.fromSpecStalk (genericPoint X) ≫ i :=
  IsOpenImmersion.lift_fac _ _ _

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalGenericPoint_appLE
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalGenericPoint_appLE

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalProjectiveGenericChartFactor
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalProjectiveGenericChartFactor

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalProjectiveGenericChartFactor_fac
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalProjectiveGenericChartFactor_fac
