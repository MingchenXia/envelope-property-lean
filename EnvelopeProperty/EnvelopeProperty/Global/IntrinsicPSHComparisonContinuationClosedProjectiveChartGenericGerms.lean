import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveChartPullbacks
import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationNativeFunctionField

/-!
# The actual original/native chart pullback preserves every original generic germ

The model is fixed ONCE at the original reference pivot. Its actual field
comparison has proved pivot independence and genuine M3. We apply it to
the literal whole-section pullback of the actual constructed scheme iso.
No field/germ/section matching premise is supplied.
Route: owned `closed-projective-chart-generic-germs-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open DeJongAlterations DeJongAlterations.Geometry DeJongAlterations.Geometry.Segre
  DeJongAlterations.Geometry.ProjectiveIdeal
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGenericCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {n : ℕ}
variable (i : X ⟶ projectiveSpace k n) [IsClosedImmersion i] (j : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)]
variable (s : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)]

/-- EVERY actual original section's geometric chart pullback keeps its SAME original germ under ONE fixed native field comparison. -/
theorem fixedOriginalNativeCoordinateChartIso_genericGerm
    (a : Γ(X, i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
    let U := M.nativeRankOneCoordinateOpen s
    M.nativeRankOneGenericGerm (fun _ => s)
      (fun c => fixedOriginalCoordinateModel_pivot_ne_zero i j s c)
      ((V.topIso.inv ≫ (fixedOriginalNativeCoordinateChartIso i j s).inv.appTop ≫
        U.topIso.hom).hom a) =
      M.nativeRankOneFunctionFieldEquiv (fun _ => j)
        (fun c => fixedOriginalCoordinateModel_pivot_ne_zero i j j c)
        (X.germToFunctionField V a) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
  let _ := (i ≫ projectiveSpaceStructure k n).sectionsAlgebra V
  let M := originalRankOneCoordinateModel i j
  let U := M.nativeRankOneCoordinateOpen s
  let b : M.ChartIndex := fun _ => s
  let bj : M.ChartIndex := fun _ => j
  let hb := fun c => fixedOriginalCoordinateModel_pivot_ne_zero i j s c
  let hj := fun c => fixedOriginalCoordinateModel_pivot_ne_zero i j j c
  let E := fixedOriginalCoordinateChartSectionsAlgEquiv i j s
  have hv := ConcreteCategory.congr_hom (fixedOriginalNativeCoordinateChartIso_sections i j s) a
  change (V.topIso.inv ≫ (fixedOriginalNativeCoordinateChartIso i j s).inv.appTop ≫
    U.topIso.hom).hom a = (M.nativeRankOneOriginalSectionsIso b hb).hom (E a) at hv
  have hg : ((E a : M.chartAlg b) : X.functionField) = X.germToFunctionField V a :=
    fixedOriginalCoordinateChartSectionsAlgEquiv_apply i j s a
  change M.nativeRankOneGenericGerm b hb _ = M.nativeRankOneFunctionFieldEquiv bj hj _
  calc
    M.nativeRankOneGenericGerm b hb
        ((V.topIso.inv ≫ (fixedOriginalNativeCoordinateChartIso i j s).inv.appTop ≫
          U.topIso.hom).hom a) =
        M.nativeRankOneGenericGerm b hb ((M.nativeRankOneOriginalSectionsIso b hb).hom (E a)) :=
      congrArg (M.nativeRankOneGenericGerm b hb) hv
    _ = M.nativeRankOneFunctionFieldEquiv b hb ((E a : M.chartAlg b) : X.functionField) :=
      (M.nativeRankOneFunctionFieldEquiv_coefficient b hb (E a)).symm
    _ = M.nativeRankOneFunctionFieldEquiv bj hj (X.germToFunctionField V a) := by
      rw [M.nativeRankOneFunctionFieldEquiv_independent b bj hb hj, hg]

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateChartIso_genericGerm
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateChartIso_genericGerm
