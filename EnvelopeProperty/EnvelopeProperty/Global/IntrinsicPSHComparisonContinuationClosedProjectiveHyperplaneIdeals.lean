import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveHyperplanePullbacks
import EnvelopeProperty.Berkovich.SchemeIdealPullback

/-!
# The SAME actual whole hyperplane ideal on the ORIGINAL projective scheme

Literal whole-section equations identify actual affine ideal comaps; the
actual original affine cover identifies ENTIRE ideal sheaves. All numerator
coordinates, including zero coordinates, are retained.
Route: owned `closed-projective-hyperplane-ideals-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open DeJongAlterations DeJongAlterations.Geometry DeJongAlterations.Geometry.Segre
  DeJongAlterations.Geometry.ProjectiveIdeal MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGenericCoefficients
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {n : ℕ}
variable (i : X ⟶ projectiveSpace k n) [IsClosedImmersion i] (j : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)]

/-- Both actual GLOBAL section pullbacks give the same literal original hyperplane equation. -/
theorem fixedOriginalNativeMap_hyperplane_appLE (s : Fin (n + 1))
    [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)]
    (l : Fin (n + 1)) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
    let hC : V ≤ i ⁻¹ᵁ coordinateOpen (R := k) s := by
      rw [← projectiveCoordinateChart_opensRange (R := k) s]
    (fixedOriginalNativeMap i j).appLE (M.nativeRankOneCoordinateOpen s) V
        (fixedOriginalNativeMap_chartContainment i j s)
        (M.nativeRankOneHyperplaneLocalEquation s l) =
      i.appLE (coordinateOpen s) V hC (coordinateHyperplaneLocalEquation s l) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  have hnat := i.map_appLE (show
    i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange ≤
      i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange from le_rfl)
    (eqToHom (projectiveCoordinateChart_opensRange (R := k) s)).op
  have hval := ConcreteCategory.congr_hom hnat
    (coordinateHyperplaneLocalEquation (R := k) s l)
  have happ : i.appLE (coordinateChartInclusion (R := k) s).opensRange
      (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange) le_rfl =
      i.app (coordinateChartInclusion (R := k) s).opensRange := by
    simp [Scheme.Hom.appLE]
  rw [happ] at hval
  exact (fixedOriginalNativeMap_hyperplane i j s l).trans hval

/-- Actual affine ideal comaps agree, using the actual original and native principal generators. -/
theorem fixedOriginalNativeMap_hyperplaneIdeal_onChart (s : Fin (n + 1))
    [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)]
    (l : Fin (n + 1)) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    let V : X.affineOpens :=
      ⟨i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange,
        (isAffineOpen_opensRange (coordinateChartInclusion (R := k) s)).preimage i⟩
    ((M.nativeRankOneHyperplaneInclusion l).ker.comap
        (fixedOriginalNativeMap i j)).ideal V =
      ((coordinateHyperplaneι (R := k) l).ker.comap i).ideal V := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let V : X.affineOpens :=
    ⟨i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange,
      (isAffineOpen_opensRange (coordinateChartInclusion (R := k) s)).preimage i⟩
  let U : M.nativeRankOneScheme.affineOpens :=
    ⟨M.nativeRankOneCoordinateOpen s, M.nativeRankOneCoordinateOpen_isAffine s⟩
  let P : (projectiveSpace k n).affineOpens :=
    ⟨coordinateOpen s, coordinateOpen_isAffineOpen s⟩
  have hC : V.1 ≤ i ⁻¹ᵁ P.1 := by
    change i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange ≤
      i ⁻¹ᵁ coordinateOpen (R := k) s
    rw [← projectiveCoordinateChart_opensRange (R := k) s]
  have hL := (M.nativeRankOneHyperplaneInclusion l).ker.comap_ideal_of_affine_opens
    (fixedOriginalNativeMap i j) V U (fixedOriginalNativeMap_chartContainment i j s)
  have hR := (coordinateHyperplaneι (R := k) l).ker.comap_ideal_of_affine_opens i V P hC
  have hgen : ((M.nativeRankOneHyperplaneInclusion l).ker.ideal U).map
      ((fixedOriginalNativeMap i j).appLE U.1 V.1
        (fixedOriginalNativeMap_chartContainment i j s)).hom =
      ((coordinateHyperplaneι (R := k) l).ker.ideal P).map
        (i.appLE P.1 V.1 hC).hom := by
    rw [M.nativeRankOneHyperplaneLocalEquation_span s l,
      coordinateHyperplaneLocalEquation_span s l,
      Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
    congr 1
    exact congrArg Set.singleton (fixedOriginalNativeMap_hyperplane_appLE i j s l)
  exact hL.trans (hgen.trans hR.symm)

/-- The actual original affine cover identifies the ENTIRE original and native hyperplane ideal comaps. -/
theorem fixedOriginalNativeMap_hyperplaneIdeal (l : Fin (n + 1)) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    (M.nativeRankOneHyperplaneInclusion l).ker.comap (fixedOriginalNativeMap i j) =
      (coordinateHyperplaneι (R := k) l).ker.comap i := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let A : (originalNonemptyCoordinateCover i).I₀ → X.affineOpens := fun s =>
    ⟨i ⁻¹ᵁ (coordinateChartInclusion (R := k) s.val).opensRange,
      (isAffineOpen_opensRange (coordinateChartInclusion (R := k) s.val)).preimage i⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top A
  · apply le_antisymm le_top
    intro x _
    obtain ⟨s, y, hy⟩ := (originalNonemptyCoordinateCover i).exists_eq x
    apply Opens.mem_iSup.mpr
    refine ⟨s, ?_⟩
    change y.val = x at hy
    exact hy ▸ y.property
  · intro s
    let _ := s.property
    exact fixedOriginalNativeMap_hyperplaneIdeal_onChart i j s.val l

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_hyperplane_appLE
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_hyperplane_appLE
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_hyperplaneIdeal_onChart
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_hyperplaneIdeal_onChart
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_hyperplaneIdeal
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_hyperplaneIdeal
