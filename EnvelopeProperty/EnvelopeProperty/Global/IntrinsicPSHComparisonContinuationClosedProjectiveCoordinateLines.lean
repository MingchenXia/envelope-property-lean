import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveHyperplaneIdeals
import EnvelopeProperty.AlgGeom.ProjectiveCoordinateIdealBaseChange
import ModularCurves.Picard.DualPullback.Iso

/-!
# Actual ORIGINAL coordinate line through the WHOLE hyperplane ideal equality

The original Cartier property is internally produced, then genuine canonical
ideal-module pullback maps and actual dual pullback give the original O(1).
Route: owned `closed-projective-coordinate-lines-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open DeJongAlterations DeJongAlterations.Geometry DeJongAlterations.Geometry.Segre
  DeJongAlterations.Geometry.ProjectiveIdeal MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual native hyperplane KERNEL IDEAL is Cartier for every actual nonzero coordinate. -/
theorem nativeRankOneHyperplaneKer_isInvertible {k K : Type u}
    [Field k] [Field K] [Algebra k K] (M : MultiModel k K 1)
    (l : Fin (M.M 0 + 1)) (hl : M.coord 0 l ≠ 0) :
    (M.nativeRankOneHyperplaneInclusion l).ker.IsInvertible := by
  intro y
  have hy : y ∈ ⨆ s, M.nativeRankOneCoordinateOpen s := by
    rw [M.nativeRankOne_iSup_coordinateOpen]
    trivial
  obtain ⟨s, hs⟩ := Opens.mem_iSup.mp hy
  have hcs : M.coord 0 s ≠ 0 := by
    intro hz
    have he : M.coordElem ⟨0, s⟩ = 0 := Subtype.ext (by simp [hz])
    change M.coordElem ⟨0, s⟩ ∉ y.asHomogeneousIdeal at hs
    exact hs (he ▸ zero_mem y.asHomogeneousIdeal.toIdeal)
  exact ⟨⟨M.nativeRankOneCoordinateOpen s, M.nativeRankOneCoordinateOpen_isAffine s⟩,
    hs, M.nativeRankOneHyperplaneLocalEquation s l,
    M.nativeRankOneHyperplaneLocalEquation_mem_nonZeroDivisors s l hcs hl,
    M.nativeRankOneHyperplaneLocalEquation_span s l⟩

end EnvelopeProperty.MultiModel
namespace EnvelopeProperty.ClosedProjectiveGenericCoefficients
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {n : ℕ}
variable (i : X ⟶ projectiveSpace k n) [IsClosedImmersion i] (j : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)]

/-- The actual ORIGINAL reference hyperplane comap is Cartier, with no admissibility input. -/
theorem originalReferenceHyperplane_comap_isInvertible :
    ((coordinateHyperplaneι (R := k) j).ker.comap i).IsInvertible := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let F := fixedOriginalNativeMap i j
  have hj : M.coord 0 j ≠ 0 := fixedOriginalCoordinateModel_pivot_ne_zero i j j 0
  have hI := M.nativeRankOneHyperplaneKer_isInvertible j hj
  let : IsIso F := by
    change IsIso (fixedOriginalNativeIso i j).hom
    infer_instance
  have hF := hI.comap_of_flat F
  exact (fixedOriginalNativeMap_hyperplaneIdeal i j j) ▸ hF

/-- Actual canonical ideal comap maps and the WHOLE ideal equality produce the genuine ideal-module iso. -/
def fixedOriginalNativeCoordinateIdealPullbackIso :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    (Scheme.Modules.pullback (fixedOriginalNativeMap i j)).obj
        (ModularCurves.idealModule (M.nativeRankOneHyperplaneInclusion j)) ≅
      (Scheme.Modules.pullback i).obj
        (ModularCurves.idealModule (coordinateHyperplaneι (R := k) j)) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let F := fixedOriginalNativeMap i j
  let I := (M.nativeRankOneHyperplaneInclusion j).ker
  let J := (coordinateHyperplaneι (R := k) j).ker
  letI : IsClosedImmersion (coordinateHyperplaneι (R := k) j) :=
    coordinateHyperplaneι_isClosedImmersion j
  have hI : I.IsInvertible := M.nativeRankOneHyperplaneKer_isInvertible j
    (fixedOriginalCoordinateModel_pivot_ne_zero i j j 0)
  have hJ : J.IsInvertible := ProjectiveCoordinateIdealBaseChange.coordinateHyperplane_ker_isInvertible j
  have hi : (J.comap i).IsInvertible := originalReferenceHyperplane_comap_isInvertible i j
  have hF : (I.comap F).IsInvertible :=
    (fixedOriginalNativeMap_hyperplaneIdeal i j j).symm ▸ hi
  letI : IsIso (I.toModulesComapPullbackMap F) :=
    hI.toModulesComapPullbackMap_isIso_of_isInvertible_comap F hF
  letI : IsIso (J.toModulesComapPullbackMap i) :=
    hJ.toModulesComapPullbackMap_isIso_of_isInvertible_comap i hi
  exact (Scheme.Modules.pullback F).mapIso
      (MorphismKernelIdealModuleComparison.kernelIdealModuleIso
        (M.nativeRankOneHyperplaneInclusion j)).symm ≪≫
    asIso (I.toModulesComapPullbackMap F) ≪≫
    Scheme.IdealSheafData.toModulesEqualityIso _ _
      (fixedOriginalNativeMap_hyperplaneIdeal i j j) ≪≫
    (asIso (J.toModulesComapPullbackMap i)).symm ≪≫
    (Scheme.Modules.pullback i).mapIso
      (MorphismKernelIdealModuleComparison.kernelIdealModuleIso
        (coordinateHyperplaneι (R := k) j))

/-- The literal native coordinate pole line pulls back to the ORIGINAL polynomial-projective O(1). -/
def fixedOriginalNativeCoordinateLinePullbackIso :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    (Scheme.Modules.pullback (fixedOriginalNativeMap i j)).obj
        (M.nativeRankOneCoordinateLine j) ≅
      (Scheme.Modules.pullback i).obj (coordinateHyperplanePoleSheaf (R := k) j) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let F := fixedOriginalNativeMap i j
  exact Scheme.Modules.dualPullbackIsoOfIsInvertible F
      (ModularCurves.idealModule (M.nativeRankOneHyperplaneInclusion j))
      (M.nativeRankOneHyperplaneIdealModule_isInvertible j
        (fixedOriginalCoordinateModel_pivot_ne_zero i j j 0)) ≪≫
    (Scheme.Modules.dualIsoObj (fixedOriginalNativeCoordinateIdealPullbackIso i j)).symm ≪≫
    (Scheme.Modules.dualPullbackIsoOfIsInvertible i
      (ModularCurves.idealModule (coordinateHyperplaneι (R := k) j))
      (coordinateHyperplaneIdealModule_isInvertible j)).symm

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.MultiModel.nativeRankOneHyperplaneKer_isInvertible
#print axioms EnvelopeProperty.MultiModel.nativeRankOneHyperplaneKer_isInvertible
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalReferenceHyperplane_comap_isInvertible
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalReferenceHyperplane_comap_isInvertible
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateIdealPullbackIso
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateIdealPullbackIso
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateLinePullbackIso
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateLinePullbackIso
