import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveGenericSchemeTriangles
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The actual same-model chart maps agree on entire original overlaps

Whole generic Scheme triangles and the EXISTING genuine dominant generic
lifts imply actual Scheme-map equality on the whole reduced overlap, by the
native separated-target theorem. No overlap compatibility is assumed.
Route: owned `closed-projective-chart-overlaps-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Alterations Alterations.Geometry Alterations.Geometry.Segre
  Alterations.Geometry.ProjectiveIdeal
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

/-- The actual original chart map is its SAME fixed native chart iso followed by the native open inclusion. -/
def fixedOriginalNativeChartMap :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange).toScheme ⟶
      (originalRankOneCoordinateModel i j).nativeRankOneScheme := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  exact (fixedOriginalNativeCoordinateChartIso i j s).hom ≫
    ((originalRankOneCoordinateModel i j).nativeRankOneCoordinateOpen s).ι

variable (t : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) t).opensRange)]

/-- The actual SAME-model chart maps agree on the ENTIRE original Scheme overlap. -/
theorem fixedOriginalNativeChartMap_overlap :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let Vs := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
    let Vt := i ⁻¹ᵁ (coordinateChartInclusion (R := k) t).opensRange
    X.homOfLE (show Vs ⊓ Vt ≤ Vs from inf_le_left) ≫ fixedOriginalNativeChartMap i j s =
      X.homOfLE (show Vs ⊓ Vt ≤ Vt from inf_le_right) ≫ fixedOriginalNativeChartMap i j t := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let Vs := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
  let Vt := i ⁻¹ᵁ (coordinateChartInclusion (R := k) t).opensRange
  let W := Vs ⊓ Vt
  have hsη : genericPoint X ∈ Vs :=
    ((genericPoint_spec X).mem_open_set_iff Vs.isOpen).mpr (by
      simpa using (inferInstance : Nonempty Vs))
  have htη : genericPoint X ∈ Vt :=
    ((genericPoint_spec X).mem_open_set_iff Vt.isOpen).mpr (by
      simpa using (inferInstance : Nonempty Vt))
  let : Nonempty W := ⟨⟨genericPoint X, hsη, htη⟩⟩
  let dW := W.isOpen.dense (by simpa using (inferInstance : Nonempty W))
  let ds := Vs.isOpen.dense (by simpa using (inferInstance : Nonempty Vs))
  let dt := Vt.isOpen.dense (by simpa using (inferInstance : Nonempty Vt))
  let lW := DenseOpenGenericFieldLift.lift W dW
  let ls := DenseOpenGenericFieldLift.lift Vs ds
  let lt := DenseOpenGenericFieldLift.lift Vt dt
  let fs := fixedOriginalNativeChartMap i j s
  let ft := fixedOriginalNativeChartMap i j t
  have hls : lW ≫ X.homOfLE (show W ≤ Vs from inf_le_left) = ls := by
    apply (cancel_mono Vs.ι).mp
    simp only [Category.assoc, Scheme.homOfLE_ι]
    exact (DenseOpenGenericFieldLift.lift_inclusion W dW).trans
      (DenseOpenGenericFieldLift.lift_inclusion Vs ds).symm
  have hlt : lW ≫ X.homOfLE (show W ≤ Vt from inf_le_right) = lt := by
    apply (cancel_mono Vt.ι).mp
    simp only [Category.assoc, Scheme.homOfLE_ι]
    exact (DenseOpenGenericFieldLift.lift_inclusion W dW).trans
      (DenseOpenGenericFieldLift.lift_inclusion Vt dt).symm
  let : IsDominant lW := DenseOpenGenericFieldLift.lift_isDominant W dW
  let : M.nativeRankOneScheme.IsSeparated := by
    change (Proj M.nativeTotalGrading).IsSeparated
    infer_instance
  let bj : M.ChartIndex := fun _ => j
  let hj := fun c => fixedOriginalCoordinateModel_pivot_ne_zero i j j c
  let Φ := M.nativeRankOneFunctionFieldEquiv bj hj
  let q := Spec.map (CommRingCat.ofHom Φ.symm.toRingHom) ≫
    M.nativeRankOneScheme.fromSpecStalk (genericPoint M.nativeRankOneScheme)
  have hs : ls ≫ fs = q := by
    simpa only [ls, fs, q, Φ, bj, hj, M, Vs, ds, fixedOriginalNativeChartMap] using
      fixedOriginalNativeCoordinateChartIso_genericTriangle i j s
  have ht : lt ≫ ft = q := by
    simpa only [lt, ft, q, Φ, bj, hj, M, Vt, dt, fixedOriginalNativeChartMap] using
      fixedOriginalNativeCoordinateChartIso_genericTriangle i j t
  apply AlgebraicGeometry.ext_of_isDominant lW
  calc
    lW ≫ (X.homOfLE (show W ≤ Vs from inf_le_left) ≫ fs) = ls ≫ fs := by
      simpa only [Category.assoc] using congrArg (fun h => h ≫ fs) hls
    _ = q := hs
    _ = lt ≫ ft := ht.symm
    _ = lW ≫ (X.homOfLE (show W ≤ Vt from inf_le_right) ≫ ft) := by
      simpa only [Category.assoc] using (congrArg (fun h => h ≫ ft) hlt).symm

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeChartMap
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeChartMap
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeChartMap_overlap
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeChartMap_overlap
