import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveGlobalMap

/-!
# Actual inverse native chart maps and their whole overlap compatibility

The inverse generic triangles follow from the proved original chart triangles
and the literal fixed function-field isomorphism, with no inverse matching input.
Route: owned `closed-projective-native-inverse-route.tex` (first three nodes).
-/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
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

/-- The actual inverse chart map uses the inverse constructed iso and the original open inclusion. -/
def fixedOriginalNativeInverseChartMap :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    ((originalRankOneCoordinateModel i j).nativeRankOneCoordinateOpen s).toScheme ⟶ X := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  exact (fixedOriginalNativeCoordinateChartIso i j s).inv ≫
    (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange).ι

/-- Every actual inverse native chart map has the SAME fixed-reference whole generic Scheme triangle. -/
theorem fixedOriginalNativeInverseChartMap_genericTriangle :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    let U := M.nativeRankOneCoordinateOpen s
    letI := M.nativeRankOneCoordinateOpen_nonempty (fun _ => s)
      (fun d => fixedOriginalCoordinateModel_pivot_ne_zero i j s d)
    let dU := U.isOpen.dense (by simpa using (inferInstance : Nonempty U))
    DenseOpenGenericFieldLift.lift U dU ≫ fixedOriginalNativeInverseChartMap i j s =
      Spec.map (CommRingCat.ofHom (M.nativeRankOneFunctionFieldEquiv (fun _ => j)
        (fun d => fixedOriginalCoordinateModel_pivot_ne_zero i j j d)).toRingHom) ≫
        X.fromSpecStalk (genericPoint X) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let U := M.nativeRankOneCoordinateOpen s
  let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
  let _ := M.nativeRankOneCoordinateOpen_nonempty (fun _ => s)
    (fun d => fixedOriginalCoordinateModel_pivot_ne_zero i j s d)
  let dU := U.isOpen.dense (by simpa using (inferInstance : Nonempty U))
  let dV := V.isOpen.dense (by simpa using (inferInstance : Nonempty V))
  let lU := DenseOpenGenericFieldLift.lift U dU
  let lV := DenseOpenGenericFieldLift.lift V dV
  let e := fixedOriginalNativeCoordinateChartIso i j s
  let Φ := M.nativeRankOneFunctionFieldEquiv (fun _ => j)
    (fun d => fixedOriginalCoordinateModel_pivot_ne_zero i j j d)
  let a := Spec.map (CommRingCat.ofHom Φ.toRingHom)
  let b := Spec.map (CommRingCat.ofHom Φ.symm.toRingHom)
  have hab : a ≫ b = 𝟙 _ := by
    change Spec.map Φ.toCommRingCatIso.hom ≫ Spec.map Φ.toCommRingCatIso.inv = _
    rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  have hf : lV ≫ e.hom ≫ U.ι = b ≫
      M.nativeRankOneScheme.fromSpecStalk (genericPoint M.nativeRankOneScheme) := by
    exact fixedOriginalNativeCoordinateChartIso_genericTriangle i j s
  have hl : a ≫ lV ≫ e.hom = lU := by
    apply (cancel_mono U.ι).mp
    calc
      (a ≫ lV ≫ e.hom) ≫ U.ι = a ≫ (lV ≫ e.hom ≫ U.ι) := by simp only [Category.assoc]
      _ = a ≫ (b ≫ M.nativeRankOneScheme.fromSpecStalk
          (genericPoint M.nativeRankOneScheme)) := by rw [hf]
      _ = M.nativeRankOneScheme.fromSpecStalk (genericPoint M.nativeRankOneScheme) := by
        rw [← Category.assoc, hab, Category.id_comp]
      _ = lU ≫ U.ι := (DenseOpenGenericFieldLift.lift_inclusion U dU).symm
  change lU ≫ (e.inv ≫ V.ι) = a ≫ X.fromSpecStalk (genericPoint X)
  rw [← hl]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [DenseOpenGenericFieldLift.lift_inclusion V dV]

variable (t : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) t).opensRange)]

/-- The constructed inverse chart maps agree on ENTIRE actual native Scheme intersections. -/
theorem fixedOriginalNativeInverseChartMap_overlap :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    let Us := M.nativeRankOneCoordinateOpen s
    let Ut := M.nativeRankOneCoordinateOpen t
    M.nativeRankOneScheme.homOfLE (show Us ⊓ Ut ≤ Us from inf_le_left) ≫
        fixedOriginalNativeInverseChartMap i j s =
      M.nativeRankOneScheme.homOfLE (show Us ⊓ Ut ≤ Ut from inf_le_right) ≫
        fixedOriginalNativeInverseChartMap i j t := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let Y := M.nativeRankOneScheme
  let Us := M.nativeRankOneCoordinateOpen s
  let Ut := M.nativeRankOneCoordinateOpen t
  let _ := M.nativeRankOneCoordinateOpen_nonempty (fun _ => s)
    (fun d => fixedOriginalCoordinateModel_pivot_ne_zero i j s d)
  let _ := M.nativeRankOneCoordinateOpen_nonempty (fun _ => t)
    (fun d => fixedOriginalCoordinateModel_pivot_ne_zero i j t d)
  have hsη : genericPoint Y ∈ Us :=
    M.nativeRankOneGenericPoint_mem_coordinateOpen (fun _ => s)
      (fun d => fixedOriginalCoordinateModel_pivot_ne_zero i j s d)
  have htη : genericPoint Y ∈ Ut :=
    M.nativeRankOneGenericPoint_mem_coordinateOpen (fun _ => t)
      (fun d => fixedOriginalCoordinateModel_pivot_ne_zero i j t d)
  let W := Us ⊓ Ut
  let : Nonempty W := ⟨⟨genericPoint Y, hsη, htη⟩⟩
  let dW := W.isOpen.dense (by simpa using (inferInstance : Nonempty W))
  let ds := Us.isOpen.dense (by simpa using (inferInstance : Nonempty Us))
  let dt := Ut.isOpen.dense (by simpa using (inferInstance : Nonempty Ut))
  let lW := DenseOpenGenericFieldLift.lift W dW
  let ls := DenseOpenGenericFieldLift.lift Us ds
  let lt := DenseOpenGenericFieldLift.lift Ut dt
  let fs := fixedOriginalNativeInverseChartMap i j s
  let ft := fixedOriginalNativeInverseChartMap i j t
  have hls : lW ≫ Y.homOfLE (show W ≤ Us from inf_le_left) = ls := by
    apply (cancel_mono Us.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι Y (show W ≤ Us from inf_le_left)]
    exact (DenseOpenGenericFieldLift.lift_inclusion W dW).trans
      (DenseOpenGenericFieldLift.lift_inclusion Us ds).symm
  have hlt : lW ≫ Y.homOfLE (show W ≤ Ut from inf_le_right) = lt := by
    apply (cancel_mono Ut.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι Y (show W ≤ Ut from inf_le_right)]
    exact (DenseOpenGenericFieldLift.lift_inclusion W dW).trans
      (DenseOpenGenericFieldLift.lift_inclusion Ut dt).symm
  let : IsDominant lW := DenseOpenGenericFieldLift.lift_isDominant W dW
  let : X.IsSeparated := ⟨by
    have h : IsSeparated ((i ≫ projectiveSpaceStructure k n) ≫
        terminal.from (Spec (.of k))) := inferInstance
    simpa only [terminal.comp_from] using h⟩
  let Φ := M.nativeRankOneFunctionFieldEquiv (fun _ => j)
    (fun d => fixedOriginalCoordinateModel_pivot_ne_zero i j j d)
  let q := Spec.map (CommRingCat.ofHom Φ.toRingHom) ≫ X.fromSpecStalk (genericPoint X)
  have hs : ls ≫ fs = q := by
    exact fixedOriginalNativeInverseChartMap_genericTriangle i j s
  have ht : lt ≫ ft = q := by
    exact fixedOriginalNativeInverseChartMap_genericTriangle i j t
  apply AlgebraicGeometry.ext_of_isDominant lW
  calc
    lW ≫ (Y.homOfLE (show W ≤ Us from inf_le_left) ≫ fs) = ls ≫ fs := by
      simpa only [Category.assoc] using congrArg (fun h => h ≫ fs) hls
    _ = q := hs
    _ = lt ≫ ft := ht.symm
    _ = lW ≫ (Y.homOfLE (show W ≤ Ut from inf_le_right) ≫ ft) := by
      simpa only [Category.assoc] using (congrArg (fun h => h ≫ ft) hlt).symm

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeInverseChartMap
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeInverseChartMap
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeInverseChartMap_genericTriangle
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeInverseChartMap_genericTriangle
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeInverseChartMap_overlap
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeInverseChartMap_overlap
