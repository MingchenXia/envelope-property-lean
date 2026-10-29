import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveInverseCharts
import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveGlobalGeneric

/-!
# Genuine native chart coverage and the actual global inverse

Original projectivity, proved actual surjectivity and true inverse-overlap
compatibility supply every part of the native gluing and both inverse identities.
Route: owned `closed-projective-native-global-inverse-route.tex`.
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

/-- Genuine surjectivity and the actual original cover produce a cover of the WHOLE native scheme. -/
def fixedOriginalNativeCoordinateCover :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (originalRankOneCoordinateModel i j).nativeRankOneScheme.OpenCover := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  exact Scheme.Cover.mkOfCovers (originalNonemptyCoordinateCover i).I₀
    (fun q => (M.nativeRankOneCoordinateOpen q.val).toScheme)
    (fun q => (M.nativeRankOneCoordinateOpen q.val).ι)
    (by
      intro y
      let _ := fixedOriginalNativeMap_surjective i j
      obtain ⟨x, hx⟩ := (fixedOriginalNativeMap i j).surjective y
      obtain ⟨q, z, hz⟩ := (originalNonemptyCoordinateCover i).exists_eq x
      let _ := q.property
      let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) q.val).opensRange
      let U := M.nativeRankOneCoordinateOpen q.val
      let e := fixedOriginalNativeCoordinateChartIso i j q.val
      have hz' : V.ι z = x := hz
      have hmap := congrArg (fun f : V.toScheme ⟶ M.nativeRankOneScheme => f z)
        (fixedOriginalNativeMap_onChart i j q.val)
      simp only [Scheme.Hom.comp_apply] at hmap
      refine ⟨q, e.hom z, ?_⟩
      calc
        U.ι (e.hom z) = fixedOriginalNativeChartMap i j q.val z := rfl
        _ = fixedOriginalNativeMap i j (V.ι z) := hmap.symm
        _ = fixedOriginalNativeMap i j x := congrArg (fixedOriginalNativeMap i j) hz'
        _ = y := hx)

/-- The proved actual inverse overlap identity supplies categorical native pullback compatibility. -/
theorem fixedOriginalNativeInverseChartMap_pullback
    (q r : (originalNonemptyCoordinateCover i).I₀) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    letI := q.property
    letI := r.property
    let M := originalRankOneCoordinateModel i j
    pullback.fst (M.nativeRankOneCoordinateOpen q.val).ι
        (M.nativeRankOneCoordinateOpen r.val).ι ≫
        fixedOriginalNativeInverseChartMap i j q.val =
      pullback.snd _ _ ≫ fixedOriginalNativeInverseChartMap i j r.val := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let _ := q.property
  let _ := r.property
  let M := originalRankOneCoordinateModel i j
  let Uq := M.nativeRankOneCoordinateOpen q.val
  let Ur := M.nativeRankOneCoordinateOpen r.val
  apply (cancel_epi (isPullback_opens_inf Uq Ur).isoPullback.hom).mp
  rw [(isPullback_opens_inf Uq Ur).isoPullback_hom_fst_assoc,
    (isPullback_opens_inf Uq Ur).isoPullback_hom_snd_assoc]
  exact fixedOriginalNativeInverseChartMap_overlap i j q.val r.val

/-- The actual inverse chart maps glue on the genuinely proved WHOLE native cover. -/
def fixedOriginalNativeInverseMap :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (originalRankOneCoordinateModel i j).nativeRankOneScheme ⟶ X := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  exact (fixedOriginalNativeCoordinateCover i j).glueMorphisms
    (fun q => by
      let _ := q.property
      exact fixedOriginalNativeInverseChartMap i j q.val)
    (fun q r => fixedOriginalNativeInverseChartMap_pullback i j q r)

/-- Every actual native restriction retains the literal constructed inverse chart map. -/
theorem fixedOriginalNativeInverseMap_onChart (s : Fin (n + 1))
    [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)] :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    ((originalRankOneCoordinateModel i j).nativeRankOneCoordinateOpen s).ι ≫
        fixedOriginalNativeInverseMap i j = fixedOriginalNativeInverseChartMap i j s := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  have h := (fixedOriginalNativeCoordinateCover i j).ι_glueMorphisms
    (fun q => by
      let _ := q.property
      exact fixedOriginalNativeInverseChartMap i j q.val)
    (fun q r => fixedOriginalNativeInverseChartMap_pullback i j q r)
    ⟨s, inferInstance⟩
  exact h

/-- The original cover proves that the actual forward map followed by its genuine glued inverse is identity. -/
theorem fixedOriginalNativeMap_inverse :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    fixedOriginalNativeMap i j ≫ fixedOriginalNativeInverseMap i j = 𝟙 X := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  apply (originalNonemptyCoordinateCover i).hom_ext
  intro q
  let _ := q.property
  change (i ⁻¹ᵁ (coordinateChartInclusion (R := k) q.val).opensRange).ι ≫
      (fixedOriginalNativeMap i j ≫ fixedOriginalNativeInverseMap i j) =
    (i ⁻¹ᵁ (coordinateChartInclusion (R := k) q.val).opensRange).ι ≫ 𝟙 X
  rw [← Category.assoc, fixedOriginalNativeMap_onChart]
  simp only [fixedOriginalNativeChartMap, Category.assoc]
  rw [fixedOriginalNativeInverseMap_onChart]
  simp only [fixedOriginalNativeInverseChartMap, Iso.hom_inv_id_assoc, Category.comp_id]

/-- The genuinely covering native charts prove the actual reverse composite is identity. -/
theorem fixedOriginalNativeInverseMap_forward :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    fixedOriginalNativeInverseMap i j ≫ fixedOriginalNativeMap i j =
      𝟙 (originalRankOneCoordinateModel i j).nativeRankOneScheme := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  apply (fixedOriginalNativeCoordinateCover i j).hom_ext
  intro q
  let _ := q.property
  change ((originalRankOneCoordinateModel i j).nativeRankOneCoordinateOpen q.val).ι ≫
      (fixedOriginalNativeInverseMap i j ≫ fixedOriginalNativeMap i j) =
    ((originalRankOneCoordinateModel i j).nativeRankOneCoordinateOpen q.val).ι ≫ 𝟙 _
  rw [← Category.assoc, fixedOriginalNativeInverseMap_onChart]
  simp only [fixedOriginalNativeInverseChartMap, Category.assoc]
  rw [fixedOriginalNativeMap_onChart]
  simp only [fixedOriginalNativeChartMap, Iso.inv_hom_id_assoc, Category.comp_id]

/-- The ORIGINAL integral projective scheme is its genuinely generated fixed native model. -/
def fixedOriginalNativeIso :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    X ≅ (originalRankOneCoordinateModel i j).nativeRankOneScheme := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  exact {
    hom := fixedOriginalNativeMap i j
    inv := fixedOriginalNativeInverseMap i j
    hom_inv_id := fixedOriginalNativeMap_inverse i j
    inv_hom_id := fixedOriginalNativeInverseMap_forward i j }

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateCover
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateCover
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeInverseChartMap_pullback
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeInverseChartMap_pullback
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeInverseMap
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeInverseMap
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeInverseMap_onChart
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeInverseMap_onChart
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_inverse
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_inverse
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeInverseMap_forward
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeInverseMap_forward
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeIso
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeIso
