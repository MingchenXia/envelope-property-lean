import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveChartOverlaps
import Mathlib.AlgebraicGeometry.Gluing

/-!
# The actual original chart maps glue into one global native morphism

The original projective coordinate opens genuinely cover X. The proved
whole overlap equality supplies all compatibility for actual Scheme gluing.
Route: owned `closed-projective-global-map-route.tex`.
-/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open DeJongAlterations DeJongAlterations.Geometry DeJongAlterations.Geometry.Segre
  DeJongAlterations.Geometry.ProjectiveIdeal
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGenericCoefficients
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {n : ℕ}
variable (i : X ⟶ projectiveSpace k n)

/-- The actual nonempty inverse projective coordinate charts cover the original scheme. -/
def originalNonemptyCoordinateCover : X.OpenCover :=
  Scheme.Cover.mkOfCovers
    {s : Fin (n + 1) // Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)}
    (fun s => (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s.val).opensRange).toScheme)
    (fun s => (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s.val).opensRange).ι)
    (by
      intro x
      have hx : i x ∈ (⊤ : (projectiveSpace k n).Opens) := trivial
      rw [← iSup_nativeCoordinateOpen_eq_top (R := k) (n := n)] at hx
      obtain ⟨s, hs⟩ := Opens.mem_iSup.mp hx
      change i x ∈ Proj.basicOpen (projectiveSpaceGrading k n) (MvPolynomial.X s) at hs
      rw [← coordinateChartInclusion_opensRange] at hs
      have hxs : x ∈ i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange := hs
      exact ⟨⟨s, ⟨⟨x, hxs⟩⟩⟩, ⟨x, hxs⟩, rfl⟩)

variable [IsClosedImmersion i] (j : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)]

/-- The proved whole original overlap equality supplies the actual categorical pullback condition. -/
theorem fixedOriginalNativeChartMap_pullback
    (s t : {s : Fin (n + 1) //
      Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)}) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    letI := s.property
    letI := t.property
    pullback.fst
        (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s.val).opensRange).ι
        (i ⁻¹ᵁ (coordinateChartInclusion (R := k) t.val).opensRange).ι ≫
        fixedOriginalNativeChartMap i j s.val =
      pullback.snd _ _ ≫ fixedOriginalNativeChartMap i j t.val := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let _ := s.property
  let _ := t.property
  let Vs := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s.val).opensRange
  let Vt := i ⁻¹ᵁ (coordinateChartInclusion (R := k) t.val).opensRange
  apply (cancel_epi (isPullback_opens_inf Vs Vt).isoPullback.hom).mp
  rw [(isPullback_opens_inf Vs Vt).isoPullback_hom_fst_assoc,
    (isPullback_opens_inf Vs Vt).isoPullback_hom_snd_assoc]
  exact fixedOriginalNativeChartMap_overlap i j s.val t.val

/-- The genuine original chart cover and proved compatibility produce one actual global Scheme map. -/
def fixedOriginalNativeMap :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    X ⟶ (originalRankOneCoordinateModel i j).nativeRankOneScheme := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  exact (originalNonemptyCoordinateCover i).glueMorphisms
    (fun s => by
      let _ := s.property
      exact fixedOriginalNativeChartMap i j s.val)
    (fun s t => fixedOriginalNativeChartMap_pullback i j s t)

/-- Every actual original chart restriction is literally the constructed same-model native chart map. -/
theorem fixedOriginalNativeMap_onChart (s : Fin (n + 1))
    [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)] :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange).ι ≫
        fixedOriginalNativeMap i j = fixedOriginalNativeChartMap i j s := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  have h := (originalNonemptyCoordinateCover i).ι_glueMorphisms
    (fun q => by
      let _ := q.property
      exact fixedOriginalNativeChartMap i j q.val)
    (fun q r => fixedOriginalNativeChartMap_pullback i j q r)
    ⟨s, inferInstance⟩
  exact h

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalNonemptyCoordinateCover
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalNonemptyCoordinateCover
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeChartMap_pullback
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeChartMap_pullback
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_onChart
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_onChart
