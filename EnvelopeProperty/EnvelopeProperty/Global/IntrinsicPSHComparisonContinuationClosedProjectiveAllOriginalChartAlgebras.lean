import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveOriginalChartAlgebras
import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationOriginalProjectiveGenericTransitions
import EnvelopeProperty.Global.NativeRankOneChartComparison

/-!
# Every genuine original affine chart belongs to ONE fixed produced native model

The reference pivot and model are fixed once. Other original nonempty pivots
supply actual nonzero coordinates in that SAME model, and cross-pivot values
identify its ENTIRE chart with the SAME original whole section ring. We then
construct the actual original-chart/native-coordinate-open scheme iso.
Global overlap compatibility and gluing remain subsequent consumers.
Route: owned `closed-projective-all-original-chart-algebras-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
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

/-- Every genuinely nonempty original pivot is nonzero in the SAME fixed reference model. -/
theorem fixedOriginalCoordinateModel_pivot_ne_zero (c : Fin 1) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (originalRankOneCoordinateModel i j).coord c s ≠ 0 := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  rw [originalRankOneCoordinateModel_coord]
  exact originalProjectiveGenericCoordinate_pivot_ne_zero i j s

/-- Every SAME model ratio is the actual original coordinate at the new original pivot. -/
theorem fixedOriginalCoordinateModel_coord_div (c : Fin 1) (l : Fin (n + 1)) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (originalRankOneCoordinateModel i j).coord c l /
      (originalRankOneCoordinateModel i j).coord c s =
        projectiveCoordinateGenericHom i s (coordinateDehomCoord s l) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  rw [originalRankOneCoordinateModel_coord, originalRankOneCoordinateModel_coord]
  exact originalProjectiveGenericCoordinate_quotient i j s l

/-- EVERY actual chart of the SAME fixed reference model is the original polynomial coefficient image at that pivot. -/
theorem fixedOriginalCoordinateModel_chartAlg_eq_range :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (originalRankOneCoordinateModel i j).chartAlg (fun _ => s) =
      (projectiveCoordinateGenericAlgHom i s).range := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let b : M.ChartIndex := fun _ => s
  let φ := projectiveCoordinateGenericAlgHom i s
  change M.chartAlg b = φ.range
  have hG : Algebra.adjoin k (Set.range (fun t : (Σ c : Fin 1, Fin (M.M c + 1)) =>
      monomial (Finsupp.single t.1 1) (M.coord t.1 t.2))) = M.S := rfl
  apply le_antisymm
  · rw [M.chartAlg_eq_adjoin b hG]
    apply Algebra.adjoin_le_iff.mpr
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨coordinateDehomCoord s t.2, ?_⟩
    rw [M.dehom_monomial, M.chartDen_single]
    exact (fixedOriginalCoordinateModel_coord_div i j s t.1 t.2).symm
  · rintro _ ⟨a, rfl⟩
    induction a using MvPolynomial.induction_on with
    | C c =>
      change φ (algebraMap k (CoordinateRing k s) c) ∈ M.chartAlg b
      rw [φ.commutes]
      exact (M.chartAlg b).algebraMap_mem c
    | add a d ha hd =>
      rw [map_add]
      exact (M.chartAlg b).add_mem ha hd
    | mul_X a l ha =>
      rw [map_mul]
      apply (M.chartAlg b).mul_mem ha
      have hc := M.coord_div_mem_chartAlg b (0 : Fin 1) l.1
      rw [fixedOriginalCoordinateModel_coord_div i j s (0 : Fin 1) l.1] at hc
      change (projectiveCoordinateGenericAlgHom i s).toRingHom (MvPolynomial.X l) ∈ M.chartAlg b
      rw [projectiveCoordinateGenericAlgHom_toRingHom]
      simpa only [coordinateDehomCoord_ne] using hc

/-- EVERY chart of ONE fixed original model is the literal original whole section-germ image. -/
theorem fixedOriginalCoordinateModel_chartAlg_eq_originalSections :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (originalRankOneCoordinateModel i j).chartAlg (fun _ => s) =
      (i ≫ projectiveSpaceStructure k n).sectionsFunctionFieldSubalgebra
        (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  rw [fixedOriginalCoordinateModel_chartAlg_eq_range,
    ← originalRankOneCoordinateModel_chartAlg_eq_range i s,
    originalRankOneCoordinateModel_chartAlg_eq_originalSections i s]

/-- The ENTIRE original section algebra at every genuine pivot identifies the SAME fixed model chart. -/
def fixedOriginalCoordinateChartSectionsAlgEquiv :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    letI := (i ≫ projectiveSpaceStructure k n).sectionsAlgebra
      (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)
    Γ(X, i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange) ≃ₐ[k]
      (originalRankOneCoordinateModel i j).chartAlg (fun _ => s) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let _ := (i ≫ projectiveSpaceStructure k n).sectionsAlgebra
    (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)
  exact ((i ≫ projectiveSpaceStructure k n).sectionsFunctionFieldEquiv _).trans
    (Subalgebra.equivOfEq _ _
      (fixedOriginalCoordinateModel_chartAlg_eq_originalSections i j s).symm)

/-- EVERY original section keeps its SAME literal original germ through this whole fixed-model equivalence. -/
theorem fixedOriginalCoordinateChartSectionsAlgEquiv_apply
    (a : Γ(X, i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    letI := (i ≫ projectiveSpaceStructure k n).sectionsAlgebra
      (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)
    ((fixedOriginalCoordinateChartSectionsAlgEquiv i j s a :
      (originalRankOneCoordinateModel i j).chartAlg (fun _ => s)) : X.functionField) =
        X.germToFunctionField (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange) a := rfl

/-- Every original nonempty affine chart is the spectrum of its SAME fixed model chart algebra. -/
def fixedOriginalCoordinateChartIso :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange).toScheme ≅
      Spec (.of ((originalRankOneCoordinateModel i j).chartAlg (fun _ => s))) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let U := (coordinateChartInclusion (R := k) s).opensRange
  let _ := (i ≫ projectiveSpaceStructure k n).sectionsAlgebra (i ⁻¹ᵁ U)
  have hV : IsAffineOpen (i ⁻¹ᵁ U) :=
    (isAffineOpen_opensRange (coordinateChartInclusion (R := k) s)).preimage i
  exact hV.isoSpec ≪≫
    (Scheme.Spec.mapIso (fixedOriginalCoordinateChartSectionsAlgEquiv i j s).toRingEquiv.toCommRingCatIso.op).symm

/-- The actual original affine chart is the SAME fixed reference model's actual native coordinate open. -/
def fixedOriginalNativeCoordinateChartIso :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange).toScheme ≅
      ((originalRankOneCoordinateModel i j).nativeRankOneCoordinateOpen s).toScheme := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  exact fixedOriginalCoordinateChartIso i j s ≪≫
    ((originalRankOneCoordinateModel i j).nativeRankOneOriginalChartIso (fun _ => s)
      (fun c => fixedOriginalCoordinateModel_pivot_ne_zero i j s c)).symm

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateModel_pivot_ne_zero
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateModel_pivot_ne_zero
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateModel_coord_div
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateModel_coord_div
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateModel_chartAlg_eq_range
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateModel_chartAlg_eq_range
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateModel_chartAlg_eq_originalSections
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateModel_chartAlg_eq_originalSections
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateChartSectionsAlgEquiv
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateChartSectionsAlgEquiv
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateChartSectionsAlgEquiv_apply
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateChartSectionsAlgEquiv_apply
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateChartIso
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateChartIso
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateChartIso
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateChartIso
