import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveRankOneModel
import EnvelopeProperty.Global.ModelCharts

/-!
# The actual original section ring is the produced original-field model chart

Both sides are literal subalgebras of the SAME original X.functionField
with its actual composite structure action. Genuine original closed-chart
surjectivity and integral generic-germ injectivity supply the whole original
section equivalence and the actual affine-scheme chart isomorphism.
No chart, field, section or model comparison is assumed.
Route: owned `closed-projective-original-chart-algebras-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
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

/-- The ACTUAL produced model chart is exactly the SAME original polynomial coefficient image. -/
theorem originalRankOneCoordinateModel_chartAlg_eq_range :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (originalRankOneCoordinateModel i j).chartAlg (fun _ => j) =
      (projectiveCoordinateGenericAlgHom i j).range := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let b : M.ChartIndex := fun _ => j
  let φ := projectiveCoordinateGenericAlgHom i j
  change M.chartAlg b = φ.range
  have hG : Algebra.adjoin k (Set.range (fun t : (Σ c : Fin 1, Fin (M.M c + 1)) =>
      monomial (Finsupp.single t.1 1) (M.coord t.1 t.2))) = M.S := rfl
  apply le_antisymm
  · rw [M.chartAlg_eq_adjoin b hG]
    apply Algebra.adjoin_le_iff.mpr
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨coordinateDehomCoord j t.2, ?_⟩
    rw [M.dehom_monomial, M.chartDen_single]
    change projectiveCoordinateGenericHom i j (coordinateDehomCoord j t.2) =
      originalRankOneCoordinates i j t.2 / originalRankOneCoordinates i j j
    rw [originalRankOneCoordinates_pivot, div_one]
    rfl
  · rintro _ ⟨a, rfl⟩
    induction a using MvPolynomial.induction_on with
    | C c =>
      change φ (algebraMap k (CoordinateRing k j) c) ∈ M.chartAlg b
      rw [φ.commutes]
      exact (M.chartAlg b).algebraMap_mem c
    | add a d ha hd =>
      rw [map_add]
      exact (M.chartAlg b).add_mem ha hd
    | mul_X a l ha =>
      rw [map_mul]
      apply (M.chartAlg b).mul_mem ha
      have hc := M.coord_div_mem_chartAlg b (0 : Fin 1) l.1
      change originalRankOneCoordinates i j l.1 / originalRankOneCoordinates i j j ∈
        M.chartAlg b at hc
      rw [originalRankOneCoordinates_pivot, div_one] at hc
      change (projectiveCoordinateGenericAlgHom i j).toRingHom (MvPolynomial.X l) ∈ M.chartAlg b
      rw [projectiveCoordinateGenericAlgHom_toRingHom]
      simpa only [originalRankOneCoordinates, coordinateDehomCoord_ne] using hc

/-- The same model chart is the LITERAL whole original section-germ subalgebra of original K(X). -/
theorem originalRankOneCoordinateModel_chartAlg_eq_originalSections :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (originalRankOneCoordinateModel i j).chartAlg (fun _ => j) =
      (i ≫ projectiveSpaceStructure k n).sectionsFunctionFieldSubalgebra
        (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  rw [originalRankOneCoordinateModel_chartAlg_eq_range]
  let U := (coordinateChartInclusion (R := k) j).opensRange
  let e := OpenImmersionGenericCoordinates.sectionRingEquiv (coordinateChartInclusion (R := k) j)
  ext z
  change (∃ a, projectiveCoordinateGenericHom i j a = z) ↔
    ∃ s, X.germToFunctionField (i ⁻¹ᵁ U) s = z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨i.app U (e a), rfl⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨a, ha⟩ := i.app_surjective U (isAffineOpen_opensRange
      (coordinateChartInclusion (R := k) j)) s
    obtain ⟨c, hc⟩ := e.surjective a
    refine ⟨c, ?_⟩
    change X.germToFunctionField (i ⁻¹ᵁ U) (i.app U (e c)) =
      X.germToFunctionField (i ⁻¹ᵁ U) s
    rw [hc, ha]

/-- The ENTIRE original affine section ring is canonically the ACTUAL produced model chart, over original k. -/
def originalCoordinateChartSectionsAlgEquiv :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    letI := (i ≫ projectiveSpaceStructure k n).sectionsAlgebra
      (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)
    Γ(X, i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange) ≃ₐ[k]
      (originalRankOneCoordinateModel i j).chartAlg (fun _ => j) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let _ := (i ≫ projectiveSpaceStructure k n).sectionsAlgebra
    (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)
  exact ((i ≫ projectiveSpaceStructure k n).sectionsFunctionFieldEquiv _).trans
    (Subalgebra.equivOfEq _ _ (originalRankOneCoordinateModel_chartAlg_eq_originalSections i j).symm)

/-- EVERY section maps to its SAME LITERAL original generic germ, not an assumed matching coefficient. -/
theorem originalCoordinateChartSectionsAlgEquiv_apply
    (s : Γ(X, i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    letI := (i ≫ projectiveSpaceStructure k n).sectionsAlgebra
      (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)
    ((originalCoordinateChartSectionsAlgEquiv i j s :
      (originalRankOneCoordinateModel i j).chartAlg (fun _ => j)) : X.functionField) =
        X.germToFunctionField (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange) s := rfl

/-- The ACTUAL original affine chart scheme is the spectrum of the produced original-field model chart algebra. -/
def originalCoordinateChartIso :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange).toScheme ≅
      Spec (.of ((originalRankOneCoordinateModel i j).chartAlg (fun _ => j))) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let U := (coordinateChartInclusion (R := k) j).opensRange
  let _ := (i ≫ projectiveSpaceStructure k n).sectionsAlgebra (i ⁻¹ᵁ U)
  have hV : IsAffineOpen (i ⁻¹ᵁ U) :=
    (isAffineOpen_opensRange (coordinateChartInclusion (R := k) j)).preimage i
  exact hV.isoSpec ≪≫
    (Scheme.Spec.mapIso (originalCoordinateChartSectionsAlgEquiv i j).toRingEquiv.toCommRingCatIso.op).symm

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalRankOneCoordinateModel_chartAlg_eq_range
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalRankOneCoordinateModel_chartAlg_eq_range

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalRankOneCoordinateModel_chartAlg_eq_originalSections
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalRankOneCoordinateModel_chartAlg_eq_originalSections

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalCoordinateChartSectionsAlgEquiv
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalCoordinateChartSectionsAlgEquiv

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalCoordinateChartSectionsAlgEquiv_apply
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalCoordinateChartSectionsAlgEquiv_apply

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalCoordinateChartIso
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalCoordinateChartIso
