import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationProjectiveHomogeneousCoordinateGerms
import EnvelopeProperty.Global.ModelQuotient

/-!
# Actual original-field rank-one model from a genuine original closed embedding

The coefficient field is literally the original X.functionField for its
actual original composite base action. Every coordinate is the actual
original homogeneous global-section coefficient germ. All MultiModel axioms,
including M3, are DERIVED from the genuine original closed embedding.
An isomorphism between its native Proj and original X remains a consumer.
Route: owned `closed-projective-rank-one-model-route.tex`.
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
variable (i : X ⟶ projectiveSpace k n) (j : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)]

/-- The actual original normalized projective coordinates, in the ORIGINAL function field. -/
def originalRankOneCoordinates (l : Fin (n + 1)) : X.functionField :=
  projectiveCoordinateGenericHom i j (coordinateDehomCoord j l)

/-- The original pivot is literally one; no nonvanishing coordinate certificate is supplied. -/
theorem originalRankOneCoordinates_pivot : originalRankOneCoordinates i j j = 1 := by
  rw [originalRankOneCoordinates, coordinateDehomCoord_self, map_one]

/-- The actual original closed embedding INTERNALLY supplies EVERY rank-one model axiom,
with coefficient field LITERALLY original X.functionField and its ORIGINAL base action. -/
def originalRankOneCoordinateModel [IsClosedImmersion i] :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    MultiModel k X.functionField 1 := by
  classical
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let z : (Σ _c : Fin 1, Fin (n + 1)) → MvPolynomial (Fin 1) X.functionField :=
    fun t => monomial (Finsupp.single t.1 1) (originalRankOneCoordinates i j t.2)
  let S := Algebra.adjoin k (Set.range z)
  refine {
    S := S
    isGraded := fun _ hp a => monomial_coeff_mem_adjoin (fun q hq => by
      obtain ⟨t, rfl⟩ := hq
      exact ⟨_, _, rfl⟩) hp a
    fg := ⟨(Set.finite_range z).toFinset, by rw [Set.Finite.coe_toFinset]⟩
    M := fun _ => n
    coord := fun _ l => originalRankOneCoordinates i j l
    coord_mem := fun c l => Algebra.subset_adjoin ⟨⟨c, l⟩, rfl⟩
    exists_coord_ne_zero := fun _ => ⟨j, by
      rw [originalRankOneCoordinates_pivot]
      exact one_ne_zero⟩
    isIntegral := fun p hp => isIntegral_algebraMap (R := S) (x := ⟨p, hp⟩)
    generates := ?_ }
  let s := {x : X.functionField | ∃ (a : Fin 1 →₀ ℕ) (f g : X.functionField),
    monomial a f ∈ S ∧ monomial a g ∈ S ∧ g ≠ 0 ∧ x = f / g}
  change IntermediateField.adjoin k s = ⊤
  apply top_unique
  rw [← projectiveCoordinateGenericVariables_generate i j]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨l, rfl⟩
  apply IntermediateField.subset_adjoin k s
  refine ⟨Finsupp.single (0 : Fin 1) 1,
    originalRankOneCoordinates i j l.1, originalRankOneCoordinates i j j,
    Algebra.subset_adjoin ⟨⟨0, l.1⟩, rfl⟩,
    Algebra.subset_adjoin ⟨⟨0, j⟩, rfl⟩, ?_, ?_⟩
  · rw [originalRankOneCoordinates_pivot]
    exact one_ne_zero
  · rw [originalRankOneCoordinates_pivot, div_one, originalRankOneCoordinates,
      coordinateDehomCoord_ne]

/-- EVERY produced model coordinate remains its literal original projective generic coefficient. -/
theorem originalRankOneCoordinateModel_coord [IsClosedImmersion i] (c : Fin 1)
    (l : Fin (n + 1)) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (originalRankOneCoordinateModel i j).coord c l = projectiveCoordinateGenericHom i j
      (coordinateDehomCoord j l) := rfl

/-- EVERY actual model coordinate is the genuine ORIGINAL homogeneous global-section frame-coefficient germ. -/
theorem originalRankOneCoordinateModel_coord_homogeneous [IsClosedImmersion i] (c : Fin 1)
    (l : Fin (n + 1)) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (originalRankOneCoordinateModel i j).coord c l =
      X.germToFunctionField (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)
        (i.app (coordinateChartInclusion (R := k) j).opensRange
          (homogeneousCoordinateOnChartRange (R := k) j l)) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  rw [originalRankOneCoordinateModel_coord, projectiveCoordinateGenericHom_homogeneous]

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalRankOneCoordinates
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalRankOneCoordinates

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalRankOneCoordinates_pivot
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalRankOneCoordinates_pivot

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalRankOneCoordinateModel
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalRankOneCoordinateModel

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalRankOneCoordinateModel_coord
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalRankOneCoordinateModel_coord

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalRankOneCoordinateModel_coord_homogeneous
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalRankOneCoordinateModel_coord_homogeneous
