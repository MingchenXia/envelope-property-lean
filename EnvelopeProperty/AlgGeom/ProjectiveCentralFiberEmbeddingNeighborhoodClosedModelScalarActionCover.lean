import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedScalarGroupPoint

/-! # The actual original model action has the entire finite scalar open cover

The native standard affine-line action is identified with literal parameter
scaling internally, then original test-configuration equivariance transfers
the true finite parameter cover to the SAME whole original total model.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped Polynomial LaurentPolynomial CategoryTheory.MonObj
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedModelScalarActionCover
open ProjBerk NativeTestConfiguration
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedScalarGroupPoint
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedParameterScalarCover
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedGroupPointTransport
variable {k : Type u} [Field k]

/-- The original standard affine-line action at the genuine original scalar point. -/
def parameterGroupPointAction (u : kˣ) : nativeParameterLine k ⟶ nativeParameterLine k := by
  let := nativeParameterLineModObj k
  exact (toUnit (nativeParameterLine k) ≫ scalarGroupPoint u) • (𝟙 (nativeParameterLine k))

private theorem groupInclusion_dominant :
    IsDominant (nativeParameterGroupInclusion k).left := by
  rw [nativeParameterGroupInclusion_left]
  constructor
  change DenseRange (PrimeSpectrum.comap (Polynomial.toLaurent : k[X] →+* k[T;T⁻¹]))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot
      (Polynomial.toLaurent : k[X] →+* k[T;T⁻¹])).mp Polynomial.toLaurent_injective]
  exact bot_le

private theorem parameterGroupPointAction_inclusion (u : kˣ) :
    nativeParameterGroupInclusion k ≫ parameterGroupPointAction u =
      (lift (toUnit (nativeMultiplicativeGroup k) ≫ scalarGroupPoint u)
        (𝟙 (nativeMultiplicativeGroup k)) ≫ μ[nativeMultiplicativeGroup k]) ≫
          nativeParameterGroupInclusion k := by
  let := nativeParameterLineModObj k
  let : ModObj (nativeMultiplicativeGroup k) (nativeMultiplicativeGroup k) := ModObj.regular _
  let : IsModHom (nativeMultiplicativeGroup k) (nativeParameterGroupInclusion k) :=
    nativeParameterGroupInclusion_isModHom k
  change nativeParameterGroupInclusion k ≫
      ((toUnit (nativeParameterLine k) ≫ scalarGroupPoint u) • (𝟙 (nativeParameterLine k))) =
    ((toUnit (nativeMultiplicativeGroup k) ≫ scalarGroupPoint u) •
      (𝟙 (nativeMultiplicativeGroup k))) ≫ nativeParameterGroupInclusion k
  rw [ModObj.comp_smul, IsModHom.map_smul]
  simp only [Category.comp_id, Category.id_comp, comp_toUnit_assoc]

/-- The ACTUAL original standard action on the ENTIRE parameter line is
literally the same original polynomial spectrum scalar map. -/
theorem parameterGroupPointAction_left (u : kˣ) :
    (parameterGroupPointAction u).left = parameterScalarMap u := by
  let : IsDominant (nativeParameterGroupInclusion k).left := groupInclusion_dominant
  let : AlgebraicGeometry.IsReduced (nativeParameterLine k).left :=
    inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (.of k[X])))
  let : (nativeParameterLine k).left.IsSeparated :=
    inferInstanceAs ((Spec (.of k[X])).IsSeparated)
  apply AlgebraicGeometry.ext_of_isDominant (nativeParameterGroupInclusion k).left
  have h := congrArg Over.Hom.left (parameterGroupPointAction_inclusion u)
  change (nativeParameterGroupInclusion k).left ≫ (parameterGroupPointAction u).left =
    (lift (toUnit (nativeMultiplicativeGroup k) ≫ scalarGroupPoint u)
      (𝟙 (nativeMultiplicativeGroup k)) ≫ μ[nativeMultiplicativeGroup k]).left ≫
        (nativeParameterGroupInclusion k).left at h
  exact h.trans (scalarGroupPoint_multiply_parameter u)

/-- The SAME original whole model point action lies over the literal SAME
parameter scalar map, derived from ORIGINAL equivariance, with no matching input. -/
theorem groupPointAction_projection {X : Over (Spec (.of k))}
    (C : NativeTestConfiguration.TestConfiguration k X) (u : kˣ) :
    groupPointAction C (scalarGroupPoint u) ≫ C.projection =
      C.projection ≫ parameterScalarMap u := by
  let := C.action
  let := nativeParameterLineModObj k
  let : IsModHom (nativeMultiplicativeGroup k) (structureOver k C.projection) := C.equivariant
  have h : ((toUnit (totalOver k C.projection) ≫ scalarGroupPoint u) •
      (𝟙 (totalOver k C.projection))) ≫ structureOver k C.projection =
    structureOver k C.projection ≫
      ((toUnit (nativeParameterLine k) ≫ scalarGroupPoint u) • (𝟙 (nativeParameterLine k))) := by
    rw [IsModHom.map_smul, ModObj.comp_smul]
    simp only [Category.comp_id, Category.id_comp, comp_toUnit_assoc]
  have hl := congrArg Over.Hom.left h
  change groupPointAction C (scalarGroupPoint u) ≫ C.projection =
    C.projection ≫ (parameterGroupPointAction u).left at hl
  exact hl.trans (congrArg (fun a => C.projection ≫ a) (parameterGroupPointAction_left u))

/-- Finitely many ACTUAL original model point-action inverse images of the
SAME original near-zero open cover the ENTIRE SAME original total scheme. -/
theorem exists_finite_groupPointAction_cover [Infinite k]
    {X : Over (Spec (.of k))} (C : NativeTestConfiguration.TestConfiguration k X)
    (g : k[X]) (hg : g.eval 0 ≠ 0) :
    ∃ T : Finset kˣ,
      (⨆ u ∈ T, groupPointAction C (scalarGroupPoint u) ⁻¹ᵁ
        (C.projection ⁻¹ᵁ PrimeSpectrum.basicOpen g)) = ⊤ := by
  obtain ⟨T, hT⟩ := exists_finite_modelParameterScalar_cover C.projection g hg
  have hpre (u : kˣ) : groupPointAction C (scalarGroupPoint u) ⁻¹ᵁ
      (C.projection ⁻¹ᵁ PrimeSpectrum.basicOpen g) =
      (C.projection ≫ parameterScalarMap u) ⁻¹ᵁ PrimeSpectrum.basicOpen g := by
    change (groupPointAction C (scalarGroupPoint u) ≫ C.projection) ⁻¹ᵁ
      PrimeSpectrum.basicOpen g = _
    rw [groupPointAction_projection]
  exact ⟨T, by simpa only [hpre] using hT⟩

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedModelScalarActionCover
