import EnvelopeProperty.AlgGeom.ResidualFunctionFieldCurve
import EnvelopeProperty.AlgGeom.FiniteProjectivePort.FiniteProjectivePreservation
import EnvelopeProperty.AlgGeom.CurveRationalPrincipalBalance

/-! # Actual projectivity and original principal balance of the SAME residual model -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Alterations
noncomputable section
universe u
namespace EnvelopeProperty.ResidualFunctionFieldCurve
variable (k L : Type u) [Field k] [Field L] [Algebra (RatFunc k) L]
  [FiniteDimensional (RatFunc k) L]

/-- Actual finite normalization internally constructs projectivity of the SAME residual model. -/
theorem structure_isProjective : IsProjectiveOver (baseMap k L) := by
  let := projection_isFinite k L
  exact Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite
    (projectiveSpaceStructure k 1) (isProjectiveOver_projectiveSpaceStructure k 1) (projection k L)

/-- The actual closed projective embedding uses the literal original coefficient projection. -/
theorem structure_isProjectiveFactorization : IsProjectiveFactorization (baseMap k L) := by
  obtain ⟨n, j, hj, hbase⟩ := structure_isProjective k L
  refine ⟨n, j, hj, ?_⟩
  convert hbase using 1
  unfold MvPolynomial.homogeneousProjπ projectiveSpaceStructure
  congr 1

/-- Noetherianity of the SAME actual residual model follows from its original proper field structure. -/
theorem model_isNoetherian : AlgebraicGeometry.IsNoetherian (model k L) := by
  let : IsProper (baseMap k L) := structure_isProper k L
  let : IsLocallyNoetherian (model k L) := LocallyOfFiniteType.isLocallyNoetherian (baseMap k L)
  let : CompactSpace (model k L) := QuasiCompact.compactSpace_of_compactSpace (baseMap k L)
  exact { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }

/-- The SAME original nonzero field element has genuine finite support of its native original orders. -/
theorem nativeOrder_hasFiniteSupport (a : L) (ha : a ≠ 0) :
    letI := model_isNoetherian k L
    Function.HasFiniteSupport ((model k L).ord ((fieldEquiv k L).symm a)) := by
  let := model_isNoetherian k L
  exact CurveRationalPrincipalBalance.hasFiniteSupport_ord (dimension_le k L)
    (stalk_isIntegrallyClosed k L) _ ((map_ne_zero_iff _ (fieldEquiv k L).symm.injective).mpr ha)

/-- Original coefficient residue weights preserve finite support on ALL original model points. -/
theorem nativeWeightedOrder_hasFiniteSupport (a : L) (ha : a ≠ 0) :
    letI := model_isNoetherian k L
    Function.HasFiniteSupport (CurveRationalPrincipalBalance.weightedOrder (baseMap k L)
      ((fieldEquiv k L).symm a)) := by
  let := model_isNoetherian k L
  exact CurveRationalPrincipalBalance.hasFiniteSupport_weightedOrder (baseMap k L)
    (dimension_le k L) (stalk_isIntegrallyClosed k L) _
    ((map_ne_zero_iff _ (fieldEquiv k L).symm.injective).mpr ha)

/-- Genuine principal balance for the SAME original field element on the SAME actual whole model. -/
theorem finsum_nativeWeightedOrder_eq_zero (a : L) (ha : a ≠ 0) :
    letI := model_isNoetherian k L
    (∑ᶠ x : model k L, CurveRationalPrincipalBalance.weightedOrder (baseMap k L)
      ((fieldEquiv k L).symm a) x) = 0 := by
  let := model_isNoetherian k L
  exact CurveRationalPrincipalBalance.finsum_weightedOrder_eq_zero (baseMap k L)
    (structure_isProjectiveFactorization k L) (dimension_le k L) (stalk_isIntegrallyClosed k L)
    _ ((map_ne_zero_iff _ (fieldEquiv k L).symm.injective).mpr ha)

end EnvelopeProperty.ResidualFunctionFieldCurve
