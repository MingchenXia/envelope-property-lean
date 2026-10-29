import EnvelopeProperty.AlgGeom.OriginalProjectivePositiveDiagonalAlgebra
import EnvelopeProperty.Global.NativeVeroneseModelComparison
import EnvelopeProperty.AlgGeom.ProjectiveFixedNativeAnalyticGluing

/-! # The actual original simultaneous positive diagonal and native Segre projective scheme -/
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open Alterations
open scoped Classical NNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.OriginalProjectiveDiagonalNativeComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The native rank-one projective scheme depends on its SAME entire original algebra, not its coordinate enumeration. -/
theorem rankOneSchemeEq (Y Z : MultiModel k K 1) (h : Y.S = Z.S) :
    Y.nativeRankOneScheme = Z.nativeRankOneScheme := by
  cases Y
  cases Z
  cases h
  rfl

/-- The actual native scheme isomorphism induced by literal equality of the entire original homogeneous algebra. -/
def rankOneSchemeIso (Y Z : MultiModel k K 1) (h : Y.S = Z.S) :
    Y.nativeRankOneScheme ≅ Z.nativeRankOneScheme := eqToIso (rankOneSchemeEq Y Z h)

/-- The SAME actual native scheme isomorphism preserves the whole original base morphism. -/
theorem rankOneSchemeIso_structure (Y Z : MultiModel k K 1) (h : Y.S = Z.S) :
    (rankOneSchemeIso Y Z h).hom ≫ Z.nativeRankOneStructure = Y.nativeRankOneStructure := by
  cases Y
  cases Z
  cases h
  rfl

/-- The SAME entire native valued-point spaces are identified by the actual whole algebra equality, retaining nongeneric supports. -/
def rankOneNativePointHomeomorph (Y Z : MultiModel k K 1) (h : Y.S = Z.S) :
    Berkovich.RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) Y.nativeRankOneStructure ≃ₜ
      Berkovich.RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) Z.nativeRankOneStructure := by
  cases Y
  cases Z
  cases h
  exact Homeomorph.refl _

/-- Coordinate enumerations do not change the WHOLE analytic space of the SAME actual rank-one algebra. -/
def rankOneAnalyticHomeomorph (Y Z : MultiModel k K 1) (h : Y.S = Z.S) : Y.an ≃ₜ Z.an :=
  Y.nativeRankOneAnalyticHomeomorph |>.trans (rankOneNativePointHomeomorph Y Z h) |>.trans
    Z.nativeRankOneAnalyticHomeomorph.symm

/-- The actual all-one diagonal is strictly positive on EVERY factor of a nonempty family. -/
theorem oneDegree_pos (r : ℕ) : ∀ j,0 < OriginalProjectivePositiveDiagonalAlgebra.oneDegree (r+1) j := by
  intro j
  change (0 : ℕ) < 1
  decide

variable {X : Scheme.{u}} [IsIntegral X] {r : ℕ} {d : Fin (r+1) → ℕ}
  (q : ∀ j,X ⟶ projectiveSpace k (d j))
  (p : X ⟶ Spec (.of k)) (hp : ∀ j,q j ≫ projectiveSpaceStructure k (d j) = p)
  [IsClosedImmersion (q 0)]

/-- Actual original simultaneous positive diagonal and actual finite Segre native scheme, DERIVED from entire actual algebra equality. -/
def actualDiagonalSchemeIso :
    let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
    let b := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
    let hb := fun j => (hp j).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
    let pivot := FiniteProjectiveNativeFieldModels.pivot q
    let hU := fun j => (FiniteProjectiveNativeFieldModels.chartSite (q j)).property
    letI := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp pivot hU
    letI := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
    letI := b.stalkAlgebra (genericPoint X)
    (FiniteProjectiveNativeFieldModels.model q b hb).nativeVeroneseScheme (oneDegree_pos r) ≅
      (ProjectiveChartFunctionFieldGeneration.fullFieldModel f
        (FiniteSegreOriginalProjectiveMaps.index d pivot)).nativeRankOneScheme := by
  let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
  let b := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
  let hb := fun j => (hp j).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
  let pivot := FiniteProjectiveNativeFieldModels.pivot q
  let hU := fun j => (FiniteProjectiveNativeFieldModels.chartSite (q j)).property
  let := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp pivot hU
  let := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
  let := b.stalkAlgebra (genericPoint X)
  exact rankOneSchemeIso _ _ (OriginalProjectivePositiveDiagonalAlgebra.model_positiveDiagonal_eq_actualSegreAlgebra q p hp)

/-- The ENTIRE original native analytic space is the SAME actual simultaneous multigraded model; no analytic comparison certificate is supplied. -/
def originalNativeSegreBaseModelHomeomorph :
    let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
    let b := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
    let hb := fun j => (hp j).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
    letI := b.stalkAlgebra (genericPoint X)
    Berkovich.RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p ≃ₜ
      (FiniteProjectiveNativeFieldModels.model q b hb).an := by
  let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
  let b := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
  let hb := fun j => (hp j).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
  let pivot := FiniteProjectiveNativeFieldModels.pivot q
  let hU := fun j => (FiniteProjectiveNativeFieldModels.chartSite (q j)).property
  let := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp pivot hU
  let := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
  let := b.stalkAlgebra (genericPoint X)
  let Y := FiniteProjectiveNativeFieldModels.model q b hb
  let Z := ProjectiveChartFunctionFieldGeneration.fullFieldModel f
    (FiniteSegreOriginalProjectiveMaps.index d pivot)
  let base : Berkovich.RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p ≃ₜ
      Berkovich.RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) b :=
    Homeomorph.setCongr (by rw [show b = p from FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp])
  exact base.trans ((ProjectiveFixedNativeAnalyticGluing.nativeModelHomeomorph f
    (FiniteSegreOriginalProjectiveMaps.index d pivot)).trans
      ((rankOneAnalyticHomeomorph (Y.veronese (oneDegree_pos r)) Z
        (OriginalProjectivePositiveDiagonalAlgebra.model_positiveDiagonal_eq_actualSegreAlgebra q p hp)).symm.trans
          (Y.veroneseHomeomorph (oneDegree_pos r)).symm))

private def originalBaseModelHomeomorph (b : X ⟶ Spec (.of k))
    (hb : ∀ j,q j ≫ projectiveSpaceStructure k (d j) = b) (h : b = p) :
    (letI := b.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q b hb).an) ≃ₜ
      (letI := p.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q p hp).an) := by
  cases h
  exact Homeomorph.refl _

/-- The WHOLE original native analytic space is the EXACT  based simultaneous family model, not a supplied homeomorphic model. -/
def originalNativeModelHomeomorph :
    letI := p.stalkAlgebra (genericPoint X)
    Berkovich.RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p ≃ₜ
      (FiniteProjectiveNativeFieldModels.model q p hp).an :=
  (originalNativeSegreBaseModelHomeomorph q p hp).trans
    (originalBaseModelHomeomorph q p hp _ _
      (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp))

end EnvelopeProperty.OriginalProjectiveDiagonalNativeComparison
