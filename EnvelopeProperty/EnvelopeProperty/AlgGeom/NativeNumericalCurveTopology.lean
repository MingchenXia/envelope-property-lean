import EnvelopeProperty.AlgGeom.NativeNumericalNefCone
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Separation.Hausdorff

/-! # The actual numerical quotient's canonical curve-weak topology

This is the topology of ALL actual closed-curve full Euler degrees. It is
not a proof of projective numerical finite dimensionality or of agreement
with the paper's finite-dimensional real vector-space topology.
-/
open CategoryTheory AlgebraicGeometry Filter Topology Scheme.Modules
noncomputable section
universe u v w
namespace EnvelopeProperty.NativeRealNumericalClasses
open NativeClosedCurveDegrees
variable {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]

/-- The actual whole degree embedding of the SAME original numerical quotient. -/
def numericalDegreeVector : Space p →ₗ[ℝ] (ClosedIntegralCurve X → ℝ) :=
  LinearMap.pi fun C => curveDegree p C

/-- Canonical WEAK topology from ALL actual original closed-curve degrees.
Finite-dimensional Euclidean compatibility is a subsequent mathematical theorem. -/
instance curveWeakTopology : TopologicalSpace (Space p) :=
  TopologicalSpace.induced (numericalDegreeVector p) inferInstance

/-- All genuine original closed-curve degrees jointly separate the SAME actual quotient. -/
theorem numericalDegreeVector_injective : Function.Injective (numericalDegreeVector p) := by
  intro x y h
  exact ext p x y (fun C => congrFun h C)

/-- This is an actual whole topological embedding, not a supplied comparison. -/
theorem numericalDegreeVector_isEmbedding : Topology.IsEmbedding (numericalDegreeVector p) :=
  Function.Injective.isEmbedding_induced (numericalDegreeVector_injective p)

/-- The actual curve-weak numerical space is Hausdorff. -/
instance curveWeakT2Space : T2Space (Space p) :=
  (numericalDegreeVector_isEmbedding p).t2Space

/-- The SAME original numerical addition and negation are continuous. -/
instance curveWeakTopologicalAddGroup : IsTopologicalAddGroup (Space p) :=
  (numericalDegreeVector_isEmbedding p).isInducing.topologicalAddGroup
    (numericalDegreeVector p).toAddMonoidHom

/-- Actual real scalar multiplication is jointly continuous for this curve-weak topology. -/
instance curveWeakContinuousSMul : ContinuousSMul ℝ (Space p) :=
  continuousSMul_induced (numericalDegreeVector p)

/-- Continuity into the SAME original numerical quotient is exactly continuity
of every TRUE original closed-curve degree. -/
theorem continuous_iff_curveDegree {T : Type v} [TopologicalSpace T] (f : T → Space p) :
    Continuous f ↔ ∀ C : ClosedIntegralCurve X, Continuous (fun t => curveDegree p C (f t)) := by
  rw [(numericalDegreeVector_isEmbedding p).isInducing.continuous_iff, continuous_pi_iff]
  rfl

/-- Actual numerical net convergence is exactly convergence of EVERY true original degree. -/
theorem tendsto_iff_curveDegree {T : Type v} (f : T → Space p) (l : Filter T) (θ : Space p) :
    Tendsto f l (𝓝 θ) ↔ ∀ C : ClosedIntegralCurve X,
      Tendsto (fun t => curveDegree p C (f t)) l (𝓝 (curveDegree p C θ)) := by
  rw [(numericalDegreeVector_isEmbedding p).isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

/-- EVERY original full-Euler closed-curve degree is continuous on the actual numerical quotient. -/
theorem continuous_curveDegree (C : ClosedIntegralCurve X) : Continuous (curveDegree p C) :=
  (continuous_iff_curveDegree p id).mp continuous_id C

/-- The ENTIRE coefficient map of EVERY finite actual original line family is continuous. -/
theorem continuous_lineFamilyMap {ι : Type v} [Fintype ι]
    (L : ι → X.Modules) (hL : ∀ i, IsInvertible (L i)) :
    Continuous (lineFamilyMap p L hL) := by
  apply (continuous_iff_curveDegree p _).mpr
  intro C
  simp only [curveDegree_lineFamilyMap]
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).mul continuous_const)

/-- Actual coefficient convergence derives convergence in the SAME original numerical quotient. -/
theorem tendsto_lineFamilyMap {ι : Type v} [Fintype ι]
    (L : ι → X.Modules) (hL : ∀ i, IsInvertible (L i))
    {T : Type w} {a : T → ι → ℝ} {l : Filter T} {b : ι → ℝ}
    (h : Tendsto a l (𝓝 b)) :
    Tendsto (fun t => lineFamilyMap p L hL (a t)) l (𝓝 (lineFamilyMap p L hL b)) :=
  ((continuous_lineFamilyMap p L hL).tendsto b).comp h

/-- The genuine original nef cone is closed, using ALL true original curve inequalities. -/
theorem isClosed_nefCone : IsClosed (nefCone p : Set (Space p)) := by
  have h : (nefCone p : Set (Space p)) =
      ⋂ C : ClosedIntegralCurve X, {θ : Space p | 0 ≤ curveDegree p C θ} := by
    ext θ
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [h]
  exact isClosed_iInter (fun C => isClosed_le continuous_const (continuous_curveDegree p C))

end EnvelopeProperty.NativeRealNumericalClasses
