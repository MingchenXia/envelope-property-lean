import EnvelopeProperty.AlgGeom.NativeNumericalCurveTopology
import EnvelopeProperty.AlgGeom.NativeNumericalAmpleFamilyOpenness
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Finiteness.Defs

/-! # Finite original line-family ranges are genuinely Euclidean with finite actual curve tests

This proves finite dimensionality ONLY of each internally specified finite
original-family range, not of the WHOLE numerical quotient. No global
finite-dimensionality, separation or topology-comparison premise is added.
-/
open AlgebraicGeometry CategoryTheory Scheme.Modules Topology
noncomputable section
universe u v
namespace EnvelopeProperty.NativeRealNumericalClasses
open NativeClosedCurveDegrees
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]
    {ι : Type v} [Fintype ι] (L : ι → X.Modules) (hL : ∀ i,IsInvertible (L i))

/-- The ACTUAL range of the SAME whole original finite-line coefficient map. -/
def lineFamilySpan : Submodule ℝ (Space p) := (lineFamilyMap p L hL).range

/-- Finite dimensionality is DERIVED from the actual original finite coefficient domain. -/
instance lineFamilySpan_finiteDimensional : FiniteDimensional ℝ (lineFamilySpan p L hL) :=
  Module.Finite.range (lineFamilyMap p L hL)

/-- The actual induced curve-weak topology on each SAME finite line range is genuinely Euclidean. -/
def lineFamilySpanEuclidean : lineFamilySpan p L hL ≃L[ℝ]
    (Fin (Module.finrank ℝ (lineFamilySpan p L hL)) → ℝ) :=
  (Module.finBasis ℝ (lineFamilySpan p L hL)).equivFunL

/-- Every actual original finite-line span is closed in the WHOLE actual curve-weak numerical space. -/
theorem isClosed_lineFamilySpan : IsClosed (lineFamilySpan p L hL : Set (Space p)) :=
  (lineFamilySpan p L hL).closed_of_finiteDimensional

private theorem exists_finite_curve_tests (W : Submodule ℝ (Space p)) [FiniteDimensional ℝ W] :
    ∃ s : Finset (ClosedIntegralCurve X), ∀ z : W,
      (∀ C ∈ s,curveDegree p C z.val = 0) → z = 0 := by
  classical
  let F : ClosedIntegralCurve X → W →ₗ[ℝ] ℝ := fun C => (curveDegree p C).comp W.subtype
  have hker : (⨅ C,LinearMap.ker (F C)) = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    change z = 0
    apply Subtype.ext
    apply ext p
    intro C
    have h : F C z = 0 := ((Submodule.mem_iInf _).mp hz) C
    change curveDegree p C z.val = 0 at h
    change curveDegree p C z.val = curveDegree p C 0
    rw [map_zero]
    exact h
  have hspan : Submodule.span ℝ (Set.range F) = ⊤ := by
    apply top_le_iff.mp
    intro φ _
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    rw [hker]
    exact bot_le
  have hfg : (Submodule.span ℝ (Set.range F)).FG := by
    rw [hspan]
    exact Module.Finite.fg_top
  obtain ⟨S,hS,hspanS⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (Set.range F)).mp hfg
  choose C hC using fun φ : S => hS φ.property
  let s := Finset.univ.image C
  refine ⟨s,fun z hz => ?_⟩
  let ev : (W →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun φ => φ z
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hann : Submodule.span ℝ (S : Set (W →ₗ[ℝ] ℝ)) ≤ LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    intro φ hφ
    change φ z = 0
    exact (congrArg (fun ψ : W →ₗ[ℝ] ℝ => ψ z) (hC ⟨φ,hφ⟩)).symm.trans
      (hz _ (Finset.mem_image.mpr ⟨⟨φ,hφ⟩,Finset.mem_univ _,rfl⟩))
  have hall : (⊤ : Submodule ℝ (W →ₗ[ℝ] ℝ)) ≤ LinearMap.ker ev := by
    rw [← hspan, hspanS]
    exact hann
  apply Subtype.ext
  apply ext p
  intro D
  have h : F D z = 0 := hall (show F D ∈ (⊤ : Submodule ℝ (W →ₗ[ℝ] ℝ)) from trivial)
  change curveDegree p D z.val = 0 at h
  change curveDegree p D z.val = curveDegree p D 0
  rw [map_zero]
  exact h

/-- Every actual finite original line span admits an INTERNALLY produced finite
set of true original closed curves giving a WHOLE closed topological embedding. -/
theorem exists_lineFamily_finite_curve_embedding :
    ∃ s : Finset (ClosedIntegralCurve X), Topology.IsClosedEmbedding
      (fun z : lineFamilySpan p L hL => fun C : s => curveDegree p C.val z.val) := by
  classical
  obtain ⟨s,hs⟩ := exists_finite_curve_tests p (lineFamilySpan p L hL)
  let F : lineFamilySpan p L hL →ₗ[ℝ] (s → ℝ) :=
    LinearMap.pi fun C => (curveDegree p C.val).comp (lineFamilySpan p L hL).subtype
  have hk : LinearMap.ker F = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    change z = 0
    apply hs z
    intro C hC
    exact congrFun (show F z = 0 from hz) ⟨C,hC⟩
  exact ⟨s,LinearMap.isClosedEmbedding_of_injective hk⟩

/-- The genuine geometric original ample cone is open in EVERY actual finite-line
span with its induced curve-weak (= genuine Euclidean) topology. -/
theorem isOpen_lineFamilySpan_ampleCone [IsIntegral X] :
    IsOpen {z : lineFamilySpan p L hL | z.val ∈ ampleCone p} := by
  let F : (ι → ℝ) →ₗ[ℝ] lineFamilySpan p L hL := (lineFamilyMap p L hL).rangeRestrict
  have hsurj : Function.Surjective F := LinearMap.surjective_rangeRestrict _
  have hopen : IsOpenMap F := LinearMap.isOpenMap_of_finiteDimensional F hsurj
  have he : {z : lineFamilySpan p L hL | z.val ∈ ampleCone p} =
      F '' {a : ι → ℝ | lineFamilyMap p L hL a ∈ ampleCone p} := by
    ext z
    constructor
    · intro hz
      obtain ⟨a,rfl⟩ := hsurj z
      exact ⟨a,hz,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ha
  rw [he]
  exact hopen _ (isOpen_lineFamilyMap_preimage_ampleCone p L hL)

end EnvelopeProperty.NativeRealNumericalClasses
