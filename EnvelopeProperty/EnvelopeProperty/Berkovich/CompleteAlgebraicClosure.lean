/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.ValuationExtension
import Mathlib.Analysis.Normed.Field.Dense

/-!
# Actual complete algebraic closures of ultrametric normed fields

An actual algebraically closed dense subfield forces a complete ultrametric
normed field to be algebraically closed in every characteristic. Root approximation
and the closed isometric base-field image replace characteristic-zero separability
arguments. The trivial norm is handled by the actual discrete topology.

A genuine norm extension to the algebraic closure followed by WithAbs and norm
completion constructs an actual complete algebraically closed isometric extension
of every complete ultrametric normed field. This reusable field factory is independent
of all analytic point spaces.
-/

open scoped NNReal
open Polynomial
noncomputable section
namespace EnvelopeProperty

/-- Dense algebraically closed subfields transfer roots through the closed isometric base image. -/
theorem isAlgClosed_of_denseRange_nontrivial {K L : Type*} [Field K]
    [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    [Algebra K L] [IsAlgClosed K] (hi : DenseRange (algebraMap K L)) : IsAlgClosed L := by
  apply IsAlgClosed.of_exists_root
  intro f fmon firr
  have fnatdeg0 : f.natDegree ≠ 0 := (Irreducible.natDegree_pos firr).ne'
  let F := f.SplittingField
  let : NormedField F := spectralNorm.normedField L F
  let : NormedAlgebra L F := spectralNorm.normedAlgebra L F
  let a := rootOfSplits (SplittingField.splits f)
      (by simpa using degree_ne_of_natDegree_ne fnatdeg0)
  have fa0 : f.aeval a = 0 := by
    rw [← eval_map_algebraMap]
    exact eval_rootOfSplits (Polynomial.SplittingField.splits f)
      (by simpa using degree_ne_of_natDegree_ne fnatdeg0)
  have hclosed : IsClosed (Set.range (algebraMap L F)) :=
    (algebraMap_isometry (𝕜 := L) (𝕜' := F)).isClosedEmbedding.isClosed_range
  have ha : a ∈ closure (Set.range (algebraMap L F)) := by
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    have hε : (δ / max ‖a‖ 1) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
    obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
      exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hi fmon hε
    obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff
      (by simpa [Polynomial.map_map] using (IsAlgClosed.splits g).map ((algebraMap L F).comp _))
    have hab : ‖a - b‖ < δ := by
      rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos hδ (by positivity)).le, mul_inv_cancel₀] at hab
      · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : max ‖a‖ 1 > 0).ne'] using hab
      · simp [fnatdeg0]
      · positivity
    rw [Polynomial.aroots_def,
      Splits.roots_map ((IsAlgClosed.splits g).map _), Multiset.mem_map] at hb
    obtain ⟨c, _, hc⟩ := hb
    refine ⟨b, ?_, ?_⟩
    · exact ⟨c, hc⟩
    · rw [dist_eq_norm]
      exact hab
  obtain ⟨a₀, ha₀⟩ := hclosed.closure_eq ▸ ha
  refine ⟨a₀, ?_⟩
  apply_fun algebraMap L F
  · rwa [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, ha₀, map_zero]
  · exact RingHom.injective _


/-- Algebraic closedness transfers across a genuine dense embedding in every characteristic. -/
theorem isAlgClosed_of_denseRange {K L : Type*} [Field K] [NormedField L]
    [CompleteSpace L] [IsUltrametricDist L] [Algebra K L] [IsAlgClosed K]
    (hi : DenseRange (algebraMap K L)) : IsAlgClosed L := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField L with h | ⟨h, rfl⟩
  · let := h
    have hs : Function.Surjective (algebraMap K L) := by
      intro a
      have ha : a ∈ closure (Set.range (algebraMap K L)) := hi a
      rwa [(isClosed_discrete _).closure_eq] at ha
    let e := RingEquiv.ofBijective (algebraMap K L) ⟨RingHom.injective _, hs⟩
    apply IsAlgClosed.of_exists_root
    intro p hmp hp
    have hpe : degree (p.map e.symm.toRingHom) ≠ 0 := by
      rw [degree_map]
      exact ne_of_gt (degree_pos_of_irreducible hp)
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (p.map e.symm.toRingHom) hpe
    refine ⟨e a, ?_⟩
    rw [IsRoot] at ha
    apply e.symm.injective
    rw [map_zero, ← ha]
    clear ha hpe hp hmp
    induction p using Polynomial.induction_on <;> simp_all
  · exact isAlgClosed_of_denseRange_nontrivial hi

/-- The actual completion of an ultrametric algebraically closed normed field is algebraically closed. -/
instance UniformSpace.Completion.isAlgClosed_ultrametric {K : Type*} [NormedField K]
    [IsUltrametricDist K] [IsAlgClosed K] : IsAlgClosed (UniformSpace.Completion K) := by
  apply isAlgClosed_of_denseRange (K := K)
  exact UniformSpace.Completion.denseRange_coe


section CompleteAlgebraicClosure
variable (K : Type*) [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The genuine extension of the complete base norm to its algebraic closure. -/
def algebraicClosureValuation : Valuation (AlgebraicClosure K) ℝ≥0 :=
  (Valuation.exists_extends_norm (K := K) (L := AlgebraicClosure K)).choose

/-- The chosen actual algebraic closure valuation preserves every original coefficient norm. -/
theorem algebraicClosureValuation_algebraMap (c : K) :
    algebraicClosureValuation K (algebraMap K (AlgebraicClosure K) c) = ‖c‖₊ :=
  (Valuation.exists_extends_norm (K := K) (L := AlgebraicClosure K)).choose_spec c

/-- The algebraic closure with the genuine extended norm. -/
abbrev ValuedAlgebraicClosure := WithAbs (Valuation.toRealAbs (algebraicClosureValuation K))

instance valuedAlgebraicClosure_isAlgClosed : IsAlgClosed (ValuedAlgebraicClosure K) :=
  IsAlgClosed.of_ringEquiv (AlgebraicClosure K) (ValuedAlgebraicClosure K)
    (WithAbs.equiv _).symm

instance valuedAlgebraicClosure_isUltrametricDist : IsUltrametricDist (ValuedAlgebraicClosure K) := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  intro a b
  change ((algebraicClosureValuation K) (a.ofAbs + b.ofAbs) : ℝ) ≤
    max ((algebraicClosureValuation K) a.ofAbs : ℝ) ((algebraicClosureValuation K) b.ofAbs : ℝ)
  exact_mod_cast (algebraicClosureValuation K).map_add a.ofAbs b.ofAbs

/-- The valued algebraic closure coefficient embedding is genuinely isometric. -/
theorem valuedAlgebraicClosure_norm_algebraMap (c : K) :
    ‖algebraMap K (ValuedAlgebraicClosure K) c‖ = ‖c‖ := by
  change ((algebraicClosureValuation K) (algebraMap K (AlgebraicClosure K) c) : ℝ) = ‖c‖
  rw [algebraicClosureValuation_algebraMap, coe_nnnorm]

instance valuedAlgebraicClosure_normedAlgebra : NormedAlgebra K (ValuedAlgebraicClosure K) where
  norm_smul_le c a := by
    rw [Algebra.smul_def, norm_mul, valuedAlgebraicClosure_norm_algebraMap]

/-- The actual completed algebraic closure of an arbitrary complete ultrametric field. -/
abbrev CompleteAlgebraicClosure := UniformSpace.Completion (ValuedAlgebraicClosure K)

instance completeAlgebraicClosure_isAlgClosed : IsAlgClosed (CompleteAlgebraicClosure K) :=
  UniformSpace.Completion.isAlgClosed_ultrametric

/-- Completion retains every norm value of the original field. -/
theorem completeAlgebraicClosure_norm_algebraMap (c : K) :
    ‖algebraMap K (CompleteAlgebraicClosure K) c‖ = ‖c‖ := by
  rw [UniformSpace.Completion.algebraMap_def, UniformSpace.Completion.norm_coe,
    valuedAlgebraicClosure_norm_algebraMap]

end CompleteAlgebraicClosure
end EnvelopeProperty
