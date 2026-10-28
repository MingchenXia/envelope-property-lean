import EnvelopeProperty.Potential.CompletedFibreIdempotentApproximation

/-! # Arbitrarily small whole coefficient defects from genuine original fractions -/

open scoped NNReal TensorProduct Topology
open Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.Spectrum

variable {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B] [Fintype ι]

private theorem fc_dense_small_coefficient_defect {E : Type*} [NormedCommRing E]
    (S : Set E) (hS : Dense S) (f : E → ℝ) (hf : Continuous f)
    (hf0 : f 0 = 0) (hfn : ∀ b, 0 ≤ f b) (e : E) (he : IsIdempotentElem e) :
    ∃ M : ℝ, 0 < M ∧ ∀ ε : ℝ, 0 < ε →
      ∃ b ∈ S, f b < M ∧ f (b^2-b) < ε ∧ ‖e-b‖ < ε := by
  let M := f e+1
  have hM : 0 < M := add_pos_of_nonneg_of_pos (hfn e) zero_lt_one
  refine ⟨M,hM,?_⟩
  intro ε hε
  have hpoly : Continuous (fun b : E => b^2-b) :=
    (continuous_id.pow 2).sub continuous_id
  have hdef : Continuous (fun b : E => f (b^2-b)) := hf.comp hpoly
  have he0 : e^2-e = 0 := by rw [pow_two,he.eq,sub_self]
  have hO : IsOpen {b : E | f b < M ∧ f (b^2-b) < ε} :=
    (isOpen_lt hf continuous_const).inter (isOpen_lt hdef continuous_const)
  have heO : e ∈ {b : E | f b < M ∧ f (b^2-b) < ε} := by
    constructor
    · exact lt_add_one (f e)
    · simpa only [he0,hf0] using hε
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds heO)
  obtain ⟨b,hb,hc⟩ := Metric.mem_closure_iff.mp (hS e) (min ε δ) (lt_min hε hδ)
  have hdist : dist b e < δ := by
    rw [dist_comm]
    exact hc.trans_le (min_le_right _ _)
  have hbounds := hball hdist
  refine ⟨b,hb,hbounds.1,hbounds.2,?_⟩
  rw [← dist_eq_norm]
  exact hc.trans_le (min_le_left _ _)

/-- Fixed norm bounds and arbitrarily small defects are DERIVED in the entire genuine
coefficient norm. No nilpotent or residue-field direction is discarded. -/
theorem exists_fractionTensor_arbitrarily_small_coefficient_defect (x : Spectrum A)
    (basis : Module.Basis ι A B)
    (e : FiniteFreeAnalyticCopy (basis.baseChange (H x))) (he : IsIdempotentElem e) :
    ∃ M : ℝ, 0 < M ∧ ∀ ε : ℝ, 0 < ε → ∃ d : A, ∃ c : B, x.val d ≠ 0 ∧
      (basis.baseChange (H x)).fcCoefficientNorm (fractionTensor x d c) < M ∧
      (basis.baseChange (H x)).fcCoefficientNorm ((fractionTensor x d c)^2-fractionTensor x d c) < ε ∧
      ‖e-completedFibreFraction x basis d c‖ < ε := by
  let E := FiniteFreeAnalyticCopy (basis.baseChange (H x))
  let f : E → ℝ := fun b => ‖FiniteFreeAnalyticCopy.coefficientEquiv (basis.baseChange (H x)) b‖
  have hf : Continuous f := continuous_norm.comp
    (FiniteFreeAnalyticCopy.continuous_coefficientEquiv (basis.baseChange (H x)))
  let S : Set E := {b | ∃ d : A, ∃ c : B, x.val d ≠ 0 ∧ b = completedFibreFraction x basis d c}
  have hS : Dense S := by
    intro b
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨d,c,hd,hc⟩ := exists_fractionTensor_ringNorm_approx x basis b ε hε
    have hc' : ‖b-completedFibreFraction x basis d c‖ < ε := hc
    refine ⟨completedFibreFraction x basis d c,⟨d,c,hd,rfl⟩,?_⟩
    rw [dist_eq_norm]
    exact hc'
  obtain ⟨M,hM,happ⟩ := fc_dense_small_coefficient_defect S hS f hf
    (by
      change ‖(basis.baseChange (H x)).equivFun 0‖ = 0
      rw [map_zero,norm_zero]) (fun b => norm_nonneg _) e he
  refine ⟨M,hM,?_⟩
  intro ε hε
  obtain ⟨b,⟨d,c,hd,rfl⟩,hb,hdef,herr⟩ := happ ε hε
  exact ⟨d,c,hd,hb,hdef,herr⟩

end EnvelopeProperty.Berkovich.Spectrum
