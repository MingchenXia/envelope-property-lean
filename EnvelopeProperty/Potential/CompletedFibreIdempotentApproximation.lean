import EnvelopeProperty.Potential.CompletedFibreCoefficientDensity
import EnvelopeProperty.Potential.FiniteFreeBanachAlgebra

/-! # Actual whole-fibre fractions with arbitrarily small genuine idempotent defect -/

open scoped NNReal TensorProduct Topology Classical
open Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.Spectrum

variable {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B] [Fintype ι]

/-- Retain the whole original tensor in the constructed finite-basis normed copy. -/
def completedFibreElement (x : Spectrum A) (basis : Module.Basis ι A B) (e : H x ⊗[A] B) :
    FiniteFreeAnalyticCopy (basis.baseChange (H x)) :=
  (FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange (H x))).symm e

/-- One actual original fraction, in the whole normed completed-fibre copy. -/
def completedFibreFraction (x : Spectrum A) (basis : Module.Basis ι A B) (d : A) (c : B) :
    FiniteFreeAnalyticCopy (basis.baseChange (H x)) :=
  completedFibreElement x basis (fractionTensor x d c)

/-- The actual whole-fibre coefficient density also holds in the genuinely constructed ring norm. -/
theorem exists_fractionTensor_ringNorm_approx (x : Spectrum A)
    (basis : Module.Basis ι A B) (e : H x ⊗[A] B) (ε : ℝ) (hε : 0 < ε) :
    ∃ d : A, ∃ c : B, x.val d ≠ 0 ∧
      ‖completedFibreElement x basis e-completedFibreFraction x basis d c‖ < ε := by
  let C := (basis.baseChange (H x)).fcMultiplicationBound
  have hC : 0 < C := (basis.baseChange (H x)).fcMultiplicationBound_pos
  obtain ⟨d,c,hd,hc⟩ := exists_fractionTensor_coefficientNorm_approx x basis e (ε/C) (div_pos hε hC)
  refine ⟨d,c,hd,?_⟩
  change (basis.baseChange (H x)).fcCoefficientRingNorm (e-fractionTensor x d c) < ε
  exact ((basis.baseChange (H x)).fcCoefficientRingNorm_le _).trans_lt
    ((mul_lt_mul_of_pos_left hc hC).trans_eq (mul_div_cancel₀ ε hC.ne'))

private theorem fc_dense_idempotent_approximation {E : Type*} [NormedCommRing E]
    (S : Set E) (hS : Dense S) (e : E) (he : IsIdempotentElem e) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ε : ℝ, 0 < ε →
      ∃ b ∈ S, ‖e-b‖ < ε ∧ ‖b‖ ≤ C ∧ C^2*‖b^2-b‖ < 1 := by
  let C := max 1 (‖e‖+1)
  have hC : 1 ≤ C := le_max_left _ _
  have hcont : Continuous (fun b : E => C^2*‖b^2-b‖) :=
    continuous_const.mul (((continuous_id.pow 2).sub continuous_id).norm)
  have he0 : e^2-e = 0 := by rw [pow_two,he.eq,sub_self]
  have hopen : IsOpen {b : E | C^2*‖b^2-b‖ < 1} :=
    isOpen_lt hcont continuous_const
  have hemem : e ∈ {b : E | C^2*‖b^2-b‖ < 1} := by
    simp only [Set.mem_ofPred_eq,he0,norm_zero,mul_zero,zero_lt_one]
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hemem)
  refine ⟨C,hC,?_⟩
  intro ε hε
  obtain ⟨b,hb,hbe⟩ := Metric.mem_closure_iff.mp (hS e)
    (min ε (min 1 δ)) (lt_min hε (lt_min zero_lt_one hδ))
  have hbe' : ‖b-e‖ < min ε (min 1 δ) := by
    simpa only [dist_eq_norm,norm_sub_rev] using hbe
  have hbδ : dist b e < δ := by
    rw [dist_eq_norm]
    exact hbe'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hb1 : ‖b-e‖ < 1 := hbe'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hbC : ‖b‖ ≤ C := calc
    _ ≤ ‖b-e‖+‖e‖ := by simpa only [norm_sub_rev,add_comm] using norm_le_insert e b
    _ ≤ 1+‖e‖ := by linarith
    _ ≤ C := by rw [add_comm]; exact le_max_right _ _
  refine ⟨b,hb,?_,hbC,hball hbδ⟩
  have herr : ‖e-b‖ < min ε (min 1 δ) := by simpa only [dist_eq_norm] using hbe
  exact herr.trans_le (min_le_left _ _)

/-- GENUINE whole-fibre fraction approximation produces the small scaled defect required by
Newton lifting. No spectral estimate discards any original coefficient direction. -/
theorem exists_fractionTensor_small_scaled_defect (x : Spectrum A)
    (basis : Module.Basis ι A B)
    (e : FiniteFreeAnalyticCopy (basis.baseChange (H x))) (he : IsIdempotentElem e) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ε : ℝ, 0 < ε →
      ∃ d : A, ∃ c : B, x.val d ≠ 0 ∧
      ‖e-completedFibreFraction x basis d c‖ < ε ∧
      ‖completedFibreFraction x basis d c‖ ≤ C ∧
      C^2*‖(completedFibreFraction x basis d c)^2-completedFibreFraction x basis d c‖ < 1 := by
  let E := FiniteFreeAnalyticCopy (basis.baseChange (H x))
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
  obtain ⟨C,hC,happ⟩ := fc_dense_idempotent_approximation S hS e he
  refine ⟨C,hC,?_⟩
  intro ε hε
  obtain ⟨b,⟨d,c,hd,rfl⟩,herr,hb,hdef⟩ := happ ε hε
  exact ⟨d,c,hd,herr,hb,hdef⟩

/-- The idempotent to be approximated is CONSTRUCTED from the actual original finite algebra,
and has its exact prescribed values at EVERY actual whole fibre point. -/
theorem exists_completedFibre_point_idempotent (x : Spectrum A)
    (basis : Module.Basis ι A B) (y : Fibre (B := B) x) :
    ∃ e : FiniteFreeAnalyticCopy (basis.baseChange (H x)), IsIdempotentElem e ∧
      ∀ z : Fibre (B := B) x,
        fibreHom z.2 ((FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange (H x))) e) =
          if z = y then 1 else 0 := by
  classical
  let : Module.Finite A B := Module.Finite.of_basis basis
  let E := H x ⊗[A] B
  let : IsArtinianRing E := IsArtinianRing.of_finite (H x) E
  let m : MaximalSpectrum E := fibreToMaximalSpectrum x y
  let e : E := ArtinianFactors.localIdempotent E m
  have he : IsIdempotentElem e := by
    apply (ArtinianFactors.powerEquiv E).injective
    change ArtinianFactors.powerEquiv E (e*e) = ArtinianFactors.powerEquiv E e
    rw [map_mul]
    change ArtinianFactors.powerEquiv E (ArtinianFactors.localIdempotent E m)*
      ArtinianFactors.powerEquiv E (ArtinianFactors.localIdempotent E m) =
      ArtinianFactors.powerEquiv E (ArtinianFactors.localIdempotent E m)
    rw [ArtinianFactors.powerEquiv_localIdempotent]
    funext n
    by_cases hnm : n = m
    · subst n
      simp only [Pi.mul_apply,Pi.single_eq_same,mul_one]
    · simp only [Pi.mul_apply,Pi.single_eq_of_ne hnm,mul_zero]
  refine ⟨completedFibreElement x basis e,he,?_⟩
  intro z
  change fibreHom z.2 e = _
  have hh := ArtinianFactors.localIdempotent_map m (fibreToMaximalSpectrum x z)
    (fibreHom z.2) rfl
  have hiff : fibreToMaximalSpectrum x z = m ↔ z = y :=
    (fibreToMaximalSpectrum_bijective x).injective.eq_iff
  simpa only [hiff] using hh

end EnvelopeProperty.Berkovich.Spectrum
