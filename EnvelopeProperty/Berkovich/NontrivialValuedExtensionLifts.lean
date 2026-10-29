/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.NontrivialCompleteValuedExtension
import EnvelopeProperty.Berkovich.NontrivialScalarField

/-! # Whole original scalar lifts to the existing radius-two extension -/

open scoped NNReal TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]

/-- The existing radius-two Gauss residue closure lifts EVERY whole original
algebra point, without a norm or completeness assumption on the original field. -/
theorem baseChangeRestriction_nontrivialCompleteValuedExtension_surjective
    (v : Valuation K ℝ≥0) :
    Function.Surjective (baseChangeRestriction (R := K) (S := NontrivialCompleteValuedExtension v)
      (A := A) (v := v) (w := NormedField.valuation)
      (nontrivialCompleteValuedExtension_nnnorm_algebraMap v)) := by
  let G := fcGaussField v 2
  let L₀ := EnvelopeProperty.ValuedAlgebraicClosure G
  let : Algebra G (NontrivialCompleteValuedExtension v) :=
    inferInstanceAs (Algebra G (EnvelopeProperty.CompleteAlgebraicClosure G))
  let : IsScalarTower K G (NontrivialCompleteValuedExtension v) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro x
  obtain ⟨z, hz⟩ := fc_baseChangeRestriction_gauss_surjective v 2 x
  obtain ⟨y, hy⟩ := fc_baseChangeRestriction_algebraicCompletion_surjective
    (K := G) (L := L₀) (A := G ⊗[K] A) z
  let y' : RelativeSpectrum (NormedField.valuation (K := NontrivialCompleteValuedExtension v))
      (NontrivialCompleteValuedExtension v ⊗[G] (G ⊗[K] A)) := y
  refine ⟨iteratedBaseChangeHomeomorph (R := K) (S := G)
    (T := NontrivialCompleteValuedExtension v) (A := A)
    (NormedField.valuation (K := NontrivialCompleteValuedExtension v)) y', ?_⟩
  apply ext_val
  intro a
  change (iteratedBaseChangeHomeomorph (R := K) (S := G)
    (T := NontrivialCompleteValuedExtension v) (A := A)
    (NormedField.valuation (K := NontrivialCompleteValuedExtension v)) y').1.val
      ((1 : NontrivialCompleteValuedExtension v) ⊗ₜ[K] a) = x.1.val a
  have hG := congrArg (fun q : RelativeSpectrum v A => q.1.val a) hz
  have hL := congrArg (fun q : RelativeSpectrum (NormedField.valuation (K := G))
    (G ⊗[K] A) => q.1.val ((1 : G) ⊗ₜ[K] a)) hy
  exact (iteratedBaseChangeHomeomorph_val_tmul (R := K) (S := G)
    (T := NontrivialCompleteValuedExtension v) (A := A) y' 1 a).trans (hL.trans hG)

end EnvelopeProperty.Berkovich.RelativeSpectrum
