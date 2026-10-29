/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.CompleteAlgebraicClosure
import EnvelopeProperty.Berkovich.SpectrumResidueField
import EnvelopeProperty.Berkovich.SpectrumGauss

open scoped NNReal Polynomial
open Polynomial
noncomputable section
namespace EnvelopeProperty.Berkovich

/-- An actual complete algebraically closed valued extension of the original valued field. -/
abbrev NontrivialCompleteValuedExtension {K : Type*} [Field K] (v : Valuation K ℝ≥0) :=
  EnvelopeProperty.CompleteAlgebraicClosure (Spectrum.gauss (Spectrum.ofValuation v) 2).H

/-- The original coefficient homomorphism into the actual Gauss residue closure. -/
def nontrivialCompleteValuedExtensionCoefficients {K : Type*} [Field K]
    (v : Valuation K ℝ≥0) : K →+* NontrivialCompleteValuedExtension v :=
  (algebraMap (Spectrum.gauss (Spectrum.ofValuation v) 2).H
    (NontrivialCompleteValuedExtension v)).comp
      ((Spectrum.gauss (Spectrum.ofValuation v) 2).toH.comp Polynomial.C)

/-- The exact original coefficient action, without replacing the original field. -/
instance nontrivialCompleteValuedExtensionAlgebra {K : Type*} [Field K]
    (v : Valuation K ℝ≥0) : Algebra K (NontrivialCompleteValuedExtension v) :=
  (nontrivialCompleteValuedExtensionCoefficients v).toAlgebra

/-- Every original coefficient retains exactly its prescribed valuation. -/
theorem nontrivialCompleteValuedExtension_nnnorm_algebraMap {K : Type*} [Field K]
    (v : Valuation K ℝ≥0) (a : K) :
    ‖algebraMap K (NontrivialCompleteValuedExtension v) a‖₊ = v a := by
  apply NNReal.coe_injective
  change ‖algebraMap (Spectrum.gauss (Spectrum.ofValuation v) 2).H
    (NontrivialCompleteValuedExtension v)
      ((Spectrum.gauss (Spectrum.ofValuation v) 2).toH (C a))‖ = _
  rw [EnvelopeProperty.completeAlgebraicClosure_norm_algebraMap, Spectrum.norm_toH,
    Spectrum.gauss_val_C]
  rfl

/-- The genuine image of the original Gauss variable in the constructed extension. -/
def nontrivialCompleteValuedExtensionParameter {K : Type*} [Field K]
    (v : Valuation K ℝ≥0) : NontrivialCompleteValuedExtension v :=
  algebraMap (Spectrum.gauss (Spectrum.ofValuation v) 2).H
    (NontrivialCompleteValuedExtension v)
      ((Spectrum.gauss (Spectrum.ofValuation v) 2).toH X)

/-- The actual original Gauss parameter has norm two, even over a trivial valuation. -/
theorem nontrivialCompleteValuedExtensionParameter_nnnorm {K : Type*} [Field K]
    (v : Valuation K ℝ≥0) :
    ‖nontrivialCompleteValuedExtensionParameter v‖₊ = 2 := by
  apply NNReal.coe_injective
  change ‖algebraMap (Spectrum.gauss (Spectrum.ofValuation v) 2).H
    (NontrivialCompleteValuedExtension v)
      ((Spectrum.gauss (Spectrum.ofValuation v) 2).toH X)‖ = _
  rw [EnvelopeProperty.completeAlgebraicClosure_norm_algebraMap, Spectrum.norm_toH,
    Spectrum.gauss_val_X]

end EnvelopeProperty.Berkovich
