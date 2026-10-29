/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.ValuationExtension

/-!
# Actual algebraic field embeddings preserve complete ultrametric norms

Norm-extension uniqueness over a complete ultrametric base identifies the norm
pulled back through every coefficient-preserving algebraic field homomorphism.
Actual algebraic closedness supplies such an embedding. The target field need not
be complete; no separability or characteristic assumption is needed.
-/

open scoped NNReal
noncomputable section
namespace EnvelopeProperty
variable {K L F : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  [NormedField F] [NormedAlgebra K F] [IsUltrametricDist F]

/-- Every actual coefficient-preserving algebraic-field homomorphism retains the given extending valuation. -/
theorem norm_algebraic_algHom (e : L →ₐ[K] F) (v : Valuation L ℝ≥0)
    (hv : ∀ c : K, v (algebraMap K L c) = ‖c‖₊) (a : L) : ‖e a‖₊ = v a := by
  have hw : ∀ c : K,
      ((NormedField.valuation (K := F)).comap e.toRingHom) (algebraMap K L c) = ‖c‖₊ := by
    intro c
    change ‖e (algebraMap K L c)‖₊ = _
    rw [e.commutes, nnnorm_algebraMap']
  have h := Valuation.eq_of_extends_norm hv hw
  exact congrArg (fun w : Valuation L ℝ≥0 => w a) h.symm

/-- Actual algebraic closedness constructs a genuine whole-field isometric embedding. -/
theorem exists_isometric_algebraic_embedding [IsAlgClosed F] (v : Valuation L ℝ≥0)
    (hv : ∀ c : K, v (algebraMap K L c) = ‖c‖₊) :
    ∃ e : L →ₐ[K] F, ∀ a : L, ‖e a‖₊ = v a :=
  ⟨IsAlgClosed.lift, fun a => norm_algebraic_algHom _ v hv a⟩

end EnvelopeProperty
