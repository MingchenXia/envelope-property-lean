import EnvelopeProperty.Potential.FiniteFreeCoefficientNorm
import Mathlib.Topology.UniformSpace.Equiv

/-! # The actual finite-basis algebra is a genuine complete normed ring -/

open scoped NNReal Topology
open Topology
noncomputable section

namespace EnvelopeProperty

variable {R E ι : Type*} [NormedCommRing R] [CommRing E] [Algebra R E] [Fintype ι]

/-- A copy of the WHOLE original algebra carrying its actually constructed normalized ring norm. -/
def FiniteFreeAnalyticCopy (_b : Module.Basis ι R E) : Type _ := E

namespace FiniteFreeAnalyticCopy

variable (b : Module.Basis ι R E)

instance commRing : CommRing (FiniteFreeAnalyticCopy b) := inferInstanceAs (CommRing E)

instance algebra : Algebra R (FiniteFreeAnalyticCopy b) := inferInstanceAs (Algebra R E)

/-- The whole original coefficient map and multiplication are retained. -/
def originalAlgEquiv : FiniteFreeAnalyticCopy b ≃ₐ[R] E := AlgEquiv.refl

instance normedCommRing : NormedCommRing (FiniteFreeAnalyticCopy b) :=
  { (b.fcCoefficientRingNorm.toNormedRing : NormedRing E), (inferInstance : CommRing E) with }

theorem norm_apply (x : FiniteFreeAnalyticCopy b) : ‖x‖ = b.fcCoefficientRingNorm x := rfl

instance normOneClass [Nontrivial E] : NormOneClass (FiniteFreeAnalyticCopy b) where
  norm_one := b.fcCoefficientRingNorm_one

instance isUltrametricDist [IsUltrametricDist R] : IsUltrametricDist (FiniteFreeAnalyticCopy b) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm b.fcCoefficientRingNorm_isNonarchimedean

/-- The actual original finite-basis coefficient equivalence. -/
def coefficientEquiv : FiniteFreeAnalyticCopy b ≃ₗ[R] (ι → R) := b.equivFun

theorem norm_coefficientEquiv (x : FiniteFreeAnalyticCopy b) :
    ‖coefficientEquiv b x‖ = b.fcCoefficientNorm x := rfl

theorem lipschitz_coefficientEquiv :
    LipschitzWith ⟨b.fcCoefficientNorm 1,b.fcCoefficientNorm_nonneg 1⟩ (coefficientEquiv b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  change ‖coefficientEquiv b x-coefficientEquiv b y‖ ≤
    b.fcCoefficientNorm 1*‖x-y‖
  rw [← map_sub,norm_coefficientEquiv,norm_apply]
  exact b.fcCoefficientNorm_le (x-y)

theorem lipschitz_coefficientEquiv_symm :
    LipschitzWith ⟨b.fcMultiplicationBound,b.fcMultiplicationBound_pos.le⟩ (coefficientEquiv b).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  change ‖(coefficientEquiv b).symm x-(coefficientEquiv b).symm y‖ ≤
    b.fcMultiplicationBound*‖x-y‖
  rw [← map_sub,norm_apply]
  have h := b.fcCoefficientRingNorm_le ((coefficientEquiv b).symm (x-y))
  change b.fcCoefficientRingNorm ((coefficientEquiv b).symm (x-y)) ≤
    b.fcMultiplicationBound*‖x-y‖
  convert h using 1
  change b.fcMultiplicationBound*‖x-y‖ =
    b.fcMultiplicationBound*‖coefficientEquiv b ((coefficientEquiv b).symm (x-y))‖
  rw [LinearEquiv.apply_symm_apply]

/-- Explicit actual norm comparison makes the original WHOLE coefficient equivalence uniform. -/
def coefficientUniformEquiv : FiniteFreeAnalyticCopy b ≃ᵤ (ι → R) where
  toEquiv := (coefficientEquiv b).toEquiv
  uniformContinuous_toFun := (lipschitz_coefficientEquiv b).uniformContinuous
  uniformContinuous_invFun := (lipschitz_coefficientEquiv_symm b).uniformContinuous

/-- Completeness is derived from the original finite product of the actual complete scalar ring. -/
instance completeSpace [CompleteSpace R] : CompleteSpace (FiniteFreeAnalyticCopy b) :=
  (coefficientUniformEquiv b).completeSpace_iff.mpr inferInstance

theorem continuous_coefficientEquiv : Continuous (coefficientEquiv b) :=
  (lipschitz_coefficientEquiv b).continuous

theorem continuous_coefficientEquiv_symm : Continuous (coefficientEquiv b).symm :=
  (lipschitz_coefficientEquiv_symm b).continuous

end FiniteFreeAnalyticCopy

end EnvelopeProperty
