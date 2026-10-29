import EnvelopeProperty.Vanishing.NadelGlobalNormalizationAffine
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Genuine WHOLE raw integral closures under the actual produced raw-algebra relabelling

This is functorial transport, consumed only with the actual internally produced
original raw chart equivalence. It does not supply a chart or cover certificate.
-/

open scoped TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalNormalization.ClosureRelabel
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B)

/-- The WHOLE generic tensor relabelling over the SAME original fraction field. -/
def tensorEquiv : FractionRing R ⊗[R] A ≃ₐ[R] FractionRing R ⊗[R] B :=
  Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := FractionRing R)) e

/-- Every SAME original raw element has its actual whole relabelled generic image. -/
theorem tensorEquiv_includeRight (a : A) :
    tensorEquiv e (Algebra.TensorProduct.includeRight a) = Algebra.TensorProduct.includeRight (e a) := by
  simp [tensorEquiv, Algebra.TensorProduct.includeRight_apply]

private theorem coefficientTriangle : (algebraMap B (FractionRing R ⊗[R] B)).comp e.toRingHom =
    (tensorEquiv e).toRingHom.comp (algebraMap A (FractionRing R ⊗[R] A)) := by
  ext a
  exact (tensorEquiv_includeRight e a).symm

/-- The ENTIRE actual raw integral closure transports with its actual whole
raw-algebra comparison; the SAME original fraction field is retained literally. -/
def equiv : integralClosure A (FractionRing R ⊗[R] A) ≃+* integralClosure B (FractionRing R ⊗[R] B) :=
  Affine.closureCongr e.toRingEquiv (tensorEquiv e).toRingEquiv (coefficientTriangle e)

/-- Every original raw coefficient is retained by the whole closure transport. -/
theorem equiv_algebraMap (a : A) :
    equiv e (algebraMap A (integralClosure A (FractionRing R ⊗[R] A)) a) =
      algebraMap B (integralClosure B (FractionRing R ⊗[R] B)) (e a) :=
  Affine.closureCongr_algebraMap _ _ _ _

end EnvelopeProperty.Vanishing.NadelGlobalNormalization.ClosureRelabel
