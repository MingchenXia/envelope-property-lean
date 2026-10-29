import EnvelopeProperty.DeligneIllusie.WittTwoNativeTwistReduction
import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineMap

/-!
# Witt Two Native Twist Lift

The original actual smooth Witt lift has the whole native geometric beta square. -/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
universe u

namespace EnvelopeProperty.DeligneIllusie.WittTwoNativeTwist

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoRelativeLift.residueCopyAlgebra
  copyReductionAlgebra copyReductionModule sourceLeftAlgebra sourceLeftModule
  nativeCoefficientAlgebra

variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]

/-- The ACTUAL affine geometric relative-Frobenius ring map, also for zero algebras. -/
def nativeBeta : NativeTwist p k A →+* ResidueAlgebra p k A :=
  (Cartier.SchemeRelativeFrobeniusAffineMap.ringMap
    (algebraMap k (ResidueAlgebra p k A)) p).hom

theorem nativeBeta_coefficient (d : k) :
    nativeBeta p k A (nativeCoefficient p k A d) =
      algebraMap k (ResidueAlgebra p k A) d := by
  exact congrArg (fun q : CommRingCat.of k ⟶ CommRingCat.of (ResidueAlgebra p k A) => q.hom d)
    (Cartier.SchemeRelativeFrobeniusAffineMap.coefficient_ringMap
      (algebraMap k (ResidueAlgebra p k A)) p)

theorem nativeBeta_source (b : ResidueAlgebra p k A) :
    nativeBeta p k A (nativeSource p k A b) = b ^ p :=
  Cartier.SchemeRelativeFrobeniusAffineMap.source_ringMap_apply
    (algebraMap k (ResidueAlgebra p k A)) p b

/-- The whole actual native reduction has the old relative-power formula on the SAME source. -/
theorem nativeBeta_sourceReduction :
    (nativeBeta p k A).comp (sourceReduction p k A) =
      (WittTwoRelativeLift.residueFrobenius p k A).toRingHom := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul w a =>
    change nativeBeta p k A (sourceReduction p k A (w ⊗ₜ[WittTwo.Ring p k] a)) = _
    rw [sourceReduction_tmul, map_mul, nativeBeta_coefficient, nativeBeta_source]
    exact (WittTwoRelativeLift.residueFrobenius_tmul p k A w a).symm

variable [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A]

/-- The existing constructed smooth lift, with its genuine LEFT W' source action retained. -/
def actualRelativeLift :
    letI := WittTwoRelativeLift.copyAlgebra p k A
    LiftSource p k A →ₐ[CoefficientCopy p k] A :=
  WittTwoRelativeLift.relativeLift p k A

/-- The ENTIRE actual beta square is derived, rather than supplied as a model certificate. -/
theorem actualRelativeLift_reduction :
    letI := WittTwoRelativeLift.copyAlgebra p k A
    (actualFlatReduction p k A).map.comp (actualRelativeLift p k A).toRingHom =
      (nativeBeta p k A).comp (actualReduction p k A).map := by
  let := WittTwoRelativeLift.copyAlgebra p k A
  change (WittTwoRelativeLift.reductionMap p k A).toRingHom.comp
      (WittTwoRelativeLift.relativeLift p k A).toRingHom =
    (nativeBeta p k A).comp (sourceReduction p k A)
  rw [nativeBeta_sourceReduction]
  exact congrArg AlgHom.toRingHom (WittTwoRelativeLift.relativeLift_reduction p k A)

/-- Actual scalar preservation is an algebra-map law BEFORE reduction. -/
theorem actualRelativeLift_coefficient (w : CoefficientCopy p k) :
    letI := WittTwoRelativeLift.copyAlgebra p k A
    actualRelativeLift p k A
      (algebraMap (CoefficientCopy p k) (LiftSource p k A) w) =
        algebraMap (CoefficientCopy p k) A w := by
  let := WittTwoRelativeLift.copyAlgebra p k A
  exact (actualRelativeLift p k A).commutes w

end EnvelopeProperty.DeligneIllusie.WittTwoNativeTwist
