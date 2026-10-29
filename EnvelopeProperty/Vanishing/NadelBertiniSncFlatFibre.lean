import EnvelopeProperty.Vanishing.NadelBertiniSncFlatBaseChange

/-! # Original parameter fibres from actual localized quotient flatness

The original parameter homomorphism is retained. Its actual unit value at the
chosen neighbourhood element internally constructs every localized scalar map
and the whole tensor cancellation isomorphism, retaining the original equation.
-/
noncomputable section
open scoped TensorProduct
universe u v w
namespace EnvelopeProperty.Vanishing.NadelBertiniSncFlatFibre
open NadelBertiniSncFlatBaseChange
variable (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]

/-- The original parameter homomorphism extended to the actual coefficient
localization, internally from the same original unit value. -/
def parameterLift {K : Type w} [CommRing K] (g : A) (φ : A →+* K)
    (hg : IsUnit (φ g)) : Localization.Away g →+* K :=
  IsLocalization.Away.lift g hg

/-- The entire actual localized parameter map retains its ORIGINAL scalar triangle. -/
theorem parameterLift_comp {K : Type w} [CommRing K] (g : A) (φ : A →+* K)
    (hg : IsUnit (φ g)) : (parameterLift A g φ hg).comp
      (algebraMap A (Localization.Away g)) = φ :=
  IsLocalization.Away.lift_comp g hg

/-- The actual whole localized fibre is the ORIGINAL scalar fibre, internally
from the ORIGINAL parameter map, with no comparison certificate supplied. -/
def fibreIso {K : Type w} [CommRing K] (g : A) (φ : A →+* K) (hg : IsUnit (φ g)) :
    letI : Algebra A K := φ.toAlgebra
    letI : Algebra (Localization.Away g) K := (parameterLift A g φ hg).toAlgebra
    K ⊗[Localization.Away g] localizedRing A (B := B) g ≃ₐ[K] K ⊗[A] B := by
  letI : Algebra A K := φ.toAlgebra
  letI : Algebra (Localization.Away g) K := (parameterLift A g φ hg).toAlgebra
  have : IsScalarTower A (Localization.Away g) K :=
    IsScalarTower.of_algebraMap_eq fun a => by
      exact (congrArg (fun f : A →+* K => f a) (parameterLift_comp A g φ hg)).symm
  exact Algebra.TensorProduct.cancelBaseChange A (Localization.Away g) K K B

/-- Whole pure-tensor coefficients are retained by the original fibre isomorphism. -/
theorem fibreIso_tmul {K : Type w} [CommRing K] (g : A) (φ : A →+* K)
    (hg : IsUnit (φ g)) (a : K) (r : Localization.Away g) (b : B) :
    letI : Algebra A K := φ.toAlgebra
    letI : Algebra (Localization.Away g) K := (parameterLift A g φ hg).toAlgebra
    fibreIso A (B := B) g φ hg (a ⊗ₜ[Localization.Away g] (r ⊗ₜ[A] b)) =
      (parameterLift A g φ hg r * a) ⊗ₜ[A] b := by
  let : Algebra A K := φ.toAlgebra
  let : Algebra (Localization.Away g) K := (parameterLift A g φ hg).toAlgebra
  have : IsScalarTower A (Localization.Away g) K :=
    IsScalarTower.of_algebraMap_eq fun a => by
      exact (congrArg (fun f : A →+* K => f a) (parameterLift_comp A g φ hg)).symm
  dsimp only [fibreIso]
  rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def]
  rfl

/-- The original equation itself is retained, including BOTH original tensor bases. -/
theorem fibreIso_equation {K : Type w} [CommRing K] (g : A) (φ : A →+* K)
    (hg : IsUnit (φ g)) (h : B) :
    letI : Algebra A K := φ.toAlgebra
    letI : Algebra (Localization.Away g) K := (parameterLift A g φ hg).toAlgebra
    fibreIso A g φ hg ((1 : K) ⊗ₜ[Localization.Away g] localizedEquation A g h) =
      (1 : K) ⊗ₜ[A] h := by
  simpa only [localizedEquation, map_one, one_mul] using
    fibreIso_tmul A g φ hg (1 : K) (1 : Localization.Away g) h

/-- Flatness ONLY of the actual localized original quotient proves the SAME
original equation regular in the ORIGINAL parameter fibre. -/
theorem tensor_regular_of_localized_flat {K : Type w} [CommRing K]
    (g : A) (h : B) (hh : IsSMulRegular B h) (φ : A →+* K) (hg : IsUnit (φ g))
    [Module.Flat (Localization.Away g) (localizedQuotient A g h)] :
    letI : Algebra A K := φ.toAlgebra
    IsSMulRegular (K ⊗[A] B) ((1 : K) ⊗ₜ[A] h) := by
  let : Algebra A K := φ.toAlgebra
  let : Algebra (Localization.Away g) K := (parameterLift A g φ hg).toAlgebra
  let : Module.Flat (Localization.Away g)
      (localizedRing A (B := B) g ⧸ Ideal.span {localizedEquation A g h}) :=
    Module.Flat.of_linearEquiv (principalQuotientIso A g h).toLinearEquiv
  have hreg := NadelBertiniFlatFibre.tensor_regular (Localization.Away g)
    (localizedEquation A g h) (localizedEquation_regular A g h hh) K
  let e := fibreIso A (B := B) g φ hg
  have he : e ((1 : K) ⊗ₜ[Localization.Away g] localizedEquation A g h) =
      (1 : K) ⊗ₜ[A] h := fibreIso_equation A g φ hg h
  change Function.Injective (fun z : K ⊗[A] B => ((1 : K) ⊗ₜ[A] h) * z)
  intro z z' hzz'
  apply e.symm.injective
  apply hreg
  apply e.injective
  simpa only [smul_eq_mul, map_mul, he, e.apply_symm_apply] using hzz'

end EnvelopeProperty.Vanishing.NadelBertiniSncFlatFibre
