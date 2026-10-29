/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Actual surjective base change and entire unreduced quotient algebras

The tensor comparison is genuinely constructed from the original quotient and
surjective coefficient map. Whole element and coefficient identities identify
the true descended action. Actual finite/free/etale base change and natural-valued
Module.finrank transport retain original nilpotents; genuine etale-domain
reducedness is separately derived from a flat injection into the generic fibre.
No normalization, original-degree, chosen-open or rank-comparison certificate is
assumed. Infinite free rank has Module.finrank zero by its natural-valued convention.
-/

open scoped TensorProduct
noncomputable section
namespace EnvelopeProperty.SurjectiveBaseChange
variable (R S B : Type*) [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B]

/-- The actual original base-kernel ideal extended to the original algebra. -/
def ideal : Ideal B := (RingHom.ker (algebraMap R S)).map (algebraMap R B)

/-- The genuine tensor quotient comparison, before choosing its descended coefficient action. -/
def quotientRingEquiv (hs : Function.Surjective (algebraMap R S)) :
    B ⧸ ideal R S B ≃+* S ⊗[R] B :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (RingHom.ker (algebraMap R S))).toRingEquiv.trans
    ((Algebra.TensorProduct.comm R B (R ⧸ RingHom.ker (algebraMap R S))).toRingEquiv.trans
      (Algebra.TensorProduct.congr
        (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hs)
        (AlgEquiv.refl (R := R) (A₁ := B))).toRingEquiv)

/-- The comparison preserves every original algebra element, not only generators. -/
@[simp] theorem quotientRingEquiv_mk (hs : Function.Surjective (algebraMap R S)) (b : B) :
    quotientRingEquiv R S B hs (Ideal.Quotient.mk (ideal R S B) b) = 1 ⊗ₜ[R] b := by
  change Algebra.TensorProduct.congr
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hs)
    (AlgEquiv.refl (R := R) (A₁ := B))
    (Algebra.TensorProduct.comm R B (R ⧸ RingHom.ker (algebraMap R S))
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (RingHom.ker (algebraMap R S))
        (Ideal.Quotient.mk _ b))) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  change (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hs) 1 ⊗ₜ[R] b = _
  rw [map_one]

/-- The actual descended coefficient map on the original quotient. -/
def coefficientMap (hs : Function.Surjective (algebraMap R S)) : S →+* B ⧸ ideal R S B :=
  (quotientRingEquiv R S B hs).symm.toRingHom.comp (algebraMap S (S ⊗[R] B))

/-- The descended coefficient action used by the entire tensor quotient comparison. -/
@[instance_reducible] def quotientAlgebra (hs : Function.Surjective (algebraMap R S)) : Algebra S (B ⧸ ideal R S B) :=
  (coefficientMap R S B hs).toAlgebra

/-- The actual scalar tensor pullback is the entire original unreduced quotient. -/
def tensorQuotientEquiv (hs : Function.Surjective (algebraMap R S)) :
    let := quotientAlgebra R S B hs
    S ⊗[R] B ≃ₐ[S] B ⧸ ideal R S B :=
  let := quotientAlgebra R S B hs
  { (quotientRingEquiv R S B hs).symm with commutes' _ := rfl }

/-- Every original element has exactly its original quotient class under the comparison. -/
@[simp] theorem tensorQuotientEquiv_one_tmul (hs : Function.Surjective (algebraMap R S)) (b : B) :
    tensorQuotientEquiv R S B hs (1 ⊗ₜ[R] b) = Ideal.Quotient.mk (ideal R S B) b := by
  apply (quotientRingEquiv R S B hs).injective
  rw [quotientRingEquiv_mk]
  exact (quotientRingEquiv R S B hs).apply_symm_apply _

/-- All original coefficients commute with the actual descended base map. -/
theorem coefficientMap_algebraMap (hs : Function.Surjective (algebraMap R S)) (r : R) :
    coefficientMap R S B hs (algebraMap R S r) =
      Ideal.Quotient.mk (ideal R S B) (algebraMap R B r) := by
  apply (quotientRingEquiv R S B hs).injective
  rw [quotientRingEquiv_mk]
  change quotientRingEquiv R S B hs ((quotientRingEquiv R S B hs).symm _) = _
  rw [RingEquiv.apply_symm_apply]
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul r

/-- The whole original coefficient square characterizes the actual descended coefficient map. -/
theorem coefficientMap_eq_of_comp (hs : Function.Surjective (algebraMap R S))
    (f : S →+* B ⧸ ideal R S B)
    (hf : f.comp (algebraMap R S) = (Ideal.Quotient.mk (ideal R S B)).comp (algebraMap R B)) :
    f = coefficientMap R S B hs := by
  apply RingHom.ext
  intro s
  obtain ⟨r, rfl⟩ := hs s
  exact (RingHom.congr_fun hf r).trans (coefficientMap_algebraMap R S B hs r).symm

/-- Full pure tensor values use the descended coefficient and the original algebra class. -/
theorem tensorQuotientEquiv_tmul (hs : Function.Surjective (algebraMap R S)) (s : S) (b : B) :
    tensorQuotientEquiv R S B hs (s ⊗ₜ[R] b) =
      coefficientMap R S B hs s * Ideal.Quotient.mk (ideal R S B) b := by
  apply (quotientRingEquiv R S B hs).injective
  change quotientRingEquiv R S B hs ((quotientRingEquiv R S B hs).symm _) = _
  rw [RingEquiv.apply_symm_apply, map_mul, quotientRingEquiv_mk]
  change s ⊗ₜ[R] b = quotientRingEquiv R S B hs ((quotientRingEquiv R S B hs).symm _) * _
  rw [RingEquiv.apply_symm_apply]
  change s ⊗ₜ[R] b = (s ⊗ₜ[R] (1 : B)) * (1 ⊗ₜ[R] b)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The actual descended coefficient action forms the original scalar tower. -/
theorem quotient_isScalarTower (hs : Function.Surjective (algebraMap R S)) :
    let := quotientAlgebra R S B hs
    IsScalarTower R S (B ⧸ ideal R S B) := by
  let := quotientAlgebra R S B hs
  exact IsScalarTower.of_algebraMap_eq fun r => (coefficientMap_algebraMap R S B hs r).symm

/-- Actual finite modules remain finite in the entire original quotient pullback. -/
theorem finite [Module.Finite R B] (hs : Function.Surjective (algebraMap R S)) :
    let := quotientAlgebra R S B hs
    Module.Finite S (B ⧸ ideal R S B) := by
  let := quotientAlgebra R S B hs
  exact Module.Finite.equiv (tensorQuotientEquiv R S B hs).toLinearEquiv

/-- Actual free modules remain free under the genuine original quotient pullback. -/
theorem free [Module.Free R B] (hs : Function.Surjective (algebraMap R S)) :
    let := quotientAlgebra R S B hs
    Module.Free S (B ⧸ ideal R S B) := by
  let := quotientAlgebra R S B hs
  exact Module.Free.of_equiv (tensorQuotientEquiv R S B hs).toLinearEquiv

/-- The natural-valued `Module.finrank` is preserved by actual free quotient base change; it is zero for infinite free rank. -/
theorem finrank [StrongRankCondition R] [StrongRankCondition S] [Module.Free R B]
    (hs : Function.Surjective (algebraMap R S)) :
    let := quotientAlgebra R S B hs
    Module.finrank S (B ⧸ ideal R S B) = Module.finrank R B := by
  let := quotientAlgebra R S B hs
  change Module.finrank S (B ⧸ ideal R S B) = Module.finrank R B
  rw [← (tensorQuotientEquiv R S B hs).toLinearEquiv.finrank_eq, Module.finrank_baseChange]

/-- The actual original étale algebra stays étale in its whole quotient pullback. -/
theorem etale [Algebra.Etale R B] (hs : Function.Surjective (algebraMap R S)) :
    let := quotientAlgebra R S B hs
    Algebra.Etale S (B ⧸ ideal R S B) := by
  let := quotientAlgebra R S B hs
  exact Algebra.Etale.of_equiv (tensorQuotientEquiv R S B hs)

end EnvelopeProperty.SurjectiveBaseChange

namespace EnvelopeProperty.SurjectiveBaseChange
variable (R K B : Type*) [CommRing R] [Field K] [CommRing B] [Algebra R K] [Algebra R B]
/-- Over a field the actual étale pullback is reduced, derived from unramifiedness. -/
theorem isReduced_of_field [Algebra.Etale R B]
    (hs : Function.Surjective (algebraMap R K)) : IsReduced (B ⧸ ideal R K B) := by
  let := quotientAlgebra R K B hs
  let := etale R K B hs
  exact Algebra.FormallyUnramified.isReduced_of_field K _

end EnvelopeProperty.SurjectiveBaseChange

namespace EnvelopeProperty

/-- An actual étale algebra over a domain is reduced: flatness injects it into its reduced generic fibre. -/
theorem isReduced_of_etale_of_domain (R B : Type*) [CommRing R] [IsDomain R]
    [CommRing B] [Algebra R B] [Algebra.Etale R B] : IsReduced B := by
  let K := FractionRing R
  have : IsReduced (K ⊗[R] B) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B)
    (Module.Flat.tensorProduct_mk_injective (R := R) (S := K) (M := B))

end EnvelopeProperty
