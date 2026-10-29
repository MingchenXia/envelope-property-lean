/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.ComponentQuotient
import EnvelopeProperty.ComponentNormalizationProduct

/-!
# Literal normalizations of the original quotient components

The actual minimal-prime quotient comparison induces genuine fraction-field and
integral-closure equivalences. Reindexing their whole product retains every
original unreduced quotient element and its actual quotient coefficient action.
No finiteness, reducedness, perfect field or chosen normalization comparison is
assumed, and the original ideal is not replaced by its radical.
-/

noncomputable section
namespace EnvelopeProperty

/-- Actual integral change of the coefficient base does not change the genuine integral-closure subring. -/
theorem isIntegralClosure_of_integral_base
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommSemiring C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra C B] [IsIntegralClosure C A B] [Algebra.IsIntegral R A] :
    IsIntegralClosure C R B := by
  constructor
  · exact IsIntegralClosure.algebraMap_injective C A B
  · intro x
    rw [← IsIntegralClosure.isIntegral_iff (A := C) (R := A) (B := B)]
    exact ⟨fun h => h.tower_top, fun h => isIntegral_trans x h⟩

namespace ReducedComponents
variable {R : Type*} [CommRing R]

/-- The actual normalization of a quotient component is the literal original component normalization, with the whole original coefficient action. -/
def quotientComponentNormalizationEquiv (I : Ideal R) (p : Index I) :
    CurveNormalization.Ring (Component (⊥ : Ideal (R ⧸ I)) (quotientIndexEquiv I p)) ≃ₐ[R]
      CurveNormalization.Ring (Component I p) := by
  let C := Component (⊥ : Ideal (R ⧸ I)) (quotientIndexEquiv I p)
  let D := Component I p
  let L := FractionRing C
  let M := FractionRing D
  have : Algebra.IsIntegral R C := Algebra.IsIntegral.trans (R ⧸ I)
  have : IsIntegralClosure (CurveNormalization.Ring C) R L :=
    isIntegralClosure_of_integral_base (A := C)
  have : IsIntegralClosure (CurveNormalization.Ring D) R M :=
    isIntegralClosure_of_integral_base (A := D)
  let e : L ≃ₐ[R] M := IsFractionRing.algEquivOfAlgEquiv (K := L) (L := M) (quotientComponentEquiv I p)
  exact (IsIntegralClosure.equiv R (CurveNormalization.Ring C) L (integralClosure R L)).trans
    (e.mapIntegralClosure.trans
      (IsIntegralClosure.equiv R (integralClosure R M) M (CurveNormalization.Ring D)))

/-- Every original ring element has its entire literal normalization class under the actual component comparison. -/
theorem quotientComponentNormalizationEquiv_mk_mk (I : Ideal R) (p : Index I) (r : R) :
    quotientComponentNormalizationEquiv I p
      (CurveNormalization.inclusion _
        (Ideal.Quotient.mk (quotientIndexEquiv I p).1 (Ideal.Quotient.mk I r))) =
      CurveNormalization.inclusion _ (Ideal.Quotient.mk p.1 r) :=
  (quotientComponentNormalizationEquiv I p).commutes r

/-- The true original quotient and its original ideal have genuinely equivalent literal normalization products. -/
def normalizationProductQuotientEquiv (I : Ideal R) :
    NormalizationProduct (⊥ : Ideal (R ⧸ I)) ≃ₐ[R] NormalizationProduct I :=
  (AlgEquiv.piCongrLeft R
    (fun q : Index (⊥ : Ideal (R ⧸ I)) => CurveNormalization.Ring (Component (⊥ : Ideal (R ⧸ I)) q))
    (quotientIndexEquiv I)).symm.trans
      (AlgEquiv.piCongrRight fun p : Index I => quotientComponentNormalizationEquiv I p)

/-- The whole actual normalization-product comparison retains every original function, not only selected coordinates. -/
theorem normalizationProductQuotientEquiv_original (I : Ideal R) (r : R) :
    normalizationProductQuotientEquiv I
      (normalizationMap (⊥ : Ideal (R ⧸ I)) (Ideal.Quotient.mk I r)) = normalizationMap I r :=
  (normalizationProductQuotientEquiv I).commutes r

/-- Every entire original unreduced quotient element follows its actual original normalization map. -/
theorem normalizationProductQuotientEquiv_quotient (I : Ideal R) (q : R ⧸ I) :
    normalizationProductQuotientEquiv I (normalizationMap (⊥ : Ideal (R ⧸ I)) q) =
      originalNormalizationMap I q := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [normalizationProductQuotientEquiv_original]
  rfl

/-- The actual original unreduced quotient coefficient action on its literal original normalization product. -/
@[instance_reducible] def normalizationProductQuotientAlgebra (I : Ideal R) :
    Algebra (R ⧸ I) (NormalizationProduct I) := (originalNormalizationMap I).toAlgebra

/-- The actual normalization-product comparison is an algebra equivalence for the entire ORIGINAL quotient action. -/
def normalizationProductQuotientEquivOverQuotient (I : Ideal R) :
    letI := normalizationProductQuotientAlgebra I
    NormalizationProduct (⊥ : Ideal (R ⧸ I)) ≃ₐ[R ⧸ I] NormalizationProduct I :=
  letI := normalizationProductQuotientAlgebra I
  { (normalizationProductQuotientEquiv I).toRingEquiv with
      commutes' := normalizationProductQuotientEquiv_quotient I }

end ReducedComponents
end EnvelopeProperty
