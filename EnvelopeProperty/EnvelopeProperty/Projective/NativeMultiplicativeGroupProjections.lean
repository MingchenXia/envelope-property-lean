/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeMultiplicativeGroup

/-!
# Whole actual coordinate projections of the genuine group product

The actual double Laurent/group-product isomorphism preserves both complete
original coordinate morphisms and the base triangle. These are used to package
the already proved action diagrams in the existing categorical interface.
-/

open scoped Classical Polynomial LaurentPolynomial TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.ProjBerk
variable (R : Type u) [CommRing R]

/-- The actual scalar tensor equivalence has precisely the first whole coordinate map. -/
theorem nativeLaurentTensorEquiv_comp_includeLeft :
    (nativeLaurentTensorEquiv R).toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
      (LaurentPolynomial.C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹]) := by
  apply RingHom.ext
  intro p
  exact (nativeLaurentTensorEquiv R).commutes p

/-- The actual scalar tensor equivalence has precisely the second whole coordinate map. -/
theorem nativeLaurentTensorEquiv_comp_includeRight :
    (nativeLaurentTensorEquiv R).toRingHom.comp
        (Algebra.TensorProduct.includeRight : R[T;T⁻¹] →ₐ[R] R[T;T⁻¹] ⊗[R] R[T;T⁻¹]).toRingHom =
      AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.C : R →+* R[T;T⁻¹]) := by
  apply RingHom.ext
  intro p
  change AddMonoidAlgebra.scalarTensorEquiv R R[T;T⁻¹] (1 ⊗ₜ[R] p) = _
  rw [AddMonoidAlgebra.scalarTensorEquiv_tmul, one_smul]
  rfl

/-- The entire genuine group-product comparison has the first actual group coordinate. -/
@[reassoc]
theorem nativeMultiplicativeGroupProductIso_fst :
    (nativeMultiplicativeGroupProductIso R).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹])) := by
  change ((Scheme.Spec.mapIso (nativeLaurentTensorEquiv R).toRingEquiv.toCommRingCatIso.op).hom ≫
    (pullbackSpecIso R R[T;T⁻¹] R[T;T⁻¹]).inv) ≫
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])))
      (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹]))) = _
  rw [Category.assoc, pullbackSpecIso_inv_fst]
  change Spec.map (CommRingCat.ofHom (nativeLaurentTensorEquiv R).toRingHom) ≫
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((nativeLaurentTensorEquiv R).toRingHom.comp
    Algebra.TensorProduct.includeLeftRingHom)) = _
  rw [nativeLaurentTensorEquiv_comp_includeLeft]

/-- The entire genuine group-product comparison has the second actual group coordinate. -/
@[reassoc]
theorem nativeMultiplicativeGroupProductIso_snd :
    (nativeMultiplicativeGroupProductIso R).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.C : R →+* R[T;T⁻¹]))) := by
  change ((Scheme.Spec.mapIso (nativeLaurentTensorEquiv R).toRingEquiv.toCommRingCatIso.op).hom ≫
    (pullbackSpecIso R R[T;T⁻¹] R[T;T⁻¹]).inv) ≫
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])))
      (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹]))) = _
  rw [Category.assoc, pullbackSpecIso_inv_snd]
  change Spec.map (CommRingCat.ofHom (nativeLaurentTensorEquiv R).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : R[T;T⁻¹] →ₐ[R] R[T;T⁻¹] ⊗[R] R[T;T⁻¹]).toRingHom) = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((nativeLaurentTensorEquiv R).toRingHom.comp
    (Algebra.TensorProduct.includeRight : R[T;T⁻¹] →ₐ[R] R[T;T⁻¹] ⊗[R] R[T;T⁻¹]).toRingHom)) = _
  rw [nativeLaurentTensorEquiv_comp_includeRight]

/-- The whole original group-product base triangle is the true iterated coefficient inclusion. -/
@[reassoc]
theorem nativeMultiplicativeGroupProductIso_base :
    (nativeMultiplicativeGroupProductIso R).hom ≫
        (nativeMultiplicativeGroup R ⊗ nativeMultiplicativeGroup R).hom =
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.C.comp (LaurentPolynomial.C : R →+* R[T;T⁻¹]))) := by
  change _ ≫ pullback.fst _ _ ≫ (nativeMultiplicativeGroup R).hom = _
  rw [← Category.assoc, nativeMultiplicativeGroupProductIso_fst]
  change Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹])) ≫
    Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* R[T;T⁻¹])) = _
  rw [← Spec.map_comp]
  rfl

/-- The actual universal first group coordinate is evaluation at the mapped
first Laurent unit over the whole double Laurent coefficient ring. -/
theorem nativeLaurent_eval_first :
    LaurentPolynomial.eval₂
        (LaurentPolynomial.C.comp (LaurentPolynomial.C : R →+* R[T;T⁻¹]))
        (Units.map (LaurentPolynomial.C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹]).toMonoidHom
          (parameterLaurentUnit R)) =
      (LaurentPolynomial.C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹]) := by
  apply RingHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | C_mul_T m r =>
    rw [LaurentPolynomial.eval₂_C_mul_T, ← map_zpow, Units.coe_map, parameterLaurentUnit_zpow]
    simp only [RingHom.comp_apply, map_mul]
    rfl

/-- The actual universal second group coordinate is evaluation at the second
Laurent unit, preserving the entire original first coefficient ring. -/
theorem nativeLaurent_eval_second :
    LaurentPolynomial.eval₂
        (LaurentPolynomial.C.comp (LaurentPolynomial.C : R →+* R[T;T⁻¹]))
        (parameterLaurentUnit R[T;T⁻¹]) =
      AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.C : R →+* R[T;T⁻¹]) := by
  apply RingHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | C_mul_T m r =>
    have hc : AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.C : R →+* R[T;T⁻¹])
        (LaurentPolynomial.C r) = LaurentPolynomial.C (LaurentPolynomial.C r) := by
      change AddMonoidAlgebra.mapRingHom ℤ LaurentPolynomial.C (.single 0 r) =
        .single 0 (LaurentPolynomial.C r)
      rw [AddMonoidAlgebra.mapRingHom_single]
    have ht : AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.C : R →+* R[T;T⁻¹])
        (LaurentPolynomial.T m) = (LaurentPolynomial.T m : R[T;T⁻¹][T;T⁻¹]) := by
      change AddMonoidAlgebra.mapRingHom ℤ LaurentPolynomial.C (.single m 1) = .single m 1
      rw [AddMonoidAlgebra.mapRingHom_single, map_one]
    rw [LaurentPolynomial.eval₂_C_mul_T, parameterLaurentUnit_zpow, map_mul, hc, ht]
    rfl

end EnvelopeProperty.ProjBerk
