/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeParameterProduct
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# The actual Laurent multiplicative-group scheme

The genuine existing Hopf algebra gives a true group object on the actual
Laurent spectrum. Whole tensor and Spec pullback isomorphisms compare its
original group operations to the very Laurent maps used in the action diagrams.
-/

open scoped Classical Polynomial LaurentPolynomial TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.ProjBerk
variable (R : Type u) [CommRing R]

/-- The actual Laurent spectrum as a scheme over the original affine base. -/
abbrev nativeMultiplicativeGroup : Over (Spec (CommRingCat.of R)) :=
  (Spec (CommRingCat.of R[T;T⁻¹])).asOver (Spec (CommRingCat.of R))

/-- The genuine Laurent Hopf algebra supplies the actual existing group-object
structure; no group-scheme or action hypothesis is introduced. -/
instance nativeMultiplicativeGroup_isGrpObj : GrpObj (nativeMultiplicativeGroup R) :=
  inferInstanceAs (GrpObj ((Spec (CommRingCat.of R[T;T⁻¹])).asOver (Spec (CommRingCat.of R))))

/-- The actual scalar tensor equivalence of the two whole Laurent rings. -/
def nativeLaurentTensorEquiv :
    R[T;T⁻¹] ⊗[R] R[T;T⁻¹] ≃ₐ[R[T;T⁻¹]] R[T;T⁻¹][T;T⁻¹] :=
  AddMonoidAlgebra.scalarTensorEquiv R R[T;T⁻¹]

/-- The whole iterated Laurent spectrum is the actual product of the two
genuine multiplicative-group schemes, through true tensor/Spec isomorphisms. -/
def nativeMultiplicativeGroupProductIso :
    Spec (CommRingCat.of R[T;T⁻¹][T;T⁻¹]) ≅
      pullback (nativeMultiplicativeGroup R).hom (nativeMultiplicativeGroup R).hom :=
  (Scheme.Spec.mapIso (nativeLaurentTensorEquiv R).toRingEquiv.toCommRingCatIso.op).trans
    (pullbackSpecIso R R[T;T⁻¹] R[T;T⁻¹]).symm

/-- The actual universal Laurent unit has precisely all original Laurent powers. -/
theorem parameterLaurentUnit_zpow (m : ℤ) :
    ((parameterLaurentUnit R) ^ m : R[T;T⁻¹]ˣ).val = LaurentPolynomial.T m := by
  cases m with
  | ofNat m => simp [zpow_natCast, Units.val_pow_eq_pow_val, parameterLaurentUnit]
  | negSucc m =>
    simp only [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    change LaurentPolynomial.T (-1) ^ (m + 1) = (LaurentPolynomial.T (Int.negSucc m) : R[T;T⁻¹])
    rw [LaurentPolynomial.T_pow]
    congr 1
    omega

/-- The genuine double Laurent product unit has the full original product powers. -/
theorem parameterLaurentProductUnit_zpow (m : ℤ) :
    ((parameterLaurentProductUnit R) ^ m : R[T;T⁻¹][T;T⁻¹]ˣ).val =
      LaurentPolynomial.T m * LaurentPolynomial.C (LaurentPolynomial.T m : R[T;T⁻¹]) := by
  have hp := _root_.mul_zpow (parameterLaurentUnit R[T;T⁻¹])
    (Units.map (LaurentPolynomial.C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹]).toMonoidHom
      (parameterLaurentUnit R)) m
  rw [parameterLaurentProductUnit, hp, Units.val_mul, parameterLaurentUnit_zpow,
    ← map_zpow, Units.coe_map, parameterLaurentUnit_zpow]
  rfl

/-- The actual Laurent Hopf counit is precisely the genuine unit evaluation. -/
theorem nativeLaurentCounit_eq_eval :
    (Bialgebra.counitAlgHom R R[T;T⁻¹]).toRingHom = LaurentPolynomial.eval₂ (RingHom.id R) 1 := by
  apply RingHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | C_mul_T m r =>
    have hc : (Bialgebra.counitAlgHom R R[T;T⁻¹]) (LaurentPolynomial.C r) = r := by
      simpa only [LaurentPolynomial.C_eq_algebraMap, Algebra.algebraMap_self, RingHom.id_apply] using
        (Bialgebra.counitAlgHom R R[T;T⁻¹]).commutes r
    change (Bialgebra.counitAlgHom R R[T;T⁻¹])
      (LaurentPolynomial.C r * LaurentPolynomial.T m) = _
    rw [map_mul, hc]
    change r * Coalgebra.counit (R := R) (LaurentPolynomial.T m : R[T;T⁻¹]) = _
    simp

/-- Actual Hopf comultiplication becomes the original whole product-unit
Laurent homomorphism under the genuine scalar tensor equivalence. -/
theorem nativeLaurentComul_eq_multiplication :
    (nativeLaurentTensorEquiv R).toRingHom.comp
        (Bialgebra.comulAlgHom R R[T;T⁻¹]).toRingHom =
      parameterLaurentMultiplicationHom (R := R) := by
  apply RingHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | C_mul_T m r =>
    have hc : (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R R[T;T⁻¹]))
        (LaurentPolynomial.C r) = LaurentPolynomial.C (LaurentPolynomial.C r) := by
      change (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R R[T;T⁻¹])) (.single 0 r) =
        .single 0 (LaurentPolynomial.C r)
      rw [AddMonoidAlgebra.mapAlgHom_single]
      rfl
    have ht : (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R R[T;T⁻¹]))
        (LaurentPolynomial.T m) = (LaurentPolynomial.T m : R[T;T⁻¹][T;T⁻¹]) := by
      change (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R R[T;T⁻¹])) (.single m 1) = .single m 1
      rw [AddMonoidAlgebra.mapAlgHom_single, map_one]
    simp [nativeLaurentTensorEquiv, parameterLaurentMultiplicationHom,
      parameterLaurentProductUnit_zpow, hc, ht, LaurentPolynomial.smul_eq_C_mul]
    ring

/-- The actual existing group-object unit is exactly the true Laurent
evaluation at one used in the whole unit-section diagrams. -/
theorem nativeMultiplicativeGroup_one :
    (MonObj.one (X := nativeMultiplicativeGroup R)).left =
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id R) 1)) := by
  rw [one_spec_asOver_spec_left]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (nativeLaurentCounit_eq_eval R)

/-- Under the whole double-Laurent product isomorphism, actual group-object
multiplication is precisely the original full product-unit Laurent morphism. -/
theorem nativeMultiplicativeGroup_mul :
    (nativeMultiplicativeGroupProductIso R).hom ≫
        (MonObj.mul (X := nativeMultiplicativeGroup R)).left =
      Spec.map (CommRingCat.ofHom (parameterLaurentMultiplicationHom (R := R))) := by
  rw [mul_spec_asOver_spec_left]
  change ((Scheme.Spec.mapIso (nativeLaurentTensorEquiv R).toRingEquiv.toCommRingCatIso.op).hom ≫
      (pullbackSpecIso R R[T;T⁻¹] R[T;T⁻¹]).inv) ≫
      ((pullbackSpecIso R R[T;T⁻¹] R[T;T⁻¹]).hom ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R R[T;T⁻¹]).toRingHom)) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  change Spec.map (CommRingCat.ofHom (nativeLaurentTensorEquiv R).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R R[T;T⁻¹]).toRingHom) = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((nativeLaurentTensorEquiv R).toRingHom.comp
    (Bialgebra.comulAlgHom R R[T;T⁻¹]).toRingHom)) = _
  rw [nativeLaurentComul_eq_multiplication]

end EnvelopeProperty.ProjBerk
