import EnvelopeProperty.Char0.AffineFieldEtaleCoordinates
import EnvelopeProperty.Char0.RoundedSncFieldBaseChange
import EnvelopeProperty.Char0.FieldDifferentialJacobian
import EnvelopeProperty.Char0.RelativeJacobianIdeal
import EnvelopeProperty.Char0.AffineTransformIdeals
import Hironaka.Scheme.BlowUp.Composite.Transition
import Hironaka.Scheme.BlowUpSequence.PullbackInduced

/-!
# The whole actual rounded-colon ideal on the literal field tensor

The original SNC ideal and every original coefficient remain literal.
Actual tensor geometry supplies SNC preservation and the full rounded
ideal formula; actual etale coordinates supply the entire Jacobian ideal.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open EnvelopeProperty.CanonicalGeometry
open scoped TensorProduct

universe u

/-- The whole actual affine pullback ideal retains the literal ring map. -/
theorem idealOfSpecSheaf_comap_specMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (J : (Spec (.of R)).IdealSheafData) :
    idealOfSpecSheaf (J.comap (Spec.map (CommRingCat.ofHom f))) =
      (idealOfSpecSheaf J).map f := by
  conv_lhs => rw [← specIdealSheaf_idealOfSpecSheaf J]
  rw [comap_specIdealSheaf_Spec_map, idealOfSpecSheaf_specIdealSheaf]

section Rounded

variable {k L B : Type u} [Field k] [Field L] [CharZero k] [CommRing B]
  [Algebra k L] [Algebra k B] {n : ℕ}

/-- Original actual etale coordinates manufacture SNC on the literal pulled ideal. -/
theorem isIdealOfSncDivisor_fieldTensor (v : Fin n → B)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (J : (Spec (.of B)).IdealSheafData) (hJ : J.IsIdealOfSncDivisor) :
    (J.comap (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := B)).toRingHom))).IsIdealOfSncDivisor := by
  let : SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    smoothOfRelativeDimension_of_etale_coordinates v hv
  let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    SmoothOfRelativeDimension.smooth n _
  exact RoundedSncIdealSheaf.isIdealOfSncDivisor_comap_of_isPullback_specMap
    (isPullback_fieldTensor (k := k) (L := L) (A := B)) J hJ

/-- The ENTIRE actual rounded affine ideal has its actual literal field-tensor image. -/
theorem roundedIdeal_fieldTensor (v : Fin n → B)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (J : (Spec (.of B)).IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    (idealOfSpecSheaf (RoundedSncIdealSheaf.rounded J hJ q)).map
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := B)).toRingHom =
      idealOfSpecSheaf (RoundedSncIdealSheaf.rounded
        (J.comap (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := B)).toRingHom)))
        (isIdealOfSncDivisor_fieldTensor v hv J hJ) q) := by
  let : SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    smoothOfRelativeDimension_of_etale_coordinates v hv
  let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    SmoothOfRelativeDimension.smooth n _
  rw [← RoundedSncIdealSheaf.rounded_comap_of_isPullback_specMap
    (isPullback_fieldTensor (k := k) (L := L) (A := B)) J hJ q,
    idealOfSpecSheaf_comap_specMap]

end Rounded

section Morphism

variable {k L A B : Type u} [Field k] [Field L] [CommRing A] [CommRing B]
  [Algebra k L] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  {n : ℕ}

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual coefficient-extended morphism is the literal tensor map. -/
def fieldTensorMorphism : (L ⊗[k] A) →ₐ[L] (L ⊗[k] B) :=
  Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom k A B)

/-- EVERY original function retains the actual original morphism coefficient. -/
theorem fieldTensorMorphism_one_tmul (a : A) :
    fieldTensorMorphism (k := k) (L := L) (A := A) (B := B) (1 ⊗ₜ[k] a) =
      1 ⊗ₜ[k] algebraMap A B a := rfl

/-- The WHOLE all-source actual Jacobian ideal retains exactly its literal field-tensor extension. -/
theorem affineRelativeJacobianIdeal_fieldTensor
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    letI : Algebra (L ⊗[k] A) (L ⊗[k] B) :=
      (fieldTensorMorphism (k := k) (L := L) (A := A) (B := B)).toAlgebra
    (affineRelativeJacobianIdeal (R := A) (etaleDifferentialBasis v hv)).map
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := B)).toRingHom =
      affineRelativeJacobianIdeal (R := L ⊗[k] A)
        (etaleDifferentialBasis (fieldTensorCoordinates (k := k) (L := L) v)
          (etale_fieldTensorCoordinates v hv)) := by
  let : Algebra (L ⊗[k] A) (L ⊗[k] B) :=
    (fieldTensorMorphism (k := k) (L := L) (A := A) (B := B)).toAlgebra
  let : IsScalarTower L (L ⊗[k] A) (L ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      ((fieldTensorMorphism (k := k) (L := L) (A := A) (B := B)).commutes r).symm
  let : Algebra A (L ⊗[k] B) :=
    ((algebraMap B (L ⊗[k] B)).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B (L ⊗[k] B) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A (L ⊗[k] A) (L ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (fieldTensorMorphism_one_tmul (k := k) (L := L) (A := A) (B := B) a).symm
  rw [affineRelativeJacobianIdeal_eq_span z hz,
    affineRelativeJacobianIdeal_eq_span (fieldTensorCoordinates (k := k) (L := L) z)
      (etale_fieldTensorCoordinates z hz),
    Ideal.map_span, Set.image_singleton,
    etaleDifferentialBasis_fieldTensorCoordinates z hz, etaleDifferentialBasis_fieldTensorCoordinates v hv]
  congr 1
  exact congrArg Set.singleton (relativeDifferentialDet_fieldBaseChange
    (k := k) (L := L) (R := A) (A := B) (R' := L ⊗[k] A) (A' := L ⊗[k] B)
    (etaleDifferentialBasis z hz) (etaleDifferentialBasis v hv))

/-- The ENTIRE actual rounded-colon ideal commutes with literal field extension. -/
theorem roundedColon_fieldTensor [CharZero k]
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (J : (Spec (.of B)).IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    letI : Algebra (L ⊗[k] A) (L ⊗[k] B) :=
      (fieldTensorMorphism (k := k) (L := L) (A := A) (B := B)).toAlgebra
    ((idealOfSpecSheaf (RoundedSncIdealSheaf.rounded J hJ q)).colon
      (affineRelativeJacobianIdeal (R := A) (etaleDifferentialBasis v hv) : Set B)).map
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := B)).toRingHom =
      (idealOfSpecSheaf (RoundedSncIdealSheaf.rounded
        (J.comap (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := B)).toRingHom)))
        (isIdealOfSncDivisor_fieldTensor v hv J hJ) q)).colon
        (affineRelativeJacobianIdeal (R := L ⊗[k] A)
          (etaleDifferentialBasis (fieldTensorCoordinates (k := k) (L := L) v)
            (etale_fieldTensorCoordinates v hv)) : Set (L ⊗[k] B)) := by
  let : Algebra (L ⊗[k] A) (L ⊗[k] B) :=
    (fieldTensorMorphism (k := k) (L := L) (A := A) (B := B)).toAlgebra
  let : Module.Flat B (L ⊗[k] B) := Module.Flat.isBaseChange k B L (L ⊗[k] B)
    (Algebra.IsPushout.out (R := k) (S := B) (R' := L) (S' := L ⊗[k] B))
  have hJac := affineRelativeJacobianIdeal_fieldTensor (L := L) z hz v hv
  have hround := roundedIdeal_fieldTensor (L := L) v hv J hJ q
  change (idealOfSpecSheaf (RoundedSncIdealSheaf.rounded J hJ q)).map
    (algebraMap B (L ⊗[k] B)) = _ at hround
  rw [← hJac, affineRelativeJacobianIdeal_eq_span z hz,
    Ideal.colon_span, Ideal.map_span, Set.image_singleton, Ideal.colon_span]
  change (_ : Ideal B).map (algebraMap B (L ⊗[k] B)) = _
  rw [map_colon_singleton_of_flat, hround]
  rfl

end Morphism

end EnvelopeProperty.Char0
