/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.RelativeJacobianIdeal
import EnvelopeProperty.Cartier.Forms

/-!
# The actual top differential image and its full source Jacobian ideal

The source image is a genuine submodule of the actual top exterior power
of Kaehler differentials and is defined independently of all bases.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open Module
open scoped Classical

section Volume

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] {n : ℕ}

/-- The actual wedge of the original differential basis. -/
def differentialVolumeForm (b : Basis (Fin n) A M) : ⋀[A]^n M :=
  exteriorPower.ιMulti A n b

/-- The actual determinant coordinate on the top exterior module. -/
def differentialVolumeCoordinate (b : Basis (Fin n) A M) : (⋀[A]^n M) →ₗ[A] A :=
  exteriorPower.alternatingMapLinearEquiv b.det

/-- The genuine basis wedge has determinant coordinate one. -/
theorem differentialVolumeCoordinate_form (b : Basis (Fin n) A M) :
    differentialVolumeCoordinate b (differentialVolumeForm b) = 1 := by
  rw [differentialVolumeCoordinate, differentialVolumeForm,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, b.det_self]

/-- The coordinate of a scalar multiple of the genuine volume form is that scalar. -/
theorem differentialVolumeCoordinate_smul_form (b : Basis (Fin n) A M) (a : A) :
    differentialVolumeCoordinate b (a • differentialVolumeForm b) = a := by
  rw [map_smul, differentialVolumeCoordinate_form, smul_eq_mul, mul_one]

/-- Every genuine top exterior vector is its determinant coordinate times the basis wedge. -/
theorem differentialVolumeCoordinate_smul_differentialVolumeForm
    (b : Basis (Fin n) A M) (ω : ⋀[A]^n M) :
    differentialVolumeCoordinate b ω • differentialVolumeForm b = ω := by
  have h : (LinearMap.smulRight (differentialVolumeCoordinate b) (differentialVolumeForm b) :
      (⋀[A]^n M) →ₗ[A] (⋀[A]^n M)) = LinearMap.id := by
    refine LinearMap.ext_on_range (exteriorPower.ιMulti_span A n M) fun v => ?_
    rw [LinearMap.smulRight_apply, LinearMap.id_apply, differentialVolumeCoordinate,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      EnvelopeProperty.Cartier.alternatingMap_eq_det_smul b (exteriorPower.ιMulti A n) v]
    rfl
  exact LinearMap.congr_fun h ω

/-- The actual top exterior module is canonically trivialized by any actual basis. -/
def differentialVolumeEquiv (b : Basis (Fin n) A M) : (⋀[A]^n M) ≃ₗ[A] A where
  toLinearMap := differentialVolumeCoordinate b
  invFun a := a • differentialVolumeForm b
  left_inv := differentialVolumeCoordinate_smul_differentialVolumeForm b
  right_inv := differentialVolumeCoordinate_smul_form b

end Volume

variable {k R A : Type*} [CommRing k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A]

/-- The full actual original-source top differential image in the genuine target
canonical module, independent of every target basis. -/
def affineCanonicalDifferentialImage (n : ℕ) : Submodule A (⋀[A]^n (KaehlerDifferential k A)) :=
  Submodule.span A (Set.range fun w : Fin n → R => exteriorPower.ιMulti A n
    (fun j => KaehlerDifferential.D k A (algebraMap R A (w j))))

omit [Algebra k R] [IsScalarTower k R A] in
/-- On every original-source differential wedge, the actual volume coordinate
is its actual original-source Jacobian determinant. -/
theorem differentialVolumeCoordinate_sourceFunctions {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential k A)) (w : Fin n → R) :
    differentialVolumeCoordinate b (exteriorPower.ιMulti A n
      (fun j => KaehlerDifferential.D k A (algebraMap R A (w j)))) =
        (sourceFunctionDifferentialMatrix b w).det := by
  rw [differentialVolumeCoordinate, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    Basis.det_apply]
  rfl

omit [Algebra k R] [IsScalarTower k R A] in
/-- The entire actual top differential image, rather than just its generators,
identifies with the full original-source Jacobian ideal under volume coordinates. -/
theorem map_affineCanonicalDifferentialImage {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential k A)) :
    (affineCanonicalDifferentialImage (k := k) (R := R) (A := A) n).map
        (differentialVolumeEquiv b).toLinearMap =
      (affineRelativeJacobianIdeal (R := R) b : Submodule A A) := by
  rw [affineCanonicalDifferentialImage, Submodule.map_span, affineRelativeJacobianIdeal]
  congr 1
  rw [← Set.range_comp]
  apply congrArg Set.range
  funext w
  exact differentialVolumeCoordinate_sourceFunctions b w

end EnvelopeProperty.Char0
