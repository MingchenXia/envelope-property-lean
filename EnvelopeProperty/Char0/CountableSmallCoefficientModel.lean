import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Data.Countable.Small
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.RingHom.Smooth

/-! # Actual countable coefficient FIELD and model in universe zero

Both the coefficient field and the original affine model are canonically
shrunk. The scalar action is the literal original action through the actual
field equivalence. Existing compatible-scalar tensor equivalence retains all
original coefficients and whole ideals. No Scheme-universe/kernel transport
or embedding of an arbitrary original ambient field is asserted.
-/

noncomputable section
open scoped TensorProduct
namespace EnvelopeProperty.Char0.CountableSmallCoefficientModel
universe u v w

variable (F : Type u) [Field F] [Countable F]

/-- The actual countable original coefficient FIELD in universe zero. -/
def Field0 : Type := Shrink.{0} F

instance field0Field : Field (Field0 F) := inferInstanceAs (Field (Shrink.{0} F))

/-- The canonical entire original coefficient-field equivalence. -/
def fieldEquiv : Field0 F ≃+* F := Shrink.ringEquiv.{0} F

instance field0Countable : Countable (Field0 F) := (fieldEquiv F).injective.countable

instance field0CharZero [CharZero F] : CharZero (Field0 F) := by
  constructor
  intro m n h
  have hF : (m : F) = n := by simpa only [map_natCast] using congrArg (fieldEquiv F) h
  exact @CharZero.cast_injective F _ inferInstance m n hF

instance field0Algebra : Algebra (Field0 F) F := (fieldEquiv F).toRingHom.toAlgebra

variable (A₀ : Type v) [CommRing A₀] [Algebra F A₀] [Countable A₀]

/-- The actual countable original MODEL in universe zero. -/
abbrev Model0 : Type := Shrink.{0} A₀

/-- The actual original F-algebra equivalence of the whole small model. -/
def modelEquiv : Model0 A₀ ≃ₐ[F] A₀ := Shrink.algEquiv.{0} F A₀

instance model0Algebra : Algebra (Field0 F) (Model0 A₀) :=
  ((algebraMap F (Model0 A₀)).comp (fieldEquiv F).toRingHom).toAlgebra

instance model0Tower : IsScalarTower (Field0 F) F (Model0 A₀) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The actual small coefficient action reads back as the SAME whole original action. -/
theorem coefficient_square (c : Field0 F) :
    modelEquiv F A₀ (algebraMap (Field0 F) (Model0 A₀) c) =
      algebraMap F A₀ (fieldEquiv F c) :=
  (modelEquiv F A₀).commutes (fieldEquiv F c)

/-- Whole original scalar multiplication is retained for EVERY model element. -/
theorem scalar_readback (c : Field0 F) (a : Model0 A₀) :
    modelEquiv F A₀ (c • a) = fieldEquiv F c • modelEquiv F A₀ a := by
  change modelEquiv F A₀ ((algebraMap F (Model0 A₀) (fieldEquiv F c)) * a) = _
  rw [map_mul, (modelEquiv F A₀).commutes]
  exact (Algebra.smul_def _ _).symm

/-- Actual original integrality is preserved by the SAME canonical model equivalence. -/
theorem model_isDomain [IsDomain A₀] : IsDomain (Model0 A₀) :=
  (Shrink.ringEquiv.{0} A₀).isDomain

/-- Actual original smoothness over F gives genuine smoothness over the SAME
actual universe-zero coefficient field, not a supplied smooth-model certificate. -/
theorem model_smooth [Algebra.Smooth F A₀] : Algebra.Smooth (Field0 F) (Model0 A₀) := by
  let : Algebra.Smooth F (Model0 A₀) := Algebra.Smooth.of_equiv (modelEquiv F A₀).symm
  let : Algebra.Smooth (Field0 F) F := RingHom.smooth_algebraMap.mp
    (RingHom.Smooth.of_bijective (fieldEquiv F).bijective)
  exact Algebra.Smooth.comp (Field0 F) F (Model0 A₀)

/-- The WHOLE original ideal on the SAME actual small model. -/
def modelIdeal (I : Ideal A₀) : Ideal (Model0 A₀) := I.comap (modelEquiv F A₀).toRingHom

omit [Countable F] in
/-- The entire original model ideal reads back exactly, with all coefficients. -/
theorem modelIdeal_map (I : Ideal A₀) :
    (modelIdeal F A₀ I).map (modelEquiv F A₀).toRingHom = I :=
  Ideal.map_comap_of_surjective _ (modelEquiv F A₀).surjective I

omit [Countable F] in
/-- The actual small model retains the WHOLE product of original ideals. -/
theorem modelIdeal_mul (I J : Ideal A₀) :
    modelIdeal F A₀ (I * J) = modelIdeal F A₀ I * modelIdeal F A₀ J := by
  have he (I : Ideal A₀) : modelIdeal F A₀ I = I.map (modelEquiv F A₀).symm.toRingHom :=
    (Ideal.map_comap_of_equiv (modelEquiv F A₀).toRingEquiv.symm).symm
  rw [he, Ideal.map_mul, he, he]

variable (L : Type w) [CommRing L] [Algebra F L]

/-- The actual small coefficient-field action on EVERY original F-algebra target. -/
@[instance_reducible]
def targetAlgebra : Algebra (Field0 F) L :=
  ((algebraMap F L).comp (fieldEquiv F).toRingHom).toAlgebra

/-- The LITERAL scalar-transport equivalence, before and after changing the
actual base field. Both base field and source model on the left are Type0. -/
def tensorEquiv :
    letI := targetAlgebra F L
    (L ⊗[Field0 F] Model0 A₀) ≃ₐ[L] (L ⊗[F] A₀) := by
  letI := targetAlgebra F L
  let : IsScalarTower (Field0 F) F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : TensorProduct.CompatibleSMul (Field0 F) F L (Model0 A₀) :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective L (Model0 A₀) (fieldEquiv F).surjective
  exact (Algebra.TensorProduct.equivOfCompatibleSMul F (Field0 F) L L (Model0 A₀)).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) (modelEquiv F A₀))

/-- EVERY original tensor coefficient and whole model element has its literal readback. -/
theorem tensorEquiv_tmul (l : L) (a : Model0 A₀) :
    letI := targetAlgebra F L
    tensorEquiv F A₀ L (l ⊗ₜ[Field0 F] a) = l ⊗ₜ[F] modelEquiv F A₀ a := rfl

/-- The inverse reads back EVERY whole original target model coefficient. -/
theorem tensorEquiv_symm_tmul (l : L) (a : A₀) :
    letI := targetAlgebra F L
    (tensorEquiv F A₀ L).symm (l ⊗ₜ[F] a) =
      l ⊗ₜ[Field0 F] (modelEquiv F A₀).symm a := by
  let := targetAlgebra F L
  apply (tensorEquiv F A₀ L).injective
  rw [AlgEquiv.apply_symm_apply, tensorEquiv_tmul, AlgEquiv.apply_symm_apply]

/-- The WHOLE original ideal square commutes with actual base-FIELD and model
transport, not merely with an abstract vector-space or ring isomorphism. -/
theorem map_tensor_modelIdeal (I : Ideal A₀) :
    letI := targetAlgebra F L
    ((modelIdeal F A₀ I).map
      (Algebra.TensorProduct.includeRight (R := Field0 F) (A := L)).toRingHom).map
        (tensorEquiv F A₀ L).toRingHom =
      I.map (Algebra.TensorProduct.includeRight (R := F) (A := L)).toRingHom := by
  let := targetAlgebra F L
  rw [Ideal.map_map]
  have h : (tensorEquiv F A₀ L).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := Field0 F) (A := L)).toRingHom =
      (Algebra.TensorProduct.includeRight (R := F) (A := L)).toRingHom.comp
        (modelEquiv F A₀).toRingHom := by
    ext a
    rfl
  rw [h, ← Ideal.map_map, modelIdeal_map]

end EnvelopeProperty.Char0.CountableSmallCoefficientModel
