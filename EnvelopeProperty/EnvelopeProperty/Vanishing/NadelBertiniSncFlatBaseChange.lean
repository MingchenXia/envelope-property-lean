import EnvelopeProperty.Vanishing.NadelBertiniFlatFibre
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Maps

/-! # The actual localized principal quotient and regular original equation -/
noncomputable section
open scoped TensorProduct
universe u v
namespace EnvelopeProperty.Vanishing.NadelBertiniSncFlatBaseChange
variable (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]

/-- The actual scalar localization of the original chart ring. -/
abbrev localizedRing (g : A) := Localization.Away g ⊗[A] B

/-- The actual scalar localization of the original principal quotient. -/
abbrev localizedQuotient (g : A) (h : B) :=
  Localization.Away g ⊗[A] (B ⧸ Ideal.span ({h} : Set B))

/-- The SAME original equation in the actual scalar-localized original chart. -/
def localizedEquation (g : A) (h : B) : localizedRing A (B := B) g :=
  (1 : Localization.Away g) ⊗ₜ[A] h

/-- The WHOLE native localized principal quotient is the actual scalar-localized
original quotient, with no comparison supplied as input. -/
def principalQuotientIso (g : A) (h : B) :
    (localizedRing A (B := B) g ⧸ Ideal.span {localizedEquation A g h}) ≃ₐ[Localization.Away g]
      localizedQuotient A g h := by
  let e := Algebra.TensorProduct.tensorQuotientEquiv (R := A)
    (Localization.Away g) B (Localization.Away g) (Ideal.span ({h} : Set B))
  have he : (Ideal.span ({h} : Set B)).map
      (Algebra.TensorProduct.includeRight (A := Localization.Away g) (R := A)) =
      Ideal.span {localizedEquation A g h} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  exact ((e.trans (Ideal.quotientEquivAlgOfEq (Localization.Away g) he))).symm

/-- The whole original quotient comparison retains actual pure-tensor sections. -/
theorem principalQuotientIso_mk_tmul (g : A) (h b : B) (a : Localization.Away g) :
    principalQuotientIso A g h
      (Ideal.Quotient.mk _ (a ⊗ₜ[A] b)) =
      a ⊗ₜ[A] Ideal.Quotient.mk (Ideal.span ({h} : Set B)) b := by
  change (Algebra.TensorProduct.tensorQuotientEquiv (R := A)
    (Localization.Away g) B (Localization.Away g) (Ideal.span ({h} : Set B))).symm
      ((Ideal.quotientEquivAlgOfEq (Localization.Away g) _).symm
        (Ideal.Quotient.mk _ (a ⊗ₜ[A] b))) = _
  simp

/-- The actual localized original equation is internally regular because the
original base localization is flat, independently of quotient flatness. -/
theorem localizedEquation_regular (g : A) (h : B) (hh : IsSMulRegular B h) :
    IsSMulRegular (localizedRing A (B := B) g) (localizedEquation A g h) := by
  let : Module.Flat A (Localization.Away g) :=
    IsLocalization.flat (Localization.Away g) (Submonoid.powers g)
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap
    (M := Localization.Away g) (NadelBertiniFlatFibre.mulMap A h) hh
  change Function.Injective (fun z : localizedRing A (B := B) g => localizedEquation A g h * z)
  intro z z' heq
  apply hinj
  rw [NadelBertiniFlatFibre.mulMap_lTensor_apply,
    NadelBertiniFlatFibre.mulMap_lTensor_apply]
  exact heq

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- This same tensor ring is the actual ring localization at the original image
of g in B, retaining the original B scalar structure. -/
def ringLocalizationIso (g : A) : localizedRing A (B := B) g ≃ₐ[B]
    Localization.Away (algebraMap A B g) :=
  IsLocalization.Away.tensorRightEquiv B g (Localization.Away g)

/-- This same quotient tensor ring is the actual localization of the ORIGINAL
principal quotient at its ORIGINAL coefficient image of g. -/
def quotientLocalizationIso (g : A) (h : B) : localizedQuotient A g h ≃ₐ[B ⧸ Ideal.span {h}]
    Localization.Away (algebraMap A (B ⧸ Ideal.span {h}) g) :=
  IsLocalization.Away.tensorRightEquiv (B ⧸ Ideal.span {h}) g (Localization.Away g)

end EnvelopeProperty.Vanishing.NadelBertiniSncFlatBaseChange
