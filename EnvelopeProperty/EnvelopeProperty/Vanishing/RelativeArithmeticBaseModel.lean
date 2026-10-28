import EnvelopeProperty.AlgGeom.ArithmeticSmoothCoefficientBase
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Arithmetic models of the original arbitrary affine base

The arithmetic coefficient ring is a smooth integer subalgebra of the
original field.  The original finite-type algebra is retained as a distinct
scalar fibre, with no domain or reducedness hypothesis on that algebra.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticBaseModel

variable {A k B R : Type u} [CommRing A] [Field k] [CommRing B] [CommRing R]
    [Algebra A k] [Algebra A B] [Algebra k R]

/-- The original coefficient map of a literal tensor model, retaining the
original target algebra rather than replacing it by its tensor presentation. -/
def originalMap (e : k ⊗[A] B ≃ₐ[k] R) : B →+* R :=
  e.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := A) (A := k) (B := B)).toRingHom

/-- The actual tensor equivalence produces the original affine-base square. -/
theorem original_isPullback (e : k ⊗[A] B ≃ₐ[k] R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (originalMap e)))
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A k))) := by
  have H : IsPushout
      (CommRingCat.ofHom (algebraMap A k))
      (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (algebraMap k R))
      (CommRingCat.ofHom (originalMap e)) := by
    apply (CommRingCat.isPushout_tensorProduct A k B).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso
    · rfl
    · rfl
    · ext x
      exact e.commutes x
    · rfl
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ H).flip

/-- Every original finite-type affine base has a produced smooth arithmetic
coefficient domain and a separate finite-presentation model, together with
its actual original cartesian square.  The original algebra may be nonreduced. -/
theorem exists_original_base_model {k R : Type u} [Field k] [CharZero k]
    [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (extra : Finset k) :
    ∃ (A : Subalgebra ℤ k), Algebra.Smooth ℤ A ∧ Algebra.FiniteType ℤ A ∧
      (∀ c ∈ extra, c ∈ A) ∧
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
        Algebra.FinitePresentation A B ∧
        ∃ e : k ⊗[A] B ≃ₐ[k] R,
          IsPullback
            (Spec.map (CommRingCat.ofHom (originalMap e)))
            (Spec.map (CommRingCat.ofHom (algebraMap k R)))
            (Spec.map (CommRingCat.ofHom (algebraMap A B)))
            (Spec.map (CommRingCat.ofHom (algebraMap A k))) := by
  let : Algebra.FinitePresentation k R :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨m, s, ⟨P⟩⟩ := Algebra.Presentation.exists_presentation_fin k R
  obtain ⟨a, ha, hSmooth, hFT, hExtra, _, hFP, _⟩ :=
    ArithmeticSmoothCoefficientBase.exists_smooth_original_presentation_base P extra
  let A := ArithmeticSmoothCoefficientBase.localizedCoefficientRing
    (ArithmeticCoefficientModel.coefficientRing P.relation extra) a ha
  let B := ArithmeticSmoothCoefficientBase.localizedPresentationModel P extra a ha
  let e := ArithmeticSmoothCoefficientBase.localizedPresentationTensorEquiv P extra a ha
  exact ⟨A, hSmooth, hFT, hExtra, B, inferInstance, inferInstance, hFP, e,
    original_isPullback e⟩

end EnvelopeProperty.Vanishing.RelativeArithmeticBaseModel
