import EnvelopeProperty.Vanishing.RelativeArithmeticBaseModel
import EnvelopeProperty.AlgGeom.ArithmeticSmoothProjectiveOriginalFamily

/-! # The prescribed original projective family over a separate arithmetic base

The modeled affine algebra is distinct from its arithmetic coefficient
domain.  The actual original relative projective embedding supplies its
whole ambient model, with no properness over the original field.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticJointModel
open ProjBerk DeJongAlterations.StableModification.Limits

/-- A genuine prescribed coefficient square gives a fixed model in the actual
finite coefficient system.  Both coefficient-corner isomorphisms are canonical. -/
def fixedModel {A k : Type u} [CommRing A] [CommRing k] [Algebra A k]
    {P Q : Scheme.{u}} (a : P ⟶ Q) (f : P ⟶ Spec (.of k))
    (q : Q ⟶ Spec (.of A))
    (H : IsPullback a f q (Spec.map (CommRingCat.ofHom (algebraMap A k))))
    (hi : Function.Injective (algebraMap A k)) :
    Model ((fgDiagram (⊤ : Subalgebra A k)).op ⋙ Scheme.Spec)
      (fgSpecCone (⊤ : Subalgebra A k))
      (f ≫ (ArithmeticFixedSmoothModel.topScalarIso A k).hom)
      (op (⊥ : FGSubalgebra A (⊤ : Subalgebra A k))) where
  Y := Q
  fY := q ≫ (ArithmeticFixedSmoothModel.bottomScalarIso A k hi).hom
  g := a
  isPullback := by
    apply H.of_iso (Iso.refl _) (Iso.refl _)
      (ArithmeticFixedSmoothModel.topScalarIso A k)
      (ArithmeticFixedSmoothModel.bottomScalarIso A k hi)
    · simp
    · simp
    · simp
    · exact (ArithmeticFixedSmoothModel.top_bottom_scalar_triangle A k hi).symm

/-- Finite presentation of the actual coefficient family is sufficient for
the constructed fixed model; no properness over its coefficients is required. -/
theorem fixedModel_isFP {A k : Type u} [CommRing A] [CommRing k] [Algebra A k]
    {P Q : Scheme.{u}} (a : P ⟶ Q) (f : P ⟶ Spec (.of k))
    (q : Q ⟶ Spec (.of A))
    (H : IsPullback a f q (Spec.map (CommRingCat.ofHom (algebraMap A k))))
    (hi : Function.Injective (algebraMap A k))
    [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q] :
    (fixedModel a f q H hi).IsFP :=
  ⟨inferInstanceAs (LocallyOfFinitePresentation
      (q ≫ (ArithmeticFixedSmoothModel.bottomScalarIso A k hi).hom)),
    inferInstanceAs (QuasiCompact
      (q ≫ (ArithmeticFixedSmoothModel.bottomScalarIso A k hi).hom)),
    inferInstanceAs (QuasiSeparated
      (q ≫ (ArithmeticFixedSmoothModel.bottomScalarIso A k hi).hom))⟩

variable {A k B R : Type u} [CommRing A] [Field k] [CommRing B] [CommRing R]
    [Algebra A k] [Algebra A B] [Algebra k R]

/-- Projective space over the SAME original affine base is the actual entire
field fibre of projective space over its separate finite arithmetic model. -/
theorem projectiveAmbient_isPullback (e : k ⊗[A] B ≃ₐ[k] R) (d : ℕ) :
    IsPullback
      (nativeCoefficientMap (n := d) (RelativeArithmeticBaseModel.originalMap e))
      (nativeStructureMap (R := R) (n := d) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (nativeStructureMap (R := B) (n := d) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A k))) :=
  (isPullback_nativeCoefficientBaseChange
    (n := d) (RelativeArithmeticBaseModel.originalMap e)).paste_vert
      (RelativeArithmeticBaseModel.original_isPullback e)

/-- The actual original projective ambient has its constructed fixed model. -/
def projectiveAmbient_fixedModel (e : k ⊗[A] B ≃ₐ[k] R)
    (hi : Function.Injective (algebraMap A k)) (d : ℕ) :=
  fixedModel
    (nativeCoefficientMap (n := d) (RelativeArithmeticBaseModel.originalMap e))
    (nativeStructureMap (R := R) (n := d) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R)))
    (nativeStructureMap (R := B) (n := d) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (projectiveAmbient_isPullback e d) hi

/-- The separate finite arithmetic affine algebra supplies the actual finite
presentation of the ambient model, even when that affine algebra is not a domain. -/
theorem projectiveAmbient_fixedModel_isFP [IsNoetherianRing A]
    [Algebra.FinitePresentation A B] (e : k ⊗[A] B ≃ₐ[k] R)
    (hi : Function.Injective (algebraMap A k)) (d : ℕ) :
    (projectiveAmbient_fixedModel e hi d).IsFP := by
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let : IsProper (nativeStructureMap (R := B) (n := d)) := nativeStructureMap_isProper
  let q := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let : LocallyOfFinitePresentation q := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  exact fixedModel_isFP _ _ _ _ hi

end EnvelopeProperty.Vanishing.RelativeArithmeticJointModel
