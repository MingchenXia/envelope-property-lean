import EnvelopeProperty.Char0.AffineFieldEtaleCoordinates
import EnvelopeProperty.AlgGeom.FlatModuleGlobalSections

/-!
# The actual changed model in an actual equivalent coefficient algebra

The target algebra is genuine data, for example a literal subalgebra of
its own fraction field. Every original coefficient and both categorical
model projections are derived from the actual algebra equivalence.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0.FieldTensorModelEquivalence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {k L : Type u} [CommRing k] [CommRing L] [Algebra k L]
  {A D : CommRingCat.{u}} [Algebra k A] [Algebra k D] [Algebra L D]
  [IsScalarTower k L D]

/-- The SAME original coefficient action in the actual target algebra. -/
def coefficientMap (e : (L ⊗[k] A) ≃ₐ[L] D) : A →ₐ[k] D :=
  (e.toAlgHom.restrictScalars k).comp Algebra.TensorProduct.includeRight

/-- EVERY original coefficient has the literal actual target readback. -/
theorem coefficientMap_apply (e : (L ⊗[k] A) ≃ₐ[L] D) (a : A) :
    coefficientMap e a = e (1 ⊗ₜ[k] a) := rfl

private def baseIso (e : (L ⊗[k] A) ≃ₐ[L] D) :
    Spec (.of (L ⊗[k] A)) ≅ Spec D :=
  Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op

private theorem baseIso_comp (e : (L ⊗[k] A) ≃ₐ[L] D) :
    (baseIso e).hom ≫ Spec.map (CommRingCat.ofHom (coefficientMap e).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := A)).toRingHom) := by
  change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact e.symm_apply_apply (1 ⊗ₜ[k] a)

/-- The actual coefficient-equivalent target retains the SAME genuine change-of-fields square. -/
theorem isPullback_coefficients (e : (L ⊗[k] A) ≃ₐ[L] D) :
    IsPullback (Spec.map (CommRingCat.ofHom (coefficientMap e).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap L D)))
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  apply (isPullback_fieldTensor (k := k) (L := L) (A := A)).of_iso'
    (baseIso e).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    exact (Iso.inv_comp_eq (baseIso e)).mpr (baseIso_comp e).symm
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ _ = _
    rw [← Spec.map_comp]
    congr 1
    ext l
    exact e.commutes l
  · simp
  · simp

variable {Y : Scheme.{u}} (g : Y ⟶ Spec A)

/-- The ACTUAL tensor-model pullback is the ACTUAL pullback to the actual coefficient-equivalent target. -/
def modelIso (e : (L ⊗[k] A) ≃ₐ[L] D) :
    FlatGlobalSections.baseChange (S := L ⊗[k] A) g ≅
      pullback g (Spec.map (CommRingCat.ofHom (coefficientMap e).toRingHom)) :=
  asIso (pullback.map _ _ _ _ (𝟙 _) (baseIso e).hom (𝟙 _)
    (by simp) (by simpa only [Category.comp_id] using (baseIso_comp e).symm))

/-- The SAME original-model projection is retained in the actual target. -/
theorem modelIso_fst (e : (L ⊗[k] A) ≃ₐ[L] D) :
    (modelIso g e).hom ≫ pullback.fst _ _ =
      FlatGlobalSections.firstProjection (S := L ⊗[k] A) g := by
  simp only [modelIso, asIso_hom, pullback.lift_fst, Category.comp_id]

/-- ALL target coefficients act through the actual inverse-equivalence spectrum map. -/
theorem modelIso_snd (e : (L ⊗[k] A) ≃ₐ[L] D) :
    (modelIso g e).hom ≫ pullback.snd _ _ =
      FlatGlobalSections.structureMap (S := L ⊗[k] A) g ≫
        Spec.map (CommRingCat.ofHom e.symm.toRingHom) := by
  simp only [modelIso, asIso_hom, pullback.lift_snd]
  rfl

end EnvelopeProperty.Char0.FieldTensorModelEquivalence
