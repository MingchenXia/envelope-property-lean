import EnvelopeProperty.AlgGeom.ArithmeticSmoothAffineModel
import DeJongAlterations.StableModification.Limits.SpreadProperty
import DeJongAlterations.StableModification.Limits.SpreadAffine

/-!
# Genuine smoothness spreading for the same fixed arithmetic model

The exact native fixed-model property descent is supplied with its affine
smooth-model input internally, from the actual original smooth morphism.
The fixed affine presentation consumers use the actual spectrum/tensor
pullback, preserving the same original model and whole generic map.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct Classical

namespace EnvelopeProperty.ArithmeticFixedSmoothModel

open DeJongAlterations.StableModification.Limits

universe u

/-- Original generic smoothness internally supplies all affine-model inputs needed to make
the SAME fixed finite-presentation model smooth after an actual later coefficient base change. -/
theorem exists_smooth_fixed_model_baseChange
    {A L : Type u} [CommRing A] [CommRing L] [Algebra A L] {R : Subalgebra A L}
    {X : Scheme.{u}} {f : X ⟶ (fgSpecCone R).pt}
    {i : (FGSubalgebra A R)ᵒᵖ}
    (m : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) f i)
    (hm : m.IsFP) [Smooth f] :
    ∃ (j : (FGSubalgebra A R)ᵒᵖ) (h : j ⟶ i), Smooth (m.baseChange h).fY := by
  let : HasRingHomProperty (@AlgebraicGeometry.Smooth.{u}) RingHom.Smooth := inferInstance
  let : IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  apply Spread.exists_baseChange_of_forall_isAffineOpen
    (@AlgebraicGeometry.Smooth.{u}) m (isLimitFGSpecCone R) hm
  intro W hW
  let : IsAffine W := hW
  let : Smooth (W.ι ≫ f) := inferInstance
  obtain ⟨B, M, hM, hs⟩ :=
    Spread.exists_smooth_model_of_isAffine (A := A) (L := L) (R := R) (W.ι ≫ f)
  exact ⟨op B, M, hM, hs⟩

/-- The actual ambient algebra is the coefficient system's top corner. -/
def topScalarIso (A L : Type u) [CommRing A] [CommRing L] [Algebra A L] :
    Spec (.of L) ≅ (fgSpecCone (⊤ : Subalgebra A L)).pt :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (Subalgebra.topEquiv (R := A) (A := L)).toRingEquiv).op

/-- Every whole original coefficient-stage projection is retained under the actual top isomorphism. -/
theorem topScalarIso_hom_stage (A L : Type u) [CommRing A] [CommRing L] [Algebra A L]
    (B : FGSubalgebra A (⊤ : Subalgebra A L)) :
    (topScalarIso A L).hom ≫ (fgSpecCone (⊤ : Subalgebra A L)).π.app (op B) =
      Spec.map (CommRingCat.ofHom (algebraMap B.1 L)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1

/-- The actual original injective base is the coefficient system's bottom corner. -/
def bottomScalarIso (A L : Type u) [CommRing A] [CommRing L] [Algebra A L]
    (hinj : Function.Injective (algebraMap A L)) :
    Spec (.of A) ≅ ((fgDiagram (⊤ : Subalgebra A L)).op ⋙ Scheme.Spec).obj
      (op (⊥ : FGSubalgebra A (⊤ : Subalgebra A L))) :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (Algebra.botEquivOfInjective hinj).toRingEquiv).op

private theorem bottomEquiv_map (A L : Type u) [CommRing A] [CommRing L] [Algebra A L]
    (hinj : Function.Injective (algebraMap A L)) (x : (⊥ : Subalgebra A L)) :
    algebraMap A L (Algebra.botEquivOfInjective hinj x) = (x : L) := by
  have h := congrArg Subtype.val ((Algebra.botEquivOfInjective hinj).symm_apply_apply x)
  exact h

/-- The whole original base-to-stage map is the actual bottom-stage transition. -/
theorem bottomScalarIso_hom_stage (A L : Type u) [CommRing A] [CommRing L] [Algebra A L]
    (hinj : Function.Injective (algebraMap A L))
    (B : FGSubalgebra A (⊤ : Subalgebra A L)) :
    Spec.map (CommRingCat.ofHom (algebraMap A B.1)) ≫ (bottomScalarIso A L hinj).hom =
      ((fgDiagram (⊤ : Subalgebra A L)).op ⋙ Scheme.Spec).map
        (homOfLE (bot_le : (⊥ : FGSubalgebra A (⊤ : Subalgebra A L)) ≤ B)).op := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact bottomEquiv_map A L hinj x

/-- The entire original base/ambient-field triangle agrees with the native coefficient cone. -/
theorem top_bottom_scalar_triangle (A L : Type u) [CommRing A] [CommRing L] [Algebra A L]
    (hinj : Function.Injective (algebraMap A L)) :
    (topScalarIso A L).hom ≫ (fgSpecCone (⊤ : Subalgebra A L)).π.app
        (op (⊥ : FGSubalgebra A (⊤ : Subalgebra A L))) =
      Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ (bottomScalarIso A L hinj).hom := by
  rw [topScalarIso_hom_stage]
  change Spec.map (CommRingCat.ofHom (algebraMap (⊥ : Subalgebra A L) L)) =
    Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫
      Spec.map (CommRingCat.ofHom (Algebra.botEquivOfInjective hinj).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (bottomEquiv_map A L hinj x).symm

end EnvelopeProperty.ArithmeticFixedSmoothModel
