import EnvelopeProperty.Vanishing.AmpleScalarBaseChange
import EnvelopeProperty.Vanishing.ArithmeticOriginalLineDescent

/-! # Genuine arithmetic coefficient transitions preserve relative ampleness

The new relative affine base is the actual tensor algebra, while the
original field square and original line are retained on the whole source.
No flatness or domain hypothesis on the original relative affine base is used.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticScalarTransition
open Alterations.StableModification.Limits
attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A D S : Type u} [CommRing A] [CommRing D] [CommRing S]
    [Algebra A D] [Algebra A S] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of A)) (g : Y ⟶ Spec (.of D))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap A D)) = f)

private theorem affine_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap D (S ⊗[A] D))))
      (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[A] D))))
      (Spec.map (CommRingCat.ofHom (algebraMap A D)))
      (Spec.map (CommRingCat.ofHom (algebraMap A S))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A S D)).flip

/-- The actual relative affine-base map after extending arithmetic coefficients. -/
def relativeMap : pullback f (Spec.map (CommRingCat.ofHom (algebraMap A S))) ⟶
    Spec (.of (S ⊗[A] D)) :=
  pullback.lift (pullback.fst _ _ ≫ g) (pullback.snd _ _)
    (by rw [Category.assoc, hg]; exact pullback.condition) ≫
      (affine_isPullback (A := A) (D := D) (S := S)).isoPullback.inv

theorem relativeMap_oldBase :
    relativeMap (S := S) f g hg ≫
      Spec.map (CommRingCat.ofHom (algebraMap D (S ⊗[A] D))) =
        pullback.fst _ _ ≫ g := by
  rw [relativeMap, Category.assoc, IsPullback.isoPullback_inv_fst, pullback.lift_fst]

theorem relativeMap_coefficient :
    relativeMap (S := S) f g hg ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[A] D))) = pullback.snd _ _ := by
  rw [relativeMap, Category.assoc, IsPullback.isoPullback_inv_snd, pullback.lift_snd]

/-- The coefficient-extended relative map is the actual base change of the
original projective affine-base morphism. -/
theorem relative_isPullback :
    IsPullback (pullback.fst _ _) (relativeMap (S := S) f g hg) g
      (Spec.map (CommRingCat.ofHom (algebraMap D (S ⊗[A] D)))) := by
  apply IsPullback.of_bot
    (v₂₁ := Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[A] D))))
    (v₂₂ := Spec.map (CommRingCat.ofHom (algebraMap A D))) ?_
    (relativeMap_oldBase (S := S) f g hg).symm
    (affine_isPullback (A := A) (D := D) (S := S))
  rw [relativeMap_coefficient, hg]
  exact IsPullback.of_hasPullback _ _

/-- The same relative very ample line survives every arithmetic coefficient extension. -/
theorem isVeryAmple (L : Y.Modules) (hL : SchemeLineAmpleness.IsVeryAmple g L) :
    SchemeLineAmpleness.IsVeryAmple (relativeMap (S := S) f g hg)
      ((Scheme.Modules.pullback (pullback.fst _ _)).obj L) :=
  AmpleScalarBaseChange.isVeryAmple_of_isPullback (pullback.fst _ _) g
    (relativeMap (S := S) f g hg) (algebraMap D (S ⊗[A] D))
    (relative_isPullback (S := S) f g hg) L hL

/-- The original positive tensor power witnesses ampleness after arbitrary
arithmetic scalar extension over the separate tensor affine algebra. -/
theorem isAmple (L : Y.Modules) (hL : SchemeLineAmpleness.IsAmple g L) :
    SchemeLineAmpleness.IsAmple (relativeMap (S := S) f g hg)
      ((Scheme.Modules.pullback (pullback.fst _ _)).obj L) :=
  AmpleScalarBaseChange.isAmple_of_isPullback (pullback.fst _ _) g
    (relativeMap (S := S) f g hg) (algebraMap D (S ⊗[A] D))
    (relative_isPullback (S := S) f g hg) L hL

section OriginalField
variable {k : Type u} [Field k] [Algebra A k]
    {X : Scheme.{u}} (a : X ⟶ Y) (p : X ⟶ Spec (.of k))
    (H : IsPullback a p f (Spec.map (CommRingCat.ofHom (algebraMap A k))))
    (C : FGSubalgebra A (⊤ : Subalgebra A k))

/-- The canonical original map into a later coefficient model is cartesian
with the original field map, without properness over the coefficient ring. -/
theorem original_isPullback :
    IsPullback (ArithmeticOriginalLineDescent.originalBaseChangeMap a p f H C) p
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A C.1))))
      (Spec.map (CommRingCat.ofHom (algebraMap C.1 k))) := by
  have ho : IsPullback
      (ArithmeticOriginalLineDescent.originalBaseChangeMap a p f H C ≫ pullback.fst _ _) p f
      (Spec.map (CommRingCat.ofHom (algebraMap C.1 k)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A C.1))) := by
    rw [ArithmeticOriginalLineDescent.originalBaseChangeMap, pullback.lift_fst,
      ← Spec.map_comp]
    exact H
  exact ho.of_right
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)

/-- Every original whole module pullback is retained through the actual
later coefficient transition. -/
def originalPullbackIso (M : Y.Modules) :
    (Scheme.Modules.pullback
      (ArithmeticOriginalLineDescent.originalBaseChangeMap a p f H C)).obj
      ((Scheme.Modules.pullback (pullback.fst _ _)).obj M) ≅
        (Scheme.Modules.pullback a).obj M :=
  (Scheme.Modules.pullbackComp
    (ArithmeticOriginalLineDescent.originalBaseChangeMap a p f H C) (pullback.fst _ _)).app M ≪≫
      (Scheme.Modules.pullbackCongr (pullback.lift_fst _ _ _)).app M

end OriginalField
end EnvelopeProperty.Vanishing.RelativeArithmeticScalarTransition
