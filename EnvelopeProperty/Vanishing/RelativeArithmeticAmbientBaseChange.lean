import EnvelopeProperty.Vanishing.AmpleScalarBaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # A projective ambient family over a separate arithmetic affine algebra

The actual arithmetic scalar extension of projective space over B is
projective over the actual tensor algebra C tensor B.  Neither B nor its
tensor extension is assumed to be a domain or flat over the coefficients.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticAmbientBaseChange
open ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (d : ℕ)

/-- The separate modeled affine algebra after arithmetic coefficient extension. -/
abbrev baseAlgebra := C ⊗[A] B

/-- The original arithmetic scalar extension of the whole projective ambient. -/
abbrev ambient : Scheme.{u} :=
  pullback (nativeStructureMap (R := B) (n := d) ≫
    Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (Spec.map (CommRingCat.ofHom (algebraMap A C)))

private theorem affine_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[A] B))))
      (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B))))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A C))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A C B)).flip

/-- The actual relative affine-base map on the coefficient-extended ambient. -/
def relativeMap : ambient (A := A) (B := B) (C := C) d ⟶ Spec (.of (C ⊗[A] B)) :=
  pullback.lift (pullback.fst _ _ ≫ nativeStructureMap) (pullback.snd _ _)
    (by rw [Category.assoc]; exact pullback.condition) ≫
      (affine_isPullback (A := A) (B := B) (C := C)).isoPullback.inv

/-- The relative map retains the original projection to the old affine algebra. -/
theorem relativeMap_oldBase :
    relativeMap (A := A) (B := B) (C := C) d ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[A] B))) =
        pullback.fst _ _ ≫ nativeStructureMap := by
  rw [relativeMap, Category.assoc,
    IsPullback.isoPullback_inv_fst, pullback.lift_fst]

/-- Its arithmetic coefficient map is exactly the original second projection. -/
theorem relativeMap_coefficient :
    relativeMap (A := A) (B := B) (C := C) d ≫
      Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B))) =
        pullback.snd _ _ := by
  rw [relativeMap, Category.assoc,
    IsPullback.isoPullback_inv_snd, pullback.lift_snd]

/-- The same arithmetic ambient is the actual relative projective base change. -/
theorem relative_isPullback :
    IsPullback (pullback.fst _ _)
      (relativeMap (A := A) (B := B) (C := C) d)
      (nativeStructureMap (R := B) (n := d))
      (Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[A] B)))) := by
  apply IsPullback.of_bot
    (v₂₁ := Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B))))
    (v₂₂ := Spec.map (CommRingCat.ofHom (algebraMap A B))) ?_
    (relativeMap_oldBase (A := A) (B := B) (C := C) d).symm
    (affine_isPullback (A := A) (B := B) (C := C))
  rw [relativeMap_coefficient]
  exact IsPullback.of_hasPullback _ _

/-- The actual pulled-back original O(1) is very ample over the separate
modeled affine algebra, by its genuine projective base-change embedding. -/
theorem twist_isVeryAmple :
    SchemeLineAmpleness.IsVeryAmple
      (relativeMap (A := A) (B := B) (C := C) d)
      ((Scheme.Modules.pullback (pullback.fst _ _)).obj
        (coordinateHyperplaneTwist (R := B) (0 : Fin (d + 1)) 1)) := by
  let idP : NativeProjectiveScheme B d ⟶ NativeProjectiveScheme B d := 𝟙 _
  have hidP : IsClosedImmersion idP := by
    dsimp only [idP]
    infer_instance
  have h : SchemeLineAmpleness.IsVeryAmple (nativeStructureMap (R := B) (n := d))
      (coordinateHyperplaneTwist (R := B) (0 : Fin (d + 1)) 1) :=
    ⟨d, idP, hidP, Category.id_comp _, ⟨(Scheme.Modules.pullbackId _).app _⟩⟩
  exact AmpleScalarBaseChange.isVeryAmple_of_isPullback (pullback.fst _ _)
    nativeStructureMap (relativeMap (A := A) (B := B) (C := C) d)
    (algebraMap B (C ⊗[A] B))
    (relative_isPullback (A := A) (B := B) (C := C) d) _ h

end EnvelopeProperty.Vanishing.RelativeArithmeticAmbientBaseChange
