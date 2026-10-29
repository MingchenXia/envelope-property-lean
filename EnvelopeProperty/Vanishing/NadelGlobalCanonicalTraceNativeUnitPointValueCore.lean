import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceUnitReadbackCore

/-! # The original native unit value in its target module

Keep the target module abstract and express the value by its original
C-linear map. No restriction-of-scalars map is reconstructed at the value.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
open scoped TensorProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem nativeUnit_postcompose_point
    {K : Type u} [Field K] {B C : CommRingCat.{u}}
    (f : Spec B ⟶ Spec (.of K)) (φ : B ⟶ C) (d : ℕ)
    [SmoothOfRelativeDimension d f] [Etale (Spec.map φ)]
    (Q : ModuleCat C)
    (T : (moduleSpecΓFunctor (R := C)).obj
      (exteriorCotangentSheaf (Spec.map φ ≫ f) d) ⟶ Q)
    (w : (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f d)) :
    ((nativeSectionsIso (B := B) (C := C) f φ d).hom ≫ T)
      (((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app
        ((moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f d))) w) =
      T (nativeCanonicalPullbackMap (B := B) (C := C) f φ d w) := by
  let : Algebra B C := φ.hom.toAlgebra
  let : (exteriorCotangentSheaf f d).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f d).isQuasicoherent
  let δw : (moduleSpecΓFunctor (R := C)).obj
      (exteriorCotangentSheaf (Spec.map φ ≫ f) d) :=
    (exteriorCotangentSheafMorphism f (Spec.map φ) d).val.app (op ⊤) w
  have hs := nativeSectionsIso_tmul (B := B) (C := C) f φ d (1 : C) w
  have h₁ := hs.trans (one_smul C δw)
  have h₂ := (nativeCanonicalPullbackMap_apply (B := B) (C := C) f φ d w).symm
  have hn := h₁.trans h₂
  change T ((nativeSectionsIso (B := B) (C := C) f φ d).hom
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app
      ((moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f d))) w)) = _
  exact congrArg T.hom.toFun hn

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
