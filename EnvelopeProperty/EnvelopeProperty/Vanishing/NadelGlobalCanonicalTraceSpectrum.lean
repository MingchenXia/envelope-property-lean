import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceBaseChange
import EnvelopeProperty.Vanishing.NadelCanonicalPushoutCore
import EnvelopeProperty.AlgGeom.AffinePullbackStalkTensorReadback

/-! # Original-ring canonical sections on the SAME whole mixed cover

The scalar ring is the original ring B or its literal tensor algebra C,
not an unidentified global-section ring.  The maps retain the SAME native
canonical differential.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
open scoped TensorProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Spectrum
variable {k : Type u} [Field k] {B C : CommRingCat.{u}}
    (f : Spec B ⟶ Spec (.of k)) (φ : B ⟶ C) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Etale (Spec.map φ)]

/-- Basis-free actual canonical base change, with the ORIGINAL B and C
scalar structures of moduleSpecΓFunctor. -/
def nativeSectionsIso :
    letI : (exteriorCotangentSheaf f n).IsQuasicoherent :=
      (canonicalLineSheaf_isInvertible f n).isQuasicoherent
    (ModuleCat.extendScalars φ.hom).obj
      ((moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f n)) ≅
      (moduleSpecΓFunctor (R := C)).obj
        (exteriorCotangentSheaf (Spec.map φ ≫ f) n) := by
  letI : (exteriorCotangentSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  letI : IsIso (exteriorCotangentSheafPullbackMap f (Spec.map φ) n) :=
    NadelBlowupCanonicalEtaleSmooth.etale_isIso f n (Spec.map φ)
  letI : Algebra B C := φ.hom.toAlgebra
  let E : (Spec C).Modules ⥤ ModuleCat C := moduleSpecΓFunctor (R := C)
  exact (AffinePullbackStalkTensorReadback.specPullbackTensorEquiv
      (exteriorCotangentSheaf f n) φ).toModuleIso ≪≫
    E.mapIso (asIso (exteriorCotangentSheafPullbackMap f (Spec.map φ) n))

/-- This whole comparison is the actual affine sections comparison followed
by the SAME actual differential, with no matching premise. -/
theorem nativeSectionsIso_hom :
    letI : (exteriorCotangentSheaf f n).IsQuasicoherent :=
      (canonicalLineSheaf_isInvertible f n).isQuasicoherent
    (nativeSectionsIso f φ n).hom =
      (AffinePullbackStalkTensorReadback.specPullbackTensorEquiv
        (exteriorCotangentSheaf f n) φ).toModuleIso.hom ≫
        (moduleSpecΓFunctor (R := C)).map
          (exteriorCotangentSheafPullbackMap f (Spec.map φ) n) := by
  let : (exteriorCotangentSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  rfl
/-- Every ORIGINAL coefficient tensor retains the SAME actual adjoint
canonical differential on every original section. -/
theorem nativeSectionsIso_tmul (c : C)
    (w : (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f n)) :
    letI : Algebra B C := φ.hom.toAlgebra
    letI : (exteriorCotangentSheaf f n).IsQuasicoherent :=
      (canonicalLineSheaf_isInvertible f n).isQuasicoherent
    (nativeSectionsIso f φ n).hom (c ⊗ₜ[B] w) =
      c • (show (moduleSpecΓFunctor (R := C)).obj
          (exteriorCotangentSheaf (Spec.map φ ≫ f) n) from
        (exteriorCotangentSheafMorphism f (Spec.map φ) n).val.app (op ⊤) w) := by
  let : Algebra B C := φ.hom.toAlgebra
  let : (exteriorCotangentSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  rw [nativeSectionsIso_hom]
  change ((moduleSpecΓFunctor (R := C)).map
      (exteriorCotangentSheafPullbackMap f (Spec.map φ) n))
    (AffinePullbackStalkTensorReadback.specPullbackTensorEquiv
      (exteriorCotangentSheaf f n) φ (c ⊗ₜ[B] w)) = _
  rw [AffinePullbackStalkTensorReadback.specPullbackTensorEquiv_tmul, map_smul]
  congr 1
  have h := sectionsIso_one_tmul f (Spec.map φ) n
    (show Γ(exteriorCotangentSheaf f n, ⊤) from w)
  rw [sectionsIso_hom] at h
  change (exteriorCotangentSheafPullbackMap f (Spec.map φ) n).val.app (op ⊤)
    ((Scheme.Modules.affinePullbackΓIso (Spec.map φ) (exteriorCotangentSheaf f n)).hom
      ((1 : Γ(Spec C, ⊤)) ⊗ₜ[Γ(Spec B, ⊤)]
        (show Γ(exteriorCotangentSheaf f n, ⊤) from w))) = _ at h
  rw [Scheme.Modules.affinePullbackΓIso_hom_one_tmul] at h
  exact h

end Spectrum

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
