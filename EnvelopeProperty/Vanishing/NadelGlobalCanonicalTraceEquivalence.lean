import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceSpectrum
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Actual canonical sections along an original affine algebra equivalence

This is the genuine adjunction unit, followed by the already proved native
canonical differential.  The ring equivalence supplies its own etaleness;
no canonical comparison or desired formula is an input.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
open scoped TensorProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {B C : CommRingCat.{u}}
    (f : Spec B ⟶ Spec (.of k)) (e : B ≃+* C) (n : ℕ)
    [SmoothOfRelativeDimension n f]

/-- Original whole canonical sections, transported along the SAME actual
ring equivalence by its genuine unit and actual canonical differential. -/
def nativeEquivSectionsIso :
    (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f n) ≅
      (ModuleCat.restrictScalars e.toRingHom).obj
        ((moduleSpecΓFunctor (R := C)).obj
          (exteriorCotangentSheaf (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ f) n)) := by
  letI : Etale (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.Etale.of_bijective e.bijective
  letI : (ModuleCat.restrictScalars e.toRingHom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  let M := (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f n)
  exact asIso ((ModuleCat.extendRestrictScalarsAdj e.toRingHom).unit.app M) ≪≫
    (ModuleCat.restrictScalars e.toRingHom).mapIso
      (nativeSectionsIso f (CommRingCat.ofHom e.toRingHom) n)

/-- Every ORIGINAL canonical section is carried by the SAME actual
adjoint canonical differential, rather than an arbitrarily selected iso. -/
theorem nativeEquivSectionsIso_apply
    (w : (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f n)) :
    (nativeEquivSectionsIso f e n).hom w =
      (show (moduleSpecΓFunctor (R := C)).obj
        (exteriorCotangentSheaf (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ f) n) from
        (exteriorCotangentSheafMorphism f (Spec.map (CommRingCat.ofHom e.toRingHom)) n).val.app
          (op ⊤) w) := by
  let : Etale (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.Etale.of_bijective e.bijective
  let : Algebra B C := e.toRingHom.toAlgebra
  change (nativeSectionsIso f (CommRingCat.ofHom e.toRingHom) n).hom ((1 : C) ⊗ₜ[B] w) = _
  simpa only [one_smul] using
    nativeSectionsIso_tmul f (CommRingCat.ofHom e.toRingHom) n (1 : C) w

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
