/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.FlatGlobalSections
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Original affine global-section base change without flatness -/
open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped TensorProduct
noncomputable section
namespace EnvelopeProperty.AffineGlobalSections
open FlatGlobalSections
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsAffine X]

/-- BOTH original coefficient projections form a genuine section pushout for ANY affine base change, without flatness. -/
theorem originalSectionSquare :
    IsPushout (CommRingCat.ofHom (ProperBirationalSections.coefficientMap f))
      (CommRingCat.ofHom (algebraMap R S)) (firstProjection (S := S) f).appTop
      (CommRingCat.ofHom (ProperBirationalSections.coefficientMap (structureMap (S := S) f))) := by
  have hp := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  apply hp.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of S)) (Iso.refl _)
  · simp [ProperBirationalSections.coefficientMap]
  · exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R S))
  · simp
  · simp [ProperBirationalSections.coefficientMap]

/-- The actual original affine global-section tensor equivalence requires NO flatness certificate. -/
def tensorEquiv :
    let : Algebra R Γ(X,⊤) := sectionsAlgebra f
    let : Algebra S Γ(baseChange (S := S) f,⊤) := sectionsAlgebra (structureMap (S := S) f)
    S ⊗[R] Γ(X,⊤) ≃ₐ[S] Γ(baseChange (S := S) f,⊤) := by
  let : Algebra R Γ(X,⊤) := sectionsAlgebra f
  let : Algebra S Γ(baseChange (S := S) f,⊤) := sectionsAlgebra (structureMap (S := S) f)
  let e₀ : CommRingCat.of (S ⊗[R] Γ(X,⊤)) ≅ Γ(baseChange (S := S) f,⊤) :=
    (CommRingCat.isPushout_tensorProduct R S Γ(X,⊤)).isoPushout ≪≫
      (originalSectionSquare (S := S) f).flip.isoPushout.symm
  refine { toRingEquiv := e₀.commRingCatIsoToRingEquiv, commutes' := ?_ }
  intro s
  change ((CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
    ((CommRingCat.isPushout_tensorProduct R S Γ(X,⊤)).isoPushout ≪≫
      (originalSectionSquare (S := S) f).flip.isoPushout.symm).hom) s=_
  simp only [Iso.trans_hom,Iso.symm_hom,IsPushout.inl_isoPushout_hom_assoc,
    IsPushout.inl_isoPushout_inv]
  rfl

/-- EVERY original scalar is the actual second-projection coefficient. -/
theorem tensorEquiv_includeLeft (s : S) :
    let : Algebra R Γ(X,⊤) := sectionsAlgebra f
    tensorEquiv (S := S) f (Algebra.TensorProduct.includeLeftRingHom s)=
      ProperBirationalSections.coefficientMap (structureMap (S := S) f) s := by
  let : Algebra R Γ(X,⊤) := sectionsAlgebra f
  let : Algebra S Γ(baseChange (S := S) f,⊤) := sectionsAlgebra (structureMap (S := S) f)
  exact (tensorEquiv (S := S) f).commutes s

/-- EVERY original global section is retained by the actual first projection. -/
theorem tensorEquiv_includeRight (b : Γ(X,⊤)) :
    let : Algebra R Γ(X,⊤) := sectionsAlgebra f
    tensorEquiv (S := S) f (Algebra.TensorProduct.includeRight b)=
      (firstProjection (S := S) f).appTop b := by
  let : Algebra R Γ(X,⊤) := sectionsAlgebra f
  change ((CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
    ((CommRingCat.isPushout_tensorProduct R S Γ(X,⊤)).isoPushout ≪≫
      (originalSectionSquare (S := S) f).flip.isoPushout.symm).hom) b=_
  simp only [Iso.trans_hom,Iso.symm_hom,IsPushout.inr_isoPushout_hom_assoc,
    IsPushout.inr_isoPushout_inv]

/-- The WHOLE pure-tensor formula retains BOTH original projection maps. -/
theorem tensorEquiv_tmul (s : S) (b : Γ(X,⊤)) :
    let : Algebra R Γ(X,⊤) := sectionsAlgebra f
    tensorEquiv (S := S) f (s ⊗ₜ[R] b)=
      ProperBirationalSections.coefficientMap (structureMap (S := S) f) s *
        (firstProjection (S := S) f).appTop b := by
  let : Algebra R Γ(X,⊤) := sectionsAlgebra f
  rw [show s ⊗ₜ[R] b=Algebra.TensorProduct.includeLeftRingHom s *
    Algebra.TensorProduct.includeRight b by simp,map_mul,tensorEquiv_includeLeft,tensorEquiv_includeRight]

end EnvelopeProperty.AffineGlobalSections
