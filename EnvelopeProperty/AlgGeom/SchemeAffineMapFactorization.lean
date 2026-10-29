import EnvelopeProperty.AlgGeom.SchemeModuleAffineEpimorphisms
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Whole affine module maps from ALL original global sections -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace EnvelopeProperty.SchemeAffineMapFactorization

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry.Scheme.Modules

/-- On an original spectrum, ALL original global sections detect equality
of ENTIRE module maps with quasicoherent source, with arbitrary target. -/
theorem spec_hom_ext {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] (f g : M ⟶ N)
    (h : f.app (⊤ : (Spec R).Opens) = g.app ⊤) : f = g := by
  have htop : moduleSpecΓFunctor.map f = moduleSpecΓFunctor.map g := by
    apply ModuleCat.hom_ext
    ext s
    exact congrArg (fun e => e s) h
  apply (cancel_epi M.fromTildeΓ).mp
  calc
    M.fromTildeΓ ≫ f = tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ :=
      (fromTildeΓNatTrans.naturality f).symm
    _ = tilde.map (moduleSpecΓFunctor.map g) ≫ N.fromTildeΓ := by rw [htop]
    _ = M.fromTildeΓ ≫ g := fromTildeΓNatTrans.naturality g

/-- On ANY original affine scheme, the actual original global-section map
of a quasicoherent source determines the ENTIRE module morphism. -/
theorem hom_ext {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] (f g : M ⟶ N)
    (h : f.app (⊤ : X.Opens) = g.app ⊤) : f = g := by
  let F := restrictFunctor (Scheme.isoSpec X).inv
  let : F.IsEquivalence :=
    inferInstanceAs ((restrictFunctor (Scheme.isoSpec X).symm.hom).IsEquivalence)
  apply F.map_injective
  apply spec_hom_ext
  change f.app ((Scheme.isoSpec X).inv ''ᵁ ⊤) = g.app ((Scheme.isoSpec X).inv ''ᵁ ⊤)
  have he : (Scheme.isoSpec X).inv ''ᵁ ⊤ = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  exact Eq.mpr (congrArg (fun U => f.app U = g.app U) he) h

/-- The ENTIRE original affine morphism factors through an actual mono
exactly when EVERY original global-section image lies in the SAME mono's
actual global-section image. No quasicoherence hypothesis on either target. -/
theorem factorization_iff_appTop_image {X : Scheme.{u}} [IsAffine X]
    {M N I : X.Modules} [M.IsQuasicoherent] (i : I ⟶ N) [Mono i] (f : M ⟶ N) :
    (∃ θ : M ⟶ I, θ ≫ i = f) ↔
      ∀ x : Γ(M, ⊤), ∃ y : Γ(I, ⊤), i.app ⊤ y = f.app ⊤ x := by
  constructor
  · rintro ⟨θ, rfl⟩ x
    exact ⟨θ.app ⊤ x, rfl⟩
  · intro h
    let T := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have he : T.Exact := ShortComplex.exact_cokernel i
    apply he.lift' f
    apply hom_ext
    apply AddCommGrpCat.hom_ext
    ext x
    obtain ⟨y, hy⟩ := h x
    change (cokernel.π i).app ⊤ (f.app ⊤ x) = 0
    rw [← hy]
    exact congrArg (fun e => e.app (⊤ : X.Opens) y) (cokernel.condition i)

end
end EnvelopeProperty.SchemeAffineMapFactorization
