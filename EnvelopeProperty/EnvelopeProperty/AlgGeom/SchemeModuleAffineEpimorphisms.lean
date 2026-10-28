import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

/-! # Genuine epimorphisms from original affine global sections -/
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeModuleAffineEpimorphisms
open AlgebraicGeometry.Scheme.Modules

/-- Surjectivity on original affine-spectrum global sections proves an ACTUAL
module epimorphism when its actual target is quasicoherent. -/
theorem spec_epi_of_appTop_surjective {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [N.IsQuasicoherent] (f : M ⟶ N)
    (hf : Function.Surjective (f.app (⊤ : (Spec R).Opens))) : Epi f := by
  constructor
  intro Q g h hfg
  have htop : moduleSpecΓFunctor.map g = moduleSpecΓFunctor.map h := by
    apply ModuleCat.hom_ext
    ext s
    obtain ⟨t, rfl⟩ := hf s
    exact congrArg (fun q => q.app (⊤ : (Spec R).Opens) t) hfg
  apply (cancel_epi N.fromTildeΓ).mp
  calc
    N.fromTildeΓ ≫ g = tilde.map (moduleSpecΓFunctor.map g) ≫ Q.fromTildeΓ :=
      (Scheme.Modules.fromTildeΓNatTrans.naturality g).symm
    _ = tilde.map (moduleSpecΓFunctor.map h) ≫ Q.fromTildeΓ := by rw [htop]
    _ = N.fromTildeΓ ≫ h := Scheme.Modules.fromTildeΓNatTrans.naturality h

/-- The same actual result on ANY original affine scheme, using its genuine
canonical spectrum isomorphism and SAME original global-section maps. -/
theorem epi_of_appTop_surjective {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} [N.IsQuasicoherent] (f : M ⟶ N)
    (hf : Function.Surjective (f.app (⊤ : X.Opens))) : Epi f := by
  let F := restrictFunctor (Scheme.isoSpec X).inv
  let : F.IsEquivalence :=
    inferInstanceAs ((restrictFunctor (Scheme.isoSpec X).symm.hom).IsEquivalence)
  have htop : Function.Surjective ((F.map f).app (⊤ : (Spec Γ(X, ⊤)).Opens)) := by
    change Function.Surjective (f.app ((Scheme.isoSpec X).inv ''ᵁ ⊤))
    have he : (Scheme.isoSpec X).inv ''ᵁ ⊤ = ⊤ := by
      rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
    exact Eq.mpr (congrArg (fun U => Function.Surjective (f.app U)) he) hf
  have he : Epi (F.map f) := spec_epi_of_appTop_surjective (F.map f) htop
  constructor
  intro Q g h hfg
  apply F.map_injective
  apply he.left_cancellation
  exact (F.map_comp f g).symm.trans ((congrArg F.map hfg).trans (F.map_comp f h))

end EnvelopeProperty.SchemeModuleAffineEpimorphisms
