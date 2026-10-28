import EnvelopeProperty.AlgGeom.Canonical.AffineCanonicalBasisFrame
import EnvelopeProperty.Char0.FormallyEtaleCanonicalDifferential
import EnvelopeProperty.AlgGeom.SchemeModuleAffineEpimorphisms

/-! # The SAME whole native affine canonical differential under formal etaleness -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace EnvelopeProperty.CanonicalGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalAffineIsIsoFromTop {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    (hφ : Function.Bijective (φ.app (⊤ : X.Opens))) : IsIso φ := by
  let F := Scheme.Modules.restrictFunctor (Scheme.isoSpec X).inv
  let : F.IsEquivalence :=
    inferInstanceAs ((Scheme.Modules.restrictFunctor (Scheme.isoSpec X).symm.hom).IsEquivalence)
  have htop : Function.Bijective ((F.map φ).app (⊤ : (Spec Γ(X, ⊤)).Opens)) := by
    change Function.Bijective (φ.app ((Scheme.isoSpec X).inv ''ᵁ ⊤))
    have he : (Scheme.isoSpec X).inv ''ᵁ ⊤ = ⊤ := by
      rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
    exact Eq.mpr (congrArg (fun U => Function.Bijective (φ.app U)) he) hφ
  have : IsIso (moduleSpecΓFunctor.map (F.map φ)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact htop
  let M' := F.obj M
  let N' := F.obj N
  let : M'.IsQuasicoherent := inferInstanceAs (F.obj M).IsQuasicoherent
  let : N'.IsQuasicoherent := inferInstanceAs (F.obj N).IsQuasicoherent
  let : IsIso M'.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M'
  let : IsIso N'.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N'
  have heq : F.map φ = inv M'.fromTildeΓ ≫
      tilde.map (moduleSpecΓFunctor.map (F.map φ)) ≫ N'.fromTildeΓ := by
    apply (cancel_epi M'.fromTildeΓ).mp
    have hn := (Scheme.Modules.fromTildeΓNatTrans.naturality (F.map φ)).symm
    change M'.fromTildeΓ ≫ F.map φ =
      tilde.map (moduleSpecΓFunctor.map (F.map φ)) ≫ N'.fromTildeΓ at hn
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hn
  let e : F.obj M ≅ F.obj N := (asIso M'.fromTildeΓ).symm ≪≫
    (tilde.functor Γ(X, ⊤)).mapIso
      (asIso (moduleSpecΓFunctor.map (F.map φ))) ≪≫ asIso N'.fromTildeΓ
  have heq' : F.map φ = e.hom := heq
  have : IsIso (F.map φ) := by rw [heq']; infer_instance
  exact isIso_of_reflects_iso φ F

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ) [SmoothOfRelativeDimension n f]

/-- Actual formal etaleness of the SAME original whole section-ring map derives an
ENTIRE native canonical differential isomorphism, without target smoothness/finite presentation. -/
theorem exteriorCotangentSheafPullbackMap_isIso_of_formallyEtale
    (bX : let := affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(X, ⊤) (KaehlerDifferential k Γ(X, ⊤)))
    (he : g.appTop.hom.FormallyEtale) :
    IsIso (exteriorCotangentSheafPullbackMap f g n) := by
  let := affineChartAlgebra f ⊤
  let := affineChartAlgebra (g ≫ f) ⊤
  let := affineChartAlgebra (g ≫ f) (g ⁻¹ᵁ ⊤)
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ(Y, g ⁻¹ᵁ ⊤) := (g.app ⊤).hom.toAlgebra
  let : IsScalarTower k Γ(X, ⊤) Γ(Y, g ⁻¹ᵁ ⊤) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((schemeMorphismSectionAlgebraHom f g ⊤).commutes a).symm
  let : Algebra.FormallyEtale Γ(X, ⊤) Γ(Y, g ⁻¹ᵁ ⊤) := he
  let : IsScalarTower k Γ(X, ⊤) Γ(Y, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((schemeMorphismSectionAlgebraHom f g ⊤).commutes a).symm
  let : Algebra.FormallyEtale Γ(X, ⊤) Γ(Y, ⊤) := he
  let bY := Char0.differentialBasisBaseChange (A := Γ(Y, ⊤)) bX
  let hY := affineCanonical_isInvertible_of_basis (g ≫ f) n bY
  let : (exteriorCotangentSheaf (g ≫ f) n).IsQuasicoherent := hY.isQuasicoherent
  let : (exteriorCotangentSheaf f n).IsQuasicoherent := (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  let : ((Scheme.Modules.pullback g).obj (exteriorCotangentSheaf f n)).IsQuasicoherent :=
    ((canonicalLineSheaf_isInvertible f n).pullback g).isQuasicoherent
  let uX := (exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤)
  let uY := (exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op ⊤)
  have hX : Function.Bijective uX :=
    affineChartExteriorSheafificationMap_bijective f (isAffineOpen_top X) bX n
  have hY' : Function.Bijective uY :=
    affineChartExteriorSheafificationMap_bijective (g ≫ f) (isAffineOpen_top Y) bY n
  let : IsIso uX := (ConcreteCategory.isIso_iff_bijective uX).mpr hX
  let : IsIso uY := (ConcreteCategory.isIso_iff_bijective uY).mpr hY'
  have hraw : Function.Bijective (exteriorCotangentRawBaseChangeMorphism f g n) := by
    change Function.Bijective (exteriorCotangentMorphismBaseChange f g ⊤ n)
    rw [exteriorCotangentMorphismBaseChange_eq_affineCanonicalDifferentialMap]
    exact Char0.affineCanonicalDifferentialMap_bijective_of_formallyEtale bX n
  let : IsIso (exteriorCotangentRawBaseChangeMorphism f g n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hraw
  let pref := (ModuleCat.extendScalars g.appTop.hom).map uX ≫
    (Scheme.Modules.affinePullbackΓIso g (exteriorCotangentSheaf f n)).hom
  let : IsIso pref := inferInstance
  have hcomm : pref ≫ (exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤) =
      exteriorCotangentRawBaseChangeMorphism f g n ≫ uY :=
    by simpa only [pref, uX, uY, Category.assoc] using nativeAffineCanonicalDifferential_unit f g n
  let : IsIso (pref ≫ (exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤)) := by
    rw [hcomm]
    infer_instance
  let : IsIso ((exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤)) := by
    have hd : (exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤) =
        inv pref ≫ (pref ≫ (exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤)) := by
      simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    rw [hd]
    infer_instance
  apply originalAffineIsIsoFromTop (exteriorCotangentSheafPullbackMap f g n)
  exact ConcreteCategory.bijective_of_isIso
    ((exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤))

end EnvelopeProperty.CanonicalGeometry
