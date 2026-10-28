import EnvelopeProperty.AlgGeom.Canonical.NativeAffineCanonicalMap
import EnvelopeProperty.AlgGeom.SchemeModuleGlobalSections
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # The actual whole canonical frame derived from original affine differentials -/

open CategoryTheory AlgebraicGeometry Opposite

namespace EnvelopeProperty.CanonicalGeometry

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem affineIsIsoOfAppTopBijective {X : Scheme.{u}} [IsAffine X]
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
    (tilde.functor Γ(X, ⊤)).mapIso (asIso (moduleSpecΓFunctor.map (F.map φ))) ≪≫
      asIso N'.fromTildeΓ
  have heq' : F.map φ = e.hom := heq
  have : IsIso (F.map φ) := by rw [heq']; infer_instance
  exact isIso_of_reflects_iso φ F

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]

/-- The actual original global canonical generator, obtained from the SAME
original top differential wedge by the SAME sheafification unit. -/
def affineCanonicalFrameSection
    (b : letI := affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(X, ⊤) (KaehlerDifferential k Γ(X, ⊤))) :
    Γ(canonicalLineSheaf f n, ⊤) :=
  letI := affineChartAlgebra f ⊤
  (exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤)
    (affineCanonicalGenerator (K := k) b)

omit [IsAffine X] [SmoothOfRelativeDimension n f] in
private theorem affineCanonicalFrameSection_smul
    (b : letI := affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(X, ⊤) (KaehlerDifferential k Γ(X, ⊤)))
    (z : letI := affineChartAlgebra f ⊤
      affineCanonicalModule k Γ(X, ⊤) n) :
    letI := affineChartAlgebra f ⊤
    (exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z =
      affineCanonicalTrivialization b z • affineCanonicalFrameSection f n b := by
  let := affineChartAlgebra f ⊤
  exact (congrArg ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤))
    (affineCanonical_eq_smul_generator b z)).trans
      (by
        change (exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤)
          (affineCanonicalTrivialization b z • affineCanonicalGenerator (K := k) b) = _
        exact ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤)).hom.map_smul _ _)

/-- The actual original differential basis DERIVES an entire original
canonical sheaf frame, rather than supplying a line-frame premise. -/
def affineCanonicalFrameIso
    (b : letI := affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(X, ⊤) (KaehlerDifferential k Γ(X, ⊤))) :
    canonicalLineSheaf f n ≅ Scheme.Modules.unitObj X := by
  letI := affineChartAlgebra f ⊤
  let M := canonicalLineSheaf f n
  let : (Scheme.Modules.unitObj X).IsQuasicoherent := Scheme.Modules.isInvertible_unit.isQuasicoherent
  let : M.IsQuasicoherent := (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  let s := affineCanonicalFrameSection f n b
  let σ := SchemeModuleGlobalSections.sectionHom M s
  have hσ (a : Γ(X, ⊤)) : σ.app ⊤ a = a • s := by
    change a • M.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op s = _
    simp
  have hu := affineChartExteriorSheafificationMap_bijective f (isAffineOpen_top X) b n
  let e : affineCanonicalModule k Γ(X, ⊤) n ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) :=
    LinearEquiv.ofBijective ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤)).hom hu
  have hσe : (fun a : Γ(X, ⊤) => σ.app ⊤ a) =
      fun a => e ((affineCanonicalTrivialization b).symm a) := by
    funext a
    rw [hσ]
    change a • s = (exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤)
      ((affineCanonicalTrivialization b).symm a)
    rw [affineCanonicalFrameSection_smul, LinearEquiv.apply_symm_apply]
  have hb : Function.Bijective (σ.app (⊤ : X.Opens)) := by
    change Function.Bijective (fun a : Γ(X, ⊤) => σ.app ⊤ a)
    rw [show (fun a : Γ(X, ⊤) => σ.app ⊤ a) =
      (fun a : Γ(X, ⊤) => e ((affineCanonicalTrivialization b).symm a)) from hσe]
    exact e.bijective.comp (affineCanonicalTrivialization b).symm.bijective
  let : IsIso σ := affineIsIsoOfAppTopBijective σ hb
  exact (asIso σ).symm

/-- The SAME derived whole canonical frame sends EVERY original top form
through the SAME sheafification unit to its EXACT original wedge coefficient. -/
theorem affineCanonicalFrameIso_hom_unit
    (b : letI := affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(X, ⊤) (KaehlerDifferential k Γ(X, ⊤)))
    (z : letI := affineChartAlgebra f ⊤
      affineCanonicalModule k Γ(X, ⊤) n) :
    letI := affineChartAlgebra f ⊤
    (affineCanonicalFrameIso f n b).hom.app ⊤
      ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z) =
        affineCanonicalTrivialization b z := by
  let := affineChartAlgebra f ⊤
  let e := affineCanonicalFrameIso f n b
  have hi : Function.Injective (e.inv.app (⊤ : X.Opens)) :=
    (ConcreteCategory.bijective_of_isIso (e.inv.app (⊤ : X.Opens))).1
  apply hi
  have hleft : e.inv.app ⊤ (e.hom.app ⊤
      ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z)) =
        (exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z :=
    Scheme.Modules.iso_hom_inv_app_applyT e (.op ⊤) _
  refine hleft.trans ?_
  change (exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z =
    affineCanonicalTrivialization b z •
      (canonicalLineSheaf f n).presheaf.map
        (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op (affineCanonicalFrameSection f n b)
  simpa using affineCanonicalFrameSection_smul f n b z

end
end EnvelopeProperty.CanonicalGeometry
