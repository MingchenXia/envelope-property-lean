import EnvelopeProperty.AlgGeom.SchemeSectionHomology
import EnvelopeProperty.AlgGeom.AffineCanonicalSectionHomology
import EnvelopeProperty.AlgGeom.AffineRestrictionSections
import EnvelopeProperty.Algebra.LeftExactHomologyCoherence

/-! # The SAME canonical section homology on ANY actual original affine open -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.AffineOpenCanonicalSectionHomology
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u
variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
variable (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
include hV

/-- Original geometry proves the SAME canonical comparison invertible on EVERY affine open. -/
theorem comparison_isIso (q : ℕ) : IsIso (SchemeSectionHomology.comparison K V q) := by
  let S := K.sc q
  let F : X.Modules ⥤ (Spec Γ(X, V)).Modules := Scheme.Modules.restrictFunctor hV.fromSpec
  let G : (Spec Γ(X, V)).Modules ⥤ ModuleCat Γ(X, V) := moduleSpecΓFunctor
  let E : X.Modules ⥤ ModuleCat Γ(X, V) :=
    Scheme.Modules.toPresheafOfModules X ⋙
      PresheafOfModules.evaluation X.ringCatSheaf.obj (op V)
  let : E.Additive := ⟨by intro M N a b; rfl⟩
  let : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let : PreservesFiniteLimits E :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits (R := X.ringCatSheaf) (op V)
  let : PreservesLimits F := Scheme.Modules.restrictFunctor_preservesLimits hV.fromSpec
  let : F.PreservesHomology := SchemeOpenRestrictionHomology.preservesHomology hV.fromSpec
  let : G.Additive := ⟨by intro M N a b; rfl⟩
  let : G.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let : G.IsRightAdjoint := (tilde.adjunction (R := Γ(X, V))).isRightAdjoint
  let : PreservesFiniteLimits (F ⋙ G) := comp_preservesFiniteLimits F G
  have hF : IsIso (LeftExactHomologyComparison.map S F) := by
    rw [LeftExactHomologyCoherence.map_eq_mapHomologyIso]
    infer_instance
  let : IsIso (LeftExactHomologyComparison.map S F) := hF
  let : S.X₁.IsQuasicoherent := (inferInstance : ∀ j, (K.X j).IsQuasicoherent) _
  let : S.X₂.IsQuasicoherent := (inferInstance : ∀ j, (K.X j).IsQuasicoherent) _
  let : S.X₃.IsQuasicoherent := (inferInstance : ∀ j, (K.X j).IsQuasicoherent) _
  let : (S.map F).X₁.IsQuasicoherent := by
    change (S.X₁.restrict hV.fromSpec).IsQuasicoherent
    infer_instance
  let : (S.map F).X₂.IsQuasicoherent := by
    change (S.X₂.restrict hV.fromSpec).IsQuasicoherent
    infer_instance
  let : (S.map F).X₃.IsQuasicoherent := by
    change (S.X₃.restrict hV.fromSpec).IsQuasicoherent
    infer_instance
  let : IsIso (LeftExactHomologyComparison.map (S.map F) G) :=
    AffineCanonicalSectionHomology.comparison_isIso Γ(X, V) (S.map F)
  let : IsIso (LeftExactHomologyComparison.map S (F ⋙ G)) := by
    rw [LeftExactHomologyCoherence.map_comp]
    infer_instance
  let α : F ⋙ G ≅ E := AffineRestrictionSections.functorIso hV
  let t := (ShortComplex.homologyFunctor (ModuleCat Γ(X, V))).mapIso (S.mapNatIso α)
  have hn : t.hom ≫ LeftExactHomologyComparison.map S E =
      LeftExactHomologyComparison.map S (F ⋙ G) ≫ α.hom.app (K.homology q) :=
    LeftExactHomologyComparison.natTrans_naturality E α.hom
  have hm : LeftExactHomologyComparison.map S E =
      t.inv ≫ (LeftExactHomologyComparison.map S (F ⋙ G) ≫ α.hom.app (K.homology q)) := by
    apply (cancel_epi t.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact hn
  change IsIso (LeftExactHomologyComparison.map S E)
  rw [hm]
  infer_instance

/-- Native homology of actual original sections is actual original homology-sheaf sections. -/
def homologyIso (q : ℕ) :
    (SchemeSectionHomology.sectionComplex K V).homology q ≅ (K.homology q).val.obj (op V) := by
  let : IsIso (SchemeSectionHomology.comparison K V q) := comparison_isIso hV K q
  exact asIso (SchemeSectionHomology.comparison K V q)

/-- The complete forward morphism is exactly the SAME original canonical comparison. -/
theorem homologyIso_hom (q : ℕ) :
    (homologyIso hV K q).hom = SchemeSectionHomology.comparison K V q := rfl

end EnvelopeProperty.AffineOpenCanonicalSectionHomology
