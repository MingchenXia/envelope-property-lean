import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationMap
import EnvelopeProperty.AlgGeom.SchemeLineSectionUnitFrames
import EnvelopeProperty.AlgGeom.SchemeModuleGlobalSections

/-! # Actual whole H0 adjunction values before Gauss-frame scalar evaluation

Every map is constructed from the SAME original native adjunction and
original module frame. The actual whole-section/unit comparison is proved;
no H0 comparison or decomposition is an input.
-/
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules SchemeLineSectionEvaluation

/-- The ACTUAL original top adjunction unit is the SAME original pulled section value. -/
theorem originalPullbackUnitTop_sectionAtOne {A B : Scheme.{u}} (g : B ⟶ A)
    (M : A.Modules) (s : Γ(M, ⊤)) :
    sectionAtOne (pullbackSectionHom g (topSectionHom M s)) = affinePullbackUnitTop g M s := by
  unfold sectionAtOne affinePullbackUnitTop
  rw [pullback_unit_app_top_applyT]
  let β := pullbackSectionHom g (topSectionHom M s)
  let i := (eqToHom (show (⊤ : B.Opens) = g ⁻¹ᵁ (⊤ : A.Opens) by simp)).op
  change β.val.app (op ⊤) (show Γ(B, ⊤) from 1) =
    ((pullback g).obj M).presheaf.map i
      (β.val.app (op (g ⁻¹ᵁ ⊤)) ((g.app ⊤).hom (show Γ(A, ⊤) from 1)))
  have hg : (g.app ⊤).hom (show Γ(A, ⊤) from 1) =
      (show Γ(B, g ⁻¹ᵁ ⊤) from 1) := map_one _
  rw [hg]
  have hn := PresheafOfModules.naturality_apply β.val i
    (show Γ(B, g ⁻¹ᵁ ⊤) from 1)
  change β.val.app (op ⊤)
      (B.presheaf.map i (show Γ(B, g ⁻¹ᵁ ⊤) from 1)) =
    ((pullback g).obj M).presheaf.map i
      (β.val.app (op (g ⁻¹ᵁ ⊤)) (show Γ(B, g ⁻¹ᵁ ⊤) from 1)) at hn
  have hi : B.presheaf.map i (show Γ(B, g ⁻¹ᵁ ⊤) from 1) =
      (show Γ(B, ⊤) from 1) := map_one _
  rw [hi] at hn
  exact hn

/-- The SAME native original global section retains every actual module image. -/
theorem originalTopSectionHom_postcomp {A : Scheme.{u}} {M N : A.Modules}
    (a : M ⟶ N) (s : Γ(M, ⊤)) :
    topSectionHom M s ≫ a = topSectionHom N (a.val.app (op ⊤) s) :=
  SchemeModuleGlobalSections.sectionHom_comp s a

/-- The actual original adjunction-unit whole section map followed by its actual frame. -/
def originalFramedGlobalPullback {A B : Scheme.{u}} (g : B ⟶ A) (M : A.Modules)
    (E : (pullback g).obj M ≅ unitObj B) : Γ(M, ⊤) →+ Γ(B, ⊤) :=
  (E.hom.val.app (op ⊤)).hom.toAddMonoidHom.comp
    (pullbackTopRestrictMap g M).hom.toAddMonoidHom

/-- Every actual original H0 value is its SAME actual native pulled frame scalar. -/
theorem originalFramedGlobalPullback_apply {A B : Scheme.{u}} (g : B ⟶ A)
    (M : A.Modules) (E : (pullback g).obj M ≅ unitObj B) (s : Γ(M, ⊤)) :
    originalFramedGlobalPullback g M E s =
      SchemeLineSectionUnitFrames.frameScalar E (pullbackSectionHom g (topSectionHom M s)) := by
  change E.hom.val.app (op ⊤) (pullbackTopRestrictMap g M s) = _
  rw [pullbackTopRestrictMap_apply, ← originalPullbackUnitTop_sectionAtOne g M s]
  rfl

/-- Original scalar multiplication retains the SAME original ring pullback and frame. -/
theorem originalFramedGlobalPullback_base_smul {A B : Scheme.{u}} (g : B ⟶ A)
    (M : A.Modules) (E : (pullback g).obj M ≅ unitObj B)
    (a : Γ(A, ⊤)) (s : Γ(M, ⊤)) :
    originalFramedGlobalPullback g M E (a • s) =
      g.appTop.hom a * originalFramedGlobalPullback g M E s := by
  have hp := (pullbackTopRestrictMap g M).hom.map_smul a s
  change pullbackTopRestrictMap g M (a • s) =
    g.appTop.hom a • pullbackTopRestrictMap g M s at hp
  have he := (E.hom.val.app (op ⊤)).hom.map_smul
    (g.appTop.hom a) (pullbackTopRestrictMap g M s)
  exact (congrArg (fun t => E.hom.val.app (op ⊤) t) hp).trans he

/-- Every actual finite original family retains all its SAME original scalar coefficients. -/
theorem originalFramedGlobalPullback_finsupp_sum {A B : Scheme.{u}} (g : B ⟶ A)
    (M : A.Modules) (E : (pullback g).obj M ≅ unitObj B)
    (c : ℤ →₀ Γ(M, ⊤)) (a : ℤ → Γ(A, ⊤)) :
    originalFramedGlobalPullback g M E (c.sum (fun n s => a n • s)) =
      c.sum (fun n s => g.appTop.hom (a n) * originalFramedGlobalPullback g M E s) := by
  classical
  simp only [Finsupp.sum, map_sum, originalFramedGlobalPullback_base_smul]

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
