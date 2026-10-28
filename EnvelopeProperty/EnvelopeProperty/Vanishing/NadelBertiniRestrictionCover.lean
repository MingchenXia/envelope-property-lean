import EnvelopeProperty.Vanishing.NadelBertiniRestrictionIdeal
import EnvelopeProperty.Vanishing.NadelBertiniProjectiveFrames
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
/-! # The actual original subscheme is covered by its genuine whole-ideal open pullbacks -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniRestrictionCover
open SchemeLineSectionEvaluation
variable {Y : Scheme.{u}}

def restrictionMap (I : Y.IdealSheafData) (V : Y.Opens) :
    (I.comap V.ι).subscheme ⟶ I.subscheme :=
  (I.comapIso V.ι).hom ≫ pullback.snd V.ι I.subschemeι

instance restrictionMap_isOpenImmersion (I : Y.IdealSheafData) (V : Y.Opens) :
    IsOpenImmersion (restrictionMap I V) := by dsimp [restrictionMap]; infer_instance

theorem restrictionMap_opensRange (I : Y.IdealSheafData) (V : Y.Opens) :
    (restrictionMap I V).opensRange = I.subschemeι ⁻¹ᵁ V := by
  change ((I.comapIso V.ι).hom ≫ pullback.snd V.ι I.subschemeι).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Hom.opensRange_pullbackSnd, Scheme.Opens.opensRange_ι]

theorem restrictionMap_toSource {X : Scheme.{u}} (I : Y.IdealSheafData) (f : Y ⟶ X) (W : X.Opens) :
    restrictionMap I (f ⁻¹ᵁ W) ≫ I.subschemeι ≫ f =
      (I.comap (f ⁻¹ᵁ W).ι).subschemeι ≫ f ∣_ W ≫ W.ι := by
  rw [morphismRestrict_ι, ← Category.assoc, ← Category.assoc]
  change (I.comapIso (f ⁻¹ᵁ W).ι).hom ≫ pullback.snd _ _ ≫ I.subschemeι ≫ f = _
  rw [← pullback.condition_assoc, I.comapIso_hom_fst_assoc]
  rfl

def restrictionCover (I : Y.IdealSheafData) {T : Type*} (W : T → Y.Opens) (hW : iSup W = ⊤) :
    I.subscheme.OpenCover :=
  Scheme.Cover.mkOfCovers T (fun a => (I.comap (W a).ι).subscheme)
    (fun a => restrictionMap I (W a)) (fun x => by
      have hx : I.subschemeι x ∈ ⨆ a, W a := by rw [hW]; trivial
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      have hx' : x ∈ (restrictionMap I (W a)).opensRange := by
        rw [restrictionMap_opensRange]
        exact ha
      change ∃ z, restrictionMap I (W a) z = x at hx'
      obtain ⟨z, hz⟩ := hx'
      exact ⟨a, z, hz⟩)

private theorem unitHom_ext {X : Scheme.{u}} {L : X.Modules} {α β : unitObj X ⟶ L}
    (h : sectionAtOne α = sectionAtOne β) : α = β := by
  apply SheafOfModules.hom_ext
  ext V
  let i := (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
  have ha := PresheafOfModules.naturality_apply α.val i (show Γ(X, ⊤) from 1)
  have hb := PresheafOfModules.naturality_apply β.val i (show Γ(X, ⊤) from 1)
  change α.val.app V (X.presheaf.map i (show Γ(X, ⊤) from 1)) = L.presheaf.map i (sectionAtOne α) at ha
  change β.val.app V (X.presheaf.map i (show Γ(X, ⊤) from 1)) = L.presheaf.map i (sectionAtOne β) at hb
  rw [map_one] at ha hb
  exact ha.trans ((congrArg (fun z => L.presheaf.map i z) h).trans hb.symm)

theorem topSectionHom_sectionAtOne {X : Scheme.{u}} {L : X.Modules} (α : unitObj X ⟶ L) :
    topSectionHom L (sectionAtOne α) = α := by
  apply unitHom_ext
  exact topSectionHom_app_top_apply_one L _

theorem pullback_sectionAtOne {X Y : Scheme.{u}} (f : Y ⟶ X) {L : X.Modules} (α : unitObj X ⟶ L) :
    affinePullbackUnitTop f L (sectionAtOne α) = sectionAtOne (pullbackSectionHom f α) := by
  rw [Berkovich.SchemeFramedSectionPullback.affinePullbackUnitTop_eq_sectionAtOne, topSectionHom_sectionAtOne]
end EnvelopeProperty.Vanishing.NadelBertiniRestrictionCover
