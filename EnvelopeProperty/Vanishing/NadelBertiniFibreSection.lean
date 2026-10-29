import EnvelopeProperty.Vanishing.NadelBertiniFibreGraph
import EnvelopeProperty.Vanishing.NadelBertiniRestrictionAlgebra
/-! # Native universal-section evaluation recovers the same original whole selected section -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniFibreSection
open NadelBertiniUniversal NadelBertiniFibreGraph NadelBertiniPullbackSections NadelBertiniRestrictionAlgebra
  SchemeLineSectionEvaluation Berkovich.SchemeFramedSectionPullback

theorem id_unitTop {X : Scheme.{u}} (L : X.Modules) (s : Γ(L, ⊤)) :
    ((pullbackId X).hom.app L).app ⊤ (affinePullbackUnitTop (𝟙 X) L s) = s := by
  have h := unit_conjugateEquiv (Adjunction.id : 𝟭 X.Modules ⊣ 𝟭 X.Modules)
    (pullbackPushforwardAdjunction (𝟙 X)) (pullbackId X).hom L
  rw [conjugateEquiv_pullbackId_hom] at h
  have h' := congrArg (fun z => z.app ⊤ s) h
  have hu : affinePullbackUnitTop (𝟙 X) L s = ((pullbackPushforwardAdjunction (𝟙 X)).unit.app L).app ⊤ s := by
    unfold affinePullbackUnitTop
    have hk : (eqToHom (show (⊤ : X.Opens) = (𝟙 X : X ⟶ X) ⁻¹ᵁ ⊤ by simp)).op = 𝟙 (op (⊤ : X.Opens)) := Subsingleton.elim _ _
    rw [hk]
    erw [CategoryTheory.Functor.map_id]
    rfl
  rw [hu]
  exact h'.symm

theorem congr_unitTop {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g) (L : X.Modules) (s : Γ(L, ⊤)) :
    ((pullbackCongr h).hom.app L).app ⊤ (affinePullbackUnitTop f L s) = affinePullbackUnitTop g L s := by
  subst g
  simp [pullbackCongr]

variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) (a : Fin (m + 1) → k)

def graphLineIso (L : X.Modules) : (pullback (graph p a)).obj (productLine (m := m) p L) ≅ L :=
  (pullbackComp (graph p a) (FlatGlobalSections.firstProjection (S := parameterRing k m) p)).app L ≪≫
    (pullbackCongr (graph_firstProjection p a)).app L ≪≫ (pullbackId X).app L

theorem graphLineIso_section (L : X.Modules) (s : Γ(L, ⊤)) :
    (graphLineIso p a L).hom.app ⊤
      (affinePullbackUnitTop (graph p a) (productLine (m := m) p L)
        (affinePullbackUnitTop (FlatGlobalSections.firstProjection (S := parameterRing k m) p) L s)) = s := by
  change ((pullbackId X).hom.app L).app ⊤
      (((pullbackCongr (graph_firstProjection p a)).hom.app L).app ⊤
        (((pullbackComp (graph p a) (FlatGlobalSections.firstProjection (S := parameterRing k m) p)).hom.app L).app ⊤
          (affinePullbackUnitTop (graph p a) (productLine (m := m) p L)
            (affinePullbackUnitTop (FlatGlobalSections.firstProjection (S := parameterRing k m) p) L s)))) = s
  rw [affinePullbackUnitTop_comp, congr_unitTop, id_unitTop]

def selectedSection (L : X.Modules) (s : Fin (m + 1) → Γ(L, ⊤)) : Γ(L, ⊤) :=
  ∑ j, ProperBirationalSections.coefficientMap p (a j) • s j

theorem universal_section (L : X.Modules) (s : Fin (m + 1) → Γ(L, ⊤)) :
    (graphLineIso p a L).hom.app ⊤
      (affinePullbackUnitTop (graph p a) (productLine (m := m) p L) (universalSection p L s)) =
      selectedSection p a L s := by
  change (graphLineIso p a L).hom.app ⊤ ((pullbackAddHom (graph p a) (productLine (m := m) p L))
    (∑ j, coefficient p j • affinePullbackUnitTop
      (FlatGlobalSections.firstProjection (S := parameterRing k m) p) L (s j))) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (graphLineIso p a L).hom.app ⊤
    (affinePullbackUnitTop (graph p a) _ (coefficient p j • affinePullbackUnitTop
      (FlatGlobalSections.firstProjection (S := parameterRing k m) p) L (s j))) = _
  rw [pullback_smul, Hom.app_smul, graphLineIso_section, graph_coefficient]

theorem universal_sectionHom (L : X.Modules) (s : Fin (m + 1) → Γ(L, ⊤)) :
    pullbackSectionHom (graph p a)
        (SchemeModuleGlobalSections.sectionHom (productLine (m := m) p L) (universalSection p L s)) ≫
        (graphLineIso p a L).hom = SchemeModuleGlobalSections.sectionHom L (selectedSection p a L s) := by
  have ht := transportedSection_sectionHom (graph p a) (graphLineIso p a L) (universalSection p L s)
  have hs : transportedSection (graph p a) (graphLineIso p a L) (universalSection p L s) =
      selectedSection p a L s := universal_section p a L s
  rw [hs] at ht
  exact ht.symm

end EnvelopeProperty.Vanishing.NadelBertiniFibreSection
