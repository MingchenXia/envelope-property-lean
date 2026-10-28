import EnvelopeProperty.Vanishing.NadelBertiniFibreSection
/-! # The literal original incidence parameter fibre is the same whole selected zero-ideal subscheme -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniFibreGeometry
open NadelBertiniUniversal NadelBertiniFibreIdeals NadelBertiniFibreGraph NadelBertiniFibreSection
  NadelBertiniRationalParameter SchemeLineSectionEvaluation
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) (a : Fin (m + 1) → k)
  (L : X.Modules) (hL : IsInvertible L) (s : Fin (m + 1) → Γ(L, ⊤))

def selectedIdeal : X.IdealSheafData :=
  LineSectionZeroIdeal.zeroIdeal L hL (SchemeModuleGlobalSections.sectionHom L (selectedSection p a L s))

theorem incidenceIdeal_comap_graph : (incidenceIdeal p L hL s).comap (graph p a) = selectedIdeal p a L hL s := by
  let f := FlatGlobalSections.firstProjection (S := parameterRing k m) p
  let α := SchemeModuleGlobalSections.sectionHom (productLine (m := m) p L) (universalSection p L s)
  change (LineSectionZeroIdeal.zeroIdeal (productLine (m := m) p L) (hL.pullback f) α).comap (graph p a) = _
  rw [zeroIdeal_comap]
  have h := zeroIdeal_iso ((Scheme.Modules.pullback (graph p a)).obj (productLine (m := m) p L)) L
    ((hL.pullback f).pullback (graph p a)) hL (graphLineIso p a L) (pullbackSectionHom (graph p a) α)
  rw [universal_sectionHom] at h
  exact h

private def subschemeIsoOfEq {Y : Scheme.{u}} {I J : Y.IdealSheafData} (h : I = J) : I.subscheme ≅ J.subscheme :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme h)

private theorem subschemeIsoOfEq_hom_ι {Y : Scheme.{u}} {I J : Y.IdealSheafData} (h : I = J) :
    (subschemeIsoOfEq h).hom ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp [subschemeIsoOfEq]

theorem fibreSquare :
    IsPullback (pullback.snd (graph p a) (incidenceIdeal p L hL s).subschemeι)
      (pullback.fst (graph p a) (incidenceIdeal p L hL s).subschemeι ≫ p)
      (toParameters p L hL s) (parameterMap a) :=
  (IsPullback.of_hasPullback (graph p a) (incidenceIdeal p L hL s).subschemeι).flip.paste_vert
    (graph_isPullback p a)

def selectedFibreIso : (selectedIdeal p a L hL s).subscheme ≅
    pullback (toParameters p L hL s) (parameterMap a) :=
  subschemeIsoOfEq (incidenceIdeal_comap_graph p a L hL s).symm ≪≫
    (incidenceIdeal p L hL s).comapIso (graph p a) ≪≫ (fibreSquare p a L hL s).isoPullback

theorem selectedFibreIso_base :
    (selectedFibreIso p a L hL s).hom ≫ pullback.snd (toParameters p L hL s) (parameterMap a) =
      (selectedIdeal p a L hL s).subschemeι ≫ p := by
  simp only [selectedFibreIso, Iso.trans_hom, Category.assoc, IsPullback.isoPullback_hom_snd]
  rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc, ← Category.assoc, subschemeIsoOfEq_hom_ι]

theorem selectedFibreIso_source :
    (selectedFibreIso p a L hL s).hom ≫ pullback.fst (toParameters p L hL s) (parameterMap a) ≫ toSource p L hL s =
      (selectedIdeal p a L hL s).subschemeι := by
  simp only [selectedFibreIso, Iso.trans_hom, Category.assoc, IsPullback.isoPullback_hom_fst_assoc]
  change (subschemeIsoOfEq (incidenceIdeal_comap_graph p a L hL s).symm).hom ≫
    ((incidenceIdeal p L hL s).comapIso (graph p a)).hom ≫
    pullback.snd (graph p a) (incidenceIdeal p L hL s).subschemeι ≫ (incidenceIdeal p L hL s).subschemeι ≫
    FlatGlobalSections.firstProjection (S := parameterRing k m) p = _
  rw [← pullback.condition_assoc]
  rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc, ← Category.assoc, subschemeIsoOfEq_hom_ι]
  rw [graph_firstProjection, Category.comp_id]
end EnvelopeProperty.Vanishing.NadelBertiniFibreGeometry
