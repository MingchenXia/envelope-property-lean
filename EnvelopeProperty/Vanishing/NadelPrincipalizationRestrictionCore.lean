import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Functorial

/-! # The actual last scheme of a pulled-back BP sequence after empty erasure -/

open AlgebraicGeometry CategoryTheory Scheme.BlowUpSequence

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelPrincipalizationRestrictionCore

set_option backward.isDefEq.respectTransparency false

private theorem stageMap_transport {X : Scheme.{u}} (S : X.BlowUpSequence)
    {i j : Fin (S.length + 1)} (h : i = j) :
    eqToHom (congrArg S.stage h) ≫ S.stageMap j = S.stageMap i := by
  subst j
  simp

variable {X Y : Scheme.{u}} (S : X.BlowUpSequence) (g : Y ⟶ X) [Flat g]

/-- The SAME native last-stage pullback map has the original cartesian square. -/
theorem pullbackLast_isPullback :
    IsPullback (S.pullbackLastHom g) (S.pullback g).composite S.composite g := by
  let e : (S.pullback g).last ≅
      (S.pullback g).stage (S.pullbackStageIdx g (Fin.last S.length)) :=
    eqToIso (congrArg (S.pullback g).stage (pullbackStageIdx_last S g).symm)
  apply (isPullback_pullbackStageHom S g (Fin.last _)).of_iso'
    e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [e, eqToIso.hom, Iso.refl_hom, Category.comp_id]
    exact stageMap_transport (S.pullback g) (pullbackStageIdx_last S g).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp

/-- The last scheme is the actual categorical pullback of the original composite. -/
def pullbackLastIso : (S.pullback g).last ≅ CategoryTheory.Limits.pullback S.composite g :=
  (pullbackLast_isPullback S g).isoIsPullback _ _ (IsPullback.of_hasPullback _ _)

theorem pullbackLastIso_fst :
    (pullbackLastIso S g).hom ≫ CategoryTheory.Limits.pullback.fst S.composite g =
      S.pullbackLastHom g :=
  (pullbackLast_isPullback S g).isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback _ _)

theorem pullbackLastIso_snd :
    (pullbackLastIso S g).hom ≫ CategoryTheory.Limits.pullback.snd S.composite g =
      (S.pullback g).composite :=
  (pullbackLast_isPullback S g).isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback _ _)

/-- Deletion of the native empty blow-ups preserves the actual pullback last scheme. -/
def erasedPullbackLastIso :
    (S.pullback g).eraseEmpty.last ≅ CategoryTheory.Limits.pullback S.composite g :=
  asIso (S.pullback g).eraseEmptyLastHom ≪≫ pullbackLastIso S g

theorem erasedPullbackLastIso_fst :
    (erasedPullbackLastIso S g).hom ≫ CategoryTheory.Limits.pullback.fst S.composite g =
      (S.pullback g).eraseEmptyLastHom ≫ S.pullbackLastHom g := by
  simp only [erasedPullbackLastIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullbackLastIso_fst]

theorem erasedPullbackLastIso_snd :
    (erasedPullbackLastIso S g).hom ≫ CategoryTheory.Limits.pullback.snd S.composite g =
      (S.pullback g).eraseEmpty.composite := by
  simp only [erasedPullbackLastIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullbackLastIso_snd]
  exact Hironaka.Sequence.eraseEmptyLastHom_comp_composite (S.pullback g)

end EnvelopeProperty.Vanishing.NadelPrincipalizationRestrictionCore
