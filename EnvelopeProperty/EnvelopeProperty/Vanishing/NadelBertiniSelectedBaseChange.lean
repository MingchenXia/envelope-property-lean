import EnvelopeProperty.Vanishing.NadelBertiniFibreSmooth
/-! # Every actual original source map retains the same whole selected projective ideal -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniSelectedBaseChange
open NadelBertiniFibreSection NadelBertiniFibreGeometry NadelBertiniFibreIdeals NadelBertiniFibreSmooth
  NadelBertiniRestrictionAlgebra NadelBertiniPullbackSections NadelBertiniRestrictionCover NadelBertiniUniversal
  Berkovich.SchemeFramedSectionPullback SchemeLineSectionEvaluation
variable {k : Type u} [Field k] {m : ℕ} {X Y : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) (f : Y ⟶ X) (a : Fin (m + 1) → k)
  (L : X.Modules) (s : Fin (m + 1) → Γ(L, ⊤))

theorem selectedSection_pullback : affinePullbackUnitTop f L (selectedSection p a L s) =
    selectedSection (f ≫ p) a ((pullback f).obj L) (fun i => affinePullbackUnitTop f L (s i)) := by
  change (pullbackAddHom f L) (∑ i, ProperBirationalSections.coefficientMap p (a i) • s i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change affinePullbackUnitTop f L (ProperBirationalSections.coefficientMap p (a i) • s i) = _
  rw [pullback_smul]
  have hc : f.appTop (ProperBirationalSections.coefficientMap p (a i)) =
      ProperBirationalSections.coefficientMap (f ≫ p) (a i) := by
    simp only [ProperBirationalSections.coefficientMap, Scheme.Hom.comp_appTop]
    rfl
  rw [hc]

theorem selectedSectionHom_pullback :
    pullbackSectionHom f (SchemeModuleGlobalSections.sectionHom L (selectedSection p a L s)) =
      SchemeModuleGlobalSections.sectionHom ((pullback f).obj L)
        (selectedSection (f ≫ p) a ((pullback f).obj L) (fun i => affinePullbackUnitTop f L (s i))) := by
  have h := transportedSection_sectionHom f (Iso.refl ((pullback f).obj L)) (selectedSection p a L s)
  change topSectionHom ((pullback f).obj L) (affinePullbackUnitTop f L (selectedSection p a L s)) =
    pullbackSectionHom f (topSectionHom L (selectedSection p a L s)) ≫ 𝟙 _ at h
  rw [Category.comp_id, selectedSection_pullback] at h
  exact h.symm

theorem selectedIdeal_comap (hL : IsInvertible L) :
    (selectedIdeal p a L hL s).comap f =
      selectedIdeal (f ≫ p) a ((pullback f).obj L) (hL.pullback f) (fun i => affinePullbackUnitTop f L (s i)) := by
  change (LineSectionZeroIdeal.zeroIdeal L hL (SchemeModuleGlobalSections.sectionHom L (selectedSection p a L s))).comap f = _
  rw [zeroIdeal_comap, selectedSectionHom_pullback]
  rfl

theorem selectedSection_iso (N : X.Modules) (e : L ≅ N) :
    e.hom.app ⊤ (selectedSection p a L s) = selectedSection p a N (fun i => e.hom.app ⊤ (s i)) := by
  change e.hom.app ⊤ (∑ i, ProperBirationalSections.coefficientMap p (a i) • s i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Hom.app_smul e.hom _ _

theorem selectedIdeal_iso (hL : IsInvertible L) (N : X.Modules) (hN : IsInvertible N) (e : L ≅ N) :
    selectedIdeal p a L hL s = selectedIdeal p a N hN (fun i => e.hom.app ⊤ (s i)) := by
  let α := SchemeModuleGlobalSections.sectionHom L (selectedSection p a L s)
  have h := zeroIdeal_iso L N hL hN e α
  have ht := topSectionHom_sectionAtOne (α ≫ e.hom)
  change topSectionHom N (e.hom.app ⊤ (sectionAtOne α)) = α ≫ e.hom at ht
  have hα : sectionAtOne α = selectedSection p a L s := topSectionHom_app_top_apply_one L _
  rw [hα, selectedSection_iso] at ht
  rw [← ht] at h
  exact h

theorem projectiveSections_pullback (j : X ⟶ DeJongAlterations.projectiveSpace k m) (i : Fin (m + 1)) :
    ((pullbackComp f j).hom.app
      (MvPolynomial.coordinateHyperplaneTwist (R := k) (0 : Fin (m + 1)) 1)).app ⊤
      (affinePullbackUnitTop f (projectiveLine j) (projectiveSections j i)) =
      projectiveSections (f ≫ j) i := by
  change ((pullbackComp f j).hom.app
      (MvPolynomial.coordinateHyperplaneTwist (R := k) (0 : Fin (m + 1)) 1)).app ⊤
      (affinePullbackUnitTop f (projectiveLine j)
        (sectionAtOne (pullbackSectionHom j
          (ProjectiveTwistGlobalGeneration.coordinateSectionHom (R := k) (0 : Fin (m + 1)) i 1)))) = _
  rw [pullback_sectionAtOne]
  exact congrArg sectionAtOne (pullbackSectionHom_comp f j
    (ProjectiveTwistGlobalGeneration.coordinateSectionHom (R := k) (0 : Fin (m + 1)) i 1))

theorem projectiveSelectedIdeal_comap (j : X ⟶ DeJongAlterations.projectiveSpace k m) :
    (projectiveSelectedIdeal j a).comap f = projectiveSelectedIdeal (f ≫ j) a := by
  let pX := j ≫ DeJongAlterations.projectiveSpaceStructure k m
  let L' := (pullback f).obj (projectiveLine j)
  let hL := (MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := k) (0 : Fin (m + 1)) 1).pullback j
  let hN := (MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := k) (0 : Fin (m + 1)) 1).pullback (f ≫ j)
  let s' := fun i => affinePullbackUnitTop f (projectiveLine j) (projectiveSections j i)
  let e : L' ≅ projectiveLine (f ≫ j) :=
    (pullbackComp f j).app (MvPolynomial.coordinateHyperplaneTwist (R := k) (0 : Fin (m + 1)) 1)
  have hi := selectedIdeal_iso (f ≫ pX) a L' s' (hL.pullback f) (projectiveLine (f ≫ j)) hN e
  have hs : (fun i => e.hom.app ⊤ (s' i)) = projectiveSections (f ≫ j) := by
    funext i
    exact projectiveSections_pullback f j i
  rw [hs] at hi
  change (selectedIdeal pX a (projectiveLine j) hL (projectiveSections j)).comap f = _
  have hf := selectedIdeal_comap pX f a (projectiveLine j) (projectiveSections j) hL
  apply hf.trans
  change selectedIdeal (f ≫ pX) a L' (hL.pullback f) s' =
    selectedIdeal ((f ≫ j) ≫ DeJongAlterations.projectiveSpaceStructure k m) a
      (projectiveLine (f ≫ j)) hN (projectiveSections (f ≫ j))
  rw [Category.assoc]
  exact hi

end EnvelopeProperty.Vanishing.NadelBertiniSelectedBaseChange
