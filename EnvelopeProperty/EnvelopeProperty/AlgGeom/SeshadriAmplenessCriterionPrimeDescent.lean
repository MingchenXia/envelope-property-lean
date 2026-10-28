import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionProjectiveAnnihilator
import EnvelopeProperty.AlgGeom.SchemeModuleClosedDescent
import EnvelopeProperty.AlgGeom.SchemeModuleAssociatedPoint
import EnvelopeProperty.AlgGeom.SchemePointClosureIntegral

/-! # The same associated-point socle survives canonical closed descent

The internally constructed original coherent annihilator descends by its
actual closed-unit isomorphism to the literal original pullback, nonzero at
the same canonical point of the original reduced singleton closure.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion

private theorem exists_nonzero_closedPullback_stalk
    {X : Scheme.{u}} (I : X.IdealSheafData) (K : X.Modules)
    [K.IsQuasicoherent]
    (hann : ∀ (x : X) (r : X.presheaf.stalk x), r ∈ I.stalkIdeal x →
      ∀ m : K.presheaf.stalk x, r • m = 0)
    (z : I.subscheme) (m : K.presheaf.stalk (I.subschemeι z)) (hm : m ≠ 0) :
    ∃ n : ((Scheme.Modules.pullback I.subschemeι).obj K).presheaf.stalk z,
      n ≠ 0 := by
  let N := (Scheme.Modules.pullback I.subschemeι).obj K
  let a := (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app K
  let : IsIso a := SchemeModuleClosedDescent.isIso_closedUnit I K hann
  let E := Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (I.subschemeι z)
  let e := E.mapIso (asIso a)
  let q := N.presheaf.stalkPushforward AddCommGrpCat I.subschemeι.base z
  have hq : IsIso q :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat I.subschemeι.isClosedEmbedding.isInducing N.presheaf z
  let eq : ((Scheme.Modules.pushforward I.subschemeι).obj N).presheaf.stalk
      (I.subschemeι z) ≅ N.presheaf.stalk z :=
    @asIso AddCommGrpCat.{u} inferInstance _ _ q hq
  let f : K.presheaf.stalk (I.subschemeι z) ≅ N.presheaf.stalk z :=
    e ≪≫ eq
  refine ⟨f.hom m, ?_⟩
  intro hzero
  apply hm
  apply ((ConcreteCategory.isIso_iff_bijective f.hom).mp inferInstance).injective
  exact hzero.trans f.hom.hom.map_zero.symm

/-- A genuinely nonzero coherent module produces a nonzero coherent module on
the SAME actual reduced point closure through its fixed canonical closed unit. -/
theorem exists_nonzero_coherent_pointClosure_descent
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [IsProjective p]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (hF : ¬ IsZero F) :
    ∃ (eta : X) (K : X.Modules) (a : K ⟶ F),
      K.IsQuasicoherent ∧ K.IsFiniteType ∧ Mono a ∧
      let I := Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
      let N := (Scheme.Modules.pullback I.subschemeι).obj K
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app K) ∧
      N.IsQuasicoherent ∧ N.IsFiniteType ∧
      ¬ Subsingleton (N.presheaf.stalk (SchemePointClosureIntegral.pointClosureLift eta)) ∧
      IsIntegral I.subscheme ∧
      IsGenericPoint (SchemePointClosureIntegral.pointClosureLift eta) Set.univ := by
  let hp : IsProjectiveFactorization p := ProjectiveFactorizationRingIso.of_isProjective p
  let : IsProper p := hp.isProper
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨eta, m, hm, hmax⟩ := SchemeModuleAssociatedPoint.exists_nativeStalk_socle F hF
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
  have hIm : ∀ r : X.presheaf.stalk eta, r ∈ I.stalkIdeal eta → r • m = 0 := by
    intro r hr
    exact hmax r (SchemeModuleAssociatedPoint.pointClosure_stalkIdeal_le_maximalIdeal eta hr)
  obtain ⟨K, a, hKQC, hKFT, ha, hann, hlift⟩ :=
    exists_projective_coherent_annihilator p I F
  let : K.IsQuasicoherent := hKQC
  let : K.IsFiniteType := hKFT
  obtain ⟨n, hn⟩ := hlift eta m hIm
  have hn0 : n ≠ 0 := by
    intro hnzero
    apply hm
    rw [← hn, hnzero]
    exact ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} eta).map a).hom.map_zero
  let N := (Scheme.Modules.pullback I.subschemeι).obj K
  let z : I.subscheme := SchemePointClosureIntegral.pointClosureLift eta
  obtain ⟨v, hv⟩ := exists_nonzero_closedPullback_stalk I K hann z n hn0
  refine ⟨eta, K, a, hKQC, hKFT, ha,
    SchemeModuleClosedDescent.isIso_closedUnit I K hann,
    SchemeModuleClosedDescent.isQuasicoherent_closedPullback I K,
    SchemeModuleClosedDescent.isFiniteType_closedPullback I K, ?_,
    SchemePointClosureIntegral.isIntegral_pointClosure eta,
    SchemePointClosureIntegral.isGenericPoint_pointClosureLift eta⟩
  intro hzero
  exact hv (hzero.elim v 0)

#check @exists_nonzero_coherent_pointClosure_descent
#print axioms exists_nonzero_coherent_pointClosure_descent

end EnvelopeProperty.SeshadriAmplenessCriterion
