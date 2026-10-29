import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionStrataAmpleness
import EnvelopeProperty.AlgGeom.SchemePointClosureIntegral
import EnvelopeProperty.AlgGeom.CurveCartierIdealDegrees
import EnvelopeProperty.AlgGeom.LineSectionZeroIdeal
import EnvelopeProperty.Projective.TestConfigurationSectionTransport

/-!
# Seshadri Ampleness Criterion Proper Cut Ampleness

Native ampleness on the same proper Cartier cut from the genuine
lower-dimensional integral closed-subscheme induction conclusion.
The cut may be reducible and nonreduced. The intermediate IH below is not
an additional input of the final numerical Nakai theorem. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme.Modules
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterionProperCutAmpleness

/-- The original nonzero cut has ample literal reduced point closures,
using the proper integral closed-map induction conclusion only on those
actual original closures. All whole pullback comparisons are internal. -/
theorem sectionCut_strataAmple_of_properIntegralClosedAmple
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (L : X.Modules) (hL : IsInvertible L) (A : X.Modules) (hA : IsInvertible A)
    (s : unitObj X ⟶ A) (hs : s ≠ 0)
    (hIH : ∀ (Y : Scheme.{u}) [IsIntegral Y] (j : Y ⟶ X),
      IsClosedImmersion j → ¬Function.Surjective j →
        SchemeLineAmpleness.IsAmple (j ≫ p) ((Scheme.Modules.pullback j).obj L)) :
    let I := LineSectionZeroIdeal.zeroIdeal A hA s
    ∀ eta : I.subscheme,
      let J := Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({eta} : Set I.subscheme), isClosed_closure⟩ : Closeds I.subscheme)
      SchemeLineAmpleness.IsAmple (J.subschemeι ≫ (I.subschemeι ≫ p))
        ((Scheme.Modules.pullback J.subschemeι).obj ((Scheme.Modules.pullback I.subschemeι).obj L)) := by
  intro I eta J
  let g := I.subschemeι
  have hCartier : I.IsInvertible := LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero A hA s hs
  have hg : ¬Function.Surjective g := by
    intro hsurj
    apply CurveCartierIdealDegrees.support_ne_top I hCartier
    apply SetLike.coe_injective
    change (I.support : Set X) = Set.univ
    exact I.range_subschemeι.symm.trans (Set.range_eq_univ.mpr hsurj)
  let : IsIntegral J.subscheme := SchemePointClosureIntegral.isIntegral_pointClosure eta
  have hj : ¬Function.Surjective (J.subschemeι ≫ g) := by
    intro hsurj
    apply hg
    intro x
    obtain ⟨z, hz⟩ := hsurj x
    exact ⟨J.subschemeι z, hz⟩
  have h := hIH J.subscheme (J.subschemeι ≫ g) inferInstance hj
  obtain ⟨_hM, r, hr, n, q, hq, hbase, ⟨e⟩⟩ := h
  let c := ((pullbackComp J.subschemeι g).app L).symm
  refine ⟨(hL.pullback g).pullback J.subschemeι, r, hr, n, q, hq, ?_,
    ⟨e ≪≫ TestConfigurationSectionTransport.tensorPowerIso c r⟩⟩
  exact hbase.trans (Category.assoc J.subschemeι g p)

/-- The same original line is natively ample on the entire actual cut.
Only the proper integral closed-map intermediate IH is assumed; the cut
itself is never assumed integral, reduced, or already ample. -/
theorem isAmple_sectionCut_of_properIntegralClosedAmple
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (L : X.Modules) (hL : IsInvertible L) (A : X.Modules) (hA : IsInvertible A)
    (s : unitObj X ⟶ A) (hs : s ≠ 0)
    (hIH : ∀ (Y : Scheme.{u}) [IsIntegral Y] (j : Y ⟶ X),
      IsClosedImmersion j → ¬Function.Surjective j →
        SchemeLineAmpleness.IsAmple (j ≫ p) ((Scheme.Modules.pullback j).obj L)) :
    let I := LineSectionZeroIdeal.zeroIdeal A hA s
    SchemeLineAmpleness.IsAmple (I.subschemeι ≫ p) ((Scheme.Modules.pullback I.subschemeι).obj L) := by
  intro I
  let : IsProjective (I.subschemeι ≫ p) := by
    obtain ⟨V, hV, hVt, i, hi, hbase⟩ :=
      (inferInstance : IsProjective p).exists_isClosedImmersion
    let : IsClosedImmersion i := hi
    exact ⟨⟨V, hV, hVt, I.subschemeι ≫ i, inferInstance,
      (Category.assoc I.subschemeι i _).trans (congrArg (fun q => I.subschemeι ≫ q) hbase)⟩⟩
  exact SeshadriAmplenessCriterionStrataAmpleness.isAmple_of_strataAmple
    (I.subschemeι ≫ p) ((Scheme.Modules.pullback I.subschemeι).obj L) (hL.pullback I.subschemeι)
    (sectionCut_strataAmple_of_properIntegralClosedAmple p L hL A hA s hs hIH)

end EnvelopeProperty.SeshadriAmplenessCriterionProperCutAmpleness
