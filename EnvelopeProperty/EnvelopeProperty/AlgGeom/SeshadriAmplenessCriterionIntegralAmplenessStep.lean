import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionDivisibleGlobalGeneration
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionFixedCoefficientGeneration
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionProperCutAmpleness
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionEulerSectionGrowth
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionCartierDifference
import EnvelopeProperty.AlgGeom.SchemeVeryAmpleTensorGeneratingSections

/-! The genuine integral geometric induction step. The proper integral
closed-subscheme ampleness premise is an intermediate induction conclusion;
the total numerical dimension induction must derive and eliminate it. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open Scheme.Modules MvPolynomial
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion
open CanonicalGeometry SchemeLineSectionEvaluation SchemeCoherentEulerIndex
attribute [local instance] Scheme.Modules.monoidalCategory
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  [CompactSpace X] [X.IsSeparated]

/-- Actual positive same-line intersection and the ordinary proper-subscheme
induction conclusion internally construct a same-line ample power cut at
each original closed point. No unknown-line section or cut ampleness is supplied. -/
theorem closedPoint_ample_powerCut_of_positive_diagonal_and_properIntegralClosedAmple
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (d : ℕ) (hd : 0 < d) (hdim : topologicalKrullDim X ≤ d)
    (L : X.Modules) (hL : IsInvertible L)
    (hpos : 0 < mixedEulerDifference p (List.replicate d L) (unitObj X))
    (hIH : ∀ (Y : Scheme.{u}) [IsIntegral Y] (j : Y ⟶ X),
      IsClosedImmersion j → ¬Function.Surjective j →
        SchemeLineAmpleness.IsAmple (j ≫ p) ((Scheme.Modules.pullback j).obj L))
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ r : ℕ, 0 < r ∧ ∃ s : unitObj X ⟶ bundleTensorPower L r, s ≠ 0 ∧
      let I := LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s
      x ∈ I.support ∧ SchemeLineAmpleness.IsAmple (I.subschemeι ≫ p)
        ((Scheme.Modules.pullback I.subschemeι).obj L) := by
  let hf := ProjectiveFactorizationRingIso.of_isProjective p
  obtain ⟨B, hB, a, b, ha, hb, _hchi⟩ :=
    exists_eulerCharacteristic_powerCartierDifference p hf L hL
  have hA : IsInvertible (L ⊗ B) :=
    (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
  have hI := SeshadriAmplenessCriterionProperCutAmpleness.isAmple_sectionCut_of_properIntegralClosedAmple
    p L hL (L ⊗ B) hA a ha hIH
  have hJ := SeshadriAmplenessCriterionProperCutAmpleness.isAmple_sectionCut_of_properIntegralClosedAmple
    p L hL B hB b hb hIH
  let U := finiteAffineOpens X
  obtain ⟨r, hr, s, hs, hsx, _hfactor⟩ :=
    exists_nonzero_power_section_at_closedPoint_of_twoCut_ample
      p U (finiteAffineOpens_cover X) (finiteAffineOpens_isAffine X)
      d hd hdim L B hL hB a ha b hb hpos x hx hI hJ
  refine ⟨r, hr, s, hs, ?_, ?_⟩
  · exact existingClosedPointZeroSupport% x (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s hsx
  · exact SeshadriAmplenessCriterionProperCutAmpleness.isAmple_sectionCut_of_properIntegralClosedAmple
      p L hL (bundleTensorPower L r) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r)
      s hs hIH

/-- Positive actual diagonal intersection and the proper integral closed
induction conclusion yield a positive ACTUAL very-ample power of SAME L.
The subsequent numerical theorem must internally supply the induction conclusion. -/
theorem isAmple_of_positive_diagonal_and_properIntegralClosedAmple
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (d : ℕ) (hd : 0 < d) (hdim : topologicalKrullDim X ≤ d)
    (L : X.Modules) (hL : IsInvertible L)
    (hpos : 0 < mixedEulerDifference p (List.replicate d L) (unitObj X))
    (hIH : ∀ (Y : Scheme.{u}) [IsIntegral Y] (j : Y ⟶ X),
      IsClosedImmersion j → ¬Function.Surjective j →
        SchemeLineAmpleness.IsAmple (j ≫ p) ((Scheme.Modules.pullback j).obj L)) :
    SchemeLineAmpleness.IsAmple p L := by
  classical
  have hcuts := closedPoint_ample_powerCut_of_positive_diagonal_and_properIntegralClosedAmple
    p d hd hdim L hL hpos hIH
  obtain ⟨x, _hx, hx⟩ := isClosed_univ.exists_closed_singleton
    (show (Set.univ : Set X).Nonempty from ⟨genericPoint X, Set.mem_univ _⟩)
  obtain ⟨r, hr, s, hs, _hxI, hI⟩ := hcuts x hx
  obtain ⟨b, hb, G, _hG⟩ := exists_positive_power_generatingSections_of_cutAmple
    p L hL r hr s hs hI
  obtain ⟨a, i, hi, hbase⟩ := ProjectiveFactorizationRingIso.of_isProjective p
  let H : X.Modules := (Scheme.Modules.pullback i).obj
    (coordinateHyperplaneTwist (R := k) (0 : Fin (a + 1)) 1)
  have hH : SchemeLineAmpleness.IsVeryAmple p H := by
    refine ⟨a, i, hi, ?_, ⟨Iso.refl H⟩⟩
    convert hbase using 1
    unfold homogeneousProjπ DeJongAlterations.projectiveSpaceStructure
    congr 1
  obtain ⟨n, hn, J, hJ⟩ :=
    SeshadriAmplenessCriterionFixedCoefficientGeneration.exists_positive_power_fixedCoefficient_generatingSections
      p (dualObj H) L hH.isInvertible.dual hL b hb G hcuts
  exact ⟨hL, n, hn,
    SchemeVeryAmpleTensorGeneratingSections.isVeryAmple_of_inverse_twist_generated
      p H (bundleTensorPower L n) hH (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n) J hJ⟩

#check @closedPoint_ample_powerCut_of_positive_diagonal_and_properIntegralClosedAmple
#print axioms closedPoint_ample_powerCut_of_positive_diagonal_and_properIntegralClosedAmple
#check @isAmple_of_positive_diagonal_and_properIntegralClosedAmple
#print axioms isAmple_of_positive_diagonal_and_properIntegralClosedAmple
end EnvelopeProperty.SeshadriAmplenessCriterion
