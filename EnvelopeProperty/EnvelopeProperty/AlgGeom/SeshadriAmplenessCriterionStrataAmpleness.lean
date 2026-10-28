import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionStrataReduction
import EnvelopeProperty.AlgGeom.SchemeVeryAmpleTensorGeneratingSections

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open TopologicalSpace Scheme.Modules MvPolynomial
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterionStrataAmpleness
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ordinary genuine ampleness on each SAME literal original reduced point
closure internally gives genuine native ampleness of the SAME original line.
The original ambient scheme can be reducible and nonreduced. This conditional
reduction does not supply its separate integral Nakai hypotheses. -/
theorem isAmple_of_strataAmple
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (L : X.Modules) (hL : IsInvertible L)
    (hstrata : ∀ eta : X,
      let I := Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
      SchemeLineAmpleness.IsAmple (I.subschemeι ≫ p)
        ((Scheme.Modules.pullback I.subschemeι).obj L)) :
    SchemeLineAmpleness.IsAmple p L := by
  classical
  obtain ⟨d, i, hi, hbase⟩ := ProjectiveFactorizationRingIso.of_isProjective p
  let H : X.Modules := (Scheme.Modules.pullback i).obj
    (coordinateHyperplaneTwist (R := k) (0 : Fin (d + 1)) 1)
  have hH : SchemeLineAmpleness.IsVeryAmple p H := by
    refine ⟨d, i, hi, ?_, ⟨Iso.refl H⟩⟩
    convert hbase using 1
    unfold homogeneousProjπ DeJongAlterations.projectiveSpaceStructure
    congr 1
  let E := dualObj H
  have hE : IsInvertible E := hH.isInvertible.dual
  let : E.IsQuasicoherent := hE.isQuasicoherent
  let : E.IsFinitePresentation := hE.isFinitePresentation
  let : E.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
    (R := X.ringCatSheaf) E
  obtain ⟨N, hN⟩ :=
    SeshadriAmplenessCriterionStrataReduction.exists_eventual_generatingSections_of_strataAmple
      p E L hL hstrata
  let m := max N 1
  have hm : 0 < m := lt_of_lt_of_le (by decide : 0 < 1) (le_max_right N 1)
  obtain ⟨G, hG⟩ := hN m (le_max_left N 1)
  have hP : IsInvertible (bundleTensorPower L m) :=
    TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m
  have hVA := SchemeVeryAmpleTensorGeneratingSections.isVeryAmple_of_inverse_twist_generated
    p H (bundleTensorPower L m) hH hP G hG
  exact ⟨hL, m, hm, hVA⟩

#print axioms isAmple_of_strataAmple
end EnvelopeProperty.SeshadriAmplenessCriterionStrataAmpleness
