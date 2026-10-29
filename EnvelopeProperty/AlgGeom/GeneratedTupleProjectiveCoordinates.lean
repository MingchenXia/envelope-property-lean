import EnvelopeProperty.AlgGeom.UnitIdealReesCoordinates
import EnvelopeProperty.Alterations.Algebra.SegreGluing
import EnvelopeProperty.Alterations.Geometry.SegreChart

/-! # Exact original coordinate ratios of the SAME native Rees tuple map -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open Alterations Alterations.Geometry.FiniteProjective
open Alterations.Geometry.BlowupProjectiveEmbedding
open Alterations.Geometry.UnitIdealBlowup
open Alterations.Geometry
open Alterations.Geometry.ProjectiveIdeal
open Alterations.Algebra.ReesPresentation
open HomogeneousLocalization
universe u
namespace EnvelopeProperty.GeneratedTupleProjectiveCoordinates
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] {m : ℕ}

/-- The literal original coefficient map followed by the literal degree-one Rees evaluation. -/
def tupleGradedMap (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) :
    projectiveSpaceGrading R m →+*ᵍ reesGrading (⊤ : Ideal A) :=
  (generatorPolynomialMap ⊤ a ha).toGradedRingHom.comp (polynomialCoefficientMap r m)

/-- The actual original graded composite sends each SAME original variable to a_i*T. -/
theorem tupleGradedMap_X (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) :
    tupleGradedMap r a ha (MvPolynomial.X i) = reesDegreeOne ⊤ (a i) (by trivial) := by
  change reesPolynomialEval ⊤ a _ (MvPolynomial.map r (MvPolynomial.X i)) = _
  rw [MvPolynomial.map_X, reesPolynomialEval, MvPolynomial.aeval_X]

/-- The true irrelevant containment comes from the original two actual maps. -/
theorem tupleGradedMap_irrelevant (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) :
    HomogeneousIdeal.irrelevant (reesGrading (⊤ : Ideal A)) ≤
      (HomogeneousIdeal.irrelevant (projectiveSpaceGrading R m)).map
        (tupleGradedMap r a ha) :=
  HomogeneousIdeal.irrelevant_le_map_comp (polynomialCoefficientMap_irrelevant r m)
    (ProjClosedImmersion.irrelevant_le_map_of_surjective _
      (generatorPolynomialMap_surjective ⊤ a ha))

/-- The SAME accepted whole tuple morphism is the composite graded-map morphism. -/
theorem affineTupleMap_graded (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) :
    affineTupleMap r a ha = (unitIdealBlowupIso A).inv ≫
      Proj.map (tupleGradedMap r a ha) (tupleGradedMap_irrelevant r a ha) := by
  unfold tupleGradedMap
  rw [Proj.map_comp]
  rfl

variable [IsDomain A]

private def coefficientEquivAt (b : reesAlgebra (⊤ : Ideal A))
    (hb : b = reesDegreeOne ⊤ 1 (by trivial)) :
    A ≃+* Away (reesGrading (⊤ : Ideal A)) b := by
  subst b
  exact (UnitIdealReesCoordinates.homogeneousCoefficientEquiv A).toRingEquiv

private theorem coefficientEquivAt_generator (b : reesAlgebra (⊤ : Ideal A))
    (hb : b = reesDegreeOne ⊤ 1 (by trivial))
    (hbd : b ∈ reesGrading (⊤ : Ideal A) 1) (a : A) :
    (coefficientEquivAt b hb).symm
      (Away.mk (reesGrading (⊤ : Ideal A)) hbd 1
        (reesDegreeOne ⊤ a (by trivial)) (by simpa using reesDegreeOne_mem ⊤ a (by trivial))) = a := by
  subst b
  exact UnitIdealReesCoordinates.homogeneousCoefficientEquiv_symm_generator A a

private theorem inverse_chartAt (b : reesAlgebra (⊤ : Ideal A))
    (hb : b = reesDegreeOne ⊤ 1 (by trivial))
    (hbd : b ∈ reesGrading (⊤ : Ideal A) 1) :
    (unitIdealBlowupIso A).inv =
      Spec.map (CommRingCat.ofHom (coefficientEquivAt b hb).symm.toRingHom) ≫
        Proj.awayι (reesGrading (⊤ : Ideal A)) b hbd (by decide : 0 < (1 : ℕ)) := by
  subst b
  exact UnitIdealReesCoordinates.inverse_homogeneousChart A

/-- The original tuple morphism has its actual native homogeneous-coordinate chart formula. -/
private theorem affineTupleMap_homogeneousChart (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1) :
    affineTupleMap r a ha =
      Spec.map (CommRingCat.ofHom ((coefficientEquivAt
        (tupleGradedMap r a ha (MvPolynomial.X i))
        ((tupleGradedMap_X r a ha i).trans (by rw [hi]))).symm.toRingHom.comp
          (Away.map (tupleGradedMap r a ha) (MvPolynomial.X i)))) ≫
        Proj.awayι (projectiveSpaceGrading R m) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X R i) (by decide : 0 < (1 : ℕ)) := by
  rw [affineTupleMap_graded, inverse_chartAt
    (tupleGradedMap r a ha (MvPolynomial.X i))
    ((tupleGradedMap_X r a ha i).trans (by rw [hi]))
    ((tupleGradedMap r a ha).map_mem (MvPolynomial.isHomogeneous_X R i)), Category.assoc,
    Proj.awayι_comp_map _ _ (by decide : 0 < (1 : ℕ)) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i), ← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  rfl

/-- The actual original normalized coordinate homomorphism of the SAME tuple map. -/
def chartRingMap (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1) :
    CoordinateRing R i →+* A :=
  ((coefficientEquivAt (tupleGradedMap r a ha (MvPolynomial.X i))
    ((tupleGradedMap_X r a ha i).trans (by rw [hi]))).symm.toRingHom.comp
      (Away.map (tupleGradedMap r a ha) (MvPolynomial.X i))).comp
    (homogeneousChartRatioHom i).toRingHom

/-- The entire original tuple morphism factors through its actual polynomial coordinate chart. -/
theorem affineTupleMap_coordinateChart (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1) :
    affineTupleMap r a ha = Spec.map (CommRingCat.ofHom (chartRingMap r a ha i hi)) ≫
      Alterations.Geometry.Segre.coordinateChartInclusion i := by
  rw [affineTupleMap_homogeneousChart r a ha i hi,
    Alterations.Geometry.Segre.coordinateChartInclusion_eq, ← Category.assoc,
    ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change _ = (coefficientEquivAt (tupleGradedMap r a ha (MvPolynomial.X i))
    ((tupleGradedMap_X r a ha i).trans (by rw [hi]))).symm
    (Away.map (tupleGradedMap r a ha) (MvPolynomial.X i)
      (homogeneousChartRatioHom i (homogeneousChartEquiv i z)))
  rw [show homogeneousChartRatioHom i (homogeneousChartEquiv (R := R) i z) = z from
    (homogeneousChartEquiv (R := R) i).symm_apply_apply z]
  rfl

/-- Each original coordinate ratio is the SAME original a_j, including the pivot. -/
theorem chartRingMap_coordinate (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1)
    (j : Fin (m + 1)) :
    chartRingMap r a ha i hi (coordinateDehomCoord i j) = a j := by
  unfold chartRingMap
  change (coefficientEquivAt _ _).symm
    (Away.map (tupleGradedMap r a ha) (MvPolynomial.X i)
      (homogeneousChartRatioHom i (coordinateDehomCoord i j))) = _
  rw [Alterations.Algebra.Segre.homogeneousChartRatioHom_coordinate, Away.map_mk]
  have h := coefficientEquivAt_generator
    (tupleGradedMap r a ha (MvPolynomial.X i))
    ((tupleGradedMap_X r a ha i).trans (by rw [hi]))
    ((tupleGradedMap r a ha).map_mem (MvPolynomial.isHomogeneous_X R i)) (a j)
  convert h using 2
  congr 1
  exact tupleGradedMap_X r a ha j

/-- The entire actual chart map retains the ORIGINAL coefficient ring map. -/
theorem chartRingMap_C (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1) (c : R) :
    chartRingMap r a ha i hi (MvPolynomial.C c) = r c := by
  have h := affineTupleMap_structure r a ha
  rw [affineTupleMap_coordinateChart r a ha i hi, Category.assoc,
    Alterations.Geometry.Segre.coordinateChartInclusion_structure,
    ← Spec.map_comp] at h
  have hh := Spec.map_injective h
  exact congrArg (fun q : CommRingCat.of R ⟶ CommRingCat.of A => q.hom c) hh

/-- The actual whole original chart homomorphism is polynomial evaluation at SAME a_j. -/
theorem chartRingMap_eq_eval (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1) :
    chartRingMap r a ha i hi = MvPolynomial.eval₂Hom r (fun j : ChartIndex i => a j.1) := by
  classical
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [chartRingMap_C, MvPolynomial.eval₂Hom_C]
  · intro j
    rw [MvPolynomial.eval₂Hom_X']
    simpa only [coordinateDehomCoord, dif_neg j.2] using
      chartRingMap_coordinate r a ha i hi j.1

/-- The SAME accepted Rees morphism has its true original normalized coordinate formula. -/
theorem affineTupleMap_eq_eval_chart (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1) :
    affineTupleMap r a ha =
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom r (fun j : ChartIndex i => a j.1))) ≫
        Alterations.Geometry.Segre.coordinateChartInclusion i := by
  rw [affineTupleMap_coordinateChart r a ha i hi, chartRingMap_eq_eval]

end EnvelopeProperty.GeneratedTupleProjectiveCoordinates
