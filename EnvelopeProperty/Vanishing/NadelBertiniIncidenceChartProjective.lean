import EnvelopeProperty.Vanishing.NadelBertiniIncidenceChartMap
import EnvelopeProperty.Vanishing.NadelBertiniProjectiveFrames
/-! # The original projective incidence is covered by actual unit-pivot polynomial quotient charts -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniIncidenceChartProjective
open NadelBertiniUniversal NadelBertiniProjectiveFrames NadelBertiniRestrictionCover SchemeLineSectionEvaluation
variable {R : Type u} [CommRing R] {m : ℕ} {X : Scheme.{u}}
  (j : X ⟶ Alterations.projectiveSpace R m) [IsClosedImmersion j] (i : Fin (m + 1))

abbrev sourceAffineOpen : X.affineOpens := ⟨sourceOpen j i, sourceOpen_affine j i⟩

abbrev coefficients : Fin (m + 1) → Γ((sourceOpen j i).toScheme, ⊤) :=
  NadelBertiniIncidenceChart.coefficients (projectiveLine j) (sourceAffineOpen j i) (coordinateFrame j i) (projectiveSections j)

theorem pivot_coefficient : coefficients j i i = 1 := by
  change (coordinateFrame j i).hom.app ⊤
    (affinePullbackUnitTop (sourceOpen j i).ι (projectiveLine j) (sectionAtOne (sectionHom j i))) = _
  rw [pullback_sectionAtOne]
  exact congrArg sectionAtOne (coordinateFrame_section j i)

abbrev quotientRing := NadelBertiniIncidenceChartMap.quotientRing
  (projectiveLine j) (sourceAffineOpen j i) (coordinateFrame j i) (projectiveSections j)

def parameterRingMap : parameterRing R m →+* quotientRing j i :=
  NadelBertiniIncidenceChartMap.parameterRingMap (j ≫ Alterations.projectiveSpaceStructure R m)
    (projectiveLine j) (sourceAffineOpen j i) (coordinateFrame j i) (projectiveSections j)

def map : Spec (.of (quotientRing j i)) ⟶ projectiveIncidence j :=
  NadelBertiniIncidenceChartMap.map (j ≫ Alterations.projectiveSpaceStructure R m)
    (projectiveLine j) ((MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) (0 : Fin (m + 1)) 1).pullback j)
    (sourceAffineOpen j i) (coordinateFrame j i) (projectiveSections j)

instance map_isOpenImmersion : IsOpenImmersion (map j i) :=
  NadelBertiniIncidenceChartMap.map_isOpenImmersion _ _ _ _ _ _

theorem map_parameter : map j i ≫ projectiveToParameters j = Spec.map (CommRingCat.ofHom (parameterRingMap j i)) :=
  NadelBertiniIncidenceChartMap.map_parameter _ _ _ _ _ _

theorem map_opensRange : (map j i).opensRange =
    (incidenceIdeal (j ≫ Alterations.projectiveSpaceStructure R m) (projectiveLine j)
      ((MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) (0 : Fin (m + 1)) 1).pullback j) (projectiveSections j)).subschemeι ⁻¹ᵁ
      NadelBertiniIncidenceChart.productOpen (j ≫ Alterations.projectiveSpaceStructure R m) (sourceAffineOpen j i) :=
  NadelBertiniIncidenceChartMap.map_opensRange _ _ _ _ _ _

omit i in
theorem maps_cover (z : projectiveIncidence j) : ∃ i y, map j i y = z := by
  have hz : j ((projectiveToSource j) z) ∈ ⨆ i : Fin (m + 1), MvPolynomial.coordinateOpen (R := R) i := by
    rw [MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hz
  have hmem : z ∈ (map j i).opensRange := by
    rw [map_opensRange]
    exact hi
  change ∃ y, map j i y = z at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨i, y, hy⟩
end EnvelopeProperty.Vanishing.NadelBertiniIncidenceChartProjective
