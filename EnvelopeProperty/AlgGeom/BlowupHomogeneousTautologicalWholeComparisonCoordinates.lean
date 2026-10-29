import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalFractionBases
import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalLine

/-! # The same original Rees map on its actual ratio tuples -/

noncomputable section
open AlgebraicGeometry CategoryTheory
open Alterations Alterations.Geometry.ProjectiveIdeal
  Alterations.Geometry.BlowupProjectiveEmbedding
universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine

variable {R A : Type u} [CommRing R] [CommRing A] [IsDomain A] {m : ℕ}

/-- The actual specified original generator ratios in the native fraction ring;
the target still has the original `m+1` coordinates. -/
def originalFractionRatioTuple (I : Ideal A) (g : Fin (m+1) → A)
    (hspan : Ideal.span (Set.range g) = I) (i : Fin (m+1)) :
    Fin (m+1) → affineBlowupFractionChart I (g i) :=
  fun j => affineBlowupChartRatio I (g i) (g j) (generator_mem I g hspan j)

/-- The original pivot ratio equals one in the actual fraction-chart ring. -/
theorem originalFractionRatioTuple_pivot (I : Ideal A) (g : Fin (m+1) → A)
    (hspan : Ideal.span (Set.range g) = I) (i : Fin (m+1)) (hi : g i ≠ 0) :
    originalFractionRatioTuple I g hspan i i = 1 := by
  apply Subtype.ext
  change algebraMap A (FractionRing A) (g i) / algebraMap A (FractionRing A) (g i) = 1
  exact div_self ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr hi)

/-- The actual original ratio tuple spans the unit ideal, internally derived
from its actual nonzero original pivot. -/
theorem originalFractionRatioTuple_span (I : Ideal A) (g : Fin (m+1) → A)
    (hspan : Ideal.span (Set.range g) = I) (i : Fin (m+1)) (hi : g i ≠ 0) :
    Ideal.span (Set.range (originalFractionRatioTuple I g hspan i)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hmem : originalFractionRatioTuple I g hspan i i ∈
      Ideal.span (Set.range (originalFractionRatioTuple I g hspan i)) :=
    Ideal.subset_span ⟨i, rfl⟩
  rwa [originalFractionRatioTuple_pivot I g hspan i hi] at hmem

/-- The whole restriction of the original specified-generator Rees morphism
equals the actual original ratio-tuple map, with the same coefficient map and
the same projective target. No map-matching hypothesis is supplied. -/
theorem affineGeneratorMap_eq_originalFractionRatioTuple
    (r : R →+* A) (I : Ideal A) (g : Fin (m+1) → A)
    (hspan : Ideal.span (Set.range g) = I) (i : Fin (m+1)) (hi : g i ≠ 0) :
    affineBlowupChartInclusion I (g i) (generator_mem I g hspan i) hi ≫
        affineProjectiveMap r I g hspan =
      Alterations.Geometry.FiniteProjective.affineTupleMap
        ((algebraMap A (affineBlowupFractionChart I (g i))).comp r)
        (originalFractionRatioTuple I g hspan i)
        (originalFractionRatioTuple_span I g hspan i hi) := by
  have hRees := affineGeneratorChartReadback r I g hspan i hi
  have hTuple := GeneratedTupleProjectiveCoordinates.affineTupleMap_eq_eval_chart
    ((algebraMap A (affineBlowupFractionChart I (g i))).comp r)
    (originalFractionRatioTuple I g hspan i)
    (originalFractionRatioTuple_span I g hspan i hi) i
    (originalFractionRatioTuple_pivot I g hspan i hi)
  exact hRees.trans hTuple.symm

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
