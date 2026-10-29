import EnvelopeProperty.ReesProjection
import Mathlib.RingTheory.MvPolynomial.Ideal

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.PolynomialProj
variable (A ι : Type u) [CommRing A]

/-- The true whole original variable ideal, without any radical replacement. -/
theorem irrelevant_eq_span_X :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule ι A)).toIdeal =
      Ideal.span (Set.range (MvPolynomial.X : ι → MvPolynomial ι A)) := by
  apply le_antisymm
  · apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
    intro d hd F hF
    change F ∈ MvPolynomial.idealOfVars ι A
    rw [← pow_one (MvPolynomial.idealOfVars ι A), MvPolynomial.mem_pow_idealOfVars_iff]
    intro m hm
    have he := (show F.IsHomogeneous d from hF).degree_eq_sum_deg_support hm
    change 1 ≤ ∑ i ∈ m.support, m i
    rw [← he]
    exact hd
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact HomogeneousIdeal.mem_irrelevant_of_mem _ (show 0 < (1 : ℕ) by decide)
      (MvPolynomial.isHomogeneous_X A i)

end EnvelopeProperty.PolynomialProj

namespace EnvelopeProperty.ReesPresentation
variable {A ι : Type u} [CommRing A] (g : ι → A)

/-- The original quotient generator ideal is EXACTLY the actual irrelevant ideal. -/
theorem irrelevant_eq_span_generators :
    (HomogeneousIdeal.irrelevant (ReesChart.grading g)).toIdeal =
      Ideal.span (Set.range (ReesChart.generator g)) := by
  apply le_antisymm
  · apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
    intro d hd q hq
    obtain ⟨F, hF, he⟩ := Submodule.mem_map.mp hq
    have hvar : F ∈ Ideal.span (Set.range (MvPolynomial.X : ι → MvPolynomial ι A)) := by
      rw [← PolynomialProj.irrelevant_eq_span_X A ι]
      exact HomogeneousIdeal.mem_irrelevant_of_mem _ hd hF
    have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (kernel g)) hvar
    rw [Ideal.map_span, ← Set.range_comp] at hm
    exact he ▸ hm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact HomogeneousIdeal.mem_irrelevant_of_mem _ (show 0 < (1 : ℕ) by decide)
      (ReesChart.generator_mem g i)

/-- The ACTUAL original coordinate charts form a genuine affine open cover. -/
def coordinateAffineOpenCover : (Scheme g).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (ReesChart.grading g) (ReesChart.generator g)
    (ReesChart.generator_mem g) (fun _ => show 0 < (1 : ℕ) by decide)
    (irrelevant_eq_span_generators g).le

/-- Every cover component map is the whole original chart immersion. -/
theorem coordinateAffineOpenCover_f (j : ι) :
    (coordinateAffineOpenCover g).f j = chartImmersion g j := rfl

/-- The true original chart morphisms are open immersions. -/
instance instIsOpenImmersion_chartImmersion (j : ι) : IsOpenImmersion (chartImmersion g j) := by
  exact (coordinateAffineOpenCover g).openCover.map_prop j

/-- An ORIGINAL zero coefficient kills the entire actual quotient variable. -/
theorem generator_eq_zero_of_eq_zero {j : ι} (hj : g j = 0) :
    ReesChart.generator g j = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change presentation g (MvPolynomial.X j) = 0
  simp only [presentation_X, hj, Polynomial.C_0, zero_mul]

/-- The actual nonzero original coefficients still give a genuine affine open cover. -/
def nonzeroCoordinateAffineOpenCover : (Scheme g).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (ReesChart.grading g)
    (fun j : {i // g i ≠ 0} => ReesChart.generator g j.1)
    (fun j => ReesChart.generator_mem g j.1) (fun _ => show 0 < (1 : ℕ) by decide) (by
      rw [irrelevant_eq_span_generators]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases hi : g i = 0
      · rw [generator_eq_zero_of_eq_zero g hi]
        exact Ideal.zero_mem _
      · exact Ideal.subset_span ⟨⟨i, hi⟩, rfl⟩)

/-- Every actual nonzero-coordinate cover map is the original full chart immersion. -/
theorem nonzeroCoordinateAffineOpenCover_f (j : {i // g i ≠ 0}) :
    (nonzeroCoordinateAffineOpenCover g).f j = chartImmersion g j.1 := rfl

end EnvelopeProperty.ReesPresentation
