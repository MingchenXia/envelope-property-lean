import EnvelopeProperty.ReesBlowupScheme
import EnvelopeProperty.ReesChart

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ReesPresentation
variable {A ι : Type u} [CommRing A] (g : ι → A)

private local instance actualChartAlgebra (j : ι) : Algebra A (ReesChart.Chart g j) :=
  ReesChart.chartAlgebra g j

/-- The real original quotient degree-zero chart immersion into its genuine Proj scheme. -/
def chartImmersion (j : ι) : Spec (CommRingCat.of (ReesChart.Chart g j)) ⟶ Scheme g :=
  Proj.awayι (ReesChart.grading g) (ReesChart.generator g j) (ReesChart.generator_mem g j) (by decide)

set_option backward.isDefEq.respectTransparency false in
/-- Every original coefficient is retained in the whole genuine chart structure morphism. -/
theorem chartImmersion_comp_projection (j : ι) :
    chartImmersion g j ≫ projection g =
      Spec.map (CommRingCat.ofHom (ReesChart.coefficients g j)) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule ι A
  let J := homogeneousKernel g
  have hsq := (GradedQuotient.isPullback_awayMap 𝒜 J
    (show 0 < (1 : ℕ) by decide) (MvPolynomial.isHomogeneous_X A j)).w
  change (chartImmersion g j ≫ immersion g) ≫ PolynomialProj.projection A ι = _
  rw [show chartImmersion g j ≫ immersion g =
    Spec.map (CommRingCat.ofHom (Away.map (GradedQuotient.gradedMk 𝒜 J.toIdeal)
      (MvPolynomial.X j))) ≫ Proj.awayι 𝒜 (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X A j) (by decide) from hsq.symm]
  rw [PolynomialProj.projection, Category.assoc,
    ← Category.assoc (Proj.awayι _ _ _ _), Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1

variable [IsDomain A] (j : ι) (hj : g j ≠ 0)

/-- The actual fraction-field generic scheme maps into the original selected Rees chart. -/
def genericLift : Spec (CommRingCat.of (FractionRing A)) ⟶ Scheme g :=
  Spec.map (CommRingCat.ofHom (ReesChart.toFractionRing g j hj).toRingHom) ≫ chartImmersion g j

/-- The whole actual generic lift has exactly the original fraction-field structure map. -/
theorem genericLift_comp_projection :
    genericLift g j hj ≫ projection g =
      Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) := by
  rw [genericLift, Category.assoc, chartImmersion_comp_projection, ← Spec.map_comp]
  congr 1
  ext a
  exact (ReesChart.toFractionRing g j hj).commutes a

include j hj in
set_option backward.isDefEq.respectTransparency false in
/-- Properness and the genuinely constructed point above the original zero prime give surjectivity. -/
theorem projection_surjective [Finite ι] : Function.Surjective (projection g) := by
  let : IsProper (projection g) := projection_isProper g
  let z : PrimeSpectrum (FractionRing A) := ⊥
  let p : PrimeSpectrum A := ⊥
  have hp : projection g (genericLift g j hj z) = p := by
    have he := congrArg (fun f => f z) (genericLift_comp_projection g j hj)
    change (genericLift g j hj ≫ projection g) z = p
    rw [he]
    apply PrimeSpectrum.ext
    ext a
    change algebraMap A (FractionRing A) a = 0 ↔ a = 0
    exact map_eq_zero_iff _ (IsFractionRing.injective A (FractionRing A))
  have hs : closure ({p} : Set (Spec (CommRingCat.of A))) ⊆ Set.range (projection g) :=
    closure_minimal (Set.singleton_subset_iff.mpr ⟨genericLift g j hj z, hp⟩)
      (projection g).isClosedMap.isClosed_range
  change closure ({p} : Set (PrimeSpectrum A)) ⊆ Set.range (projection g) at hs
  rw [PrimeSpectrum.closure_singleton, show p.asIdeal = ⊥ from rfl,
    PrimeSpectrum.zeroLocus_bot] at hs
  intro x
  exact hs (Set.mem_univ x)

end EnvelopeProperty.ReesPresentation
