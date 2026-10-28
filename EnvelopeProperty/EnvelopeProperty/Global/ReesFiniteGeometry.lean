/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.ReesFiniteCoordinateCharts
import EnvelopeProperty.ReesChartAway
import EnvelopeProperty.ReesGoodOpenDensity
import EnvelopeProperty.ProperBirationalSections
import EnvelopeProperty.ProjectiveReduced
import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# Genuine geometric source properties of the finite-coordinate Rees scheme

The same original quotient has a true generic point, reduced and integral
scheme, and an actual dense-open inverse over every nonzero original
coefficient. No birational or geometric-connectedness certificate is supplied.
-/

open scoped Classical nonZeroDivisors
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ReesPresentation
variable {A : Type u} [CommRing A] [IsDomain A] {n : ℕ} (g : Fin (n + 1) → A)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private local instance finiteChartAlgebra (l : Fin (n + 1)) : Algebra A (ReesChart.Chart g l) :=
  ReesChart.chartAlgebra g l

/-- The very original finite-coordinate Rees kernel quotient is a domain. -/
theorem fcFinite_quotient_isDomain : IsDomain (ReesChart.Quotient g) :=
  (quotientEquiv g).toRingEquiv.toMulEquiv.isDomain _

/-- The actual original quotient Proj is genuinely reduced. -/
theorem fcFinite_scheme_isReduced : IsReduced (fcFiniteScheme g) := by
  let := fcFinite_quotient_isDomain g
  exact proj_isReduced (ReesChart.grading g)

omit [IsDomain A] in
/-- A nonzero original coefficient gives a nonzero original quotient variable. -/
theorem fcFinite_generator_ne_zero (l : Fin (n + 1)) (hl : g l ≠ 0) :
    ReesChart.generator g l ≠ 0 := by
  intro h
  apply hl
  simpa only [ReesChart.quotientEvaluation_generator, map_zero] using
    congrArg (quotientEvaluation g) h

/-- The actual zero homogeneous prime is a true original scheme point. -/
def fcFiniteGenericPoint (l : Fin (n + 1)) (hl : g l ≠ 0) : fcFiniteScheme g := by
  let : IsDomain (MvPolynomial (Fin (n + 1)) A ⧸ (homogeneousKernel g).toIdeal) :=
    fcFinite_quotient_isDomain g
  refine ⟨⊥, ?_, ?_⟩
  · exact Ideal.isPrime_bot
  · intro h
    apply fcFinite_generator_ne_zero g l hl
    exact (show ReesChart.generator g l ∈ (⊥ : HomogeneousIdeal (ReesChart.grading g)) from
      h (HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < (1 : ℕ))
        (ReesChart.generator_mem g l)))

/-- The genuine zero-prime point specializes to every original Rees point. -/
theorem fcFiniteGenericPoint_isGenericPoint (l : Fin (n + 1)) (hl : g l ≠ 0) :
    IsGenericPoint (fcFiniteGenericPoint g l hl) Set.univ := by
  let : GradedRing (ReesChart.grading g) := ReesChart.quotientGradedRing g
  change closure ({fcFiniteGenericPoint g l hl} : Set (fcFiniteScheme g)) = Set.univ
  apply Set.eq_univ_of_forall
  intro x
  apply (ProjectiveSpectrum.le_iff_mem_closure (ReesChart.grading g) _ x).mp
  change (⊥ : HomogeneousIdeal (ReesChart.grading g)) ≤ x.asHomogeneousIdeal
  exact bot_le

/-- Every actual nonzero original centre gives a genuinely integral Rees scheme. -/
theorem fcFinite_scheme_isIntegral (l : Fin (n + 1)) (hl : g l ≠ 0) :
    IsIntegral (fcFiniteScheme g) := by
  let := fcFinite_scheme_isReduced g
  let : IrreducibleSpace (fcFiniteScheme g) := (irreducibleSpace_def _).mpr
    (fcFiniteGenericPoint_isGenericPoint g l hl).isIrreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced _

omit [IsDomain A] in
/-- The original chart-to-coefficient-localization map is a genuine open immersion. -/
theorem fcFinite_isOpenImmersion_specMap_toAway (l : Fin (n + 1)) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (ReesChart.toAway g l).toRingHom)) := by
  let : Algebra (ReesChart.Chart g l) (Localization.Away (g l)) :=
    (ReesChart.toAway g l).toRingHom.toAlgebra
  let : IsLocalization.Away (algebraMap A (ReesChart.Chart g l) (g l))
      (Localization.Away (g l)) := ReesChart.toAway_isLocalization g l
  exact IsOpenImmersion.of_isLocalization (algebraMap A (ReesChart.Chart g l) (g l))

/-- The genuine coefficient principal open maps into the same original Rees scheme. -/
def fcFiniteGoodOpenLift (l : Fin (n + 1)) :
    Spec (CommRingCat.of (Localization.Away (g l))) ⟶ fcFiniteScheme g :=
  Spec.map (CommRingCat.ofHom (ReesChart.toAway g l).toRingHom) ≫ fcFiniteChartImmersion g l

/-- The actual original good-open morphism is an open immersion. -/
instance fcFiniteGoodOpenLift_isOpenImmersion (l : Fin (n + 1)) :
    IsOpenImmersion (fcFiniteGoodOpenLift g l) := by
  let := fcFinite_isOpenImmersion_specMap_toAway g l
  unfold fcFiniteGoodOpenLift
  infer_instance

omit [IsDomain A] in
/-- The actual whole coefficient triangle of the true good-open lift. -/
theorem fcFiniteGoodOpenLift_comp_projection (l : Fin (n + 1)) :
    fcFiniteGoodOpenLift g l ≫ fcFiniteProjection g =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (g l)))) := by
  rw [fcFiniteGoodOpenLift, Category.assoc, fcFiniteChartImmersion_comp_projection,
    ← Spec.map_comp]
  congr 1
  ext a
  exact (ReesChart.toAway g l).commutes a

/-- The actual good-open lift has dense range for every nonzero original coefficient. -/
theorem fcFiniteGoodOpenLift_denseRange (l : Fin (n + 1)) (hl : g l ≠ 0) :
    DenseRange (fcFiniteGoodOpenLift g l) := by
  let := fcFinite_scheme_isIntegral g l hl
  let : IsDomain (Localization.Away (g l)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away (g l))
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hl))
  exact (fcFiniteGoodOpenLift g l).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _

private local instance finiteBaseOpenImmersion (l : Fin (n + 1)) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (g l))))) :=
  IsOpenImmersion.of_isLocalization (g l)

/-- Actual good-open morphisms and their real dense ranges construct the birational inverse. -/
def fcFiniteGeneratorPartialIso (l : Fin (n + 1)) (hl : g l ≠ 0) :
    Scheme.PartialIso (fcFiniteScheme g) (Spec (CommRingCat.of A)) where
  source := (fcFiniteGoodOpenLift g l).opensRange
  dense_source := fcFiniteGoodOpenLift_denseRange g l hl
  target := (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (g l))))).opensRange
  dense_target := by
    change Dense (Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away (g l)))))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (g l)) (g l)]
    exact dense_basicOpen_of_mem_nonZeroDivisors (g l) (mem_nonZeroDivisors_iff_ne_zero.mpr hl)
  iso := (fcFiniteGoodOpenLift g l).isoOpensRange.symm ≪≫
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (g l))))).isoOpensRange

/-- The genuine dense-open inverse preserves the entire original coefficient projection. -/
theorem fcFiniteGeneratorPartialIso_isOver (l : Fin (n + 1)) (hl : g l ≠ 0) :
    (fcFiniteGeneratorPartialIso g l hl).IsOver (fcFiniteProjection g)
      (𝟙 (Spec (CommRingCat.of A))) := by
  change ((fcFiniteGoodOpenLift g l).isoOpensRange.inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (g l))))).isoOpensRange.hom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (g l))))).opensRange.ι ≫
        𝟙 _ = (fcFiniteGoodOpenLift g l).opensRange.ι ≫ fcFiniteProjection g
  simp only [Category.comp_id, Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  rw [← fcFiniteGoodOpenLift_comp_projection g l, ← Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp]

/-- The actual same original finite Rees projection is birational over its coefficient base. -/
theorem fcFinite_birationalOver_projection (l : Fin (n + 1)) (hl : g l ≠ 0) :
    Scheme.BirationalOver (fcFiniteProjection g) (𝟙 (Spec (CommRingCat.of A))) :=
  ⟨fcFiniteGeneratorPartialIso g l hl, fcFiniteGeneratorPartialIso_isOver g l hl⟩

/-- Actual normality, properness and the constructed birational inverse derive the
whole original coefficient-map bijection on global sections. -/
theorem fcFinite_coefficientMap_bijective [IsIntegrallyClosed A]
    (l : Fin (n + 1)) (hl : g l ≠ 0) :
    Function.Bijective (ProperBirationalSections.coefficientMap (fcFiniteProjection g)) := by
  let := fcFinite_scheme_isReduced g
  exact ProperBirationalSections.coefficientMap_bijective_of_proper_birationalOver
    (fcFiniteProjection g) (fcFinite_birationalOver_projection g l hl)

end EnvelopeProperty.ReesPresentation
