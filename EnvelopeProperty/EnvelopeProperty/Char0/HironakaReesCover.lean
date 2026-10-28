/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.HironakaCharts
import Hironaka.Scheme.BlowUp.AffineBlowUp.Chart

/-!
# The actual finite scheme cover by Rees ratio charts

The previously checked chart-ring equivalence now induces actual open immersions into the
Rees-Proj blowup. Its nonzero-denominator charts form a finite actual affine cover. This is the
one-step scheme transport used in the recursive finite-tree adapter.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory
open scoped Classical

universe u

variable {B K : Type u} [CommRing B] [Field K] [Algebra B K]

/-- The actual open immersion from a nonzero ratio chart into the affine Rees-Proj blowup. -/
def reesAffineBlowUpChart (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i : Fin n) (hi : g i ≠ 0) :
    Spec (.of (reesTreeChart C g i)) ⟶ affineBlowUp (Ideal.span (Set.range g)) :=
  Spec.map (affineBlowUpReesChartEquiv C g i hi).toCommRingCatIso.hom ≫
    affineBlowUp.chart (Ideal.span (Set.range g)) ⟨g i, Ideal.subset_span ⟨i, rfl⟩⟩

/-- The ratio chart has its actual scheme-theoretic open-immersion structure. -/
instance isOpenImmersion_reesAffineBlowUpChart (C : Subalgebra B K) {n : ℕ}
    (g : Fin n → C) (i : Fin n) (hi : g i ≠ 0) :
    IsOpenImmersion (reesAffineBlowUpChart C g i hi) := by
  unfold reesAffineBlowUpChart
  infer_instance

/-- The chart morphism to the original affine scheme is induced by the algebra inclusion. -/
theorem reesAffineBlowUpChart_π (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i : Fin n) (hi : g i ≠ 0) :
    reesAffineBlowUpChart C g i hi ≫ affineBlowUp.π (Ideal.span (Set.range g)) =
      Spec.map (CommRingCat.ofHom (reesTreeChartIncl C g i).toRingHom) := by
  rw [reesAffineBlowUpChart, Category.assoc, affineBlowUp.chart_π, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact affineBlowUpReesChartEquiv_algebraMap C g i hi c

/-- A chart containing a point cannot have zero denominator: that denominator is a
nonzerodivisor in its chart algebra. -/
theorem affineBlowUp_chart_denominator_ne_zero {R : Type u} [CommRing R] (I : Ideal R)
    (a : I) (p : Spec (.of (affineBlowUpAlgebra I a))) : (a : R) ≠ 0 := by
  have : Nontrivial (affineBlowUpAlgebra I a) := PrimeSpectrum.nontrivial p
  intro ha
  have hreg := affineBlowUpAlgebra.algebraMap_mem_nonZeroDivisors (I := I) (a := (a : R))
  have hzero : algebraMap R (affineBlowUpAlgebra I a) a = 0 := by rw [ha, map_zero]
  exact zero_notMem_nonZeroDivisors (hzero ▸ hreg)

/-- Contravariance sends a ring isomorphism to a surjective map of actual affine schemes. -/
theorem spec_map_iso_surjective {R S : CommRingCat.{u}} (e : R ≅ S) :
    Function.Surjective (Spec.map e.hom) := by
  have : Surjective (Spec.map e.hom) := inferInstance
  exact (Spec.map e.hom).surjective

/-- Every point of the actual affine blowup lies in a nonzero finite ratio chart. -/
theorem exists_mem_reesAffineBlowUpChart (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (x : affineBlowUp (Ideal.span (Set.range g))) :
    ∃ i : {i : Fin n // g i ≠ 0}, x ∈ Set.range (reesAffineBlowUpChart C g i.1 i.2) := by
  obtain ⟨⟨a, ha⟩, hx⟩ := affineBlowUp.exists_mem_opensRange_chart_of_span_eq
    (Ideal.span (Set.range g)) (Set.range g) rfl x
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨p, hp⟩ := Scheme.Hom.mem_opensRange.mp hx
  have hi : g i ≠ 0 := affineBlowUp_chart_denominator_ne_zero _ _ p
  let e := (affineBlowUpReesChartEquiv C g i hi).toCommRingCatIso
  obtain ⟨q, hq⟩ := spec_map_iso_surjective e p
  refine ⟨⟨i, hi⟩, q, ?_⟩
  change (Spec.map e.hom ≫ affineBlowUp.chart (Ideal.span (Set.range g))
    ⟨g i, Ideal.subset_span ⟨i, rfl⟩⟩) q = x
  rw [Scheme.Hom.comp_apply, hq]
  exact hp

/-- The finite nonzero generator charts, with their actual maps, form an affine open cover. -/
def reesAffineBlowUpOpenCover (C : Subalgebra B K) {n : ℕ} (g : Fin n → C) :
    (affineBlowUp (Ideal.span (Set.range g))).AffineOpenCover where
  I₀ := {i : Fin n // g i ≠ 0}
  X i := .of (reesTreeChart C g i.1)
  f i := reesAffineBlowUpChart C g i.1 i.2
  idx x := (exists_mem_reesAffineBlowUpChart C g x).choose
  covers x := (exists_mem_reesAffineBlowUpChart C g x).choose_spec

/-- Omitting zero denominators preserves finiteness of the actual chart cover. -/
instance finite_reesAffineBlowUpOpenCover_index (C : Subalgebra B K) {n : ℕ}
    (g : Fin n → C) : Finite (reesAffineBlowUpOpenCover C g).I₀ := by
  change Finite {i : Fin n // g i ≠ 0}
  infer_instance

end EnvelopeProperty.Char0
