/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.PrincipalCoverCharts
import EnvelopeProperty.Char0.ActualReesTree

/-!
# Actual finite principal-open covers as Rees chart covers

A finite family generating the unit ideal gives literal principal-localization
Rees charts whose actual open immersions cover the original spectrum. These
nodes attach genuine principal refinements to the already realized blowup tree.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory
open scoped Classical

universe u

variable {B K : Type u} [CommRing B] [Field K] [Algebra B K]

/-- The original inclusion chart map factors through the actual principal localization isomorphism. -/
theorem principalReesChartMap_eq (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (hg : Ideal.span (Set.range g) = ⊤) (i : Fin n) (hi : g i ≠ 0) :
    subalgebraSpecMap (le_reesTreeChart C g i) =
      Spec.map (principalCoverLocalizationEquiv C g hg i hi).toCommRingCatIso.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away (g i)))) := by
  rw [subalgebraSpecMap, ← Spec.map_comp]
  congr 1
  ext c
  exact congrArg (fun z : reesTreeChart C g i => (z : K))
    (principalCoverLocalizationEquiv_algebraMap C g hg i hi c).symm

/-- The principal-cover Rees inclusion is an actual open immersion. -/
theorem isOpenImmersion_principalReesChartMap (C : Subalgebra B K) {n : ℕ}
    (g : Fin n → C) (hg : Ideal.span (Set.range g) = ⊤) (i : Fin n) (hi : g i ≠ 0) :
    IsOpenImmersion (subalgebraSpecMap (le_reesTreeChart C g i)) := by
  rw [principalReesChartMap_eq C g hg i hi]
  infer_instance

/-- Its actual image is exactly the original basic open. -/
theorem range_principalReesChartMap (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (hg : Ideal.span (Set.range g) = ⊤) (i : Fin n) (hi : g i ≠ 0) :
    Set.range (subalgebraSpecMap (le_reesTreeChart C g i)) =
      (PrimeSpectrum.basicOpen (g i)).1 := by
  rw [principalReesChartMap_eq C g hg i hi]
  have hloc := PrimeSpectrum.localization_away_comap_range (Localization.Away (g i)) (g i)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    apply hloc.le
    exact ⟨_, rfl⟩
  · intro hx
    obtain ⟨y, hy⟩ := hloc.ge hx
    obtain ⟨z, hz⟩ := spec_map_iso_surjective
      (principalCoverLocalizationEquiv C g hg i hi).toCommRingCatIso y
    refine ⟨z, ?_⟩
    rw [Scheme.Hom.comp_apply, hz]
    exact hy

/-- The actual nonzero unit-family Rees charts cover every point of the original spectrum. -/
theorem exists_mem_principalReesChartMap (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (hg : Ideal.span (Set.range g) = ⊤) (x : Spec (.of C)) :
    ∃ (i : {i : Fin n // g i ≠ 0}) (p : Spec (.of (reesTreeChart C g i))),
      subalgebraSpecMap (le_reesTreeChart C g i) p = x := by
  have hgen : ∃ i, g i ∉ x.asIdeal := by
    by_contra h
    push Not at h
    have hspan : Ideal.span (Set.range g) ≤ x.asIdeal := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact h i
    rw [hg] at hspan
    exact x.isPrime.ne_top (top_le_iff.mp hspan)
  obtain ⟨i, hi⟩ := hgen
  have hi0 : g i ≠ 0 := fun hzero => hi (hzero ▸ x.asIdeal.zero_mem)
  have hx : x ∈ Set.range (subalgebraSpecMap (le_reesTreeChart C g i)) := by
    rw [range_principalReesChartMap C g hg i hi0]
    exact hi
  obtain ⟨p, hp⟩ := hx
  exact ⟨⟨i, hi0⟩, p, hp⟩

/-- The actual principal refinement is a finite affine open cover with literal Rees chart rings. -/
def principalReesOpenCover (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (hg : Ideal.span (Set.range g) = ⊤) : (Spec (.of C)).AffineOpenCover where
  I₀ := {i : Fin n // g i ≠ 0}
  X i := .of (reesTreeChart C g i)
  f i := subalgebraSpecMap (le_reesTreeChart C g i)
  map_prop i := isOpenImmersion_principalReesChartMap C g hg i i.2
  idx x := (exists_mem_principalReesChartMap C g hg x).choose
  covers x := (exists_mem_principalReesChartMap C g hg x).choose_spec

/-- Its actual nonzero generator index set is finite. -/
instance finite_principalReesOpenCover_index (C : Subalgebra B K) {n : ℕ}
    (g : Fin n → C) (hg : Ideal.span (Set.range g) = ⊤) :
    Finite (principalReesOpenCover C g hg).I₀ := by
  change Finite {i : Fin n // g i ≠ 0}
  infer_instance

/-- The genuine principal refinement family has a nonzero generator, internally. -/
theorem exists_nonzero_of_span_eq_top (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (hg : Ideal.span (Set.range g) = ⊤) : ∃ i, g i ≠ 0 := by
  obtain ⟨i, _, _⟩ := exists_mem_principalReesChartMap C g hg ⟨⊥, Ideal.isPrime_bot⟩
  exact ⟨i.1, i.2⟩

end EnvelopeProperty.Char0
