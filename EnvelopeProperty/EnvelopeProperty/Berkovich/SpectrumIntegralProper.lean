/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumFilters
import EnvelopeProperty.Berkovich.SpectrumIntegral

/-!
# Integral maps are proper for arbitrary real seminorm spectra

Convergent pullback ultrafilters give eventual bounds on every integral element
through its actual monic equation. The closed evaluation embedding then produces
a source limit. This proves the genuine proper-map criterion, for absolute and
prescribed-base spectra, without finite type or local compactness hypotheses.
-/

open scoped NNReal Topology
open Topology Filter

noncomputable section

namespace EnvelopeProperty.Berkovich

namespace Spectrum

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Integral pullback is proper by actual ultrafilter lifting, for arbitrary
commutative rings and without a local-compactness hypothesis. -/
theorem isProperMap_comap_of_isIntegral (φ : A →+* B) (hφ : φ.IsIntegral) :
    IsProperMap (comap φ) := by
  classical
  rw [isProperMap_iff_ultrafilter_of_t2]
  refine ⟨continuous_comap φ, fun {U} {x} hx => ?_⟩
  have hcoeff : ∀ a : A, ∃ M : ℝ≥0, ∀ᶠ y in (U : Filter (Spectrum B)), y.val (φ a) ≤ M := by
    intro a
    have ht : Tendsto (fun y : Spectrum B => y.val (φ a)) U (𝓝 (x.val a)) :=
      ((continuous_abs a).tendsto x).comp hx
    obtain ⟨M, hM⟩ := ht.isBoundedUnder_le
    exact ⟨M, hM⟩
  have hbound : ∀ b : B, ∃ M : ℝ≥0, ∀ᶠ y in (U : Filter (Spectrum B)), y.val b ≤ M := by
    intro b
    obtain ⟨p, hp, hpb⟩ := hφ b
    choose M hM using fun i : Fin p.natDegree => hcoeff (p.coeff i)
    have hall : ∀ᶠ y in (U : Filter (Spectrum B)),
        ∀ i : Fin p.natDegree, y.val (φ (p.coeff i)) ≤ M i := eventually_all.2 hM
    refine ⟨max 1 (Finset.univ.sup M), hall.mono fun y hy => ?_⟩
    refine EnvelopeProperty.Valuation.le_of_monic_eval₂_eq_zero y.val φ hp hpb
      (le_max_left _ _) fun i hi => ?_
    exact (hy ⟨i, hi⟩).trans
      ((Finset.le_sup (Finset.mem_univ (⟨i, hi⟩ : Fin p.natDegree))).trans (le_max_right _ _))
  exact exists_ultrafilter_limit_of_bounded_evaluations U hbound

/-- Integral spectrum pullbacks are closed as a consequence of the proved properness criterion. -/
theorem isClosedMap_comap_of_isIntegral (φ : A →+* B) (hφ : φ.IsIntegral) :
    IsClosedMap (comap φ) :=
  (isProperMap_comap_of_isIntegral φ hφ).isClosedMap

end Spectrum

namespace RelativeSpectrum

variable {R : Type*} [CommRing R] {v : Valuation R ℝ≥0}
    {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Properness of integral pullback is retained on any prescribed-base spectrum. -/
theorem isProperMap_comap_of_isIntegral (φ : A →ₐ[R] B) (hφ : φ.toRingHom.IsIntegral) :
    IsProperMap (comap (v := v) φ) := by
  have hcomp : IsProperMap
      (((↑) : RelativeSpectrum v A → Spectrum A) ∘ comap (v := v) φ) :=
    (Spectrum.isProperMap_comap_of_isIntegral φ.toRingHom hφ).comp
      isClosedEmbedding_subtypeVal.isProperMap
  exact isProperMap_of_comp_of_inj (continuous_comap φ) continuous_subtype_val hcomp
    Subtype.val_injective

/-- Relative integral pullback is closed for every prescribed base seminorm. -/
theorem isClosedMap_comap_of_isIntegral (φ : A →ₐ[R] B) (hφ : φ.toRingHom.IsIntegral) :
    IsClosedMap (comap (v := v) φ) :=
  (isProperMap_comap_of_isIntegral φ hφ).isClosedMap

end RelativeSpectrum

end EnvelopeProperty.Berkovich
