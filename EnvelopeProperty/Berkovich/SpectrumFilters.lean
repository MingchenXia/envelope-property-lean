/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumTopology

/-!
# Coordinate-bounded ultrafilter limits

A closed subspace of a product of nonnegative real coordinates contains the
limit of any ultrafilter whose coordinates are individually eventually bounded.
This applies to absolute spectra and every prescribed-base relative spectrum;
no simultaneous eventual bound across all ring elements is assumed.
-/

open scoped NNReal Topology
open Topology Filter

noncomputable section

namespace EnvelopeProperty

/-- A closed evaluation embedding contains the limit of every ultrafilter with
individually eventually bounded coordinates. -/
theorem exists_ultrafilter_limit_of_bounded_coordinates
    {X ι : Type*} [TopologicalSpace X] {E : X → ι → ℝ≥0}
    (hE : IsClosedEmbedding E) (U : Ultrafilter X)
    (hM : ∀ a : ι, ∃ M : ℝ≥0, ∀ᶠ z in (U : Filter X), E z a ≤ M) :
    ∃ z : X, (U : Filter X) ≤ 𝓝 z := by
  classical
  choose M hM using hM
  have hlim : ∀ a : ι, ∃ r : ℝ≥0, Tendsto (fun z : X => E z a) U (𝓝 r) := by
    intro a
    have hmem : Set.Icc (0 : ℝ≥0) (M a) ∈ Ultrafilter.map (fun z : X => E z a) U := by
      change ∀ᶠ z in (U : Filter X), E z a ∈ Set.Icc 0 (M a)
      exact (hM a).mono fun z hz => ⟨zero_le, hz⟩
    obtain ⟨r, _, hr⟩ := isCompact_Icc.ultrafilter_le_nhds' _ hmem
    exact ⟨r, hr⟩
  choose w hw using hlim
  have ht : Tendsto E U (𝓝 w) := tendsto_pi_nhds.2 hw
  have hm : w ∈ Set.range E := hE.isClosed_range.mem_of_tendsto ht
    (Eventually.of_forall fun z => ⟨z, rfl⟩)
  obtain ⟨z, rfl⟩ := hm
  exact ⟨z, hE.tendsto_nhds_iff.2 ht⟩

namespace Berkovich

namespace Spectrum

variable {A : Type*} [CommRing A]

/-- Every ultrafilter with eventually bounded ring evaluations has a seminorm limit. -/
theorem exists_ultrafilter_limit_of_bounded_evaluations (U : Ultrafilter (Spectrum A))
    (hM : ∀ a : A, ∃ M : ℝ≥0, ∀ᶠ z in (U : Filter (Spectrum A)), z.val a ≤ M) :
    ∃ z : Spectrum A, (U : Filter (Spectrum A)) ≤ 𝓝 z :=
  exists_ultrafilter_limit_of_bounded_coordinates isClosedEmbedding_toFun U hM

end Spectrum

namespace RelativeSpectrum

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {v : Valuation R ℝ≥0}

/-- Prescribing the base seminorm retains limits of evaluation-bounded ultrafilters. -/
theorem exists_ultrafilter_limit_of_bounded_evaluations (U : Ultrafilter (RelativeSpectrum v A))
    (hM : ∀ a : A, ∃ M : ℝ≥0,
      ∀ᶠ z in (U : Filter (RelativeSpectrum v A)), z.1.val a ≤ M) :
    ∃ z : RelativeSpectrum v A, (U : Filter (RelativeSpectrum v A)) ≤ 𝓝 z :=
  exists_ultrafilter_limit_of_bounded_coordinates
    (Spectrum.isClosedEmbedding_toFun.comp isClosedEmbedding_subtypeVal) U hM

end RelativeSpectrum

end Berkovich

end EnvelopeProperty
