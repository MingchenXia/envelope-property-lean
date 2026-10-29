/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumTopology
import EnvelopeProperty.Berkovich.ValuationIntegral

/-!
# Compact inverse images under integral maps of seminorm spectra

An integral homomorphism of arbitrary commutative rings induces a pullback map
with compact inverse images of compact sets. Every integral element satisfies
a monic equation, whose coefficients are uniformly bounded on a compact set.
The monic-root estimate then supplies a bound for every evaluation coordinate
of the inverse image, placing it inside a compact coordinate-bounded set.

The same conclusion holds for arbitrary prescribed-base relative spectra.
There are no field, trivial valuation, finite type, or completeness hypotheses.
Fibres are proved compact, without asserting their finiteness or a general
topological properness or closed-map conclusion.
-/

open scoped NNReal Topology
open Topology Set

noncomputable section

namespace EnvelopeProperty.Berkovich

namespace Spectrum

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Every evaluation is bounded above on a compact set in an arbitrary seminorm spectrum. -/
theorem exists_abs_le_of_isCompact {K : Set (Spectrum A)} (hK : IsCompact K) (a : A) :
    ∃ M : ℝ≥0, ∀ x ∈ K, x.val a ≤ M := by
  obtain ⟨M, hM⟩ := (hK.image (continuous_abs a)).bddAbove
  exact ⟨M, fun x hx => hM ⟨x, hx, rfl⟩⟩

/-- A finite collection of evaluations has a common upper bound on a compact set. -/
theorem exists_forall_abs_le_of_isCompact {K : Set (Spectrum A)} (hK : IsCompact K)
    (S : Finset A) : ∃ M : ℝ≥0, K ⊆ {x | ∀ a ∈ S, x.val a ≤ M} := by
  choose M hM using exists_abs_le_of_isCompact hK
  exact ⟨S.sup M, fun x hx a ha => (hM a x hx).trans (Finset.le_sup ha)⟩

/-- An integral element is bounded on the inverse image of every compact set. -/
theorem exists_abs_le_of_isIntegral (φ : A →+* B) {b : B} (hb : φ.IsIntegralElem b)
    {K : Set (Spectrum A)} (hK : IsCompact K) :
    ∃ M : ℝ≥0, ∀ y : Spectrum B, comap φ y ∈ K → y.val b ≤ M := by
  classical
  obtain ⟨p, hp, hpb⟩ := hb
  obtain ⟨M, hM⟩ := exists_forall_abs_le_of_isCompact hK
    ((Finset.range p.natDegree).image p.coeff)
  refine ⟨max 1 M, fun y hy => ?_⟩
  refine EnvelopeProperty.Valuation.le_of_monic_eval₂_eq_zero y.val φ hp hpb
    (le_max_left _ _) fun i hi => ?_
  exact (hM hy (p.coeff i) (Finset.mem_image_of_mem _ (Finset.mem_range.2 hi))).trans
    (le_max_right _ _)

/-- Integral ring maps have compact inverse images of compact sets, without finite type. -/
theorem isCompact_preimage_comap_of_isIntegral (φ : A →+* B) (hφ : φ.IsIntegral)
    {K : Set (Spectrum A)} (hK : IsCompact K) : IsCompact (comap φ ⁻¹' K) := by
  choose M hM using fun b : B => exists_abs_le_of_isIntegral φ (hφ b) hK
  refine (isCompact_setOf_forall_val_le M).of_isClosed_subset
    (hK.isClosed.preimage (continuous_comap φ)) ?_
  exact fun y hy b => hM b y hy

/-- Every fibre of an integral ring-map pullback is compact. -/
theorem isCompact_preimage_singleton_of_isIntegral (φ : A →+* B) (hφ : φ.IsIntegral)
    (x : Spectrum A) : IsCompact (comap φ ⁻¹' {x}) :=
  isCompact_preimage_comap_of_isIntegral φ hφ isCompact_singleton

end Spectrum

namespace RelativeSpectrum

variable {R : Type*} [CommRing R] {v : Valuation R ℝ≥0}
  {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Integral algebra maps have compact inverse images in any prescribed-base spectrum. -/
theorem isCompact_preimage_comap_of_isIntegral (φ : A →ₐ[R] B)
    (hφ : φ.toRingHom.IsIntegral) {K : Set (RelativeSpectrum v A)} (hK : IsCompact K) :
    IsCompact (comap φ ⁻¹' K) := by
  have heq : comap (v := v) φ ⁻¹' K =
      ((↑) : RelativeSpectrum v B → Spectrum B) ⁻¹'
        (Spectrum.comap φ.toRingHom ⁻¹'
          (((↑) : RelativeSpectrum v A → Spectrum A) '' K)) := by
    ext y
    constructor
    · intro hy
      exact ⟨comap φ y, hy, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      have he : x = comap φ y := Subtype.ext hxy
      rwa [he] at hx
  rw [heq]
  exact isClosedEmbedding_subtypeVal.isCompact_preimage
    (Spectrum.isCompact_preimage_comap_of_isIntegral φ.toRingHom hφ
      (hK.image continuous_subtype_val))

/-- Fibres of an integral algebra-map pullback are compact for any prescribed base valuation. -/
theorem isCompact_preimage_singleton_of_isIntegral (φ : A →ₐ[R] B)
    (hφ : φ.toRingHom.IsIntegral) (x : RelativeSpectrum v A) :
    IsCompact (comap φ ⁻¹' {x}) :=
  isCompact_preimage_comap_of_isIntegral φ hφ isCompact_singleton

end RelativeSpectrum

end EnvelopeProperty.Berkovich
