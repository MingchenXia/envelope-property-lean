/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.Projective.NormalizedSpectrum
import EnvelopeProperty.Berkovich.SpectrumFilters

/-!
# Genuine absolute normalized-projective coefficient properness

The true closed evaluation embedding and individual finite-polynomial
coefficient bounds prove properness directly by convergent ultrafilters.
No bound on the original coefficient valuation or projective compactness
certificate is assumed.
-/
open scoped NNReal Topology
open Topology Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum
variable {R σ : Type*} [CommRing R]

/-- Every ORIGINAL polynomial is bounded by its true finite coefficient maximum when actual variable values are at most one. -/
theorem val_le_sup_coeff_of_variables_le_one (x : Spectrum (MvPolynomial σ R))
    (hx : ∀ i, x.val (MvPolynomial.X i) ≤ 1) (F : MvPolynomial σ R) :
    x.val F ≤ F.support.sup (fun m => x.val (MvPolynomial.C (F.coeff m))) := by
  classical
  conv_lhs => rw [← F.support_sum_monomial_coeff]
  apply x.val.map_sum_le
  intro m hm
  refine le_trans ?_ (Finset.le_sup (f := fun m => x.val (MvPolynomial.C (F.coeff m))) hm)
  rw [MvPolynomial.monomial_eq, map_mul]
  have hp : x.val (m.prod (fun i e => MvPolynomial.X i ^ e) : MvPolynomial σ R) ≤ 1 := by
    rw [Finsupp.prod, map_prod]
    apply Finset.prod_le_one
    · intro i _
      exact zero_le
    · intro i _
      rw [map_pow]
      exact pow_le_one₀ zero_le (hx i)
  exact (mul_le_mul' le_rfl hp).trans_eq (mul_one _)

end EnvelopeProperty.Berkovich.Spectrum

namespace EnvelopeProperty.Berkovich.NormalizedProjectiveSpectrum
open EnvelopeProperty.Berkovich
variable {R : Type*} [CommRing R] {n : ℕ}

/-- The actual original coefficient restriction on the WHOLE absolute normalized projective point. -/
def coefficientRestriction (x : NormalizedProjectiveSpectrum R n) : Spectrum R :=
  Spectrum.comap MvPolynomial.C x.1

/-- EVERY original coefficient is retained by the whole original restriction. -/
@[simp]
theorem coefficientRestriction_val (x : NormalizedProjectiveSpectrum R n) (r : R) :
    (coefficientRestriction x).val r = x.1.val (MvPolynomial.C r) := rfl

/-- True full pointwise evaluation gives continuity of the original coefficient restriction. -/
theorem continuous_coefficientRestriction :
    Continuous (coefficientRestriction (R := R) (n := n)) :=
  (Spectrum.continuous_comap MvPolynomial.C).comp continuous_val

/-- The original normalized grading and coordinate conditions give a genuine CLOSED full-evaluation embedding. -/
theorem isClosedEmbedding_evaluation :
    IsClosedEmbedding (fun x : NormalizedProjectiveSpectrum R n => fun F => x.1.val F) :=
  Spectrum.isClosedEmbedding_toFun.comp isClosed_carrier.isClosedEmbedding_subtypeVal

/-- Convergent coefficient ultrafilters have genuine original normalized-projective limits, proving actual properness. -/
theorem isProperMap_coefficientRestriction :
    IsProperMap (coefficientRestriction (R := R) (n := n)) := by
  classical
  rw [isProperMap_iff_ultrafilter_of_t2]
  refine ⟨continuous_coefficientRestriction, fun {U} {x} hx => ?_⟩
  apply EnvelopeProperty.exists_ultrafilter_limit_of_bounded_coordinates isClosedEmbedding_evaluation U
  intro F
  have hcoeff : ∀ r : R, ∃ M : ℝ≥0,
      ∀ᶠ z in (U : Filter (NormalizedProjectiveSpectrum R n)), z.1.val (MvPolynomial.C r) ≤ M := by
    intro r
    have ht : Tendsto (fun z : NormalizedProjectiveSpectrum R n => z.1.val (MvPolynomial.C r))
        U (𝓝 (x.val r)) := ((Spectrum.continuous_val_apply r).tendsto x).comp hx
    exact ht.isBoundedUnder_le
  choose M hM using hcoeff
  have hall : ∀ᶠ z in (U : Filter (NormalizedProjectiveSpectrum R n)),
      ∀ m ∈ F.support, z.1.val (MvPolynomial.C (F.coeff m)) ≤ M (F.coeff m) :=
    (eventually_all_finset F.support).mpr fun m _ => hM (F.coeff m)
  refine ⟨F.support.sup (fun m => M (F.coeff m)), hall.mono fun z hz => ?_⟩
  exact (Spectrum.val_le_sup_coeff_of_variables_le_one z.1 (val_X_le_one z) F).trans
    (Finset.sup_le fun m hm => (hz m hm).trans (Finset.le_sup (f := fun m => M (F.coeff m)) hm))

/-- Actual properness gives closedness without any coefficient bound or local-compactness assumption. -/
theorem isClosedMap_coefficientRestriction :
    IsClosedMap (coefficientRestriction (R := R) (n := n)) :=
  isProperMap_coefficientRestriction.isClosedMap

end EnvelopeProperty.Berkovich.NormalizedProjectiveSpectrum
