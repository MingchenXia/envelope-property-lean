/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.Spectrum

/-!
# Closed realizations and compact bounds for arbitrary seminorm spectra

For any commutative ring, its real-valued ultrametric seminorm spectrum is a closed
subspace of the product of all evaluation coordinates. Prescribing a finite upper
bound for every coordinate cuts out a compact set, by Tychonoff's theorem.

The same compactness statement holds in a relative spectrum for any prescribed
base valuation. No field, triviality, finite generation, or completeness hypothesis
is required. The chosen bounds may be incompatible, yielding an empty compact set.
-/

open scoped NNReal Topology
open Topology Set

noncomputable section

namespace EnvelopeProperty.Berkovich

namespace Spectrum

variable {A : Type*} [CommRing A]

/-- A multiplicative ultrametric seminorm specified by its evaluation function. -/
def ofFun (w : A → ℝ≥0) (h0 : w 0 = 0) (h1 : w 1 = 1)
    (hmul : ∀ a b, w (a * b) = w a * w b) (hadd : ∀ a b, w (a + b) ≤ max (w a) (w b)) :
    Spectrum A where
  val :=
    { toFun := w
      map_zero' := h0
      map_one' := h1
      map_mul' := hmul
      map_add_le_max' := hadd }

@[simp]
theorem ofFun_val_apply (w : A → ℝ≥0) (h0 : w 0 = 0) (h1 : w 1 = 1)
    (hmul : ∀ a b, w (a * b) = w a * w b) (hadd : ∀ a b, w (a + b) ≤ max (w a) (w b))
    (a : A) : (ofFun w h0 h1 hmul hadd).val a = w a := rfl

/-- The closed seminorm axioms in the full product of evaluation coordinates. -/
def rangeSet (A : Type*) [CommRing A] : Set (A → ℝ≥0) :=
  {w | w 0 = 0 ∧ w 1 = 1 ∧ (∀ a b, w (a * b) = w a * w b) ∧
    ∀ a b, w (a + b) ≤ max (w a) (w b)}

theorem range_toFun : range (toFun : Spectrum A → A → ℝ≥0) = rangeSet A := by
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val.map_zero, x.val.map_one, x.val.map_mul, x.val.map_add⟩
  · rintro ⟨h0, h1, hmul, hadd⟩
    exact ⟨ofFun w h0 h1 hmul hadd, rfl⟩

theorem isClosed_rangeSet : IsClosed (rangeSet A) := by
  have heq : rangeSet A =
      {w : A → ℝ≥0 | w 0 = 0} ∩ {w | w 1 = 1} ∩
        (⋂ a, ⋂ b, {w | w (a * b) = w a * w b}) ∩
        (⋂ a, ⋂ b, {w | w (a + b) ≤ max (w a) (w b)}) := by
    ext w
    simp only [rangeSet, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    tauto
  rw [heq]
  exact (((isClosed_eq (continuous_apply _) continuous_const).inter
    (isClosed_eq (continuous_apply _) continuous_const)).inter
    (isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (continuous_apply (a * b)) ((continuous_apply a).mul (continuous_apply b)))).inter
    (isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le (continuous_apply (a + b)) ((continuous_apply a).max (continuous_apply b)))

/-- All multiplicative ultrametric seminorms form a closed subspace of the evaluation product. -/
theorem isClosedEmbedding_toFun : IsClosedEmbedding (toFun : Spectrum A → A → ℝ≥0) :=
  ⟨isEmbedding_toFun, by rw [range_toFun]; exact isClosed_rangeSet⟩

theorem isClosed_setOf_forall_val_le (M : A → ℝ≥0) :
    IsClosed {x : Spectrum A | ∀ a : A, x.val a ≤ M a} := by
  have heq : {x : Spectrum A | ∀ a : A, x.val a ≤ M a} =
      ⋂ a : A, {x : Spectrum A | x.val a ≤ M a} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact isClosed_iInter fun a => isClosed_le (continuous_abs a) continuous_const

/-- Prescribing an arbitrary finite upper bound for every ring element gives a compact set. -/
theorem isCompact_setOf_forall_val_le (M : A → ℝ≥0) :
    IsCompact {x : Spectrum A | ∀ a : A, x.val a ≤ M a} := by
  rw [isInducing_toFun.isCompact_iff]
  refine (isCompact_univ_pi fun a => isCompact_Icc (a := (0 : ℝ≥0)) (b := M a)).of_isClosed_subset
    (isClosedEmbedding_toFun.isClosedMap _ (isClosed_setOf_forall_val_le M)) ?_
  rintro _ ⟨x, hx, rfl⟩ a _
  exact ⟨zero_le, hx a⟩

end Spectrum

namespace RelativeSpectrum

variable {R : Type*} [CommRing R] {v : Valuation R ℝ≥0}
  {A : Type*} [CommRing A] [Algebra R A]

/-- Arbitrary coordinate bounds are compact in a spectrum with a prescribed base valuation. -/
theorem isCompact_setOf_forall_val_le (M : A → ℝ≥0) :
    IsCompact {x : RelativeSpectrum v A | ∀ a : A, val x a ≤ M a} :=
  isClosedEmbedding_subtypeVal.isCompact_preimage (Spectrum.isCompact_setOf_forall_val_le M)

end RelativeSpectrum

end EnvelopeProperty.Berkovich
