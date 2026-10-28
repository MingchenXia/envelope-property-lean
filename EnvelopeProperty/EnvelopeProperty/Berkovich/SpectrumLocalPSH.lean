/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumTopology
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Independent finite-coefficient local presentations at a prescribed base valuation

This is the actual finite-A formula, defined for arbitrary commutative rings
and actual prescribed coefficient values. No old field-only function class,
analytic identification or comparison certificate enters these definitions.
-/
open scoped NNReal Topology
open Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] {v : Valuation R ℝ≥0}

/-- The original rational affine expression in EVERY actual original coefficient value. -/
def tropAffine {n : ℕ} (a : Fin n → A) (p : (Fin n → ℚ) × ℚ)
    (y : RelativeSpectrum v A) : ℝ :=
  ∑ i, (p.1 i : ℝ) * Real.log (y.1.val (a i) : ℝ) + p.2

/-- Independently defined finite-A rational maxima on the actual relative spectrum. -/
def IsConvexPLOn (U : Set (RelativeSpectrum v A)) (u : RelativeSpectrum v A → EReal) : Prop :=
  ∀ x ∈ U, ∃ W : Set (RelativeSpectrum v A), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
    ∃ (n : ℕ) (a : Fin n → A) (s : Finset ((Fin n → ℚ) × ℚ)) (hs : s.Nonempty),
      (∀ y ∈ W, ∀ i, y.1.val (a i) ≠ 0) ∧
      ∀ y ∈ W, u y = ((s.sup' hs fun p => tropAffine a p y : ℝ) : EReal)

/-- Genuine whole decreasing sequences with their actual pointwise infima. -/
def IsDecrConvexPLLimitOn (U : Set (RelativeSpectrum v A)) (u : RelativeSpectrum v A → EReal) : Prop :=
  ∃ w : ℕ → RelativeSpectrum v A → EReal, (∀ j, IsConvexPLOn U (w j)) ∧
    (∀ y ∈ U, Antitone fun j => w j y) ∧ ∀ y ∈ U, u y = ⨅ j, w j y

/-- The independent actual finite-A local decreasing-limit presentation class. -/
def IsLocallyPSHOn (U : Set (RelativeSpectrum v A)) (u : RelativeSpectrum v A → EReal) : Prop :=
  ∀ x ∈ U, ∃ W : Set (RelativeSpectrum v A), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
    IsDecrConvexPLLimitOn W u

/-- Actual whole coefficient comaps preserve each ORIGINAL rational expression. -/
theorem tropAffine_comap (φ : A →ₐ[R] B) {n : ℕ} (a : Fin n → A)
    (p : (Fin n → ℚ) × ℚ) (y : RelativeSpectrum v B) :
    tropAffine a p (comap φ y) = tropAffine (fun i => φ (a i)) p y := rfl

/-- Full original coefficient maps pull back genuine finite-A presentations. -/
theorem IsConvexPLOn.comp_comap {U : Set (RelativeSpectrum v A)} {u : RelativeSpectrum v A → EReal}
    (hu : IsConvexPLOn U u) (φ : A →ₐ[R] B) :
    IsConvexPLOn (comap φ ⁻¹' U) (fun y => u (comap φ y)) := by
  intro y hy
  obtain ⟨W, hW, hyW, hWU, n, a, s, hs, ha, hform⟩ := hu (comap φ y) hy
  refine ⟨comap φ ⁻¹' W, hW.preimage (continuous_comap φ), hyW,
    Set.preimage_mono hWU, n, (fun i => φ (a i)), s, hs, ?_, ?_⟩
  · intro z hz i
    exact ha (comap φ z) hz i
  · intro z hz
    exact hform (comap φ z) hz

/-- Whole continuous comaps preserve genuine monotone sequences and all original infima. -/
theorem IsDecrConvexPLLimitOn.comp_comap {U : Set (RelativeSpectrum v A)}
    {u : RelativeSpectrum v A → EReal} (hu : IsDecrConvexPLLimitOn U u) (φ : A →ₐ[R] B) :
    IsDecrConvexPLLimitOn (comap φ ⁻¹' U) (fun y => u (comap φ y)) := by
  obtain ⟨w, hw, hanti, hlim⟩ := hu
  exact ⟨fun j y => w j (comap φ y), fun j => (hw j).comp_comap φ,
    fun y hy => hanti _ hy, fun y hy => hlim _ hy⟩

/-- The genuinely local presentation class pulls back without a field or coefficient-bound hypothesis. -/
theorem IsLocallyPSHOn.comp_comap {U : Set (RelativeSpectrum v A)}
    {u : RelativeSpectrum v A → EReal} (hu : IsLocallyPSHOn U u) (φ : A →ₐ[R] B) :
    IsLocallyPSHOn (comap φ ⁻¹' U) (fun y => u (comap φ y)) := by
  intro y hy
  obtain ⟨W, hW, hyW, hWU, hloc⟩ := hu (comap φ y) hy
  exact ⟨comap φ ⁻¹' W, hW.preimage (continuous_comap φ), hyW,
    Set.preimage_mono hWU, hloc.comp_comap φ⟩

end EnvelopeProperty.Berkovich.RelativeSpectrum
