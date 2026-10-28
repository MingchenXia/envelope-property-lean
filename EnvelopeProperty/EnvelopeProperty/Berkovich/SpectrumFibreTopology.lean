/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumFibre
import EnvelopeProperty.Berkovich.SpectrumTopology
import EnvelopeProperty.Berkovich.SpectrumBaseChange
import EnvelopeProperty.Berkovich.SpectrumFilters

/-!
# Homeomorphisms of completed-residue-field fibres

Every ultrafilter with eventually bounded evaluation coordinates has a limit
in a prescribed-base spectrum. Applied to tensor restriction, finite sums of
elementary tensors supply these bounds from convergent original-ring values.
Thus the genuine completed-residue-field fibre equivalence is a homeomorphism,
without finite generation or local compactness hypotheses.
-/

open scoped NNReal Topology
open Topology Filter TensorProduct

noncomputable section

namespace EnvelopeProperty.Berkovich

namespace RelativeSpectrum

variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C] {v : Valuation R ℝ≥0}

/-- Coordinatewise eventual finite bounds suffice for convergence of an ultrafilter
in a prescribed-base spectrum; the eventual sets may depend on the coordinate. -/
theorem exists_ultrafilter_limit_of_eventually_bounded
    (U : Ultrafilter (RelativeSpectrum v C))
    (hM : ∀ a : C, ∃ M : ℝ≥0, ∀ᶠ z in (U : Filter (RelativeSpectrum v C)), z.1.val a ≤ M) :
    ∃ z : RelativeSpectrum v C, (U : Filter (RelativeSpectrum v C)) ≤ 𝓝 z :=
  exists_ultrafilter_limit_of_bounded_evaluations U hM

end RelativeSpectrum

namespace Spectrum

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- Elementary tensor values in the completed-field spectrum follow from the
generic prescribed-base tensor formula. -/
theorem fibreRestrict_val_tmul (x : Spectrum A)
    (z : RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] B)) (c : H x) (b : B) :
    z.1.val (c ⊗ₜ[A] b) = ‖c‖₊ * (fibreRestrict x z).1.val b := by
  have hwv : ∀ a : A, (NormedField.valuation (K := H x)) (algebraMap A (H x) a) = x.val a :=
    fun a => nnnorm_toH x a
  exact RelativeSpectrum.baseChange_val_tmul hwv z c b

/-- Completed-field tensor restriction is proper by the ultrafilter lifting
criterion, without compact-generation or local-compactness assumptions. -/
theorem isProperMap_fibreRestrict (x : Spectrum A) : IsProperMap (fibreRestrict (B := B) x) := by
  rw [isProperMap_iff_ultrafilter_of_t2]
  refine ⟨continuous_fibreRestrict x, fun {U} {y} hy => ?_⟩
  have hbound : ∀ t : H x ⊗[A] B, ∃ M : ℝ≥0,
      ∀ᶠ z in (U : Filter (RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] B))),
        z.1.val t ≤ M := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, Eventually.of_forall fun z => by simp only [map_zero, le_refl]⟩
    | tmul c b =>
      have ht : Tendsto (fun z => (fibreRestrict x z).1.val b) U (𝓝 (y.1.val b)) :=
        (((continuous_abs b).comp continuous_subtype_val).tendsto y).comp hy
      obtain ⟨M, hM⟩ := ht.isBoundedUnder_le
      change ∀ᶠ z in
        (U : Filter (RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] B))),
          (fibreRestrict x z).1.val b ≤ M at hM
      refine ⟨‖c‖₊ * M, hM.mono fun z hz => ?_⟩
      rw [fibreRestrict_val_tmul]
      exact mul_le_mul' le_rfl hz
    | add t s ht hs =>
      obtain ⟨M, hM⟩ := ht
      obtain ⟨N, hN⟩ := hs
      exact ⟨max M N, (hM.and hN).mono fun z hz =>
        (z.1.val.map_add t s).trans (max_le_max hz.1 hz.2)⟩
  exact RelativeSpectrum.exists_ultrafilter_limit_of_eventually_bounded U hbound

/-- Restriction is closed as a consequence of the proved proper-map criterion. -/
theorem isClosedMap_fibreRestrict (x : Spectrum A) : IsClosedMap (fibreRestrict (B := B) x) :=
  (isProperMap_fibreRestrict x).isClosedMap

/-- The actual completed-residue-field tensor spectrum is homeomorphic to the
original seminorm fibre. -/
def fibreHomeomorph (x : Spectrum A) :
    RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] B) ≃ₜ Fibre (B := B) x :=
  (fibreEquiv x).toHomeomorphOfContinuousClosed
    (continuous_fibreRestrict x) (isClosedMap_fibreRestrict x)

@[simp]
theorem fibreHomeomorph_apply (x : Spectrum A)
    (z : RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] B)) :
    fibreHomeomorph x z = fibreRestrict x z := rfl

@[simp]
theorem fibreHomeomorph_symm_apply (x : Spectrum A) (y : Fibre (B := B) x) :
    (fibreHomeomorph x).symm y = fibrePoint y.2 := rfl

/-- The genuinely constructed tensor seminorm varies continuously over the whole fibre. -/
@[fun_prop]
theorem continuous_fibrePoint (x : Spectrum A) :
    Continuous (fun y : Fibre (B := B) x => fibrePoint y.2) :=
  (fibreHomeomorph x).symm.continuous

end Spectrum

end EnvelopeProperty.Berkovich
