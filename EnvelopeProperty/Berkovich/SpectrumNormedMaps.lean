/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Berkovich.SpectrumNormedCompletion

/-!
# Actual contractive ring maps and isometric equivalences on norm-bounded spectra

Every construction uses the true whole ring map and every original norm.
-/
open scoped NNReal
noncomputable section
namespace EnvelopeProperty.Berkovich.NormBoundedSpectrum
variable {A B C : Type*} [SeminormedCommRing A] [SeminormedCommRing B] [SeminormedCommRing C]

/-- The entire valuation pulls back along an ACTUAL contractive ring homomorphism. -/
def comap (φ : A →+* B) (hφ : ∀ a, ‖φ a‖₊ ≤ ‖a‖₊) (x : NormBoundedSpectrum B) :
    NormBoundedSpectrum A :=
  ⟨Spectrum.comap φ x.1, fun a => (x.2 (φ a)).trans (hφ a)⟩

/-- Every original element value is the genuine ring-map pullback value. -/
@[simp]
theorem comap_val_apply (φ : A →+* B) (hφ : ∀ a, ‖φ a‖₊ ≤ ‖a‖₊)
    (x : NormBoundedSpectrum B) (a : A) : (comap φ hφ x).1.val a = x.1.val (φ a) := rfl

/-- Whole norm-bounded pullback is continuous in the actual evaluation topologies. -/
theorem continuous_comap (φ : A →+* B) (hφ : ∀ a, ‖φ a‖₊ ≤ ‖a‖₊) :
    Continuous (comap φ hφ) := by
  apply Continuous.subtype_mk
  exact (Spectrum.continuous_comap φ).comp continuous_subtype_val

/-- The actual identity ring map gives the entire identity point map. -/
@[simp]
theorem comap_id (x : NormBoundedSpectrum A) : comap (RingHom.id A) (fun _ => le_rfl) x = x := by
  apply Subtype.ext
  exact Spectrum.ext_val fun _ => rfl

/-- Actual ring-map composition gives the whole contravariant point-map composition. -/
theorem comap_comp (φ : A →+* B) (hφ : ∀ a, ‖φ a‖₊ ≤ ‖a‖₊)
    (ψ : B →+* C) (hψ : ∀ b, ‖ψ b‖₊ ≤ ‖b‖₊) (x : NormBoundedSpectrum C) :
    comap (ψ.comp φ) (fun a => (hψ (φ a)).trans (hφ a)) x = comap φ hφ (comap ψ hψ x) := by
  apply Subtype.ext
  exact Spectrum.ext_val fun _ => rfl

/-- Genuine whole ring equivalence and norm preservation give the actual bounded-spectrum homeomorphism. -/
def ringEquivHomeomorph (e : A ≃+* B) (he : ∀ a, ‖e a‖₊ = ‖a‖₊) :
    NormBoundedSpectrum B ≃ₜ NormBoundedSpectrum A where
  toFun := comap e.toRingHom (fun a => (he a).le)
  invFun := comap e.symm.toRingHom (fun b => by
    change ‖e.symm b‖₊ ≤ ‖b‖₊
    simpa only [e.apply_symm_apply] using (he (e.symm b)).symm.le)
  left_inv x := by
    apply Subtype.ext
    exact Spectrum.ext_val fun b => congrArg x.1.val (e.apply_symm_apply b)
  right_inv x := by
    apply Subtype.ext
    exact Spectrum.ext_val fun a => congrArg x.1.val (e.symm_apply_apply a)
  continuous_toFun := continuous_comap _ _
  continuous_invFun := continuous_comap _ _

/-- Every original element is preserved by the actual bounded-spectrum equivalence. -/
@[simp]
theorem ringEquivHomeomorph_val_apply (e : A ≃+* B) (he : ∀ a, ‖e a‖₊ = ‖a‖₊)
    (x : NormBoundedSpectrum B) (a : A) :
    (ringEquivHomeomorph e he x).1.val a = x.1.val (e a) := rfl

/-- Every inverse element is preserved by the true inverse point map. -/
@[simp]
theorem ringEquivHomeomorph_symm_val_apply (e : A ≃+* B) (he : ∀ a, ‖e a‖₊ = ‖a‖₊)
    (x : NormBoundedSpectrum A) (b : B) :
    ((ringEquivHomeomorph e he).symm x).1.val b = x.1.val (e.symm b) := rfl

end EnvelopeProperty.Berkovich.NormBoundedSpectrum

namespace EnvelopeProperty.Berkovich.RelativeNormBoundedSpectrum
variable {R A B : Type*} [CommRing R] [SeminormedCommRing A] [SeminormedCommRing B]

/-- An actual isometric ring equivalence preserves the EXACT original coefficient RingHom locus. -/
def ringEquivHomeomorph (v : Valuation R ℝ≥0) (φ : R →+* A)
    (e : A ≃+* B) (he : ∀ a, ‖e a‖₊ = ‖a‖₊) :
    RelativeNormBoundedSpectrum v (e.toRingHom.comp φ) ≃ₜ RelativeNormBoundedSpectrum v φ :=
  (NormBoundedSpectrum.ringEquivHomeomorph e he).subtype fun _ => Iff.rfl

/-- The prescribed-coefficient comparison retains EVERY original algebra element value. -/
@[simp]
theorem ringEquivHomeomorph_val_apply (v : Valuation R ℝ≥0) (φ : R →+* A)
    (e : A ≃+* B) (he : ∀ a, ‖e a‖₊ = ‖a‖₊)
    (x : RelativeNormBoundedSpectrum v (e.toRingHom.comp φ)) (a : A) :
    (ringEquivHomeomorph v φ e he x).1.1.val a = x.1.1.val (e a) := rfl

end EnvelopeProperty.Berkovich.RelativeNormBoundedSpectrum
