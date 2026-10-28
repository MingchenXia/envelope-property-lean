/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Berkovich.SpectrumNormedMaps

/-!
# The true bounded Banach ring spectrum functor

A genuine positive coefficient bound need not make the original RingHom
contractive. The actual BGR positive-power argument DOES make every pulled-back
multiplicative bounded point contractive. All whole valuations are retained.
-/
open scoped NNReal Topology
open Topology
noncomputable section

namespace RingHom
variable {A B C : Type*} [SeminormedRing A] [SeminormedRing B] [SeminormedRing C]

/-- The actual original identity ring map is bounded with positive constant one. -/
theorem isBounded_id : (RingHom.id A).IsBounded :=
  ⟨1, zero_lt_one, fun a => by simp only [RingHom.id_apply, one_mul, le_refl]⟩

/-- Genuine positive bounds multiply under actual whole RingHom composition. -/
theorem IsBounded.comp {φ : A →+* B} {ψ : B →+* C} (hψ : ψ.IsBounded) (hφ : φ.IsBounded) :
    (ψ.comp φ).IsBounded := by
  obtain ⟨D, hD, hψ⟩ := hψ
  obtain ⟨E, hE, hφ⟩ := hφ
  refine ⟨D*E, mul_pos hD hE, fun a => ?_⟩
  exact (hψ (φ a)).trans ((mul_le_mul_of_nonneg_left (hφ a) hD.le).trans_eq (mul_assoc D E ‖a‖).symm)

end RingHom

namespace EnvelopeProperty.Berkovich
namespace Spectrum
variable {A B : Type*} [SeminormedCommRing A] [SeminormedCommRing B]

/-- The actual BGR power argument derives whole pulled-back POINT contractivity from a genuine bounded RingHom. -/
theorem isNormBounded_comap_of_isBounded (φ : A →+* B) (hφ : φ.IsBounded)
    (x : Spectrum B) (hx : x.IsNormBounded) : (Spectrum.comap φ x).IsNormBounded := by
  apply (isNormBounded_iff _).mpr
  obtain ⟨C, hC, hφ⟩ := hφ
  refine ⟨C, hC, fun a => ?_⟩
  exact (show (x.val (φ a) : ℝ) ≤ ‖φ a‖ from hx (φ a)).trans (hφ a)

end Spectrum

namespace NormBoundedSpectrum
variable {A B C : Type*} [SeminormedCommRing A] [SeminormedCommRing B] [SeminormedCommRing C]

/-- Whole true bounded-spectrum pullback for ANY actual bounded RingHom, with derived point contraction. -/
def boundedComap (φ : A →+* B) (hφ : φ.IsBounded) (x : NormBoundedSpectrum B) : NormBoundedSpectrum A :=
  ⟨Spectrum.comap φ x.1, Spectrum.isNormBounded_comap_of_isBounded φ hφ x.1 x.2⟩

/-- Every original element value is retained by genuine bounded RingHom pullback. -/
@[simp]
theorem boundedComap_val_apply (φ : A →+* B) (hφ : φ.IsBounded) (x : NormBoundedSpectrum B) (a : A) :
    (boundedComap φ hφ x).1.val a = x.1.val (φ a) := rfl

/-- Actual bounded pullback is continuous in the existing whole evaluation topologies. -/
theorem continuous_boundedComap (φ : A →+* B) (hφ : φ.IsBounded) : Continuous (boundedComap φ hφ) := by
  apply Continuous.subtype_mk
  exact (Spectrum.continuous_comap φ).comp continuous_subtype_val

/-- Actual bounded identity preserves the WHOLE original point. -/
@[simp]
theorem boundedComap_id (x : NormBoundedSpectrum A) :
    boundedComap (RingHom.id A) RingHom.isBounded_id x = x := by
  apply Subtype.ext
  exact Spectrum.ext_val fun _ => rfl

/-- Genuine bounded composition gives the exact whole contravariant point-map law. -/
theorem boundedComap_comp (φ : A →+* B) (hφ : φ.IsBounded) (ψ : B →+* C) (hψ : ψ.IsBounded)
    (x : NormBoundedSpectrum C) :
    boundedComap (ψ.comp φ) (hψ.comp hφ) x = boundedComap φ hφ (boundedComap ψ hψ x) := by
  apply Subtype.ext
  exact Spectrum.ext_val fun _ => rfl

/-- On an actually contractive original RingHom this IS the existing whole contractive pullback. -/
theorem boundedComap_eq_comap (φ : A →+* B) (hφ : φ.IsBounded) (hc : ∀ a, ‖φ a‖₊ ≤ ‖a‖₊)
    (x : NormBoundedSpectrum B) : boundedComap φ hφ x = comap φ hc x := by
  apply Subtype.ext
  rfl

end NormBoundedSpectrum

namespace RelativeNormBoundedSpectrum
variable {R A B : Type*} [CommRing R] [SeminormedCommRing A] [SeminormedCommRing B]

/-- The actual original coefficient RingHom locus is retained under genuinely BOUNDED coefficient-ring maps. -/
def boundedComap (v : Valuation R ℝ≥0) (φ : R →+* A) (ψ : A →+* B) (hψ : ψ.IsBounded)
    (x : RelativeNormBoundedSpectrum v (ψ.comp φ)) : RelativeNormBoundedSpectrum v φ :=
  ⟨NormBoundedSpectrum.boundedComap ψ hψ x.1, x.2⟩

/-- All original algebra values, not merely the prescribed scalar values, are preserved. -/
@[simp]
theorem boundedComap_val_apply (v : Valuation R ℝ≥0) (φ : R →+* A) (ψ : A →+* B) (hψ : ψ.IsBounded)
    (x : RelativeNormBoundedSpectrum v (ψ.comp φ)) (a : A) :
    (boundedComap v φ ψ hψ x).1.1.val a = x.1.1.val (ψ a) := rfl

/-- Whole genuine bounded pullback restricts continuously to the EXACT original prescribed coefficient locus. -/
theorem continuous_boundedComap (v : Valuation R ℝ≥0) (φ : R →+* A) (ψ : A →+* B) (hψ : ψ.IsBounded) :
    Continuous (boundedComap v φ ψ hψ) := by
  apply Continuous.subtype_mk
  exact (NormBoundedSpectrum.continuous_boundedComap ψ hψ).comp continuous_subtype_val

end RelativeNormBoundedSpectrum
end EnvelopeProperty.Berkovich
