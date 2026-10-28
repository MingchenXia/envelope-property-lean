/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.Spectrum
import EnvelopeProperty.Berkovich.Basic

/-!
# Compatibility of the general spectrum with trivial-field analytification

The existing affine analytification `Berk k A` is canonically the relative spectrum
over the trivial valuation of `k`. The homeomorphism preserves every evaluation and
commutes with pullback along algebra homomorphisms.
-/

open scoped NNReal Topology
open Topology Classical

noncomputable section

namespace EnvelopeProperty.Berk

open Berkovich

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- Forget the prescribed trivial value on the coefficient field. -/
def toSpectrum (x : Berk k A) : Spectrum A := ⟨x.val⟩

@[simp]
theorem toSpectrum_val (x : Berk k A) : (toSpectrum x).val = x.val := rfl

@[simp]
theorem logAbs_toSpectrum (x : Berk k A) (a : A) :
    Spectrum.logAbs a (toSpectrum x) = logAbs a x := rfl

@[fun_prop]
theorem continuous_toSpectrum : Continuous (toSpectrum : Berk k A → Spectrum A) := by
  rw [Spectrum.continuous_iff]
  exact fun a => continuous_abs a

/-- The trivial-field affine analytification is exactly the relative spectrum for
the trivial valuation of the field, including its required value at zero. -/
def relativeSpectrumHomeomorph :
    Berk k A ≃ₜ RelativeSpectrum (1 : Valuation k ℝ≥0) A where
  toFun x := ⟨toSpectrum x, fun c => by
    change x.val (algebraMap k A c) = (1 : Valuation k ℝ≥0) c
    by_cases hc : c = 0
    · simp [hc]
    · rw [x.val_algebraMap c hc, Valuation.one_apply_of_ne_zero hc]⟩
  invFun x :=
    { val := x.1.val
      val_algebraMap := fun c hc => by
        simpa only [Valuation.one_apply_of_ne_zero hc] using x.2 c }
  left_inv x := Berk.ext rfl
  right_inv x := Subtype.ext (Spectrum.ext rfl)
  continuous_toFun := RelativeSpectrum.continuous_iff.2 fun a => continuous_abs a
  continuous_invFun := continuous_iff.2 fun a => RelativeSpectrum.continuous_val_apply a

@[simp]
theorem relativeSpectrumHomeomorph_apply_coe (x : Berk k A) :
    (relativeSpectrumHomeomorph x : Spectrum A) = toSpectrum x := rfl

@[simp]
theorem relativeSpectrumHomeomorph_apply_val (x : Berk k A) (a : A) :
    (relativeSpectrumHomeomorph x).1.val a = x.val a := rfl

@[simp]
theorem relativeSpectrumHomeomorph_symm_val
    (x : RelativeSpectrum (1 : Valuation k ℝ≥0) A) :
    (relativeSpectrumHomeomorph.symm x).val = x.1.val := rfl

/-- The forgetful map realizes the old analytification as a closed subspace of the
general seminorm spectrum. -/
theorem isClosedEmbedding_toSpectrum :
    IsClosedEmbedding (toSpectrum : Berk k A → Spectrum A) :=
  RelativeSpectrum.isClosedEmbedding_subtypeVal.comp
    relativeSpectrumHomeomorph.isClosedEmbedding

section comap

variable {B : Type*} [CommRing B] [Algebra k B]

@[simp]
theorem toSpectrum_comap (φ : A →ₐ[k] B) (y : Berk k B) :
    toSpectrum (comap φ y) = Spectrum.comap φ.toRingHom (toSpectrum y) := rfl

/-- The specialization homeomorphism is natural for algebra homomorphisms. -/
@[simp]
theorem relativeSpectrumHomeomorph_comap (φ : A →ₐ[k] B) (y : Berk k B) :
    relativeSpectrumHomeomorph (comap φ y) =
      RelativeSpectrum.comap φ (relativeSpectrumHomeomorph y) := rfl

end comap

end EnvelopeProperty.Berk
