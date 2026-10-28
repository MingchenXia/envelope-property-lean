/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumResidueField
import EnvelopeProperty.Berkovich.SpectrumTopology
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful

/-!
# Actual norm-bounded seminorms and separated ring completions

Contractive multiplicative ultrametric seminorms extend to the actual norm
completion through their true completed residue fields. The original ring may
be seminormed and need not have an ultrametric norm. No analytic sheaf or harmonic
function structure is asserted.
-/

open scoped NNReal Topology
open UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich

namespace Spectrum
variable {A : Type*} [SeminormedCommRing A]

/-- Contractivity against the specified ring seminorm, on EVERY original element. -/
def IsNormBounded (x : Spectrum A) : Prop := ∀ a : A, x.val a ≤ ‖a‖₊

/-- The usual positive-constant boundedness of a multiplicative seminorm is EXACTLY contractivity. -/
theorem isNormBounded_iff (x : Spectrum A) : x.IsNormBounded ↔
    ∃ C : ℝ, 0 < C ∧ ∀ a : A, (x.val a : ℝ) ≤ C * ‖a‖ := by
  constructor
  · intro hx
    exact ⟨1, zero_lt_one, fun a => by simpa only [one_mul] using
      (show (x.val a : ℝ) ≤ ‖a‖ from hx a)⟩
  · rintro ⟨C, hC, hb⟩ a
    have hp : IsPowMul (norm : x.H → ℝ) := fun z n _ => norm_pow z n
    have ht : x.toH.IsBounded := ⟨C, hC, fun a => by simpa only [norm_toH] using hb a⟩
    exact_mod_cast (show (x.val a : ℝ) ≤ ‖a‖ by
      simpa only [norm_toH] using contraction_of_isPowMul hp ht a)

/-- The actual map into the true completed residue field is contractive. -/
theorem lipschitz_toH_of_isNormBounded (x : Spectrum A) (hx : x.IsNormBounded) :
    LipschitzWith 1 x.toH := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub, norm_toH] using
    (show (x.val (a-b) : ℝ) ≤ ‖a-b‖ from hx (a-b))

/-- The entire evaluation function of an actual norm-bounded point is continuous. -/
theorem continuous_val_of_isNormBounded (x : Spectrum A) (hx : x.IsNormBounded) :
    Continuous x.val := by
  simpa only [Function.comp_def, nnnorm_toH] using continuous_nnnorm.comp
    (x.lipschitz_toH_of_isNormBounded hx).continuous

/-- The genuine ring extension into H(x), constructed by completion. -/
def normCompletionToH (x : Spectrum A) (hx : x.IsNormBounded) :
    Completion A →+* x.H :=
  Completion.extensionHom x.toH (x.lipschitz_toH_of_isNormBounded hx).continuous

@[simp]
theorem normCompletionToH_coe (x : Spectrum A) (hx : x.IsNormBounded) (a : A) :
    x.normCompletionToH hx (a : Completion A) = x.toH a :=
  Completion.extensionHom_coe _ _ a

/-- The genuine entire completion evaluation homomorphism is continuous. -/
theorem continuous_normCompletionToH (x : Spectrum A) (hx : x.IsNormBounded) :
    Continuous (x.normCompletionToH hx) := Completion.continuous_extension

/-- Density gives uniqueness of the ACTUAL continuous ring map into H(x), not just its seminorm. -/
theorem normCompletionToH_unique (x : Spectrum A) (hx : x.IsNormBounded)
    (g : Completion A →+* x.H) (hg : Continuous g)
    (h : ∀ a : A, g (a : Completion A) = x.toH a) : g = x.normCompletionToH hx := by
  apply RingHom.ext
  exact congrFun (Completion.denseRange_coe.equalizer hg
    (x.continuous_normCompletionToH hx) (funext fun a => by
      change g (a : Completion A) = x.normCompletionToH hx (a : Completion A)
      rw [normCompletionToH_coe]
      exact h a))

/-- Every actual completion element satisfies the true whole norm bound. -/
theorem norm_normCompletionToH_le (x : Spectrum A) (hx : x.IsNormBounded) (a : Completion A) :
    ‖x.normCompletionToH hx a‖ ≤ ‖a‖ := by
  induction a using Completion.induction_on with
  | hp => exact isClosed_le (continuous_norm.comp Completion.continuous_extension) continuous_norm
  | ih a => simpa only [normCompletionToH_coe, norm_toH, Completion.norm_coe] using
      (show (x.val a : ℝ) ≤ ‖a‖ from hx a)

/-- The actual multiplicative ultrametric seminorm extended through H(x). -/
def normCompletionLift (x : Spectrum A) (hx : x.IsNormBounded) : Spectrum (Completion A) :=
  ofValuation ((NormedField.valuation (K := x.H)).comap (x.normCompletionToH hx))

@[simp]
theorem normCompletionLift_val_coe (x : Spectrum A) (hx : x.IsNormBounded) (a : A) :
    (x.normCompletionLift hx).val (a : Completion A) = x.val a := by
  change ‖x.normCompletionToH hx (a : Completion A)‖₊ = x.val a
  rw [normCompletionToH_coe, nnnorm_toH]

theorem normCompletionLift_isNormBounded (x : Spectrum A) (hx : x.IsNormBounded) :
    (x.normCompletionLift hx).IsNormBounded := by
  intro a
  change ‖x.normCompletionToH hx a‖₊ ≤ ‖a‖₊
  exact x.norm_normCompletionToH_le hx a

/-- The value of EVERY completion element is the norm of its genuine extended H(x)-evaluation. -/
@[simp]
theorem normCompletionLift_val_apply (x : Spectrum A) (hx : x.IsNormBounded) (a : Completion A) :
    (x.normCompletionLift hx).val a = ‖x.normCompletionToH hx a‖₊ := rfl

/-- Actual norm-bounded completion points are determined by ALL original elements. -/
theorem normCompletion_ext {x y : Spectrum (Completion A)}
    (hx : x.IsNormBounded) (hy : y.IsNormBounded)
    (h : ∀ a : A, x.val (a : Completion A) = y.val (a : Completion A)) : x = y := by
  apply ext_val
  exact congrFun (Completion.denseRange_coe.equalizer
    (x.continuous_val_of_isNormBounded hx) (y.continuous_val_of_isNormBounded hy) (funext h))

end Spectrum

/-- Actual multiplicative ultrametric seminorms contractive for the specified whole ring norm. -/
abbrev NormBoundedSpectrum (A : Type*) [SeminormedCommRing A] :=
  {x : Spectrum A // x.IsNormBounded}

namespace NormBoundedSpectrum
variable {A : Type*} [SeminormedCommRing A]
instance compactSpace : CompactSpace (NormBoundedSpectrum A) :=
  isCompact_iff_compactSpace.mp (Spectrum.isCompact_setOf_forall_val_le (fun a : A => ‖a‖₊))

/-- True restriction along the actual separated completion ring map. -/
def completionComap (x : NormBoundedSpectrum (Completion A)) : NormBoundedSpectrum A :=
  ⟨Spectrum.comap Completion.coeRingHom x.1, fun a => by
    change x.1.val (a : Completion A) ≤ ‖a‖₊
    simpa only [Completion.nnnorm_coe] using x.2 (a : Completion A)⟩

/-- True contractive extension through the actual completed residue field. -/
def completionLift (x : NormBoundedSpectrum A) : NormBoundedSpectrum (Completion A) :=
  ⟨x.1.normCompletionLift x.2, x.1.normCompletionLift_isNormBounded x.2⟩

@[simp]
theorem completionComap_completionLift (x : NormBoundedSpectrum A) :
    completionComap (completionLift x) = x := by
  apply Subtype.ext
  exact Spectrum.ext_val fun a => x.1.normCompletionLift_val_coe x.2 a

@[simp]
theorem completionLift_completionComap (x : NormBoundedSpectrum (Completion A)) :
    completionLift (completionComap x) = x := by
  apply Subtype.ext
  apply Spectrum.normCompletion_ext (completionLift _).2 x.2
  intro a
  exact (completionComap x).1.normCompletionLift_val_coe (completionComap x).2 a

/-- Restriction of the ENTIRE actual completion spectrum is continuous. -/
theorem continuous_completionComap : Continuous (completionComap (A := A)) := by
  apply Continuous.subtype_mk
  exact (Spectrum.continuous_comap (Completion.coeRingHom : A →+* Completion A)).comp
    continuous_subtype_val

/-- The genuine completion preserves the entire norm-bounded spectrum and all original values. -/
def completionHomeomorph : NormBoundedSpectrum (Completion A) ≃ₜ NormBoundedSpectrum A :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.mk completionComap completionLift
    completionLift_completionComap completionComap_completionLift) continuous_completionComap

@[simp]
theorem completionHomeomorph_val_apply (x : NormBoundedSpectrum (Completion A)) (a : A) :
    (completionHomeomorph x).1.val a = x.1.val (a : Completion A) := rfl

end NormBoundedSpectrum

/-- Genuine prescribed coefficients along an ACTUAL ring map, without choosing an unrelated algebra action. -/
abbrev RelativeNormBoundedSpectrum {R A : Type*} [CommRing R] [SeminormedCommRing A]
    (v : Valuation R ℝ≥0) (φ : R →+* A) :=
  {x : NormBoundedSpectrum A // ∀ r : R, x.1.val (φ r) = v r}

namespace RelativeNormBoundedSpectrum
variable {R A : Type*} [CommRing R] [SeminormedCommRing A]
  (v : Valuation R ℝ≥0) (φ : R →+* A)

/-- Actual separated completion preserves EVERY prescribed coefficient value. -/
def completionHomeomorph :
    RelativeNormBoundedSpectrum v ((Completion.coeRingHom : A →+* Completion A).comp φ) ≃ₜ
      RelativeNormBoundedSpectrum v φ :=
  (NormBoundedSpectrum.completionHomeomorph (A := A)).subtype fun x => by rfl

@[simp]
theorem completionHomeomorph_val_apply
    (x : RelativeNormBoundedSpectrum v ((Completion.coeRingHom : A →+* Completion A).comp φ))
    (a : A) : (completionHomeomorph v φ x).1.1.val a = x.1.1.val (a : Completion A) := rfl

instance compactSpace : CompactSpace (RelativeNormBoundedSpectrum v φ) := by
  apply isCompact_iff_compactSpace.mp
  apply IsClosed.isCompact
  change IsClosed {x : NormBoundedSpectrum A | ∀ r : R, x.1.val (φ r) = v r}
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun r : R => isClosed_eq
    ((Spectrum.continuous_val_apply (φ r)).comp continuous_subtype_val) continuous_const

end RelativeNormBoundedSpectrum
end EnvelopeProperty.Berkovich
