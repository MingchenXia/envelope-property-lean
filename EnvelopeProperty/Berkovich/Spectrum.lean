/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# General affine spectra of real-valued ultrametric seminorms

`Spectrum A` is the space of real-valued multiplicative ultrametric seminorms on an
arbitrary commutative ring `A`, with the topology of pointwise convergence.
`RelativeSpectrum v A` fixes the restriction to a prescribed seminorm `v` on an
arbitrary coefficient ring `R`. Neither construction requires a field or a trivial
valuation. No boundedness relative to a Banach algebra norm is imposed here.

The usual affine analytification over a trivially valued field is identified with the
appropriate relative spectrum in `EnvelopeProperty.Berkovich.SpectrumBridge`.
-/

open scoped NNReal ENNReal Topology
open Topology

noncomputable section

namespace EnvelopeProperty.Berkovich

/-- The affine spectrum of real-valued multiplicative ultrametric seminorms on a ring. -/
@[ext]
structure Spectrum (A : Type*) [CommRing A] where
  /-- The multiplicative ultrametric seminorm of the point. -/
  val : Valuation A ℝ≥0

namespace Spectrum

variable {A : Type*} [CommRing A]

/-- Every real-valued valuation is a point of the affine seminorm spectrum. -/
def ofValuation (v : Valuation A ℝ≥0) : Spectrum A := ⟨v⟩

@[simp]
theorem ofValuation_val (v : Valuation A ℝ≥0) : (ofValuation v).val = v := rfl

/-- Evaluation of a seminorm at a ring element. -/
abbrev abs (a : A) (x : Spectrum A) : ℝ≥0 := x.val a

/-- The map that records all values of a seminorm. -/
def toFun (x : Spectrum A) : A → ℝ≥0 := fun a => x.val a

@[simp]
theorem toFun_apply (x : Spectrum A) (a : A) : toFun x a = x.val a := rfl

theorem ext_val {x y : Spectrum A} (h : ∀ a, x.val a = y.val a) : x = y :=
  Spectrum.ext (Valuation.ext h)

theorem toFun_injective : Function.Injective (toFun : Spectrum A → A → ℝ≥0) := by
  intro x y h
  exact ext_val fun a => congrFun h a

instance : TopologicalSpace (Spectrum A) :=
  TopologicalSpace.induced toFun inferInstance

theorem isInducing_toFun : IsInducing (toFun : Spectrum A → A → ℝ≥0) := ⟨rfl⟩

theorem isEmbedding_toFun : IsEmbedding (toFun : Spectrum A → A → ℝ≥0) :=
  ⟨isInducing_toFun, toFun_injective⟩

instance : T2Space (Spectrum A) := isEmbedding_toFun.t2Space

@[fun_prop]
theorem continuous_toFun : Continuous (toFun : Spectrum A → A → ℝ≥0) :=
  isInducing_toFun.continuous

@[fun_prop]
theorem continuous_abs (a : A) : Continuous (abs a : Spectrum A → ℝ≥0) :=
  (continuous_apply a).comp continuous_toFun

@[fun_prop]
theorem continuous_val_apply (a : A) : Continuous fun x : Spectrum A => x.val a :=
  continuous_abs a

/-- Continuity into a seminorm spectrum is equivalent to continuity of all evaluations. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {g : X → Spectrum A} :
    Continuous g ↔ ∀ a : A, Continuous fun z => (g z).val a := by
  rw [isInducing_toFun.continuous_iff, continuous_pi_iff]
  rfl

/-! ### Logarithmic evaluations -/

/-- The extended logarithm of a seminorm evaluation, with zero represented by `-∞`. -/
def logAbs (a : A) (x : Spectrum A) : EReal := ENNReal.log (x.val a : ℝ≥0∞)

@[fun_prop]
theorem continuous_logAbs (a : A) : Continuous (logAbs a : Spectrum A → EReal) :=
  ENNReal.continuous_log.comp (ENNReal.continuous_coe.comp (continuous_abs a))

@[simp]
theorem logAbs_one (x : Spectrum A) : logAbs (1 : A) x = 0 := by simp [logAbs]

@[simp]
theorem logAbs_zero (x : Spectrum A) : logAbs (0 : A) x = ⊥ := by simp [logAbs]

theorem logAbs_mul (a b : A) (x : Spectrum A) :
    logAbs (a * b) x = logAbs a x + logAbs b x := by
  simp [logAbs, ENNReal.coe_mul, ENNReal.log_mul_add]

theorem logAbs_pow (a : A) (n : ℕ) (x : Spectrum A) :
    logAbs (a ^ n) x = n * logAbs a x := by
  simp [logAbs, ENNReal.coe_pow, ENNReal.log_pow]

theorem logAbs_ne_top (a : A) (x : Spectrum A) : logAbs a x ≠ ⊤ := by
  simp [logAbs, ENNReal.log_eq_top_iff]

theorem logAbs_eq_bot_iff (a : A) (x : Spectrum A) : logAbs a x = ⊥ ↔ x.val a = 0 := by
  simp [logAbs, ENNReal.log_eq_bot_iff]

theorem logAbs_add_le (a b : A) (x : Spectrum A) :
    logAbs (a + b) x ≤ max (logAbs a x) (logAbs b x) := by
  simp only [logAbs]
  rw [← ENNReal.log_monotone.map_max]
  apply ENNReal.log_monotone
  rw [← ENNReal.coe_max]
  exact ENNReal.coe_le_coe.2 (x.val.map_add a b)

section comap

variable {B C : Type*} [CommRing B] [CommRing C]

/-- Restriction of seminorms along a unital ring homomorphism. -/
def comap (φ : A →+* B) (x : Spectrum B) : Spectrum A := ⟨x.val.comap φ⟩

@[simp]
theorem comap_val_apply (φ : A →+* B) (x : Spectrum B) (a : A) :
    (comap φ x).val a = x.val (φ a) := rfl

@[simp]
theorem logAbs_comap (φ : A →+* B) (a : A) (x : Spectrum B) :
    logAbs a (comap φ x) = logAbs (φ a) x := rfl

@[fun_prop]
theorem continuous_comap (φ : A →+* B) : Continuous (comap φ) := by
  rw [continuous_iff]
  exact fun a => continuous_abs (φ a)

@[simp]
theorem comap_id (x : Spectrum A) : comap (RingHom.id A) x = x :=
  ext_val fun _ => rfl

@[simp]
theorem comap_comp (φ : A →+* B) (ψ : B →+* C) (x : Spectrum C) :
    comap (ψ.comp φ) x = comap φ (comap ψ x) := rfl

end comap

end Spectrum

/-! ### Relative spectra over a prescribed base seminorm -/

/-- The closed locus of seminorms restricting to a specified seminorm on the base ring. -/
def relativeLocus {R : Type*} [CommRing R] (v : Valuation R ℝ≥0) (A : Type*)
    [CommRing A] [Algebra R A] : Set (Spectrum A) :=
  {x | ∀ r : R, x.val (algebraMap R A r) = v r}

@[simp]
theorem mem_relativeLocus {R : Type*} [CommRing R] (v : Valuation R ℝ≥0) (A : Type*)
    [CommRing A] [Algebra R A] (x : Spectrum A) :
    x ∈ relativeLocus v A ↔ ∀ r : R, x.val (algebraMap R A r) = v r := Iff.rfl

/-- The affine relative spectrum for an arbitrary commutative base ring with a fixed
real-valued ultrametric seminorm. -/
abbrev RelativeSpectrum {R : Type*} [CommRing R] (v : Valuation R ℝ≥0) (A : Type*)
    [CommRing A] [Algebra R A] : Type _ := relativeLocus v A

/-- Fixing the restriction of a seminorm to the coefficient ring is a closed condition. -/
theorem isClosed_relativeLocus {R : Type*} [CommRing R] (v : Valuation R ℝ≥0) (A : Type*)
    [CommRing A] [Algebra R A] : IsClosed (relativeLocus v A) := by
  have heq : relativeLocus v A =
      ⋂ r : R, {x : Spectrum A | x.val (algebraMap R A r) = v r} := by
    ext x
    simp only [mem_relativeLocus, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [heq]
  exact isClosed_iInter fun r =>
    isClosed_eq (Spectrum.continuous_abs (algebraMap R A r)) continuous_const

namespace RelativeSpectrum

variable {R : Type*} [CommRing R] {v : Valuation R ℝ≥0}
variable {A : Type*} [CommRing A] [Algebra R A]

/-- The prescribed base seminorm itself is a relative point over the base ring. -/
def self (v : Valuation R ℝ≥0) : RelativeSpectrum v R :=
  ⟨Spectrum.ofValuation v, fun r => by simp⟩

@[simp]
theorem self_val (v : Valuation R ℝ≥0) : (self v).1.val = v := rfl

/-- The relative spectrum is a closed subspace of the absolute seminorm spectrum. -/
theorem isClosedEmbedding_subtypeVal :
    IsClosedEmbedding ((↑) : RelativeSpectrum v A → Spectrum A) :=
  (isClosed_relativeLocus v A).isClosedEmbedding_subtypeVal

/-- The underlying seminorm of a relative point. -/
abbrev val (x : RelativeSpectrum v A) : Valuation A ℝ≥0 := x.1.val

@[simp]
theorem val_apply (x : RelativeSpectrum v A) (a : A) : val x a = x.1.val a := rfl

@[simp]
theorem val_algebraMap (x : RelativeSpectrum v A) (r : R) :
    val x (algebraMap R A r) = v r := x.2 r

theorem ext_val {x y : RelativeSpectrum v A} (h : ∀ a, val x a = val y a) : x = y :=
  Subtype.ext (Spectrum.ext_val h)

@[fun_prop]
theorem continuous_val_apply (a : A) : Continuous fun x : RelativeSpectrum v A => val x a :=
  (Spectrum.continuous_abs a).comp continuous_subtype_val

/-- Relative spectra retain the coordinate characterization of continuity. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {g : X → RelativeSpectrum v A} :
    Continuous g ↔ ∀ a : A, Continuous fun z => val (g z) a := by
  constructor
  · exact fun hg a => (continuous_val_apply a).comp hg
  · intro hg
    exact (Spectrum.continuous_iff.2 hg).subtype_mk fun z => (g z).2

section comap

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

/-- Restriction of a relative seminorm along a homomorphism of base algebras. -/
def comap (φ : A →ₐ[R] B) (x : RelativeSpectrum v B) : RelativeSpectrum v A :=
  ⟨Spectrum.comap φ.toRingHom x.1, fun r => by
    change x.1.val (φ (algebraMap R A r)) = v r
    rw [φ.commutes]
    exact x.2 r⟩

@[simp]
theorem comap_coe (φ : A →ₐ[R] B) (x : RelativeSpectrum v B) :
    (comap φ x : Spectrum A) = Spectrum.comap φ.toRingHom x.1 := rfl

@[simp]
theorem comap_val_apply (φ : A →ₐ[R] B) (x : RelativeSpectrum v B) (a : A) :
    val (comap φ x) a = val x (φ a) := rfl

@[fun_prop]
theorem continuous_comap (φ : A →ₐ[R] B) : Continuous (comap (v := v) φ) := by
  rw [continuous_iff]
  exact fun a => continuous_val_apply (φ a)

@[simp]
theorem comap_id (x : RelativeSpectrum v A) : comap (AlgHom.id R A) x = x :=
  ext_val fun _ => rfl

@[simp]
theorem comap_comp (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) (x : RelativeSpectrum v C) :
    comap (ψ.comp φ) x = comap φ (comap ψ x) := rfl

end comap

end RelativeSpectrum

end EnvelopeProperty.Berkovich
