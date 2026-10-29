/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumQuotient

/-!
# Supports of general seminorms

For every commutative ring the support map from its real-valued seminorm spectrum
to its prime spectrum is continuous and surjective. Absolute seminorm zero loci
detect exactly the radicals of ideals.

For a relative spectrum the support is continuous and its contraction to the base
ring is exactly the support of the prescribed base seminorm. Surjectivity of an
arbitrary relative support map is not asserted.
-/

open scoped NNReal Topology
open Topology Classical

noncomputable section

namespace EnvelopeProperty.Berkovich

namespace Spectrum

variable {A : Type*} [CommRing A]

/-- The prime ideal where a seminorm vanishes. -/
def support (x : Spectrum A) : PrimeSpectrum A := ⟨x.val.supp, inferInstance⟩

@[simp]
theorem support_asIdeal (x : Spectrum A) : (support x).asIdeal = x.val.supp := rfl

@[simp]
theorem mem_support (x : Spectrum A) (a : A) : a ∈ (support x).asIdeal ↔ x.val a = 0 :=
  Iff.rfl

theorem preimage_support_zeroLocus (I : Ideal A) :
    (support : Spectrum A → PrimeSpectrum A) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) =
      zeroLocus I := rfl

@[fun_prop]
theorem continuous_support : Continuous (support : Spectrum A → PrimeSpectrum A) := by
  rw [continuous_iff_isClosed]
  intro Z hZ
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).1 hZ
  rw [preimage_support_zeroLocus]
  exact isClosed_zeroLocus I

@[simp]
theorem support_comap {B : Type*} [CommRing B] (φ : A →+* B) (y : Spectrum B) :
    support (comap φ y) = PrimeSpectrum.comap φ (support y) :=
  PrimeSpectrum.ext (Valuation.comap_supp y.val φ)

/-- A point with any prescribed support, from the trivial seminorm of its prime quotient. -/
def primePoint (p : PrimeSpectrum A) : Spectrum A :=
  quotientComap p.asIdeal (ofValuation (1 : Valuation (A ⧸ p.asIdeal) ℝ≥0))

@[simp]
theorem primePoint_val_eq_zero_iff (p : PrimeSpectrum A) (a : A) :
    (primePoint p).val a = 0 ↔ a ∈ p.asIdeal := by
  change (1 : Valuation (A ⧸ p.asIdeal) ℝ≥0) (Ideal.Quotient.mk p.asIdeal a) = 0 ↔ _
  by_cases ha : a ∈ p.asIdeal
  · simp [Ideal.Quotient.eq_zero_iff_mem.2 ha, ha]
  · have hne : Ideal.Quotient.mk p.asIdeal a ≠ 0 :=
      mt Ideal.Quotient.eq_zero_iff_mem.1 ha
    rw [Valuation.one_apply_of_ne_zero hne]
    simp [ha]

@[simp]
theorem support_primePoint (p : PrimeSpectrum A) : support (primePoint p) = p := by
  apply PrimeSpectrum.ext
  exact Ideal.ext fun a => primePoint_val_eq_zero_iff p a

theorem support_surjective : Function.Surjective (support : Spectrum A → PrimeSpectrum A) :=
  fun p => ⟨primePoint p, support_primePoint p⟩

@[simp]
theorem zeroLocus_radical (I : Ideal A) : zeroLocus I.radical = zeroLocus I := by
  ext x
  exact (inferInstance : x.val.supp.IsPrime).radical_le_iff

theorem zeroLocus_subset_zeroLocus_iff (I J : Ideal A) :
    zeroLocus I ⊆ zeroLocus J ↔ J ≤ I.radical := by
  rw [← preimage_support_zeroLocus I, ← preimage_support_zeroLocus J,
    support_surjective.preimage_subset_preimage_iff,
    PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]

theorem zeroLocus_eq_zeroLocus_iff (I J : Ideal A) :
    zeroLocus I = zeroLocus J ↔ I.radical = J.radical := by
  rw [← preimage_support_zeroLocus I, ← preimage_support_zeroLocus J,
    support_surjective.preimage_injective.eq_iff,
    PrimeSpectrum.zeroLocus_eq_iff]

/-- Functions equal modulo nilpotents have equal values at every absolute seminorm. -/
theorem val_eq_of_sub_isNilpotent (x : Spectrum A) {a b : A} (hab : IsNilpotent (a - b)) :
    x.val a = x.val b := by
  have h := x.val.map_add_supp b (nilradical_le_supp x (mem_nilradical.2 hab))
  simpa only [← add_sub_assoc, add_sub_cancel_left] using h

theorem logAbs_eq_of_sub_isNilpotent (x : Spectrum A) {a b : A}
    (hab : IsNilpotent (a - b)) : logAbs a x = logAbs b x := by
  simp only [logAbs, val_eq_of_sub_isNilpotent x hab]

/-- An element vanishes at every absolute seminorm precisely when it is nilpotent. -/
theorem val_eq_zero_forall_iff_isNilpotent (a : A) :
    (∀ x : Spectrum A, x.val a = 0) ↔ IsNilpotent a := by
  constructor
  · intro ha
    rw [← mem_nilradical, PrimeSpectrum.nilradical_eq_iInf, Ideal.mem_iInf]
    intro p
    exact (primePoint_val_eq_zero_iff p a).1 (ha (primePoint p))
  · exact fun ha x => val_eq_zero_of_isNilpotent x ha

@[simp]
theorem zeroLocus_nilradical : zeroLocus (nilradical A) = Set.univ := by
  ext x
  exact iff_true_intro (nilradical_le_supp x)

end Spectrum

namespace RelativeSpectrum

variable {R : Type*} [CommRing R] {v : Valuation R ℝ≥0}
variable {A : Type*} [CommRing A] [Algebra R A]

/-- The underlying scheme point of a relative seminorm. -/
def support (x : RelativeSpectrum v A) : PrimeSpectrum A := Spectrum.support x.1

@[simp]
theorem support_asIdeal (x : RelativeSpectrum v A) : (support x).asIdeal = x.1.val.supp := rfl

@[fun_prop]
theorem continuous_support : Continuous (support : RelativeSpectrum v A → PrimeSpectrum A) :=
  Spectrum.continuous_support.comp continuous_subtype_val

@[simp]
theorem support_comap {B : Type*} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (y : RelativeSpectrum v B) :
    support (comap φ y) = PrimeSpectrum.comap φ.toRingHom (support y) :=
  Spectrum.support_comap φ.toRingHom y.1

/-- The support of a relative point contracts exactly to the support of the base seminorm. -/
theorem supp_comap_algebraMap (x : RelativeSpectrum v A) :
    Ideal.comap (algebraMap R A) x.1.val.supp = v.supp := by
  ext r
  simp only [Ideal.mem_comap, Valuation.mem_supp_iff, x.2 r]

/-- Every relative scheme support lies over the prescribed base scheme support. -/
@[simp]
theorem support_base (x : RelativeSpectrum v A) :
    PrimeSpectrum.comap (algebraMap R A) (support x) =
      Spectrum.support (Spectrum.ofValuation v) :=
  PrimeSpectrum.ext (supp_comap_algebraMap x)

end RelativeSpectrum

end EnvelopeProperty.Berkovich
