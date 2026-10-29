/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.ClosedImmersion
import EnvelopeProperty.Berkovich.SpectrumSupport

/-!
# Supports and invariance under reduction

The support map from affine analytification to the Zariski prime spectrum is continuous
and surjective. The trivial seminorm of a prime quotient gives a point with any prescribed
support. Consequently analytic zero loci determine precisely the radicals of ideals,
and a regular function vanishes at every analytic point exactly when it is nilpotent.

The quotient by the nilradical induces a homeomorphism on analytifications. These results
justify the support convention of Fang–Han–Xia, §2.1, and the convention in §5 that closed
subsets carry their reduced induced structure. No finite type or reducedness assumption
on the algebra is required.
-/

open scoped NNReal Topology
open Topology

noncomputable section

namespace EnvelopeProperty.Berk

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-! ### The support map -/

/-- The underlying scheme point of an analytic point: the prime ideal where its
multiplicative seminorm vanishes. -/
def support (x : Berk k A) : PrimeSpectrum A := ⟨x.val.supp, inferInstance⟩

@[simp]
theorem support_asIdeal (x : Berk k A) : (support x).asIdeal = x.val.supp := rfl

@[simp]
theorem mem_support (x : Berk k A) (a : A) : a ∈ (support x).asIdeal ↔ x.val a = 0 :=
  Iff.rfl

/-- Analytic zero loci are inverse images of their scheme-theoretic zero loci. -/
theorem preimage_support_zeroLocus (I : Ideal A) :
    (support : Berk k A → PrimeSpectrum A) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) =
      zeroLocus I := rfl

/-- The support map is continuous for the Zariski topology on the prime spectrum. -/
@[fun_prop]
theorem continuous_support : Continuous (support : Berk k A → PrimeSpectrum A) := by
  exact Berkovich.Spectrum.continuous_support.comp continuous_toSpectrum

/-- Supports commute with pullback along an algebra homomorphism. -/
@[simp]
theorem support_comap {B : Type*} [CommRing B] [Algebra k B]
    (φ : A →ₐ[k] B) (y : Berk k B) :
    support (comap φ y) = PrimeSpectrum.comap φ.toRingHom (support y) :=
  Berkovich.Spectrum.support_comap φ.toRingHom y.toSpectrum

/-! ### A point over every prime -/

/-- The point with support `p` obtained by pulling back the trivial seminorm of `A ⧸ p`. -/
def primePoint (p : PrimeSpectrum A) : Berk k A :=
  quotientComap p.asIdeal (triv : Berk k (A ⧸ p.asIdeal))

@[simp]
theorem primePoint_val_eq_zero_iff (p : PrimeSpectrum A) (a : A) :
    (primePoint (k := k) p).val a = 0 ↔ a ∈ p.asIdeal := by
  change (triv : Berk k (A ⧸ p.asIdeal)).val (Ideal.Quotient.mk p.asIdeal a) = 0 ↔ _
  by_cases ha : a ∈ p.asIdeal
  · simp [Ideal.Quotient.eq_zero_iff_mem.2 ha, ha]
  · have hne : Ideal.Quotient.mk p.asIdeal a ≠ 0 :=
      mt Ideal.Quotient.eq_zero_iff_mem.1 ha
    rw [triv_val_of_ne_zero hne]
    simp [ha]

@[simp]
theorem support_primePoint (p : PrimeSpectrum A) : support (primePoint (k := k) p) = p := by
  apply PrimeSpectrum.ext
  exact Ideal.ext fun a => primePoint_val_eq_zero_iff p a

/-- Every scheme point is the support of an analytic point over a trivially valued field. -/
theorem support_surjective : Function.Surjective (support : Berk k A → PrimeSpectrum A) :=
  fun p => ⟨primePoint p, support_primePoint p⟩

/-! ### Analytic vanishing and radicals -/

/-- The analytic zero locus only depends on the radical of its ideal. -/
@[simp]
theorem zeroLocus_radical (I : Ideal A) : zeroLocus (k := k) I.radical = zeroLocus I := by
  ext x
  exact (inferInstance : x.val.supp.IsPrime).radical_le_iff

/-- Inclusion of analytic zero loci is exactly reverse inclusion in the ideal radical. -/
theorem zeroLocus_subset_zeroLocus_iff (I J : Ideal A) :
    zeroLocus (k := k) I ⊆ zeroLocus J ↔ J ≤ I.radical := by
  rw [← preimage_support_zeroLocus I, ← preimage_support_zeroLocus J,
    support_surjective.preimage_subset_preimage_iff,
    PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]

/-- Two ideals have the same analytic zero locus exactly when they have the same radical. -/
theorem zeroLocus_eq_zeroLocus_iff (I J : Ideal A) :
    zeroLocus (k := k) I = zeroLocus J ↔ I.radical = J.radical := by
  rw [← preimage_support_zeroLocus I, ← preimage_support_zeroLocus J,
    support_surjective.preimage_injective.eq_iff,
    PrimeSpectrum.zeroLocus_eq_iff]

/-! ### Nilpotents -/

/-- Every analytic support contains the nilradical. -/
theorem nilradical_le_supp (x : Berk k A) : nilradical A ≤ x.val.supp :=
  Berkovich.Spectrum.nilradical_le_supp x.toSpectrum

/-- Nilpotent regular functions vanish at every analytic point. -/
theorem val_eq_zero_of_isNilpotent (x : Berk k A) {a : A} (ha : IsNilpotent a) :
    x.val a = 0 :=
  Berkovich.Spectrum.val_eq_zero_of_isNilpotent x.toSpectrum ha

/-- Functions that agree modulo nilpotents have the same value at every analytic point. -/
theorem val_eq_of_sub_isNilpotent (x : Berk k A) {a b : A} (hab : IsNilpotent (a - b)) :
    x.val a = x.val b :=
  Berkovich.Spectrum.val_eq_of_sub_isNilpotent x.toSpectrum hab

/-- Logarithmic evaluations also descend through reduction. -/
theorem logAbs_eq_of_sub_isNilpotent (x : Berk k A) {a b : A}
    (hab : IsNilpotent (a - b)) : logAbs a x = logAbs b x :=
  Berkovich.Spectrum.logAbs_eq_of_sub_isNilpotent x.toSpectrum hab

/-- An element vanishes at every analytic point exactly when it is nilpotent. -/
theorem val_eq_zero_forall_iff_isNilpotent (a : A) :
    (∀ x : Berk k A, x.val a = 0) ↔ IsNilpotent a := by
  constructor
  · intro ha
    rw [← mem_nilradical, PrimeSpectrum.nilradical_eq_iInf, Ideal.mem_iInf]
    intro p
    exact (primePoint_val_eq_zero_iff p a).1 (ha (primePoint p))
  · exact fun ha x => val_eq_zero_of_isNilpotent x ha

@[simp]
theorem zeroLocus_nilradical : zeroLocus (k := k) (nilradical A) = Set.univ := by
  ext x
  exact iff_true_intro (nilradical_le_supp x)

/-! ### Invariance under reduction -/

/-- The quotient by the nilradical induces a homeomorphism on analytifications. -/
def reductionHomeomorph : Berk k (A ⧸ nilradical A) ≃ₜ Berk k A where
  toFun := quotientComap (nilradical A)
  invFun x := quotientLift (nilradical A) x (nilradical_le_supp x)
  left_inv := quotientLift_quotientComap (nilradical A)
  right_inv x := quotientComap_quotientLift (nilradical A) x (nilradical_le_supp x)
  continuous_toFun := continuous_quotientComap (nilradical A)
  continuous_invFun := (continuous_quotientLift (nilradical A)).comp
    (continuous_id.subtype_mk fun x => nilradical_le_supp x)

@[simp]
theorem reductionHomeomorph_apply (y : Berk k (A ⧸ nilradical A)) :
    reductionHomeomorph y = quotientComap (nilradical A) y := rfl

@[simp]
theorem reductionHomeomorph_val_apply (y : Berk k (A ⧸ nilradical A)) (a : A) :
    (reductionHomeomorph y).val a = y.val (Ideal.Quotient.mk (nilradical A) a) := rfl

@[simp]
theorem reductionHomeomorph_symm_val_mk (x : Berk k A) (a : A) :
    (reductionHomeomorph.symm x).val (Ideal.Quotient.mk (nilradical A) a) = x.val a := rfl

end EnvelopeProperty.Berk
