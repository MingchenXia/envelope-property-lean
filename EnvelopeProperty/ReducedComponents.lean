/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Actual minimal components and original reduced quotient maps

The component index is the actual minimal-prime subtype of the ORIGINAL
ideal. Genuine Noetherian finiteness supplies that index; the whole product
quotient map has exact radical kernel. Literal reduced and unreduced quotient
maps retain every original element, true finiteness and whole prime lifts.
No component list, quotient embedding or support-surjectivity certificate is
an input. Algebraic reduction does not alter any independently supplied model
ideal data.
-/

noncomputable section
namespace EnvelopeProperty.ReducedComponents
variable {R : Type*} [CommRing R]

/-- The actual minimal primes of the ORIGINAL ideal, not an assumed component list. -/
abbrev Index (I : Ideal R) := I.minimalPrimes

/-- Every actual component index has its genuinely prime original ideal. -/
instance indexPrime (I : Ideal R) (p : Index I) : p.1.IsPrime := p.2.isPrime

/-- Genuine Noetherian minimal-prime finiteness supplies the entire component index. -/
instance finiteIndex (I : Ideal R) [IsNoetherianRing R] : Finite (Index I) :=
  (I.finite_minimalPrimes_of_isNoetherianRing R).to_subtype

/-- The actual original prime quotient of one minimal component. -/
abbrev Component (I : Ideal R) (p : Index I) := R ⧸ p.1

/-- The whole original ring map into ALL actual minimal prime quotients. -/
def ringMap (I : Ideal R) : R →+* ∀ p : Index I, Component I p :=
  RingHom.pi fun p => Ideal.Quotient.mk p.1

/-- Every original ring element retains its actual quotient in each component. -/
theorem ringMap_apply (I : Ideal R) (r : R) (p : Index I) :
    ringMap I r p = Ideal.Quotient.mk p.1 r := rfl

/-- The actual entire map kernel is precisely the original ideal radical. -/
theorem ker_ringMap (I : Ideal R) : RingHom.ker (ringMap I) = I.radical := by
  rw [ringMap, Ideal.ker_Pi_Quotient_mk]
  simpa only [sInf_eq_iInf, iInf_subtype] using I.sInf_minimalPrimes

/-- The genuine reduced quotient embeds into the product of the actual original components. -/
def reducedEmbedding (I : Ideal R) : (R ⧸ I.radical) →+* ∀ p : Index I, Component I p :=
  Ideal.Quotient.lift I.radical (ringMap I) (ker_ringMap I).symm.le

/-- This actual reduction map preserves every original ring element in every component. -/
theorem reducedEmbedding_mk (I : Ideal R) (r : R) (p : Index I) :
    reducedEmbedding I (Ideal.Quotient.mk I.radical r) p = Ideal.Quotient.mk p.1 r := rfl

/-- Genuine minimal-prime intersection makes this entire reduced embedding injective. -/
theorem reducedEmbedding_injective (I : Ideal R) : Function.Injective (reducedEmbedding I) := by
  apply RingHom.lift_injective_of_ker_le_ideal
  exact (ker_ringMap I).le

/-- The actual unreduced original quotient map, preserving its original point restrictions. -/
def originalMap (I : Ideal R) : (R ⧸ I) →+* ∀ p : Index I, Component I p :=
  Ideal.Quotient.lift I (ringMap I) (I.le_radical.trans (ker_ringMap I).symm.le)

/-- Original quotient elements retain every actual component value. -/
theorem originalMap_mk (I : Ideal R) (r : R) (p : Index I) :
    originalMap I (Ideal.Quotient.mk I r) p = Ideal.Quotient.mk p.1 r := rfl

/-- The whole unreduced quotient map factors through the literal algebraic reduction. -/
theorem originalMap_eq_reducedEmbedding_comp (I : Ideal R) :
    originalMap I = (reducedEmbedding I).comp (Ideal.Quotient.factor I.le_radical) := by
  apply Ideal.Quotient.ringHom_ext
  ext r p
  rfl

/-- The whole original product map is genuinely finite over every Noetherian original ring. -/
theorem ringMap_finite (I : Ideal R) [IsNoetherianRing R] : (ringMap I).Finite := by
  change Module.Finite R (∀ p : Index I, Component I p)
  infer_instance

/-- The original quotient map has exactly the radical-image kernel, retaining its original nilpotents. -/
theorem ker_originalMap (I : Ideal R) :
    RingHom.ker (originalMap I) = I.radical.map (Ideal.Quotient.mk I) := by
  rw [originalMap, Ideal.ker_quotient_lift, ker_ringMap]

/-- The exact kernel in the original quotient is its nilradical, not an alteration of any other ideal data. -/
theorem ker_originalMap_eq_nilradical (I : Ideal R) :
    RingHom.ker (originalMap I) = nilradical (R ⧸ I) := by
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change ringMap I r = 0 ↔ Ideal.Quotient.mk I r ∈ nilradical (R ⧸ I)
  rw [← RingHom.mem_ker, ker_ringMap]
  simp only [Ideal.mem_radical_iff, mem_nilradical, IsNilpotent,
    ← map_pow, Ideal.Quotient.eq_zero_iff_mem]

/-- The genuine reduced product embedding is finite, with the original scalar action. -/
theorem reducedEmbedding_finite (I : Ideal R) [IsNoetherianRing R] :
    (reducedEmbedding I).Finite := by
  have he : (reducedEmbedding I).comp (Ideal.Quotient.mk I.radical) = ringMap I := by
    ext r p
    rfl
  exact RingHom.Finite.of_comp_finite (he.symm ▸ ringMap_finite I)

/-- The actual map out of the entire original quotient is finite. -/
theorem originalMap_finite (I : Ideal R) [IsNoetherianRing R] : (originalMap I).Finite := by
  have he : (originalMap I).comp (Ideal.Quotient.mk I) = ringMap I := by
    ext r p
    rfl
  exact RingHom.Finite.of_comp_finite (he.symm ▸ ringMap_finite I)

/-- Every entire prime of the literal reduced quotient has an actual component lift. -/
theorem reducedEmbedding_comap_surjective (I : Ideal R) [IsNoetherianRing R] :
    Function.Surjective (PrimeSpectrum.comap (reducedEmbedding I)) := by
  let : Algebra (R ⧸ I.radical) (∀ p : Index I, Component I p) := (reducedEmbedding I).toAlgebra
  have : Module.Finite (R ⧸ I.radical) (∀ p : Index I, Component I p) := reducedEmbedding_finite I
  have : FaithfulSMul (R ⧸ I.radical) (∀ p : Index I, Component I p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (reducedEmbedding_injective I)
  exact Algebra.IsIntegral.comap_surjective _ _

/-- Actual integral lying-over and the exact nilradical kernel lift every whole prime of the ORIGINAL quotient. -/
theorem originalMap_comap_surjective (I : Ideal R) [IsNoetherianRing R] :
    Function.Surjective (PrimeSpectrum.comap (originalMap I)) := by
  let : Algebra (R ⧸ I) (∀ p : Index I, Component I p) := (originalMap I).toAlgebra
  have : Module.Finite (R ⧸ I) (∀ p : Index I, Component I p) := originalMap_finite I
  intro ⟨P, hP⟩
  have : P.IsPrime := hP
  have hker : (⊥ : Ideal (∀ p : Index I, Component I p)).under (R ⧸ I) ≤ P := by
    change RingHom.ker (originalMap I) ≤ P
    rw [ker_originalMap_eq_nilradical]
    exact nilradical_le_prime P
  obtain ⟨Q, _, hQ, rfl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P
    (⊥ : Ideal (∀ p : Index I, Component I p)) hker
  exact ⟨⟨Q, hQ⟩, rfl⟩

end EnvelopeProperty.ReducedComponents
