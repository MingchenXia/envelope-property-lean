/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# The dimension of an affine variety is a natural number

Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Lemma 5.23
(`lem:projection-existence`) is stated for an affine variety `Y` "of dimension `n ≥ 1`". For the
formal statement (`EnvelopeProperty.ProjectionExistence`) the dimension is the Krull dimension
`ringKrullDim A` of `A = k[Y]`, a priori an element of `WithBot ℕ∞`. This file shows that it is a
natural number for a nonzero algebra of finite type over a field, and that it is at least `1` as
soon as there are two comparable primes.

* `ringKrullDim_le_of_isIntegral`: if `S` is integral over `R`, then `dim S ≤ dim R`
  (incomparability: contraction is strictly monotone on primes).
* `exists_ringKrullDim_eq_natCast`: `dim R ∈ ℕ` for `R ≠ 0` of finite type over a field (Noether
  normalization `exists_integral_inj_algHom_of_fg` and `dim k[x₁, …, xₛ] = s`).
* `one_le_ringKrullDim_of_lt`: two primes `P < Q` give `1 ≤ dim R`.
-/

namespace EnvelopeProperty

/-- **Incomparability bounds the dimension.** If `S` is integral over `R` (via `f`), then
`dim S ≤ dim R`: the contraction `PrimeSpectrum S → PrimeSpectrum R` is strictly monotone. -/
theorem ringKrullDim_le_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.IsIntegral) : ringKrullDim S ≤ ringKrullDim R := by
  let := f.toAlgebra
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f) fun P Q hPQ => ?_
  obtain ⟨x, hxQ, hxP⟩ := SetLike.exists_of_lt (show P.asIdeal < Q.asIdeal from hPQ)
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff (R := R) hPQ.le ⟨hxQ, hxP⟩ (hf x)

/-- **The dimension of an affine variety is a natural number**: a nonzero algebra of finite type
over a field has Krull dimension in `ℕ` (at most the number of variables of a Noether
normalization). -/
theorem exists_ringKrullDim_eq_natCast (k R : Type*) [Field k] [CommRing R] [Nontrivial R]
    [Algebra k R] [Algebra.FiniteType k R] : ∃ n : ℕ, ringKrullDim R = n := by
  obtain ⟨s, g, -, hg⟩ := exists_integral_inj_algHom_of_fg k R
  have hle : ringKrullDim R ≤ s := by
    have h := ringKrullDim_le_of_isIntegral (g : MvPolynomial (Fin s) k →+* R) hg
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim R := ringKrullDim_nonneg_of_nontrivial
  generalize ringKrullDim R = d at hle h0
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast, WithBot.coe_le_coe, top_le_iff] at hle
      exact absurd hle (ENat.natCast_ne_top s)
    | coe d => exact ⟨d, rfl⟩

/-- Two comparable primes give dimension at least one. -/
theorem one_le_ringKrullDim_of_lt {R : Type*} [CommRing R] {P Q : Ideal R} [P.IsPrime]
    [Q.IsPrime] (h : P < Q) : 1 ≤ ringKrullDim R :=
  Order.one_le_krullDim_iff.mpr ⟨⟨P, ‹_›⟩, ⟨Q, ‹_›⟩, h⟩

end EnvelopeProperty
