/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Embedding a countable algebraically closed field of characteristic zero into `ℂ`

This file formalizes `lem:c0-embedding` of the blueprint chapter `char0.tex` (the
characteristic-zero route to Fang–Han–Xia, *The envelope property for unibranch projective
varieties*, Theorem 3.1 on `ℙⁿ`, under the standing assumption of FHX §5 that `k` is countable,
algebraically closed and of characteristic `0`): such a field admits a ring embedding `k → ℂ`.

## Proof

Let `s` be a transcendence basis of `k` over `ℤ` (it is countable, as `k` is) and `t` one of `ℂ`
over `ℤ`; `t` has the cardinality of `ℂ`
(`IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'`), so it is infinite and
there is an injection `e : s → t`. The family `e` is algebraically independent in `ℂ`, so
`ℤ[s] ≅ MvPolynomial s ℤ → ℂ`, `x ↦ e x`, is injective. Since `k` is algebraic over `ℤ[s]` and `ℂ`
is algebraically closed, this map extends to `k` (`IsAlgClosed.lift`).

## Main results

* `EnvelopeProperty.nonempty_ringHom_complex` (`lem:c0-embedding`).
-/

open Cardinal

noncomputable section

namespace EnvelopeProperty

/-- **`lem:c0-embedding`.** A countable algebraically closed field `k` of characteristic `0`
admits a ring embedding `k → ℂ` (every ring map out of a field is injective,
`RingHom.injective`). -/
theorem nonempty_ringHom_complex (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]
    [Countable k] : Nonempty (k →+* ℂ) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℤ k
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℤ ℂ
  have htc : #ℂ = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' ((↑) : t → ℂ) ht
      (le_of_eq Cardinal.mk_int) (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
  have hinf : (t : Set ℂ).Infinite := by
    rw [← Set.infinite_coe_iff, Cardinal.infinite_iff, ← htc, Cardinal.mk_complex]
    exact Cardinal.aleph0_le_continuum
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat s
  let e : s → t := fun x => hinf.natEmbedding t (f x)
  have he : Function.Injective e := (hinf.natEmbedding t).injective.comp hf
  have hind : AlgebraicIndependent ℤ (fun x : s => ((e x : t) : ℂ)) := ht.1.comp e he
  let R := Algebra.adjoin ℤ (Set.range ((↑) : s → k))
  let φ : R →ₐ[ℤ] ℂ :=
    (MvPolynomial.aeval fun x : s => ((e x : t) : ℂ)).comp hs.1.aevalEquiv.symm.toAlgHom
  have hφ : Function.Injective φ :=
    (algebraicIndependent_iff_injective_aeval.1 hind).comp hs.1.aevalEquiv.symm.injective
  let : Algebra R ℂ := φ.toRingHom.toAlgebra
  have : Module.IsTorsionFree R ℂ := Module.isTorsionFree_iff_algebraMap_injective.2 hφ
  have : Algebra.IsAlgebraic R k := hs.isAlgebraic
  exact ⟨(IsAlgClosed.lift : k →ₐ[R] ℂ).toRingHom⟩

end EnvelopeProperty
