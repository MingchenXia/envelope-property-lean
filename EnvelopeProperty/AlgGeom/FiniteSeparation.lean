/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Separating a closed subset from the rest of its preimage under a finite map

This file proves the commutative algebra behind the choice of `g` in the proof of Fang–Han–Xia,
*The envelope property for unibranch projective varieties*, Theorem 5.25
(`thm:normal-local-regularization`).

Let `φ : B → A` be integral with `A` noetherian, `π = Spec φ : U = Spec A → S = Spec B`, and let
`W = V(J) ⊆ U` be a nonempty closed subset such that `π|_W` is a closed immersion, i.e.
`B → A / J` is surjective. Put `𝔭 = φ⁻¹(J)`, so that `π(W) = V(𝔭)`, `π⁻¹(π(W)) = V(𝔭 A)`, and
`Z' = π⁻¹(π(W)) \ W` is the set of primes `Q` with `𝔭 ⊆ φ⁻¹(Q)` and `J ⊄ Q`.

`exists_separation` produces `b ∈ B` such that, on `U_b = π⁻¹(S_b)`, the set `W ∩ U_b` is
nonempty and `Z' ∩ U_b` is closed and disjoint from `W ∩ U_b`; explicitly, an element `f₁ ∈ A`
vanishing on `Z'` with `φ b - f₁ ∈ J`. In `A_{φ b}`, the elements `f₁ / φ b` and
`(φ b - f₁) / φ b` are then a partition of unity separating `Z' ∩ U_b` from `W ∩ U_b`.

## The argument

The source argues by dimension: every irreducible component of `closure(Z')` meets `Z'` and has
dimension at most `dim W`, hence does not contain an irreducible component of `W`. Here we use
instead that the irreducible components of `W` are irreducible components of `π⁻¹(π(W))`:

* every minimal prime `P` of `J` is a minimal prime of `𝔭 A` (`mem_minimalPrimes_map_comap`):
  if `𝔭 A ⊆ Q ⊆ P`, then `φ⁻¹(Q) ⊇ 𝔭` is the contraction of a prime `Q' ⊇ J`
  (as `B / 𝔭 ≅ A / J`), and incomparability for the integral `φ` shows that `Q ⊊ P` would give
  `Q' ⊊ P`, contradicting minimality of `P` over `J`;
* `K`, the intersection of the finitely many minimal primes of `𝔭 A` not containing `J`, vanishes
  on `Z'` (every point of `Z'` specializes from such a minimal prime) and is not contained in a
  chosen minimal prime `P` of `J` (prime avoidance and minimality of `P` over `𝔭 A`);
* `f₁ ∈ K \ P` and `b ∈ B` with `φ b ≡ f₁ mod J` (surjectivity of `B → A / J`) do the job.

No dimension theory is needed; only incomparability (`Ideal.comap_lt_comap_of_integral_mem_sdiff`)
and the finiteness of the set of minimal primes in a noetherian ring.

## Shrinking the target around a fibre

`exists_dvd_notMem_of_map_eq_top` is the shrinking at the end of the proof of FHX Lemma 5.23
(`lem:projection-existence`): if `J A = ⊤` for an ideal `J` of a ring `A₀` mapping to `A`
(the principal opens `D(c)`, `c ∈ J`, cover `Spec A`), there are `c ∈ J` and `b ∉ 𝔮` with
`π⁻¹(D(b)) ⊆ D(c)`. The fibre of `π` over `𝔮` consists of minimal primes of `𝔮 A`
(`mem_minimalPrimes_map_of_comap_eq`), hence is finite, and prime avoidance applies.
-/

namespace EnvelopeProperty

open Ideal

variable {A B : Type*} [CommRing A] [CommRing B]

/-- If `B → A / J` is surjective, every prime `𝔮 ⊇ φ⁻¹(J)` of `B` is the contraction of a prime
`Q ⊇ J` of `A`. -/
theorem exists_isPrime_comap_eq_of_surjective (φ : B →+* A) (J : Ideal A)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp φ)) (𝔮 : Ideal B) [𝔮.IsPrime]
    (h : J.comap φ ≤ 𝔮) : ∃ Q : Ideal A, Q.IsPrime ∧ J ≤ Q ∧ Q.comap φ = 𝔮 := by
  set ψ := (Ideal.Quotient.mk J).comp φ
  have hker : RingHom.ker ψ = J.comap φ := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
  have hk : RingHom.ker ψ ≤ 𝔮 := hker ▸ h
  have hprime : (𝔮.map ψ).IsPrime := Ideal.map_isPrime_of_surjective hsurj hk
  refine ⟨(𝔮.map ψ).comap (Ideal.Quotient.mk J), Ideal.comap_isPrime _ _, ?_, ?_⟩
  · intro x hx
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  · rw [Ideal.comap_comap, Ideal.comap_map_of_surjective' ψ hsurj, sup_eq_left.mpr hk]

/-- If `B → A / J` is surjective, the contraction `Q ↦ φ⁻¹(Q)` reflects inclusions between primes
containing `J`. -/
theorem le_of_comap_le_of_surjective (φ : B →+* A) (J : Ideal A)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp φ)) {Q₁ Q₂ : Ideal A}
    (h₁ : J ≤ Q₁) (h₂ : J ≤ Q₂) (hc : Q₁.comap φ ≤ Q₂.comap φ) : Q₁ ≤ Q₂ := by
  intro x hx
  obtain ⟨b, hb⟩ := hsurj (Ideal.Quotient.mk J x)
  have hbx : φ b - x ∈ J := Ideal.Quotient.eq.mp hb
  have hb₁ : φ b ∈ Q₁ := by simpa using Q₁.add_mem (h₁ hbx) hx
  have hb₂ : φ b ∈ Q₂ := hc hb₁
  simpa using Q₂.sub_mem hb₂ (h₂ hbx)

/-- **The irreducible components of `W` are irreducible components of `π⁻¹(π(W))`.** If `φ` is
integral and `B → A / J` is surjective, every minimal prime of `J` is a minimal prime of
`φ⁻¹(J) A`. -/
theorem mem_minimalPrimes_map_comap (φ : B →+* A) (hφ : φ.IsIntegral) (J : Ideal A)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp φ)) {P : Ideal A}
    (hP : P ∈ J.minimalPrimes) : P ∈ ((J.comap φ).map φ).minimalPrimes := by
  let := φ.toAlgebra
  have hPprime : P.IsPrime := hP.1.1
  refine ⟨⟨hPprime, Ideal.map_comap_le.trans hP.1.2⟩, fun {Q} hQ hQP => ?_⟩
  obtain ⟨hQprime, hLQ⟩ := hQ
  by_contra hPQ
  have hlt : Q < P := lt_of_le_not_ge hQP hPQ
  obtain ⟨x, hxP, hxQ⟩ := SetLike.exists_of_lt hlt
  have hclt : Q.comap φ < P.comap φ :=
    Ideal.comap_lt_comap_of_integral_mem_sdiff (R := B) hQP ⟨hxP, hxQ⟩ (hφ x)
  obtain ⟨Q', hQ'prime, hJQ', hQ'c⟩ := exists_isPrime_comap_eq_of_surjective φ J hsurj
    (Q.comap φ) (Ideal.map_le_iff_le_comap.mp hLQ)
  have hQ'P : Q' ≤ P := le_of_comap_le_of_surjective φ J hsurj hJQ' hP.1.2 (hQ'c ▸ hclt.le)
  have hPQ' : P ≤ Q' := hP.2 ⟨hQ'prime, hJQ'⟩ hQ'P
  have : Q'.comap φ = P.comap φ := by rw [le_antisymm hQ'P hPQ']
  exact hclt.ne (hQ'c ▸ this)

/-- **The choice of `g` in the proof of FHX Theorem 5.25** (`thm:normal-local-regularization`),
in commutative algebra. Let `φ : B → A` be integral, `A` noetherian, and `J ≠ ⊤` an ideal of `A`
with `B → A / J` surjective (`W = V(J)` is nonempty and `π = Spec φ` restricts to a closed
immersion on `W`). There are `b ∈ B` and `f₁ ∈ A` such that

* `W ∩ D(φ b) ≠ ∅`: some prime `P ⊇ J` does not contain `φ b`;
* `φ b - f₁ ∈ J`, i.e. `f₁ = φ b` on `W`;
* `f₁` vanishes on `Z' = π⁻¹(π(W)) \ W`: `f₁ ∈ Q` for every prime `Q` with
  `φ⁻¹(J) ⊆ φ⁻¹(Q)` and `J ⊄ Q`.

So on `π⁻¹(S_b) = D(φ b)`, `f₁ / φ b + (φ b - f₁) / φ b = 1` separates `Z'` from `W`. -/
theorem exists_separation (φ : B →+* A) (hφ : φ.IsIntegral) [IsNoetherianRing A] (J : Ideal A)
    (hJ : J ≠ ⊤) (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp φ)) :
    ∃ b : B, (∃ P : Ideal A, P.IsPrime ∧ J ≤ P ∧ φ b ∉ P) ∧ ∃ f₁ : A, φ b - f₁ ∈ J ∧
      ∀ Q : Ideal A, Q.IsPrime → J.comap φ ≤ Q.comap φ → ¬ J ≤ Q → f₁ ∈ Q := by
  classical
  set L := (J.comap φ).map φ with hL
  have hfin : L.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing A L
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  have := hm.isPrime
  obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le hJm
  have hPprime : P.IsPrime := hP.1.1
  have hPL : P ∈ L.minimalPrimes := mem_minimalPrimes_map_comap φ hφ J hsurj hP
  -- `K`: the intersection of the minimal primes of `𝔭 A` not containing `J`.
  set S : Finset (Ideal A) := hfin.toFinset.filter (fun Q => ¬ J ≤ Q) with hS
  have hKP : ¬ S.inf id ≤ P := by
    rw [hPprime.inf_le']
    rintro ⟨Q, hQS, hQP⟩
    rw [hS, Finset.mem_filter, Set.Finite.mem_toFinset] at hQS
    exact hQS.2 (hP.1.2.trans (hPL.2 hQS.1.1 hQP))
  obtain ⟨x, hxK, hxP⟩ := Set.not_subset.mp hKP
  obtain ⟨b, hb⟩ := hsurj (Ideal.Quotient.mk J x)
  have hbx : φ b - x ∈ J := Ideal.Quotient.eq.mp hb
  refine ⟨b, ⟨P, hPprime, hP.1.2, fun hbP => hxP ?_⟩, x, hbx, ?_⟩
  · simpa using P.sub_mem hbP (hP.1.2 hbx)
  · intro Q hQ hcQ hJQ
    obtain ⟨Q₁, hQ₁, hQ₁Q⟩ := Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mpr hcQ)
    have hQ₁S : Q₁ ∈ S := by
      rw [hS, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨hQ₁, fun h => hJQ (h.trans hQ₁Q)⟩
    exact hQ₁Q (Finset.inf_le (f := id) hQ₁S hxK)

/-! ### Shrinking the target of a finite map around a fibre -/

/-- **The fibre of an integral map consists of minimal primes**: if `φ` is integral, every prime
`Q` of `A` lying over a prime `𝔮` of `B` is a minimal prime of `𝔮 A` (incomparability). -/
theorem mem_minimalPrimes_map_of_comap_eq (φ : B →+* A) (hφ : φ.IsIntegral) {𝔮 : Ideal B}
    {Q : Ideal A} [hQ : Q.IsPrime] (hQc : Q.comap φ = 𝔮) : Q ∈ (𝔮.map φ).minimalPrimes := by
  let := φ.toAlgebra
  refine ⟨⟨hQ, Ideal.map_le_iff_le_comap.mpr hQc.ge⟩, fun {Q'} hQ' hQ'Q => ?_⟩
  obtain ⟨hQ'prime, hle⟩ := hQ'
  by_contra hQQ'
  obtain ⟨x, hxQ, hxQ'⟩ := SetLike.exists_of_lt (lt_of_le_not_ge hQ'Q hQQ')
  have hlt : Q'.comap φ < Q.comap φ :=
    Ideal.comap_lt_comap_of_integral_mem_sdiff (R := B) hQ'Q ⟨hxQ, hxQ'⟩ (hφ x)
  exact hlt.not_ge (hQc ▸ Ideal.map_le_iff_le_comap.mp hle)

/-- **Shrinking the target of a finite map around a fibre** (FHX Lemma 5.23, end of the proof:
"shrink the target to a principal affine neighbourhood of the image of `z`"). Let `φ : B → A` be
integral with `A` noetherian, `𝔮` a prime of `B` (a point `s ∈ Spec B`), and `J` an ideal of a
ring `A₀` mapping to `A` with `J A = ⊤` (the opens `D(c)`, `c ∈ J`, cover `Spec A`). There are
`c ∈ J` and `b ∉ 𝔮` with `c ∣ φ b` in `A`: so `s ∈ D(b)` and `π⁻¹(D(b)) ⊆ D(c)`.

Proof: by prime avoidance some `c ∈ J` lies in no prime of the finite set of minimal primes of
`𝔮 A`, which contains the fibre over `𝔮` (`mem_minimalPrimes_map_of_comap_eq`). If every `b`
with `φ b ∈ c A` were in `𝔮`, lying over would give a prime `Q ⊇ c A` over `𝔮`. -/
theorem exists_dvd_notMem_of_map_eq_top {A₀ : Type*} [CommRing A₀] [Algebra A₀ A] (φ : B →+* A)
    (hφ : φ.IsIntegral) [IsNoetherianRing A] (𝔮 : Ideal B) [𝔮.IsPrime] (J : Ideal A₀)
    (hJ : J.map (algebraMap A₀ A) = ⊤) :
    ∃ c ∈ J, ∃ b : B, b ∉ 𝔮 ∧ algebraMap A₀ A c ∣ φ b := by
  classical
  let := φ.toAlgebra
  have : Algebra.IsIntegral B A := ⟨hφ⟩
  have hfin : (𝔮.map φ).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing A _
  -- Prime avoidance.
  have hav : ¬ (J : Set A₀) ⊆ ⋃ Q ∈ (hfin.toFinset : Set (Ideal A)),
      (Q.comap (algebraMap A₀ A) : Set A₀) := by
    rw [Ideal.subset_union_prime ⊥ ⊥ fun Q hQ _ _ => by
      rw [Set.Finite.mem_toFinset] at hQ
      exact Ideal.comap_isPrime _ Q (H := hQ.1.1)]
    rintro ⟨Q, hQ, hJQ⟩
    rw [Set.Finite.mem_toFinset] at hQ
    have := Ideal.map_le_iff_le_comap.mpr hJQ
    rw [hJ, top_le_iff] at this
    exact hQ.1.1.ne_top this
  obtain ⟨c, hcJ, hc⟩ := Set.not_subset.mp hav
  simp only [Set.Finite.mem_toFinset, Set.mem_iUnion, SetLike.mem_coe, Ideal.mem_comap,
    not_exists] at hc
  refine ⟨c, hcJ, ?_⟩
  by_contra! H
  have hle : (Ideal.span {algebraMap A₀ A c}).comap (algebraMap B A) ≤ 𝔮 := by
    intro b hb
    by_contra hb𝔮
    exact H b hb𝔮 (Ideal.mem_span_singleton.mp hb)
  obtain ⟨Q, hcQ, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔮 _ hle
  exact hc Q (mem_minimalPrimes_map_of_comap_eq φ hφ hQc)
    (hcQ (Ideal.mem_span_singleton_self _))

end EnvelopeProperty
