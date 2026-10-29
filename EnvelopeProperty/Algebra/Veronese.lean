/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Algebra.GradedClosureBasic

/-!
# Veronese subalgebras of graded subalgebras of `A[T]`

Let `B ⊆ A[T]` be a graded `k`-subalgebra (`EnvelopeProperty.IsTGraded`, `conv:wu-graded` of the
blueprint chapter `wu-discharge.tex`) and `e ≥ 1`. The *Veronese subalgebra*
`B^{(e)} = ⊕_d B_{de}` is modelled as the `k`-subalgebra `EnvelopeProperty.veronese B e` of the
elements of `B` all of whose homogeneous components have degree divisible by `e`; its piece of
degree `d` (in the grading of `B^{(e)}`) is `B_{de}` (`EnvelopeProperty.gradedPiece_veronese`).

This is `lem:wu-veronese` of the blueprint (used in the compactification of Fang–Han–Xia,
*The envelope property for unibranch projective varieties*, Lemma 5.9 `lem:boundary-presentation`,
and for Corollary 5.26).

## Main results

* `EnvelopeProperty.exists_veronese_generated` (**`lem:wu-veronese`**, first part): if `B` is
  finitely generated and `B_0 = k`, there is `e ≥ 1` with `B_{ne} = (B_e)^n` for all `n ≥ 1`
  (`Submodule` powers: spans of `n`-fold products), hence `B^{(e)} = k[B_e]`.
* `EnvelopeProperty.isIntegrallyClosed_veronese` (second part): if `B` is an integrally closed
  domain, so is `B^{(e)}`, for every `e`.
* `EnvelopeProperty.homLoc_veronese` (third part): `B^{(e)}_{(σ)} = B_{(σ)}` for `σ ∈ B_e`.

## Implementation notes

The blueprint takes `e = rδ` with `δ` the least common multiple of the degrees `d_i` of `r`
homogeneous generators; we take `δ = ∏ d_i` and `e = (r + 1) δ`, which avoids the special case
`r = 0` and needs only `δ_i ∣ δ`. The degree-`ne` monomials are split off one degree-`e` factor at
a time (`EnvelopeProperty.exists_le_sum_mul_eq`) instead of being grouped all at once.

For integral closedness the blueprint decomposes `z ∈ Frac B^{(e)}` into residue classes of
degrees modulo `e`; here we write `z = p / q` with `p, q ∈ B^{(e)}`, find `r ∈ B` with `q r = p`
(normality of `B`) and show that the components of `r` of degree not divisible by `e` vanish
(`EnvelopeProperty.coeff_eq_zero_of_mul_eq`).
-/

open Polynomial

noncomputable section

namespace EnvelopeProperty

/-! ### Supports in `eℕ` -/

section Support

variable {A : Type*} [CommRing A]

theorem coeff_mul_eq_zero_of_forall {p q : A[X]} {n : ℕ}
    (h : ∀ a b, a + b = n → p.coeff a = 0 ∨ q.coeff b = 0) : (p * q).coeff n = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rcases h x.1 x.2 (Finset.HasAntidiagonal.mem_antidiagonal.1 hx) with h | h <;> simp [h]

/-- If `q r = p` with `q ≠ 0` and `p`, `q` supported in degrees divisible by `e`, then so is `r`. -/
theorem coeff_eq_zero_of_mul_eq [IsDomain A] {e : ℕ} {p q r : A[X]} (hq0 : q ≠ 0)
    (hq : ∀ n, ¬e ∣ n → q.coeff n = 0) (hp : ∀ n, ¬e ∣ n → p.coeff n = 0) (h : q * r = p) :
    ∀ n, ¬e ∣ n → r.coeff n = 0 := by
  classical
  set r₀ : A[X] := ∑ n ∈ r.support.filter (e ∣ ·), monomial n (r.coeff n) with hr₀_def
  have hr₀ : ∀ n, r₀.coeff n = if e ∣ n then r.coeff n else 0 := by
    intro n
    rw [hr₀_def, finsetSum_coeff]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_filter, mem_support_iff]
    by_cases hn : e ∣ n
    · by_cases hr : r.coeff n = 0
      · simp [hr]
      · simp [hr, hn]
    · simp [hn]
  set r₁ := r - r₀
  have hr₁ : ∀ n, e ∣ n → r₁.coeff n = 0 := fun n hn => by
    rw [coeff_sub, hr₀, if_pos hn, sub_self]
  have hqr₀ : ∀ n, ¬e ∣ n → (q * r₀).coeff n = 0 := fun n hn =>
    coeff_mul_eq_zero_of_forall fun a b hab => by
      by_cases ha : e ∣ a
      · right
        rw [hr₀, if_neg]
        intro hb
        exact hn (hab ▸ dvd_add ha hb)
      · exact Or.inl (hq a ha)
  have hqr₁ : q * r₁ = 0 := by
    ext n
    rw [coeff_zero]
    by_cases hn : e ∣ n
    · refine coeff_mul_eq_zero_of_forall fun a b hab => ?_
      by_cases ha : e ∣ a
      · right
        refine hr₁ b ?_
        have : e ∣ a + b := hab ▸ hn
        exact (Nat.dvd_add_right ha).1 this
      · exact Or.inl (hq a ha)
    · have : q * r₁ = p - q * r₀ := by rw [mul_sub, h]
      rw [this, coeff_sub, hp n hn, hqr₀ n hn, sub_zero]
  have hr : r = r₀ := by
    have := (mul_eq_zero.1 hqr₁).resolve_left hq0
    exact sub_eq_zero.1 this
  intro n hn
  rw [hr, hr₀, if_neg hn]

end Support

/-! ### The Veronese subalgebra -/

section Veronese

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- The Veronese subalgebra `B^{(e)} = ⊕_d B_{de}` of a graded subalgebra `B ⊆ A[T]`: the
elements of `B` whose homogeneous components all have degree divisible by `e`. Its piece of
degree `d` is `B_{de}` (`gradedPiece_veronese`). -/
def veronese (B : Subalgebra k A[X]) (e : ℕ) : Subalgebra k A[X] where
  carrier := {p | p ∈ B ∧ ∀ n, ¬e ∣ n → p.coeff n = 0}
  mul_mem' := fun {p q} hp hq => ⟨B.mul_mem hp.1 hq.1, fun n hn =>
    coeff_mul_eq_zero_of_forall fun a b hab => by
      by_cases ha : e ∣ a
      · right
        refine hq.2 b fun hb => hn (hab ▸ dvd_add ha hb)
      · exact Or.inl (hp.2 a ha)⟩
  add_mem' := fun {p q} hp hq => ⟨B.add_mem hp.1 hq.1, fun n hn => by
    rw [coeff_add, hp.2 n hn, hq.2 n hn, add_zero]⟩
  algebraMap_mem' := fun c => ⟨B.algebraMap_mem c, fun n hn => by
    rw [Polynomial.algebraMap_apply, coeff_C, if_neg]
    rintro rfl
    exact hn (dvd_zero e)⟩

variable {B : Subalgebra k A[X]} {e : ℕ}

theorem mem_veronese {p : A[X]} : p ∈ veronese B e ↔ p ∈ B ∧ ∀ n, ¬e ∣ n → p.coeff n = 0 :=
  Iff.rfl

theorem veronese_le (B : Subalgebra k A[X]) (e : ℕ) : veronese B e ≤ B :=
  fun _ hp => hp.1

theorem monomial_mem_veronese {d : ℕ} {a : A} (hd : e ∣ d) :
    monomial d a ∈ veronese B e ↔ monomial d a ∈ B := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun n hn => ?_⟩⟩
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact hn hd

theorem C_mem_veronese {a : A} : C a ∈ veronese B e ↔ C a ∈ B := by
  rw [← monomial_zero_left]
  exact monomial_mem_veronese (dvd_zero e)

/-- The Veronese subalgebra of a graded subalgebra is graded. -/
theorem IsTGraded.veronese (hB : IsTGraded B) : IsTGraded (veronese B e) := by
  intro p hp d
  refine ⟨hB p hp.1 d, fun n hn => ?_⟩
  rw [coeff_homogComp]
  split_ifs with h
  · exact hp.2 d (h ▸ hn)
  · rfl

/-- The degree `d` piece of `B^{(e)}` is `B_{de}`. -/
theorem gradedPiece_veronese (d : ℕ) :
    gradedPiece (veronese B e) (d * e) = gradedPiece B (d * e) := by
  ext p
  refine ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, fun n hn => h.2.coeff_of_ne ?_⟩, h.2⟩⟩
  rintro rfl
  exact hn (dvd_mul_left e d)

/-- `B^{(e)}` has no elements of degree not divisible by `e`. -/
theorem gradedPiece_veronese_of_not_dvd {n : ℕ} (hn : ¬e ∣ n) :
    gradedPiece (veronese B e) n = ⊥ := by
  refine eq_bot_iff.2 fun p hp => ?_
  rw [Submodule.mem_bot, hp.2.eq_monomial, hp.1.2 n hn, map_zero]

/-! ### Generation of the Veronese subalgebra in degree one -/

section Combinatorics

variable {ι : Type*} [Fintype ι]

/-- If `t ≤ ∑ q_i`, there is `q' ≤ q` with `∑ q'_i = t`. -/
theorem exists_le_sum_eq (q : ι → ℕ) {t : ℕ} (ht : t ≤ ∑ i, q i) :
    ∃ q' ≤ q, ∑ i, q' i = t := by
  classical
  induction t with
  | zero => exact ⟨0, fun i => Nat.zero_le _, by simp⟩
  | succ t ih =>
    obtain ⟨q'', hle, hsum⟩ := ih (by omega)
    obtain ⟨i, hi⟩ : ∃ i, q'' i < q i := by
      by_contra hcon
      push Not at hcon
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hcon i
      omega
    refine ⟨q'' + Pi.single i 1, fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        simp only [Pi.add_apply, Pi.single_eq_same]
        omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero]
        exact hle j
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, hsum, Finset.sum_pi_single', if_pos (Finset.mem_univ i)]

/-- If `d_i ∣ δ`, `0 < δ` and `∑ α_i d_i ≥ (t + |ι|) δ`, then some `α' ≤ α` has degree exactly
`∑ α'_i d_i = t δ`. -/
theorem exists_le_sum_mul_eq {d : ι → ℕ} {δ : ℕ} (hδ : ∀ i, d i ∣ δ) (hδ0 : 0 < δ)
    (α : ι → ℕ) (t : ℕ) (h : t * δ + Fintype.card ι * δ ≤ ∑ i, α i * d i) :
    ∃ α' ≤ α, ∑ i, α' i * d i = t * δ := by
  set m : ι → ℕ := fun i => δ / d i
  have hmd : ∀ i, m i * d i = δ := fun i => Nat.div_mul_cancel (hδ i)
  have hm0 : ∀ i, 0 < m i := fun i => by
    rcases Nat.eq_zero_or_pos (m i) with h0 | h0
    · have := hmd i
      rw [h0, zero_mul] at this
      omega
    · exact h0
  set q : ι → ℕ := fun i => α i / m i
  set ρ : ι → ℕ := fun i => α i % m i
  have hαd : ∀ i, α i * d i = q i * δ + ρ i * d i := fun i => by
    have h1 := Nat.div_add_mod (α i) (m i)
    rw [← hmd i]
    calc α i * d i = (m i * (α i / m i) + α i % m i) * d i := by rw [h1]
      _ = q i * (m i * d i) + ρ i * d i := by simp only [q, ρ]; ring
  have hρ : ∀ i, ρ i * d i ≤ δ := fun i => by
    rw [← hmd i]
    exact Nat.mul_le_mul_right _ (Nat.mod_lt _ (hm0 i)).le
  have hsum : ∑ i, α i * d i = (∑ i, q i) * δ + ∑ i, ρ i * d i := by
    rw [Finset.sum_congr rfl fun i _ => hαd i, Finset.sum_add_distrib, Finset.sum_mul]
  have hρsum : ∑ i, ρ i * d i ≤ Fintype.card ι * δ := by
    calc ∑ i, ρ i * d i ≤ ∑ _i : ι, δ := Finset.sum_le_sum fun i _ => hρ i
      _ = Fintype.card ι * δ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have ht : t ≤ ∑ i, q i := by
    refine Nat.le_of_mul_le_mul_right ?_ hδ0
    omega
  obtain ⟨q', hq', hq'sum⟩ := exists_le_sum_eq q ht
  refine ⟨fun i => q' i * m i, fun i => ?_, ?_⟩
  · calc q' i * m i ≤ q i * m i := Nat.mul_le_mul_right _ (hq' i)
      _ ≤ α i := by
        have h1 := Nat.div_add_mod (α i) (m i)
        simp only [q]
        rw [mul_comm]
        omega
  · calc ∑ i, q' i * m i * d i = ∑ i, q' i * δ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_assoc, hmd i]
      _ = t * δ := by rw [← Finset.sum_mul, hq'sum]

variable {b : ι → A[X]} {d : ι → ℕ}

/-- **The monomial step of `lem:wu-veronese`.** With `e = (|ι| + 1) δ`, `d_i ∣ δ`, every monomial
`∏ b_i^{α_i}` of degree `ne` (`n ≥ 1`) in homogeneous generators `b_i` of degree `d_i` is a product
of `n` elements of `B_e`. -/
theorem prod_pow_mem_gradedPiece_pow (hb : ∀ i, IsHomog (d i) (b i)) {δ : ℕ}
    (hδ : ∀ i, d i ∣ δ) (hδ0 : 0 < δ) {n : ℕ} (hn : 0 < n) (α : ι → ℕ)
    (hα : ∑ i, α i * d i = n * ((Fintype.card ι + 1) * δ)) :
    ∏ i, b i ^ α i ∈
      gradedPiece (Algebra.adjoin k (Set.range b)) ((Fintype.card ι + 1) * δ) ^ n := by
  set e := (Fintype.card ι + 1) * δ with he
  induction n, hn using Nat.le_induction generalizing α with
  | base =>
    rw [pow_one]
    refine ⟨prod_pow_mem_adjoin b α, ?_⟩
    have hα' : ∑ i, α i * d i = e := by simpa using hα
    exact hα' ▸ isHomog_prod_pow hb α
  | succ n hn ih =>
    have h1 : e ≤ n * e := Nat.le_mul_of_pos_left e hn
    have h2 : Fintype.card ι * δ ≤ e := by rw [he]; exact Nat.mul_le_mul_right _ (by omega)
    have hkey : (Fintype.card ι + 1) * δ + Fintype.card ι * δ ≤ (n + 1) * e := by
      rw [← he, add_mul, one_mul]
      omega
    obtain ⟨α', hα', hα'sum⟩ := exists_le_sum_mul_eq hδ hδ0 α (Fintype.card ι + 1)
      (by rw [hα]; exact hkey)
    rw [← he] at hα'sum
    set β : ι → ℕ := fun i => α i - α' i
    have hαβ : ∀ i, α i = α' i + β i := fun i => by
      have : α' i ≤ α i := hα' i
      simp only [β]
      omega
    have hβ : ∑ i, β i * d i = n * e := by
      have : ∑ i, α i * d i = ∑ i, α' i * d i + ∑ i, β i * d i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [hαβ i, add_mul]
      rw [hα, hα'sum, add_mul, one_mul] at this
      omega
    have hprod : ∏ i, b i ^ α i = (∏ i, b i ^ α' i) * ∏ i, b i ^ β i := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [hαβ i, pow_add]
    rw [hprod, pow_succ']
    refine Submodule.mul_mem_mul ⟨prod_pow_mem_adjoin b α', ?_⟩ (ih β hβ)
    exact hα'sum ▸ isHomog_prod_pow hb α'

end Combinatorics

/-- `M^n ⊆ k[M]` for a `k`-submodule `M ⊆ A[T]`. -/
theorem pow_le_toSubmodule_adjoin (M : Submodule k A[X]) (n : ℕ) :
    M ^ n ≤ Subalgebra.toSubmodule (Algebra.adjoin k (M : Set A[X])) := by
  induction n with
  | zero => exact Submodule.one_le.2 (Subalgebra.one_mem _)
  | succ n ih =>
    rw [pow_succ]
    exact Submodule.mul_le.2 fun x hx y hy =>
      Subalgebra.mul_mem _ (ih hx) (Algebra.subset_adjoin hy)

/-- **`lem:wu-veronese`, generation.** A finitely generated graded subalgebra `B ⊆ A[T]` with
`B_0 = k` has some `e ≥ 1` with `B_{ne} = (B_e)^n` for all `n ≥ 1`. -/
theorem exists_gradedPiece_mul_eq_pow (hB : IsTGraded B) (hfg : B.FG)
    (h0 : ∀ a : A, C a ∈ B → ∃ c : k, algebraMap k A c = a) :
    ∃ e, 0 < e ∧ ∀ n, 0 < n → gradedPiece B (n * e) = gradedPiece B e ^ n := by
  obtain ⟨r, b, d, hd, hb, rfl⟩ := exists_homog_generators hB hfg h0
  set δ := ∏ i, d i
  have hδ0 : 0 < δ := Finset.prod_pos fun i _ => hd i
  have hδ : ∀ i, d i ∣ δ := fun i => Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  refine ⟨(Fintype.card (Fin r) + 1) * δ, Nat.mul_pos (Nat.succ_pos _) hδ0, fun n hn =>
    le_antisymm ?_ (gradedPiece_pow_le _ n)⟩
  refine (gradedPiece_adjoin_le_span hb _).trans (Submodule.span_le.2 ?_)
  rintro _ ⟨α, hα, rfl⟩
  exact prod_pow_mem_gradedPiece_pow hb hδ hδ0 hn α hα

/-- If `B_{ne} = (B_e)^n` for all `n ≥ 1` and `B_0 = k`, then `B^{(e)}` is generated by `B_e`. -/
theorem veronese_eq_adjoin (hB : IsTGraded B) (h0 : ∀ a : A, C a ∈ B → ∃ c : k, algebraMap k A c = a)
    (hpow : ∀ n, 0 < n → gradedPiece B (n * e) = gradedPiece B e ^ n) :
    veronese B e = Algebra.adjoin k (gradedPiece B e : Set A[X]) := by
  refine le_antisymm (fun p hp => ?_) (Algebra.adjoin_le fun p hp => ⟨hp.1, fun n hn => ?_⟩)
  · rw [← sum_homogComp p]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    by_cases hj : e ∣ j
    · obtain ⟨n, rfl⟩ := hj
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · obtain ⟨c, hc⟩ := h0 (p.coeff 0) (by
          rw [← monomial_zero_left]; exact hB p hp.1 0)
        rw [mul_zero, homogComp_apply, monomial_zero_left, ← hc, ← Polynomial.algebraMap_apply]
        exact Subalgebra.algebraMap_mem _ c
      · have h1 := hB.homogComp_mem hp.1 (e * n)
        rw [mul_comm, hpow n hn] at h1
        rw [mul_comm]
        exact pow_le_toSubmodule_adjoin _ n h1
    · rw [homogComp_apply, hp.2 j hj, map_zero]
      exact Subalgebra.zero_mem _
  · refine hp.2.coeff_of_ne ?_
    rintro rfl
    exact hn dvd_rfl

/-- **`lem:wu-veronese`, first part.** A finitely generated graded subalgebra `B ⊆ A[T]` with
`B_0 = k` has some `e ≥ 1` such that `B_{ne} = (B_e)^n` for all `n ≥ 1`; thus the Veronese
subalgebra `B^{(e)}` is generated by `B_e`. -/
theorem exists_veronese_generated (hB : IsTGraded B) (hfg : B.FG)
    (h0 : ∀ a : A, C a ∈ B → ∃ c : k, algebraMap k A c = a) :
    ∃ e, 0 < e ∧ (∀ n, 0 < n → gradedPiece B (n * e) = gradedPiece B e ^ n) ∧
      veronese B e = Algebra.adjoin k (gradedPiece B e : Set A[X]) := by
  obtain ⟨e, he, hpow⟩ := exists_gradedPiece_mul_eq_pow hB hfg h0
  exact ⟨e, he, hpow, veronese_eq_adjoin hB h0 hpow⟩

/-! ### Integral closedness -/

/-- **`lem:wu-veronese`, second part.** If `B ⊆ A[T]` is an integrally closed domain, so is every
Veronese subalgebra `B^{(e)}`. -/
theorem isIntegrallyClosed_veronese [IsDomain A] (B : Subalgebra k A[X]) [IsIntegrallyClosed B]
    (e : ℕ) : IsIntegrallyClosed (veronese B e) := by
  set V := veronese B e
  let incl : V →+* B := (Subalgebra.inclusion (veronese_le B e)).toRingHom
  have hincl : Function.Injective incl := Subalgebra.inclusion_injective _
  have hg : Function.Injective ((algebraMap B (FractionRing B)).comp incl) :=
    (IsFractionRing.injective B (FractionRing B)).comp hincl
  let φ : FractionRing V →+* FractionRing B := IsFractionRing.lift hg
  have hφ : (algebraMap B (FractionRing B)).comp incl = φ.comp (algebraMap V (FractionRing V)) :=
    RingHom.ext fun v => by
      rw [RingHom.comp_apply, RingHom.comp_apply, IsFractionRing.lift_algebraMap]
      rfl
  rw [isIntegrallyClosed_iff (FractionRing V)]
  intro x hx
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hq0' : (q : A[X]) ≠ 0 := fun h => hq0 (Subtype.ext h)
  have hqV : algebraMap V (FractionRing V) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hq0
  have hqB : algebraMap B (FractionRing B) (incl q) ≠ 0 :=
    (map_ne_zero_iff _ hg).2 hq0
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.map_of_comp_eq incl φ hφ hx)
  rw [map_div₀, ← RingHom.comp_apply φ, ← RingHom.comp_apply φ, ← hφ, RingHom.comp_apply,
    RingHom.comp_apply] at hr
  have h1 : incl q * r = incl p := IsFractionRing.injective B (FractionRing B) (by
    rw [map_mul, hr, mul_div_cancel₀ _ hqB])
  have h2 : (q : A[X]) * r = p := congrArg Subtype.val h1
  have hrV : (r : A[X]) ∈ V := ⟨r.2, coeff_eq_zero_of_mul_eq hq0' (mem_veronese.1 q.2).2
    (mem_veronese.1 p.2).2 h2⟩
  refine ⟨⟨r, hrV⟩, ?_⟩
  have h3 : q * ⟨r, hrV⟩ = p := Subtype.ext h2
  rw [eq_div_iff hqV, ← map_mul, mul_comm, h3]

/-! ### Homogeneous localizations -/

/-- **`lem:wu-veronese`, third part.** For `σ = s T^e`, `B^{(e)}_{(σ)} = B_{(σ)}`. -/
theorem homLoc_veronese [IsDomain A] (B : Subalgebra k A[X]) (s : A) (e : ℕ) :
    homLoc (veronese B e) s e = homLoc B s e := by
  unfold homLoc
  congr 1
  ext x
  exact exists_congr fun j => exists_congr fun a =>
    and_congr_left' (monomial_mem_veronese (dvd_mul_left e j))

end Veronese

end EnvelopeProperty
