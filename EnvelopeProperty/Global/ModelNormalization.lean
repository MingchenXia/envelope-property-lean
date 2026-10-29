/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.ModelCharts
import EnvelopeProperty.Algebra.NormalizationFinite
import EnvelopeProperty.Algebra.GradedClosureBasic

/-!
# Normalizations of integral multiprojective models

This file implements parts (2) and (3) of the blueprint remark `rmk:gl-model-examples`
(`global.tex`, subsection `subsec:gl-model`) for the formalization of Fang–Han–Xia, *The envelope
property for unibranch projective varieties*: the normalization of a model and its normalization
in a finite extension `E ⊇ K` are normal models.

## The torus action and gradedness (`lem:wu-graded-closure`(1), multigraded)

For a commutative `k`-algebra `A`, the torus `(k^×)^r` acts on `A[T_1, …, T_r]` by the scalings
`T_c ↦ t T_c` (`EnvelopeProperty.scaleVar c t`, `coeff_m(scaleVar c t p) = t^{m_c} coeff_m p`). If
`k` is infinite, a `k`-submodule stable under all scalings contains the homogeneous components
`p_a T^a` of its elements (`EnvelopeProperty.monomial_coeff_mem_of_scaleVar`): by the Vandermonde
argument of `homogComp_mem_span_torusAut`, applied to one variable at a time, the parts of `p` of
fixed degree in `T_c` (`EnvelopeProperty.varPart`) are `k`-combinations of the `scaleVar c t p`.

## Normalization in a finite extension (`rmk:gl-model-examples`(2),(3))

For a finite extension `E ⊇ K` (with `k → K → E` a scalar tower), let `μ : K[T] → E[T]` be the
coefficientwise inclusion and `S_E ⊆ E[T]` the integral closure of `μ(S)`
(`MultiModel.normalizationInS`). Then `𝒳_E = (E, S_E, z)` (`MultiModel.normalizationIn`) is a
normal model (`MultiModel.isNormal_normalizationIn`), the normalization of `𝒳` in `E`:

* `S_E` is graded by the torus argument (`k` infinite);
* `S_E` is a finite `S`-module (`MultiModel.finite_normalizationInHom`), by the finiteness of
  normalization over a perfect field (`thm:bj-normalization-finite`,
  `EnvelopeProperty.finite_of_isIntegralClosure_of_finiteType`) applied to
  `S ⊆ Frac S = K(T) ⊆ E(T)`: `S_E` is the integral closure of `S` in `E(T)` because `E[T]` is
  integrally closed; hence `S_E` is finitely generated;
* (M2) by transitivity of integrality;
* (M3): every `e ∈ E` is a quotient `f / g` with `f, g ∈ (S_E)_a`: write `y e` integral over a
  chart algebra `A_j` (`y ∈ A_j`), and clear denominators
  (`MultiModel.isIntegral_monomial_of_isIntegral_chartAlg`, the argument of
  `isIntegrallyClosed_chartAlg`).

The normalization `𝒳^ν = (K, S^ν, z)` is the case `E = K` (`MultiModel.normalization`), with
`p ∈ S^ν ↔ p` integral over `S` (`MultiModel.mem_normalization_S`).

Hypotheses: `k` infinite (torus argument) and perfect (finiteness of normalization); both hold for
the algebraically closed `k` of the blueprint.
-/

open scoped NNReal ENNReal Topology nonZeroDivisors

open MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Scaling one variable -/

section Torus

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A] {σ : Type*}
  [DecidableEq σ]

/-- The scaling `T_c ↦ t T_c` of `A[T]`, `t ∈ k`. -/
def scaleVar (c : σ) (t : k) : MvPolynomial σ A →ₐ[A] MvPolynomial σ A :=
  aeval fun d => C (if d = c then algebraMap k A t else 1) * X d

theorem scaleVar_monomial (c : σ) (t : k) (m : σ →₀ ℕ) (a : A) :
    scaleVar c t (monomial m a) = monomial m (algebraMap k A (t ^ m c) * a) := by
  have h : (m.prod fun d n => (C (if d = c then algebraMap k A t else 1) * X d : MvPolynomial σ A)
      ^ n) = C (algebraMap k A (t ^ m c)) * monomial m 1 := by
    simp_rw [mul_pow, ← map_pow]
    rw [Finsupp.prod_mul, ← map_finsuppProd,
      show (m.prod fun d n => (X d : MvPolynomial σ A) ^ n) = monomial m 1 by
        rw [monomial_eq, C_1, one_mul]]
    congr 2
    rw [Finsupp.prod]
    simp_rw [ite_pow, one_pow]
    rw [Finset.prod_ite_eq', ← map_pow]
    split_ifs with hc
    · rfl
    · rw [Finsupp.notMem_support_iff.1 hc, pow_zero, map_one]
  rw [scaleVar, aeval_monomial, h, MvPolynomial.algebraMap_eq, ← mul_assoc, ← map_mul,
    C_mul_monomial, mul_one, mul_comm a]

theorem coeff_scaleVar (c : σ) (t : k) (p : MvPolynomial σ A) (m : σ →₀ ℕ) :
    (scaleVar c t p).coeff m = algebraMap k A (t ^ m c) * p.coeff m := by
  induction p using MvPolynomial.induction_on' with
  | monomial n a =>
    rw [scaleVar_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

/-- The part of `p` of degree `n` in the variable `T_c`. -/
def varPart (c : σ) (n : ℕ) (p : MvPolynomial σ A) : MvPolynomial σ A :=
  weightedHomogeneousComponent (Pi.single c 1 : σ → ℕ) n p

theorem coeff_varPart (c : σ) (n : ℕ) (p : MvPolynomial σ A) (m : σ →₀ ℕ) :
    (varPart c n p).coeff m = if m c = n then p.coeff m else 0 := by
  rw [varPart, coeff_weightedHomogeneousComponent, Finsupp.weight_single_index, smul_eq_mul,
    mul_one]

variable (k) in
/-- **Vandermonde step.** For `k` infinite, the part of `p` of degree `n` in `T_c` is a
`k`-linear combination of the scalings `p(…, t T_c, …)`, `t ∈ k^×`. -/
theorem varPart_mem_span_scaleVar [Infinite k] (c : σ) (n : ℕ) (p : MvPolynomial σ A) :
    varPart c n p ∈ Submodule.span k
      (Set.range fun t : kˣ => scaleVar (A := A) c (t : k) p) := by
  set D := p.support.sup fun m => m c
  have hD : ∀ m ∈ p.support, m c ≤ D := fun m hm => Finset.le_sup (f := fun m => m c) hm
  rcases lt_or_ge D n with hn | hn
  · have : varPart c n p = 0 := by
      ext m
      rw [coeff_varPart, coeff_zero]
      split_ifs with h
      · by_contra hm
        exact absurd (hD m (mem_support_iff.2 hm)) (by omega)
      · rfl
    rw [this]
    exact Submodule.zero_mem _
  have := infinite_units_of_infinite (k := k)
  set N := D + 1
  let μ : Fin N ↪ kˣ := Fin.valEmbedding.trans (Infinite.natEmbedding kˣ)
  set ν : Fin N → k := fun i => (μ i : k)
  have hν : Function.Injective ν := fun i j hij => μ.injective (Units.ext hij)
  set V := Matrix.vandermonde ν
  have hdet : IsUnit V.det := isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hν)
  have hVV : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdet
  set n' : Fin N := ⟨n, Nat.lt_succ_of_le hn⟩
  have key : varPart c n p = ∑ i, V⁻¹ n' i • scaleVar (A := A) c (μ i : k) p := by
    ext m
    rw [coeff_varPart, coeff_sum]
    simp only [coeff_smul, coeff_scaleVar]
    simp only [Algebra.smul_def]
    have hsum : ∑ i, algebraMap k A (V⁻¹ n' i) * (algebraMap k A ((μ i : k) ^ m c) * p.coeff m) =
        algebraMap k A (∑ i, V⁻¹ n' i * ν i ^ m c) * p.coeff m := by
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]
      ring
    change _ = ∑ i, algebraMap k A (V⁻¹ n' i) * (algebraMap k A ((μ i : k) ^ m c) * p.coeff m)
    rw [hsum]
    by_cases hm : m ∈ p.support
    · have hmD : m c < N := Nat.lt_succ_of_le (hD m hm)
      have : ∑ i, V⁻¹ n' i * ν i ^ m c = (V⁻¹ * V) n' ⟨m c, hmD⟩ := by
        rw [Matrix.mul_apply]
        rfl
      rw [this, hVV, Matrix.one_apply]
      by_cases hmn : m c = n
      · rw [if_pos hmn, if_pos (Fin.ext hmn.symm), map_one, one_mul]
      · rw [if_neg hmn, if_neg (fun h => hmn (congrArg Fin.val h).symm), map_zero, zero_mul]
    · rw [notMem_support_iff.1 hm, mul_zero]
      split_ifs <;> rfl
  rw [key]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ i, rfl⟩)

/-- **Torus argument** (`lem:wu-graded-closure`(1), multigraded): for `k` infinite and `σ` finite,
a `k`-submodule of `A[T]` stable under the scalings `T_c ↦ t T_c`, `t ∈ k^×`, contains the
homogeneous components `p_a T^a` of its elements. -/
theorem monomial_coeff_mem_of_scaleVar [Infinite k] [Fintype σ]
    (N : Submodule k (MvPolynomial σ A))
    (hN : ∀ (c : σ) (t : k), t ≠ 0 → ∀ p ∈ N, scaleVar (A := A) c t p ∈ N)
    {p : MvPolynomial σ A} (hp : p ∈ N) (a : σ →₀ ℕ) : monomial a (p.coeff a) ∈ N := by
  classical
  have hpart : ∀ (c : σ) (n : ℕ) (q : MvPolynomial σ A), q ∈ N → varPart c n q ∈ N :=
    fun c n q hq => Submodule.span_le.2 (Set.range_subset_iff.2 fun t : kˣ =>
      hN c (t : k) t.ne_zero q hq)
      (varPart_mem_span_scaleVar k c n q)
  -- The part of `p` with prescribed degrees in the variables of `s`.
  have hs : ∀ s : Finset σ, ∃ q ∈ N, ∀ m,
      q.coeff m = if ∀ d ∈ s, m d = a d then p.coeff m else 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨p, hp, fun m => by simp⟩
    | insert c s hc ih =>
      obtain ⟨q, hq, hqc⟩ := ih
      refine ⟨varPart c (a c) q, hpart c (a c) q hq, fun m => ?_⟩
      rw [coeff_varPart, hqc]
      by_cases h1 : m c = a c
      · rw [if_pos h1]
        congr 1
        exact propext ⟨fun h d hd => by
          rcases Finset.mem_insert.1 hd with rfl | hd
          · exact h1
          · exact h d hd, fun h d hd => h d (Finset.mem_insert_of_mem hd)⟩
      · rw [if_neg h1, if_neg fun h => h1 (h c (Finset.mem_insert_self c s))]
  obtain ⟨q, hq, hqc⟩ := hs Finset.univ
  have : q = monomial a (p.coeff a) := by
    ext m
    rw [hqc, coeff_monomial]
    by_cases hm : m = a
    · subst hm; simp
    · rw [if_neg fun h => hm (Finsupp.ext fun d => h d (Finset.mem_univ d)),
        if_neg (Ne.symm hm)]
  rwa [this] at hq

end Torus

/-! ### Finiteness of `K[T] → E[T]` -/

/-- For a finite field extension `E ⊇ K`, `E[T]` is a finite `K[T]`-module (spanned by the
constants `C e`, `e` in a spanning set of `E` over `K`). -/
theorem finite_map_algebraMap {K E σ : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] :
    (MvPolynomial.map (σ := σ) (algebraMap K E)).Finite := by
  let := (MvPolynomial.map (σ := σ) (algebraMap K E)).toAlgebra
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := E)
  classical
  refine ⟨⟨s.image C, eq_top_iff.2 fun p _ => ?_⟩⟩
  induction p using MvPolynomial.induction_on' with
  | monomial m e =>
    have he : e ∈ Submodule.span K (s : Set E) := by rw [hs]; exact Submodule.mem_top
    obtain ⟨f, -, rfl⟩ := Submodule.mem_span_finset.1 he
    rw [map_sum]
    refine Submodule.sum_mem _ fun x hx => ?_
    have : monomial m (f x • x) =
        (monomial m (f x) : MvPolynomial σ K) • (C x : MvPolynomial σ E) := by
      rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_monomial,
        mul_comm (monomial m _), C_mul_monomial, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [hx]))
  | add p q hp hq => exact Submodule.add_mem _ (hp trivial) (hq trivial)

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  (X : MultiModel k K r)
  (E : Type u) [Field E] [Algebra K E] [Algebra k E] [IsScalarTower k K E]

/-! ### The image of `S` in `E[T]` -/

variable (k) in
/-- The coefficientwise inclusion `μ : K[T] → E[T]`. -/
def coeffMap : MvPolynomial (Fin r) K →ₐ[k] MvPolynomial (Fin r) E :=
  MvPolynomial.mapAlgHom (IsScalarTower.toAlgHom k K E)

theorem coeffMap_apply (p : MvPolynomial (Fin r) K) :
    coeffMap k E p = MvPolynomial.map (algebraMap K E) p :=
  rfl

theorem coeffMap_monomial (a : Fin r →₀ ℕ) (f : K) :
    coeffMap k E (monomial a f) = monomial a (algebraMap K E f) :=
  map_monomial _ _ _

theorem coeffMap_injective : Function.Injective (coeffMap (K := K) (r := r) k E) :=
  map_injective _ (algebraMap K E).injective

/-- The image `μ(S) ⊆ E[T]`. -/
def imageS : Subalgebra k (MvPolynomial (Fin r) E) :=
  X.S.map (coeffMap k E)

variable {X E}

theorem coeffMap_mem_imageS {p : MvPolynomial (Fin r) K} (hp : p ∈ X.S) :
    coeffMap k E p ∈ X.imageS E :=
  ⟨p, hp, rfl⟩

/-- `μ(S)` is graded. -/
theorem monomial_coeff_mem_imageS {q : MvPolynomial (Fin r) E} (hq : q ∈ X.imageS E)
    (a : Fin r →₀ ℕ) : monomial a (q.coeff a) ∈ X.imageS E := by
  obtain ⟨p, hp, rfl⟩ := hq
  change monomial a ((MvPolynomial.map (algebraMap K E) p).coeff a) ∈ X.imageS E
  rw [coeff_map, ← coeffMap_monomial (k := k)]
  exact coeffMap_mem_imageS (X.isGraded p hp a)

/-- `μ(S)` is stable under the scalings `T_c ↦ t T_c`, `t ∈ k`. -/
theorem scaleVar_mem_imageS (c : Fin r) (t : k) {q : MvPolynomial (Fin r) E}
    (hq : q ∈ X.imageS E) : scaleVar (A := E) c t q ∈ X.imageS E := by
  rw [q.as_sum, map_sum]
  refine Subalgebra.sum_mem _ fun m _ => ?_
  rw [scaleVar_monomial, ← Algebra.smul_def, ← smul_monomial]
  exact Subalgebra.smul_mem _ (monomial_coeff_mem_imageS hq m) _

variable (X E)

/-- The coordinate ring `S_E ⊆ E[T]` of the normalization of `𝒳` in `E`: the integral closure of
`μ(S)` in `E[T]` (`rmk:gl-model-examples`(3)). -/
def normalizationInS : Subalgebra k (MvPolynomial (Fin r) E) :=
  (integralClosure (X.imageS E) (MvPolynomial (Fin r) E)).restrictScalars k

variable {X E}

theorem mem_normalizationInS {p : MvPolynomial (Fin r) E} :
    p ∈ X.normalizationInS E ↔ IsIntegral (X.imageS E) p :=
  Iff.rfl

theorem imageS_le_normalizationInS : X.imageS E ≤ X.normalizationInS E := fun q hq =>
  mem_normalizationInS.2 (isIntegral_algebraMap (R := X.imageS E) (x := ⟨q, hq⟩))

theorem coeffMap_mem_normalizationInS {p : MvPolynomial (Fin r) K} (hp : p ∈ X.S) :
    coeffMap k E p ∈ X.normalizationInS E :=
  imageS_le_normalizationInS (coeffMap_mem_imageS hp)

/-- `S_E` is stable under the scalings `T_c ↦ t T_c`. -/
theorem scaleVar_mem_normalizationInS (c : Fin r) (t : k) {p : MvPolynomial (Fin r) E}
    (hp : p ∈ X.normalizationInS E) : scaleVar (A := E) c t p ∈ X.normalizationInS E := by
  rw [mem_normalizationInS] at hp ⊢
  let ψ : MvPolynomial (Fin r) E →+* MvPolynomial (Fin r) E := (scaleVar (A := E) c t).toRingHom
  let φ : X.imageS E →+* X.imageS E :=
    (ψ.comp (algebraMap (X.imageS E) (MvPolynomial (Fin r) E))).codRestrict (X.imageS E)
      fun q => scaleVar_mem_imageS c t q.2
  exact IsIntegral.map_of_comp_eq φ ψ (RingHom.ext fun _ => rfl) hp

/-- `S_E` is graded (torus argument, `k` infinite). -/
theorem isGraded_normalizationInS [Infinite k] {p : MvPolynomial (Fin r) E}
    (hp : p ∈ X.normalizationInS E) (a : Fin r →₀ ℕ) :
    monomial a (p.coeff a) ∈ X.normalizationInS E :=
  monomial_coeff_mem_of_scaleVar (Subalgebra.toSubmodule (X.normalizationInS E))
    (fun c t _ _ hq => scaleVar_mem_normalizationInS c t hq) hp a

/-! ### Clearing denominators -/

/-- **Clearing denominators.** If `w ∈ E` is a root of a monic polynomial over the chart algebra
`A_j` (acting on `E` through `K → E`), then `w z̃_j^N T^N` is integral over `μ(S)` for some `N`
(as in `isIntegrallyClosed_chartAlg_of_isIntegrallyClosedIn`). -/
theorem exists_isIntegral_monomial_of_chartAlg {j : X.ChartIndex}
    (hj : ∀ c, X.coord c (j c) ≠ 0) {w : E} (p : Polynomial (X.chartAlg j)) (hpm : p.Monic)
    (hp : p.eval₂ ((algebraMap K E).comp (X.chartAlg j).val.toRingHom) w = 0) :
    ∃ N : Fin r →₀ ℕ,
      IsIntegral (X.imageS E) (monomial N (w * algebraMap K E (X.chartDen j N))) := by
  set n := p.natDegree with hn
  choose d f hf hdf using fun i => (mem_chartAlg_iff hj).1 (p.coeff i).2
  set N : Fin r →₀ ℕ := ∑ i ∈ Finset.range n, d i
  refine ⟨N, ?_⟩
  set D := X.chartDen j N with hD_def
  have hdN : ∀ i < n, d i ≤ N := fun i hi =>
    Finset.single_le_sum (f := d) (fun _ _ => zero_le) (Finset.mem_range.2 hi)
  have hc : ∀ i : Fin n, (p.coeff i : K) * D ^ (n - i) ∈ X.piece ((n - i) • N) := by
    intro i
    have hi : d i ≤ N := hdN i i.2
    have h1 : f i * X.chartDen j (N - d i) ∈ X.piece N := by
      have := mul_mem_piece (hf i) (X.chartDen_mem_piece j (N - d i))
      rwa [add_tsub_cancel_of_le hi] at this
    obtain ⟨m, hm⟩ : ∃ m, n - (i : ℕ) = m + 1 := ⟨n - i - 1, by omega⟩
    have h2 := mul_mem_piece h1 (pow_mem_piece (X.chartDen_mem_piece j N) m)
    have e1 : N + m • N = (n - i) • N := by rw [hm, succ_nsmul']
    have hDd : D = X.chartDen j (N - d i) * X.chartDen j (d i) := by
      rw [hD_def, ← X.chartDen_add, tsub_add_cancel_of_le hi]
    have hdi : X.chartDen j (d i) ≠ 0 := chartDen_ne_zero hj _
    have e2 : f i * X.chartDen j (N - d i) * D ^ m = (p.coeff i : K) * D ^ (n - i) := by
      rw [hdf i, hm, pow_succ]
      calc f i * X.chartDen j (N - d i) * D ^ m
          = f i / X.chartDen j (d i) * (D ^ m * (X.chartDen j (N - d i) * X.chartDen j (d i))) := by
            field_simp
        _ = f i / X.chartDen j (d i) * (D ^ m * D) := by rw [← hDd]
    rw [e1, e2] at h2
    exact h2
  set D' := algebraMap K E D with hD'_def
  set u := monomial N (w * D') with hu_def
  set P : Polynomial (X.imageS E) := Polynomial.X ^ n +
    ∑ i : Fin n, Polynomial.C ⟨coeffMap k E (X.ofPiece (hc i)).1,
      coeffMap_mem_imageS (X.ofPiece (hc i)).2⟩ * Polynomial.X ^ (i : ℕ)
  have hPm : P.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hpw : w ^ n + ∑ i ∈ Finset.range n, algebraMap K E (p.coeff i : K) * w ^ i = 0 := by
    rw [hpm.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_finsetSum] at hp
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hp
    exact hp
  have hterm : ∀ i : Fin n, algebraMap (X.imageS E) (MvPolynomial (Fin r) E)
      ⟨coeffMap k E (X.ofPiece (hc i)).1, coeffMap_mem_imageS (X.ofPiece (hc i)).2⟩ *
      u ^ (i : ℕ) = monomial (n • N) (D' ^ n * (algebraMap K E (p.coeff i : K) * w ^ (i : ℕ))) := by
    intro i
    rw [show algebraMap (X.imageS E) (MvPolynomial (Fin r) E)
        ⟨coeffMap k E (X.ofPiece (hc i)).1, coeffMap_mem_imageS (X.ofPiece (hc i)).2⟩ =
        monomial ((n - i) • N) (algebraMap K E ((p.coeff i : K) * D ^ (n - i))) from
          coeffMap_monomial _ _ _, hu_def, monomial_pow, monomial_mul]
    have hni : n = (n - i) + i := by omega
    congr 1
    · rw [← add_nsmul, ← hni]
    · rw [← pow_sub_mul_pow D' (show (i : ℕ) ≤ n from i.2.le), map_mul, map_pow]
      ring
  have hPu : Polynomial.eval₂ (algebraMap (X.imageS E) (MvPolynomial (Fin r) E)) u P = 0 := by
    simp only [P, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C]
    rw [Finset.sum_congr rfl fun i _ => hterm i, hu_def, monomial_pow, ← map_sum, ← map_add,
      ← Finset.sum_range (fun i => D' ^ n * (algebraMap K E (p.coeff i : K) * w ^ i)),
      ← Finset.mul_sum, mul_pow, mul_comm (w ^ n), ← mul_add, hpw, mul_zero, map_zero]
  exact ⟨P, hPm, hPu⟩

/-- **(M3) for the normalization in `E`.** Every `e ∈ E` is a quotient `f / g` with
`f T^a, g T^a ∈ S_E`, `g ≠ 0`: for a chart `j`, some `y ≠ 0` in `A_j` has `y e` integral over `A_j`
(`E / K` is algebraic and `K = Frac A_j`); clearing denominators gives
`(y e) z̃_j^N ∈ (S_E)_N`, and `e = ((y e) z̃_j^N z̃_j^a) / (f z̃_j^N)` for `y = f / z̃_j^a`. -/
theorem exists_eq_div_normalizationInS [FiniteDimensional K E] (e : E) :
    ∃ (a : Fin r →₀ ℕ) (f g : E), monomial a f ∈ X.normalizationInS E ∧
      monomial a g ∈ X.normalizationInS E ∧ g ≠ 0 ∧ e = f / g := by
  obtain ⟨j, hj⟩ := X.exists_chartIndex_ne_zero
  let A := X.chartAlg j
  have := isFractionRing_chartAlg hj
  have : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hea : IsAlgebraic A e :=
    (IsFractionRing.isAlgebraic_iff A K E).2 (Algebra.IsAlgebraic.isAlgebraic e)
  obtain ⟨y, hy0, hyi⟩ := hea.exists_integral_multiple
  obtain ⟨p, hpm, hp⟩ := hyi
  obtain ⟨N, hN⟩ := exists_isIntegral_monomial_of_chartAlg (E := E) hj (w := y • e) p hpm hp
  obtain ⟨a, f, hf, hyf⟩ := (mem_chartAlg_iff hj).1 y.2
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hy0 (Subtype.ext (by rw [hyf, zero_div]; rfl))
  have hDa := chartDen_ne_zero hj a
  have hDN := chartDen_ne_zero hj N
  have hye : y • e = algebraMap K E f / algebraMap K E (X.chartDen j a) * e := by
    rw [Algebra.smul_def]
    change algebraMap K E (y : K) * e = _
    rw [hyf, map_div₀]
  refine ⟨N + a, y • e * algebraMap K E (X.chartDen j N) * algebraMap K E (X.chartDen j a),
    algebraMap K E (f * X.chartDen j N), ?_, ?_, ?_, ?_⟩
  · rw [← monomial_mul]
    exact Subalgebra.mul_mem _ (mem_normalizationInS.2 hN)
      (by rw [← coeffMap_monomial (k := k)]
          exact coeffMap_mem_normalizationInS (X.chartDen_mem_piece j a))
  · rw [← coeffMap_monomial (k := k), add_comm]
    exact coeffMap_mem_normalizationInS (mul_mem_piece hf (X.chartDen_mem_piece j N))
  · exact (map_ne_zero _).2 (mul_ne_zero hf0 hDN)
  · rw [hye, map_mul]
    have h1 : algebraMap K E f ≠ 0 := (map_ne_zero _).2 hf0
    have h2 : algebraMap K E (X.chartDen j a) ≠ 0 := (map_ne_zero _).2 hDa
    have h3 : algebraMap K E (X.chartDen j N) ≠ 0 := (map_ne_zero _).2 hDN
    field_simp

/-! ### Integrality over `S` and over `μ(S)` -/

variable (X E) in
/-- The ring map `S → E[T]`, `p ↦ μ(p)`. -/
def coeffMapS : X.S →+* MvPolynomial (Fin r) E :=
  (coeffMap k E).toRingHom.comp X.S.val.toRingHom

/-- Integrality over `μ(S)` is integrality over `S` (acting through `μ`): `S → μ(S)` is
surjective. -/
theorem isIntegral_imageS_iff {u : MvPolynomial (Fin r) E} :
    IsIntegral (X.imageS E) u ↔ (X.coeffMapS E).IsIntegralElem u := by
  let g : X.S →+* X.imageS E := (X.coeffMapS E).codRestrict _ fun p => coeffMap_mem_imageS p.2
  have hg : Function.Surjective g := by
    rintro ⟨_, p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩
  have hcomp : (algebraMap (X.imageS E) (MvPolynomial (Fin r) E)).comp g = X.coeffMapS E :=
    RingHom.ext fun _ => rfl
  constructor
  · rintro ⟨q, hqm, hq⟩
    have : Nontrivial (X.imageS E) := inferInstance
    obtain ⟨p, hpq, -, hpm⟩ := Polynomial.lifts_and_degree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective hg q) hqm
    refine ⟨p, hpm, ?_⟩
    rw [← hcomp, ← Polynomial.eval₂_map, hpq, hq]
  · rintro ⟨p, hpm, hp⟩
    refine ⟨p.map g, hpm.map g, ?_⟩
    rw [Polynomial.eval₂_map, hcomp, hp]

/-! ### (M2) and finiteness -/

/-- **(M2) for the normalization in `E`.** Elements of `S_E` are integral over the subalgebra
generated by the coordinates `μ(z^{(c)}_j)`: `μ(S)` is integral over `μ(k[z])` and `S_E` over
`μ(S)`. -/
theorem isIntegral_coordAlg_normalizationInS {p : MvPolynomial (Fin r) E}
    (hp : p ∈ X.normalizationInS E) :
    IsIntegral (Algebra.adjoin k (Set.range fun i : X.CoordIndex =>
      monomial (Finsupp.single i.1 1) (algebraMap K E (X.coord i.1 i.2)))) p := by
  set R' := Algebra.adjoin k (Set.range fun i : X.CoordIndex =>
      monomial (Finsupp.single i.1 1) (algebraMap K E (X.coord i.1 i.2)))
  have hmap : ∀ q ∈ X.coordAlg, coeffMap k E q ∈ R' := by
    intro q hq
    have e : X.coordAlg.map (coeffMap k E) = R' := by
      rw [coordAlg, AlgHom.map_adjoin, ← Set.range_comp]
      exact congrArg (Algebra.adjoin k) (congrArg Set.range (funext fun i =>
        coeffMap_monomial _ _ _))
    rw [← e]
    exact ⟨q, hq, rfl⟩
  set T' := integralClosure R' (MvPolynomial (Fin r) E)
  have hST : ∀ q ∈ X.imageS E, q ∈ T' := by
    rintro _ ⟨s, hs, rfl⟩
    let φ : X.coordAlg →+* R' :=
      ((coeffMap k E).toRingHom.comp X.coordAlg.val.toRingHom).codRestrict R'
        fun q => hmap q q.2
    exact (mem_integralClosure_iff _ _).2 (IsIntegral.map_of_comp_eq φ (coeffMap k E).toRingHom
      (RingHom.ext fun _ => rfl) (X.isIntegral_coordAlg hs))
  let ψ : X.imageS E →+* T' :=
    { toFun := fun q => ⟨q.1, hST q.1 q.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra (X.imageS E) T' := ψ.toAlgebra
  have : IsScalarTower (X.imageS E) T' (MvPolynomial (Fin r) E) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : IsIntegral T' p := (mem_normalizationInS.1 hp).tower_top
  exact isIntegral_trans p h1

variable (X E) in
/-- The inclusion `S → S_E`, `p ↦ μ(p)`. -/
def normalizationInHom : X.S →+* X.normalizationInS E :=
  (X.coeffMapS E).codRestrict _ fun p => coeffMap_mem_normalizationInS p.2

/-- **Finiteness of the normalization** (`rmk:gl-model-examples`(2),(3),
`thm:bj-normalization-finite`): `S_E` is a finite `S`-module, for `k` perfect and `E / K` finite.
It is the integral closure of `S` in `E(T) = Frac E[T]` (`E[T]` is integrally closed), and
`E(T)` is a finite extension of `K(T) = Frac S`. -/
theorem finite_normalizationInHom [PerfectField k] [FiniteDimensional K E] :
    (X.normalizationInHom E).Finite := by
  set R := MvPolynomial (Fin r) K
  set B := MvPolynomial (Fin r) E
  set K' := FractionRing R
  set L := FractionRing B
  let _ : Algebra R B := (MvPolynomial.map (σ := Fin r) (algebraMap K E)).toAlgebra
  have hμ : Function.Injective (algebraMap R B) :=
    MvPolynomial.map_injective _ (algebraMap K E).injective
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).2 hμ
  have : Module.Finite R B := finite_map_algebraMap
  have hBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).2 (by
    rw [IsScalarTower.algebraMap_eq R B L]
    exact hBL.comp hμ)
  let _ : Algebra K' L := FractionRing.liftAlgebra R L
  have : IsScalarTower R K' L := FractionRing.isScalarTower_liftAlgebra R L
  have : FiniteDimensional K' L := Module.Finite.of_isLocalization R B R⁰
  have := X.isFractionRing_S
  have : IsScalarTower X.S K' L := IsScalarTower.of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply R K' L x.1
  let _ : Algebra X.S (X.normalizationInS E) := (X.normalizationInHom E).toAlgebra
  have : IsScalarTower X.S (X.normalizationInS E) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower X.S B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hint : ∀ u : B, IsIntegral X.S u ↔ IsIntegral (X.imageS E) u := fun u =>
    isIntegral_imageS_iff.symm
  have : IsIntegralClosure (X.normalizationInS E) X.S L := by
    refine ⟨fun y z h => Subtype.ext (hBL h), fun {x} => ⟨fun hx => ?_, ?_⟩⟩
    · obtain ⟨u, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hx.tower_top (A := B))
      have hu : IsIntegral X.S u :=
        (isIntegral_algHom_iff (IsScalarTower.toAlgHom X.S B L) hBL).1 hx
      exact ⟨⟨u, mem_normalizationInS.2 ((hint u).1 hu)⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ((hint y.1).2 (mem_normalizationInS.1 y.2)).map (IsScalarTower.toAlgHom X.S B L)
  exact finite_of_isIntegralClosure_of_finiteType k X.S K' L (X.normalizationInS E)

theorem finiteType_normalizationInS [PerfectField k] [FiniteDimensional K E] :
    Algebra.FiniteType k (X.normalizationInS E) := by
  let _ : Algebra X.S (X.normalizationInS E) := (X.normalizationInHom E).toAlgebra
  have : Module.Finite X.S (X.normalizationInS E) := X.finite_normalizationInHom
  have : IsScalarTower k X.S (X.normalizationInS E) := IsScalarTower.of_algebraMap_eq fun c =>
    Subtype.ext (((coeffMap k E).commutes c).symm)
  exact Algebra.FiniteType.trans (S := X.S) inferInstance inferInstance

/-! ### The normalization in `E` and the normalization -/

variable (X E) in
/-- **The normalization of `𝒳` in a finite extension `E ⊇ K`** (`rmk:gl-model-examples`(3)):
`(E, S_E, z)`, where `S_E ⊆ E[T]` is the integral closure of `μ(S)` and the coordinates are the
images of those of `𝒳`. It is a normal model (`isNormal_normalizationIn`). Here `k` is infinite
(gradedness, torus argument) and perfect (finiteness of normalization). -/
def normalizationIn [Infinite k] [PerfectField k] [FiniteDimensional K E] : MultiModel k E r where
  S := X.normalizationInS E
  isGraded _ hp a := isGraded_normalizationInS hp a
  fg := (Subalgebra.fg_iff_finiteType _).2 X.finiteType_normalizationInS
  M := X.M
  coord c j := algebraMap K E (X.coord c j)
  coord_mem c j := by
    rw [← coeffMap_monomial (k := k)]
    exact coeffMap_mem_normalizationInS (X.coord_mem c j)
  exists_coord_ne_zero c := by
    obtain ⟨j, hj⟩ := X.exists_coord_ne_zero c
    exact ⟨j, (map_ne_zero _).2 hj⟩
  isIntegral _ hp := isIntegral_coordAlg_normalizationInS hp
  generates := eq_top_iff.2 fun x _ =>
    IntermediateField.subset_adjoin _ _ (exists_eq_div_normalizationInS x)

section normalizationIn

variable [Infinite k] [PerfectField k] [FiniteDimensional K E]

theorem normalizationIn_S : (X.normalizationIn E).S = X.normalizationInS E :=
  rfl

theorem normalizationIn_coord (c : Fin r) (j : Fin (X.M c + 1)) :
    (X.normalizationIn E).coord c j = algebraMap K E (X.coord c j) :=
  rfl

theorem mem_normalizationIn_S {p : MvPolynomial (Fin r) E} :
    p ∈ (X.normalizationIn E).S ↔ IsIntegral (X.imageS E) p :=
  Iff.rfl

/-- `μ(S) ⊆ S_E`. -/
theorem coeffMap_mem_normalizationIn_S {p : MvPolynomial (Fin r) K} (hp : p ∈ X.S) :
    coeffMap k E p ∈ (X.normalizationIn E).S :=
  coeffMap_mem_normalizationInS hp

/-- **`rmk:gl-model-examples`(3).** The normalization of `𝒳` in `E` is a normal model. -/
theorem isNormal_normalizationIn : (X.normalizationIn E).IsNormal := by
  rw [isNormal_iff, isIntegrallyClosedIn_iff]
  refine ⟨Subtype.val_injective, fun {x} hx => ?_⟩
  -- `S_E` is integral over `μ(S)`, so `x` is integral over `μ(S)`.
  let ι : X.imageS E →+* (X.normalizationIn E).S :=
    { toFun := fun q => ⟨q.1, imageS_le_normalizationInS q.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra (X.imageS E) (X.normalizationIn E).S := ι.toAlgebra
  have : IsScalarTower (X.imageS E) (X.normalizationIn E).S (MvPolynomial (Fin r) E) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral (X.imageS E) (X.normalizationIn E).S :=
    ⟨fun y => (isIntegral_algHom_iff (IsScalarTower.toAlgHom (X.imageS E)
      (X.normalizationIn E).S (MvPolynomial (Fin r) E)) Subtype.val_injective).1
        (mem_normalizationInS.1 y.2)⟩
  exact ⟨⟨x, mem_normalizationInS.2 (isIntegral_trans x hx)⟩, rfl⟩

end normalizationIn

/-- `μ(S) = S` for `E = K`. -/
theorem imageS_self : X.imageS K = X.S := by
  have h : ∀ p : MvPolynomial (Fin r) K, coeffMap k K p = p := fun p => by
    rw [coeffMap_apply, Algebra.algebraMap_self, map_id]
  ext q
  refine ⟨?_, fun hq => ⟨q, hq, h q⟩⟩
  rintro ⟨p, hp, rfl⟩
  change coeffMap k K p ∈ X.S
  rw [h p]
  exact hp

variable (X) in
/-- **The normalization** `𝒳^ν = (K, S^ν, z)` of `𝒳` (`rmk:gl-model-examples`(2)): `S^ν` is the
integral closure of `S` in `K[T]` (`mem_normalization_S`); it is a normal model
(`isNormal_normalization`), finite over `S` (`finite_normalization`). -/
def normalization [Infinite k] [PerfectField k] : MultiModel k K r :=
  X.normalizationIn K

section normalization

variable [Infinite k] [PerfectField k]

/-- `p ∈ S^ν` iff `p ∈ K[T]` is integral over `S`. -/
theorem mem_normalization_S {p : MvPolynomial (Fin r) K} :
    p ∈ X.normalization.S ↔ IsIntegral X.S p := by
  change IsIntegral (X.imageS K) p ↔ _
  rw [X.imageS_self]

theorem le_normalization_S : X.S ≤ X.normalization.S := fun p hp =>
  mem_normalization_S.2 (isIntegral_algebraMap (R := X.S) (x := ⟨p, hp⟩))

theorem normalization_coord (c : Fin r) (j : Fin (X.M c + 1)) :
    X.normalization.coord c j = X.coord c j :=
  rfl

theorem normalization_M : X.normalization.M = X.M :=
  rfl

theorem isNormal_normalization : X.normalization.IsNormal :=
  X.isNormal_normalizationIn (E := K)

omit [Infinite k] in
/-- `S^ν` is a finite `S`-module. -/
theorem finite_normalization : (X.normalizationInHom K).Finite :=
  X.finite_normalizationInHom

end normalization

end MultiModel

end EnvelopeProperty
