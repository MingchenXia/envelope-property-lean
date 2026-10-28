/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.ValuationExtension
import EnvelopeProperty.Berkovich.GaussValuation

/-!
# Weighted Gauss norms of norm forms

This file proves the algebraic heart of Fang–Han–Xia, *The envelope property for unibranch
projective varieties*, Lemma 5.13 (`lem:finite-flat-norm`), in the étale case, over an abstract
complete field: the computation in the proof of `prop:weighted-coefficient-norm` (FHX §4),
identifying the weighted Gauss norm of the coefficients of a norm form.

Let `H` be a field with a complete nonarchimedean norm (possibly trivial), `L/H` a finite
separable extension, `|·|_L` the unique extension of the norm of `H` to `L`, `b_j ∈ L` and
`r_j = e^{λ_j} ≥ 0` (`j ∈ σ`, a finite type). The norm form of the linear form `∑_j b_j X_j` is
`P = N_{L[X]/H[X]}(∑_j b_j X_j) = ∑_α c_α X^α ∈ H[X]`. Then
`max_α |c_α| r^α = (max_j |b_j|_L r_j)^{[L:H]}`.

The proof: in an algebraic closure `Ω` of `H`, with the unique extension `|·|_Ω` of the norm,
`P = ∏_{τ : L → Ω} ∑_j τ(b_j) X_j` (both sides agree at every `H`-point by
`Algebra.norm_eq_prod_embeddings`, and `H` is infinite); weighted Gauss norms are multiplicative
(Gauss's lemma), the weighted Gauss norm of `∑_j τ(b_j) X_j` is `max_j |τ(b_j)|_Ω r_j`, and
`|τ(·)|_Ω = |·|_L` by uniqueness of extensions (`EnvelopeProperty.Valuation.eq_of_extends_norm`).
For a finite étale algebra `E ≅ ∏_i L_i` the norm is the product of the norms of the factors,
so `max_α |c_α| r^α = ∏_i (max_j |b_{ij}|_{L_i} r_j)^{[L_i:H]}`.

## Main definitions

* `EnvelopeProperty.monoWeight r α = ∏_j r_j^{α_j}`; `EnvelopeProperty.expRadius λ` gives the
  radii `r_j = e^{λ_j}` (`EnvelopeProperty.coe_monoWeight_expRadius`:
  `r^α = exp (∑_j α_j λ_j)`).
* `EnvelopeProperty.wgaussValuation v r`: the weighted Gauss valuation
  `∑_α a_α X^α ↦ max_α v(a_α) r^α` on `MvPolynomial σ R`, for a valuation `v : R → ℝ≥0`.

## Main results

* `EnvelopeProperty.wgaussValuation` is a valuation (multiplicativity `wgaussFun_mul`: Gauss's
  lemma, via lexicographically minimal exponents realising the maxima);
  `wgaussValuation_linear`: the value on a linear form `∑_j C(b_j) X_j` is `max_j v(b_j) r_j`;
  `wgaussValuation_map`: compatibility with extension of coefficients.
* `EnvelopeProperty.eval_norm_sum_X_tmul`: the norm of `∑_j X_j ⊗ b_j` in
  `K[X] ⊗_K E` over `K[X]` (for a finite `K`-algebra `E`) evaluates at `t ∈ K^σ` to
  `N_{E/K}(∑_j t_j b_j)`.
* `EnvelopeProperty.algebraNorm_pi`: the norm on a finite product of finite free algebras is the
  product of the norms.
* `EnvelopeProperty.wgaussValuation_eq_pow_of_eval_eq_norm`,
  `EnvelopeProperty.wgaussValuation_norm_sum_X_tmul`: the norm identity for a finite separable
  field extension.
* `EnvelopeProperty.wgaussValuation_eq_prod_of_eval_eq_prod_norm`,
  `EnvelopeProperty.wgaussValuation_eq_prod_of_eval_eq_norm`,
  `EnvelopeProperty.wgaussValuation_norm_sum_X_tmul_of_algEquiv`: the norm identity for a finite
  étale algebra `E ≃ₐ[H] ∏_i L_i`.

The norm form is characterised by its values at `H`-points
(`∀ t, eval t P = N(∑_j t_j b_j)`), which determines `P` as `H` is assumed infinite; this is the
interface used for fibre algebras `H(s) ⊗_{k[S]} k[Y]` in `lem:finite-flat-norm`. The infinite
field hypothesis holds for the completed residue fields in FHX §5, which contain the
algebraically closed field `k`.
-/

open scoped NNReal ENNReal Topology TensorProduct

open MvPolynomial

noncomputable section

namespace EnvelopeProperty

section WeightedGauss

variable {R : Type*} [CommRing R] (v : Valuation R ℝ≥0) {σ : Type*} (r : σ → ℝ≥0)

/-- The weight `r^α = ∏_j r_j^{α_j}` of a monomial exponent `α`. -/
def monoWeight (α : σ →₀ ℕ) : ℝ≥0 :=
  α.prod fun j n => r j ^ n

theorem monoWeight_add (α β : σ →₀ ℕ) :
    monoWeight r (α + β) = monoWeight r α * monoWeight r β :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

@[simp]
theorem monoWeight_zero : monoWeight r 0 = 1 :=
  Finsupp.prod_zero_index

@[simp]
theorem monoWeight_single (j : σ) (n : ℕ) : monoWeight r (Finsupp.single j n) = r j ^ n :=
  Finsupp.prod_single_index (pow_zero _)

/-- The underlying function of the weighted Gauss valuation. -/
def wgaussFun (P : MvPolynomial σ R) : ℝ≥0 :=
  P.support.sup fun α => v (P.coeff α) * monoWeight r α

theorem le_wgaussFun (P : MvPolynomial σ R) (α : σ →₀ ℕ) :
    v (P.coeff α) * monoWeight r α ≤ wgaussFun v r P := by
  by_cases h : α ∈ P.support
  · exact Finset.le_sup (f := fun α => v (P.coeff α) * monoWeight r α) h
  · rw [notMem_support_iff.1 h, v.map_zero, zero_mul]
    exact zero_le

theorem wgaussFun_le_iff (P : MvPolynomial σ R) (c : ℝ≥0) :
    wgaussFun v r P ≤ c ↔ ∀ α, v (P.coeff α) * monoWeight r α ≤ c :=
  ⟨fun h α => (le_wgaussFun v r P α).trans h, fun h => Finset.sup_le fun α _ => h α⟩

theorem wgaussFun_eq_sup_of_subset (P : MvPolynomial σ R) {s : Finset (σ →₀ ℕ)}
    (hs : P.support ⊆ s) :
    wgaussFun v r P = s.sup fun α => v (P.coeff α) * monoWeight r α :=
  le_antisymm (Finset.sup_mono hs) (Finset.sup_le fun α _ => le_wgaussFun v r P α)

theorem exists_eq_wgaussFun (P : MvPolynomial σ R) :
    ∃ α, wgaussFun v r P = v (P.coeff α) * monoWeight r α := by
  rcases P.support.eq_empty_or_nonempty with h | h
  · refine ⟨0, ?_⟩
    rw [support_eq_empty.1 h]
    simp [wgaussFun]
  · obtain ⟨α, -, hα⟩ := Finset.exists_mem_eq_sup _ h fun α => v (P.coeff α) * monoWeight r α
    exact ⟨α, hα⟩

theorem wgaussFun_monomial (α : σ →₀ ℕ) (a : R) :
    wgaussFun v r (monomial α a) = v a * monoWeight r α := by
  classical
  rw [wgaussFun_eq_sup_of_subset v r _ (support_monomial_subset (s := α) (a := a)),
    Finset.sup_singleton, coeff_monomial, if_pos rfl]

theorem wgaussFun_C (a : R) : wgaussFun v r (C a : MvPolynomial σ R) = v a := by
  rw [← monomial_zero', wgaussFun_monomial, monoWeight_zero, mul_one]

theorem wgaussFun_add_le (P Q : MvPolynomial σ R) :
    wgaussFun v r (P + Q) ≤ max (wgaussFun v r P) (wgaussFun v r Q) := by
  rw [wgaussFun_le_iff]
  intro α
  rw [coeff_add]
  calc v (P.coeff α + Q.coeff α) * monoWeight r α
      ≤ max (v (P.coeff α)) (v (Q.coeff α)) * monoWeight r α := by
        gcongr
        exact v.map_add _ _
    _ = max (v (P.coeff α) * monoWeight r α) (v (Q.coeff α) * monoWeight r α) :=
        max_mul_of_nonneg _ _ zero_le
    _ ≤ max (wgaussFun v r P) (wgaussFun v r Q) :=
        max_le_max (le_wgaussFun v r P α) (le_wgaussFun v r Q α)

theorem wgaussFun_mul_le (P Q : MvPolynomial σ R) :
    wgaussFun v r (P * Q) ≤ wgaussFun v r P * wgaussFun v r Q := by
  classical
  rw [wgaussFun_le_iff]
  intro γ
  rw [coeff_mul]
  obtain ⟨x, hx, hle⟩ := exists_valuation_sum_le v
    (s := Finset.HasAntidiagonal.antidiagonal γ) ⟨(0, γ), by simp⟩
    fun x => P.coeff x.1 * Q.coeff x.2
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  calc v (∑ x ∈ Finset.HasAntidiagonal.antidiagonal γ, P.coeff x.1 * Q.coeff x.2) * monoWeight r γ
      ≤ v (P.coeff x.1 * Q.coeff x.2) * monoWeight r γ := by gcongr
    _ = (v (P.coeff x.1) * monoWeight r x.1) * (v (Q.coeff x.2) * monoWeight r x.2) := by
        rw [v.map_mul, ← hx, monoWeight_add]; ring
    _ ≤ wgaussFun v r P * wgaussFun v r Q :=
        mul_le_mul' (le_wgaussFun v r P _) (le_wgaussFun v r Q _)

/-- In a linear order on exponents compatible with addition, a minimal exponent realising the
maximum. -/
theorem exists_lex_min_eq_wgaussFun [LinearOrder σ] (P : MvPolynomial σ R)
    (hP : wgaussFun v r P ≠ 0) :
    ∃ α, wgaussFun v r P = v (P.coeff α) * monoWeight r α ∧
      ∀ β, toLex β < toLex α → v (P.coeff β) * monoWeight r β < wgaussFun v r P := by
  classical
  obtain ⟨α₀, hα₀⟩ := exists_eq_wgaussFun v r P
  set S := P.support.filter fun α => v (P.coeff α) * monoWeight r α = wgaussFun v r P
  have hα₀S : α₀ ∈ S := by
    refine Finset.mem_filter.2 ⟨mem_support_iff.2 fun h => hP ?_, hα₀.symm⟩
    rw [hα₀, h, v.map_zero, zero_mul]
  obtain ⟨α, hαS, hmin⟩ := S.exists_min_image toLex ⟨α₀, hα₀S⟩
  refine ⟨α, (Finset.mem_filter.1 hαS).2.symm, fun β hβ => ?_⟩
  refine lt_of_le_of_ne (le_wgaussFun v r P β) fun h => ?_
  have hβS : β ∈ S := by
    refine Finset.mem_filter.2 ⟨mem_support_iff.2 fun h0 => hP ?_, h⟩
    rw [← h, h0, v.map_zero, zero_mul]
  exact absurd (hmin β hβS) (not_le.2 hβ)

/-- **Gauss's lemma** for weighted Gauss norms (lower bound), via lexicographically minimal
exponents realising the maxima. -/
theorem mul_le_wgaussFun_mul (P Q : MvPolynomial σ R) :
    wgaussFun v r P * wgaussFun v r Q ≤ wgaussFun v r (P * Q) := by
  classical
  let : LinearOrder σ := linearOrderOfSTO WellOrderingRel
  by_cases hP : wgaussFun v r P = 0
  · rw [hP, zero_mul]; exact zero_le
  by_cases hQ : wgaussFun v r Q = 0
  · rw [hQ, mul_zero]; exact zero_le
  obtain ⟨α, hα, hαmin⟩ := exists_lex_min_eq_wgaussFun v r P hP
  obtain ⟨β, hβ, hβmin⟩ := exists_lex_min_eq_wgaussFun v r Q hQ
  have key : v (P.coeff α * Q.coeff β) * monoWeight r (α + β) =
      wgaussFun v r P * wgaussFun v r Q := by
    rw [hα, hβ, v.map_mul, monoWeight_add]; ring
  refine le_trans ?_ (le_wgaussFun v r (P * Q) (α + β))
  rw [coeff_mul,
    v.map_sum_eq_of_lt (j := (α, β)) (Finset.HasAntidiagonal.mem_antidiagonal.2 rfl), key]
  intro x hx
  rw [Finset.mem_sdiff, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_singleton] at hx
  obtain ⟨hxsum, hxne⟩ := hx
  refine lt_of_mul_lt_mul_right (a := monoWeight r (α + β)) ?_ zero_le
  rw [key]
  have hcases : toLex x.1 < toLex α ∨ toLex x.2 < toLex β := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    rcases h1.lt_or_eq with h1 | h1
    · have : toLex (α + β) < toLex (x.1 + x.2) :=
        add_lt_add_of_lt_of_le h1 h2
      rw [hxsum] at this
      exact lt_irrefl _ this
    rcases h2.lt_or_eq with h2 | h2
    · have : toLex (α + β) < toLex (x.1 + x.2) :=
        add_lt_add_of_le_of_lt h1.le h2
      rw [hxsum] at this
      exact lt_irrefl _ this
    exact hxne (Prod.ext (toLex.injective h1).symm (toLex.injective h2).symm)
  calc v (P.coeff x.1 * Q.coeff x.2) * monoWeight r (α + β)
      = (v (P.coeff x.1) * monoWeight r x.1) * (v (Q.coeff x.2) * monoWeight r x.2) := by
        rw [v.map_mul, ← hxsum, monoWeight_add]; ring
    _ < wgaussFun v r P * wgaussFun v r Q := by
        rcases hcases with h | h
        · calc (v (P.coeff x.1) * monoWeight r x.1) * (v (Q.coeff x.2) * monoWeight r x.2)
              ≤ (v (P.coeff x.1) * monoWeight r x.1) * wgaussFun v r Q := by
                gcongr; exact le_wgaussFun v r Q _
            _ < wgaussFun v r P * wgaussFun v r Q := by
                gcongr; exact hαmin _ h
        · calc (v (P.coeff x.1) * monoWeight r x.1) * (v (Q.coeff x.2) * monoWeight r x.2)
              ≤ wgaussFun v r P * (v (Q.coeff x.2) * monoWeight r x.2) := by
                gcongr; exact le_wgaussFun v r P _
            _ < wgaussFun v r P * wgaussFun v r Q := by
                gcongr; exact hβmin _ h

/-- **Gauss's lemma**: weighted Gauss norms are multiplicative. -/
theorem wgaussFun_mul (P Q : MvPolynomial σ R) :
    wgaussFun v r (P * Q) = wgaussFun v r P * wgaussFun v r Q :=
  le_antisymm (wgaussFun_mul_le v r P Q) (mul_le_wgaussFun_mul v r P Q)

/-- The **weighted Gauss valuation** on `R[X_j : j ∈ σ]` attached to a valuation `v` on `R` and
radii `r_j ≥ 0`: `|∑_α a_α X^α| = max_α v(a_α) ∏_j r_j^{α_j}`. -/
def wgaussValuation : Valuation (MvPolynomial σ R) ℝ≥0 where
  toFun := wgaussFun v r
  map_zero' := by simp [wgaussFun]
  map_one' := by rw [← C_1, wgaussFun_C, v.map_one]
  map_mul' := wgaussFun_mul v r
  map_add_le_max' := wgaussFun_add_le v r

theorem wgaussValuation_apply (P : MvPolynomial σ R) :
    wgaussValuation v r P = P.support.sup fun α => v (P.coeff α) * monoWeight r α :=
  rfl

theorem wgaussValuation_le_iff (P : MvPolynomial σ R) (c : ℝ≥0) :
    wgaussValuation v r P ≤ c ↔ ∀ α, v (P.coeff α) * monoWeight r α ≤ c :=
  wgaussFun_le_iff v r P c

theorem le_wgaussValuation (P : MvPolynomial σ R) (α : σ →₀ ℕ) :
    v (P.coeff α) * monoWeight r α ≤ wgaussValuation v r P :=
  le_wgaussFun v r P α

theorem wgaussValuation_eq_sup_of_subset (P : MvPolynomial σ R) {s : Finset (σ →₀ ℕ)}
    (hs : P.support ⊆ s) :
    wgaussValuation v r P = s.sup fun α => v (P.coeff α) * monoWeight r α :=
  wgaussFun_eq_sup_of_subset v r P hs

@[simp]
theorem wgaussValuation_monomial (α : σ →₀ ℕ) (a : R) :
    wgaussValuation v r (monomial α a) = v a * monoWeight r α :=
  wgaussFun_monomial v r α a

@[simp]
theorem wgaussValuation_C (a : R) : wgaussValuation v r (C a : MvPolynomial σ R) = v a :=
  wgaussFun_C v r a

@[simp]
theorem wgaussValuation_X (j : σ) : wgaussValuation v r (X j : MvPolynomial σ R) = r j := by
  rw [X, wgaussValuation_monomial, v.map_one, one_mul, monoWeight_single, pow_one]

/-- The weighted Gauss norm of a linear form `∑_j b_j X_j` is `max_j v(b_j) r_j`. -/
theorem wgaussValuation_linear [Fintype σ] (b : σ → R) :
    wgaussValuation v r (∑ j, C (b j) * X j) = Finset.univ.sup fun j => v (b j) * r j := by
  classical
  have hcoeff : ∀ α, (∑ j, C (b j) * X j : MvPolynomial σ R).coeff α =
      ∑ j, if Finsupp.single j 1 = α then b j else 0 := by
    intro α
    rw [coeff_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [C_mul_X_eq_monomial, coeff_monomial]
  have hsingle : ∀ i, (∑ j, C (b j) * X j : MvPolynomial σ R).coeff (Finsupp.single i 1) =
      b i := by
    intro i
    rw [hcoeff, Finset.sum_eq_single i (fun j _ hj => if_neg fun h =>
      hj (Finsupp.single_left_injective one_ne_zero h)) (fun h => absurd (Finset.mem_univ i) h),
      if_pos rfl]
  have hsupp : (∑ j, C (b j) * X j : MvPolynomial σ R).support ⊆
      Finset.univ.image fun j => Finsupp.single j 1 := by
    intro α hα
    rw [mem_support_iff, hcoeff] at hα
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
    refine Finset.mem_image.2 ⟨j, Finset.mem_univ j, ?_⟩
    by_contra h
    exact hj (if_neg h)
  rw [wgaussValuation_eq_sup_of_subset v r _ hsupp, Finset.sup_image]
  refine Finset.sup_congr rfl fun j _ => ?_
  simp only [Function.comp_apply, hsingle, monoWeight_single, pow_one]

/-- Weighted Gauss norms are compatible with coefficient extensions that extend the valuation. -/
theorem wgaussValuation_map {S : Type*} [CommRing S] (f : R →+* S) (w : Valuation S ℝ≥0)
    (hw : ∀ a, w (f a) = v a) (P : MvPolynomial σ R) :
    wgaussValuation w r (map f P) = wgaussValuation v r P := by
  classical
  rw [wgaussValuation_eq_sup_of_subset w r _ (support_map_subset f P), wgaussValuation_apply]
  refine Finset.sup_congr rfl fun α _ => ?_
  rw [coeff_map, hw]

/-- Radii `r_j = e^{λ_j}` attached to real weights `λ_j`. -/
def expRadius (lam : σ → ℝ) (j : σ) : ℝ≥0 :=
  ⟨Real.exp (lam j), (Real.exp_pos _).le⟩

@[simp]
theorem coe_expRadius (lam : σ → ℝ) (j : σ) : (expRadius lam j : ℝ) = Real.exp (lam j) :=
  rfl

/-- For the radii `r_j = e^{λ_j}`, the weight of `α` is `exp (∑_j α_j λ_j)`. -/
theorem coe_monoWeight_expRadius (lam : σ → ℝ) (α : σ →₀ ℕ) :
    (monoWeight (expRadius lam) α : ℝ) = Real.exp (α.sum fun j n => n * lam j) := by
  rw [monoWeight, Finsupp.prod, NNReal.coe_prod, Finsupp.sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [NNReal.coe_pow, Real.exp_nat_mul]
  rfl

end WeightedGauss

/-! ### Norms of linear forms -/

section NormForm

variable {σ : Type*}

/-- The determinant of a block diagonal matrix with blocks of varying sizes. -/
theorem det_blockDiagonal' {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    {m : ι → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (d : ∀ i, Matrix (m i) (m i) R) :
    (Matrix.blockDiagonal' d).det = ∏ i, (d i).det := by
  classical
  let : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  rw [(Matrix.blockTriangular_blockDiagonal' d).det]
  have hblock : ∀ a, ((Matrix.blockDiagonal' d).toSquareBlock Sigma.fst a).det = (d a).det := by
    intro a
    let e : m a ≃ {x : Σ i, m i // x.1 = a} := (Equiv.sigmaSubtype a).symm
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext p q
    exact Matrix.blockDiagonal'_apply_eq d a p q
  rw [Finset.prod_congr rfl fun a _ => hblock a]
  refine Finset.prod_subset (Finset.subset_univ _) fun a _ ha => ?_
  have : IsEmpty (m a) := ⟨fun p => ha (Finset.mem_image.2 ⟨⟨a, p⟩, Finset.mem_univ _, rfl⟩)⟩
  exact Matrix.det_isEmpty

/-- The norm on a finite product of finite free algebras is the product of the norms. -/
theorem algebraNorm_pi {K ι : Type*} [CommRing K] [Fintype ι] {E : ι → Type*} [∀ i, CommRing (E i)]
    [∀ i, Algebra K (E i)] [∀ i, Module.Free K (E i)] [∀ i, Module.Finite K (E i)]
    (x : ∀ i, E i) : Algebra.norm K x = ∏ i, Algebra.norm K (x i) := by
  classical
  let b : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex K (E i)) K (E i) :=
    fun i => Module.Free.chooseBasis K (E i)
  rw [Algebra.norm_eq_matrix_det (Pi.basis b)]
  simp_rw [Algebra.norm_eq_matrix_det (b _)]
  rw [← det_blockDiagonal']
  congr 1
  ext ⟨i, p⟩ ⟨j, q⟩
  rw [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr, Matrix.blockDiagonal'_apply]
  dsimp only
  by_cases hij : i = j
  · subst hij
    rw [dif_pos rfl, Pi.mul_apply, Pi.single_eq_same, Algebra.leftMulMatrix_eq_repr_mul]
    rfl
  · rw [dif_neg hij, Pi.mul_apply, Pi.single_eq_of_ne hij, mul_zero, map_zero,
      Finsupp.zero_apply]

/-- The norm form of a linear form commutes with specialisation: for a finite `K`-algebra `E`
and `b_j ∈ E`, evaluating the norm of `∑_j X_j ⊗ b_j ∈ K[X] ⊗_K E` over `K[X]` at `t ∈ K^σ`
gives the norm of `∑_j t_j b_j` over `K`. -/
theorem eval_norm_sum_X_tmul {K E σ : Type*} [Field K] [CommRing E] [Algebra K E]
    [Module.Finite K E] [Fintype σ] (b : σ → E) (t : σ → K) :
    eval t (Algebra.norm (MvPolynomial σ K) (∑ j, (X j : MvPolynomial σ K) ⊗ₜ[K] b j)) =
      Algebra.norm K (∑ j, t j • b j) := by
  classical
  let e := Module.finBasis K E
  let B := Algebra.TensorProduct.basis (MvPolynomial σ K) e
  rw [Algebra.norm_eq_matrix_det B, Algebra.norm_eq_matrix_det e, RingHom.map_det]
  congr 1
  ext a c
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply, Finset.sum_mul,
    Finset.sum_mul]
  simp [Algebra.TensorProduct.tmul_mul_tmul, B]

/-- Two polynomials over an integral domain `Ω`, one of them with coefficients in an infinite
subring `K ↪ Ω`, are equal if they agree on all `K`-points. -/
theorem map_eq_of_eval_eq {K Ω : Type*} [CommRing K] [Infinite K] [CommRing Ω] [IsDomain Ω]
    (ι : K →+* Ω) (hι : Function.Injective ι) {P : MvPolynomial σ K} {Q : MvPolynomial σ Ω}
    (h : ∀ t : σ → K, eval (ι ∘ t) Q = ι (eval t P)) : map ι P = Q := by
  refine funext_set (fun _ => Set.range ι) (fun _ => Set.infinite_range_of_injective hι)
    fun x hx => ?_
  choose t ht using fun i => hx i (Set.mem_univ i)
  have hxt : x = ι ∘ t := funext fun i => (ht i).symm
  subst hxt
  rw [h, eval_map]
  exact (eval₂_comp_left ι (RingHom.id K) t P).symm

variable {K : Type*} [Field K]

/-- For a finite separable extension `L/K` and an algebraically closed extension `Ω` of `K`, the
product of the conjugate linear forms `∑_j τ(b_j) X_j` over the `K`-embeddings `τ : L → Ω`
evaluates at a `K`-point `t` to the norm of `∑_j t_j b_j`. -/
theorem eval_prod_embeddings [Fintype σ] {L Ω : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (b : σ → L) (t : σ → K) :
    eval (algebraMap K Ω ∘ t) (∏ τ : L →ₐ[K] Ω, ∑ j, C (τ (b j)) * X j) =
      algebraMap K Ω (Algebra.norm K (∑ j, t j • b j)) := by
  rw [Algebra.norm_eq_prod_embeddings, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, eval_C, eval_X, map_smul, Algebra.smul_def, mul_comm]
  rfl

section Complete

variable {H : Type*} [NormedField H] [CompleteSpace H] [IsUltrametricDist H]

/-- The weighted Gauss norm of the product of the conjugates `∑_j τ(b_j) X_j`, for the unique
extension `w_Ω` of the norm of `H` to an algebraic extension `Ω`, is
`(max_j |b_j|_L r_j)^{[L:H]}`: each conjugate has weighted Gauss norm `max_j |τ(b_j)|_Ω r_j`
and `|τ(·)|_Ω = |·|_L` by uniqueness of extensions. -/
theorem wgaussValuation_prod_embeddings [Fintype σ] {L Ω : Type*} [Field L] [Algebra H L]
    [FiniteDimensional H L] [Algebra.IsSeparable H L] [Field Ω] [Algebra H Ω] [IsAlgClosed Ω]
    (wΩ : Valuation Ω ℝ≥0) (w : Valuation L ℝ≥0)
    (hwΩ : ∀ c : H, wΩ (algebraMap H Ω c) = ‖c‖₊) (hw : ∀ c : H, w (algebraMap H L c) = ‖c‖₊)
    (b : σ → L) (r : σ → ℝ≥0) :
    wgaussValuation wΩ r (∏ τ : L →ₐ[H] Ω, ∑ j, C (τ (b j)) * X j) =
      (Finset.univ.sup fun j => w (b j) * r j) ^ Module.finrank H L := by
  have hτ : ∀ (τ : L →ₐ[H] Ω) (x : L), wΩ (τ x) = w x := by
    intro τ x
    have := Valuation.eq_of_extends_norm (K := H) (v := wΩ.comap (τ : L →+* Ω)) (w := w)
      (fun c => by rw [Valuation.comap_apply, RingHom.coe_coe, AlgHom.commutes, hwΩ]) hw
    exact congrArg (fun u : Valuation L ℝ≥0 => u x) this
  rw [map_prod, ← AlgHom.card H L Ω, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [wgaussValuation_linear]
  simp only [hτ]

/-- **Norm identity for a finite separable extension** (FHX `lem:finite-flat-norm`, étale case;
proof of `prop:weighted-coefficient-norm`). Let `H` be a complete nonarchimedean field (possibly
trivially normed), infinite, `L/H` a finite separable extension with the unique extension `w` of
the norm of `H`, `b_j ∈ L`, and `P ∈ H[X_j]` the norm form of `∑_j b_j X_j`, characterised by
`P(t) = N_{L/H}(∑_j t_j b_j)` for all `t ∈ H^σ`. Then for all radii `r_j`,
`max_α |c_α| r^α = (max_j |b_j|_L r_j)^{[L:H]}`. -/
theorem wgaussValuation_eq_pow_of_eval_eq_norm [Infinite H] [Fintype σ] {L : Type*} [Field L]
    [Algebra H L] [FiniteDimensional H L] [Algebra.IsSeparable H L] (w : Valuation L ℝ≥0)
    (hw : ∀ c : H, w (algebraMap H L c) = ‖c‖₊) (b : σ → L) (r : σ → ℝ≥0)
    {P : MvPolynomial σ H} (hP : ∀ t : σ → H, eval t P = Algebra.norm H (∑ j, t j • b j)) :
    wgaussValuation NormedField.valuation r P =
      (Finset.univ.sup fun j => w (b j) * r j) ^ Module.finrank H L := by
  obtain ⟨wΩ, hwΩ⟩ := Valuation.exists_extends_norm (K := H) (L := AlgebraicClosure H)
  have hmap : map (algebraMap H (AlgebraicClosure H)) P =
      ∏ τ : L →ₐ[H] AlgebraicClosure H, ∑ j, C (τ (b j)) * X j :=
    map_eq_of_eval_eq _ (algebraMap H (AlgebraicClosure H)).injective fun t => by
      rw [eval_prod_embeddings, hP]
  rw [← wgaussValuation_map NormedField.valuation r (algebraMap H (AlgebraicClosure H)) wΩ
    (fun c => by rw [hwΩ, NormedField.valuation_apply]), hmap,
    wgaussValuation_prod_embeddings wΩ w hwΩ hw]

/-- **Norm identity for a finite étale algebra** `∏_i L_i` (product form): if
`P(t) = ∏_i N_{L_i/H}(∑_j t_j b_{ij})` for all `t ∈ H^σ`, then
`max_α |c_α| r^α = ∏_i (max_j |b_{ij}|_{L_i} r_j)^{[L_i:H]}`. -/
theorem wgaussValuation_eq_prod_of_eval_eq_prod_norm [Infinite H] [Fintype σ] {ι : Type*}
    [Fintype ι] {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra H (L i)]
    [∀ i, FiniteDimensional H (L i)] [∀ i, Algebra.IsSeparable H (L i)]
    (w : ∀ i, Valuation (L i) ℝ≥0) (hw : ∀ i (c : H), w i (algebraMap H (L i) c) = ‖c‖₊)
    (b : σ → ∀ i, L i) (r : σ → ℝ≥0) {P : MvPolynomial σ H}
    (hP : ∀ t : σ → H, eval t P = ∏ i, Algebra.norm H (∑ j, t j • b j i)) :
    wgaussValuation NormedField.valuation r P =
      ∏ i, (Finset.univ.sup fun j => w i (b j i) * r j) ^ Module.finrank H (L i) := by
  obtain ⟨wΩ, hwΩ⟩ := Valuation.exists_extends_norm (K := H) (L := AlgebraicClosure H)
  have hmap : map (algebraMap H (AlgebraicClosure H)) P =
      ∏ i, ∏ τ : L i →ₐ[H] AlgebraicClosure H, ∑ j, C (τ (b j i)) * X j :=
    map_eq_of_eval_eq _ (algebraMap H (AlgebraicClosure H)).injective fun t => by
      rw [hP, map_prod, map_prod]
      exact Finset.prod_congr rfl fun i _ => eval_prod_embeddings (fun j => b j i) t
  rw [← wgaussValuation_map NormedField.valuation r (algebraMap H (AlgebraicClosure H)) wΩ
    (fun c => by rw [hwΩ, NormedField.valuation_apply]), hmap, map_prod]
  exact Finset.prod_congr rfl fun i _ =>
    wgaussValuation_prod_embeddings wΩ (w i) hwΩ (hw i) (fun j => b j i) r

/-- **Norm identity for a finite separable extension**, stated for the norm form
`N_{H[X] ⊗_H L / H[X]}(∑_j X_j ⊗ b_j)` itself. -/
theorem wgaussValuation_norm_sum_X_tmul [Infinite H] [Fintype σ] {L : Type*} [Field L]
    [Algebra H L] [FiniteDimensional H L] [Algebra.IsSeparable H L] (w : Valuation L ℝ≥0)
    (hw : ∀ c : H, w (algebraMap H L c) = ‖c‖₊) (b : σ → L) (r : σ → ℝ≥0) :
    wgaussValuation NormedField.valuation r
        (Algebra.norm (MvPolynomial σ H) (∑ j, (X j : MvPolynomial σ H) ⊗ₜ[H] b j)) =
      (Finset.univ.sup fun j => w (b j) * r j) ^ Module.finrank H L :=
  wgaussValuation_eq_pow_of_eval_eq_norm w hw b r (eval_norm_sum_X_tmul b)

/-- **Norm identity for a finite étale algebra** `E ≃ₐ[H] ∏_i L_i`: if
`P(t) = N_{E/H}(∑_j t_j b_j)` for all `t ∈ H^σ`, then
`max_α |c_α| r^α = ∏_i (max_j |b_j|_{L_i} r_j)^{[L_i:H]}`, where `|b_j|_{L_i}` is the absolute
value of the `i`-th component of `b_j`. -/
theorem wgaussValuation_eq_prod_of_eval_eq_norm [Infinite H] [Fintype σ] {E : Type*}
    [CommRing E] [Algebra H E] {ι : Type*} [Fintype ι] {L : ι → Type*} [∀ i, Field (L i)]
    [∀ i, Algebra H (L i)] [∀ i, FiniteDimensional H (L i)] [∀ i, Algebra.IsSeparable H (L i)]
    (e : E ≃ₐ[H] ∀ i, L i) (w : ∀ i, Valuation (L i) ℝ≥0)
    (hw : ∀ i (c : H), w i (algebraMap H (L i) c) = ‖c‖₊) (b : σ → E) (r : σ → ℝ≥0)
    {P : MvPolynomial σ H} (hP : ∀ t : σ → H, eval t P = Algebra.norm H (∑ j, t j • b j)) :
    wgaussValuation NormedField.valuation r P =
      ∏ i, (Finset.univ.sup fun j => w i (e (b j) i) * r j) ^ Module.finrank H (L i) :=
  wgaussValuation_eq_prod_of_eval_eq_prod_norm w hw (fun j => e (b j)) r fun t => by
    rw [hP, ← Algebra.norm_eq_of_algEquiv e, algebraNorm_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_sum, Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply]

/-- **Norm identity for a finite étale algebra** `E ≃ₐ[H] ∏_i L_i`, stated for the norm form
`N_{H[X] ⊗_H E / H[X]}(∑_j X_j ⊗ b_j)` itself. -/
theorem wgaussValuation_norm_sum_X_tmul_of_algEquiv [Infinite H] [Fintype σ] {E : Type*}
    [CommRing E] [Algebra H E] {ι : Type*} [Fintype ι] {L : ι → Type*} [∀ i, Field (L i)]
    [∀ i, Algebra H (L i)] [∀ i, FiniteDimensional H (L i)] [∀ i, Algebra.IsSeparable H (L i)]
    (e : E ≃ₐ[H] ∀ i, L i) (w : ∀ i, Valuation (L i) ℝ≥0)
    (hw : ∀ i (c : H), w i (algebraMap H (L i) c) = ‖c‖₊) (b : σ → E) (r : σ → ℝ≥0) :
    wgaussValuation NormedField.valuation r
        (Algebra.norm (MvPolynomial σ H) (∑ j, (X j : MvPolynomial σ H) ⊗ₜ[H] b j)) =
      ∏ i, (Finset.univ.sup fun j => w i (e (b j) i) * r j) ^ Module.finrank H (L i) := by
  have : Module.Finite H E := Module.Finite.equiv e.symm.toLinearEquiv
  exact wgaussValuation_eq_prod_of_eval_eq_norm e w hw b r (eval_norm_sum_X_tmul b)

end Complete

end NormForm

end EnvelopeProperty
