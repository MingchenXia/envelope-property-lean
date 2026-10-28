import EnvelopeProperty.Cartier.PBasis

/-!
# The `p`-basis of a polynomial ring and of its fraction field

Let `k` be a perfect field of characteristic `p`, `P = k[x_i : i ∈ σ]` a polynomial ring in finitely
many variables and `F` its fraction field. The variables `x` form a `p`-basis of `P` and of `F`
(`isPBasis_X`, `isPBasis_X_fractionRing`): every `f` is uniquely `∑_{a ∈ [0,p)^σ} (f_a)^p x^a`,
with
`coeff c (f_a) = (coeff (p • c + a) f)^{1/p}`.

The Frobenius trace `Φ_x` of `EnvelopeProperty.Cartier.PBasis` and its iterates are computed by the
explicit coefficient formula (`traceIter_X`, `traceIter_X_fractionRing`)
`coeff c (Φ_x^e f) = (coeff (p^e • c + (p^e - 1, …, p^e - 1)) f)^{1/p^e}`,
i.e. `Φ_x^e f` is the coefficient of `x^{(q-1,…,q-1)}` in the decomposition of `f` over `P^q`,
`q = p^e`. In particular `Φ_x^e` maps `P` into `P` (FHX eq. (3.6) and the proof of Lemma 3.3,
`lem:divisorial-trace-estimate`, where `Φ_e` is the trace for the trivialization
`dx_1 ∧ ⋯ ∧ dx_m` of `ω_P`).

## Main definitions

* `EnvelopeProperty.Cartier.rootPoly p e a`: `f ↦ f_a` for the decomposition over `P^{p^e}`.
* `EnvelopeProperty.Cartier.polyTrace p e`: `Φ_e = rootPoly p e (p^e - 1, …, p^e - 1)`.
-/

noncomputable section

open scoped NNReal ENNReal Topology

namespace EnvelopeProperty.Cartier

open MvPolynomial Finset

variable {σ k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] [PerfectRing k p]

section Root

theorem smul_add_injective {q : ℕ} (hq : q ≠ 0) (a : σ →₀ ℕ) :
    Function.Injective (fun c : σ →₀ ℕ => q • c + a) := by
  intro c d h
  ext i
  have := DFunLike.congr_fun h i
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) (by omega)

theorem pow_ne_zero' (e : ℕ) : p ^ e ≠ 0 :=
  pow_ne_zero e hp.out.ne_zero

/-- `rootPoly p e a f` is the polynomial with `coeff c = (coeff (p^e • c + a) f)^{1/p^e}`; for `a`
in the box `[0,p^e)^σ` these are the coefficients of `f = ∑_a (f_a)^{p^e} x^a`. -/
def rootPoly (e : ℕ) (a : σ →₀ ℕ) : MvPolynomial σ k →+ MvPolynomial σ k :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp <|
    (Finsupp.mapRange.addMonoidHom (iterateFrobeniusEquiv k p e).symm.toAddMonoidHom).comp <|
      (Finsupp.comapDomain.addMonoidHom (smul_add_injective (pow_ne_zero' p e) a)).comp
        AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom

theorem coeff_rootPoly (e : ℕ) (a : σ →₀ ℕ) (f : MvPolynomial σ k) (c : σ →₀ ℕ) :
    coeff c (rootPoly p e a f) = (iterateFrobeniusEquiv k p e).symm (coeff (p ^ e • c + a) f) :=
  rfl

theorem iterateFrobeniusEquiv_symm_pow' (e : ℕ) (x : k) :
    (iterateFrobeniusEquiv k p e).symm x ^ p ^ e = x := by
  rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]

theorem iterateFrobeniusEquiv_symm_pow_mul' (e : ℕ) (x y : k) :
    (iterateFrobeniusEquiv k p e).symm (x ^ p ^ e * y) =
      x * (iterateFrobeniusEquiv k p e).symm y := by
  rw [map_mul, ← iterateFrobeniusEquiv_def, RingEquiv.symm_apply_apply]

theorem rootPoly_monomial_smul_add (e : ℕ) (a c : σ →₀ ℕ) (s : k) :
    rootPoly p e a (monomial (p ^ e • c + a) s) =
      monomial c ((iterateFrobeniusEquiv k p e).symm s) := by
  classical
  ext d
  rw [coeff_rootPoly, coeff_monomial, coeff_monomial]
  by_cases h : c = d
  · subst h
    simp
  · rw [if_neg ((smul_add_injective (pow_ne_zero' p e) a).ne h), if_neg h, map_zero]

theorem rootPoly_monomial_of_ne (e : ℕ) (a b : σ →₀ ℕ) (s : k)
    (h : ∀ c : σ →₀ ℕ, p ^ e • c + a ≠ b) : rootPoly p e a (monomial b s) = 0 := by
  classical
  ext d
  rw [coeff_rootPoly, coeff_monomial, if_neg (h d).symm, map_zero, coeff_zero]

private theorem nat_mul_add_eq_aux {q a b c u : ℕ} (ha : a < q)
    (h : q * c + a = q * u + b) : u ≤ c ∧ b = q * (c - u) + a := by
  have huc : u ≤ c := by
    by_contra h'
    push Not at h'
    nlinarith
  refine ⟨huc, ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le huc
  simp only [mul_add, Nat.add_sub_cancel_left] at h ⊢
  omega

/-- Semilinearity of the coefficients: `(g^q f)_a = g f_a` for `a` in the box. -/
theorem rootPoly_pow_mul (e : ℕ) {a : σ →₀ ℕ} (ha : ∀ i, a i < p ^ e)
    (g f : MvPolynomial σ k) : rootPoly p e a (g ^ p ^ e * f) = g * rootPoly p e a f := by
  induction f using MvPolynomial.induction_on' with
  | monomial b s =>
    induction g using MvPolynomial.induction_on' with
    | monomial u r =>
      rw [monomial_pow, monomial_mul]
      by_cases hb : ∃ c, p ^ e • c + a = b
      · obtain ⟨c, rfl⟩ := hb
        rw [show p ^ e • u + (p ^ e • c + a) = p ^ e • (u + c) + a by rw [smul_add, add_assoc],
          rootPoly_monomial_smul_add, rootPoly_monomial_smul_add, monomial_mul,
          iterateFrobeniusEquiv_symm_pow_mul']
      · push Not at hb
        rw [rootPoly_monomial_of_ne p e a b s hb, mul_zero, rootPoly_monomial_of_ne]
        intro c hc
        apply hb (c - u)
        ext i
        have := DFunLike.congr_fun hc i
        simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul] at this
        simp only [Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_tsub, Pi.add_apply,
          Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        exact (nat_mul_add_eq_aux (ha i) this).2.symm
    | add g₁ g₂ h₁ h₂ => rw [add_pow_char_pow, add_mul, map_add, h₁, h₂, add_mul]
  | add f₁ f₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add]

theorem rootPoly_one_monomial_smul_add (a c : σ →₀ ℕ) (s : k) :
    rootPoly p 1 a (monomial (p • c + a) s) =
      monomial c ((iterateFrobeniusEquiv k p 1).symm s) := by
  have := rootPoly_monomial_smul_add (k := k) p 1 a c s
  rwa [pow_one] at this

theorem rootPoly_one_pow_mul {a : σ →₀ ℕ} (ha : ∀ i, a i < p)
    (g f : MvPolynomial σ k) : rootPoly p 1 a (g ^ p * f) = g * rootPoly p 1 a f := by
  have := rootPoly_pow_mul p 1 (a := a) (by simpa using ha) g f
  rwa [pow_one] at this

theorem iterateFrobeniusEquiv_one_symm_pow (x : k) :
    (iterateFrobeniusEquiv k p 1).symm x ^ p = x := by
  have := iterateFrobeniusEquiv_symm_pow' (k := k) p 1 x
  rwa [pow_one] at this

end Root

/-! ### The variables form a `p`-basis -/

section PBasisX

variable [Fintype σ] [DecidableEq σ]

/-- A digit vector as a finitely supported exponent. -/
def Box.toFinsupp {q : ℕ} (a : Box σ q) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm a.toNat

omit [DecidableEq σ] in
@[simp]
theorem Box.toFinsupp_apply {q : ℕ} (a : Box σ q) (i : σ) : a.toFinsupp i = a i :=
  rfl

omit [DecidableEq σ] in
theorem Box.toFinsupp_injective {q : ℕ} : Function.Injective (Box.toFinsupp : Box σ q → σ →₀ ℕ) :=
  fun a b h => Box.toNat_injective (by simpa [Box.toFinsupp] using h)

omit [DecidableEq σ] in
theorem mono_X (n : σ → ℕ) :
    mono (X : σ → MvPolynomial σ k) n = monomial (Finsupp.equivFunOnFinite.symm n) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  rfl

omit [DecidableEq σ] in
theorem exists_box_smul_add (b : σ →₀ ℕ) : ∃ (c : σ →₀ ℕ) (a : Box σ p), p • c + a.toFinsupp = b := by
  refine ⟨Finsupp.mapRange (· / p) (Nat.zero_div _) b, Box.ofNat b, ?_⟩
  ext i
  simp [Box.toFinsupp, Box.ofNat, Nat.div_add_mod]

omit hp [DecidableEq σ] in
theorem box_eq_of_smul_add_eq {a a' : Box σ p} {c c' : σ →₀ ℕ}
    (h : p • c + a.toFinsupp = p • c' + a'.toFinsupp) : a = a' := by
  funext i
  have := DFunLike.congr_fun h i
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Box.toFinsupp_apply] at this
  have h1 := congrArg (· % p) this
  simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt (a i).2, Nat.mod_eq_of_lt (a' i).2] at h1
  exact Fin.ext h1

omit [Fintype σ] [DecidableEq σ] in
theorem rootPoly_one_monomial_self (a : σ →₀ ℕ) :
    rootPoly p 1 a (monomial a (1 : k)) = 1 := by
  have := rootPoly_monomial_smul_add (k := k) p 1 a 0 1
  rw [smul_zero, zero_add] at this
  rw [this, map_one (iterateFrobeniusEquiv k p 1).symm, ← C_apply, C_1]

omit [DecidableEq σ] in
theorem rootPoly_one_monomial_of_ne {a b : Box σ p} (hab : a ≠ b) :
    rootPoly p 1 a.toFinsupp (monomial b.toFinsupp (1 : k)) = 0 :=
  rootPoly_monomial_of_ne p 1 _ _ 1 fun c hc => by
    rw [pow_one] at hc
    exact hab (box_eq_of_smul_add_eq p (c := c) (c' := 0) (by rw [smul_zero, zero_add]; exact hc))

/-- The decomposition `f = ∑_{a ∈ [0,p)^σ} (f_a)^p x^a`. -/
theorem sum_rootPoly (f : MvPolynomial σ k) :
    ∑ a : Box σ p, rootPoly p 1 a.toFinsupp f ^ p * mono X a.toNat = f := by
  induction f using MvPolynomial.induction_on' with
  | monomial b s =>
    obtain ⟨c₀, a₀, rfl⟩ := exists_box_smul_add p b
    rw [Finset.sum_eq_single a₀]
    · rw [mono_X, show Finsupp.equivFunOnFinite.symm a₀.toNat = a₀.toFinsupp from rfl,
        rootPoly_one_monomial_smul_add, monomial_pow, monomial_mul, mul_one,
        iterateFrobeniusEquiv_one_symm_pow]
    · intro a _ hne
      rw [rootPoly_monomial_of_ne, zero_pow hp.out.ne_zero, zero_mul]
      intro c hc
      rw [pow_one] at hc
      exact hne (box_eq_of_smul_add_eq p hc)
    · intro h
      exact absurd (Finset.mem_univ a₀) h
  | add f g hf hg =>
    simp only [map_add, add_pow_char, add_mul, Finset.sum_add_distrib, hf, hg]

/-- Uniqueness: the `a`-coefficient of `∑_b (g_b)^p x^b` is `g_a`. -/
theorem rootPoly_pSum (g : Box σ p → MvPolynomial σ k) (a : Box σ p) :
    rootPoly p 1 a.toFinsupp (pSum p X g) = g a := by
  have ha : ∀ i, a.toFinsupp i < p := fun i => (a i).2
  rw [pSum_apply, map_sum, Finset.sum_eq_single a]
  · rw [rootPoly_one_pow_mul p ha, mono_X,
      show Finsupp.equivFunOnFinite.symm a.toNat = a.toFinsupp from rfl,
      rootPoly_one_monomial_self, mul_one]
  · intro b _ hne
    rw [rootPoly_one_pow_mul p ha, mono_X,
      show Finsupp.equivFunOnFinite.symm b.toNat = b.toFinsupp from rfl,
      rootPoly_one_monomial_of_ne p (Ne.symm hne), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The variables form a `p`-basis of the polynomial ring over a perfect field. -/
theorem isPBasis_X : IsPBasis p (X : σ → MvPolynomial σ k) := by
  constructor
  · intro g g' h
    funext a
    rw [← rootPoly_pSum p g a, ← rootPoly_pSum p g' a, h]
  · intro f
    exact ⟨fun a => rootPoly p 1 a.toFinsupp f, sum_rootPoly p f⟩

theorem isPBasis_X_coeff (f : MvPolynomial σ k) (a : Box σ p) :
    (isPBasis_X (σ := σ) (k := k) p).coeff f a = rootPoly p 1 a.toFinsupp f := by
  rw [(isPBasis_X p).coeff_eq_of_sum_eq (sum_rootPoly p f)]

/-- The exponent `(p^e - 1, …, p^e - 1)`. -/
def topExp (e : ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun _ => p ^ e - 1

omit hp [DecidableEq σ] in
@[simp]
theorem topExp_apply (e : ℕ) (i : σ) : topExp (σ := σ) p e i = p ^ e - 1 :=
  rfl

/-- The Frobenius trace of the polynomial ring: `Φ_e f = f_{(q-1,…,q-1)}`, `q = p^e`, i.e.
`coeff c (Φ_e f) = (coeff (q • c + (q-1,…,q-1)) f)^{1/q}`. -/
def polyTrace (e : ℕ) : MvPolynomial σ k →+ MvPolynomial σ k :=
  rootPoly p e (topExp p e)

omit [DecidableEq σ] in
theorem coeff_polyTrace (e : ℕ) (f : MvPolynomial σ k) (c : σ →₀ ℕ) :
    coeff c (polyTrace p e f) =
      (iterateFrobeniusEquiv k p e).symm (coeff (p ^ e • c + topExp p e) f) :=
  rfl

omit [DecidableEq σ] in
theorem polyTrace_pow_mul (e : ℕ) (g f : MvPolynomial σ k) :
    polyTrace p e (g ^ p ^ e * f) = g * polyTrace p e f :=
  rootPoly_pow_mul p e (fun i => by simp [Nat.sub_lt (Nat.pos_of_ne_zero (pow_ne_zero' p e))])
    g f

theorem trace_X (f : MvPolynomial σ k) : (isPBasis_X (σ := σ) (k := k) p).trace f =
    polyTrace p 1 f := by
  rw [IsPBasis.trace_apply, isPBasis_X_coeff, polyTrace]
  congr 2
  ext i
  simp only [Box.toFinsupp_apply, topExp_apply, pow_one]
  rfl

omit [DecidableEq σ] in
theorem polyTrace_zero (f : MvPolynomial σ k) : polyTrace p 0 f = f := by
  have h0 : topExp (σ := σ) p 0 = 0 := by
    ext i
    simp
  ext c
  rw [coeff_polyTrace, h0]
  simp

omit [DecidableEq σ] in
/-- `Φ_1 ∘ Φ_e = Φ_{e+1}`. -/
theorem polyTrace_one_polyTrace (e : ℕ) (f : MvPolynomial σ k) :
    polyTrace p 1 (polyTrace p e f) = polyTrace p (e + 1) f := by
  have hA : 1 ≤ p ^ e := Nat.one_le_iff_ne_zero.2 (pow_ne_zero' p e)
  have hB : 1 ≤ p := hp.out.one_lt.le
  have hAB : 1 ≤ p ^ e * p := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero' p e)
    hp.out.ne_zero)
  ext c
  rw [coeff_polyTrace, coeff_polyTrace, coeff_polyTrace, ← iterateFrobeniusEquiv_symm_add_apply,
    add_comm 1 e]
  congr 2
  ext i
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    topExp_apply, pow_succ, pow_zero, one_mul]
  zify [hA, hB, hAB]
  ring

/-- The iterated trace in the coordinates `x` is the polynomial Frobenius trace `Φ_e`. -/
theorem traceIter_X (e : ℕ) (f : MvPolynomial σ k) :
    (isPBasis_X (σ := σ) (k := k) p).traceIter e f = polyTrace p e f := by
  induction e with
  | zero => rw [IsPBasis.traceIter_zero, polyTrace_zero]
  | succ e ih => rw [IsPBasis.traceIter_succ, ih, trace_X, polyTrace_one_polyTrace]


/-! ### The decomposition over `P^q`, `q = p^e` -/

section QDecomposition

omit [DecidableEq σ] in
theorem exists_box_smul_add_pow (e : ℕ) (b : σ →₀ ℕ) :
    ∃ (c : σ →₀ ℕ) (a : Box σ (p ^ e)), p ^ e • c + a.toFinsupp = b := by
  refine ⟨Finsupp.mapRange (· / p ^ e) (Nat.zero_div _) b, Box.ofNat b, ?_⟩
  ext i
  simp [Box.toFinsupp, Box.ofNat, Nat.div_add_mod]

omit hp [DecidableEq σ] in
theorem box_eq_of_smul_add_eq_pow {q : ℕ} {a a' : Box σ q} {c c' : σ →₀ ℕ}
    (h : q • c + a.toFinsupp = q • c' + a'.toFinsupp) : a = a' := by
  funext i
  have := DFunLike.congr_fun h i
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Box.toFinsupp_apply] at this
  have h1 := congrArg (· % q) this
  simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt (a i).2, Nat.mod_eq_of_lt (a' i).2] at h1
  exact Fin.ext h1

omit [Fintype σ] [DecidableEq σ] in
theorem rootPoly_monomial_self (e : ℕ) (a : σ →₀ ℕ) :
    rootPoly p e a (monomial a (1 : k)) = 1 := by
  have := rootPoly_monomial_smul_add (k := k) p e a 0 1
  rw [smul_zero, zero_add] at this
  rw [this, map_one (iterateFrobeniusEquiv k p e).symm, ← C_apply, C_1]

omit [DecidableEq σ] in
theorem rootPoly_monomial_of_ne_pow (e : ℕ) {a b : Box σ (p ^ e)} (hab : a ≠ b) :
    rootPoly p e a.toFinsupp (monomial b.toFinsupp (1 : k)) = 0 :=
  rootPoly_monomial_of_ne p e _ _ 1 fun c hc =>
    hab (box_eq_of_smul_add_eq_pow (c := c) (c' := 0) (by rw [smul_zero, zero_add]; exact hc))

/-- **The decomposition over `P^q`**, `q = p^e`: `f = ∑_{a ∈ [0,q)^σ} (f_a)^q x^a` with
`f_a = rootPoly p e a f`. -/
theorem sum_rootPoly_pow (e : ℕ) (f : MvPolynomial σ k) :
    ∑ a : Box σ (p ^ e), rootPoly p e a.toFinsupp f ^ p ^ e * mono X a.toNat = f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial b s =>
    obtain ⟨c₀, a₀, rfl⟩ := exists_box_smul_add_pow p e b
    rw [Finset.sum_eq_single a₀]
    · rw [mono_X, show Finsupp.equivFunOnFinite.symm a₀.toNat = a₀.toFinsupp from rfl,
        rootPoly_monomial_smul_add, monomial_pow, monomial_mul, mul_one,
        iterateFrobeniusEquiv_symm_pow']
    · intro a _ hne
      rw [rootPoly_monomial_of_ne, zero_pow (pow_ne_zero' p e), zero_mul]
      intro c hc
      exact hne (box_eq_of_smul_add_eq_pow hc)
    · intro h
      exact absurd (Finset.mem_univ a₀) h
  | add f g hf hg =>
    simp only [map_add, add_pow_char_pow, add_mul, Finset.sum_add_distrib, hf, hg]

/-- **Uniqueness of the decomposition over `P^q`**: the `a`-coefficient of `∑_b (g_b)^q x^b`
is `g_a`. -/
theorem rootPoly_sum_pow (e : ℕ) (g : Box σ (p ^ e) → MvPolynomial σ k) (a : Box σ (p ^ e)) :
    rootPoly p e a.toFinsupp (∑ b : Box σ (p ^ e), g b ^ p ^ e * mono X b.toNat) = g a := by
  classical
  have ha : ∀ i, a.toFinsupp i < p ^ e := fun i => (a i).2
  rw [map_sum, Finset.sum_eq_single a]
  · rw [rootPoly_pow_mul p e ha, mono_X,
      show Finsupp.equivFunOnFinite.symm a.toNat = a.toFinsupp from rfl,
      rootPoly_monomial_self, mul_one]
  · intro b _ hne
    rw [rootPoly_pow_mul p e ha, mono_X,
      show Finsupp.equivFunOnFinite.symm b.toNat = b.toFinsupp from rfl,
      rootPoly_monomial_of_ne_pow p e (Ne.symm hne), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

omit [DecidableEq σ] in
/-- `Φ_e f` is the coefficient of `x^{(q-1,…,q-1)}` in the decomposition of `f` over `P^q`. -/
theorem polyTrace_eq_rootPoly_top (e : ℕ) (f : MvPolynomial σ k) :
    polyTrace p e f = rootPoly p e (Box.top : Box σ (p ^ e)).toFinsupp f := by
  rw [polyTrace]
  congr 2

/-- `Φ_e(P) ⊆ P` together with the decomposition: `f = Φ_e(f)^q x^{q-1} + ∑_{a ≠ top} (f_a)^q x^a`
characterizes `Φ_e(f)` (uniqueness). -/
theorem polyTrace_eq_of_sum_eq (e : ℕ) {f : MvPolynomial σ k}
    {g : Box σ (p ^ e) → MvPolynomial σ k}
    (hg : ∑ b : Box σ (p ^ e), g b ^ p ^ e * mono X b.toNat = f) :
    polyTrace p e f = g Box.top := by
  rw [polyTrace_eq_rootPoly_top, ← hg, rootPoly_sum_pow]

end QDecomposition

/-! ### The fraction field -/

section FractionRing

variable {F : Type*} [Field F] [Algebra (MvPolynomial σ k) F] [IsFractionRing (MvPolynomial σ k) F]
  [CharP F p]

/-- The images of the variables form a `p`-basis of the fraction field `k(x)`. -/
theorem isPBasis_X_fractionRing :
    IsPBasis p (fun i => algebraMap (MvPolynomial σ k) F (X i)) :=
  (isPBasis_X p).map_of_isFractionRing (K := F)

theorem isPBasis_X_fractionRing_coeff (f : MvPolynomial σ k) :
    (isPBasis_X_fractionRing (σ := σ) (k := k) (F := F) p).coeff
      (algebraMap (MvPolynomial σ k) F f) =
      algebraMap (MvPolynomial σ k) F ∘ (isPBasis_X p).coeff f := by
  apply IsPBasis.coeff_eq_of_sum_eq
  have := map_pSum p (algebraMap (MvPolynomial σ k) F) X ((isPBasis_X p).coeff f)
  rw [IsPBasis.pSum_coeff] at this
  rw [this]
  rfl

theorem trace_X_fractionRing (f : MvPolynomial σ k) :
    (isPBasis_X_fractionRing (σ := σ) (k := k) (F := F) p).trace
      (algebraMap (MvPolynomial σ k) F f) =
      algebraMap (MvPolynomial σ k) F ((isPBasis_X p).trace f) := by
  rw [IsPBasis.trace_apply, isPBasis_X_fractionRing_coeff]
  rfl

/-- On `P ⊆ F = k(x)`, the iterated trace `Φ_x^e` of the fraction field is the polynomial trace
`Φ_e`; in particular it maps `P` into `P`. -/
theorem traceIter_X_fractionRing (e : ℕ) (f : MvPolynomial σ k) :
    (isPBasis_X_fractionRing (σ := σ) (k := k) (F := F) p).traceIter e
      (algebraMap (MvPolynomial σ k) F f) =
      algebraMap (MvPolynomial σ k) F (polyTrace p e f) := by
  induction e generalizing f with
  | zero => rw [IsPBasis.traceIter_zero, polyTrace_zero]
  | succ e ih =>
    rw [IsPBasis.traceIter_succ, ih, trace_X_fractionRing, trace_X, polyTrace_one_polyTrace]

end FractionRing

end PBasisX

end EnvelopeProperty.Cartier
