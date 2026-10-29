import EnvelopeProperty.Cartier.Derivation

/-!
# The Jacobian of a change of `p`-basis and the one-step invariance of the Cartier operator

For `p`-bases `y` and `u` of a commutative ring `A` of characteristic `p` we set
`J(y/u) = det (∂y_i/∂u_j)` (`IsPBasis.jac`), so that `dy_1 ∧ ⋯ ∧ dy_m = J(y/u) du_1 ∧ ⋯ ∧ du_m`.
By the chain rule `J(y/u) = J(y/v) J(v/u)` (`IsPBasis.jac_mul`).

The Cartier operator on top forms is `C(f du) = Φ_u(f) du`. Its independence of the `p`-basis is
the identity
`Φ_u(f) = Φ_y(J(y/u)^{p-1} f)`
(equivalently `C(f dy) = C(f J(y/u) du)`). Here we prove it when `u` is obtained from `y` by
exchanging one element (`IsPBasis.trace_update`). The proof only uses the characterization of
`C` by semilinearity, `C(exact) = 0` (`IsPBasis.trace_pderiv`), and the identity
`Φ_y(s^{p-1} ∂s · w) = ∂s · Φ_y(y_i^{p-1} w)` for `∂ = ∂/∂y_i`, `∂w = 0`, which is additive in `s`
because of the integral identity
`(s+r)^{p-1}(∂s+∂r) - s^{p-1}∂s - r^{p-1}∂r = ∂(∑_{0<i<p} (C(p,i)/p) s^i r^{p-i})`
(`derivation_pow_sub_one_add`), and which holds on `s = y_i^n` by direct computation.

The general case (arbitrary pairs of `p`-bases of a field) follows by a Steinitz exchange argument
in `EnvelopeProperty.Cartier.Exchange`. This is the "independence of the trivialization" used in
the proof of FHX Lemma 3.3 (`lem:divisorial-trace-estimate`).
-/

noncomputable section

open scoped NNReal ENNReal Topology

namespace EnvelopeProperty.Cartier

open Finset

section QIdentity

variable {A : Type*} [CommRing A]

/-- The integral identity behind the additivity of `s ↦ s^{p-1} Ds` modulo exact elements:
`(s + r)^{p-1} (Ds + Dr) = s^{p-1} Ds + r^{p-1} Dr + D(∑_{0<i<p} (C(p,i)/p) s^i r^{p-i})`. -/
theorem derivation_pow_sub_one_add (D : Derivation ℤ A A) {p : ℕ} (hp : p.Prime) (s r : A) :
    (s + r) ^ (p - 1) * (D s + D r) = s ^ (p - 1) * D s + r ^ (p - 1) * D r +
      D (∑ i ∈ range (p - 1), ((p.choose (i + 1) / p : ℕ) : A) * (s ^ (i + 1) * r ^ (p - 1 - i))) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_lt.le).symm⟩
  simp only [Nat.add_sub_cancel]
  -- the two binomial identities
  have hc1 : ∀ i ∈ range n, ((n + 1).choose (i + 1) / (n + 1)) * (i + 1) = n.choose i := by
    intro i hi
    rw [mem_range] at hi
    have hdvd : n + 1 ∣ (n + 1).choose (i + 1) :=
      hp.dvd_choose_self (Nat.succ_ne_zero i) (by omega)
    have h := Nat.add_one_mul_choose_eq n i
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.mul_div_cancel_left _ (Nat.succ_pos n)]
    rw [hc, mul_assoc] at h
    exact (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) h).symm
  have hc2 : ∀ i ∈ range n, ((n + 1).choose (i + 1) / (n + 1)) * (n - i) = n.choose (i + 1) := by
    intro i hi
    rw [mem_range] at hi
    have hdvd : n + 1 ∣ (n + 1).choose (i + 1) :=
      hp.dvd_choose_self (Nat.succ_ne_zero i) (by omega)
    have h := Nat.choose_mul_succ_eq n (i + 1)
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.mul_div_cancel_left _ (Nat.succ_pos n)]
    rw [hc, show n + 1 - (i + 1) = n - i by omega, mul_comm (n.choose (i + 1)), mul_assoc] at h
    exact (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) h).symm
  -- expand the derivative of `Q`
  have hDQ : D (∑ i ∈ range n, (((n + 1).choose (i + 1) / (n + 1) : ℕ) : A) *
      (s ^ (i + 1) * r ^ (n - i))) =
      (∑ i ∈ range n, (n.choose i : A) * (s ^ i * r ^ (n - i))) * D s +
      (∑ i ∈ range n, (n.choose (i + 1) : A) * (s ^ (i + 1) * r ^ (n - i - 1))) * D r := by
    rw [map_sum, sum_mul, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    have h1 := hc1 i hi
    have h2 := hc2 i hi
    rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow]
    rw [Derivation.map_natCast]
    simp only [nsmul_eq_mul, smul_eq_mul, Nat.add_sub_cancel]
    rw [← h1, ← h2, Nat.cast_mul, Nat.cast_mul]
    rw [mem_range] at hi
    have : n - i - 1 = n - (i + 1) := by omega
    rw [Nat.cast_add_one, Nat.cast_sub hi.le, this]
    ring
  rw [hDQ]
  -- the binomial expansions of `(s + r)^n`
  have hb1 : (s + r) ^ n = (∑ i ∈ range n, (n.choose i : A) * (s ^ i * r ^ (n - i))) + s ^ n := by
    rw [add_pow, sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, mul_one, Nat.cast_one,
      mul_one]
    congr 1
    refine sum_congr rfl fun i _ => by ring
  have hb2 : (s + r) ^ n =
      (∑ i ∈ range n, (n.choose (i + 1) : A) * (s ^ (i + 1) * r ^ (n - i - 1))) + r ^ n := by
    rw [add_pow, sum_range_succ', Nat.choose_zero_right, Nat.sub_zero, pow_zero, one_mul,
      Nat.cast_one, mul_one]
    congr 1
    refine sum_congr rfl fun i _ => by rw [Nat.sub_sub]; ring
  rw [mul_add]
  nth_rewrite 1 [hb1]
  rw [hb2]
  ring

end QIdentity

variable {A : Type*} [CommRing A] {p : ℕ} [hp : Fact p.Prime] [CharP A p]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

section Mono

omit [DecidableEq σ] in
theorem mono_comp_equiv (y : σ → A) (e : σ ≃ σ) (n : σ → ℕ) :
    mono (y ∘ e) n = mono y (n ∘ e.symm) := by
  unfold mono
  exact Fintype.prod_equiv e _ _ fun i => by simp

omit [CharP A p] hp in
theorem mono_update (y : σ → A) (i : σ) (t : A) (n : σ → ℕ) :
    mono (Function.update y i t) n = t ^ n i * mono y (Function.update n i 0) := by
  unfold mono
  rw [← Finset.mul_prod_erase univ _ (mem_univ i), ← Finset.mul_prod_erase univ _ (mem_univ i)]
  simp only [Function.update_self, pow_zero, one_mul]
  congr 1
  refine prod_congr rfl fun j hj => ?_
  have hji : j ≠ i := ne_of_mem_erase hj
  simp [Function.update_of_ne hji]

end Mono

namespace IsPBasis

variable {y u : σ → A}

/-- The Jacobian `J(y/u) = det (∂y_i/∂u_j)` of a family `y` with respect to a `p`-basis `u`, so
that `dy_1 ∧ ⋯ ∧ dy_m = J(y/u) du_1 ∧ ⋯ ∧ du_m`. -/
def jac (hu : IsPBasis p u) (y : σ → A) : A :=
  (Matrix.of fun i j => hu.pderiv j (y i)).det

theorem jac_self (hy : IsPBasis p y) : hy.jac y = 1 := by
  rw [jac]
  convert Matrix.det_one (n := σ) (R := A)
  ext i j
  rw [Matrix.of_apply, pderiv_self, Matrix.one_apply]
  simp [eq_comm]

/-- The chain rule: `J(y/u) = J(y/v) J(v/u)`. -/
theorem jac_mul {v : σ → A} (hu : IsPBasis p u) (hv : IsPBasis p v) (y : σ → A) :
    hu.jac y = hv.jac y * hu.jac v := by
  rw [jac, jac, jac, ← Matrix.det_mul]
  congr 1
  ext i j
  rw [Matrix.of_apply, Matrix.mul_apply, hv.derivation_apply_eq_sum (hu.pderiv j)]
  refine sum_congr rfl fun k _ => ?_
  simp only [Matrix.of_apply]
  ring

theorem jac_mul_jac (hu : IsPBasis p u) (hy : IsPBasis p y) : hu.jac y * hy.jac u = 1 := by
  rw [mul_comm, ← jac_mul, jac_self]

theorem isUnit_jac (hu : IsPBasis p u) (hy : IsPBasis p y) : IsUnit (hu.jac y) :=
  IsUnit.of_mul_eq_one _ (jac_mul_jac hu hy)

/-- The Jacobian of a one-element exchange `y' = y[i ↦ t]` is `∂y_i/∂t`. -/
theorem jac_update {i : σ} {t : A} (hy' : IsPBasis p (Function.update y i t)) :
    hy'.jac y = hy'.pderiv i (y i) := by
  rw [jac]
  have hrow : ∀ l, l ≠ i → (fun j => hy'.pderiv j (y l)) = (1 : Matrix σ σ A) l := by
    intro l hl
    funext j
    have : y l = Function.update y i t l := (Function.update_of_ne hl t y).symm
    rw [this, pderiv_self, Matrix.one_apply]
    simp [eq_comm]
  have hM : (Matrix.of fun l j => hy'.pderiv j (y l)) =
      (1 : Matrix σ σ A).updateRow i (∑ k, (fun j => hy'.pderiv j (y i)) k • (1 : Matrix σ σ A) k) := by
    ext l j
    by_cases hl : l = i
    · subst hl
      simp only [Matrix.of_apply, Matrix.updateRow_self, Finset.sum_apply, Pi.smul_apply,
        Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
    · rw [Matrix.updateRow_ne hl, Matrix.of_apply]
      exact congr_fun (hrow l hl) j
  rw [hM, Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one]

/-! ### The one-step invariance -/

section OneStep

variable (hy : IsPBasis p y)

/-- The key identity: for `∂ = ∂/∂y_i` and `∂w = 0`,
`Φ_y(s^{p-1} ∂s · w) = ∂s · Φ_y(y_i^{p-1} w)`. -/
theorem trace_pow_sub_one_mul_pderiv (i : σ) {w : A} (hw : hy.pderiv i w = 0) (s : A) :
    hy.trace (s ^ (p - 1) * hy.pderiv i s * w) =
      hy.pderiv i s * hy.trace (y i ^ (p - 1) * w) := by
  set D := hy.pderiv i
  -- `Ψ s = Φ(s^{p-1} Ds w) - Ds Φ(y_i^{p-1} w)` is additive
  let Ψ : A → A := fun s => hy.trace (s ^ (p - 1) * D s * w) - D s * hy.trace (y i ^ (p - 1) * w)
  have hΨadd : ∀ s r, Ψ (s + r) = Ψ s + Ψ r := by
    intro s r
    have hQ := derivation_pow_sub_one_add D hp.out s r
    simp only [Ψ, map_add]
    rw [hQ, add_mul, add_mul, map_add, map_add]
    have : D (∑ i ∈ range (p - 1), ((p.choose (i + 1) / p : ℕ) : A) *
        (s ^ (i + 1) * r ^ (p - 1 - i))) * w = D ((∑ i ∈ range (p - 1),
          ((p.choose (i + 1) / p : ℕ) : A) * (s ^ (i + 1) * r ^ (p - 1 - i))) * w) := by
      rw [Derivation.leibniz, hw, smul_zero, zero_add, smul_eq_mul, mul_comm]
    rw [this, trace_pderiv]
    ring
  have hΨ0 : Ψ 0 = 0 := by
    simp [Ψ]
  -- `Ψ (κ s) = κ Ψ s` when `D κ = 0`
  have hΨmul : ∀ κ s, D κ = 0 → Ψ (κ * s) = κ * Ψ s := by
    intro κ s hκ
    simp only [Ψ]
    rw [Derivation.leibniz, hκ, smul_zero, add_zero, smul_eq_mul]
    have hp1 : p = p - 1 + 1 := (Nat.sub_add_cancel hp.out.one_lt.le).symm
    have hκp : κ ^ p = κ ^ (p - 1) * κ := by rw [← pow_succ, ← hp1]
    rw [show (κ * s) ^ (p - 1) * (κ * D s) * w = κ ^ p * (s ^ (p - 1) * D s * w) by
      rw [hκp, mul_pow]; ring, hy.trace_pow_mul]
    ring
  -- `Ψ (y_i^n) = 0` for `n < p`
  have hΨpow : ∀ n < p, Ψ (y i ^ n) = 0 := by
    intro n hn
    simp only [Ψ]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [D]
    · rw [Derivation.leibniz_pow, pderiv_self, if_pos rfl, nsmul_eq_mul, smul_eq_mul, mul_one]
      have hp1 : p = p - 1 + 1 := (Nat.sub_add_cancel hp.out.one_lt.le).symm
      have hexp : n * (p - 1) + (n - 1) = (n - 1) * p + (p - 1) := by
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, hp1⟩
        rw [hp']
        simp only [Nat.add_sub_cancel]
        ring
      have hrw : (y i ^ n) ^ (p - 1) * ((n : A) * y i ^ (n - 1)) * w =
          ((n : A) * y i ^ (n - 1)) ^ p * (y i ^ (p - 1) * w) := by
        rw [mul_pow, natCast_pow_char, ← pow_mul, ← pow_mul,
          show y i ^ (n * (p - 1)) * ((n : A) * y i ^ (n - 1)) * w =
            (n : A) * (y i ^ (n * (p - 1) + (n - 1)) * w) by rw [pow_add]; ring, hexp, pow_add]
        ring
      rw [hrw, hy.trace_pow_mul]
      ring
  -- decompose `s` along the `p`-basis
  have hΨ : Ψ s = 0 := by
    induction s using hy.induction_on with
    | h0 => exact hΨ0
    | hadd f g hf hg => rw [hΨadd, hf, hg, add_zero]
    | hmono c a =>
      have hsplit : c ^ p * mono y a.toNat =
          (c ^ p * mono y (Function.update a.toNat i 0)) * y i ^ (a i : ℕ) := by
        have h := mono_update y i (y i) a.toNat
        rw [Function.update_eq_self] at h
        rw [h]
        simp only [Box.toNat_apply]
        ring
      have hκ : D (c ^ p * mono y (Function.update a.toNat i 0)) = 0 :=
        hy.pderiv_pow_mul_mono_of_eq_zero i c (by simp)
      rw [hsplit, hΨmul _ _ hκ, hΨpow _ (a i).2, mul_zero]
  simp only [Ψ] at hΨ
  exact sub_eq_zero.1 hΨ

/-- **One-step invariance of the Cartier operator.** If `y` and `y' = y[i ↦ t]` are both
`p`-bases then `Φ_{y'}(g) = Φ_y(J(y/y')^{p-1} g)`, where `J(y/y') = ∂y_i/∂t`. -/
theorem trace_update {i : σ} {t : A} (hy' : IsPBasis p (Function.update y i t)) (g : A) :
    hy'.trace g = hy.trace (hy'.jac y ^ (p - 1) * g) := by
  set y' := Function.update y i t with hy'def
  set h := hy'.jac y with hhdef
  have hh : h = hy'.pderiv i (y i) := jac_update hy'
  set D := hy.pderiv i
  -- `∂/∂t = h ∂/∂y_i`
  have hD' : hy'.pderiv i = h • D := by
    refine hy.derivation_ext fun j => ?_
    rw [Derivation.smul_apply, smul_eq_mul]
    by_cases hj : j = i
    · subst hj
      simp [D, pderiv_self, hh]
    · have : y j = y' j := (Function.update_of_ne hj t y).symm
      rw [this, pderiv_self, if_neg (Ne.symm hj), ← this]
      simp [D, pderiv_self, if_neg (Ne.symm hj)]
  -- `h ∂t/∂y_i = 1`
  have hhD : h * D t = 1 := by
    have h1 : hy'.pderiv i (y' i) = 1 := by rw [pderiv_self, if_pos rfl]
    rw [hD', Derivation.smul_apply, smul_eq_mul] at h1
    rwa [show y' i = t from Function.update_self i t y] at h1
  have hp1 : p = p - 1 + 1 := (Nat.sub_add_cancel hp.out.one_lt.le).symm
  have hhp : h ^ (p - 1) = h ^ p * D t := by
    conv_rhs => rw [hp1, pow_succ, mul_assoc, hhD, mul_one]
  -- reduce to basis monomials of `y'`
  induction g using hy'.induction_on with
  | h0 => simp
  | hadd f g hf hg => rw [map_add, hf, hg, mul_add, map_add]
  | hmono c a =>
    rw [hy'.trace_pow_mul, mul_left_comm, hy.trace_pow_mul]
    congr 1
    -- `y'^a = t^{a_i} w` with `∂w = 0`
    set w := mono y (Function.update a.toNat i 0) with hwdef
    have hw : D w = 0 := by
      have := hy.pderiv_pow_mul_mono_of_eq_zero i 1 (n := Function.update a.toNat i 0) (by simp)
      simpa using this
    have hmono' : mono y' a.toNat = t ^ (a i : ℕ) * w := mono_update y i t a.toNat
    conv_rhs => rw [hmono', hhp]
    rw [show h ^ p * D t * (t ^ (a i : ℕ) * w) = h ^ p * (D t * t ^ (a i : ℕ) * w) by ring,
      hy.trace_pow_mul]
    by_cases ha : (a i : ℕ) = p - 1
    · -- the top case
      have key := trace_pow_sub_one_mul_pderiv hy i hw t
      rw [ha, show D t * t ^ (p - 1) * w = t ^ (p - 1) * D t * w by ring, key, ← mul_assoc, hhD,
        one_mul]
      have hmonoy : mono y a.toNat = y i ^ (p - 1) * w := by
        have h := mono_update y i (y i) a.toNat
        rw [Function.update_eq_self] at h
        rw [h, hwdef]
        simp [ha]
      rw [← hmonoy]
      -- both sides are `δ_{a, top}`
      by_cases htop : a = Box.top
      · subst htop
        rw [hy.trace_mono_top]
        exact hy'.trace_mono_top
      · have h1 := hy.trace_pow_mul_mono_of_ne htop 1
        have h2 := hy'.trace_pow_mul_mono_of_ne htop 1
        simp only [one_pow, one_mul] at h1 h2
        rw [h1, h2]
    · -- the non-top case: `D t t^{b} w = D(t^{b+1} w)/(b+1)` is exact
      have hb : (a i : ℕ) + 1 < p := by have := (a i).2; omega
      have hunit : IsUnit (((a i : ℕ) + 1 : ℕ) : A) :=
        isUnit_natCast_of_not_dvd (fun hd => by
          have := Nat.le_of_dvd (Nat.succ_pos _) hd
          omega)
      have hexact : (((a i : ℕ) + 1 : ℕ) : A) * (D t * t ^ (a i : ℕ) * w) =
          D (t ^ ((a i : ℕ) + 1) * w) := by
        rw [Derivation.leibniz, hw, smul_zero, zero_add, Derivation.leibniz_pow, smul_eq_mul,
          nsmul_eq_mul, smul_eq_mul, Nat.add_sub_cancel]
        ring
      have h0 : hy.trace (D t * t ^ (a i : ℕ) * w) = 0 := by
        have := congrArg hy.trace hexact
        rw [trace_pderiv, ← natCast_pow_char (A := A) ((a i : ℕ) + 1), hy.trace_pow_mul] at this
        exact (hunit.mul_right_eq_zero).1 this
      rw [h0, mul_zero]
      have htop : a ≠ Box.top := by
        intro h
        apply ha
        rw [h]
        rfl
      have h2 := hy'.trace_pow_mul_mono_of_ne htop 1
      simp only [one_pow, one_mul] at h2
      exact h2

end OneStep

end IsPBasis

end EnvelopeProperty.Cartier
