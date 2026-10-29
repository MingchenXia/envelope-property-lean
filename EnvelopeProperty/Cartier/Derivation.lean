import EnvelopeProperty.Cartier.PBasis

/-!
# The partial derivatives attached to a `p`-basis

Let `y` be a `p`-basis of a commutative ring `A` of characteristic `p`. The partial derivative
`∂_i = ∂/∂y_i` is the additive map
`∂_i (∑_a (f_a)^p y^a) = ∑_a (f_a)^p a_i y^{a - e_i}`.
It is a derivation (`IsPBasis.pderiv`) with `∂_i y_j = δ_{ij}`, it kills `p`-th powers, and every
derivation `D` of `A` is `∑_i D(y_i) ∂_i` (`IsPBasis.derivation_eq_sum`). The Frobenius trace kills
the image of each `∂_i` (`IsPBasis.trace_pderiv`): this is the vanishing of the Cartier operator on
exact top forms.

These are used to define the Jacobian of a change of `p`-basis and to prove that the Cartier
operator on top forms does not depend on the `p`-basis (groundwork for FHX Lemma 3.3,
`lem:divisorial-trace-estimate`).
-/

noncomputable section

open scoped NNReal ENNReal Topology

namespace EnvelopeProperty.Cartier

open Finset

variable {A : Type*} [CommRing A] {p : ℕ} [hp : Fact p.Prime] [CharP A p]

include hp in
/-- In characteristic `p`, natural numbers are fixed by Frobenius. -/
theorem natCast_pow_char (n : ℕ) : (n : A) ^ p = n := by
  induction n with
  | zero => simp [zero_pow hp.out.ne_zero]
  | succ n ih => rw [Nat.cast_succ, add_pow_char, ih, one_pow]

include hp in
/-- In characteristic `p`, a natural number prime to `p` is a unit. -/
theorem isUnit_natCast_of_not_dvd {n : ℕ} (hn : ¬ p ∣ n) : IsUnit (n : A) := by
  have hz : (n : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hu : IsUnit (n : ZMod p) := hz.isUnit
  have := hu.map (ZMod.castHom (dvd_refl p) A)
  simpa using this

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

section MonoArith

/-- Exponent of `y^{n - e_i}`. -/
def lowerExp (n : σ → ℕ) (i : σ) : σ → ℕ :=
  n - Pi.single i 1

omit [Fintype σ] in
@[simp]
theorem lowerExp_apply_self (n : σ → ℕ) (i : σ) : lowerExp n i i = n i - 1 := by
  simp [lowerExp]

omit [Fintype σ] in
theorem lowerExp_apply_of_ne (n : σ → ℕ) {i j : σ} (h : j ≠ i) : lowerExp n i j = n j := by
  simp [lowerExp, h]

omit [Fintype σ] in
theorem add_lowerExp {m n : σ → ℕ} {i : σ} (hn : 1 ≤ n i) : m + lowerExp n i = lowerExp (m + n) i := by
  funext j
  by_cases h : j = i
  · subst h
    simp only [Pi.add_apply, lowerExp_apply_self]
    omega
  · simp [lowerExp_apply_of_ne _ h]

/-- The Leibniz rule for monomials: `(m_i + n_i) y^{m+n-e_i} = n_i y^m y^{n-e_i} + m_i y^n y^{m-e_i}`. -/
theorem mono_leibniz (y : σ → A) (m n : σ → ℕ) (i : σ) :
    ((m i + n i : ℕ) : A) * mono y (lowerExp (m + n) i) =
      (n i : A) * (mono y m * mono y (lowerExp n i)) +
        (m i : A) * (mono y n * mono y (lowerExp m i)) := by
  rcases Nat.eq_zero_or_pos (n i) with hn | hn <;> rcases Nat.eq_zero_or_pos (m i) with hm | hm
  · simp [hn, hm]
  · rw [hn, Nat.cast_zero, zero_mul, zero_add, add_zero, ← mono_add, add_lowerExp hm,
      add_comm n m]
  · rw [hm, Nat.cast_zero, zero_mul, add_zero, zero_add, ← mono_add, add_lowerExp hn]
  · rw [← mono_add, ← mono_add, add_lowerExp hn, add_lowerExp hm, add_comm n m, Nat.cast_add]
    ring

end MonoArith

/-- Arithmetic of `y^n = (y^{⌊n/p⌋})^p y^{n mod p}` for `n - e_i`. -/
theorem mono_lowerExp_eq (y : σ → A) (p : ℕ) [NeZero p] (n : σ → ℕ) (i : σ) (h : n i % p ≠ 0) :
    mono y (fun j => n j / p) ^ p * mono y (lowerExp (Box.ofNat (p := p) n).toNat i) =
      mono y (lowerExp n i) := by
  rw [← mono_smul, ← mono_add]
  congr 1
  funext j
  have hp0 : 0 < p := NeZero.pos p
  by_cases hj : j = i
  · subst hj
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lowerExp_apply_self, Box.toNat_ofNat]
    have := Nat.div_add_mod (n j) p
    omega
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lowerExp_apply_of_ne _ hj,
      Box.toNat_ofNat]
    exact Nat.div_add_mod (n j) p

variable {y : σ → A} (hy : IsPBasis p y)

namespace IsPBasis

/-- The coefficient extraction applied to an arbitrary monomial times a `p`-th power. -/
theorem coeff_pow_mul_mono_nat (g : A) (n : σ → ℕ) :
    hy.coeff (g ^ p * mono y n) =
      Pi.single (Box.ofNat (p := p) n) (g * mono y fun i => n i / p) := by
  rw [hy.coeff_pow_mul, hy.coeff_mono_nat]
  funext a
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> simp

theorem trace_pow_mul_mono_nat (g : A) (n : σ → ℕ) :
    hy.trace (g ^ p * mono y n) =
      if Box.ofNat (p := p) n = Box.top then g * mono y (fun i => n i / p) else 0 := by
  rw [trace_apply, coeff_pow_mul_mono_nat, Pi.single_apply]
  by_cases h : Box.ofNat (p := p) n = Box.top
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

/-- The function underlying `∂_i`. -/
def pderivFun (i : σ) (f : A) : A :=
  ∑ a : Box σ p, hy.coeff f a ^ p * ((a i : ℕ) : A) * mono y (lowerExp a.toNat i)

theorem pderivFun_add (i : σ) (f g : A) :
    hy.pderivFun i (f + g) = hy.pderivFun i f + hy.pderivFun i g := by
  simp [pderivFun, add_pow_char, add_mul, sum_add_distrib]

theorem pderivFun_pow_mul_mono (i : σ) (g : A) (n : σ → ℕ) :
    hy.pderivFun i (g ^ p * mono y n) = g ^ p * ((n i : ℕ) : A) * mono y (lowerExp n i) := by
  rw [pderivFun, coeff_pow_mul_mono_nat, sum_eq_single (Box.ofNat (p := p) n)]
  · rw [Pi.single_eq_same]
    have hcast : (((Box.ofNat (p := p) n) i : ℕ) : A) = ((n i : ℕ) : A) := by
      rw [show ((Box.ofNat (p := p) n i : ℕ)) = n i % p from rfl, ← CharP.cast_eq_mod]
    rw [hcast]
    by_cases h : n i % p = 0
    · rw [(CharP.cast_eq_zero_iff A p (n i)).2 (Nat.dvd_of_mod_eq_zero h)]
      simp
    · rw [mul_pow, ← mono_lowerExp_eq y p n i h]
      ring
  · intro b _ hb
    simp [hb, zero_pow hp.out.ne_zero]
  · simp

theorem pderivFun_mono (i : σ) (n : σ → ℕ) :
    hy.pderivFun i (mono y n) = ((n i : ℕ) : A) * mono y (lowerExp n i) := by
  simpa using hy.pderivFun_pow_mul_mono i 1 n

theorem pderivFun_pow_mul (i : σ) (g f : A) :
    hy.pderivFun i (g ^ p * f) = g ^ p * hy.pderivFun i f := by
  simp [pderivFun, hy.coeff_pow_mul, mul_pow, mul_sum, mul_assoc]

theorem pderivFun_zero (i : σ) : hy.pderivFun i 0 = 0 := by
  simpa using hy.pderivFun_add i 0 0

include hy in
/-- Induction along the decomposition `f = ∑_a (f_a)^p y^a`. -/
theorem induction_on {Q : A → Prop} (h0 : Q 0) (hadd : ∀ f g, Q f → Q g → Q (f + g))
    (hmono : ∀ (c : A) (a : Box σ p), Q (c ^ p * mono y a.toNat)) (f : A) : Q f := by
  rw [← hy.sum_coeff f]
  exact Finset.sum_induction _ Q hadd h0 fun a _ => hmono _ a

theorem pderivFun_mul (i : σ) (f g : A) :
    hy.pderivFun i (f * g) = f * hy.pderivFun i g + g * hy.pderivFun i f := by
  have key : ∀ (c d : A) (m n : σ → ℕ),
      hy.pderivFun i ((c ^ p * mono y m) * (d ^ p * mono y n)) =
        (c ^ p * mono y m) * hy.pderivFun i (d ^ p * mono y n) +
          (d ^ p * mono y n) * hy.pderivFun i (c ^ p * mono y m) := by
    intro c d m n
    rw [show (c ^ p * mono y m) * (d ^ p * mono y n) = (c * d) ^ p * mono y (m + n) by
      rw [mono_add, mul_pow]; ring]
    rw [pderivFun_pow_mul_mono, pderivFun_pow_mul_mono, pderivFun_pow_mul_mono, Pi.add_apply,
      mul_assoc, mono_leibniz y m n i, mul_pow]
    ring
  induction f using hy.induction_on generalizing g with
  | h0 => simp [pderivFun_zero]
  | hadd f₁ f₂ h₁ h₂ => rw [add_mul, pderivFun_add, h₁, h₂, pderivFun_add]; ring
  | hmono c a =>
    induction g using hy.induction_on with
    | h0 => simp [pderivFun_zero]
    | hadd g₁ g₂ h₁ h₂ => rw [mul_add, pderivFun_add, h₁, h₂, pderivFun_add]; ring
    | hmono d b => exact key c d a.toNat b.toNat

/-- `∂_i` as an additive map. -/
def pderivHom (i : σ) : A →+ A where
  toFun := hy.pderivFun i
  map_zero' := hy.pderivFun_zero i
  map_add' := hy.pderivFun_add i

/-- The partial derivative `∂_i = ∂/∂y_i` attached to the `p`-basis `y`, as a derivation. -/
def pderiv (i : σ) : Derivation ℤ A A :=
  Derivation.mk' (hy.pderivHom i).toIntLinearMap fun f g => by
    simp only [AddMonoidHom.coe_toIntLinearMap, smul_eq_mul]
    exact hy.pderivFun_mul i f g

theorem pderiv_apply (i : σ) (f : A) : hy.pderiv i f = hy.pderivFun i f :=
  rfl

theorem pderiv_pow_mul_mono (i : σ) (g : A) (n : σ → ℕ) :
    hy.pderiv i (g ^ p * mono y n) = g ^ p * ((n i : ℕ) : A) * mono y (lowerExp n i) :=
  hy.pderivFun_pow_mul_mono i g n

theorem pderiv_mono (i : σ) (n : σ → ℕ) :
    hy.pderiv i (mono y n) = ((n i : ℕ) : A) * mono y (lowerExp n i) :=
  hy.pderivFun_mono i n

theorem pderiv_pow_mul (i : σ) (g f : A) : hy.pderiv i (g ^ p * f) = g ^ p * hy.pderiv i f :=
  hy.pderivFun_pow_mul i g f

theorem pderiv_pow (i : σ) (g : A) : hy.pderiv i (g ^ p) = 0 := by
  rw [← mul_one (g ^ p), hy.pderiv_pow_mul, Derivation.map_one_eq_zero, mul_zero]

/-- `∂_i y_j = δ_{ij}`. -/
theorem pderiv_self (i j : σ) : hy.pderiv i (y j) = if i = j then 1 else 0 := by
  have h := hy.pderiv_mono i (Pi.single j 1)
  rw [mono_single, pow_one] at h
  rw [h]
  by_cases hij : i = j
  · subst hij
    have : lowerExp (Pi.single i 1 : σ → ℕ) i = 0 := by
      funext l
      by_cases hl : l = i
      · subst hl; simp
      · simp [lowerExp_apply_of_ne _ hl, hl]
    simp [this]
  · simp [hij]

omit hp in
/-- Any derivation kills `p`-th powers in characteristic `p`. -/
theorem _root_.EnvelopeProperty.Cartier.derivation_pow_char (D : Derivation ℤ A A) (g : A) :
    D (g ^ p) = 0 := by
  rw [Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

include hy in
/-- A derivation vanishing on the `p`-basis vanishes. -/
theorem derivation_eq_zero_of_apply_eq_zero (D : Derivation ℤ A A) (h : ∀ i, D (y i) = 0) :
    D = 0 := by
  ext f
  have hmono : ∀ n : σ → ℕ, D (mono y n) = 0 := by
    intro n
    unfold mono
    induction (univ : Finset σ) using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [prod_insert hi, Derivation.leibniz, ih, Derivation.leibniz_pow, h i]
      simp
  rw [← hy.sum_coeff f, map_sum]
  refine sum_eq_zero fun a _ => ?_
  rw [Derivation.leibniz, hmono, derivation_pow_char]
  simp

include hy in
/-- Two derivations agreeing on a `p`-basis agree. -/
theorem derivation_ext {D D' : Derivation ℤ A A} (h : ∀ i, D (y i) = D' (y i)) : D = D' := by
  have := hy.derivation_eq_zero_of_apply_eq_zero (D - D') (fun i => by simp [h i])
  exact sub_eq_zero.1 this

omit [CharP A p] in
theorem _root_.EnvelopeProperty.Cartier.derivation_sum_apply {ι : Type*} (s : Finset ι)
    (D : ι → Derivation ℤ A A) (f : A) : (∑ i ∈ s, D i) f = ∑ i ∈ s, D i f := by
  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl

/-- Every derivation is `∑_i D(y_i) ∂_i`. -/
theorem derivation_eq_sum (D : Derivation ℤ A A) : D = ∑ i, D (y i) • hy.pderiv i := by
  refine hy.derivation_ext fun j => ?_
  rw [derivation_sum_apply]
  simp only [Derivation.smul_apply, pderiv_self, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq']
  simp

theorem derivation_apply_eq_sum (D : Derivation ℤ A A) (f : A) :
    D f = ∑ i, D (y i) * hy.pderiv i f := by
  conv_lhs => rw [hy.derivation_eq_sum D]
  rw [derivation_sum_apply]
  rfl

/-- The trace kills the image of `∂_i` (the Cartier operator kills exact top forms). -/
theorem trace_pderiv (i : σ) (f : A) : hy.trace (hy.pderiv i f) = 0 := by
  rw [pderiv_apply, pderivFun, map_sum]
  refine sum_eq_zero fun a _ => ?_
  rw [show hy.coeff f a ^ p * ((a i : ℕ) : A) = (hy.coeff f a * ((a i : ℕ) : A)) ^ p by
    rw [mul_pow, natCast_pow_char], trace_pow_mul_mono_nat]
  rcases Nat.eq_zero_or_pos (a i : ℕ) with h0 | hpos
  · simp [h0]
  · rw [if_neg]
    intro h
    have := congr_fun h i
    simp only [Box.ofNat, Box.top, Fin.mk.injEq, lowerExp_apply_self, Box.toNat_apply] at this
    have hlt := (a i).2
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega

/-- `∂_i` kills the monomials not involving `y_i`. -/
theorem pderiv_pow_mul_mono_of_eq_zero (i : σ) (g : A) {n : σ → ℕ} (hn : n i = 0) :
    hy.pderiv i (g ^ p * mono y n) = 0 := by
  rw [pderiv_pow_mul_mono, hn]
  simp

end IsPBasis

end EnvelopeProperty.Cartier
