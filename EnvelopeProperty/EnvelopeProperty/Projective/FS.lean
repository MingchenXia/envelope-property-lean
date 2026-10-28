/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Basic

/-!
# Fubini–Study functions on `(ℙⁿ)^an` and rational PL functions

For `X = ℙⁿ` over the trivially valued field `k` and `n ≥ 1`, `Pic(X)_ℚ = ℚ`, the class
`a ∈ ℚ` standing for `O(a)`, and `H⁰(X, O(d))` is the space of forms of degree `d` in
`k[x₀, …, xₙ]`. At `n = 0` the geometric Picard and numerical class groups vanish.
The definitions retain all `n : ℕ`; their scalar parameters at `n = 0` are formal
model parameters, rather than an identification of geometric classes with `ℚ` or `ℝ`.
Following Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field*
(BJ22), `defi:FS`, and Fang–Han–Xia, *The envelope property for unibranch
projective varieties*, §2.2 (`subsec:prelim-psh`, `eq:FS-function`), a **Fubini–Study function**
for `O(a)` is a function `(ℙⁿ)^an → [-∞, ∞)` of the form
`φ = m⁻¹ max_j (log|s_j| + λ_j)` with `m ∈ ℤ_{>0}`, `d = m a ∈ ℕ`, a finite family of forms `s_j`
of degree `d`, not all zero, and constants `λ_j`. On the model `ProjBerk k n` of `(ℙⁿ)^an`
(`EnvelopeProperty.Projective.Basic`), `log|s_j|` is `ProjBerk.logAbs s_j`.

Since `ℙⁿ` is irreducible, "generically finite" (BJ22 `defi:FS`(i)) means finite at `v_triv`,
which is exactly the condition that the `s_j` are not all zero (`ProjBerk.FSData.eval_triv_ne_bot`).

## Main definitions

* `ProjBerk.FSData k n a`: the data `(m, d, (s_j, λ_j)_j)` of an FS function for `O(a)`, with
  `ProjBerk.FSData.eval` the function `m⁻¹ max_j (log|s_j| + λ_j)`; `ProjBerk.FSData.IsRational`:
  all `λ_j ∈ ℚ`.
* `ProjBerk.IsFS a φ`: `φ ∈ H^gf_ℝ(O(a))` (real `λ_j`; BJ22's `𝓗^gf_ℝ(L)`, the class used in
  BJ22 Definition 4.1).
* `ProjBerk.IsRatFS a φ`: `φ ∈ H^gf(O(a))`, rational `λ_j` (FHX's `H^gf(L)`, BJ22's `𝓗^gf_ℚ(L)`).
* `ProjBerk.IsFiniteRatFS a φ`: `φ ∈ H(O(a))`, rational and finite valued everywhere (BJ22's
  `𝓗_ℚ(L)`).
* `ProjBerk.IsRatPL f`: **rational PL functions**, differences `φ - ψ` of finite-valued rational
  FS functions of arbitrary classes (BJ22 §2: PL functions are differences of FS functions); these
  form the `ℚ`-span of `⋃_a H(O(a))`, since FS functions are stable under sums and positive
  rational multiples. They are real valued.

## Main results

* `ProjBerk.FSData.continuous_eval`, `ProjBerk.FSData.eval_ne_top`,
  `ProjBerk.FSData.eval_triv_ne_bot`.
* `ProjBerk.FSData.const` (`eval_const`): constants are FS functions for every class `a ≥ 0`, using
  `max_i log|xᵢ^d| = 0`.
* `ProjBerk.FSData.sup` (`eval_sup`): the maximum of two FS functions of the same class;
  `ProjBerk.FSData.add` (`eval_add`): the sum of FS functions of classes `a`, `b` is an FS function
  of class `a + b`; `ProjBerk.FSData.smul` (`eval_smul`): `c φ` for `c ∈ ℚ_{>0}` has class `c a`.
  The corresponding closure properties of `IsFS`, `IsRatFS`, `IsFiniteRatFS` (BJ22
  `prop:FS`(iii)).
* `ProjBerk.IsRatPL.add`, `ProjBerk.IsRatPL.smul` (rational scalars of any sign),
  `ProjBerk.IsRatPL.neg`, `ProjBerk.IsRatPL.sub`, `ProjBerk.isRatPL_const`,
  `ProjBerk.IsRatPL.continuous`.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

namespace ProjBerk

universe u

/-! ### Auxiliary facts on `EReal` -/

theorem ereal_coe_mul_monotone {c : ℝ} (hc : 0 ≤ c) : Monotone fun x : EReal => (c : EReal) * x :=
  fun _ _ h => mul_le_mul_of_nonneg_left h (by exact_mod_cast hc)

theorem ereal_coe_mul_finset_sup {ι : Type*} {c : ℝ} (hc : 0 < c) (s : Finset ι)
    (f : ι → EReal) : (c : EReal) * s.sup f = s.sup fun i => (c : EReal) * f i :=
  Finset.apply_sup_eq_sup_comp_of_linearOrder _ (ereal_coe_mul_monotone hc.le)
    (EReal.coe_mul_bot_of_pos hc)

theorem ereal_coe_mul_max {c : ℝ} (hc : 0 ≤ c) (x y : EReal) :
    (c : EReal) * max x y = max ((c : EReal) * x) ((c : EReal) * y) :=
  (ereal_coe_mul_monotone hc).map_max

theorem ereal_coe_mul_coe_mul (c d : ℝ) (x : EReal) :
    (c : EReal) * ((d : EReal) * x) = ((c * d : ℝ) : EReal) * x := by
  rw [← mul_assoc, EReal.coe_mul]

theorem ereal_coe_mul_add {c : ℝ} (hc : 0 ≤ c) (x y : EReal) :
    (c : EReal) * (x + y) = (c : EReal) * x + (c : EReal) * y :=
  EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hc) (EReal.coe_ne_top c) x y

theorem ereal_coe_mul_ne_top {c : ℝ} (hc : 0 ≤ c) {x : EReal} (hx : x ≠ ⊤) :
    (c : EReal) * x ≠ ⊤ := by
  rw [Ne, EReal.mul_eq_top]
  have : ¬ (c : EReal) < 0 := not_lt.2 (by exact_mod_cast hc)
  simp [hx, this]

theorem ereal_coe_mul_ne_bot {c : ℝ} (hc : 0 ≤ c) {x : EReal} (hx : x ≠ ⊥) :
    (c : EReal) * x ≠ ⊥ := by
  rw [Ne, EReal.mul_eq_bot]
  have : ¬ (c : EReal) < 0 := not_lt.2 (by exact_mod_cast hc)
  simp [hx, this]

/-- A finite maximum of sums is the sum of the maxima. -/
theorem ereal_finset_sup_product_add {ι κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι → EReal)
    (g : κ → EReal) : (s ×ˢ t).sup (fun p => f p.1 + g p.2) = s.sup f + t.sup g := by
  rw [Finset.sup_product_left]
  have h1 : ∀ i, (t.sup fun j => f i + g j) = f i + t.sup g := fun i =>
    (Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x => f i + x)
      (fun _ _ h => add_le_add_right h _) (EReal.add_bot _)).symm
  simp only [h1]
  exact (Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x => x + t.sup g)
    (fun _ _ h => add_le_add_left h _) (EReal.bot_add _)).symm

theorem continuous_ereal_coe_mul {c : ℝ} (hc : c ≠ 0) :
    Continuous fun x : EReal => (c : EReal) * x := by
  have hc' : (c : EReal) ≠ 0 := by exact_mod_cast hc
  refine continuous_iff_continuousAt.2 fun x => ?_
  exact (EReal.continuousAt_mul (p := ((c : EReal), x)) (Or.inl hc') (Or.inl hc')
    (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))).comp
    (continuous_const.prodMk continuous_id).continuousAt

theorem continuous_ereal_add_coe (c : ℝ) : Continuous fun x : EReal => x + (c : EReal) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  exact ContinuousAt.comp (g := fun p : EReal × EReal => p.1 + p.2)
    (f := fun x : EReal => (x, (c : EReal)))
    (EReal.continuousAt_add (p := (x, (c : EReal))) (Or.inr (EReal.coe_ne_bot c))
      (Or.inr (EReal.coe_ne_top c))) (continuous_id.prodMk continuous_const).continuousAt

variable {k : Type u} [Field k] {n : ℕ}

/-! ### Terms `log|s| + λ` -/

/-- The value `log|s|_v + λ` of a term `t = (s, λ)`. -/
def termVal (t : MvPolynomial (Fin (n + 1)) k × ℝ) (v : ProjBerk k n) : EReal :=
  logAbs t.1 v + (t.2 : EReal)

theorem termVal_def (t : MvPolynomial (Fin (n + 1)) k × ℝ) (v : ProjBerk k n) :
    termVal t v = logAbs t.1 v + (t.2 : EReal) := rfl

@[fun_prop]
theorem continuous_termVal (t : MvPolynomial (Fin (n + 1)) k × ℝ) :
    Continuous (termVal t : ProjBerk k n → EReal) :=
  (continuous_ereal_add_coe t.2).comp (continuous_logAbs t.1)

theorem termVal_ne_top (t : MvPolynomial (Fin (n + 1)) k × ℝ) (v : ProjBerk k n) :
    termVal t v ≠ ⊤ :=
  EReal.add_ne_top (logAbs_ne_top _ _) (EReal.coe_ne_top _)

/-- `log|s^r| + rλ = r (log|s| + λ)`. -/
theorem termVal_pow (t : MvPolynomial (Fin (n + 1)) k × ℝ) (r : ℕ) (v : ProjBerk k n) :
    termVal (t.1 ^ r, (r : ℝ) * t.2) v = ((r : ℝ) : EReal) * termVal t v := by
  rw [termVal_def, termVal_def, ereal_coe_mul_add (Nat.cast_nonneg r), logAbs_pow, EReal.coe_mul]
  rfl

/-- `log|s^p s'^q| + (pλ + qλ') = p (log|s| + λ) + q (log|s'| + λ')`. -/
theorem termVal_mul_pow (t t' : MvPolynomial (Fin (n + 1)) k × ℝ) (p q : ℕ) (v : ProjBerk k n) :
    termVal (t.1 ^ p * t'.1 ^ q, (p : ℝ) * t.2 + (q : ℝ) * t'.2) v =
      ((p : ℝ) : EReal) * termVal t v + ((q : ℝ) : EReal) * termVal t' v := by
  rw [← termVal_pow, ← termVal_pow, termVal_def, termVal_def, termVal_def, logAbs_mul,
    EReal.coe_add, add_add_add_comm]

open Classical in
/-- The family `(s_j^r, r λ_j)_j` representing the same FS function with `m` replaced by `r m`
(BJ22 `equ:FSpower`). -/
def scaleTerms (r : ℕ) (T : Finset (MvPolynomial (Fin (n + 1)) k × ℝ)) :
    Finset (MvPolynomial (Fin (n + 1)) k × ℝ) :=
  T.image fun t => (t.1 ^ r, (r : ℝ) * t.2)

theorem mem_scaleTerms {r : ℕ} {T : Finset (MvPolynomial (Fin (n + 1)) k × ℝ)}
    {t : MvPolynomial (Fin (n + 1)) k × ℝ} :
    t ∈ scaleTerms r T ↔ ∃ t₀ ∈ T, (t₀.1 ^ r, (r : ℝ) * t₀.2) = t := by
  classical
  simp only [scaleTerms, Finset.mem_image]

theorem sup_scaleTerms {r : ℕ} (hr : 0 < r) (T : Finset (MvPolynomial (Fin (n + 1)) k × ℝ))
    (v : ProjBerk k n) :
    (scaleTerms r T).sup (fun t => termVal t v) =
      ((r : ℝ) : EReal) * T.sup fun t => termVal t v := by
  classical
  rw [ereal_coe_mul_finset_sup (by exact_mod_cast hr)]
  simp only [scaleTerms]
  convert Finset.sup_image T (fun t => (t.1 ^ r, (r : ℝ) * t.2)) (fun t => termVal t v) using 1
  exact Finset.sup_congr rfl fun t _ => (termVal_pow t r v).symm

theorem isHomogeneous_scaleTerms {T : Finset (MvPolynomial (Fin (n + 1)) k × ℝ)} {d : ℕ}
    (hT : ∀ t ∈ T, t.1.IsHomogeneous d) (r : ℕ) :
    ∀ t ∈ scaleTerms r T, t.1.IsHomogeneous (d * r) := by
  intro t ht
  obtain ⟨t₀, h₀, rfl⟩ := mem_scaleTerms.1 ht
  exact (hT t₀ h₀).pow r

theorem exists_ne_zero_scaleTerms {T : Finset (MvPolynomial (Fin (n + 1)) k × ℝ)}
    (hT : ∃ t ∈ T, t.1 ≠ 0) (r : ℕ) : ∃ t ∈ scaleTerms r T, t.1 ≠ 0 := by
  obtain ⟨t, ht, hne⟩ := hT
  exact ⟨_, mem_scaleTerms.2 ⟨t, ht, rfl⟩, pow_ne_zero r hne⟩

theorem isRational_scaleTerms {T : Finset (MvPolynomial (Fin (n + 1)) k × ℝ)}
    (hT : ∀ t ∈ T, ∃ q : ℚ, t.2 = q) (r : ℕ) : ∀ t ∈ scaleTerms r T, ∃ q : ℚ, t.2 = q := by
  intro t ht
  obtain ⟨t₀, h₀, rfl⟩ := mem_scaleTerms.1 ht
  obtain ⟨q, hq⟩ := hT t₀ h₀
  exact ⟨r * q, by simp [hq]⟩

/-! ### Fubini–Study data -/

variable (k n) in
/-- The data of a **Fubini–Study function for `O(a)`** on `(ℙⁿ)^an`
(BJ22 `defi:FS`, FHX `eq:FS-function`): an integer `m > 0` with `d = m a ∈ ℕ`, and a finite family
of pairs `(s_j, λ_j)` of forms `s_j` of degree `d`, not all zero, and reals `λ_j`. The function is
`m⁻¹ max_j (log|s_j| + λ_j)` (`FSData.eval`). -/
structure FSData (a : ℚ) where
  /-- The integer `m > 0` such that `m a` is an integer. -/
  m : ℕ
  m_pos : 0 < m
  /-- The degree `d = m a` of the sections. -/
  deg : ℕ
  deg_eq : (deg : ℚ) = m * a
  /-- The finite family of pairs `(s_j, λ_j)`. -/
  terms : Finset (MvPolynomial (Fin (n + 1)) k × ℝ)
  /-- The `s_j` are sections of `O(d)`, i.e. forms of degree `d`. -/
  isHomogeneous : ∀ t ∈ terms, t.1.IsHomogeneous deg
  /-- The `s_j` are not all zero (generic finiteness). -/
  exists_ne_zero : ∃ t ∈ terms, t.1 ≠ 0

namespace FSData

variable {a b : ℚ}

/-- The Fubini–Study function `m⁻¹ max_j (log|s_j| + λ_j)` defined by the data. -/
def eval (D : FSData k n a) (v : ProjBerk k n) : EReal :=
  (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup fun t => logAbs t.1 v + (t.2 : EReal)

/-- The constants `λ_j` are rational (FHX's `H^gf(L)`). -/
def IsRational (D : FSData k n a) : Prop :=
  ∀ t ∈ D.terms, ∃ q : ℚ, t.2 = q

variable (D : FSData k n a)

theorem eval_def (v : ProjBerk k n) :
    D.eval v = (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup fun t => termVal t v := rfl

theorem m_ne_zero : (D.m : ℝ) ≠ 0 := by exact_mod_cast D.m_pos.ne'

theorem inv_m_pos : 0 < (D.m : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast D.m_pos)

theorem a_nonneg (D : FSData k n a) : 0 ≤ a := by
  have h := D.deg_eq
  have hm : (0 : ℚ) < D.m := by exact_mod_cast D.m_pos
  by_contra! ha
  have : (D.m : ℚ) * a < 0 := mul_neg_of_pos_of_neg hm ha
  rw [← h] at this
  exact absurd this (not_lt.2 (Nat.cast_nonneg _))

/-- FS functions are continuous (BJ22 `lem:FSgenfin`). -/
@[fun_prop]
theorem continuous_eval : Continuous D.eval :=
  (continuous_ereal_coe_mul (inv_ne_zero D.m_ne_zero)).comp
    (Continuous.finset_sup_apply fun t _ => continuous_termVal t)

/-- FS functions take values in `[-∞, ∞)`. -/
theorem eval_ne_top (v : ProjBerk k n) : D.eval v ≠ ⊤ := by
  refine ereal_coe_mul_ne_top D.inv_m_pos.le (lt_top_iff_ne_top.1 ?_)
  exact (Finset.sup_lt_iff (bot_lt_top)).2 fun t _ => lt_top_iff_ne_top.2 (termVal_ne_top t v)

theorem termVal_le_eval_mul (v : ProjBerk k n) {t : MvPolynomial (Fin (n + 1)) k × ℝ}
    (ht : t ∈ D.terms) :
    (((D.m : ℝ)⁻¹ : ℝ) : EReal) * termVal t v ≤ D.eval v :=
  ereal_coe_mul_monotone D.inv_m_pos.le (Finset.le_sup (f := fun t => termVal t v) ht)

/-- **Generic finiteness**: an FS function is finite at the trivial valuation, the `s_j` being not
all zero. -/
theorem eval_triv_ne_bot : D.eval triv ≠ ⊥ := by
  obtain ⟨t, ht, hne⟩ := D.exists_ne_zero
  refine ne_bot_of_le_ne_bot ?_ (D.termVal_le_eval_mul triv ht)
  rw [termVal_def, logAbs_triv_of_ne_zero hne, zero_add, ← EReal.coe_mul]
  exact EReal.coe_ne_bot _

/-! #### Constants -/

open Classical in
/-- The constant function `c` as an FS function of class `a ≥ 0`:
`c = m⁻¹ max_i (log|xᵢ^d| + m c)` with `a = d/m` in lowest terms, since `max_i log|xᵢ| = 0`. -/
def const (a : ℚ) (ha : 0 ≤ a) (c : ℝ) : FSData k n a where
  m := a.den
  m_pos := a.den_pos
  deg := a.num.toNat
  deg_eq := by
    have h : ((a.num.toNat : ℕ) : ℚ) = (a.num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 ha)
    rw [h, Rat.den_mul_eq_num]
  terms := Finset.univ.image fun i => (MvPolynomial.X i ^ a.num.toNat, (a.den : ℝ) * c)
  isHomogeneous := by
    intro t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
    exact MvPolynomial.isHomogeneous_X_pow i _
  exists_ne_zero := ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ 0),
    pow_ne_zero _ (MvPolynomial.X_ne_zero 0)⟩

theorem eval_const (a : ℚ) (ha : 0 ≤ a) (c : ℝ) (v : ProjBerk k n) :
    (const a ha c : FSData k n a).eval v = (c : EReal) := by
  classical
  have hsup : ((const a ha c : FSData k n a).terms.sup fun t => termVal t v) =
      (((a.den : ℝ) * c : ℝ) : EReal) := by
    refine le_antisymm (Finset.sup_le fun t ht => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
      rw [termVal_def]
      calc logAbs (MvPolynomial.X i ^ a.num.toNat) v + (((a.den : ℝ) * c : ℝ) : EReal)
          ≤ 0 + (((a.den : ℝ) * c : ℝ) : EReal) := add_le_add_left (logAbs_le_zero _ v) _
        _ = _ := zero_add _
    · obtain ⟨j, hj⟩ := exists_val_X_eq_one v
      refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun t => termVal t v)
        (Finset.mem_image_of_mem (fun i => (MvPolynomial.X i ^ a.num.toNat, (a.den : ℝ) * c))
          (Finset.mem_univ j)))
      simp only [termVal_def]
      rw [logAbs_def, map_pow, hj, one_pow, ENNReal.coe_one, ENNReal.log_one, zero_add]
  rw [eval_def, hsup, ← EReal.coe_mul]
  congr 1
  change ((a.den : ℝ))⁻¹ * ((a.den : ℝ) * c) = c
  have : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  field_simp

theorem isRational_const (a : ℚ) (ha : 0 ≤ a) (c : ℚ) :
    (const a ha (c : ℝ) : FSData k n a).IsRational := by
  classical
  intro t ht
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
  exact ⟨a.den * c, by push_cast; ring⟩

/-! #### Maxima -/

theorem inv_m_mul_m_cancel (D D' : FSData k n a) :
    ((D.m : ℝ) * D'.m)⁻¹ * D'.m = (D.m : ℝ)⁻¹ := by
  field_simp [D.m_ne_zero, D'.m_ne_zero]

open Classical in
/-- The maximum of two FS functions of the same class `a` (BJ22 `prop:FS`): with `m'' = m m'`,
join the families `(s_j^{m'}, m' λ_j)` and `(s'_l^m, m λ'_l)` of forms of degree `d m' = d' m`. -/
def sup (D D' : FSData k n a) : FSData k n a where
  m := D.m * D'.m
  m_pos := Nat.mul_pos D.m_pos D'.m_pos
  deg := D.deg * D'.m
  deg_eq := by push_cast; rw [D.deg_eq]; ring
  terms := scaleTerms D'.m D.terms ∪ scaleTerms D.m D'.terms
  isHomogeneous := by
    intro t ht
    rcases Finset.mem_union.1 ht with h | h
    · exact isHomogeneous_scaleTerms D.isHomogeneous D'.m t h
    · have e : D'.deg * D.m = D.deg * D'.m := by
        have : ((D'.deg * D.m : ℕ) : ℚ) = ((D.deg * D'.m : ℕ) : ℚ) := by
          push_cast; rw [D.deg_eq, D'.deg_eq]; ring
        exact_mod_cast this
      exact e ▸ isHomogeneous_scaleTerms D'.isHomogeneous D.m t h
  exists_ne_zero := by
    obtain ⟨t, ht, hne⟩ := exists_ne_zero_scaleTerms D.exists_ne_zero D'.m
    exact ⟨t, Finset.mem_union_left _ ht, hne⟩

theorem eval_sup (D D' : FSData k n a) (v : ProjBerk k n) :
    (D.sup D').eval v = max (D.eval v) (D'.eval v) := by
  classical
  have hm : (((D.sup D').m : ℕ) : ℝ) = (D.m : ℝ) * D'.m := Nat.cast_mul _ _
  have ht : (D.sup D').terms = scaleTerms D'.m D.terms ∪ scaleTerms D.m D'.terms := rfl
  rw [eval_def, eval_def, eval_def, ht, Finset.sup_union, sup_scaleTerms D'.m_pos,
    sup_scaleTerms D.m_pos, hm, ereal_coe_mul_max (inv_nonneg.2 (by positivity)),
    ereal_coe_mul_coe_mul, ereal_coe_mul_coe_mul, inv_m_mul_m_cancel, mul_comm (D.m : ℝ),
    inv_m_mul_m_cancel]

theorem IsRational.sup {D D' : FSData k n a} (h : D.IsRational) (h' : D'.IsRational) :
    (D.sup D').IsRational := by
  classical
  intro t ht
  rcases Finset.mem_union.1 ht with h1 | h1
  · exact isRational_scaleTerms h _ t h1
  · exact isRational_scaleTerms h' _ t h1

/-! #### Sums -/

open Classical in
/-- The sum of FS functions of classes `a` and `b` is an FS function of class `a + b`
(BJ22 `prop:FS`(iii)): with `m'' = m m'`, take the products `s_j^{m'} s'_l^m` (forms of degree
`d m' + d' m`) with constants `m' λ_j + m λ'_l`. -/
def add {b : ℚ} (D : FSData k n a) (D' : FSData k n b) : FSData k n (a + b) where
  m := D.m * D'.m
  m_pos := Nat.mul_pos D.m_pos D'.m_pos
  deg := D.deg * D'.m + D'.deg * D.m
  deg_eq := by push_cast; rw [D.deg_eq, D'.deg_eq]; ring
  terms := (D.terms ×ˢ D'.terms).image fun p =>
    (p.1.1 ^ D'.m * p.2.1 ^ D.m, (D'.m : ℝ) * p.1.2 + (D.m : ℝ) * p.2.2)
  isHomogeneous := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ht
    rw [Finset.mem_product] at hp
    exact ((D.isHomogeneous _ hp.1).pow _).mul ((D'.isHomogeneous _ hp.2).pow _)
  exists_ne_zero := by
    obtain ⟨t, ht, hne⟩ := D.exists_ne_zero
    obtain ⟨t', ht', hne'⟩ := D'.exists_ne_zero
    have hmem : (t, t') ∈ D.terms ×ˢ D'.terms := Finset.mem_product.2 ⟨ht, ht'⟩
    exact ⟨_, Finset.mem_image_of_mem _ hmem,
      mul_ne_zero (pow_ne_zero _ hne) (pow_ne_zero _ hne')⟩

theorem eval_add {b : ℚ} (D : FSData k n a) (D' : FSData k n b) (v : ProjBerk k n) :
    (D.add D').eval v = D.eval v + D'.eval v := by
  classical
  have hm : (((D.add D').m : ℕ) : ℝ) = (D.m : ℝ) * D'.m := Nat.cast_mul _ _
  have hsup : ((D.add D').terms.sup fun t => termVal t v) =
      ((D'.m : ℝ) : EReal) * (D.terms.sup fun t => termVal t v) +
        ((D.m : ℝ) : EReal) * (D'.terms.sup fun t => termVal t v) := by
    change ((D.terms ×ˢ D'.terms).image fun p =>
      (p.1.1 ^ D'.m * p.2.1 ^ D.m, (D'.m : ℝ) * p.1.2 + (D.m : ℝ) * p.2.2)).sup _ = _
    rw [Finset.sup_image, ereal_coe_mul_finset_sup (by exact_mod_cast D'.m_pos),
      ereal_coe_mul_finset_sup (by exact_mod_cast D.m_pos), ← ereal_finset_sup_product_add]
    exact Finset.sup_congr rfl fun p _ => termVal_mul_pow p.1 p.2 D'.m D.m v
  have h1 : ((D.m : ℝ) * D'.m)⁻¹ * D'.m = (D.m : ℝ)⁻¹ := by
    field_simp [D.m_ne_zero, D'.m_ne_zero]
  have h2 : ((D.m : ℝ) * D'.m)⁻¹ * D.m = (D'.m : ℝ)⁻¹ := by
    field_simp [D.m_ne_zero, D'.m_ne_zero]
  rw [eval_def, eval_def, eval_def, hsup, hm, ereal_coe_mul_add (inv_nonneg.2 (by positivity)),
    ereal_coe_mul_coe_mul, ereal_coe_mul_coe_mul, h1, h2]

theorem IsRational.add {b : ℚ} {D : FSData k n a} {D' : FSData k n b} (h : D.IsRational)
    (h' : D'.IsRational) : (D.add D').IsRational := by
  classical
  intro t ht
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ht
  rw [Finset.mem_product] at hp
  obtain ⟨q, hq⟩ := h _ hp.1
  obtain ⟨q', hq'⟩ := h' _ hp.2
  exact ⟨D'.m * q + D.m * q', by simp [hq, hq']⟩

/-! #### Positive rational multiples -/

/-- A positive rational multiple `c φ` of an FS function of class `a` is an FS function of class
`c a` (BJ22 `prop:FS`(iii)): with `c = p/q` in lowest terms, take `(s_j^p, p λ_j)` and `q m`. -/
def smul (c : ℚ) (hc : 0 < c) (D : FSData k n a) : FSData k n (c * a) where
  m := c.den * D.m
  m_pos := Nat.mul_pos c.den_pos D.m_pos
  deg := D.deg * c.num.toNat
  deg_eq := by
    have h : ((c.num.toNat : ℕ) : ℚ) = (c.num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hc.le)
    rw [Nat.cast_mul, Nat.cast_mul, h, D.deg_eq, ← Rat.den_mul_eq_num]
    ring
  terms := scaleTerms c.num.toNat D.terms
  isHomogeneous := isHomogeneous_scaleTerms D.isHomogeneous _
  exists_ne_zero := exists_ne_zero_scaleTerms D.exists_ne_zero _

theorem eval_smul (c : ℚ) (hc : 0 < c) (D : FSData k n a) (v : ProjBerk k n) :
    (D.smul c hc).eval v = ((c : ℝ) : EReal) * D.eval v := by
  have hp : 0 < c.num.toNat := by have := Rat.num_pos.2 hc; omega
  have hm : (((D.smul c hc).m : ℕ) : ℝ) = (c.den : ℝ) * D.m := Nat.cast_mul _ _
  have ht : (D.smul c hc).terms = scaleTerms c.num.toNat D.terms := rfl
  rw [eval_def, eval_def, hm, ht, sup_scaleTerms hp, ereal_coe_mul_coe_mul, ereal_coe_mul_coe_mul]
  congr 2
  have h : ((c.num.toNat : ℕ) : ℝ) = (c.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hc.le)
  have hd : (c.den : ℝ) ≠ 0 := by exact_mod_cast c.den_ne_zero
  rw [h, Rat.cast_def]
  field_simp [D.m_ne_zero]

theorem IsRational.smul {c : ℚ} (hc : 0 < c) {D : FSData k n a} (h : D.IsRational) :
    (D.smul c hc).IsRational :=
  isRational_scaleTerms h _

end FSData

/-! ### The classes `H^gf_ℝ(O(a))`, `H^gf(O(a))` and `H(O(a))` -/

/-- `φ ∈ H^gf_ℝ(O(a))`: `φ` is a (real, generically finite) **Fubini–Study function for `O(a)`**,
`φ = m⁻¹ max_j (log|s_j| + λ_j)` with `λ_j ∈ ℝ` (BJ22 `defi:FS`(i) with `Λ = ℝ`). -/
def IsFS (a : ℚ) (φ : ProjBerk k n → EReal) : Prop :=
  ∃ D : FSData k n a, φ = D.eval

/-- `φ ∈ H^gf(O(a))`: a **rational** Fubini–Study function for `O(a)`, i.e. with `λ_j ∈ ℚ`
(FHX `eq:FS-function`; BJ22's `𝓗^gf_ℚ(L)`). -/
def IsRatFS (a : ℚ) (φ : ProjBerk k n → EReal) : Prop :=
  ∃ D : FSData k n a, D.IsRational ∧ φ = D.eval

/-- `φ ∈ H(O(a))`: a rational Fubini–Study function that is finite valued on all of `(ℙⁿ)^an`
(BJ22 `defi:FS`(ii), `𝓗_ℚ(L)`). -/
def IsFiniteRatFS (a : ℚ) (φ : ProjBerk k n → EReal) : Prop :=
  IsRatFS a φ ∧ ∀ v, φ v ≠ ⊥

variable {a b : ℚ} {φ ψ : ProjBerk k n → EReal}

theorem IsRatFS.isFS (h : IsRatFS a φ) : IsFS a φ := by
  obtain ⟨D, -, rfl⟩ := h
  exact ⟨D, rfl⟩

theorem IsFiniteRatFS.isRatFS (h : IsFiniteRatFS a φ) : IsRatFS a φ := h.1

theorem IsFiniteRatFS.isFS (h : IsFiniteRatFS a φ) : IsFS a φ := h.1.isFS

theorem IsFiniteRatFS.ne_bot (h : IsFiniteRatFS a φ) (v : ProjBerk k n) : φ v ≠ ⊥ := h.2 v

theorem IsFS.continuous (h : IsFS a φ) : Continuous φ := by
  obtain ⟨D, rfl⟩ := h
  exact D.continuous_eval

theorem IsFS.ne_top (h : IsFS a φ) (v : ProjBerk k n) : φ v ≠ ⊤ := by
  obtain ⟨D, rfl⟩ := h
  exact D.eval_ne_top v

/-- FS functions are finite at the trivial valuation (generic finiteness). -/
theorem IsFS.triv_ne_bot (h : IsFS a φ) : φ triv ≠ ⊥ := by
  obtain ⟨D, rfl⟩ := h
  exact D.eval_triv_ne_bot

/-- Only classes `a ≥ 0` carry FS functions (`O(a)` has no nonzero sections for `a < 0`). -/
theorem IsFS.nonneg (h : IsFS a φ) : 0 ≤ a := by
  obtain ⟨D, rfl⟩ := h
  exact D.a_nonneg

/-- Real constants are FS functions for every class `a ≥ 0`. -/
theorem isFS_const (ha : 0 ≤ a) (c : ℝ) : IsFS (k := k) (n := n) a fun _ => (c : EReal) :=
  ⟨FSData.const a ha c, funext fun v => (FSData.eval_const a ha c v).symm⟩

/-- Rational constants are rational FS functions for every class `a ≥ 0`. -/
theorem isRatFS_const (ha : 0 ≤ a) (c : ℚ) :
    IsRatFS (k := k) (n := n) a fun _ => ((c : ℝ) : EReal) :=
  ⟨FSData.const a ha c, FSData.isRational_const a ha c,
    funext fun v => (FSData.eval_const a ha c v).symm⟩

theorem isFiniteRatFS_const (ha : 0 ≤ a) (c : ℚ) :
    IsFiniteRatFS (k := k) (n := n) a fun _ => ((c : ℝ) : EReal) :=
  ⟨isRatFS_const ha c, fun _ => EReal.coe_ne_bot _⟩

/-- The maximum of two FS functions of the same class is an FS function of that class. -/
theorem IsFS.max (hφ : IsFS a φ) (hψ : IsFS a ψ) : IsFS a fun v => max (φ v) (ψ v) := by
  obtain ⟨D, rfl⟩ := hφ
  obtain ⟨D', rfl⟩ := hψ
  exact ⟨D.sup D', funext fun v => (D.eval_sup D' v).symm⟩

theorem IsRatFS.max (hφ : IsRatFS a φ) (hψ : IsRatFS a ψ) :
    IsRatFS a fun v => max (φ v) (ψ v) := by
  obtain ⟨D, hD, rfl⟩ := hφ
  obtain ⟨D', hD', rfl⟩ := hψ
  exact ⟨D.sup D', hD.sup hD', funext fun v => (D.eval_sup D' v).symm⟩

theorem IsFiniteRatFS.max (hφ : IsFiniteRatFS a φ) (hψ : IsFiniteRatFS a ψ) :
    IsFiniteRatFS a fun v => max (φ v) (ψ v) :=
  ⟨hφ.1.max hψ.1, fun v => ne_bot_of_le_ne_bot (hφ.2 v) (le_max_left _ _)⟩

/-- The sum of FS functions of classes `a`, `b` is an FS function of class `a + b`. -/
theorem IsFS.add (hφ : IsFS a φ) (hψ : IsFS b ψ) : IsFS (a + b) fun v => φ v + ψ v := by
  obtain ⟨D, rfl⟩ := hφ
  obtain ⟨D', rfl⟩ := hψ
  exact ⟨D.add D', funext fun v => (D.eval_add D' v).symm⟩

theorem IsRatFS.add (hφ : IsRatFS a φ) (hψ : IsRatFS b ψ) :
    IsRatFS (a + b) fun v => φ v + ψ v := by
  obtain ⟨D, hD, rfl⟩ := hφ
  obtain ⟨D', hD', rfl⟩ := hψ
  exact ⟨D.add D', hD.add hD', funext fun v => (D.eval_add D' v).symm⟩

theorem IsFiniteRatFS.add (hφ : IsFiniteRatFS a φ) (hψ : IsFiniteRatFS b ψ) :
    IsFiniteRatFS (a + b) fun v => φ v + ψ v :=
  ⟨hφ.1.add hψ.1, fun v => by
    rw [Ne, EReal.add_eq_bot_iff, not_or]
    exact ⟨hφ.2 v, hψ.2 v⟩⟩

/-- A positive rational multiple `c φ` of an FS function of class `a` has class `c a`. -/
theorem IsFS.smul (hφ : IsFS a φ) {c : ℚ} (hc : 0 < c) :
    IsFS (c * a) fun v => ((c : ℝ) : EReal) * φ v := by
  obtain ⟨D, rfl⟩ := hφ
  exact ⟨D.smul c hc, funext fun v => (D.eval_smul c hc v).symm⟩

theorem IsRatFS.smul (hφ : IsRatFS a φ) {c : ℚ} (hc : 0 < c) :
    IsRatFS (c * a) fun v => ((c : ℝ) : EReal) * φ v := by
  obtain ⟨D, hD, rfl⟩ := hφ
  exact ⟨D.smul c hc, hD.smul hc, funext fun v => (D.eval_smul c hc v).symm⟩

theorem IsFiniteRatFS.smul (hφ : IsFiniteRatFS a φ) {c : ℚ} (hc : 0 < c) :
    IsFiniteRatFS (c * a) fun v => ((c : ℝ) : EReal) * φ v :=
  ⟨hφ.1.smul hc, fun v => ereal_coe_mul_ne_bot (by exact_mod_cast hc.le) (hφ.2 v)⟩

/-! ### Rational PL functions -/

/-- **Rational PL functions** on `(ℙⁿ)^an`: differences `φ - ψ` of finite-valued rational FS
functions `φ ∈ H(O(a))`, `ψ ∈ H(O(b))` of arbitrary classes (BJ22 §2: PL functions are differences
of FS functions). They are real valued. -/
def IsRatPL (f : ProjBerk k n → ℝ) : Prop :=
  ∃ (a b : ℚ) (φ ψ : ProjBerk k n → EReal), IsFiniteRatFS a φ ∧ IsFiniteRatFS b ψ ∧
    ∀ v, f v = (φ v).toReal - (ψ v).toReal

theorem IsFiniteRatFS.isRatPL (h : IsFiniteRatFS a φ) : IsRatPL fun v => (φ v).toReal :=
  ⟨a, 0, φ, _, h, isFiniteRatFS_const le_rfl 0, fun v => by simp⟩

/-- Rational constants are rational PL functions. -/
theorem isRatPL_const (c : ℚ) : IsRatPL (k := k) (n := n) fun _ => (c : ℝ) :=
  ⟨0, 0, _, _, isFiniteRatFS_const le_rfl c, isFiniteRatFS_const le_rfl 0, fun v => by simp⟩

theorem IsRatPL.add {f g : ProjBerk k n → ℝ} (hf : IsRatPL f) (hg : IsRatPL g) :
    IsRatPL fun v => f v + g v := by
  obtain ⟨a, b, φ, ψ, hφ, hψ, hf⟩ := hf
  obtain ⟨a', b', φ', ψ', hφ', hψ', hg⟩ := hg
  refine ⟨a + a', b + b', _, _, hφ.add hφ', hψ.add hψ', fun v => ?_⟩
  dsimp only
  rw [hf, hg, EReal.toReal_add (hφ.isFS.ne_top v) (hφ.2 v) (hφ'.isFS.ne_top v) (hφ'.2 v),
    EReal.toReal_add (hψ.isFS.ne_top v) (hψ.2 v) (hψ'.isFS.ne_top v) (hψ'.2 v)]
  ring

theorem IsRatPL.neg {f : ProjBerk k n → ℝ} (hf : IsRatPL f) : IsRatPL fun v => -f v := by
  obtain ⟨a, b, φ, ψ, hφ, hψ, hf⟩ := hf
  exact ⟨b, a, ψ, φ, hψ, hφ, fun v => by dsimp only; rw [hf]; ring⟩

theorem IsRatPL.sub {f g : ProjBerk k n → ℝ} (hf : IsRatPL f) (hg : IsRatPL g) :
    IsRatPL fun v => f v - g v := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem IsRatPL.smul_of_pos {f : ProjBerk k n → ℝ} (hf : IsRatPL f) {c : ℚ} (hc : 0 < c) :
    IsRatPL fun v => (c : ℝ) * f v := by
  obtain ⟨a, b, φ, ψ, hφ, hψ, hf⟩ := hf
  refine ⟨c * a, c * b, _, _, hφ.smul hc, hψ.smul hc, fun v => ?_⟩
  dsimp only
  rw [hf, EReal.toReal_mul, EReal.toReal_mul, EReal.toReal_coe]
  ring

/-- Rational multiples of rational PL functions are rational PL functions. -/
theorem IsRatPL.smul {f : ProjBerk k n → ℝ} (hf : IsRatPL f) (c : ℚ) :
    IsRatPL fun v => (c : ℝ) * f v := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have h := (hf.smul_of_pos (neg_pos.2 hc)).neg
    simpa only [Rat.cast_neg, neg_mul, neg_neg] using h
  · simpa using isRatPL_const (k := k) (n := n) 0
  · exact hf.smul_of_pos hc

/-- Rational PL functions are continuous. -/
theorem IsRatPL.continuous {f : ProjBerk k n → ℝ} (hf : IsRatPL f) : Continuous f := by
  obtain ⟨a, b, φ, ψ, hφ, hψ, hf⟩ := hf
  have hc : ∀ {c : ℚ} {χ : ProjBerk k n → EReal}, IsFiniteRatFS c χ →
      Continuous fun v => (χ v).toReal := fun {c χ} hχ =>
    EReal.continuousOn_toReal.comp_continuous hχ.isFS.continuous fun v => by
      simp [hχ.2 v, hχ.isFS.ne_top v]
  rw [show f = fun v => (φ v).toReal - (ψ v).toReal from funext hf]
  exact (hc hφ).sub (hc hψ)

end ProjBerk

end EnvelopeProperty
