/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.BlowupModel
import EnvelopeProperty.Projective.SubvarietyPSH

/-!
# Fubini–Study and psh functions on the blowup `X'`

Let `X = V(I) ⊆ ℙ^M` be a projective subvariety over a trivially valued field `k`, and
`B : X.BlowupCenter M'` forms `G₀, …, G_{M'}` of one degree `d`, not all in `I`. The blowup
`X' ⊆ ℙ^M × ℙ^{M'}` of `X` along `(Ḡ₀, …, Ḡ_{M'})` is modelled by
`X'^an = B.an ⊆ (ℙ^M × ℙ^{M'})^an = BiProjBerk k M M'`, the bigraded normalized seminorms on
`R_{M,M'} = k[x₀, …, x_M, y₀, …, y_{M'}]` vanishing on the bihomogeneous prime `I' = B.ideal`,
with trivial point `⋆' = B.triv` and blowup map `μ = B.proj : X'^an → X^an`
(`EnvelopeProperty.Projective.BlowupModel`).

This file makes `(X'^an, ⋆')` a **Fubini–Study system of rank two**
(`EnvelopeProperty.FSSystem`) and so defines the `θ`-psh functions on `X'^an` for `θ ∈ ℝ²`,
following the blueprint chapter `projective-general.tex` (nodes `def:pg-blowup-fs`,
`lem:pg-blowup-fs-system`, `def:pg-blowup-psh`), which supplies the psh theory on modifications
used in the descent step of Fang–Han–Xia, *The envelope property for unibranch projective
varieties* (FHX), Corollary 5.26 (`cor:normal-weak-global`). The definitions follow
Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field* (BJ22),
`defi:FS`, FS, FSgenfin and `defi:psh`. The class `(a, b) ∈ ℚ²` stands for
`a μ^*O(1) + b O(0, 1)`; in particular `PSH(X', μ^*O(a)) = PSH(X', (a, 0))`
(`rmk:pg-blowup-psh-comparison`: `μ^*O(1)` is not ample, so the approximating classes
`(a + δ, δ)` need the second grading).

## Bigraded Fubini–Study data on `(ℙ^M × ℙ^{M'})^an`

`BiProjBerk.FSData k M M' a b` (for `a, b ∈ ℚ`) is the data of a bigraded Fubini–Study function
`m⁻¹ max_t (log|F_t| + λ_t)`: an integer `m > 0` with `m a, m b ∈ ℕ`, and finitely many pairs
`(F_t, λ_t)` of bihomogeneous `F_t ∈ R_{M,M'}` of bidegree `(m a, m b)` and `λ_t ∈ ℝ`
(`BiProjBerk.FSData.eval`). It is the bigraded analogue of `ProjBerk.FSData`
(`EnvelopeProperty.Projective.FS`), with the same operations, proved in the same way:

* `BiProjBerk.FSData.const` (`eval_const`): real constants of every class `(a, b) ≥ 0`, as
  `m⁻¹ max_{j,l} (log|x_j^{m a} y_l^{m b}| + m c)`, using the two normalizations
  `max_j |x_j| = 1 = max_l |y_l|`;
* `BiProjBerk.FSData.sup`, `add`, `smul` (`eval_sup`, `eval_add`, `eval_smul`): maxima of data of
  the same class (after passing to a common `m`), sums (products of the families), positive
  rational multiples (powers);
* `BiProjBerk.FSData.reweight` and `BiProjBerk.FSData.exists_antitone_isRational`: every FS
  function is the decreasing limit of the real-valued rational FS functions
  `max(m⁻¹ max_t (log|F_t| + q_t^{(N)}), -N)`, with rationals `q_t^{(N)} ↓ λ_t`
  (BJ22 FSgenfin, as `ProjBerk.IsFS.exists_antitone_finiteRatFS`);
* `BiProjBerk.FSData.comapFst`: an FS datum of class `a` on `ℙ^M` gives one of class `(a, 0)`,
  with `eval ∘ fst`; `BiProjBerk.FSData.single`: the single term `log|F| + λ`.

## Fubini–Study functions on `X'^an` (`def:pg-blowup-fs`)

* `ProjSubvariety.BlowupCenter.IsFS B a b f` (`𝓗(X', (a, b))`): `f = m⁻¹ max_t (log|F_t| + λ_t)`
  on `X'^an` for bigraded FS data of class `(a, b)` at least one of whose `F_t` is not in `I'`.
* `ProjSubvariety.BlowupCenter.IsFinFS B a b f` (`𝓗_fin(X', (a, b))`): moreover all `λ_t ∈ ℚ`,
  and at every point of `X'^an` some `|F_t| ≠ 0`.

## Main results

* `ProjSubvariety.BlowupCenter.fsSystem B : FSSystem B.an 2` is the proof of
  `lem:pg-blowup-fs-system`, with `𝓗(a) = 𝓗(X', (a 0, a 1))` for `a ∈ ℚ²`. The axioms are
  `IsFS.le_apply_triv` (FS1: `|F| ≤ 1` on `X'^an`, `|F|_{⋆'} = 1` for `F ∉ I'`, `|F| = 0` on
  `X'^an` for `F ∈ I'`), `IsFS.mono_class` (FS2: add the constant `0` of class
  `(a' - a, b' - b)`), `isFS_const`, `IsFS.max` (FS3), `IsFS.add`, `IsFS.smul` (FS4),
  `IsFS.exists_antitone_isFinFS` (FS5) and their `IsFinFS` analogues. As in
  `EnvelopeProperty.Projective.SubvarietyPSH`, "some `F_t ∉ I'`" and "no common zero on `X'^an`"
  are handled as finiteness of the FS function at `⋆'`, resp. on `X'^an`
  (`exists_notMem_iff_eval_triv_ne_bot`, `forall_exists_val_ne_zero_iff`), so that the closure
  properties follow from the formulas for the data.
* `ProjSubvariety.BlowupCenter.IsPSH B θ u` (`def:pg-blowup-psh`, `PSH(X', θ)` for `θ ∈ ℝ²`): the
  `θ`-psh functions of `B.fsSystem`; `PSH(X', μ^*O(a))` is `B.IsPSH ![a, 0]`.
* `isFS_logAbs`, `isPSH_logAbs`: `log|F| ∈ 𝓗(X', (p, q)) ⊆ PSH(X', (p, q))` for `F ∉ I'`
  bihomogeneous of bidegree `(p, q)`.
* `IsFS.comp_proj`, `IsFinFS.comp_proj`, `IsPSH.comp_proj`: pullback along `μ`,
  `μ^* 𝓗(X, a) ⊆ 𝓗(X', (a, 0))` and `μ^* PSH(X, θ) ⊆ PSH(X', (θ, 0))` (BJ22 PSH(iii) for
  `μ`; not needed for FHX 5.26, which is the converse).
* Rank-two forms of the psh API of `EnvelopeProperty.Projective.FSSystem` and
  `EnvelopeProperty.Projective.FSSystemRegularization`: `IsFS.isPSH`, `IsPSH.nonneg`,
  `IsPSH.le_apply_triv`, `IsPSH.add`, `IsPSH.smul`, `IsPSH.max`, `IsPSH.add_const`,
  `isPSH_const`, `IsPSH.mono_class`, `isPSH_of_antitone_seq` (PSH2), and, for countable `k`,
  `IsPSH.exists_isFinFS_seq_of_pos` (fixed class `(a, b)`, `a, b > 0`) and
  `IsPSH.exists_isFinFS_seq_dyadic` (classes `(a + 2^{-k}, b + 2^{-k})`).
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

/-- `ℚ² → ℝ²`, coordinatewise cast of `![a, b]`. -/
theorem ratCast_vecCons_two (a b : ℚ) :
    (fun c => (((![a, b] : Fin 2 → ℚ) c : ℚ) : ℝ)) = ![(a : ℝ), (b : ℝ)] := by
  funext c
  fin_cases c <;> rfl

namespace BiProjBerk

variable {k : Type u} [Field k] {M M' : ℕ}

/-! ### Terms `log|F| + λ` -/

/-- The value `log|F|_v + λ` of a term `t = (F, λ)` at `v ∈ (ℙ^M × ℙ^{M'})^an`. -/
def termVal (t : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ) (v : BiProjBerk k M M') :
    EReal :=
  logAbs t.1 v + (t.2 : EReal)

theorem termVal_def (t : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ)
    (v : BiProjBerk k M M') : termVal t v = logAbs t.1 v + (t.2 : EReal) := rfl

@[fun_prop]
theorem continuous_termVal (t : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ) :
    Continuous (termVal t : BiProjBerk k M M' → EReal) :=
  (ProjBerk.continuous_ereal_add_coe t.2).comp (continuous_logAbs t.1)

theorem termVal_ne_top (t : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ)
    (v : BiProjBerk k M M') : termVal t v ≠ ⊤ :=
  EReal.add_ne_top (logAbs_ne_top _ _) (EReal.coe_ne_top _)

/-- A term is finite at `v` iff its polynomial does not vanish at `v`. -/
theorem termVal_ne_bot_iff (t : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ)
    (v : BiProjBerk k M M') : termVal t v ≠ ⊥ ↔ v.1.val t.1 ≠ 0 := by
  rw [termVal_def, Ne, EReal.add_eq_bot_iff, not_or, logAbs_eq_bot_iff]
  exact and_iff_left (EReal.coe_ne_bot _)

/-- `log|F^r| + rλ = r (log|F| + λ)`. -/
theorem termVal_pow (t : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ) (r : ℕ)
    (v : BiProjBerk k M M') :
    termVal (t.1 ^ r, (r : ℝ) * t.2) v = ((r : ℝ) : EReal) * termVal t v := by
  rw [termVal_def, termVal_def, ProjBerk.ereal_coe_mul_add (Nat.cast_nonneg r), logAbs_pow,
    EReal.coe_mul]
  rfl

/-- `log|F^p F'^q| + (pλ + qλ') = p (log|F| + λ) + q (log|F'| + λ')`. -/
theorem termVal_mul_pow (t t' : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ) (p q : ℕ)
    (v : BiProjBerk k M M') :
    termVal (t.1 ^ p * t'.1 ^ q, (p : ℝ) * t.2 + (q : ℝ) * t'.2) v =
      ((p : ℝ) : EReal) * termVal t v + ((q : ℝ) : EReal) * termVal t' v := by
  rw [← termVal_pow, ← termVal_pow, termVal_def, termVal_def, termVal_def, logAbs_mul,
    EReal.coe_add, add_add_add_comm]

open Classical in
/-- The family `(F_t^r, r λ_t)_t`, representing the same FS function with `m` replaced by `r m`
(BJ22 `equ:FSpower`). -/
def scaleTerms (r : ℕ) (T : Finset (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ)) :
    Finset (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ) :=
  T.image fun t => (t.1 ^ r, (r : ℝ) * t.2)

theorem mem_scaleTerms {r : ℕ} {T : Finset (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ)}
    {t : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ} :
    t ∈ scaleTerms r T ↔ ∃ t₀ ∈ T, (t₀.1 ^ r, (r : ℝ) * t₀.2) = t := by
  classical
  simp only [scaleTerms, Finset.mem_image]

theorem sup_scaleTerms {r : ℕ} (hr : 0 < r)
    (T : Finset (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ)) (v : BiProjBerk k M M') :
    (scaleTerms r T).sup (fun t => termVal t v) =
      ((r : ℝ) : EReal) * T.sup fun t => termVal t v := by
  classical
  rw [ProjBerk.ereal_coe_mul_finset_sup (by exact_mod_cast hr)]
  simp only [scaleTerms]
  convert Finset.sup_image T (fun t => (t.1 ^ r, (r : ℝ) * t.2)) (fun t => termVal t v) using 1
  exact Finset.sup_congr rfl fun t _ => (termVal_pow t r v).symm

theorem isWeightedHomogeneous_scaleTerms
    {T : Finset (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ)} {p : ℕ × ℕ}
    (hT : ∀ t ∈ T, t.1.IsWeightedHomogeneous (biWeight M M') p) (r : ℕ) :
    ∀ t ∈ scaleTerms r T, t.1.IsWeightedHomogeneous (biWeight M M') (r • p) := by
  intro t ht
  obtain ⟨t₀, h₀, rfl⟩ := mem_scaleTerms.1 ht
  exact (hT t₀ h₀).pow r

theorem isRational_scaleTerms {T : Finset (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ)}
    (hT : ∀ t ∈ T, ∃ q : ℚ, t.2 = q) (r : ℕ) : ∀ t ∈ scaleTerms r T, ∃ q : ℚ, t.2 = q := by
  intro t ht
  obtain ⟨t₀, h₀, rfl⟩ := mem_scaleTerms.1 ht
  obtain ⟨q, hq⟩ := hT t₀ h₀
  exact ⟨r * q, by simp [hq]⟩

/-- The `r`-fold multiple of a bidegree, componentwise. -/
theorem nsmul_bidegree (r : ℕ) (p : ℕ × ℕ) : r • p = (r * p.1, r * p.2) := rfl

/-! ### Bigraded Fubini–Study data -/

variable (k M M') in
/-- The data of a **bigraded Fubini–Study function of class `(a, b)`** on `(ℙ^M × ℙ^{M'})^an`
(`def:pg-blowup-fs`; BJ22 `defi:FS` for the classes `a O(1, 0) + b O(0, 1)`): an integer `m > 0`
with `m a, m b ∈ ℕ` (the bidegree `deg = (m a, m b)`), and a finite family of pairs `(F_t, λ_t)`
of bihomogeneous `F_t ∈ R_{M,M'}` of bidegree `(m a, m b)` and reals `λ_t`. The function is
`m⁻¹ max_t (log|F_t| + λ_t)` (`FSData.eval`). Generic finiteness is imposed on the subvariety
`X'^an` (`ProjSubvariety.BlowupCenter.IsFS`), not here. -/
structure FSData (a b : ℚ) where
  /-- The integer `m > 0` such that `m a` and `m b` are integers. -/
  m : ℕ
  m_pos : 0 < m
  /-- The bidegree `(m a, m b)` of the polynomials. -/
  deg : ℕ × ℕ
  deg_fst : (deg.1 : ℚ) = m * a
  deg_snd : (deg.2 : ℚ) = m * b
  /-- The finite family of pairs `(F_t, λ_t)`. -/
  terms : Finset (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ)
  /-- The `F_t` are bihomogeneous of bidegree `deg`. -/
  isWeightedHomogeneous : ∀ t ∈ terms, t.1.IsWeightedHomogeneous (biWeight M M') deg

namespace FSData

variable {a b a' b' : ℚ}

/-- The bigraded Fubini–Study function `m⁻¹ max_t (log|F_t| + λ_t)` defined by the data. -/
def eval (D : FSData k M M' a b) (v : BiProjBerk k M M') : EReal :=
  (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup fun t => termVal t v

/-- The constants `λ_t` are rational. -/
def IsRational (D : FSData k M M' a b) : Prop :=
  ∀ t ∈ D.terms, ∃ q : ℚ, t.2 = q

variable (D : FSData k M M' a b)

theorem eval_def (v : BiProjBerk k M M') :
    D.eval v = (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup fun t => termVal t v := rfl

theorem m_ne_zero : (D.m : ℝ) ≠ 0 := by exact_mod_cast D.m_pos.ne'

theorem inv_m_pos : 0 < (D.m : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast D.m_pos)

theorem a_nonneg (D : FSData k M M' a b) : 0 ≤ a := by
  have h := D.deg_fst
  have hm : (0 : ℚ) < D.m := by exact_mod_cast D.m_pos
  by_contra! ha
  have : (D.m : ℚ) * a < 0 := mul_neg_of_pos_of_neg hm ha
  rw [← h] at this
  exact absurd this (not_lt.2 (Nat.cast_nonneg _))

theorem b_nonneg (D : FSData k M M' a b) : 0 ≤ b := by
  have h := D.deg_snd
  have hm : (0 : ℚ) < D.m := by exact_mod_cast D.m_pos
  by_contra! hb
  have : (D.m : ℚ) * b < 0 := mul_neg_of_pos_of_neg hm hb
  rw [← h] at this
  exact absurd this (not_lt.2 (Nat.cast_nonneg _))

/-- Bigraded FS functions are continuous. -/
@[fun_prop]
theorem continuous_eval : Continuous D.eval :=
  (ProjBerk.continuous_ereal_coe_mul (inv_ne_zero D.m_ne_zero)).comp
    (Continuous.finset_sup_apply fun t _ => continuous_termVal t)

/-- Bigraded FS functions take values in `[-∞, ∞)`. -/
theorem eval_ne_top (v : BiProjBerk k M M') : D.eval v ≠ ⊤ := by
  refine ProjBerk.ereal_coe_mul_ne_top D.inv_m_pos.le (lt_top_iff_ne_top.1 ?_)
  exact (Finset.sup_lt_iff (bot_lt_top)).2 fun t _ => lt_top_iff_ne_top.2 (termVal_ne_top t v)

theorem termVal_le_eval_mul (v : BiProjBerk k M M')
    {t : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ} (ht : t ∈ D.terms) :
    (((D.m : ℝ)⁻¹ : ℝ) : EReal) * termVal t v ≤ D.eval v :=
  ProjBerk.ereal_coe_mul_monotone D.inv_m_pos.le (Finset.le_sup (f := fun t => termVal t v) ht)

/-- A bigraded FS function is finite at a point iff one of its polynomials does not vanish
there. -/
theorem eval_ne_bot_iff_exists_val_ne_zero (v : BiProjBerk k M M') :
    D.eval v ≠ ⊥ ↔ ∃ t ∈ D.terms, v.1.val t.1 ≠ 0 := by
  constructor
  · intro h
    by_contra hcon
    apply h
    have hsup : (D.terms.sup fun t => termVal t v) = ⊥ := by
      rw [Finset.sup_eq_bot_iff]
      intro t ht
      by_contra h0
      exact hcon ⟨t, ht, (termVal_ne_bot_iff t v).1 h0⟩
    rw [eval_def, hsup]
    exact EReal.coe_mul_bot_of_pos D.inv_m_pos
  · rintro ⟨t, ht, hv⟩
    exact ne_bot_of_le_ne_bot
      (ProjBerk.ereal_coe_mul_ne_bot D.inv_m_pos.le ((termVal_ne_bot_iff t v).2 hv))
      (D.termVal_le_eval_mul v ht)

/-! #### Constants -/

open Classical in
/-- The constant function `c` as a bigraded FS function of class `(a, b) ≥ 0`:
`c = m⁻¹ max_{j,l} (log|x_j^{m a} y_l^{m b}| + m c)` with `m = den a · den b`, since
`max_j |x_j| = 1 = max_l |y_l|` on `(ℙ^M × ℙ^{M'})^an`. -/
def const (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (c : ℝ) : FSData k M M' a b where
  m := a.den * b.den
  m_pos := Nat.mul_pos a.den_pos b.den_pos
  deg := (a.num.toNat * b.den, b.num.toNat * a.den)
  deg_fst := by
    have h : ((a.num.toNat : ℕ) : ℚ) = (a.num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 ha)
    simp only [Nat.cast_mul]
    rw [h, ← Rat.den_mul_eq_num]
    ring
  deg_snd := by
    have h : ((b.num.toNat : ℕ) : ℚ) = (b.num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hb)
    simp only [Nat.cast_mul]
    rw [h, ← Rat.den_mul_eq_num]
    ring
  terms := (Finset.univ : Finset (Fin (M + 1) × Fin (M' + 1))).image fun p =>
    (MvPolynomial.X (Sum.inl p.1) ^ (a.num.toNat * b.den) *
      MvPolynomial.X (Sum.inr p.2) ^ (b.num.toNat * a.den), ((a.den * b.den : ℕ) : ℝ) * c)
  isWeightedHomogeneous := by
    intro t ht
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 ht
    have h := ((MvPolynomial.isWeightedHomogeneous_X k (biWeight M M') (Sum.inl p.1)).pow
      (a.num.toNat * b.den)).mul
      ((MvPolynomial.isWeightedHomogeneous_X k (biWeight M M') (Sum.inr p.2)).pow
        (b.num.toNat * a.den))
    have e : (a.num.toNat * b.den) • biWeight M M' (Sum.inl p.1) +
        (b.num.toNat * a.den) • biWeight M M' (Sum.inr p.2) =
          (a.num.toNat * b.den, b.num.toNat * a.den) := by
      simp
    rw [e] at h
    exact h

theorem eval_const (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (c : ℝ) (v : BiProjBerk k M M') :
    (const a b ha hb c : FSData k M M' a b).eval v = (c : EReal) := by
  classical
  have hsup : ((const a b ha hb c : FSData k M M' a b).terms.sup fun t => termVal t v) =
      ((((a.den * b.den : ℕ) : ℝ) * c : ℝ) : EReal) := by
    refine le_antisymm (Finset.sup_le fun t ht => ?_) ?_
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 ht
      rw [termVal_def]
      calc logAbs (MvPolynomial.X (Sum.inl p.1) ^ (a.num.toNat * b.den) *
              MvPolynomial.X (Sum.inr p.2) ^ (b.num.toNat * a.den)) v +
            ((((a.den * b.den : ℕ) : ℝ) * c : ℝ) : EReal)
          ≤ 0 + ((((a.den * b.den : ℕ) : ℝ) * c : ℝ) : EReal) :=
            add_le_add_left (logAbs_le_zero _ v) _
        _ = _ := zero_add _
    · obtain ⟨j, hj⟩ := exists_val_X_inl_eq_one v
      obtain ⟨l, hl⟩ := exists_val_X_inr_eq_one v
      refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun t => termVal t v)
        (Finset.mem_image_of_mem (fun p : Fin (M + 1) × Fin (M' + 1) =>
          (MvPolynomial.X (Sum.inl p.1) ^ (a.num.toNat * b.den) *
            MvPolynomial.X (Sum.inr p.2) ^ (b.num.toNat * a.den),
              ((a.den * b.den : ℕ) : ℝ) * c)) (Finset.mem_univ (j, l))))
      simp only [termVal_def]
      rw [logAbs_def, map_mul, map_pow, map_pow, hj, hl, one_pow, one_pow, mul_one,
        ENNReal.coe_one, ENNReal.log_one, zero_add]
  rw [eval_def, hsup, ← EReal.coe_mul]
  congr 1
  change (((a.den * b.den : ℕ) : ℝ))⁻¹ * (((a.den * b.den : ℕ) : ℝ) * c) = c
  have : ((a.den * b.den : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos a.den_pos b.den_pos).ne'
  field_simp

theorem isRational_const (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (c : ℚ) :
    (const a b ha hb (c : ℝ) : FSData k M M' a b).IsRational := by
  classical
  intro t ht
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 ht
  exact ⟨(a.den * b.den : ℕ) * c, by push_cast; ring⟩

/-! #### Maxima -/

theorem inv_m_mul_m_cancel (D D' : FSData k M M' a b) :
    ((D.m : ℝ) * D'.m)⁻¹ * D'.m = (D.m : ℝ)⁻¹ := by
  field_simp [D.m_ne_zero, D'.m_ne_zero]

/-- Data of the same class have proportional bidegrees: `m deg' = m' deg`. -/
theorem nsmul_deg_eq (D D' : FSData k M M' a b) : D.m • D'.deg = D'.m • D.deg := by
  have e1 : D.m * D'.deg.1 = D'.m * D.deg.1 := by
    have : ((D.m * D'.deg.1 : ℕ) : ℚ) = ((D'.m * D.deg.1 : ℕ) : ℚ) := by
      push_cast; rw [D.deg_fst, D'.deg_fst]; ring
    exact_mod_cast this
  have e2 : D.m * D'.deg.2 = D'.m * D.deg.2 := by
    have : ((D.m * D'.deg.2 : ℕ) : ℚ) = ((D'.m * D.deg.2 : ℕ) : ℚ) := by
      push_cast; rw [D.deg_snd, D'.deg_snd]; ring
    exact_mod_cast this
  rw [nsmul_bidegree, nsmul_bidegree, e1, e2]

open Classical in
/-- The maximum of two bigraded FS functions of the same class (BJ22 FS): with
`m'' = m m'`, join the families `(F_t^{m'}, m' λ_t)` and `(F'_s^m, m λ'_s)`, of bidegree
`m' deg = m deg'`. -/
def sup (D D' : FSData k M M' a b) : FSData k M M' a b where
  m := D.m * D'.m
  m_pos := Nat.mul_pos D.m_pos D'.m_pos
  deg := D'.m • D.deg
  deg_fst := by
    rw [nsmul_bidegree]
    push_cast
    rw [D.deg_fst]
    ring
  deg_snd := by
    rw [nsmul_bidegree]
    push_cast
    rw [D.deg_snd]
    ring
  terms := scaleTerms D'.m D.terms ∪ scaleTerms D.m D'.terms
  isWeightedHomogeneous := by
    intro t ht
    rcases Finset.mem_union.1 ht with h | h
    · exact isWeightedHomogeneous_scaleTerms D.isWeightedHomogeneous D'.m t h
    · exact nsmul_deg_eq D D' ▸ isWeightedHomogeneous_scaleTerms D'.isWeightedHomogeneous D.m t h

theorem eval_sup (D D' : FSData k M M' a b) (v : BiProjBerk k M M') :
    (D.sup D').eval v = max (D.eval v) (D'.eval v) := by
  classical
  have hm : (((D.sup D').m : ℕ) : ℝ) = (D.m : ℝ) * D'.m := Nat.cast_mul _ _
  have ht : (D.sup D').terms = scaleTerms D'.m D.terms ∪ scaleTerms D.m D'.terms := rfl
  rw [eval_def, eval_def, eval_def, ht, Finset.sup_union, sup_scaleTerms D'.m_pos,
    sup_scaleTerms D.m_pos, hm, ProjBerk.ereal_coe_mul_max (inv_nonneg.2 (by positivity)),
    ProjBerk.ereal_coe_mul_coe_mul, ProjBerk.ereal_coe_mul_coe_mul, inv_m_mul_m_cancel,
    mul_comm (D.m : ℝ), inv_m_mul_m_cancel]

theorem IsRational.sup {D D' : FSData k M M' a b} (h : D.IsRational) (h' : D'.IsRational) :
    (D.sup D').IsRational := by
  classical
  intro t ht
  rcases Finset.mem_union.1 ht with h1 | h1
  · exact isRational_scaleTerms h _ t h1
  · exact isRational_scaleTerms h' _ t h1

/-! #### Sums -/

open Classical in
/-- The sum of bigraded FS functions of classes `(a, b)` and `(a', b')` is a bigraded FS function
of class `(a + a', b + b')` (BJ22 FS(iii)): with `m'' = m m'`, take the products
`F_t^{m'} F'_s^m` with constants `m' λ_t + m λ'_s`. -/
def add (D : FSData k M M' a b) (D' : FSData k M M' a' b') :
    FSData k M M' (a + a') (b + b') where
  m := D.m * D'.m
  m_pos := Nat.mul_pos D.m_pos D'.m_pos
  deg := D'.m • D.deg + D.m • D'.deg
  deg_fst := by
    rw [Prod.fst_add, nsmul_bidegree, nsmul_bidegree]
    push_cast
    rw [D.deg_fst, D'.deg_fst]
    ring
  deg_snd := by
    rw [Prod.snd_add, nsmul_bidegree, nsmul_bidegree]
    push_cast
    rw [D.deg_snd, D'.deg_snd]
    ring
  terms := (D.terms ×ˢ D'.terms).image fun p =>
    (p.1.1 ^ D'.m * p.2.1 ^ D.m, (D'.m : ℝ) * p.1.2 + (D.m : ℝ) * p.2.2)
  isWeightedHomogeneous := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ht
    rw [Finset.mem_product] at hp
    exact ((D.isWeightedHomogeneous _ hp.1).pow _).mul ((D'.isWeightedHomogeneous _ hp.2).pow _)

theorem eval_add (D : FSData k M M' a b) (D' : FSData k M M' a' b') (v : BiProjBerk k M M') :
    (D.add D').eval v = D.eval v + D'.eval v := by
  classical
  have hm : (((D.add D').m : ℕ) : ℝ) = (D.m : ℝ) * D'.m := Nat.cast_mul _ _
  have hsup : ((D.add D').terms.sup fun t => termVal t v) =
      ((D'.m : ℝ) : EReal) * (D.terms.sup fun t => termVal t v) +
        ((D.m : ℝ) : EReal) * (D'.terms.sup fun t => termVal t v) := by
    change ((D.terms ×ˢ D'.terms).image fun p =>
      (p.1.1 ^ D'.m * p.2.1 ^ D.m, (D'.m : ℝ) * p.1.2 + (D.m : ℝ) * p.2.2)).sup _ = _
    rw [Finset.sup_image, ProjBerk.ereal_coe_mul_finset_sup (by exact_mod_cast D'.m_pos),
      ProjBerk.ereal_coe_mul_finset_sup (by exact_mod_cast D.m_pos),
      ← ProjBerk.ereal_finset_sup_product_add]
    exact Finset.sup_congr rfl fun p _ => termVal_mul_pow p.1 p.2 D'.m D.m v
  have h1 : ((D.m : ℝ) * D'.m)⁻¹ * D'.m = (D.m : ℝ)⁻¹ := by
    field_simp [D.m_ne_zero, D'.m_ne_zero]
  have h2 : ((D.m : ℝ) * D'.m)⁻¹ * D.m = (D'.m : ℝ)⁻¹ := by
    field_simp [D.m_ne_zero, D'.m_ne_zero]
  rw [eval_def, eval_def, eval_def, hsup, hm,
    ProjBerk.ereal_coe_mul_add (inv_nonneg.2 (by positivity)), ProjBerk.ereal_coe_mul_coe_mul,
    ProjBerk.ereal_coe_mul_coe_mul, h1, h2]

theorem IsRational.add {D : FSData k M M' a b} {D' : FSData k M M' a' b'} (h : D.IsRational)
    (h' : D'.IsRational) : (D.add D').IsRational := by
  classical
  intro t ht
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ht
  rw [Finset.mem_product] at hp
  obtain ⟨q, hq⟩ := h _ hp.1
  obtain ⟨q', hq'⟩ := h' _ hp.2
  exact ⟨D'.m * q + D.m * q', by simp [hq, hq']⟩

/-! #### Positive rational multiples -/

/-- A positive rational multiple `c φ` of a bigraded FS function of class `(a, b)` is one of
class `(c a, c b)` (BJ22 FS(iii)): with `c = p/q` in lowest terms, take `(F_t^p, p λ_t)`
and `q m`. -/
def smul (c : ℚ) (hc : 0 < c) (D : FSData k M M' a b) : FSData k M M' (c * a) (c * b) where
  m := c.den * D.m
  m_pos := Nat.mul_pos c.den_pos D.m_pos
  deg := c.num.toNat • D.deg
  deg_fst := by
    have h : ((c.num.toNat : ℕ) : ℚ) = (c.num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hc.le)
    rw [nsmul_bidegree, Nat.cast_mul, Nat.cast_mul, h, D.deg_fst, ← Rat.den_mul_eq_num]
    ring
  deg_snd := by
    have h : ((c.num.toNat : ℕ) : ℚ) = (c.num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hc.le)
    rw [nsmul_bidegree, Nat.cast_mul, Nat.cast_mul, h, D.deg_snd, ← Rat.den_mul_eq_num]
    ring
  terms := scaleTerms c.num.toNat D.terms
  isWeightedHomogeneous := isWeightedHomogeneous_scaleTerms D.isWeightedHomogeneous _

theorem eval_smul (c : ℚ) (hc : 0 < c) (D : FSData k M M' a b) (v : BiProjBerk k M M') :
    (D.smul c hc).eval v = ((c : ℝ) : EReal) * D.eval v := by
  have hp : 0 < c.num.toNat := by have := Rat.num_pos.2 hc; omega
  have hm : (((D.smul c hc).m : ℕ) : ℝ) = (c.den : ℝ) * D.m := Nat.cast_mul _ _
  have ht : (D.smul c hc).terms = scaleTerms c.num.toNat D.terms := rfl
  rw [eval_def, eval_def, hm, ht, sup_scaleTerms hp, ProjBerk.ereal_coe_mul_coe_mul,
    ProjBerk.ereal_coe_mul_coe_mul]
  congr 2
  have h : ((c.num.toNat : ℕ) : ℝ) = (c.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hc.le)
  have hd : (c.den : ℝ) ≠ 0 := by exact_mod_cast c.den_ne_zero
  rw [h, Rat.cast_def]
  field_simp [D.m_ne_zero]

theorem IsRational.smul {c : ℚ} (hc : 0 < c) {D : FSData k M M' a b} (h : D.IsRational) :
    (D.smul c hc).IsRational :=
  isRational_scaleTerms h _

/-! #### Changing the weights -/

open Classical in
/-- The data `(m, deg, (F_t, r(λ_t))_t)` obtained by changing the weights `λ_t` through a map
`r : ℝ → ℝ`. -/
def reweight (r : ℝ → ℝ) : FSData k M M' a b where
  m := D.m
  m_pos := D.m_pos
  deg := D.deg
  deg_fst := D.deg_fst
  deg_snd := D.deg_snd
  terms := D.terms.image fun t => (t.1, r t.2)
  isWeightedHomogeneous := by
    intro t ht
    obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.1 ht
    exact D.isWeightedHomogeneous t₀ h₀

theorem eval_reweight (r : ℝ → ℝ) (v : BiProjBerk k M M') :
    (D.reweight r).eval v =
      (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup fun t => termVal (t.1, r t.2) v := by
  classical
  rw [eval_def]
  congr 1
  change (D.terms.image fun t => (t.1, r t.2)).sup _ = _
  rw [Finset.sup_image]
  rfl

/-- Rational new weights give rational data. -/
theorem isRational_reweight {r : ℝ → ℝ} (hr : ∀ t ∈ D.terms, ∃ q : ℚ, r t.2 = q) :
    (D.reweight r).IsRational := by
  classical
  intro t ht
  obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.1 ht
  exact hr t₀ h₀

theorem eval_reweight_mono {r r' : ℝ → ℝ} (hr : ∀ t ∈ D.terms, r t.2 ≤ r' t.2)
    (v : BiProjBerk k M M') : (D.reweight r).eval v ≤ (D.reweight r').eval v := by
  rw [eval_reweight, eval_reweight]
  refine ProjBerk.ereal_coe_mul_monotone D.inv_m_pos.le (Finset.sup_mono_fun fun t ht => ?_)
  rw [termVal_def, termVal_def]
  exact add_le_add_right (EReal.coe_le_coe_iff.2 (hr t ht)) _

/-- Shifting all weights by `m c` adds `c` to the FS function. -/
theorem eval_reweight_add (c : ℝ) (v : BiProjBerk k M M') :
    (D.reweight fun x => x + D.m * c).eval v = D.eval v + (c : EReal) := by
  have hsup : (D.terms.sup fun t => termVal (t.1, t.2 + D.m * c) v) =
      (D.terms.sup fun t => termVal t v) + ((D.m * c : ℝ) : EReal) := by
    rw [Finset.apply_sup_eq_sup_comp_of_linearOrder (s := D.terms)
      (fun x : EReal => x + ((D.m * c : ℝ) : EReal)) (fun _ _ h => add_le_add_left h _)
      (EReal.bot_add _)]
    refine Finset.sup_congr rfl fun t _ => ?_
    simp only [Function.comp_apply, termVal_def, EReal.coe_add, add_assoc]
  rw [eval_reweight, hsup, eval_def, ProjBerk.ereal_coe_mul_add D.inv_m_pos.le,
    ← EReal.coe_mul, ← mul_assoc, inv_mul_cancel₀ D.m_ne_zero, one_mul]

theorem le_eval_reweight {r : ℝ → ℝ} {c : ℝ} (hr : ∀ t ∈ D.terms, t.2 + D.m * c ≤ r t.2)
    (v : BiProjBerk k M M') : D.eval v + (c : EReal) ≤ (D.reweight r).eval v := by
  rw [← eval_reweight_add]
  exact D.eval_reweight_mono hr v

theorem eval_reweight_le {r : ℝ → ℝ} {c : ℝ} (hr : ∀ t ∈ D.terms, r t.2 ≤ t.2 + D.m * c)
    (v : BiProjBerk k M M') : (D.reweight r).eval v ≤ D.eval v + (c : EReal) := by
  rw [← eval_reweight_add]
  exact D.eval_reweight_mono hr v

/-! #### Rational approximation (FS5) -/

/-- **Rational approximation** (BJ22 FSgenfin, `lem:bj-fs-basic`(4)): every bigraded FS
function is the pointwise limit (= infimum) of a decreasing sequence of real-valued rational
bigraded FS functions of the same class,
`max(m⁻¹ max_t (log|F_t| + q_t^{(N)}), -N)` with rationals
`q_t^{(N)} ∈ (λ_t + m/(N+2), λ_t + m/(N+1))`. -/
theorem exists_antitone_isRational : ∃ E : ℕ → FSData k M M' a b,
    (∀ N, (E N).IsRational) ∧ (∀ N v, (E N).eval v ≠ ⊥) ∧
      (∀ v, Antitone fun N => (E N).eval v) ∧ ∀ v, D.eval v = ⨅ N, (E N).eval v := by
  have hm : (0 : ℝ) < D.m := by exact_mod_cast D.m_pos
  have hδ : ∀ N : ℕ, (1 : ℝ) / ((N : ℝ) + 2) < 1 / ((N : ℝ) + 1) := fun N =>
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  choose q hq using fun (N : ℕ) (x : ℝ) => exists_rat_btwn
    (show x + D.m * (1 / ((N : ℝ) + 2)) < x + D.m * (1 / ((N : ℝ) + 1)) by
      have := mul_lt_mul_of_pos_left (hδ N) hm
      linarith)
  set R : ℕ → FSData k M M' a b := fun N => D.reweight fun x => (q N x : ℝ) with hR
  have hlow : ∀ (N : ℕ) v, D.eval v + ((1 / ((N : ℝ) + 2) : ℝ) : EReal) ≤ (R N).eval v :=
    fun N v => D.le_eval_reweight (fun t _ => (hq N t.2).1.le) v
  have hup : ∀ (N : ℕ) v, (R N).eval v ≤ D.eval v + ((1 / ((N : ℝ) + 1) : ℝ) : EReal) :=
    fun N v => D.eval_reweight_le (fun t _ => (hq N t.2).2.le) v
  have hrat : ∀ N, (R N).IsRational := fun N =>
    D.isRational_reweight fun t _ => ⟨q N t.2, rfl⟩
  have hD := D.eval_ne_top
  set E : ℕ → FSData k M M' a b := fun N =>
    (R N).sup (const a b D.a_nonneg D.b_nonneg ((-(N : ℚ) : ℚ) : ℝ)) with hE
  have hEval : ∀ N v, (E N).eval v = max ((R N).eval v) ((((-(N : ℚ) : ℚ) : ℝ) : EReal)) :=
    fun N v => by rw [hE, eval_sup, eval_const]
  refine ⟨E, fun N => (hrat N).sup (isRational_const _ _ _ _ _), fun N v => ?_, fun v => ?_,
    fun v => ?_⟩
  · rw [hEval]
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)
  · refine antitone_nat_of_succ_le fun N => ?_
    rw [hEval, hEval]
    refine max_le_max ?_ ?_
    · refine (hup (N + 1) v).trans ((le_of_eq ?_).trans (hlow N v))
      push_cast
      ring_nf
    · exact EReal.coe_le_coe_iff.2 (by push_cast; linarith)
  · refine le_antisymm (le_iInf fun N => ?_) (le_of_forall_gt_imp_ge_of_dense fun c hc => ?_)
    · rw [hEval]
      by_cases hv : D.eval v = ⊥
      · rw [hv]; exact bot_le
      · exact (ProjBerk.ereal_lt_add_coe hv (hD v) (by positivity)).le.trans
          ((hlow N v).trans (le_max_left _ _))
    · obtain ⟨s, hs₁, hs₂⟩ := EReal.lt_iff_exists_real_btwn.1 hc
      -- choose `N` with `D.eval v + 1/(N+1) ≤ s` and `-N ≤ s`
      obtain ⟨N₁, hN₁⟩ : ∃ N : ℕ, D.eval v + ((1 / ((N : ℝ) + 1) : ℝ) : EReal) ≤ s := by
        by_cases hv : D.eval v = ⊥
        · exact ⟨0, by rw [hv, EReal.bot_add]; exact bot_le⟩
        · lift D.eval v to ℝ using ⟨hD v, hv⟩ with r hr
          have hrs : r < s := EReal.coe_lt_coe_iff.1 hs₁
          obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 hrs)
          exact ⟨N, by rw [← EReal.coe_add, EReal.coe_le_coe_iff]; linarith⟩
      obtain ⟨N₂, hN₂⟩ := exists_nat_ge (-s)
      set N := Max.max N₁ N₂
      refine (iInf_le _ N).trans ?_
      rw [hEval]
      refine le_trans (max_le ?_ ?_) hs₂.le
      · refine (hup N v).trans ((add_le_add_right (EReal.coe_le_coe_iff.2 ?_) _).trans hN₁)
        exact one_div_le_one_div_of_le (by positivity)
          (by have : (N₁ : ℝ) ≤ N := by exact_mod_cast le_max_left N₁ N₂
              linarith)
      · refine EReal.coe_le_coe_iff.2 ?_
        have : (N₂ : ℝ) ≤ N := by exact_mod_cast le_max_right N₁ N₂
        push_cast
        linarith

/-! #### Single terms and pullbacks from `ℙ^M` -/

/-- The single term `log|F| + λ` as a bigraded FS function of class `(p, q)`, for `F`
bihomogeneous of bidegree `(p, q)` (`m = 1`). -/
def single {p q : ℕ} (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)
    (hF : F.IsWeightedHomogeneous (biWeight M M') (p, q)) (c : ℝ) :
    FSData k M M' (p : ℚ) (q : ℚ) where
  m := 1
  m_pos := one_pos
  deg := (p, q)
  deg_fst := by simp
  deg_snd := by simp
  terms := {(F, c)}
  isWeightedHomogeneous := by
    intro t ht
    rw [Finset.mem_singleton] at ht
    rw [ht]
    exact hF

theorem eval_single {p q : ℕ} (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)
    (hF : F.IsWeightedHomogeneous (biWeight M M') (p, q)) (c : ℝ) (v : BiProjBerk k M M') :
    (single F hF c).eval v = logAbs F v + (c : EReal) := by
  have h1 : (((single F hF c).m : ℕ) : ℝ)⁻¹ = 1 := by
    change ((1 : ℕ) : ℝ)⁻¹ = 1
    simp
  rw [eval_def, h1, EReal.coe_one, one_mul]
  change ({(F, c)} : Finset _).sup (fun t => termVal t v) = _
  rw [Finset.sup_singleton, termVal_def]

theorem isRational_single {p q : ℕ} (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)
    (hF : F.IsWeightedHomogeneous (biWeight M M') (p, q)) (c : ℚ) :
    (single F hF (c : ℝ)).IsRational := by
  intro t ht
  rw [show (single F hF (c : ℝ)).terms = {(F, (c : ℝ))} from rfl, Finset.mem_singleton] at ht
  exact ⟨c, by rw [ht]⟩

open Classical in
/-- The pullback along the first projection `(ℙ^M × ℙ^{M'})^an → (ℙ^M)^an` of FS data of class
`a` on `ℙ^M`: the forms `s_t(x)` of degree `m a` are bihomogeneous of bidegree `(m a, 0)`, so they
give bigraded data of class `(a, 0)` (`eval_comapFst`). -/
def comapFst {a : ℚ} (D : ProjBerk.FSData k M a) : FSData k M M' a 0 where
  m := D.m
  m_pos := D.m_pos
  deg := (D.deg, 0)
  deg_fst := D.deg_eq
  deg_snd := by simp
  terms := D.terms.image fun t =>
    (MvPolynomial.rename (Sum.inl : Fin (M + 1) → Fin (M + 1) ⊕ Fin (M' + 1)) t.1, t.2)
  isWeightedHomogeneous := by
    intro t ht
    obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.1 ht
    exact isWeightedHomogeneous_rename_inl (D.isHomogeneous t₀ h₀)

theorem eval_comapFst {a : ℚ} (D : ProjBerk.FSData k M a) (v : BiProjBerk k M M') :
    (comapFst (M' := M') D).eval v = D.eval (fst v) := by
  classical
  rw [eval_def, ProjBerk.FSData.eval_def]
  congr 1
  change (D.terms.image fun t =>
    (MvPolynomial.rename (Sum.inl : Fin (M + 1) → Fin (M + 1) ⊕ Fin (M' + 1)) t.1, t.2)).sup _ = _
  rw [Finset.sup_image]
  rfl

theorem isRational_comapFst {a : ℚ} {D : ProjBerk.FSData k M a} (h : D.IsRational) :
    (comapFst (M' := M') D).IsRational := by
  classical
  intro t ht
  obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.1 ht
  exact h t₀ h₀

end FSData

end BiProjBerk

/-! ### The blowup `X'^an` -/

namespace ProjSubvariety.BlowupCenter

variable {k : Type u} [Field k] {M : ℕ} {V : ProjSubvariety k M} {M' : ℕ} (B : V.BlowupCenter M')

/-! #### The trivial point -/

variable {B} in
/-- A polynomial does not vanish at the trivial point `⋆'` of `X'` iff it is not in `I'`. -/
theorem triv_val_ne_zero_iff {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k} :
    (B.triv : BiProjBerk k M M').1.val F ≠ 0 ↔ F ∉ B.ideal := by
  refine ⟨fun h hF => h (B.triv_val_of_mem hF), fun h => ?_⟩
  rw [B.triv_val_of_notMem h]
  exact one_ne_zero

/-- `log|F|_{⋆'} = 0` for `F ∉ I'`. -/
theorem logAbs_triv_of_notMem {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F ∉ B.ideal) : BiProjBerk.logAbs F (B.triv : BiProjBerk k M M') = 0 := by
  rw [BiProjBerk.logAbs_def, B.triv_val_of_notMem hF, ENNReal.coe_one, ENNReal.log_one]

/-- Termwise (FS1): `log|F|_v + λ ≤ log|F|_{⋆'} + λ` on `X'^an`, since `|F|_v ≤ 1 = |F|_{⋆'}`
for `F ∉ I'` and `|F|_v = 0` for `F ∈ I'`. -/
theorem termVal_le_termVal_triv (t : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ)
    (v : B.an) :
    BiProjBerk.termVal t v ≤ BiProjBerk.termVal t (B.triv : BiProjBerk k M M') := by
  by_cases ht : t.1 ∈ B.ideal
  · rw [BiProjBerk.termVal_def, (BiProjBerk.logAbs_eq_bot_iff t.1 _).2 (B.val_eq_zero_of_mem v ht),
      EReal.bot_add]
    exact bot_le
  · rw [BiProjBerk.termVal_def, BiProjBerk.termVal_def, B.logAbs_triv_of_notMem ht]
    gcongr
    exact BiProjBerk.logAbs_le_zero _ _

/-- (FS1) for bigraded FS data on `X'^an`: `f(v) ≤ f(⋆')`. -/
theorem eval_le_eval_triv {a b : ℚ} (D : BiProjBerk.FSData k M M' a b) (v : B.an) :
    D.eval v ≤ D.eval (B.triv : BiProjBerk k M M') := by
  rw [BiProjBerk.FSData.eval_def, BiProjBerk.FSData.eval_def]
  exact ProjBerk.ereal_coe_mul_monotone D.inv_m_pos.le
    (Finset.sup_mono_fun fun t _ => B.termVal_le_termVal_triv t v)

/-- Some polynomial of the data is not in `I'` iff the FS function is finite at `⋆'`. -/
theorem exists_notMem_iff_eval_triv_ne_bot {a b : ℚ} (D : BiProjBerk.FSData k M M' a b) :
    (∃ t ∈ D.terms, t.1 ∉ B.ideal) ↔ D.eval (B.triv : BiProjBerk k M M') ≠ ⊥ := by
  rw [D.eval_ne_bot_iff_exists_val_ne_zero]
  exact exists_congr fun t => and_congr_right fun _ => triv_val_ne_zero_iff.symm

/-- The polynomials of the data have no common zero on `X'^an` iff the FS function is finite on
`X'^an`. -/
theorem forall_exists_val_ne_zero_iff {a b : ℚ} (D : BiProjBerk.FSData k M M' a b) :
    (∀ v : B.an, ∃ t ∈ D.terms, (v : BiProjBerk k M M').1.val t.1 ≠ 0) ↔
      ∀ v : B.an, D.eval v ≠ ⊥ :=
  forall_congr' fun v => (D.eval_ne_bot_iff_exists_val_ne_zero v).symm

/-! #### Fubini–Study functions on `X'^an` (`def:pg-blowup-fs`) -/

/-- **Fubini–Study functions of class `(a, b)` on `X'^an`** (`def:pg-blowup-fs`,
`𝓗(X', (a, b))`; BJ22 `defi:FS` for the class `a μ^*O(1) + b O(0, 1)`):
`f = m⁻¹ max_t (log|F_t| + λ_t)` on `X'^an`, for bigraded FS data (`m ∈ ℤ_{>0}`,
`m a, m b ∈ ℕ`, finitely many bihomogeneous `F_t` of bidegree `(m a, m b)`, `λ_t ∈ ℝ`) at least
one of whose polynomials is not in `I'`. -/
def IsFS (a b : ℚ) (f : B.an → EReal) : Prop :=
  ∃ D : BiProjBerk.FSData k M M' a b, (∃ t ∈ D.terms, t.1 ∉ B.ideal) ∧
    ∀ v : B.an, f v = D.eval v

/-- **Finite rational Fubini–Study functions of class `(a, b)` on `X'^an`**
(`def:pg-blowup-fs`, `𝓗_fin(X', (a, b))`; BJ22's `𝓗_ℚ`): as `IsFS`, with all `λ_t ∈ ℚ` and
such that at every point of `X'^an` some `|F_t| ≠ 0`. -/
def IsFinFS (a b : ℚ) (f : B.an → EReal) : Prop :=
  ∃ D : BiProjBerk.FSData k M M' a b, D.IsRational ∧
    (∀ v : B.an, ∃ t ∈ D.terms, (v : BiProjBerk k M M').1.val t.1 ≠ 0) ∧
      ∀ v : B.an, f v = D.eval v

variable {B} {a b a' b' : ℚ} {f g : B.an → EReal}

/-- `IsFS` in terms of finiteness at `⋆'`. -/
theorem isFS_iff : B.IsFS a b f ↔ ∃ D : BiProjBerk.FSData k M M' a b,
    D.eval (B.triv : BiProjBerk k M M') ≠ ⊥ ∧ ∀ v : B.an, f v = D.eval v := by
  simp only [IsFS, exists_notMem_iff_eval_triv_ne_bot]

/-- `IsFinFS` in terms of finiteness on `X'^an`. -/
theorem isFinFS_iff : B.IsFinFS a b f ↔ ∃ D : BiProjBerk.FSData k M M' a b, D.IsRational ∧
    (∀ v : B.an, D.eval v ≠ ⊥) ∧ ∀ v : B.an, f v = D.eval v := by
  simp only [IsFinFS, forall_exists_val_ne_zero_iff]

/-! #### The axioms (FS1)–(FS5) -/

theorem IsFS.continuous (h : B.IsFS a b f) : Continuous f := by
  obtain ⟨D, -, hf⟩ := h
  rw [show f = fun v : B.an => D.eval v from funext hf]
  exact D.continuous_eval.comp continuous_subtype_val

theorem IsFS.nonneg_fst (h : B.IsFS a b f) : 0 ≤ a := by
  obtain ⟨D, -, -⟩ := h
  exact D.a_nonneg

theorem IsFS.nonneg_snd (h : B.IsFS a b f) : 0 ≤ b := by
  obtain ⟨D, -, -⟩ := h
  exact D.b_nonneg

/-- (FS1) `f(⋆') ≠ -∞`. -/
theorem IsFS.apply_triv_ne_bot (h : B.IsFS a b f) : f B.triv ≠ ⊥ := by
  obtain ⟨D, hD, hf⟩ := isFS_iff.1 h
  rw [hf]
  exact hD

theorem IsFS.ne_top (h : B.IsFS a b f) (v : B.an) : f v ≠ ⊤ := by
  obtain ⟨D, -, hf⟩ := h
  rw [hf]
  exact D.eval_ne_top _

/-- (FS1) `f ≤ f(⋆')`. -/
theorem IsFS.le_apply_triv (h : B.IsFS a b f) (v : B.an) : f v ≤ f B.triv := by
  obtain ⟨D, -, hf⟩ := h
  rw [hf, hf]
  exact B.eval_le_eval_triv D v

theorem IsFinFS.isFS (h : B.IsFinFS a b f) : B.IsFS a b f := by
  obtain ⟨D, -, hD, hf⟩ := h
  obtain ⟨t, ht, hv⟩ := hD B.triv
  exact ⟨D, ⟨t, ht, triv_val_ne_zero_iff.1 hv⟩, hf⟩

/-- Finite Fubini–Study functions are real valued. -/
theorem IsFinFS.ne_bot (h : B.IsFinFS a b f) (v : B.an) : f v ≠ ⊥ := by
  obtain ⟨D, -, hD, hf⟩ := isFinFS_iff.1 h
  rw [hf]
  exact hD v

theorem IsFinFS.coe_toReal (h : B.IsFinFS a b f) (v : B.an) :
    ((f v).toReal : EReal) = f v :=
  EReal.coe_toReal (h.isFS.ne_top v) (h.ne_bot v)

variable (B) in
/-- (FS3) real constants are Fubini–Study functions of every class `(a, b) ≥ 0`. -/
theorem isFS_const (ha : 0 ≤ a) (hb : 0 ≤ b) (c : ℝ) : B.IsFS a b fun _ => (c : EReal) := by
  refine isFS_iff.2 ⟨BiProjBerk.FSData.const a b ha hb c, ?_, fun v =>
    (BiProjBerk.FSData.eval_const a b ha hb c _).symm⟩
  rw [BiProjBerk.FSData.eval_const]
  exact EReal.coe_ne_bot c

variable (B) in
/-- (FS3) rational constants are finite Fubini–Study functions of every class `(a, b) ≥ 0`. -/
theorem isFinFS_const (ha : 0 ≤ a) (hb : 0 ≤ b) (c : ℚ) :
    B.IsFinFS a b fun _ => ((c : ℝ) : EReal) := by
  refine isFinFS_iff.2 ⟨BiProjBerk.FSData.const a b ha hb (c : ℝ),
    BiProjBerk.FSData.isRational_const a b ha hb c, fun v => ?_, fun v =>
    (BiProjBerk.FSData.eval_const a b ha hb (c : ℝ) _).symm⟩
  rw [BiProjBerk.FSData.eval_const]
  exact EReal.coe_ne_bot _

/-- (FS3) maxima of Fubini–Study functions of the same class. -/
theorem IsFS.max (hf : B.IsFS a b f) (hg : B.IsFS a b g) :
    B.IsFS a b fun v => max (f v) (g v) := by
  obtain ⟨D, hD, hf⟩ := isFS_iff.1 hf
  obtain ⟨D', -, hg⟩ := isFS_iff.1 hg
  refine isFS_iff.2 ⟨D.sup D', ?_, fun v => by rw [BiProjBerk.FSData.eval_sup, hf, hg]⟩
  rw [BiProjBerk.FSData.eval_sup]
  exact ne_bot_of_le_ne_bot hD (le_max_left _ _)

/-- (FS3) maxima of finite Fubini–Study functions of the same class. -/
theorem IsFinFS.max (hf : B.IsFinFS a b f) (hg : B.IsFinFS a b g) :
    B.IsFinFS a b fun v => max (f v) (g v) := by
  obtain ⟨D, hDr, hD, hf⟩ := isFinFS_iff.1 hf
  obtain ⟨D', hD'r, -, hg⟩ := isFinFS_iff.1 hg
  refine isFinFS_iff.2 ⟨D.sup D', hDr.sup hD'r, fun v => ?_, fun v => by
    rw [BiProjBerk.FSData.eval_sup, hf, hg]⟩
  rw [BiProjBerk.FSData.eval_sup]
  exact ne_bot_of_le_ne_bot (hD v) (le_max_left _ _)

/-- (FS4) `𝓗(X', (a, b)) + 𝓗(X', (a', b')) ⊆ 𝓗(X', (a + a', b + b'))`. -/
theorem IsFS.add (hf : B.IsFS a b f) (hg : B.IsFS a' b' g) :
    B.IsFS (a + a') (b + b') fun v => f v + g v := by
  obtain ⟨D, hD, hf⟩ := isFS_iff.1 hf
  obtain ⟨D', hD', hg⟩ := isFS_iff.1 hg
  refine isFS_iff.2 ⟨D.add D', ?_, fun v => by rw [BiProjBerk.FSData.eval_add, hf, hg]⟩
  rw [BiProjBerk.FSData.eval_add]
  exact EReal.add_ne_bot_iff.2 ⟨hD, hD'⟩

/-- (FS4) `𝓗_fin(X', (a, b)) + 𝓗_fin(X', (a', b')) ⊆ 𝓗_fin(X', (a + a', b + b'))`. -/
theorem IsFinFS.add (hf : B.IsFinFS a b f) (hg : B.IsFinFS a' b' g) :
    B.IsFinFS (a + a') (b + b') fun v => f v + g v := by
  obtain ⟨D, hDr, hD, hf⟩ := isFinFS_iff.1 hf
  obtain ⟨D', hD'r, hD', hg⟩ := isFinFS_iff.1 hg
  refine isFinFS_iff.2 ⟨D.add D', hDr.add hD'r, fun v => ?_, fun v => by
    rw [BiProjBerk.FSData.eval_add, hf, hg]⟩
  rw [BiProjBerk.FSData.eval_add]
  exact EReal.add_ne_bot_iff.2 ⟨hD v, hD' v⟩

/-- (FS4) `c 𝓗(X', (a, b)) ⊆ 𝓗(X', (c a, c b))` for `c ∈ ℚ_{>0}`. -/
theorem IsFS.smul (h : B.IsFS a b f) {c : ℚ} (hc : 0 < c) :
    B.IsFS (c * a) (c * b) fun v => ((c : ℝ) : EReal) * f v := by
  obtain ⟨D, hD, hf⟩ := isFS_iff.1 h
  refine isFS_iff.2 ⟨D.smul c hc, ?_, fun v => by rw [BiProjBerk.FSData.eval_smul, hf]⟩
  rw [BiProjBerk.FSData.eval_smul]
  exact ProjBerk.ereal_coe_mul_ne_bot (by exact_mod_cast hc.le) hD

/-- (FS4) `c 𝓗_fin(X', (a, b)) ⊆ 𝓗_fin(X', (c a, c b))` for `c ∈ ℚ_{>0}`. -/
theorem IsFinFS.smul (h : B.IsFinFS a b f) {c : ℚ} (hc : 0 < c) :
    B.IsFinFS (c * a) (c * b) fun v => ((c : ℝ) : EReal) * f v := by
  obtain ⟨D, hDr, hD, hf⟩ := isFinFS_iff.1 h
  refine isFinFS_iff.2 ⟨D.smul c hc, hDr.smul hc, fun v => ?_, fun v => by
    rw [BiProjBerk.FSData.eval_smul, hf]⟩
  rw [BiProjBerk.FSData.eval_smul]
  exact ProjBerk.ereal_coe_mul_ne_bot (by exact_mod_cast hc.le) (hD v)

/-- (FS2) `𝓗(X', (a, b)) ⊆ 𝓗(X', (a', b'))` for `a ≤ a'`, `b ≤ b'`: add the constant `0` of class
`(a' - a, b' - b)`, i.e. multiply by all monomials `x^β y^γ` of bidegree
`(m (a' - a), m (b' - b))`, whose maximum has logarithm `0`. -/
theorem IsFS.mono_class (h : B.IsFS a b f) (ha : a ≤ a') (hb : b ≤ b') : B.IsFS a' b' f := by
  have h' := h.add (B.isFS_const (sub_nonneg.2 ha) (sub_nonneg.2 hb) 0)
  rw [add_sub_cancel, add_sub_cancel] at h'
  simpa only [EReal.coe_zero, add_zero] using h'

/-- (FS2) `𝓗_fin(X', (a, b)) ⊆ 𝓗_fin(X', (a', b'))` for `a ≤ a'`, `b ≤ b'`. -/
theorem IsFinFS.mono_class (h : B.IsFinFS a b f) (ha : a ≤ a') (hb : b ≤ b') :
    B.IsFinFS a' b' f := by
  have h' := h.add (B.isFinFS_const (sub_nonneg.2 ha) (sub_nonneg.2 hb) 0)
  rw [add_sub_cancel, add_sub_cancel] at h'
  simpa only [Rat.cast_zero, EReal.coe_zero, add_zero] using h'

/-- (FS5) every `f ∈ 𝓗(X', (a, b))` is the limit of a decreasing sequence in
`𝓗_fin(X', (a, b))`: the rational approximants
`max(m⁻¹ max_t (log|F_t| + λ_t^{(n)}), -n)` (`BiProjBerk.FSData.exists_antitone_isRational`),
which are finite on all of `(ℙ^M × ℙ^{M'})^an`. -/
theorem IsFS.exists_antitone_isFinFS (h : B.IsFS a b f) : ∃ g : ℕ → B.an → EReal,
    (∀ n, B.IsFinFS a b (g n)) ∧ (∀ x, Antitone fun n => g n x) ∧ ∀ x, f x = ⨅ n, g n x := by
  obtain ⟨D, -, hf⟩ := h
  obtain ⟨E, hErat, hEne, hanti, hinf⟩ := D.exists_antitone_isRational
  exact ⟨fun n v => (E n).eval v, fun n => isFinFS_iff.2 ⟨E n, hErat n, fun v => hEne n v,
    fun v => rfl⟩, fun v => hanti v, fun v => by rw [hf, hinf]⟩

/-! #### Logarithms of bihomogeneous polynomials and pullbacks along `μ` -/

variable (B) in
/-- `log|F| ∈ 𝓗(X', (p, q))` for `F ∉ I'` bihomogeneous of bidegree `(p, q)` (`m = 1`, a single
term). For instance `log|G_l y_l| ∈ 𝓗(X', (d, 1))` (`lem:pg-descent-cover`). -/
theorem isFS_logAbs {p q : ℕ} {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (p, q)) (hFI : F ∉ B.ideal) :
    B.IsFS p q fun v => BiProjBerk.logAbs F v := by
  refine ⟨BiProjBerk.FSData.single F hF 0, ⟨(F, 0), Finset.mem_singleton_self _, hFI⟩,
    fun v => ?_⟩
  rw [BiProjBerk.FSData.eval_single, EReal.coe_zero, add_zero]

variable (B) in
/-- **Pullback of Fubini–Study functions along `μ`**: `μ^* 𝓗(X, a) ⊆ 𝓗(X', (a, 0))`. The forms
`s_t` of degree `m a` give bihomogeneous `s_t(x)` of bidegree `(m a, 0)`, not in `I'` if `s_t ∉ I`
(`I' ∩ R_M = I`), and `|s_t(x)|_v = |s_t|_{μ(v)}`. -/
theorem _root_.EnvelopeProperty.ProjSubvariety.IsFS.comp_proj {a : ℚ} {φ : V.an → EReal}
    (h : V.IsFS a φ) : B.IsFS a 0 (φ ∘ B.proj) := by
  classical
  obtain ⟨D, ⟨t, ht, htI⟩, hφ⟩ := h
  refine ⟨BiProjBerk.FSData.comapFst D,
    ⟨(MvPolynomial.rename Sum.inl t.1, t.2), Finset.mem_image_of_mem _ ht,
      fun h => htI ((B.rename_inl_mem_ideal_iff t.1).1 h)⟩, fun v => ?_⟩
  rw [BiProjBerk.FSData.eval_comapFst, Function.comp_apply, hφ]
  rfl

variable (B) in
/-- **Pullback of finite Fubini–Study functions along `μ`**:
`μ^* 𝓗_fin(X, a) ⊆ 𝓗_fin(X', (a, 0))`. -/
theorem _root_.EnvelopeProperty.ProjSubvariety.IsFinFS.comp_proj {a : ℚ} {φ : V.an → EReal}
    (h : V.IsFinFS a φ) : B.IsFinFS a 0 (φ ∘ B.proj) := by
  obtain ⟨D, hDr, hD, hφ⟩ := ProjSubvariety.isFinFS_iff.1 h
  refine isFinFS_iff.2 ⟨BiProjBerk.FSData.comapFst D,
    BiProjBerk.FSData.isRational_comapFst hDr, fun v => ?_, fun v => ?_⟩
  · rw [BiProjBerk.FSData.eval_comapFst]
    exact hD (B.proj v)
  · rw [BiProjBerk.FSData.eval_comapFst, Function.comp_apply, hφ]
    rfl

/-! ### The Fubini–Study system of `X'` (`lem:pg-blowup-fs-system`) -/

variable (B) in
/-- **`(X'^an, ⋆')` is a Fubini–Study system of rank two** (`lem:pg-blowup-fs-system`; BJ22
FS, FSgenfin), with `𝓗(a) = 𝓗(X', (a 0, a 1))` and
`𝓗_fin(a) = 𝓗_fin(X', (a 0, a 1))` for `a ∈ ℚ²`. -/
def fsSystem : FSSystem B.an 2 where
  triv := B.triv
  IsFS a f := B.IsFS (a 0) (a 1) f
  IsFinFS a f := B.IsFinFS (a 0) (a 1) f
  continuous_of_isFS h := h.continuous
  nonneg_of_isFS h := fun c => by
    fin_cases c
    · exact h.nonneg_fst
    · exact h.nonneg_snd
  apply_triv_ne_bot h := h.apply_triv_ne_bot
  apply_triv_ne_top h := h.ne_top _
  le_apply_triv h x := h.le_apply_triv x
  isFS_of_isFinFS h := h.isFS
  ne_bot_of_isFinFS h := h.ne_bot
  isFS_mono h hab := h.mono_class (hab 0) (hab 1)
  isFinFS_mono h hab := h.mono_class (hab 0) (hab 1)
  isFS_const ha c := B.isFS_const (ha 0) (ha 1) c
  isFinFS_const ha c := B.isFinFS_const (ha 0) (ha 1) c
  isFS_max hf hg := hf.max hg
  isFinFS_max hf hg := hf.max hg
  isFS_add hf hg := hf.add hg
  isFinFS_add hf hg := hf.add hg
  isFS_smul hc h := h.smul hc
  isFinFS_smul hc h := h.smul hc
  exists_antitone_isFinFS h := h.exists_antitone_isFinFS

@[simp] theorem fsSystem_triv : B.fsSystem.triv = B.triv := rfl

theorem fsSystem_isFS_iff {a : Fin 2 → ℚ} : B.fsSystem.IsFS a f ↔ B.IsFS (a 0) (a 1) f :=
  Iff.rfl

theorem fsSystem_isFinFS_iff {a : Fin 2 → ℚ} :
    B.fsSystem.IsFinFS a f ↔ B.IsFinFS (a 0) (a 1) f :=
  Iff.rfl

variable (B) in
/-- `X'^an` is second countable for countable `k` (`lem:pg-blowup-basic`(3)): it is a subspace
of `(ℙ^M × ℙ^{M'})^an` (`BiProjBerk.instSecondCountableTopology`). -/
theorem secondCountableTopology_an [Countable k] : SecondCountableTopology B.an :=
  inferInstance

/-! ### Psh functions on `X'^an` (`def:pg-blowup-psh`) -/

variable (B) in
/-- **`θ`-psh functions on the blowup `X'^an`** (`def:pg-blowup-psh`, `PSH(X', θ)` for
`θ ∈ ℝ²`; BJ22 Definition 4.1 for the classes `θ₀ μ^*O(1) + θ₁ O(0, 1)`, see
`rmk:pg-blowup-psh-comparison`): the `θ`-psh functions (`def:pg-psh`, `FSSystem.IsPSH`) of the
Fubini–Study system `B.fsSystem`. The `μ^*O(a)`-psh functions are `B.IsPSH ![a, 0]`:
`PSH(X', μ^*O(a)) = PSH(X', (a, 0))`. -/
abbrev IsPSH (θ : Fin 2 → ℝ) (u : B.an → EReal) : Prop :=
  B.fsSystem.IsPSH θ u

variable {θ θ' : Fin 2 → ℝ} {u u' : B.an → EReal}

/-- PSH1 (`thm:pg-psh2`(1)): `𝓗(X', (a, b)) ⊆ PSH(X', (a, b))`. -/
theorem IsFS.isPSH (h : B.IsFS a b f) : B.IsPSH ![(a : ℝ), (b : ℝ)] f := by
  have h' := FSSystem.IsFS.isPSH (F := B.fsSystem) (a := ![a, b]) h
  rwa [ratCast_vecCons_two] at h'

theorem IsFinFS.isPSH (h : B.IsFinFS a b f) : B.IsPSH ![(a : ℝ), (b : ℝ)] f :=
  h.isFS.isPSH

variable (B) in
/-- `log|F| ∈ PSH(X', (p, q))` for `F ∉ I'` bihomogeneous of bidegree `(p, q)`. -/
theorem isPSH_logAbs {p q : ℕ} {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (p, q)) (hFI : F ∉ B.ideal) :
    B.IsPSH ![(p : ℝ), (q : ℝ)] fun v => BiProjBerk.logAbs F v := by
  have h := (B.isFS_logAbs hF hFI).isPSH
  simpa only [Rat.cast_natCast] using h

/-- `PSH(X', θ) ≠ ∅` forces `θ ≥ 0` (`prop:pg-maxprin`). -/
theorem IsPSH.nonneg (h : B.IsPSH θ u) : 0 ≤ θ :=
  FSSystem.IsPSH.nonneg h

/-- **The maximum principle** (`prop:pg-maxprin`): `u ≤ u(⋆')`. -/
theorem IsPSH.le_apply_triv (h : B.IsPSH θ u) (x : B.an) : u x ≤ u B.triv :=
  FSSystem.IsPSH.le_apply_triv h x

/-- A `θ`-psh function is finite at `⋆'` (`prop:pg-maxprin`). -/
theorem IsPSH.apply_triv_ne_bot (h : B.IsPSH θ u) : u B.triv ≠ ⊥ :=
  FSSystem.IsPSH.apply_triv_ne_bot h

/-- `PSH(X', θ) + PSH(X', θ') ⊆ PSH(X', θ + θ')` (`thm:pg-psh-basic`(1)). -/
theorem IsPSH.add (h : B.IsPSH θ u) (h' : B.IsPSH θ' u') :
    B.IsPSH (θ + θ') fun x => u x + u' x :=
  FSSystem.IsPSH.add h h'

/-- `t PSH(X', θ) ⊆ PSH(X', t θ)` for real `t > 0` (`thm:pg-psh-basic`(1)). -/
theorem IsPSH.smul (h : B.IsPSH θ u) {t : ℝ} (ht : 0 < t) :
    B.IsPSH (t • θ) fun x => (t : EReal) * u x :=
  FSSystem.IsPSH.smul h ht

/-- Maxima (`thm:pg-psh-basic`(2)). -/
theorem IsPSH.max (h : B.IsPSH θ u) (h' : B.IsPSH θ u') :
    B.IsPSH θ fun x => max (u x) (u' x) :=
  FSSystem.IsPSH.max h h'

/-- Adding real constants (`thm:pg-psh-basic`(2)). -/
theorem IsPSH.add_const (h : B.IsPSH θ u) (c : ℝ) : B.IsPSH θ fun x => u x + (c : EReal) :=
  FSSystem.IsPSH.add_const h c

variable (B) in
/-- Real constants are `θ`-psh for `θ ≥ 0` (`thm:pg-psh-basic`(2)). -/
theorem isPSH_const (hθ : 0 ≤ θ) (c : ℝ) : B.IsPSH θ fun _ => (c : EReal) :=
  FSSystem.isPSH_const hθ c

/-- Monotonicity in the class (`thm:pg-psh-basic`(3)). -/
theorem IsPSH.mono_class (h : B.IsPSH θ u) (hθθ' : θ ≤ θ') : B.IsPSH θ' u :=
  FSSystem.IsPSH.mono_class h hθθ'

/-- **PSH2** for decreasing sequences (`thm:pg-psh2`(3)): if `u_m ∈ PSH(X', θ_m)` decreases,
`θ_m → θ₀` and `w = inf_m u_m ≢ -∞`, then `w ∈ PSH(X', θ₀)`. -/
theorem isPSH_of_antitone_seq {θ : ℕ → Fin 2 → ℝ} {θ₀ : Fin 2 → ℝ}
    (hθ : Tendsto θ atTop (𝓝 θ₀)) {u : ℕ → B.an → EReal} (hu : ∀ m, B.IsPSH (θ m) (u m))
    (hanti : ∀ x, Antitone fun m => u m x) {w : B.an → EReal} (hw : ∀ x, w x = ⨅ m, u m x)
    (hfin : ∃ x, w x ≠ ⊥) : B.IsPSH θ₀ w :=
  FSSystem.isPSH_of_antitone_seq hθ hu hanti hw hfin

variable (B) in
/-- **Pullback of psh functions along `μ`**: `μ^* PSH(X, θ) ⊆ PSH(X', (θ, 0))` (BJ22
PSH(iii) for `μ`). The pullbacks of an approximating net on `X` approximate `u ∘ μ`
(`ProjSubvariety.IsFS.comp_proj`); `u ∘ μ` is usc as `μ` is continuous, and finite at `⋆'` as
`μ(⋆') = ⋆`. -/
theorem _root_.EnvelopeProperty.ProjSubvariety.IsPSH.comp_proj {θ₀ : ℝ} {φ : V.an → EReal}
    (h : V.IsPSH θ₀ φ) : B.IsPSH ![θ₀, 0] (φ ∘ B.proj) := by
  have htriv : (φ ∘ B.proj) B.triv ≠ ⊥ := by
    rw [Function.comp_apply, B.proj_triv]
    exact FSSystem.IsPSH.apply_triv_ne_bot (F := V.fsSystem) h
  obtain ⟨-, -, ι, _, _, _, a, f, hf, ha, hanti, hφ⟩ := h
  refine FSSystem.isPSH_of_iInf ⟨B.triv, htriv⟩ (fun i => ![a i 0, 0]) (fun i => f i ∘ B.proj)
    (fun i => ProjSubvariety.IsFS.comp_proj B (hf i)) ?_ (fun x i j hij => hanti _ hij)
    (fun x => hφ _)
  refine tendsto_pi_nhds.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · simpa using tendsto_pi_nhds.1 ha 0
  · simp

/-! ### Regularization on `X'^an` (`thm:pg-regularization`, `cor:pg-countable-regularization`) -/

/-- **Regularization in a fixed class** (`thm:pg-regularization`(2) and
`cor:pg-countable-regularization`(1) on `X'`): for countable `k` and `a, b ∈ ℚ_{>0}`, every
`u ∈ PSH(X', (a, b))` is the limit of a decreasing sequence in `𝓗_fin(X', (a, b))`. -/
theorem IsPSH.exists_isFinFS_seq_of_pos [Countable k] (ha : 0 < a) (hb : 0 < b)
    (h : B.IsPSH ![(a : ℝ), (b : ℝ)] u) :
    ∃ f : ℕ → B.an → EReal, (∀ m, B.IsFinFS a b (f m)) ∧ (∀ x, Antitone fun m => f m x) ∧
      ∀ x, u x = ⨅ m, f m x := by
  rw [← ratCast_vecCons_two] at h
  exact FSSystem.IsPSH.exists_isFinFS_seq_of_pos (θ := ![a, b])
    (Fin.forall_fin_two.2 ⟨ha, hb⟩) h

/-- **Dyadic regularization** (`cor:pg-countable-regularization`(2) on `X'`): for countable `k`
and `a, b ∈ ℚ`, every `u ∈ PSH(X', (a, b))` is the limit of a decreasing sequence
`f_j ∈ 𝓗_fin(X', (a + 2^{-j}, b + 2^{-j}))`. For `(a, b) = (1, 0)` these are the approximants
`Φ_j ∈ 𝓗_fin(X', (1 + 2^{-j}, 2^{-j}))` of `lem:pg-descent-weakly-psh`. -/
theorem IsPSH.exists_isFinFS_seq_dyadic [Countable k] (h : B.IsPSH ![(a : ℝ), (b : ℝ)] u) :
    ∃ f : ℕ → B.an → EReal,
      (∀ j, B.IsFinFS (a + ((2 : ℚ) ^ j)⁻¹) (b + ((2 : ℚ) ^ j)⁻¹) (f j)) ∧
        (∀ x, Antitone fun j => f j x) ∧ ∀ x, u x = ⨅ j, f j x := by
  rw [← ratCast_vecCons_two] at h
  exact FSSystem.IsPSH.exists_isFinFS_seq_dyadic (θ := ![a, b]) h

end ProjSubvariety.BlowupCenter

end EnvelopeProperty
