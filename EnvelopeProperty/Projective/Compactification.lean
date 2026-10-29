/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.CompactificationDivisibility
import EnvelopeProperty.Projective.Regularization
import EnvelopeProperty.Local.Regularizable

/-!
# The compactification lemma on `ℙⁿ`

Let `k` be a field with the trivial absolute value, `σ` a nonzero form of degree `e ≥ 1` in
`R = k[x₀, …, xₙ]`, `S = ℙⁿ_σ = Spec A_σ` the affine chart `{σ ≠ 0}` (`ProjBerk.chartAlg σ e`), and
`ι_σ : U_σ ≃ S^an` the chart of `EnvelopeProperty.Projective.Chart` (`ProjBerk.chartMap`, with
inverse `ProjBerk.chartInv`). This file proves Fang–Han–Xia, *The envelope property for unibranch
projective varieties*, Lemma 5.10 (`lem:compactification`) for `P = ℙⁿ`, `H = O(e)`, `s = σ`: the
correspondence between regularizable functions on `S` and `θ`-psh functions on `ℙⁿ`. Blueprint:
`bj22.tex`, subsection "The compactification lemma on projective space"
(`lem:bj-compactification-regularize`, `lem:bj-compactification-extend`,
`rmk:bj-compactification-full`). The class `c O(e)` is the rational number `c e`.

## Part (1) (`lem:bj-compactification-regularize`)

`ProjBerk.IsPSH.exists_chartFS`: for countable `k`, `c ∈ ℚ_{>0}` and `Φ ∈ PSH(c e)`, there are
affine FS functions `u_j ∈ FS(S)` decreasing to `Φ - c log|σ|` on `S^an` with `u_j + c log|σ|`
bounded; hence `(Φ - c log|σ|)|_{S^an} ∈ ℛ(S)` (`ProjBerk.IsPSH.isRegularizable_chart`). Following
the blueprint, `Φ` is the limit of a decreasing sequence `Φ_j ∈ H_ℚ(c e)`
(`ProjBerk.IsPSH.exists_finiteRatFS_seq_of_rat`, countable regularization), and
`Φ_j - c log|σ| = max{(e m)⁻¹ log|s_ℓ^e / σ^{d}| + λ_ℓ / m, c log|x^α/σ| - C_j, -C_j}` with
`Φ_j = m⁻¹ max_ℓ (log|s_ℓ| + λ_ℓ)`, `d = deg s_ℓ = m c e` and `-C_j ≤ min Φ_j`
(`ProjBerk.chartFSData`, `ProjBerk.eval_chartFSData`).

## Part (2) for regularizable functions (`lem:bj-compactification-extend`)

For `w : S^an → [-∞, ∞)` and `a ∈ ℝ`, `ProjBerk.chartExt σ e w a` is the function equal to
`w ∘ ι_σ + a log|σ|` on `U_σ` and to `-∞` on its complement.

* `ProjBerk.isPSH_chartExt_of_fs` (FS form): if `w` is the limit of a decreasing sequence
  `u_j ∈ FS(S)` with `u_j ≤ -α log|σ| + C_j` and `α < a`, `a > 0`, and `w ≢ -∞`, then
  `chartExt σ e w a ∈ PSH(a e)`. Each term `a_i log|τ_i/σ^{N_i}| + b_i` of `u_j` satisfies
  `log|τ_i| - N_i log|σ| ≤ -(α/a_i) log|σ| + C`, so the divisibility lemma
  (`ProjBerk.pow_floor_dvd_of_log_le`, `lem:bj-divisibility`) applied to `τ_i^r` gives
  `τ_i^r = σ^{N'_i} τ'_i`, and `a_i log|f_i| + a log|σ| = ε_i log|τ'_i| + δ_i log|σ| + b_i` with
  `ε_i, δ_i > 0` and `ε_i deg τ'_i + δ_i e = a e` (`ProjBerk.isPSH_chartExt_fsTerm`). The
  extension of `u_j + a log|σ|` is the maximum of these psh functions of class `a e` and of
  `a log|σ| + b_0`, and PSH2 (`ProjBerk.isPSH_of_antitone_seq`) passes to the limit.
* `ProjBerk.isPSH_chartExt` (`lem:bj-compactification-extend`): under `WuRegularization`
  (through its growth control `WuRegularization.growthControl`, FHX Lemma 5.11(5),
  `thm:import-growth-control`), if
  `w ∈ ℛ(S)`, `w ≤ -κ log|σ| + B₀` with `κ ∈ ℚ_{>0}`, and `a ∈ ℚ` with `a > κ`, then
  `chartExt σ e w a ∈ PSH(a e)`. The growth control is applied to `g = -κ log|σ| ∈ FS(S)`
  (`ProjBerk.growthFSData`) and a rational `c ∈ (1, a/κ)`. `WuRegularization` is an instance
  argument; the growth control needs `A_σ` integrally closed, which is also an instance argument
  (it is not formalized for general `σ`; see
  `EnvelopeProperty.Projective.CompactificationAffine` for `σ = xⱼ h`).

## Deviations from the blueprint

* In part (2) the projective Fubini–Study functions `Ψ_j` of the blueprint are not assembled
  into a single FS datum: each term is shown to be psh of class `a e` (sums, positive real
  multiples and constants of FS functions are psh), and `Ψ_j` is their finite maximum
  (`ProjBerk.isPSH_max_finset_sup`). Terms with `f_i = 0` are `-∞` and are absorbed by the
  constant term. The blueprint's auxiliary `κ' ∈ [κ, a)` is not needed (we take `κ' = κ`), and
  the integer `r` is used uniformly (when `N_i < α/a_i`, `⌊r (N_i - α/a_i)⌋₊ = 0`).
* Finiteness of the limit: the blueprint uses `φ(v_triv) = w(v_triv) > -∞`
  (`lem:reg-triv-finite`); here `w ≢ -∞` (part of `w ∈ ℛ(S)`) is transported directly, since
  `chartExt σ e w a (ι_σ⁻¹ y) = w y + a log|σ|(ι_σ⁻¹ y)` with `log|σ|` finite on `U_σ`.
* Part (2) is stated for real `a > 0` in the FS form, and needs `n ≥ 1` (for the
  divisibility lemma).
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter MvPolynomial

noncomputable section

namespace EnvelopeProperty

namespace ProjBerk

universe u

variable {k : Type u} [Field k] {n : ℕ} {σ : MvPolynomial (Fin (n + 1)) k} {e : ℕ}

/-! ### Preliminaries -/

/-- `log|s|` is an FS function of class `d` for a nonzero form `s` of degree `d`. -/
theorem isFS_logAbs {d : ℕ} {s : MvPolynomial (Fin (n + 1)) k} (hs : s.IsHomogeneous d)
    (hs0 : s ≠ 0) : IsFS (d : ℚ) (logAbs s) := by
  classical
  let D : FSData k n (d : ℚ) :=
    { m := 1
      m_pos := one_pos
      deg := d
      deg_eq := (by simp)
      terms := {(s, 0)}
      isHomogeneous := (fun t ht => by rw [Finset.mem_singleton.1 ht]; exact hs)
      exists_ne_zero := ⟨(s, 0), Finset.mem_singleton_self _, hs0⟩ }
  refine ⟨D, funext fun v => ?_⟩
  simp [D, FSData.eval]

/-- On `U_σ`, `log|σ|` is the real number `log |σ|_v`. -/
theorem logAbs_eq_coe_log {s : MvPolynomial (Fin (n + 1)) k} {v : ProjBerk k n}
    (hv : v.1.val s ≠ 0) : logAbs s v = ((Real.log (v.1.val s : ℝ) : ℝ) : EReal) := by
  rw [logAbs_def, ENNReal.log_of_nnreal hv]

theorem real_log_val_le_zero (s : MvPolynomial (Fin (n + 1)) k) (v : ProjBerk k n) :
    Real.log (v.1.val s : ℝ) ≤ 0 :=
  Real.log_nonpos (NNReal.coe_nonneg _) (by exact_mod_cast val_le_one v s)

theorem ereal_coe_mul_neg_coe_mul (x y z : ℝ) :
    (x : EReal) * (-(y : EReal) * (z : EReal)) = -((x * y : ℝ) : EReal) * (z : EReal) := by
  rw [← EReal.coe_neg, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_neg, ← EReal.coe_mul]
  congr 1
  ring

/-- A finite rational FS function has a rational lower bound. -/
theorem IsFiniteRatFS.exists_rat_le {a : ℚ} {φ : ProjBerk k n → EReal} (h : IsFiniteRatFS a φ) :
    ∃ q : ℚ, ∀ v, ((q : ℝ) : EReal) ≤ φ v := by
  obtain ⟨v₀, -, hv₀⟩ := isCompact_univ.exists_isMinOn ⟨triv, mem_univ _⟩
    h.isFS.continuous.continuousOn
  replace hv₀ : ∀ v, φ v₀ ≤ φ v := fun v => hv₀ (mem_univ v)
  obtain ⟨q, hq⟩ := exists_rat_lt (φ v₀).toReal
  refine ⟨q, fun v => le_trans ?_ (hv₀ v)⟩
  rw [← EReal.coe_toReal (h.isFS.ne_top v₀) (h.2 v₀)]
  exact_mod_cast hq.le

/-! ### Part (1): psh functions give regularizable functions on the chart -/

section Part1

variable (hσ : σ.IsHomogeneous e) (he : 0 < e)

open Classical in
/-- The affine FS datum on `A_σ` attached to a rational FS datum `D` of class `c e`
(`Φ_j = m⁻¹ max_ℓ (log|s_ℓ| + λ_ℓ)`) and a rational `q`: the terms
`((s_ℓ^e) / σ^{deg D}, (e m)⁻¹, λ_ℓ / m)` and `(x^α / σ, c, q)`, `|α| = e`, and the constant `q`
(`lem:bj-compactification-regularize`). -/
def chartFSData {c : ℚ} (hc : 0 < c) (D : FSData k n (c * e)) (hD : D.IsRational) (q : ℚ) :
    EnvelopeProperty.FSData k (chartAlg σ e) where
  terms := (D.terms.attach.image fun t => (chartMk σ e D.deg (t.1.1 ^ e), (1 : ℚ) / (e * D.m),
      Classical.choose (hD t.1 t.2) / D.m)) ∪
    (Finset.finsuppAntidiag Finset.univ e).image fun α => (chartGen σ e α, c, q)
  const := q
  pos t ht := by
    rcases Finset.mem_union.1 ht with ht | ht
    · obtain ⟨t', -, rfl⟩ := Finset.mem_image.1 ht
      have h1 : (0 : ℚ) < e := by exact_mod_cast he
      have h2 : (0 : ℚ) < D.m := by exact_mod_cast D.m_pos
      exact div_pos one_pos (mul_pos h1 h2)
    · obtain ⟨α, -, rfl⟩ := Finset.mem_image.1 ht
      exact hc
  gen := by
    refine eq_top_iff.2 ((adjoin_chartGen hσ).symm.le.trans (Algebra.adjoin_mono ?_))
    rintro _ ⟨α, hα, rfl⟩
    refine ⟨(chartGen σ e α, c, q), Finset.mem_union_right _ (Finset.mem_image.2
      ⟨α, mem_finsuppAntidiag_univ.2 hα, rfl⟩), rfl⟩

variable {hσ he}

/-- The value of `chartFSData`: if `q ≤ Φ_j`, then the affine FS function equals
`Φ_j - c log|σ|` on `S^an = U_σ` (`lem:bj-compactification-regularize`). -/
theorem eval_chartFSData {c : ℚ} (hc : 0 < c) (D : FSData k n (c * e)) (hD : D.IsRational)
    {q : ℚ} (hq : ∀ v, ((q : ℝ) : EReal) ≤ D.eval v) (y : Berk k (chartAlg σ e)) :
    (chartFSData hσ he hc D hD q).eval y =
      D.eval (chartInv σ e hσ he y) - ((c : ℝ) : EReal) * logAbs σ (chartInv σ e hσ he y) := by
  classical
  set v := chartInv σ e hσ he y with hv_def
  have hσv : v.1.val σ ≠ 0 := chartInv_val_ne_zero hσ he y
  have hy : chartMap σ e v hσv = y := chartMap_chartInv hσ he y
  set L := Real.log (v.1.val σ : ℝ) with hL_def
  have hL0 : L ≤ 0 := real_log_val_le_zero σ v
  have hLσ : logAbs σ v = (L : EReal) := logAbs_eq_coe_log hσv
  have hX : D.eval v - ((c : ℝ) : EReal) * logAbs σ v = D.eval v + ((-(c * L) : ℝ) : EReal) := by
    rw [hLσ, ← EReal.coe_mul, sub_eq_add_neg, ← EReal.coe_neg]
  rw [hX]
  have hm : (0 : ℝ) < D.m := by exact_mod_cast D.m_pos
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hdeg : (D.deg : ℝ) = D.m * (c * e) := by exact_mod_cast D.deg_eq
  -- the terms coming from `D`
  have hterm : ∀ t : D.terms, fsTerm (chartMk σ e D.deg (t.1.1 ^ e), (1 : ℚ) / (e * D.m),
      Classical.choose (hD t.1 t.2) / D.m) y =
      (((D.m : ℝ)⁻¹ : ℝ) : EReal) * termVal t.1 v + ((-(c * L) : ℝ) : EReal) := by
    intro t
    have hqt := Classical.choose_spec (hD t.1 t.2)
    set qt := Classical.choose (hD t.1 t.2)
    have hτ : (t.1.1 ^ e).IsHomogeneous (D.deg * e) := (D.isHomogeneous t.1 t.2).pow e
    rw [fsTerm_def, ← hy, logAbs_chartMap_chartMk v hσv hτ, termVal_def, hqt, logAbs_pow, hLσ]
    by_cases hs : v.1.val t.1.1 = 0
    · rw [(logAbs_eq_bot_iff _ v).2 hs]
      have h1 : ((e : ℕ) : EReal) * (⊥ : EReal) = ⊥ := by
        rw [← EReal.coe_natCast]; exact EReal.coe_mul_bot_of_pos he'
      have h2 : (0 : ℝ) < (((1 : ℚ) / (e * D.m) : ℚ) : ℝ) := by
        have : (0 : ℚ) < (1 : ℚ) / (e * D.m) := div_pos one_pos (mul_pos (by exact_mod_cast he)
          (by exact_mod_cast D.m_pos))
        exact_mod_cast this
      rw [h1, EReal.bot_sub, EReal.coe_mul_bot_of_pos h2, EReal.bot_add,
        EReal.bot_add, EReal.coe_mul_bot_of_pos (inv_pos.2 hm), EReal.bot_add]
    · rw [logAbs_eq_coe_log hs]
      set ls := Real.log (v.1.val t.1.1 : ℝ)
      rw [← EReal.coe_natCast, ← EReal.coe_natCast, ← EReal.coe_mul, ← EReal.coe_mul,
        ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_mul,
        ← EReal.coe_add]
      congr 1
      push_cast
      rw [hdeg]
      field_simp
      ring
  have hsup1 : ((D.terms.attach.image fun t => (chartMk σ e D.deg (t.1.1 ^ e), (1 : ℚ) / (e * D.m),
      Classical.choose (hD t.1 t.2) / D.m)).sup fun t => fsTerm t y) =
      D.eval v + ((-(c * L) : ℝ) : EReal) := by
    rw [Finset.sup_image]
    simp only [Function.comp_def, hterm]
    rw [← EnvelopeProperty.FSData.sup_add_coe, ← ereal_coe_mul_finset_sup (inv_pos.2 hm),
      Finset.sup_attach (f := fun t => termVal t v), FSData.eval_def]
  -- the generator terms are dominated
  have hsup2 : ((Finset.finsuppAntidiag Finset.univ e).image fun α =>
      (chartGen σ e α, c, q)).sup (fun t => fsTerm t y) ≤ D.eval v + ((-(c * L) : ℝ) : EReal) := by
    refine Finset.sup_le fun t ht => ?_
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 ht
    have h1 := logAbs_chartMap_chartGen_le v hσv (mem_finsuppAntidiag_univ.1 hα)
    rw [hy, hLσ] at h1
    rw [fsTerm_def]
    calc ((c : ℝ) : EReal) * Berk.logAbs (chartGen σ e α) y + ((q : ℝ) : EReal)
        ≤ ((c : ℝ) : EReal) * (-(L : EReal)) + ((q : ℝ) : EReal) := by
          gcongr
      _ = ((q : ℝ) : EReal) + ((-(c * L) : ℝ) : EReal) := by
          rw [add_comm, ← EReal.coe_neg, ← EReal.coe_mul]
          congr 2
          ring
      _ ≤ _ := by gcongr; exact hq v
  have hconst : ((q : ℝ) : EReal) ≤ D.eval v + ((-(c * L) : ℝ) : EReal) := by
    calc ((q : ℝ) : EReal) = ((q : ℝ) : EReal) + ((0 : ℝ) : EReal) := by simp
      _ ≤ D.eval v + ((-(c * L) : ℝ) : EReal) := by
          gcongr
          · exact hq v
          · have : 0 ≤ -(c * L) := by
              have : (0 : ℝ) ≤ c := by exact_mod_cast hc.le
              nlinarith
            exact_mod_cast this
  rw [EnvelopeProperty.FSData.eval_def]
  dsimp only [chartFSData]
  rw [Finset.sup_union, hsup1, max_eq_left hsup2, max_eq_right hconst]

/-- **Compactification, part (1)** (FHX Lemma 5.10(1), `lem:bj-compactification-regularize`).
Let `k` be countable, `σ` a form of degree `e ≥ 1`, `c ∈ ℚ_{>0}` and `Φ ∈ PSH(c e)`. There are
affine FS functions `u_j ∈ FS(S)` on the chart `S = Spec A_σ` decreasing to `Φ - c log|σ|`
(transported to `S^an` by `ι_σ⁻¹`), with each `u_j + c log|σ|` bounded. -/
theorem IsPSH.exists_chartFS [Countable k] (hσ : σ.IsHomogeneous e) (he : 0 < e) {c : ℚ}
    (hc : 0 < c) {Φ : ProjBerk k n → EReal} (hΦ : IsPSH ((c : ℝ) * e) Φ) :
    ∃ g : ℕ → EnvelopeProperty.FSData k (chartAlg σ e),
      (∀ y, Antitone fun j => (g j).eval y) ∧
      (∀ y, Φ (chartInv σ e hσ he y) - ((c : ℝ) : EReal) * logAbs σ (chartInv σ e hσ he y) =
        ⨅ j, (g j).eval y) ∧
      ∀ j, ∃ C : ℝ, ∀ y,
        ((-C : ℝ) : EReal) ≤ (g j).eval y + ((c : ℝ) : EReal) * logAbs σ (chartInv σ e hσ he y) ∧
        (g j).eval y + ((c : ℝ) : EReal) * logAbs σ (chartInv σ e hσ he y) ≤ (C : EReal) := by
  have hce : (0 : ℚ) < c * e := mul_pos hc (by exact_mod_cast he)
  have hΦ' : IsPSH ((c * e : ℚ) : ℝ) Φ := by push_cast; exact hΦ
  obtain ⟨φ, hφ, hanti, -, hinf⟩ := hΦ'.exists_finiteRatFS_seq_of_rat hce
  choose D hD hφD using fun j => (hφ j).1
  choose q hq using fun j => (hφ j).exists_rat_le
  have hqD : ∀ j v, ((q j : ℝ) : EReal) ≤ (D j).eval v := fun j v => by
    rw [← hφD j]; exact hq j v
  -- `Φ_j - c log|σ| = Φ_j + K(y)` with `K` real
  have hK : ∀ y, ∃ K : ℝ, ∀ x : EReal, x - ((c : ℝ) : EReal) * logAbs σ (chartInv σ e hσ he y) =
      x + (K : EReal) ∧ x - ((c : ℝ) : EReal) * logAbs σ (chartInv σ e hσ he y) +
        ((c : ℝ) : EReal) * logAbs σ (chartInv σ e hσ he y) = x := fun y => by
    have hσv := chartInv_val_ne_zero hσ he y
    refine ⟨-(c * Real.log ((chartInv σ e hσ he y).1.val σ : ℝ)), fun x => ⟨?_, ?_⟩⟩
    · rw [logAbs_eq_coe_log hσv, ← EReal.coe_mul, sub_eq_add_neg, ← EReal.coe_neg]
    · rw [logAbs_eq_coe_log hσv, ← EReal.coe_mul, sub_eq_add_neg, ← EReal.coe_neg]
      exact ereal_add_neg_add_coe x _
  refine ⟨fun j => chartFSData hσ he hc (D j) (hD j) (q j), fun y j j' hjj' => ?_, fun y => ?_,
    fun j => ?_⟩
  · dsimp only
    rw [eval_chartFSData hc _ _ (hqD j) y, eval_chartFSData hc _ _ (hqD j') y, ← hφD, ← hφD]
    obtain ⟨K, hK⟩ := hK y
    rw [(hK _).1, (hK _).1]
    exact add_le_add_left (hanti _ hjj') _
  · obtain ⟨K, hK⟩ := hK y
    simp only [eval_chartFSData hc _ _ (hqD _) y, ← hφD, (hK _).1]
    rw [iInf_add_coe_of_antitone (fun _ _ h => hanti _ h) ((hφ 0).isFS.ne_top _), ← hinf]
  · obtain ⟨Cup, hCup⟩ : ∃ C : ℝ, ∀ v, φ j v ≤ (C : EReal) :=
      ⟨(φ j triv).toReal, fun v => by
        rw [EReal.coe_toReal ((hφ j).isFS.ne_top _) ((hφ j).2 _)]
        exact (hφ j).isFS.antitone (triv_le v)⟩
    refine ⟨Max.max Cup (-(q j : ℝ)), fun y => ?_⟩
    obtain ⟨K, hK⟩ := hK y
    rw [eval_chartFSData hc _ _ (hqD j) y, ← hφD, (hK _).2]
    refine ⟨le_trans ?_ (hq j _), (hCup _).trans (by exact_mod_cast le_max_left _ _)⟩
    have : -(Max.max Cup (-(q j : ℝ))) ≤ (q j : ℝ) := by
      have := le_max_right Cup (-(q j : ℝ))
      linarith
    exact_mod_cast this

/-- **Compactification, part (1)**, regularizability (FHX Lemma 5.10(1),
`lem:bj-compactification-regularize`): for countable `k`, a nonzero form `σ` of degree `e ≥ 1`,
`c ∈ ℚ_{>0}` and `Φ ∈ PSH(c e)`, the restriction `(Φ - c log|σ|)|_{S^an}` is regularizable on the
chart `S = Spec A_σ`. -/
theorem IsPSH.isRegularizable_chart [Countable k] (hσ : σ.IsHomogeneous e) (he : 0 < e)
    (hσ0 : σ ≠ 0) {c : ℚ} (hc : 0 < c) {Φ : ProjBerk k n → EReal}
    (hΦ : IsPSH ((c : ℝ) * e) Φ) :
    IsRegularizable fun y => Φ (chartInv σ e hσ he y) -
      ((c : ℝ) : EReal) * logAbs σ (chartInv σ e hσ he y) := by
  obtain ⟨g, hanti, hinf, -⟩ := hΦ.exists_chartFS hσ he hc
  refine ⟨⟨chartMap σ e triv (triv_val_ne_zero hσ0), ?_⟩, g, hanti, hinf⟩
  dsimp only
  rw [chartInv_chartMap, logAbs_triv_of_ne_zero hσ0, mul_zero, sub_zero]
  exact hΦ.apply_triv_ne_bot

end Part1

/-! ### Part (2): extension of regularizable functions -/

section Part2

variable (σ e) in
open Classical in
/-- The function on `(ℙⁿ)^an` equal to `w ∘ ι_σ + a log|σ|` on `U_σ = {|σ| ≠ 0}` and to `-∞` on
its complement (FHX Lemma 5.10(2), `lem:bj-compactification-extend`). -/
def chartExt (w : Berk k (chartAlg σ e) → EReal) (a : ℝ) (v : ProjBerk k n) : EReal :=
  if hv : v.1.val σ ≠ 0 then w (chartMap σ e v hv) + (a : EReal) * logAbs σ v else ⊥

theorem chartExt_of_ne_zero (w : Berk k (chartAlg σ e) → EReal) (a : ℝ) {v : ProjBerk k n}
    (hv : v.1.val σ ≠ 0) : chartExt σ e w a v = w (chartMap σ e v hv) + (a : EReal) * logAbs σ v :=
  dif_pos hv

theorem chartExt_of_eq_zero (w : Berk k (chartAlg σ e) → EReal) (a : ℝ) {v : ProjBerk k n}
    (hv : v.1.val σ = 0) : chartExt σ e w a v = ⊥ :=
  dif_neg (not_not.2 hv)

theorem chartExt_chartInv (hσ : σ.IsHomogeneous e) (he : 0 < e)
    (w : Berk k (chartAlg σ e) → EReal) (a : ℝ) (y : Berk k (chartAlg σ e)) :
    chartExt σ e w a (chartInv σ e hσ he y) =
      w y + (a : EReal) * logAbs σ (chartInv σ e hσ he y) := by
  rw [chartExt_of_ne_zero w a (chartInv_val_ne_zero hσ he y), chartMap_chartInv]

/-- The extension of a constant `b`: `a log|σ| + b`, of class `a e`. -/
theorem isPSH_chartExt_const (hσ : σ.IsHomogeneous e) (hσ0 : σ ≠ 0) {a : ℝ} (ha : 0 < a)
    (b : ℝ) : IsPSH (a * e) (chartExt σ e (fun _ => (b : EReal)) a) := by
  have h : chartExt σ e (fun _ => (b : EReal)) a = fun v => (a : EReal) * logAbs σ v + b := by
    funext v
    by_cases hv : v.1.val σ = 0
    · rw [chartExt_of_eq_zero _ _ hv, (logAbs_eq_bot_iff σ v).2 hv, EReal.coe_mul_bot_of_pos ha,
        EReal.bot_add]
    · rw [chartExt_of_ne_zero _ _ hv, add_comm]
  rw [h]
  have := ((isFS_logAbs hσ hσ0).isPSH.smul ha).add_const b
  simpa only [Rat.cast_natCast] using this

/-- A finite maximum `max(B, maxᵢ Fᵢ)` is `θ`-psh if all `max(B, Fᵢ)` are. -/
theorem isPSH_max_finset_sup {θ : ℝ} {ι : Type*} (s : Finset ι) {B : ProjBerk k n → EReal}
    (hB : IsPSH θ B) {F : ι → ProjBerk k n → EReal}
    (hF : ∀ i ∈ s, IsPSH θ fun v => max (B v) (F i v)) :
    IsPSH θ fun v => max (B v) (s.sup fun i => F i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty, max_bot_right] using hB
  | insert i s hi ih =>
    simp only [Finset.sup_insert]
    have h := (hF i (Finset.mem_insert_self i s)).max
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))
    have e : (fun v => max (B v) (max (F i v) (s.sup fun i => F i v))) =
        fun v => max (max (B v) (F i v)) (max (B v) (s.sup fun i => F i v)) := by
      funext v
      exact sup_sup_distrib_left _ _ _
    rw [e]
    exact h

/-- **The divisibility step** of `lem:bj-compactification-extend`: if a term `a_t log|f| + b_t`
of an affine FS function on `S`, with `f ≠ 0`, satisfies `a_t log|f| + b_t ≤ -α log|σ| + C` on
`S^an`, and `α < a`, then its extension `chartExt σ e (fsTerm t) a` is psh of class `a e`. Writing
`f = τ/σ^N`, the divisibility lemma applied to `τ^r` gives `τ^r = σ^{N'} τ'` and the extension is
`(a_t/r) log|τ'| + (a - a_t N + a_t N'/r) log|σ| + b_t`, with positive coefficients for `r`
large. -/
theorem isPSH_chartExt_fsTerm (hn : n ≠ 0) (hσ : σ.IsHomogeneous e) (he : 0 < e) (hσ0 : σ ≠ 0)
    {t : chartAlg σ e × ℚ × ℚ} (ht : 0 < t.2.1) (hf : t.1 ≠ 0) {α a C : ℝ} (hαa : α < a)
    (hbound : ∀ y, fsTerm t y ≤ -(α : EReal) * logAbs σ (chartInv σ e hσ he y) + (C : EReal)) :
    IsPSH (a * e) (chartExt σ e (fsTerm t) a) := by
  obtain ⟨f, a₁, b₁⟩ := t
  simp only at ht hf
  obtain ⟨N, τ, hτ, rfl⟩ := exists_eq_chartMk hσ f
  have hτ0 : τ ≠ 0 := by rintro rfl; exact hf (chartMk_zero N)
  have hat : (0 : ℝ) < a₁ := by exact_mod_cast ht
  -- the growth bound in real form
  have hreal : ∀ v : ProjBerk k n, v.1.val σ ≠ 0 → v.1.val τ ≠ 0 →
      (a₁ : ℝ) * (Real.log (v.1.val τ) - N * Real.log (v.1.val σ)) + b₁ ≤
        -α * Real.log (v.1.val σ) + C := by
    intro v hσv hτv
    have h1 := hbound (chartMap σ e v hσv)
    rw [chartInv_chartMap, fsTerm_def, logAbs_chartMap_chartMk v hσv hτ, logAbs_eq_coe_log hσv,
      logAbs_eq_coe_log hτv] at h1
    exact_mod_cast h1
  -- the integer `r`
  have haα : 0 < a - α := sub_pos.2 hαa
  obtain ⟨r, hr⟩ := exists_nat_gt ((a₁ : ℝ) / (a - α))
  have hr0 : (0 : ℝ) < r := lt_trans (div_pos hat haα) hr
  have hr0' : r ≠ 0 := by rintro rfl; simp at hr0
  have hrat : (a₁ : ℝ) / r < a - α := by
    rw [div_lt_iff₀ hr0]
    rw [div_lt_iff₀ haα] at hr
    linarith
  -- divisibility
  have hdiv : σ ^ ⌊((N * r : ℕ) : ℝ) - r * α / a₁⌋₊ ∣ τ ^ r := by
    refine pow_floor_dvd_of_log_le (C := r * (C - b₁) / a₁) hn hσ hσ0 (hτ.pow r)
      fun v hσv hτv => ?_
    have hτv' : v.1.val τ ≠ 0 := fun h0 => hτv (by rw [map_pow, h0, zero_pow hr0'])
    have h1 := hreal v hσv hτv'
    rw [map_pow, NNReal.coe_pow, Real.log_pow]
    refine le_of_mul_le_mul_left ?_ hat
    have key := mul_le_mul_of_nonneg_left h1 hr0.le
    have e1 : (a₁ : ℝ) * (-(r * α / a₁) * Real.log (v.1.val σ) + r * (C - b₁) / a₁) =
        r * (-α * Real.log (v.1.val σ) + C) - r * b₁ := by
      field_simp
      ring
    rw [e1]
    push_cast
    nlinarith [key]
  set N' := ⌊((N * r : ℕ) : ℝ) - r * α / a₁⌋₊ with hN'
  obtain ⟨hle, τ', hτ', hfac⟩ :=
    exists_isHomogeneous_eq_mul_of_dvd (hσ.pow N') (hτ.pow r) (pow_ne_zero r hτ0) hdiv
  have hτ'0 : τ' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hfac
    exact pow_ne_zero r hτ0 hfac
  have hD' : ((N * e * r - e * N' : ℕ) : ℝ) = N * e * r - e * N' := by
    rw [Nat.cast_sub hle]
    push_cast
    ring
  -- the coefficients `ε = a_t / r` and `δ = a - a_t N + a_t N' / r`
  have hε : 0 < (a₁ : ℝ) / r := div_pos hat hr0
  have hδ : 0 < a - a₁ * N + a₁ * N' / r := by
    rcases le_or_gt 0 (((N * r : ℕ) : ℝ) - r * α / a₁) with h | h
    · have h1 : ((N * r : ℕ) : ℝ) - r * α / a₁ < N' + 1 := Nat.lt_floor_add_one _
      have h2 : 0 < ((a₁ : ℝ) / r) * (N' - (N * r - r * α / a₁ - 1)) := by
        refine mul_pos hε ?_
        push_cast at h1
        linarith
      have e2 : ((a₁ : ℝ) / r) * (N' - (N * r - r * α / a₁ - 1)) =
          a₁ * N' / r - a₁ * N + α + a₁ / r := by
        field_simp
        ring
      linarith
    · have hN0 : N' = 0 := Nat.floor_eq_zero.2 (h.trans one_pos)
      have h2 : ((a₁ : ℝ) / r) * (N * r - r * α / a₁) < 0 := by
        refine mul_neg_of_pos_of_neg hε ?_
        push_cast at h
        linarith
      have e2 : ((a₁ : ℝ) / r) * (N * r - r * α / a₁) = a₁ * N - α := by
        field_simp
      rw [hN0, Nat.cast_zero, mul_zero, zero_div, add_zero]
      linarith
  have hclass : (a₁ : ℝ) / r * ((N * e * r - e * N' : ℕ) : ℝ) +
      (a - a₁ * N + a₁ * N' / r) * e = a * e := by
    rw [hD']
    field_simp
    ring
  -- the psh function
  have hψ : IsPSH (a * e) fun v => (((a₁ : ℝ) / r : ℝ) : EReal) * logAbs τ' v +
      ((a - a₁ * N + a₁ * N' / r : ℝ) : EReal) * logAbs σ v + ((b₁ : ℝ) : EReal) := by
    have h1 := (((isFS_logAbs hτ' hτ'0).isPSH.smul hε).add
      ((isFS_logAbs hσ hσ0).isPSH.smul hδ)).add_const b₁
    rw [Rat.cast_natCast, Rat.cast_natCast, hclass] at h1
    exact h1
  convert hψ using 1
  funext v
  by_cases hσv : v.1.val σ = 0
  · rw [chartExt_of_eq_zero _ _ hσv, (logAbs_eq_bot_iff σ v).2 hσv, EReal.coe_mul_bot_of_pos hδ,
      EReal.add_bot, EReal.bot_add]
  rw [chartExt_of_ne_zero _ _ hσv, fsTerm_def, logAbs_chartMap_chartMk v hσv hτ]
  have hfacv : v.1.val τ ^ r = v.1.val σ ^ N' * v.1.val τ' := by
    rw [← map_pow, hfac, map_mul, map_pow]
  by_cases hτv : v.1.val τ = 0
  · have hτ'v : v.1.val τ' = 0 := by
      rw [hτv, zero_pow hr0'] at hfacv
      exact (mul_eq_zero.1 hfacv.symm).resolve_left (pow_ne_zero _ hσv)
    rw [(logAbs_eq_bot_iff τ v).2 hτv, (logAbs_eq_bot_iff τ' v).2 hτ'v]
    simp only [EReal.bot_sub, EReal.coe_mul_bot_of_pos hat, EReal.coe_mul_bot_of_pos hε,
      EReal.bot_add]
  have hτ'v : v.1.val τ' ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hfacv
    exact pow_ne_zero r hτv hfacv
  have hrel : (r : ℝ) * Real.log (v.1.val τ) =
      N' * Real.log (v.1.val σ) + Real.log (v.1.val τ') := by
    have h1 := congrArg (fun x : ℝ≥0 => Real.log (x : ℝ)) hfacv
    simp only [NNReal.coe_pow, NNReal.coe_mul] at h1
    rw [Real.log_pow, Real.log_mul (pow_ne_zero _ (by exact_mod_cast hσv))
      (by exact_mod_cast hτ'v), Real.log_pow] at h1
    exact h1
  rw [logAbs_eq_coe_log hσv, logAbs_eq_coe_log hτv, logAbs_eq_coe_log hτ'v]
  have hLτ' : Real.log (v.1.val τ' : ℝ) =
      r * Real.log (v.1.val τ) - N' * Real.log (v.1.val σ) := by linarith
  have key : (a₁ : ℝ) * (Real.log (v.1.val τ) - N * Real.log (v.1.val σ)) + b₁ +
      a * Real.log (v.1.val σ) = a₁ / r * Real.log (v.1.val τ') +
        (a - a₁ * N + a₁ * N' / r) * Real.log (v.1.val σ) + b₁ := by
    rw [hLτ']
    field_simp
    ring
  exact_mod_cast key

/-- The extension of an affine FS function is the maximum of the extensions of its constant and of
its terms. -/
theorem chartExt_eval (g : EnvelopeProperty.FSData k (chartAlg σ e)) (a : ℝ) :
    chartExt σ e g.eval a = fun v => max (chartExt σ e (fun _ => ((g.const : ℝ) : EReal)) a v)
      (g.terms.sup fun t => chartExt σ e (fsTerm t) a v) := by
  funext v
  by_cases hv : v.1.val σ = 0
  · simp only [chartExt_of_eq_zero _ _ hv, Finset.sup_bot, max_self]
  · simp only [chartExt_of_ne_zero _ _ hv]
    rw [EnvelopeProperty.FSData.eval_def, ← max_add_add_right, EnvelopeProperty.FSData.sup_add_coe]

/-- **Compactification, part (2)**, FS form (`lem:bj-compactification-extend`): let
`n ≥ 1`, `σ ≠ 0` a form of degree `e ≥ 1`, and `w` the limit of a decreasing sequence of affine FS
functions `u_j` on `S = Spec A_σ` with `u_j ≤ -α log|σ| + C_j`, `w ≢ -∞`. For every real
`a > max(α, 0)`, the function equal to `w + a log|σ|` on `S^an = U_σ` and to `-∞` elsewhere is
psh of class `a e`. -/
theorem isPSH_chartExt_of_fs (hn : n ≠ 0) (hσ : σ.IsHomogeneous e) (he : 0 < e) (hσ0 : σ ≠ 0)
    {g : ℕ → EnvelopeProperty.FSData k (chartAlg σ e)} (hanti : ∀ y, Antitone fun j => (g j).eval y)
    {w : Berk k (chartAlg σ e) → EReal} (hw : ∀ y, w y = ⨅ j, (g j).eval y) (hfin : ∃ y, w y ≠ ⊥)
    {α a : ℝ} (ha : 0 < a) (hαa : α < a)
    (hgrowth : ∀ j, ∃ C : ℝ, ∀ y,
      (g j).eval y ≤ -(α : EReal) * logAbs σ (chartInv σ e hσ he y) + (C : EReal)) :
    IsPSH (a * e) (chartExt σ e w a) := by
  have hΨ : ∀ j, IsPSH (a * e) (chartExt σ e (g j).eval a) := by
    intro j
    obtain ⟨C, hC⟩ := hgrowth j
    rw [chartExt_eval]
    refine isPSH_max_finset_sup _ (isPSH_chartExt_const hσ hσ0 ha _) fun t ht => ?_
    by_cases hf : t.1 = 0
    · have h0 : chartExt σ e (fsTerm t) a = fun _ => ⊥ := by
        funext v
        by_cases hv : v.1.val σ = 0
        · exact chartExt_of_eq_zero _ _ hv
        · rw [chartExt_of_ne_zero _ _ hv, fsTerm_eq_bot ((g j).pos t ht) (by rw [hf, map_zero]),
            EReal.bot_add]
      rw [h0]
      simpa only [max_bot_right] using isPSH_chartExt_const hσ hσ0 ha _
    · exact (isPSH_chartExt_const hσ hσ0 ha _).max (isPSH_chartExt_fsTerm hn hσ he hσ0
        ((g j).pos t ht) hf hαa fun y => ((g j).fsTerm_le_eval ht y).trans (hC y))
  refine isPSH_of_antitone_seq (θ := fun _ => a * e) tendsto_const_nhds hΨ
    (fun v j j' hjj' => ?_) (fun v => ?_) ?_
  · dsimp only
    by_cases hv : v.1.val σ = 0
    · rw [chartExt_of_eq_zero _ _ hv, chartExt_of_eq_zero _ _ hv]
    · rw [chartExt_of_ne_zero _ _ hv, chartExt_of_ne_zero _ _ hv]
      exact add_le_add_left (hanti _ hjj') _
  · by_cases hv : v.1.val σ = 0
    · simp only [chartExt_of_eq_zero _ _ hv, iInf_const]
    · simp only [chartExt_of_ne_zero _ _ hv]
      rw [logAbs_eq_coe_log hv, ← EReal.coe_mul, iInf_add_coe_of_antitone (hanti _)
        ((g 0).eval_ne_top _), hw]
  · obtain ⟨y, hy⟩ := hfin
    refine ⟨chartInv σ e hσ he y, ?_⟩
    rw [chartExt_chartInv, logAbs_eq_coe_log (chartInv_val_ne_zero hσ he y), ← EReal.coe_mul]
    exact EReal.add_ne_bot_iff.2 ⟨hy, EReal.coe_ne_bot _⟩

/-- The affine FS function `max{0, max_{|α| = e} κ log|x^α / σ|}` on `S = Spec A_σ`, equal to
`-κ log|σ|` on `S^an = U_σ` (`eval_growthFSData`). -/
def growthFSData (hσ : σ.IsHomogeneous e) {κ : ℚ} (hκ : 0 < κ) :
    EnvelopeProperty.FSData k (chartAlg σ e) := by
  classical
  exact
  { terms := (Finset.finsuppAntidiag Finset.univ e).image fun α => (chartGen σ e α, κ, 0)
    const := 0
    pos := fun t ht => by
      obtain ⟨α, -, rfl⟩ := Finset.mem_image.1 ht
      exact hκ
    gen := by
      refine eq_top_iff.2 ((adjoin_chartGen hσ).symm.le.trans (Algebra.adjoin_mono ?_))
      rintro _ ⟨α, hα, rfl⟩
      exact ⟨(chartGen σ e α, κ, 0), Finset.mem_image.2 ⟨α, mem_finsuppAntidiag_univ.2 hα, rfl⟩,
        rfl⟩ }

theorem eval_growthFSData (hσ : σ.IsHomogeneous e) (he : 0 < e) {κ : ℚ} (hκ : 0 < κ)
    (y : Berk k (chartAlg σ e)) :
    (growthFSData hσ hκ).eval y = -((κ : ℝ) : EReal) * logAbs σ (chartInv σ e hσ he y) := by
  classical
  set v := chartInv σ e hσ he y with hv_def
  have hσv : v.1.val σ ≠ 0 := chartInv_val_ne_zero hσ he y
  have hy : chartMap σ e v hσv = y := chartMap_chartInv hσ he y
  have hL0 : Real.log (v.1.val σ : ℝ) ≤ 0 := real_log_val_le_zero σ v
  have hκ' : (0 : ℝ) < κ := by exact_mod_cast hκ
  rw [EnvelopeProperty.FSData.eval_def]
  dsimp only [growthFSData]
  rw [Finset.sup_image]
  simp only [Function.comp_def, fsTerm_def, Rat.cast_zero, EReal.coe_zero, add_zero]
  rw [← EnvelopeProperty.FSData.coe_mul_sup _ _ hκ', ← hy, sup_logAbs_chartMap_chartGen v hσv,
    logAbs_eq_coe_log hσv, ← EReal.coe_neg, ← EReal.coe_mul, ← EReal.coe_neg, ← EReal.coe_mul,
    max_eq_right (by exact_mod_cast (mul_nonneg hκ'.le (neg_nonneg.2 hL0)))]
  congr 1
  ring

/-- **Compactification, part (2), for regularizable functions** (FHX Lemma 5.10(2) for
`w ∈ ℛ(S)`, `lem:bj-compactification-extend`), under `WuRegularization` (through
`WuRegularization.growthControl`, FHX Lemma 5.11(5), `thm:import-growth-control`). Let `k` be algebraically closed, `n ≥ 1`, `σ ≠ 0` a form of degree
`e ≥ 1` with `A_σ` integrally closed, `w ∈ ℛ(S)` on the chart `S = Spec A_σ`, and `κ ∈ ℚ_{>0}`,
`B₀ ∈ ℝ` with `w ≤ -κ log|σ| + B₀` on `S^an`. For every rational `a > κ`, the function equal to
`w + a log|σ|` on `S^an = U_σ` and to `-∞` elsewhere lies in `PSH(a e)`. -/
theorem isPSH_chartExt [IsAlgClosed k] [WuRegularization.{u, u} k] (hn : n ≠ 0)
    (hσ : σ.IsHomogeneous e) (he : 0 < e) (hσ0 : σ ≠ 0) [IsIntegrallyClosed (chartAlg σ e)]
    {w : Berk k (chartAlg σ e) → EReal} (hw : IsRegularizable w) {κ : ℚ} (hκ : 0 < κ) {B₀ : ℝ}
    (hwB : ∀ y, w y ≤ -((κ : ℝ) : EReal) * logAbs σ (chartInv σ e hσ he y) + (B₀ : EReal))
    {a : ℚ} (ha : κ < a) : IsPSH ((a : ℝ) * e) (chartExt σ e w a) := by
  have := Berk.isDomain_localizationAway hσ0
  have := finiteType_chartAlg hσ
  obtain ⟨c, hc1, hca⟩ := exists_rat_btwn (show (1 : ℚ) < a / κ from (one_lt_div hκ).2 ha)
  have hcκ : c * κ < a := (lt_div_iff₀ hκ).1 hca
  obtain ⟨h, hanti, hinf, hbd⟩ := WuRegularization.growthControl (chartAlg σ e) w
    (growthFSData hσ hκ) B₀ hw (fun y => by rw [eval_growthFSData hσ he]; exact hwB y) c hc1
  have ha0 : (0 : ℝ) < a := by exact_mod_cast hκ.trans ha
  refine isPSH_chartExt_of_fs hn hσ he hσ0 hanti hinf hw.1 (α := ((c * κ : ℚ) : ℝ)) ha0
    (by exact_mod_cast hcκ) fun j => ?_
  obtain ⟨C, hC⟩ := hbd j
  refine ⟨C, fun y => (hC y).trans_eq ?_⟩
  rw [eval_growthFSData hσ he, logAbs_eq_coe_log (chartInv_val_ne_zero hσ he y),
    ereal_coe_mul_neg_coe_mul, Rat.cast_mul]

end Part2

end ProjBerk

end EnvelopeProperty
