/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.FSSystemC

/-!
# The multiplicative diagonal lemma

This file implements the blueprint nodes `lem:nn-mult-diagonal` and `cor:nn-sandwich-diagonal` of
the chapter `nonnef.tex` (`sec:nonnef`, "Classes outside the model-nef cone") of the formalization
of Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX).

## Context

FHX uses the decreasing-limit property PSH2 (Boucksom–Jonsson, *Global pluripotential theory over
a trivially valued field* (BJ22), Theorem 4.5) at possibly non-nef classes. BJ22
derives PSH2 from its Lemma 4.6, whose statement is false for families of functions
taking the value `-∞` (`prop:nn-bj-lemma46-false`); the repairs in `Global/FSSystemC.lean`
(`FSSystemC.isPSH_of_antitone`) need the limit class to lie in the closure of the semiample cone.
The multiplicative diagonal lemma replaces the additive slack `ε` of BJ22's diagonal argument by a
factor `1 - κ`: approximants are compared up to a factor, which makes sense *including at the
poles*, where an additive constant does not help.

## Main statements

Let `(K, ⋆, 𝓗)` be a Fubini–Study system with semiample cone (`EnvelopeProperty.FSSystemC`). Only
the rational scaling axiom (FS4), `FSSystemC.IsFS.smul`, is used; no compactness of `K` and no
condition on the limit class `θ` are needed.

* `EnvelopeProperty.exists_antitone_net_of_multCompatible` (`lem:nn-mult-diagonal`, net form,
  independent of the Fubini–Study system): let `(uᵢ)_{i ∈ I}` be a net of functions
  `K → [-∞, 0]` on a directed set (decreasing in the applications; this is not needed),
  `θᵢ → θ` in `ℝ^r`, and for each `i` let `𝒜ᵢ` be a set of pairs `(a, f)`,
  `a ∈ ℚ^r`, with `uᵢ ≤ f ≤ 0`, such that
  (A) for all `i`, `x`, real `M > uᵢ(x)` and `η > 0` some `(a, f) ∈ 𝒜ᵢ` has `|a - θᵢ| < η` and
      `f(x) < M`;
  (B) for all `i₁, i₂ ≤ i`, `(a_ν, f_ν) ∈ 𝒜_{i_ν}`, rational `γ ∈ (0, 1)` and `η > 0` some
      `(a, f) ∈ 𝒜ᵢ` has `|a - θᵢ| < η`, `f ≤ γ f₁` and `f ≤ γ f₂`.
  Then `u = infᵢ uᵢ` is the pointwise limit of a decreasing net of functions `(1 - κ) f` with
  `(a, f) ∈ 𝒜ᵢ`, `κ ∈ ℚ ∩ (0, 1)`, whose classes `(1 - κ) a` tend to `θ`. The index set is the
  set of quadruples `(i, a, f, κ)` with `|a - θᵢ| < κ` (`EnvelopeProperty.MultDiagonalIndex`),
  preordered by `i ≤ i'`, `κ' ≤ κ` and `(1 - κ') f' ≤ (1 - κ) f` on `K`.
* `EnvelopeProperty.FSSystemC.isPSH_of_multCompatible` (`lem:nn-mult-diagonal`): if moreover
  every `f` with `(a, f) ∈ 𝒜ᵢ` lies in `𝓗(a)` and `u ≢ -∞`, then `u ∈ PSH(θ)`.
* `EnvelopeProperty.FSSystemC.isPSH_of_sandwich` (`cor:nn-sandwich-diagonal`): if `uᵢ ≤ 0` is a
  decreasing net, `θᵢ → θ`, `u = infᵢ uᵢ ≢ -∞`, and for every `i`, rational `δ ∈ (0, 1)` and
  `η > 0` there are `a ∈ ℚ^r` with `|a - θᵢ| < η` and `f ∈ 𝓗(a)` with `uᵢ ≤ f ≤ (1 - δ) uᵢ`,
  then `u ∈ PSH(θ)`. `EnvelopeProperty.FSSystemC.isPSH_of_sandwich_seq` is the case of
  sequences.

Here `|·|` is the sup norm on `ℝ^r`, i.e. the distance of `Fin r → ℝ`.

## Deviations from the blueprint

* `lem:nn-mult-diagonal` assumes that `(uᵢ)` is decreasing and `u = limᵢ uᵢ`. The proof never
  uses the monotonicity (only `u ≤ uᵢ` and: `u(x) < M'` implies `u_{i₀}(x) < M'` for some `i₀`,
  which hold for `u = infᵢ uᵢ`), so the Lean statements assume neither and take `u = infᵢ uᵢ`.
  Monotonicity is used in `cor:nn-sandwich-diagonal`, to verify (B).
* In the proof of `cor:nn-sandwich-diagonal` we take for `𝒜ᵢ` all pairs `(a, f)` with
  `f ∈ 𝓗(a)` and `uᵢ ≤ f ≤ 0` (instead of those with `uᵢ ≤ f ≤ (1 - δ) uᵢ` for some `δ`);
  hypothesis (B) is verified by the same chain `f ≤ γ uᵢ ≤ γ u_{i_ν} ≤ γ f_ν`.
* The convergence of the classes is proved with filters (`(1 - κ_d) a_d → 1 • θ`, using
  `|a_d - θ_{i_d}| < κ_d → 0` and `θ_{i_d} → θ`) instead of the explicit bound
  `|(1 - κ) a - θ| ≤ |a - θᵢ| + κ|a| + |θᵢ - θ|`.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u v

/-! ### Auxiliary facts on `EReal` -/

/-- `x ≤ s x` for `0 < s ≤ 1` and `x ≤ 0` in `EReal`. -/
theorem ereal_le_coe_mul_of_nonpos {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {x : EReal} (hx : x ≤ 0) :
    x ≤ (s : EReal) * x := by
  have := ProjBerk.ereal_coe_mul_le_of_nonpos hs hs1 hx
  rwa [EReal.coe_one, one_mul] at this

/-- `s x ≤ 0` for `0 ≤ s` and `x ≤ 0` in `EReal`. -/
theorem ereal_coe_mul_nonpos_of_nonpos {s : ℝ} (hs : 0 ≤ s) {x : EReal} (hx : x ≤ 0) :
    (s : EReal) * x ≤ 0 := by
  simpa only [mul_zero] using ProjBerk.ereal_coe_mul_monotone hs hx

/-- **Choice of the multiplicative slack.** For reals `m' < m` there is a rational `κ ∈ (0, 1)`
with `(1 - κ) y < m` for every `y ∈ EReal` with `y < m'`. -/
theorem exists_rat_one_sub_mul_lt {m' m : ℝ} (h : m' < m) :
    ∃ κ : ℚ, 0 < κ ∧ κ < 1 ∧ ∀ y : EReal, y < (m' : EReal) →
      (((1 - κ : ℚ) : ℝ) : EReal) * y < (m : EReal) := by
  have hpos : 0 < min 1 ((m - m') / (|m'| + 1)) :=
    lt_min one_pos (div_pos (sub_pos.2 h) (by positivity))
  obtain ⟨κ, hκ0, hκ⟩ := exists_rat_btwn hpos
  have hκ0' : (0 : ℚ) < κ := by exact_mod_cast hκ0
  have hκ1 : (κ : ℝ) < 1 := hκ.trans_le (min_le_left _ _)
  have hκm : (κ : ℝ) * (|m'| + 1) < m - m' :=
    (lt_div_iff₀ (by positivity)).1 (hκ.trans_le (min_le_right _ _))
  refine ⟨κ, hκ0', by exact_mod_cast hκ1, fun y hy => ?_⟩
  have hc : (0 : ℝ) < ((1 - κ : ℚ) : ℝ) := by push_cast; linarith
  refine (ProjBerk.ereal_coe_mul_lt_coe_mul hc hy).trans ?_
  rw [← EReal.coe_mul, EReal.coe_lt_coe_iff]
  have habs : (κ : ℝ) * -m' ≤ κ * |m'| := mul_le_mul_of_nonneg_left (neg_le_abs m') hκ0.le
  push_cast
  nlinarith

/-! ### The index set of the multiplicative diagonal lemma -/

section Index

variable {K : Type u} {r : ℕ} {ι : Type v}

/-- The index set of the proof of `lem:nn-mult-diagonal`: quadruples `d = (i, a, f, κ)` with
`(a, f) ∈ 𝒜ᵢ`, `κ ∈ ℚ ∩ (0, 1)` and `|a - θᵢ| < κ` (sup norm). -/
structure MultDiagonalIndex (A : ι → Set ((Fin r → ℚ) × (K → EReal))) (θs : ι → Fin r → ℝ) where
  /-- The index `i` of the outer net. -/
  i : ι
  /-- The pair `(a, f) ∈ 𝒜ᵢ`. -/
  p : (Fin r → ℚ) × (K → EReal)
  /-- The multiplicative slack `κ`. -/
  κ : ℚ
  /-- `(a, f) ∈ 𝒜ᵢ`. -/
  mem : p ∈ A i
  /-- `0 < κ`. -/
  κ_pos : 0 < κ
  /-- `κ < 1`. -/
  κ_lt_one : κ < 1
  /-- `|a - θᵢ| < κ`. -/
  dist_lt : dist (fun c => (p.1 c : ℝ)) (θs i) < κ

namespace MultDiagonalIndex

variable {A : ι → Set ((Fin r → ℚ) × (K → EReal))} {θs : ι → Fin r → ℝ}

/-- The approximant `W_d = (1 - κ) f` attached to `d = (i, a, f, κ)`. -/
def approx (d : MultDiagonalIndex A θs) (x : K) : EReal :=
  (((1 - d.κ : ℚ) : ℝ) : EReal) * d.p.2 x

/-- The preorder of the proof of `lem:nn-mult-diagonal`: `d ≤ d'` iff `i ≤ i'`, `κ' ≤ κ` and
`W_{d'} ≤ W_d` on `K`. -/
instance [Preorder ι] : Preorder (MultDiagonalIndex A θs) where
  le d d' := d.i ≤ d'.i ∧ d'.κ ≤ d.κ ∧ ∀ x, d'.approx x ≤ d.approx x
  le_refl d := ⟨le_rfl, le_rfl, fun _ => le_rfl⟩
  le_trans _ _ _ h₁ h₂ :=
    ⟨h₁.1.trans h₂.1, h₂.2.1.trans h₁.2.1, fun x => (h₂.2.2 x).trans (h₁.2.2 x)⟩

theorem le_def [Preorder ι] {d d' : MultDiagonalIndex A θs} :
    d ≤ d' ↔ d.i ≤ d'.i ∧ d'.κ ≤ d.κ ∧ ∀ x, d'.approx x ≤ d.approx x :=
  Iff.rfl

/-- The factor `1 - κ` is positive. -/
theorem one_sub_κ_pos (d : MultDiagonalIndex A θs) : (0 : ℝ) < ((1 - d.κ : ℚ) : ℝ) := by
  have := d.κ_lt_one
  have : (0 : ℚ) < 1 - d.κ := sub_pos.2 this
  exact_mod_cast this

end MultDiagonalIndex

end Index

/-! ### The multiplicative diagonal lemma (`lem:nn-mult-diagonal`) -/

/-- **The multiplicative diagonal lemma** (`lem:nn-mult-diagonal`), net form. Let `(uᵢ)` be a
net of functions `K → [-∞, 0]` with infimum `w` (no monotonicity is needed), `θᵢ → θ` in `ℝ^r`,
and for each `i` let `𝒜ᵢ` be a set of pairs `(a, f)` with `uᵢ ≤ f ≤ 0`, satisfying the
approximation hypothesis (A) (`happrox`) and the multiplicative compatibility hypothesis (B)
(`hcompat`). Then `w` is the pointwise limit (= infimum) of a decreasing net of functions
`(1 - κ_d) f_d`, with `(a_d, f_d) ∈ 𝒜_{i_d}` and `κ_d ∈ ℚ ∩ (0, 1)`, whose classes `(1 - κ_d) a_d`
tend to `θ`. -/
theorem exists_antitone_net_of_multCompatible {K : Type u} [Nonempty K] {r : ℕ} {ι : Type v}
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {u : ι → K → EReal} (hu : ∀ i x, u i x ≤ 0)
    {θs : ι → Fin r → ℝ} {θ : Fin r → ℝ} (hθ : Tendsto θs atTop (𝓝 θ)) {w : K → EReal}
    (hw : ∀ x, w x = ⨅ i, u i x) {A : ι → Set ((Fin r → ℚ) × (K → EReal))}
    (hA : ∀ i, ∀ p ∈ A i, (∀ x, u i x ≤ p.2 x) ∧ ∀ x, p.2 x ≤ 0)
    (happrox : ∀ i x (M : ℝ), u i x < (M : EReal) → ∀ η : ℝ, 0 < η →
      ∃ p ∈ A i, dist (fun c => (p.1 c : ℝ)) (θs i) < η ∧ p.2 x < (M : EReal))
    (hcompat : ∀ i₁ i₂ i, i₁ ≤ i → i₂ ≤ i → ∀ p₁ ∈ A i₁, ∀ p₂ ∈ A i₂, ∀ γ : ℚ, 0 < γ → γ < 1 →
      ∀ η : ℝ, 0 < η → ∃ p ∈ A i, dist (fun c => (p.1 c : ℝ)) (θs i) < η ∧
        (∀ x, p.2 x ≤ ((γ : ℝ) : EReal) * p₁.2 x) ∧ ∀ x, p.2 x ≤ ((γ : ℝ) : EReal) * p₂.2 x) :
    ∃ (D : Type (max u v)) (_ : Preorder D) (_ : IsDirected D (· ≤ ·)) (_ : Nonempty D)
      (idx : D → ι) (p : D → (Fin r → ℚ) × (K → EReal)) (κ : D → ℚ),
      (∀ d, p d ∈ A (idx d)) ∧ (∀ d, 0 < κ d ∧ κ d < 1) ∧
        Tendsto (fun d c => (((1 - κ d) • (p d).1) c : ℝ)) atTop (𝓝 θ) ∧
          (∀ x, Antitone fun d => (((1 - κ d : ℚ) : ℝ) : EReal) * (p d).2 x) ∧
            ∀ x, w x = ⨅ d, (((1 - κ d : ℚ) : ℝ) : EReal) * (p d).2 x := by
  classical
  let D := MultDiagonalIndex A θs
  -- every index `i` and every slack `κ` occur: (A) at any point with `M = 1`
  have hex : ∀ (i : ι) (κ : ℚ), 0 < κ → κ < 1 → ∃ d : D, d.i = i ∧ d.κ = κ := by
    intro i κ h0 h1
    obtain ⟨x⟩ := ‹Nonempty K›
    have hM : u i x < ((1 : ℝ) : EReal) :=
      (hu i x).trans_lt (by rw [EReal.coe_one]; exact zero_lt_one)
    obtain ⟨p, hp, hdist, -⟩ := happrox i x 1 hM κ (by exact_mod_cast h0)
    exact ⟨⟨i, p, κ, hp, h0, h1, hdist⟩, rfl, rfl⟩
  have hne : Nonempty D := by
    obtain ⟨d, -⟩ := hex (Classical.arbitrary ι) (1 / 2) (by norm_num) (by norm_num)
    exact ⟨d⟩
  -- directedness: hypothesis (B) with `γ = (1 - min κ₁ κ₂) / (1 - κ)`
  have hdir : IsDirected D (· ≤ ·) := by
    refine ⟨fun d₁ d₂ => ?_⟩
    obtain ⟨i, h₁, h₂⟩ := directed_of (· ≤ ·) d₁.i d₂.i
    set μ := min d₁.κ d₂.κ
    have hμ0 : 0 < μ := lt_min d₁.κ_pos d₂.κ_pos
    have hμ1 : μ < 1 := (min_le_left _ _).trans_lt d₁.κ_lt_one
    set κ := μ / 2
    have hκ0 : 0 < κ := half_pos hμ0
    have hκμ : κ < μ := half_lt_self hμ0
    have hκ1 : κ < 1 := hκμ.trans hμ1
    set γ := (1 - μ) / (1 - κ)
    have hγ0 : 0 < γ := div_pos (sub_pos.2 hμ1) (sub_pos.2 hκ1)
    have hγ1 : γ < 1 := (div_lt_one (sub_pos.2 hκ1)).2 (by linarith)
    have hκγ : (1 - κ) * γ = 1 - μ := mul_div_cancel₀ _ (sub_pos.2 hκ1).ne'
    obtain ⟨p, hp, hdist, hle₁, hle₂⟩ := hcompat d₁.i d₂.i i h₁ h₂ d₁.p d₁.mem d₂.p d₂.mem γ hγ0
      hγ1 κ (by exact_mod_cast hκ0)
    let d : D := ⟨i, p, κ, hp, hκ0, hκ1, hdist⟩
    have hc : (0 : ℝ) < ((1 - κ : ℚ) : ℝ) := by
      have : (0 : ℚ) < 1 - κ := sub_pos.2 hκ1
      exact_mod_cast this
    -- `(1 - κ) f ≤ (1 - κ) γ f_ν = (1 - μ) f_ν ≤ (1 - κ_ν) f_ν`
    have key : ∀ d' : D, μ ≤ d'.κ → (∀ x, p.2 x ≤ ((γ : ℝ) : EReal) * d'.p.2 x) →
        ∀ x, d.approx x ≤ d'.approx x := by
      intro d' hμd' hle x
      have h₁ : d.approx x ≤ (((1 - κ : ℚ) : ℝ) : EReal) * (((γ : ℝ) : EReal) * d'.p.2 x) :=
        ProjBerk.ereal_coe_mul_monotone hc.le (hle x)
      rw [ProjBerk.ereal_coe_mul_coe_mul, ← Rat.cast_mul, hκγ] at h₁
      refine h₁.trans (ProjBerk.ereal_coe_mul_le_of_nonpos d'.one_sub_κ_pos ?_
        ((hA _ _ d'.mem).2 x))
      have : (1 - d'.κ : ℚ) ≤ 1 - μ := by linarith
      exact_mod_cast this
    refine ⟨d, ⟨h₁, hκμ.le.trans (min_le_left _ _), key d₁ (min_le_left _ _) hle₁⟩,
      ⟨h₂, hκμ.le.trans (min_le_right _ _), key d₂ (min_le_right _ _) hle₂⟩⟩
  -- the outer indices tend to infinity
  have hi : Tendsto (fun d : D => d.i) atTop atTop := by
    refine tendsto_atTop.2 fun i₀ => ?_
    obtain ⟨d₀, hd₀, -⟩ := hex i₀ (1 / 2) (by norm_num) (by norm_num)
    exact eventually_atTop.2 ⟨d₀, fun d hd => hd₀ ▸ hd.1⟩
  -- the slacks tend to `0`
  have hκ : Tendsto (fun d : D => (d.κ : ℝ)) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun d => ?_, fun a ha => ?_⟩
    · exact ha.trans (by exact_mod_cast d.κ_pos)
    · obtain ⟨κ₀, hκ₀0, hκ₀a⟩ := exists_rat_btwn (lt_min ha one_pos)
      have hκ₀0' : (0 : ℚ) < κ₀ := by exact_mod_cast hκ₀0
      have hκ₀1 : κ₀ < 1 := by exact_mod_cast hκ₀a.trans_le (min_le_right _ _)
      obtain ⟨d₀, -, hd₀⟩ := hex (Classical.arbitrary ι) κ₀ hκ₀0' hκ₀1
      refine eventually_atTop.2 ⟨d₀, fun d hd => ?_⟩
      have : d.κ ≤ κ₀ := hd₀ ▸ hd.2.1
      have : (d.κ : ℝ) ≤ κ₀ := by exact_mod_cast this
      exact this.trans_lt (hκ₀a.trans_le (min_le_left _ _))
  -- the classes `a_d` tend to `θ`
  have ha : Tendsto (fun d : D => fun c => (d.p.1 c : ℝ)) atTop (𝓝 θ) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
      (fun d => (dist_triangle _ (θs d.i) _).trans (add_le_add_left d.dist_lt.le _)) ?_)
    simpa only [add_zero, Function.comp_apply] using
      hκ.add (tendsto_iff_dist_tendsto_zero.1 (hθ.comp hi))
  refine ⟨D, inferInstance, hdir, hne, fun d => d.i, fun d => d.p, fun d => d.κ, fun d => d.mem,
    fun d => ⟨d.κ_pos, d.κ_lt_one⟩, ?_, fun x _ _ h => (MultDiagonalIndex.le_def.1 h).2.2 x,
    fun x => ?_⟩
  · -- the classes `(1 - κ_d) a_d` tend to `θ`
    have h := (tendsto_const_nhds (x := (1 : ℝ)).sub hκ).smul ha
    rw [sub_zero, one_smul] at h
    refine h.congr fun d => ?_
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
  · -- pointwise convergence
    refine le_antisymm (le_iInf fun d => ?_) (le_of_forall_gt_imp_ge_of_dense fun c hc => ?_)
    · -- lower bound: `W_d ≥ f ≥ u_i ≥ w`
      calc w x ≤ u d.i x := by rw [hw x]; exact iInf_le _ _
        _ ≤ d.p.2 x := (hA _ _ d.mem).1 x
        _ ≤ d.approx x :=
          ereal_le_coe_mul_of_nonpos d.one_sub_κ_pos (by
            have : (1 - d.κ : ℚ) ≤ 1 := by linarith [d.κ_pos]
            exact_mod_cast this) ((hA _ _ d.mem).2 x)
    · -- upper bound, via (A)
      obtain ⟨m, hm₁, hm₂⟩ := EReal.lt_iff_exists_real_btwn.1 hc
      obtain ⟨m', hm'₁, hm'₂⟩ := EReal.lt_iff_exists_real_btwn.1 hm₁
      obtain ⟨κ₀, hκ₀0, hκ₀1, hκ₀⟩ := exists_rat_one_sub_mul_lt (EReal.coe_lt_coe_iff.1 hm'₂)
      rw [hw x] at hm'₁
      obtain ⟨i₀, hi₀⟩ := iInf_lt_iff.1 hm'₁
      obtain ⟨p, hp, hdist, hpx⟩ := happrox i₀ x m' hi₀ κ₀ (by exact_mod_cast hκ₀0)
      let d₀ : D := ⟨i₀, p, κ₀, hp, hκ₀0, hκ₀1, hdist⟩
      exact (iInf_le _ d₀).trans ((hκ₀ _ hpx).trans hm₂).le

namespace FSSystemC

variable {K : Type u} [TopologicalSpace K] {r : ℕ} (F : FSSystemC K r)

/-- **The multiplicative diagonal lemma** (`lem:nn-mult-diagonal`). Let `(uᵢ)` be a net of
functions `K → [-∞, 0]` (decreasing in the applications; this is not needed) whose infimum `w` is
not identically `-∞`, `θᵢ → θ` in `ℝ^r`, and for each `i` let `𝒜ᵢ` be a set of pairs `(a, f)`
with `f ∈ 𝓗(a)` and `uᵢ ≤ f ≤ 0`, satisfying the approximation hypothesis (A) (`happrox`) and the
multiplicative compatibility hypothesis (B) (`hcompat`). Then `w ∈ PSH(θ)`, for **every**
`θ ∈ ℝ^r`. (The approximating net is that of `exists_antitone_net_of_multCompatible`.) -/
theorem isPSH_of_multCompatible {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u : ι → K → EReal} (hu : ∀ i x, u i x ≤ 0) {θs : ι → Fin r → ℝ} {θ : Fin r → ℝ}
    (hθ : Tendsto θs atTop (𝓝 θ)) {w : K → EReal} (hw : ∀ x, w x = ⨅ i, u i x)
    (hfin : ∃ x, w x ≠ ⊥) {A : ι → Set ((Fin r → ℚ) × (K → EReal))}
    (hA : ∀ i, ∀ p ∈ A i, F.IsFS p.1 p.2 ∧ (∀ x, u i x ≤ p.2 x) ∧ ∀ x, p.2 x ≤ 0)
    (happrox : ∀ i x (M : ℝ), u i x < (M : EReal) → ∀ η : ℝ, 0 < η →
      ∃ p ∈ A i, dist (fun c => (p.1 c : ℝ)) (θs i) < η ∧ p.2 x < (M : EReal))
    (hcompat : ∀ i₁ i₂ i, i₁ ≤ i → i₂ ≤ i → ∀ p₁ ∈ A i₁, ∀ p₂ ∈ A i₂, ∀ γ : ℚ, 0 < γ → γ < 1 →
      ∀ η : ℝ, 0 < η → ∃ p ∈ A i, dist (fun c => (p.1 c : ℝ)) (θs i) < η ∧
        (∀ x, p.2 x ≤ ((γ : ℝ) : EReal) * p₁.2 x) ∧ ∀ x, p.2 x ≤ ((γ : ℝ) : EReal) * p₂.2 x) :
    F.IsPSH θ w := by
  have : Nonempty K := let ⟨x, _⟩ := hfin; ⟨x⟩
  obtain ⟨D, _, _, _, idx, p, κ, hmem, hκ, hcl, hanti', hlim⟩ :=
    exists_antitone_net_of_multCompatible hu hθ hw (fun i q hq => (hA i q hq).2) happrox
      hcompat
  exact isPSH_of_iInf hfin (ι := D) (fun d => (1 - κ d) • (p d).1)
    (fun d x => (((1 - κ d : ℚ) : ℝ) : EReal) * (p d).2 x)
    (fun d => (hA _ _ (hmem d)).1.smul (sub_pos.2 (hκ d).2)) hcl hanti' hlim

/-! ### Multiplicatively sandwiched approximants (`cor:nn-sandwich-diagonal`) -/

/-- **Multiplicatively sandwiched approximants** (`cor:nn-sandwich-diagonal`). Let `(uᵢ)` be a
decreasing net of functions `K → [-∞, 0]` whose infimum `w` is not identically `-∞`, and `θᵢ → θ`
in `ℝ^r`. If for every `i`, every rational `δ ∈ (0, 1)` and every `η > 0` there are `a ∈ ℚ^r` with
`|a - θᵢ| < η` and `f ∈ 𝓗(a)` with `uᵢ ≤ f ≤ (1 - δ) uᵢ`, then `w ∈ PSH(θ)`, for **every**
`θ ∈ ℝ^r`. -/
theorem isPSH_of_sandwich {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u : ι → K → EReal} (hanti : ∀ x, Antitone fun i => u i x) (hu : ∀ i x, u i x ≤ 0)
    {θs : ι → Fin r → ℝ} {θ : Fin r → ℝ} (hθ : Tendsto θs atTop (𝓝 θ)) {w : K → EReal}
    (hw : ∀ x, w x = ⨅ i, u i x) (hfin : ∃ x, w x ≠ ⊥)
    (hsand : ∀ i (δ : ℚ), 0 < δ → δ < 1 → ∀ η : ℝ, 0 < η → ∃ (a : Fin r → ℚ) (f : K → EReal),
      dist (fun c => (a c : ℝ)) (θs i) < η ∧ F.IsFS a f ∧ (∀ x, u i x ≤ f x) ∧
        ∀ x, f x ≤ (((1 - δ : ℚ) : ℝ) : EReal) * u i x) :
    F.IsPSH θ w := by
  -- `(1 - δ) uᵢ ≤ 0`
  have hnonpos : ∀ (δ : ℚ), δ < 1 → ∀ i x, (((1 - δ : ℚ) : ℝ) : EReal) * u i x ≤ 0 :=
    fun δ hδ i x => ereal_coe_mul_nonpos_of_nonpos (by
      have : (0 : ℚ) ≤ 1 - δ := by linarith
      exact_mod_cast this) (hu i x)
  refine F.isPSH_of_multCompatible hu hθ hw hfin
    (A := fun i => {p | F.IsFS p.1 p.2 ∧ (∀ x, u i x ≤ p.2 x) ∧ ∀ x, p.2 x ≤ 0})
    (fun i p hp => hp) ?_ ?_
  · -- (A): choose `δ` with `(1 - δ) uᵢ(x) < M`
    intro i x M hM η hη
    obtain ⟨m', hm'₁, hm'₂⟩ := EReal.lt_iff_exists_real_btwn.1 hM
    obtain ⟨δ, hδ0, hδ1, hδ⟩ := exists_rat_one_sub_mul_lt (EReal.coe_lt_coe_iff.1 hm'₂)
    obtain ⟨a, f, hdist, hf, hlow, hup⟩ := hsand i δ hδ0 hδ1 η hη
    exact ⟨(a, f), ⟨hf, hlow, fun y => (hup y).trans (hnonpos δ hδ1 i y)⟩, hdist,
      (hup x).trans_lt (hδ _ hm'₁)⟩
  · -- (B): with `δ = 1 - γ`, `f ≤ γ uᵢ ≤ γ u_{i_ν} ≤ γ f_ν`
    intro i₁ i₂ i h₁ h₂ p₁ hp₁ p₂ hp₂ γ hγ0 hγ1 η hη
    obtain ⟨a, f, hdist, hf, hlow, hup⟩ := hsand i (1 - γ) (sub_pos.2 hγ1) (by linarith) η hη
    simp only [sub_sub_cancel] at hup
    have hγ : (0 : ℝ) ≤ (γ : ℝ) := by exact_mod_cast hγ0.le
    refine ⟨(a, f), ⟨hf, hlow, fun y => (hup y).trans (by
      simpa only [sub_sub_cancel] using hnonpos (1 - γ) (by linarith) i y)⟩, hdist,
      fun y => ?_, fun y => ?_⟩
    · exact (hup y).trans (ProjBerk.ereal_coe_mul_monotone hγ ((hanti y h₁).trans (hp₁.2.1 y)))
    · exact (hup y).trans (ProjBerk.ereal_coe_mul_monotone hγ ((hanti y h₂).trans (hp₂.2.1 y)))

/-- **Multiplicatively sandwiched approximants** (`cor:nn-sandwich-diagonal`) for decreasing
sequences. -/
theorem isPSH_of_sandwich_seq {u : ℕ → K → EReal} (hanti : ∀ x, Antitone fun n => u n x)
    (hu : ∀ n x, u n x ≤ 0) {θs : ℕ → Fin r → ℝ} {θ : Fin r → ℝ} (hθ : Tendsto θs atTop (𝓝 θ))
    {w : K → EReal} (hw : ∀ x, w x = ⨅ n, u n x) (hfin : ∃ x, w x ≠ ⊥)
    (hsand : ∀ n (δ : ℚ), 0 < δ → δ < 1 → ∀ η : ℝ, 0 < η → ∃ (a : Fin r → ℚ) (f : K → EReal),
      dist (fun c => (a c : ℝ)) (θs n) < η ∧ F.IsFS a f ∧ (∀ x, u n x ≤ f x) ∧
        ∀ x, f x ≤ (((1 - δ : ℚ) : ℝ) : EReal) * u n x) :
    F.IsPSH θ w := by
  have hdown : Tendsto (ULift.down : ULift.{u} ℕ → ℕ) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨ULift.up b, fun a ha => ha⟩
  refine F.isPSH_of_sandwich (ι := ULift.{u} ℕ) (u := fun n => u n.down)
    (fun x _ _ h => hanti x h) (fun n => hu n.down) (hθ.comp hdown) (fun x => ?_) hfin
    fun n => hsand n.down
  rw [hw x]
  exact (Equiv.ulift.iInf_comp (g := fun n => u n x)).symm

end FSSystemC

end EnvelopeProperty
