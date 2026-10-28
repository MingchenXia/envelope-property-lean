/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyPSH

/-!
# Uniform limits with converging classes, and the ε-argument of our route to FHX Lemma 5.5

This file proves the real-analysis step ("link 9" of the native-scheme pipeline for the class
`LocalPositivity`, `.archon-horizon/scratch/ep/PLAN-LP-ASSEMBLY.md`) of our formalization route
for Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Lemma 5.5
(`lem:local-PL-positivity`): once a function `φ` on `X^an` is, for every `b ≥ 1`, the
normalized difference of a Fubini–Study function of class `b e + e'` and a bounded error, it is
`a`-psh with `a = e / r` (Boucksom–Jonsson, *Global pluripotential theory over a trivially valued
field*, BJ22, Theorem 4.7 (`thm:PSH`(ii)): uniform limits of psh functions are psh).

This step is ours, not FHX's: FHX prove `lem:local-PL-positivity` by writing `φ` as the model
function of a line bundle on a normal test configuration (BJ22 Theorem 2.31) and checking, via
BJ22 Definition 3.2 and Lemma 4.3, that it has nonnegative degree on the curves of the central
fibre, which they deduce from the positivity criterion of Chambert-Loir–Ducros (CLD12). Their
argument has no parameter `b`; the family indexed by `b`, the limit `b → ∞` and the convergence
of the classes `(b r)⁻¹ (b e + e') → a` belong to the native route formalized here.

## Main results

* `EnvelopeProperty.FSSystem.isPSH_of_uniform_limit`: in a compact Fubini–Study system, if
  `w_i ∈ PSH(θ_i)` converges uniformly to `u` along a nontrivial filter and `θ_i → θ₀`, then
  `u ∈ PSH(θ₀)`. This is BJ22 `thm:PSH`(ii) with varying classes; the fixed-class version on
  `(ℙⁿ)^an` is `ProjBerk.isPSH_of_uniform_limit`.
* `EnvelopeProperty.ProjSubvariety.isPSH_of_uniform_limit`: the same on `X^an`, `X = V(I)`.
* `EnvelopeProperty.ProjSubvariety.isPSH_of_forall_approx`: if for every `ε > 0` there is a
  real-valued `ψ ∈ PSH(X, θ)` with `|θ - a| ≤ ε` and `|ψ - φ| ≤ ε`, then `φ ∈ PSH(X, a)`.
* `EnvelopeProperty.ProjSubvariety.isPSH_of_potential_family` (**the ε-argument**): let
  `r ≥ 1`, `e = r a`, `p_M = r φ + c` and `|p_H| ≤ K`. If for arbitrarily large `b ∈ ℕ` the
  function `b p_M + p_H` belongs to `PSH(X, b e + e')`, then `φ ∈ PSH(X, a)`: indeed
  `(b r)⁻¹ (b p_M + p_H) - c / r = φ + p_H / (b r)` lies in `PSH(X, a + e' / (b r))` and is
  `K / (b r)`-close to `φ`.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

namespace FSSystem

variable {K : Type u} [TopologicalSpace K] {r : ℕ} {F : FSSystem K r}

/-- **Uniform limits with converging classes** (BJ22 `thm:PSH`(ii)). Let `K` be compact. If
`w_i ∈ PSH(θ_i)` along a nontrivial filter `l`, `θ_i → θ₀`, and `w_i → u` uniformly in the sense
that eventually `w_i ≤ u + ε` and `u ≤ w_i + ε` everywhere, then `u ∈ PSH(θ₀)`. Choose `i_m` with
`ε = 2⁻ᵐ` and `θ_{i_m}` within `2⁻ᵐ` of `θ₀`; then `w_{i_m} + 3 · 2⁻ᵐ` decreases to `u` and PSH2
(`FSSystem.isPSH_of_antitone_seq`) applies. -/
theorem isPSH_of_uniform_limit [CompactSpace K] {ι : Type*} {l : Filter ι} [l.NeBot]
    {θ : ι → Fin r → ℝ} {θ₀ : Fin r → ℝ} (hθ : Tendsto θ l (𝓝 θ₀))
    {w : ι → K → EReal} (hw : ∀ i, F.IsPSH (θ i) (w i)) {u : K → EReal}
    (hunif : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ x, w i x ≤ u x + (ε : EReal) ∧
      u x ≤ w i x + (ε : EReal)) : F.IsPSH θ₀ u := by
  have hε : ∀ m : ℕ, (0 : ℝ) < (1 / 2) ^ m := fun m => by positivity
  have hex : ∀ m : ℕ, ∃ i, (∀ x, w i x ≤ u x + (((1 / 2) ^ m : ℝ) : EReal) ∧
      u x ≤ w i x + (((1 / 2) ^ m : ℝ) : EReal)) ∧ dist (θ i) θ₀ < (1 / 2) ^ m := fun m =>
    ((hunif _ (hε m)).and (hθ.eventually (Metric.ball_mem_nhds θ₀ (hε m)))).exists
  choose i hi hiθ using hex
  set ε : ℕ → ℝ := fun m => (1 / 2) ^ m with hε_def
  have hεsucc : ∀ m, ε m + ε (m + 1) + 3 * ε (m + 1) = 3 * ε m := fun m => by
    simp only [hε_def, pow_succ]; ring
  have hutop : ∀ x, u x ≠ ⊤ := fun x => by
    intro htop
    have := (hi 0 x).2
    rw [htop, top_le_iff] at this
    exact EReal.add_ne_top ((hw (i 0)).ne_top x) (EReal.coe_ne_top _) this
  have hθi : Tendsto (fun m => θ (i m)) atTop (𝓝 θ₀) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun m => dist_nonneg)
      (fun m => (hiθ m).le) ?_)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  set ψ : ℕ → K → EReal := fun m x => w (i m) x + ((3 * ε m : ℝ) : EReal) with hψ_def
  have hanti : ∀ x, Antitone fun m => ψ m x := fun x => antitone_nat_of_succ_le fun m => by
    calc ψ (m + 1) x ≤ u x + (ε (m + 1) : EReal) + ((3 * ε (m + 1) : ℝ) : EReal) :=
          add_le_add_left (hi (m + 1) x).1 _
      _ ≤ w (i m) x + (ε m : EReal) + (ε (m + 1) : EReal) + ((3 * ε (m + 1) : ℝ) : EReal) :=
          add_le_add_left (add_le_add_left (hi m x).2 _) _
      _ = ψ m x := by
          rw [hψ_def, add_assoc, add_assoc, ← EReal.coe_add, ← EReal.coe_add, ← add_assoc,
            hεsucc]
  refine isPSH_of_antitone_seq hθi (fun m => (hw (i m)).add_const _) hanti (fun x => ?_)
    ⟨F.triv, ?_⟩
  · refine le_antisymm (le_iInf fun m => ?_) ?_
    · refine (hi m x).2.trans (add_le_add_right (EReal.coe_le_coe_iff.2 ?_) _)
      have := hε m
      linarith
    · have hlim : Tendsto (fun m => u x + ((4 * ε m : ℝ) : EReal)) atTop (𝓝 (u x)) := by
        have h0 : Tendsto (fun m => ((4 * ε m : ℝ) : EReal)) atTop (𝓝 ((0 : ℝ) : EReal)) := by
          refine EReal.tendsto_coe.2 ?_
          simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
            (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 4
        have hc := (EReal.continuousAt_add (p := (u x, ((0 : ℝ) : EReal))) (Or.inl (hutop x))
          (Or.inr (EReal.coe_ne_top 0))).tendsto.comp (tendsto_const_nhds.prodMk_nhds h0)
        simpa only [Function.comp_def, EReal.coe_zero, add_zero] using hc
      refine ge_of_tendsto' hlim fun m => (iInf_le _ m).trans ?_
      calc ψ m x ≤ u x + (ε m : EReal) + ((3 * ε m : ℝ) : EReal) := add_le_add_left (hi m x).1 _
        _ = u x + ((4 * ε m : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add]; ring_nf
  · intro hbot
    have := (hi 0 F.triv).1
    rw [hbot, EReal.bot_add, le_bot_iff] at this
    exact (hw (i 0)).apply_triv_ne_bot this

end FSSystem

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

variable {X} in
/-- **Uniform limits with converging classes on `X^an`** (BJ22 `thm:PSH`(ii)): if
`w_i ∈ PSH(X, θ_i)`, `θ_i → θ₀` and `w_i → u` uniformly along a nontrivial filter, then
`u ∈ PSH(X, θ₀)`. -/
theorem isPSH_of_uniform_limit {ι : Type*} {l : Filter ι} [l.NeBot] {θ : ι → ℝ} {θ₀ : ℝ}
    (hθ : Tendsto θ l (𝓝 θ₀)) {w : ι → X.an → EReal} (hw : ∀ i, X.IsPSH (θ i) (w i))
    {u : X.an → EReal}
    (hunif : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ x, w i x ≤ u x + (ε : EReal) ∧
      u x ≤ w i x + (ε : EReal)) : X.IsPSH θ₀ u :=
  FSSystem.isPSH_of_uniform_limit (F := X.fsSystem) (θ := fun i _ => θ i)
    (tendsto_pi_nhds.2 fun _ => hθ) hw hunif

/-- Real-valued uniform closeness `|ψ - φ| ≤ ε` gives the two `EReal` inequalities of
`isPSH_of_uniform_limit`. -/
private theorem ereal_le_add_of_abs_sub_le {s t ε : ℝ} (h : |s - t| ≤ ε) :
    ((s : ℝ) : EReal) ≤ ((t : ℝ) : EReal) + (ε : EReal) ∧
      ((t : ℝ) : EReal) ≤ ((s : ℝ) : EReal) + (ε : EReal) := by
  rw [abs_le] at h
  refine ⟨?_, ?_⟩ <;> rw [← EReal.coe_add, EReal.coe_le_coe_iff] <;> linarith

variable {X} in
/-- **Approximation criterion.** If for every `ε > 0` there are a class `θ` with `|θ - a| ≤ ε`
and a real-valued `ψ ∈ PSH(X, θ)` with `|ψ - φ| ≤ ε` on `X^an`, then `φ ∈ PSH(X, a)`. -/
theorem isPSH_of_forall_approx {a : ℝ} {φ : X.an → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ (θ : ℝ) (ψ : X.an → ℝ), |θ - a| ≤ ε ∧
      X.IsPSH θ (fun x => (ψ x : EReal)) ∧ ∀ x, |ψ x - φ x| ≤ ε) :
    X.IsPSH a fun x => (φ x : EReal) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose θ ψ hθ hψ hclose using fun n : ℕ => h _ (hpos n)
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine isPSH_of_uniform_limit (l := atTop) (θ := θ) ?_ hψ fun ε hε => ?_
  · refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg)
      (fun n => ?_) hlim)
    rw [Real.dist_eq]
    exact hθ n
  · filter_upwards [(hlim.eventually (gt_mem_nhds hε))] with n hn x
    exact ereal_le_add_of_abs_sub_le ((hclose n x).trans hn.le)

variable {X} in
/-- **The ε-argument of our route to FHX Lemma 5.5** (class bookkeeping; a step of our native
route, not of FHX's proof, see the module docstring). Let `r ≥ 1`, `a ∈ ℚ` and
`e = r a`. Let `p_M = r φ + c` (the model potential of the twisted ratio line, up to a constant)
and let `p_H` be bounded, `|p_H| ≤ K` (a potential of an auxiliary line). Suppose that for
arbitrarily large `b ∈ ℕ` the function `b p_M + p_H` is `(b e + e')`-psh (e.g. a finite
Fubini–Study function of the ample line `M^b ⊗ H`). Then `φ ∈ PSH(X, a)`: the functions
`(b r)⁻¹ (b p_M + p_H) - c / r = φ + p_H / (b r)` lie in `PSH(X, a + e' / (b r))` and are
`K / (b r)`-close to `φ`. -/
theorem isPSH_of_potential_family {r : ℕ} (hr : 0 < r) {a e e' c K : ℝ} (hea : e = r * a)
    {φ pM pH : X.an → ℝ} (hpM : ∀ x, pM x = r * φ x + c) (hpH : ∀ x, |pH x| ≤ K)
    (hFS : ∀ N : ℕ, ∃ b : ℕ, N ≤ b ∧ 0 < b ∧
      X.IsPSH (b * e + e') fun x => ((b * pM x + pH x : ℝ) : EReal)) :
    X.IsPSH a fun x => (φ x : EReal) := by
  refine isPSH_of_forall_approx fun ε hε => ?_
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  -- choose `b` with `(|e'| + K) / (b r) ≤ ε`
  obtain ⟨N, hN⟩ := exists_nat_gt ((|e'| + K + 1) / (ε * r))
  obtain ⟨b, hNb, hb, hpsh⟩ := hFS N
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hbr : (0 : ℝ) < b * r := mul_pos hb' hr'
  have hK : 0 ≤ K := (abs_nonneg _).trans (hpH X.triv)
  have hNb' : ((|e'| + K + 1) / (ε * r) : ℝ) < b :=
    hN.trans_le (by exact_mod_cast hNb)
  have hsmall : (|e'| + K + 1) / (b * r) < ε := by
    rw [div_lt_iff₀ hbr]
    rw [div_lt_iff₀ (mul_pos hε hr')] at hNb'
    nlinarith
  have hsmallK : K / (b * r) ≤ ε :=
    le_of_lt (lt_of_le_of_lt (div_le_div_of_nonneg_right (by linarith [abs_nonneg e'])
      hbr.le) hsmall)
  have hsmalle : |e'| / (b * r) ≤ ε :=
    le_of_lt (lt_of_le_of_lt (div_le_div_of_nonneg_right (by linarith) hbr.le) hsmall)
  refine ⟨((b : ℝ) * r)⁻¹ * (b * e + e'),
    fun x => ((b : ℝ) * r)⁻¹ * (b * pM x + pH x) - c / r, ?_, ?_, ?_⟩
  · have hcl : ((b : ℝ) * r)⁻¹ * (b * e + e') - a = e' / (b * r) := by
      rw [hea]; field_simp; ring
    rw [hcl, abs_div, abs_of_pos hbr]
    exact hsmalle
  · have h1 := (hpsh.smul (inv_pos.2 hbr)).add_const (-(c / r))
    convert h1 using 2 with x
    rw [← EReal.coe_mul, ← EReal.coe_add]
    simp only [sub_eq_add_neg]
  · intro x
    have hx : ((b : ℝ) * r)⁻¹ * (b * pM x + pH x) - c / r - φ x = pH x / (b * r) := by
      rw [hpM]; field_simp; ring
    rw [hx, abs_div, abs_of_pos hbr]
    exact (div_le_div_of_nonneg_right (hpH x) hbr.le).trans hsmallK

end ProjSubvariety

end EnvelopeProperty
