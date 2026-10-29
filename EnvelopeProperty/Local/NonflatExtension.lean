/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.CompactificationAffine
import EnvelopeProperty.Projective.SmoothEP
import EnvelopeProperty.Projective.PSH2
import EnvelopeProperty.Local.PrincipalExtension
import EnvelopeProperty.Local.Gluing
import EnvelopeProperty.Local.NonflatImport

/-!
# The extension step of FHX Proposition 5.22

Let `k` be a countable algebraically closed field with the trivial absolute value, `n ≥ 1`,
`0 ≠ h_S ∈ k[y₁, …, yₙ]`, `S = Spec k[y]_{h_S}` the principal open of `𝔸ⁿ`, `0 ≠ h ∈ k[S]` and
`S₀ = S_h`. This file proves the extension step of Fang–Han–Xia, *The envelope property for
unibranch projective varieties*, Proposition 5.22 (`prop:nonflat-norm`, paragraph "Extension to
`S`"; blueprint `lem:nonflat-extension`):

> if every rational class `a > 0` on `ℙⁿ` has the envelope property, and `v₀ ∈ ℛ(S₀)` satisfies
> `v₀ ≤ g + B` on `S₀^an` for some `g ∈ FS(S)` and `B ∈ ℝ`, then there is `v ∈ ℛ(S)` with
> `v = v₀` on `S₀^an`.

The proof follows the blueprint, steps (1)–(7).

1. `h_S = dehom₀ t` for a form `t` of degree `d` (`ProjBerk.exists_dehom_eq`; any such form, not
   necessarily the homogenization, will do), and `σ = x₀ t`, so that `S ≃ ℙⁿ_σ` and
   `S^an ≃ U_σ` by the chart `ProjBerk.mulChart` (`lem:bj-chart`).
2. Every `f ∈ k[S] = A_σ` is `τ / σ^N` with `|τ| ≤ 1`, so `|f| ≤ |σ|^{-N}`
   (`ProjBerk.exists_val_le_exp_chartLog`), and every `g ∈ FS(S)` satisfies
   `g ≤ -κ_g log|σ| + C_g` with `κ_g ∈ ℚ_{>0}` (`ProjBerk.exists_eval_le_chartLog`). Here
   `ProjBerk.chartLog` is the real number `log|σ|` at the point of `U_σ` attached to `y ∈ S^an`.
3. With `c_i = 1/(i+1)`, the extension `w_i` of `v₀ + c_i log|h|` by `-∞` lies in `ℛ(S)`
   (`IsRegularizable.awayExtend_add`, FHX Lemma 5.12) and `w_i ≤ -κ log|σ| + B₀` with
   `κ = κ_g + N_h`, `B₀ = B + C_g`.
4. For the rational `a = κ + 1 > κ`, the compactified function `φ_i` (`ProjBerk.mulChartExt`) lies
   in `PSH(a (d + 1))` (`ProjBerk.isPSH_mulChartExt`, FHX Lemma 5.10(2)) and `φ_i ≤ B₀`.
5. By the envelope property, `ψ_m = (sup_{i ≥ m} φ_i)^⋆` is `a (d + 1)`-psh; the `ψ_m` decrease
   to `Ψ`, which is `a (d + 1)`-psh by PSH2 (`ProjBerk.isPSH_of_antitone_seq`) once it is not
   identically `-∞`.
6. On `S₀^an` (embedded in `(ℙⁿ)^an` by the open embedding `T`), for `i ≥ m`,
   `φ_i ≤ G_m = v₀ + c_m max(log|h|, 0) + a log|σ|`, which is usc on `S₀^an`; extending `G_m` by
   `+∞` off `T(S₀^an)` gives a usc function on `(ℙⁿ)^an` (`upperSemicontinuous_extend_top`)
   dominating `sup_{i ≥ m} φ_i`, hence `ψ_m ≤ G_m` on `S₀^an`. Conversely `ψ_m ≥ φ_i` for `i ≥ m`
   and `φ_i → v₀ + a log|σ|` on `S₀^an`. So `Ψ = v₀ + a log|σ|` on `S₀^an`.
7. `v = (Ψ - a log|σ|)|_{S^an}` lies in `ℛ(S)` (`ProjBerk.IsPSH.isRegularizable_mulChart`, FHX
   Lemma 5.10(1)) and `v = v₀` on `S₀^an`.

## Main results

* `ProjBerk.exists_extend_mulChart`: the statement on the chart `S = Spec k[y]_{dehom t}`.
* `IsRegularizable.exists_extend_of_hasEnvelopeProperty`: the statement for
  `S = Spec k[y]_{h_S}`.
* `IsRegularizable.exists_extend_of_charP`: in characteristic `p > 0` the envelope property of
  `ℙⁿ` is a theorem (`ProjBerk.hasEnvelopeProperty_of_charP`, `thm:pn-ep-charp`) and is dropped
  from the hypotheses.
* `IsRegularizable.exists_extend_of_isAffineSpacePrincipalOpen` (and `..._of_charP`): the same
  for a `k`-algebra `B` with `IsAffineSpacePrincipalOpen k B n`, transported along
  `B ≃ₐ[k] k[y]_{h_S}`.

## Hypotheses

* `WuRegularization k`: the imported FHX Lemma 5.11(5),(6) (an explicit class hypothesis, not an
  axiom), used by FHX Lemmas 5.10(2) and 5.12.
* `Countable k`: used by FHX Lemma 5.10(1) (`ProjBerk.IsPSH.isRegularizable_mulChart`, through
  Boucksom–Jonsson's countable regularization); FHX §5 assumes `k` countable throughout.
* The envelope property of every rational class `a > 0` on `ℙⁿ` (`hEP`), discharged in
  characteristic `p`.

## Deviations from the blueprint

* Finiteness of `Ψ` (step (5)) is checked at a point `y₀ ∈ S₀^an` with `v₀(y₀) ≠ -∞` (part of
  `v₀ ∈ ℛ(S₀)`), instead of at `v_triv` via `lem:reg-triv-finite`.
* The bound `ψ_m ≤ G_m` on the open set `S₀^an` (step (6)) is obtained from the extension of
  `G_m` by `+∞`, which is usc on `(ℙⁿ)^an`.
* The form `t` with `dehom₀ t = h_S` is any form, not necessarily the homogenization of `h_S`.
-/

open scoped NNReal ENNReal Topology

open Filter Topology MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Auxiliary facts on `EReal`-valued functions -/

namespace NonflatExtension

variable {X : Type*} [TopologicalSpace X]

/-- Adding a continuous real-valued function preserves upper semicontinuity. -/
theorem upperSemicontinuous_add_coe {f : X → EReal} (hf : UpperSemicontinuous f) {g : X → ℝ}
    (hg : Continuous g) : UpperSemicontinuous fun x => f x + (g x : EReal) :=
  hf.add' (continuous_coe_real_ereal.comp hg).upperSemicontinuous fun _ =>
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))

/-- Extending an upper semicontinuous function along an open embedding by `⊤` gives an upper
semicontinuous function. -/
theorem upperSemicontinuous_extend_top {Y : Type*} [TopologicalSpace Y] {T : X → Y}
    (hT : IsOpenEmbedding T) {G : X → EReal} (hG : UpperSemicontinuous G) :
    UpperSemicontinuous (Function.extend T G fun _ => ⊤) := by
  intro y c hc
  by_cases hy : ∃ x, T x = y
  · obtain ⟨x, rfl⟩ := hy
    rw [hT.injective.extend_apply] at hc
    rw [← hT.map_nhds_eq, Filter.eventually_map]
    exact (hG x c hc).mono fun x' hx' => by
      simp only at hx' ⊢
      rwa [hT.injective.extend_apply]
  · rw [Function.extend_apply' _ _ _ hy] at hc
    exact absurd hc (not_lt.2 le_top)

/-- `x + r_m → x + r₀` in `EReal` when the real numbers `r_m` tend to `r₀`. -/
theorem ereal_tendsto_add_coe (x : EReal) {r : ℕ → ℝ} {r₀ : ℝ} (hr : Tendsto r atTop (𝓝 r₀)) :
    Tendsto (fun m => x + (r m : EReal)) atTop (𝓝 (x + (r₀ : EReal))) :=
  ((EReal.continuousAt_add (p := (x, (r₀ : EReal))) (Or.inr (EReal.coe_ne_bot _))
    (Or.inr (EReal.coe_ne_top _))).tendsto).comp
    (tendsto_const_nhds.prodMk_nhds ((continuous_coe_real_ereal.tendsto r₀).comp hr))

/-- `x + r - r = x` in `EReal` for real `r`. -/
theorem ereal_add_coe_sub_coe (x : EReal) (r : ℝ) : x + (r : EReal) - (r : EReal) = x := by
  rw [sub_eq_add_neg, ← EReal.coe_neg]
  exact ProjBerk.ereal_add_coe_add_neg x r

/-- A localization `A_f` of a finitely generated `k`-algebra `A` is finitely generated. -/
theorem finiteType_localizationAway {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (f : A) : Algebra.FiniteType k (Localization.Away f) :=
  have : Algebra.FiniteType A (Localization.Away f) :=
    have := IsLocalization.Away.finitePresentation (S := Localization.Away f) f
    Algebra.FiniteType.of_finitePresentation
  Algebra.FiniteType.trans (S := A) inferInstance inferInstance

end NonflatExtension

open NonflatExtension

/-! ### The extension step on the chart `U_{xⱼ t} ≃ (Spec k[y]_{dehom t})^an` -/

namespace ProjBerk

variable {k : Type u} [Field k] {n : ℕ} (j : Fin (n + 1)) {d : ℕ}
  {t : MvPolynomial (Fin (n + 1)) k}

/-- The real number `log |xⱼ t|_v` at the point `v` of `U_{xⱼ t}` attached by the chart
`mulChart` to `y ∈ S^an`, `S = Spec k[y]_{dehom t}`. -/
def chartLog (ht : t.IsHomogeneous d) (y : Berk k (Localization.Away (dehom j t))) : ℝ :=
  Real.log (((mulChart j ht).symm y : ProjBerk k n).1.val (X j * t) : ℝ)

/-- The point of `U_{xⱼ t}` attached to `y` lies in `U_{xⱼ t}`. -/
theorem val_mulChart_symm_ne_zero (ht : t.IsHomogeneous d)
    (y : Berk k (Localization.Away (dehom j t))) :
    ((mulChart j ht).symm y : ProjBerk k n).1.val (X j * t) ≠ 0 :=
  ((mulChart j ht).symm y).2

/-- `log|xⱼ t| ≤ 0` on `(ℙⁿ)^an`. -/
theorem chartLog_nonpos (ht : t.IsHomogeneous d) (y : Berk k (Localization.Away (dehom j t))) :
    chartLog j ht y ≤ 0 :=
  real_log_val_le_zero _ _

/-- `log|xⱼ t|` is finite on `U_{xⱼ t}`, equal to `chartLog`. -/
theorem logAbs_mulChart_symm (ht : t.IsHomogeneous d)
    (y : Berk k (Localization.Away (dehom j t))) :
    logAbs (X j * t) ((mulChart j ht).symm y) = (chartLog j ht y : EReal) :=
  logAbs_eq_coe_log (val_mulChart_symm_ne_zero j ht y)

/-- `chartLog` is continuous on `S^an`. -/
theorem continuous_chartLog (ht : t.IsHomogeneous d) : Continuous (chartLog (n := n) j ht) := by
  refine Continuous.log ?_ fun y => NNReal.coe_ne_zero.2 (val_mulChart_symm_ne_zero j ht y)
  have hc : Continuous fun y : Berk k (Localization.Away (dehom j t)) =>
      ((mulChart j ht).symm y : ProjBerk k n) :=
    (mulChart j ht).symm.continuous.subtype_val
  exact NNReal.continuous_coe.comp ((Berk.continuous_abs (X j * t)).comp
    (continuous_val.comp hc))

/-- Every `f ∈ k[y]_{dehom t} = A_{xⱼ t}` satisfies `|f| ≤ |xⱼ t|^{-N}` for some `N`, since
`f = τ / (xⱼ t)^N` with `|τ| ≤ 1`. -/
theorem exists_val_le_exp_chartLog (ht : t.IsHomogeneous d)
    (f : Localization.Away (dehom j t)) :
    ∃ N : ℕ, ∀ y : Berk k (Localization.Away (dehom j t)),
      (y.val f : ℝ) ≤ Real.exp (-(N : ℝ) * chartLog j ht y) := by
  obtain ⟨N, τ, hτ, he⟩ :=
    exists_eq_chartMk (isHomogeneous_X_mul j ht) ((mulChartEquiv j ht).symm f)
  refine ⟨N, fun y => ?_⟩
  have hval : ∀ v : chartDomain (X j * t),
      (mulChart j ht v).val f = v.1.1.val τ / v.1.1.val (X j * t) ^ N := fun v => by
    rw [mulChart, Homeomorph.trans_apply, Berk.homeomorphOfAlgEquiv_val_apply, he,
      chartHomeomorph_val_chartMk _ _ _ hτ]
  have h1 := hval ((mulChart j ht).symm y)
  rw [Homeomorph.apply_symm_apply] at h1
  rw [h1, chartLog]
  have hs : (0 : ℝ) < (((mulChart j ht).symm y : ProjBerk k n).1.val (X j * t) : ℝ) :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2 (val_mulChart_symm_ne_zero j ht y))
  have hτ1 : ((((mulChart j ht).symm y : ProjBerk k n).1.val τ : ℝ≥0) : ℝ) ≤ 1 := by
    exact_mod_cast val_le_one _ τ
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hs, NNReal.coe_div, NNReal.coe_pow,
    ← one_div]
  gcongr

/-- **Growth of affine FS functions on `S ⊆ 𝔸ⁿ`** (`lem:nonflat-extension`, step (2)): every
`g ∈ FS(S)` satisfies `g ≤ -κ log|xⱼ t| + C` on `S^an` for a rational `κ > 0`. -/
theorem exists_eval_le_chartLog (ht : t.IsHomogeneous d)
    (g : EnvelopeProperty.FSData k (Localization.Away (dehom j t))) :
    ∃ κ : ℚ, 0 < κ ∧ ∃ C : ℝ, ∀ y,
      g.eval y ≤ ((-(κ : ℝ) * chartLog j ht y + C : ℝ) : EReal) := by
  classical
  choose N hN using exists_val_le_exp_chartLog j ht
  have hpos : ∀ s ∈ g.terms, (0 : ℚ) ≤ s.2.1 * N s.1 := fun s hs =>
    mul_nonneg (g.pos s hs).le (Nat.cast_nonneg _)
  refine ⟨1 + ∑ s ∈ g.terms, s.2.1 * N s.1,
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg hpos),
    |(g.const : ℝ)| + ∑ s ∈ g.terms, |(s.2.2 : ℝ)|, fun y => ?_⟩
  have hL := chartLog_nonpos j ht y
  have hS0 : (0 : ℝ) ≤ ∑ s ∈ g.terms, (s.2.1 : ℝ) * N s.1 :=
    Finset.sum_nonneg fun s hs => by exact_mod_cast hpos s hs
  have hB0 : (0 : ℝ) ≤ ∑ s ∈ g.terms, |(s.2.2 : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [EnvelopeProperty.FSData.eval_def]
  refine max_le ?_ (Finset.sup_le fun s hs => ?_)
  · rw [EReal.coe_le_coe_iff]
    push_cast
    nlinarith [le_abs_self (g.const : ℝ)]
  · refine (fsTerm_le_of_abs_le_exp (g.pos s hs) (hN s.1 y)).trans ?_
    rw [EReal.coe_le_coe_iff]
    push_cast
    have h1 : (s.2.1 : ℝ) * N s.1 ≤ ∑ s ∈ g.terms, (s.2.1 : ℝ) * N s.1 :=
      Finset.single_le_sum (f := fun s : _ × ℚ × ℚ => (s.2.1 : ℝ) * N s.1)
        (fun s hs => by exact_mod_cast hpos s hs) hs
    have h2 : (s.2.2 : ℝ) ≤ ∑ s ∈ g.terms, |(s.2.2 : ℝ)| :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun s : _ × ℚ × ℚ => |(s.2.2 : ℝ)|)
        (fun _ _ => abs_nonneg _) hs)
    have h3 := mul_le_mul_of_nonneg_right h1 (neg_nonneg.2 hL)
    nlinarith [abs_nonneg (g.const : ℝ)]

/-- **The extension step of FHX Proposition 5.22 on a chart** (`lem:nonflat-extension`). Let
`n ≥ 1`, `t` a nonzero form of degree `d`, `S = Spec k[y]_{dehom t} ⊆ 𝔸ⁿ` (identified with the
chart `U_{xⱼ t}` of `ℙⁿ`), `0 ≠ f ∈ k[S]`, and `v₀ ∈ ℛ(S_f)` with `v₀ ≤ g + B` for some
`g ∈ FS(S)`. If every rational class `a > 0` on `ℙⁿ` has the envelope property, then `v₀` extends
to some `v ∈ ℛ(S)`. -/
theorem exists_extend_mulChart [IsAlgClosed k] [Countable k] [WuRegularization.{u, u} k]
    (hn : n ≠ 0) (hEP : ∀ a : ℚ, 0 < a → HasEnvelopeProperty k n (a : ℝ))
    (ht : t.IsHomogeneous d) (ht0 : t ≠ 0) {f : Localization.Away (dehom j t)} (hf : f ≠ 0)
    {v₀ : Berk k (Localization.Away f) → EReal} (hv₀ : IsRegularizable v₀)
    (g : EnvelopeProperty.FSData k (Localization.Away (dehom j t))) (B : ℝ)
    (hv₀g : ∀ y, v₀ y ≤ g.eval (Berk.awayComap f y) + (B : EReal)) :
    ∃ v : Berk k (Localization.Away (dehom j t)) → EReal, IsRegularizable v ∧
      ∀ y, v (Berk.awayComap f y) = v₀ y := by
  classical
  have hdt : dehom j t ≠ 0 := dehom_ne_zero j ht ht0
  have : IsDomain (Localization.Away (dehom j t)) := Berk.isDomain_localizationAway hdt
  have : IsIntegrallyClosed (Localization.Away (dehom j t)) :=
    isIntegrallyClosed_localizationAway hdt
  have : Algebra.FiniteType k (Localization.Away (dehom j t)) :=
    Algebra.FiniteType.equiv (finiteType_chartAlg (isHomogeneous_X_mul j ht)) (mulChartEquiv j ht)
  /- Step (2): growth bounds `g ≤ -κ_g log|σ| + C_g` and `|f| ≤ |σ|^{-N_f}`. -/
  obtain ⟨κg, hκg, Cg, hg⟩ := exists_eval_le_chartLog j ht g
  obtain ⟨Nf, hNf⟩ := exists_val_le_exp_chartLog j ht f
  set κ : ℚ := κg + Nf with hκdef
  have hκ : 0 < κ := add_pos_of_pos_of_nonneg hκg (Nat.cast_nonneg _)
  set B₀ : ℝ := B + Cg with hB₀def
  /- Step (3): the extensions `w i` of `v₀ + c i log|f|`, `c i = 1 / (i + 1)`. -/
  set c : ℕ → ℚ := fun i => 1 / ((i : ℚ) + 1) with hcdef
  have hc : ∀ i, (0 : ℝ) < c i := fun i => by simp only [hcdef]; push_cast; positivity
  have hc1 : ∀ i, (c i : ℝ) ≤ 1 := fun i => by
    simp only [hcdef]; push_cast
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have hcanti : Antitone fun i => (c i : ℝ) := fun i i' hii' => by
    simp only [hcdef]; push_cast
    gcongr
  have hclim : Tendsto (fun i => (c i : ℝ)) atTop (𝓝 0) := by
    simp only [hcdef]; push_cast
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  set w : ℕ → Berk k (Localization.Away (dehom j t)) → EReal := fun i =>
    awayExtend f fun y => v₀ y + ((c i : ℝ) : EReal) * Berk.logAbs f (Berk.awayComap f y)
    with hwdef
  have hw : ∀ i, IsRegularizable (w i) := fun i =>
    hv₀.awayExtend_add hf g B hv₀g (by exact_mod_cast hc i)
  have hwB : ∀ i x, w i x ≤
      -((κ : ℝ) : EReal) * logAbs (X j * t) ((mulChart j ht).symm x) + (B₀ : EReal) := by
    intro i x
    rw [logAbs_mulChart_symm]
    by_cases hx : x.val f = 0
    · simp only [hwdef]
      rw [awayExtend_of_eq_zero f _ hx]
      exact bot_le
    · simp only [hwdef]
      rw [awayExtend_of_ne_zero f _ hx, Berk.awayComap_awayLift]
      have h1 := hv₀g (Berk.awayLift f x hx)
      rw [Berk.awayComap_awayLift] at h1
      have hxpos : (0 : ℝ) < x.val f := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hx)
      have h3 : Real.log (x.val f : ℝ) ≤ -(Nf : ℝ) * chartLog j ht x :=
        (Real.log_le_iff_le_exp hxpos).2 (hNf x)
      have hL := chartLog_nonpos j ht x
      have h4 : (c i : ℝ) * Real.log (x.val f : ℝ) ≤ -(Nf : ℝ) * chartLog j ht x := by
        have h5 := mul_le_mul_of_nonneg_left h3 (hc i).le
        have h6 : 0 ≤ -(Nf : ℝ) * chartLog j ht x := by
          have : (0 : ℝ) ≤ Nf := Nat.cast_nonneg _
          nlinarith
        have h7 := mul_le_of_le_one_left h6 (hc1 i)
        linarith
      rw [Berk.logAbs_eq_coe_log hx, ← EReal.coe_mul]
      calc v₀ (Berk.awayLift f x hx) + (((c i : ℝ) * Real.log (x.val f : ℝ) : ℝ) : EReal)
          ≤ (g.eval x + (B : EReal)) + ((-(Nf : ℝ) * chartLog j ht x : ℝ) : EReal) :=
            add_le_add h1 (EReal.coe_le_coe_iff.2 h4)
        _ ≤ ((-(κg : ℝ) * chartLog j ht x + Cg : ℝ) : EReal) + (B : EReal) +
            ((-(Nf : ℝ) * chartLog j ht x : ℝ) : EReal) :=
            add_le_add (add_le_add (hg x) le_rfl) le_rfl
        _ = -((κ : ℝ) : EReal) * (chartLog j ht x : EReal) + (B₀ : EReal) := by
          rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_mul, ← EReal.coe_add,
            EReal.coe_eq_coe_iff, hκdef, hB₀def]
          push_cast
          ring
  /- Step (4): the compactified functions `φ i ∈ PSH(a (d + 1))`, bounded by `B₀`. -/
  set a : ℚ := κ + 1 with hadef
  have hκa : κ < a := lt_add_one κ
  have ha : 0 < a := hκ.trans hκa
  set φ : ℕ → ProjBerk k n → EReal := fun i => mulChartExt j ht (w i) a with hφdef
  have hφ : ∀ i, IsPSH ((a : ℝ) * (d + 1 : ℕ)) (φ i) := fun i =>
    isPSH_mulChartExt j hn ht ht0 (hw i) hκ (hwB i) hκa
  have hφB : ∀ i v, φ i v ≤ (B₀ : EReal) := by
    intro i v
    by_cases hv : v ∈ chartDomain (X j * t)
    · simp only [hφdef]
      rw [mulChartExt_of_mem j ht _ _ hv]
      have h1 := hwB i (mulChart j ht ⟨v, hv⟩)
      rw [Homeomorph.symm_apply_apply] at h1
      have hLv : logAbs (X j * t) v = ((Real.log (v.1.val (X j * t) : ℝ) : ℝ) : EReal) :=
        logAbs_eq_coe_log hv
      rw [hLv] at h1 ⊢
      have hle := real_log_val_le_zero (X j * t) v
      have hκa' : (κ : ℝ) < a := by exact_mod_cast hκa
      calc w i (mulChart j ht ⟨v, hv⟩) +
            ((a : ℝ) : EReal) * ((Real.log (v.1.val (X j * t) : ℝ) : ℝ) : EReal)
          ≤ (-((κ : ℝ) : EReal) * ((Real.log (v.1.val (X j * t) : ℝ) : ℝ) : EReal) +
              (B₀ : EReal)) +
            ((a : ℝ) : EReal) * ((Real.log (v.1.val (X j * t) : ℝ) : ℝ) : EReal) :=
            add_le_add h1 le_rfl
        _ ≤ (B₀ : EReal) := by
          rw [← EReal.coe_neg, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_add,
            EReal.coe_le_coe_iff]
          nlinarith
    · simp only [hφdef]
      rw [mulChartExt_of_not_mem j ht _ _ hv]
      exact bot_le
  /- Step (5): `ψ m = (sup_{i ≥ m} φ i)^⋆ ∈ PSH(a (d + 1))`, decreasing to `Ψ`. -/
  have hEPθ : HasEnvelopeProperty k n ((a : ℝ) * (d + 1 : ℕ)) := by
    have e : (((a * ((d + 1 : ℕ) : ℚ)) : ℚ) : ℝ) = (a : ℝ) * ((d + 1 : ℕ) : ℝ) := by
      push_cast; ring
    have := hEP (a * ((d + 1 : ℕ) : ℚ)) (by positivity)
    rwa [e] at this
  set ψ : ℕ → ProjBerk k n → EReal := fun m => uscReg fun v => ⨆ i : {i : ℕ // m ≤ i}, φ i v
    with hψdef
  have hψ : ∀ m, IsPSH ((a : ℝ) * (d + 1 : ℕ)) (ψ m) := fun m =>
    haveI : Nonempty {i : ℕ // m ≤ i} := ⟨⟨m, le_rfl⟩⟩
    hEPθ.isPSH_uscReg_iSup (fun i => hφ i.1) ⟨B₀, fun i v => hφB i.1 v⟩
  have hψanti : ∀ v, Antitone fun m => ψ m v := by
    intro v m m' hmm'
    have hle : (fun v' => ⨆ i : {i : ℕ // m' ≤ i}, φ i v') ≤
        fun v' => ⨆ i : {i : ℕ // m ≤ i}, φ i v' := fun v' =>
      iSup_le fun i => le_iSup_of_le (⟨i.1, hmm'.trans i.2⟩ : {i : ℕ // m ≤ i}) le_rfl
    exact uscReg_mono hle v
  set Ψ : ProjBerk k n → EReal := fun v => ⨅ m, ψ m v with hΨdef
  /- Step (6): `Ψ = v₀ + a log|σ|` on `S_f^an`. -/
  set T : Berk k (Localization.Away f) → ProjBerk k n := fun y =>
    ((mulChart j ht).symm (Berk.awayComap f y) : ProjBerk k n) with hTdef
  have hT : IsOpenEmbedding T :=
    ((isOpen_chartDomain (X j * t)).isOpenEmbedding_subtypeVal.comp
      (mulChart j ht).symm.isOpenEmbedding).comp (Berk.isOpenEmbedding_awayComap f)
  set ℓ : Berk k (Localization.Away f) → ℝ := fun y =>
    Real.log ((Berk.awayComap f y).val f : ℝ) with hℓdef
  have hℓ : Continuous ℓ := by
    refine Continuous.log ?_ fun y => NNReal.coe_ne_zero.2 (Berk.awayComap_val_ne_zero f y)
    exact NNReal.continuous_coe.comp ((Berk.continuous_abs f).comp (Berk.continuous_awayComap f))
  have hℓeq : ∀ y, Berk.logAbs f (Berk.awayComap f y) = (ℓ y : EReal) := fun y =>
    Berk.logAbs_eq_coe_log (Berk.awayComap_val_ne_zero f y)
  set L : Berk k (Localization.Away f) → ℝ := fun y => chartLog j ht (Berk.awayComap f y)
    with hLdef
  have hL : Continuous L := (continuous_chartLog j ht).comp (Berk.continuous_awayComap f)
  have hφT : ∀ i y, φ i (T y) = v₀ y + (((c i : ℝ) * ℓ y + (a : ℝ) * L y : ℝ) : EReal) := by
    intro i y
    simp only [hφdef, hTdef]
    rw [mulChartExt_mulChart_symm, logAbs_mulChart_symm]
    simp only [hwdef]
    rw [awayExtend_awayComap, hℓeq, add_assoc, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  have hΨT : ∀ y, Ψ (T y) = v₀ y + (((a : ℝ) * L y : ℝ) : EReal) := by
    intro y
    have hlim : Tendsto (fun i => φ i (T y)) atTop
        (𝓝 (v₀ y + (((a : ℝ) * L y : ℝ) : EReal))) := by
      simp only [hφT]
      refine ereal_tendsto_add_coe (v₀ y) ?_
      simpa using (hclim.mul_const (ℓ y)).add_const ((a : ℝ) * L y)
    have hlim' : Tendsto (fun m => v₀ y +
        ((((c m : ℝ) * max (ℓ y) 0 + (a : ℝ) * L y) : ℝ) : EReal)) atTop
        (𝓝 (v₀ y + (((a : ℝ) * L y : ℝ) : EReal))) := by
      refine ereal_tendsto_add_coe (v₀ y) ?_
      simpa using (hclim.mul_const (max (ℓ y) 0)).add_const ((a : ℝ) * L y)
    have hup : ∀ m, Ψ (T y) ≤
        v₀ y + ((((c m : ℝ) * max (ℓ y) 0 + (a : ℝ) * L y) : ℝ) : EReal) := by
      intro m
      set G : Berk k (Localization.Away f) → EReal := fun y' => v₀ y' +
        ((((c m : ℝ) * max (ℓ y') 0 + (a : ℝ) * L y') : ℝ) : EReal) with hGdef
      have hG : UpperSemicontinuous G := upperSemicontinuous_add_coe hv₀.upperSemicontinuous
        ((continuous_const.mul (hℓ.max continuous_const)).add (continuous_const.mul hL))
      have hle : (fun v => ⨆ i : {i : ℕ // m ≤ i}, φ i v) ≤
          Function.extend T G fun _ => ⊤ := by
        intro v
        by_cases hv : ∃ y', T y' = v
        · obtain ⟨y', rfl⟩ := hv
          rw [hT.injective.extend_apply]
          refine iSup_le fun i => ?_
          rw [hφT, hGdef]
          refine add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)
          have h1 : (c i.1 : ℝ) ≤ c m := hcanti i.2
          have h2 := mul_le_mul_of_nonneg_left (le_max_left (ℓ y') 0) (hc i.1).le
          have h3 := mul_le_mul_of_nonneg_right h1 (le_max_right (ℓ y') 0)
          linarith
        · rw [Function.extend_apply' _ _ _ hv]
          exact le_top
      calc Ψ (T y) ≤ ψ m (T y) := iInf_le (fun m => ψ m (T y)) m
        _ ≤ Function.extend T G (fun _ => ⊤) (T y) :=
          uscReg_le_of_le (upperSemicontinuous_extend_top hT hG) hle (T y)
        _ = G y := hT.injective.extend_apply _ _ _
    have hlow : ∀ m, v₀ y + (((a : ℝ) * L y : ℝ) : EReal) ≤ ψ m (T y) := by
      intro m
      refine le_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop m] with i hi
      exact (le_iSup_of_le (f := fun i : {i : ℕ // m ≤ i} => φ i (T y)) ⟨i, hi⟩ le_rfl).trans
        (le_uscReg (fun v => ⨆ i : {i : ℕ // m ≤ i}, φ i v) (T y))
    exact le_antisymm (ge_of_tendsto' hlim' hup) (le_iInf hlow)
  have hΨfin : ∃ v, Ψ v ≠ ⊥ := by
    obtain ⟨y₀, hy₀⟩ := hv₀.1
    exact ⟨T y₀, by rw [hΨT]; exact ereal_add_coe_ne_bot hy₀ _⟩
  have hΨ : IsPSH ((a : ℝ) * (d + 1 : ℕ)) Ψ :=
    isPSH_of_antitone_seq tendsto_const_nhds hψ hψanti (fun v => rfl) hΨfin
  /- Step (7): `v = (Ψ - a log|σ|)|_{S^an} ∈ ℛ(S)` and `v = v₀` on `S_f^an`. -/
  have hreg := IsPSH.isRegularizable_mulChart j ht ht0 ha hΨ
  refine ⟨_, hreg, fun y => ?_⟩
  rw [logAbs_mulChart_symm]
  have e1 : ((mulChart j ht).symm (Berk.awayComap f y) : ProjBerk k n) = T y := rfl
  rw [e1, hΨT, ← EReal.coe_mul]
  exact ereal_add_coe_sub_coe _ _

end ProjBerk

/-! ### The extension step for principal opens of `𝔸ⁿ` -/

/-- **The extension step of FHX Proposition 5.22** (`lem:nonflat-extension`, the "Extension"
paragraph of `prop:nonflat-norm`), **conditional on the imported `WuRegularization`** (FHX
Lemma 5.11(5),(6); an explicit hypothesis, not an axiom) and on the envelope property of the
rational classes of `ℙⁿ`. Let `k` be countable and algebraically closed, `n ≥ 1`,
`S = Spec k[y₁, …, yₙ]_{h_S}` a principal open of `𝔸ⁿ`, `0 ≠ h ∈ k[S]` and `v₀ ∈ ℛ(S_h)` with
`v₀ ≤ g + B` on `S_h^an` for some `g ∈ FS(S)` and `B ∈ ℝ`. Then there is `v ∈ ℛ(S)` with `v = v₀`
on `S_h^an`. -/
theorem IsRegularizable.exists_extend_of_hasEnvelopeProperty {k : Type u} [Field k]
    [IsAlgClosed k] [Countable k] [WuRegularization.{u, u} k] {n : ℕ} (hn : 1 ≤ n)
    (hEP : ∀ a : ℚ, 0 < a → ProjBerk.HasEnvelopeProperty k n (a : ℝ))
    {hS : MvPolynomial (Fin n) k} (hS0 : hS ≠ 0) {h : Localization.Away hS} (hh : h ≠ 0)
    {v₀ : Berk k (Localization.Away h) → EReal} (hv₀ : IsRegularizable v₀)
    (g : FSData k (Localization.Away hS)) (B : ℝ)
    (hv₀g : ∀ y, v₀ y ≤ g.eval (Berk.awayComap h y) + (B : EReal)) :
    ∃ v : Berk k (Localization.Away hS) → EReal, IsRegularizable v ∧
      ∀ y, v (Berk.awayComap h y) = v₀ y := by
  obtain ⟨d, t, ht, rfl⟩ := ProjBerk.exists_dehom_eq (0 : Fin (n + 1)) hS
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hS0 (map_zero _)
  exact ProjBerk.exists_extend_mulChart 0 (by omega) hEP ht ht0 hh hv₀ g B hv₀g

/-- **The extension step of FHX Proposition 5.22 in characteristic `p`** (`lem:nonflat-extension`
with `thm:pn-ep-charp`): the envelope property of `ℙⁿ` holds by
`ProjBerk.hasEnvelopeProperty_of_charP`, so only the imported `WuRegularization` remains as a
hypothesis. -/
theorem IsRegularizable.exists_extend_of_charP {k : Type u} [Field k] [IsAlgClosed k]
    [Countable k] [WuRegularization.{u, u} k] (p : ℕ) [Fact p.Prime] [CharP k p] {n : ℕ}
    (hn : 1 ≤ n) {hS : MvPolynomial (Fin n) k} (hS0 : hS ≠ 0) {h : Localization.Away hS}
    (hh : h ≠ 0) {v₀ : Berk k (Localization.Away h) → EReal} (hv₀ : IsRegularizable v₀)
    (g : FSData k (Localization.Away hS)) (B : ℝ)
    (hv₀g : ∀ y, v₀ y ≤ g.eval (Berk.awayComap h y) + (B : EReal)) :
    ∃ v : Berk k (Localization.Away hS) → EReal, IsRegularizable v ∧
      ∀ y, v (Berk.awayComap h y) = v₀ y :=
  hv₀.exists_extend_of_hasEnvelopeProperty hn
    (fun _ ha => ProjBerk.hasEnvelopeProperty_of_charP p n (by exact_mod_cast ha.le))
    hS0 hh g B hv₀g

/-- **The extension step of FHX Proposition 5.22 for a principal open of `𝔸ⁿ` given up to
isomorphism** (`lem:nonflat-extension`, in the encoding `IsAffineSpacePrincipalOpen k B n` of
`EnvelopeProperty.Local.NonflatImport`): the statement of
`IsRegularizable.exists_extend_of_hasEnvelopeProperty` transported along
`B ≃ₐ[k] k[y]_{h_S}`. -/
theorem IsRegularizable.exists_extend_of_isAffineSpacePrincipalOpen {k : Type u} [Field k]
    [IsAlgClosed k] [Countable k] [WuRegularization.{u, u} k] {B : Type*} [CommRing B]
    [Algebra k B] {n : ℕ} (hn : 1 ≤ n) (hB : IsAffineSpacePrincipalOpen k B n)
    (hEP : ∀ a : ℚ, 0 < a → ProjBerk.HasEnvelopeProperty k n (a : ℝ))
    {h : B} (hh : h ≠ 0) {v₀ : Berk k (Localization.Away h) → EReal} (hv₀ : IsRegularizable v₀)
    (g : FSData k B) (C : ℝ) (hv₀g : ∀ y, v₀ y ≤ g.eval (Berk.awayComap h y) + (C : EReal)) :
    ∃ v : Berk k B → EReal, IsRegularizable v ∧ ∀ y, v (Berk.awayComap h y) = v₀ y := by
  have hBft := hB.finiteType
  obtain ⟨hS, hS0, ⟨E⟩⟩ := hB
  have hSft : Algebra.FiniteType k (Localization.Away hS) := finiteType_localizationAway hS
  set h' : Localization.Away hS := E h with hh'def
  have hh' : h' ≠ 0 := (map_ne_zero_iff _ E.injective).2 hh
  have hh'ft : Algebra.FiniteType k (Localization.Away h') := finiteType_localizationAway h'
  -- `F : B_h ≃ k[y]_{h_S, E h}` extending `E`.
  set F : Localization.Away h ≃ₐ[k] Localization.Away h' :=
    IsLocalization.algEquivOfAlgEquiv (Localization.Away h) (Localization.Away h') E
      (Submonoid.map_powers E h) with hFdef
  have hF : ∀ b : B, F (algebraMap B (Localization.Away h) b) =
      algebraMap (Localization.Away hS) (Localization.Away h') (E b) := fun b =>
    IsLocalization.algEquivOfAlgEquiv_eq _ b
  have hFsymm : ∀ a : Localization.Away hS, F.symm (algebraMap _ (Localization.Away h') a) =
      algebraMap B (Localization.Away h) (E.symm a) := fun a => by
    rw [AlgEquiv.symm_apply_eq, hF, AlgEquiv.apply_symm_apply]
  -- Transport `v₀` and `g`.
  set v₀' : Berk k (Localization.Away h') → EReal := fun z =>
    v₀ (Berk.comap (F : Localization.Away h →ₐ[k] Localization.Away h') z) with hv₀'def
  have hv₀' : IsRegularizable v₀' := by
    obtain ⟨y₀, hy₀⟩ := hv₀.1
    refine hv₀.comp_comap (F : Localization.Away h →ₐ[k] Localization.Away h')
      ⟨Berk.comap (F.symm : Localization.Away h' →ₐ[k] Localization.Away h) y₀, ?_⟩
    rw [Berk.comap_comap_symm]
    exact hy₀
  set g' : FSData k (Localization.Away hS) :=
    FSData.mapSup (E : B →ₐ[k] Localization.Away hS) g (FSData.std k (Localization.Away hS))
    with hg'def
  have hcomm : ∀ z : Berk k (Localization.Away h'),
      Berk.awayComap h (Berk.comap (F : Localization.Away h →ₐ[k] Localization.Away h') z) =
        Berk.comap (E : B →ₐ[k] Localization.Away hS) (Berk.awayComap h' z) := fun z =>
    Berk.ext_val fun b => by
      simp only [Berk.awayComap_val_apply, Berk.comap_val_apply]
      exact congrArg z.val (hF b)
  have hv₀'g : ∀ z, v₀' z ≤ g'.eval (Berk.awayComap h' z) + (C : EReal) := fun z => by
    refine (hv₀g _).trans (add_le_add ?_ le_rfl)
    rw [hcomm, hg'def, FSData.eval_mapSup]
    exact le_max_left _ _
  obtain ⟨v', hv', hv'eq⟩ :=
    hv₀'.exists_extend_of_hasEnvelopeProperty hn hEP hS0 hh' g' C hv₀'g
  -- Transport back along `E`.
  refine ⟨fun x => v' (Berk.comap (E.symm : Localization.Away hS →ₐ[k] B) x), ?_, fun y => ?_⟩
  · obtain ⟨x₀, hx₀⟩ := hv'.1
    refine hv'.comp_comap (E.symm : Localization.Away hS →ₐ[k] B)
      ⟨Berk.comap (E : B →ₐ[k] Localization.Away hS) x₀, ?_⟩
    rw [Berk.comap_symm_comap]
    exact hx₀
  · have hcomm' : Berk.comap (E.symm : Localization.Away hS →ₐ[k] B) (Berk.awayComap h y) =
        Berk.awayComap h'
          (Berk.comap (F.symm : Localization.Away h' →ₐ[k] Localization.Away h) y) :=
      Berk.ext_val fun a => by
        simp only [Berk.awayComap_val_apply, Berk.comap_val_apply]
        exact congrArg y.val (hFsymm a).symm
    simp only
    rw [hcomm', hv'eq, hv₀'def]
    simp only
    rw [Berk.comap_comap_symm]

/-- **The extension step of FHX Proposition 5.22 in characteristic `p`, for a principal open of
`𝔸ⁿ` given up to isomorphism**: `IsRegularizable.exists_extend_of_isAffineSpacePrincipalOpen` with
the envelope property of `ℙⁿ` supplied by `ProjBerk.hasEnvelopeProperty_of_charP`. -/
theorem IsRegularizable.exists_extend_of_isAffineSpacePrincipalOpen_of_charP {k : Type u}
    [Field k] [IsAlgClosed k] [Countable k] [WuRegularization.{u, u} k] (p : ℕ) [Fact p.Prime]
    [CharP k p] {B : Type*} [CommRing B] [Algebra k B] {n : ℕ} (hn : 1 ≤ n)
    (hB : IsAffineSpacePrincipalOpen k B n) {h : B} (hh : h ≠ 0)
    {v₀ : Berk k (Localization.Away h) → EReal} (hv₀ : IsRegularizable v₀) (g : FSData k B)
    (C : ℝ) (hv₀g : ∀ y, v₀ y ≤ g.eval (Berk.awayComap h y) + (C : EReal)) :
    ∃ v : Berk k B → EReal, IsRegularizable v ∧ ∀ y, v (Berk.awayComap h y) = v₀ y :=
  hv₀.exists_extend_of_isAffineSpacePrincipalOpen hn hB
    (fun _ ha => ProjBerk.hasEnvelopeProperty_of_charP p n (by exact_mod_cast ha.le)) hh g C hv₀g

end EnvelopeProperty
