/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.BlowupChart
import EnvelopeProperty.Projective.BlowupPSH
import EnvelopeProperty.Projective.SubvarietyCompactification

/-!
# Psh descent along blowups: the charts

This file proves the two chart lemmas of the descent of plurisubharmonicity along blowups,
Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX), Corollary 5.26
(`cor:normal-weak-global`), in the model of the blueprint chapter `projective-general.tex`
(subsection `subsec:pg-descent`): `lem:pg-descent-weakly-psh` (FHX Lemma 5.4(2) on the blowup `X'`,
in the charts of the blowup) and `lem:pg-descent-cover` (FHX Lemma 5.10(1) on `X'` over the locus
where `μ` is an isomorphism). The theorem itself (`thm:pg-psh-descent`) is
`ProjSubvariety.isPSH_of_isPSH_comp_proj` in `EnvelopeProperty.Projective.BlowupDescent`.

## Setting (`conv:pg-descent`)

`X = V(I) ⊆ ℙ^M` is a projective subvariety (`ProjSubvariety k M`, here called `V`),
`B : V.BlowupCenter M'` are forms `G₀, …, G_{M'}` of one degree `d`, not all in `I`, and
`μ = B.proj : X'^an → X^an` is the blowup model (`EnvelopeProperty.Projective.BlowupModel`); `φ`
is a function on `X^an` with `φ ∘ μ ∈ PSH(X', (a, 0))` (`BlowupCenter.IsPSH`, `a ∈ ℚ`). For `i`
with `x_i ∉ I` (equivalently `A_i = QuotChartAlg I x_i 1` is a domain), `ι_i` is the chart
`U_{x_i} ∩ X^an ≅ (Spec A_i)^an` (`ProjSubvariety.chartMap`, `ProjSubvariety.chartInv`) and
`𝔞_i = B.centerSet i = {g_{im} = Ḡ_m / x̄_i^d}`; the blowup of `Spec A_i` along `𝔞_i` has the charts
`Spec A_i[𝔞_i/g]`, `g ∈ 𝔞_i \ {0}` (`EnvelopeProperty.blowupChart`), with the points
`κ(w) = B.chartPoint i hg hg0 w ∈ X'^an` (`EnvelopeProperty.Projective.BlowupChart`).

## Main definitions

* `ProjSubvariety.descentChartFun V i a φ`: the function `u_i = (φ - a log|x_i|) ∘ ι_i⁻¹` on
  `(Spec A_i)^an`.
* `chartToAway k s hg : A[s/g] →ₐ[k] A_g` (`g ≠ 0`): the inclusion of the blowup chart into the
  principal localization, both inside `Frac A`.
* `ProjSubvariety.BlowupCenter.chartTerms`: the terms `(δ(F_t), 1/m, λ_t/m)` on the chart
  `A_i[𝔞_i/g]` of bigraded FS data `m⁻¹ max_t (log|F_t| + λ_t)`, `δ = B.chartHom i g`.

## Main results

* `BlowupCenter.sup_fsTerm_chartTerms`: `m⁻¹ max_t (log|δ(F_t)| + λ_t) = D ∘ κ + a log μ_x +
  b log μ_y` for FS data `D` of class `(a, b)` (`lem:pg-blowup-chart`(2)).
* `BlowupCenter.isRegularizable_descentChartFun_comap_chartMap`: for countable `k`, on each
  chart `Spec A_i[𝔞_i/g]`, `w ↦ u_i(w|_{A_i})` is regularizable; hence
  `BlowupCenter.isDecrConvexPLLimitOn_descentChartFun_comap_chartMap` and
  `BlowupCenter.isWeaklyPSHOn_descentChartFun` (**`lem:pg-descent-weakly-psh`**).
* `BlowupCenter.isRegularizable_descentChartFun_awayComap` (**`lem:pg-descent-cover`**): for
  `g ∈ 𝔞_i \ {0}`, the restriction of `u_i` to `(Spec (A_i)_g)^an` is regularizable.

## Deviations from the blueprint

* The class `a ∈ ℚ` is arbitrary; the blueprint first rescales to `a = 1`.
* `lem:pg-descent-weakly-psh`: the blueprint shows that the functions
  `G_j = m_j⁻¹ max_t (log|δ(F_t)| + λ_t)` are convex PL by a local argument. Here the maxima of
  `G_j` with the FS functions `FSData.truncStd j` (which contain generators of the chart and
  decrease to `-∞`) are FS functions on the chart with the same decreasing limit, so `u_i` is
  even regularizable on each chart; convex PL limits and weak plurisubharmonicity follow
  (`IsRegularizable.isDecrConvexPLLimitOn`, `IsRegularizable.isLocallyPSHOn`).
* `lem:pg-descent-cover`: the blueprint proves it with fixed-class regularization of
  `φ ∘ μ + log|G_l y_l| ∈ PSH(X', (1 + d, 1))` and the graph points over the isomorphism locus
  (FHX Lemma 5.10(1) on `X'`). Here it follows from the chart statement: `A_i[𝔞_i/g] ⊆ (A_i)_g`, so
  `(Spec (A_i)_g)^an` maps to the chart over the inclusion into `(Spec A_i)^an`
  (`comap_chartMap_comap_chartToAway`), and regularizable functions pull back (FHX Lemma 5.11(4),
  `IsRegularizable.comp_comap`). Neither fixed-class regularization nor graph points are needed.

## Implementation notes

As in `EnvelopeProperty.Projective.BlowupChart`, instances on the charts `A[s/g]` of
`A = QuotChartAlg I σ d` are slow to synthesize: we add the shortcut instance
`ProjBerk.instIsDomainBlowupChartQuotChartAlg`, state the algebra generically (`chartToAway`,
`comap_chartMap_triv`), and do the termwise computation by the generic lemma
`fsTerm_eq_inv_mul_add` (rewriting or unifying with metavariables in goals over these charts
times out).
-/

open scoped NNReal ENNReal Topology

open Topology Filter MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

open ProjBerk (QuotChartAlg)

/-! ### Generic blowup charts and auxiliary computations -/

section Generic

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]

/-- The domain structure of a blowup chart `A[s/g] ⊆ Frac A`, as synthesized for a general
domain `A`; used for the shortcut instance `ProjBerk.instIsDomainBlowupChartQuotChartAlg`. -/
abbrev blowupChartIsDomain (s : Finset A) (g : A) : IsDomain (blowupChart s g) := inferInstance

/-- The chart map `A → A[s/g]` is injective, so it maps the trivial valuation of `A[s/g]` to the
trivial valuation of `A`. -/
theorem comap_chartMap_triv (s : Finset A) (g : A) :
    Berk.comap (chartMap k s g) (Berk.triv : Berk k (blowupChart s g)) = Berk.triv := by
  refine Berk.ext (Valuation.ext fun f => ?_)
  rw [Berk.comap_val_apply]
  by_cases hf : f = 0
  · rw [hf, map_zero, map_zero, map_zero]
  · rw [Berk.triv_val_of_ne_zero hf, Berk.triv_val_of_ne_zero
      ((map_ne_zero_iff _ (chartMap_injective s g)).2 hf)]

/-- For `g ≠ 0`, the `A`-algebra map `A[s/g] → A_g`: both are subrings of `Frac A`
(`Localization.mapToFractionRing`), and `A[s/g] ⊆ A_g` since `h/g = h · g⁻¹`. -/
def chartToAwayAux (s : Finset A) {g : A} (hg : g ≠ 0) :
    blowupChart s g →ₐ[A] Localization.Away g :=
  let hS : Submonoid.powers g ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hg
  let ι : Localization.Away g →ₐ[A] FractionRing A :=
    Localization.mapToFractionRing (FractionRing A) (Submonoid.powers g) (Localization.Away g) hS
  have hle : blowupChart s g ≤ ι.range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨h, -, rfl⟩
    refine ⟨algebraMap A (Localization.Away g) h * IsLocalization.Away.invSelf g, ?_⟩
    have h1 : algebraMap A (FractionRing A) g * ι (IsLocalization.Away.invSelf g) = 1 := by
      rw [← ι.commutes g, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    have hinv : ι (IsLocalization.Away.invSelf g) = (algebraMap A (FractionRing A) g)⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    show ι (algebraMap A (Localization.Away g) h * IsLocalization.Away.invSelf g) =
      algebraMap A (FractionRing A) h / algebraMap A (FractionRing A) g
    rw [map_mul, ι.commutes, hinv, div_eq_mul_inv]
  ((IsLocalization.algEquiv (Submonoid.powers g) ι.range (Localization.Away g)).toAlgHom.comp
    (Subalgebra.inclusion hle))

variable (k) in
/-- For `g ≠ 0`, the `k`-algebra map `A[s/g] → A_g`: on analytifications, `(Spec A_g)^an` maps
to the chart `Spec A[s/g]^an` of the blowup, over the identity of `(Spec A_g)^an ⊆ (Spec A)^an`
(`comap_chartMap_comap_chartToAway`); it is the locus where the blowup is an isomorphism. -/
def chartToAway (s : Finset A) {g : A} (hg : g ≠ 0) :
    blowupChart s g →ₐ[k] Localization.Away g :=
  (chartToAwayAux s hg).restrictScalars k

/-- `A → A[s/g] → A_g` is the localization map. -/
theorem chartToAway_chartMap (s : Finset A) {g : A} (hg : g ≠ 0) (a : A) :
    chartToAway k s hg (chartMap k s g a) = algebraMap A (Localization.Away g) a := by
  rw [chartMap_apply]
  exact (chartToAwayAux s hg).commutes a

/-- `(Spec A_g)^an → Spec A[s/g]^an → (Spec A)^an` is the inclusion `awayComap g`. -/
theorem comap_chartMap_comap_chartToAway (s : Finset A) {g : A} (hg : g ≠ 0)
    (z : Berk k (Localization.Away g)) :
    Berk.comap (chartMap k s g) (Berk.comap (chartToAway k s hg) z) = Berk.awayComap g z := by
  refine Berk.ext (Valuation.ext fun f => ?_)
  rw [Berk.comap_val_apply, Berk.comap_val_apply, chartToAway_chartMap, Berk.awayComap_val_apply]

omit [IsDomain A] in
/-- A localization `A_f` of a finitely generated `k`-algebra `A` is finitely generated. -/
theorem finiteType_localizationAway_of_finiteType [Algebra.FiniteType k A] (f : A) :
    Algebra.FiniteType k (Localization.Away f) :=
  have : Algebra.FiniteType A (Localization.Away f) :=
    have := IsLocalization.Away.finitePresentation (S := Localization.Away f) f
    Algebra.FiniteType.of_finitePresentation
  Algebra.FiniteType.trans (S := A) inferInstance inferInstance

end Generic

/-- `c (L - P + λ) + r = c L + (c (λ - P) + r)` in `EReal`, for `L ≠ +∞` and real `c > 0`, `P`,
`λ`, `r`. -/
theorem ereal_coe_mul_sub_add_add {L : EReal} (hL : L ≠ ⊤) {c : ℝ} (hc : 0 < c) (P lam r : ℝ) :
    (c : EReal) * (L - (P : EReal) + (lam : EReal)) + (r : EReal) =
      (c : EReal) * L + ((c * (lam - P) + r : ℝ) : EReal) := by
  induction L using EReal.rec with
  | bot => simp [EReal.bot_sub, EReal.coe_mul_bot_of_pos hc]
  | coe L =>
    rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul,
      ← EReal.coe_add]
    congr 1
    ring
  | top => exact absurd rfl hL

/-- The form of `ereal_coe_mul_sub_add_add` used on the blowup charts:
`c (L - (p lx + q ly) + λ) + r = c L + (c (λ - (p lx + q ly)) + r)` for natural `p`, `q`. -/
theorem ereal_coe_mul_sub_natCast_add_add {L : EReal} (hL : L ≠ ⊤) {c : ℝ} (hc : 0 < c)
    (p q : ℕ) (lx ly lam r : ℝ) :
    (c : EReal) * (L - ((p : EReal) * (lx : EReal) + (q : EReal) * (ly : EReal)) + (lam : EReal)) +
        (r : EReal) =
      (c : EReal) * L + ((c * (lam - (p * lx + q * ly)) + r : ℝ) : EReal) := by
  rw [← ereal_coe_mul_sub_add_add hL hc]
  push_cast
  rfl

/-- `λ / m = m⁻¹ (λ - (p lx + q ly)) + (a lx + b ly)` for `p = m a`, `q = m b`. -/
theorem div_eq_inv_mul_sub_add {m p q a b : ℝ} (hm : m ≠ 0) (hp : p = m * a) (hq : q = m * b)
    (lx ly lam : ℝ) : lam / m = m⁻¹ * (lam - (p * lx + q * ly)) + (a * lx + b * ly) := by
  subst hp hq
  field_simp
  ring

/-- The term `(f, 1/m, q₀/m)` evaluated at `w`, when `LF = log|f|_w - (p lx + q ly)` with
`p = m a`, `q = m b` and `q₀ = λ`: `m⁻¹ (LF + λ) + (a lx + b ly)`. -/
theorem fsTerm_eq_inv_mul_add {k : Type*} [Field k] {C : Type*} [CommRing C] [Algebra k C]
    (f : C) (w : Berk k C) {m p q : ℕ} (hm : 0 < m) {a b : ℚ} (hp : (p : ℝ) = m * a)
    (hq : (q : ℝ) = m * b) (lx ly lam : ℝ) {q₀ : ℚ} (hq₀ : (q₀ : ℝ) = lam) {LF : EReal}
    (hLF : LF = Berk.logAbs f w - ((p : EReal) * (lx : EReal) + (q : EReal) * (ly : EReal))) :
    fsTerm (f, ((m : ℚ))⁻¹, q₀ / m) w =
      (((m : ℝ)⁻¹ : ℝ) : EReal) * (LF + (lam : EReal)) +
        (((a : ℝ) * lx + (b : ℝ) * ly : ℝ) : EReal) := by
  have hm' : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hm)
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [hLF, ereal_coe_mul_sub_natCast_add_add (Berk.logAbs_ne_top f w) hm', fsTerm_def,
    Rat.cast_inv, Rat.cast_natCast, Rat.cast_div, hq₀, Rat.cast_natCast,
    div_eq_inv_mul_sub_add hmne hp hq]

/-- The real sequence `(a + 2^{-j}) lx + (0 + 2^{-j}) ly` decreases to `a lx` for `lx, ly ≥ 0`. -/
theorem antitone_dyadic_coeff (a : ℚ) {lx ly : ℝ} (hlx : 0 ≤ lx) (hly : 0 ≤ ly) :
    Antitone fun j : ℕ => ((a + ((2 : ℚ) ^ j)⁻¹ : ℚ) : ℝ) * lx +
      (((0 : ℚ) + ((2 : ℚ) ^ j)⁻¹ : ℚ) : ℝ) * ly := by
  intro j j' hjj'
  have he : ((2 : ℝ) ^ j')⁻¹ ≤ ((2 : ℝ) ^ j)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hjj')
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right he hlx, mul_le_mul_of_nonneg_right he hly]

/-- The real sequence `(a + 2^{-j}) lx + (0 + 2^{-j}) ly` tends to `a lx`. -/
theorem tendsto_dyadic_coeff (a : ℚ) (lx ly : ℝ) :
    Tendsto (fun j : ℕ => ((a + ((2 : ℚ) ^ j)⁻¹ : ℚ) : ℝ) * lx +
      (((0 : ℚ) + ((2 : ℚ) ^ j)⁻¹ : ℚ) : ℝ) * ly) atTop (𝓝 ((a : ℝ) * lx)) := by
  have hE : Tendsto (fun j : ℕ => ((2 : ℝ) ^ j)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have h := ((tendsto_const_nhds (x := (a : ℝ))).add hE).mul_const lx |>.add (hE.mul_const ly)
  simp only [add_zero, zero_mul] at h
  push_cast
  simpa only [zero_add] using h

namespace ProjBerk

/-- Shortcut instance: the domain structure of the blowup charts `A[s/g]` of
`A = QuotChartAlg I σ d`, equal to the generic one (`blowupChartIsDomain`); its direct synthesis
times out (compare `ProjBerk.instAlgebraBlowupChartQuotChartAlg`). -/
instance instIsDomainBlowupChartQuotChartAlg {k : Type*} [Field k] {M : ℕ}
    (I : Ideal (MvPolynomial (Fin (M + 1)) k)) (σ : MvPolynomial (Fin (M + 1)) k) (d : ℕ)
    [IsDomain (QuotChartAlg I σ d)] (s : Finset (QuotChartAlg I σ d)) (g : QuotChartAlg I σ d) :
    IsDomain (blowupChart s g) :=
  blowupChartIsDomain s g

end ProjBerk

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} (V : ProjSubvariety k M)

/-- The function `u_i = (φ - a log|x_i|) ∘ ι_{x_i}⁻¹` on the chart
`Y_i^an = (Spec A_i)^an ≅ U_{x_i} ∩ X^an`, `A_i = QuotChartAlg I (x_i) 1` (`conv:pg-descent`). -/
def descentChartFun (i : Fin (M + 1)) (a : ℝ) (φ : V.an → EReal)
    (y : Berk k (QuotChartAlg V.ideal (X i) 1)) : EReal :=
  φ (V.chartInv (X i) 1 (isHomogeneous_X k i) one_pos y) +
    -(a : EReal) * ProjBerk.logAbs (X i) (V.chartInv (X i) 1 (isHomogeneous_X k i) one_pos y).1

variable {V}

/-- `u_i(ι_{x_i}(x)) = φ(x) - a log|x_i|_x`. -/
theorem descentChartFun_chartMap (i : Fin (M + 1)) (a : ℝ) (φ : V.an → EReal) (x : V.an)
    (hx : (x : ProjBerk k M).1.val (X i) ≠ 0) :
    V.descentChartFun i a φ (V.chartMap (X i) 1 x hx) =
      φ x + ((-(a * Real.log ((x : ProjBerk k M).1.val (X i) : ℝ)) : ℝ) : EReal) := by
  rw [descentChartFun, chartInv_chartMap, ProjBerk.logAbs_eq_coe_log hx, ← EReal.coe_neg,
    ← EReal.coe_mul, neg_mul]

/-- `u_i(v_triv) = φ(⋆)`: `ι_{x_i}` maps `⋆` to the trivial valuation of `A_i`
(`lem:wu-proj-chart`(4)), and `|x_i|_⋆ = 1`. -/
theorem descentChartFun_triv {i : Fin (M + 1)} [IsDomain (QuotChartAlg V.ideal (X i) 1)] (a : ℝ)
    (φ : V.an → EReal) : V.descentChartFun i a φ Berk.triv = φ V.triv := by
  have hi : (X i : MvPolynomial (Fin (M + 1)) k) ∉ V.ideal :=
    BlowupCenter.X_notMem_ideal_of_isDomain i
  rw [← chartMap_triv (isHomogeneous_X k i) hi, descentChartFun, chartInv_chartMap,
    V.logAbs_triv_of_notMem hi, mul_zero, add_zero]

namespace BlowupCenter

variable {M' : ℕ} (B : V.BlowupCenter M') {i : Fin (M + 1)}
  [IsDomain (QuotChartAlg V.ideal (X i) 1)]

/-- `u_i(w|_{A_i}) = φ(μ(κ(w))) + a log μ_x(w)` on the blowup chart `A_i[𝔞_i/g]`
(`lem:pg-blowup-chart`(3)). -/
theorem descentChartFun_comap_chartMap (a : ℝ) (φ : V.an → EReal)
    {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (w : Berk k (blowupChart (B.centerSet i) g)) :
    V.descentChartFun i a φ (Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g) w) =
      φ (B.proj (B.chartPoint i hg hg0 w)) +
        ((a * Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) : ℝ) : EReal) := by
  rw [descentChartFun, B.logAbs_chartInv_comap_X_self hg hg0 w, ← B.proj_chartPoint hg hg0 w,
    ENNReal.log_of_nnreal (B.scaleX_chartHom_ne_zero g w), ← EReal.coe_neg, ← EReal.coe_neg,
    ← EReal.coe_mul]
  congr 2
  ring

/-! ### Fubini–Study data read on the blowup charts -/

open Classical in
/-- A rational weight of a term `(F, λ)` with `λ ∈ ℚ` (and `0` otherwise). -/
def termRatWeight {R : Type*} (t : R × ℝ) : ℚ :=
  if h : ∃ q : ℚ, t.2 = q then h.choose else 0

/-- For `λ ∈ ℚ`, `termRatWeight (F, λ) = λ`. -/
theorem termRatWeight_eq {R : Type*} {t : R × ℝ} (h : ∃ q : ℚ, t.2 = q) :
    ((termRatWeight t : ℚ) : ℝ) = t.2 := by
  rw [termRatWeight, dif_pos h]
  exact h.choose_spec.symm

variable (i) in
open Classical in
/-- The terms `(δ(F_t), 1/m, λ_t/m)` on the blowup chart `A_i[𝔞_i/g]` of bigraded FS data
`m⁻¹ max_t (log|F_t| + λ_t)` with rational `λ_t` (`δ = B.chartHom i g`, proof of
`lem:pg-descent-weakly-psh`). -/
def chartTerms (g : QuotChartAlg V.ideal (X i) 1) {a b : ℚ} (D : BiProjBerk.FSData k M M' a b) :
    Finset (blowupChart (B.centerSet i) g × ℚ × ℚ) :=
  D.terms.image fun t => (B.chartHom i g t.1, ((D.m : ℚ))⁻¹, termRatWeight t / D.m)

/-- The coefficients `1/m` of `chartTerms` are positive. -/
theorem chartTerms_pos (g : QuotChartAlg V.ideal (X i) 1) {a b : ℚ}
    (D : BiProjBerk.FSData k M M' a b) : ∀ t ∈ B.chartTerms i g D, 0 < t.2.1 := by
  classical
  intro t ht
  unfold chartTerms at ht
  obtain ⟨t₀, -, rfl⟩ := Finset.mem_image.1 ht
  show (0 : ℚ) < ((D.m : ℚ))⁻¹
  exact inv_pos.2 (by exact_mod_cast D.m_pos)

/-- One term of `sup_fsTerm_chartTerms`. -/
theorem fsTerm_chartTerm {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i)
    (hg0 : g ≠ 0) {a b : ℚ} (D : BiProjBerk.FSData k M M' a b)
    {t : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k × ℝ} (ht : t ∈ D.terms)
    (hq : ∃ q : ℚ, t.2 = q) (w : Berk k (blowupChart (B.centerSet i) g)) :
    fsTerm (B.chartHom i g t.1, ((D.m : ℚ))⁻¹, termRatWeight t / D.m) w =
      (((D.m : ℝ)⁻¹ : ℝ) : EReal) * BiProjBerk.termVal t (B.chartPoint i hg hg0 w) +
        (((a : ℝ) * Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) +
          (b : ℝ) * Real.log (BiProjBerk.scaleY (B.chartHom i g) w : ℝ) : ℝ) : EReal) := by
  have hF : t.1.IsWeightedHomogeneous (biWeight M M') (D.deg.1, D.deg.2) :=
    D.isWeightedHomogeneous t ht
  have hL := B.logAbs_chartPoint_of_isWeightedHomogeneous hg hg0 w hF
  have hdeg1 : ((D.deg.1 : ℕ) : ℝ) = D.m * (a : ℝ) := by exact_mod_cast D.deg_fst
  have hdeg2 : ((D.deg.2 : ℕ) : ℝ) = D.m * (b : ℝ) := by exact_mod_cast D.deg_snd
  have hx := ENNReal.log_of_nnreal (B.scaleX_chartHom_ne_zero g w)
  have hy := ENNReal.log_of_nnreal (B.scaleY_chartHom_ne_zero hg hg0 w)
  rw [hx, hy] at hL
  rw [BiProjBerk.termVal_def]
  exact fsTerm_eq_inv_mul_add _ w D.m_pos hdeg1 hdeg2 _ _ t.2 (termRatWeight_eq hq) hL

/-- **The FS data read on a blowup chart** (proof of `lem:pg-descent-weakly-psh`): for bigraded
FS data `D` of class `(a, b)` with rational weights and `w ∈ (Spec A_i[𝔞_i/g])^an`,
`m⁻¹ max_t (log|δ(F_t)|_w + λ_t) = D(κ(w)) + a log μ_x(w) + b log μ_y(w)`, by
`log|F|_{κ(w)} = log|δ(F)|_w - p log μ_x(w) - q log μ_y(w)` for `F` of bidegree
`(p, q) = (m a, m b)` (`lem:pg-blowup-chart`(2)). -/
theorem sup_fsTerm_chartTerms {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i)
    (hg0 : g ≠ 0) {a b : ℚ} (D : BiProjBerk.FSData k M M' a b) (hD : D.IsRational)
    (w : Berk k (blowupChart (B.centerSet i) g)) :
    ((B.chartTerms i g D).sup fun t => fsTerm t w) =
      D.eval (B.chartPoint i hg hg0 w : BiProjBerk k M M') +
        (((a : ℝ) * Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) +
          (b : ℝ) * Real.log (BiProjBerk.scaleY (B.chartHom i g) w : ℝ) : ℝ) : EReal) := by
  classical
  have hm : (0 : ℝ) < (D.m : ℝ)⁻¹ := D.inv_m_pos
  have h1 : ((B.chartTerms i g D).sup fun t => fsTerm t w) = D.terms.sup fun t =>
      fsTerm (B.chartHom i g t.1, ((D.m : ℚ))⁻¹, termRatWeight t / D.m) w := by
    unfold chartTerms
    exact Finset.sup_image _ _ _
  have h2 : D.eval (B.chartPoint i hg hg0 w : BiProjBerk k M M') +
      (((a : ℝ) * Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) +
        (b : ℝ) * Real.log (BiProjBerk.scaleY (B.chartHom i g) w : ℝ) : ℝ) : EReal) =
      D.terms.sup fun t => (((D.m : ℝ)⁻¹ : ℝ) : EReal) *
        BiProjBerk.termVal t (B.chartPoint i hg hg0 w) +
        (((a : ℝ) * Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) +
          (b : ℝ) * Real.log (BiProjBerk.scaleY (B.chartHom i g) w : ℝ) : ℝ) : EReal) := by
    rw [BiProjBerk.FSData.eval_def, ProjBerk.ereal_coe_mul_finset_sup hm,
      EnvelopeProperty.FSData.sup_add_coe]
  exact h1.trans ((Finset.sup_congr rfl fun t ht =>
    B.fsTerm_chartTerm hg hg0 D ht (hD t ht) w).trans h2.symm)

/-- `log μ_x(w) ≥ 0` on the blowup charts (`μ_x ≥ 1`). -/
theorem log_scaleX_chartHom_nonneg (g : QuotChartAlg V.ideal (X i) 1)
    (w : Berk k (blowupChart (B.centerSet i) g)) :
    0 ≤ Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) :=
  Real.log_nonneg (by exact_mod_cast B.one_le_scaleX_chartHom g w)

/-- `log μ_y(w) ≥ 0` on the blowup charts (`μ_y ≥ 1`). -/
theorem log_scaleY_chartHom_nonneg {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i)
    (hg0 : g ≠ 0) (w : Berk k (blowupChart (B.centerSet i) g)) :
    0 ≤ Real.log (BiProjBerk.scaleY (B.chartHom i g) w : ℝ) :=
  Real.log_nonneg (by exact_mod_cast B.one_le_scaleY_chartHom hg hg0 w)

variable (i) in
/-- **Regularizability on the blowup charts** (the core of `lem:pg-descent-weakly-psh`; FHX
Lemma 5.4(2) on `X'` in the charts of the blowup). Let `k` be countable, `φ ∘ μ ∈ PSH(X', (a, 0))`,
`g ∈ 𝔞_i \ {0}`. Then `w ↦ u_i(w|_{A_i})` is regularizable on the chart `Spec A_i[𝔞_i/g]`. By
dyadic regularization on `X'` (`cor:pg-countable-regularization`(2)), `φ ∘ μ` is the limit of a
decreasing sequence `Φ_j = m_j⁻¹ max_t (log|F_t| + λ_t) ∈ 𝓗_fin(X', (a + 2^{-j}, 2^{-j}))`; read on
the chart (`sup_fsTerm_chartTerms`), `G_j = m_j⁻¹ max_t (log|δ(F_t)| + λ_t)
= Φ_j ∘ κ + (a + 2^{-j}) log μ_x + 2^{-j} log μ_y` decreases (`log μ_x, log μ_y ≥ 0`) to
`φ ∘ μ ∘ κ + a log μ_x = u_i(w|_{A_i})` (`descentChartFun_comap_chartMap`). The maxima of the `G_j`
with the FS functions `truncStd j ↓ -∞` (which supply generators of the chart) are FS functions
decreasing to the same limit. -/
theorem isRegularizable_descentChartFun_comap_chartMap [Countable k] {a : ℚ}
    {φ : V.an → EReal} (h : B.IsPSH ![(a : ℝ), 0] (φ ∘ B.proj))
    {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0) :
    IsRegularizable fun w : Berk k (blowupChart (B.centerSet i) g) =>
      V.descentChartFun i a φ (Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g) w) := by
  have : Algebra.FiniteType k (QuotChartAlg V.ideal (X i) 1) :=
    ProjBerk.finiteType_quotChartAlg (isHomogeneous_X k i)
  have htriv : φ V.triv ≠ ⊥ := by
    have h1 := h.apply_triv_ne_bot
    rwa [Function.comp_apply, B.proj_triv] at h1
  have h' : B.IsPSH ![((a : ℚ) : ℝ), ((0 : ℚ) : ℝ)] (φ ∘ B.proj) := by
    rw [Rat.cast_zero]
    exact h
  obtain ⟨Φ, hΦ, hanti, hlim⟩ := h'.exists_isFinFS_seq_dyadic
  choose D hDrat hDne hDeq using fun j => isFinFS_iff.1 (hΦ j)
  have hG : ∀ (j : ℕ) (w : Berk k (blowupChart (B.centerSet i) g)),
      ((B.chartTerms i g (D j)).sup fun t => fsTerm t w) =
        Φ j (B.chartPoint i hg hg0 w) +
          (((((a + ((2 : ℚ) ^ j)⁻¹ : ℚ) : ℝ)) *
              Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) +
            ((((0 : ℚ) + ((2 : ℚ) ^ j)⁻¹ : ℚ) : ℝ)) *
              Real.log (BiProjBerk.scaleY (B.chartHom i g) w : ℝ) : ℝ) : EReal) := fun j w =>
    (B.sup_fsTerm_chartTerms hg hg0 (D j) (hDrat j) w).trans
      (congrArg (· + _) (hDeq j _).symm)
  have hGanti : ∀ w : Berk k (blowupChart (B.centerSet i) g), Antitone fun j =>
      ((B.chartTerms i g (D j)).sup fun t => fsTerm t w) := by
    intro w j j' hjj'
    exact (hG j' w).trans_le ((add_le_add (hanti _ hjj') (EReal.coe_le_coe_iff.2
      (antitone_dyadic_coeff a (B.log_scaleX_chartHom_nonneg g w)
        (B.log_scaleY_chartHom_nonneg hg hg0 w) hjj'))).trans_eq (hG j w).symm)
  refine ⟨⟨Berk.triv, ?_⟩, fun j => (FSData.truncStd k _ j).addTerms (B.chartTerms i g (D j))
    (B.chartTerms_pos g (D j)), fun w j j' hjj' => ?_, fun w => ?_⟩
  · show V.descentChartFun i a φ (Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g)
      Berk.triv) ≠ ⊥
    rw [comap_chartMap_triv, descentChartFun_triv]
    exact htriv
  · simp only [FSData.eval_addTerms]
    exact max_le_max (FSData.antitone_truncStd k _ w hjj') (hGanti w hjj')
  · show V.descentChartFun i a φ (Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g) w) =
      ⨅ j, ((FSData.truncStd k _ j).addTerms (B.chartTerms i g (D j))
        (B.chartTerms_pos g (D j))).eval w
    have hlx := B.log_scaleX_chartHom_nonneg g w
    have hly := B.log_scaleY_chartHom_nonneg hg hg0 w
    have hr : ⨅ j : ℕ, (((((a + ((2 : ℚ) ^ j)⁻¹ : ℚ) : ℝ)) *
          Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) +
        ((((0 : ℚ) + ((2 : ℚ) ^ j)⁻¹ : ℚ) : ℝ)) *
          Real.log (BiProjBerk.scaleY (B.chartHom i g) w : ℝ) : ℝ) : EReal) =
        (((a : ℝ) * Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) : ℝ) : EReal) :=
      iInf_eq_of_tendsto_of_antitone
        (fun _ _ hjj' => EReal.coe_le_coe_iff.2 (antitone_dyadic_coeff a hlx hly hjj'))
        ((continuous_coe_real_ereal.tendsto _).comp (tendsto_dyadic_coeff a _ _))
    have hsum := iInf_add_of_antitone (hanti (B.chartPoint i hg hg0 w))
      (fun _ _ hjj' => EReal.coe_le_coe_iff.2 (antitone_dyadic_coeff a hlx hly hjj'))
      ((hΦ 0).isFS.ne_top _) (EReal.coe_ne_top _)
    have e1 : (⨅ j, ((FSData.truncStd k _ j).addTerms (B.chartTerms i g (D j))
        (B.chartTerms_pos g (D j))).eval w) =
        ⨅ j, ((B.chartTerms i g (D j)).sup fun t => fsTerm t w) := by
      rw [← FSData.iInf_max_truncStd k _ (hGanti w) w]
      refine iInf_congr fun j => ?_
      rw [FSData.eval_addTerms, max_comm]
    rw [e1, B.descentChartFun_comap_chartMap a φ hg hg0 w, ← hr, ← Function.comp_apply (f := φ),
      hlim, ← hsum]
    exact iInf_congr fun j => (hG j w).symm

variable (i) in
/-- **`lem:pg-descent-weakly-psh`**, chart form: for `g ∈ 𝔞_i \ {0}`, `w ↦ u_i(w|_{A_i})` is the
limit of a decreasing sequence of convex PL functions on all of `(Spec A_i[𝔞_i/g])^an`. -/
theorem isDecrConvexPLLimitOn_descentChartFun_comap_chartMap [Countable k] {a : ℚ}
    {φ : V.an → EReal} (h : B.IsPSH ![(a : ℝ), 0] (φ ∘ B.proj))
    {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0) :
    IsDecrConvexPLLimitOn Set.univ fun w : Berk k (blowupChart (B.centerSet i) g) =>
      V.descentChartFun i a φ (Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g) w) :=
  (B.isRegularizable_descentChartFun_comap_chartMap i h hg hg0).isDecrConvexPLLimitOn

variable (i) in
/-- **Weak plurisubharmonicity on the charts** (`lem:pg-descent-weakly-psh`; FHX Lemma 5.4(2) on
`X'`, in the charts of the blowup): for countable `k` and `φ ∘ μ ∈ PSH(X', (a, 0))`, the function
`u_i = (φ - a log|x_i|) ∘ ι_{x_i}⁻¹` is weakly psh on `Y_i^an = (Spec A_i)^an`, with the blowup of
`Spec A_i` along `𝔞_i = (g_{i0}, …, g_{iM'})` as witness (`isWeaklyPSHOn_of_forall_chart`): on each
chart it is regularizable, hence locally psh. -/
theorem isWeaklyPSHOn_descentChartFun [Countable k] {a : ℚ} {φ : V.an → EReal}
    (h : B.IsPSH ![(a : ℝ), 0] (φ ∘ B.proj)) :
    IsWeaklyPSHOn Set.univ (V.descentChartFun i a φ) :=
  B.isWeaklyPSHOn_of_forall_chart fun g hg hg0 => by
    have hreg := B.isRegularizable_descentChartFun_comap_chartMap i h hg hg0
    exact hreg.isLocallyPSHOn (isOpen_univ.preimage (Berk.continuous_comap _))

variable (i) in
/-- **Regularizability off the centre** (`lem:pg-descent-cover`; FHX Lemma 5.10(1) on `X'` over
the locus where `μ` is an isomorphism): for countable `k`, `φ ∘ μ ∈ PSH(X', (a, 0))` and
`g = g_{il} ∈ 𝔞_i \ {0}`, the restriction of `u_i` to `(Y_i)_g^an = (Spec (A_i)_g)^an` is
regularizable. The principal open `Spec (A_i)_g` maps to the blowup chart `Spec A_i[𝔞_i/g]`
(`chartToAway`, `A_i[𝔞_i/g] ⊆ (A_i)_g`) over the inclusion into `Spec A_i`
(`comap_chartMap_comap_chartToAway`), and regularizable functions pull back
(`IsRegularizable.comp_comap`, FHX Lemma 5.11(4)); the pullback is finite at the trivial
valuation. -/
theorem isRegularizable_descentChartFun_awayComap [Countable k] {a : ℚ} {φ : V.an → EReal}
    (h : B.IsPSH ![(a : ℝ), 0] (φ ∘ B.proj)) {g : QuotChartAlg V.ideal (X i) 1}
    (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0) :
    IsRegularizable fun z : Berk k (Localization.Away g) =>
      V.descentChartFun i a φ (Berk.awayComap g z) := by
  have : Algebra.FiniteType k (QuotChartAlg V.ideal (X i) 1) :=
    ProjBerk.finiteType_quotChartAlg (isHomogeneous_X k i)
  have : Algebra.FiniteType k (Localization.Away g) := finiteType_localizationAway_of_finiteType g
  have : IsDomain (Localization.Away g) := Berk.isDomain_localizationAway hg0
  have htriv : φ V.triv ≠ ⊥ := by
    have h1 := h.apply_triv_ne_bot
    rwa [Function.comp_apply, B.proj_triv] at h1
  have hreg := B.isRegularizable_descentChartFun_comap_chartMap i h hg hg0
  have hcomp := comap_chartMap_comap_chartToAway (k := k) (B.centerSet i) hg0
  have hne : ∃ z : Berk k (Localization.Away g), V.descentChartFun i a φ
      (Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g)
        (Berk.comap (chartToAway k (B.centerSet i) hg0) z)) ≠ ⊥ :=
    ⟨Berk.triv, by rw [hcomp, Berk.awayComap_triv, descentChartFun_triv]; exact htriv⟩
  exact (hreg.comp_comap (chartToAway k (B.centerSet i) hg0) hne).congr fun z => by
    simp only [hcomp]

end BlowupCenter

end ProjSubvariety

end EnvelopeProperty
