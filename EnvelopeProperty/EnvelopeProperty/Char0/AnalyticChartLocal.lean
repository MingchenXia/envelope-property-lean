/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import EnvelopeProperty.Char0.Weights

/-!
# Local analytic charts on a hypersurface given by an algebraic function

This file contains the analytic half of the blueprint lemma `lem:c0-analytic-chart`
(`EnvelopeProperty/blueprint/src/char0.tex`), in an abstract form that does not mention valuation
rings.

Let `K` be a field over `ℂ`, `w : Fin n → K` and `θ ∈ K`, and let
`Φ ∈ ℂ[T, w₁, …, wₙ]` (a polynomial in the variables `Option (Fin n)`, `none ↦ T`) with
`Φ(θ, w) = 0` in `K`. Let `(t₀, p₀) ∈ ℂ × ℂⁿ` be a point with `Φ(t₀, p₀) = 0` and
`∂_T Φ(t₀, p₀) ≠ 0` (`IsChartPoint`). The holomorphic implicit function theorem gives a
holomorphic `ϑ` near `p₀` with `ϑ(p₀) = t₀` and `Φ(ϑ(p), p) = 0` (`chartTheta`).

Assume moreover the *divisibility property* `ChartDiv`: every `H ∈ ℂ[T, w]` with `H(θ, w) = 0`
satisfies `c(w) H = Φ M` for some nonzero `c ∈ ℂ[w]` and some `M`. (In the application `Φ` is a
cleared minimal polynomial of `θ` over `ℂ(w)`.) Then `H(ϑ(p), p) = 0` near `p₀`
(`eventually_eval_chartGraph_eq_zero`): a nonzero polynomial does not vanish on a nonempty open
set (`volume_mvPolynomial_zeroSet_eq_zero`). Consequently the evaluation
`P(θ, w) / Q(θ, w) ↦ P(ϑ, p) / Q(ϑ, p)` (for `Q(t₀, p₀) ≠ 0`) is a well defined ring
homomorphism `chartEv` from the subring `chartRing` of `K` to germs of functions at `p₀`: this is
the evaluation homomorphism `ev` of the blueprint proof.

Finally, for derivations `D_j` of `K` with `D_j(w_i) = δ_{ij}` (`IsChartDeriv`), `chartRing` is
stable under the `D_j`, and `ev(x)` is holomorphic near `p₀` with partial derivatives `ev(D_j x)`
(`eventually_hasFDerivAt_chartFun`). This is the chain-rule step of the blueprint proof, which
gives `det Dμ = ev(det (D_j z_i))` for `μ = (ev(z_1), …, ev(z_m))` (`eventually_det_chartMap`).

## Main definitions and results

* `chartPt`: the point `(t, p)`; `chartVar`: the point `(θ, w)` of `K`;
* `hasFDerivAt_eval_mvPolynomial`: the chain rule for polynomial expressions;
* `exists_chartTheta`, `chartTheta`: the holomorphic implicit function theorem for `Φ`;
* `ChartDiv`, `eventually_eval_chartGraph_eq_zero`;
* `chartRing`, `chartFun`, `chartFun_eventuallyEq`, `chartEv`;
* `derivation_mem_chartRing`, `eventually_hasFDerivAt_chartFun`;
* `chartMap`, `eventually_hasFDerivAt_chartMap`, `eventually_det_chartMap`.
-/

noncomputable section

open scoped NNReal ENNReal Topology

open MvPolynomial Filter

namespace EnvelopeProperty.Char0

/-! ### Derivatives of polynomial expressions -/

section EvalDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {σ : Type*} [Fintype σ]
  [DecidableEq σ]

/-- **Chain rule for polynomials**: `D(P ∘ f) = ∑_o (∂_o P)(f) · D f_o`. -/
theorem hasFDerivAt_eval_mvPolynomial {f : E → σ → ℂ} {f' : σ → E →L[ℂ] ℂ} {x : E}
    (hf : ∀ o, HasFDerivAt (fun y => f y o) (f' o) x) (P : MvPolynomial σ ℂ) :
    HasFDerivAt (fun y => eval (f y) P) (∑ o, eval (f x) (pderiv o P) • f' o) x := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ((hasFDerivAt_const (𝕜 := ℂ) c x).congr_of_eventuallyEq
      (Eventually.of_forall fun y => by simp)).congr_fderiv ?_
    ext v
    simp
  | add P Q hP hQ =>
    refine ((hP.add hQ).congr_of_eventuallyEq
      (Eventually.of_forall fun y => by simp)).congr_fderiv ?_
    ext v
    simp [add_mul, Finset.sum_add_distrib]
  | mul_X P o hP =>
    refine ((hP.mul (hf o)).congr_of_eventuallyEq
      (Eventually.of_forall fun y => by simp)).congr_fderiv ?_
    have h1 : ∀ i, eval (f x) (pderiv i (P * X o)) =
        f x o * eval (f x) (pderiv i P) + if o = i then eval (f x) P else 0 := by
      intro i
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X,
        Pi.single_apply]
      split_ifs <;> simp [mul_comm, add_comm]
    simp only [h1]
    rw [Finset.sum_congr rfl fun i _ => add_smul _ _ (f' i), Finset.sum_add_distrib,
      Finset.smul_sum]
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, smul_smul]
    abel

/-- **Chain rule for derivations**: `D(P(v)) = ∑_o (∂_o P)(v) · D(v_o)` for a `ℂ`-derivation `D`
of a `ℂ`-algebra. -/
theorem derivation_aeval {K : Type*} [CommRing K] [Algebra ℂ K] (D : Derivation ℂ K K)
    (v : σ → K) (P : MvPolynomial σ ℂ) :
    D (aeval v P) = ∑ o, aeval v (pderiv o P) * D (v o) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P o hP =>
    have h1 : ∀ i, aeval v (pderiv i (P * X o)) =
        v o * aeval v (pderiv i P) + if o = i then aeval v P else 0 := by
      intro i
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X,
        Pi.single_apply]
      split_ifs <;> simp [mul_comm, add_comm]
    rw [Finset.sum_congr rfl fun i _ => by rw [h1 i]]
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hP, add_mul,
      Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.mul_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

end EvalDeriv

/-! ### The implicit function -/

section Graph

variable {n : ℕ}

/-- The coordinate functionals of `(p, t) ↦ (t, p)`. -/
def chartCoord (o : Option (Fin n)) : (Fin n → ℂ) × ℂ →L[ℂ] ℂ :=
  o.elim (ContinuousLinearMap.snd ℂ _ _) fun i =>
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ _ _)

/-- The point `(t, p)` of `ℂ^{1+n}`, indexed by `Option (Fin n)` (`none ↦ t`). -/
def chartPt (p : Fin n → ℂ) (t : ℂ) : Option (Fin n) → ℂ := fun o => o.elim t p

@[simp]
theorem chartPt_none (p : Fin n → ℂ) (t : ℂ) : chartPt p t none = t :=
  rfl

@[simp]
theorem chartPt_some (p : Fin n → ℂ) (t : ℂ) (i : Fin n) : chartPt p t (some i) = p i :=
  rfl

theorem chartPt_comp_some (p : Fin n → ℂ) (t : ℂ) : chartPt p t ∘ some = p :=
  rfl

theorem eval_chartPt_rename_some (p : Fin n → ℂ) (t : ℂ) (c : MvPolynomial (Fin n) ℂ) :
    eval (chartPt p t) (rename some c) = eval p c := by
  rw [eval_rename, chartPt_comp_some]

theorem chartCoord_apply (o : Option (Fin n)) (v : (Fin n → ℂ) × ℂ) :
    chartCoord o v = chartPt v.1 v.2 o := by
  cases o <;> rfl

/-- **The holomorphic implicit function theorem** for a polynomial `Φ(T, w)`: if `Φ(t₀, p₀) = 0`
and `∂_T Φ(t₀, p₀) ≠ 0`, there is `ϑ`, holomorphic near `p₀`, with `ϑ(p₀) = t₀` and
`Φ(ϑ(p), p) = 0` near `p₀`. -/
theorem exists_chartTheta (Φ : MvPolynomial (Option (Fin n)) ℂ) {p0 : Fin n → ℂ} {t0 : ℂ}
    (h0 : eval (chartPt p0 t0) Φ = 0) (hT : eval (chartPt p0 t0) (pderiv none Φ) ≠ 0) :
    ∃ ϑ : (Fin n → ℂ) → ℂ, ϑ p0 = t0 ∧ ∀ᶠ p in 𝓝 p0,
      eval (chartPt p (ϑ p)) Φ = 0 ∧ DifferentiableAt ℂ ϑ p := by
  set f : (Fin n → ℂ) × ℂ → ℂ := fun v => eval (chartPt v.1 v.2) Φ with hf_def
  set u : (Fin n → ℂ) × ℂ := (p0, t0)
  have hc : ∀ o, HasFDerivAt (fun v : (Fin n → ℂ) × ℂ => chartPt v.1 v.2 o) (chartCoord o) u :=
    fun o => ((chartCoord o).hasFDerivAt).congr_of_eventuallyEq
      (Eventually.of_forall fun v => (chartCoord_apply o v).symm)
  have hfd : HasFDerivAt f (∑ o, eval (chartPt p0 t0) (pderiv o Φ) • chartCoord o) u :=
    hasFDerivAt_eval_mvPolynomial hc Φ
  have hL : f = fun v => eval (ContinuousLinearMap.pi chartCoord v) Φ := by
    funext v
    have : chartPt v.1 v.2 = ContinuousLinearMap.pi chartCoord v :=
      funext fun o => (chartCoord_apply o v).symm
    rw [hf_def]
    exact congrArg (fun y => eval y Φ) this
  have han : AnalyticAt ℂ (fun v => eval (ContinuousLinearMap.pi chartCoord v) Φ) u :=
    AnalyticOnNhd.eval_continuousLinearMap (ContinuousLinearMap.pi chartCoord) Φ u (Set.mem_univ _)
  have cdf : ContDiffAt ℂ 1 f u := by
    rw [hL]
    exact han.contDiffAt
  set a := eval (chartPt p0 t0) (pderiv none Φ)
  have hinr : (fderiv ℂ f u ∘L ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ) =
      a • ContinuousLinearMap.id ℂ ℂ := by
    rw [hfd.fderiv]
    ext
    simp [chartCoord, Fintype.sum_option, a]
  have if₂ : (fderiv ℂ f u ∘L ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ).IsInvertible := by
    rw [hinr]
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := a⁻¹ • ContinuousLinearMap.id ℂ ℂ)
      ?_ ?_ <;>
    · ext; simp [hT]
  have pn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  refine ⟨cdf.implicitFunction pn if₂, cdf.implicitFunction_apply_self pn if₂, ?_⟩
  have h1 := cdf.eventually_apply_implicitFunction pn if₂
  have h2 := (cdf.contDiffAt_implicitFunction pn if₂).eventually (by simp)
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1.trans h0, hp2.differentiableAt one_ne_zero⟩

/-- The base point of a chart: `Φ(t₀, p₀) = 0` and `∂_T Φ(t₀, p₀) ≠ 0`. -/
structure IsChartPoint (Φ : MvPolynomial (Option (Fin n)) ℂ) (p0 : Fin n → ℂ) (t0 : ℂ) :
    Prop where
  /-- `Φ(t₀, p₀) = 0`. -/
  eval_eq_zero : eval (chartPt p0 t0) Φ = 0
  /-- `∂_T Φ(t₀, p₀) ≠ 0`. -/
  eval_pderiv_ne_zero : eval (chartPt p0 t0) (pderiv none Φ) ≠ 0

variable {Φ : MvPolynomial (Option (Fin n)) ℂ} {p0 : Fin n → ℂ} {t0 : ℂ}

/-- The implicit function `ϑ` of `Φ` at a chart point (`exists_chartTheta`). -/
def chartTheta (h : IsChartPoint Φ p0 t0) : (Fin n → ℂ) → ℂ :=
  Classical.choose (exists_chartTheta Φ h.eval_eq_zero h.eval_pderiv_ne_zero)

theorem chartTheta_self (h : IsChartPoint Φ p0 t0) : chartTheta h p0 = t0 :=
  (Classical.choose_spec (exists_chartTheta Φ h.eval_eq_zero h.eval_pderiv_ne_zero)).1

theorem eventually_chartTheta (h : IsChartPoint Φ p0 t0) :
    ∀ᶠ p in 𝓝 p0, eval (chartPt p (chartTheta h p)) Φ = 0 ∧ DifferentiableAt ℂ (chartTheta h) p :=
  (Classical.choose_spec (exists_chartTheta Φ h.eval_eq_zero h.eval_pderiv_ne_zero)).2

/-- The graph `p ↦ (ϑ(p), p)` of the implicit function. -/
def chartGraph (h : IsChartPoint Φ p0 t0) (p : Fin n → ℂ) : Option (Fin n) → ℂ :=
  chartPt p (chartTheta h p)

theorem chartGraph_self (h : IsChartPoint Φ p0 t0) : chartGraph h p0 = chartPt p0 t0 := by
  rw [chartGraph, chartTheta_self]

theorem continuousAt_chartGraph (h : IsChartPoint Φ p0 t0) {p : Fin n → ℂ}
    (hp : DifferentiableAt ℂ (chartTheta h) p) : ContinuousAt (chartGraph h) p := by
  refine continuousAt_pi.2 fun o => ?_
  cases o with
  | none => exact hp.continuousAt
  | some i => exact continuousAt_apply i p

theorem eventually_continuousAt_eval_chartGraph (h : IsChartPoint Φ p0 t0)
    (P : MvPolynomial (Option (Fin n)) ℂ) :
    ∀ᶠ p in 𝓝 p0, ContinuousAt (fun q => eval (chartGraph h q) P) p :=
  (eventually_chartTheta h).mono fun _ hp =>
    (continuous_eval P).continuousAt.comp (continuousAt_chartGraph h hp.2)

theorem eventually_eval_chartGraph_ne_zero (h : IsChartPoint Φ p0 t0)
    {Q : MvPolynomial (Option (Fin n)) ℂ} (hQ : eval (chartPt p0 t0) Q ≠ 0) :
    ∀ᶠ p in 𝓝 p0, eval (chartGraph h p) Q ≠ 0 := by
  have hc := (eventually_continuousAt_eval_chartGraph h Q).self_of_nhds
  refine hc.eventually_ne ?_
  rwa [chartGraph_self]

/-- **Vanishing on the graph.** If `c(w) H = Φ M` with `c ≠ 0`, then `H(ϑ(p), p) = 0` near `p₀`:
`c(p) H(ϑ(p), p) = 0` near `p₀`, and `{c ≠ 0}` is dense since `{c = 0}` is Lebesgue-null. -/
theorem eventually_eval_chartGraph_eq_zero_of_mul (h : IsChartPoint Φ p0 t0)
    {H : MvPolynomial (Option (Fin n)) ℂ} {c : MvPolynomial (Fin n) ℂ} (hc : c ≠ 0)
    {M : MvPolynomial (Option (Fin n)) ℂ} (hcH : rename some c * H = Φ * M) :
    ∀ᶠ p in 𝓝 p0, eval (chartGraph h p) H = 0 := by
  obtain ⟨U, hU, hUo, hp0U⟩ := eventually_nhds_iff.1 (eventually_chartTheta h)
  refine Filter.eventually_of_mem (hUo.mem_nhds hp0U) fun p1 hp1 => ?_
  by_contra hne
  have hcont : ContinuousAt (fun q => eval (chartGraph h q) H) p1 :=
    (continuous_eval H).continuousAt.comp (continuousAt_chartGraph h (hU p1 hp1).2)
  have hev : ∀ᶠ q in 𝓝 p1, q ∈ U ∧ eval (chartGraph h q) H ≠ 0 :=
    (hUo.eventually_mem hp1).and (hcont.eventually_ne hne)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hsub : Metric.ball p1 r ⊆ {q : Fin n → ℂ | eval q c = 0} := by
    intro q hq
    obtain ⟨hqU, hqH⟩ := hball q hq
    have h1 := congrArg (eval (chartGraph h q)) hcH
    rw [map_mul, map_mul, chartGraph, eval_chartPt_rename_some, (hU q hqU).1, zero_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_right hqH
  have hpos := Metric.measure_ball_pos MeasureTheory.volume p1 hr
  have hnull := volume_mvPolynomial_zeroSet_eq_zero hc
  exact hpos.ne' (MeasureTheory.measure_mono_null hsub hnull)

end Graph

/-! ### The evaluation homomorphism -/

section Ring

variable {n : ℕ} {K : Type*}

/-- The point `(θ, w)` of `K^{1+n}`. -/
def chartVar (w : Fin n → K) (θ : K) : Option (Fin n) → K := fun o => o.elim θ w

@[simp]
theorem chartVar_none (w : Fin n → K) (θ : K) : chartVar w θ none = θ :=
  rfl

@[simp]
theorem chartVar_some (w : Fin n → K) (θ : K) (i : Fin n) : chartVar w θ (some i) = w i :=
  rfl

variable [Field K] [Algebra ℂ K] (w : Fin n → K) (θ : K)

theorem aeval_chartVar_rename_some (c : MvPolynomial (Fin n) ℂ) :
    aeval (chartVar w θ) (rename some c) = aeval w c := by
  rw [aeval_rename]
  rfl

/-- **The divisibility property**: every `H(T, w)` vanishing at `(θ, w)` satisfies
`c(w) H = Φ M` with `c ≠ 0`. -/
def ChartDiv (Φ : MvPolynomial (Option (Fin n)) ℂ) : Prop :=
  ∀ H : MvPolynomial (Option (Fin n)) ℂ, aeval (chartVar w θ) H = 0 →
    ∃ c : MvPolynomial (Fin n) ℂ, c ≠ 0 ∧ ∃ M, rename some c * H = Φ * M

/-- **The ring of the chart**: elements `P(θ, w) / Q(θ, w)` of `K` with `Q(t₀, p₀) ≠ 0`. -/
def chartRing (p0 : Fin n → ℂ) (t0 : ℂ) : Subalgebra ℂ K where
  carrier := {x | ∃ P Q : MvPolynomial (Option (Fin n)) ℂ, eval (chartPt p0 t0) Q ≠ 0 ∧
    x * aeval (chartVar w θ) Q = aeval (chartVar w θ) P}
  mul_mem' := by
    rintro x y ⟨P₁, Q₁, h₁, e₁⟩ ⟨P₂, Q₂, h₂, e₂⟩
    refine ⟨P₁ * P₂, Q₁ * Q₂, by simp [h₁, h₂], ?_⟩
    simp only [map_mul]
    rw [← e₁, ← e₂]
    ring
  add_mem' := by
    rintro x y ⟨P₁, Q₁, h₁, e₁⟩ ⟨P₂, Q₂, h₂, e₂⟩
    refine ⟨P₁ * Q₂ + P₂ * Q₁, Q₁ * Q₂, by simp [h₁, h₂], ?_⟩
    simp only [map_mul, map_add]
    rw [← e₁, ← e₂]
    ring
  algebraMap_mem' c := ⟨C c, 1, by simp, by simp [Algebra.algebraMap_eq_smul_one]⟩

variable {w θ}

theorem mem_chartRing {p0 : Fin n → ℂ} {t0 : ℂ} {x : K} :
    x ∈ chartRing w θ p0 t0 ↔ ∃ P Q : MvPolynomial (Option (Fin n)) ℂ,
      eval (chartPt p0 t0) Q ≠ 0 ∧ x * aeval (chartVar w θ) Q = aeval (chartVar w θ) P :=
  Iff.rfl

theorem aeval_mem_chartRing (p0 : Fin n → ℂ) (t0 : ℂ) (P : MvPolynomial (Option (Fin n)) ℂ) :
    aeval (chartVar w θ) P ∈ chartRing w θ p0 t0 :=
  ⟨P, 1, by simp, by simp⟩

theorem mem_chartRing_of_mul {p0 : Fin n → ℂ} {t0 : ℂ} {x : K}
    {P Q : MvPolynomial (Option (Fin n)) ℂ} (hQ : eval (chartPt p0 t0) Q ≠ 0)
    (hx : x * aeval (chartVar w θ) Q = aeval (chartVar w θ) P) : x ∈ chartRing w θ p0 t0 :=
  ⟨P, Q, hQ, hx⟩

variable {Φ : MvPolynomial (Option (Fin n)) ℂ} {p0 : Fin n → ℂ} {t0 : ℂ}

/-- **Vanishing on the graph**: `H(θ, w) = 0` implies `H(ϑ(p), p) = 0` near `p₀`. -/
theorem eventually_eval_chartGraph_eq_zero (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0)
    {H : MvPolynomial (Option (Fin n)) ℂ} (hH : aeval (chartVar w θ) H = 0) :
    ∀ᶠ p in 𝓝 p0, eval (chartGraph h p) H = 0 := by
  obtain ⟨c, hc, M, hcM⟩ := hdiv H hH
  exact eventually_eval_chartGraph_eq_zero_of_mul h hc hcM

theorem aeval_ne_zero_of_eval_ne_zero (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0)
    {Q : MvPolynomial (Option (Fin n)) ℂ} (hQ : eval (chartPt p0 t0) Q ≠ 0) :
    aeval (chartVar w θ) Q ≠ 0 := by
  intro h0
  have := (eventually_eval_chartGraph_eq_zero hdiv h h0).self_of_nhds
  rw [chartGraph_self] at this
  exact hQ this

variable (w θ)

open Classical in
/-- **The evaluation map** `ev`: `ev(x)(p) = P(ϑ(p), p) / Q(ϑ(p), p)` for a chosen representation
`x = P(θ, w) / Q(θ, w)`, and `0` off `chartRing`. -/
def chartFun (h : IsChartPoint Φ p0 t0) (x : K) : (Fin n → ℂ) → ℂ :=
  if hx : x ∈ chartRing w θ p0 t0 then
    fun p => eval (chartGraph h p) (Classical.choose hx) /
      eval (chartGraph h p) (Classical.choose (Classical.choose_spec hx))
  else 0

variable {w θ}

/-- **`ev` is independent of the representation**. -/
theorem chartFun_eventuallyEq (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0) {x : K}
    {P Q : MvPolynomial (Option (Fin n)) ℂ} (hQ : eval (chartPt p0 t0) Q ≠ 0)
    (hx : x * aeval (chartVar w θ) Q = aeval (chartVar w θ) P) :
    chartFun w θ h x =ᶠ[𝓝 p0] fun p => eval (chartGraph h p) P / eval (chartGraph h p) Q := by
  have hmem : x ∈ chartRing w θ p0 t0 := ⟨P, Q, hQ, hx⟩
  set P' := Classical.choose hmem
  set Q' := Classical.choose (Classical.choose_spec hmem)
  have hQ' : eval (chartPt p0 t0) Q' ≠ 0 := (Classical.choose_spec (Classical.choose_spec hmem)).1
  have hx' : x * aeval (chartVar w θ) Q' = aeval (chartVar w θ) P' :=
    (Classical.choose_spec (Classical.choose_spec hmem)).2
  have hfun : chartFun w θ h x = fun p => eval (chartGraph h p) P' / eval (chartGraph h p) Q' := by
    rw [chartFun, dif_pos hmem]
  have hH : aeval (chartVar w θ) (P' * Q - P * Q') = 0 := by
    rw [map_sub, map_mul, map_mul, ← hx, ← hx']
    ring
  filter_upwards [eventually_eval_chartGraph_eq_zero hdiv h hH,
    eventually_eval_chartGraph_ne_zero h hQ, eventually_eval_chartGraph_ne_zero h hQ'] with
    p hp hpQ hpQ'
  rw [hfun]
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at hp
  rw [div_eq_div_iff hpQ' hpQ, hp]

theorem chartFun_aeval_eventuallyEq (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0)
    (P : MvPolynomial (Option (Fin n)) ℂ) :
    chartFun w θ h (aeval (chartVar w θ) P) =ᶠ[𝓝 p0] fun p => eval (chartGraph h p) P := by
  filter_upwards [chartFun_eventuallyEq hdiv h (x := aeval (chartVar w θ) P) (Q := 1) (P := P)
    (by simp) (by simp)] with p hp
  rw [hp, map_one, div_one]

variable (w θ) in
/-- **The evaluation homomorphism** `ev : chartRing → germs at p₀`. -/
def chartEv (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0) :
    chartRing w θ p0 t0 →+* Germ (𝓝 p0) ℂ where
  toFun x := (chartFun w θ h x : Germ (𝓝 p0) ℂ)
  map_one' := by
    have h1 := chartFun_eventuallyEq hdiv h (x := 1) (P := 1) (Q := 1) (by simp) (by simp)
    change (chartFun w θ h 1 : Germ (𝓝 p0) ℂ) = (↑(fun _ : Fin n → ℂ => (1 : ℂ)) : Germ (𝓝 p0) ℂ)
    exact Germ.coe_eq.2 (h1.trans (Eventually.of_forall fun p => by simp))
  map_mul' := by
    rintro ⟨x, P₁, Q₁, h₁, e₁⟩ ⟨y, P₂, Q₂, h₂, e₂⟩
    have hxy : x * y * aeval (chartVar w θ) (Q₁ * Q₂) = aeval (chartVar w θ) (P₁ * P₂) := by
      simp only [map_mul]
      rw [← e₁, ← e₂]
      ring
    change (chartFun w θ h (x * y) : Germ (𝓝 p0) ℂ) =
      (chartFun w θ h x : Germ (𝓝 p0) ℂ) * (chartFun w θ h y : Germ (𝓝 p0) ℂ)
    rw [← Germ.coe_mul, Germ.coe_eq]
    filter_upwards [chartFun_eventuallyEq hdiv h (by simp [h₁, h₂]) hxy,
      chartFun_eventuallyEq hdiv h h₁ e₁, chartFun_eventuallyEq hdiv h h₂ e₂] with p hp hp₁ hp₂
    rw [Pi.mul_apply, hp, hp₁, hp₂, map_mul, map_mul, mul_div_mul_comm]
  map_zero' := by
    have h1 := chartFun_eventuallyEq hdiv h (x := 0) (P := 0) (Q := 1) (by simp) (by simp)
    change (chartFun w θ h 0 : Germ (𝓝 p0) ℂ) = (↑(fun _ : Fin n → ℂ => (0 : ℂ)) : Germ (𝓝 p0) ℂ)
    exact Germ.coe_eq.2 (h1.trans (Eventually.of_forall fun p => by simp))
  map_add' := by
    rintro ⟨x, P₁, Q₁, h₁, e₁⟩ ⟨y, P₂, Q₂, h₂, e₂⟩
    have hxy : (x + y) * aeval (chartVar w θ) (Q₁ * Q₂) =
        aeval (chartVar w θ) (P₁ * Q₂ + P₂ * Q₁) := by
      simp only [map_mul, map_add]
      rw [← e₁, ← e₂]
      ring
    change (chartFun w θ h (x + y) : Germ (𝓝 p0) ℂ) =
      (chartFun w θ h x : Germ (𝓝 p0) ℂ) + (chartFun w θ h y : Germ (𝓝 p0) ℂ)
    rw [← Germ.coe_add, Germ.coe_eq]
    filter_upwards [chartFun_eventuallyEq hdiv h (by simp [h₁, h₂]) hxy,
      chartFun_eventuallyEq hdiv h h₁ e₁, chartFun_eventuallyEq hdiv h h₂ e₂,
      eventually_eval_chartGraph_ne_zero h h₁, eventually_eval_chartGraph_ne_zero h h₂] with
      p hp hp₁ hp₂ hq₁ hq₂
    rw [Pi.add_apply, hp, hp₁, hp₂, map_mul, map_add, map_mul, map_mul, div_add_div _ _ hq₁ hq₂]
    ring

theorem chartEv_apply (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0)
    (x : chartRing w θ p0 t0) :
    chartEv w θ hdiv h x = (chartFun w θ h x : Germ (𝓝 p0) ℂ) :=
  rfl

theorem chartFun_mul_eventuallyEq (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0) {x y : K}
    (hx : x ∈ chartRing w θ p0 t0) (hy : y ∈ chartRing w θ p0 t0) :
    chartFun w θ h (x * y) =ᶠ[𝓝 p0] chartFun w θ h x * chartFun w θ h y := by
  have := map_mul (chartEv w θ hdiv h) ⟨x, hx⟩ ⟨y, hy⟩
  rw [chartEv_apply, chartEv_apply, chartEv_apply, ← Germ.coe_mul, Germ.coe_eq] at this
  exact this

theorem chartFun_pow_eventuallyEq (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0) {x : K}
    (hx : x ∈ chartRing w θ p0 t0) (k : ℕ) :
    chartFun w θ h (x ^ k) =ᶠ[𝓝 p0] chartFun w θ h x ^ k := by
  have := map_pow (chartEv w θ hdiv h) ⟨x, hx⟩ k
  rw [chartEv_apply, chartEv_apply, ← Germ.coe_pow, Germ.coe_eq] at this
  exact this

theorem chartFun_algebraMap_eventuallyEq (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0)
    (c : ℂ) : chartFun w θ h (algebraMap ℂ K c) =ᶠ[𝓝 p0] fun _ => c := by
  filter_upwards [chartFun_eventuallyEq hdiv h (x := algebraMap ℂ K c) (P := C c) (Q := 1)
    (by simp) (by simp [Algebra.algebraMap_eq_smul_one])] with p hp
  rw [hp]
  simp

/-- `ev(w_i)` is the coordinate `p_i`. -/
theorem chartFun_w_eventuallyEq (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0) (i : Fin n) :
    chartFun w θ h (w i) =ᶠ[𝓝 p0] fun p => p i := by
  have := chartFun_aeval_eventuallyEq hdiv h (X (some i))
  rw [aeval_X, chartVar_some] at this
  filter_upwards [this] with p hp
  rw [hp, eval_X]
  rfl

/-- `ev(θ) = ϑ`. -/
theorem chartFun_theta_eventuallyEq (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0) :
    chartFun w θ h θ =ᶠ[𝓝 p0] chartTheta h := by
  have := chartFun_aeval_eventuallyEq hdiv h (X none)
  rw [aeval_X, chartVar_none] at this
  filter_upwards [this] with p hp
  rw [hp, eval_X]
  rfl

/-- **Units of `chartRing` evaluate to functions without zeros near `p₀`.** -/
theorem eventually_chartFun_ne_zero (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0) {x : K}
    (hx0 : x ≠ 0) (hx : x ∈ chartRing w θ p0 t0) (hx' : x⁻¹ ∈ chartRing w θ p0 t0) :
    ∀ᶠ p in 𝓝 p0, chartFun w θ h x p ≠ 0 := by
  have h1 := chartFun_mul_eventuallyEq hdiv h hx hx'
  rw [mul_inv_cancel₀ hx0] at h1
  have h2 : chartFun w θ h (1 : K) =ᶠ[𝓝 p0] fun _ => (1 : ℂ) := by
    simpa using chartFun_algebraMap_eventuallyEq hdiv h (1 : ℂ)
  filter_upwards [h1, h2] with p hp1 hp2
  intro hp
  rw [hp2, Pi.mul_apply, hp, zero_mul] at hp1
  exact one_ne_zero hp1

/-- **`ev(f(z)) = f ∘ μ`** for polynomials `f` and `z_i ∈ chartRing`. -/
theorem chartFun_aeval_eventuallyEq_eval (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0)
    {m : ℕ} {z : Fin m → K} (hz : ∀ i, z i ∈ chartRing w θ p0 t0) (f : MvPolynomial (Fin m) ℂ) :
    chartFun w θ h (aeval z f) =ᶠ[𝓝 p0] fun p => eval (fun i => chartFun w θ h (z i) p) f := by
  set z' : Fin m → chartRing w θ p0 t0 := fun i => ⟨z i, hz i⟩
  have hcoe : ∀ f : MvPolynomial (Fin m) ℂ,
      ((aeval z' f : chartRing w θ p0 t0) : K) = aeval z f := by
    intro f
    have := congrArg (fun φ : MvPolynomial (Fin m) ℂ →ₐ[ℂ] K => φ f)
      (MvPolynomial.comp_aeval (R := ℂ) z' (chartRing w θ p0 t0).val)
    simp only [AlgHom.comp_apply, Subalgebra.coe_val] at this
    rw [this]
  set ψ₁ : MvPolynomial (Fin m) ℂ →+* Germ (𝓝 p0) ℂ :=
    (chartEv w θ hdiv h).comp (aeval z' : MvPolynomial (Fin m) ℂ →ₐ[ℂ] chartRing w θ p0 t0)
  set ψ₂ : MvPolynomial (Fin m) ℂ →+* Germ (𝓝 p0) ℂ :=
    (Germ.coeRingHom (𝓝 p0)).comp
      (RingHom.pi fun p : Fin n → ℂ => eval fun i => chartFun w θ h (z i) p)
  have hψ : ψ₁ = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · change chartEv w θ hdiv h (aeval z' (C c)) =
      (↑(fun p : Fin n → ℂ => eval (fun i => chartFun w θ h (z i) p) (C c)) : Germ (𝓝 p0) ℂ)
      rw [chartEv_apply, hcoe, aeval_C, Germ.coe_eq]
      filter_upwards [chartFun_algebraMap_eventuallyEq hdiv h c] with p hp
      rw [hp, eval_C]
    · change chartEv w θ hdiv h (aeval z' (X i)) =
      (↑(fun p : Fin n → ℂ => eval (fun i => chartFun w θ h (z i) p) (X i)) : Germ (𝓝 p0) ℂ)
      rw [chartEv_apply, hcoe, aeval_X, Germ.coe_eq]
      exact Eventually.of_forall fun p => by simp only [eval_X]
  have := congrArg (fun ψ => ψ f) hψ
  change chartEv w θ hdiv h (aeval z' f) =
    (↑(fun p : Fin n → ℂ => eval (fun i => chartFun w θ h (z i) p) f) : Germ (𝓝 p0) ℂ) at this
  rw [chartEv_apply, hcoe, Germ.coe_eq] at this
  exact this

end Ring

/-! ### Derivatives of evaluated functions -/

section Deriv

variable {n : ℕ} {K : Type*} [Field K] [Algebra ℂ K] {w : Fin n → K} {θ : K}
  {Φ : MvPolynomial (Option (Fin n)) ℂ} {p0 : Fin n → ℂ} {t0 : ℂ}

variable (w) in
/-- Derivations `D_j` of `K` with `D_j(w_i) = δ_{ij}`. -/
def IsChartDeriv (D : Fin n → Derivation ℂ K K) : Prop :=
  ∀ j i, D j (w i) = if i = j then 1 else 0

variable (Φ) in
/-- `∂_T Φ` times the total derivative of `P(ϑ(w), w)` in the direction `w_j`:
`∂_j P · ∂_T Φ - ∂_T P · ∂_j Φ`. -/
def chartDPoly (j : Fin n) (P : MvPolynomial (Option (Fin n)) ℂ) :
    MvPolynomial (Option (Fin n)) ℂ :=
  pderiv (some j) P * pderiv none Φ - pderiv none P * pderiv (some j) Φ

theorem derivation_aeval_chartVar {D : Fin n → Derivation ℂ K K} (hD : IsChartDeriv w D)
    (j : Fin n) (R : MvPolynomial (Option (Fin n)) ℂ) :
    D j (aeval (chartVar w θ) R) =
      aeval (chartVar w θ) (pderiv none R) * D j θ + aeval (chartVar w θ) (pderiv (some j) R) := by
  rw [derivation_aeval, Fintype.sum_option]
  simp only [chartVar_none, chartVar_some, hD j, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- `Φ_T(θ, w) · D_j(P(θ, w)) = (chartDPoly Φ j P)(θ, w)`. -/
theorem aeval_chartDPoly {D : Fin n → Derivation ℂ K K} (hD : IsChartDeriv w D)
    (hΦ : aeval (chartVar w θ) Φ = 0) (j : Fin n) (P : MvPolynomial (Option (Fin n)) ℂ) :
    aeval (chartVar w θ) (chartDPoly Φ j P) =
      aeval (chartVar w θ) (pderiv none Φ) * D j (aeval (chartVar w θ) P) := by
  have hΦ' := derivation_aeval_chartVar (θ := θ) hD j Φ
  rw [hΦ, map_zero] at hΦ'
  rw [chartDPoly, map_sub, map_mul, map_mul, derivation_aeval_chartVar hD j P]
  linear_combination (aeval (chartVar w θ) (pderiv none P)) * hΦ'

/-- The representation of `D_j x` from one of `x`. -/
theorem derivation_mul_aeval {D : Fin n → Derivation ℂ K K} (hD : IsChartDeriv w D)
    (hΦ : aeval (chartVar w θ) Φ = 0) (j : Fin n) {x : K}
    {P Q : MvPolynomial (Option (Fin n)) ℂ}
    (hx : x * aeval (chartVar w θ) Q = aeval (chartVar w θ) P) :
    D j x * aeval (chartVar w θ) (Q ^ 2 * pderiv none Φ) =
      aeval (chartVar w θ) (Q * chartDPoly Φ j P - P * chartDPoly Φ j Q) := by
  have h1 := congrArg (D j) hx
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
  simp only [map_sub, map_mul, map_pow, aeval_chartDPoly hD hΦ]
  linear_combination (aeval (chartVar w θ) Q * aeval (chartVar w θ) (pderiv none Φ)) * h1 -
    (aeval (chartVar w θ) (pderiv none Φ) * D j (aeval (chartVar w θ) Q)) * hx

/-- **`chartRing` is stable under the derivations `D_j`**. -/
theorem derivation_mem_chartRing (h : IsChartPoint Φ p0 t0) {D : Fin n → Derivation ℂ K K}
    (hD : IsChartDeriv w D) (hΦ : aeval (chartVar w θ) Φ = 0) (j : Fin n) {x : K}
    (hx : x ∈ chartRing w θ p0 t0) : D j x ∈ chartRing w θ p0 t0 := by
  obtain ⟨P, Q, hQ, hxQ⟩ := hx
  exact ⟨_, Q ^ 2 * pderiv none Φ, by simp [hQ, h.eval_pderiv_ne_zero],
    derivation_mul_aeval hD hΦ j hxQ⟩

/-- Derivatives of `P(ϑ(p), p)` near `p₀`. -/
theorem eventually_hasFDerivAt_eval_chartGraph (h : IsChartPoint Φ p0 t0) :
    ∀ᶠ p in 𝓝 p0, ∀ P : MvPolynomial (Option (Fin n)) ℂ,
      HasFDerivAt (fun q => eval (chartGraph h q) P)
        (∑ j, (eval (chartGraph h p) (chartDPoly Φ j P) /
          eval (chartGraph h p) (pderiv none Φ)) •
            ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j) p := by
  filter_upwards [(eventually_chartTheta h).eventually_nhds,
    eventually_eval_chartGraph_ne_zero h h.eval_pderiv_ne_zero] with p hp hpT
  have hϑ : DifferentiableAt ℂ (chartTheta h) p := hp.self_of_nhds.2
  set L := fderiv ℂ (chartTheta h) p
  have hγ : ∀ o, HasFDerivAt (fun q => chartGraph h q o)
      (o.elim L fun i => ContinuousLinearMap.proj i) p := by
    intro o
    cases o with
    | none => exact hϑ.hasFDerivAt
    | some i => exact hasFDerivAt_apply i p
  have hz : HasFDerivAt (fun q => eval (chartGraph h q) Φ) (0 : (Fin n → ℂ) →L[ℂ] ℂ) p :=
    (hasFDerivAt_const (𝕜 := ℂ) (0 : ℂ) p).congr_of_eventuallyEq (hp.mono fun q hq => hq.1)
  have h0 := (hasFDerivAt_eval_mvPolynomial hγ Φ).unique hz
  intro P
  refine (hasFDerivAt_eval_mvPolynomial hγ P).congr_fderiv ?_
  ext v
  have hv := congrArg (fun T : (Fin n → ℂ) →L[ℂ] ℂ => T v) h0
  simp only [Fintype.sum_option, add_apply, sum_apply,
    smul_apply, smul_eq_mul, Option.elim, ContinuousLinearMap.proj_apply,
    zero_apply] at hv ⊢
  simp only [chartDPoly, map_sub, map_mul]
  set a := eval (chartGraph h p) (pderiv none Φ)
  have hL : L v = -(∑ i, eval (chartGraph h p) (pderiv (some i) Φ) * v i) / a := by
    field_simp
    linear_combination hv
  rw [hL]
  field_simp
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring

/-- Derivatives of `P(ϑ(p), p) / Q(ϑ(p), p)` near `p₀`. -/
theorem eventually_hasFDerivAt_div_chartGraph (h : IsChartPoint Φ p0 t0) :
    ∀ᶠ p in 𝓝 p0, ∀ P Q : MvPolynomial (Option (Fin n)) ℂ, eval (chartGraph h p) Q ≠ 0 →
      HasFDerivAt (fun q => eval (chartGraph h q) P / eval (chartGraph h q) Q)
        (∑ j, (eval (chartGraph h p) (Q * chartDPoly Φ j P - P * chartDPoly Φ j Q) /
          eval (chartGraph h p) (Q ^ 2 * pderiv none Φ)) •
            ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j) p := by
  filter_upwards [eventually_hasFDerivAt_eval_chartGraph h,
    eventually_eval_chartGraph_ne_zero h h.eval_pderiv_ne_zero] with p hp hpT
  intro P Q hQ
  have hinv := (hasFDerivAt_inv hQ).comp p (hp Q)
  refine (((hp P).mul hinv).congr_of_eventuallyEq
    (Eventually.of_forall fun q => by simp [div_eq_mul_inv])).congr_fderiv ?_
  ext v
  simp only [add_apply, sum_apply,
    smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, Function.comp_apply]
  simp only [map_sub, map_mul, map_pow]
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring

variable (D : Fin n → Derivation ℂ K K)

/-- **Compatibility of `ev` with the derivations** (chain rule step of `lem:c0-analytic-chart`):
`ev(x)` is holomorphic near `p₀` with `∂ ev(x) / ∂ p_j = ev(D_j x)`. -/
theorem eventually_hasFDerivAt_chartFun (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0)
    {D : Fin n → Derivation ℂ K K} (hD : IsChartDeriv w D) (hΦ : aeval (chartVar w θ) Φ = 0)
    {x : K} (hx : x ∈ chartRing w θ p0 t0) :
    ∀ᶠ p in 𝓝 p0, HasFDerivAt (chartFun w θ h x)
      (∑ j, chartFun w θ h (D j x) p •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j) p := by
  obtain ⟨P, Q, hQ, hxQ⟩ := hx
  have e0 := chartFun_eventuallyEq hdiv h hQ hxQ
  have ej : ∀ j, chartFun w θ h (D j x) =ᶠ[𝓝 p0] fun p =>
      eval (chartGraph h p) (Q * chartDPoly Φ j P - P * chartDPoly Φ j Q) /
        eval (chartGraph h p) (Q ^ 2 * pderiv none Φ) := fun j =>
    chartFun_eventuallyEq hdiv h (by simp [hQ, h.eval_pderiv_ne_zero])
      (derivation_mul_aeval hD hΦ j hxQ)
  filter_upwards [e0.eventuallyEq_nhds, eventually_all.2 ej,
    eventually_hasFDerivAt_div_chartGraph h,
    eventually_eval_chartGraph_ne_zero h hQ] with p hp0 hpj hpd hpQ
  refine ((hpd P Q hpQ).congr_of_eventuallyEq hp0).congr_fderiv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hpj j]

/-- `ev(x)` is holomorphic near `p₀`. -/
theorem eventually_differentiableAt_chartFun (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0)
    {x : K} (hx : x ∈ chartRing w θ p0 t0) :
    ∀ᶠ p in 𝓝 p0, DifferentiableAt ℂ (chartFun w θ h x) p := by
  obtain ⟨P, Q, hQ, hxQ⟩ := hx
  filter_upwards [(chartFun_eventuallyEq hdiv h hQ hxQ).eventuallyEq_nhds,
    eventually_hasFDerivAt_div_chartGraph h, eventually_eval_chartGraph_ne_zero h hQ] with
    p hp0 hpd hpQ
  exact ((hpd P Q hpQ).congr_of_eventuallyEq hp0).differentiableAt

variable (w θ) in
/-- The map `μ = (ev(z_1), …, ev(z_m))`. -/
def chartMap {m : ℕ} (h : IsChartPoint Φ p0 t0) (z : Fin m → K) (p : Fin n → ℂ) : Fin m → ℂ :=
  fun i => chartFun w θ h (z i) p

/-- **The derivative of `μ`**: `Dμ(p)` has the entries `ev(D_j z_i)(p)`. -/
theorem eventually_hasFDerivAt_chartMap {m : ℕ} (hdiv : ChartDiv w θ Φ)
    (h : IsChartPoint Φ p0 t0) {D : Fin n → Derivation ℂ K K} (hD : IsChartDeriv w D)
    (hΦ : aeval (chartVar w θ) Φ = 0) {z : Fin m → K} (hz : ∀ i, z i ∈ chartRing w θ p0 t0) :
    ∀ᶠ p in 𝓝 p0, HasFDerivAt (chartMap w θ h z)
      (ContinuousLinearMap.pi fun i => ∑ j, chartFun w θ h (D j (z i)) p •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j) p := by
  filter_upwards [eventually_all.2 fun i => eventually_hasFDerivAt_chartFun hdiv h hD hΦ (hz i)]
    with p hp
  refine hasFDerivAt_pi.2 fun i => ?_
  exact hp i

/-- The determinant of the matrix of a linear map `ℂⁿ → ℂⁿ` given by its rows. -/
theorem det_pi_sum_smul_proj (M : Matrix (Fin n) (Fin n) ℂ) :
    (ContinuousLinearMap.pi fun i => ∑ j, M i j •
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).det = M.det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
  congr 1
  ext i j
  simp [LinearMap.toMatrix'_apply, Pi.single_apply]

/-- **`det Dμ = ev(det (D_j z_i))`** near `p₀`. -/
theorem eventually_det_chartMap (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0)
    {D : Fin n → Derivation ℂ K K} (hD : IsChartDeriv w D) (hΦ : aeval (chartVar w θ) Φ = 0)
    {z : Fin n → K} (hz : ∀ i, z i ∈ chartRing w θ p0 t0) :
    ∀ᶠ p in 𝓝 p0, (ContinuousLinearMap.pi fun i => ∑ j, chartFun w θ h (D j (z i)) p •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).det =
      chartFun w θ h (Matrix.of fun i j => D j (z i)).det p := by
  set M : Matrix (Fin n) (Fin n) (chartRing w θ p0 t0) := fun i j =>
    ⟨D j (z i), derivation_mem_chartRing h hD hΦ j (hz i)⟩
  have hdet : ((M.det : chartRing w θ p0 t0) : K) = (Matrix.of fun i j => D j (z i)).det := by
    rw [← Subalgebra.coe_val, AlgHom.map_det]
    rfl
  have hev := RingHom.map_det (chartEv w θ hdiv h) M
  rw [chartEv_apply, hdet] at hev
  set F : Matrix (Fin n) (Fin n) ((Fin n → ℂ) → ℂ) := fun i j => chartFun w θ h (D j (z i))
  have hF : (chartEv w θ hdiv h).mapMatrix M = (Germ.coeRingHom (𝓝 p0)).mapMatrix F := by
    ext i j
    rfl
  rw [hF, ← RingHom.map_det] at hev
  have hev' : (chartFun w θ h (Matrix.of fun i j => D j (z i)).det : Germ (𝓝 p0) ℂ) =
      ((F.det : (Fin n → ℂ) → ℂ) : Germ (𝓝 p0) ℂ) := hev
  rw [Germ.coe_eq] at hev'
  filter_upwards [hev'] with p hp
  refine (det_pi_sum_smul_proj (n := n) (fun i j => chartFun w θ h (D j (z i)) p)).trans ?_
  rw [hp]
  have := RingHom.map_det (Pi.evalRingHom (fun _ : Fin n → ℂ => ℂ) p) F
  rw [Pi.evalRingHom_apply] at this
  rw [this]
  rfl

end Deriv

end EnvelopeProperty.Char0
