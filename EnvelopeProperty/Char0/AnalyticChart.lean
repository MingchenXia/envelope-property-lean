/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.AnalyticChartAlgebra

/-!
# Analytic coordinates at a general point of the divisor (`lem:c0-analytic-chart`)

Let `V` be a divisorial valuation ring over `ℂ` in `N` variables (`BirationalDVR ℂ ℂ[z]`), with
coordinates `w = (π, u)` (a uniformizer `π` and lifts `u` of a transcendence basis of the residue
field, `lem:c0-dvr-curve`), indexed by `e : Option ι ≃ Fin N`, and let `f_1, …, f_p ∈ ℂ[z]` be
nonzero. This file proves the blueprint lemma `lem:c0-analytic-chart`
(`EnvelopeProperty/blueprint/src/char0.tex`): there are a point `p₀` of `ℂᴺ` with `p₀(π) = 0`, a
radius `δ ∈ (0, 1)` and a holomorphic map `μ : U → ℂᴺ` on the polydisc `U = ball p₀ δ` (sup norm),
with bounded image, such that, writing `s = p(π)` for the coordinate of `π`,

1. `f_i ∘ μ = s^{ord_V(f_i)} h_i` with `h_i` holomorphic and without zeros on `U`;
2. `det Dμ = s^{A(V) - 1} h_0` with `h_0` holomorphic and without zeros on `U`;
3. `μ` is injective on `U ∩ {s ≠ 0}`.

Here `A(V) = 1 + ord_V(Jac_V)` is `EnvelopeProperty.Char0.logDiscrepancy` for the coordinates
`(π, u)` (`lem:c0-dvr-jacobian`).

## Proof

`μ = (ev(z_1), …, ev(z_N))` for the evaluation homomorphism `ev` of
`EnvelopeProperty.Char0.AnalyticChartLocal`, built from the algebraic chart data of
`EnvelopeProperty.Char0.AnalyticChartAlgebra` at a point given by the Nullstellensatz
(`exists_chartPoint`) at which finitely many denominators do not vanish. Every nonzero `r ∈ V` is
`ε_r π^{ord_V r}` with `ε_r` a unit, so `ev(r) = s^{ord_V r} ev(ε_r)`, and `ev(ε_r)` has no zeros
near `p₀` since `ev(ε_r) ev(ε_r⁻¹) = 1`. This gives (1) for `r = f_i` and (2) for `r = Jac_V`,
using `det Dμ = ev(det(∂_j z_i))` (`eventually_det_chartMap`). For (3), `w_i = num_i(z)/den_i(z)`
gives `den_i(μ) p_i = num_i(μ)`, and `den_i(μ) = s^{ord den_i} ev(ε_{den_i})` has no zeros on
`{s ≠ 0}`.

## Main results

* `EnvelopeProperty.Char0.exists_analyticChart`: `lem:c0-analytic-chart`.
-/

noncomputable section

open scoped NNReal ENNReal Topology

open MvPolynomial Filter IsLocalRing Metric

namespace EnvelopeProperty.Char0

/-! ### Units times powers of a coordinate -/

section Abstract

variable {n : ℕ} {K : Type*} [Field K] [Algebra ℂ K] {w : Fin n → K} {θ : K}
  {Φ : MvPolynomial (Option (Fin n)) ℂ} {p0 : Fin n → ℂ} {t0 : ℂ}

/-- If `x = ε w_{s₀}^m` with `ε, ε⁻¹ ∈ chartRing`, then `ev(x) = p_{s₀}^m ev(ε)` near `p₀`, where
`ev(ε)` is holomorphic and without zeros. -/
theorem eventually_chartFun_eq_mul_pow (hdiv : ChartDiv w θ Φ) (h : IsChartPoint Φ p0 t0)
    {x ε : K} {m : ℕ} {s0 : Fin n} (hx : x = ε * w s0 ^ m) (hε0 : ε ≠ 0)
    (hε : ε ∈ chartRing w θ p0 t0) (hε' : ε⁻¹ ∈ chartRing w θ p0 t0) :
    ∀ᶠ p in 𝓝 p0, chartFun w θ h x p = p s0 ^ m * chartFun w θ h ε p ∧
      chartFun w θ h ε p ≠ 0 ∧ DifferentiableAt ℂ (chartFun w θ h ε) p := by
  have hw : w s0 ∈ chartRing w θ p0 t0 := by
    have := aeval_mem_chartRing (w := w) (θ := θ) p0 t0 (X (some s0))
    rwa [aeval_X, chartVar_some] at this
  have h1 := chartFun_mul_eventuallyEq hdiv h hε (pow_mem hw m)
  have h2 := chartFun_pow_eventuallyEq hdiv h hw m
  have h3 := chartFun_w_eventuallyEq hdiv h s0
  filter_upwards [h1, h2, h3, eventually_chartFun_ne_zero hdiv h hε0 hε hε',
    eventually_differentiableAt_chartFun hdiv h hε] with p hp1 hp2 hp3 hp4 hp5
  refine ⟨?_, hp4, hp5⟩
  rw [hx, hp1, Pi.mul_apply, hp2, Pi.pow_apply, hp3, mul_comm]

end Abstract

/-! ### The chart at a divisorial valuation ring -/

section Chart

variable {N : ℕ} (V : BirationalDVR ℂ (MvPolynomial (Fin N) ℂ)) {ι : Type*} [Fintype ι]
  [DecidableEq ι] {π : V.ring} {u : ι → V.ring}

omit [Fintype ι] [DecidableEq ι] in
theorem algebraMap_eq_aeval_X (F : MvPolynomial (Fin N) ℂ) :
    algebraMap (MvPolynomial (Fin N) ℂ) (FractionRing (MvPolynomial (Fin N) ℂ)) F =
      aeval (fun i => algebraMap (MvPolynomial (Fin N) ℂ)
        (FractionRing (MvPolynomial (Fin N) ℂ)) (X i)) F := by
  have := MvPolynomial.algHom_ext
    (f := IsScalarTower.toAlgHom ℂ (MvPolynomial (Fin N) ℂ) (FractionRing (MvPolynomial (Fin N) ℂ)))
    (g := aeval fun i => algebraMap (MvPolynomial (Fin N) ℂ)
      (FractionRing (MvPolynomial (Fin N) ℂ)) (X i)) (fun i => by simp)
  exact DFunLike.congr_fun this F

theorem logDiscrepancy_sub_one_toNat (hπ : Irreducible π)
    (hu : IsTranscendenceBasis ℂ (residue V.ring ∘ u)) (e : Option ι ≃ Fin N) :
    (logDiscrepancy hπ hu (z := fun o =>
        algebraMap (MvPolynomial (Fin N) ℂ) (FractionRing (MvPolynomial (Fin N) ℂ)) (X (e o)))
        (fun _ => V.algebraMap_mem _) - 1).toNat =
      (IsDiscreteValuationRing.addVal V.ring
        ⟨_, jacobian_mem hπ hu (z := fun o =>
          algebraMap (MvPolynomial (Fin N) ℂ) (FractionRing (MvPolynomial (Fin N) ℂ)) (X (e o)))
          (fun _ => V.algebraMap_mem _)⟩).toNat := by
  rw [logDiscrepancy]
  generalize IsDiscreteValuationRing.addVal V.ring _ = a
  induction a using ENat.recTopCoe with
  | top => simp
  | coe n => norm_cast; simp

/-- **Analytic coordinates at a general point of the divisor** (`lem:c0-analytic-chart`). For a
divisorial valuation ring `V` over `ℂ` with coordinates `(π, u)` indexed by `e`, and finitely many
nonzero polynomials `f_k`, there are `p₀` with `p₀(π) = 0`, `δ ∈ (0, 1)` and a holomorphic map
`μ` with derivative `μ'` on `U = ball p₀ δ`, with bounded image, such that (with `s = p(π)`)
`f_k ∘ μ = s^{ord_V f_k} h_k` and `det μ' = s^{A(V) - 1} h₀` with `h_k`, `h₀` holomorphic without
zeros on `U`, and `μ` is injective on `U ∩ {s ≠ 0}`. -/
theorem exists_analyticChart (hπ : Irreducible π) (hu : IsTranscendenceBasis ℂ (residue V.ring ∘ u))
    (e : Option ι ≃ Fin N) {κ : Type*} [Finite κ] (f : κ → MvPolynomial (Fin N) ℂ)
    (hf : ∀ k, f k ≠ 0) :
    ∃ (p0 : Fin N → ℂ) (δ : ℝ) (μ : (Fin N → ℂ) → Fin N → ℂ)
      (μ' : (Fin N → ℂ) → (Fin N → ℂ) →L[ℂ] Fin N → ℂ) (h : κ → (Fin N → ℂ) → ℂ)
      (h0 : (Fin N → ℂ) → ℂ),
      p0 (e none) = 0 ∧ 0 < δ ∧ δ < 1 ∧
      (∀ p ∈ ball p0 δ, HasFDerivAt μ (μ' p) p) ∧
      Bornology.IsBounded (μ '' ball p0 δ) ∧
      (∀ k, DifferentiableOn ℂ (h k) (ball p0 δ)) ∧
      (∀ k, ∀ p ∈ ball p0 δ,
        h k p ≠ 0 ∧ eval (μ p) (f k) = p (e none) ^ (V.ord (f k)).toNat * h k p) ∧
      DifferentiableOn ℂ h0 (ball p0 δ) ∧
      (∀ p ∈ ball p0 δ, h0 p ≠ 0 ∧ (μ' p).det = p (e none) ^ (logDiscrepancy hπ hu
        (z := fun o =>
          algebraMap (MvPolynomial (Fin N) ℂ) (FractionRing (MvPolynomial (Fin N) ℂ)) (X (e o)))
        (fun _ => V.algebraMap_mem _) - 1).toNat * h0 p) ∧
      Set.InjOn μ (ball p0 δ ∩ {p | p (e none) ≠ 0}) := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  set K := FractionRing (MvPolynomial (Fin N) ℂ)
  set w := chartW π u e
  set D := chartDeriv e hπ hu
  set s0 := e none
  set z : Fin N → K := fun i => algebraMap (MvPolynomial (Fin N) ℂ) K (X i)
  set Jac := jacobian (isTranscendenceBasis_dvrCoordinates hπ hu)
    (fun o => algebraMap (MvPolynomial (Fin N) ℂ) K (X (e o)))
  have hJac := BirationalDVR.jacobian_mem_and_ne_zero V hπ hu e
  obtain ⟨θ, Φ, hθV, hΦ, hΦT, hdiv, hrep⟩ := exists_chartData (V := V) e hπ hu
  -- `w_i = num_i(z) / den_i(z)`
  have hfrac : ∀ i, ∃ num den : MvPolynomial (Fin N) ℂ, den ≠ 0 ∧
      algebraMap (MvPolynomial (Fin N) ℂ) K den * w i =
        algebraMap (MvPolynomial (Fin N) ℂ) K num := by
    intro i
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin N) ℂ) (w i)
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap (MvPolynomial (Fin N) ℂ) K b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ K)).2 hb0
    refine ⟨a, b, hb0, ?_⟩
    rw [← hab, mul_div_cancel₀ _ hbK]
  choose num den hden hnd using hfrac
  -- the nonzero elements `f_k`, `den_i`, `Jac` of `V`
  let g : κ ⊕ (Fin N ⊕ Unit) → K := Sum.elim (fun k => algebraMap (MvPolynomial (Fin N) ℂ) K (f k))
    (Sum.elim (fun i => algebraMap (MvPolynomial (Fin N) ℂ) K (den i)) fun _ => Jac)
  have hgV : ∀ j, g j ∈ V.ring := by
    rintro (k | i | _)
    · exact V.algebraMap_mem _
    · exact V.algebraMap_mem _
    · exact hJac.1
  have hg0 : ∀ j, g j ≠ 0 := by
    rintro (k | i | _)
    · exact (map_ne_zero_iff _ (IsFractionRing.injective _ K)).2 (hf k)
    · exact (map_ne_zero_iff _ (IsFractionRing.injective _ K)).2 (hden i)
    · exact hJac.2
  have hdec : ∀ j, ∃ (m : ℕ) (ε : V.ringˣ), (⟨g j, hgV j⟩ : V.ring) = ε * π ^ m := fun j =>
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (fun h0 => hg0 j (congrArg Subtype.val h0)) hπ
  choose m ε hmε using hdec
  have hgε : ∀ j, g j = ((ε j : V.ring) : K) * w s0 ^ m j := by
    intro j
    have := congrArg Subtype.val (hmε j)
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow] at this
    have h' : g j = ((ε j : V.ring) : K) * (π : K) ^ m j := this
    rw [h']
    congr 2
    exact (chartW_apply_none π u e).symm
  -- the elements which must lie in the chart ring
  let Y : ((κ ⊕ (Fin N ⊕ Unit)) ⊕ (κ ⊕ (Fin N ⊕ Unit))) ⊕ Fin N → K :=
    Sum.elim (Sum.elim (fun j => ((ε j : V.ring) : K)) fun j => (((ε j)⁻¹ : V.ringˣ) : V.ring)) z
  have hYV : ∀ j, Y j ∈ V.ring := by
    rintro ((j | j) | i)
    · exact (ε j : V.ring).2
    · exact (((ε j)⁻¹ : V.ringˣ) : V.ring).2
    · exact V.algebraMap_mem _
  choose P Q hQ hPQ using fun j => hrep (Y j) (hYV j)
  set Qt := pderiv none Φ * ∏ j, Q j
  have hQt : aeval (chartVar w θ) Qt ∈ vUnits V.ring := by
    rw [map_mul, map_prod]
    exact (vUnits V.ring).mul_mem hΦT (prod_mem fun j _ => hQ j)
  have hs0m : (⟨w s0, chartW_mem π u e s0⟩ : V.ring) ∈ maximalIdeal V.ring := by
    have : (⟨w s0, chartW_mem π u e s0⟩ : V.ring) = π := Subtype.ext (chartW_apply_none π u e)
    rw [this]
    exact hπ.not_isUnit
  obtain ⟨p0, t0, hQt0, hΦ0, hp0⟩ :=
    exists_chartPoint V.ring (chartW_mem π u e) hθV hΦ hs0m hQt
  rw [map_mul, map_prod] at hQt0
  have hT : eval (chartPt p0 t0) (pderiv none Φ) ≠ 0 := left_ne_zero_of_mul hQt0
  have hQj : ∀ j, eval (chartPt p0 t0) (Q j) ≠ 0 := fun j =>
    Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hQt0) j (Finset.mem_univ j)
  set hcp : IsChartPoint Φ p0 t0 := ⟨hΦ0, hT⟩
  have hYR : ∀ j, Y j ∈ chartRing w θ p0 t0 := fun j => ⟨P j, Q j, hQj j, hPQ j⟩
  have hεR : ∀ j, ((ε j : V.ring) : K) ∈ chartRing w θ p0 t0 := fun j => hYR (Sum.inl (Sum.inl j))
  have hεR' : ∀ j, ((ε j : V.ring) : K)⁻¹ ∈ chartRing w θ p0 t0 := by
    intro j
    have := hYR (Sum.inl (Sum.inr j))
    have hinv : ((((ε j)⁻¹ : V.ringˣ) : V.ring) : K) = ((ε j : V.ring) : K)⁻¹ := by
      refine (eq_inv_of_mul_eq_one_right ?_)
      rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    simpa [Y, hinv] using this
  have hε0 : ∀ j, ((ε j : V.ring) : K) ≠ 0 := fun j h0 => (ε j).ne_zero (Subtype.ext h0)
  have hzR : ∀ i, z i ∈ chartRing w θ p0 t0 := fun i => hYR (Sum.inr i)
  have hD := isChartDeriv_chartDeriv e hπ hu
  set μ := chartMap w θ hcp z
  set μ' : (Fin N → ℂ) → (Fin N → ℂ) →L[ℂ] Fin N → ℂ := fun p =>
    ContinuousLinearMap.pi fun i => ∑ j, chartFun w θ hcp (D j (z i)) p •
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) j
  -- the eventual properties at `p₀`
  have hunit := fun j => eventually_chartFun_eq_mul_pow hdiv hcp (hgε j) (hε0 j) (hεR j) (hεR' j)
  have hpoly : ∀ F : MvPolynomial (Fin N) ℂ, chartFun w θ hcp (algebraMap _ K F) =ᶠ[𝓝 p0]
      fun p => eval (μ p) F := by
    intro F
    rw [algebraMap_eq_aeval_X]
    exact chartFun_aeval_eventuallyEq_eval hdiv hcp hzR F
  have hgR : ∀ j, g j ∈ chartRing w θ p0 t0 := by
    intro j
    rw [hgε j]
    have hw : w s0 ∈ chartRing w θ p0 t0 := by
      have := aeval_mem_chartRing (w := w) (θ := θ) p0 t0 (X (some s0))
      rwa [aeval_X, chartVar_some] at this
    exact mul_mem (hεR j) (pow_mem hw _)
  have hE5 : ∀ i, ∀ᶠ p in 𝓝 p0, eval (μ p) (den i) * p i = eval (μ p) (num i) := by
    intro i
    have hwi : w i ∈ chartRing w θ p0 t0 := by
      have := aeval_mem_chartRing (w := w) (θ := θ) p0 t0 (X (some i))
      rwa [aeval_X, chartVar_some] at this
    have h1 := chartFun_mul_eventuallyEq hdiv hcp (hgR (Sum.inr (Sum.inl i))) hwi
    simp only [g, Sum.elim_inr, Sum.elim_inl] at h1
    rw [hnd i] at h1
    filter_upwards [h1, hpoly (den i), hpoly (num i), chartFun_w_eventuallyEq hdiv hcp i] with
      p hp1 hp2 hp3 hp4
    rw [Pi.mul_apply, hp2, hp4, hp3] at hp1
    exact hp1.symm
  have hE1 := eventually_hasFDerivAt_chartMap hdiv hcp hD hΦ hzR
  have hE2 := eventually_det_chartMap hdiv hcp hD hΦ hzR
  have hE6 : ∀ᶠ p in 𝓝 p0, μ p ∈ ball (μ p0) 1 :=
    hE1.self_of_nhds.continuousAt.preimage_mem_nhds (ball_mem_nhds _ one_pos)
  have hall : ∀ᶠ p in 𝓝 p0, HasFDerivAt μ (μ' p) p ∧
      (μ' p).det = chartFun w θ hcp (Matrix.of fun i j => D j (z i)).det p ∧
      (∀ j, chartFun w θ hcp (g j) p = p s0 ^ m j * chartFun w θ hcp (ε j : V.ring) p ∧
        chartFun w θ hcp (ε j : V.ring) p ≠ 0 ∧
        DifferentiableAt ℂ (chartFun w θ hcp (ε j : V.ring)) p) ∧
      (∀ j, chartFun w θ hcp (g (Sum.inl j)) p = eval (μ p) (f j)) ∧
      (∀ i, chartFun w θ hcp (g (Sum.inr (Sum.inl i))) p = eval (μ p) (den i)) ∧
      (∀ i, eval (μ p) (den i) * p i = eval (μ p) (num i)) ∧ μ p ∈ ball (μ p0) 1 := by
    filter_upwards [hE1, hE2, eventually_all.2 hunit, eventually_all.2 fun k => hpoly (f k),
      eventually_all.2 fun i => hpoly (den i), eventually_all.2 hE5, hE6] with
      p h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.eventually_nhds_iff_ball.1 hall
  set δ := min δ₁ (1 / 2)
  have hδsub : ball p0 δ ⊆ ball p0 δ₁ := ball_subset_ball (min_le_left _ _)
  have hord : ∀ k, (V.ord (f k)).toNat = m (Sum.inl k) := by
    intro k
    have : V.toRing (f k) = ⟨g (Sum.inl k), hgV (Sum.inl k)⟩ := rfl
    rw [BirationalDVR.ord, this, IsDiscreteValuationRing.addVal_def _ (ε (Sum.inl k)) hπ _
      (hmε (Sum.inl k)), ENat.toNat_natCast]
  have hdetJ : (Matrix.of fun i j => D j (z i)).det = g (Sum.inr (Sum.inr ())) :=
    det_chartDeriv_eq_jacobian e hπ hu
  have hA : (logDiscrepancy hπ hu (z := fun o =>
        algebraMap (MvPolynomial (Fin N) ℂ) (FractionRing (MvPolynomial (Fin N) ℂ)) (X (e o)))
        (fun _ => V.algebraMap_mem _) - 1).toNat = m (Sum.inr (Sum.inr ())) := by
    rw [logDiscrepancy_sub_one_toNat]
    have := IsDiscreteValuationRing.addVal_def _ (ε (Sum.inr (Sum.inr ()))) hπ _
      (hmε (Sum.inr (Sum.inr ())))
    exact (congrArg ENat.toNat this).trans (ENat.toNat_natCast _)
  refine ⟨p0, δ, μ, μ', fun k => chartFun w θ hcp (ε (Sum.inl k) : V.ring),
    chartFun w θ hcp (ε (Sum.inr (Sum.inr ())) : V.ring), hp0, lt_min hδ₁ (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), fun p hp => (hball p (hδsub hp)).1, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · refine (isBounded_ball (x := μ p0) (r := 1)).subset ?_
    rintro _ ⟨p, hp, rfl⟩
    exact (hball p (hδsub hp)).2.2.2.2.2.2
  · intro k p hp
    exact ((hball p (hδsub hp)).2.2.1 (Sum.inl k)).2.2.differentiableWithinAt
  · intro k p hp
    obtain ⟨-, -, h3, h4, -, -, -⟩ := hball p (hδsub hp)
    refine ⟨(h3 (Sum.inl k)).2.1, ?_⟩
    rw [← h4 k, (h3 (Sum.inl k)).1, hord k]
  · intro p hp
    exact ((hball p (hδsub hp)).2.2.1 (Sum.inr (Sum.inr ()))).2.2.differentiableWithinAt
  · intro p hp
    obtain ⟨-, h2, h3, -, -, -, -⟩ := hball p (hδsub hp)
    refine ⟨(h3 (Sum.inr (Sum.inr ()))).2.1, ?_⟩
    rw [h2, hdetJ, (h3 (Sum.inr (Sum.inr ()))).1, hA]
  · rintro p ⟨hp, hps⟩ q ⟨hq, hqs⟩ hpq
    obtain ⟨-, -, hp3, -, hp5, hp6, -⟩ := hball p (hδsub hp)
    obtain ⟨-, -, hq3, -, hq5, hq6, -⟩ := hball q (hδsub hq)
    funext i
    have hdp : eval (μ p) (den i) ≠ 0 := by
      rw [← hp5 i, (hp3 (Sum.inr (Sum.inl i))).1]
      exact mul_ne_zero (pow_ne_zero _ hps) (hp3 _).2.1
    have hdq : eval (μ q) (den i) ≠ 0 := by
      rw [← hq5 i, (hq3 (Sum.inr (Sum.inl i))).1]
      exact mul_ne_zero (pow_ne_zero _ hqs) (hq3 _).2.1
    have h1 : p i = eval (μ p) (num i) / eval (μ p) (den i) := by
      rw [← hp6 i, mul_div_cancel_left₀ _ hdp]
    have h2 : q i = eval (μ q) (num i) / eval (μ q) (den i) := by
      rw [← hq6 i, mul_div_cancel_left₀ _ hdq]
    rw [h1, h2, hpq]

end Chart

end EnvelopeProperty.Char0
