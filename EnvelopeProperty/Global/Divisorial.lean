/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.ModelPSH
import EnvelopeProperty.Projective.ComparisonShilov

/-!
# Gauss extensions and divisorial points of a model

Let `𝒳 = (K, S, z)` be an integral multiprojective model of rank `r` over a trivially valued field
`k` (`EnvelopeProperty.MultiModel`, `def:gl-model`). This file implements the blueprint nodes
`def:gl-div`, `lem:gl-div-generic` and the construction part of `lem:gl-rees-points` of the global
chapter `global.tex` (subsection `subsec:gl-comparison`) of the formalization of Fang–Han–Xia,
*The envelope property for unibranch projective varieties* (FHX,
`subsec:prelim-berkovich`), following Boucksom–Jonsson, *Global pluripotential theory over a
trivially valued field* (BJ22, §1.3, Definition 2.10, Lemma 2.13). It generalizes the rank-one
template `EnvelopeProperty.Projective.SubvarietyGauss` to `MultiModel`; the divisoriality of the
points attached to discrete valuation rings of the charts is in
`EnvelopeProperty.Global.DivisorialChart`.

## Main definitions

* `MultiModel.gaussPt X v = σ(v)` (`def:gl-div`): the Gauss extension
  `|∑_λ p_λ t^λ|_{σ(v)} = max_λ |p_λ|_v e^{-λ}` of `v ∈ (Spec S)^an` to `S[t]`
  (`Berk.gauss v e⁻¹`).
* `MultiModel.IsDivisorial X v` (`def:gl-div`): `log|g|_{σ(v)} = -c ord_{R'}(g)` for all
  `g ∈ S[t]`, for some `c ∈ ℚ_{>0}` and some discrete valuation ring
  `S[t] ⊆ R' ⊆ Frac(S[t])`, essentially of finite type over `k` (`BirationalDVR k S[t]`).
* `MultiModel.tAdicDVR X = S[t]_{(t)}`.
* `EnvelopeProperty.mvGaussIdeal σ W`: the prime `m_W W[Y]` of `W[Y_σ]` for a discrete valuation
  ring `W`; its localization is the **Gauss extension of `W` in the variables `Y`**
  (`lem:bj-gauss-dvr` in several variables), a discrete valuation ring
  (`EnvelopeProperty.isDiscreteValuationRing_mvGaussIdeal`) with
  `ord(∑_a w_a Y^a) = min_a ord_W(w_a)` (`EnvelopeProperty.addVal_mvGaussIdeal`).
* `BirationalDVR.berkPoint V q`: the point `F ↦ q^{ord_V(F)}` of `(Spec B)^an` attached to a
  discrete valuation ring `V` birational to `B`.
* `MultiModel.ChartRing X j = B_j = A_j[t]` for a chart `j` (`lem:gl-charts`).
* `MultiModel.chartDivPoint X j hj V b` (`lem:gl-rees-points`): for a chart `j` and a discrete
  valuation ring `V` birational to `B_j`, the point `v_V ∈ U_j` with
  `|p T^a|_{v_V} = exp(-ord_V(p / z̃_j^a) / b)` (`MultiModel.chartDivPoint_val_ofPiece`); it is the
  inverse chart `ι_j⁻¹` of the point `x ↦ e^{-ord_V(x)/b}` of `(Spec A_j)^an`
  (`MultiModel.chartDivBerk`), and `|z^{(c)}_{j_c}|_{v_V} = 1`
  (`MultiModel.chartDivPoint_val_coordElem`).

## Main results

* `MultiModel.isDivisorial_triv` (`lem:gl-div-generic`): `⋆` is divisorial, with
  `R' = S[t]_{(t)}` and `c = 1`.
* `MultiModel.IsDivisorial.hasGenericSupport`, `MultiModel.IsDivisorial.mem_valSet`,
  `MultiModel.IsDivisorial.secAbs_ne_zero` (`lem:gl-div-generic`): `𝒳^div ⊆ 𝒳^val`; nonzero
  sections have finite logarithm at divisorial points.
* `MultiModel.chartMap_chartDivPoint`, `MultiModel.gauss_chartDivBerk_val`: `ι_j(v_V)` is
  `x ↦ e^{-ord_V(x)/b}`, and the Gauss point over it is `F ↦ e^{-ord_V(F)/b}` on `B_j` if `V` is
  monomial in `t` with `ord_V(t) = b > 0`.

## Deviations from the blueprint

* The point `v_V` is defined through the inverse chart `ι_j⁻¹` of `x ↦ e^{-ord_V(x)/b}`
  (`lem:gl-charts`(2)) rather than through `lem:gl-multigraded-extension` directly; the two agree
  (`MultiModel.chartDivPoint_val_ofPiece`).
* `lem:gl-rees-points` is split: the construction of `v_V` is here, its divisoriality in
  `EnvelopeProperty.Global.DivisorialChart` (for an arbitrary discrete valuation ring `V` monomial
  in `t` with `ord_V(t) = b > 0`), and the application to Rees valuations in
  `EnvelopeProperty.Global.Shilov`.
-/

open scoped NNReal ENNReal Topology Polynomial

open IsDiscreteValuationRing

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Gauss extensions of discrete valuation rings in several variables -/

section MvGauss

open MvPolynomial

variable (σ : Type*) (W : Type*) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

/-- The prime `m_W W[Y_σ]` of the polynomial ring over a discrete valuation ring `W`; the
localization `W[Y]_{m_W W[Y]}` is the Gauss extension of `W` in the variables `Y`
(`lem:bj-gauss-dvr` in several variables). -/
def mvGaussIdeal : Ideal (MvPolynomial σ W) :=
  Ideal.map (C : W →+* MvPolynomial σ W) (IsLocalRing.maximalIdeal W)

variable {σ W}

theorem mvGaussIdeal_eq_span {ϖ : W} (hϖ : Irreducible ϖ) :
    mvGaussIdeal σ W = Ideal.span {C ϖ} := by
  rw [mvGaussIdeal, (irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span, Set.image_singleton]

instance isPrime_mvGaussIdeal : (mvGaussIdeal σ W).IsPrime := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible W
  rw [mvGaussIdeal_eq_span hϖ, Ideal.span_singleton_prime (C_ne_zero.2 hϖ.ne_zero)]
  exact (prime_C_iff σ).2 hϖ.prime

/-- The Gauss extension `W[Y]_{m_W W[Y]}` of a discrete valuation ring in finitely many variables is
a discrete valuation ring. -/
instance isDiscreteValuationRing_mvGaussIdeal [Finite σ] :
    IsDiscreteValuationRing (Localization.AtPrime (mvGaussIdeal σ W)) := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible W
  exact isDiscreteValuationRing_atPrime (mvGaussIdeal_eq_span hϖ) (C_ne_zero.2 hϖ.ne_zero)

/-- **Gauss's lemma for the Gauss extension** (`lem:bj-gauss-dvr`, several variables):
`ord(∑_a w_a Y^a) = min_a ord_W(w_a)`. -/
theorem addVal_mvGaussIdeal [Finite σ] (p : MvPolynomial σ W) :
    addVal (Localization.AtPrime (mvGaussIdeal σ W))
        (algebraMap (MvPolynomial σ W) (Localization.AtPrime (mvGaussIdeal σ W)) p) =
      p.support.inf fun a => addVal W (p.coeff a) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible W
  by_cases hp : p = 0
  · simp [hp]
  obtain ⟨c₀, hc₀, hmin⟩ := p.support.exists_min_image (fun a => addVal W (p.coeff a))
    (by rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty])
  have hne : p.coeff c₀ ≠ 0 := mem_support_iff.1 hc₀
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 ((addVal_eq_top_iff (R := W)).not.2 hne)
  have hdiv : ∀ a, ϖ ^ m ∣ p.coeff a := fun a => by
    by_cases ha : a ∈ p.support
    · rw [← addVal_le_iff_dvd, addVal_pow, addVal_uniformizer hϖ, nsmul_one, hm]
      exact hmin a ha
    · rw [notMem_support_iff.1 ha]; exact dvd_zero _
  obtain ⟨q, hq⟩ := (C_dvd_iff_dvd_coeff _ _).2 hdiv
  have hq0 : ¬ C ϖ ∣ q := by
    rw [C_dvd_iff_dvd_coeff]
    intro h
    have h1 : p.coeff c₀ = ϖ ^ m * q.coeff c₀ := by rw [hq, coeff_C_mul]
    have h2 := congrArg (addVal W) h1
    rw [addVal_mul, addVal_pow, addVal_uniformizer hϖ, nsmul_one, ← hm] at h2
    have h3 : (1 : ℕ∞) ≤ addVal W (q.coeff c₀) := by
      rw [← addVal_uniformizer hϖ]; exact addVal_le_iff_dvd.2 (h c₀)
    have h4 : (m : ℕ∞) + 1 ≤ m := by
      calc (m : ℕ∞) + 1 ≤ m + addVal W (q.coeff c₀) := add_le_add_right h3 _
        _ = m := h2.symm
    exact absurd h4 (not_le.2 (ENat.lt_add_one_iff (ENat.natCast_ne_top m) |>.2 le_rfl))
  have key : addVal (Localization.AtPrime (mvGaussIdeal σ W))
      (algebraMap (MvPolynomial σ W) _ p) = m := by
    rw [hq, C_pow, addVal_algebraMap_atPrime (mvGaussIdeal_eq_span hϖ) m hq0]
  rw [key]
  refine le_antisymm (Finset.le_inf fun a ha => hm ▸ hmin a ha) ?_
  exact (Finset.inf_le hc₀).trans_eq hm.symm

end MvGauss

/-! ### Points defined by discrete valuation rings -/

namespace BirationalDVR

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]

/-- The point `F ↦ q^{ord_V(F)}` of `(Spec B)^an` attached to a discrete valuation ring `V`
birational to `B` and `0 ≤ q ≤ 1`. -/
def berkPoint (V : BirationalDVR k B) (q : ℝ≥0) (hq : q ≤ 1) : Berk k B :=
  Berk.ofFun (fun F => expOrd q (V.ord F)) (by simp) (by simp)
    (fun F G => by rw [V.ord_mul, expOrd_add])
    (fun F G => by
      rw [← (expOrd_antitone hq).map_min]
      exact expOrd_antitone hq (V.min_le_ord_add F G))
    (fun c hc => by rw [V.ord_algebraMap hc, expOrd_zero])

@[simp]
theorem berkPoint_val (V : BirationalDVR k B) {q : ℝ≥0} (hq : q ≤ 1) (F : B) :
    (V.berkPoint q hq).val F = expOrd q (V.ord F) :=
  rfl

theorem berkPoint_val_le_one (V : BirationalDVR k B) {q : ℝ≥0} (hq : q ≤ 1) (F : B) :
    (V.berkPoint q hq).val F ≤ 1 :=
  expOrd_le_one hq _

end BirationalDVR

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

/-- The coordinate ring `S` of a model is Noetherian (a finitely generated `k`-algebra). -/
instance isNoetherianRing_coordRing : IsNoetherianRing X.S :=
  Algebra.FiniteType.isNoetherianRing k X.S

instance isNoetherianRing_polynomial_coordRing : IsNoetherianRing (Polynomial X.S) :=
  Polynomial.isNoetherianRing

instance essFiniteType_polynomial_coordRing : Algebra.EssFiniteType k (Polynomial X.S) := by
  have : Algebra.FiniteType k (Polynomial X.S) :=
    Algebra.FiniteType.trans (S := X.S) inferInstance inferInstance
  infer_instance

/-! ### The Gauss extension and divisorial points (`def:gl-div`) -/

variable (X) in
/-- The **Gauss extension** `σ(v)` of `v ∈ (Spec S)^an` to `S[t]` (`def:gl-div`):
`|∑_λ p_λ t^λ|_{σ(v)} = max_λ |p_λ|_v e^{-λ}`. -/
def gaussPt (v : Berk k X.S) : Berk k (Polynomial X.S) :=
  Berk.gauss v ProjBerk.gaussRadius

theorem gaussPt_val (v : Berk k X.S) (g : Polynomial X.S) :
    (X.gaussPt v).val g = g.support.sup fun ℓ => v.val (g.coeff ℓ) * ProjBerk.gaussRadius ^ ℓ :=
  rfl

@[simp]
theorem gaussPt_val_C (v : Berk k X.S) (p : X.S) : (X.gaussPt v).val (Polynomial.C p) = v.val p :=
  Berk.gauss_val_C v _ p

variable (X) in
/-- **Divisorial points** of `𝒳` (`def:gl-div`; FHX `subsec:prelim-berkovich`, BJ22 §1.3):
`v ∈ 𝒳^an` is divisorial if there are `c ∈ ℚ_{>0}` and a discrete valuation ring
`S[t] ⊆ R' ⊆ Frac(S[t])`, essentially of finite type over `k` (`BirationalDVR k S[t]`), with
`log|g|_{σ(v)} = -c ord_{R'}(g)` for all `g ∈ S[t]`. -/
def IsDivisorial (v : X.an) : Prop :=
  ∃ (R' : BirationalDVR k (Polynomial X.S)) (c : ℚ), 0 < c ∧
    ∀ g : Polynomial X.S,
      Berk.logAbs g (X.gaussPt v.1) = -((c : ℝ) : EReal) * (R'.ord g : EReal)

/-- Multiplicative criterion for divisorial points: `|g|_{σ(v)} = e^{-c ord_{R'}(g)}`. -/
theorem isDivisorial_of_val_eq {v : X.an} (R' : BirationalDVR k (Polynomial X.S)) {c : ℚ}
    (hc : 0 < c) (h : ∀ g, (X.gaussPt v.1).val g = expOrd (expNeg c) (R'.ord g)) :
    X.IsDivisorial v :=
  ⟨R', c, hc, fun g => by rw [Berk.logAbs, h, log_expOrd_expNeg (by exact_mod_cast hc)]⟩

/-! #### The trivial point (`lem:gl-div-generic`) -/

instance isPrime_span_X_coordRing : (Ideal.span {(Polynomial.X : Polynomial X.S)}).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).2 Polynomial.prime_X

variable (X) in
/-- The discrete valuation ring `S[t]_{(t)} ⊆ Frac(S[t])` of the `t`-adic valuation. -/
def tAdicDVR : BirationalDVR k (Polynomial X.S) where
  ring := atPrimeRange (P := Ideal.span {Polynomial.X})
    (IsScalarTower.toAlgHom k _ (FractionRing (Polynomial X.S))) (IsFractionRing.injective _ _)
  isDVR := isDiscreteValuationRing_atPrimeRange _ _ rfl Polynomial.X_ne_zero
  essFiniteType := essFiniteType_atPrimeRange _ _
  algebraMap_mem g := mem_atPrimeRange _ _ g

theorem tAdicDVR_ord_X_pow_mul (m : ℕ) {q : Polynomial X.S} (hq : q.coeff 0 ≠ 0) :
    (X.tAdicDVR).ord (Polynomial.X ^ m * q) = m := by
  have hq' : ¬ (Polynomial.X : Polynomial X.S) ∣ q := by rw [Polynomial.X_dvd_iff]; exact hq
  have : IsDiscreteValuationRing (atPrimeRange (P := Ideal.span {Polynomial.X})
      (IsScalarTower.toAlgHom k _ (FractionRing (Polynomial X.S)))
      (IsFractionRing.injective _ _)) := (X.tAdicDVR).isDVR
  exact addVal_atPrimeRange _ _ rfl Polynomial.X_ne_zero m hq'

/-- `ord_{(t)}(g)` is the order of vanishing of `g` in `t`. -/
theorem tAdicDVR_ord {g : Polynomial X.S} (hg : g ≠ 0) :
    (X.tAdicDVR).ord g = g.natTrailingDegree := by
  obtain ⟨q, hq⟩ : Polynomial.X ^ g.natTrailingDegree ∣ g :=
    Polynomial.X_pow_dvd_iff.2 fun d hd => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd
  have hq0 : q.coeff 0 ≠ 0 := by
    have h := Polynomial.coeff_X_pow_mul q g.natTrailingDegree 0
    rw [zero_add, ← hq] at h
    rw [← h]
    exact mt Polynomial.trailingCoeff_eq_zero.1 hg
  conv_lhs => rw [hq]
  exact tAdicDVR_ord_X_pow_mul _ hq0

/-- `|g|_{σ(⋆)} = e^{-ord_t(g)}`. -/
theorem gaussPt_triv_val (g : Polynomial X.S) :
    (X.gaussPt (X.triv : Berk k X.S)).val g = expOrd (expNeg 1) ((X.tAdicDVR).ord g) := by
  by_cases hg : g = 0
  · simp [hg]
  rw [tAdicDVR_ord hg, expOrd_coe, gaussPt_val]
  refine le_antisymm (Finset.sup_le fun ℓ hℓ => ?_) ?_
  · rw [X.triv_val_of_ne_zero (Polynomial.mem_support_iff.1 hℓ), one_mul]
    exact pow_le_pow_of_le_one zero_le ProjBerk.gaussRadius_le_one
      (Polynomial.natTrailingDegree_le_of_mem_supp ℓ hℓ)
  · refine le_trans ?_ (Finset.le_sup (f := fun ℓ => (X.triv : Berk k X.S).val (g.coeff ℓ) *
      ProjBerk.gaussRadius ^ ℓ) (Polynomial.natTrailingDegree_mem_support_of_nonzero hg))
    rw [X.triv_val_of_ne_zero
      (Polynomial.mem_support_iff.1 (Polynomial.natTrailingDegree_mem_support_of_nonzero hg)),
      one_mul]
    rfl

variable (X) in
/-- **`lem:gl-div-generic`, first part**: the trivial point `⋆` is divisorial, with
`R' = S[t]_{(t)}` and `c = 1`. -/
theorem isDivisorial_triv : X.IsDivisorial X.triv :=
  isDivisorial_of_val_eq X.tAdicDVR one_pos fun g => by
    rw [gaussPt_triv_val, Rat.cast_one]

/-- **`lem:gl-div-generic`, second part**: divisorial points have generic support,
`𝒳^div ⊆ 𝒳^val`: `ord_{R'}(p) < ∞` for `p ≠ 0`, so `log|p|_v = -c ord_{R'}(p) > -∞`. -/
theorem IsDivisorial.hasGenericSupport {v : X.an} (hv : X.IsDivisorial v) :
    X.HasGenericSupport v.1 := by
  intro p hp h0
  obtain ⟨R', c, hc, h⟩ := hv
  have h1 := h (Polynomial.C p)
  have hbot : Berk.logAbs (Polynomial.C p) (X.gaussPt v.1) = ⊥ := by
    rw [Berk.logAbs_eq_bot_iff, gaussPt_val_C, h0]
  rw [hbot] at h1
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1
    ((R'.ord_eq_top_iff).not.2 (Polynomial.C_ne_zero.2 hp))
  rw [← hm] at h1
  have hm' : ((m : ℕ∞) : EReal) = ((m : ℝ) : EReal) := by
    rw [ENat.toENNReal_coe, ← ENNReal.coe_natCast, EReal.coe_nnreal_eq_coe_real,
      NNReal.coe_natCast]
  have : -((c : ℝ) : EReal) * ((m : ℕ∞) : EReal) ≠ ⊥ := by
    rw [hm', ← EReal.coe_neg, ← EReal.coe_mul]
    exact EReal.coe_ne_bot _
  exact this h1.symm

/-- `𝒳^div ⊆ 𝒳^val`: divisorial points lie in `MultiModel.valSet`. -/
theorem IsDivisorial.mem_valSet {v : X.an} (hv : X.IsDivisorial v) : v.1 ∈ X.valSet :=
  ⟨v.2, hv.hasGenericSupport⟩

/-- **`lem:gl-div-generic`**: a nonzero section has nonzero absolute value (finite logarithm) at
every divisorial point. -/
theorem IsDivisorial.secAbs_ne_zero {v : X.an} (hv : X.IsDivisorial v) {d : Fin r → ℤ} {f : K}
    (hf : f ∈ X.sections d) (hf0 : f ≠ 0) : X.secAbs v.1 d f ≠ 0 :=
  MultiModel.secAbs_ne_zero v.2.2 hv.hasGenericSupport hf hf0

theorem IsDivisorial.logSecAbs_ne_bot {v : X.an} (hv : X.IsDivisorial v) {d : Fin r → ℤ} {f : K}
    (hf : f ∈ X.sections d) (hf0 : f ≠ 0) : X.logSecAbs v.1 d f ≠ ⊥ := by
  rw [Ne, logSecAbs_eq_bot_iff]
  exact hv.secAbs_ne_zero hf hf0

/-! ### The point `v_V` of a chart (`lem:gl-rees-points`) -/

section ChartDivPoint

variable (X) in
/-- The ring `B_j = A_j[t]` of the chart `j`. -/
abbrev ChartRing (j : X.ChartIndex) : Type u := Polynomial (X.chartAlg j)

instance finiteType_chartRing (j : X.ChartIndex) : Algebra.FiniteType k (X.ChartRing j) :=
  Algebra.FiniteType.trans (S := X.chartAlg j) inferInstance inferInstance

theorem expNeg_inv_le_one (b : ℕ) : expNeg (b : ℝ)⁻¹ ≤ 1 :=
  ProjBerk.expNeg_le_one (by positivity)

variable {j : X.ChartIndex}

variable (X j) in
/-- The point `x ↦ e^{-ord_V(x)/b}` of `(Spec A_j)^an` attached to a discrete valuation ring `V`
birational to `B_j = A_j[t]` and `b ∈ ℕ`. -/
def chartDivBerk (V : BirationalDVR k (X.ChartRing j)) (b : ℕ) : Berk k (X.chartAlg j) :=
  Berk.proj (V.berkPoint (expNeg (b : ℝ)⁻¹) (expNeg_inv_le_one b))

theorem chartDivBerk_val (V : BirationalDVR k (X.ChartRing j)) (b : ℕ) (x : X.chartAlg j) :
    (X.chartDivBerk j V b).val x = expOrd (expNeg (b : ℝ)⁻¹) (V.ord (Polynomial.C x)) :=
  rfl

theorem chartDivBerk_val_le_one (V : BirationalDVR k (X.ChartRing j)) (b : ℕ)
    (x : X.chartAlg j) : (X.chartDivBerk j V b).val x ≤ 1 :=
  expOrd_le_one (expNeg_inv_le_one b) _

theorem chartScale_chartDivBerk (hj : ∀ c, X.coord c (j c) ≠ 0)
    (V : BirationalDVR k (X.ChartRing j)) (b : ℕ) (c : Fin r) :
    X.chartScale j (X.chartDivBerk j V b) c = 1 :=
  le_antisymm (Finset.sup_le fun _ _ => chartDivBerk_val_le_one V b _)
    (one_le_chartScale hj _ c)

theorem chartScalePow_chartDivBerk (hj : ∀ c, X.coord c (j c) ≠ 0)
    (V : BirationalDVR k (X.ChartRing j)) (b : ℕ) (a : Fin r →₀ ℕ) :
    X.chartScalePow j (X.chartDivBerk j V b) a = 1 := by
  simp [chartScalePow, chartScale_chartDivBerk hj]

variable (X j) in
/-- **The point `v_V`** (`lem:gl-rees-points`): for a chart `j` with all `f^{(c)}_{j_c} ≠ 0` and a
discrete valuation ring `B_j ⊆ V ⊆ Frac B_j`, the point `ι_j⁻¹(x ↦ e^{-ord_V(x)/b}) ∈ U_j`, with
`|p T^a|_{v_V} = e^{-ord_V(p / z̃_j^a)/b}` (`chartDivPoint_val_ofPiece`). -/
def chartDivPoint (hj : ∀ c, X.coord c (j c) ≠ 0) (V : BirationalDVR k (X.ChartRing j)) (b : ℕ) :
    X.an :=
  X.chartInv j hj (X.chartDivBerk j V b)

variable (hj : ∀ c, X.coord c (j c) ≠ 0) (V : BirationalDVR k (X.ChartRing j)) (b : ℕ)

/-- `|p T^a|_{v_V} = e^{-ord_V(p / z̃_j^a)/b}` (`lem:gl-rees-points`). -/
theorem chartDivPoint_val_ofPiece {a : Fin r →₀ ℕ} {f : K} (hf : f ∈ X.piece a) :
    (X.chartDivPoint j hj V b).1.val (X.ofPiece hf) =
      expOrd (expNeg (b : ℝ)⁻¹)
        (V.ord (Polynomial.C ⟨f / X.chartDen j a, div_chartDen_mem_chartAlg hf⟩)) := by
  rw [chartDivPoint, chartInv_val_ofPiece, chartScalePow_chartDivBerk hj, div_one]
  rfl

/-- `|z^{(c)}_{j_c}|_{v_V} = 1`. -/
theorem chartDivPoint_val_coordElem (c : Fin r) :
    (X.chartDivPoint j hj V b).1.val (X.coordElem ⟨c, j c⟩) = 1 := by
  rw [← X.chartMono_single, chartDivPoint, chartInv_val_chartMono,
    chartScalePow_chartDivBerk hj, inv_one]

theorem chartDivPoint_val_coordElem_ne_zero (c : Fin r) :
    (X.chartDivPoint j hj V b).1.val (X.coordElem ⟨c, j c⟩) ≠ 0 := by
  rw [chartDivPoint_val_coordElem]
  exact one_ne_zero

/-- `ι_j(v_V)` is the point `x ↦ e^{-ord_V(x)/b}` of `(Spec A_j)^an`. -/
theorem chartMap_chartDivPoint
    (h : ∀ c, (X.chartDivPoint j hj V b).1.val (X.coordElem ⟨c, j c⟩) ≠ 0) :
    X.chartMap hj (X.chartDivPoint j hj V b).1 h = X.chartDivBerk j V b :=
  chartMap_chartInv hj _

/-- The Gauss point of radius `e⁻¹` over `x ↦ e^{-ord_V(x)/b}` is `F ↦ e^{-ord_V(F)/b}` on
`B_j`, if `V` is monomial in `t` with `ord_V(t) = b > 0`. -/
theorem gauss_chartDivBerk_val (hb : 0 < b)
    (htorus : ∀ F : X.ChartRing j, V.ord F = F.support.inf fun ℓ =>
      V.ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞))
    (F : X.ChartRing j) :
    (Berk.gauss (X.chartDivBerk j V b) ProjBerk.gaussRadius).val F =
      expOrd (expNeg (b : ℝ)⁻¹) (V.ord F) := by
  rw [Berk.gauss_val_apply, htorus, expOrd_inf (expNeg_inv_le_one b)]
  refine Finset.sup_congr rfl fun ℓ _ => ?_
  rw [chartDivBerk_val, ProjBerk.gaussRadius_eq_pow hb, ← pow_mul, expOrd_add, expOrd_coe,
    mul_comm b ℓ]

end ChartDivPoint

end MultiModel

end EnvelopeProperty
