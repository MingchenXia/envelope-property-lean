/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.FiniteFibres
import EnvelopeProperty.Global.Comparison
import EnvelopeProperty.Global.ModelChangeSections
import EnvelopeProperty.Local.FiniteFlatNorm

/-!
# Weighted coefficient norms along finite morphisms of models

This file implements the blueprint node `prop:gl-weighted-norm` of `global.tex` (subsection
`subsec:gl-ample`) for the formalization of Fang–Han–Xia, *The envelope property for unibranch
projective varieties* (FHX, §4, Proposition 4.1,
`prop:weighted-coefficient-norm`, and `eq:divisorial-field-average`).

Let `h : 𝒯 → 𝒳` be a finite morphism of models (`MultiModel.FiniteHom`) with function fields
`K ⊆ E` of degree `d = [E : K]`, and `𝒳` **normal**. For Fubini–Study data
`φ = m⁻¹ max_t (log|s_t| + λ_t)` on `𝒯` of class `a` (`MultiModel.FSData`, `s_t ∈ R_{ma}(𝒯) ⊆ E`)
write the norm form of the linear form `∑_t X_t s_t` as
`N_{E[X]/K[X]}(∑_t X_t s_t) = ∑_I c_I X^I` (`EnvelopeProperty.normForm`, here
`normForm K D.termSec`).

## Main results

* `MultiModel.FiniteHom.coeff_normForm_mem_sections`: **`c_I ∈ R_{dma}(𝒳)`** (normality of `𝒳`
  only). On a chart `j` of `𝒳`, `c_I / z̃_j^{dma}` is a coefficient of the norm form of the
  `s_t / z̃_j^{ma} ∈ B_j`, elements of `E` integral over the integrally closed chart algebra
  `A_j`; norms of such elements lie in `A_j` (`Algebra.isIntegral_norm`, no separability), the
  coefficients of the norm form are recovered from its values on `k^σ` by the torus argument
  (`EnvelopeProperty.coeff_mem_of_forall_eval_mem`), and an element of `K` whose chart
  quotients lie in all chart algebras is a section
  (`MultiModel.mem_sections_of_forall_div_chartDenZ`, through the pigeonhole step
  `MultiModel.isAdmissible_of_forall_mul_chartDen` of the ideal argument).
* `MultiModel.FiniteHom.avFSData`: the Fubini–Study data
  `Av_h(φ) = (md)⁻¹ max_I (log|c_I| + ∑_t I_t λ_t)` of class `a` on `𝒳`;
  `MultiModel.FiniteHom.isFS_avFSData`: it is a Fubini–Study function (some `c_I ≠ 0`).
* `MultiModel.FiniteHom.eval_avFSData`: **the divisorial field average**
  `Av_h(φ)(v) = d⁻¹ ∑_{h(w) = v} d(w/v) φ(w)` for **every** `v ∈ 𝒳^val` (points with generic
  support, stronger than FHX, who state it on `𝒳^div`), with the multiplicities
  `d(w/v) = MultiModel.fibreDeg` of `def:gl-finite-fibres`. This is the norm identity for weighted
  Gauss norms over the completion `H(v)` (`Berk.wgaussValuation_normForm_flat` for `E / K` at the
  point `fieldPoint v` of `(Spec K)^an`, after the fibre bijection of `lem:gl-finite-fibres`), read
  on a chart `j` with `|z^{(c)}_{j_c}|_v = 1`.
* `MultiModel.FiniteHom.eval_avFSData_triv`: `Av_h(φ)(⋆) = φ(⋆)`.
* `MultiModel.FiniteHom.eval_avFSData_le`, `MultiModel.FiniteHom.eval_avFSData_eq`
  (`k` algebraically closed): **monotonicity and independence of the presentation**: if
  `φ ≤ φ'` on `𝒯^an` (any classes) then `Av_h(φ) ≤ Av_h(φ')` on `𝒳^an`, by the divisorial
  comparison theorem (`thm:gl-comparison`).

## Auxiliary algebra

* `EnvelopeProperty.eval_normForm_field`, `EnvelopeProperty.normForm_algebraMap_mul`,
  `EnvelopeProperty.normForm_ne_zero`: norm forms of finite field extensions.
* `EnvelopeProperty.coeff_normForm_mem_of_isIntegral`: the coefficients of the norm form of
  elements integral over an integrally closed `k`-subalgebra `A ⊆ K` with fraction field `K` lie
  in `A` (`k` infinite).
* `EnvelopeProperty.ereal_wavg_const`, `EnvelopeProperty.ereal_wavg_mono`: weighted averages in
  `[-∞, +∞]`.

## Deviations from the blueprint proof

* The blueprint shows integrality of the norm of the homogeneous linear form over `S[X]` and then
  uses the "ideal argument"; here integrality is proved on the charts `A_j` (integrally closed
  since `𝒳` is normal) for single elements, and the multivariable statement follows from the
  torus (Vandermonde) argument on the values `N_{E/K}(∑_t t_t s_t)`, `t ∈ k^σ`.
* The norm identity is applied at the field level (`E / K` at `fieldPoint v`), not on chart
  algebras `A_j ⊆ B_j`; the chart is only used to compare `|·|_v` with the absolute value on `K`.
* Normality of `𝒯` is never used.
-/

open scoped NNReal ENNReal Topology TensorProduct

open Topology MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Norm forms of finite field extensions -/

section NormFormField

variable {K E : Type*} [Field K] [Field E] [Algebra K E] {σ : Type*} [Fintype σ]

/-- The norm form of a finite field extension evaluates to the norm:
`N(∑_j X_j b_j)(t) = N_{E/K}(∑_j t_j b_j)`. -/
theorem eval_normForm_field [FiniteDimensional K E] (b : σ → E) (t : σ → K) :
    eval t (normForm K b) = Algebra.norm K (∑ j, t j • b j) := by
  have h := eval_map_normForm (K := K) (B := K) b t
  rw [Algebra.algebraMap_self, MvPolynomial.map_id] at h
  rw [h, ← Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.lid K E)]
  congr 1
  simp [map_sum]

/-- Homogeneity of the norm form: `N(∑_j X_j c b_j) = c^{[E : K]} N(∑_j X_j b_j)` for `c ∈ K`. -/
theorem normForm_algebraMap_mul [FiniteDimensional K E] (c : K) (b : σ → E) :
    normForm K (fun j => algebraMap K E c * b j) =
      C (c ^ Module.finrank K E) * normForm K b := by
  have e : (∑ j, (X j : MvPolynomial σ K) ⊗ₜ[K] (algebraMap K E c * b j)) =
      algebraMap (MvPolynomial σ K) (MvPolynomial σ K ⊗[K] E) (C c) *
        ∑ j, (X j : MvPolynomial σ K) ⊗ₜ[K] b j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      ← Algebra.smul_def, TensorProduct.tmul_smul, Algebra.algebraMap_self, RingHom.id_apply,
      MvPolynomial.C_mul', TensorProduct.smul_tmul']
  rw [normForm, e, map_mul, Algebra.norm_algebraMap, Module.finrank_baseChange, ← map_pow]
  rfl

/-- The norm form of a family with a nonzero member is nonzero. -/
theorem normForm_ne_zero [FiniteDimensional K E] {b : σ → E} {j₀ : σ} (hj₀ : b j₀ ≠ 0) :
    normForm K b ≠ 0 := by
  classical
  intro h0
  have h := eval_normForm_field (K := K) b (Pi.single j₀ 1)
  rw [h0, map_zero] at h
  have hs : ∑ j, (Pi.single j₀ (1 : K) : σ → K) j • b j = b j₀ := by
    rw [Finset.sum_eq_single j₀ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
      (fun h => absurd (Finset.mem_univ j₀) h), Pi.single_eq_same, one_smul]
  rw [hs] at h
  exact (Algebra.norm_ne_zero_iff.2 hj₀) h.symm

/-- **Coefficients from values** (torus argument): for `k ⊆ K` infinite and a `k`-subspace
`V ⊆ K`, if a polynomial `P ∈ K[X_j]` takes values in `V` on `k^σ`, its coefficients lie in
`V`. -/
theorem coeff_mem_of_forall_eval_mem {k : Type*} [Field k] [Infinite k] [Algebra k K]
    (V : Submodule k K) {P : MvPolynomial σ K}
    (hP : ∀ t : σ → k, eval (fun j => algebraMap k K (t j)) P ∈ V) (I : σ →₀ ℕ) :
    P.coeff I ∈ V := by
  classical
  let N : Submodule k (MvPolynomial σ K) :=
    { carrier := {Q | ∀ t : σ → k, eval (fun j => algebraMap k K (t j)) Q ∈ V}
      add_mem' := fun {Q Q'} hQ hQ' t => by
        rw [Set.mem_ofPred_eq] at hQ hQ'
        rw [map_add]; exact V.add_mem (hQ t) (hQ' t)
      zero_mem' := fun t => by rw [map_zero]; exact V.zero_mem
      smul_mem' := fun c Q hQ t => by
        rw [Set.mem_ofPred_eq] at hQ
        rw [← algebraMap_smul K c Q, smul_eval, ← Algebra.smul_def]
        exact V.smul_mem c (hQ t) }
  have hN : ∀ (c : σ) (s : k), s ≠ 0 → ∀ Q ∈ N, scaleVar (A := K) c s Q ∈ N := by
    intro c s _ Q hQ t
    have e : (eval fun j => algebraMap k K (t j)).comp (scaleVar (A := K) c s).toRingHom =
        eval fun j => algebraMap k K ((if j = c then s else 1) * t j) := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) fun d => ?_
      · simp [scaleVar]
      · simp [scaleVar]
        split_ifs <;> simp
    have := congrArg (fun F : MvPolynomial σ K →+* K => F Q) e
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    change eval _ (scaleVar c s Q) ∈ V
    rw [show eval (fun j => algebraMap k K (t j)) (scaleVar (A := K) c s Q) =
      eval (fun j => algebraMap k K ((if j = c then s else 1) * t j)) Q from this]
    exact hQ _
  have h1 := monomial_coeff_mem_of_scaleVar N hN hP I (fun _ => 1)
  rw [eval_monomial] at h1
  simpa [Finsupp.prod] using h1

/-- **Norm forms of integral elements over a normal domain.** Let `k ⊆ K` be infinite, `A ⊆ K`
an integrally closed `k`-subalgebra with fraction field `K`, and `b_j ∈ E` integral over `A`.
Then the coefficients of `N_{E[X]/K[X]}(∑_j X_j b_j)` lie in `A`. The values
`N_{E/K}(∑_j t_j b_j)`, `t ∈ k^σ`, are norms of elements integral over `A`, hence integral over `A`
(`Algebra.isIntegral_norm`, no separability) and in `A`; conclude by
`coeff_mem_of_forall_eval_mem`. -/
theorem coeff_normForm_mem_of_isIntegral {k : Type*} [Field k] [Infinite k] [Algebra k K]
    [Algebra k E] [IsScalarTower k K E] [FiniteDimensional K E]
    (A : Subalgebra k K) [IsIntegrallyClosed A] [IsFractionRing A K]
    {b : σ → E} (hb : ∀ j, IsIntegral A (b j)) (I : σ →₀ ℕ) : (normForm K b).coeff I ∈ A := by
  refine coeff_mem_of_forall_eval_mem (Subalgebra.toSubmodule A) (fun t => ?_) I
  rw [eval_normForm_field]
  have hx : IsIntegral A (∑ j, algebraMap k K (t j) • b j) := by
    refine IsIntegral.sum _ fun j _ => ?_
    rw [Algebra.smul_def]
    refine IsIntegral.mul ?_ (hb j)
    have : algebraMap K E (algebraMap k K (t j)) = algebraMap A E (algebraMap k A (t j)) := by
      rw [IsScalarTower.algebraMap_apply A K E]
      rfl
    rw [this]
    exact isIntegral_algebraMap
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm K hx)
  rw [Subalgebra.mem_toSubmodule, ← hy]
  exact y.2

end NormFormField

/-! ### Weighted averages in `[-∞, +∞]` -/

section WeightedAverage

/-- A weighted average `n⁻¹ ∑_i d_i y` of a constant, with positive integer weights `d_i` adding
up to `n > 0`, is `y` (also for `y = ±∞`). -/
theorem ereal_wavg_const {ι : Type*} (s : Finset ι) (d : ι → ℕ) {n : ℕ}
    (hd : ∀ i ∈ s, 1 ≤ d i) (hn : ∑ i ∈ s, d i = n) (hn0 : 0 < n) (y : EReal) :
    (((n : ℝ)⁻¹ : ℝ) : EReal) * ∑ i ∈ s, ((d i : ℝ) : EReal) * y = y := by
  classical
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.sum_empty] at hn
    exact hn0.ne hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hdR : ∀ i ∈ s, (0 : ℝ) < d i := fun i hi => by exact_mod_cast hd i hi
  induction y using EReal.rec with
  | bot =>
    have : ∑ i ∈ s, ((d i : ℝ) : EReal) * ⊥ = ⊥ := by
      rw [Finset.sum_congr rfl fun i hi => EReal.coe_mul_bot_of_pos (hdR i hi)]
      obtain ⟨i₀, hi₀⟩ := hs
      rw [← Finset.add_sum_erase s _ hi₀, EReal.bot_add]
    rw [this, EReal.coe_mul_bot_of_pos (inv_pos.2 hnR)]
  | top =>
    have : ∑ i ∈ s, ((d i : ℝ) : EReal) * ⊤ = ⊤ := by
      rw [Finset.sum_congr rfl fun i hi => EReal.coe_mul_top_of_pos (hdR i hi)]
      obtain ⟨i₀, hi₀⟩ := hs
      rw [← Finset.add_sum_erase s _ hi₀]
      exact EReal.top_add_of_ne_bot (ereal_finsetSum_ne_bot _ _ fun _ _ => top_ne_bot)
    rw [this, EReal.coe_mul_top_of_pos (inv_pos.2 hnR)]
  | coe y =>
    have h1 : ∑ i ∈ s, ((d i : ℝ) : EReal) * (y : EReal) =
        ((∑ i ∈ s, (d i : ℝ) * y : ℝ) : EReal) := by
      have := map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal)
        (fun i => (d i : ℝ) * y) s
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
      rw [this]
      simp only [EReal.coe_mul]
    have h2 : ∑ i ∈ s, (d i : ℝ) * y = n * y := by
      rw [← Finset.sum_mul, ← hn, Nat.cast_sum]
    rw [h1, h2, ← EReal.coe_mul, inv_mul_cancel_left₀ hnR.ne']

/-- Weighted averages with nonnegative weights are monotone. -/
theorem ereal_wavg_mono {ι : Type*} (s : Finset ι) (d : ι → ℕ) (n : ℕ) {x y : ι → EReal}
    (hxy : ∀ i ∈ s, x i ≤ y i) :
    (((n : ℝ)⁻¹ : ℝ) : EReal) * ∑ i ∈ s, ((d i : ℝ) : EReal) * x i ≤
      (((n : ℝ)⁻¹ : ℝ) : EReal) * ∑ i ∈ s, ((d i : ℝ) : EReal) * y i :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left (hxy i hi) (by exact_mod_cast (Nat.cast_nonneg (d i) : (0 : ℝ) ≤ _)))
    (by exact_mod_cast (inv_nonneg.2 (Nat.cast_nonneg n) : (0 : ℝ) ≤ _))

end WeightedAverage

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

/-! ### Chart denominators in `ℤ^r` and sections -/

theorem chartDenZ_ne_zero {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0) (a : Fin r → ℤ) :
    X.chartDenZ j a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun c _ => zpow_ne_zero _ (hj c)

theorem chartDenZ_nsmul (j : X.ChartIndex) (n : ℕ) (a : Fin r → ℤ) :
    X.chartDenZ j (n • a) = X.chartDenZ j a ^ n := by
  rw [chartDenZ, chartDenZ, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Pi.smul_apply, nsmul_eq_mul, mul_comm, zpow_mul, zpow_natCast]

/-- **Sections from charts**: if `f / z̃_j^a ∈ A_j` for every chart index `j` with nonzero
coordinates, then `f ∈ R_a` (`lem:gl-sections`(4), converse; the ideal argument). -/
theorem mem_sections_of_forall_div_chartDenZ {a : Fin r → ℤ} {f : K}
    (h : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → f / X.chartDenZ j a ∈ X.chartAlg j) :
    f ∈ X.sections a := by
  classical
  have hex : ∀ j : X.ChartIndex, ∃ e : Fin r →₀ ℕ, (∀ c, X.coord c (j c) ≠ 0) →
      ∃ g ∈ X.piece e, f * X.chartDen j e = g * X.chartDenZ j a := by
    intro j
    by_cases hj : ∀ c, X.coord c (j c) ≠ 0
    · obtain ⟨e, g, hg, hfg⟩ := (mem_chartAlg_iff hj).1 (h j hj)
      refine ⟨e, fun _ => ⟨g, hg, ?_⟩⟩
      rw [div_eq_div_iff (chartDenZ_ne_zero hj a) (chartDen_ne_zero hj e)] at hfg
      exact hfg
    · exact ⟨0, fun h' => absurd h' hj⟩
  choose e he using hex
  obtain ⟨b₀, hb₀⟩ := exists_nonneg_add a
  set C : Fin r →₀ ℕ := b₀ + ∑ j, e j with hCdef
  have hle : ∀ j, ∀ c, b₀ c + e j c ≤ C c := fun j c => by
    rw [hCdef, Finsupp.add_apply, Finsupp.finsetSum_apply]
    exact Nat.add_le_add_left (Finset.single_le_sum (f := fun j => e j c)
      (fun _ _ => zero_le) (Finset.mem_univ j)) _
  refine (isAdmissible_of_forall_mul_chartDen (C := C) (fun c => ?_) fun j hj => ?_).mem_sections
  · have h1 := hb₀ c
    have h2 : b₀ c ≤ C c := (Nat.le_add_right _ _).trans (hle (Classical.arbitrary _) c)
    have : (b₀ c : ℤ) ≤ C c := by exact_mod_cast h2
    omega
  · obtain ⟨g, hg, hfg⟩ := he j hj
    set D : Fin r →₀ ℕ := C - e j
    have hCD : C = e j + D := by
      ext c
      simp only [D, Finsupp.add_apply, Finsupp.tsub_apply]
      have := hle j c
      omega
    have hD : ∀ c, 0 ≤ a c + D c := fun c => by
      have h1 := hb₀ c
      have h2 : b₀ c ≤ D c := by
        simp only [D, Finsupp.tsub_apply]
        have := hle j c
        omega
      have : (b₀ c : ℤ) ≤ D c := by exact_mod_cast h2
      omega
    rw [hCD, chartDen_add, ← mul_assoc, hfg, mul_assoc, ← chartDen_addDeg hj hD]
    have := mul_mem_piece hg (X.chartDen_mem_piece j (addDeg a D))
    rwa [add_comm (e j), addDeg_add hD, add_comm (addDeg a D)]

/-! ### Fubini–Study data as logarithms -/

section Log

variable {Y : MultiModel k K r}

/-- The radius `e^λ ∈ ℝ_{≥0}`. -/
def expNN (x : ℝ) : ℝ≥0 :=
  ⟨Real.exp x, (Real.exp_pos x).le⟩

theorem coe_expNN (x : ℝ) : (expNN x : ℝ) = Real.exp x :=
  rfl

/-- `log |f|_v + λ = log (|f|_v e^λ)`. -/
theorem termVal_eq_log (d : Fin r → ℤ) (t : K × ℝ) (v : Y.an) :
    Y.termVal d t v = ENNReal.log ((Y.secAbs v.1 d t.1 * expNN t.2 : ℝ≥0) : ℝ≥0∞) := by
  rw [termVal_def, logSecAbs, ENNReal.coe_mul, ENNReal.log_mul_add,
    log_coe_nnreal_of_coe_eq_exp (coe_expNN t.2)]

/-- `φ(v) = m⁻¹ log max_t |f_t|_v e^{λ_t}`. -/
theorem FSData.eval_eq_log {a : Fin r → ℚ} (D : Y.FSData a) (v : Y.an) :
    D.eval v = (((D.m : ℝ)⁻¹ : ℝ) : EReal) *
      ENNReal.log ((D.terms.sup fun t => Y.secAbs v.1 D.deg t.1 * expNN t.2 : ℝ≥0) : ℝ≥0∞) := by
  rw [FSData.eval_def, log_coe_nnreal_finsetSup]
  congr 1
  exact Finset.sup_congr rfl fun t _ => termVal_eq_log _ _ _

/-- `m φ(v) = log max_t |f_t|_v e^{λ_t}`. -/
theorem FSData.coe_m_mul_eval {a : Fin r → ℚ} (D : Y.FSData a) (v : Y.an) :
    ((D.m : ℝ) : EReal) * D.eval v =
      ENNReal.log ((D.terms.sup fun t => Y.secAbs v.1 D.deg t.1 * expNN t.2 : ℝ≥0) : ℝ≥0∞) := by
  rw [FSData.eval_eq_log, ← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ D.m_ne_zero,
    EReal.coe_one, one_mul]

end Log

/-! ### The terms of Fubini–Study data -/

section Terms

variable {E : Type u} [Field E] [Algebra k E] {T : MultiModel k E r}

/-- The sections `s_t ∈ E` of Fubini–Study data, indexed by the terms. -/
def FSData.termSec {a : Fin r → ℚ} (D : T.FSData a) : D.terms → E :=
  fun t => t.1.1

/-- The weights `∑_t I_t λ_t` of the monomials `X^I` (`I ∈ ℕ^{terms}`). -/
def FSData.termWeight {a : Fin r → ℚ} (D : T.FSData a) (I : D.terms →₀ ℕ) : ℝ :=
  I.sum fun t n => (n : ℝ) * t.1.2

end Terms

/-! ### The weighted coefficient norm (`prop:gl-weighted-norm`) -/

namespace FiniteHom

variable {E : Type u} [Field E] [Algebra K E] [Algebra k E] [IsScalarTower k K E]
  {T : MultiModel k E r} (h : FiniteHom T X)

theorem chartDenZ_chartIndex (j : X.ChartIndex) (d : Fin r → ℤ) :
    T.chartDenZ (h.chartIndex j) d = algebraMap K E (X.chartDenZ j d) := by
  simp only [chartDenZ, coord_chartIndex, map_prod, map_zpow₀]

/-- The elements of the chart algebra `B_j` of `𝒯` are integral over the chart algebra `A_j`
of `𝒳`. -/
theorem isIntegral_of_mem_chartAlg (j : X.ChartIndex) {b : E}
    (hb : b ∈ T.chartAlg (h.chartIndex j)) : IsIntegral (X.chartAlg j) b := by
  obtain ⟨P, hPm, hP⟩ := h.isIntegral_chartAlgHom j ⟨b, hb⟩
  refine ⟨P, hPm, ?_⟩
  have e : algebraMap (X.chartAlg j) E = ((T.chartAlg (h.chartIndex j)).val :
      T.chartAlg (h.chartIndex j) →+* E).comp
        (h.chartAlgHom j : X.chartAlg j →+* T.chartAlg (h.chartIndex j)) :=
    RingHom.ext fun x => (h.coe_chartAlgHom j x).symm
  have := congrArg ((T.chartAlg (h.chartIndex j)).val :
      T.chartAlg (h.chartIndex j) →+* E) hP
  rw [map_zero, Polynomial.hom_eval₂] at this
  rw [e]
  exact this

variable [Infinite k]

include h in
/-- **`prop:gl-weighted-norm`, the coefficients are sections**: for a normal model `𝒳` and
Fubini–Study data `D` on `𝒯` of degree `m a`, the coefficients `c_I` of
`N_{E[X]/K[X]}(∑_t X_t s_t)` lie in `R_{d m a}(𝒳)`, `d = [E : K]`. -/
theorem coeff_normForm_mem_sections (hX : X.IsNormal) {a : Fin r → ℚ} (D : T.FSData a)
    (I : D.terms →₀ ℕ) :
    (normForm K D.termSec).coeff I ∈ X.sections (Module.finrank K E • D.deg) := by
  have := h.finiteDimensional
  refine mem_sections_of_forall_div_chartDenZ fun j hj => ?_
  set z := X.chartDenZ j D.deg
  have hz : z ≠ 0 := chartDenZ_ne_zero hj _
  set b : D.terms → E := fun t => D.termSec t / algebraMap K E z
  have hsb : D.termSec = fun t => algebraMap K E z * b t := by
    funext t
    rw [mul_div_cancel₀ _ ((map_ne_zero _).2 hz)]
  have hb : ∀ t, b t ∈ T.chartAlg (h.chartIndex j) := fun t => by
    have := T.div_chartDenZ_mem_chartAlg (h.chartIndex_ne_zero hj) (D.mem_sections t.1 t.2)
    rwa [h.chartDenZ_chartIndex] at this
  rw [hsb, normForm_algebraMap_mul, coeff_C_mul, ← chartDenZ_nsmul,
    mul_div_cancel_left₀ _ (chartDenZ_ne_zero hj _)]
  have := X.isIntegrallyClosed_chartAlg hj hX
  have := isFractionRing_chartAlg hj
  exact coeff_normForm_mem_of_isIntegral (X.chartAlg j)
    (fun t => h.isIntegral_of_mem_chartAlg j (hb t)) I

open Classical in
/-- **The weighted coefficient norm** `Av_h(φ)` (`prop:gl-weighted-norm`, FHX
`prop:weighted-coefficient-norm`) of Fubini–Study data `φ = m⁻¹ max_t (log|s_t| + λ_t)` on `𝒯`
of class `a`, for a normal model `𝒳`: the data
`(md)⁻¹ max_I (log|c_I| + ∑_t I_t λ_t)` of class `a` on `𝒳`, where
`N_{E[X]/K[X]}(∑_t X_t s_t) = ∑_I c_I X^I` and `d = [E : K]`. -/
def avFSData (hX : X.IsNormal) {a : Fin r → ℚ} (D : T.FSData a) : X.FSData a where
  m := Module.finrank K E * D.m
  m_pos := Nat.mul_pos (haveI := h.finiteDimensional; Module.finrank_pos) D.m_pos
  deg := Module.finrank K E • D.deg
  deg_eq c := by
    rw [intCast_nsmul_apply, D.deg_eq, Nat.cast_mul]
    ring
  terms := (normForm K D.termSec).support.image fun I =>
    ((normForm K D.termSec).coeff I, D.termWeight I)
  mem_sections t ht := by
    obtain ⟨I, -, rfl⟩ := Finset.mem_image.1 ht
    exact h.coeff_normForm_mem_sections hX D I

/-- `Av_h(φ)` is a Fubini–Study function of class `a` on `𝒳` as soon as one of the sections of
`φ` is nonzero (`prop:gl-weighted-norm`: "not all `c_I` vanish"). -/
theorem isFS_avFSData (hX : X.IsNormal) {a : Fin r → ℚ} (D : T.FSData a)
    (hD : ∃ t ∈ D.terms, t.1 ≠ 0) : X.IsFS a (h.avFSData hX D).eval := by
  classical
  have := h.finiteDimensional
  obtain ⟨t, ht, ht0⟩ := hD
  have hP : normForm K D.termSec ≠ 0 := normForm_ne_zero (j₀ := ⟨t, ht⟩) ht0
  obtain ⟨I, hI⟩ := Finset.nonempty_iff_ne_empty.2 fun h0 => hP (MvPolynomial.support_eq_empty.1 h0)
  refine ⟨h.avFSData hX D, ⟨((normForm K D.termSec).coeff I, D.termWeight I),
    Finset.mem_image.2 ⟨I, hI, rfl⟩, (MvPolynomial.mem_support_iff.1 hI)⟩, fun _ => rfl⟩

/-- **The divisorial field average** (`prop:gl-weighted-norm`, FHX
`eq:divisorial-field-average`): for every point `v ∈ 𝒳^val` (generic support),
`Av_h(φ)(v) = d⁻¹ ∑_{h(w) = v} d(w/v) φ(w)`, `d = [E : K]`, `d(w/v)` the multiplicities of
`def:gl-finite-fibres`.

Proof: on a chart `j` with `|z^{(c)}_{j_c}|_v = 1`, `|c_I|_v = |c_I / z̃_j^{dma}|_v` and
`|s_t|_w = |s_t / z̃_j^{ma}|_w` for `w` over `v`; the coefficients `c_I / z̃_j^{dma}` are those of
the norm form of the `b_t = s_t / z̃_j^{ma}` (homogeneity), and the weighted Gauss norm of that norm
form at `fieldPoint v` is `∏_w (max_t |b_t|_w e^{λ_t})^{d(w/v)}`
(`Berk.wgaussValuation_normForm_flat`, the norm identity over `H(v)`, reindexed by the fibre
bijection `FiniteHom.fibreEquiv`). Take logarithms. -/
theorem eval_avFSData (hX : X.IsNormal) {a : Fin r → ℚ} (D : T.FSData a) (v : X.an)
    (hv : X.HasGenericSupport v.1) :
    (h.avFSData hX D).eval v = (((Module.finrank K E : ℝ)⁻¹ : ℝ) : EReal) *
      ∑ w ∈ h.fibre v, ((T.fibreDeg K w : ℝ) : EReal) * D.eval w := by
  classical
  have := h.finiteDimensional
  set n := Module.finrank K E with hn
  obtain ⟨j, hj, hv1⟩ := X.exists_chartIndex v
  have hj' := h.chartIndex_ne_zero hj
  set z := X.chartDenZ j D.deg
  have hz : z ≠ 0 := chartDenZ_ne_zero hj _
  set b : D.terms → E := fun t => D.termSec t / algebraMap K E z
  have hsb : D.termSec = fun t => algebraMap K E z * b t := by
    funext t
    rw [mul_div_cancel₀ _ ((map_ne_zero _).2 hz)]
  set ρ : D.terms → ℝ≥0 := expRadius fun t => t.1.2
  set P := normForm K D.termSec
  set Pb := normForm K b
  have hcoeff : ∀ I, P.coeff I = X.chartDenZ j (n • D.deg) * Pb.coeff I := fun I => by
    simp only [P, Pb]
    rw [hsb, normForm_algebraMap_mul, coeff_C_mul, ← chartDenZ_nsmul]
  have hsupp : Pb.support ⊆ P.support := fun I hI => by
    rw [MvPolynomial.mem_support_iff] at hI ⊢
    rw [hcoeff]
    exact mul_ne_zero (chartDenZ_ne_zero hj _) hI
  -- the norm identity at `fieldPoint v`
  have hkey := Berk.wgaussValuation_normForm_flat (k := k) (B := K) (A := E) b ρ
    (X.fieldPoint v hv)
  -- left side: the coefficients of `Av_h(φ)`
  have hL : wgaussValuation (X.fieldPoint v hv).val ρ Pb =
      (h.avFSData hX D).terms.sup fun t =>
        X.secAbs v.1 (h.avFSData hX D).deg t.1 * expNN t.2 := by
    rw [wgaussValuation_eq_sup_of_subset _ _ _ hsupp]
    change _ = (P.support.image fun I => (P.coeff I, D.termWeight I)).sup _
    rw [Finset.sup_image]
    refine Finset.sup_congr rfl fun I _ => ?_
    simp only [Function.comp_apply]
    congr 1
    · change _ = X.secAbs v.1 (n • D.deg) (P.coeff I)
      rw [secAbs_eq_fieldVal hj v hv hv1 (h.coeff_normForm_mem_sections hX D I), hcoeff,
        mul_div_cancel_left₀ _ (chartDenZ_ne_zero hj _)]
      rfl
    · exact NNReal.eq ((coe_monoWeight_expRadius _ I).trans rfl)
  -- right side: reindex by the fibre of `h`
  have hR : ∏ y ∈ (Berk.finite_preimage_singleton (A := E) (X.fieldPoint v hv)).toFinset,
      (Finset.univ.sup fun t => y.val (b t) * ρ t) ^ Berk.flatFibreMult K y =
      ∏ w ∈ h.fibre v, (D.terms.sup fun t => T.secAbs w.1 D.deg t.1 * expNN t.2) ^
        T.fibreDeg K w := by
    symm
    refine Finset.prod_bij (fun w hw => (h.fibreEquiv v hv ⟨w, (h.mem_fibre).1 hw⟩ : Berk k E))
      (fun w hw => (Set.Finite.mem_toFinset _).2 (h.fibreEquiv v hv ⟨w, (h.mem_fibre).1 hw⟩).2)
      (fun w₁ h₁ w₂ h₂ he => ?_) (fun y hy => ?_) (fun w hw => ?_)
    · have := (h.fibreEquiv v hv).injective (Subtype.ext he)
      exact congrArg Subtype.val this
    · obtain ⟨⟨w, hw⟩, hwy⟩ :=
        (h.fibreEquiv v hv).surjective ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩
      exact ⟨w, (h.mem_fibre).2 hw, congrArg Subtype.val hwy⟩
    · have hwv : h.anMap w = v := (h.mem_fibre).1 hw
      have hgw : T.HasGenericSupport w.1 :=
        h.hasGenericSupport_of_anMap (by rw [hwv]; exact hv)
      have hw1 : ∀ c, w.1.val (T.coordElem ⟨c, h.chartIndex j c⟩) = 1 := fun c => by
        have := h.anMap_val_coordElem w ⟨c, j c⟩
        rw [hwv, hv1 c] at this
        exact this.symm
      rw [coe_fibreEquiv_apply, fibreDeg_of_hasGenericSupport hgw]
      congr 1
      rw [← univ_sup_subtype_val]
      refine Finset.sup_congr rfl fun t _ => ?_
      congr 1
      rw [secAbs_eq_fieldVal hj' w hgw hw1 (D.mem_sections t.1 t.2), h.chartDenZ_chartIndex]
      rfl
  -- take logarithms
  rw [FSData.eval_eq_log, ← hL, hkey, hR, log_coe_nnreal_finsetProd]
  simp only [log_coe_nnreal_pow, ← FSData.coe_m_mul_eval]
  have hm : (((h.avFSData hX D).m : ℝ)⁻¹ : ℝ) = (n : ℝ)⁻¹ * (D.m : ℝ)⁻¹ := by
    change (((n * D.m : ℕ) : ℝ))⁻¹ = _
    rw [Nat.cast_mul, mul_inv]
  rw [hm, EReal.coe_mul, mul_assoc]
  congr 1
  rw [ereal_coe_mul_finsetSum _ _ (inv_nonneg.2 (Nat.cast_nonneg _))]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← mul_assoc, ← mul_assoc, mul_comm (((D.m : ℝ)⁻¹ : ℝ) : EReal), mul_assoc, mul_assoc,
    ← mul_assoc (((D.m : ℝ)⁻¹ : ℝ) : EReal), ← EReal.coe_mul, inv_mul_cancel₀ D.m_ne_zero,
    EReal.coe_one, one_mul]

/-- `Av_h(φ)(⋆) = φ(⋆)`: the only point over `⋆` is `⋆`, with multiplicity `d`. -/
theorem eval_avFSData_triv (hX : X.IsNormal) {a : Fin r → ℚ} (D : T.FSData a) :
    (h.avFSData hX D).eval X.triv = D.eval T.triv := by
  have := h.finiteDimensional
  have hgv : X.HasGenericSupport (X.triv : X.an).1 := X.hasGenericSupport_triv
  rw [h.eval_avFSData hX D X.triv hgv]
  have e : ∑ w ∈ h.fibre X.triv, ((T.fibreDeg K w : ℝ) : EReal) * D.eval w =
      ∑ w ∈ h.fibre X.triv, ((T.fibreDeg K w : ℝ) : EReal) * D.eval T.triv :=
    Finset.sum_congr rfl fun w hw => by rw [h.eq_triv_of_anMap_eq_triv ((h.mem_fibre).1 hw)]
  rw [e]
  exact ereal_wavg_const _ _ (fun w hw => one_le_fibreDeg (h.hasGenericSupport_of_anMap
    (by rw [(h.mem_fibre).1 hw]; exact hgv))) (h.sum_fibreDeg _ hgv) Module.finrank_pos _

variable [IsAlgClosed k]

/-- **`prop:gl-weighted-norm`, monotonicity**: if `φ ≤ φ'` on `𝒯^an` (Fubini–Study data of any
classes, `φ` with a nonzero section), then `Av_h(φ) ≤ Av_h(φ')` on `𝒳^an`. Both agree with the
weighted averages on `𝒳^val ⊇ 𝒳^div`, and `Av_h(φ)` is psh; conclude by divisorial
comparison (`thm:gl-comparison`). -/
theorem eval_avFSData_le (hX : X.IsNormal) {a a' : Fin r → ℚ} (D : T.FSData a)
    (D' : T.FSData a') (hD : ∃ t ∈ D.terms, t.1 ≠ 0) (hle : ∀ w, D.eval w ≤ D'.eval w)
    (v : X.an) : (h.avFSData hX D).eval v ≤ (h.avFSData hX D').eval v :=
  (h.isFS_avFSData hX D hD).isPSH.le_of_forall_isDivisorial_le
    (h.avFSData hX D').continuous_eval.upperSemicontinuous (h.avFSData hX D').eval_ne_top
    (fun v hv => by
      rw [h.eval_avFSData hX D v hv.hasGenericSupport,
        h.eval_avFSData hX D' v hv.hasGenericSupport]
      exact ereal_wavg_mono _ _ _ fun w _ => hle w) v

/-- **`prop:gl-weighted-norm`, independence of the presentation**: Fubini–Study data defining the
same function on `𝒯^an` have the same weighted coefficient norm. -/
theorem eval_avFSData_eq (hX : X.IsNormal) {a a' : Fin r → ℚ} (D : T.FSData a)
    (D' : T.FSData a') (hD : ∃ t ∈ D.terms, t.1 ≠ 0) (hD' : ∃ t ∈ D'.terms, t.1 ≠ 0)
    (heq : ∀ w, D.eval w = D'.eval w) (v : X.an) :
    (h.avFSData hX D).eval v = (h.avFSData hX D').eval v :=
  le_antisymm (h.eval_avFSData_le hX D D' hD (fun w => (heq w).le) v)
    (h.eval_avFSData_le hX D' D hD' (fun w => (heq w).ge) v)

end FiniteHom

end MultiModel

end EnvelopeProperty
