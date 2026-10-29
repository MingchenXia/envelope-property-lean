/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PositivityImport
import EnvelopeProperty.Projective.SubvarietyCompactification
import EnvelopeProperty.Local.PLApproxImport

/-!
# Local convexity on projective subvarieties and the uniform positivity theorem

Let `X = V(I) ⊆ ℙᴹ` be a projective subvariety (`ProjSubvariety`) over a trivially valued field
`k`, with quotient charts `ι_σ: U_σ ∩ X^an ≃ (Spec S''_{(σ̄)})^an` (`Projective/Subvariety.lean`).
This file proves

* the **remark after FHX Definition 5.3** (Fang–Han–Xia, *The envelope property for unibranch
  projective varieties*, `def:locally-L-psh`): local `O(a)`-convexity in one chart near each point
  (`ProjSubvariety.IsLocallyConvex`, `def:wu-proj-functions`(2)) implies convexity of
  `φ - m⁻¹ log|s|` on all of `P_s^an` for every admissible pair `(m, s)`
  (`ProjSubvariety.IsLocallyConvex.isLocallyConvexAll`), and conversely for `a > 0`
  (`ProjSubvariety.isLocallyConvexAll_iff`). The proof is FHX's: the chart change
  `ι_s ∘ ι_σ⁻¹` writes every function `τ̄ / σ̄^N` of the `σ`-chart as
  `(τ̄^D / s̄^{N d})^{1/D} (σ̄^D / s̄^d)^{-N/D}` in the `s`-chart (`D = deg s`, `d = deg σ`), so
  convex PL functions are transported (`ProjSubvariety.isConvexPLOn_comp_chartInv`), and
  `(a/d) log|σ| - m⁻¹ log|s| = (a / (d D)) log|σ̄^D / s̄^d|` is a rational multiple of the log of a
  function invertible on `P_σ ∩ P_s` (FHX Lemma 5.2(1), `IsConvexPLOn.add_smul_logAbs`);
* locally convex functions are continuous (`ProjSubvariety.IsLocallyConvex.continuous`);
* **uniform positivity** (`thm:wu-pos`), from the imported FHX Lemma 5.5 (`LocalPositivity`) and
  the uniform approximation of continuous psh functions (`lem:pg-uniform-approximation`):
  a locally `O(a)`-convex `φ: X^an → ℝ` on a projectively normal `X` is, for every `ε > 0`,
  within `ε` of a finite Fubini–Study function of class `O(a)`
  (`LocalPositivity.exists_isFiniteFS_abs_sub_le`). No continuity hypothesis is needed.

Blueprint: `wu-discharge.tex`, `def:wu-proj-functions` (the remark on FHX Definition 5.3) and
`thm:wu-pos`.

## Main results

* `ProjSubvariety.val_quotChartMk_eq`, `ProjSubvariety.log_val_quotChartMk_eq`: values of
  `τ̄ / σ̄^N` on the chart, read through `ι_σ⁻¹` (`lem:wu-proj-chart`(3)).
* The imported `ProjSubvariety.exists_eq_quotChartMk` represents every chart element as `τ̄ / σ̄^N`.
* `ProjSubvariety.isConvexPLOn_comp_chartInv`: chart change for convex PL functions.
* `ProjSubvariety.IsLocallyConvex.isLocallyConvexAll`,
  `ProjSubvariety.IsLocallyConvexAll.isLocallyConvex`,
  `ProjSubvariety.isLocallyConvexAll_iff`.
* `ProjSubvariety.IsLocallyConvex.continuous`.
* `LocalPositivity.isPSH_of_isLocallyConvex`, `LocalPositivity.exists_isFiniteFS_abs_sub_le`
  (`thm:wu-pos`, for every class `O(a)`, `a ∈ ℚ_{>0}`; the blueprint states `a = 1`).
-/

open scoped NNReal ENNReal Topology

open Topology

noncomputable section

namespace EnvelopeProperty

open ProjBerk

universe u

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}

/-! ### Functions on the charts -/

section ChartValues

variable {σ : MvPolynomial (Fin (M + 1)) k} {d : ℕ} (hσ : σ.IsHomogeneous d) (hd : 0 < d)

include hσ hd in
/-- `|τ̄ / σ̄^N|_y = |τ|_v / |σ|_v^N` with `v = ι_σ⁻¹(y)`, for a form `τ` of degree `N d`. -/
theorem val_quotChartMk_eq (y : Berk k (QuotChartAlg X.ideal σ d)) {N : ℕ}
    {τ : MvPolynomial (Fin (M + 1)) k} (hτ : τ.IsHomogeneous (N * d)) :
    y.val (quotChartMk X.ideal σ d N τ) =
      (X.chartInv σ d hσ hd y : ProjBerk k M).1.val τ /
        (X.chartInv σ d hσ hd y : ProjBerk k M).1.val σ ^ N := by
  conv_lhs => rw [← chartMap_chartInv hσ hd y]
  exact chartMap_val_quotChartMk _ _ hτ

include hσ hd in
/-- `log|τ̄ / σ̄^N|_y = log|τ|_v - N log|σ|_v` with `v = ι_σ⁻¹(y)`, where `|τ|_v ≠ 0`. -/
theorem log_val_quotChartMk_eq (y : Berk k (QuotChartAlg X.ideal σ d)) {N : ℕ}
    {τ : MvPolynomial (Fin (M + 1)) k} (hτ : τ.IsHomogeneous (N * d))
    (hτv : (X.chartInv σ d hσ hd y : ProjBerk k M).1.val τ ≠ 0) :
    Real.log (y.val (quotChartMk X.ideal σ d N τ) : ℝ) =
      Real.log ((X.chartInv σ d hσ hd y : ProjBerk k M).1.val τ : ℝ) -
        N * Real.log ((X.chartInv σ d hσ hd y : ProjBerk k M).1.val σ : ℝ) := by
  have hσv := chartInv_val_ne_zero hσ hd y
  rw [val_quotChartMk_eq hσ hd y hτ, NNReal.coe_div, NNReal.coe_pow,
    Real.log_div (NNReal.coe_ne_zero.2 hτv) (pow_ne_zero _ (NNReal.coe_ne_zero.2 hσv)),
    Real.log_pow]


end ChartValues

/-! ### Chart change for convex PL functions -/

/-- The linear identity behind the chart change: with `Lτᵢ = log|τᵢ|`, `Lσ = log|σ|`,
`Ls = log|s|`, a tropical affine function `∑ cᵢ (Lτᵢ - Nᵢ Lσ) + b` of the `σ`-chart is the
tropical affine function of the `s`-chart with the functions `σ̄^D / s̄^d` (coefficient
`-(∑ cᵢ Nᵢ) / D`) and `τ̄ᵢ^D / s̄^{Nᵢ d}` (coefficients `cᵢ / D`). -/
private theorem chart_change_identity {n : ℕ} (c : Fin n → ℝ) (N : Fin n → ℕ) (Lτ : Fin n → ℝ)
    (Lσ Ls : ℝ) {D : ℕ} (hD : (D : ℝ) ≠ 0) (d : ℕ) (b : ℝ) :
    ∑ i, c i * (Lτ i - N i * Lσ) + b =
      -(∑ i, c i * N i) / D * (D * Lσ - d * Ls) +
        ∑ i, c i / D * (D * Lτ i - ((N i * d : ℕ) : ℝ) * Ls) + b := by
  have h : ∀ i, c i / D * (D * Lτ i - ((N i * d : ℕ) : ℝ) * Ls) =
      c i * (Lτ i - N i * Lσ) + c i * N i / D * (D * Lσ - d * Ls) := by
    intro i
    push_cast
    field_simp
    ring
  simp only [h, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div]
  ring

/-- **Chart change** (FHX, the observation before Definition 5.3, with FHX Lemma 5.2(1)). Let
`W ⊆ X^an` be contained in `U_σ`, and let `F : X^an → [-∞, ∞]` be convex PL in the chart of `σ`
on `W`, i.e. `F ∘ ι_σ⁻¹` is convex PL on `ι_σ(W)`. Then `F` is convex PL in the chart of any other
form `s` of positive degree on `W ∩ U_s`: `F ∘ ι_s⁻¹` is convex PL on `ι_s(W ∩ U_s)`. A local
presentation `max_p (∑ cᵢ log|τ̄ᵢ / σ̄^{Nᵢ}| + b)` becomes
`max_p (-(∑ cᵢ Nᵢ)/D log|σ̄^D / s̄^d| + ∑ (cᵢ / D) log|τ̄ᵢ^D / s̄^{Nᵢ d}| + b)`. -/
theorem isConvexPLOn_comp_chartInv {σ : MvPolynomial (Fin (M + 1)) k} {d : ℕ}
    (hσ : σ.IsHomogeneous d) (hd : 0 < d) {s : MvPolynomial (Fin (M + 1)) k} {D : ℕ}
    (hs : s.IsHomogeneous D) (hD : 0 < D) {F : X.an → EReal} {W : Set X.an}
    (hWσ : ∀ v ∈ W, (v : ProjBerk k M).1.val σ ≠ 0)
    (hF : IsConvexPLOn (X.chartInv σ d hσ hd ⁻¹' W) fun y => F (X.chartInv σ d hσ hd y)) :
    IsConvexPLOn (X.chartInv s D hs hD ⁻¹' W) fun y => F (X.chartInv s D hs hD y) := by
  classical
  intro y hy
  have hvσ : (X.chartInv s D hs hD y : ProjBerk k M).1.val σ ≠ 0 := hWσ _ hy
  have hy'v : X.chartInv σ d hσ hd (X.chartMap σ d (X.chartInv s D hs hD y) hvσ) =
      X.chartInv s D hs hD y := chartInv_chartMap hσ hd _ hvσ
  obtain ⟨W', hW', hy'W', hW'W, n, f, S, hS, hf, hFeq⟩ :=
    hF (X.chartMap σ d (X.chartInv s D hs hD y) hvσ) (by rw [Set.mem_preimage, hy'v]; exact hy)
  choose N τ hτ hfτ using fun i => exists_eq_quotChartMk (X := X) hσ (f i)
  -- the functions of the `s`-chart
  let g : Fin (n + 1) → QuotChartAlg X.ideal s D :=
    Matrix.vecCons (quotChartMk X.ideal s D d (σ ^ D))
      fun i => quotChartMk X.ideal s D (N i * d) (τ i ^ D)
  -- the coefficients in the `s`-chart
  let T : (Fin n → ℚ) × ℚ → (Fin (n + 1) → ℚ) × ℚ := fun p =>
    (Matrix.vecCons (-(∑ i, p.1 i * N i) / D) fun i => p.1 i / D, p.2)
  have hσD : (σ ^ D).IsHomogeneous (d * D) := hσ.pow D
  have hτD : ∀ i, (τ i ^ D).IsHomogeneous ((N i * d) * D) := fun i => (hτ i).pow D
  have hopen : IsOpen (X.chartInv σ d hσ hd '' W') :=
    (isOpenEmbedding_chartInv hσ hd).isOpenMap _ hW'
  -- the facts needed at a point `z` of the new neighbourhood
  have key : ∀ z ∈ X.chartInv s D hs hD ⁻¹' (X.chartInv σ d hσ hd '' W'),
      ∃ z' ∈ W', X.chartInv σ d hσ hd z' = X.chartInv s D hs hD z ∧
        (X.chartInv s D hs hD z : ProjBerk k M).1.val σ ≠ 0 ∧
        ∀ i, (X.chartInv s D hs hD z : ProjBerk k M).1.val (τ i) ≠ 0 := by
    rintro z ⟨z', hz', hzz'⟩
    refine ⟨z', hz', hzz', hzz' ▸ chartInv_val_ne_zero hσ hd z', fun i => ?_⟩
    have h1 := hf z' hz' i
    rw [hfτ i, val_quotChartMk_eq hσ hd z' (hτ i), hzz'] at h1
    exact fun h0 => h1 (by rw [h0, zero_div])
  refine ⟨X.chartInv s D hs hD ⁻¹' (X.chartInv σ d hσ hd '' W'),
    hopen.preimage (continuous_chartInv hs hD), ⟨_, hy'W', hy'v⟩, ?_, n + 1, g, S.image T,
    hS.image T, ?_, ?_⟩
  · rintro z ⟨z', hz', hzz'⟩
    rw [Set.mem_preimage, ← hzz']
    exact hW'W hz'
  · intro z hz i
    obtain ⟨-, -, -, hzσ, hzτ⟩ := key z hz
    have hzs := chartInv_val_ne_zero hs hD z
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [g, Matrix.cons_val_zero]
      rw [val_quotChartMk_eq hs hD z hσD, map_pow]
      exact div_ne_zero (pow_ne_zero _ hzσ) (pow_ne_zero _ hzs)
    · simp only [g, Matrix.cons_val_succ]
      rw [val_quotChartMk_eq hs hD z (hτD j), map_pow]
      exact div_ne_zero (pow_ne_zero _ (hzτ j)) (pow_ne_zero _ hzs)
  · intro z hz
    obtain ⟨z', hz', hzz', hzσ, hzτ⟩ := key z hz
    have hzs := chartInv_val_ne_zero hs hD z
    have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    show F (X.chartInv s D hs hD z) = _
    rw [← hzz', show F (X.chartInv σ d hσ hd z') = _ from hFeq z' hz', Finset.sup'_image]
    congr 1
    refine Finset.sup'_congr hS rfl fun p _ => ?_
    simp only [Function.comp_apply, tropAffine, T, g, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    -- the logarithms in both charts
    have hlogf : ∀ i, Real.log (z'.val (f i) : ℝ) =
        Real.log ((X.chartInv s D hs hD z : ProjBerk k M).1.val (τ i) : ℝ) -
          N i * Real.log ((X.chartInv s D hs hD z : ProjBerk k M).1.val σ : ℝ) := by
      intro i
      rw [hfτ i, log_val_quotChartMk_eq hσ hd z' (hτ i) (by rw [hzz']; exact hzτ i), hzz']
    have hlog0 : Real.log (z.val (quotChartMk X.ideal s D d (σ ^ D)) : ℝ) =
        D * Real.log ((X.chartInv s D hs hD z : ProjBerk k M).1.val σ : ℝ) -
          d * Real.log ((X.chartInv s D hs hD z : ProjBerk k M).1.val s : ℝ) := by
      rw [log_val_quotChartMk_eq hs hD z hσD (by rw [map_pow]; exact pow_ne_zero _ hzσ), map_pow,
        NNReal.coe_pow, Real.log_pow]
    have hlogτ : ∀ i, Real.log (z.val (quotChartMk X.ideal s D (N i * d) (τ i ^ D)) : ℝ) =
        D * Real.log ((X.chartInv s D hs hD z : ProjBerk k M).1.val (τ i) : ℝ) -
          ((N i * d : ℕ) : ℝ) * Real.log ((X.chartInv s D hs hD z : ProjBerk k M).1.val s : ℝ) := by
      intro i
      rw [log_val_quotChartMk_eq hs hD z (hτD i) (by rw [map_pow]; exact pow_ne_zero _ (hzτ i)),
        map_pow, NNReal.coe_pow, Real.log_pow]
    simp only [hlogf, hlog0, hlogτ]
    have hid := chart_change_identity (fun i => (p.1 i : ℝ)) N
      (fun i => Real.log ((X.chartInv s D hs hD z : ProjBerk k M).1.val (τ i) : ℝ))
      (Real.log ((X.chartInv s D hs hD z : ProjBerk k M).1.val σ : ℝ))
      (Real.log ((X.chartInv s D hs hD z : ProjBerk k M).1.val s : ℝ)) hDr d (p.2 : ℝ)
    refine hid.trans ?_
    push_cast
    ring

/-! ### The remark after FHX Definition 5.3 -/

/-- **The remark after FHX Definition 5.3** (`def:locally-L-psh`; `def:wu-proj-functions`). If
`φ` is locally `O(a)`-convex in the chart-wise sense of (near each point, in the chart of
some form `σ ∉ I`), then `φ - m⁻¹ log|s|` is convex PL on all of `P_s^an` for every admissible pair
`(m, s)`: `φ` is locally `L`-convex in the sense of FHX Definition 5.3. Near a point of `P_s^an`,
take the chart `σ` of the hypothesis; the chart change (`isConvexPLOn_comp_chartInv`) transports
`φ - (a/d) log|σ|` to the `s`-chart, and
`(φ - (a/d) log|σ|) + (a / (d D)) log|σ̄^D / s̄^d| = φ - (a / D) log|s| = φ - m⁻¹ log|s|`
(FHX Lemma 5.2(1), `IsConvexPLOn.add_smul_logAbs`). -/
theorem IsLocallyConvex.isLocallyConvexAll {a : ℚ} {φ : X.an → ℝ} (h : X.IsLocallyConvex a φ) :
    X.IsLocallyConvexAll a φ := by
  intro m D s hs hD hm hDa _
  refine isConvexPLOn_of_local fun y _ => ?_
  obtain ⟨W, -, hxW, σ, d, hσ, hd, -, hWσ, hconv⟩ := h (X.chartInv s D hs hD y)
  let F : X.an → EReal := fun v =>
    ((φ v - (a : ℝ) / d * Real.log ((v : ProjBerk k M).1.val σ : ℝ) : ℝ) : EReal)
  have h1 : IsConvexPLOn (X.chartInv s D hs hD ⁻¹' W) fun z => F (X.chartInv s D hs hD z) :=
    isConvexPLOn_comp_chartInv hσ hd hs hD hWσ hconv
  have h2 := h1.add_smul_logAbs (quotChartMk X.ideal s D d (σ ^ D)) (a / (d * D))
  have hσD : (σ ^ D).IsHomogeneous (d * D) := hσ.pow D
  refine ⟨_, h2.isOpen, ⟨hxW, ?_⟩, Set.subset_univ _, h2.congr fun z hz => ?_⟩
  · show y.val _ ≠ 0
    rw [val_quotChartMk_eq hs hD y hσD, map_pow]
    exact div_ne_zero (pow_ne_zero _ (hWσ _ hxW)) (pow_ne_zero _ (chartInv_val_ne_zero hs hD y))
  · obtain ⟨hzW, hz0⟩ := hz
    have hzσ := hWσ _ hzW
    have hzs := chartInv_val_ne_zero hs hD z
    rw [Berk.logAbs_eq_coe_log hz0,
      log_val_quotChartMk_eq hs hD z hσD (by rw [map_pow]; exact pow_ne_zero _ hzσ), map_pow,
      NNReal.coe_pow, Real.log_pow]
    simp only [F, admChartFun]
    rw [← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    have hDa' : (D : ℝ) = m * a := by exact_mod_cast hDa
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have ha' : (a : ℝ) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hDa'
      exact hD' hDa'
    push_cast
    field_simp
    rw [hDa']
    ring

/-- Conversely (for `a > 0`), FHX's local `O(a)`-convexity implies the chart-wise one: every
point `x` has `|x_j|_x = 1` for some `j`, and `(m, s) = (den a, x_j^{num a})` is an admissible
pair with `x ∈ P_s^an`. -/
theorem IsLocallyConvexAll.isLocallyConvex {a : ℚ} (ha : 0 < a) {φ : X.an → ℝ}
    (h : X.IsLocallyConvexAll a φ) : X.IsLocallyConvex a φ := by
  intro x
  obtain ⟨j, hj⟩ := ProjBerk.exists_val_X_eq_one (x : ProjBerk k M)
  have hnum : 0 < a.num := Rat.num_pos.2 ha
  have hD : 0 < a.num.toNat := by omega
  have hs : ((MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ^ a.num.toNat).IsHomogeneous
      a.num.toNat := by
    simpa using (MvPolynomial.isHomogeneous_X k j).pow a.num.toNat
  have hxs : (x : ProjBerk k M).1.val
      ((MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ^ a.num.toNat) ≠ 0 := by
    rw [map_pow, hj, one_pow]
    exact one_ne_zero
  have hDa : ((a.num.toNat : ℕ) : ℚ) = a.den * a := by
    have hcast : ((a.num.toNat : ℕ) : ℚ) = (a.num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg hnum.le
    rw [hcast, mul_comm, Rat.mul_den_eq_num]
  have hsI := notMem_ideal_of_val_ne_zero hxs
  refine ⟨_, isOpen_setOf_val_ne_zero, hxs, _, a.num.toNat, hs, hD, hsI, fun v hv => hv, ?_⟩
  have h1 := h a.den a.num.toNat _ hs hD a.den_pos hDa hsI
  rw [admChartFun_eq_chartFun X a.den_pos hDa] at h1
  exact h1.mono (isOpen_setOf_val_ne_zero.preimage (continuous_chartInv hs hD))
    (Set.subset_univ _)

/-- **FHX Definition 5.3 and its remark**: for `a > 0`, FHX's local `O(a)`-convexity (every
admissible pair) is equivalent to chart-wise local `O(a)`-convexity. -/
theorem isLocallyConvexAll_iff {a : ℚ} (ha : 0 < a) {φ : X.an → ℝ} :
    X.IsLocallyConvexAll a φ ↔ X.IsLocallyConvex a φ :=
  ⟨fun h => h.isLocallyConvex ha, fun h => h.isLocallyConvexAll⟩

/-! ### Locally convex functions are continuous -/

/-- A locally `O(a)`-convex function is continuous: near `x`, in the chart of `σ`,
`φ ∘ ι_σ⁻¹ = (φ - (a/d) log|σ|) ∘ ι_σ⁻¹ + (a/d) log|σ| ∘ ι_σ⁻¹`, a convex PL (hence continuous)
function plus a continuous one, and `ι_σ⁻¹` is an open embedding. -/
theorem IsLocallyConvex.continuous {a : ℚ} {φ : X.an → ℝ} (h : X.IsLocallyConvex a φ) :
    Continuous φ := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨W, hW, hxW, σ, d, hσ, hd, -, hWσ, hconv⟩ := h x
  have hyx : X.chartInv σ d hσ hd (X.chartMap σ d x (hWσ x hxW)) = x :=
    chartInv_chartMap hσ hd x _
  have hyW : X.chartMap σ d x (hWσ x hxW) ∈ X.chartInv σ d hσ hd ⁻¹' W := by
    rw [Set.mem_preimage, hyx]
    exact hxW
  have hc : ContinuousAt (X.chartFun a φ σ d hσ hd) (X.chartMap σ d x (hWσ x hxW)) :=
    hconv.continuousOn.continuousAt ((hW.preimage (continuous_chartInv hσ hd)).mem_nhds hyW)
  let lg : Berk k (QuotChartAlg X.ideal σ d) → ℝ := fun y =>
    Real.log ((X.chartInv σ d hσ hd y : ProjBerk k M).1.val σ : ℝ)
  let r : Berk k (QuotChartAlg X.ideal σ d) → ℝ := fun y =>
    φ (X.chartInv σ d hσ hd y) - (a : ℝ) / d * lg y
  have hr : ContinuousAt r (X.chartMap σ d x (hWσ x hxW)) :=
    EReal.isEmbedding_coe.isInducing.continuousAt_iff.2 hc
  have h0 : Continuous fun y : Berk k (QuotChartAlg X.ideal σ d) =>
      (X.chartInv σ d hσ hd y : ProjBerk k M) :=
    continuous_subtype_val.comp (continuous_chartInv hσ hd)
  have hval : Continuous fun y : Berk k (QuotChartAlg X.ideal σ d) =>
      ((X.chartInv σ d hσ hd y : ProjBerk k M).1.val σ : ℝ) :=
    NNReal.continuous_coe.comp ((Berk.continuous_val_apply σ).comp
      (ProjBerk.continuous_val.comp h0))
  have hlg : ContinuousAt lg (X.chartMap σ d x (hWσ x hxW)) :=
    hval.continuousAt.log (NNReal.coe_ne_zero.2 (chartInv_val_ne_zero hσ hd _))
  have hconst : ContinuousAt (fun _ : Berk k (QuotChartAlg X.ideal σ d) => (a : ℝ) / d)
      (X.chartMap σ d x (hWσ x hxW)) := continuousAt_const
  have hcomp : ContinuousAt (φ ∘ X.chartInv σ d hσ hd) (X.chartMap σ d x (hWσ x hxW)) := by
    refine (hr.add (hconst.mul hlg)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [r, Function.comp_apply, Pi.add_apply, Pi.mul_apply]
    ring
  rw [← hyx]
  exact (isOpenEmbedding_chartInv hσ hd).continuousAt_iff.1 hcomp

end ProjSubvariety

/-! ### Uniform positivity (`thm:wu-pos`) -/

namespace LocalPositivity

variable {k : Type u} [Field k] [IsAlgClosed k] [LocalPositivity k] {M : ℕ}

/-- **FHX Lemma 5.5 for chart-wise locally convex functions.** On a projectively normal
`X = V(I) ⊆ ℙᴹ`, a function that is locally `O(a)`-convex in the chart-wise sense of (`def:wu-proj-functions`(2)) is `a`-psh: by the remark after FHX Definition 5.3
(`ProjSubvariety.IsLocallyConvex.isLocallyConvexAll`) it is locally `O(a)`-convex in the sense of
FHX, and the imported `LocalPositivity` applies. -/
theorem isPSH_of_isLocallyConvex (X : ProjSubvariety k M)
    (hX : IsIntegrallyClosed (MvPolynomial (Fin (M + 1)) k ⧸ X.ideal)) {a : ℚ} (ha : 0 < a)
    {φ : X.an → ℝ} (hφ : X.IsLocallyConvex a φ) : X.IsPSH (a : ℝ) fun v => (φ v : EReal) :=
  LocalPositivity.isPSH_of_isLocallyConvexAll X hX a ha φ hφ.isLocallyConvexAll

/-- **Positivity, uniform form** (`thm:wu-pos`). Let `X = V(I) ⊆ ℙᴹ` be projectively normal
(`R_M / I` integrally closed) and `a ∈ ℚ_{>0}`. For every locally `O(a)`-convex function
`φ : X^an → ℝ` and every `ε > 0` there is a finite Fubini–Study function `ψ` of class `O(a)` with
`|φ - ψ| ≤ ε` on `X^an`. Proof: `φ ∈ PSH(X, a)` by FHX Lemma 5.5 (`isPSH_of_isLocallyConvex`),
`φ` is continuous (`ProjSubvariety.IsLocallyConvex.continuous`), and continuous psh functions are
uniform limits of finite FS functions in their class (`lem:pg-uniform-approximation`,
`ProjSubvariety.IsPSH.exists_isFiniteFS_abs_sub_le`). The blueprint states the case `a = 1`. -/
theorem exists_isFiniteFS_abs_sub_le (X : ProjSubvariety k M)
    (hX : IsIntegrallyClosed (MvPolynomial (Fin (M + 1)) k ⧸ X.ideal)) {a : ℚ} (ha : 0 < a)
    {φ : X.an → ℝ} (hφ : X.IsLocallyConvex a φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : X.an → ℝ, X.IsFiniteFS a ψ ∧ ∀ x, |φ x - ψ x| ≤ ε :=
  (isPSH_of_isLocallyConvex X hX ha hφ).exists_isFiniteFS_abs_sub_le ha hφ.continuous hε

end LocalPositivity

end EnvelopeProperty
