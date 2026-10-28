/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.Comparison
import EnvelopeProperty.Global.Scaling

/-!
# Homogeneous Fubini–Study functions and comparison at Rees points

Let `𝒳 = (K, S, z)` be an integral multiprojective model of rank `r` over a trivially valued field
`k` (`EnvelopeProperty.MultiModel`, `def:gl-model`). This file implements the blueprint nodes
`lem:nn-hom-fs-operations`, `lem:nn-rees-points` and `lem:nn-hom-shilov` of the chapter
`nonnef.tex` (subsection `subsec:nn-shilov`, "Homogeneous comparison at Rees points") of the
formalization of Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX,
revision `832e086`). It is the input of PSH2 for homogeneous functions at classes outside the
model-nef cone (`thm:nn-psh2-hom`, `thm:nn-hom-max-diagonal`), which repairs the uses of
Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field* (BJ22), Theorem 4.5
at non-nef classes; the method is that of BJ22 `lem:Shilov` (`lem:CLT`, `lem:supPL`).

## Homogeneous Fubini–Study functions (`lem:nn-hom-fs-operations`)

For `F ∈ 𝓗_hom(𝒳, a)` (`MultiModel.IsHomFS`, all weights `0`):

1. `MultiModel.IsHomFS.isFS` (in `ModelPSH`), `MultiModel.IsHomFS.isScaleHomogeneous` (in
   `Scaling`), `MultiModel.IsHomFS.apply_triv` (`F(⋆) = 0`) and `MultiModel.IsHomFS.le_zero`
   (`F ≤ 0`);
2. `MultiModel.IsHomFS.mono_class`: `𝓗_hom(𝒳, a) ⊆ 𝓗_hom(𝒳, b)` for `a ≤ b`;
3. `MultiModel.IsHomFS.smul`: `c 𝓗_hom(𝒳, a) ⊆ 𝓗_hom(𝒳, c a)` for `c ∈ ℚ_{>0}`.

Parts 2 and 3 are deduced from the corresponding statements for `𝓗(𝒳, a)` and the
characterization `𝓗_hom = 𝓗 ∩ {homogeneous}` (`MultiModel.isHomFS_iff`, `lem:gl-scaling`(2)),
instead of the explicit families of the blueprint's proof.

## Points attached to Rees valuations (`lem:nn-rees-points`)

Let `j` be a chart (all `f^{(c)}_{j_c} ≠ 0`), `A_j` the chart algebra (`MultiModel.chartAlg`) and
`φ : ι → A_j` a finite family. The Rees valuation rings `V` of `(I; φ)`, `I = (φ_ι)`, are taken
inside `Frac A_j` (`EnvelopeProperty.reesValuationRing`, `def:bj-rees`); over a perfect field they
are discrete valuation rings, essentially of finite type over `k`
(`MultiModel.chartReesDVR`). The point `y_V = e^{-ord_V}` of `(Spec A_j)^an`
(`MultiModel.chartReesBerk`) is `≤ 1` on `A_j`, so its scales `μ_c(y_V)` are `1`, and
`v_V = ι_j⁻¹(y_V) ∈ U_j` (`MultiModel.chartReesPoint`) satisfies

* `MultiModel.chartReesPoint_val_coordElem`: `|z^{(c)}_{j_c}|_{v_V} = 1`;
* `MultiModel.secAbs_chartReesPoint`, `MultiModel.logSecAbs_chartReesPoint`:
  `log |f|(v_V) = -ord_V(f / z̃_j^d)` for `f ∈ R_d`, `d ∈ ℤ^r`;
* `MultiModel.chartReesDVR_ord_idx_pos`, `MultiModel.chartReesDVR_ord_idx_ne_top`,
  `MultiModel.chartReesDVR_ord_idx_le`: `ord_V(I) = ord_V(φ_ℓ)` (`ℓ` the chart of `V`) is a
  positive integer.

## Homogeneous comparison at finitely many points (`lem:nn-hom-shilov`)

`MultiModel.IsHomFS.exists_finset_le_of_le` (`k` algebraically closed): for every
`F ∈ 𝓗_hom(𝒳, a)` there is a finite set `Σ_F ⊆ 𝒳^an` with `F(v) ∈ (-∞, 0)` on `Σ_F` such that for
every `b ∈ ℚ^r`, every `G ∈ 𝓗_hom(𝒳, b)` and every rational `c > 0`, `G ≤ c F` on `Σ_F` implies
`G ≤ c F` on `𝒳^an`. With `F = m⁻¹ max_t log |f_t|`, `G = M⁻¹ max_s log |g_s|` and `c = p / q`, the
inequality `G(v) ≤ c F(v)` is `max_s |g_s|_v^{q m} ≤ max_t |f_t|_v^{p M}`
(`MultiModel.FSData.eval_le_mul_eval_iff`). `Σ_F` consists of the points `v_V` for the Rees
valuations `V` of the chart ideals `I_j = (f_t / z̃_j^{m a})_t`, over all charts. At `v_V` the
inequality says `ord_V(h_s) ≥ p M ord_V(I_j)` for `h_s = (g_s / z̃_j^{M b})^{q m}`
(`BirationalDVR.exists_nsmul_ord_le_of_berkPoint_le`); at a point `v` with `F(v) > -∞`, in a chart
with `|z^{(c)}_{j_c}|_v = 1`, the Rees valuations detect integral closure (`thm:bj-rees`,
`EnvelopeProperty.valuation_le_sup_pow_of_forall_dvd`) for the seminorm `ι_j(v)`, which gives
`G(v) ≤ c F(v)`. Divisorial points lie in `{F > -∞}` (`lem:gl-div-generic`), so the divisorial
comparison theorem (`thm:gl-comparison`, `MultiModel.IsPSH.le_of_forall_isDivisorial_le`, applied
to the psh function `G` and the continuous function `c F`) gives `G ≤ c F` everywhere.

## Deviations from the blueprint

* The Rees valuation rings are taken in `FractionRing A_j` rather than in `K` (an isomorphic
  fraction field), so that `EnvelopeProperty.BirationalDVR.ofSubalgebra` and
  `EnvelopeProperty.BirationalDVR.berkPoint` apply; the points `v_V` of `lem:nn-rees-points` are
  built directly on `A_j` (not on the cone chart `A_j[t]` of `EnvelopeProperty.Global.Shilov`,
  whose Rees points need sections without common zero, i.e. `t^N ∈ I^{(j)}`; here the sections
  `f_t` may have common zeros, which is the point of the non-nef case).
* `lem:nn-hom-fs-operations`(2), (3) are proved through `MultiModel.isHomFS_iff` (see above).
* The points of `Σ_F` are not shown to be divisorial (not needed).
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter IsDiscreteValuationRing

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Rees valuation rings: the chart generator is not a unit -/

/-- In a Rees valuation ring `V = (E_ℓ)_P` attached to the chart `ℓ` of `(g_i)_i`, the generator
`g_ℓ` is not a unit: it lies in the minimal prime `P` of `g_ℓ E_ℓ`. Hence `ord_V(I) = ord_V(g_ℓ)`
is positive (`def:bj-rees`). -/
theorem not_isUnit_algebraMap_idx_reesValuationRing {B : Type*} [CommRing B] {K : Type*} [Field K]
    [Algebra B K] [IsFractionRing B K] {ι : Type*} {g : ι → B} (x : ReesIndex K g) :
    ¬IsUnit (algebraMap B (reesValuationRing K g x) (g x.idx)) := by
  set E := reesNormalChart K g x.idx
  have hP : algebraMap B E (g x.idx) ∈ x.ideal :=
    x.mem_minimalPrimes.1.2 (Ideal.mem_span_singleton_self _)
  rintro ⟨u, hu⟩
  obtain ⟨a, s, hs, hv⟩ := mem_reesValuationRing.1 (u⁻¹ : (reesValuationRing K g x)ˣ).1.2
  have hs0 : (s : K) ≠ 0 := fun h => hs (by
    rw [show s = 0 from Subtype.ext h]; exact Ideal.zero_mem _)
  have h1 : algebraMap B K (g x.idx) * ((a : K) * (s : K)⁻¹) = 1 := by
    rw [← hv]
    have := congrArg Subtype.val u.mul_inv
    rw [hu] at this
    exact this
  have h2 : algebraMap B E (g x.idx) * a = s := by
    apply Subtype.ext
    change algebraMap B K (g x.idx) * (a : K) = (s : K)
    field_simp at h1
    exact h1
  exact hs (h2 ▸ Ideal.mul_mem_right _ _ hP)

/-! ### Points of discrete valuation rings: comparison of values -/

/-- At the point `F ↦ q^{ord_V(F)}` (`0 < q < 1`), the inequality `|F| ≤ max_{i ∈ s} |g_i|^n`
means `ord_V(F) ≥ n ord_V(g_i)` for some `i ∈ s` (the one of least order). -/
theorem BirationalDVR.exists_nsmul_ord_le_of_berkPoint_le {k : Type*} [Field k] {B : Type*}
    [CommRing B] [IsDomain B] [Algebra k B] (V : BirationalDVR k B) {q : ℝ≥0} (hq0 : 0 < q)
    (hq1 : q < 1) {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (g : ι → B) {F : B} {n : ℕ}
    (h : (V.berkPoint q hq1.le).val F ≤ (s.sup fun i => (V.berkPoint q hq1.le).val (g i)) ^ n) :
    ∃ i ∈ s, n • V.ord (g i) ≤ V.ord F := by
  simp only [BirationalDVR.berkPoint_val] at h
  obtain ⟨i₀, hi₀s, hi₀⟩ := Finset.exists_min_image s (fun i => V.ord (g i)) hs
  have hsup : (s.sup fun i => expOrd q (V.ord (g i))) = expOrd q (V.ord (g i₀)) :=
    le_antisymm (Finset.sup_le fun i hi => expOrd_antitone hq1.le (hi₀ i hi))
      (Finset.le_sup (f := fun i => expOrd q (V.ord (g i))) hi₀s)
  rw [hsup, ← expOrd_nsmul] at h
  exact ⟨i₀, hi₀s, le_of_expOrd_le hq0 hq1 h⟩

/-- `μ L ∈ (-∞, 0)` for a real `μ > 0` and `L ∈ (-∞, 0)`. -/
theorem ereal_coe_mul_mem_Ioo_of_pos {μ : ℝ} (hμ : 0 < μ) {L : EReal} (hL : L ≠ ⊥) (hL0 : L < 0) :
    ⊥ < (μ : EReal) * L ∧ (μ : EReal) * L < 0 := by
  induction L using EReal.rec with
  | bot => exact absurd rfl hL
  | top => exact absurd hL0 (not_lt.2 le_top)
  | coe l =>
    rw [← EReal.coe_mul]
    refine ⟨EReal.bot_lt_coe _, ?_⟩
    rw [← EReal.coe_zero, EReal.coe_lt_coe_iff] at hL0 ⊢
    exact mul_neg_of_pos_of_neg hμ hL0

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

/-! ### Homogeneous Fubini–Study functions (`lem:nn-hom-fs-operations`) -/

section Operations

variable {a b : Fin r → ℚ} {F : X.an → EReal}

/-- **`lem:nn-hom-fs-operations`(1)**: a homogeneous Fubini–Study function vanishes at `⋆`. -/
theorem IsHomFS.apply_triv (hF : X.IsHomFS a F) : F X.triv = 0 :=
  hF.isFS.isPSH.apply_triv_eq_zero hF.isScaleHomogeneous

/-- **`lem:nn-hom-fs-operations`(1)**: `F ≤ 0 = F(⋆)` for `F ∈ 𝓗_hom(𝒳, a)`. -/
theorem IsHomFS.le_zero (hF : X.IsHomFS a F) (v : X.an) : F v ≤ 0 :=
  hF.isFS.isPSH.nonpos hF.isScaleHomogeneous v

/-- **`lem:nn-hom-fs-operations`(2)**: `𝓗_hom(𝒳, a) ⊆ 𝓗_hom(𝒳, b)` for `a ≤ b`. -/
theorem IsHomFS.mono_class (hF : X.IsHomFS a F) (hab : a ≤ b) : X.IsHomFS b F :=
  isHomFS_iff.2 ⟨hF.isFS.mono_class hab, hF.isScaleHomogeneous⟩

/-- **`lem:nn-hom-fs-operations`(3)**: `c 𝓗_hom(𝒳, a) ⊆ 𝓗_hom(𝒳, c a)` for `c ∈ ℚ_{>0}`. -/
theorem IsHomFS.smul (hF : X.IsHomFS a F) {c : ℚ} (hc : 0 < c) :
    X.IsHomFS (c • a) fun v => ((c : ℝ) : EReal) * F v :=
  isHomFS_iff.2 ⟨hF.isFS.smul hc, fun t ht v => by
    simp only
    rw [hF.isScaleHomogeneous t ht v, mul_left_comm]⟩

end Operations

/-! ### Homogeneous Fubini–Study data in multiplicative form -/

section Multiplicative

variable {a b : Fin r → ℚ}

/-- For data with zero weights, `m⁻¹ max_t log |f_t|_v = m⁻¹ log max_t |f_t|_v`. -/
theorem FSData.eval_eq_log_sup_secAbs (D : X.FSData a) (hD : ∀ t ∈ D.terms, t.2 = 0)
    (v : X.an) :
    D.eval v = (((D.m : ℝ)⁻¹ : ℝ) : EReal) *
      ENNReal.log ((D.terms.sup fun t => X.secAbs v.1 D.deg t.1 : ℝ≥0) : ℝ≥0∞) := by
  rw [FSData.eval_def, Finset.apply_sup_eq_sup_comp_of_linearOrder
    (fun x : ℝ≥0 => ENNReal.log (x : ℝ≥0∞)) (ENNReal.log_monotone.comp ENNReal.coe_mono)
    (by simp)]
  congr 1
  refine Finset.sup_congr rfl fun t ht => ?_
  rw [termVal_def, hD t ht, EReal.coe_zero, add_zero]
  rfl

/-- **Multiplicative form of `G ≤ c F`** for homogeneous Fubini–Study data: with
`F = m⁻¹ max_t log |f_t|`, `G = M⁻¹ max_s log |g_s|` and `c = p / q` (`q = c.den`,
`p = c.num`), `G(v) ≤ c F(v)` iff `max_s |g_s|_v^{q m} ≤ max_t |f_t|_v^{p M}`. -/
theorem FSData.eval_le_mul_eval_iff (E : X.FSData b) (hE : ∀ s ∈ E.terms, s.2 = 0)
    (D : X.FSData a) (hD : ∀ t ∈ D.terms, t.2 = 0) {c : ℚ} (hc : 0 < c) (v : X.an) :
    E.eval v ≤ ((c : ℝ) : EReal) * D.eval v ↔
      (E.terms.sup fun s => X.secAbs v.1 E.deg s.1) ^ (c.den * D.m) ≤
        (D.terms.sup fun t => X.secAbs v.1 D.deg t.1) ^ (c.num.toNat * E.m) := by
  have hM : (0 : ℝ) < E.m := by exact_mod_cast E.m_pos
  have hm : (0 : ℝ) < D.m := by exact_mod_cast D.m_pos
  have hq : (0 : ℝ) < c.den := by exact_mod_cast c.den_pos
  have hp : ((c.num.toNat : ℕ) : ℝ) = (c : ℝ) * c.den := by
    have h1 : ((c.num.toNat : ℕ) : ℝ) = (c.num : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hc.le)
    rw [h1, Rat.cast_def]
    field_simp
  have hN : (0 : ℝ) < c.den * D.m * E.m := by positivity
  rw [eval_eq_log_sup_secAbs E hE, eval_eq_log_sup_secAbs D hD, ← mul_assoc, ← EReal.coe_mul,
    ← ENNReal.log_rpow, ← ENNReal.log_rpow, ENNReal.log_le_log_iff,
    ← ENNReal.rpow_le_rpow_iff hN, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  have e1 : (E.m : ℝ)⁻¹ * (c.den * D.m * E.m) = ((c.den * D.m : ℕ) : ℝ) := by
    push_cast
    field_simp
  have e2 : (c : ℝ) * (D.m : ℝ)⁻¹ * (c.den * D.m * E.m) = ((c.num.toNat * E.m : ℕ) : ℝ) := by
    push_cast
    rw [hp]
    field_simp
  rw [e1, e2, ENNReal.rpow_natCast, ENNReal.rpow_natCast, ← ENNReal.coe_pow, ← ENNReal.coe_pow,
    ENNReal.coe_le_coe]

end Multiplicative

/-! ### Points attached to Rees valuations of chart ideals (`lem:nn-rees-points`) -/

section ReesPoints

variable [PerfectField k] {j : X.ChartIndex} {ι : Type*} [Finite ι] (φ : ι → X.chartAlg j)

/-- The normalized blowup charts `E_ℓ` of a finite family in the chart algebra `A_j` are
Noetherian (finiteness of normalization over a perfect field). -/
theorem isNoetherianRing_reesNormalChart_chartAlg (ℓ : ι) :
    IsNoetherianRing (reesNormalChart (FractionRing (X.chartAlg j)) φ ℓ) :=
  isNoetherianRing_reesNormalChart _ φ k ℓ

attribute [local instance] isNoetherianRing_reesNormalChart_chartAlg

/-- A finite family in `A_j` has finitely many Rees valuations. -/
theorem finite_reesIndex_chartAlg : Finite (ReesIndex (FractionRing (X.chartAlg j)) φ) :=
  finite_reesIndex

attribute [local instance] finite_reesIndex_chartAlg

/-- The Rees valuation ring `V` of `(I; φ)`, `I = (φ_i)_i ⊆ A_j`, attached to `x`, as a discrete
valuation ring birational to `A_j`, essentially of finite type over `k` (`def:bj-rees`). -/
def chartReesDVR (x : ReesIndex (FractionRing (X.chartAlg j)) φ) : BirationalDVR k (X.chartAlg j) :=
  haveI := essFiniteType_reesValuationRing k x
  BirationalDVR.ofSubalgebra (reesValuationRing _ _ x)

variable (x : ReesIndex (FractionRing (X.chartAlg j)) φ)

theorem chartReesDVR_ord (y : X.chartAlg j) :
    (chartReesDVR φ x).ord y = addVal (reesValuationRing _ φ x) (algebraMap _ _ y) :=
  rfl

/-- `ord_V(φ_ℓ) > 0` for the chart `ℓ` of `V`. -/
theorem chartReesDVR_ord_idx_pos : 0 < (chartReesDVR φ x).ord (φ x.idx) := by
  rw [chartReesDVR_ord, pos_iff_ne_zero, Ne, addVal_eq_zero_iff]
  exact not_isUnit_algebraMap_idx_reesValuationRing x

/-- `ord_V(φ_ℓ) < ∞`, as `φ_ℓ ≠ 0`. -/
theorem chartReesDVR_ord_idx_ne_top : (chartReesDVR φ x).ord (φ x.idx) ≠ ⊤ :=
  (BirationalDVR.ord_eq_top_iff _).not.2 x.ne_zero

/-- `ord_V(I) = ord_V(φ_ℓ)`: `φ_ℓ` divides every `φ_i` in `V`. -/
theorem chartReesDVR_ord_idx_le (i : ι) :
    (chartReesDVR φ x).ord (φ x.idx) ≤ (chartReesDVR φ x).ord (φ i) := by
  rw [chartReesDVR_ord, chartReesDVR_ord, addVal_le_iff_dvd]
  exact algebraMap_dvd_reesValuationRing x i

/-- `n ord_V(g) ≤ ord_V(h)` means that `g^n` divides `h` in the Rees valuation ring. -/
theorem algebraMap_pow_dvd_of_nsmul_ord_le {g h : X.chartAlg j} {n : ℕ}
    (hle : n • (chartReesDVR φ x).ord g ≤ (chartReesDVR φ x).ord h) :
    algebraMap _ (reesValuationRing (FractionRing (X.chartAlg j)) φ x) g ^ n ∣
      algebraMap _ (reesValuationRing (FractionRing (X.chartAlg j)) φ x) h := by
  rw [← addVal_le_iff_dvd, addVal_pow]
  exact hle

/-- The point `y_V = e^{-ord_V}` of `(Spec A_j)^an` (`lem:nn-rees-points`). -/
def chartReesBerk : Berk k (X.chartAlg j) :=
  (chartReesDVR φ x).berkPoint (expNeg 1) (expNeg_lt_one_of_pos one_pos).le

theorem chartReesBerk_val (y : X.chartAlg j) :
    (chartReesBerk φ x).val y = expOrd (expNeg 1) ((chartReesDVR φ x).ord y) :=
  rfl

theorem chartReesBerk_val_le_one (y : X.chartAlg j) : (chartReesBerk φ x).val y ≤ 1 :=
  BirationalDVR.berkPoint_val_le_one _ _ _

/-- The scales of `y_V` are `μ_c(y_V) = 1`, since `y_V ≤ 1` on `A_j`. -/
theorem chartScale_chartReesBerk (hj : ∀ c, X.coord c (j c) ≠ 0) (c : Fin r) :
    X.chartScale j (chartReesBerk φ x) c = 1 :=
  le_antisymm (Finset.sup_le fun _ _ => chartReesBerk_val_le_one φ x _)
    (one_le_chartScale hj _ c)

/-- **The point `v_V`** (`lem:nn-rees-points`): for a chart `j` with all `f^{(c)}_{j_c} ≠ 0` and a
Rees valuation ring `V` of a finite family in `A_j`, the point `ι_j⁻¹(y_V) ∈ U_j`,
`y_V = e^{-ord_V}`. -/
def chartReesPoint (hj : ∀ c, X.coord c (j c) ≠ 0) : X.an :=
  X.chartInv j hj (chartReesBerk φ x)

variable (hj : ∀ c, X.coord c (j c) ≠ 0)

/-- **`lem:nn-rees-points`**: `|z^{(c)}_{j_c}|_{v_V} = 1` for every `c`. -/
theorem chartReesPoint_val_coordElem (c : Fin r) :
    (chartReesPoint φ x hj).1.val (X.coordElem ⟨c, j c⟩) = 1 := by
  rw [← X.chartMono_single, chartReesPoint, chartInv_val_chartMono, chartScalePow_single,
    chartScale_chartReesBerk φ x hj, inv_one]

theorem chartReesPoint_mem_chartUnitDomain : chartReesPoint φ x hj ∈ X.chartUnitDomain j :=
  chartReesPoint_val_coordElem φ x hj

/-- `|f|_{v_V} = |f / z̃_j^d|_{y_V}` for `f ∈ R_d`. -/
theorem secAbs_chartReesPoint {d : Fin r → ℤ} (f : X.sections d) :
    X.secAbs (chartReesPoint φ x hj).1 d f = (chartReesBerk φ x).val (X.sectionChart hj f) := by
  have h := secAbs_chartInv hj (chartReesBerk φ x) f
  have h1 : ∀ c, (X.chartInv j hj (chartReesBerk φ x)).1.val (X.coordElem ⟨c, j c⟩) = 1 :=
    chartReesPoint_val_coordElem φ x hj
  simp only [h1, one_zpow, Finset.prod_const_one, mul_one] at h
  exact h

/-- **`lem:nn-rees-points`**: `log |f|(v_V) = -ord_V(f / z̃_j^d)` for `f ∈ R_d`, `d ∈ ℤ^r`. -/
theorem logSecAbs_chartReesPoint {d : Fin r → ℤ} (f : X.sections d) :
    X.logSecAbs (chartReesPoint φ x hj).1 d f =
      -(((chartReesDVR φ x).ord (X.sectionChart hj f) : ℝ≥0∞) : EReal) := by
  rw [logSecAbs, secAbs_chartReesPoint, chartReesBerk_val, log_expOrd_expNeg one_pos,
    EReal.coe_one, neg_mul, one_mul]

end ReesPoints

/-! ### Comparison at Rees points (`lem:nn-hom-shilov`) -/

section Shilov

variable {a b : Fin r → ℚ}

/-- The generators `φ^{(j)}_t = f_t / z̃_j^{m a} ∈ A_j` of the chart ideal `I_j` of a Fubini–Study
datum `m⁻¹ max_t (log |f_t| + λ_t)`. -/
def FSData.chartIdealGen (D : X.FSData a) {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0)
    (t : D.terms) : X.chartAlg j :=
  X.sectionChart hj ⟨t.1.1, D.mem_sections t.1 t.2⟩

/-- At a point with `|z^{(c)}_{j_c}|_v = 1`, `max_t |f_t|_v = max_t |φ^{(j)}_t|_{ι_j(v)}`. -/
theorem FSData.sup_secAbs_eq_chartMap (D : X.FSData a) {j : X.ChartIndex}
    (hj : ∀ c, X.coord c (j c) ≠ 0) {v : X.an} (hv1 : ∀ c, v.1.val (X.coordElem ⟨c, j c⟩) = 1) :
    (D.terms.sup fun t => X.secAbs v.1 D.deg t.1) =
      Finset.univ.sup fun t : D.terms =>
        (X.chartMap hj v.1 (val_coordElem_ne_zero_of_eq_one hv1)).val (D.chartIdealGen hj t) := by
  conv_lhs => rw [← Finset.sup_attach]
  rw [Finset.univ_eq_attach]
  exact Finset.sup_congr rfl fun t _ =>
    secAbs_eq_chartMap_of_eq_one hj hv1 ⟨t.1.1, D.mem_sections t.1 t.2⟩

section Rees

variable [PerfectField k]

attribute [local instance] isNoetherianRing_reesNormalChart_chartAlg finite_reesIndex_chartAlg

/-- At the point `v_V` of a Rees valuation of `I_j`, `max_t |f_t|_{v_V} = max_t |φ^{(j)}_t|_{y_V}`. -/
theorem FSData.sup_secAbs_chartReesPoint (D : X.FSData a) {j : X.ChartIndex}
    (hj : ∀ c, X.coord c (j c) ≠ 0) {ι : Type*} [Finite ι] (φ : ι → X.chartAlg j)
    (x : ReesIndex (FractionRing (X.chartAlg j)) φ) :
    (D.terms.sup fun t => X.secAbs (chartReesPoint φ x hj).1 D.deg t.1) =
      Finset.univ.sup fun t : D.terms => (chartReesBerk φ x).val (D.chartIdealGen hj t) := by
  conv_lhs => rw [← Finset.sup_attach]
  rw [Finset.univ_eq_attach]
  exact Finset.sup_congr rfl fun t _ =>
    secAbs_chartReesPoint φ x hj ⟨t.1.1, D.mem_sections t.1 t.2⟩

/-- **`lem:nn-hom-shilov`, first claim**: a homogeneous Fubini–Study function `F = D.eval` takes
values in `(-∞, 0)` at the points `v_V` of the Rees valuations `V` of its chart ideals:
`F(v_V) = -m⁻¹ ord_V(I_j)`. -/
theorem FSData.eval_chartReesPoint_mem_Ioo (D : X.FSData a) (hD : ∀ t ∈ D.terms, t.2 = 0)
    {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0)
    (x : ReesIndex (FractionRing (X.chartAlg j)) (D.chartIdealGen hj)) :
    ⊥ < D.eval (chartReesPoint (D.chartIdealGen hj) x hj) ∧
      D.eval (chartReesPoint (D.chartIdealGen hj) x hj) < 0 := by
  have hq1 : expNeg 1 < 1 := expNeg_lt_one_of_pos one_pos
  -- the value `max_t |φ_t|_{y_V} = |φ_ℓ|_{y_V}` is in `(0, 1)`
  have hsup : (Finset.univ.sup fun t : D.terms =>
      (chartReesBerk (D.chartIdealGen hj) x).val (D.chartIdealGen hj t)) =
      (chartReesBerk (D.chartIdealGen hj) x).val (D.chartIdealGen hj x.idx) :=
    le_antisymm (Finset.sup_le fun t _ => expOrd_antitone hq1.le
      (chartReesDVR_ord_idx_le (D.chartIdealGen hj) x t))
      (Finset.le_sup (f := fun t : D.terms =>
        (chartReesBerk (D.chartIdealGen hj) x).val (D.chartIdealGen hj t)) (Finset.mem_univ _))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (chartReesDVR_ord_idx_ne_top (D.chartIdealGen hj) x)
  have hn1 : 1 ≤ n := by
    have := chartReesDVR_ord_idx_pos (D.chartIdealGen hj) x
    rw [← hn] at this
    exact_mod_cast this
  have hval : (chartReesBerk (D.chartIdealGen hj) x).val (D.chartIdealGen hj x.idx) =
      expNeg 1 ^ n := by
    rw [chartReesBerk_val, ← hn, expOrd_coe]
  have hpos : 0 < expNeg 1 ^ n := pow_pos (zero_lt_expNeg 1) n
  have hlt : expNeg 1 ^ n < 1 := pow_lt_one₀ (zero_lt_expNeg 1).le hq1 (by omega)
  rw [FSData.eval_eq_log_sup_secAbs D hD, FSData.sup_secAbs_chartReesPoint, hsup, hval]
  refine ereal_coe_mul_mem_Ioo_of_pos D.inv_m_pos ?_ ?_
  · rw [Ne, ENNReal.log_eq_bot_iff, ENNReal.coe_eq_zero]
    exact hpos.ne'
  · rw [ENNReal.log_lt_zero_iff, ← ENNReal.coe_one, ENNReal.coe_lt_coe]
    exact hlt

/-- **`lem:nn-hom-shilov`, the condition at `v_V`**: if `G ≤ c F` at the point `v_V` of a Rees
valuation `V` of `I_j` (`G = M⁻¹ max_s log |g_s|`, `F = m⁻¹ max_t log |f_t|`, `c = p / q`), then
`ord_V(h_s) ≥ p M ord_V(I_j)` for `h_s = (g_s / z̃_j^{M b})^{q m}`, in divisibility form. -/
theorem FSData.exists_dvd_of_eval_le_chartReesPoint (D : X.FSData a)
    (hD : ∀ t ∈ D.terms, t.2 = 0) (hDne : D.terms.Nonempty) (E : X.FSData b)
    (hE : ∀ s ∈ E.terms, s.2 = 0) {c : ℚ} (hc : 0 < c) {j : X.ChartIndex}
    (hj : ∀ c, X.coord c (j c) ≠ 0)
    (x : ReesIndex (FractionRing (X.chartAlg j)) (D.chartIdealGen hj))
    (h : E.eval (chartReesPoint (D.chartIdealGen hj) x hj) ≤
      ((c : ℝ) : EReal) * D.eval (chartReesPoint (D.chartIdealGen hj) x hj))
    {s : K × ℝ} (hs : s ∈ E.terms) :
    ∃ i, algebraMap (X.chartAlg j)
        (reesValuationRing (FractionRing (X.chartAlg j)) (D.chartIdealGen hj) x)
        (D.chartIdealGen hj i) ^ (c.num.toNat * E.m) ∣
      algebraMap (X.chartAlg j)
        (reesValuationRing (FractionRing (X.chartAlg j)) (D.chartIdealGen hj) x)
        (X.sectionChart hj ⟨s.1, E.mem_sections s hs⟩ ^ (c.den * D.m)) := by
  rw [FSData.eval_le_mul_eval_iff E hE D hD hc, D.sup_secAbs_chartReesPoint hj _ x] at h
  -- `Finset.le_sup` without a type ascription: unifying an ascribed `≤` (instance
  -- `NNReal.instPartialOrder`) with the lattice `≤` of `Finset.le_sup` times out here
  have h3 := pow_le_pow_left₀ zero_le (Finset.le_sup (f := fun s : K × ℝ =>
    X.secAbs (chartReesPoint (D.chartIdealGen hj) x hj).1 E.deg s.1) hs) (c.den * D.m)
  have h4 : X.secAbs (chartReesPoint (D.chartIdealGen hj) x hj).1 E.deg s.1 =
      (chartReesBerk (D.chartIdealGen hj) x).val
        (X.sectionChart hj ⟨s.1, E.mem_sections s hs⟩) :=
    secAbs_chartReesPoint _ x hj ⟨s.1, E.mem_sections s hs⟩
  have h2 : (chartReesBerk (D.chartIdealGen hj) x).val
      (X.sectionChart hj ⟨s.1, E.mem_sections s hs⟩ ^ (c.den * D.m)) ≤
      (Finset.univ.sup fun t : D.terms =>
        (chartReesBerk (D.chartIdealGen hj) x).val (D.chartIdealGen hj t)) ^
          (c.num.toNat * E.m) := by
    rw [map_pow, ← h4]
    exact le_trans h3 h
  have := hDne.coe_sort
  obtain ⟨i, -, hi⟩ := BirationalDVR.exists_nsmul_ord_le_of_berkPoint_le (chartReesDVR _ x)
    (zero_lt_expNeg 1) (expNeg_lt_one_of_pos one_pos) Finset.univ_nonempty _ h2
  exact ⟨i, algebraMap_pow_dvd_of_nsmul_ord_le _ x hi⟩

/-- **`lem:nn-hom-shilov`, the comparison off the base locus**: let `w ∈ 𝒳^an` with `F(w) > -∞`
and `j` a chart with `|z^{(c)}_{j_c}|_w = 1`. If `G ≤ c F` at the points `v_V` of the Rees
valuations of `I_j`, then `G(w) ≤ c F(w)` (Rees valuations detect integral closure, `thm:bj-rees`,
for the seminorm `ι_j(w) ≤ 1` on `A_j`). -/
theorem FSData.eval_le_mul_eval_of_forall_chartReesPoint (D : X.FSData a)
    (hD : ∀ t ∈ D.terms, t.2 = 0) (E : X.FSData b) (hE : ∀ s ∈ E.terms, s.2 = 0) {c : ℚ}
    (hc : 0 < c) {w : X.an} (hw : D.eval w ≠ ⊥) {j : X.ChartIndex}
    (hj : ∀ c, X.coord c (j c) ≠ 0) (hw1 : ∀ c, w.1.val (X.coordElem ⟨c, j c⟩) = 1)
    (h : ∀ x : ReesIndex (FractionRing (X.chartAlg j)) (D.chartIdealGen hj),
      E.eval (chartReesPoint (D.chartIdealGen hj) x hj) ≤
        ((c : ℝ) : EReal) * D.eval (chartReesPoint (D.chartIdealGen hj) x hj)) :
    E.eval w ≤ ((c : ℝ) : EReal) * D.eval w := by
  obtain ⟨t, ht, hne0⟩ := (D.eval_ne_bot_iff_exists_secAbs_ne_zero w).1 hw
  have hg : ∃ t, (X.chartMap hj w.1 (val_coordElem_ne_zero_of_eq_one hw1)).val
      (D.chartIdealGen hj t) ≠ 0 :=
    ⟨⟨t, ht⟩, fun h0 =>
      hne0 ((secAbs_eq_chartMap_of_eq_one hj hw1 ⟨t.1, D.mem_sections t ht⟩).trans h0)⟩
  rw [FSData.eval_le_mul_eval_iff E hE D hD hc w, D.sup_secAbs_eq_chartMap hj hw1,
    Finset.apply_sup_eq_sup_comp_of_linearOrder (fun y : ℝ≥0 => y ^ (c.den * D.m))
      (pow_left_mono _) (by simp [Nat.mul_ne_zero c.den_ne_zero D.m_pos.ne'])]
  refine Finset.sup_le fun s hs => ?_
  simp only [Function.comp_apply]
  rw [secAbs_eq_chartMap_of_eq_one hj hw1 ⟨s.1, E.mem_sections s hs⟩, ← map_pow]
  exact valuation_le_sup_pow_of_forall_dvd (K := FractionRing (X.chartAlg j))
    (g := D.chartIdealGen hj) _ (chartMap_val_le_one_of_eq_one hj hw1) hg fun x =>
      D.exists_dvd_of_eval_le_chartReesPoint hD ⟨t, ht⟩ E hE hc hj x (h x) hs

end Rees

variable [IsAlgClosed k]

attribute [local instance] isNoetherianRing_reesNormalChart_chartAlg finite_reesIndex_chartAlg

/-- **Homogeneous comparison at finitely many points** (**`lem:nn-hom-shilov`**): for every
`F ∈ 𝓗_hom(𝒳, a)` there is a finite set `Σ_F ⊆ 𝒳^an` with `F(v) ∈ (-∞, 0)` for `v ∈ Σ_F` such that
for every `b ∈ ℚ^r`, every `G ∈ 𝓗_hom(𝒳, b)` and every rational `c > 0`: if `G ≤ c F` on `Σ_F`,
then `G ≤ c F` on `𝒳^an`. `Σ_F` consists of the points `v_V` (`MultiModel.chartReesPoint`) of the
Rees valuations `V` of the chart ideals `I_j = (f_t / z̃_j^{m a})_t` of `F`, over all charts. -/
theorem IsHomFS.exists_finset_le_of_le {F : X.an → EReal} (hF : X.IsHomFS a F) :
    ∃ S : Finset X.an, (∀ v ∈ S, ⊥ < F v ∧ F v < 0) ∧
      ∀ (b : Fin r → ℚ) (G : X.an → EReal) (c : ℚ), 0 < c → X.IsHomFS b G →
        (∀ v ∈ S, G v ≤ ((c : ℝ) : EReal) * F v) → ∀ v, G v ≤ ((c : ℝ) : EReal) * F v := by
  have hFle := hF.le_zero
  obtain ⟨D, hD0, ⟨t₀, ht₀, ht₀0⟩, hFD⟩ := hF
  have hFD' : F = D.eval := funext hFD
  subst hFD'
  have hfin : (⋃ j : X.GoodChart, Set.range fun x => chartReesPoint (D.chartIdealGen j.2) x j.2 :
      Set X.an).Finite :=
    Set.finite_iUnion fun j => Set.finite_range _
  refine ⟨hfin.toFinset, fun v hv => ?_, fun b G c hc hG hS => ?_⟩
  · obtain ⟨j, x, rfl⟩ := Set.mem_iUnion.1 (hfin.mem_toFinset.1 hv)
    exact D.eval_chartReesPoint_mem_Ioo hD0 j.2 x
  have hGpsh := hG.isFS.isPSH
  obtain ⟨E, hE0, -, hGE⟩ := hG
  -- the inequality on `{F > -∞}`
  have key : ∀ w : X.an, D.eval w ≠ ⊥ → G w ≤ ((c : ℝ) : EReal) * D.eval w := by
    intro w hw
    obtain ⟨j, hj, hw1⟩ := X.exists_chartIndex w
    rw [hGE w]
    refine D.eval_le_mul_eval_of_forall_chartReesPoint hD0 E hE0 hc hw hj hw1 fun x => ?_
    rw [← hGE]
    exact hS _ (hfin.mem_toFinset.2 (Set.mem_iUnion.2 ⟨⟨j, hj⟩, x, rfl⟩))
  -- the divisorial comparison theorem
  have hc' : ((c : ℝ)) ≠ 0 := by exact_mod_cast hc.ne'
  refine hGpsh.le_of_forall_isDivisorial_le (h := fun v => ((c : ℝ) : EReal) * D.eval v)
    ((ProjBerk.continuous_ereal_coe_mul hc').comp D.continuous_eval).upperSemicontinuous
    (fun v => ne_top_of_le_ne_top EReal.zero_ne_top ?_) (fun w hw => key w ?_)
  · calc ((c : ℝ) : EReal) * D.eval v ≤ ((c : ℝ) : EReal) * 0 :=
          ProjBerk.ereal_coe_mul_monotone (by exact_mod_cast hc.le) (hFle v)
      _ = 0 := mul_zero _
  · exact (D.eval_ne_bot_iff_exists_secAbs_ne_zero w).2
      ⟨t₀, ht₀, hw.secAbs_ne_zero (D.mem_sections t₀ ht₀) ht₀0⟩

end Shilov

end MultiModel

end EnvelopeProperty
