/-
Copyright (c) 2026. All rights reserved.
-/
import TranscendentalNakamaye.Pending.OhsawaTakegoshiPoint
import TranscendentalNakamaye.Pending.AnalyticSingularities
import EnvelopeProperty.Char0.Weights

/-!
# The Ohsawa–Takegoshi theorem at a point (adapter to TranscendentalNakamaye)

This file proves `lem:c0-ot-point` of the characteristic-zero blueprint
(`EnvelopeProperty/blueprint/src/char0.tex`) from the pinned dependency TranscendentalNakamaye
(TN, see `deps/TN-PIN.md`):

* `exists_extension_from_point_ball`: for every `r > 0` there is `C_r > 0` such that for every
  `y ∈ ℂ^N`, every plurisubharmonic `ψ` on `B(y, r)` (TN's `PlurisubharmonicOn`, extended real
  valued) and every `c > 0` there is `f` holomorphic on `B(y, r)` with `f y = 1` and
  `∫_{B(y,r)} |f|² e^{-cψ} ≤ C_r e^{-cψ(y)}` (TN's `multiplierWeight c (ψ z) = e^{-cψ(z)}`).
  It is TN's `OhsawaTakegoshiPoint.exists_extension_from_zero` on `B(0, r)`, translated to `y`
  (so that `C_r` does not depend on `y`).

TN states its integrals for the Borel σ-algebra `borel (ComplexModel N)`, which is
propositionally (not definitionally) equal to Mathlib's instance on `EuclideanSpace ℂ (Fin N)`;
`setLIntegral_borel_eq` transports them.

We also record the plurisubharmonicity of `c log ∑_j |g_j|²` for a finite family of polynomials
(`plurisubharmonicOn_mul_generatorLog`) and the value of the corresponding TN weight
(`multiplierWeight_one_mul_generatorLog`), which is how `lem:c0-ot-point` is applied in
`prop:c0-l2-extension`.
-/

open scoped NNReal ENNReal Topology
open MeasureTheory Metric Set

noncomputable section

namespace EnvelopeProperty.Char0

open TranscendentalNakamaye TranscendentalNakamaye.FirstPass

variable {N : ℕ}

/-- TN's set integrals for the Borel σ-algebra agree with Mathlib's on `ComplexModel N`. -/
theorem setLIntegral_borel_eq (s : Set (ComplexModel N)) (F : ComplexModel N → ℝ≥0∞) :
    (letI : MeasurableSpace (ComplexModel N) := borel _
     letI : BorelSpace (ComplexModel N) := ⟨rfl⟩
     ∫⁻ z in s, F z) = ∫⁻ z in s, F z := by
  have key : ∀ (m : MeasurableSpace (ComplexModel N)) [hb : @BorelSpace _ _ m],
      (∫⁻ z in s, F z) = (letI : MeasurableSpace (ComplexModel N) := borel _
        letI : BorelSpace (ComplexModel N) := ⟨rfl⟩
        ∫⁻ z in s, F z) := by
    intro m hb
    obtain rfl : m = borel _ := hb.measurable_eq
    rfl
  exact (key _).symm

/-- **The Ohsawa–Takegoshi theorem at a point** (`lem:c0-ot-point`). For every `r > 0` there is
`C_r > 0` such that for every `y ∈ ℂ^N`, every plurisubharmonic `ψ` on `B(y, r)` and every `c > 0`
there is `f` holomorphic on `B(y, r)` with `f y = 1` and
`∫_{B(y,r)} |f|² e^{-cψ} dλ ≤ C_r e^{-cψ(y)}`. -/
theorem exists_extension_from_point_ball {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ComplexModel N) (ψ : ComplexModel N → EReal),
      PlurisubharmonicOn ψ (ball y r) → ∀ c : ℝ, 0 < c →
      ∃ f : ComplexModel N → ℂ, DifferentiableOn ℂ f (ball y r) ∧ f y = 1 ∧
        ∫⁻ z in ball y r, ENNReal.ofReal (‖f z‖ ^ 2) * multiplierWeight c (ψ z) ≤
          ENNReal.ofReal C * multiplierWeight c (ψ y) := by
  obtain ⟨C, hC, h0⟩ := Pending.OhsawaTakegoshiPoint.exists_extension_from_zero N r hr
  refine ⟨C, hC, fun y ψ hψ c hc => ?_⟩
  have hψ' : PlurisubharmonicOn (fun x => ψ (x + y)) (ball 0 r) :=
    Pending.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic isOpen_ball
      ((differentiable_id.add_const y).differentiableOn) (fun x hx => by
        simpa [mem_ball, dist_eq_norm] using hx) hψ
  obtain ⟨F, hFhol, hF0, hFint⟩ := h0 (ball 0 r) isOpen_ball (convex_ball 0 r)
    (fun z hz => by simpa using hz) _ hψ' c hc (mem_ball_self hr)
  rw [setLIntegral_borel_eq] at hFint
  refine ⟨fun x => F (x - y), ?_, by simpa using hF0, ?_⟩
  · refine hFhol.comp (differentiable_id.sub_const y).differentiableOn fun x hx => ?_
    simpa [mem_ball, dist_eq_norm] using hx
  · have hmp : MeasurePreserving (fun x : ComplexModel N => x + y) volume volume :=
      measurePreserving_add_right volume y
    have hpre : (fun x : ComplexModel N => x + y) ⁻¹' ball y r = ball 0 r := by
      ext x; simp [mem_ball, dist_eq_norm]
    have htrans : (∫⁻ z in ball y r, ENNReal.ofReal (‖F (z - y)‖ ^ 2) * multiplierWeight c (ψ z))
        = ∫⁻ x in ball 0 r, multiplierDensity (fun x => ψ (x + y)) c F x := by
      rw [← hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight y), hpre]
      simp only [multiplierDensity, add_sub_cancel_right]
    rw [htrans]
    simpa using hFint

/-- The extended logarithm `log ∑_j |h_j|²` of a finite family of functions (value `-∞` on the
common zero set), i.e. `2 log |h|` in the notation of `conv:c0`. -/
def logNormSqFam {ι : Type*} [Fintype ι] (h : ι → ComplexModel N → ℂ) (z : ComplexModel N) :
    EReal :=
  ENNReal.log (ENNReal.ofReal (∑ j, ‖h j z‖ ^ 2))

/-- **`lem:c0-weight` (1) in TN's sense**: for a finite family of entire functions `h_j` and
`c > 0`, `c log ∑_j |h_j|²` is plurisubharmonic on `ℂ^N` (TN's `PlurisubharmonicOn`). -/
theorem plurisubharmonicOn_mul_logNormSqFam {ι : Type*} [Fintype ι]
    {h : ι → ComplexModel N → ℂ} (hh : ∀ j, Differentiable ℂ (h j)) {c : ℝ} (hc : 0 < c) :
    PlurisubharmonicOn (fun z => (c : EReal) * logNormSqFam h z) univ := by
  classical
  set e := Fintype.equivFin ι
  set f : Fin (Fintype.card ι) → ComplexModel N → ℂ := fun i => h (e.symm i) with hf
  have heq : (fun z => (c : EReal) * logNormSqFam h z) =
      fun z => (c : EReal) * generatorLog f z := by
    funext z
    rw [generatorLog, logNormSqFam, logNormSq, generatorVector_norm_sq, generatorNormSq]
    congr 3
    exact (e.symm.sum_comp fun j => ‖h j z‖ ^ 2).symm
  rw [heq]
  intro x _
  exact Pending.plurisubharmonicAt_scaled_generatorLog
    ⟨univ, isOpen_univ, mem_univ x, fun j => (hh _).differentiableOn⟩ hc

/-- Off the zero set, TN's weight `e^{-c log S}` is `S^{-c}`. -/
theorem multiplierWeight_log_ofReal {S : ℝ} (hS : 0 < S) (c : ℝ) :
    multiplierWeight c (ENNReal.log (ENNReal.ofReal S)) = ENNReal.ofReal (S ^ (-c)) := by
  rw [ENNReal.log_ofReal_of_pos hS, multiplierWeight_coe, Real.rpow_def_of_pos hS]
  congr 2
  ring

/-- TN's weight `e^{-c log S}` dominates the real weight `S^{-c}` (which is `0` at `S = 0`). -/
theorem ofReal_rpow_neg_le_multiplierWeight {S : ℝ} (hS : 0 ≤ S) {c : ℝ} (hc : 0 < c) :
    ENNReal.ofReal (S ^ (-c)) ≤ multiplierWeight c (ENNReal.log (ENNReal.ofReal S)) := by
  rcases hS.lt_or_eq with hS | rfl
  · rw [multiplierWeight_log_ofReal hS]
  · rw [Real.zero_rpow (by linarith), ENNReal.ofReal_zero]
    exact zero_le

end EnvelopeProperty.Char0
