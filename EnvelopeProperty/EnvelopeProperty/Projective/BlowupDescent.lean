/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.BlowupDescentCharts
import EnvelopeProperty.Local.LocalRegularizationFinal
import EnvelopeProperty.Local.LocalRegularizationPositivity
import EnvelopeProperty.Local.ProjectionChartRegularizable
import EnvelopeProperty.Local.NonflatNorm

/-!
# Psh descent along blowups (FHX Corollary 5.26)

This file proves Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX),
Corollary 5.26 (`cor:normal-weak-global`) in the model of the blueprint chapter
`projective-general.tex`: the node `thm:pg-psh-descent` (see `rmk:pg-psh-descent-source` for the
comparison with the source). Let `k` be a countable algebraically closed field (trivially valued),
`X = V(I) ⊆ ℙ^M` projectively normal (`ProjSubvariety.IsProjNormal`), `μ : X' → X` the blowup of
`X` along forms `G₀, …, G_{M'}` of one degree (`B : X.BlowupCenter M'`, `μ = B.proj`), `a ∈ ℚ_{>0}`
and `φ : X^an → [-∞, ∞)`. If `φ ∘ μ ∈ PSH(X', (a, 0)) = PSH(X', μ^*O(a))`, then `φ ∈ PSH(X, a)`
(`ProjSubvariety.isPSH_of_isPSH_comp_proj`).

## The proof (`thm:pg-psh-descent`)

* *Bounds*: by the maximum principle on `X'` and `μ(⋆') = ⋆`, `φ ∘ μ ≤ φ(⋆) ∈ ℝ`; since `μ` is
  surjective, `φ ≤ φ(⋆)`.
* *Regularizability on the charts*: for `x_i ∉ I`, the function `u_i = (φ - a log|x_i|) ∘ ι_i⁻¹`
  (`ProjSubvariety.descentChartFun`) on the normal affine chart `Y_i = Spec A_i`
  (`lem:pg-chart-normal`) is chart-regularizable (`lem:nf-descent-chart`, refining
  `lem:pg-descent-weakly-psh`), of logarithmic growth
  (`u_i ≤ -a log|x_i| + φ(⋆)`, an FS function plus a constant), and regularizable on the principal
  opens `(Y_i)_g`, `g ∈ 𝔞_i \ {0}`, which cover `Y_i^an \ V(𝔞_i)^an` (`lem:pg-descent-cover`). By
  FHX Theorem 5.25 for chart-regularizable functions
  (`IsRegularizable.of_isChartRegularizable_of_convexPLApproximation`), `u_i ∈ ℛ(Y_i)`.
* *Extension*: for rational `a' > a`, the compactification lemma `lem:pg-compactification-extend`
  (`ProjSubvariety.isPSH_chartExt`, `σ = x_i`, `e = 1`, `κ = a`) shows that the function equal to
  `u_i ∘ ι_i + a' log|x_i| = φ + (a' - a) log|x_i|` on `U_{x_i} ∩ X^an` and to `-∞` elsewhere is
  in `PSH(X, a')`. These functions are `≤ φ`, with equality where `|x_i| = 1`, so `φ` is their
  maximum over the `i` with `x_i ∉ I` and lies in `PSH(X, a')`.
* *Conclusion*: PSH2 (`ProjSubvariety.isPSH_of_antitone_seq`) for the constant sequence `φ` with
  the classes `a + 1/(n+1) → a`.

## Trust boundary

The theorem is conditional on exactly the imported statements of FHX Theorem 5.25:
`ConvexPLApproximation` (equivalent to `WuRegularization`, FHX Lemma 5.11(5),(6)) or the stronger
`LocalPositivity` (FHX Lemma 5.5, which implies it), explicit instance arguments, not axioms.
FHX Proposition 5.22 is not assumed: the form needed here (for functions regularizable on the charts
of a blowup) is a theorem, the instance `ChartNonflatNorms.of_wuRegularization`
(`Local/NonflatNorm.lean`, lanes NF1–NF7, without Gubler–Rabinoff potential theory). The variant
`ProjSubvariety.isPSH_of_isPSH_comp_proj_of_convexPLApproximation` assumes
`ConvexPLApproximation`.

## Deviations from the blueprint

* The class `a` is not rescaled to `1`: the chart functions are `φ - a log|x_i|` and the extension
  classes are `a' > a`.
* The blowup `X'` is not assumed normal (as in the blueprint; FHX states 5.26 for normal `X'`).
* For the chart lemmas see `EnvelopeProperty.Projective.BlowupDescentCharts`.
-/

open scoped NNReal ENNReal Topology

open Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

open ProjBerk (QuotChartAlg)

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} {V : ProjSubvariety k M}

/-- The extension of `u_i` from the chart: `chartExt (u_i) a' = φ + (a' - a) log|x_i|` on
`U_{x_i} ∩ X^an`. -/
theorem chartExt_descentChartFun (i : Fin (M + 1)) (a a' : ℝ) (φ : V.an → EReal) {x : V.an}
    (hx : (x : ProjBerk k M).1.val (MvPolynomial.X i) ≠ 0) :
    V.chartExt (MvPolynomial.X i) 1 (V.descentChartFun i a φ) a' x =
      φ x + (((a' - a) * Real.log ((x : ProjBerk k M).1.val (MvPolynomial.X i) : ℝ) : ℝ) :
        EReal) := by
  rw [chartExt_of_ne_zero _ _ hx, descentChartFun_chartMap, ProjBerk.logAbs_eq_coe_log hx,
    ← EReal.coe_mul, add_assoc, ← EReal.coe_add]
  congr 2
  ring

/-- `chartExt (u_i) a' ≤ φ` for `a ≤ a'`, since `log|x_i| ≤ 0` on `X^an`. -/
theorem chartExt_descentChartFun_le (i : Fin (M + 1)) {a a' : ℝ} (haa' : a ≤ a')
    (φ : V.an → EReal) (x : V.an) :
    V.chartExt (MvPolynomial.X i) 1 (V.descentChartFun i a φ) a' x ≤ φ x := by
  by_cases hx : (x : ProjBerk k M).1.val (MvPolynomial.X i) = 0
  · rw [chartExt_of_eq_zero _ _ hx]
    exact bot_le
  · rw [chartExt_descentChartFun i a a' φ hx]
    have hl := ProjBerk.real_log_val_le_zero (MvPolynomial.X i) (x : ProjBerk k M)
    have h0 : (a' - a) * Real.log ((x : ProjBerk k M).1.val (MvPolynomial.X i) : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 haa') hl
    calc φ x + (((a' - a) * Real.log ((x : ProjBerk k M).1.val (MvPolynomial.X i) : ℝ) : ℝ) :
          EReal) ≤ φ x + 0 := add_le_add_right (by exact_mod_cast h0) _
      _ = φ x := add_zero _

/-- `chartExt (u_i) a' = φ` at the points where `|x_i| = 1`. -/
theorem chartExt_descentChartFun_of_val_eq_one (i : Fin (M + 1)) (a a' : ℝ) (φ : V.an → EReal)
    {x : V.an} (hx : (x : ProjBerk k M).1.val (MvPolynomial.X i) = 1) :
    V.chartExt (MvPolynomial.X i) 1 (V.descentChartFun i a φ) a' x = φ x := by
  rw [chartExt_descentChartFun i a a' φ (by rw [hx]; exact one_ne_zero), hx, NNReal.coe_one,
    Real.log_one, mul_zero, EReal.coe_zero, add_zero]

/-- **Psh descent along blowups** (`thm:pg-psh-descent`, FHX Corollary 5.26
`cor:normal-weak-global` in the model of `projective-general.tex`), conditional on
`ConvexPLApproximation` only (FHX Prop 5.22 for chart-regularizable functions is the instance
`ChartNonflatNorms.of_wuRegularization`). Let `k` be countable and
algebraically closed, `X = V(I) ⊆ ℙ^M` projectively normal, `μ : X' → X` the blowup along forms
`G₀, …, G_{M'}` of one degree (`B : X.BlowupCenter M'`), `a ∈ ℚ_{>0}` and `φ : X^an → [-∞, ∞)`.
If `φ ∘ μ ∈ PSH(X', (a, 0)) = PSH(X', μ^*O(a))`, then `φ ∈ PSH(X, a)`. -/
theorem isPSH_of_isPSH_comp_proj_of_convexPLApproximation {k : Type u} [Field k] [IsAlgClosed k]
    [Countable k] [ConvexPLApproximation.{u, u} k] {M M' : ℕ}
    (X : ProjSubvariety k M) (hX : X.IsProjNormal) (B : X.BlowupCenter M') {a : ℚ} (ha : 0 < a)
    {φ : X.an → EReal} (h : B.IsPSH ![(a : ℝ), 0] (φ ∘ B.proj)) : X.IsPSH a φ := by
  -- Bounds: `φ ∘ μ ≤ (φ ∘ μ)(⋆') = φ(⋆) ∈ ℝ` and `μ` is surjective.
  have htriv : φ X.triv ≠ ⊥ := by
    have h1 := h.apply_triv_ne_bot
    rwa [Function.comp_apply, B.proj_triv] at h1
  have htop : φ X.triv ≠ ⊤ := by
    have h1 := FSSystem.IsPSH.apply_triv_ne_top h
    rwa [BlowupCenter.fsSystem_triv, Function.comp_apply, B.proj_triv] at h1
  have hle : ∀ x, φ x ≤ ((φ X.triv).toReal : EReal) := by
    intro x
    obtain ⟨v, rfl⟩ := B.proj_surjective x
    rw [EReal.coe_toReal htop htriv]
    have h1 := h.le_apply_triv v
    rwa [Function.comp_apply, Function.comp_apply, B.proj_triv] at h1
  -- Extension: `φ ∈ PSH(X, a')` for every rational `a' > a`.
  have hext : ∀ a' : ℚ, a < a' → X.IsPSH a' φ := by
    intro a' haa'
    classical
    let S := Finset.univ.filter fun i : Fin (M + 1) =>
      (MvPolynomial.X i : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal
    have hS : S.Nonempty := by
      obtain ⟨i, hi⟩ := X.exists_X_notMem
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩
    have hψ : ∀ i ∈ S, X.IsPSH a'
        (X.chartExt (MvPolynomial.X i) 1 (X.descentChartFun i a φ) a') := by
      intro i hi
      have hi' := (Finset.mem_filter.1 hi).2
      obtain ⟨hdom, hft, hic⟩ :=
        isIntegrallyClosed_quotChartAlg_and hX (MvPolynomial.isHomogeneous_X k i) hi'
      -- `u_i` is chart-regularizable, of logarithmic growth, and regularizable off `V(𝔞_i)`
      have hwpsh := B.isChartRegularizable_descentChartFun i h
      have hlog : HasLogGrowth (X.descentChartFun i a φ) :=
        ⟨X.growthFSData (MvPolynomial.isHomogeneous_X k i) ha, (φ X.triv).toReal, fun y => by
          rw [descentChartFun, eval_growthFSData (MvPolynomial.isHomogeneous_X k i) one_pos ha,
            add_comm]
          exact add_le_add_right (hle _) _⟩
      have hcover : ∀ y : Berk k (QuotChartAlg X.ideal (MvPolynomial.X i) 1),
          (∃ f ∈ B.centerSet i, y.val f ≠ 0) → ∃ g : QuotChartAlg X.ideal (MvPolynomial.X i) 1,
            g ≠ 0 ∧ y.val g ≠ 0 ∧
              IsRegularizable fun z => X.descentChartFun i a φ (Berk.awayComap g z) := by
        rintro y ⟨f, hf, hyf⟩
        have hf0 : f ≠ 0 := fun h0 => hyf (by rw [h0, map_zero])
        exact ⟨f, hf0, hyf, B.isRegularizable_descentChartFun_awayComap i h hf hf0⟩
      -- Theorem 5.25
      have hreg := IsRegularizable.of_isChartRegularizable_of_convexPLApproximation (B.centerSet i)
        (B.exists_mem_centerSet_ne_zero i) hwpsh hlog hcover
      -- Lemma 5.10(2) on `X` (`lem:pg-compactification-extend`, `σ = x_i`, `e = 1`, `κ = a`)
      have hwB : ∀ y, X.descentChartFun i a φ y ≤
          -((a : ℝ) : EReal) * ProjBerk.logAbs (MvPolynomial.X i)
            (X.chartInv (MvPolynomial.X i) 1 (MvPolynomial.isHomogeneous_X k i) one_pos y).1 +
            (((φ X.triv).toReal : ℝ) : EReal) := fun y => by
        rw [descentChartFun, add_comm]
        exact add_le_add_right (hle _) _
      have h1 := isPSH_chartExt hX (MvPolynomial.isHomogeneous_X k i) one_pos hi' hreg ha hwB
        haa'
      rwa [Nat.cast_one, mul_one] at h1
    have hsup := FSSystem.isPSH_finset_sup' (F := X.fsSystem) hS hψ
    have heq : (fun x => S.sup' hS fun i =>
        X.chartExt (MvPolynomial.X i) 1 (X.descentChartFun i a φ) a' x) = φ := by
      funext x
      refine le_antisymm (Finset.sup'_le _ _ fun i _ =>
        chartExt_descentChartFun_le i (by exact_mod_cast haa'.le) φ x) ?_
      obtain ⟨i, hi⟩ := (x : ProjBerk k M).exists_val_X_eq_one
      have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i,
        notMem_ideal_of_val_ne_zero (v := x) (by rw [hi]; exact one_ne_zero)⟩
      exact (chartExt_descentChartFun_of_val_eq_one i a a' φ hi).symm.le.trans
        (Finset.le_sup' (fun i => X.chartExt (MvPolynomial.X i) 1 (X.descentChartFun i a φ) a' x)
          hiS)
    rw [heq] at hsup
    exact hsup
  -- Conclusion: PSH2 with the constant sequence `φ` and the classes `a + 1/(n+1) → a`.
  refine isPSH_of_antitone_seq (θ := fun n : ℕ => ((a + 1 / ((n : ℚ) + 1) : ℚ) : ℝ))
    ?_ (fun n => hext _ (lt_add_of_pos_right _ Nat.one_div_pos_of_nat)) (fun _ => antitone_const)
    (fun _ => iInf_const.symm) ⟨X.triv, htriv⟩
  have h1 := (tendsto_const_nhds (x := (a : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at h1
  push_cast
  exact h1

/-- **Psh descent along blowups** (`thm:pg-psh-descent`, FHX Corollary 5.26
`cor:normal-weak-global` in the model of `projective-general.tex`), conditional on FHX Lemma 5.5
(`LocalPositivity`) only (FHX Proposition 5.22 for chart-regularizable functions is a theorem), as
FHX Theorem 5.25 in
`IsRegularizable.of_isChartRegularizable_of_localPositivity`. Let `k` be countable and algebraically
closed, `X = V(I) ⊆ ℙ^M` projectively normal, `μ : X' → X` the blowup along forms
`G₀, …, G_{M'}` of one degree, `a ∈ ℚ_{>0}` and `φ : X^an → [-∞, ∞)`. If
`φ ∘ μ ∈ PSH(X', (a, 0)) = PSH(X', μ^*O(a))`, then `φ ∈ PSH(X, a)`. -/
theorem isPSH_of_isPSH_comp_proj {k : Type u} [Field k] [IsAlgClosed k] [Countable k]
    [LocalPositivity.{u} k] {M M' : ℕ} (X : ProjSubvariety k M)
    (hX : X.IsProjNormal) (B : X.BlowupCenter M') {a : ℚ} (ha : 0 < a) {φ : X.an → EReal}
    (h : B.IsPSH ![(a : ℝ), 0] (φ ∘ B.proj)) : X.IsPSH a φ :=
  isPSH_of_isPSH_comp_proj_of_convexPLApproximation X hX B ha h

end ProjSubvariety

end EnvelopeProperty
