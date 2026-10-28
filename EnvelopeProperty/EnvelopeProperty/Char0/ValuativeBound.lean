/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.AnalyticChart
import EnvelopeProperty.Char0.L2Extension

/-!
# The valuative bound for square integrable polynomials (`prop:c0-valuative-bound`)

Let `V` be a divisorial valuation ring over `ℂ` in `N = n + 1` variables, with coordinates
`(π, u)` and log discrepancy `A(V) = 1 + ord_V(Jac_V)` (`lem:c0-dvr-jacobian`). Let
`g = (g_j)` be polynomials, not all zero, `c > 0`, and `f` a polynomial which is square integrable
against `|g|^{-2c}` on compact sets. This file proves the blueprint proposition
`prop:c0-valuative-bound` (`EnvelopeProperty/blueprint/src/char0.tex`):
`ord_V(f) > c ord_V(g) - A(V)` (`valuativeBound_of_coordinates`).

## Proof

Apply `lem:c0-analytic-chart` (`exists_analyticChart`) to `f` and the nonzero `g_j`, and shrink the
polydisc so that the functions `h` are bounded above and below. With `a = ord_V f`,
`b ≤ ord_V g_j`, `α = A(V) - 1` and `s` the coordinate of `π`: on `U_* = U ∩ {s ≠ 0}`,
`|f ∘ μ|² ≥ c₁ |s|^{2a}`, `0 < |g ∘ μ|² ≤ C₂ |s|^{2b}`, and the real Jacobian of the holomorphic
map `μ` is `|det Dμ|² ≥ c₃ |s|^{2α}` (`det_restrictScalars_real`). The change of variables
formula and the hypothesis on a ball containing `μ(U)` give
`∞ > ∫_{μ(U_*)} |f|²|g|^{-2c} ≥ c₁ c₃ C₂^{-c} ∫_{U_*} |s|^{2(a - cb + α)}`, and by Fubini and polar
coordinates in `s` (`integrableOn_ball_norm_rpow_iff`, `lem:c0-analytic-basics` (3), proved in
`EnvelopeProperty.Char0.L2Extension`) the last integral is finite only if `a - cb + α > -1`
(`neg_one_lt_of_setLIntegral_rpow_lt_top`).

## Conventions

`|g|^{-2c}` is the real power `(∑_j |g_j|²)^{-c}` (which is `0` on `Z(g)`), as in
`EnvelopeProperty.Char0.IsSqIntegrableAgainst`.
-/

noncomputable section

open scoped NNReal ENNReal Topology

open MvPolynomial Filter MeasureTheory Metric Set IsLocalRing

namespace EnvelopeProperty.Char0

/-! ### Real Jacobians of holomorphic maps -/

/-- The real determinant of a `ℂ`-linear map of `ℂᵐ` is `|det_ℂ|²`. -/
theorem det_restrictScalars_real {m : ℕ} (L : (Fin m → ℂ) →L[ℂ] Fin m → ℂ) :
    (L.restrictScalars ℝ).det = ‖L.det‖ ^ 2 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.det]
  change LinearMap.det ((L : (Fin m → ℂ) →ₗ[ℂ] Fin m → ℂ).restrictScalars ℝ) = _
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

/-! ### Bounds on compact sets -/

theorem exists_pos_le_norm_of_continuousOn {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {φ : X → ℂ} (hφ : ContinuousOn φ K) (h0 : ∀ x ∈ K, φ x ≠ 0) :
    ∃ c > 0, ∀ x ∈ K, c ≤ ‖φ x‖ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun x hx => absurd hx (Set.notMem_empty x)⟩
  obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne hφ.norm
  exact ⟨‖φ x0‖, norm_pos_iff.2 (h0 x0 hx0), fun x hx => hmin hx⟩

/-! ### Polar coordinates in one variable and Fubini -/

/-- **The integrability criterion in the coordinate `s`**: if
`∫_{B(p₀, δ) ∩ {s ≠ 0}} |s|^{2κ} dλ < ∞` for a coordinate `s = p_{s₀}` with `p₀(s₀) = 0`, then
`κ > -1` (Fubini and `lem:c0-analytic-basics` (3)). -/
theorem neg_one_lt_of_setLIntegral_rpow_lt_top {n : ℕ} (s0 : Fin (n + 1)) {p0 : Fin (n + 1) → ℂ}
    (hp0 : p0 s0 = 0) {δ : ℝ} (hδ : 0 < δ) {κ : ℝ}
    (h : ∫⁻ p in ball p0 δ ∩ {p | p s0 ≠ 0}, ENNReal.ofReal (‖p s0‖ ^ (2 * κ)) < ⊤) :
    -1 < κ := by
  set E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) s0
  have hE : MeasurePreserving E volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) s0
  set B1 : Set ℂ := ball 0 δ \ {0}
  set B2 : Set (Fin n → ℂ) := ball (fun i => p0 (s0.succAbove i)) δ
  set φ : ℂ → ℝ≥0∞ := fun s => ENNReal.ofReal (‖s‖ ^ (2 * κ))
  have hsub : E ⁻¹' (B1 ×ˢ B2) ⊆ ball p0 δ ∩ {p | p s0 ≠ 0} := by
    rintro p ⟨⟨hp1, hp1'⟩, hp2⟩
    simp only [E, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
      mem_ball, dist_zero_right] at hp1 hp1' hp2
    refine ⟨?_, hp1'⟩
    rw [mem_ball, dist_pi_lt_iff hδ]
    intro k
    rcases Fin.eq_self_or_eq_succAbove s0 k with rfl | ⟨i, rfl⟩
    · rw [hp0, dist_zero_right]
      exact hp1
    · rw [mem_ball, dist_pi_lt_iff hδ] at hp2
      exact hp2 i
  have h1 : ∫⁻ p in E ⁻¹' (B1 ×ˢ B2), φ (p s0) < ⊤ :=
    (lintegral_mono_set hsub).trans_lt h
  have h2 : ∫⁻ p in E ⁻¹' (B1 ×ˢ B2), φ (p s0) = (∫⁻ s in B1, φ s) * volume B2 := by
    have := hE.setLIntegral_comp_preimage_emb E.measurableEmbedding (fun q => φ q.1) (B1 ×ˢ B2)
    rw [show (∫⁻ p in E ⁻¹' (B1 ×ˢ B2), φ (p s0)) =
      ∫⁻ a in E ⁻¹' (B1 ×ˢ B2), (fun q : ℂ × (Fin n → ℂ) => φ q.1) (E a) from rfl, this,
      Measure.volume_eq_prod, setLIntegral_prod]
    · simp only [setLIntegral_const]
      rw [lintegral_mul_const']
      exact (measure_ball_lt_top).ne
    · exact (measurable_fst.norm.pow_const _ |>.ennreal_ofReal).aemeasurable
  rw [h2] at h1
  have hB2 : volume B2 ≠ 0 := (measure_ball_pos volume _ hδ).ne'
  have h3 : ∫⁻ s in B1, φ s < ⊤ := by
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc, ENNReal.top_mul hB2] at h1
    exact lt_irrefl _ h1
  have h4 : IntegrableOn (fun s : ℂ => ‖s‖ ^ (2 * κ)) B1 := by
    refine ⟨(continuous_norm.measurable.pow_const _).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun s => ?_)) h3
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (norm_nonneg s) _)]
  have h5 : IntegrableOn (fun s : ℂ => ‖s‖ ^ (2 * κ)) (ball 0 δ) := by
    have hae : B1 =ᵐ[volume] ball (0 : ℂ) δ := sdiff_null_ae_eq_self (measure_singleton 0)
    exact (integrableOn_congr_set_ae hae).1 h4
  exact (integrableOn_ball_norm_rpow_iff hδ κ).1 h5

/-! ### The valuative bound -/

section Bound

variable {n : ℕ} (V : BirationalDVR ℂ (MvPolynomial (Fin (n + 1)) ℂ)) {ι' : Type*} [Fintype ι']
  [DecidableEq ι'] {π : V.ring} {u : ι' → V.ring}

theorem logDiscrepancy_toNat_eq (hπ : Irreducible π)
    (hu : IsTranscendenceBasis ℂ (residue V.ring ∘ u)) (e : Option ι' ≃ Fin (n + 1)) :
    (logDiscrepancy hπ hu (z := fun o => algebraMap (MvPolynomial (Fin (n + 1)) ℂ)
        (FractionRing (MvPolynomial (Fin (n + 1)) ℂ)) (X (e o)))
        (fun o => V.algebraMap_mem (X (e o)))).toNat =
      (logDiscrepancy hπ hu (z := fun o => algebraMap (MvPolynomial (Fin (n + 1)) ℂ)
        (FractionRing (MvPolynomial (Fin (n + 1)) ℂ)) (X (e o)))
        (fun o => V.algebraMap_mem (X (e o))) - 1).toNat + 1 := by
  have hA := BirationalDVR.logDiscrepancy_ne_top V hπ hu e
  rw [logDiscrepancy] at hA ⊢
  generalize IsDiscreteValuationRing.addVal V.ring _ = a at hA ⊢
  induction a using ENat.recTopCoe with
  | top => simp at hA
  | coe k =>
    norm_cast
    simp [add_comm]

/-- **The valuative bound** (`prop:c0-valuative-bound`). Let `V` be a divisorial valuation ring
over `ℂ` in `n + 1` variables with coordinates `(π, u)` indexed by `e`, and `A(V)` its log
discrepancy (`lem:c0-dvr-jacobian`). If `g = (g_j)` is not identically zero, `c > 0`, `f ≠ 0`,
`∫_K |f|² |g|^{-2c} dλ < ∞` for every compact `K`, and `b ≤ ord_V(g_j)` for all `j`, then
`c b < ord_V(f) + A(V)`. -/
theorem valuativeBound_of_coordinates (hπ : Irreducible π)
    (hu : IsTranscendenceBasis ℂ (residue V.ring ∘ u)) (e : Option ι' ≃ Fin (n + 1))
    {ι : Type*} [Fintype ι] (g : ι → MvPolynomial (Fin (n + 1)) ℂ) (hg : ∃ j, g j ≠ 0) {c : ℝ}
    (hc : 0 < c) {f : MvPolynomial (Fin (n + 1)) ℂ} (hf : f ≠ 0)
    (hfg : ∀ K : Set (Fin (n + 1) → ℂ), IsCompact K →
      ∫⁻ z in K, ENNReal.ofReal ((∑ j, ‖eval z (g j)‖ ^ 2) ^ (-c)) * ‖eval z f‖ₑ ^ 2 < ⊤)
    {b : ℕ} (hb : ∀ j, (b : ℕ∞) ≤ V.ord (g j)) :
    c * b < (V.ord f).toNat + (logDiscrepancy hπ hu (z := fun o =>
      algebraMap (MvPolynomial (Fin (n + 1)) ℂ) (FractionRing (MvPolynomial (Fin (n + 1)) ℂ))
        (X (e o))) (fun o => V.algebraMap_mem (X (e o)))).toNat := by
  classical
  set s0 := e none
  obtain ⟨j0, hj0⟩ := hg
  let J := {j // g j ≠ 0}
  let F : Option J → MvPolynomial (Fin (n + 1)) ℂ := fun o => o.elim f fun j => g j.1
  have hF : ∀ o, F o ≠ 0 := by
    rintro (_ | ⟨j, hj⟩)
    · exact hf
    · exact hj
  obtain ⟨p0, δ, μ, μ', h, h0, hp0, hδ, hδ1, hμ, hbdd, hhd, hhf, hh0d, hh0, hinj⟩ :=
    exists_analyticChart V hπ hu e F hF
  set a := (V.ord f).toNat
  set α := (logDiscrepancy hπ hu (z := fun o =>
      algebraMap (MvPolynomial (Fin (n + 1)) ℂ) (FractionRing (MvPolynomial (Fin (n + 1)) ℂ))
        (X (e o))) (fun o => V.algebraMap_mem (X (e o))) - 1).toNat
  set δ' := δ / 2
  have hδ' : 0 < δ' := half_pos hδ
  have hcb : closedBall p0 δ' ⊆ ball p0 δ := closedBall_subset_ball (half_lt_self hδ)
  have hcK : IsCompact (closedBall p0 δ') := isCompact_closedBall _ _
  obtain ⟨c1, hc1, hc1b⟩ := exists_pos_le_norm_of_continuousOn hcK
    ((hhd none).continuousOn.mono hcb) (fun p hp => (hhf none p (hcb hp)).1)
  obtain ⟨c3, hc3, hc3b⟩ := exists_pos_le_norm_of_continuousOn hcK
    (hh0d.continuousOn.mono hcb) (fun p hp => (hh0 p (hcb hp)).1)
  have hC2 : ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ j : J, ∀ p ∈ closedBall p0 δ', ‖h (some j) p‖ ≤ C2 := by
    choose C hC using fun j : J =>
      hcK.exists_bound_of_continuousOn ((hhd (some j)).continuousOn.mono hcb)
    refine ⟨∑ j, |C j|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun j p hp =>
      (hC j p hp).trans ((le_abs_self _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ j)))⟩
  obtain ⟨C2, hC2nn, hC2b⟩ := hC2
  set C : ℝ := (Fintype.card ι : ℝ) * C2 ^ 2 + 1
  have hCpos : 0 < C := by positivity
  set κ : ℝ := (a + α : ℝ) - b * c
  set K0 : ℝ := c3 ^ 2 * c1 ^ 2 * C ^ (-c)
  have hK0 : 0 < K0 := by positivity
  set U := ball p0 δ' ∩ {p | p s0 ≠ 0}
  set Fz : (Fin (n + 1) → ℂ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal ((∑ j, ‖eval z (g j)‖ ^ 2) ^ (-c)) * ‖eval z f‖ₑ ^ 2
  have hUsub : U ⊆ ball p0 δ := fun p hp => hcb (ball_subset_closedBall hp.1)
  have hUsub' : U ⊆ ball p0 δ ∩ {p | p (e none) ≠ 0} := fun p hp => ⟨hUsub hp, hp.2⟩
  -- the pointwise lower bound on `U`
  have hpt : ∀ p ∈ U, ENNReal.ofReal (K0 * ‖p s0‖ ^ (2 * κ)) ≤
      ENNReal.ofReal |((μ' p).restrictScalars ℝ).det| * Fz (μ p) := by
    rintro p ⟨hpb, hps⟩
    have hpc : p ∈ closedBall p0 δ' := ball_subset_closedBall hpb
    have hpδ : p ∈ ball p0 δ := hcb hpc
    set t := ‖p s0‖
    have ht0 : 0 < t := norm_pos_iff.2 hps
    have ht1 : t ≤ 1 := by
      have h1 : t = dist (p s0) (p0 s0) := by rw [hp0, dist_zero_right]
      rw [h1]
      have : δ' < 1 := by simp only [δ']; linarith
      exact ((dist_le_pi_dist p p0 s0).trans (mem_ball.1 hpb).le).trans this.le
    obtain ⟨-, hfeq⟩ := hhf none p hpδ
    have hfn : c1 * t ^ a ≤ ‖eval (μ p) f‖ := by
      have : eval (μ p) f = p s0 ^ a * h none p := hfeq
      rw [this, norm_mul, norm_pow, mul_comm (‖p s0‖ ^ a)]
      exact mul_le_mul_of_nonneg_right (hc1b p hpc) (by positivity)
    have hgj : ∀ j, ‖eval (μ p) (g j)‖ ^ 2 ≤ C2 ^ 2 * t ^ (2 * b) := by
      intro j
      by_cases hj : g j = 0
      · rw [hj, map_zero, norm_zero]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
      obtain ⟨-, hgeq⟩ := hhf (some ⟨j, hj⟩) p hpδ
      have hgeq' : eval (μ p) (g j) = p s0 ^ (V.ord (g j)).toNat * h (some ⟨j, hj⟩) p := hgeq
      have hbj : b ≤ (V.ord (g j)).toNat := by
        obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (V.ord_eq_top_iff.not.2 hj)
        have := hb j
        rw [← hk] at this ⊢
        rw [ENat.toNat_natCast]
        exact_mod_cast this
      rw [hgeq', norm_mul, norm_pow, mul_pow, mul_comm (C2 ^ 2)]
      refine mul_le_mul ?_ (pow_le_pow_left₀ (norm_nonneg _) (hC2b _ p hpc) 2) (by positivity)
        (by positivity)
      rw [show t ^ (2 * b) = (t ^ b) ^ 2 by ring]
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_of_le_one ht0.le ht1 hbj) 2
    have hgle : ∑ j, ‖eval (μ p) (g j)‖ ^ 2 ≤ C * t ^ (2 * b) := by
      calc ∑ j, ‖eval (μ p) (g j)‖ ^ 2 ≤ ∑ _j : ι, C2 ^ 2 * t ^ (2 * b) :=
            Finset.sum_le_sum fun j _ => hgj j
        _ = (Fintype.card ι : ℝ) * C2 ^ 2 * t ^ (2 * b) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
        _ ≤ C * t ^ (2 * b) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            linarith
    have hgpos : 0 < ∑ j, ‖eval (μ p) (g j)‖ ^ 2 := by
      obtain ⟨hh, hgeq⟩ := hhf (some ⟨j0, hj0⟩) p hpδ
      have hgeq' : eval (μ p) (g j0) = p s0 ^ (V.ord (g j0)).toNat * h (some ⟨j0, hj0⟩) p := hgeq
      have : 0 < ‖eval (μ p) (g j0)‖ ^ 2 := by
        rw [hgeq']
        have : p s0 ^ (V.ord (g j0)).toNat * h (some ⟨j0, hj0⟩) p ≠ 0 :=
          mul_ne_zero (pow_ne_zero _ hps) hh
        positivity
      exact this.trans_le (Finset.single_le_sum (f := fun j => ‖eval (μ p) (g j)‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ j0))
    obtain ⟨-, hdet⟩ := hh0 p hpδ
    have hdetn : c3 * t ^ α ≤ ‖(μ' p).det‖ := by
      rw [hdet, norm_mul, norm_pow, mul_comm (‖p (e none)‖ ^ α)]
      exact mul_le_mul_of_nonneg_right (hc3b p hpc) (by positivity)
    have hW : C ^ (-c) * t ^ (-(2 * b * c)) ≤ (∑ j, ‖eval (μ p) (g j)‖ ^ 2) ^ (-c) := by
      have h1 := Real.rpow_le_rpow_of_nonpos hgpos hgle (neg_nonpos.2 hc.le)
      refine le_trans (le_of_eq ?_) h1
      rw [Real.mul_rpow hCpos.le (by positivity), ← Real.rpow_natCast t (2 * b),
        ← Real.rpow_mul ht0.le]
      congr 2
      push_cast
      ring
    have e1 : t ^ (2 * κ) = (t ^ α) ^ 2 * (t ^ a) ^ 2 * t ^ (-(2 * b * c)) := by
      rw [show 2 * κ = ((2 * α : ℕ) : ℝ) + ((2 * a : ℕ) : ℝ) + (-(2 * b * c)) by
        simp only [κ]; push_cast; ring, Real.rpow_add ht0, Real.rpow_add ht0, Real.rpow_natCast,
        Real.rpow_natCast, ← pow_mul, ← pow_mul, mul_comm α 2, mul_comm a 2]
    have hreal : K0 * t ^ (2 * κ) ≤
        ‖(μ' p).det‖ ^ 2 * ((∑ j, ‖eval (μ p) (g j)‖ ^ 2) ^ (-c) * ‖eval (μ p) f‖ ^ 2) := by
      calc K0 * t ^ (2 * κ) = (c3 * t ^ α) ^ 2 * (C ^ (-c) * t ^ (-(2 * b * c)) *
            (c1 * t ^ a) ^ 2) := by rw [e1]; simp only [K0]; ring
        _ ≤ ‖(μ' p).det‖ ^ 2 * ((∑ j, ‖eval (μ p) (g j)‖ ^ 2) ^ (-c) * ‖eval (μ p) f‖ ^ 2) := by
            refine mul_le_mul (pow_le_pow_left₀ (by positivity) hdetn 2) ?_ (by positivity)
              (by positivity)
            exact mul_le_mul hW (pow_le_pow_left₀ (by positivity) hfn 2) (by positivity)
              (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => by positivity) _)
    simp only [Fz]
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => by positivity) _),
      ← ENNReal.ofReal_mul (abs_nonneg _), det_restrictScalars_real,
      abs_of_nonneg (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  -- change of variables and the hypothesis on a ball containing `μ(U)`
  have hUm : MeasurableSet U :=
    (isOpen_ball.inter (isOpen_ne_fun (continuous_apply s0) continuous_const)).measurableSet
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hUm
    (fun p hp => ((hμ p (hUsub hp)).restrictScalars ℝ).hasFDerivWithinAt)
    (hinj.mono hUsub') Fz
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall 0
  have hsubimg : μ '' U ⊆ closedBall 0 R := (image_mono hUsub).trans hR
  have hfin := hfg (closedBall 0 R) (isCompact_closedBall 0 R)
  have h1 : ∫⁻ p in U, ENNReal.ofReal (K0 * ‖p s0‖ ^ (2 * κ)) < ⊤ := by
    calc ∫⁻ p in U, ENNReal.ofReal (K0 * ‖p s0‖ ^ (2 * κ))
        ≤ ∫⁻ p in U, ENNReal.ofReal |((μ' p).restrictScalars ℝ).det| * Fz (μ p) :=
          setLIntegral_mono' hUm hpt
      _ = ∫⁻ z in μ '' U, Fz z := hcov.symm
      _ ≤ ∫⁻ z in closedBall 0 R, Fz z := lintegral_mono_set hsubimg
      _ < ⊤ := hfin
  have h2 : ∫⁻ p in U, ENNReal.ofReal (‖p s0‖ ^ (2 * κ)) < ⊤ := by
    simp_rw [ENNReal.ofReal_mul hK0.le] at h1
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h1
    by_contra hc'
    rw [not_lt, top_le_iff] at hc'
    rw [hc', ENNReal.mul_top (ENNReal.ofReal_pos.2 hK0).ne'] at h1
    exact lt_irrefl _ h1
  have h3 := neg_one_lt_of_setLIntegral_rpow_lt_top s0 hp0 hδ' h2
  rw [logDiscrepancy_toNat_eq]
  simp only [κ] at h3
  push_cast
  linarith

end Bound

end EnvelopeProperty.Char0
