import EnvelopeProperty.AlgGeom.NativeNumericalRationalAmpleLines
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Actual geometric rational ample approximation of every intrinsic ample class -/
open AlgebraicGeometry CategoryTheory Filter
open Scheme.Modules
open scoped Topology
noncomputable section
universe u
namespace EnvelopeProperty.NativeRealNumericalClasses
open NativeClosedCurveDegrees
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (p : X ⟶ Spec (.of k)) [IsProjective p]

private theorem positive_rational_near (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ |(q : ℝ) - a| < ε := by
  have hab : max 0 (a - ε) < a + ε := max_lt (by linarith) (by linarith)
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hab
  refine ⟨q, ?_, abs_lt.mpr ⟨?_, ?_⟩⟩
  · have hpos : 0 < (q : ℝ) := (le_max_left 0 (a - ε)).trans_lt hq₁
    exact_mod_cast hpos
  · have hh := (le_max_right 0 (a - ε)).trans_lt hq₁
    linarith
  · linarith

/-- Arbitrarily close POSITIVE rational coefficients on actual original ample lines
come from an INTERNALLY constructed positive rational multiple of an actual ample line. -/
theorem exists_positive_rational_ample_approximation {n : ℕ} (hn : 0 < n)
    (A : Fin n → X.Modules) (hA : ∀ i, SchemeLineAmpleness.IsAmple p (A i))
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : Fin n → ℚ, (∀ i, 0 < q i ∧ |(q i : ℝ) - a i| < ε) ∧
      ∃ d : ℕ, 0 < d ∧ ∃ L : X.Modules, ∃ hL : SchemeLineAmpleness.IsAmple p L,
        lineFamilyMap p A (fun i => (hA i).isInvertible) (fun i => (q i : ℝ)) =
          (d : ℝ)⁻¹ • lineClass p L hL.isInvertible := by
  choose q hq using fun i => positive_rational_near (a i) ε (ha i) hε
  exact ⟨q, hq, exists_rational_ample_line_representative p hn A hA q (fun i => (hq i).1)⟩

/-- Every intrinsic ample class has internally produced SAME actual finite ample lines,
positive rational vectors converging in ordinary coefficients, and actual geometric ample
representatives at EVERY stage, with all original true closed-curve degree limits. -/
theorem exists_geometric_ample_approximation (θ : Space p) (hθ : θ ∈ ampleCone p) :
    ∃ n : ℕ, 0 < n ∧ ∃ A : Fin n → X.Modules,
      ∃ hA : ∀ i, SchemeLineAmpleness.IsAmple p (A i), ∃ a : Fin n → ℝ,
        (∀ i, 0 < a i) ∧ θ = lineFamilyMap p A (fun i => (hA i).isInvertible) a ∧
        ∃ q : ℕ → Fin n → ℚ, ∃ d : ℕ → ℕ, ∃ L : ℕ → X.Modules,
          ∃ hL : ∀ s, SchemeLineAmpleness.IsAmple p (L s),
            (∀ s, 0 < d s) ∧
            (∀ s i, 0 < q s i ∧ |(q s i : ℝ) - a i| < 1 / ((s : ℝ) + 1)) ∧
            (∀ s, lineFamilyMap p A (fun i => (hA i).isInvertible) (fun i => (q s i : ℝ)) =
              (d s : ℝ)⁻¹ • lineClass p (L s) (hL s).isInvertible) ∧
            Tendsto (fun s i => (q s i : ℝ)) atTop (𝓝 a) ∧
            ∀ C : ClosedIntegralCurve X,
              Tendsto (fun s => (d s : ℝ)⁻¹ * curveDegree p C
                (lineClass p (L s) (hL s).isInvertible)) atTop (𝓝 (curveDegree p C θ)) := by
  classical
  obtain ⟨n, hn, A, hA, a, ha, he⟩ := exists_positive_ample_line_sum p θ hθ
  have hstage (s : ℕ) := exists_positive_rational_ample_approximation p hn A hA a ha
    (1 / ((s : ℝ) + 1)) (by positivity)
  choose q hq d hd L hL hrep using hstage
  have hlim : Tendsto (fun s i => (q s i : ℝ)) atTop (𝓝 a) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hzero := squeeze_zero (fun s => abs_nonneg ((q s i : ℝ) - a i))
      (fun s => (hq s i).2.le) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [Real.dist_eq] using hzero
  refine ⟨n, hn, A, hA, a, ha, he, q, d, L, hL, hd, hq, hrep, hlim, fun C => ?_⟩
  have hcont : Continuous (fun b : Fin n → ℝ => ∑ i,
      b i * curveDegree p C (lineClass p (A i) (hA i).isInvertible)) := by
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const
  have hh := hcont.continuousAt.tendsto.comp hlim
  have hvalue (s : ℕ) :
      (∑ i, (q s i : ℝ) * curveDegree p C (lineClass p (A i) (hA i).isInvertible)) =
        (d s : ℝ)⁻¹ * curveDegree p C (lineClass p (L s) (hL s).isInvertible) := by
    have h := congrArg (curveDegree p C) (hrep s)
    simpa only [curveDegree_lineFamilyMap, (curveDegree p C).map_smul, smul_eq_mul] using h
  change Tendsto (fun s => ∑ i, (q s i : ℝ) *
    curveDegree p C (lineClass p (A i) (hA i).isInvertible)) atTop
      (𝓝 (∑ i, a i * curveDegree p C (lineClass p (A i) (hA i).isInvertible))) at hh
  rw [he, curveDegree_lineFamilyMap]
  simpa only [hvalue] using hh

end EnvelopeProperty.NativeRealNumericalClasses
