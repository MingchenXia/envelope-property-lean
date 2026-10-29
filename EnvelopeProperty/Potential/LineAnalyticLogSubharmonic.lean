import EnvelopeProperty.Potential.LineRationalLogSubharmonic
import EnvelopeProperty.Potential.LineSubharmonicLimits
import EnvelopeProperty.Potential.LineAffinoidAlgebra

/-! # Subharmonic logarithms of every function in the genuine completed affinoid algebra -/

open scoped NNReal ENNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

private theorem fc_max_nnnorm_eq_of_sub_le {A : Type*} [SeminormedAddCommGroup A]
    [IsUltrametricDist A] (a b : A) (δ : ℝ≥0) (h : ‖a-b‖₊ ≤ δ) :
    max ‖a‖₊ δ = max ‖b‖₊ δ := by
  have ha : ‖a‖₊ ≤ max ‖b‖₊ δ := by
    calc
      ‖a‖₊ = ‖(a-b)+b‖₊ := by rw [sub_add_cancel]
      _ ≤ max ‖a-b‖₊ ‖b‖₊ := IsUltrametricDist.nnnorm_add_le_max _ _
      _ ≤ max ‖b‖₊ δ := max_le (h.trans (le_max_right _ _)) (le_max_left _ _)
  have hba : ‖b-a‖₊ ≤ δ := by
    have h' : ‖-(a-b)‖₊ ≤ δ := by simpa only [nnnorm_neg] using h
    simpa only [neg_sub] using h'
  have hb : ‖b‖₊ ≤ max ‖a‖₊ δ := by
    calc
      ‖b‖₊ = ‖(b-a)+a‖₊ := by rw [sub_add_cancel]
      _ ≤ max ‖b-a‖₊ ‖a‖₊ := IsUltrametricDist.nnnorm_add_le_max _ _
      _ ≤ max ‖a‖₊ δ := max_le (hba.trans (le_max_right _ _)) (le_max_left _ _)
  exact le_antisymm (max_le ha (le_max_right _ _)) (max_le hb (le_max_right _ _))

private theorem fc_log_nnreal_max (a b : ℝ≥0) :
    ENNReal.log ((max a b : ℝ≥0) : ℝ≥0∞) =
      max (ENNReal.log (a : ℝ≥0∞)) (ENNReal.log (b : ℝ≥0∞)) := by
  rw [ENNReal.coe_max]
  exact ENNReal.log_monotone.map_max

private theorem fc_iInf_max_log_pos (a : EReal) :
    (⨅ δ : {r : ℝ≥0 // 0 < r}, max a (ENNReal.log (δ.1 : ℝ≥0∞))) = a := by
  apply le_antisymm
  · have hcont : Continuous (fun δ : ℝ≥0 => max a (ENNReal.log (δ : ℝ≥0∞))) :=
      continuous_const.max (ENNReal.continuous_log.comp ENNReal.continuous_coe)
    have hlim : Tendsto (fun δ : ℝ≥0 => max a (ENNReal.log (δ : ℝ≥0∞)))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 a) := by
      simpa only [ENNReal.coe_zero,ENNReal.log_zero,max_eq_left bot_le] using
        (hcont.tendsto (0 : ℝ≥0)).mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact iInf_le (fun r : {r : ℝ≥0 // 0 < r} => max a (ENNReal.log (r.1 : ℝ≥0∞))) ⟨δ,hδ⟩
  · exact le_iInf fun δ => le_max_left _ _

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}

namespace FCStandardAffinoid

variable (U : FCStandardAffinoid w m)

/-- The whole completed function's actual logarithm, extended by bottom outside its original carrier. -/
def analyticLog (f : U.AnalyticFunctions) (x : RelativeSpectrum w K[X]) : EReal := by
  classical
  exact if hx : x ∈ U.carrier then ENNReal.log (U.analyticValue f ⟨x,hx⟩ : ℝ≥0∞) else ⊥

theorem analyticLog_apply (f : U.AnalyticFunctions) (x : U.carrier) :
    U.analyticLog f x.1 = ENNReal.log (U.analyticValue f x : ℝ≥0∞) := by
  simp only [analyticLog,dif_pos x.2]

/-- Density and evaluations in the SAME original H(x) give simultaneous exact clipped values. -/
theorem exists_rational_clippedValue_eq (f : U.AnalyticFunctions) (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ g : U.RationalFunctions, ∀ x : U.carrier,
      max (U.analyticValue f x) δ = max (U.rationalValue g x) δ := by
  obtain ⟨g,hg⟩ := U.denseRange_rationalMap.exists_dist_lt f (show 0 < (δ : ℝ) from hδ)
  have hnorm : ‖f-U.rationalMap g‖₊ < δ := by
    exact_mod_cast (show ‖f-U.rationalMap g‖ < (δ : ℝ) by simpa only [dist_eq_norm] using hg)
  refine ⟨g,fun x => ?_⟩
  have he : ‖U.evaluationToH x f-U.evaluationToH x (U.rationalMap g)‖₊ ≤ δ := by
    rw [← map_sub]
    exact (U.nnnorm_evaluationToH_le x _).trans hnorm.le
  rw [← U.analyticValue_rationalMap g x]
  exact fc_max_nnnorm_eq_of_sub_le _ _ δ he

theorem isLineSubharmonicOn_analyticLog_clipped (f : U.AnalyticFunctions)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    IsLineSubharmonicOn (fun x => max (U.analyticLog f x) (ENNReal.log (δ : ℝ≥0∞)))
      (interior U.carrier) := by
  obtain ⟨g,hg⟩ := U.exists_rational_clippedValue_eq f δ hδ
  have hc : IsLineSubharmonicOn (fun _ : RelativeSpectrum w K[X] => ENNReal.log (δ : ℝ≥0∞))
      (interior U.carrier) := by
    rw [ENNReal.log_of_nnreal hδ.ne']
    exact IsLineSubharmonicOn.const _ _
  apply ((U.isLineSubharmonicOn_rationalLog g).sup hc).congr
  intro x hx
  rw [U.rationalLog_apply g ⟨x,interior_subset hx⟩,
    U.analyticLog_apply f ⟨x,interior_subset hx⟩,← fc_log_nnreal_max,← fc_log_nnreal_max]
  exact congrArg (fun r : ℝ≥0 => ENNReal.log (r : ℝ≥0∞)) (hg ⟨x,interior_subset hx⟩).symm

/-- Every genuine completed analytic function satisfies the literal actual harmonic comparison for its log. -/
theorem isLineSubharmonicOn_analyticLog (f : U.AnalyticFunctions) :
    IsLineSubharmonicOn (U.analyticLog f) (interior U.carrier) := by
  let I := {r : ℝ≥0 // 0 < r}
  let _ : Nonempty I := ⟨⟨1,zero_lt_one⟩⟩
  let v : I → RelativeSpectrum w K[X] → EReal :=
    fun δ x => max (U.analyticLog f x) (ENNReal.log (δ.1 : ℝ≥0∞))
  have hv : ∀ δ : I, IsLineSubharmonicOn (v δ) (interior U.carrier) :=
    fun δ => U.isLineSubharmonicOn_analyticLog_clipped f δ.1 δ.2
  have hdir : Directed (· ≥ ·) (fun (δ : I) (x : interior U.carrier) => v δ x.1) := by
    intro a b
    refine ⟨⟨min a.1 b.1,lt_min a.2 b.2⟩,?_,?_⟩
    · intro x
      exact max_le_max_left _ (ENNReal.log_monotone (by exact_mod_cast min_le_left a.1 b.1))
    · intro x
      exact max_le_max_left _ (ENNReal.log_monotone (by exact_mod_cast min_le_right a.1 b.1))
  apply (IsLineSubharmonicOn.iInf_directed v hv hdir).congr
  intro x _
  exact fc_iInf_max_log_pos (U.analyticLog f x)

end FCStandardAffinoid

end EnvelopeProperty.Berkovich.RelativeSpectrum
