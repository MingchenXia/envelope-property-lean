import EnvelopeProperty.Potential.CurveNeighbourhoodDefectBounds
import EnvelopeProperty.Potential.CompletedFibreSmallDefects
import EnvelopeProperty.Potential.CurveAnalyticSpecializationNorm
import EnvelopeProperty.Potential.BanachIdempotentBounded
import EnvelopeProperty.Potential.BanachIdempotentUniqueness

/-! # Actual analytic neighbourhood lifting of the entire original fibre idempotent -/

open scoped NNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
variable [CommRing B] [Algebra K[X] B] [Fintype ι]

/-- Every WHOLE actual completed-fibre idempotent lifts to a genuine analytic idempotent on
an actual standard-affinoid neighbourhood, with EXACT whole original specialization. -/
theorem fc_exists_standardAffinoid_analytic_idempotent
    (x : RelativeSpectrum w K[X]) (basis : Module.Basis ι K[X] B)
    (e : FiniteFreeAnalyticCopy (basis.baseChange x.1.H)) (he : IsIdempotentElem e) :
    ∃ m : ℕ, ∃ U : FCStandardAffinoid w m, ∃ hx : x ∈ interior U.carrier,
      ∃ a : U.CurveAnalyticAlgebra basis, IsIdempotentElem a ∧
        U.curveAnalyticNormedSpecialization basis ⟨x,interior_subset hx⟩ a = e := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hnonempty
  · let : IsEmpty ι := hempty
    obtain ⟨m,U,hx,_⟩ := fc_exists_standardAffinoid_nhds x Filter.univ_mem
    have hezero : e = 0 := by
      apply (FiniteFreeAnalyticCopy.coefficientEquiv (basis.baseChange x.1.H)).injective
      funext i
      exact isEmptyElim i
    refine ⟨m,U,hx,0,by simp only [IsIdempotentElem,mul_zero],?_⟩
    rw [map_zero,hezero]
  · let : Nonempty ι := hnonempty
    obtain ⟨M,hM,happrox⟩ := Spectrum.exists_fractionTensor_arbitrarily_small_coefficient_defect x.1 basis e he
    let T := fcCurveMultiplicationUpper x basis
    let F := fcCurveOneCoefficientUpper x basis
    let C := max 1 (T*M)
    let L := (basis.baseChange x.1.H).fcMultiplicationBound*F
    have hT : 0 < T := fcCurveMultiplicationUpper_pos x basis
    have hF : 0 < F := fcCurveOneCoefficientUpper_pos x basis
    have hC : 1 ≤ C := le_max_left _ _
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    have hL : 0 < L := mul_pos (basis.baseChange x.1.H).fcMultiplicationBound_pos hF
    let η := min (1/(C^2*T)) (1/(2*L*C*T))
    have hη : 0 < η := lt_min (div_pos zero_lt_one (mul_pos (sq_pos_of_pos hCpos) hT))
      (div_pos zero_lt_one (by positivity))
    obtain ⟨d,c,hd,hfrac,hdef,hclose⟩ := happrox (min η (1/2)) (lt_min hη (by norm_num))
    obtain ⟨m,U,hx,hdU,hTU,hFU,hfracU,hdefU⟩ :=
      fc_exists_standardAffinoid_curve_fraction_bounds x basis d c hd M η hM hη hfrac
        (hdef.trans_le (min_le_left _ _))
    let xx : U.carrier := ⟨x,interior_subset hx⟩
    let a := U.curveAnalyticFraction basis d c
    let q := ‖a^2-a‖
    have hq : q < T*η := by
      have hg := (U.curveAnalyticBasis basis).fcCoefficientRingNorm_le
        (U.curveAnalyticOriginalEquiv basis (a^2-a))
      change q ≤ (U.curveAnalyticBasis basis).fcMultiplicationBound*
        (U.curveAnalyticBasis basis).fcCoefficientNorm
          (U.curveAnalyticOriginalEquiv basis (a^2-a)) at hg
      exact hg.trans_lt ((mul_le_mul_of_nonneg_right hTU
        ((U.curveAnalyticBasis basis).fcCoefficientNorm_nonneg _)).trans_lt
          (mul_lt_mul_of_pos_left hdefU hT))
    have hnorma : ‖a‖ ≤ C := by
      have hg := (U.curveAnalyticBasis basis).fcCoefficientRingNorm_le
        (U.curveAnalyticOriginalEquiv basis a)
      change ‖a‖ ≤ (U.curveAnalyticBasis basis).fcMultiplicationBound*
        (U.curveAnalyticBasis basis).fcCoefficientNorm (U.curveAnalyticOriginalEquiv basis a) at hg
      exact (hg.trans (mul_le_mul hTU hfracU.le
        ((U.curveAnalyticBasis basis).fcCoefficientNorm_nonneg _) hT.le)).trans (le_max_right _ _)
    have hηC : C^2*(T*η) ≤ 1 := calc
      _ = (C^2*T)*η := by ring
      _ ≤ (C^2*T)*(1/(C^2*T)) := mul_le_mul_of_nonneg_left (min_le_left _ _)
        (mul_pos (sq_pos_of_pos hCpos) hT).le
      _ = 1 := by field_simp
    have hqC : C^2*q < 1 := (mul_lt_mul_of_pos_left hq (sq_pos_of_pos hCpos)).trans_le hηC
    let : Nontrivial U.AnalyticFunctions := NormOneClass.nontrivial
    let : Nontrivial (U.CurveAnalyticTensor B) :=
      (U.curveAnalyticBasis basis).equivFun.toEquiv.nontrivial
    let : NormOneClass (U.CurveAnalyticAlgebra basis) :=
      FiniteFreeAnalyticCopy.normOneClass (U.curveAnalyticBasis basis)
    have hqC' : C^2*‖a*a-a‖ < 1 := by simpa only [q,pow_two] using hqC
    obtain ⟨b,hb,hba,_⟩ := exists_idempotent_close_of_scaled_norm_defect_lt_one a C hC hnorma hqC'
    have hba' : ‖b-a‖ ≤ C*q := by simpa only [q,pow_two] using hba
    let sp := U.curveAnalyticNormedSpecialization basis xx
    have hspa : sp a = Spectrum.completedFibreFraction x.1 basis d c := by
      change Spectrum.completedFibreElement x.1 basis
          (U.curveAnalyticSpecialization xx
            (U.curveAnalyticOriginalEquiv basis (U.curveAnalyticFraction basis d c))) = _
      rw [U.curveAnalyticFraction_specialization basis d c hdU xx]
      rfl
    have hspec : ‖sp b-sp a‖ ≤ L*‖b-a‖ := by
      rw [← sp.map_sub]
      exact (U.norm_curveAnalyticNormedSpecialization_le basis xx _).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hFU (basis.baseChange x.1.H).fcMultiplicationBound_pos.le)
          (norm_nonneg _))
    have hηL : L*C*(T*η) ≤ 1/2 := calc
      _ = (L*C*T)*η := by ring
      _ ≤ (L*C*T)*(1/(2*L*C*T)) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = 1/2 := by field_simp
    have hstrict : L*(C*q) < 1/2 := calc
      _ = (L*C)*q := by ring
      _ < (L*C)*(T*η) := mul_lt_mul_of_pos_left hq (mul_pos hL hCpos)
      _ ≤ 1/2 := hηL
    have hspecsmall : ‖sp b-sp a‖ < 1/2 :=
      (hspec.trans (mul_le_mul_of_nonneg_left hba' hL.le)).trans_lt hstrict
    have hfracsmall : ‖sp a-e‖ < 1/2 := by
      calc
        _ = ‖Spectrum.completedFibreFraction x.1 basis d c-e‖ := by rw [hspa]
        _ = ‖e-Spectrum.completedFibreFraction x.1 basis d c‖ := norm_sub_rev _ _
        _ < 1/2 := hclose.trans_le (min_le_right _ _)
    have hbe : ‖sp b-e‖ < 1 := by
      have heq : sp b-e = (sp b-sp a)+(sp a-e) := by abel
      rw [heq]
      exact ((IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt hspecsmall hfracsmall)).trans (by norm_num)
    refine ⟨m,U,hx,b,hb,?_⟩
    exact eq_of_isIdempotent_of_norm_sub_lt_one (sp b) e (hb.map sp) he hbe

/-- At every actual original fibre point, the analytic idempotent is CONSTRUCTED and has
exact value one there and zero at EVERY other actual original fibre point. -/
theorem fc_exists_standardAffinoid_analytic_point_idempotent
    (x : RelativeSpectrum w K[X]) (basis : Module.Basis ι K[X] B) (y : Spectrum.Fibre (B := B) x.1) :
    ∃ m : ℕ, ∃ U : FCStandardAffinoid w m, ∃ hx : x ∈ interior U.carrier,
      ∃ a : U.CurveAnalyticAlgebra basis, IsIdempotentElem a ∧
        ∀ z : Spectrum.Fibre (B := B) x.1,
          Spectrum.fibreHom z.2
            (U.curveAnalyticSpecialization ⟨x,interior_subset hx⟩ (U.curveAnalyticOriginalEquiv basis a)) =
              if z = y then 1 else 0 := by
  obtain ⟨e,he,heval⟩ := Spectrum.exists_completedFibre_point_idempotent x.1 basis y
  obtain ⟨m,U,hx,a,ha,hsp⟩ := fc_exists_standardAffinoid_analytic_idempotent x basis e he
  refine ⟨m,U,hx,a,ha,?_⟩
  intro z
  have hraw := congrArg (FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.H)) hsp
  change (FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.H))
      ((FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.H)).symm
        (U.curveAnalyticSpecialization ⟨x,interior_subset hx⟩ (U.curveAnalyticOriginalEquiv basis a))) =
      (FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.H)) e at hraw
  rw [AlgEquiv.apply_symm_apply] at hraw
  rw [hraw]
  exact heval z

end EnvelopeProperty.Berkovich.RelativeSpectrum
