import EnvelopeProperty.Potential.LineSubharmonic
import EnvelopeProperty.Potential.LineBoundaryMaximum
import EnvelopeProperty.Berkovich.RationalUnitAllPointLocalMaximum

/-! # Actual polynomial logarithms satisfy harmonic comparison -/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}

private theorem fc_affineValue_eventually_eq_of_isLocalMax {J : Type*} [Fintype J]
    (p q : J → K[X]) (hp : ∀ j, p j ≠ 0) (hq : ∀ j, q j ≠ 0)
    (c : ℝ) (α : J → ℝ) (x : RelativeSpectrum w K[X])
    (hx : ∀ j, x.1.val (p j*q j) ≠ 0)
    (hmax : IsLocalMax (RationalUnitFamily.affineValue w p q c α) x) :
    ∃ W, IsOpen W ∧ x ∈ W ∧
      (∀ y ∈ W, RationalUnitFamily.affineValue w p q c α y =
        RationalUnitFamily.affineValue w p q c α x) ∧
      ∀ y ∈ W, ∀ j, y.1.val (p j*q j) ≠ 0 := by
  classical
  let I : Finset Unit := {()}
  have hI : I.Nonempty := by simp [I]
  have he : RationalUnitFamily.maxValue w p q I hI (fun _ => c) (fun _ => α) =
      RationalUnitFamily.affineValue w p q c α := by
    funext y
    simp only [RationalUnitFamily.maxValue,I,Finset.sup'_singleton]
  simpa only [he] using RationalUnitFamily.exists_open_maxValue_constant_of_isLocalMax_any_point
    w p q hp hq I hI (fun _ => c) (fun _ => α) x hx (he ▸ hmax)

namespace FCStandardAffinoid

variable {m : ℕ} (U : FCStandardAffinoid w m)

private def fcLogPolynomialFamily (p : K[X]) : Fin (m+1) → K[X] :=
  Fin.cases p (fun j => X-C (U.holeCenter j))

private def fcLogPolynomialCoefficients (γ : Fin m → ℝ) : Fin (m+1) → ℝ :=
  Fin.cases 1 (fun j => -γ j)

omit [IsAlgClosed K] in
private theorem fc_logPolynomial_affine_eq (p : K[X]) (c : ℝ) (γ : Fin m → ℝ)
    (x : RelativeSpectrum w K[X])
    (hx : ∀ j, x.1.val (U.fcLogPolynomialFamily p j * (1 : K[X])) ≠ 0) :
    RationalUnitFamily.affineValue w (U.fcLogPolynomialFamily p) (fun _ => 1)
      (-c) (fcLogPolynomialCoefficients γ) x =
      polynomialRealLog w x p-U.harmonicExpression c γ x := by
  classical
  unfold RationalUnitFamily.affineValue
  have he : ∀ j, (rationalUnitLog w (U.fcLogPolynomialFamily p j) 1 x).toReal =
      polynomialRealLog w x (U.fcLogPolynomialFamily p j) := by
    intro j
    rw [rationalUnitLog_eq w _ _ x (hx j),EReal.toReal_coe]
    simp only [rationalRealLog,polynomialRealLog,map_one,NNReal.coe_one,Real.log_one,sub_zero]
  simp_rw [he]
  rw [Fin.sum_univ_succ]
  simp only [fcLogPolynomialFamily,fcLogPolynomialCoefficients,Fin.cases_zero,Fin.cases_succ,
    one_mul,neg_mul,Finset.sum_neg_distrib,harmonicExpression,polynomialRealLog]
  ring

/-- The actual logarithmic difference inherits all-point local plateaux from the original unit family. -/
theorem logPolynomial_sub_harmonic_eventually_eq_of_isLocalMax
    (p : K[X]) (hp : p ≠ 0) (c : ℝ) (γ : Fin m → ℝ)
    (x : RelativeSpectrum w K[X]) (hpx : x.1.val p ≠ 0)
    (hx : ∀ j, x.1.val (X-C (U.holeCenter j)) ≠ 0)
    (hmax : IsLocalMax
      (fun y => Spectrum.logAbs p y.1 + ((-U.harmonicExpression c γ y : ℝ) : EReal)) x) :
    ∀ᶠ y in 𝓝 x,
      Spectrum.logAbs p y.1 + ((-U.harmonicExpression c γ y : ℝ) : EReal) =
        Spectrum.logAbs p x.1 + ((-U.harmonicExpression c γ x : ℝ) : EReal) := by
  classical
  let P := U.fcLogPolynomialFamily p
  let Q : Fin (m+1) → K[X] := fun _ => 1
  let α := fcLogPolynomialCoefficients γ
  let A := RationalUnitFamily.affineValue w P Q (-c) α
  have hP : ∀ j, P j ≠ 0 := by
    intro j
    refine Fin.cases hp (fun j => Polynomial.X_sub_C_ne_zero _) j
  have hQ : ∀ j, Q j ≠ 0 := fun _ => one_ne_zero
  have hunits : ∀ j, x.1.val (P j*Q j) ≠ 0 := by
    intro j
    simp only [Q,mul_one]
    exact Fin.cases hpx (fun j => hx j) j
  have he : ∀ y, (∀ j, y.1.val (P j*Q j) ≠ 0) →
      Spectrum.logAbs p y.1 + ((-U.harmonicExpression c γ y : ℝ) : EReal) = (A y : EReal) := by
    intro y hy
    have hyp : y.1.val p ≠ 0 := by simpa only [P,Q,fcLogPolynomialFamily,Fin.cases_zero,mul_one] using hy 0
    rw [show A y = polynomialRealLog w y p-U.harmonicExpression c γ y from
      U.fc_logPolynomial_affine_eq p c γ y hy]
    rw [Spectrum.logAbs,ENNReal.log_of_nnreal hyp,← EReal.coe_add]
    congr 1
  let N : Set (RelativeSpectrum w K[X]) := {y | ∀ j, y.1.val (P j*Q j) ≠ 0}
  have hNo : IsOpen N := by
    change IsOpen {y : RelativeSpectrum w K[X] | ∀ j, y.1.val (P j*Q j) ≠ 0}
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_ne_fun (continuous_val_apply (P j*Q j)) continuous_const
  have hn : ∀ᶠ y in 𝓝 x, y ∈ N := hNo.mem_nhds hunits
  have hmaxA : IsLocalMax A x := by
    filter_upwards [hmax,hn] with y hy hyN
    have h := hy
    rw [he y hyN,he x hunits] at h
    exact_mod_cast h
  obtain ⟨W,hWo,hxW,hW,hWunits⟩ :=
    fc_affineValue_eventually_eq_of_isLocalMax P Q hP hQ (-c) α x hunits hmaxA
  filter_upwards [hWo.mem_nhds hxW] with y hy
  rw [he y (hWunits y hy),he x hunits]
  exact congrArg (fun r : ℝ => (r : EReal)) (hW y hy)

end FCStandardAffinoid

/-- Actual extended polynomial logarithms satisfy the literal standard-affinoid harmonic comparison. -/
theorem isLineSubharmonicOn_logAbs_polynomial (p : K[X])
    (Ω : Set (RelativeSpectrum w K[X])) :
    IsLineSubharmonicOn (fun x => Spectrum.logAbs p x.1) Ω := by
  by_cases hp : p = 0
  · subst p
    simpa only [Spectrum.logAbs_zero] using IsLineSubharmonicOn.bot (w := w) Ω
  have hlog : Continuous (fun x : RelativeSpectrum w K[X] => Spectrum.logAbs p x.1) :=
    (Spectrum.continuous_logAbs p).comp continuous_subtype_val
  refine ⟨hlog.upperSemicontinuous.upperSemicontinuousOn Ω,?_,?_⟩
  · intro x _ he
    exact ENNReal.coe_ne_top (ENNReal.log_eq_top_iff.mp he)
  · intro m U h _ hh hB x
    obtain ⟨c,γ,hγ⟩ := hh
    let F : RelativeSpectrum w K[X] → EReal :=
      fun y => Spectrum.logAbs p y.1 + ((-U.harmonicExpression c γ y : ℝ) : EReal)
    have hE : ContinuousOn (U.harmonicExpression c γ) U.carrier :=
      continuousOn_iff_continuous_domRestrict.mpr (U.continuous_harmonicExpression c γ)
    have hneg : ContinuousOn
        (fun y => ((-U.harmonicExpression c γ y : ℝ) : EReal)) U.carrier :=
      continuous_coe_real_ereal.comp_continuousOn hE.neg
    have hF : ContinuousOn F U.carrier := by
      intro y hy
      exact (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
        (Or.inr (EReal.coe_ne_top _))).comp_continuousWithinAt
          ((hlog.continuousWithinAt).prodMk (hneg y hy))
    have hFB : ∀ z ∈ U.boundary, F z ≤ 0 := by
      intro z hz
      have hb := hB ⟨z,U.boundary_subset hz⟩ hz
      rw [hγ] at hb
      calc
        F z ≤ (U.harmonicExpression c γ z : EReal) +
            ((-U.harmonicExpression c γ z : ℝ) : EReal) :=
          add_le_add hb le_rfl
        _ = 0 := by rw [← EReal.coe_add,add_neg_cancel,EReal.coe_zero]
    have hbound : ∀ y ∈ U.carrier, F y ≤ 0 :=
      U.le_zero_of_boundary_of_local_max_plateau F hF hFB (by
        intro y hy hpos hmax
        have hyp : y.1.val p ≠ 0 := by
          intro hzero
          have hbot : F y = ⊥ := by simp [F,Spectrum.logAbs,hzero]
          rw [hbot] at hpos
          exact not_lt_of_ge bot_le hpos
        exact U.logPolynomial_sub_harmonic_eventually_eq_of_isLocalMax p hp c γ y hyp
          (fun j => (U.holeCoordinate_pos ⟨y,interior_subset hy⟩ j).ne') hmax)
    have he := (EReal.le_sub_iff_add_le
      (Or.inl (EReal.coe_ne_bot (-U.harmonicExpression c γ x.1)))
      (Or.inl (EReal.coe_ne_top (-U.harmonicExpression c γ x.1)))).mpr (hbound x.1 x.2)
    rw [hγ]
    simpa only [zero_sub,EReal.coe_neg,neg_neg] using he

end EnvelopeProperty.Berkovich.RelativeSpectrum
