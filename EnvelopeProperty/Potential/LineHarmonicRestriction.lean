import EnvelopeProperty.Potential.LineHarmonicSubharmonic
import EnvelopeProperty.Potential.LineRigidDensity

/-! # Actual harmonic restriction and the logarithms of original polynomial units -/

open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}

namespace FCStandardAffinoid

variable {m : ℕ} (U : FCStandardAffinoid w m)

theorem IsHarmonic.multisetSum {ι : Type*} (s : Multiset ι) (f : ι → U.carrier → ℝ)
    (hf : ∀ i ∈ s, U.IsHarmonic (f i)) :
    U.IsHarmonic (fun x => (s.map fun i => f i x).sum) := by
  revert hf
  induction s using Multiset.induction_on with
  | empty => intro _; simpa only [Multiset.map_zero,Multiset.sum_zero] using IsHarmonic.const U 0
  | @cons i s ih =>
    intro hf
    have hi := hf i (Multiset.mem_cons_self _ _)
    have hs := ih (fun j hj => hf j (Multiset.mem_cons_of_mem hj))
    simpa only [Multiset.map_cons,Multiset.sum_cons,Pi.add_def] using hi.add U hs

/-- A nonvanishing original linear section has a literal constant or original hole-coordinate logarithm. -/
theorem isHarmonic_logLinear_of_nonvanishing (a : K)
    (ha : ∀ x : U.carrier, val x.1 (X-C a) ≠ 0) :
    U.IsHarmonic (fun x => Real.log (val x.1 (X-C a) : ℝ)) := by
  classical
  have haU : fcRigidPoint (w := w) a ∉ U.carrier := by
    intro haU
    have h := ha ⟨fcRigidPoint a,haU⟩
    exact h (by simp [fcRigidPoint,fc_centeredGauss_val_X_sub_C])
  by_cases ho : w (a-U.center) ≤ U.radius
  · have hh : ∃ j, w (a-U.holeCenter j) < U.holeRadius j := by
      by_contra hn
      apply haU
      constructor
      · simpa only [fcRigidPoint,fc_centeredGauss_val_X_sub_C,max_zero] using ho
      · intro j
        have hj := le_of_not_gt (not_exists.mp hn j)
        simpa only [fcRigidPoint,fc_centeredGauss_val_X_sub_C,max_zero] using hj
    obtain ⟨j,hj⟩ := hh
    refine ⟨0,fun i => if i = j then 1 else 0,?_⟩
    intro x
    have hd : w (U.holeCenter j-a) < val x.1 (X-C (U.holeCenter j)) := by
      rw [show U.holeCenter j-a = -(a-U.holeCenter j) by ring,Valuation.map_neg]
      exact hj.trans_le (x.2.2 j)
    change Real.log (val x.1 (X-C a) : ℝ) = _
    rw [fc_linear_value_eq_max x.1 (U.holeCenter j) a hd.ne',max_eq_left hd.le]
    simp [harmonicExpression,ite_mul]
  · have hd : U.radius < w (U.center-a) := by
      rw [show U.center-a = -(a-U.center) by ring,Valuation.map_neg]
      exact lt_of_not_ge ho
    have he : (fun x : U.carrier => Real.log (val x.1 (X-C a) : ℝ)) =
        fun _ => Real.log (w (U.center-a) : ℝ) := by
      funext x
      rw [fc_linear_value_eq_max x.1 U.center a (ne_of_lt (x.2.1.trans_lt hd)),
        max_eq_right (x.2.1.trans hd.le)]
    rw [he]
    exact IsHarmonic.const U _

/-- Every literal original harmonic expression restricts to any actual standard subaffinoid. -/
theorem isHarmonic_harmonicExpression_of_subset {n : ℕ} (V : FCStandardAffinoid w n)
    (hVU : V.carrier ⊆ U.carrier) (c : ℝ) (γ : Fin m → ℝ) :
    V.IsHarmonic (fun x => U.harmonicExpression c γ x.1) := by
  classical
  have hsum : V.IsHarmonic (fun x =>
      ((Finset.univ : Finset (Fin m)).val.map fun j =>
        γ j*Real.log (val x.1 (X-C (U.holeCenter j)) : ℝ)).sum) := by
    apply IsHarmonic.multisetSum V
    intro j _
    have hj := V.isHarmonic_logLinear_of_nonvanishing (U.holeCenter j)
      (fun x => (U.holeCoordinate_pos ⟨x.1,hVU x.2⟩ j).ne')
    simpa only [Pi.smul_def,smul_eq_mul] using hj.smul V (γ j)
  simpa only [Pi.add_def,harmonicExpression,Finset.sum] using
    (IsHarmonic.const V c).add V hsum

theorem IsHarmonic.restrict {h : U.carrier → ℝ} (hh : U.IsHarmonic h)
    {n : ℕ} (V : FCStandardAffinoid w n) (hVU : V.carrier ⊆ U.carrier) :
    V.IsHarmonic (fun x => h ⟨x.1,hVU x.2⟩) := by
  obtain ⟨c,γ,hγ⟩ := hh
  simpa only [hγ] using U.isHarmonic_harmonicExpression_of_subset V hVU c γ

theorem isLineHarmonicOn_harmonicExpression (c : ℝ) (γ : Fin m → ℝ) :
    IsLineHarmonicOn (U.harmonicExpression c γ) U.carrier where
  isHarmonic := fun V hVU => U.isHarmonic_harmonicExpression_of_subset V hVU c γ

variable [IsAlgClosed K]

theorem isHarmonic_polynomialRealLog_of_nonvanishing (p : K[X])
    (hp : ∀ x : U.carrier, x.1.1.val p ≠ 0) :
    U.IsHarmonic (fun x => polynomialRealLog w x.1 p) := by
  have hs : U.IsHarmonic (fun x =>
      (p.roots.map fun a => Real.log (val x.1 (X-C a) : ℝ)).sum) := by
    apply IsHarmonic.multisetSum U
    intro a ha
    exact U.isHarmonic_logLinear_of_nonvanishing a
      (fun x => linear_val_ne_zero_of_polynomial_ne_zero w x.1 p (hp x) ha)
  have hsum := (IsHarmonic.const U (Real.log (w p.leadingCoeff : ℝ))).add U hs
  have he : (fun x : U.carrier => polynomialRealLog w x.1 p) =
      (fun _ : U.carrier => Real.log (w p.leadingCoeff : ℝ))+
        (fun x => (p.roots.map fun a => Real.log (val x.1 (X-C a) : ℝ)).sum) := by
    funext x
    exact polynomialRealLog_eq_root_sum w x.1 p (hp x)
  rw [he]
  exact hsum

end FCStandardAffinoid

variable [IsAlgClosed K]

theorem isLineHarmonicOn_polynomialRealLog (p : K[X])
    (Ω : Set (RelativeSpectrum w K[X])) (hp : ∀ x ∈ Ω, x.1.val p ≠ 0) :
    IsLineHarmonicOn (fun x => polynomialRealLog w x p) Ω where
  isHarmonic := fun U hU => U.isHarmonic_polynomialRealLog_of_nonvanishing p
    (fun x => hp x.1 (hU x.2))

theorem isLineHarmonicOn_rationalRealLog (p q : K[X])
    (Ω : Set (RelativeSpectrum w K[X])) (hpq : ∀ x ∈ Ω, x.1.val (p*q) ≠ 0) :
    IsLineHarmonicOn (fun x => rationalRealLog w x p q) Ω where
  isHarmonic := by
    intro m U hU
    have hprod (x : U.carrier) := hpq x.1 (hU x.2)
    simp only [map_mul,mul_ne_zero_iff] at hprod
    have hp := U.isHarmonic_polynomialRealLog_of_nonvanishing p (fun x => (hprod x).1)
    have hq := U.isHarmonic_polynomialRealLog_of_nonvanishing q (fun x => (hprod x).2)
    simpa only [Pi.sub_def,rationalRealLog] using hp.sub U hq

end EnvelopeProperty.Berkovich.RelativeSpectrum
