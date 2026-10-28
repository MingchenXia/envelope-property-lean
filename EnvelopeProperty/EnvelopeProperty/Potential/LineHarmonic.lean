import EnvelopeProperty.Potential.LineSkeleton
import EnvelopeProperty.Potential.LineBranchEnds
import EnvelopeProperty.Berkovich.RationalUnitGaussLocalMaximum

/-!
# Actual logarithmic harmonic functions on standard line affinoids

Harmonicity means the literal finite real linear combination of the original
logarithmic hole coordinates. Coefficients are not required to be unique.
-/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

/-- The actual logarithmic expression in the original linear coordinates. -/
def harmonicExpression (c : ℝ) (γ : Fin m → ℝ) (x : RelativeSpectrum w K[X]) : ℝ :=
  c + ∑ j, γ j * Real.log (val x (X-C (U.holeCenter j)) : ℝ)

/-- A function on the actual affinoid is harmonic precisely when represented by actual coefficients. -/
def IsHarmonic (h : U.carrier → ℝ) : Prop :=
  ∃ (c : ℝ) (γ : Fin m → ℝ), ∀ x, h x = U.harmonicExpression c γ x.1

theorem holeCoordinate_pos (x : U.carrier) (j : Fin m) :
    0 < val x.1 (X-C (U.holeCenter j)) :=
  (U.holeRadius_pos j).trans_le (x.2.2 j)

/-- The original skeleton projection preserves each original hole coordinate exactly. -/
theorem holeCoordinate_skeletonProjection (x : RelativeSpectrum w K[X]) (j : Fin m) :
    val (U.skeletonProjection x) (X-C (U.holeCenter j)) = val x (X-C (U.holeCenter j)) := by
  rw [skeletonProjection,fcCenteredInflation_val_X_sub_C,
    max_eq_left (U.skeletonRadius_le_hole x j)]

theorem harmonicExpression_skeletonProjection (c : ℝ) (γ : Fin m → ℝ)
    (x : RelativeSpectrum w K[X]) :
    U.harmonicExpression c γ (U.skeletonProjection x) = U.harmonicExpression c γ x := by
  simp only [harmonicExpression,U.holeCoordinate_skeletonProjection]

theorem harmonicExpression_gauss (c : ℝ) (γ : Fin m → ℝ) (b : K) (s : ℝ≥0) :
    U.harmonicExpression c γ (centeredGauss (self w) b s) =
      c + ∑ j, γ j * Real.log (max (w (b-U.holeCenter j)) s : ℝ≥0) := by
  simp only [harmonicExpression,fc_centeredGauss_val_X_sub_C]

/-- All logarithms are genuinely continuous on the actual affinoid because the holes have positive radii. -/
theorem continuous_harmonicExpression (c : ℝ) (γ : Fin m → ℝ) :
    Continuous (fun x : U.carrier => U.harmonicExpression c γ x.1) := by
  have hj : ∀ j : Fin m, Continuous (fun x : U.carrier =>
      Real.log (val x.1 (X-C (U.holeCenter j)) : ℝ)) := by
    intro j
    apply Continuous.log
    · exact continuous_subtype_val.comp ((continuous_val_apply _).comp continuous_subtype_val)
    · intro x
      exact ne_of_gt (show (0 : ℝ) < (val x.1 (X-C (U.holeCenter j)) : ℝ) from
        by exact_mod_cast U.holeCoordinate_pos x j)
  exact continuous_const.add (continuous_finsetSum _ fun j _ => continuous_const.mul (hj j))

theorem IsHarmonic.continuous {h : U.carrier → ℝ} (hh : U.IsHarmonic h) : Continuous h := by
  obtain ⟨c,γ,hγ⟩ := hh
  have he : h = fun x => U.harmonicExpression c γ x.1 := funext hγ
  rw [he]
  exact U.continuous_harmonicExpression c γ

private theorem harmonicExpression_translation_eq_affineValue (a : K) (c : ℝ)
    (γ : Fin m → ℝ) (z : RelativeSpectrum w K[X])
    (hz : ∀ j, val z ((X-C (U.holeCenter j-a))*1) ≠ 0) :
    U.harmonicExpression c γ (polynomialTranslation a z) =
      RationalUnitFamily.affineValue w (fun j => X-C (U.holeCenter j-a)) (fun _ => 1) c γ z := by
  unfold harmonicExpression RationalUnitFamily.affineValue
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [fcTranslate_val_X_sub_C,rationalUnitLog_eq w _ _ z (hz j)]
  simp only [EReal.toReal_coe,rationalRealLog,polynomialRealLog,map_one,
    NNReal.coe_one,Real.log_one,sub_zero]

variable [IsAlgClosed K]

theorem IsHarmonic.retraction_invariant {h : U.carrier → ℝ} (hh : U.IsHarmonic h)
    (x : U.carrier) :
    h ⟨(U.radialRetraction x).1,U.radialSkeleton_subset (U.radialRetraction x).2⟩ = h x := by
  obtain ⟨c,γ,hγ⟩ := hh
  rw [hγ,hγ]
  exact U.harmonicExpression_skeletonProjection c γ x.1

/-- A strict residue disc makes every original finite coordinate constant away from its possible Gauss vertex. -/
theorem harmonicExpression_eventually_eq_of_min_nongauss (c : ℝ) (γ : Fin m → ℝ)
    (x : RelativeSpectrum w K[X]) (j : Fin m)
    (hmin : ∀ i, val x (X-C (U.holeCenter j)) ≤ val x (X-C (U.holeCenter i)))
    (hne : x ≠ centeredGauss (self w) (U.holeCenter j) (val x (X-C (U.holeCenter j)))) :
    ∀ᶠ y in 𝓝 x, U.harmonicExpression c γ y = U.harmonicExpression c γ x := by
  let s := val x (X-C (U.holeCenter j))
  obtain ⟨b,_,hxb⟩ := fc_exists_strict_residue_disc x (U.holeCenter j) s le_rfl hne
  have hN : ∀ᶠ y in 𝓝 x, val y (X-C b) < s :=
    (isOpen_lt (continuous_val_apply _) continuous_const).mem_nhds hxb
  filter_upwards [hN] with y hy
  unfold harmonicExpression
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hxi : val x (X-C b) < val x (X-C (U.holeCenter i)) := hxb.trans_le (hmin i)
  have hd : w (b-U.holeCenter i) = val x (X-C (U.holeCenter i)) := by
    apply le_antisymm
    · exact (fc_center_distance_bound x b (U.holeCenter i)).trans_eq (max_eq_right hxi.le)
    · apply le_of_not_gt
      intro hbad
      exact not_lt_of_ge (fc_linear_bound x b (U.holeCenter i)) (max_lt hxi hbad)
  have hyi : val y (X-C b) < w (b-U.holeCenter i) := by
    rw [hd]
    exact hy.trans_le (hmin i)
  rw [fc_linear_value_eq_max y b (U.holeCenter i) hyi.ne,max_eq_right hyi.le,hd]

/-- Genuine original rational-unit slopes give local constancy at any translated positive-radius Gauss maximum. -/
theorem harmonicExpression_eventually_eq_of_isLocalMax_gauss (c : ℝ) (γ : Fin m → ℝ)
    (a : K) (r : ℝ≥0) (hr : 0 < r)
    (hmax : IsLocalMax (U.harmonicExpression c γ) (centeredGauss (self w) a r)) :
    ∀ᶠ y in 𝓝 (centeredGauss (self w) a r),
      U.harmonicExpression c γ y = U.harmonicExpression c γ (centeredGauss (self w) a r) := by
  classical
  let p : Fin m → K[X] := fun j => X-C (U.holeCenter j-a)
  let q : Fin m → K[X] := fun _ => 1
  have hp : ∀ j, p j ≠ 0 := fun j => Polynomial.X_sub_C_ne_zero _
  have hq : ∀ j, q j ≠ 0 := fun _ => one_ne_zero
  let η : RelativeSpectrum w K[X] := gauss (self w) r
  let T : RelativeSpectrum w K[X] ≃ₜ RelativeSpectrum w K[X] := polynomialTranslation a
  have hη : T η = centeredGauss (self w) a r := rfl
  have hEt : IsLocalMax (fun z => U.harmonicExpression c γ (T z)) η := by
    rw [← hη] at hmax
    exact hmax.comp_continuous T.continuous.continuousAt
  let N := RationalUnitFamily.neighborhood w r hr p q
  have hNo : IsOpen N := RationalUnitFamily.isOpen_neighborhood w r hr p q
  have hηN : η ∈ N := RationalUnitFamily.gauss_mem_neighborhood w r hr p q
  have heN : ∀ z ∈ N, U.harmonicExpression c γ (T z) =
      RationalUnitFamily.affineValue w p q c γ z := by
    intro z hz
    exact U.harmonicExpression_translation_eq_affineValue a c γ z
      (fun j => RationalUnitFamily.unit_mul_ne_zero_on_neighborhood w r hr p q hp hq j z hz)
  let I : Finset Unit := {()}
  have hI : I.Nonempty := by simp [I]
  let cc : Unit → ℝ := fun _ => c
  let α : Unit → Fin m → ℝ := fun _ => γ
  let M := RationalUnitFamily.maxValue w p q I hI cc α
  have hM : ∀ z, M z = RationalUnitFamily.affineValue w p q c γ z := by
    intro z
    simp only [M,RationalUnitFamily.maxValue,I,Finset.sup'_singleton,cc,α]
  have hN : ∀ᶠ z in 𝓝 η, z ∈ N := hNo.mem_nhds hηN
  have hEM : (fun z => U.harmonicExpression c γ (T z)) =ᶠ[𝓝 η] M :=
    hN.mono fun z hz => (heN z hz).trans (hM z).symm
  have hmaxM : IsLocalMax M η := hEt.congr hEM
  obtain ⟨W,hWo,hηW,hW,_⟩ :=
    RationalUnitFamily.exists_open_maxValue_constant_of_isLocalMax w r hr p q hp hq
      I hI cc α hmaxM
  have hE : ∀ᶠ z in 𝓝 η, U.harmonicExpression c γ (T z) =
      U.harmonicExpression c γ (T η) := by
    filter_upwards [hNo.mem_nhds hηN,hWo.mem_nhds hηW] with z hzN hzW
    exact (heN z hzN).trans ((hM z).symm.trans ((hW z hzW).trans ((hM η).trans (heN η hηN).symm)))
  have ht : Tendsto T.symm (𝓝 (centeredGauss (self w) a r)) (𝓝 η) := by
    rw [← hη]
    simpa only [T.symm_apply_apply] using T.symm.continuous.tendsto (T η)
  simpa only [T.apply_symm_apply,hη] using ht.eventually hE

/-- Every actual local maximum on the common positive coordinate locus is locally constant. -/
theorem harmonicExpression_eventually_eq_of_isLocalMax (c : ℝ) (γ : Fin m → ℝ)
    (x : RelativeSpectrum w K[X])
    (hpos : ∀ j, 0 < val x (X-C (U.holeCenter j)))
    (hmax : IsLocalMax (U.harmonicExpression c γ) x) :
    ∀ᶠ y in 𝓝 x, U.harmonicExpression c γ y = U.harmonicExpression c γ x := by
  classical
  by_cases hm : m = 0
  · subst m
    exact Eventually.of_forall (by intro y; simp [harmonicExpression])
  · have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
      ⟨⟨0,Nat.pos_of_ne_zero hm⟩,Finset.mem_univ _⟩
    obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_inf' hnonempty
      (fun i : Fin m => val x (X-C (U.holeCenter i)))
    have hmin : ∀ i, val x (X-C (U.holeCenter j)) ≤ val x (X-C (U.holeCenter i)) := by
      intro i
      rw [← hj]
      exact Finset.inf'_le _ (Finset.mem_univ i)
    by_cases he : x = centeredGauss (self w) (U.holeCenter j) (val x (X-C (U.holeCenter j)))
    · have hh := U.harmonicExpression_eventually_eq_of_isLocalMax_gauss c γ
        (U.holeCenter j) (val x (X-C (U.holeCenter j))) (hpos j)
      rw [← he] at hh
      exact hh hmax
    · exact U.harmonicExpression_eventually_eq_of_min_nongauss c γ x j hmin he

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
