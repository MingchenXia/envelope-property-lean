import EnvelopeProperty.FiniteAffineMax

/-! # The true weighted inequality for actual active finite affine maxima -/
noncomputable section
namespace EnvelopeProperty.FiniteAffineMax
variable {ι δ : Type*}

/-- Original nonnegative weights and genuine individual WEIGHTED balancing
imply the nonnegative WEIGHTED sum of the SAME actual active-max slopes.
This pure finite real lemma retains every original residue-degree weight;
its analytic consumers must derive their own genuine slopes and balance. -/
theorem sum_weighted_activeSlope_nonneg (I : Finset ι) (hI : I.Nonempty) (D : Finset δ)
    (b : ι → ℝ) (s : ι → δ → ℝ) (w : δ → ℝ) (hw : ∀ d ∈ D, 0 ≤ w d)
    (hs : ∀ i ∈ I, ∑ d ∈ D, w d*s i d = 0) :
    0 ≤ ∑ d ∈ D, w d*activeSlope I hI b s d := by
  classical
  obtain ⟨i, hi⟩ := active_nonempty I hI b
  have hiI := (Finset.mem_filter.mp hi).1
  have hle : (∑ d ∈ D, w d*s i d) ≤ ∑ d ∈ D, w d*activeSlope I hI b s d :=
    Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left
      (Finset.le_sup' (fun j => s j d) hi) (hw d hd))
  rwa [hs i hiI] at hle

end EnvelopeProperty.FiniteAffineMax
