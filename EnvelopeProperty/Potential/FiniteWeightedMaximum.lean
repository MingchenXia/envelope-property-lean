import EnvelopeProperty.Local.FiniteFlatNorm

/-! # Actual finite positive weighted sum saturation, including bottom-valued input -/

noncomputable section
namespace EnvelopeProperty

/-- A finite positive weighted sum reaches its common finite bound only when EVERY
original extended-real value reaches that bound. No finite-value premise is assumed. -/
theorem eq_of_finite_positive_weighted_sum_eq_max {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (hc : ∀ i ∈ s, 0 < c i) (u : ι → EReal) (R : ℝ)
    (hu : ∀ i ∈ s, u i ≤ (R : EReal))
    (hsum : ∑ i ∈ s, (c i : EReal)*u i = (((∑ i ∈ s, c i)*R : ℝ) : EReal)) :
    ∀ i ∈ s, u i = (R : EReal) := by
  classical
  have hut (i : ι) (hi : i ∈ s) : u i ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top R) (hu i hi)
  have hub (i : ι) (hi : i ∈ s) : u i ≠ ⊥ := by
    intro hbot
    have ht : (c i : EReal)*u i = ⊥ := by
      rw [hbot,EReal.coe_mul_bot_of_pos (hc i hi)]
    have hs := hsum
    rw [← Finset.sum_erase_add s (fun i => (c i : EReal)*u i) hi,ht,EReal.add_bot] at hs
    exact EReal.coe_ne_bot _ hs.symm
  have heq (i : ι) (hi : i ∈ s) : ((u i).toReal : EReal) = u i :=
    EReal.coe_toReal (hut i hi) (hub i hi)
  have hle : ∀ i ∈ s, c i*(u i).toReal ≤ c i*R := by
    intro i hi
    have hui : (u i).toReal ≤ R := by
      apply EReal.coe_le_coe_iff.mp
      rw [heq i hi]
      exact hu i hi
    exact mul_le_mul_of_nonneg_left hui (hc i hi).le
  have hreal : ∑ i ∈ s, c i*(u i).toReal = (∑ i ∈ s, c i)*R := by
    apply EReal.coe_injective
    have hcoe_sum (S : Finset ι) (f : ι → ℝ) : ((∑ i ∈ S, f i : ℝ) : EReal) =
        ∑ i ∈ S, (f i : EReal) := by
      induction S using Finset.induction_on with
      | empty => simp only [Finset.sum_empty,EReal.coe_zero]
      | insert i S hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi,EReal.coe_add,ih]
    calc
      (((∑ i ∈ s, c i*(u i).toReal : ℝ)) : EReal) = ∑ i ∈ s, (c i : EReal)*u i := by
        rw [hcoe_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [EReal.coe_mul,heq i hi]
      _ = _ := hsum
  have hterms : ∀ i ∈ s, c i*(u i).toReal = c i*R :=
    (Finset.sum_eq_sum_iff_of_le hle).mp (hreal.trans (Finset.sum_mul _ _ _))
  intro i hi
  have hiR : (u i).toReal = R := mul_left_cancel₀ (hc i hi).ne' (hterms i hi)
  rw [← heq i hi,hiR]

end EnvelopeProperty
