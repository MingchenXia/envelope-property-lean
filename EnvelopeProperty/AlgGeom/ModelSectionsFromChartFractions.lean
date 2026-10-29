import EnvelopeProperty.Global.ModelChangeSections

/-! # Whole genuine model sections are exactly their actual regular chart fractions -/
open scoped Classical NNReal Topology
open Topology MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
variable {k K : Type u} [Field k] [Field K] [Algebra k K] {r : ℕ}
  (P : MultiModel k K r)

/-- A genuine WHOLE original chart-algebra fraction internally supplies an actual
homogeneous clearing exponent, also for original negative integer degrees. -/
theorem exists_clear_chart_fraction (a : Fin r → ℤ) (f : K) (j : P.ChartIndex)
    (hj : ∀ c, P.coord c (j c) ≠ 0) (hf : f / P.chartDenZ j a ∈ P.chartAlg j) :
    ∃ b : Fin r →₀ ℕ, (∀ c, 0 ≤ a c + b c) ∧ f * P.chartDen j b ∈ P.piece (addDeg a b) := by
  obtain ⟨b,g,hg,he⟩ := (P.mem_chartAlg_iff hj).mp hf
  let n : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun c => (-a c).toNat)
  have hn : ∀ c, 0 ≤ a c + n c := by
    intro c
    change 0 ≤ a c + ((-a c).toNat : ℤ)
    omega
  have hden : P.chartDenZ j a ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun c _ => zpow_ne_zero _ (hj c))
  have hmul : f * P.chartDen j b = g * P.chartDenZ j a :=
    (div_eq_div_iff hden (P.chartDen_ne_zero hj b)).mp he
  refine ⟨n + b,fun c => ?_,?_⟩
  · have h := hn c
    simp only [Finsupp.add_apply,Nat.cast_add]
    omega
  · rw [addDeg_add hn b]
    have hfield : f * P.chartDen j (n + b) = g * P.chartDen j (addDeg a n) := by
      rw [P.chartDen_add, P.chartDen_addDeg hj hn]
      calc
        f * (P.chartDen j n * P.chartDen j b) =
            (f * P.chartDen j b) * P.chartDen j n := by ring
        _ = g * P.chartDenZ j a * P.chartDen j n := by rw [hmul]
        _ = g * (P.chartDenZ j a * P.chartDen j n) := by ring
    rw [hfield]
    have h := P.mul_mem_piece hg (P.chartDen_mem_piece j (addDeg a n))
    simpa only [add_comm b (addDeg a n)] using h

/-- ALL original nonempty chart fractions internally give ONE common original
homogeneous clearing exponent; finiteness comes from the actual model coordinates. -/
theorem exists_uniform_clear_chart_fractions (a : Fin r → ℤ) (f : K)
    (hf : ∀ j : P.ChartIndex, (∀ c, P.coord c (j c) ≠ 0) →
      f / P.chartDenZ j a ∈ P.chartAlg j) :
    ∃ C : Fin r →₀ ℕ, (∀ c, 0 ≤ a c + C c) ∧
      ∀ j : P.ChartIndex, (∀ c, P.coord c (j c) ≠ 0) →
        f * P.chartDen j C ∈ P.piece (addDeg a C) := by
  classical
  let J := {j : P.ChartIndex // ∀ c, P.coord c (j c) ≠ 0}
  choose b hb0 hb using (fun j : J => P.exists_clear_chart_fraction a f j.1 j.2 (hf j.1 j.2))
  let n : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun c => (-a c).toNat)
  let C : Fin r →₀ ℕ := n + ∑ j : J, b j
  have hle (j : J) : b j ≤ C := by
    have h := Finset.single_le_sum (fun q (_ : q ∈ (Finset.univ : Finset J)) => (show 0 ≤ b q from zero_le))
      (Finset.mem_univ j)
    exact h.trans le_add_self
  have hn : ∀ c, 0 ≤ a c + n c := by
    intro c
    change 0 ≤ a c + ((-a c).toNat : ℤ)
    omega
  have hC : ∀ c, 0 ≤ a c + C c := by
    intro c
    have h := hn c
    have hle : n c ≤ C c := le_self_add
    omega
  refine ⟨C,hC,fun j hj => ?_⟩
  let z : J := ⟨j,hj⟩
  let e := C - b z
  have he : b z + e = C := add_tsub_cancel_of_le (hle z)
  have hfield : f * P.chartDen j C = (f * P.chartDen j (b z)) * P.chartDen j e := by
    rw [← he,P.chartDen_add]
    ring
  have hdeg : addDeg a C = addDeg a (b z) + e := by rw [← he,addDeg_add (hb0 z)]
  rw [hfield,hdeg]
  exact P.mul_mem_piece (hb z) (P.chartDen_mem_piece j e)

/-- The WHOLE original model section space is EXACTLY the actual regular-fraction
condition on ALL genuine nonempty coordinate charts, with no normality assumption. -/
theorem mem_sections_iff_chart_fractions (a : Fin r → ℤ) (f : K) :
    f ∈ P.sections a ↔ ∀ j : P.ChartIndex, (∀ c, P.coord c (j c) ≠ 0) →
      f / P.chartDenZ j a ∈ P.chartAlg j := by
  constructor
  · intro hf j hj
    exact P.div_chartDenZ_mem_chartAlg hj hf
  · intro hf
    obtain ⟨C,hC,h⟩ := P.exists_uniform_clear_chart_fractions a f hf
    exact (isAdmissible_of_forall_mul_chartDen hC h).mem_sections

end EnvelopeProperty.MultiModel
