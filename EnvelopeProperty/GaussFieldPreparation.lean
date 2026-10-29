/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.DistinguishedGaussFunctions
import Mathlib.Data.Set.Finite.Lemmas

/-! # Genuine preparation for every nonzero one-variable Gauss function over SAME complete field -/
open scoped NNReal Polynomial Topology
open Polynomial UniformSpace Topology Filter
noncomputable section
namespace EnvelopeProperty.CompletedMonicDivision
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem exists_highest_of_cofinite (c : ℕ → ℝ≥0) (hc : Tendsto c cofinite (𝓝 0))
    (hpos : ∃ i, 0<c i) : ∃ d, 0<c d ∧ (∀ i, c i≤c d) ∧ ∀ i>d, c i<c d := by
  classical
  obtain ⟨i,hi⟩ := hpos
  have he : ∀ᶠ j in cofinite, c j<c i := hc.eventually (gt_mem_nhds hi)
  have hs : {j | ¬c j<c i}.Finite := eventually_cofinite.mp he
  obtain ⟨n,hn,hmax⟩ := Set.exists_max_image {j | ¬c j<c i} c hs ⟨i,lt_irrefl _⟩
  have hall : ∀ j, c j≤c n := by
    intro j
    by_cases hj : c j<c i
    · exact hj.le.trans (hmax i (lt_irrefl _))
    · exact hmax j hj
  have hcn : 0<c n := hi.trans_le (hall i)
  have hE : {j | c j=c n}.Finite := hs.subset (by
    intro j hj
    rw [Set.mem_ofPred_eq] at hj ⊢
    rw [hj]
    exact not_lt_of_ge (hall i))
  obtain ⟨d,hd,hdmax⟩ := Set.exists_max_image {j | c j=c n} id hE ⟨n,rfl⟩
  refine ⟨d,hd ▸ hcn,fun j => (hall j).trans_eq hd.symm,?_⟩
  intro j hj
  apply lt_of_le_of_ne ((hall j).trans_eq hd.symm)
  intro hje
  have hm : j≤d := hdmax j (hje.trans hd)
  exact (not_le_of_gt hj) hm

/-- A genuine highest ORIGINAL coefficient attains the WHOLE completed norm for every nonzero function. -/
theorem exists_highest_functionCoefficient (r : ℝ≥0) (hr : 0<r)
    (f : Ring (A := K) r hr) (hf : f≠0) :
    ∃ d : ℕ, functionCoefficient r hr d f≠0 ∧
      ‖functionCoefficient r hr d f‖₊ * r^d=‖f‖₊ ∧
      (∀ i, ‖functionCoefficient r hr i f‖₊ * r^i≤‖functionCoefficient r hr d f‖₊ * r^d) ∧
      ∀ i>d, ‖functionCoefficient r hr i f‖₊ * r^i<‖functionCoefficient r hr d f‖₊ * r^d := by
  have hp : ∃ i, 0<‖functionCoefficient r hr i f‖₊ * r^i := by
    by_contra hn
    push Not at hn
    have hz : ‖f‖₊≤0 := (nnnorm_le_iff_functionCoefficient r hr f 0).mpr hn
    exact hf (nnnorm_eq_zero.mp (le_antisymm hz zero_le))
  obtain ⟨d,hd,hall,hstrict⟩ := exists_highest_of_cofinite _ (tendsto_weighted_functionCoefficient r hr f) hp
  refine ⟨d,?_,?_,hall,hstrict⟩
  · intro hz
    simp only [hz,nnnorm_zero,zero_mul,lt_self_iff_false] at hd
  · apply le_antisymm
    · exact (nnnorm_le_iff_functionCoefficient r hr f ‖f‖₊).mp le_rfl d
    · exact (nnnorm_le_iff_functionCoefficient r hr f _).mpr hall

/-- Every nonzero actual completed function DERIVES its genuine SAME-K monic preparation.
The original coefficient at the constructed monic degree is nonzero, retaining polynomial degree control. -/
theorem exists_bounded_monic_preparation (r : ℝ≥0) (hr : 0<r)
    (f : Ring (A := K) r hr) (hf : f≠0) :
    ∃ P : K[X], P.Monic ∧
      (∀ i<P.natDegree, ‖P.coeff i‖₊ * r^i≤r^P.natDegree) ∧
      functionCoefficient r hr P.natDegree f≠0 ∧
      ∃ u : (Ring (A := K) r hr)ˣ, f=(u : Ring (A := K) r hr)*polynomialMap r hr P ∧
        ∀ P' : K[X], P'.Monic → P'.natDegree=P.natDegree → ∀ v : (Ring (A := K) r hr)ˣ,
          f=(v : Ring (A := K) r hr)*polynomialMap r hr P' → P'=P ∧ v=u := by
  obtain ⟨d,hd,_,hall,hstrict⟩ := exists_highest_functionCoefficient r hr f hf
  let a := Units.mk0 (functionCoefficient r hr d f) hd
  have hna : 0<‖functionCoefficient r hr d f‖₊ := nnnorm_pos.mpr hd
  have hvalue (i : ℕ) : ‖(↑a⁻¹ : K)*functionCoefficient r hr i f‖₊ * r^i =
      (‖functionCoefficient r hr i f‖₊ * r^i)/‖functionCoefficient r hr d f‖₊ := by
    simp only [a,Units.val_inv_eq_inv_val,Units.val_mk0,nnnorm_mul,nnnorm_inv]
    ring
  have hlower : ∀ i<d, ‖(↑a⁻¹ : K)*functionCoefficient r hr i f‖₊ * r^i≤r^d := by
    intro i _
    rw [hvalue]
    exact (div_le_iff₀ hna).mpr (by simpa only [mul_comm] using hall i)
  have htail : ∀ i>d, ‖(↑a⁻¹ : K)*functionCoefficient r hr i f‖₊ * r^i<r^d := by
    intro i hi
    rw [hvalue]
    exact (div_lt_iff₀ hna).mpr (by simpa only [mul_comm] using hstrict i hi)
  obtain ⟨P,hP,hdeg,hb,u,hfP,huniq⟩ := exists_preparation_of_coefficients r hr f d a rfl hlower htail
  refine ⟨P,hP,hb,?_,u,hfP,?_⟩
  · rwa [hdeg]
  · intro P' hP' hd' v hv
    exact huniq P' hP' (hd'.trans hdeg) v hv

/-- For an ORIGINAL nonzero polynomial the derived bounded monic factor has no larger original degree. -/
theorem exists_bounded_monic_preparation_polynomial (r : ℝ≥0) (hr : 0<r)
    (b : K[X]) (hb : b≠0) :
    ∃ P : K[X], P.Monic ∧ P.natDegree≤b.natDegree ∧
      (∀ i<P.natDegree, ‖P.coeff i‖₊ * r^i≤r^P.natDegree) ∧
      ∃ u : (Ring (A := K) r hr)ˣ,
        polynomialMap r hr b=(u : Ring (A := K) r hr)*polynomialMap r hr P := by
  have hmb : polynomialMap r hr b≠0 := by
    intro he
    apply hb
    exact (polynomialMap_injective r hr) (he.trans (map_zero _).symm)
  obtain ⟨P,hP,hbound,hcoeff,u,hu,_⟩ := exists_bounded_monic_preparation r hr (polynomialMap r hr b) hmb
  rw [functionCoefficient_polynomialMap] at hcoeff
  exact ⟨P,hP,le_natDegree_of_ne_zero hcoeff,hbound,u,hu⟩

omit [CompleteSpace K] in
/-- The SAME actual Gauss completion is nontrivial by its genuine original coefficient injection. -/
theorem gaussField_nontrivial (r : ℝ≥0) (hr : 0<r) : Nontrivial (Ring (A := K) r hr) :=
  ((polynomialMap_injective (A := K) r hr).comp C_injective).nontrivial

/-- Genuine actual preparation and bounded-monic multiplication DERIVE the original Gauss algebra domain. -/
theorem gaussField_isDomain (r : ℝ≥0) (hr : 0<r) : IsDomain (Ring (A := K) r hr) := by
  let : Nontrivial (Ring (A := K) r hr) := gaussField_nontrivial r hr
  let : NoZeroDivisors (Ring (A := K) r hr) := ⟨by
    intro f g hfg
    by_cases hf : f=0
    · exact Or.inl hf
    · obtain ⟨P,hP,hbound,_,u,hu,_⟩ := exists_bounded_monic_preparation r hr f hf
      have hPg : polynomialMap r hr P*g=0 := by
        apply u.isUnit.mul_left_cancel
        simpa only [← mul_assoc,← hu,mul_zero] using hfg
      right
      exact (normalForm_unique r hr hP hbound g 0 0 0 (by simp) (by simp)
        (by simpa only [map_zero,add_zero,mul_zero] using hPg)).1⟩
  exact {}

end EnvelopeProperty.CompletedMonicDivision
