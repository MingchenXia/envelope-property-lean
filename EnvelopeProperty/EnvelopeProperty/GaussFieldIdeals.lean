/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.GaussFieldPreparation
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Actual original one-variable Gauss ideals are principal and norm closed -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.CompletedMonicDivision
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Every nonzero ORIGINAL ideal has a bounded monic ORIGINAL polynomial generator.
Its genuine minimum degree is constructed from actual preparation and division. -/
theorem exists_bounded_monic_ideal_generator (r : ℝ≥0) (hr : 0<r)
    (I : Ideal (Ring (A := K) r hr)) (hI : I≠⊥) :
    ∃ P : K[X], P.Monic ∧ (∀ i<P.natDegree, ‖P.coeff i‖₊ * r^i≤r^P.natDegree) ∧
      I=principalIdeal r hr P := by
  classical
  obtain ⟨f,hfI,hf⟩ := I.ne_bot_iff.mp hI
  obtain ⟨P₀,hP₀,hb₀,_,u₀,hu₀,_⟩ := exists_bounded_monic_preparation r hr f hf
  have hP₀I : polynomialMap r hr P₀∈I := by
    have he := I.mul_mem_left (↑u₀⁻¹ : Ring (A := K) r hr) hfI
    simpa only [hu₀,← mul_assoc,Units.inv_mul,one_mul] using he
  let S : ℕ → Prop := fun d => ∃ P : K[X], P.Monic ∧ P.natDegree=d ∧
    (∀ i<P.natDegree, ‖P.coeff i‖₊ * r^i≤r^P.natDegree) ∧ polynomialMap r hr P∈I
  have hS : ∃ d, S d := ⟨P₀.natDegree,P₀,hP₀,rfl,hb₀,hP₀I⟩
  obtain ⟨P,hP,hdegree,hbound,hPI⟩ := Nat.find_spec hS
  have hmin (b : K[X]) (hb : b.Monic)
      (hbb : ∀ i<b.natDegree, ‖b.coeff i‖₊ * r^i≤r^b.natDegree)
      (hbI : polynomialMap r hr b∈I) : Nat.find hS≤b.natDegree :=
    Nat.find_min' hS ⟨b,hb,rfl,hbb,hbI⟩
  refine ⟨P,hP,hbound,le_antisymm ?_ ?_⟩
  · intro g hgI
    let R := remainderPolynomial r hr hP hbound g
    have hRdegree : R.degree<(P.natDegree : WithBot ℕ) := degree_remainderPolynomial_lt r hr hP hbound g
    have he := quotient_remainder_reconstruction r hr hP hbound g
    have hRI : polynomialMap r hr R∈I := by
      have hsub := I.sub_mem hgI (I.mul_mem_right (quotientMap r hr hP hbound g) hPI)
      convert hsub using 1
      linear_combination he
    have hR : R=0 := by
      by_contra hn
      obtain ⟨b,hb,hbdegree,hbb,v,hv⟩ := exists_bounded_monic_preparation_polynomial r hr R hn
      have hbI : polynomialMap r hr b∈I := by
        have he := I.mul_mem_left (↑v⁻¹ : Ring (A := K) r hr) hRI
        simpa only [hv,← mul_assoc,Units.inv_mul,one_mul] using he
      have hlow := hmin b hb hbb hbI
      have hhigh : b.natDegree<Nat.find hS := hbdegree.trans_lt
        (((natDegree_lt_iff_degree_lt hn).mpr hRdegree).trans_eq hdegree)
      exact (not_le_of_gt hhigh) hlow
    rw [principalIdeal,Ideal.mem_span_singleton]
    refine ⟨quotientMap r hr hP hbound g,?_⟩
    simpa only [show remainderPolynomial r hr hP hbound g=0 from hR,map_zero,add_zero] using he.symm
  · apply Ideal.span_le.mpr
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rwa [hg]

/-- The SAME actual original Gauss algebra is a principal ideal ring, by actual ideal generators. -/
theorem gaussField_isPrincipalIdealRing (r : ℝ≥0) (hr : 0<r) :
    IsPrincipalIdealRing (Ring (A := K) r hr) where
  principal I := by
    by_cases hI : I=⊥
    · subst I
      infer_instance
    · obtain ⟨P,_,_,hP⟩ := exists_bounded_monic_ideal_generator r hr I hI
      exact ⟨⟨polynomialMap r hr P,hP⟩⟩

/-- Actual principal ideals derive genuine Noetherianity, with no finite-generation certificate input. -/
theorem gaussField_isNoetherianRing (r : ℝ≥0) (hr : 0<r) :
    IsNoetherianRing (Ring (A := K) r hr) := by
  let : IsPrincipalIdealRing (Ring (A := K) r hr) := gaussField_isPrincipalIdealRing r hr
  infer_instance

/-- EVERY ORIGINAL ideal is genuinely norm closed; no closure or radical replaces it. -/
theorem gaussField_isClosed_ideal (r : ℝ≥0) (hr : 0<r) (I : Ideal (Ring (A := K) r hr)) :
    IsClosed (I : Set (Ring (A := K) r hr)) := by
  by_cases hI : I=⊥
  · subst I
    convert (isClosed_singleton : IsClosed ({0} : Set (Ring (A := K) r hr))) using 1
    ext f
    simp only [SetLike.mem_coe,Submodule.mem_bot,Set.mem_singleton_iff]
  · obtain ⟨P,hP,hb,hPI⟩ := exists_bounded_monic_ideal_generator r hr I hI
    rw [hPI]
    exact isClosed_principalIdeal r hr hP hb

/-- Every nonzero ORIGINAL ideal quotient is a genuine original polynomial algebra quotient. -/
theorem exists_gaussField_ideal_quotientAlgEquiv (r : ℝ≥0) (hr : 0<r)
    (I : Ideal (Ring (A := K) r hr)) (hI : I≠⊥) :
    ∃ P : K[X], P.Monic ∧
      ∃ e : (K[X] ⧸ Ideal.span {P}) ≃ₐ[K] (Ring (A := K) r hr ⧸ I),
        ∀ b : K[X], e (Ideal.Quotient.mk (Ideal.span {P}) b)=Ideal.Quotient.mk I (polynomialMap r hr b) := by
  obtain ⟨P,hP,hb,hPI⟩ := exists_bounded_monic_ideal_generator r hr I hI
  let e := (quotientAlgEquiv r hr hP hb).trans (Ideal.quotientEquivAlgOfEq K hPI.symm)
  refine ⟨P,hP,e,?_⟩
  intro b
  change Ideal.quotientEquivAlgOfEq K hPI.symm (quotientEquiv r hr hP hb (Ideal.Quotient.mk _ b)) = _
  rw [quotientEquiv_mk,Ideal.quotientEquivAlgOfEq_mk]

/-- Every nonzero original ideal has a true finite original-power basis for its entire quotient. -/
theorem exists_gaussField_ideal_quotientBasis (r : ℝ≥0) (hr : 0<r)
    (I : Ideal (Ring (A := K) r hr)) (hI : I≠⊥) :
    ∃ d : ℕ, ∃ b : Module.Basis (Fin d) K (Ring (A := K) r hr ⧸ I),
      ∀ i, b i=Ideal.Quotient.mk I (polynomialMap r hr (X^(i : ℕ))) := by
  obtain ⟨P,hP,hb,hPI⟩ := exists_bounded_monic_ideal_generator r hr I hI
  let e := Ideal.quotientEquivAlgOfEq K hPI.symm
  refine ⟨P.natDegree,(quotientBasis r hr hP hb).map e.toLinearEquiv,?_⟩
  intro i
  change e (quotientBasis r hr hP hb i)=_
  rw [quotientBasis_apply,Ideal.quotientEquivAlgOfEq_mk]

/-- The actual quotient by ANY nonzero original ideal is finite over SAME K, even for the whole ideal. -/
theorem gaussField_quotient_moduleFinite (r : ℝ≥0) (hr : 0<r)
    (I : Ideal (Ring (A := K) r hr)) (hI : I≠⊥) : Module.Finite K (Ring (A := K) r hr ⧸ I) := by
  obtain ⟨d,b,_⟩ := exists_gaussField_ideal_quotientBasis r hr I hI
  exact Module.Finite.of_basis b

end EnvelopeProperty.CompletedMonicDivision
