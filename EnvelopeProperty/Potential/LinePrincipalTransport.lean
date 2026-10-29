import EnvelopeProperty.Potential.LineInverseRestrictions
import EnvelopeProperty.Potential.LineFiniteHoleDomains
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Whole actual principal transport through strict original hole containment -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] {m n : ℕ}
variable (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)

omit [IsAlgClosed K] in
theorem principal_closure_zero (j : Fin m) : (0 : U.AnalyticFunctions) ∈ closure (U.rationalComponentSet (some j)) := by
  rw [← U.range_analyticComponent]
  exact ⟨0,map_zero _⟩

omit [IsAlgClosed K] in
theorem principal_closure_add (j : Fin m) (f g : U.AnalyticFunctions)
    (hf : f ∈ closure (U.rationalComponentSet (some j)))
    (hg : g ∈ closure (U.rationalComponentSet (some j))) :
    f+g ∈ closure (U.rationalComponentSet (some j)) := by
  rw [← U.range_analyticComponent] at hf hg ⊢
  obtain ⟨a,rfl⟩ := hf
  obtain ⟨b,rfl⟩ := hg
  exact ⟨a+b,map_add _ _ _⟩

omit [IsAlgClosed K] in
theorem principal_closure_coefficient_mul (j : Fin m) (a : K) (f : U.AnalyticFunctions)
    (hf : f ∈ closure (U.rationalComponentSet (some j))) :
    algebraMap K U.AnalyticFunctions a*f ∈ closure (U.rationalComponentSet (some j)) := by
  rw [← U.range_analyticComponent] at hf ⊢
  obtain ⟨g,rfl⟩ := hf
  exact ⟨algebraMap K U.AnalyticFunctions a*g,U.analyticComponent_coefficient_mul (some j) a g⟩

omit [IsAlgClosed K] [IsUltrametricDist K] in
private theorem degree_mul_lt_add (p q : K[X]) (a b : ℕ) (hp : p.degree < a) (hq : q.degree < b) :
    (p*q).degree < ((a+b : ℕ) : WithBot ℕ) := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro k hk
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  have hsum : x.1+x.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  by_cases ha : a ≤ x.1
  · rw [(Polynomial.degree_lt_iff_coeff_zero _ _).mp hp _ ha,zero_mul]
  · have hb : b ≤ x.2 := by omega
    rw [(Polynomial.degree_lt_iff_coeff_zero _ _).mp hq _ hb,mul_zero]

omit [IsAlgClosed K] in
/-- The WHOLE completed principal closure is an actual nonunital subalgebra. -/
theorem principal_closure_mul (j : Fin m) (f g : U.AnalyticFunctions)
    (hf : f ∈ closure (U.rationalComponentSet (some j)))
    (hg : g ∈ closure (U.rationalComponentSet (some j))) :
    f*g ∈ closure (U.rationalComponentSet (some j)) := by
  have hbase (a : U.AnalyticFunctions) (ha : a ∈ U.rationalComponentSet (some j))
      (b : U.AnalyticFunctions) (hb : b ∈ U.rationalComponentSet (some j)) :
      a*b ∈ closure (U.rationalComponentSet (some j)) := by
    obtain ⟨p,k,hp,rfl⟩ := ha
    obtain ⟨q,l,hq,rfl⟩ := hb
    apply subset_closure
    refine ⟨p*q,k+l,degree_mul_lt_add p q k l hp hq,?_⟩
    simp only [properRationalPart,map_mul,pow_add]
    ring
  have hleft (a : U.AnalyticFunctions) (ha : a ∈ U.rationalComponentSet (some j)) :
      ∀ b ∈ closure (U.rationalComponentSet (some j)),
        a*b ∈ closure (U.rationalComponentSet (some j)) :=
    closure_minimal (hbase a ha) (isClosed_closure.preimage (continuous_const.mul continuous_id))
  exact closure_minimal (fun a ha => hleft a ha g hg)
    (isClosed_closure.preimage (continuous_id.mul continuous_const)) hf

omit [IsAlgClosed K] in
theorem principal_closure_pow_succ (j : Fin m) (f : U.AnalyticFunctions)
    (hf : f ∈ closure (U.rationalComponentSet (some j))) (k : ℕ) :
    f^(k+1) ∈ closure (U.rationalComponentSet (some j)) := by
  induction k with
  | zero => simpa only [zero_add,pow_one] using hf
  | succ k ih => rw [pow_succ]; exact U.principal_closure_mul j _ _ ih hf

omit [IsAlgClosed K] in
theorem principal_closure_inverse_pow (j : Fin m) (k : ℕ) :
    (U.rationalMap (U.rationalHoleInverse j))^(k+1) ∈ closure (U.rationalComponentSet (some j)) := by
  apply subset_closure
  refine ⟨1,k+1,?_,?_⟩
  · simpa only [Polynomial.degree_one] using (show (0 : WithBot ℕ) < ((k+1 : ℕ) : WithBot ℕ) from by exact_mod_cast Nat.succ_pos k)
  · simp only [properRationalPart,map_one,one_mul,map_pow]

omit [IsAlgClosed K] in
theorem principal_closure_sum {ι : Type*} (j : Fin m) (s : Finset ι) (f : ι → U.AnalyticFunctions)
    (hf : ∀ i ∈ s, f i ∈ closure (U.rationalComponentSet (some j))) :
    ∑ i ∈ s, f i ∈ closure (U.rationalComponentSet (some j)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using U.principal_closure_zero j
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact U.principal_closure_add j _ _ (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

/-- EVERY actual inverse with centre strictly in the ORIGINAL open hole is a WHOLE original principal limit. -/
theorem inverse_mem_principal_closure (j : Fin m) (a : K)
    (ha : ‖a-U.holeCenter j‖₊ < U.holeRadius j) (t : U.AnalyticFunctions)
    (ht : U.polynomialAnalyticMap (X-C a)*t = 1) :
    t ∈ closure (U.rationalComponentSet (some j)) := by
  let z := U.rationalMap (U.rationalHoleInverse j)
  let c := algebraMap K U.AnalyticFunctions (a-U.holeCenter j)
  let e := c*z
  have hdz : U.polynomialAnalyticMap (X-C (U.holeCenter j))*z = 1 := by
    simpa only [map_mul,map_one,polynomialAnalyticMap,RingHom.comp_apply,z] using
      congrArg U.rationalMap (U.holeCoordinate_mul_rationalHoleInverse j)
  have hpoly : U.polynomialAnalyticMap (X-C a) =
      U.polynomialAnalyticMap (X-C (U.holeCenter j))-c := by
    change U.polynomialAnalyticMap (X-C a) =
      U.polynomialAnalyticMap (X-C (U.holeCenter j))-U.polynomialAnalyticMap (C (a-U.holeCenter j))
    rw [← map_sub]
    congr 1
    rw [map_sub]
    ring
  have hlin : t = z+e*t := by
    calc
      t = (U.polynomialAnalyticMap (X-C (U.holeCenter j))*z)*t := by rw [hdz,one_mul]
      _ = z*((U.polynomialAnalyticMap (X-C (U.holeCenter j))-c)*t)+e*t := by dsimp [e]; ring
      _ = z+e*t := by rw [← hpoly,ht,mul_one]
  have hnz : ‖z‖₊ = (U.holeRadius j)⁻¹ := by
    have h := U.nnnorm_inverseRationalPolynomial j X
    simpa only [inverseRationalPolynomial,Polynomial.aeval_X,gaussFun_X] using h
  have he : ‖e‖ < 1 := by
    have hn : ‖e‖₊ ≤ ‖a-U.holeCenter j‖₊*(U.holeRadius j)⁻¹ := by
      exact (nnnorm_mul_le c z).trans_eq (by rw [U.nnnorm_algebraMap_analyticFunctions,hnz,NormedField.valuation_apply])
    have hb : ‖a-U.holeCenter j‖₊*(U.holeRadius j)⁻¹ < 1 := by
      exact (mul_inv_lt_iff₀ (U.holeRadius_pos j)).mpr (by simpa using ha)
    exact_mod_cast hn.trans_lt hb
  have hsum (N : ℕ) : ∑ k ∈ Finset.range N, e^k*z = t-e^N*t := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ,ih,pow_succ]
      linear_combination -(e^N)*hlin
  have hlim : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, e^k*z) atTop (𝓝 t) := by
    have h := (tendsto_const_nhds (x := t) (f := atTop (α := ℕ))).sub
      ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one he).mul_const t)
    simpa only [hsum,zero_mul,sub_zero] using h
  apply isClosed_closure.mem_of_tendsto hlim
  apply Eventually.of_forall
  intro N
  apply U.principal_closure_sum j
  intro k _
  have hterm : e^k*z = algebraMap K U.AnalyticFunctions ((a-U.holeCenter j)^k)*z^(k+1) := by
    dsimp [e,c]
    rw [map_pow,mul_pow,pow_succ]
    ring
  rw [hterm]
  exact U.principal_closure_coefficient_mul j _ _ (U.principal_closure_inverse_pow j k)

variable (W : FCStandardAffinoid (NormedField.valuation (K := K)) n)
variable (hWU : W.carrier ⊆ U.carrier)

/-- WHOLE actual principal transport allows DIFFERENT original centres under strict open-hole containment. -/
theorem analyticRestriction_principal_closure_of_hole_subset (i : Fin m) (j : Fin n)
    (hholes : fcOpenLinearDisc (w := NormedField.valuation (K := K)) (U.holeCenter i) (U.holeRadius i) ⊆
      fcOpenLinearDisc (W.holeCenter j) (W.holeRadius j))
    (f : U.AnalyticFunctions) (hf : f ∈ closure (U.rationalComponentSet (some i))) :
    U.analyticRestriction W hWU f ∈ closure (W.rationalComponentSet (some j)) := by
  have hc : ‖U.holeCenter i-W.holeCenter j‖₊ < W.holeRadius j := by
    have hx : centeredGauss (self (NormedField.valuation (K := K))) (U.holeCenter i) 0 ∈
        fcOpenLinearDisc (U.holeCenter i) (U.holeRadius i) := by
      simpa only [fcOpenLinearDisc,Set.mem_ofPred_eq,fc_centeredGauss_val_X_sub_C,sub_self,
        map_zero,max_self] using U.holeRadius_pos i
    have h := hholes hx
    have he : W.holeCenter j-U.holeCenter i = -(U.holeCenter i-W.holeCenter j) := by ring
    simpa only [fcOpenLinearDisc,Set.mem_ofPred_eq,fc_centeredGauss_val_X_sub_C,
      NormedField.valuation_apply,max_zero,he,nnnorm_neg] using h
  let t := U.analyticRestriction W hWU (U.rationalMap (U.rationalHoleInverse i))
  have ht : W.polynomialAnalyticMap (X-C (U.holeCenter i))*t = 1 := by
    have h := congrArg (U.analyticRestriction W hWU)
      (congrArg U.rationalMap (U.holeCoordinate_mul_rationalHoleInverse i))
    simp only [map_mul,map_one] at h
    change U.analyticRestriction W hWU (U.polynomialAnalyticMap (X-C (U.holeCenter i)))*t = 1 at h
    rwa [U.analyticRestriction_polynomial W hWU] at h
  have htmem := W.inverse_mem_principal_closure j (U.holeCenter i) hc t ht
  have hsub : U.rationalComponentSet (some i) ⊆
      {g | U.analyticRestriction W hWU g ∈ closure (W.rationalComponentSet (some j))} := by
    rintro g ⟨p,k,hp,rfl⟩
    change U.analyticRestriction W hWU (U.rationalMap (U.properRationalPart p i k)) ∈
      closure (W.rationalComponentSet (some j))
    rw [U.properRationalPart_eq_inversePolynomial p i k hp]
    simp only [inverseRationalPolynomial,inversePrincipalPolynomial,map_sum,Polynomial.aeval_monomial,
      map_mul,map_pow,U.rationalMap_original_coefficient,U.analyticRestriction_algebraMap]
    apply W.principal_closure_sum j
    intro l hl
    have hkl : 0 < k-l := Nat.sub_pos_of_lt (Finset.mem_range.mp hl)
    have he : k-l = (k-l-1)+1 := by omega
    rw [he]
    exact W.principal_closure_coefficient_mul j _ _ (W.principal_closure_pow_succ j t htmem _)
  exact closure_minimal hsub (isClosed_closure.preimage (U.continuous_analyticRestriction W hWU)) hf

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
