import EnvelopeProperty.Potential.LinePrincipalTransport
import Mathlib.Topology.Algebra.Ring.Basic

/-! # Whole polynomial transport from original holes outside the target outer disc -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] {m n : ℕ}
variable (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)

omit [IsAlgClosed K] in
/-- The actual polynomial closure is the topological closure of the ORIGINAL polynomial ring image. -/
def polynomialClosureSubring : Subring U.AnalyticFunctions := U.polynomialAnalyticMap.range.topologicalClosure

omit [IsAlgClosed K] in
theorem mem_polynomialClosureSubring_iff (f : U.AnalyticFunctions) :
    f ∈ U.polynomialClosureSubring ↔ f ∈ closure (U.rationalComponentSet none) := Iff.rfl

omit [IsAlgClosed K] in
/-- Every WHOLE actual inverse whose original centre is outside the actual outer disc is a polynomial limit. -/
theorem inverse_mem_polynomial_closure (a : K) (ha : U.radius < ‖a-U.center‖₊)
    (t : U.AnalyticFunctions) (ht : U.polynomialAnalyticMap (X-C a)*t = 1) :
    t ∈ closure (U.rationalComponentSet none) := by
  let δ := U.center-a
  have hδ : δ ≠ 0 := by
    intro h
    have he : a-U.center = 0 := by dsimp [δ] at h; linear_combination -h
    have hbad := ha
    rw [he,nnnorm_zero] at hbad
    exact not_lt_of_ge zero_le hbad
  let b := algebraMap K U.AnalyticFunctions δ⁻¹
  let d := U.polynomialAnalyticMap (X-C U.center)
  let e := -b*d
  have hδnorm : ‖δ‖₊ = ‖a-U.center‖₊ := by
    have he : δ = -(a-U.center) := by dsimp [δ]; ring
    rw [he,nnnorm_neg]
  have hpoly : U.polynomialAnalyticMap (X-C a) =
      d+algebraMap K U.AnalyticFunctions δ := by
    change U.polynomialAnalyticMap (X-C a) =
      U.polynomialAnalyticMap (X-C U.center)+U.polynomialAnalyticMap (C δ)
    rw [← map_add]
    congr 1
    dsimp [δ]
    rw [map_sub]
    ring
  have hbδ : b*algebraMap K U.AnalyticFunctions δ = 1 := by
    dsimp [b]
    rw [← map_mul,inv_mul_cancel₀ hδ,map_one]
  have hlin : t = b+e*t := by
    calc
      t = (b*algebraMap K U.AnalyticFunctions δ)*t := by rw [hbδ,one_mul]
      _ = b*((d+algebraMap K U.AnalyticFunctions δ)*t)+e*t := by dsimp [e]; ring
      _ = b+e*t := by rw [← hpoly,ht,mul_one]
  have hnd : ‖d‖₊ = U.radius := by
    have h := U.nnnorm_outerTranslatedPolynomial X
    have hp : Polynomial.algEquivAevalXAddC (-U.center) X = X-C U.center := by
      simp [Polynomial.algEquivAevalXAddC]
      ring
    simpa only [hp,gaussFun_X] using h
  have he : ‖e‖ < 1 := by
    have hn : ‖e‖₊ ≤ (‖δ‖₊)⁻¹*U.radius := by
      dsimp [e]
      exact (nnnorm_mul_le (-b) d).trans_eq (by
        rw [nnnorm_neg,U.nnnorm_algebraMap_analyticFunctions,NormedField.valuation_apply,nnnorm_inv,hnd])
    have hb : (‖δ‖₊)⁻¹*U.radius < 1 := by
      rw [mul_comm]
      exact (mul_inv_lt_iff₀ (nnnorm_pos.mpr hδ)).mpr (by simpa only [one_mul,hδnorm] using ha)
    exact_mod_cast hn.trans_lt hb
  have hsum (N : ℕ) : ∑ k ∈ Finset.range N, e^k*b = t-e^N*t := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ,ih,pow_succ]
      linear_combination -(e^N)*hlin
  have hlim : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, e^k*b) atTop (𝓝 t) := by
    have h := (tendsto_const_nhds (x := t) (f := atTop (α := ℕ))).sub
      ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one he).mul_const t)
    simpa only [hsum,zero_mul,sub_zero] using h
  apply isClosed_closure.mem_of_tendsto hlim
  apply Eventually.of_forall
  intro N
  let q : K[X] := ∑ k ∈ Finset.range N, (-C δ⁻¹*(X-C U.center))^k*C δ⁻¹
  apply subset_closure
  refine ⟨q,?_⟩
  simp only [q,map_sum,map_mul,map_pow,map_neg]
  rfl

variable (W : FCStandardAffinoid (NormedField.valuation (K := K)) n)
variable (hWU : W.carrier ⊆ U.carrier)

/-- Disjointness from the ACTUAL target outer disc sends the WHOLE original principal closure to the polynomial closure. -/
theorem analyticRestriction_principal_closure_of_hole_disjoint_outer (i : Fin m)
    (hdisj : Disjoint
      (fcOpenLinearDisc (w := NormedField.valuation (K := K)) (U.holeCenter i) (U.holeRadius i))
      (fcClosedLinearDisc W.center W.radius))
    (f : U.AnalyticFunctions) (hf : f ∈ closure (U.rationalComponentSet (some i))) :
    U.analyticRestriction W hWU f ∈ closure (W.rationalComponentSet none) := by
  have hc : W.radius < ‖U.holeCenter i-W.center‖₊ := by
    apply lt_of_not_ge
    intro hbad
    let x := centeredGauss (self (NormedField.valuation (K := K))) (U.holeCenter i) 0
    have hxH : x ∈ fcOpenLinearDisc (U.holeCenter i) (U.holeRadius i) := by
      simpa only [x,fcOpenLinearDisc,Set.mem_ofPred_eq,fc_centeredGauss_val_X_sub_C,sub_self,
        map_zero,max_self] using U.holeRadius_pos i
    have hxD : x ∈ fcClosedLinearDisc W.center W.radius := by
      have he : W.center-U.holeCenter i = -(U.holeCenter i-W.center) := by ring
      simpa only [x,fcClosedLinearDisc,Set.mem_ofPred_eq,fc_centeredGauss_val_X_sub_C,
        NormedField.valuation_apply,max_zero,he,nnnorm_neg] using hbad
    exact Set.disjoint_left.mp hdisj hxH hxD
  let t := U.analyticRestriction W hWU (U.rationalMap (U.rationalHoleInverse i))
  have ht : W.polynomialAnalyticMap (X-C (U.holeCenter i))*t = 1 := by
    have h := congrArg (U.analyticRestriction W hWU)
      (congrArg U.rationalMap (U.holeCoordinate_mul_rationalHoleInverse i))
    simp only [map_mul,map_one] at h
    change U.analyticRestriction W hWU (U.polynomialAnalyticMap (X-C (U.holeCenter i)))*t = 1 at h
    rwa [U.analyticRestriction_polynomial W hWU] at h
  have htmem : t ∈ W.polynomialClosureSubring := W.inverse_mem_polynomial_closure (U.holeCenter i) hc t ht
  have hsub : U.rationalComponentSet (some i) ⊆
      {g | U.analyticRestriction W hWU g ∈ closure (W.rationalComponentSet none)} := by
    rintro g ⟨p,k,hp,rfl⟩
    change U.analyticRestriction W hWU (U.rationalMap (U.properRationalPart p i k)) ∈
      W.polynomialClosureSubring
    rw [U.properRationalPart_eq_inversePolynomial p i k hp]
    simp only [inverseRationalPolynomial,inversePrincipalPolynomial,map_sum,Polynomial.aeval_monomial,
      map_mul,map_pow,U.rationalMap_original_coefficient,U.analyticRestriction_algebraMap]
    apply W.polynomialClosureSubring.sum_mem
    intro l _
    apply W.polynomialClosureSubring.mul_mem
    · apply subset_closure
      exact ⟨C (p.coeff l),rfl⟩
    · exact W.polynomialClosureSubring.pow_mem htmem _
  exact closure_minimal hsub (isClosed_closure.preimage (U.continuous_analyticRestriction W hWU)) hf
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
