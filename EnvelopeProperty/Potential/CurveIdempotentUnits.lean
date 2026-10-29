import EnvelopeProperty.Potential.ProjectiveNormUnits
import EnvelopeProperty.Potential.CurveIdempotentNorm
import EnvelopeProperty.Potential.CurveAnalyticRestrictions

/-! # Genuine local units in the actual analytic idempotent quotient -/

open scoped NNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m n : ℕ}
variable (U : FCStandardAffinoid w m)

/-- Nonzero actual value produces an actual unit on a genuine smaller neighbourhood. -/
theorem exists_standardAffinoid_isUnit_restriction (f : U.AnalyticFunctions)
    (x : RelativeSpectrum w K[X]) (hx : x ∈ interior U.carrier)
    (hf : U.analyticValue f ⟨x,interior_subset hx⟩ ≠ 0) :
    ∃ n : ℕ, ∃ V : FCStandardAffinoid w n, ∃ _hxV : x ∈ interior V.carrier,
      ∃ hVU : V.carrier ⊆ U.carrier, IsUnit (U.analyticRestriction V hVU f) := by
  have hnear : {y : U.carrier | U.analyticValue f y ≠ 0} ∈ 𝓝 ⟨x,interior_subset hx⟩ :=
    (isOpen_ne.preimage (U.continuous_analyticValue f)).mem_nhds hf
  rw [nhds_subtype_eq_comap] at hnear
  obtain ⟨N,hN,hsub⟩ := hnear
  obtain ⟨n,V,hxV,hVN⟩ := fc_exists_standardAffinoid_nhds x
    (Filter.inter_mem hN (isOpen_interior.mem_nhds hx))
  let hVU : V.carrier ⊆ U.carrier := fun y hy => interior_subset (hVN hy).2
  refine ⟨n,V,hxV,hVU,(V.analyticFunctions_isUnit_iff _).mpr ?_⟩
  intro y
  rw [U.analyticValue_analyticRestriction V hVU]
  exact hsub (hVN y.2).1

variable {B ι : Type*} [CommRing B] [Algebra K[X] B] [Fintype ι]
variable (V : FCStandardAffinoid w n) (hVU : V.carrier ⊆ U.carrier)

/-- Genuine WHOLE curve tensor base change along actual analytic restriction. -/
def curveAnalyticRestrictionTensorEquiv :
    let := (U.analyticRestriction V hVU).toAlgebra
    V.AnalyticFunctions ⊗[U.AnalyticFunctions] U.CurveAnalyticTensor B ≃ₐ[V.AnalyticFunctions]
      V.CurveAnalyticTensor B := by
  let := (U.analyticRestriction V hVU).toAlgebra
  let : IsScalarTower K[X] U.AnalyticFunctions V.AnalyticFunctions :=
    IsScalarTower.of_algebraMap_eq (fun p => ((U.polynomialAnalyticRestriction V hVU).commutes p).symm)
  exact Algebra.TensorProduct.cancelBaseChange K[X] U.AnalyticFunctions
    V.AnalyticFunctions V.AnalyticFunctions B

theorem curveAnalyticRestrictionTensorEquiv_one_tmul (z : U.CurveAnalyticTensor B) :
    let := (U.analyticRestriction V hVU).toAlgebra
    U.curveAnalyticRestrictionTensorEquiv V hVU ((1 : V.AnalyticFunctions) ⊗ₜ[U.AnalyticFunctions] z) =
      U.curveAnalyticRestriction V hVU z := by
  let := (U.analyticRestriction V hVU).toAlgebra
  induction z using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero,map_zero]
  | add a b ha hb => simp only [TensorProduct.tmul_add,map_add,ha,hb]
  | tmul a b =>
    simp only [curveAnalyticRestrictionTensorEquiv,Algebra.TensorProduct.cancelBaseChange_tmul,
      curveAnalyticRestriction,Algebra.TensorProduct.map_tmul,AlgHom.id_apply]
    change (U.analyticRestriction V hVU a*1) ⊗ₜ[K[X]] b = _
    rw [mul_one]
    rfl

/-- Actual scalar summand norm commutes with arbitrary actual carrier restriction. -/
theorem analyticRestriction_curveIdempotentNorm (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (b : B) :
    U.analyticRestriction V hVU (U.curveIdempotentNorm basis he b) =
      V.curveIdempotentNorm basis (he.map (U.curveAnalyticNormedRestriction V hVU basis)) b := by
  let := (U.analyticRestriction V hVU).toAlgebra
  let := Module.Free.of_basis (U.curveAnalyticBasis basis)
  let := Module.Finite.of_basis (U.curveAnalyticBasis basis)
  let := Module.Free.of_basis (V.curveAnalyticBasis basis)
  let := Module.Finite.of_basis (V.curveAnalyticBasis basis)
  let h := he.map (U.curveAnalyticOriginalEquiv basis)
  let g := U.curveAnalyticRestrictionTensorEquiv (B := B) V hVU
  change U.analyticRestriction V hVU (IdempotentSummand.norm (R := U.AnalyticFunctions) h
    ((1 : U.AnalyticFunctions) ⊗ₜ[K[X]] b)) =
      IdempotentSummand.norm (R := V.AnalyticFunctions)
        (h.map (U.curveAnalyticRestriction V hVU)) ((1 : V.AnalyticFunctions) ⊗ₜ[K[X]] b)
  have hb := IdempotentSummand.norm_baseChange (R := U.AnalyticFunctions)
    (S := V.AnalyticFunctions) h ((1 : U.AnalyticFunctions) ⊗ₜ[K[X]] b)
  have hg := IdempotentSummand.norm_algEquiv (R := V.AnalyticFunctions) g
    (h.map (Algebra.TensorProduct.includeRight : U.CurveAnalyticTensor B →ₐ[U.AnalyticFunctions]
      V.AnalyticFunctions ⊗[U.AnalyticFunctions] U.CurveAnalyticTensor B))
    ((1 : V.AnalyticFunctions) ⊗ₜ[U.AnalyticFunctions] ((1 : U.AnalyticFunctions) ⊗ₜ[K[X]] b))
  exact hb.symm.trans (by
    simpa only [g,h,Algebra.TensorProduct.includeRight_apply,
      curveAnalyticRestrictionTensorEquiv_one_tmul,curveAnalyticRestriction,
      Algebra.TensorProduct.map_tmul,map_one,AlgHom.id_apply] using hg.symm)

omit [IsAlgClosed K] in
/-- The genuine analytic norm detects an ACTUAL unit in the original quotient summand. -/
theorem isUnit_curveIdempotentQuotient_iff (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (b : B) :
    IsUnit (IdempotentSummand.quotient (R := U.AnalyticFunctions)
      (U.curveAnalyticOriginalEquiv basis e) ((1 : U.AnalyticFunctions) ⊗ₜ[K[X]] b)) ↔
      IsUnit (U.curveIdempotentNorm basis he b) := by
  let := Module.Free.of_basis (U.curveAnalyticBasis basis)
  let := Module.Finite.of_basis (U.curveAnalyticBasis basis)
  let := IdempotentSummand.finite (R := U.AnalyticFunctions) (U.curveAnalyticOriginalEquiv basis e)
  let := IdempotentSummand.projective (R := U.AnalyticFunctions)
    (he.map (U.curveAnalyticOriginalEquiv basis))
  exact (isUnit_projectiveNorm_iff _).symm

/-- Original nonvanishing on the actual central piece CONSTRUCTS an actual quotient
unit after shrinking. Even the empty selected piece is included, with norm one. -/
theorem exists_standardAffinoid_isUnit_idempotentQuotient (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (b : B)
    (x : RelativeSpectrum w K[X]) (hx : x ∈ interior U.carrier)
    (hb : let := Module.Finite.of_basis basis
      ∀ y ∈ Spectrum.completedIdempotentFibrePiece x.1
        (U.curveIdempotentSpecialization basis e ⟨x,interior_subset hx⟩), y.1.val b ≠ 0) :
    ∃ n : ℕ, ∃ V : FCStandardAffinoid w n, ∃ _hxV : x ∈ interior V.carrier,
      ∃ hVU : V.carrier ⊆ U.carrier,
        IsUnit (IdempotentSummand.quotient (R := V.AnalyticFunctions)
          (V.curveAnalyticOriginalEquiv basis (U.curveAnalyticNormedRestriction V hVU basis e))
          ((1 : V.AnalyticFunctions) ⊗ₜ[K[X]] b)) := by
  let := Module.Finite.of_basis basis
  have hnorm : U.analyticValue (U.curveIdempotentNorm basis he b) ⟨x,interior_subset hx⟩ ≠ 0 := by
    change NormedField.valuation (U.evaluationToH ⟨x,interior_subset hx⟩
      (U.curveIdempotentNorm basis he b)) ≠ 0
    rw [U.valuation_evaluation_curveIdempotentNorm basis he b]
    exact Finset.prod_ne_zero_iff.mpr (fun y hy => pow_ne_zero _ (hb y hy))
  obtain ⟨n,V,hxV,hVU,hunit⟩ := U.exists_standardAffinoid_isUnit_restriction
    (U.curveIdempotentNorm basis he b) x hx hnorm
  rw [U.analyticRestriction_curveIdempotentNorm V hVU basis he b] at hunit
  exact ⟨n,V,hxV,hVU,
    (V.isUnit_curveIdempotentQuotient_iff basis (he.map (U.curveAnalyticNormedRestriction V hVU basis)) b).mpr hunit⟩

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
