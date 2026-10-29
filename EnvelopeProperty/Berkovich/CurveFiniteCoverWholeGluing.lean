/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.LineFiniteCoverWholeGluing
import EnvelopeProperty.Potential.CurveAnalyticRestrictions

open scoped NNReal Polynomial TensorProduct
open Polynomial
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

section Restriction
variable {K B ι : Type*} [Field K] [IsAlgClosed K] [CommRing B] [Algebra K[X] B]
  [Fintype ι] {w : Valuation K ℝ≥0} {m n : ℕ}
variable (U : FCStandardAffinoid w m) (V : FCStandardAffinoid w n)
  (hVU : V.carrier ⊆ U.carrier) (basis : Module.Basis ι K[X] B)

/-- EVERY original tensor-basis coefficient commutes with the SAME whole restriction. -/
theorem curveAnalyticRestriction_coefficient (z : U.CurveAnalyticTensor B) (k : ι) :
    (V.curveAnalyticBasis basis).equivFun (U.curveAnalyticRestriction V hVU z) k =
      U.analyticRestriction V hVU ((U.curveAnalyticBasis basis).equivFun z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul r b =>
    rw [U.curveAnalyticRestriction_tmul, V.curveAnalyticBasis_coefficient_tmul,
      U.curveAnalyticBasis_coefficient_tmul, map_mul, U.analyticRestriction_polynomial]
  | add z t hz ht => simp only [map_add, Pi.add_apply, hz, ht]

private theorem curveNormedRestriction_coefficient (z : U.CurveAnalyticAlgebra basis) (k : ι) :
    (V.curveAnalyticBasis basis).equivFun
        (V.curveAnalyticOriginalEquiv basis (U.curveAnalyticNormedRestriction V hVU basis z)) k =
      U.analyticRestriction V hVU
        ((U.curveAnalyticBasis basis).equivFun (U.curveAnalyticOriginalEquiv basis z) k) :=
  U.curveAnalyticRestriction_coefficient V hVU basis _ k
end Restriction

section Cover
variable {K B ι J : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K]
  [CommRing B] [Algebra K[X] B] [Fintype ι] [Fintype J] {m : ℕ} {n : J → ℕ}
variable (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)
  (V : ∀ j, FCStandardAffinoid (NormedField.valuation (K := K)) (n j))
  (hVU : ∀ j, (V j).carrier ⊆ U.carrier)
  (hcover : ∀ x ∈ U.carrier, ∃ j, x ∈ (V j).carrier)
  (basis : Module.Basis ι K[X] B)

include hcover in
omit [Fintype J] in
private theorem curveCover_joint_injective {a b : U.CurveAnalyticAlgebra basis}
    (h : ∀ j, U.curveAnalyticNormedRestriction (V j) (hVU j) basis a =
      U.curveAnalyticNormedRestriction (V j) (hVU j) basis b) : a = b := by
  apply (U.curveAnalyticOriginalEquiv basis).injective
  apply (U.curveAnalyticBasis basis).equivFun.injective
  funext k
  apply U.analyticFunctions_eq_of_cover_restrictions_eq V hVU hcover
  intro j
  have he := congrArg (fun z => (V j).curveAnalyticBasis basis |>.equivFun
    ((V j).curveAnalyticOriginalEquiv basis z) k) (h j)
  simpa only [curveNormedRestriction_coefficient] using he

include hcover in
/-- Genuine SAME whole-fibre compatibility constructs a UNIQUE whole original curve glue,
with the exact joint norm of EACH original basis coefficient. -/
theorem exists_unique_curve_finite_cover_glue
    (f : ∀ j, (V j).CurveAnalyticAlgebra basis)
    (hcompat : ∀ i j x (hi : x ∈ (V i).carrier) (hj : x ∈ (V j).carrier),
      (V i).curveAnalyticNormedSpecialization basis ⟨x, hi⟩ (f i) =
        (V j).curveAnalyticNormedSpecialization basis ⟨x, hj⟩ (f j)) :
    ∃! g : U.CurveAnalyticAlgebra basis,
      (∀ j, U.curveAnalyticNormedRestriction (V j) (hVU j) basis g = f j) ∧
      ∀ k, ‖(U.curveAnalyticBasis basis).equivFun (U.curveAnalyticOriginalEquiv basis g) k‖₊ =
        Finset.univ.sup (fun j => ‖(V j).curveAnalyticBasis basis |>.equivFun
          ((V j).curveAnalyticOriginalEquiv basis (f j)) k‖₊) := by
  classical
  let c (j : J) : ι → (V j).AnalyticFunctions :=
    (V j).curveAnalyticBasis basis |>.equivFun ((V j).curveAnalyticOriginalEquiv basis (f j))
  have hc (k : ι) : ∀ i j x (hi : x ∈ (V i).carrier) (hj : x ∈ (V j).carrier),
      (V i).evaluationToH ⟨x, hi⟩ (c i k) = (V j).evaluationToH ⟨x, hj⟩ (c j k) := by
    intro i j x hi hj
    have he := congrArg (fun z : FiniteFreeAnalyticCopy (basis.baseChange x.1.H) =>
      (basis.baseChange x.1.H).equivFun
        (FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.H) z) k)
      (hcompat i j x hi hj)
    change (basis.baseChange x.1.H).equivFun
        ((V i).curveAnalyticSpecialization ⟨x, hi⟩ ((V i).curveAnalyticOriginalEquiv basis (f i))) k =
      (basis.baseChange x.1.H).equivFun
        ((V j).curveAnalyticSpecialization ⟨x, hj⟩ ((V j).curveAnalyticOriginalEquiv basis (f j))) k at he
    exact ((V i).curveAnalyticSpecialization_coefficient basis ⟨x, hi⟩ _ k).symm.trans
      (he.trans ((V j).curveAnalyticSpecialization_coefficient basis ⟨x, hj⟩ _ k))
  have hex (k : ι) : ∃ a : U.AnalyticFunctions,
      (∀ j, U.analyticRestriction (V j) (hVU j) a = c j k) ∧
        ‖a‖₊ = Finset.univ.sup (fun j => ‖c j k‖₊) :=
    (U.exists_unique_finite_cover_glue V hVU hcover (fun j => c j k) (hc k)).exists
  choose a ha using hex
  let g : U.CurveAnalyticAlgebra basis :=
    (U.curveAnalyticOriginalEquiv basis).symm ((U.curveAnalyticBasis basis).equivFun.symm a)
  have hgc (k : ι) :
      (U.curveAnalyticBasis basis).equivFun (U.curveAnalyticOriginalEquiv basis g) k = a k := by
    simp only [g, AlgEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hg (j : J) : U.curveAnalyticNormedRestriction (V j) (hVU j) basis g = f j := by
    apply ((V j).curveAnalyticOriginalEquiv basis).injective
    apply ((V j).curveAnalyticBasis basis).equivFun.injective
    funext k
    rw [curveNormedRestriction_coefficient, hgc]
    exact (ha k).1 j
  refine ⟨g, ⟨hg, fun k => ?_⟩, fun b hb => ?_⟩
  · rw [hgc]
    exact (ha k).2
  · exact U.curveCover_joint_injective V hVU hcover basis (fun j => (hb.1 j).trans (hg j).symm)

/-- The LITERAL original subring of whole curve families matching in EVERY original fibre. -/
def curveAnalyticCompatibleFamilies : Subring (∀ j, (V j).CurveAnalyticAlgebra basis) where
  carrier := {f | ∀ i j x (hi : x ∈ (V i).carrier) (hj : x ∈ (V j).carrier),
    (V i).curveAnalyticNormedSpecialization basis ⟨x, hi⟩ (f i) =
      (V j).curveAnalyticNormedSpecialization basis ⟨x, hj⟩ (f j)}
  zero_mem' := by intro i j x hi hj; exact (map_zero _).trans (map_zero _).symm
  one_mem' := by intro i j x hi hj; exact (map_one _).trans (map_one _).symm
  add_mem' := by intro f g hf hg i j x hi hj; rw [Pi.add_apply, Pi.add_apply, map_add, map_add, hf i j x hi hj, hg i j x hi hj]
  mul_mem' := by intro f g hf hg i j x hi hj; rw [Pi.mul_apply, Pi.mul_apply, map_mul, map_mul, hf i j x hi hj, hg i j x hi hj]
  neg_mem' := by intro f hf i j x hi hj; rw [Pi.neg_apply, Pi.neg_apply, map_neg, map_neg, hf i j x hi hj]

private def curveCompatibleRestriction :
    U.CurveAnalyticAlgebra basis →+* curveAnalyticCompatibleFamilies V basis := by
  let r : U.CurveAnalyticAlgebra basis →+* (∀ j, (V j).CurveAnalyticAlgebra basis) :=
    { toFun := fun a j => U.curveAnalyticNormedRestriction (V j) (hVU j) basis a
      map_one' := funext (fun j => map_one _)
      map_zero' := funext (fun j => map_zero _)
      map_add' := fun a b => funext (fun j => map_add _ a b)
      map_mul' := fun a b => funext (fun j => map_mul _ a b) }
  exact r.codRestrict (curveAnalyticCompatibleFamilies V basis) (by
    intro a i j x hi hj
    change (V i).curveAnalyticNormedSpecialization basis ⟨x, hi⟩
        (U.curveAnalyticNormedRestriction (V i) (hVU i) basis a) =
      (V j).curveAnalyticNormedSpecialization basis ⟨x, hj⟩
        (U.curveAnalyticNormedRestriction (V j) (hVU j) basis a)
    rw [U.curveAnalyticNormedRestriction_specialization, U.curveAnalyticNormedRestriction_specialization])

/-- The SAME original whole curve restriction is a ring equivalence onto its actual matching subring. -/
def curveAnalyticCoverRestrictionEquiv :
    U.CurveAnalyticAlgebra basis ≃+* curveAnalyticCompatibleFamilies V basis :=
  RingEquiv.ofBijective (curveCompatibleRestriction U V hVU basis) (by
    constructor
    · intro a b h
      exact U.curveCover_joint_injective V hVU hcover basis
        (fun j => congrArg (fun f : curveAnalyticCompatibleFamilies V basis => f.1 j) h)
    · intro f
      obtain ⟨g, hg, _⟩ := U.exists_unique_curve_finite_cover_glue V hVU hcover basis f.1 f.2
      exact ⟨g, Subtype.ext (funext fun j => hg.1 j)⟩)

end Cover
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
