/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.PolynomialRetractionFibres

open scoped Polynomial NNReal Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {v : Valuation R ℝ≥0}

/-- Translate whole original polynomial points by the actual original algebra automorphism. -/
def polynomialTranslation (a : A) : RelativeSpectrum v A[X] ≃ₜ RelativeSpectrum v A[X] where
  toFun := comap ((Polynomial.algEquivAevalXAddC a).toAlgHom.restrictScalars R)
  invFun := comap ((Polynomial.algEquivAevalXAddC a).symm.toAlgHom.restrictScalars R)
  left_inv x := by
    apply ext_val
    intro p
    change val x (Polynomial.algEquivAevalXAddC a ((Polynomial.algEquivAevalXAddC a).symm p)) =
      val x p
    rw [AlgEquiv.apply_symm_apply]
  right_inv x := by
    apply ext_val
    intro p
    change val x ((Polynomial.algEquivAevalXAddC a).symm (Polynomial.algEquivAevalXAddC a p)) =
      val x p
    rw [AlgEquiv.symm_apply_apply]
  continuous_toFun := continuous_comap _
  continuous_invFun := continuous_comap _

/-- EVERY original polynomial is evaluated by its actual original translated polynomial. -/
theorem polynomialTranslation_val_apply (a : A) (x : RelativeSpectrum v A[X]) (p : A[X]) :
    val (polynomialTranslation a x) p = val x (Polynomial.algEquivAevalXAddC a p) := rfl

/-- The true inverse point map is translation by the original additive inverse. -/
theorem polynomialTranslation_symm_apply (a : A) (x : RelativeSpectrum v A[X]) :
    (polynomialTranslation a).symm x = polynomialTranslation (-a) x := by
  change comap ((Polynomial.algEquivAevalXAddC a).symm.toAlgHom.restrictScalars R) x = _
  rw [Polynomial.algEquivAevalXAddC_symm]
  rfl

/-- The translation fixes the ENTIRE original coefficient point, not only its prescribed R values. -/
theorem proj_polynomialTranslation (a : A) (x : RelativeSpectrum v A[X]) :
    proj (polynomialTranslation a x) = proj x := by
  apply ext_val
  intro c
  change val x (Polynomial.algEquivAevalXAddC a (C c)) = val x (C c)
  simp [Polynomial.algEquivAevalXAddC]

/-- The exact centred coordinate value after translation is the original coordinate value. -/
theorem polynomialTranslation_val_X_sub_C (a : A) (x : RelativeSpectrum v A[X]) :
    val (polynomialTranslation a x) (X - C a) = val x X := by
  rw [polynomialTranslation_val_apply]
  have h : Polynomial.algEquivAevalXAddC a (X - C a) = X := by
    simp [Polynomial.algEquivAevalXAddC]
  rw [h]

/-- The genuine strict disc centred at an ORIGINAL coefficient in the WHOLE prescribed fibre. -/
abbrev CenteredFibreOpenDisc (y : RelativeSpectrum v A) (a : A) (r : ℝ≥0) :=
  {x : RelativeSpectrum v A[X] // proj x = y ∧ val x (X - C a) < r}

namespace FibreOpenDisc

/-- Actual whole polynomial translation identifies the original zero-centred and centred strict discs. -/
def centeredHomeomorph (y : RelativeSpectrum v A) (a : A) (r : ℝ≥0) :
    FibreOpenDisc y r ≃ₜ CenteredFibreOpenDisc y a r where
  toFun x := ⟨polynomialTranslation a x.1,
    (proj_polynomialTranslation a x.1).trans x.2.1, by
      rw [polynomialTranslation_val_X_sub_C]
      exact x.2.2⟩
  invFun x := ⟨(polynomialTranslation a).symm x.1, by
    rw [polynomialTranslation_symm_apply]
    exact (proj_polynomialTranslation (-a) x.1).trans x.2.1, by
      rw [polynomialTranslation_symm_apply, polynomialTranslation_val_apply]
      have h : Polynomial.algEquivAevalXAddC (-a) (X : A[X]) = X - C a := by
        simp [Polynomial.algEquivAevalXAddC, sub_eq_add_neg]
      rw [h]
      exact x.2.2⟩
  left_inv x := Subtype.ext ((polynomialTranslation a).symm_apply_apply x.1)
  right_inv x := Subtype.ext ((polynomialTranslation a).apply_symm_apply x.1)
  continuous_toFun := ((polynomialTranslation a).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((polynomialTranslation a).symm.continuous.comp continuous_subtype_val).subtype_mk _

end FibreOpenDisc
namespace CenteredFibreOpenDisc

/-- Every actual positive-radius centred strict fibre disc is contractible over arbitrary original rings. -/
theorem contractibleSpace (y : RelativeSpectrum v A) (a : A) (r : ℝ≥0) (hr : 0 < r) :
    ContractibleSpace (CenteredFibreOpenDisc y a r) := by
  let := FibreOpenDisc.contractibleSpace y r hr
  exact (FibreOpenDisc.centeredHomeomorph y a r).symm.contractibleSpace

end CenteredFibreOpenDisc
end EnvelopeProperty.Berkovich.RelativeSpectrum
