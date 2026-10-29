import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsParameterCharts
import EnvelopeProperty.Char0.MultiplierFamilySmoothnessCoordinates

/-! # Every original polynomial keeps its SAME original dehomogenization and parameter -/

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
open ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The actual quotient-polynomial map keeps every original coefficient. -/
theorem quotientPolynomialAlgEquiv_mk {A : Type u} [CommRing A] [Algebra k A]
    (I : Ideal A) (F : A[X]) :
    quotientPolynomialAlgEquiv (k := k) I (Ideal.Quotient.mk _ F) = F.map (Ideal.Quotient.mk I) :=
  Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk I F

/-- The actual whole family quotient equivalence has its original explicit
coefficient-interchange, quotient and old-chart formula. -/
theorem familyCoordinateQuotientEquiv_mk (j : Fin (M + 1))
    (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal)
    (F : CoordinateRing k[X] j) :
    familyCoordinateQuotientEquiv X j hj (Ideal.Quotient.mk _ F) =
      ((chartParameterEquiv j F).map
        (Ideal.Quotient.mk (X.ideal.map (coordinateDehom j).toRingHom))).map
          (Char0.MultiplierFamilySmoothness.coordinateQuotientEquiv X j hj).toRingHom := by
  rw [familyCoordinateQuotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlg_mk,
    AlgEquiv.trans_apply, quotientPolynomialAlgEquiv_mk]
  rfl

private def primitiveQuotDehom (j : Fin (M + 1)) :
    MvPolynomial (Fin (M + 1)) k →ₐ[k] QuotChartAlg X.ideal (MvPolynomial.X j) 1 :=
  (Ideal.Quotient.mkₐ k (chartIdeal X.ideal (MvPolynomial.X j) 1)).comp
    (MvPolynomial.aeval fun i => chartMk (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) 1 1 (MvPolynomial.X i))

private theorem primitiveQuotDehom_apply (j : Fin (M + 1)) (s : MvPolynomial (Fin (M + 1)) k) :
    primitiveQuotDehom X j s = X.quotDehom j s := rfl

/-- The SAME original native coordinate quotient sends every original
coefficient polynomial to its actual old dehomogenization. -/
theorem coordinateQuotientEquiv_mk_dehom (j : Fin (M + 1))
    (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal)
    (s : MvPolynomial (Fin (M + 1)) k) :
    Char0.MultiplierFamilySmoothness.coordinateQuotientEquiv X j hj
      (Ideal.Quotient.mk _ (coordinateDehom j s)) = X.quotDehom j s := by
  let E := Char0.MultiplierFamilySmoothness.coordinateQuotientEquiv X j hj
  have h : (E.toAlgHom.comp (Ideal.Quotient.mkₐ k (X.ideal.map (coordinateDehom j).toRingHom))).comp
      (coordinateDehom j) = primitiveQuotDehom X j := by
    apply MvPolynomial.algHom_ext
    intro i
    have hh := Char0.MultiplierFamilySmoothness.coordinateQuotientEquiv_mk_homogeneous X j hj
      (MvPolynomial.isHomogeneous_X k i)
    simpa only [E, primitiveQuotDehom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      Ideal.Quotient.mkₐ_eq_mk, MvPolynomial.aeval_X, quotChartMk] using hh
  exact (AlgHom.congr_fun h s).trans (primitiveQuotDehom_apply X j s)

/-- The actual whole family quotient keeps the SAME original parameter
and coefficient polynomial for every original polynomial, not just homogeneous forms. -/
theorem familyCoordinateQuotientEquiv_parameterDehom (j : Fin (M + 1))
    (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal)
    (g : (MvPolynomial (Fin (M + 1)) k)[X]) :
    familyCoordinateQuotientEquiv X j hj
      (Ideal.Quotient.mk _ (coordinateDehom j (parameterEquiv g))) =
      g.map (X.quotDehom j).toRingHom := by
  induction g using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg, Polynomial.map_add]
  | monomial l s =>
      rw [familyCoordinateQuotientEquiv_mk, parameterEquiv_monomial]
      simp only [map_mul, coordinateDehom_map, chartParameterEquiv_map_C,
        Polynomial.map_mul, Polynomial.map_C]
      have ht : chartParameterEquiv (k := k) j
          (coordinateDehom j (MvPolynomial.C ((Polynomial.X : k[X]) ^ l))) =
          (Polynomial.X : (CoordinateRing k j)[X]) ^ l := by
        simp [coordinateDehom, chartParameterEquiv, polynomialCoefficientSwap_C]
      rw [ht]
      simp only [Polynomial.map_pow, Polynomial.map_X, Polynomial.map_monomial,
        Polynomial.C_mul_X_pow_eq_monomial]
      apply congrArg (Polynomial.monomial l)
      exact coordinateQuotientEquiv_mk_dehom X j hj s

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
