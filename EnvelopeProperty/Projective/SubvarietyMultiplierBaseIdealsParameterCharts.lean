import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsGeometry
import EnvelopeProperty.Char0.MultiplierFamilySmoothnessChartAlgebra
import EnvelopeProperty.PolynomialCoefficientSwap
import Mathlib.RingTheory.Polynomial.Quotient

/-! # The ACTUAL original family coordinate quotient is the SAME original chart polynomial ring -/

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

/-- The actual whole polynomial interchange on the SAME original complementary coordinates. -/
def chartParameterEquiv (j : Fin (M + 1)) : CoordinateRing k[X] j ≃ₐ[k] (CoordinateRing k j)[X] :=
  polynomialCoefficientSwap k (ChartIndex j)

/-- An original coordinate polynomial is retained coefficientwise by the actual interchange. -/
theorem chartParameterEquiv_map_C (j : Fin (M + 1)) (F : CoordinateRing k j) :
    chartParameterEquiv j (MvPolynomial.map (Polynomial.C : k →+* k[X]) F) = Polynomial.C F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [chartParameterEquiv]
  | add F G hF hG => simp only [map_add, hF, hG]
  | mul_X F i hF =>
      simp only [map_mul, MvPolynomial.map_X, chartParameterEquiv, polynomialCoefficientSwap_X]
      rw [show polynomialCoefficientSwap k (ChartIndex j)
        (MvPolynomial.map (Polynomial.C : k →+* k[X]) F) = Polynomial.C F from hF]

/-- The ENTIRE original defining coordinate ideal is exactly its true polynomial extension. -/
theorem familyCoordinateIdeal_map (j : Fin (M + 1)) :
    (((familyHomogeneousIdeal X).toIdeal.map (coordinateDehom j).toRingHom).map
      (chartParameterEquiv (k := k) j).toRingHom) =
      (X.ideal.map (coordinateDehom j).toRingHom).map
        (Polynomial.C : CoordinateRing k j →+* (CoordinateRing k j)[X]) := by
  change ((X.ideal.map (MvPolynomial.map (Polynomial.C : k →+* k[X]))).map
    (coordinateDehom j).toRingHom).map _ = _
  rw [Ideal.map_map, Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro F
  change chartParameterEquiv j (coordinateDehom j (MvPolynomial.map Polynomial.C F)) =
    Polynomial.C (coordinateDehom j F)
  rw [coordinateDehom_map, chartParameterEquiv_map_C]

/-- The genuine polynomial quotient equivalence retains the SAME original base-field algebra. -/
def quotientPolynomialAlgEquiv {A : Type u} [CommRing A] [Algebra k A] (I : Ideal A) :
    (A[X] ⧸ (I.map (Polynomial.C : A →+* A[X]) : Ideal A[X])) ≃ₐ[k] (A ⧸ I)[X] := by
  refine { (Ideal.polynomialQuotientEquivQuotientPolynomial I).symm with commutes' := ?_ }
  intro a
  change (Ideal.polynomialQuotientEquivQuotientPolynomial I).symm
    (Ideal.Quotient.mk _ (Polynomial.C (algebraMap k A a))) =
      Polynomial.C (Ideal.Quotient.mk I (algebraMap k A a))
  rw [Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk, Polynomial.map_C]

/-- The WHOLE actual parameter-family coordinate quotient is the polynomial
ring of the SAME old original chart; every ideal is internally compared. -/
def familyCoordinateQuotientEquiv (j : Fin (M + 1))
    (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal) :
    (CoordinateRing k[X] j ⧸ (familyHomogeneousIdeal X).toIdeal.map (coordinateDehom j).toRingHom) ≃ₐ[k]
      (QuotChartAlg X.ideal (MvPolynomial.X j) 1)[X] :=
  (Ideal.quotientEquivAlg _ _ (chartParameterEquiv (k := k) j) (familyCoordinateIdeal_map X j).symm).trans
    ((quotientPolynomialAlgEquiv (k := k) (X.ideal.map (coordinateDehom j).toRingHom)).trans
      (Polynomial.mapAlgEquiv (Char0.MultiplierFamilySmoothness.coordinateQuotientEquiv X j hj)))

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
