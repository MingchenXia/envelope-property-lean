import EnvelopeProperty.Local.PLIdealParameterScaling
import EnvelopeProperty.Projective.NormalizedCoefficientMap

/-! # Full actual parameter-monomial ideal norms at arbitrary relative points -/
open scoped Classical Polynomial NNReal ENNReal Topology
open AlgebraicGeometry
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
variable {R : Type u} [CommRing R] (v : Valuation R ℝ≥0) (r : ℝ≥0) {n : ℕ}

/-- Every actual parameter-monomial value is computed from the whole original
coefficient-restricted point. No Gauss-extension hypothesis on the point. -/
theorem val_parameterMonomial
    (x : RelativeNormalizedProjectiveSpectrum (gaussValuation v r) n)
    (F : MvPolynomial (Fin (n + 1)) R) (e : ℕ) :
    x.1.1.val (parameterMonomial F e) =
      (polynomialRestriction v r x).1.1.val F * r ^ e := by
  rw [parameterMonomial, map_mul, x.2]
  change x.1.1.val (MvPolynomial.map Polynomial.C F) *
    (Spectrum.gauss (Spectrum.ofValuation v) r).val (Polynomial.X ^ e) = _
  rw [map_pow, Spectrum.gauss_val_X]
  rfl

private local instance nativeModelProper :
    IsProper (ProjBerk.nativeStructureMap (R := R[X]) (n := n)) :=
  ProjBerk.nativeStructureMap_isProper

/-- The TRUE proper-center model norm of a finite parameter-monomial
homogeneous ideal is the explicit original finite maximum, at EVERY genuine
relative point over the prescribed Gauss base, including zero generators. -/
theorem modelIdealNorm_parameterMonomial_span
    (hb : ∀ p : R[X], gaussValuation v r p ≤ 1)
    (J : HomogeneousIdeal (ProjBerk.ProjectiveGrading R[X] n))
    (S : Finset (MvPolynomial (Fin (n + 1)) R × ℕ))
    (hS : J.toIdeal = Ideal.span ((fun p => parameterMonomial p.1 p.2) ''
      (S : Set (MvPolynomial (Fin (n + 1)) R × ℕ))))
    (x : RelativeNormalizedProjectiveSpectrum (gaussValuation v r) n) :
    RelativeSchemeValuedPoint.modelIdealNorm (ProjBerk.nativeHomogeneousIdealSheaf J)
      hb (nativeHomeomorph (gaussValuation v r) x) =
      ((S.sup fun p => (polynomialRestriction v r x).1.1.val p.1 * r ^ p.2 : ℝ≥0) : ℝ≥0∞) := by
  rw [modelIdealNorm_quotient_eq_idealNorm, hS]
  have he : (fun p : MvPolynomial (Fin (n + 1)) R × ℕ => parameterMonomial p.1 p.2) ''
      (S : Set (MvPolynomial (Fin (n + 1)) R × ℕ)) =
      ((S.image fun p => parameterMonomial p.1 p.2) : Set (MvPolynomial (Fin (n + 1)) R[X])) :=
    (Finset.coe_image).symm
  rw [he, Spectrum.idealNorm_span_finset (isBounded_polynomial _ hb x), Finset.sup_image]
  congr 1
  exact Finset.sup_congr rfl (fun p _ => val_parameterMonomial v r x p.1 p.2)
/-- The SAME true original ideal norm at an ARBITRARY relative point equals
its value at the actual Gauss extension of the original coefficient restriction.
This is proved from actual monomial generators, not inferred from Gauss values. -/
theorem modelIdealNorm_parameterMonomial_eq_GaussRestriction
    (hb : ∀ p : R[X], gaussValuation v r p ≤ 1)
    (J : HomogeneousIdeal (ProjBerk.ProjectiveGrading R[X] n))
    (S : Finset (MvPolynomial (Fin (n + 1)) R × ℕ))
    (hS : J.toIdeal = Ideal.span ((fun p => parameterMonomial p.1 p.2) ''
      (S : Set (MvPolynomial (Fin (n + 1)) R × ℕ))))
    (x : RelativeNormalizedProjectiveSpectrum (gaussValuation v r) n) :
    RelativeSchemeValuedPoint.modelIdealNorm (ProjBerk.nativeHomogeneousIdealSheaf J)
      hb (nativeHomeomorph (gaussValuation v r) x) =
    RelativeSchemeValuedPoint.modelIdealNorm (ProjBerk.nativeHomogeneousIdealSheaf J)
      hb (nativeHomeomorph (gaussValuation v r)
        (polynomialGauss v (polynomialRestriction v r x) r)) := by
  rw [modelIdealNorm_parameterMonomial_span v r hb J S hS,
    modelIdealNorm_parameterMonomial_span v r hb J S hS,
    polynomialRestriction_polynomialGauss]

/-- The full true-center logarithm has the same actual Gauss-restriction
identity, including negative infinity, without a nonvanishing assumption. -/
theorem modelIdealLog_parameterMonomial_eq_GaussRestriction
    (hb : ∀ p : R[X], gaussValuation v r p ≤ 1)
    (J : HomogeneousIdeal (ProjBerk.ProjectiveGrading R[X] n))
    (S : Finset (MvPolynomial (Fin (n + 1)) R × ℕ))
    (hS : J.toIdeal = Ideal.span ((fun p => parameterMonomial p.1 p.2) ''
      (S : Set (MvPolynomial (Fin (n + 1)) R × ℕ))))
    (x : RelativeNormalizedProjectiveSpectrum (gaussValuation v r) n) :
    RelativeSchemeValuedPoint.modelIdealLog (ProjBerk.nativeHomogeneousIdealSheaf J)
      hb (nativeHomeomorph (gaussValuation v r) x) =
    RelativeSchemeValuedPoint.modelIdealLog (ProjBerk.nativeHomogeneousIdealSheaf J)
      hb (nativeHomeomorph (gaussValuation v r)
        (polynomialGauss v (polynomialRestriction v r x) r)) :=
  congrArg ENNReal.log (modelIdealNorm_parameterMonomial_eq_GaussRestriction v r hb J S hS x)

end EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
