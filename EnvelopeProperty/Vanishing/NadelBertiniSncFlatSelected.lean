import EnvelopeProperty.Vanishing.NadelBertiniSncFlatPolynomial

/-! # Actual good parameters give regular ORIGINAL selected chart coefficients

The universal regular equation and its actual localized quotient flatness are
produced internally. The whole original polynomial-fibre evaluation transports
regularity to the SAME original selected linear-combination coefficient.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniSncFlatSelected
open NadelBertiniLinearSmooth NadelBertiniSncFlatPolynomial
variable {k C : Type u} [Field k] [CommRing C] [Algebra k C]
  {S : Type} [Fintype S] [DecidableEq S]

/-- A SAME actual original good parameter internally gives a nonzerodivisor
for the SAME original selected local linear equation, through the ACTUAL global
incidence quotient chart and its exact ORIGINAL coefficient triangle. -/
theorem selectedEquation_regular_of_globalGoodOpen {Y : Scheme.{u}}
    (F : Y ⟶ Spec (.of (MvPolynomial S k))) [LocallyOfFinitePresentation F] [IsProper F]
    (c : S → C) (j : S) (hj : c j = 1) (a : S → k)
    (ν : Spec (.of (MvPolynomial S C ⧸ Ideal.span {linearForm c})) ⟶ Y)
    [IsOpenImmersion ν]
    (hν : ν ≫ F = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {linearForm c})).comp
        (coefficientMap (k := k) (C := C)))))
    (ha : Spec.map (CommRingCat.ofHom (MvPolynomial.eval a)) (⊥ : PrimeSpectrum k) ∈
      NadelBertiniGenericOpen.goodOpen F) :
    IsSMulRegular C (∑ i, algebraMap k C (a i) * c i) := by
  let : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
    (coefficientMap (k := k) (C := C)).toAlgebra
  let : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
  have hν' : ν ≫ F = NadelBertiniSncFlatAffine.quotientStructure
      (MvPolynomial S k) (linearForm c) := hν
  have hreg : IsSMulRegular (k ⊗[MvPolynomial S k] MvPolynomial S C)
      ((1 : k) ⊗ₜ[MvPolynomial S k] linearForm c) :=
    NadelBertiniSncFlatAffine.tensor_regular_of_globalGoodOpen (MvPolynomial S k)
      F (linearForm c) (NadelBertiniSncLinearRegular.linearForm_regular c j hj)
      ν hν' (MvPolynomial.eval a) ha
  let e := fibreEvaluationIso (C := C) a
  have he : e ((1 : k) ⊗ₜ[MvPolynomial S k] linearForm c) =
      ∑ i, algebraMap k C (a i) * c i := fibreEvaluationIso_linearForm a c
  change Function.Injective (fun z : C => (∑ i, algebraMap k C (a i) * c i) * z)
  intro z z' hzz'
  apply e.symm.injective
  apply hreg
  apply e.injective
  simpa only [smul_eq_mul, map_mul, he, e.apply_symm_apply] using hzz'

end EnvelopeProperty.Vanishing.NadelBertiniSncFlatSelected
