import EnvelopeProperty.AlgGeom.SchemeModuleLaurentCoefficients

/-! # Actual evaluations of the entire original Laurent-pulled module -/
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial TensorProduct Classical NNReal
noncomputable section
universe u v
namespace EnvelopeProperty.SchemeModuleLaurentEvaluation

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (p : X ⟶ Spec (.of R)) [CompactSpace X] [X.IsSeparated]
variable (M : X.Modules) [M.IsQuasicoherent]
variable {B : Type v} [CommRing B] [Module R B]

/-- Apply an original linear functional to the actual unique original
coefficients of EVERY original Laurent-pulled module section. -/
def evaluate (φ : AffineModuleFlatBaseChange.sections p M →ₗ[R] B)
    (σ : SchemeModuleLaurentCoefficients.pulledSections p M) : B[T;T⁻¹] :=
  LaurentModuleExpansion.evaluate φ
    ((FlatModuleGlobalSections.tensorEquiv (S := R[T;T⁻¹]) p M).symm σ)

/-- Every actual evaluated coefficient is the original functional applied
to the actual original geometric coefficient. -/
theorem evaluate_coeff (φ : AffineModuleFlatBaseChange.sections p M →ₗ[R] B)
    (σ : SchemeModuleLaurentCoefficients.pulledSections p M) (i : ℤ) :
    (evaluate p M φ σ).coeff i =
      φ (SchemeModuleLaurentCoefficients.coefficients p M σ i) := rfl

/-- Evaluation retains the actual original monomial/unit formula. -/
theorem evaluate_monomial (φ : AffineModuleFlatBaseChange.sections p M →ₗ[R] B)
    (i : ℤ) (m : AffineModuleFlatBaseChange.sections p M) :
    evaluate p M φ
      ((ProperBirationalSections.coefficientMap
        (FlatGlobalSections.structureMap (S := R[T;T⁻¹]) p)
        (LaurentPolynomial.T i)) • Scheme.Modules.affinePullbackUnitTop
          (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p) M m) =
      LaurentPolynomial.C (φ m) * LaurentPolynomial.T i := by
  change LaurentModuleExpansion.evaluate φ
    ((FlatModuleGlobalSections.tensorEquiv (S := R[T;T⁻¹]) p M).symm _) = _
  rw [← FlatModuleGlobalSections.tensorEquiv_tmul,
    LinearEquiv.symm_apply_apply, LaurentModuleExpansion.evaluate_T_tmul]

/-- The actual Laurent Gauss value of EVERY original pulled-module section
is the finite maximum over its own original geometric coefficient support. -/
theorem laurentGauss_evaluate (φ : AffineModuleFlatBaseChange.sections p M →ₗ[R] B)
    (w : Valuation B ℝ≥0) (r : ℝ≥0) (hr : 0 < r)
    (σ : SchemeModuleLaurentCoefficients.pulledSections p M) :
    (Berkovich.Spectrum.laurentGauss w r hr).val (evaluate p M φ σ) =
      (SchemeModuleLaurentCoefficients.coefficients p M σ).support.sup
        (fun i => w (φ (SchemeModuleLaurentCoefficients.coefficients p M σ i)) * r ^ i) := by
  exact LaurentModuleExpansion.laurentGauss_evaluate φ w r hr
    ((FlatModuleGlobalSections.tensorEquiv (S := R[T;T⁻¹]) p M).symm σ)

/-- ONE actual finite original coefficient/weight family works for every
original linear evaluation, valuation and positive radius. -/
theorem laurentGauss_finite_family
    (G : Finset (SchemeModuleLaurentCoefficients.pulledSections p M))
    (φ : AffineModuleFlatBaseChange.sections p M →ₗ[R] B)
    (w : Valuation B ℝ≥0) (r : ℝ≥0) (hr : 0 < r) :
    G.sup (fun σ => (Berkovich.Spectrum.laurentGauss w r hr).val (evaluate p M φ σ)) =
      (SchemeModuleLaurentCoefficients.terms p M G).sup
        (fun t => w (φ t.1) * r ^ t.2) := by
  rw [SchemeModuleLaurentCoefficients.terms_eq_tensor_terms]
  have h := LaurentModuleExpansion.laurentGauss_finite_family
    (G.image (FlatModuleGlobalSections.tensorEquiv (S := R[T;T⁻¹]) p M).symm)
    φ w r hr
  simpa only [Finset.sup_image, Function.comp_def, evaluate] using h

end EnvelopeProperty.SchemeModuleLaurentEvaluation
