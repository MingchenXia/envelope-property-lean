import EnvelopeProperty.AlgGeom.FlatModuleGlobalSections
import EnvelopeProperty.Algebra.LaurentModuleExpansion

/-! # Entire original Laurent coefficients of original pulled-module sections -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped LaurentPolynomial TensorProduct Classical
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleLaurentCoefficients

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (p : X ⟶ Spec (.of R))

/-- The literal whole original section module on the original Laurent base change. -/
abbrev pulledSections (M : X.Modules) : ModuleCat R[T;T⁻¹] :=
  AffineModuleFlatBaseChange.sections (FlatGlobalSections.structureMap (S := R[T;T⁻¹]) p)
    ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p)).obj M)

variable [CompactSpace X] [X.IsSeparated]

/-- Every actual original Laurent-pulled module section has its unique
whole finitely supported family of actual original module coefficients. -/
def coefficients (M : X.Modules) [M.IsQuasicoherent] :
    pulledSections p M ≃ (ℤ →₀ AffineModuleFlatBaseChange.sections p M) := by
  exact (FlatModuleGlobalSections.tensorEquiv (S := R[T;T⁻¹]) p M).toEquiv.symm.trans
    (LaurentModuleExpansion.coefficients
      (R := R) (M := AffineModuleFlatBaseChange.sections p M)).toEquiv

/-- The geometric coefficient map agrees with the actual entire Laurent
tensor coefficients after the genuine original whole H0 equivalence. -/
theorem coefficients_tensorEquiv (M : X.Modules) [M.IsQuasicoherent]
    (z : R[T;T⁻¹] ⊗[R] AffineModuleFlatBaseChange.sections p M) :
    coefficients p M (FlatModuleGlobalSections.tensorEquiv (S := R[T;T⁻¹]) p M z) =
      LaurentModuleExpansion.coefficients z := by
  change LaurentModuleExpansion.coefficients
      ((FlatModuleGlobalSections.tensorEquiv (S := R[T;T⁻¹]) p M).symm
        (FlatModuleGlobalSections.tensorEquiv (S := R[T;T⁻¹]) p M z)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Every original Laurent coefficient of the actual original coefficient
multiple of an original pullback-unit section is the expected original scalar. -/
theorem coefficients_pure (M : X.Modules) [M.IsQuasicoherent]
    (F : R[T;T⁻¹]) (m : AffineModuleFlatBaseChange.sections p M) (i : ℤ) :
    coefficients p M
        ((ProperBirationalSections.coefficientMap
          (FlatGlobalSections.structureMap (S := R[T;T⁻¹]) p) F) •
          Scheme.Modules.affinePullbackUnitTop
            (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p) M m) i =
      F.coeff i • m := by
  have h := coefficients_tensorEquiv p M (F ⊗ₜ[R] m)
  rw [FlatModuleGlobalSections.tensorEquiv_tmul] at h
  exact (congrArg (fun f : ℤ →₀ AffineModuleFlatBaseChange.sections p M => f i) h).trans
    (LaurentModuleExpansion.coefficients_tmul F m i)

/-- Every original monomial times the actual original unit section has
exactly the original singleton coefficient family. -/
theorem coefficients_monomial (M : X.Modules) [M.IsQuasicoherent]
    (i : ℤ) (m : AffineModuleFlatBaseChange.sections p M) :
    coefficients p M
        ((ProperBirationalSections.coefficientMap
          (FlatGlobalSections.structureMap (S := R[T;T⁻¹]) p)
          (LaurentPolynomial.T i)) • Scheme.Modules.affinePullbackUnitTop
            (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p) M m) =
      Finsupp.single i m := by
  have h := coefficients_tensorEquiv p M ((LaurentPolynomial.T i : R[T;T⁻¹]) ⊗ₜ[R] m)
  rw [FlatModuleGlobalSections.tensorEquiv_tmul,
    LaurentModuleExpansion.coefficients_T_tmul] at h
  exact h

/-- The inverse geometric coefficient map is the original whole H0 map
of the inverse original Laurent tensor coefficient equivalence. -/
theorem coefficients_symm_tensorEquiv (M : X.Modules) [M.IsQuasicoherent]
    (c : ℤ →₀ AffineModuleFlatBaseChange.sections p M) :
    (coefficients p M).symm c =
      FlatModuleGlobalSections.tensorEquiv (S := R[T;T⁻¹]) p M
        (LaurentModuleExpansion.coefficients.symm c) := rfl

/-- The inverse is the actual finite sum of original monomial coefficient
multiples of original pullback-unit sections. -/
theorem coefficients_symm (M : X.Modules) [M.IsQuasicoherent]
    (c : ℤ →₀ AffineModuleFlatBaseChange.sections p M) :
    (coefficients p M).symm c = c.sum (fun i m =>
      (ProperBirationalSections.coefficientMap
        (FlatGlobalSections.structureMap (S := R[T;T⁻¹]) p)
        (LaurentPolynomial.T i)) • Scheme.Modules.affinePullbackUnitTop
          (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p) M m) := by
  rw [coefficients_symm_tensorEquiv, LaurentModuleExpansion.coefficients_symm]
  simp only [Finsupp.sum, map_sum, FlatModuleGlobalSections.tensorEquiv_tmul]
  rfl

/-- EVERY original pulled-module section has its actual unique finite
Laurent expansion in original sections and original integer weights. -/
theorem eq_sum_monomial (M : X.Modules) [M.IsQuasicoherent]
    (σ : pulledSections p M) :
    σ = (coefficients p M σ).sum (fun i m =>
      (ProperBirationalSections.coefficientMap
        (FlatGlobalSections.structureMap (S := R[T;T⁻¹]) p)
        (LaurentPolynomial.T i)) • Scheme.Modules.affinePullbackUnitTop
          (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p) M m) :=
  ((coefficients p M).symm_apply_apply σ).symm.trans (coefficients_symm p M _)

/-- One actual finite original coefficient/weight family is constructed
from the original finite section family BEFORE every point or evaluation. -/
def terms (M : X.Modules) [M.IsQuasicoherent]
    (G : Finset (pulledSections p M)) :
    Finset (AffineModuleFlatBaseChange.sections p M × ℤ) :=
  G.biUnion fun σ => (coefficients p M σ).support.image fun i => (coefficients p M σ i, i)

/-- The actual original geometric coefficient family is exactly the original
Laurent tensor family after the inverse entire original H0 equivalence. -/
theorem terms_eq_tensor_terms (M : X.Modules) [M.IsQuasicoherent]
    (G : Finset (pulledSections p M)) :
    terms p M G = LaurentModuleExpansion.terms
      (G.image (FlatModuleGlobalSections.tensorEquiv (S := R[T;T⁻¹]) p M).symm) := by
  simp only [terms, LaurentModuleExpansion.terms, Finset.image_biUnion]
  rfl

end EnvelopeProperty.SchemeModuleLaurentCoefficients
