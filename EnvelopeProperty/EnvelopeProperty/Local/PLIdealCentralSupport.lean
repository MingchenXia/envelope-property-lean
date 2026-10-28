/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealPrincipalization
import EnvelopeProperty.Projective.NativeCoefficientSupport

/-!
# The genuine nonzero-parameter isomorphism of constructed PL blowups

Actual parameter powers in the original homogeneous ideals confine the true
ideal-sheaf supports to the central fibre. The constructed simultaneous blowup
is therefore an isomorphism over the whole actual inverse image of D(t).
-/

open scoped Classical Polynomial NNReal ENNReal Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

namespace EnvelopeProperty.ProjBerk
variable {k : Type u} [Field k] {n : ℕ}

/-- Actual parameter-power membership puts the whole ambient product ideal
support in the true central fibre, through the actual polynomial-base map. -/
theorem parameterOpen_le_compl_productIdeal_support
    (J : HomogeneousIdeal (ProjectiveGrading k[X] n)) (A : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ J.toIdeal) :
    nativePolynomialLineProductStructure (R := k) (n := n) ⁻¹ᵁ
        PrimeSpectrum.basicOpen (Polynomial.X : k[X]) ≤
      (nativePolynomialLineProductIdeal J).support.compl := by
  intro p hp
  change p ∉ (nativePolynomialLineProductIdeal J).support
  rw [nativePolynomialLineProductIdeal, Scheme.IdealSheafData.support_comap]
  change (nativePolynomialLineProductIso k n).inv p ∉ (nativeHomogeneousIdealSheaf J).support
  apply coefficientOpen_le_compl_support_of_power_mem J Polynomial.X A hA
  change nativeStructureMap ((nativePolynomialLineProductIso k n).inv p) ∈
    PrimeSpectrum.basicOpen (Polynomial.X : k[X])
  rw [← Scheme.Hom.comp_apply, nativePolynomialLineProductIso_inv_over_base]
  exact hp

end EnvelopeProperty.ProjBerk

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

/-- An actual open-restricted isomorphism stays an isomorphism on every smaller
actual open, with both scheme restrictions identified by their true isomorphism. -/
theorem isIso_morphismRestrict_of_le {Y Z : Scheme.{u}} (μ : Z ⟶ Y)
    {U W : Y.Opens} (hU : U ≤ W) [IsIso (μ ∣_ W)] : IsIso (μ ∣_ U) := by
  let V : W.toScheme.Opens := W.ι ⁻¹ᵁ U
  have hV : W.ι ''ᵁ V = U := by
    ext p
    change (∃ q : W, q.1 ∈ U ∧ q.1 = p) ↔ p ∈ U
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hp
      exact ⟨⟨p, hU hp⟩, hp, rfl⟩
  have h : IsIso (μ ∣_ W ∣_ V) :=
    IsZariskiLocalAtTarget.restrict (P := .isomorphisms _) (by infer_instance) V
  exact (MorphismProperty.arrow_mk_iso_iff (.isomorphisms _)
    (morphismRestrictRestrict μ W V ≪≫ morphismRestrictEq μ hV)).mp h

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.ProjSubvariety
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
open ProjBerk

/-- Actual parameter-power membership confines the entire restricted ideal
support on the actual variety product to its genuine central fibre. -/
theorem parameterOpen_le_compl_nativeProductIdeal_support
    (J : HomogeneousIdeal (ProjectiveGrading k[X] M)) (A : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ J.toIdeal) :
    X.nativeProductStructure ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : k[X]) ≤
      (X.nativeProductIdeal J).support.compl := by
  intro p hp
  change p ∉ (X.nativeProductIdeal J).support
  rw [nativeProductIdeal, Scheme.IdealSheafData.support_comap]
  change X.nativeProductInclusion p ∉ (nativePolynomialLineProductIdeal J).support
  exact parameterOpen_le_compl_productIdeal_support J A hA hp

/-- The actual constructed simultaneous blowup of parameter-power ideals is
an isomorphism over the whole genuine nonzero-parameter locus. -/
theorem simultaneousIdealBlowup_isIso_over_parameter_of_power_mem
    (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)) (A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal) :
    IsIso (X.simultaneousIdealBlowupProjection
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) ∣_
        (X.nativeProductStructure ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : k[X]))) := by
  apply RelativeSchemeValuedPoint.isIso_morphismRestrict_of_le
    (W := ((X.nativeProductIdeal I) * (X.nativeProductIdeal J)).support.compl)
  intro p hp
  have hI := X.parameterOpen_le_compl_nativeProductIdeal_support I A hA hp
  have hJ := X.parameterOpen_le_compl_nativeProductIdeal_support J B hB hp
  rw [Scheme.IdealSheafData.support_mul]
  change ¬ (p ∈ (X.nativeProductIdeal I).support ∨ p ∈ (X.nativeProductIdeal J).support)
  exact not_or.mpr ⟨hI, hJ⟩

/-- Actual PL data alone produce genuine vertical ambient ideals, their actual
variety-product restrictions, a proper simultaneous Cartier blowup, its whole
nonzero-parameter isomorphism, and the exact finite Gauss log-difference formula. -/
theorem IsPL.exists_verticalCartierIdeal_models {φ : X.an → ℝ} (hφ : X.IsPL φ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ)
      (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)) (A B : ℕ),
      0 < A ∧ 0 < B ∧ MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal ∧
      MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal ∧
      let I' := X.nativeProductIdeal I
      let J' := X.nativeProductIdeal J
      ∃ (hfin : ∀ w : X.an,
        RelativeSchemeValuedPoint.modelIdealLog I' gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint w) ≠ ⊥ ∧
        RelativeSchemeValuedPoint.modelIdealLog J' gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint w) ≠ ⊥),
      IsIso (X.simultaneousIdealBlowupProjection I' J' ∣_
        (X.nativeProductStructure ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : k[X]))) ∧
      (I'.comap (X.simultaneousIdealBlowupProjection I' J')).IsInvertible ∧
      (J'.comap (X.simultaneousIdealBlowupProjection I' J')).IsInvertible ∧
      ∀ w : X.an, (((r : ℝ) * φ w : ℝ) : EReal) =
        RelativeSchemeValuedPoint.modelIdealLog
          (I'.comap (X.simultaneousIdealBlowupProjection I' J')) gaussModelCoefficient_le_one
          (X.simultaneousIdealBlowupGaussPoint I' J' w (hfin w).1 (hfin w).2) -
        RelativeSchemeValuedPoint.modelIdealLog
          (J'.comap (X.simultaneousIdealBlowupProjection I' J')) gaussModelCoefficient_le_one
          (X.simultaneousIdealBlowupGaussPoint I' J' w (hfin w).1 (hfin w).2) + ((C : ℝ) : EReal) := by
  obtain ⟨r, hr, C, I, J, _hIfg, _hJfg, ⟨A, hA, hAI⟩, ⟨B, hB, hBJ⟩, hfin, heq⟩ :=
    hφ.exists_vertical_productIdeal_models
  have hfin' : ∀ w : X.an,
      RelativeSchemeValuedPoint.modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      RelativeSchemeValuedPoint.modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥ := by
    intro w
    simpa only [X.modelIdealLog_nativeProductIdeal] using hfin w
  refine ⟨r, hr, C, I, J, A, B, hA, hB, hAI, hBJ, hfin',
    X.simultaneousIdealBlowup_isIso_over_parameter_of_power_mem I J A B hAI hBJ,
    (X.simultaneousIdealBlowup_isInvertible _ _).1,
    (X.simultaneousIdealBlowup_isInvertible _ _).2, fun w => ?_⟩
  simpa only [X.modelIdealLog_simultaneousIdealBlowup_comap,
    X.modelIdealLog_nativeProductIdeal] using heq w

end EnvelopeProperty.ProjSubvariety
