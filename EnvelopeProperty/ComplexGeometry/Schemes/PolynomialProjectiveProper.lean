import EnvelopeProperty.ComplexGeometry.Schemes.PolynomialProjectiveCanonical
import EnvelopeProperty.ComplexGeometry.Schemes.AffineChartSectionExtension
import EnvelopeProperty.ComplexGeometry.Schemes.SchemeConstants
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Native properness of actual polynomial projective space

The literal degree-zero constants are a ring equivalence. The actual
polynomial algebra is finite type over that actual degree-zero ring, so
native Proj properness applies to the actual structural morphism.
-/

open CategoryTheory AlgebraicGeometry Algebra

namespace ComplexSchemes

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type) [Field K] (n : ℕ)

/-- Genuine homogeneous degree-zero polynomials are exactly structural constants. -/
theorem polynomialProjDegreeZeroConstants_bijective :
    Function.Bijective (homogeneousPolynomialDegreeZeroConstants
      (K := K) (I := Fin (n + 1))) := by
  constructor
  · intro a b hab
    apply MvPolynomial.C_injective
    exact congrArg Subtype.val hab
  · intro p
    refine ⟨p.val.coeff 0, Subtype.ext ?_⟩
    exact ((MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (n + 1))).mpr p.property)).symm

/-- The actual structural constants give the genuine degree-zero ring equivalence. -/
def polynomialProjDegreeZeroRingEquiv :
    K ≃+* MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K 0 :=
  RingEquiv.ofBijective homogeneousPolynomialDegreeZeroConstants
    (polynomialProjDegreeZeroConstants_bijective K n)

/-- This genuine equivalence is literally the actual structural constant map. -/
theorem polynomialProjDegreeZeroRingEquiv_apply (a : K) :
    polynomialProjDegreeZeroRingEquiv K n a = homogeneousPolynomialDegreeZeroConstants a := rfl

/-- The actual ambient polynomial ring is finite type over its actual degree-zero ring. -/
theorem polynomialProjDegreeZero_finiteType :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K 0)
      (MvPolynomial (Fin (n + 1)) K) := by
  apply RingHom.finiteType_algebraMap.mp
  apply RingHom.FiniteType.of_comp_finiteType
    (f := homogeneousPolynomialDegreeZeroConstants (K := K) (I := Fin (n + 1)))
  change (algebraMap K (MvPolynomial (Fin (n + 1)) K)).FiniteType
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The actual polynomial projective structural morphism is native proper. -/
instance polynomialProjStructureMap_isProper : IsProper (polynomialProjStructureMap K n) := by
  let : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K 0)
      (MvPolynomial (Fin (n + 1)) K) :=
    polynomialProjDegreeZero_finiteType K n
  let : IsIso (CommRingCat.ofHom (homogeneousPolynomialDegreeZeroConstants
      (K := K) (I := Fin (n + 1)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (polynomialProjDegreeZeroConstants_bijective K n)
  unfold polynomialProjStructureMap
  infer_instance

/-- Actual projective properness gives native separatedness of the actual structural map. -/
theorem polynomialProjStructureMap_isSeparated : IsSeparated (polynomialProjStructureMap K n) :=
  inferInstance

/-- Actual projective properness gives native universal closedness of the actual structural map. -/
theorem polynomialProjStructureMap_universallyClosed :
    UniversallyClosed (polynomialProjStructureMap K n) := inferInstance

/-- Actual proper integral polynomial projective space has only actual structural constants. -/
def polynomialProjGlobalConstantsRingEquiv [IsAlgClosed K] :
    K ≃+* Γ(polynomialProj K n, ⊤) :=
  schemeConstantsRingEquiv (polynomialProjStructureMap K n)

/-- The literal global degree-zero space has dimension one under its actual structural algebra. -/
theorem polynomialProj_globalSections_finrank [IsAlgClosed K] :
    letI := schemeGlobalSectionsAlgebra (polynomialProjStructureMap K n)
    Module.finrank K Γ(polynomialProj K n, ⊤) = 1 :=
  schemeGlobalSections_finrank (polynomialProjStructureMap K n)

end

end ComplexSchemes
