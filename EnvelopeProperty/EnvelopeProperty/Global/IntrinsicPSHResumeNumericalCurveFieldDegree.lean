import EnvelopeProperty.AlgGeom.SchemeFinitePrincipalDegrees
import Mathlib.RingTheory.Localization.Integral
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # The canonical original function-field degree of finite dominant maps

Finite inverse-chart algebras and their actual fraction-localization towers
derive finiteness and positivity of the canonical dominant-map field degree.
Every original nonempty affine inverse computes that same degree. No flatness,
normality, dimension bound or independently supplied coefficient map is used.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace EnvelopeProperty.NumericalCurveFieldDegree
variable {C D : Scheme.{u}} [IsIntegral C] [IsIntegral D]
  (g : D ⟶ C) [IsDominant g] [IsFinite g]

/-- The degree of the actual canonical generic-stalk field embedding. -/
def degree : ℕ :=
  letI := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
  Module.finrank C.functionField D.functionField

/-- Actual finiteness derives finiteness of the SAME canonical function-field extension. -/
theorem functionFields_finite :
    letI := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
    Module.Finite C.functionField D.functionField := by
  let := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint C ∈ (⊤ : C.Opens) from trivial)
  let : Nonempty U := ⟨⟨genericPoint C, hx⟩⟩
  let := (g.app U).hom.toAlgebra
  let := SchemeFinitePrincipalDegrees.nonempty_preimage g U
  let : IsDomain Γ(C, U) := IsIntegral.component_integral U
  let : IsDomain Γ(D, g ⁻¹ᵁ U) := IsIntegral.component_integral (g ⁻¹ᵁ U)
  let : Module.Finite Γ(C, U) Γ(D, g ⁻¹ᵁ U) := g.finite_app U hU
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  let := functionField_isFractionRing_of_isAffineOpen C U hU
  let := functionField_isFractionRing_of_isAffineOpen D (g ⁻¹ᵁ U) hV
  let : Algebra Γ(C, U) D.functionField :=
    ((D.germToFunctionField (g ⁻¹ᵁ U)).hom.comp (g.app U).hom).toAlgebra
  let : IsScalarTower Γ(C, U) Γ(D, g ⁻¹ᵁ U) D.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower Γ(C, U) C.functionField D.functionField :=
    IsScalarTower.of_algebraMap_eq fun s =>
      (DominantFunctionFieldMaps.functionFieldMap_section g U s).symm
  let : Algebra.IsIntegral Γ(C, U) Γ(D, g ⁻¹ᵁ U) :=
    Algebra.IsIntegral.of_finite Γ(C, U) Γ(D, g ⁻¹ᵁ U)
  let : Algebra.IsAlgebraic C.functionField D.functionField :=
    isAlgebraic_of_isFractionRing Γ(C, U) Γ(D, g ⁻¹ᵁ U) C.functionField D.functionField
  let : Algebra.EssFiniteType Γ(D, g ⁻¹ᵁ U) D.functionField :=
    Algebra.EssFiniteType.of_isLocalization D.functionField (nonZeroDivisors Γ(D, g ⁻¹ᵁ U))
  let : Algebra.EssFiniteType Γ(C, U) D.functionField :=
    Algebra.EssFiniteType.comp Γ(C, U) Γ(D, g ⁻¹ᵁ U) D.functionField
  let : Algebra.EssFiniteType C.functionField D.functionField :=
    Algebra.EssFiniteType.of_comp Γ(C, U) C.functionField D.functionField
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- The genuine canonical original extension degree is positive, internally derived. -/
theorem degree_pos : 0 < degree g := by
  let := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
  let : Module.Finite C.functionField D.functionField := functionFields_finite g
  exact Module.finrank_pos

/-- EVERY original nonempty affine inverse has the SAME canonical original field degree. -/
theorem degree_eq_affineRank (U : C.affineOpens) [Nonempty U.1] :
    degree g =
      letI := (g.app U.1).hom.toAlgebra
      Module.finrank Γ(C, U.1) Γ(D, g ⁻¹ᵁ U.1) := by
  let := (g.app U.1).hom.toAlgebra
  let := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
  let := SchemeFinitePrincipalDegrees.nonempty_preimage g U.1
  let : IsDomain Γ(C, U.1) := IsIntegral.component_integral U.1
  let : IsDomain Γ(D, g ⁻¹ᵁ U.1) := IsIntegral.component_integral (g ⁻¹ᵁ U.1)
  have hV : IsAffineOpen (g ⁻¹ᵁ U.1) := U.2.preimage g
  let := functionField_isFractionRing_of_isAffineOpen C U.1 U.2
  let := functionField_isFractionRing_of_isAffineOpen D (g ⁻¹ᵁ U.1) hV
  let : Algebra Γ(C, U.1) D.functionField :=
    ((D.germToFunctionField (g ⁻¹ᵁ U.1)).hom.comp (g.app U.1).hom).toAlgebra
  let : IsScalarTower Γ(C, U.1) Γ(D, g ⁻¹ᵁ U.1) D.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower Γ(C, U.1) C.functionField D.functionField :=
    IsScalarTower.of_algebraMap_eq fun s =>
      (DominantFunctionFieldMaps.functionFieldMap_section g U.1 s).symm
  exact IsFractionRing.finrank_eq Γ(C, U.1) C.functionField Γ(D, g ⁻¹ᵁ U.1) D.functionField

end EnvelopeProperty.NumericalCurveFieldDegree
