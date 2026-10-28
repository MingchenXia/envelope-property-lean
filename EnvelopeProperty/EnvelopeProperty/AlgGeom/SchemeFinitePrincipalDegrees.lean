import EnvelopeProperty.Algebra.FiniteAlgebraPrincipalDegrees
import EnvelopeProperty.AlgGeom.DominantFunctionFieldMaps
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Same whole original affine principal degrees under finite NONflat curve maps -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.SchemeFinitePrincipalDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f]

/-- Actual dominance derives nonemptiness of the ENTIRE inverse of every original nonempty open. -/
theorem nonempty_preimage (U : X.Opens) [Nonempty U] : Nonempty (f ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint Y, ?_⟩⟩
  change f (genericPoint Y) ∈ U
  rw [DominantFunctionFieldMaps.genericPoint_map f]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨x.1, trivial, x.property⟩)

omit [IsIntegral X] [IsIntegral Y] [IsDominant f] in
/-- The actual original affine open derives the SAME original ring dimension bound. -/
theorem sections_krullDimLE (hdim : topologicalKrullDim X ≤ 1) (U : X.affineOpens) :
    Ring.KrullDimLE 1 Γ(X, U.1) := by
  rw [Ring.krullDimLE_iff]
  have h := U.2.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  change topologicalKrullDim (PrimeSpectrum Γ(X, U.1)) ≤ topologicalKrullDim X at h
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
  exact h.trans hdim

/-- The whole actual original finite inverse-chart algebra has true principal degree, even over singular curve charts. -/
theorem affinePrincipal_length_eq_genericRank [IsFinite f] [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (U : X.affineOpens) [Nonempty U.1]
    (c : Γ(X, U.1)) (hc : c ≠ 0) :
    letI := (f.app U.1).hom.toAlgebra
    Module.length Γ(X, U.1) (Γ(Y, f ⁻¹ᵁ U.1) ⧸ Ideal.span {(f.app U.1) c}) =
      (Module.finrank Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) : ℕ∞) * Ring.ord Γ(X, U.1) c := by
  let := (f.app U.1).hom.toAlgebra
  let := nonempty_preimage f U.1
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  let : IsDomain Γ(Y, f ⁻¹ᵁ U.1) := IsIntegral.component_integral (f ⁻¹ᵁ U.1)
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let := sections_krullDimLE hdim U
  let : Module.Finite Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) := f.finite_app U.1 U.2
  let := IsSchemeTheoreticallyDominant.of_isDominant f
  exact FiniteAlgebraPrincipalDegrees.length_principalQuotient_eq_rank_mul_ord
    (f.app_injective U.1) c hc

/-- The SAME native original function-field map and original whole charts
compute actual principal degree by the TRUE original function-field extension degree.
No flatness, normality, chosen-field map or degree comparison premise. -/
theorem affinePrincipal_length_eq_functionFieldDegree [IsFinite f] [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (U : X.affineOpens) [Nonempty U.1]
    (c : Γ(X, U.1)) (hc : c ≠ 0) :
    letI := (f.app U.1).hom.toAlgebra
    letI := (DominantFunctionFieldMaps.functionFieldMap f).hom.toAlgebra
    Module.length Γ(X, U.1) (Γ(Y, f ⁻¹ᵁ U.1) ⧸ Ideal.span {(f.app U.1) c}) =
      (Module.finrank X.functionField Y.functionField : ℕ∞) * Ring.ord Γ(X, U.1) c := by
  let := (f.app U.1).hom.toAlgebra
  let := (DominantFunctionFieldMaps.functionFieldMap f).hom.toAlgebra
  let := nonempty_preimage f U.1
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  let : IsDomain Γ(Y, f ⁻¹ᵁ U.1) := IsIntegral.component_integral (f ⁻¹ᵁ U.1)
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let := sections_krullDimLE hdim U
  let : Module.Finite Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) := f.finite_app U.1 U.2
  let := IsSchemeTheoreticallyDominant.of_isDominant f
  have hV : IsAffineOpen (f ⁻¹ᵁ U.1) := U.2.preimage f
  let := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  let := functionField_isFractionRing_of_isAffineOpen Y (f ⁻¹ᵁ U.1) hV
  let : Algebra Γ(X, U.1) Y.functionField :=
    ((Y.germToFunctionField (f ⁻¹ᵁ U.1)).hom.comp (f.app U.1).hom).toAlgebra
  let : IsScalarTower Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) Y.functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower Γ(X, U.1) X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq (fun s => by
      exact (DominantFunctionFieldMaps.functionFieldMap_section f U.1 s).symm)
  exact FiniteAlgebraPrincipalDegrees.length_principalQuotient_eq_fieldDegree_mul_ord
    (f.app_injective U.1) X.functionField Y.functionField c hc

end EnvelopeProperty.SchemeFinitePrincipalDegrees
