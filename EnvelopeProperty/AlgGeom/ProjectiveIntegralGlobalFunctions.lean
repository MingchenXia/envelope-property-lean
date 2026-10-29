import EnvelopeProperty.AlgGeom.FiniteClosedIdealLocalDegrees
import EnvelopeProperty.AlgGeom.UnitModuleAutomorphisms

/-! # The actual global function ring of an original integral projective scheme is a field -/
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveIntegralGlobalFunctions
open SchemeCoherentEulerIndex FiniteClosedIdealLocalDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k]

omit [IsIntegral X] in
/-- The SAME entire original function ring, with its original structure-map
coefficient action, is genuinely finite over the original field. -/
theorem sections_finite (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p) :
    letI := structureSectionsAlgebra p
    Module.Finite k Γ(X, ⊤) := by
  let := structureSectionsAlgebra p
  let : (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj X).IsFinitePresentation := isInvertible_unit.isFinitePresentation
  let : Module.Finite k (fieldSections p (unitObj X)) := fieldSections_finite p hp (unitObj X)
  exact Module.Finite.equiv (structureFieldSectionsIso p).toLinearEquiv

/-- Actual projective coherent finiteness and original integrality DERIVE
that the SAME entire original global function ring is a field. -/
theorem sections_isField (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p) :
    IsField Γ(X, ⊤) := by
  let := structureSectionsAlgebra p
  let : Module.Finite k Γ(X, ⊤) := sections_finite p hp
  exact IsField.of_isDomain_of_finite k Γ(X, ⊤)

/-- Every actual nonzero ORIGINAL global function is a true global unit;
no global-function field or constancy certificate is supplied. -/
theorem section_isUnit (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (a : Γ(X, ⊤)) (ha : a ≠ 0) : IsUnit a := by
  let := structureSectionsAlgebra p
  let : Module.Finite k Γ(X, ⊤) := sections_finite p hp
  exact FiniteDimensional.isUnit k ha

/-- The SAME nonzero original scalar gives a genuine whole original
structure-line automorphism under the actual canonical multiplication map. -/
theorem unitEndomorphism_isIso (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (a : Γ(X, ⊤)) (ha : a ≠ 0) :
    IsIso (ModularCurves.unitEndomorphismOfTopSection a) := by
  have hu := section_isUnit p hp a ha
  rw [← hu.unit_spec]
  exact (ModularCurves.unitAutomorphismOfTopUnit hu.unit).isIso_hom

end EnvelopeProperty.ProjectiveIntegralGlobalFunctions
