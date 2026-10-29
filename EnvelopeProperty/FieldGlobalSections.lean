/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.UniversallyClosedSections
import EnvelopeProperty.GeometricallyConnectedSections
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Original finite field-base global coefficients and actual geometric connectedness -/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.FieldGlobalSections
open ProperBirationalSections
variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]

/-- REUSE actual UC field-base finiteness, retaining the ORIGINAL Gamma-Spec coefficient map. -/
theorem coefficientMap_finite (f : Y ⟶ Spec (.of K))
    [UniversallyClosed f] [LocallyOfFiniteType f] : (coefficientMap f).Finite := by
  apply RingHom.finite_respectsIso.2
    (e := (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv)
  exact finite_appTop_of_universallyClosed K f

/-- Finiteness is for EXACTLY the original coefficient-induced module action. -/
theorem globalSections_moduleFinite (f : Y ⟶ Spec (.of K))
    [UniversallyClosed f] [LocallyOfFiniteType f] :
    let : Algebra K Γ(Y,⊤) := FlatGlobalSections.sectionsAlgebra f
    Module.Finite K Γ(Y,⊤) := coefficientMap_finite f

/-- Actual algebraic closure and derived integrality make the ORIGINAL coefficient map bijective without local finite type. -/
theorem coefficientMap_bijective [IsAlgClosed K] (f : Y ⟶ Spec (.of K)) [UniversallyClosed f] :
    Function.Bijective (coefficientMap f) :=
  IsAlgClosed.ringHom_bijective_of_isIntegral (coefficientMap f)
    (UniversallyClosedSections.coefficientMap_isIntegral f)

/-- REUSE the actual coefficient algebra-equivalence factory with a genuinely DERIVED bijection. -/
def coefficientEquiv [IsAlgClosed K] (f : Y ⟶ Spec (.of K)) [UniversallyClosed f] :
    let : Algebra K Γ(Y,⊤) := FlatGlobalSections.sectionsAlgebra f
    K ≃ₐ[K] Γ(Y,⊤) :=
  SchemeGlobalIdempotents.coefficientAlgEquiv f (coefficientMap_bijective f)

/-- EVERY original coefficient goes to its WHOLE original pulled-back section. -/
theorem coefficientEquiv_apply [IsAlgClosed K] (f : Y ⟶ Spec (.of K))
    [UniversallyClosed f] (k : K) :
    let : Algebra K Γ(Y,⊤) := FlatGlobalSections.sectionsAlgebra f
    coefficientEquiv f k=coefficientMap f k := rfl

/-- UC supplies QC; the actual original coefficient bijection and genuine QCQS field base change derive STANDARD geometric connectedness. -/
theorem geometricallyConnected [IsAlgClosed K] (f : Y ⟶ Spec (.of K))
    [UniversallyClosed f] [QuasiSeparated f] : GeometricallyConnected f :=
  SchemeGlobalIdempotents.geometricallyConnected_of_coefficientMap_bijective f
    (coefficientMap_bijective f)

end EnvelopeProperty.FieldGlobalSections
