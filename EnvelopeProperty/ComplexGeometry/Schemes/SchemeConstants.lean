import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Actual global constants on an integral proper variety

The structural map gives the actual constant section map. Universal closedness
makes it integral, and an algebraically closed base field makes it bijective.
Thus the degree-zero section-space dimension is derived geometrically, rather
than prescribed as part of a section-ring record or Hilbert asymptotic.
-/

open CategoryTheory AlgebraicGeometry

namespace ComplexSchemes

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [IsIntegral X] [UniversallyClosed f]

/-- The actual constants map through the structural morphism. -/
noncomputable def schemeConstantMap : K →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom

omit [IsAlgClosed K] [IsIntegral X] in
/-- Universal closedness makes the actual structural constants map integral. -/
theorem schemeConstantMap_isIntegral : (schemeConstantMap f).IsIntegral := by
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed f

/-- Proper integral varieties over an algebraically closed field have only
constant global regular functions. -/
theorem schemeConstantMap_bijective : Function.Bijective (schemeConstantMap f) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  exact schemeConstantMap_isIntegral f

/-- A genuine ring equivalence, constructed from the actual constants map. -/
noncomputable def schemeConstantsRingEquiv : K ≃+* Γ(X, ⊤) :=
  RingEquiv.ofBijective (schemeConstantMap f) (schemeConstantMap_bijective f)

/-- The structural algebra on actual global sections. -/
@[instance_reducible]
noncomputable def schemeGlobalSectionsAlgebra : Algebra K Γ(X, ⊤) :=
  (schemeConstantMap f).toAlgebra

/-- The actual constant-section linear equivalence for the structural algebra. -/
noncomputable def schemeConstantsLinearEquiv :
    letI := schemeGlobalSectionsAlgebra f
    K ≃ₗ[K] Γ(X, ⊤) := by
  letI := schemeGlobalSectionsAlgebra f
  exact (AlgEquiv.ofBijective (Algebra.ofId K Γ(X, ⊤))
    (schemeConstantMap_bijective f)).toLinearEquiv

/-- In particular, the actual global degree-zero piece has dimension one. -/
theorem schemeGlobalSections_finrank :
    letI := schemeGlobalSectionsAlgebra f
    Module.finrank K Γ(X, ⊤) = 1 := by
  let := schemeGlobalSectionsAlgebra f
  rw [← (schemeConstantsLinearEquiv f).finrank_eq]
  exact Module.finrank_self K

end ComplexSchemes
