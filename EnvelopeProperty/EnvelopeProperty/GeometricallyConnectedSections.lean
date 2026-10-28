/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.SchemeGlobalIdempotents
import EnvelopeProperty.FlatGlobalSections
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Actual field global-section coefficients derive geometric connectedness -/
open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.SchemeGlobalIdempotents
variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- The genuine ORIGINAL coefficient map, when bijective, is a K-algebra equivalence. -/
def coefficientAlgEquiv (hf : Function.Bijective (ProperBirationalSections.coefficientMap f)) :
    let : Algebra K Γ(X,⊤) := FlatGlobalSections.sectionsAlgebra f
    K ≃ₐ[K] Γ(X,⊤) := by
  let : Algebra K Γ(X,⊤) := FlatGlobalSections.sectionsAlgebra f
  exact AlgEquiv.ofBijective (Algebra.ofId K Γ(X,⊤)) hf

/-- EVERY genuine field scalar extension has the SAME whole field of ORIGINAL global sections. -/
def fieldSectionsEquiv (hf : Function.Bijective (ProperBirationalSections.coefficientMap f))
    [QuasiCompact f] [QuasiSeparated f] (L : Type u) [Field L] [Algebra K L] :
    let : Algebra L Γ(FlatGlobalSections.baseChange (S := L) f,⊤) :=
      FlatGlobalSections.sectionsAlgebra (FlatGlobalSections.structureMap (S := L) f)
    L ≃ₐ[L] Γ(FlatGlobalSections.baseChange (S := L) f,⊤) := by
  let : Algebra K Γ(X,⊤) := FlatGlobalSections.sectionsAlgebra f
  let : Algebra L Γ(FlatGlobalSections.baseChange (S := L) f,⊤) :=
    FlatGlobalSections.sectionsAlgebra (FlatGlobalSections.structureMap (S := L) f)
  exact (Algebra.TensorProduct.rid K L L).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) (coefficientAlgEquiv f hf)).trans
      (FlatGlobalSections.fieldTensorEquiv f))

/-- Actual QCQS flat base change over EVERY true field extension derives STANDARD geometric connectedness. -/
theorem geometricallyConnected_of_coefficientMap_bijective
    (hf : Function.Bijective (ProperBirationalSections.coefficientMap f))
    [QuasiCompact f] [QuasiSeparated f] : GeometricallyConnected f := by
  constructor
  refine (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun Y : Scheme.{u} => ConnectedSpace Y) (f := f)).mpr ?_
  intro L _ _
  let : Algebra L Γ(FlatGlobalSections.baseChange (S := L) f,⊤) :=
    FlatGlobalSections.sectionsAlgebra (FlatGlobalSections.structureMap (S := L) f)
  have : IsDomain Γ(FlatGlobalSections.baseChange (S := L) f,⊤) :=
    (fieldSectionsEquiv f hf L).symm.toRingEquiv.toMulEquiv.isDomain _
  exact connectedSpace_of_globalSections_isDomain _

end EnvelopeProperty.SchemeGlobalIdempotents
