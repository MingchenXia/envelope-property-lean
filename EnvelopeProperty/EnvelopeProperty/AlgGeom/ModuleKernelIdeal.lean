import EnvelopeProperty.Algebra.ModuleKernelLocalization
import Hironaka.Scheme.Modules.Sections
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import ModularCurves.Picard.InvertibleSheaf

/-!
# The entire actual ideal sheaf kernel of a structure-module map

Actual quasicoherence derives full principal-open compatibility. The original
kernel ideals themselves are used, without a compatible-subfamily replacement.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} {M : X.Modules} (α : unitObj X ⟶ M)

/-- The ENTIRE actual affine kernel in the SAME original ring of functions. -/
def unitMapKernelIdeal (U : X.affineOpens) : Ideal Γ(X, U.1) :=
  (α.val.app (.op U.1)).hom.ker

/-- Actual quasicoherence itself derives exact principal-open localization
of the ENTIRE original affine section-map kernels. -/
theorem map_unitMapKernelIdeal_basicOpen [M.IsQuasicoherent]
    (U : X.affineOpens) (r : Γ(X, U.1)) :
    (unitMapKernelIdeal α U).map
        (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom =
      unitMapKernelIdeal α (X.affineBasicOpen r) := by
  let R := Γ(X, U.1)
  let S := Γ(X, X.basicOpen r)
  let L := Γ(M, U.1)
  let N := Γ(M, X.basicOpen r)
  let h := X.basicOpen_le r
  let f : R →+* S := (X.presheaf.map (homOfLE h).op).hom
  let : Algebra R S := f.toAlgebra
  let : IsLocalization (Submonoid.powers r) S := U.2.isLocalization_basicOpen r
  let : Module R N := Module.compHom _ f
  let a : R →ₗ[R] L := (α.val.app (.op U.1)).hom
  let b : S →ₗ[S] N := (α.val.app (.op (X.basicOpen r))).hom
  let ρ : L →ₗ[R] N := M.resₗ h
  let : IsLocalizedModule (Submonoid.powers r) ρ :=
    M.isLocalizedModule_resₗ_basicOpen U.2 r
  have hsquare : ∀ x : R, ρ (a x) = b (algebraMap R S x) := by
    intro x
    exact (PresheafOfModules.naturality_apply α.val (homOfLE h).op x).symm
  change Ideal.map (algebraMap R S) a.ker = b.ker
  exact EnvelopeProperty.map_kernel_ideal_of_isLocalizedModule
    (R := R) (S := S) (M := L) (N := N) (Submonoid.powers r) a b ρ hsquare

/-- The actual whole ideal sheaf whose components are the ENTIRE original
section-map kernels, with compatibility derived from actual quasicoherence. -/
def unitMapKernelIdealSheaf [M.IsQuasicoherent] : X.IdealSheafData where
  ideal U := unitMapKernelIdeal α U
  map_ideal_basicOpen U r := map_unitMapKernelIdeal_basicOpen α U r

/-- The actual whole object retains the ENTIRE original affine kernel. -/
theorem unitMapKernelIdealSheaf_ideal [M.IsQuasicoherent] (U : X.affineOpens) :
    (unitMapKernelIdealSheaf α).ideal U = unitMapKernelIdeal α U := rfl

/-- Actual membership is exactly actual vanishing of the SAME original
section under the SAME original whole module map. -/
theorem mem_unitMapKernelIdealSheaf_ideal_iff [M.IsQuasicoherent]
    (U : X.affineOpens) (a : Γ(X, U.1)) :
    a ∈ (unitMapKernelIdealSheaf α).ideal U ↔ α.val.app (.op U.1) a = 0 := Iff.rfl

end
end AlgebraicGeometry.Scheme.Modules
