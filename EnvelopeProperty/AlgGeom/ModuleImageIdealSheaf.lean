import EnvelopeProperty.Algebra.ModuleImageIdealLocalization
import Hironaka.Scheme.Modules.Sections
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import ModularCurves.Picard.InvertibleSheaf

/-! # The entire affine image of an actual map into the structure module -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} {M : X.Modules} (α : M ⟶ unitObj X)

/-- The entire original image, in the same original affine coordinate ring. -/
def unitTargetImageIdeal (U : X.affineOpens) : Ideal Γ(X, U.1) :=
  (α.val.app (.op U.1)).hom.range

/-- Actual quasicoherence derives localization of the entire affine image. -/
theorem map_unitTargetImageIdeal_basicOpen [M.IsQuasicoherent]
    (U : X.affineOpens) (r : Γ(X, U.1)) :
    (unitTargetImageIdeal α U).map
        (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom =
      unitTargetImageIdeal α (X.affineBasicOpen r) := by
  let R := Γ(X, U.1)
  let S := Γ(X, X.basicOpen r)
  let L := Γ(M, U.1)
  let N := Γ(M, X.basicOpen r)
  let h := X.basicOpen_le r
  let f : R →+* S := (X.presheaf.map (homOfLE h).op).hom
  let : Algebra R S := f.toAlgebra
  let : IsLocalization (Submonoid.powers r) S := U.2.isLocalization_basicOpen r
  let : Module R N := Module.compHom _ f
  let : IsScalarTower R S N := .of_algebraMap_smul fun _ _ => rfl
  let a : L →ₗ[R] R := (α.val.app (.op U.1)).hom
  let b : N →ₗ[S] S := (α.val.app (.op (X.basicOpen r))).hom
  let ρ : L →ₗ[R] N := M.resₗ h
  let : IsLocalizedModule (Submonoid.powers r) ρ :=
    M.isLocalizedModule_resₗ_basicOpen U.2 r
  have hsquare : ∀ x : L, b (ρ x) = algebraMap R S (a x) := by
    intro x
    exact PresheafOfModules.naturality_apply α.val (homOfLE h).op x
  change Ideal.map (algebraMap R S) a.range = b.range
  exact EnvelopeProperty.map_image_ideal_of_isLocalizedModule
    (R := R) (S := S) (Submonoid.powers r) a b ρ hsquare

/-- The actual image ideal sheaf uses the whole original images themselves. -/
def unitTargetImageIdealSheaf [M.IsQuasicoherent] : X.IdealSheafData where
  ideal U := unitTargetImageIdeal α U
  map_ideal_basicOpen U r := map_unitTargetImageIdeal_basicOpen α U r

/-- Its affine ideal is the entire image of the original section map. -/
theorem unitTargetImageIdealSheaf_ideal [M.IsQuasicoherent] (U : X.affineOpens) :
    (unitTargetImageIdealSheaf α).ideal U = unitTargetImageIdeal α U := rfl

/-- Membership means an actual original section maps to the same function. -/
theorem mem_unitTargetImageIdealSheaf_ideal_iff [M.IsQuasicoherent]
    (U : X.affineOpens) (a : Γ(X, U.1)) :
    a ∈ (unitTargetImageIdealSheaf α).ideal U ↔
      ∃ m : Γ(M, U.1), α.val.app (.op U.1) m = a := Iff.rfl

end
end AlgebraicGeometry.Scheme.Modules
