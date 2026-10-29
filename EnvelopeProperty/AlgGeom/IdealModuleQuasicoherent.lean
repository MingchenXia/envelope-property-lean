import EnvelopeProperty.AlgGeom.CartierIdealModules
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

/-! # Quasicoherence of the SAME original geometric ideal module -/
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.IdealSheafData
open AlgebraicGeometry.Scheme.Modules

/-- Every actual original ideal module is quasicoherent, without any
Noetherian, finite-generation or Cartier premise. -/
theorem isQuasicoherent_toModules {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.toModules.IsQuasicoherent := by
  have hlocal (U : X.affineOpens) : (I.toModules.over U.1).IsQuasicoherent := by
    let : IsAffine U.1.toScheme := U.2
    let : IsIso (I.toModules.restrict U.2.fromSpec).fromTildeΓ :=
      I.isIso_fromTildeΓ_toModules U.2
    have hSpec : (I.toModules.restrict U.2.fromSpec).IsQuasicoherent :=
      (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
    let : (I.toModules.restrict U.2.fromSpec).IsQuasicoherent := hSpec
    have hOpen : (I.toModules.restrict U.1.ι).IsQuasicoherent :=
      (isQuasicoherent U.1).prop_of_iso (I.toModules.restrictιIso U.2) (by infer_instance)
    let : (I.toModules.restrict U.1.ι).IsQuasicoherent := hOpen
    exact isQuasicoherent_over_of_restrict_of_isAffineOpen I.toModules U.1
  have hcover : (Opens.grothendieckTopology X).CoversTop
      (fun U : X.affineOpens => U.1) := by
    rw [Opens.coversTop_iff, IsOpenCover, iSup_affineOpens_eq_top X]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ I.toModules _ (fun U : X.affineOpens => U.1) hcover hlocal

end AlgebraicGeometry.Scheme.IdealSheafData
