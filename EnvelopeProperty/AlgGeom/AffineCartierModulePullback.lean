/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.IdealModulePullbackSections
import EnvelopeProperty.AlgGeom.AffineIdealTensorSections
import Hironaka.Scheme.BlowUp.FlatBaseChange
import ModularCurves.ForMathlib.AffineModuleBaseChange

/-!
# Actual affine flat pullback of Cartier ideal module sheaves

The true affine pullback unit formula identifies the canonical comparison
with the real tensor base-change isomorphism, and actual quasicoherent
sheaf geometry promotes this to a whole sheaf isomorphism.
-/

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}

/-- The actual affine pullback unit section is sent to the original entire
scheme section image by the genuine canonical ideal module comparison. -/
theorem toModulesComapPullbackMap_affineUnitTop (I : Y.IdealSheafData) (f : X ⟶ Y)
    (x : Γ(I.toModules, (⊤ : Y.Opens))) :
    (show (I.comap f).toSubmodule.obj (op (⊤ : X.Opens)) from
      (I.toModulesComapPullbackMap f).app ⊤
        (Scheme.Modules.affinePullbackUnitTop f I.toModules x)).1 =
      f.appTop.hom (x : I.toSubmodule.obj (op (⊤ : Y.Opens))).1 := by
  have hu : Scheme.Modules.affinePullbackUnitTop f I.toModules x =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app I.toModules).app ⊤ x :
        Γ((Scheme.Modules.pullback f).obj I.toModules, (⊤ : X.Opens))) := by
    unfold Scheme.Modules.affinePullbackUnitTop
    change ((Scheme.Modules.pullback f).obj I.toModules).presheaf.map
      (𝟙 (op (⊤ : X.Opens))) _ = _
    exact ConcreteCategory.congr_hom
      (((Scheme.Modules.pullback f).obj I.toModules).presheaf.map_id (op ⊤)) _
  exact (congrArg (fun t : Γ((Scheme.Modules.pullback f).obj I.toModules, (⊤ : X.Opens)) =>
    (show (I.comap f).toSubmodule.obj (op (⊤ : X.Opens)) from
      (I.toModulesComapPullbackMap f).app ⊤ t).1) hu).trans
        (I.toModulesComapPullbackMap_unit_app_inclusion f ⊤ x)

/-- The true affine pullback tensor comparison has the actual canonical
included multiplication formula; no compatibility premise is used. -/
theorem toModulesComapPullbackMap_affine_tmul [IsAffine X] [IsAffine Y] (I : Y.IdealSheafData) (f : X ⟶ Y)
    [I.toModules.IsQuasicoherent] (s : Γ(X, (⊤ : X.Opens)))
    (x : Γ(I.toModules, (⊤ : Y.Opens))) :
    letI := f.appTop.hom.toAlgebra
    (show (I.comap f).toSubmodule.obj (op (⊤ : X.Opens)) from
      (I.toModulesComapPullbackMap f).app ⊤
        ((Scheme.Modules.affinePullbackΓIso f I.toModules).hom
          (s ⊗ₜ[Γ(Y, (⊤ : Y.Opens))] x))).1 =
      s * f.appTop.hom (x : I.toSubmodule.obj (op (⊤ : Y.Opens))).1 := by
  let := f.appTop.hom.toAlgebra
  let e := Scheme.Modules.affinePullbackΓIso f I.toModules
  have hs : e.hom (s ⊗ₜ[Γ(Y, (⊤ : Y.Opens))] x) =
      s • e.hom ((1 : Γ(X, (⊤ : X.Opens))) ⊗ₜ[Γ(Y, (⊤ : Y.Opens))] x) := by
    rw [show s ⊗ₜ[Γ(Y, (⊤ : Y.Opens))] x =
        s • ((1 : Γ(X, (⊤ : X.Opens))) ⊗ₜ[Γ(Y, (⊤ : Y.Opens))] x) by
          change s ⊗ₜ[Γ(Y, (⊤ : Y.Opens))] x =
            (s * (1 : Γ(X, (⊤ : X.Opens)))) ⊗ₜ[Γ(Y, (⊤ : Y.Opens))] x
          rw [mul_one]]
    exact e.hom.hom.map_smul s _
  have hu : (show (I.comap f).toSubmodule.obj (op (⊤ : X.Opens)) from
      (I.toModulesComapPullbackMap f).app ⊤
        (e.hom ((1 : Γ(X, (⊤ : X.Opens))) ⊗ₜ[Γ(Y, (⊤ : Y.Opens))] x))).1 =
      f.appTop.hom (x : I.toSubmodule.obj (op (⊤ : Y.Opens))).1 :=
    (congrArg (fun t : Γ((Scheme.Modules.pullback f).obj I.toModules, (⊤ : X.Opens)) =>
      (show (I.comap f).toSubmodule.obj (op (⊤ : X.Opens)) from
        (I.toModulesComapPullbackMap f).app ⊤ t).1)
      (Scheme.Modules.affinePullbackΓIso_hom_one_tmul f I.toModules x)).trans
        (I.toModulesComapPullbackMap_affineUnitTop f x)
  calc
    _ = (show (I.comap f).toSubmodule.obj (op (⊤ : X.Opens)) from
        (I.toModulesComapPullbackMap f).app ⊤
          (s • e.hom ((1 : Γ(X, (⊤ : X.Opens))) ⊗ₜ[Γ(Y, (⊤ : Y.Opens))] x))).1 :=
      congrArg (fun t : Γ((Scheme.Modules.pullback f).obj I.toModules, (⊤ : X.Opens)) =>
        (show (I.comap f).toSubmodule.obj (op (⊤ : X.Opens)) from
          (I.toModulesComapPullbackMap f).app ⊤ t).1) hs
    _ = s * (show Γ(X, (⊤ : X.Opens)) from
      (show (I.comap f).toSubmodule.obj (op (⊤ : X.Opens)) from
        (I.toModulesComapPullbackMap f).app ⊤
          (e.hom ((1 : Γ(X, (⊤ : X.Opens))) ⊗ₜ[Γ(Y, (⊤ : Y.Opens))] x))).1) :=
      congrArg (fun t : Γ((I.comap f).toModules, (⊤ : X.Opens)) =>
        (t : (I.comap f).toSubmodule.obj (op (⊤ : X.Opens))).1)
        (Scheme.Modules.Hom.app_smul (I.toModulesComapPullbackMap f) s _)
    _ = _ := congrArg (s * ·) hu

/-- Actual affine flat pullback of an actual effective Cartier ideal module
is the true module sheaf of the original geometric ideal comap. -/
theorem IsInvertible.affine_toModulesComapPullbackMap_isIso [IsAffine X] [IsAffine Y]
    {I : Y.IdealSheafData} (hI : I.IsInvertible) (f : X ⟶ Y) [Flat f] :
    IsIso (I.toModulesComapPullbackMap f) := by
  have : I.toModules.IsLocallyFree := hI.isLocallyFree_toModules
  have : (I.comap f).toModules.IsLocallyFree :=
    (hI.comap_of_flat f).isLocallyFree_toModules
  have : ((Scheme.Modules.pullback f).obj I.toModules).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback_of_isAffine f I.toModules
  apply Scheme.Modules.isIso_of_isQuasicoherent_of_isIso_app_top
  rw [ConcreteCategory.isIso_iff_bijective]
  let := f.appTop.hom.toAlgebra
  let e := Scheme.Modules.affinePullbackΓIso f I.toModules
  let a := I.affineTensorSectionsEquiv f
  have h : ∀ t, (I.toModulesComapPullbackMap f).app ⊤ (e.hom t) = a t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
      apply Subtype.ext
      exact (I.toModulesComapPullbackMap_affine_tmul f s x).trans
        (I.affineTensorSectionsEquiv_tmul f s x).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  constructor
  · intro x y hxy
    obtain ⟨s, rfl⟩ := e.toLinearEquiv.surjective x
    obtain ⟨t, rfl⟩ := e.toLinearEquiv.surjective y
    exact congrArg e.hom (a.injective ((h s).symm.trans (hxy.trans (h t))))
  · intro y
    obtain ⟨t, ht⟩ := a.surjective y
    exact ⟨e.hom t, (h t).trans ht⟩

end AlgebraicGeometry.Scheme.IdealSheafData
