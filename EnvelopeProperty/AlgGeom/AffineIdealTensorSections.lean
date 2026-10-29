/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Algebra.IdealTensorBaseChange
import EnvelopeProperty.AlgGeom.IdealModuleFunctorial
import EnvelopeProperty.Berkovich.SchemeIdealPullback
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Actual flat base change of affine ideal-module sections

The genuine geometric ideal comap has the actual affine ideal image, so
flat ring-module tensor base change yields the true original sections.
-/

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]

/-- The actual tensor base change of original affine ideal-module sections is
the true section module of the original geometric ideal comap. -/
def affineTensorSectionsEquiv (I : Y.IdealSheafData) (f : X ⟶ Y) [Flat f] :
    letI := f.appTop.hom.toAlgebra
    Γ(X, (⊤ : X.Opens)) ⊗[Γ(Y, (⊤ : Y.Opens))] Γ(I.toModules, (⊤ : Y.Opens)) ≃ₗ[Γ(X, (⊤ : X.Opens))]
      Γ((I.comap f).toModules, (⊤ : X.Opens)) := by
  letI := f.appTop.hom.toAlgebra
  haveI : Module.Flat Γ(Y, (⊤ : Y.Opens)) Γ(X, (⊤ : X.Opens)) := f.flat_appTop
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let V : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  exact ((I.toModulesSectionsEquiv V).baseChange Γ(Y, (⊤ : Y.Opens)) Γ(X, (⊤ : X.Opens))).trans
    ((EnvelopeProperty.IdealTensorBaseChange.equiv Γ(X, (⊤ : X.Opens)) (I.ideal V)).trans
      ((LinearEquiv.ofEq _ _ (I.comap_ideal_top_of_isAffine_native f).symm).trans
        ((I.comap f).toModulesSectionsEquiv U).symm))

/-- The actual affine section equivalence is the true original multiplication
formula on every pure tensor, in the original actual structure ring. -/
theorem affineTensorSectionsEquiv_tmul (I : Y.IdealSheafData) (f : X ⟶ Y) [Flat f]
    (s : Γ(X, (⊤ : X.Opens))) (x : Γ(I.toModules, (⊤ : Y.Opens))) :
    letI := f.appTop.hom.toAlgebra
    (show (I.comap f).toSubmodule.obj (op (⊤ : X.Opens)) from
      I.affineTensorSectionsEquiv f (s ⊗ₜ[Γ(Y, (⊤ : Y.Opens))] x)).1 =
        s * f.appTop.hom (x : I.toSubmodule.obj (op (⊤ : Y.Opens))).1 := by
  let := f.appTop.hom.toAlgebra
  have : Module.Flat Γ(Y, (⊤ : Y.Opens)) Γ(X, (⊤ : X.Opens)) := f.flat_appTop
  change ((I.affineTensorSectionsEquiv f (s ⊗ₜ[Γ(Y, (⊤ : Y.Opens))] x) :
    (I.comap f).toSubmodule.obj (op (⊤ : X.Opens))).1) = _
  simp only [affineTensorSectionsEquiv, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
  exact EnvelopeProperty.IdealTensorBaseChange.equiv_tmul (R := Γ(Y, (⊤ : Y.Opens)))
    Γ(X, (⊤ : X.Opens)) (I.ideal ⟨⊤, isAffineOpen_top Y⟩) s _

end AlgebraicGeometry.Scheme.IdealSheafData
