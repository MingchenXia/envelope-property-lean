/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import ModularCurves.ForMathlib.PullbackTensorGeneral

/-!
# Monoidality of presheaf pullback composition

The canonical comparison from iterated pullback to pullback along a composite morphism
of schemes is monoidal for the presheaf-of-modules tensor products.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace PresheafOfModules

/-- The canonical presheaf pullback-composition comparison is monoidal. -/
theorem pullbackComp_hom_isMonoidal
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    letI : MonoidalCategory (PresheafOfModules
      ((TopologicalSpace.Opens.map f.base).op ⋙
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))) := by
      rw [show (TopologicalSpace.Opens.map f.base).op ⋙
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) =
          ((TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj) ⋙
            forget₂ CommRingCat RingCat by rfl]
      exact PresheafOfModules.monoidalCategory
    letI := pullbackMonoidal g
    letI := pullbackMonoidal f
    letI : (pullback
        (F := TopologicalSpace.Opens.map g.base ⋙ TopologicalSpace.Opens.map f.base)
        (R := X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)
        (schemeRingPresheafHom g ≫ Functor.whiskerLeft
          (TopologicalSpace.Opens.map g.base).op (schemeRingPresheafHom f))).Monoidal := by
      change (pullback (schemeRingPresheafHom (f ≫ g))).Monoidal
      exact pullbackMonoidal (f ≫ g)
    (pullbackComp (schemeRingPresheafHom g) (schemeRingPresheafHom f)).hom.IsMonoidal := by
  let : MonoidalCategory (PresheafOfModules
    ((TopologicalSpace.Opens.map f.base).op ⋙
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))) := by
    rw [show (TopologicalSpace.Opens.map f.base).op ⋙
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) =
        ((TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj) ⋙
          forget₂ CommRingCat RingCat by rfl]
    exact PresheafOfModules.monoidalCategory
  let φg := schemeRingPresheafHom g
  let φf := schemeRingPresheafHom f
  let φfg := schemeRingPresheafHom (f ≫ g)
  let qG : (pushforwardFactored φg).LaxMonoidal :=
    pushforwardFactoredLaxMonoidal φg
  let qF : (pushforwardFactored φf).LaxMonoidal :=
    pushforwardFactoredLaxMonoidal φf
  let qFG : (pushforwardFactored φfg).LaxMonoidal :=
    pushforwardFactoredLaxMonoidal φfg
  let oG : (pullback φg).OplaxMonoidal := pullbackOplaxMonoidal φg
  have : IsIso (Functor.OplaxMonoidal.η (pullback φg)) := isIso_pullback_η g
  have : ∀ P Q, IsIso (Functor.OplaxMonoidal.δ (pullback φg) P Q) :=
    fun P Q => isIso_pullback_δ g P Q
  let hG : (pullback φg).Monoidal := Functor.Monoidal.ofOplaxMonoidal (pullback φg)
  let oF : (pullback φf).OplaxMonoidal := pullbackOplaxMonoidal φf
  have : IsIso (Functor.OplaxMonoidal.η (pullback φf)) := isIso_pullback_η f
  have : ∀ P Q, IsIso (Functor.OplaxMonoidal.δ (pullback φf) P Q) :=
    fun P Q => isIso_pullback_δ f P Q
  let hF : (pullback φf).Monoidal := Functor.Monoidal.ofOplaxMonoidal (pullback φf)
  let oFG : (pullback φfg).OplaxMonoidal := pullbackOplaxMonoidal φfg
  have : IsIso (Functor.OplaxMonoidal.η (pullback φfg)) := isIso_pullback_η (f ≫ g)
  have : ∀ P Q, IsIso (Functor.OplaxMonoidal.δ (pullback φfg) P Q) :=
    fun P Q => isIso_pullback_δ (f ≫ g) P Q
  let hFG : (pullback φfg).Monoidal := Functor.Monoidal.ofOplaxMonoidal (pullback φfg)
  let hComp : (pullback
      (F := TopologicalSpace.Opens.map g.base ⋙ TopologicalSpace.Opens.map f.base)
      (R := X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)
      (φg ≫ Functor.whiskerLeft (TopologicalSpace.Opens.map g.base).op φf)).Monoidal := by
    change (pullback φfg).Monoidal
    exact hFG
  let hadjG : (pullbackPushforwardFactoredAdjunction φg).IsMonoidal := by
    infer_instance
  let hadjF : (pullbackPushforwardFactoredAdjunction φf).IsMonoidal := by
    infer_instance
  let hadjFG : (pullbackPushforwardFactoredAdjunction φfg).IsMonoidal := by
    infer_instance
  let pG : (pushforward φg).LaxMonoidal := by
    change (pushforwardFactored φg).LaxMonoidal
    exact qG
  let pF : (pushforward φf).LaxMonoidal := by
    change (pushforwardFactored φf).LaxMonoidal
    exact qF
  let pFG : (pushforward φfg).LaxMonoidal := by
    change (pushforwardFactored φfg).LaxMonoidal
    exact qFG
  have hadjOrigG : (pullbackPushforwardAdjunction φg).IsMonoidal := by
    rw [← pullbackPushforwardFactoredAdjunction_eq φg]
    exact hadjG
  have hadjOrigF : (pullbackPushforwardAdjunction φf).IsMonoidal := by
    rw [← pullbackPushforwardFactoredAdjunction_eq φf]
    exact hadjF
  have hadjOrigFG : (pullbackPushforwardAdjunction φfg).IsMonoidal := by
    rw [← pullbackPushforwardFactoredAdjunction_eq φfg]
    exact hadjFG
  let α : pushforward φfg ⟶ pushforward φf ⋙ pushforward φg :=
    (pushforwardComp φg φf).inv
  have hα : α.IsMonoidal := by
    refine { unit := ?_, tensor := fun M N => ?_ }
    · rfl
    · ext1 U
      refine ModuleCat.MonoidalCategory.tensor_ext (fun x y => ?_)
      rfl
  have hadjOrigComp : ((pullbackPushforwardAdjunction φg).comp
      (pullbackPushforwardAdjunction φf)).IsMonoidal := by
    let := hadjOrigG
    let := hadjOrigF
    infer_instance
  have hmate : ((conjugateEquiv
      (pullbackPushforwardAdjunction φfg)
      ((pullbackPushforwardAdjunction φg).comp
        (pullbackPushforwardAdjunction φf))).symm α).IsMonoidal :=
    CategoryTheory.conjugateEquiv_symm_isMonoidal _ _ hadjOrigFG hadjOrigComp α hα
  rw [pullbackComp, Adjunction.leftAdjointCompIso_hom]
  exact hmate

end PresheafOfModules
