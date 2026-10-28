import EnvelopeProperty.AlgGeom.CyclicSectionStructuralUnitOpenNaturality

/-! # The same original constant coordinate of the actual splitting over every affine base -/

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CyclicSectionAffineBaseConstantCoordinates
open CyclicSectionAlgebra CyclicSectionAffineCover CyclicSectionGlobalCover
open CyclicSectionGlobalCoverConstantTerm CyclicSectionGlobalCoverStructuralUnit
open CyclicSectionStructuralUnitNaturality CyclicSectionStructuralUnitRestriction
open CyclicSectionStructuralUnitOpenSquare CyclicSectionStructuralUnitOpenNaturality

private theorem naturality_of_restriction
    {Y X U V : Scheme.{u}} (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (f : V ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] (H : IsPullback q g f p)
    (rP : (pushforward p).obj (unitObj Y) ⟶ unitObj X)
    (rQ : (pushforward q).obj (unitObj U) ⟶ unitObj V)
    (hr : (restrictPushforwardIsoOfIsPullbackApp p q g f H (unitObj Y)).hom ≫
        (pushforward q).map (restrictUnitIso g).hom ≫ rQ =
      (restrictFunctor f).map rP ≫ (restrictUnitIso f).hom) :
    unitSquareMap p q g f H.w.symm ≫ (pushforward f).map rQ =
      rP ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  let F := restrictFunctor f
  let ε := (restrictFunctorAdjCounitIso f).hom
  apply ((restrictAdjunction f).homEquiv ((pushforward p).obj (unitObj Y)) (unitObj V)).symm.injective
  change F.map (unitSquareMap p q g f H.w.symm ≫ (pushforward f).map rQ) ≫ ε.app (unitObj V) =
    F.map (rP ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫ ε.app (unitObj V)
  calc
    _ = F.map (unitSquareMap p q g f H.w.symm) ≫
        ε.app ((pushforward q).obj (unitObj U)) ≫ rQ := by
      rw [F.map_comp, Category.assoc]
      exact congrArg (fun k => F.map (unitSquareMap p q g f H.w.symm) ≫ k) (ε.naturality rQ)
    _ = (restrictPushforwardIsoOfIsPullbackApp p q g f H (unitObj Y)).hom ≫
        (pushforward q).map (restrictUnitIso g).hom ≫ rQ := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ rQ) (restrict_unitSquareMap p q g f H))
    _ = F.map rP ≫ (restrictUnitIso f).hom := hr
    _ = F.map rP ≫
        (F.map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫ ε.app (unitObj V)) :=
      congrArg (fun k => F.map rP ≫ k) (restrictUnit_counit f).symm
    _ = _ := by rw [F.map_comp, Category.assoc]

/-- The SAME actual affine-base retraction commutes with its original defining root-spectrum square. -/
theorem affineBaseRetraction_square (X : Scheme.{u}) [IsAffine X] (n : ℕ)
    (a : Γ(X, ⊤)) (hn : 0 < n) :
    unitSquareMap (structureMap n a) (projection X n a) (toRootSpec X n a) X.toSpecΓ
        (equation_isPullback X n a).w.symm ≫
      (pushforward X.toSpecΓ).map (affineBaseRetraction X n a hn) =
    constantRetraction n a hn ≫
      SheafOfModules.unitToPushforwardObjUnit X.toSpecΓ.toRingCatSheafHom := by
  apply naturality_of_restriction (structureMap n a) (projection X n a)
    (toRootSpec X n a) X.toSpecΓ (equation_isPullback X n a)
  let J := restrictPushforwardIsoOfIsPullbackApp (structureMap n a) (projection X n a)
      (toRootSpec X n a) X.toSpecΓ (equation_isPullback X n a)
      (unitObj (Spec (.of (RootRing n a)))) ≪≫
    (pushforward (projection X n a)).mapIso (restrictUnitIso (toRootSpec X n a))
  change J.hom ≫ J.inv ≫
      ((restrictFunctor X.toSpecΓ).map (constantRetraction n a hn) ≫
        (restrictUnitIso X.toSpecΓ).hom) = _
  exact J.hom_inv_id_assoc _

/-- On original root-spectrum sections the actual affine-base splitting is the SAME constant coordinate. -/
theorem affineBaseRetraction_top (X : Scheme.{u}) [IsAffine X] (n : ℕ)
    (a : Γ(X, ⊤)) (hn : 0 < n) (z : Γ(Spec (.of (RootRing n a)), ⊤)) :
    (affineBaseRetraction X n a hn).app ⊤ ((toRootSpec X n a).appTop z) =
      constantTerm n a hn ((Scheme.ΓSpecIso (.of (RootRing n a))).hom z) := by
  have he := congrArg (fun k => (k.app ⊤).hom
      (show Γ((pushforward (structureMap n a)).obj
        (unitObj (Spec (.of (RootRing n a)))), ⊤) from z))
    (affineBaseRetraction_square X n a hn)
  change (affineBaseRetraction X n a hn).app ⊤
      ((unitSquareMap (structureMap n a) (projection X n a) (toRootSpec X n a) X.toSpecΓ
        (equation_isPullback X n a).w.symm).app ⊤ z) =
    X.toSpecΓ.appTop ((constantRetraction n a hn).app ⊤ z) at he
  calc
    _ = X.toSpecΓ.appTop ((constantRetraction n a hn).app ⊤ z) :=
      (congrArg ((affineBaseRetraction X n a hn).app ⊤)
        (unitSquareMap_top (structureMap n a) (projection X n a)
          (toRootSpec X n a) X.toSpecΓ (equation_isPullback X n a).w.symm z).symm).trans he
    _ = (Scheme.ΓSpecIso (.of Γ(X, ⊤))).hom ((constantRetraction n a hn).app ⊤ z) :=
      ConcreteCategory.congr_hom (Scheme.toSpecΓ_appTop X) ((constantRetraction n a hn).app ⊤ z)
    _ = _ := constantRetraction_top (.of Γ(X, ⊤)) n a hn z

end EnvelopeProperty.CyclicSectionAffineBaseConstantCoordinates
