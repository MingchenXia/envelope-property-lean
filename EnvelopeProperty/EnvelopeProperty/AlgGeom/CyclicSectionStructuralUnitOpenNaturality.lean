import EnvelopeProperty.AlgGeom.CyclicSectionStructuralUnitOpenSquare

/-! # Whole open-restriction naturality of the same original cyclic constant splitting -/

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CyclicSectionStructuralUnitOpenNaturality
open CyclicSectionAlgebra CyclicSectionAffineCover
open CyclicSectionGlobalCoverStructuralUnit CyclicSectionStructuralUnitNaturality
open CyclicSectionStructuralUnitOpenSquare

/-- The SAME restricted structural unit followed by the native open counit is the native unit iso. -/
theorem restrictUnit_counit {X V : Scheme.{u}} (f : V ⟶ X) [IsOpenImmersion f] :
    (restrictFunctor f).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
      (restrictFunctorAdjCounitIso f).hom.app (unitObj V) = (restrictUnitIso f).hom := by
  apply (fullyFaithfulToPresheafOfModules).map_injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change V.presheaf.map (eqToHom (f.preimage_image_eq W.unop).symm).op
      (f.app (f ''ᵁ W.unop) x) = (f.appIso W.unop).hom x
  have he : f.app (f ''ᵁ W.unop) ≫
      V.presheaf.map (eqToHom (f.preimage_image_eq W.unop).symm).op =
      (f.appIso W.unop).hom := by
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appIso_hom', Scheme.Hom.appLE_map]
  exact ConcreteCategory.congr_hom he x

/-- A WHOLE structural-square naturality equality becomes the SAME native open restriction equality.
This generic transport lemma does not assert existence of any splitting or compatibility. -/
theorem restriction_of_naturality
    {Y X U V : Scheme.{u}} (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (f : V ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] (H : IsPullback q g f p)
    (rP : (pushforward p).obj (unitObj Y) ⟶ unitObj X)
    (rQ : (pushforward q).obj (unitObj U) ⟶ unitObj V)
    (hnat : unitSquareMap p q g f H.w.symm ≫ (pushforward f).map rQ =
      rP ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :
    (restrictPushforwardIsoOfIsPullbackApp p q g f H (unitObj Y)).hom ≫
        (pushforward q).map (restrictUnitIso g).hom ≫ rQ =
      (restrictFunctor f).map rP ≫ (restrictUnitIso f).hom := by
  let F := restrictFunctor f
  let ε := (restrictFunctorAdjCounitIso f).hom
  calc
    _ = F.map (unitSquareMap p q g f H.w.symm) ≫
        ε.app ((pushforward q).obj (unitObj U)) ≫ rQ := by
      exact (congrArg (fun k => k ≫ rQ) (restrict_unitSquareMap p q g f H)).symm.trans
        (Category.assoc _ _ _)
    _ = F.map (unitSquareMap p q g f H.w.symm) ≫ F.map ((pushforward f).map rQ) ≫
        ε.app (unitObj V) := by
      exact congrArg (fun k => F.map (unitSquareMap p q g f H.w.symm) ≫ k)
        (ε.naturality rQ).symm
    _ = F.map (unitSquareMap p q g f H.w.symm ≫ (pushforward f).map rQ) ≫
        ε.app (unitObj V) := by
      rw [F.map_comp, Category.assoc]
    _ = F.map (rP ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        ε.app (unitObj V) := congrArg (fun k => F.map k ≫ ε.app (unitObj V)) hnat
    _ = F.map rP ≫
        (F.map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          ε.app (unitObj V)) := by
      rw [F.map_comp, Category.assoc]
    _ = _ := congrArg (fun k => F.map rP ≫ k) (restrictUnit_counit f)

variable {R S : CommRingCat.{u}} [Algebra R S]

private instance coefficient_open (n : ℕ) (a : R) (b : S) (h : b = algebraMap R S a)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    IsOpenImmersion (coefficientSpecMap n a b h) :=
  isOpenImmersion_coefficientSpecMap n a b h

/-- The WHOLE original constant sheaf retraction commutes with the SAME actual open coefficient square. -/
theorem coefficient_restriction (n : ℕ) (a : R) (b : S) (h : b = algebraMap R S a) (hn : 0 < n)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    (restrictPushforwardIsoOfIsPullbackApp (structureMap n a) (structureMap n b)
        (coefficientSpecMap n a b h) (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (isPullback n a b h) (unitObj (Spec (.of (RootRing n a))))).hom ≫
      (pushforward (structureMap n b)).map (restrictUnitIso (coefficientSpecMap n a b h)).hom ≫
      constantRetraction n b hn =
    (restrictFunctor (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
        (constantRetraction n a hn) ≫
      (restrictUnitIso (Spec.map (CommRingCat.ofHom (algebraMap R S)))).hom :=
  restriction_of_naturality (structureMap n a) (structureMap n b)
    (coefficientSpecMap n a b h) (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (isPullback n a b h) (constantRetraction n a hn) (constantRetraction n b hn)
    (coefficient_naturality n a b h hn)

end EnvelopeProperty.CyclicSectionStructuralUnitOpenNaturality
