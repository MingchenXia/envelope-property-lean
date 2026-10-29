import EnvelopeProperty.AlgGeom.CyclicSectionStructuralUnitNaturality
import EnvelopeProperty.AlgGeom.CyclicSectionStructuralUnitRestriction

/-! # The native open cartesian comparison is the same actual structural-square map -/

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CyclicSectionStructuralUnitOpenSquare
open CyclicSectionStructuralUnitNaturality

/-- On every original open the actual square map is the original structure-sheaf pullback. -/
theorem unitSquareMap_app {Y X U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (f : V ⟶ X)
    (h : g ≫ p = q ≫ f) (W : X.Opens) (x : Γ(Y, p ⁻¹ᵁ W)) :
    (unitSquareMap p q g f h).app W x =
      U.presheaf.map (eqToHom (congrArg (fun k => k ⁻¹ᵁ W) h.symm)).op
        (g.app (p ⁻¹ᵁ W) x) := rfl

/-- The WHOLE actual square map restricts to the SAME native cartesian unit comparison. -/
theorem restrict_unitSquareMap {Y X U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (f : V ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] (H : IsPullback q g f p) :
    (restrictFunctor f).map (unitSquareMap p q g f H.w.symm) ≫
      (restrictFunctorAdjCounitIso f).hom.app ((pushforward q).obj (unitObj U)) =
    (restrictPushforwardIsoOfIsPullbackApp p q g f H (unitObj Y)).hom ≫
      (pushforward q).map (restrictUnitIso g).hom := by
  apply (fullyFaithfulToPresheafOfModules).map_injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let hcart := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W.unop
  let hc := (f.preimage_image_eq W.unop).symm
  let he := congrArg (fun k => k ⁻¹ᵁ (f ''ᵁ W.unop)) H.w
  change U.presheaf.map ((TopologicalSpace.Opens.map q.base).map (eqToHom hc)).op
      (U.presheaf.map (eqToHom he).op (g.app (p ⁻¹ᵁ f ''ᵁ W.unop) x)) =
    (g.appIso (q ⁻¹ᵁ W.unop)).hom (Y.presheaf.map (eqToHom hcart).op x)
  have hr : g.app (p ⁻¹ᵁ f ''ᵁ W.unop) ≫
      U.presheaf.map (eqToHom he).op ≫
      U.presheaf.map ((TopologicalSpace.Opens.map q.base).map (eqToHom hc)).op =
      Y.presheaf.map (eqToHom hcart).op ≫ (g.appIso (q ⁻¹ᵁ W.unop)).hom := by
    simp only [← Category.assoc, Scheme.Hom.app_eq_appLE, Scheme.Hom.appIso_hom',
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  exact ConcreteCategory.congr_hom hr x

end EnvelopeProperty.CyclicSectionStructuralUnitOpenSquare
