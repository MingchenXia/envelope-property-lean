import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Native module restriction through an actual scheme square

Categorical support for the canonical trace comparison. This constructs
the natural transformation from the actual adjunction unit and native
composition comparisons, with every original module retained.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def moduleSquareNat {Y X U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (s : V ⟶ X)
    (h : g ≫ p = q ≫ s) :
    pushforward p ⟶ pullback g ⋙ (pushforward q ⋙ pushforward s) :=
  (pushforward p).leftUnitor.inv ≫
    Functor.whiskerRight (pullbackPushforwardAdjunction g).unit (pushforward p) ≫
    (Functor.associator (pullback g) (pushforward g) (pushforward p)).hom ≫
    Functor.whiskerLeft (pullback g)
      ((pushforwardComp g p).hom ≫ (pushforwardCongr h).hom ≫ (pushforwardComp q s).inv)

theorem moduleSquareNat_app {Y X U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (s : V ⟶ X)
    (h : g ≫ p = q ≫ s) (M : Y.Modules) :
    (moduleSquareNat p q g s h).app M =
      (pushforward p).map ((pullbackPushforwardAdjunction g).unit.app M) ≫
        (pushforwardComp g p).hom.app ((pullback g).obj M) ≫
        (pushforwardCongr h).hom.app ((pullback g).obj M) ≫
        (pushforwardComp q s).inv.app ((pullback g).obj M) := by
  simp only [moduleSquareNat, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp]

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
