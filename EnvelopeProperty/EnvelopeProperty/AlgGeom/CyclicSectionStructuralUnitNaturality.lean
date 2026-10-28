import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverStructuralUnit

/-! # Naturality of the same actual cyclic constant sheaf retraction -/

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CyclicSectionStructuralUnitNaturality
open CyclicSectionAlgebra CyclicSectionBaseChange CyclicSectionAffineCover
open CyclicSectionGlobalCoverConstantTerm CyclicSectionGlobalCoverStructuralUnit

/-- The actual structural square induces its original module pushforward map. -/
def unitSquareMap {Y X U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (f : V ⟶ X)
    (h : g ≫ p = q ≫ f) :
    (pushforward p).obj (unitObj Y) ⟶
      (pushforward f).obj ((pushforward q).obj (unitObj U)) :=
  (pushforward p).map (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ≫
    (pushforwardComp g p).hom.app (unitObj U) ≫
    (pushforwardCongr h).hom.app (unitObj U) ≫
    (pushforwardComp q f).inv.app (unitObj U)

/-- On actual top sections this is the SAME original upper scheme-map pullback. -/
theorem unitSquareMap_top {Y X U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (f : V ⟶ X)
    (h : g ≫ p = q ≫ f) (x : Γ(Y, ⊤)) :
    (unitSquareMap p q g f h).app ⊤ x = g.appTop x := by
  let ht : (g ≫ p) ⁻¹ᵁ (⊤ : X.Opens) = (q ≫ f) ⁻¹ᵁ ⊤ :=
    congrArg (fun k => k ⁻¹ᵁ (⊤ : X.Opens)) h
  change U.presheaf.map (eqToHom ht).op (g.appTop x) = g.appTop x
  have he : (eqToHom ht).op = 𝟙 (op (⊤ : U.Opens)) := Subsingleton.elim _ _
  rw [he]
  exact ConcreteCategory.congr_hom (U.presheaf.map_id (op ⊤)) (g.appTop x)

/-- The SAME actual affine sheaf retraction is the original constant projection on top sections. -/
theorem constantRetraction_top (R : CommRingCat.{u}) (n : ℕ) (a : R) (hn : 0 < n)
    (x : Γ(Spec (.of (RootRing n a)), ⊤)) :
    (Scheme.ΓSpecIso R).hom ((constantRetraction n a hn).app ⊤ x) =
      constantTerm n a hn ((Scheme.ΓSpecIso (.of (RootRing n a))).hom x) := by
  let x' : (moduleSpecΓFunctor (R := R)).obj
      ((pushforward (structureMap n a)).obj (unitObj (Spec (.of (RootRing n a))))) := x
  have he := congrArg (unitSectionsEquiv R)
    (ConcreteCategory.congr_hom (constantRetraction_sections n a hn) x')
  change (Scheme.ΓSpecIso R).hom ((constantRetraction n a hn).app ⊤ x) =
      (unitSectionsEquiv R) ((unitSectionsEquiv R).symm
        (constantTerm n a hn ((Scheme.ΓSpecIso (.of (RootRing n a))).hom x))) at he
  exact he.trans ((unitSectionsEquiv R).apply_symm_apply _)

private theorem affineHom_top_ext (A : CommRingCat.{u}) (M N : (Spec A).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f g : M ⟶ N)
    (h : ∀ x : Γ(M, ⊤), f.app ⊤ x = g.app ⊤ x) : f = g := by
  let MQ : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory :=
    ⟨M, inferInstance⟩
  let NQ : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory :=
    ⟨N, inferInstance⟩
  have he : ObjectProperty.homMk (X := MQ) (Y := NQ) f =
      ObjectProperty.homMk (X := MQ) (Y := NQ) g := by
    apply ((tildeEquiv (R := A)).inverse).map_injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact h x
  exact congrArg (fun k => k.hom) he

variable {R S : CommRingCat.{u}} [Algebra R S]

/-- The SAME actual constant sheaf retractions commute with the original coefficient square. -/
theorem coefficient_naturality (n : ℕ) (a : R) (b : S)
    (h : b = algebraMap R S a) (hn : 0 < n) :
    unitSquareMap (structureMap n a) (structureMap n b) (coefficientSpecMap n a b h)
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (coefficientSpecMap_structure n a b h) ≫
      (pushforward (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
        (constantRetraction n b hn) =
    constantRetraction n a hn ≫
      SheafOfModules.unitToPushforwardObjUnit
        (Spec.map (CommRingCat.ofHom (algebraMap R S))).toRingCatSheafHom := by
  apply affineHom_top_ext R
  intro x
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).hom).1
  change (Scheme.ΓSpecIso S).hom
      ((constantRetraction n b hn).app ⊤
        ((unitSquareMap (structureMap n a) (structureMap n b) (coefficientSpecMap n a b h)
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (coefficientSpecMap_structure n a b h)).app ⊤ x)) =
    (Scheme.ΓSpecIso S).hom
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop
        ((constantRetraction n a hn).app ⊤ x))
  calc
    _ = constantTerm n b hn
        ((Scheme.ΓSpecIso (.of (RootRing n b))).hom ((coefficientSpecMap n a b h).appTop x)) := by
      exact (congrArg
        (fun z => (Scheme.ΓSpecIso S).hom ((constantRetraction n b hn).app ⊤ z))
        (unitSquareMap_top (structureMap n a) (structureMap n b) (coefficientSpecMap n a b h)
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (coefficientSpecMap_structure n a b h) x)).trans
        (constantRetraction_top S n b hn ((coefficientSpecMap n a b h).appTop x))
    _ = constantTerm n b hn
        ((coefficientMap n a b h) ((Scheme.ΓSpecIso (.of (RootRing n a))).hom x)) :=
      congrArg (constantTerm n b hn)
        (ConcreteCategory.congr_hom
          (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (coefficientMap n a b h).toRingHom)) x)
    _ = algebraMap R S (constantTerm n a hn ((Scheme.ΓSpecIso (.of (RootRing n a))).hom x)) :=
      congrArg (fun l => l ((Scheme.ΓSpecIso (.of (RootRing n a))).hom x))
        (constantTerm_baseChange n a b h hn)
    _ = algebraMap R S ((Scheme.ΓSpecIso R).hom ((constantRetraction n a hn).app ⊤ x)) :=
      congrArg (algebraMap R S) (constantRetraction_top R n a hn x).symm
    _ = _ := (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R S)))
      ((constantRetraction n a hn).app ⊤ x)).symm

end EnvelopeProperty.CyclicSectionStructuralUnitNaturality
