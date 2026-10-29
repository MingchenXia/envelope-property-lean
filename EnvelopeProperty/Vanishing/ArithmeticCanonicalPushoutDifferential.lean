import EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalBaseChange
import EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalUnits

/-! # Actual universal differentials for arithmetic structural squares

The square below records the original coefficient homomorphisms. All maps
are constructed from those homomorphisms and the original universal
derivations, in every exterior degree.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutDifferential

open CanonicalGeometry ArithmeticCanonicalGlobal

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S]
    {X Y : Scheme.{u}} (φ : CommRingCat.of R ⟶ CommRingCat.of S)
    (f : X ⟶ Spec (.of R)) (h : Y ⟶ Spec (.of S)) (g : Y ⟶ X)

/-- The actual square of structural coefficients on every original open. -/
def CoefficientSquare : Prop := ∀ U : X.Opens,
  (relativeConstants f).app (.op U) ≫ g.app U =
    φ ≫ (relativeConstants h).app (.op (g ⁻¹ᵁ U))

theorem coefficientSquare_of_structuralSquare
    (w : g ≫ f = h ≫ Spec.map φ) : CoefficientSquare φ f h g := by
  intro U
  rw [ArithmeticCanonicalGlobalBaseChange.morphismConstantsSquare, w]
  exact ArithmeticCanonicalGlobalBaseChange.compositionConstants φ h _

variable (w : CoefficientSquare φ f h g)

/-- The actual map on raw relative cotangent modules. -/
def cotangentPresheafMap : relativeCotangentPresheaf f ⟶
    (PresheafOfModules.pushforward g.toRingCatSheafHom.hom).obj
      (relativeCotangentPresheaf h) where
  app U := CommRingCat.KaehlerDifferential.map
    (f := (relativeConstants f).app U)
    (f' := (relativeConstants h).app (.op (g ⁻¹ᵁ U.unop)))
    (g := φ) (g' := g.app U.unop) (w U.unop).symm
  naturality {U V} i := by
    apply CommRingCat.KaehlerDifferential.ext (f := (relativeConstants f).app U)
    intro a
    change CommRingCat.KaehlerDifferential.map (w V.unop).symm
        ((relativeCotangentPresheaf f).map i (CommRingCat.KaehlerDifferential.d a)) = _
    change CommRingCat.KaehlerDifferential.map (w V.unop).symm
        ((relativeCotangentPresheaf f).map i ((relativeDerivation f).d a)) = _
    refine (congrArg (CommRingCat.KaehlerDifferential.map (w V.unop).symm)
      ((relativeDerivation f).d_map i a).symm).trans ?_
    refine (CommRingCat.KaehlerDifferential.map_d (w V.unop).symm
      (X.presheaf.map i a)).trans ?_
    change (relativeDerivation h).d (g.app V.unop (X.presheaf.map i a)) =
      (relativeCotangentPresheaf h).map ((Opens.map g.base).op.map i)
        (CommRingCat.KaehlerDifferential.map (w U.unop).symm
          (CommRingCat.KaehlerDifferential.d a))
    refine Eq.trans ?_ (congrArg ((relativeCotangentPresheaf h).map
      ((Opens.map g.base).op.map i))
        (CommRingCat.KaehlerDifferential.map_d (w U.unop).symm a)).symm
    exact (congrArg (relativeDerivation h).d (congr($(g.c.naturality i).hom a))).trans
      ((relativeDerivation h).d_map ((Opens.map g.base).op.map i) (g.app U.unop a))

theorem cotangentPresheafMap_d (U : X.Opens) (a : Γ(X, U)) :
    (cotangentPresheafMap φ f h g w).app (.op U) ((relativeDerivation f).d a) =
      (relativeDerivation h).d (g.app U a) :=
  CommRingCat.KaehlerDifferential.map_d (w U).symm a

local instance (U : X.Opensᵒᵖ) : Module (X.presheaf.obj U)
    ((relativeCotangentPresheaf f).obj U) := ((relativeCotangentPresheaf f).obj U).isModule

local instance (U : Y.Opensᵒᵖ) : Module (Y.presheaf.obj U)
    ((relativeCotangentPresheaf h).obj U) := ((relativeCotangentPresheaf h).obj U).isModule

def cotangentSemilinear (U : X.Opensᵒᵖ) :
    (relativeCotangentPresheaf f).obj U →ₛₗ[(g.app U.unop).hom]
      (relativeCotangentPresheaf h).obj ((Opens.map g.base).op.obj U) where
  toFun := (cotangentPresheafMap φ f h g w).app U
  map_add' := ((cotangentPresheafMap φ f h g w).app U).hom.map_add
  map_smul' r x := ((cotangentPresheafMap φ f h g w).app U).hom.map_smul r x

def exteriorComponent (q : ℕ) (U : X.Opensᵒᵖ) :
    (relativeExteriorPresheaf f q).obj U ⟶
      ((PresheafOfModules.pushforward g.toRingCatSheafHom.hom).obj
        (relativeExteriorPresheaf h q)).obj U := by
  let E := exteriorSemilinearMap (g.app U.unop).hom
    (cotangentSemilinear φ f h g w U) q
  exact ModuleCat.ofHom
    (X := (relativeExteriorPresheaf f q).obj U)
    (Y := ((PresheafOfModules.pushforward g.toRingCatSheafHom.hom).obj
      (relativeExteriorPresheaf h q)).obj U)
    { toFun := E, map_add' := E.map_add, map_smul' := E.map_smulₛₗ }

theorem exteriorComponent_wedge (q : ℕ) (U : X.Opensᵒᵖ)
    (m : Fin q → (relativeCotangentPresheaf f).obj U) :
    exteriorComponent φ f h g w q U (exteriorPower.ιMulti (X.presheaf.obj U) q m) =
      exteriorPower.ιMulti (Y.presheaf.obj ((Opens.map g.base).op.obj U)) q
        (M := (relativeCotangentPresheaf h).obj ((Opens.map g.base).op.obj U))
        (fun j => cotangentSemilinear φ f h g w U (m j)) :=
  exteriorSemilinearMap_ιMulti (g.app U.unop).hom (cotangentSemilinear φ f h g w U) q m

set_option backward.isDefEq.respectTransparency true in
def exteriorPresheafMap (q : ℕ) : relativeExteriorPresheaf f q ⟶
    (PresheafOfModules.pushforward g.toRingCatSheafHom.hom).obj
      (relativeExteriorPresheaf h q) where
  app U := exteriorComponent φ f h g w q U
  naturality {U V} i := by
    apply ModuleCat.Hom.ext
    apply LinearMap.ext_on (exteriorPower.ιMulti_span
      (X.presheaf.obj U) q ((relativeCotangentPresheaf f).obj U))
    rintro _ ⟨m, rfl⟩
    change exteriorComponent φ f h g w q V
        ((relativeExteriorPresheaf f q).map i (exteriorPower.ιMulti (X.presheaf.obj U) q m)) =
      (relativeExteriorPresheaf h q).map ((Opens.map g.base).op.map i)
        (exteriorComponent φ f h g w q U (exteriorPower.ιMulti (X.presheaf.obj U) q m))
    refine (congrArg (exteriorComponent φ f h g w q V)
      (exteriorPresheaf_map_mk (relativeCotangentPresheaf f) q i m)).trans ?_
    refine (exteriorComponent_wedge φ f h g w q V _).trans ?_
    refine Eq.trans ?_ ((congrArg ((relativeExteriorPresheaf h q).map
      ((Opens.map g.base).op.map i)) (exteriorComponent_wedge φ f h g w q U m)).symm)
    refine Eq.trans ?_ (exteriorPresheaf_map_mk (relativeCotangentPresheaf h) q
      ((Opens.map g.base).op.map i) _).symm
    congr 1
    funext j
    exact PresheafOfModules.naturality_apply (cotangentPresheafMap φ f h g w) i (m j)

def exteriorSheafPushMap (q : ℕ) : relativeExteriorSheaf f q ⟶
    (Scheme.Modules.pushforward g).obj (relativeExteriorSheaf h q) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).symm
    (exteriorPresheafMap φ f h g w q ≫
      (PresheafOfModules.pushforward g.toRingCatSheafHom.hom).map
        (exteriorSheafificationMap (relativeCotangentPresheaf h) q))

theorem exteriorSheafPushMap_unit (q : ℕ) :
    exteriorSheafificationMap (relativeCotangentPresheaf f) q ≫
        (exteriorSheafPushMap φ f h g w q).val =
      exteriorPresheafMap φ f h g w q ≫
        (PresheafOfModules.pushforward g.toRingCatSheafHom.hom).map
          (exteriorSheafificationMap (relativeCotangentPresheaf h) q) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).apply_symm_apply _

def exteriorPullbackMap (q : ℕ) :
    (Scheme.Modules.pullback g).obj (relativeExteriorSheaf f q) ⟶
      relativeExteriorSheaf h q :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
    (exteriorSheafPushMap φ f h g w q)

theorem exteriorPullbackMap_unit (q : ℕ) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        (relativeExteriorSheaf f q) ≫
      (Scheme.Modules.pushforward g).map (exteriorPullbackMap φ f h g w q) =
        exteriorSheafPushMap φ f h g w q :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).apply_symm_apply _

end EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutDifferential
