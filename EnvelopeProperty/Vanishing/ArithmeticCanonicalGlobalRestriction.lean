import EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobal

/-! # Actual open restrictions of global arithmetic differential objects

The coefficient maps and their inverses are those of the original open
immersion. All ring comparisons and isomorphisms are constructed internally.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalRestriction

open CanonicalGeometry ArithmeticCanonicalGlobal

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (g : Y ⟶ X) [IsOpenImmersion g]

/-- Actual structural constants commute with the open-immersion coefficient isomorphism. -/
theorem constantsSquare (U : Y.Opensᵒᵖ) :
    (relativeConstants f).app (g.opensFunctor.op.obj U) ≫ (g.appIso U.unop).hom =
      (relativeConstants (g ≫ f)).app U := by
  have htop : g.appLE ⊤ ⊤ (by simp) = g.appTop := by
    unfold Scheme.Hom.appLE
    change g.appTop ≫ Y.presheaf.map (𝟙 (op (⊤ : Y.Opens))) = g.appTop
    simp
  have hm : X.presheaf.map (g.opensFunctor.op.obj U).unop.leTop.op ≫
      (g.appIso U.unop).hom = g.appTop ≫ Y.presheaf.map U.unop.leTop.op := by
    change X.presheaf.map (g ''ᵁ U.unop).leTop.op ≫ _ = _
    rw [g.appIso_hom']
    exact ((g.map_appLE (g.preimage_image_eq U.unop).ge
      (g ''ᵁ U.unop).leTop.op).trans
      (g.appLE_map (U := ⊤) (V := ⊤) (by simp) U.unop.leTop.op).symm).trans
        (congrArg (fun h => h ≫ Y.presheaf.map U.unop.leTop.op) htop)
  ext r
  change (g.appIso U.unop).hom
      (X.presheaf.map (g.opensFunctor.op.obj U).unop.leTop.op
        (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r))) =
    Y.presheaf.map U.unop.leTop.op
      (g.appTop (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)))
  exact congr($(hm).hom (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)))

theorem constantsSquare_inv (U : Y.Opensᵒᵖ) :
    (relativeConstants (g ≫ f)).app U ≫ (g.appIso U.unop).inv =
      (relativeConstants f).app (g.opensFunctor.op.obj U) := by
  ext r
  have hr : (g.appIso U.unop).hom
      ((relativeConstants f).app (g.opensFunctor.op.obj U) r) =
      (relativeConstants (g ≫ f)).app U r :=
    congr($(constantsSquare f g U).hom r)
  exact (congrArg (fun z => (g.appIso U.unop).inv z) hr.symm).trans
    ((g.appIso U.unop).commRingCatIsoToRingEquiv.left_inv _)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse actual coefficient maps induce the actual relative cotangent map. -/
def cotangentPresheafMap :
    relativeCotangentPresheaf (g ≫ f) ⟶
      openImmersionPresheafRestrict g (relativeCotangentPresheaf f) where
  app U := CommRingCat.KaehlerDifferential.map
    (f := (relativeConstants (g ≫ f)).app U)
    (f' := (relativeConstants f).app (g.opensFunctor.op.obj U))
    (g := 𝟙 (CommRingCat.of R))
    (g' := (g.appIso U.unop).inv)
    (by
      dsimp [constantRingPresheaf]
      exact (Category.id_comp _).trans (constantsSquare_inv f g U).symm)
  naturality {U V} i := by
    apply CommRingCat.KaehlerDifferential.ext
      (f := (relativeConstants (g ≫ f)).app U)
    intro a
    have hU : 𝟙 (CommRingCat.of R) ≫
        (relativeConstants f).app (g.opensFunctor.op.obj U) =
        (relativeConstants (g ≫ f)).app U ≫ (g.appIso U.unop).inv :=
      (Category.id_comp _).trans (constantsSquare_inv f g U).symm
    have hV : 𝟙 (CommRingCat.of R) ≫
        (relativeConstants f).app (g.opensFunctor.op.obj V) =
        (relativeConstants (g ≫ f)).app V ≫ (g.appIso V.unop).inv :=
      (Category.id_comp _).trans (constantsSquare_inv f g V).symm
    change CommRingCat.KaehlerDifferential.map hV
        ((relativeCotangentPresheaf (g ≫ f)).map i (CommRingCat.KaehlerDifferential.d a)) =
      (openImmersionPresheafRestrict g (relativeCotangentPresheaf f)).map i
        (CommRingCat.KaehlerDifferential.map hU (CommRingCat.KaehlerDifferential.d a))
    rw [CommRingCat.KaehlerDifferential.map_d]
    change CommRingCat.KaehlerDifferential.map hV
        ((relativeCotangentPresheaf (g ≫ f)).map i ((relativeDerivation (g ≫ f)).d a)) =
      (relativeCotangentPresheaf f).map (g.opensFunctor.op.map i)
        ((relativeDerivation f).d ((g.appIso U.unop).inv a))
    refine (congrArg (CommRingCat.KaehlerDifferential.map hV)
      ((relativeDerivation (g ≫ f)).d_map i a).symm).trans ?_
    exact (CommRingCat.KaehlerDifferential.map_d hV (Y.presheaf.map i a)).trans
      ((congrArg (relativeDerivation f).d
        (congr($(g.appIso_inv_naturality i).hom a))).trans
        ((relativeDerivation f).d_map (g.opensFunctor.op.map i)
          ((g.appIso U.unop).inv a)))

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient maps are actual isomorphisms, hence so are the cotangent maps. -/
def cotangentPresheafIso :
    relativeCotangentPresheaf (g ≫ f) ≅
      openImmersionPresheafRestrict g (relativeCotangentPresheaf f) :=
  PresheafOfModules.isoMk
    (fun U => (LinearEquiv.ofBijective
      ((cotangentPresheafMap f g).app U).hom
      (kaehlerCoefficientMap_bijective
        ((relativeConstants (g ≫ f)).app U)
        ((relativeConstants f).app (g.opensFunctor.op.obj U))
        (g.appIso U.unop).symm (constantsSquare_inv f g U))).toModuleIso)
    (fun {_ _} i => (cotangentPresheafMap f g).naturality i)

def cotangentRestrictIso :
    (Scheme.Modules.restrictFunctor g).obj (relativeCotangentSheaf f) ≅
      relativeCotangentSheaf (g ≫ f) :=
  openImmersionSheafificationIso g (relativeCotangentPresheaf f) ≪≫
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).mapIso
      (cotangentPresheafIso f g).symm

/-- Actual global relative cotangent objects respect true native open pullback. -/
def cotangentPullbackIso :
    (Scheme.Modules.pullback g).obj (relativeCotangentSheaf f) ≅
      relativeCotangentSheaf (g ≫ f) :=
  ((Scheme.Modules.restrictFunctorIsoPullback g).app (relativeCotangentSheaf f)).symm ≪≫
    cotangentRestrictIso f g

set_option backward.isDefEq.respectTransparency false

local instance (U : Y.Opensᵒᵖ) : Module (Y.presheaf.obj U)
    ((relativeCotangentPresheaf (g ≫ f)).obj U) :=
  ((relativeCotangentPresheaf (g ≫ f)).obj U).isModule

local instance (U : X.Opensᵒᵖ) : Module (X.presheaf.obj U)
    ((relativeCotangentPresheaf f).obj U) :=
  ((relativeCotangentPresheaf f).obj U).isModule

def cotangentSemilinear (U : Y.Opensᵒᵖ) :
    (relativeCotangentPresheaf (g ≫ f)).obj U →ₛₗ[(g.appIso U.unop).inv.hom]
      (relativeCotangentPresheaf f).obj (g.opensFunctor.op.obj U) where
  toFun := (cotangentPresheafMap f g).app U
  map_add' := ((cotangentPresheafMap f g).app U).hom.map_add
  map_smul' a x := ((cotangentPresheafMap f g).app U).hom.map_smul a x

def exteriorComponent (q : ℕ) (U : Y.Opensᵒᵖ) :
    (relativeExteriorPresheaf (g ≫ f) q).obj U ⟶
      (openImmersionPresheafRestrict g (relativeExteriorPresheaf f q)).obj U := by
  let E := exteriorSemilinearMap (g.appIso U.unop).inv.hom (cotangentSemilinear f g U) q
  exact ModuleCat.ofHom
    (X := (relativeExteriorPresheaf (g ≫ f) q).obj U)
    (Y := (openImmersionPresheafRestrict g (relativeExteriorPresheaf f q)).obj U)
    { toFun := E, map_add' := E.map_add, map_smul' := E.map_smulₛₗ }

theorem exteriorComponent_wedge (q : ℕ) (U : Y.Opensᵒᵖ)
    (m : Fin q → (relativeCotangentPresheaf (g ≫ f)).obj U) :
    exteriorComponent f g q U (exteriorPower.ιMulti (Y.presheaf.obj U) q m) =
      exteriorPower.ιMulti (X.presheaf.obj (g.opensFunctor.op.obj U)) q
        (M := (relativeCotangentPresheaf f).obj (g.opensFunctor.op.obj U))
        (fun j => cotangentSemilinear f g U (m j)) :=
  exteriorSemilinearMap_ιMulti (g.appIso U.unop).inv.hom (cotangentSemilinear f g U) q m

set_option backward.isDefEq.respectTransparency true in
def exteriorPresheafMap (q : ℕ) :
    relativeExteriorPresheaf (g ≫ f) q ⟶
      openImmersionPresheafRestrict g (relativeExteriorPresheaf f q) where
  app U := exteriorComponent f g q U
  naturality {U V} i := by
    apply ModuleCat.Hom.ext
    apply LinearMap.ext_on (exteriorPower.ιMulti_span
      (Y.presheaf.obj U) q ((relativeCotangentPresheaf (g ≫ f)).obj U))
    rintro _ ⟨m, rfl⟩
    change exteriorComponent f g q V
        ((relativeExteriorPresheaf (g ≫ f) q).map i
          (exteriorPower.ιMulti (Y.presheaf.obj U) q m)) =
      (relativeExteriorPresheaf f q).map (g.opensFunctor.op.map i)
        (exteriorComponent f g q U (exteriorPower.ιMulti (Y.presheaf.obj U) q m))
    refine (congrArg (exteriorComponent f g q V)
      (exteriorPresheaf_map_mk (relativeCotangentPresheaf (g ≫ f)) q i m)).trans ?_
    refine (exteriorComponent_wedge f g q V _).trans ?_
    refine Eq.trans ?_ ((congrArg ((relativeExteriorPresheaf f q).map
      (g.opensFunctor.op.map i)) (exteriorComponent_wedge f g q U m)).symm)
    refine Eq.trans ?_ (exteriorPresheaf_map_mk (relativeCotangentPresheaf f) q
      (g.opensFunctor.op.map i) _).symm
    congr 1
    funext j
    exact PresheafOfModules.naturality_apply (cotangentPresheafMap f g) i (m j)

theorem exteriorComponent_bijective (q : ℕ) (U : Y.Opensᵒᵖ) :
    Function.Bijective (exteriorComponent f g q U) := by
  exact exteriorSemilinearMap_bijective_of_ringIso
    (g.appIso U.unop).symm.commRingCatIsoToRingEquiv (cotangentSemilinear f g U)
    (kaehlerCoefficientMap_bijective
      ((relativeConstants (g ≫ f)).app U)
      ((relativeConstants f).app (g.opensFunctor.op.obj U))
      (g.appIso U.unop).symm (constantsSquare_inv f g U)) q

def exteriorPresheafIso (q : ℕ) :
    relativeExteriorPresheaf (g ≫ f) q ≅
      openImmersionPresheafRestrict g (relativeExteriorPresheaf f q) :=
  PresheafOfModules.isoMk
    (fun U => (LinearEquiv.ofBijective (exteriorComponent f g q U).hom
      (exteriorComponent_bijective f g q U)).toModuleIso)
    (fun {_ _} i => (exteriorPresheafMap f g q).naturality i)

def exteriorRestrictIso (q : ℕ) :
    (Scheme.Modules.restrictFunctor g).obj (relativeExteriorSheaf f q) ≅
      relativeExteriorSheaf (g ≫ f) q :=
  openImmersionSheafificationIso g (relativeExteriorPresheaf f q) ≪≫
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).mapIso
      (exteriorPresheafIso f g q).symm

/-- Every whole relative exterior object respects actual native open pullback. -/
def exteriorPullbackIso (q : ℕ) :
    (Scheme.Modules.pullback g).obj (relativeExteriorSheaf f q) ≅
      relativeExteriorSheaf (g ≫ f) q :=
  ((Scheme.Modules.restrictFunctorIsoPullback g).app (relativeExteriorSheaf f q)).symm ≪≫
    exteriorRestrictIso f g q

end EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalRestriction
