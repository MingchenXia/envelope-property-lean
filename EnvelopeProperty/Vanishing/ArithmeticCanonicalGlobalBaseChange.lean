import EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalFrames

/-! # The actual global base-change differential on arithmetic fibres

The fibre is the native categorical pullback with original X as the first
factor. Structural coefficients, universal derivations and both adjunctions
construct the whole global morphism without any comparison certificate.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalBaseChange

open CanonicalGeometry ArithmeticCanonicalGlobal

section Constants

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

theorem morphismConstantsSquare (f : X ⟶ Spec (.of R)) (g : Y ⟶ X) (U : X.Opens) :
    (relativeConstants f).app (.op U) ≫ g.app U =
      (relativeConstants (g ≫ f)).app (.op (g ⁻¹ᵁ U)) := by
  have htop : g.appLE ⊤ ⊤ (by simp) = g.appTop := by
    unfold Scheme.Hom.appLE
    change g.appTop ≫ Y.presheaf.map (𝟙 (op ⊤)) = g.appTop
    simp
  have hu : g.appLE U (g ⁻¹ᵁ U) le_rfl = g.app U := by
    unfold Scheme.Hom.appLE
    simp
  have hm : X.presheaf.map U.leTop.op ≫ g.app U =
      g.appTop ≫ Y.presheaf.map (g ⁻¹ᵁ U).leTop.op := by
    rw [← hu]
    exact ((g.map_appLE le_rfl U.leTop.op).trans
      (g.appLE_map (U := ⊤) (V := ⊤) (by simp)
        (g ⁻¹ᵁ U).leTop.op).symm).trans
      (congrArg (fun h => h ≫ Y.presheaf.map (g ⁻¹ᵁ U).leTop.op) htop)
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ X.presheaf.map U.leTop.op) ≫
      g.app U = (Scheme.ΓSpecIso (.of R)).inv ≫ (g ≫ f).appTop ≫
        Y.presheaf.map (g ⁻¹ᵁ U).leTop.op
  rw [Scheme.Hom.comp_appTop]
  simp only [Category.assoc]
  rw [hm]

theorem compositionConstants {S : Type u} [CommRing S]
    (φ : CommRingCat.of R ⟶ CommRingCat.of S) (h : Y ⟶ Spec (.of S)) (U : Y.Opensᵒᵖ) :
    (relativeConstants (h ≫ Spec.map φ)).app U = φ ≫ (relativeConstants h).app U := by
  change (Scheme.ΓSpecIso (.of R)).inv ≫ (h ≫ Spec.map φ).appTop ≫
      Y.presheaf.map U.unop.leTop.op =
    φ ≫ (Scheme.ΓSpecIso (.of S)).inv ≫ h.appTop ≫ Y.presheaf.map U.unop.leTop.op
  have he := congrArg
    (fun z : CommRingCat.of R ⟶ Γ(Spec (.of S), ⊤) =>
      z ≫ h.appTop ≫ Y.presheaf.map U.unop.leTop.op)
    (Scheme.ΓSpecIso_inv_naturality φ).symm
  simpa only [Scheme.Hom.comp_appTop, Category.assoc] using he

end Constants

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

def baseMap : Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The actual categorical base change, with original X retained as first factor. -/
def fiberScheme : Scheme.{u} := Limits.pullback f (baseMap (R := R) S)

def fiberProjection : fiberScheme S f ⟶ X := Limits.pullback.fst f (baseMap (R := R) S)

def fiberStructure : fiberScheme S f ⟶ Spec (.of S) :=
  Limits.pullback.snd f (baseMap (R := R) S)

theorem fiberSquare : fiberProjection S f ≫ f = fiberStructure S f ≫ baseMap (R := R) S :=
  Limits.pullback.condition

theorem fiberConstantsSquare (U : X.Opens) :
    (relativeConstants f).app (.op U) ≫ (fiberProjection S f).app U =
      CommRingCat.ofHom (algebraMap R S) ≫
        (relativeConstants (fiberStructure S f)).app (.op (fiberProjection S f ⁻¹ᵁ U)) := by
  rw [morphismConstantsSquare, fiberSquare]
  exact compositionConstants (CommRingCat.ofHom (algebraMap R S)) (fiberStructure S f) _

set_option backward.isDefEq.respectTransparency false in
/-- The actual S-relative universal derivation annihilates the original
R-constants after the genuine fibre projection. -/
def cotangentDerivation :
    ((PresheafOfModules.pushforward (fiberProjection S f).toRingCatSheafHom.hom).obj
      (relativeCotangentPresheaf (fiberStructure S f))).Derivation' (relativeConstants f) where
  d {U} := (relativeDerivation (fiberStructure S f)).d.comp
    ((fiberProjection S f).app U.unop).hom.toAddMonoidHom
  d_mul {U} a b := by
    change (relativeDerivation (fiberStructure S f)).d
      ((fiberProjection S f).app U.unop (a * b)) = _
    rw [map_mul, (relativeDerivation (fiberStructure S f)).d_mul]
    rfl
  d_map {U V} i a := by
    change (relativeDerivation (fiberStructure S f)).d
      ((fiberProjection S f).app V.unop (X.presheaf.map i a)) = _
    have h : (fiberProjection S f).app V.unop (X.presheaf.map i a) =
        (fiberScheme S f).presheaf.map ((Opens.map (fiberProjection S f).base).op.map i)
          ((fiberProjection S f).app U.unop a) :=
      congr($((fiberProjection S f).c.naturality i).hom a)
    exact (congrArg (relativeDerivation (fiberStructure S f)).d h).trans
      ((relativeDerivation (fiberStructure S f)).d_map
        ((Opens.map (fiberProjection S f).base).op.map i) ((fiberProjection S f).app U.unop a))
  d_app {U} r := by
    change (relativeDerivation (fiberStructure S f)).d
      ((fiberProjection S f).app U.unop ((relativeConstants f).app U r)) = 0
    have h : (fiberProjection S f).app U.unop ((relativeConstants f).app U r) =
        (relativeConstants (fiberStructure S f)).app
          (.op (fiberProjection S f ⁻¹ᵁ U.unop)) (algebraMap R S r) :=
      congr($(fiberConstantsSquare S f U.unop).hom r)
    exact (congrArg (relativeDerivation (fiberStructure S f)).d h).trans
      ((relativeDerivation (fiberStructure S f)).d_app (algebraMap R S r))

def cotangentPresheafMap : relativeCotangentPresheaf f ⟶
    (PresheafOfModules.pushforward (fiberProjection S f).toRingCatSheafHom.hom).obj
      (relativeCotangentPresheaf (fiberStructure S f)) :=
  (relativeUniversal f).desc (cotangentDerivation S f)

theorem cotangentPresheafMap_d (U : X.Opens) (a : Γ(X, U)) :
    (cotangentPresheafMap S f).app (.op U) ((relativeDerivation f).d a) =
      (relativeDerivation (fiberStructure S f)).d ((fiberProjection S f).app U a) := by
  exact PresheafOfModules.Derivation.congr_d
    ((relativeUniversal f).fac (cotangentDerivation S f)) a

set_option backward.isDefEq.respectTransparency false in
def cotangentSheafPushMap : relativeCotangentSheaf f ⟶
    (Scheme.Modules.pushforward (fiberProjection S f)).obj
      (relativeCotangentSheaf (fiberStructure S f)) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
    (P := relativeCotangentPresheaf f)
    (F := (Scheme.Modules.pushforward (fiberProjection S f)).obj
      (relativeCotangentSheaf (fiberStructure S f)))).symm
    (cotangentPresheafMap S f ≫
      (PresheafOfModules.pushforward (fiberProjection S f).toRingCatSheafHom.hom).map
        (X := relativeCotangentPresheaf (fiberStructure S f))
        (Y := (relativeCotangentSheaf (fiberStructure S f)).val)
        (relativeCotangentSheafificationMap (fiberStructure S f)))

theorem cotangentSheafPushMap_unit :
    relativeCotangentSheafificationMap f ≫ (cotangentSheafPushMap S f).val =
      cotangentPresheafMap S f ≫
        (PresheafOfModules.pushforward (fiberProjection S f).toRingCatSheafHom.hom).map
          (X := relativeCotangentPresheaf (fiberStructure S f))
          (Y := (relativeCotangentSheaf (fiberStructure S f)).val)
          (relativeCotangentSheafificationMap (fiberStructure S f)) := by
  exact (PresheafOfModules.sheafificationHomEquiv
    (𝟙 X.ringCatSheaf.obj)).apply_symm_apply _

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual canonical whole-sheaf base-change differential. Its being an
isomorphism is a separate comparison obligation, not an input certificate. -/
def cotangentPullbackMap :
    (Scheme.Modules.pullback (fiberProjection S f)).obj (relativeCotangentSheaf f) ⟶
      relativeCotangentSheaf (fiberStructure S f) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (fiberProjection S f)).homEquiv _ _).symm
    (cotangentSheafPushMap S f)

theorem cotangentPullbackMap_unit :
    (Scheme.Modules.pullbackPushforwardAdjunction (fiberProjection S f)).unit.app
        (relativeCotangentSheaf f) ≫
      (Scheme.Modules.pushforward (fiberProjection S f)).map (cotangentPullbackMap S f) =
        cotangentSheafPushMap S f := by
  exact ((Scheme.Modules.pullbackPushforwardAdjunction (fiberProjection S f)).homEquiv
    _ _).apply_symm_apply (cotangentSheafPushMap S f)

set_option backward.isDefEq.respectTransparency false

local instance (U : X.Opensᵒᵖ) : Module (X.presheaf.obj U)
    ((relativeCotangentPresheaf f).obj U) := ((relativeCotangentPresheaf f).obj U).isModule

local instance (U : (fiberScheme S f).Opensᵒᵖ) : Module ((fiberScheme S f).presheaf.obj U)
    ((relativeCotangentPresheaf (fiberStructure S f)).obj U) :=
  ((relativeCotangentPresheaf (fiberStructure S f)).obj U).isModule

def cotangentSemilinear (U : X.Opensᵒᵖ) :
    (relativeCotangentPresheaf f).obj U →ₛₗ[((fiberProjection S f).app U.unop).hom]
      (relativeCotangentPresheaf (fiberStructure S f)).obj
        ((Opens.map (fiberProjection S f).base).op.obj U) where
  toFun := (cotangentPresheafMap S f).app U
  map_add' := ((cotangentPresheafMap S f).app U).hom.map_add
  map_smul' r x := ((cotangentPresheafMap S f).app U).hom.map_smul r x

def exteriorComponent (q : ℕ) (U : X.Opensᵒᵖ) :
    (relativeExteriorPresheaf f q).obj U ⟶
      ((PresheafOfModules.pushforward (fiberProjection S f).toRingCatSheafHom.hom).obj
        (relativeExteriorPresheaf (fiberStructure S f) q)).obj U := by
  let E := exteriorSemilinearMap ((fiberProjection S f).app U.unop).hom
    (cotangentSemilinear S f U) q
  exact ModuleCat.ofHom
    (X := (relativeExteriorPresheaf f q).obj U)
    (Y := ((PresheafOfModules.pushforward (fiberProjection S f).toRingCatSheafHom.hom).obj
      (relativeExteriorPresheaf (fiberStructure S f) q)).obj U)
    { toFun := E, map_add' := E.map_add, map_smul' := E.map_smulₛₗ }

theorem exteriorComponent_wedge (q : ℕ) (U : X.Opensᵒᵖ)
    (m : Fin q → (relativeCotangentPresheaf f).obj U) :
    exteriorComponent S f q U (exteriorPower.ιMulti (X.presheaf.obj U) q m) =
      exteriorPower.ιMulti ((fiberScheme S f).presheaf.obj
        ((Opens.map (fiberProjection S f).base).op.obj U)) q
        (M := (relativeCotangentPresheaf (fiberStructure S f)).obj
          ((Opens.map (fiberProjection S f).base).op.obj U))
        (fun j => cotangentSemilinear S f U (m j)) :=
  exteriorSemilinearMap_ιMulti ((fiberProjection S f).app U.unop).hom
    (cotangentSemilinear S f U) q m

set_option backward.isDefEq.respectTransparency true in
def exteriorPresheafMap (q : ℕ) : relativeExteriorPresheaf f q ⟶
    (PresheafOfModules.pushforward (fiberProjection S f).toRingCatSheafHom.hom).obj
      (relativeExteriorPresheaf (fiberStructure S f) q) where
  app U := exteriorComponent S f q U
  naturality {U V} i := by
    apply ModuleCat.Hom.ext
    apply LinearMap.ext_on (exteriorPower.ιMulti_span
      (X.presheaf.obj U) q ((relativeCotangentPresheaf f).obj U))
    rintro _ ⟨m, rfl⟩
    change exteriorComponent S f q V
        ((relativeExteriorPresheaf f q).map i (exteriorPower.ιMulti (X.presheaf.obj U) q m)) =
      (relativeExteriorPresheaf (fiberStructure S f) q).map
        ((Opens.map (fiberProjection S f).base).op.map i)
        (exteriorComponent S f q U (exteriorPower.ιMulti (X.presheaf.obj U) q m))
    refine (congrArg (exteriorComponent S f q V)
      (exteriorPresheaf_map_mk (relativeCotangentPresheaf f) q i m)).trans ?_
    refine (exteriorComponent_wedge S f q V _).trans ?_
    refine Eq.trans ?_ ((congrArg ((relativeExteriorPresheaf (fiberStructure S f) q).map
      ((Opens.map (fiberProjection S f).base).op.map i))
      (exteriorComponent_wedge S f q U m)).symm)
    refine Eq.trans ?_ (exteriorPresheaf_map_mk
      (relativeCotangentPresheaf (fiberStructure S f)) q
      ((Opens.map (fiberProjection S f).base).op.map i) _).symm
    congr 1
    funext j
    exact PresheafOfModules.naturality_apply (cotangentPresheafMap S f) i (m j)

def exteriorSheafPushMap (q : ℕ) : relativeExteriorSheaf f q ⟶
    (Scheme.Modules.pushforward (fiberProjection S f)).obj
      (relativeExteriorSheaf (fiberStructure S f) q) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).symm
    (exteriorPresheafMap S f q ≫
      (PresheafOfModules.pushforward (fiberProjection S f).toRingCatSheafHom.hom).map
        (exteriorSheafificationMap (relativeCotangentPresheaf (fiberStructure S f)) q))

theorem exteriorSheafPushMap_unit (q : ℕ) :
    exteriorSheafificationMap (relativeCotangentPresheaf f) q ≫
        (exteriorSheafPushMap S f q).val =
      exteriorPresheafMap S f q ≫
        (PresheafOfModules.pushforward (fiberProjection S f).toRingCatSheafHom.hom).map
          (exteriorSheafificationMap (relativeCotangentPresheaf (fiberStructure S f)) q) := by
  exact (PresheafOfModules.sheafificationHomEquiv
    (𝟙 X.ringCatSheaf.obj)).apply_symm_apply _

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual whole exterior base-change differential in every degree. -/
def exteriorPullbackMap (q : ℕ) :
    (Scheme.Modules.pullback (fiberProjection S f)).obj (relativeExteriorSheaf f q) ⟶
      relativeExteriorSheaf (fiberStructure S f) q :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (fiberProjection S f)).homEquiv _ _).symm
    (exteriorSheafPushMap S f q)

theorem exteriorPullbackMap_unit (q : ℕ) :
    (Scheme.Modules.pullbackPushforwardAdjunction (fiberProjection S f)).unit.app
        (relativeExteriorSheaf f q) ≫
      (Scheme.Modules.pushforward (fiberProjection S f)).map (exteriorPullbackMap S f q) =
        exteriorSheafPushMap S f q := by
  exact ((Scheme.Modules.pullbackPushforwardAdjunction (fiberProjection S f)).homEquiv
    _ _).apply_symm_apply (exteriorSheafPushMap S f q)

/-- For an actual field fibre the canonical morphism targets the already
existing native exterior object of that same whole categorical fibre. -/
def fieldExteriorPullbackMap (k : Type u) [Field k] [Algebra R k] (q : ℕ) :
    (Scheme.Modules.pullback (fiberProjection k f)).obj (relativeExteriorSheaf f q) ⟶
      exteriorCotangentSheaf (fiberStructure k f) q :=
  exteriorPullbackMap k f q ≫ (fieldExteriorIso (fiberStructure k f) q).hom

end EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalBaseChange
