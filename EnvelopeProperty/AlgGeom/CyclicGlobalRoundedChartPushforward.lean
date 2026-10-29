import EnvelopeProperty.AlgGeom.SchemeOpenRestrictionModuleMorphismDescent
import EnvelopeProperty.AlgGeom.CyclicSectionStructuralUnitOpenSquare
import EnvelopeProperty.AlgGeom.CyclicSectionSNCOriginalRoundedGluing

/-! # Actual chart comparisons of the global rounded-cover pushforward

These comparison producers retain the original global projection, original
chart projections, their structure units and their exact whole composition.
No weighted decomposition or global unit retraction is asserted here.
-/
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CyclicGlobalRoundedChartPushforward

def cartesianUnitComparison {B V C D : Scheme.{u}}
    (p : V ⟶ B) (q : D ⟶ C) (g : D ⟶ V) (f : C ⟶ B)
    [IsOpenImmersion g] [IsOpenImmersion f] (H : IsPullback q g f p) :
    (restrictFunctor f).obj ((pushforward p).obj (unitObj V)) ≅
      (pushforward q).obj (unitObj D) :=
  restrictPushforwardIsoOfIsPullbackApp p q g f H (unitObj V) ≪≫
    (pushforward q).mapIso (restrictUnitIso g)

private theorem cartesianUnitComparison_app {B V C D : Scheme.{u}}
    (p : V ⟶ B) (q : D ⟶ C) (g : D ⟶ V) (f : C ⟶ B)
    [IsOpenImmersion g] [IsOpenImmersion f] (H : IsPullback q g f p)
    (W : C.Opens) (x : Γ(((pushforward p).obj (unitObj V)).restrict f, W)) :
    (cartesianUnitComparison p q g f H).hom.app W x =
      (g.appIso (q ⁻¹ᵁ W)).hom
        (V.presheaf.map (eqToHom
          (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W)).op x) := rfl

def restrictionComposition {B C D : Scheme.{u}} (M : B.Modules)
    (g : D ⟶ C) (f : C ⟶ B) (h : D ⟶ B)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsOpenImmersion h] (w : g ≫ f = h) :
    M.restrict h ≅ (M.restrict f).restrict g :=
  (restrictFunctorCongr w.symm).app M ≪≫ (restrictFunctorComp g f).app M

private theorem image_factor {B C D : Scheme.{u}} (g : D ⟶ C) (f : C ⟶ B)
    (h : D ⟶ B) [IsOpenImmersion g] [IsOpenImmersion f] [IsOpenImmersion h]
    (w : g ≫ f = h) (W : D.Opens) : f ''ᵁ (g ''ᵁ W) = h ''ᵁ W := by
  simpa only [w] using (Scheme.Hom.comp_image g f W).symm

theorem restrictionComposition_app {B C D : Scheme.{u}} (M : B.Modules)
    (g : D ⟶ C) (f : C ⟶ B) (h : D ⟶ B)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsOpenImmersion h] (w : g ≫ f = h)
    (W : D.Opens) (x : Γ(M.restrict h, W)) :
    (restrictionComposition M g f h w).hom.app W x =
      M.presheaf.map (eqToHom (image_factor g f h w W)).op x := by
  let α := (restrictFunctorCongr w.symm).hom.app M
  let β := (restrictFunctorComp g f).hom.app M
  have ha := ConcreteCategory.congr_hom
    (restrictFunctorCongr_hom_app_app (U := W) w.symm M) x
  have hb := ConcreteCategory.congr_hom (restrictFunctorComp_hom_app_app (U := W) g f M)
  change β.app W (α.app W x) = _
  rw [ha]
  erw [hb]
  change M.presheaf.map _ (M.presheaf.map _ x) = _
  rw [← M.presheaf.map_comp_apply]
  exact ConcreteCategory.congr_hom (M.presheaf.congr_map (Subsingleton.elim _ _)) x

theorem cartesianUnitComparison_comp
    {B V C D Yc Yd : Scheme.{u}} (p : V ⟶ B)
    (q : Yd ⟶ D) (r : Yc ⟶ C) (gd : Yd ⟶ V) (gc : Yc ⟶ V)
    (k : Yc ⟶ Yd) (fd : D ⟶ B) (fc : C ⟶ B) (g : C ⟶ D)
    [IsOpenImmersion gd] [IsOpenImmersion gc] [IsOpenImmersion k]
    [IsOpenImmersion fd] [IsOpenImmersion fc] [IsOpenImmersion g]
    (HD : IsPullback q gd fd p) (HC : IsPullback r gc fc p)
    (HK : IsPullback r k g q) (hk : k ≫ gd = gc) (hg : g ≫ fd = fc) :
    (restrictionComposition ((pushforward p).obj (unitObj V)) g fd fc hg).hom ≫
      (restrictFunctor g).map (cartesianUnitComparison p q gd fd HD).hom ≫
      (cartesianUnitComparison q r k g HK).hom =
        (cartesianUnitComparison p r gc fc HC).hom := by
  apply (fullyFaithfulToPresheafOfModules).map_injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let hD := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback HD (g ''ᵁ W.unop)
  let hC := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback HC W.unop
  let hK := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback HK W.unop
  change (k.appIso (r ⁻¹ᵁ W.unop)).hom
    (Yd.presheaf.map (eqToHom hK).op
      ((gd.appIso (q ⁻¹ᵁ g ''ᵁ W.unop)).hom
        (V.presheaf.map (eqToHom hD).op
          (((restrictionComposition ((pushforward p).obj (unitObj V)) g fd fc hg).hom).app
            W.unop x)))) =
    (gc.appIso (r ⁻¹ᵁ W.unop)).hom (V.presheaf.map (eqToHom hC).op x)
  erw [restrictionComposition_app]
  let j := (TopologicalSpace.Opens.map p.base).map (eqToHom (image_factor g fd fc hg W.unop))
  change (k.appIso (r ⁻¹ᵁ W.unop)).hom
    (Yd.presheaf.map (eqToHom hK).op
      ((gd.appIso (q ⁻¹ᵁ g ''ᵁ W.unop)).hom
        (V.presheaf.map (eqToHom hD).op (V.presheaf.map j.op x)))) = _
  have he : V.presheaf.map j.op ≫ V.presheaf.map (eqToHom hD).op ≫
      (gd.appIso (q ⁻¹ᵁ g ''ᵁ W.unop)).hom ≫ Yd.presheaf.map (eqToHom hK).op ≫
        (k.appIso (r ⁻¹ᵁ W.unop)).hom =
      V.presheaf.map (eqToHom hC).op ≫ (gc.appIso (r ⁻¹ᵁ W.unop)).hom := by
    simp only [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE, hk]
  exact ConcreteCategory.congr_hom he x


open CanonicalGeometry CyclicSectionSNCAdaptedFramedAtlas
open CyclicSectionSNCAdaptedRoundedCharts CyclicSectionSNCAdaptedRoundedDiagram
variable {X : Scheme.{u}} [IsIntegral X]
variable (L : X.Modules) (hL : IsInvertible L) (n : ℕ)
  (s : unitObj X ⟶ bundleTensorPower L n)
variable {k : Type u} [Field k] [PerfectField k]
variable (f : X ⟶ Spec (CommRingCat.of k)) (d : ℕ) [SmoothOfRelativeDimension d f]
variable {F : Scheme.DivisorFamily X} (hF : F.IsSnc) (a : F.ι → ℕ)
variable (hJF : LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L n)
  (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n) s = ∏ i, F.component i ^ a i)
  (hn : 0 < n)
local notation "Y₀" => CyclicSectionSNCOriginalRoundedGluing.gluedScheme L hL n s f d hF a hJF hn
local notation "p₀" => CyclicSectionSNCOriginalRoundedGluing.gluedProjection L hL n s f d hF a hJF hn
local notation "j₀" => CyclicSectionSNCOriginalRoundedGluing.chartι L hL n s f d hF a hJF hn

/-- The actual pushforward of the actual structure module along the original geometrically glued projection. -/
def globalPushforward : X.Modules := (pushforward p₀).obj (unitObj Y₀)

local notation "P₀" => globalPushforward L hL n s f d hF a hJF hn

/-- The SAME actual chart square is cartesian over the actual original coefficient spectrum. -/
theorem chartSpec_isPullback (c : Chart L n s F a) :
    IsPullback (affineProjection c hn) (j₀ c) (chartAffine c).2.fromSpec p₀ := by
  exact (CyclicSectionSNCOriginalRoundedGluing.isPullback_chartι L hL n s f d hF a hJF hn c).of_iso
    (Iso.refl _) (chartAffine c).2.isoSpec (Iso.refl _) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.id_comp] using projection_affine c hn)
    (by simp)
    (by simpa only [Iso.refl_hom, Category.comp_id] using
      (chartAffine c).2.isoSpec_hom_fromSpec.symm)
    (by simp)

/-- The entire actual global pushforward restricted to the original open is the SAME chart pushforward. -/
def chartPushforwardUnitIso (c : Chart L n s F a) :
    (P₀).restrict (chartAffine c).1.ι ≅ (pushforward (projection c hn)).obj (unitObj (chart c hn)) :=
  cartesianUnitComparison p₀ (projection c hn) (j₀ c) (chartAffine c).1.ι
    (CyclicSectionSNCOriginalRoundedGluing.isPullback_chartι L hL n s f d hF a hJF hn c)

/-- On every actual original-open section this is the original chart-inclusion function isomorphism. -/
theorem chartPushforwardUnitIso_app (c : Chart L n s F a)
    (W : (chartAffine c).1.toScheme.Opens) (x : Γ((P₀).restrict (chartAffine c).1.ι, W)) :
    (chartPushforwardUnitIso L hL n s f d hF a hJF hn c).hom.app W x =
      ((j₀ c).appIso (projection c hn ⁻¹ᵁ W)).hom
        ((Y₀).presheaf.map (eqToHom
          (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
            (CyclicSectionSNCOriginalRoundedGluing.isPullback_chartι L hL n s f d hF a hJF hn c) W)).op x) :=
  cartesianUnitComparison_app _ _ _ _ _ W x

/-- The actual original-open comparison preserves the actual canonical structural unit. -/
theorem chartPushforwardUnitIso_unit (c : Chart L n s F a) :
    (restrictFunctor (chartAffine c).1.ι).map
        (SheafOfModules.unitToPushforwardObjUnit (p₀).toRingCatSheafHom) ≫
      (chartPushforwardUnitIso L hL n s f d hF a hJF hn c).hom =
    (restrictUnitIso (chartAffine c).1.ι).hom ≫
      SheafOfModules.unitToPushforwardObjUnit (projection c hn).toRingCatSheafHom :=
  CyclicSectionStructuralUnitRestriction.restrictPushforwardUnit_triangle _ _ _ _ _

private instance chartMap_open {c e : Chart L n s F a} (h : c ⟶ e) :
    IsOpenImmersion (chartMap h hn) := by
  apply MorphismProperty.of_isPullback (chartMap_isPullback h hn).flip
  infer_instance

/-- The complete actual original-open comparison composes through every original chart arrow. -/
theorem chartPushforwardUnitIso_comp {c e : Chart L n s F a} (h : c ⟶ e) :
    (restrictOpenCompIso h.hom).hom.app (P₀) ≫
      (restrictFunctor (X.homOfLE h.hom.le)).map
        (chartPushforwardUnitIso L hL n s f d hF a hJF hn e).hom ≫
      (restrictPushforwardIsoOfIsPullbackApp (projection e hn) (projection c hn)
        (chartMap h hn) (X.homOfLE h.hom.le) (chartMap_isPullback h hn).flip
          (unitObj (chart e hn))).hom ≫
      (pushforward (projection c hn)).map (restrictUnitIso (chartMap h hn)).hom =
    (chartPushforwardUnitIso L hL n s f d hF a hJF hn c).hom :=
  cartesianUnitComparison_comp p₀ (projection e hn) (projection c hn) (j₀ e) (j₀ c)
    (chartMap h hn) (chartAffine e).1.ι (chartAffine c).1.ι (X.homOfLE h.hom.le)
    (CyclicSectionSNCOriginalRoundedGluing.isPullback_chartι L hL n s f d hF a hJF hn e)
    (CyclicSectionSNCOriginalRoundedGluing.isPullback_chartι L hL n s f d hF a hJF hn c)
    (chartMap_isPullback h hn).flip
    (CyclicSectionSNCOriginalRoundedGluing.chartMap_chartι L hL n s f d hF a hJF hn h)
    (X.homOfLE_ι h.hom.le)

/-- The actual coefficient-spectrum restriction is the SAME literal native affine chart pushforward. -/
def chartSpecPushforwardUnitIso (c : Chart L n s F a) :
    (P₀).restrict (chartAffine c).2.fromSpec ≅
      (pushforward (affineProjection c hn)).obj (unitObj (chart c hn)) :=
  cartesianUnitComparison p₀ (affineProjection c hn) (j₀ c) (chartAffine c).2.fromSpec
    (chartSpec_isPullback L hL n s f d hF a hJF hn c)

/-- Its actual value on EVERY coefficient-spectrum open is the original function isomorphism. -/
theorem chartSpecPushforwardUnitIso_app (c : Chart L n s F a)
    (W : (Spec (CommRingCat.of (coefficientRing c))).Opens)
    (x : Γ((P₀).restrict (chartAffine c).2.fromSpec, W)) :
    (chartSpecPushforwardUnitIso L hL n s f d hF a hJF hn c).hom.app W x =
      ((j₀ c).appIso (affineProjection c hn ⁻¹ᵁ W)).hom
        ((Y₀).presheaf.map (eqToHom
          (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
            (chartSpec_isPullback L hL n s f d hF a hJF hn c) W)).op x) :=
  cartesianUnitComparison_app _ _ _ _ _ W x

private instance coefficientSpec_open {c e : Chart L n s F a} (h : c ⟶ e) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (CyclicSectionSNCAdaptedRoundedTransitions.restriction h))) := by
  have he : Spec.map (CommRingCat.ofHom
      (CyclicSectionSNCAdaptedRoundedTransitions.restriction h)) =
      (chartAffine c).2.isoSpec.inv ≫ X.homOfLE h.hom.le ≫ (chartAffine e).2.isoSpec.hom := by
    apply (cancel_epi (chartAffine c).2.isoSpec.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using affine_naturality h
  rw [he]
  infer_instance

omit [IsIntegral X] in
private theorem coefficientBaseEquation {c e : Chart L n s F a} (h : c ⟶ e) :
    Spec.map (CommRingCat.ofHom (CyclicSectionSNCAdaptedRoundedTransitions.restriction h)) ≫
      (chartAffine e).2.fromSpec = (chartAffine c).2.fromSpec := by
  change Spec.map (CommRingCat.ofHom (CyclicSectionSNCAdaptedRoundedTransitions.restriction h)) ≫
    ((chartAffine e).2.isoSpec.inv ≫ (chartAffine e).1.ι) =
      (chartAffine c).2.isoSpec.inv ≫ (chartAffine c).1.ι
  rw [← Category.assoc, affine_inv_naturality h, Category.assoc, X.homOfLE_ι h.hom.le]

/-- The actual global module's coefficient-chart restriction comparison uses precisely the original base arrow. -/
def chartSpecRestrictionIso {c e : Chart L n s F a} (h : c ⟶ e) :
    (P₀).restrict (chartAffine c).2.fromSpec ≅
      ((P₀).restrict (chartAffine e).2.fromSpec).restrict
        (Spec.map (CommRingCat.ofHom (CyclicSectionSNCAdaptedRoundedTransitions.restriction h))) :=
  restrictionComposition (P₀)
    (Spec.map (CommRingCat.ofHom (CyclicSectionSNCAdaptedRoundedTransitions.restriction h)))
    (chartAffine e).2.fromSpec (chartAffine c).2.fromSpec (coefficientBaseEquation L n s a h)

/-- The SAME entire coefficient-spectrum chart comparison composes through the actual whole rounded map. -/
theorem chartSpecPushforwardUnitIso_comp {c e : Chart L n s F a} (h : c ⟶ e) :
    (chartSpecRestrictionIso L hL n s f d hF a hJF hn h).hom ≫
      (restrictFunctor (Spec.map (CommRingCat.ofHom
        (CyclicSectionSNCAdaptedRoundedTransitions.restriction h)))).map
          (chartSpecPushforwardUnitIso L hL n s f d hF a hJF hn e).hom ≫
      (restrictPushforwardIsoOfIsPullbackApp (affineProjection e hn) (affineProjection c hn)
        (chartMap h hn)
        (Spec.map (CommRingCat.ofHom (CyclicSectionSNCAdaptedRoundedTransitions.restriction h)))
        (chartMap_affine_isPullback h hn).flip (unitObj (chart e hn))).hom ≫
      (pushforward (affineProjection c hn)).map (restrictUnitIso (chartMap h hn)).hom =
    (chartSpecPushforwardUnitIso L hL n s f d hF a hJF hn c).hom :=
  cartesianUnitComparison_comp p₀ (affineProjection e hn) (affineProjection c hn) (j₀ e) (j₀ c)
    (chartMap h hn) (chartAffine e).2.fromSpec (chartAffine c).2.fromSpec
    (Spec.map (CommRingCat.ofHom (CyclicSectionSNCAdaptedRoundedTransitions.restriction h)))
    (chartSpec_isPullback L hL n s f d hF a hJF hn e)
    (chartSpec_isPullback L hL n s f d hF a hJF hn c)
    (chartMap_affine_isPullback h hn).flip
    (CyclicSectionSNCOriginalRoundedGluing.chartMap_chartι L hL n s f d hF a hJF hn h)
    (coefficientBaseEquation L n s a h)

end EnvelopeProperty.CyclicGlobalRoundedChartPushforward
