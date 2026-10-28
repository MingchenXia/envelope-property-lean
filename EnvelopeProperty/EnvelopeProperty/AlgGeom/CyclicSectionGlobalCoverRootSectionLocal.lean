import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverRootSectionCoordinates
import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverRootSectionPowers

/-! # Actual original line-valued root sections on the original charts -/
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.CyclicSectionGlobalCoverRootSectionLocal
open CanonicalGeometry NativeLineTransitionCocycles CyclicSectionGlobalCoverFrames
open CyclicSectionGlobalCover CyclicSectionGlobalCoverGluing
open CyclicSectionGlobalCoverRootSectionCoordinates CyclicSectionGlobalCoverRootSectionPowers
open SchemeLineSectionEvaluation SchemePulledPowerFrames SchemeGlobalSectionTensorPowerNorms

/-- Transition units commute with every actual original factor-frame pullback. -/
theorem transitionUnit_factor {X Y W : Scheme.{u}} (L : X.Modules)
    (i : W ⟶ Y) (b : Y ⟶ X) (g : W ⟶ X) (hi : i ≫ b = g)
    (e d : (pullback b).obj L ≅ unitObj Y) :
    transitionUnit (frameViaFactor i b g hi e) (frameViaFactor i b g hi d) =
      Units.map i.appTop.hom.toMonoidHom (transitionUnit e d) := by
  rw [transitionUnit, transitionUnit, ← unitScalar_pullback]
  congr 1
  apply Iso.ext
  simp only [frameViaFactor, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Iso.symm_inv,
    Category.assoc, Iso.hom_inv_id_assoc]

/-- Actual section transport through an original structural triangle. -/
def factorSection {X Y W : Scheme.{u}} (L : X.Modules)
    (i : W ⟶ Y) (b : Y ⟶ X) (g : W ⟶ X) (hi : i ≫ b = g)
    (τ : unitObj Y ⟶ (pullback b).obj L) : unitObj W ⟶ (pullback g).obj L :=
  pullbackSectionHom i τ ≫ (frameFactorIso i b g hi L).hom

/-- Actual factor transport pulls back the same original frame coefficient. -/
theorem factorSection_coefficient {X Y W : Scheme.{u}} (L : X.Modules)
    (i : W ⟶ Y) (b : Y ⟶ X) (g : W ⟶ X) (hi : i ≫ b = g)
    (τ : unitObj Y ⟶ (pullback b).obj L)
    (e : (pullback b).obj L ≅ unitObj Y) (a : Γ(Y, ⊤))
    (ha : τ ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection a) :
    factorSection L i b g hi τ ≫ (frameViaFactor i b g hi e).hom =
      ModularCurves.unitEndomorphismOfTopSection (i.appTop a) := by
  simp only [factorSection, frameViaFactor, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc]
  unfold pullbackSectionHom
  rw [Category.assoc, ← Category.assoc ((pullback i).map τ), ← Functor.map_comp, ha]
  exact ModularCurves.pullback_unitEndomorphismOfTopSection i a

variable {X : Scheme.{u}} (L : X.Modules) (n : ℕ)
  (s : unitObj X ⟶ bundleTensorPower L n)

/-- The original frame transported through the true identity structural triangle. -/
def normalizedFrame (c : FramedOpen L) : (pullback c.1.ι).obj L ≅ unitObj c.1.toScheme :=
  frameViaFactor (𝟙 _) c.1.ι c.1.ι (Category.id_comp _) c.2

/-- Identity transport keeps the coefficient of the SAME original section. -/
theorem normalizedFrame_coefficient (c : FramedOpen L) :
    sectionCoefficient L n s c.1.ι (normalizedFrame L c) = coefficient L n s c :=
  sectionCoefficient_factor L n s c.1.ι c.2 (𝟙 _) c.1.ι (Category.id_comp _)

/-- Normalized genuine original frames still have the SAME derived chart transition. -/
theorem normalizedFrame_transition {c d : FramedOpen L} (h : c ⟶ d) :
    transitionUnit (normalizedFrame L c)
      (frameViaFactor (X.homOfLE h.hom.le) d.1.ι c.1.ι (Scheme.homOfLE_ι _ _)
        (normalizedFrame L d)) = frameUnit L h := by
  have hd := siteFrame_comp L (𝟙 (frameObject L d)) (frameArrow L h) d.2
  rw [Category.comp_id] at hd
  change transitionUnit (siteFrame L (𝟙 (frameObject L c)) c.2)
    (siteFrame L (frameArrow L h) (siteFrame L (𝟙 (frameObject L d)) d.2)) = _
  rw [hd]
  rfl

/-- The original chart's entire structural map to the original base scheme. -/
def localBase (c : FramedOpen L) : chart L n s c ⟶ X :=
  projection c.1.toScheme n (coefficient L n s c) ≫ c.1.ι

/-- The actual induced original line frame on the original cyclic equation. -/
def localFrame (c : FramedOpen L) :
    (pullback (localBase L n s c)).obj L ≅ unitObj (chart L n s c) :=
  frameViaFactor (projection c.1.toScheme n (coefficient L n s c)) c.1.ι
    (localBase L n s c) rfl (normalizedFrame L c)

/-- The actual original root, now as a section of the original pulled line. -/
def localRoot (c : FramedOpen L) :
    unitObj (chart L n s c) ⟶ (pullback (localBase L n s c)).obj L :=
  ModularCurves.unitEndomorphismOfTopSection
    (rootCoordinate c.1.toScheme n (coefficient L n s c)) ≫ (localFrame L n s c).inv

/-- The actual chart section retains the original quotient root in its original frame. -/
theorem localRoot_coefficient (c : FramedOpen L) :
    localRoot L n s c ≫ (localFrame L n s c).hom =
      ModularCurves.unitEndomorphismOfTopSection
        (rootCoordinate c.1.toScheme n (coefficient L n s c)) := by
  simp only [localRoot, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The coefficient of the SAME pulled original power-section is the original coefficient image. -/
theorem localFrame_sectionCoefficient (c : FramedOpen L) :
    sectionCoefficient L n s (localBase L n s c) (localFrame L n s c) =
      (projection c.1.toScheme n (coefficient L n s c)).appTop (coefficient L n s c) := by
  rw [localFrame, sectionCoefficient_factor, normalizedFrame_coefficient]
  rfl

/-- The actual original local root section satisfies the SAME original section equation. -/
theorem localRoot_power (c : FramedOpen L) :
    powerSectionHom (localRoot L n s c) n =
      pullbackSectionHom (localBase L n s c) s ≫
        (BundleTensorPowerPullback.pullbackIso (localBase L n s c) L n).hom := by
  apply (cancel_mono (SchemeTensorPowerFrames.powerFrame (localFrame L n s c) n).hom).mp
  rw [powerSectionHom_frame _ _ _ (localRoot_coefficient L n s c), rootCoordinate_pow]
  have hs := unitHom_eq_globalScalar (pullbackSectionHom (localBase L n s c) s ≫
    (pullbackPowerFrame (localBase L n s c) (localFrame L n s c) n).hom)
  change _ = ModularCurves.unitEndomorphismOfTopSection
    (sectionCoefficient L n s (localBase L n s c) (localFrame L n s c)) at hs
  rw [localFrame_sectionCoefficient] at hs
  exact hs.symm

/-- Actual chart restriction transports precisely the original target frame. -/
theorem localFrame_factor {c d : FramedOpen L} (h : c ⟶ d) :
    frameViaFactor (chartMap L n s h) (localBase L n s d) (localBase L n s c)
      (chartMap_base L n s h) (localFrame L n s d) =
    frameViaFactor (projection c.1.toScheme n (coefficient L n s c)) c.1.ι (localBase L n s c) rfl
      (frameViaFactor (X.homOfLE h.hom.le) d.1.ι c.1.ι (Scheme.homOfLE_ι _ _)
        (normalizedFrame L d)) := by
  rw [localFrame, frameViaFactor_comp, frameViaFactor_comp]
  simp only [chartMap_projection]

/-- The original degree-one chart frames have precisely the pulled original transition unit. -/
theorem localFrame_transition {c d : FramedOpen L} (h : c ⟶ d) :
    transitionUnit (localFrame L n s c)
      (frameViaFactor (chartMap L n s h) (localBase L n s d) (localBase L n s c)
        (chartMap_base L n s h) (localFrame L n s d)) =
      Units.map (projection c.1.toScheme n (coefficient L n s c)).appTop.hom.toMonoidHom
        (frameUnit L h) := by
  rw [localFrame_factor, localFrame, transitionUnit_factor, normalizedFrame_transition L h]
  rfl

/-- The actual original local root sections agree through every genuine original chart inclusion. -/
theorem localRoot_factor {c d : FramedOpen L} (h : c ⟶ d) :
    factorSection L (chartMap L n s h) (localBase L n s d) (localBase L n s c)
      (chartMap_base L n s h) (localRoot L n s d) = localRoot L n s c := by
  let ed := frameViaFactor (chartMap L n s h) (localBase L n s d) (localBase L n s c)
    (chartMap_base L n s h) (localFrame L n s d)
  apply (cancel_mono ed.hom).mp
  rw [factorSection_coefficient L _ _ _ _ _ _ _ (localRoot_coefficient L n s d)]
  have hu := congrArg Iso.hom (unitScalar_spec ((localFrame L n s c).symm ≪≫ ed))
  change (localFrame L n s c).inv ≫ ed.hom =
    ModularCurves.unitEndomorphismOfTopSection
      (transitionUnit (localFrame L n s c) ed : Γ(chart L n s c, ⊤)) at hu
  rw [show transitionUnit (localFrame L n s c) ed = _ from localFrame_transition L n s h] at hu
  change _ = (ModularCurves.unitEndomorphismOfTopSection _ ≫ (localFrame L n s c).inv) ≫ ed.hom
  rw [Category.assoc, hu, ModularCurves.unitEndomorphismOfTopSection_comp, chartMap_rootCoordinate]
  congr 1
  exact mul_comm _ _

end EnvelopeProperty.CyclicSectionGlobalCoverRootSectionLocal
