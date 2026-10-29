import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationOpenUnit

/-! # Actual original twist and normalization maps on the section-open square

The native whole twist pullback carries multiplication by the SAME original
section power to multiplication by its SAME pulled power. Since actual
normalization is its inverse, cancellation derives the actual normalized
square, without an incoming cocycle or normalization matching equation.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleCechLineSectionLocalization
open CanonicalGeometry SchemeLineSectionEvaluation SchemeGlobalSectionTensorPowerNorms
attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable instance naturalPullbackMonoidal {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (pullback g).Monoidal := pullbackMonoidal g

private theorem tensorSectionMap_postcomp {X : Scheme.{u}} (F : X.Modules)
    {A B : X.Modules} (t : unitObj X ⟶ A) (f : A ⟶ B) :
    tensorSectionMap F t ≫ (𝟙 F ⊗ₘ f) = tensorSectionMap F (t ≫ f) := by
  simp only [tensorSectionMap, Category.assoc, id_tensorHom, whiskerLeft_comp]

/-- The actual WHOLE pullback of the SAME original F-twist, retaining the
native original tensor-power pullback comparison. -/
def twistPullbackIso {X Y : Scheme.{u}} (g : Y ⟶ X) (F L : X.Modules) (m : ℕ) :
    (pullback g).obj (F ⊗ bundleTensorPower L m) ≅
      (pullback g).obj F ⊗ bundleTensorPower ((pullback g).obj L) m :=
  (Functor.Monoidal.μIso (pullback g) F (bundleTensorPower L m)).symm ≪≫
    (Iso.refl _ ⊗ᵢ BundleTensorPowerPullback.pullbackIso g L m)

/-- Actual native pullback carries multiplication by the SAME original
s^m to multiplication by the SAME actual pulled s raised to m. -/
theorem powerSectionTensorMap_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F L : X.Modules) (s : unitObj X ⟶ L) (m : ℕ) :
    (pullback g).map (powerSectionTensorMap F L s m) ≫
        (twistPullbackIso g F L m).hom =
      powerSectionTensorMap ((pullback g).obj F) ((pullback g).obj L)
        (pullbackSectionHom g s) m := by
  change (pullback g).map (tensorSectionMap F (powerSectionHom s m)) ≫
    (Functor.Monoidal.μIso (pullback g) F (bundleTensorPower L m)).inv ≫
      (𝟙 _ ⊗ₘ (BundleTensorPowerPullback.pullbackIso g L m).hom) = _
  rw [← Category.assoc, tensorSectionMap_pullback, tensorSectionMap_postcomp,
    CyclicSectionGlobalCoverRootSectionPowers.pullback_powerSectionHom]
  rfl

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L)
local notation "Vₛ" => sectionOpen L hL s
private abbrev naturalPulledSectionOpen : Y.Opens :=
  sectionOpen ((pullback g).obj L) (hL.pullback g) (pullbackSectionHom g s)
local notation "Wₛ" => naturalPulledSectionOpen g L hL s
local notation "hₛ" => sectionOpenMap g L hL s

/-- The WHOLE actual normalization commutes with the internally constructed
original section-open square. It is proved by cancelling multiplication by
that SAME actual section power, not by supplying normalization matching. -/
theorem normalizedTwistIso_openSquare (F : X.Modules) (m : ℕ) :
    (sectionOpenModuleIso g L hL s (F ⊗ bundleTensorPower L m)).hom ≫
        (pullback (Wₛ).ι).map (twistPullbackIso g F L m).hom ≫
        (normalizedTwistIso ((pullback g).obj L) (hL.pullback g)
          (pullbackSectionHom g s) ((pullback g).obj F) m).hom =
      (pullback hₛ).map (normalizedTwistIso L hL s F m).hom ≫
        (sectionOpenModuleIso g L hL s F).hom := by
  let f := powerSectionTensorMap F L s m
  have hf : (pullback (Vₛ).ι).map f = (normalizedTwistIso L hL s F m).inv := by
    apply (cancel_mono (normalizedTwistIso L hL s F m).hom).mp
    exact (powerSectionTensorMap_normalized L hL s F m).trans
      (Iso.inv_hom_id (normalizedTwistIso L hL s F m)).symm
  have hfi : IsIso ((pullback (Vₛ).ι).map f) := by
    rw [hf]
    infer_instance
  let := hfi
  let E := pullbackComp hₛ (Vₛ).ι ≪≫ pullbackCongr (sectionOpenMap_fac g L hL s) ≪≫
    (pullbackComp (Wₛ).ι g).symm
  have hn : (pullback hₛ).map ((pullback (Vₛ).ι).map f) ≫
        (sectionOpenModuleIso g L hL s (F ⊗ bundleTensorPower L m)).hom =
      (sectionOpenModuleIso g L hL s F).hom ≫ (pullback (Wₛ).ι).map ((pullback g).map f) :=
    E.hom.naturality f
  apply (cancel_epi ((pullback hₛ).map ((pullback (Vₛ).ι).map f))).mp
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← (pullback (Wₛ).ι).map_comp_assoc, powerSectionTensorMap_pullback,
    powerSectionTensorMap_normalized]
  rw [← (pullback hₛ).map_comp_assoc, powerSectionTensorMap_normalized]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

/-- Native-adjoint representation of actual restriction divided by the SAME
original s^m, with the SAME actual pulled original module as target. -/
def normalizedPushforwardMap (F : X.Modules) (m : ℕ) :
    F ⊗ bundleTensorPower L m ⟶
      (pushforward (Vₛ).ι).obj ((pullback (Vₛ).ι).obj F) :=
  (pullbackPushforwardAdjunction (Vₛ).ι).unit.app _ ≫
    (pushforward (Vₛ).ι).map (normalizedTwistIso L hL s F m).hom

/-- Every actual original finite transition preserves the actual native
normalized whole-map, so its native Cech map also preserves normalized cochains. -/
theorem normalizedPushforwardMap_transition (F : X.Modules) (m a : ℕ) :
    twistIterate F L s m a ≫ normalizedPushforwardMap L hL s F (m + a) =
      normalizedPushforwardMap L hL s F m := by
  unfold normalizedPushforwardMap
  have hn := (pullbackPushforwardAdjunction (Vₛ).ι).unit.naturality (twistIterate F L s m a)
  change twistIterate F L s m a ≫
      (pullbackPushforwardAdjunction (Vₛ).ι).unit.app (F ⊗ bundleTensorPower L (m + a)) =
    (pullbackPushforwardAdjunction (Vₛ).ι).unit.app (F ⊗ bundleTensorPower L m) ≫
      (pushforward (Vₛ).ι).map ((pullback (Vₛ).ι).map (twistIterate F L s m a)) at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← (pushforward (Vₛ).ι).map_comp, twistIterate_normalized]

/-- The actual normalized whole original restriction map commutes with
actual open pullback and the native original twist comparison. -/
theorem normalizedPushforwardMap_pullback [IsOpenImmersion g] (F : X.Modules) (m : ℕ) :
    (pullback g).map (normalizedPushforwardMap L hL s F m) ≫
        (sectionOpenPushforwardIso g L hL s F).hom =
      (twistPullbackIso g F L m).hom ≫
        normalizedPushforwardMap ((pullback g).obj L) (hL.pullback g)
          (pullbackSectionHom g s) ((pullback g).obj F) m := by
  let M := F ⊗ bundleTensorPower L m
  let ν := (normalizedTwistIso L hL s F m).hom
  have hn := Vanishing.NadelPrincipalizationOpenPushforward.openIso_naturality
    (Vₛ).ι (Wₛ).ι hₛ g (sectionOpenSquare g L hL s) ν
  change (pullback g).map
      ((pullbackPushforwardAdjunction (Vₛ).ι).unit.app M ≫ (pushforward (Vₛ).ι).map ν) ≫
      (Vanishing.NadelPrincipalizationOpenPushforward.openIso (Vₛ).ι (Wₛ).ι hₛ g
        (sectionOpenSquare g L hL s) ((pullback (Vₛ).ι).obj F)).hom ≫
      (pushforward (Wₛ).ι).map (sectionOpenModuleIso g L hL s F).hom = _
  rw [Functor.map_comp, Category.assoc, reassoc_of% hn]
  rw [← (pushforward (Wₛ).ι).map_comp]
  have hc := normalizedTwistIso_openSquare g L hL s F m
  have he : (pullback hₛ).map ν ≫ (sectionOpenModuleIso g L hL s F).hom =
      (sectionOpenModuleIso g L hL s M).hom ≫
        (pullback (Wₛ).ι).map (twistPullbackIso g F L m).hom ≫
        (normalizedTwistIso ((pullback g).obj L) (hL.pullback g)
          (pullbackSectionHom g s) ((pullback g).obj F) m).hom := hc.symm
  rw [he]
  simp only [Functor.map_comp]
  have hu := sectionOpenPushforwardIso_unit g L hL s M
  change (pullback g).map ((pullbackPushforwardAdjunction (Vₛ).ι).unit.app M) ≫
      (Vanishing.NadelPrincipalizationOpenPushforward.openIso (Vₛ).ι (Wₛ).ι hₛ g
        (sectionOpenSquare g L hL s) ((pullback (Vₛ).ι).obj M)).hom ≫
      (pushforward (Wₛ).ι).map (sectionOpenModuleIso g L hL s M).hom =
    (pullbackPushforwardAdjunction (Wₛ).ι).unit.app ((pullback g).obj M) at hu
  rw [reassoc_of% hu]
  have ht := (pullbackPushforwardAdjunction (Wₛ).ι).unit.naturality
    (twistPullbackIso g F L m).hom
  change (twistPullbackIso g F L m).hom ≫
      (pullbackPushforwardAdjunction (Wₛ).ι).unit.app
        ((pullback g).obj F ⊗ bundleTensorPower ((pullback g).obj L) m) =
    (pullbackPushforwardAdjunction (Wₛ).ι).unit.app ((pullback g).obj M) ≫
      (pushforward (Wₛ).ι).map ((pullback (Wₛ).ι).map (twistPullbackIso g F L m).hom) at ht
  rw [← reassoc_of% ht]
  rfl

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
