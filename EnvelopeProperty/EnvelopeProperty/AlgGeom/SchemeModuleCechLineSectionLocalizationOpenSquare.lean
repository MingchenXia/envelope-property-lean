import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationUniformLocal
import EnvelopeProperty.Berkovich.SchemeLocalSectionOriginalFrames
import EnvelopeProperty.Vanishing.NadelPrincipalizationOpenPushforward

/-! # The actual original section-open square and canonical power frames

The literal nonzero opens of the original section and its actual pullback
form the actual restriction square. All maps and Cartesian comparisons are
derived from original zero-support pullback. Original section-power values
derive the whole canonical-frame compatibility, with no matching premise.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.SchemeModuleCechLineSectionLocalization

open CanonicalGeometry SchemeLineSectionEvaluation SchemeGlobalSectionTensorPowerNorms

attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable instance openSquarePullbackMonoidal {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (pullback g).Monoidal := pullbackMonoidal g

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L)
local notation "V" => sectionOpen L hL s
private abbrev pulledSectionOpen : Y.Opens :=
  sectionOpen ((pullback g).obj L) (hL.pullback g) (pullbackSectionHom g s)
local notation "W" => pulledSectionOpen g L hL s

private theorem sectionOpenMap_range : Set.range ((W).ι ≫ g) ⊆ Set.range (V).ι := by
  rintro _ ⟨y, rfl⟩
  rw [(V).range_ι]
  have hy : (W).ι y ∈ g ⁻¹ᵁ V := by
    rw [← sectionOpen_pullback L hL s g]
    exact y.property
  exact hy

/-- The actual original pulled section's nonzero open maps to the SAME
original section's nonzero open, with no supplied square or open matching. -/
def sectionOpenMap : (W).toScheme ⟶ (V).toScheme :=
  IsOpenImmersion.lift (V).ι ((W).ι ≫ g) (sectionOpenMap_range g L hL s)

/-- The SAME actual original open-map triangle, proved internally. -/
theorem sectionOpenMap_fac : sectionOpenMap g L hL s ≫ (V).ι = (W).ι ≫ g :=
  IsOpenImmersion.lift_fac _ _ _

/-- Actual zero-support pullback proves the SAME literal section-open
square Cartesian, rather than accepting a caller Cartesian certificate. -/
theorem sectionOpenSquare : IsPullback (W).ι (sectionOpenMap g L hL s) g (V).ι := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback (sectionOpenMap g L hL s) (W).ι (V).ι g
  · exact (sectionOpenMap_fac g L hL s).symm
  · simpa only [Scheme.Opens.opensRange_ι] using (sectionOpen_pullback L hL s g).symm

private noncomputable instance sectionOpenMap_isOpen [IsOpenImmersion g] :
    IsOpenImmersion (sectionOpenMap g L hL s) := by
  unfold sectionOpenMap
  infer_instance

/-- The SAME original m-power frame on the actual restricted square agrees
with the canonical frame of the SAME pulled original section power. The
whole matching equation is derived from the two actual section-one laws. -/
theorem powerSectionFrame_openSquare (m : ℕ) :
    (pullback (W).ι).mapIso (BundleTensorPowerPullback.pullbackIso g L m) ≪≫
        powerSectionFrame ((pullback g).obj L) (hL.pullback g) (pullbackSectionHom g s) m =
      (pullbackComp (W).ι g).app (bundleTensorPower L m) ≪≫
        frameViaFactor (sectionOpenMap g L hL s) (V).ι ((W).ι ≫ g)
          (sectionOpenMap_fac g L hL s) (powerSectionFrame L hL s m) := by
  let τ := pullbackSectionHom (W).ι (pullbackSectionHom g (powerSectionHom s m))
  let E := (pullback (W).ι).mapIso (BundleTensorPowerPullback.pullbackIso g L m) ≪≫
    powerSectionFrame ((pullback g).obj L) (hL.pullback g) (pullbackSectionHom g s) m
  let D := (pullbackComp (W).ι g).app (bundleTensorPower L m) ≪≫
    frameViaFactor (sectionOpenMap g L hL s) (V).ι ((W).ι ≫ g)
      (sectionOpenMap_fac g L hL s) (powerSectionFrame L hL s m)
  have ht : pullbackSectionHom (W).ι (pullbackSectionHom g (powerSectionHom s m)) ≫
      (pullback (W).ι).map (BundleTensorPowerPullback.pullbackIso g L m).hom =
    pullbackSectionHom (W).ι (powerSectionHom (pullbackSectionHom g s) m) := by
    have h := congrArg (fun t => pullbackSectionHom (W).ι t)
      (CyclicSectionGlobalCoverRootSectionPowers.pullback_powerSectionHom g s m)
    simpa only [pullbackSectionHom, Functor.map_comp, Category.assoc] using h
  have hE : τ ≫ E.hom = 𝟙 _ := by
    change (τ ≫ (pullback (W).ι).map (BundleTensorPowerPullback.pullbackIso g L m).hom) ≫
      (powerSectionFrame ((pullback g).obj L) (hL.pullback g) (pullbackSectionHom g s) m).hom = _
    rw [ht, powerSectionFrame_section]
  have hD : τ ≫ D.hom = 𝟙 _ := by
    have h := SchemeLocalSectionOriginalFrames.sectionViaFactor_frameOne
      (sectionOpenMap g L hL s) (V).ι ((W).ι ≫ g) (sectionOpenMap_fac g L hL s)
      (pullbackSectionHom (V).ι (powerSectionHom s m)) (powerSectionFrame L hL s m)
      (powerSectionFrame_section L hL s m)
    rw [SchemeLocalSectionRatioPullback.sectionViaFactor_global] at h
    dsimp only [D, Iso.trans_hom]
    rw [← Category.assoc]
    simp only [Iso.app_hom, τ]
    rw [pullbackSectionHom_comp]
    exact h
  have hi : IsIso (τ ≫ E.hom) := by rw [hE]; infer_instance
  let := hi
  have hτ : IsIso τ := IsIso.of_isIso_comp_right τ E.hom
  let := hτ
  apply Iso.ext
  apply (cancel_epi τ).mp
  exact hE.trans hD.symm

/-- Native pseudofunctoriality on the SAME actual section-open triangle
retains the original arbitrary module F, as a WHOLE original module iso. -/
def sectionOpenModuleIso (F : X.Modules) :
    (pullback (sectionOpenMap g L hL s)).obj ((pullback (V).ι).obj F) ≅
      (pullback (W).ι).obj ((pullback g).obj F) :=
  (pullbackComp (sectionOpenMap g L hL s) (V).ι).app F ≪≫
    (pullbackCongr (sectionOpenMap_fac g L hL s)).app F ≪≫
      ((pullbackComp (W).ι g).app F).symm

/-- The existing native open Cartesian pushforward comparison, consumed on
the actual ORIGINAL section-open square and original module F. No caller
Cartesianness, target module identification or acyclicity is input. -/
def sectionOpenPushforwardIso [IsOpenImmersion g] (F : X.Modules) :
    (pullback g).obj ((pushforward (V).ι).obj ((pullback (V).ι).obj F)) ≅
      (pushforward (W).ι).obj ((pullback (W).ι).obj ((pullback g).obj F)) :=
  Vanishing.NadelPrincipalizationOpenPushforward.openIso (V).ι (W).ι
      (sectionOpenMap g L hL s) g (sectionOpenSquare g L hL s) ((pullback (V).ι).obj F) ≪≫
    (pushforward (W).ι).mapIso (sectionOpenModuleIso g L hL s F)

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
