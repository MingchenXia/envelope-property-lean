import EnvelopeProperty.AlgGeom.SchemeSectionPreservingGluing
import EnvelopeProperty.AlgGeom.SchemeModuleOpenCoverDetection
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

/-! # Native module morphism descent on original open-immersion charts

This bridges actual scheme pullbacks to the existing original over-site Hom
sheaf. Matching is the ordinary equality of those native local restrictions;
no affine, quasicoherent or cyclic-cover hypothesis is used.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeOpenCoverModuleMorphismDescent
open SchemeSectionPreservingGluing SchemeModuleMorphismGluing
variable {X Y : Scheme.{u}} {M N : X.Modules}

private def imageFunctor (j : Y ⟶ X) [IsOpenImmersion j] :=
  (overEquiv j.opensRange).functor ⋙ pullback j.isoOpensRange.hom

private def imageFunctorFullyFaithful (j : Y ⟶ X) [IsOpenImmersion j] :
    (imageFunctor j).FullyFaithful := by
  let : (pullback j.isoOpensRange.hom).IsEquivalence :=
    pullback_isEquivalence_of_iso j.isoOpensRange
  change ((overEquiv j.opensRange).functor ⋙ pullback j.isoOpensRange.hom).FullyFaithful
  exact (overEquiv j.opensRange).fullyFaithfulFunctor.comp
    (Functor.FullyFaithful.ofFullyFaithful (pullback j.isoOpensRange.hom))

/-- The original chart's actual pullback is the native over-site restriction
followed by equivalence with its original open image. -/
def imagePullbackIso (j : Y ⟶ X) [IsOpenImmersion j] :
    SheafOfModules.overFunctor X.ringCatSheaf j.opensRange ⋙ imageFunctor j ≅ pullback j :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (overPullbackIso j.opensRange) (pullback j.isoOpensRange.hom) ≪≫
    pullbackComp j.isoOpensRange.hom j.opensRange.ι ≪≫
    pullbackCongr j.isoOpensRange_hom_ι

/-- Convert an actual native chart-pullback morphism to the SAME original
native over-site morphism on its actual open image. -/
def overHomOfPullback (j : Y ⟶ X) [IsOpenImmersion j]
    (α : (pullback j).obj M ⟶ (pullback j).obj N) : M.over j.opensRange ⟶ N.over j.opensRange :=
  (imageFunctorFullyFaithful j).preimage
    ((imagePullbackIso j).hom.app M ≫ α ≫ (imagePullbackIso j).inv.app N)

/-- The conversion has its defining WHOLE native pullback comparison. -/
theorem map_overHomOfPullback (j : Y ⟶ X) [IsOpenImmersion j]
    (α : (pullback j).obj M ⟶ (pullback j).obj N) :
    (imageFunctor j).map (overHomOfPullback j α) =
      (imagePullbackIso j).hom.app M ≫ α ≫ (imagePullbackIso j).inv.app N :=
  (imageFunctorFullyFaithful j).map_preimage _

/-- Every original global map converts to its SAME original over-site restriction. -/
theorem overHomOfPullback_map (j : Y ⟶ X) [IsOpenImmersion j] (f : M ⟶ N) :
    overHomOfPullback j ((pullback j).map f) =
      (SheafOfModules.overFunctor X.ringCatSheaf j.opensRange).map f := by
  apply (imageFunctorFullyFaithful j).map_injective
  rw [map_overHomOfPullback]
  have hn := (imagePullbackIso j).hom.naturality f
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- The conversion reflects equality of ENTIRE actual local chart morphisms. -/
theorem overHomOfPullback_injective (j : Y ⟶ X) [IsOpenImmersion j] :
    Function.Injective (overHomOfPullback (M := M) (N := N) j) := by
  intro α β h
  have hm := congrArg (imageFunctor j).map h
  rw [map_overHomOfPullback, map_overHomOfPullback] at hm
  apply (cancel_epi ((imagePullbackIso j).hom.app M)).mp
  apply (cancel_mono ((imagePullbackIso j).inv.app N)).mp
  simpa only [Category.assoc] using hm

variable {ι : Type v} (C : ι → Scheme.{u}) (j : ∀ i, C i ⟶ X)
  [∀ i, IsOpenImmersion (j i)]
  (hc : ∀ x : X, ∃ (i : ι) (y : C i), j i y = x)
  (M N : X.Modules)
  (α : ∀ i, (pullback (j i)).obj M ⟶ (pullback (j i)).obj N)
  (ha : ∀ i k,
    bundleHomRestriction M N (Opens.infLELeft (j i).opensRange (j k).opensRange)
      (overHomOfPullback (j i) (α i)) =
    bundleHomRestriction M N (Opens.infLERight (j i).opensRange (j k).opensRange)
      (overHomOfPullback (j k) (α k)))

include hc in
private theorem images_cover (x : X) : ∃ i, x ∈ (j i).opensRange := by
  obtain ⟨i,y,rfl⟩ := hc x
  exact ⟨i,y,rfl⟩

include hc ha

/-- Glue actual native chart-pullback maps using their ordinary native overlap matching. -/
def glueHom : M ⟶ N :=
  bundleGlueHom M N (fun i => (j i).opensRange) (images_cover C j hc)
    (fun i => overHomOfPullback (j i) (α i)) ha

/-- The global map has EXACTLY the prescribed pullback along every original chart. -/
theorem pullback_glueHom (i : ι) :
    (pullback (j i)).map (glueHom C j hc M N α ha) = α i := by
  apply overHomOfPullback_injective (j i)
  rw [overHomOfPullback_map]
  exact bundleGlueHom_restrict M N (fun i => (j i).opensRange) (images_cover C j hc)
    (fun i => overHomOfPullback (j i) (α i)) ha i

/-- Original local morphisms satisfying their ordinary matching condition give a
UNIQUE original global morphism retaining their entire native pullbacks. -/
theorem existsUnique_glueHom :
    ∃! f : M ⟶ N, ∀ i, (pullback (j i)).map f = α i := by
  refine ⟨glueHom C j hc M N α ha, pullback_glueHom C j hc M N α ha, ?_⟩
  intro f hf
  apply SchemeModuleOpenCoverDetection.hom_ext C j hc
  intro i
  exact (hf i).trans (pullback_glueHom C j hc M N α ha i).symm

end EnvelopeProperty.SchemeOpenCoverModuleMorphismDescent
