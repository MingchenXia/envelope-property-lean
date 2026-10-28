import EnvelopeProperty.AlgGeom.SchemeModuleMorphismGluing
import ModularCurves.Picard.DualPullback.OverRestriction

/-! # Descent using actual native restriction functors on original opens -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeOpenRestrictionModuleMorphismDescent
open SchemeModuleMorphismGluing
variable {X : Scheme.{u}} {M N : X.Modules}

/-- The actual native open restriction of an original over-site morphism. -/
def restrictionOfOverHom (U : X.Opens) (β : M.over U ⟶ N.over U) :
    (restrictFunctor U.ι).obj M ⟶ (restrictFunctor U.ι).obj N :=
  (overFunctorEquiv U).inv.app M ≫ (overEquiv U).functor.map β ≫
    (overFunctorEquiv U).hom.app N

/-- Recover the original over-site map from an actual native restriction map. -/
def overHomOfRestriction (U : X.Opens)
    (α : (restrictFunctor U.ι).obj M ⟶ (restrictFunctor U.ι).obj N) :
    M.over U ⟶ N.over U :=
  (overEquiv U).fullyFaithfulFunctor.preimage
    ((overFunctorEquiv U).hom.app M ≫ α ≫ (overFunctorEquiv U).inv.app N)

theorem map_overHomOfRestriction (U : X.Opens)
    (α : (restrictFunctor U.ι).obj M ⟶ (restrictFunctor U.ι).obj N) :
    (overEquiv U).functor.map (overHomOfRestriction U α) =
      (overFunctorEquiv U).hom.app M ≫ α ≫ (overFunctorEquiv U).inv.app N :=
  (overEquiv U).fullyFaithfulFunctor.map_preimage _

theorem restrictionOfOverHom_overHomOfRestriction (U : X.Opens)
    (α : (restrictFunctor U.ι).obj M ⟶ (restrictFunctor U.ι).obj N) :
    restrictionOfOverHom U (overHomOfRestriction U α) = α := by
  simp only [restrictionOfOverHom, map_overHomOfRestriction, Category.assoc,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]

theorem overHomOfRestriction_restrictionOfOverHom (U : X.Opens)
    (β : M.over U ⟶ N.over U) :
    overHomOfRestriction U (restrictionOfOverHom U β) = β := by
  apply (overEquiv U).functor.map_injective
  simp only [map_overHomOfRestriction, restrictionOfOverHom, Category.assoc,
    Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

theorem restrictionOfOverHom_injective (U : X.Opens) :
    Function.Injective (restrictionOfOverHom (M := M) (N := N) U) := by
  intro α β h
  simpa only [overHomOfRestriction_restrictionOfOverHom] using
    congrArg (overHomOfRestriction U) h

/-- Restriction along an inclusion of original opens, with its actual native
composition comparison on the original source and target modules. -/
def restrictOpenHom {U V : X.Opens} (i : V ⟶ U)
    (α : (restrictFunctor U.ι).obj M ⟶ (restrictFunctor U.ι).obj N) :
    (restrictFunctor V.ι).obj M ⟶ (restrictFunctor V.ι).obj N :=
  (restrictOpenCompIso i).hom.app M ≫
    (restrictFunctor (X.homOfLE (leOfHom i))).map α ≫
    (restrictOpenCompIso i).inv.app N

private theorem overEquiv_map_bundleHomRestriction {U V : X.Opens} (i : V ⟶ U)
    (β : M.over U ⟶ N.over U) :
    (overEquiv V).functor.map (bundleHomRestriction M N i β) =
      (overRestrictModuleIso M i).hom ≫
        (restrictFunctor (X.homOfLE (leOfHom i))).map ((overEquiv U).functor.map β) ≫
        (overRestrictModuleIso N i).inv := by
  have h := (overMapCompOverEquiv i).hom.naturality β
  simp only [Functor.comp_map] at h
  have hm : (overMapCompOverEquiv i).hom.app (M.over U) ≫
        (restrictFunctor (X.homOfLE (leOfHom i))).map ((overEquiv U).functor.map β) ≫
        (overMapCompOverEquiv i).inv.app (N.over U) =
      (overEquiv V).functor.map ((SheafOfModules.overMap X.ringCatSheaf i).map β) := by
    rw [← reassoc_of% h, Iso.hom_inv_id_app]
    exact Category.comp_id _
  simp only [bundleHomRestriction, overRestrictModuleIso, Functor.map_comp,
    Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.symm_hom, Iso.symm_inv, Category.assoc]
  change (overEquiv V).functor.map
      ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app M).inv ≫
      (overEquiv V).functor.map ((SheafOfModules.overMap X.ringCatSheaf i).map β) ≫
      (overEquiv V).functor.map
      ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app N).hom =
    (overEquiv V).functor.map
      ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app M).inv ≫
      (overMapCompOverEquiv i).hom.app (M.over U) ≫
      (restrictFunctor (X.homOfLE (leOfHom i))).map ((overEquiv U).functor.map β) ≫
      (overMapCompOverEquiv i).inv.app (N.over U) ≫
      (overEquiv V).functor.map
      ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app N).hom
  simpa only [Category.assoc] using
    congrArg (fun q => (overEquiv V).functor.map
      ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app M).inv ≫ q ≫
      (overEquiv V).functor.map
      ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app N).hom) hm.symm

/-- The whole over-site restriction is exactly the actual native restriction. -/
theorem restrictionOfOverHom_restrict {U V : X.Opens} (i : V ⟶ U)
    (β : M.over U ⟶ N.over U) :
    restrictionOfOverHom V (bundleHomRestriction M N i β) =
      restrictOpenHom i (restrictionOfOverHom U β) := by
  have hn : (overRestrictModuleIso N i).inv ≫ (overFunctorEquiv V).hom.app N =
      (restrictFunctor (X.homOfLE (leOfHom i))).map
        ((overFunctorEquiv U).hom.app N) ≫ (restrictOpenCompIso i).inv.app N := by
    apply (cancel_epi (overRestrictModuleIso N i).hom).mp
    rw [Iso.hom_inv_id_assoc]
    have h := congrArg (fun q => q ≫ (restrictOpenCompIso i).inv.app N)
      (overRestrictModuleIso_comp_overFunctorEquiv N i)
    simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using h.symm
  simp only [restrictionOfOverHom, overEquiv_map_bundleHomRestriction,
    restrictOpenHom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((overFunctorEquiv V).inv.app M),
    overRestrictionComparison_inv, Category.assoc, hn]

/-- Native overlap restriction converts back to ordinary original Hom restriction. -/
theorem overHomOfRestriction_restrict {U V : X.Opens} (i : V ⟶ U)
    (α : (restrictFunctor U.ι).obj M ⟶ (restrictFunctor U.ι).obj N) :
    overHomOfRestriction V (restrictOpenHom i α) =
      bundleHomRestriction M N i (overHomOfRestriction U α) := by
  apply restrictionOfOverHom_injective V
  rw [restrictionOfOverHom_overHomOfRestriction, restrictionOfOverHom_restrict,
    restrictionOfOverHom_overHomOfRestriction]

theorem restrictionOfOverHom_map (U : X.Opens) (f : M ⟶ N) :
    restrictionOfOverHom U ((SheafOfModules.overFunctor X.ringCatSheaf U).map f) =
      (restrictFunctor U.ι).map f := by
  have h := (overFunctorEquiv U).hom.naturality f
  simp only [Functor.comp_map] at h
  unfold restrictionOfOverHom
  calc
    _ = (overFunctorEquiv U).inv.app M ≫
        ((overFunctorEquiv U).hom.app M ≫ (restrictFunctor U.ι).map f) :=
      congrArg (fun q => (overFunctorEquiv U).inv.app M ≫ q) h
    _ = _ := by rw [Iso.inv_hom_id_app_assoc]

variable {ι : Type v} (U : ι → X.Opens) (hc : ∀ x : X, ∃ i, x ∈ U i)
  (M N : X.Modules)
  (α : ∀ i, (restrictFunctor (U i).ι).obj M ⟶ (restrictFunctor (U i).ι).obj N)
  (ha : ∀ i k, restrictOpenHom (Opens.infLELeft (U i) (U k)) (α i) =
    restrictOpenHom (Opens.infLERight (U i) (U k)) (α k))

include ha in
private theorem overlapMatching (i k : ι) :
    bundleHomRestriction M N (Opens.infLELeft (U i) (U k))
      (overHomOfRestriction (U i) (α i)) =
    bundleHomRestriction M N (Opens.infLERight (U i) (U k))
      (overHomOfRestriction (U k) (α k)) := by
  rw [← overHomOfRestriction_restrict, ← overHomOfRestriction_restrict, ha i k]

/-- Glue actual native restrictions with their ordinary native overlap matching. -/
def glueRestrictionHom : M ⟶ N :=
  bundleGlueHom M N U hc (fun i => overHomOfRestriction (U i) (α i))
    (overlapMatching U M N α ha)

include hc ha

/-- The entire actual native restriction of the glued map is the prescribed one. -/
theorem restrict_glueRestrictionHom (i : ι) :
    (restrictFunctor (U i).ι).map (glueRestrictionHom U hc M N α ha) = α i := by
  rw [← restrictionOfOverHom_map, glueRestrictionHom, bundleGlueHom_restrict,
    restrictionOfOverHom_overHomOfRestriction]

/-- Native compatible local maps give a unique original module morphism. -/
theorem existsUnique_glueRestrictionHom :
    ∃! f : M ⟶ N, ∀ i, (restrictFunctor (U i).ι).map f = α i := by
  refine ⟨glueRestrictionHom U hc M N α ha,
    restrict_glueRestrictionHom U hc M N α ha, ?_⟩
  intro f hf
  apply bundleHom_ext M N U hc
  intro i
  apply restrictionOfOverHom_injective (U i)
  rw [restrictionOfOverHom_map, restrictionOfOverHom_map, hf i,
    restrict_glueRestrictionHom U hc M N α ha i]

end EnvelopeProperty.SchemeOpenRestrictionModuleMorphismDescent
