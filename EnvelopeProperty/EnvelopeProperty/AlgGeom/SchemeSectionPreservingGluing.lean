import EnvelopeProperty.AlgGeom.SchemeModuleMorphismGluing
import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization

/-! # Actual local comparisons preserving SAME original sections glue to whole original isomorphisms -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.SchemeSectionPreservingGluing
open SchemeLineSectionEvaluation SchemeLineSectionFactorization SchemeModuleMorphismGluing
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {K M N : X.Modules}

/-- The actual native over-site/restriction/pullback comparison, as ONE genuine natural isomorphism. -/
def overPullbackIso (U : X.Opens) :
    SheafOfModules.overFunctor X.ringCatSheaf U ⋙ (overEquiv U).functor ≅
      Scheme.Modules.pullback U.ι :=
  overFunctorEquiv U ≪≫ restrictFunctorIsoPullback U.ι

/-- An actual original pullback-module isomorphism gives the SAME whole original over-site comparison. -/
def overIsoOfPullback (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ (Scheme.Modules.pullback U.ι).obj N) :
    M.over U ≅ N.over U :=
  (overEquiv U).fullyFaithfulFunctor.preimageIso
    ((overPullbackIso U).app M ≪≫ e ≪≫ ((overPullbackIso U).app N).symm)

private theorem overIsoOfPullback_map (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ (Scheme.Modules.pullback U.ι).obj N) :
    (overEquiv U).functor.map (overIsoOfPullback U e).hom =
      (overPullbackIso U).hom.app M ≫ e.hom ≫ (overPullbackIso U).inv.app N := by
  simp only [overIsoOfPullback, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]

/-- A local comparison preserving SAME original pulled sections preserves their original whole over-site maps. -/
theorem overIsoOfPullback_section (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ (Scheme.Modules.pullback U.ι).obj N)
    (α : unitObj X ⟶ M) (β : unitObj X ⟶ N)
    (h : pullbackSectionHom U.ι α ≫ e.hom = pullbackSectionHom U.ι β) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).map α ≫ (overIsoOfPullback U e).hom =
      (SheafOfModules.overFunctor X.ringCatSheaf U).map β := by
  have hmap : (Scheme.Modules.pullback U.ι).map α ≫ e.hom =
      (Scheme.Modules.pullback U.ι).map β := by
    apply (cancel_epi (pullbackUnitIso U.ι).inv).mp
    exact h
  apply (overEquiv U).functor.map_injective
  rw [Functor.map_comp, overIsoOfPullback_map]
  have ha := (overPullbackIso U).hom.naturality α
  have hb := (overPullbackIso U).hom.naturality β
  simp only [Functor.comp_map] at ha hb
  calc
    _ = ((overEquiv U).functor.map ((SheafOfModules.overFunctor X.ringCatSheaf U).map α) ≫
        (overPullbackIso U).hom.app M) ≫ e.hom ≫ (overPullbackIso U).inv.app N := by
      simp only [Category.assoc]
    _ = ((overPullbackIso U).hom.app (unitObj X) ≫
        (Scheme.Modules.pullback U.ι).map α) ≫ e.hom ≫ (overPullbackIso U).inv.app N := by
      exact congrArg (fun q => q ≫ e.hom ≫ (overPullbackIso U).inv.app N) ha
    _ = (overPullbackIso U).hom.app (unitObj X) ≫
        (Scheme.Modules.pullback U.ι).map β ≫ (overPullbackIso U).inv.app N := by
      simpa only [Category.assoc] using
        congrArg (fun q => (overPullbackIso U).hom.app (unitObj X) ≫ q ≫
          (overPullbackIso U).inv.app N) hmap
    _ = ((overEquiv U).functor.map ((SheafOfModules.overFunctor X.ringCatSheaf U).map β) ≫
        (overPullbackIso U).hom.app N) ≫ (overPullbackIso U).inv.app N := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ (overPullbackIso U).inv.app N) hb.symm
    _ = _ := by
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact Category.comp_id _

/-- Native pullback-section isomorphisms are ACTUAL original over-site section isomorphisms. -/
theorem over_map_isIso_of_pullbackSectionHom (U : X.Opens) (α : unitObj X ⟶ M)
    (hα : IsIso (pullbackSectionHom U.ι α)) :
    IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map α) := by
  have hc : IsIso ((pullbackUnitIso U.ι).inv ≫ (Scheme.Modules.pullback U.ι).map α) := hα
  let := hc
  have hm : IsIso ((Scheme.Modules.pullback U.ι).map α) :=
    IsIso.of_isIso_comp_left (pullbackUnitIso U.ι).inv ((Scheme.Modules.pullback U.ι).map α)
  let := hm
  have hn := (overPullbackIso U).hom.naturality α
  simp only [Functor.comp_map] at hn
  have hi : IsIso ((overEquiv U).functor.map
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map α) ≫
        (overPullbackIso U).hom.app M) := by
    rw [hn]
    infer_instance
  let := hi
  have hF : IsIso ((overEquiv U).functor.map
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map α)) :=
    IsIso.of_isIso_comp_right _ ((overPullbackIso U).hom.app M)
  exact (isIso_iff_of_reflects_iso _ (overEquiv U).functor).mp hF

/-- EVERY original whole section identity restricts to every subordinate original open. -/
theorem bundleRestriction_section {U V : X.Opens} (hVU : V ≤ U)
    (α : K ⟶ M) (β : K ⟶ N) (t : M.over U ⟶ N.over U)
    (h : (SheafOfModules.overFunctor X.ringCatSheaf U).map α ≫ t =
      (SheafOfModules.overFunctor X.ringCatSheaf U).map β) :
    (SheafOfModules.overFunctor X.ringCatSheaf V).map α ≫
      bundleHomRestriction M N (homOfLE hVU) t =
        (SheafOfModules.overFunctor X.ringCatSheaf V).map β := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  exact congrArg (fun q : K.over U ⟶ N.over U =>
    (q.val.app ((Over.map (homOfLE hVU)).op.obj W)).hom x) h

variable {ι κ : Type*}

/-- Original section preservation and actual pivot isomorphisms DERIVE whole
original overlap matching of the actual local comparisons. -/
theorem overComparisons_compatible (U : ι → X.Opens)
    (e : ∀ a, (Scheme.Modules.pullback (U a).ι).obj M ≅
      (Scheme.Modules.pullback (U a).ι).obj N)
    (α : κ → (unitObj X ⟶ M)) (β : κ → (unitObj X ⟶ N)) (pivot : ι → κ)
    (hβ : ∀ a, IsIso (pullbackSectionHom (U a).ι (β (pivot a))))
    (hpres : ∀ a j, pullbackSectionHom (U a).ι (α j) ≫ (e a).hom =
      pullbackSectionHom (U a).ι (β j)) (a b : ι) :
    bundleHomRestriction M N (Opens.infLELeft (U a) (U b)) (overIsoOfPullback (U a) (e a)).hom =
      bundleHomRestriction M N (Opens.infLERight (U a) (U b)) (overIsoOfPullback (U b) (e b)).hom := by
  let W := U a ⊓ U b
  have hαa : IsIso (pullbackSectionHom (U a).ι (α (pivot a))) := by
    have hh : IsIso (pullbackSectionHom (U a).ι (α (pivot a)) ≫ (e a).hom) := by
      rw [hpres a (pivot a)]
      exact hβ a
    let := hh
    exact IsIso.of_isIso_comp_right _ (e a).hom
  have hαW : IsIso (pullbackSectionHom W.ι (α (pivot a))) :=
    isIso_pullbackSectionHom_factor (X.homOfLE (inf_le_left : W ≤ U a)) (U a).ι W.ι
      (X.homOfLE_ι _) (α (pivot a)) hαa
  have hOver : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf W).map (α (pivot a))) :=
    over_map_isIso_of_pullbackSectionHom W (α (pivot a)) hαW
  let := hOver
  apply (cancel_epi ((SheafOfModules.overFunctor X.ringCatSheaf W).map (α (pivot a)))).mp
  exact (bundleRestriction_section (inf_le_left : W ≤ U a) (α (pivot a)) (β (pivot a))
    (overIsoOfPullback (U a) (e a)).hom
    (overIsoOfPullback_section (U a) (e a) (α (pivot a)) (β (pivot a)) (hpres a (pivot a)))).trans
    (bundleRestriction_section (inf_le_right : W ≤ U b) (α (pivot a)) (β (pivot a))
      (overIsoOfPullback (U b) (e b)).hom
      (overIsoOfPullback_section (U b) (e b) (α (pivot a)) (β (pivot a)) (hpres b (pivot a)))).symm

/-- Actual local comparisons preserving SAME original sections construct an
ACTUAL WHOLE original isomorphism; its overlap matching is internally DERIVED. -/
def glueOfSections (U : ι → X.Opens) (hc : ∀ x : X, ∃ a, x ∈ U a)
    (e : ∀ a, (Scheme.Modules.pullback (U a).ι).obj M ≅
      (Scheme.Modules.pullback (U a).ι).obj N)
    (α : κ → (unitObj X ⟶ M)) (β : κ → (unitObj X ⟶ N)) (pivot : ι → κ)
    (hβ : ∀ a, IsIso (pullbackSectionHom (U a).ι (β (pivot a))))
    (hpres : ∀ a j, pullbackSectionHom (U a).ι (α j) ≫ (e a).hom =
      pullbackSectionHom (U a).ι (β j)) : M ≅ N :=
  bundleGlueIso M N U hc (fun a => overIsoOfPullback (U a) (e a))
    (overComparisons_compatible U e α β pivot hβ hpres)

/-- The actual global original isomorphism retains every SAME original local comparison. -/
theorem glueOfSections_restrict (U : ι → X.Opens) (hc : ∀ x : X, ∃ a, x ∈ U a)
    (e : ∀ a, (Scheme.Modules.pullback (U a).ι).obj M ≅
      (Scheme.Modules.pullback (U a).ι).obj N)
    (α : κ → (unitObj X ⟶ M)) (β : κ → (unitObj X ⟶ N)) (pivot : ι → κ)
    (hβ : ∀ a, IsIso (pullbackSectionHom (U a).ι (β (pivot a))))
    (hpres : ∀ a j, pullbackSectionHom (U a).ι (α j) ≫ (e a).hom =
      pullbackSectionHom (U a).ι (β j)) (a : ι) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U a)).mapIso
      (glueOfSections U hc e α β pivot hβ hpres) = overIsoOfPullback (U a) (e a) :=
  bundleGlueIso_restrict M N U hc (fun a => overIsoOfPullback (U a) (e a))
    (overComparisons_compatible U e α β pivot hβ hpres) a

/-- EVERY SAME original global section is preserved on the ENTIRE original scheme. -/
theorem glueOfSections_section (U : ι → X.Opens) (hc : ∀ x : X, ∃ a, x ∈ U a)
    (e : ∀ a, (Scheme.Modules.pullback (U a).ι).obj M ≅
      (Scheme.Modules.pullback (U a).ι).obj N)
    (α : κ → (unitObj X ⟶ M)) (β : κ → (unitObj X ⟶ N)) (pivot : ι → κ)
    (hβ : ∀ a, IsIso (pullbackSectionHom (U a).ι (β (pivot a))))
    (hpres : ∀ a j, pullbackSectionHom (U a).ι (α j) ≫ (e a).hom =
      pullbackSectionHom (U a).ι (β j)) (j : κ) :
    α j ≫ (glueOfSections U hc e α β pivot hβ hpres).hom = β j := by
  apply bundleHom_ext (unitObj X) N U hc
  intro a
  rw [Functor.map_comp]
  have hr := congrArg Iso.hom (glueOfSections_restrict U hc e α β pivot hβ hpres a)
  change (SheafOfModules.overFunctor X.ringCatSheaf (U a)).map
    (glueOfSections U hc e α β pivot hβ hpres).hom = (overIsoOfPullback (U a) (e a)).hom at hr
  rw [hr]
  exact overIsoOfPullback_section (U a) (e a) (α j) (β j) (hpres a j)

end EnvelopeProperty.SchemeSectionPreservingGluing
