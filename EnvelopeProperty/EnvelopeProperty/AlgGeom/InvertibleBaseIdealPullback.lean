import EnvelopeProperty.AlgGeom.InvertibleBaseIdealFrameCoefficients
import EnvelopeProperty.AlgGeom.QuasicoherentImageFactorization
import EnvelopeProperty.AlgGeom.IdealModulePullbackEpimorphism
import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationDualCanonicalSectionPullback
import EnvelopeProperty.Berkovich.SchemeFramedSectionPullback
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Functor.EpiMono

/-! # The whole ideal of the actual pulled global section

The original section is pulled by the actual adjunction unit. The canonical
dual pullback and its unit law identify the entire evaluation maps. Actual
epimorphisms onto their image ideals then compare the genuine geometric
ideal comap, including the zero section and nonflat morphisms.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
universe u
namespace EnvelopeProperty.InvertibleBaseIdealPullback
open Scheme.Modules InvertibleSheafBaseIdeal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

private theorem imageIdeal_eq_of_epi_factor {X : Scheme.{u}} {N : X.Modules}
    [N.IsQuasicoherent] (a : N ⟶ unitObj X) (I : X.IdealSheafData)
    (p : N ⟶ I.toModules) [Epi p] (hp : p ≫ I.toModulesInclusion = a) :
    QuasicoherentImageIdeal.imageIdeal N a = I := by
  apply le_antisymm
  · exact (QuasicoherentImageFactorization.imageIdeal_le_iff_factor a I).mpr ⟨p, hp⟩
  · let J := QuasicoherentImageIdeal.imageIdeal N a
    let : StrongEpi p := strongEpi_of_epi p
    let F : StrongEpiMonoFactorisation a :=
      { I := I.toModules
        m := I.toModulesInclusion
        e := p
        fac := hp }
    let G : MonoFactorisation a :=
      { I := J.toModules
        m := J.toModulesInclusion
        e := QuasicoherentImageModule.imageFactor a
        fac := QuasicoherentImageModule.imageFactor_inclusion a }
    let l : I.toModules ⟶ J.toModules := F.toMonoIsImage.lift G
    have hl : l ≫ J.toModulesInclusion = I.toModulesInclusion :=
      F.toMonoIsImage.lift_fac G
    intro U c hc
    let z : Γ(I.toModules, U.1) := (I.toModulesSectionsEquiv U).symm ⟨c, hc⟩
    have hz := (J.toModulesSectionsEquiv U (l.val.app (op U.1) z)).property
    have he := congrArg (fun q : I.toModules ⟶ unitObj X =>
      q.val.app (op U.1) z) hl
    change (l.val.app (op U.1) z).1 = c at he
    exact he ▸ hz

private theorem dualPullback_unit_evaluation {X Y : Scheme.{u}} (f : Y ⟶ X) :
    dualPullbackHom f (unitObj X) ≫
        dualMapObj (pullbackUnitIso f).inv ≫ (dualUnitObjIso (X := Y)).hom =
      (Scheme.Modules.pullback f).map (dualUnitObjIso (X := X)).hom ≫ (pullbackUnitIso f).hom := by
  let P := Scheme.Modules.pullback f
  let e := pullbackUnitIso f
  let dX := dualUnitObjIso (X := X)
  let dY := dualUnitObjIso (X := Y)
  have hc := OriginalDualPullbackCoherence.canonicalDualSection_pullback f
    (𝟙 (unitObj X))
  have h : e.inv ≫ P.map dX.inv ≫ dualPullbackHom f (unitObj X) =
      dY.inv ≫ (dualIsoObj e).hom := by
    have hid : dualMapObj (𝟙 (unitObj X)) = 𝟙 (dualObj (unitObj X)) :=
      ModularCurves.SheafOfModules.dualMap_id X.ringCatSheaf (unitObj X)
    have hs : dX.inv ≫ dualMapObj (𝟙 (unitObj X)) = dX.inv := by
      rw [hid, Category.comp_id]
    have ht : P.map (𝟙 (unitObj X)) ≫ e.hom = e.hom := by
      rw [P.map_id, Category.id_comp]
    change (e.inv ≫ P.map (dX.inv ≫ dualMapObj (𝟙 (unitObj X)))) ≫
        dualPullbackHom f (unitObj X) =
      dY.inv ≫ dualMapObj (P.map (𝟙 (unitObj X)) ≫ e.hom) at hc
    rw [hs, ht] at hc
    exact (Category.assoc _ _ _).symm.trans hc
  apply (cancel_epi (e.inv ≫ P.map dX.inv)).mp
  change (e.inv ≫ P.map dX.inv) ≫
      (dualPullbackHom f (unitObj X) ≫ (dualIsoObj e).inv ≫ dY.hom) =
    (e.inv ≫ P.map dX.inv) ≫ (P.map dX.hom ≫ e.hom)
  calc
    _ = (e.inv ≫ P.map dX.inv ≫ dualPullbackHom f (unitObj X)) ≫
        (dualIsoObj e).inv ≫ dY.hom := by simp only [Category.assoc]
    _ = (dY.inv ≫ (dualIsoObj e).hom) ≫ (dualIsoObj e).inv ≫ dY.hom := by rw [h]
    _ = 𝟙 (unitObj Y) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
    _ = (e.inv ≫ P.map dX.inv) ≫ (P.map dX.hom ≫ e.hom) := by
      have hm : P.map dX.inv ≫ P.map dX.hom = 𝟙 _ :=
        (P.mapIso dX).inv_hom_id
      symm
      calc
        _ = e.inv ≫ (P.map dX.inv ≫ P.map dX.hom) ≫ e.hom := by
          simp only [Category.assoc]
        _ = e.inv ≫ (𝟙 _) ≫ e.hom := by rw [hm]
        _ = 𝟙 _ := by rw [Category.id_comp, e.inv_hom_id]

private theorem sectionEvaluation_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : X.Modules) (s : Γ(L, ⊤)) :
    dualPullbackHom f L ≫
        sectionEvaluation ((Scheme.Modules.pullback f).obj L) (affinePullbackUnitTop f L s) =
      (Scheme.Modules.pullback f).map (sectionEvaluation L s) ≫ (pullbackUnitIso f).hom := by
  let P := Scheme.Modules.pullback f
  let q := SchemeModuleGlobalSections.sectionHom L s
  let e := pullbackUnitIso f
  have hs : SchemeModuleGlobalSections.sectionHom (P.obj L)
      (affinePullbackUnitTop f L s) = e.inv ≫ P.map q := by
    apply OriginalDualPullbackCoherence.unitHom_ext_top
    change (topSectionHom (P.obj L) (affinePullbackUnitTop f L s)).val.app
        (op ⊤) (1 : Γ(Y, ⊤)) =
      SchemeLineSectionEvaluation.sectionAtOne
        (SchemeLineSectionEvaluation.pullbackSectionHom f (topSectionHom L s))
    exact (topSectionHom_app_top_apply_one (P.obj L) (affinePullbackUnitTop f L s)).trans
      (Berkovich.SchemeFramedSectionPullback.affinePullbackUnitTop_eq_sectionAtOne f L s)
  have hn := dualPullbackHom_naturality f q
  have hd : dualMapObj (e.inv ≫ P.map q) =
      dualMapObj (P.map q) ≫ dualMapObj e.inv :=
    ModularCurves.SheafOfModules.dualMap_comp Y.ringCatSheaf e.inv (P.map q)
  rw [InvertibleBaseIdealFrameCoefficients.sectionEvaluation_eq_dual,
    InvertibleBaseIdealFrameCoefficients.sectionEvaluation_eq_dual, hs, hd]
  calc
    _ = (dualPullbackHom f L ≫ dualMapObj (P.map q)) ≫
        dualMapObj e.inv ≫ (dualUnitObjIso (X := Y)).hom := by
      simp only [Category.assoc]
    _ = (P.map (dualMapObj q) ≫ dualPullbackHom f (unitObj X)) ≫
        dualMapObj e.inv ≫ (dualUnitObjIso (X := Y)).hom := by rw [hn]
    _ = P.map (dualMapObj q) ≫
        (P.map (dualUnitObjIso (X := X)).hom ≫ e.hom) := by
      simpa only [Category.assoc] using congrArg
        (fun z => P.map (dualMapObj q) ≫ z) (dualPullback_unit_evaluation f)
    _ = _ := by
      change P.map (dualMapObj q) ≫ P.map (dualUnitObjIso (X := X)).hom ≫ e.hom =
        P.map (dualMapObj q ≫ (dualUnitObjIso (X := X)).hom) ≫ e.hom
      rw [Functor.map_comp, Category.assoc]

/-- The ideal of the SAME actual global section commutes with every genuine
scheme pullback. The section on the right is the original adjunction-unit
pullback, with no supplied frame, evaluation or ideal comparison. -/
theorem sectionIdeal_comap {X Y : Scheme.{u}} (f : Y ⟶ X)
    {L : X.Modules} (hL : IsInvertible L) (s : Γ(L, ⊤)) :
    (sectionIdeal hL s).comap f =
      sectionIdeal (hL.pullback f) (affinePullbackUnitTop f L s) := by
  let P := Scheme.Modules.pullback f
  let : (dualObj L).IsQuasicoherent := hL.dual.isQuasicoherent
  let : (dualObj (P.obj L)).IsQuasicoherent := (hL.pullback f).dual.isQuasicoherent
  let : P.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (pullbackPushforwardAdjunction f)
  let a := sectionEvaluation L s
  let I := sectionIdeal hL s
  let e := dualPullbackIsoOfIsInvertible f L hL
  let : Epi (QuasicoherentImageModule.imageFactor a) :=
    QuasicoherentImageModule.imageFactor_epi a
  let : Epi (I.toModulesComapPullbackMap f) := I.toModulesComapPullbackMap_epi f
  let p : dualObj (P.obj L) ⟶ (I.comap f).toModules :=
    e.inv ≫ P.map (QuasicoherentImageModule.imageFactor a) ≫
      I.toModulesComapPullbackMap f
  let : Epi p := by dsimp only [p]; infer_instance
  have hu : SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom =
      (pullbackUnitIso f).hom := rfl
  have hp : p ≫ (I.comap f).toModulesInclusion =
      sectionEvaluation (P.obj L) (affinePullbackUnitTop f L s) := by
    calc
      _ = e.inv ≫ P.map
          (QuasicoherentImageModule.imageFactor a ≫ I.toModulesInclusion) ≫
            (pullbackUnitIso f).hom := by
        have hi := congrArg (fun z =>
          e.inv ≫ P.map (QuasicoherentImageModule.imageFactor a) ≫ z)
          (I.toModulesComapPullbackMap_inclusion f)
        change (e.inv ≫ P.map (QuasicoherentImageModule.imageFactor a) ≫
            I.toModulesComapPullbackMap f) ≫ (I.comap f).toModulesInclusion =
          e.inv ≫ P.map
            (QuasicoherentImageModule.imageFactor a ≫ I.toModulesInclusion) ≫
              (pullbackUnitIso f).hom
        change e.inv ≫ P.map (QuasicoherentImageModule.imageFactor a) ≫
            (I.toModulesComapPullbackMap f ≫ (I.comap f).toModulesInclusion) =
          e.inv ≫ P.map (QuasicoherentImageModule.imageFactor a) ≫
            P.map I.toModulesInclusion ≫
              SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom at hi
        simpa only [Category.assoc, Functor.map_comp, hu] using hi
      _ = e.inv ≫ P.map a ≫ (pullbackUnitIso f).hom := by
        have hf : QuasicoherentImageModule.imageFactor a ≫ I.toModulesInclusion = a := by
          change QuasicoherentImageModule.imageFactor a ≫
            (QuasicoherentImageIdeal.imageIdeal (dualObj L) a).toModulesInclusion = a
          exact QuasicoherentImageModule.imageFactor_inclusion a
        exact congrArg (fun z : dualObj L ⟶ unitObj X =>
          e.inv ≫ P.map z ≫ (pullbackUnitIso f).hom) hf
      _ = e.inv ≫ e.hom ≫
          sectionEvaluation (P.obj L) (affinePullbackUnitTop f L s) := by
        have hc : e.hom ≫ sectionEvaluation (P.obj L) (affinePullbackUnitTop f L s) =
            P.map a ≫ (pullbackUnitIso f).hom := by
          change dualPullbackHom f L ≫
              sectionEvaluation ((Scheme.Modules.pullback f).obj L)
                (affinePullbackUnitTop f L s) =
            (Scheme.Modules.pullback f).map (sectionEvaluation L s) ≫ (pullbackUnitIso f).hom
          exact sectionEvaluation_pullback f L s
        exact congrArg (fun z => e.inv ≫ z) hc.symm
      _ = _ := e.inv_hom_id_assoc _
  exact (imageIdeal_eq_of_epi_factor
    (sectionEvaluation (P.obj L) (affinePullbackUnitTop f L s)) (I.comap f) p hp).symm

end EnvelopeProperty.InvertibleBaseIdealPullback
