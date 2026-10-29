import EnvelopeProperty.DI.ActualWittHigherExteriorEvaluation
import EnvelopeProperty.DI.ActualWittHigherExteriorMaps
import EnvelopeProperty.DI.CechTotalCupEvaluation
import EnvelopeProperty.DI.ActualWittExteriorCartier
import EnvelopeProperty.DI.AffineLocalCochainHomology
import EnvelopeProperty.DI.AffineLocalMapLocality

/-!
# Actual Witt Higher Sheaf Cartier

The actual higher Witt maps induce the original global Cartier sheaf class. -/
noncomputable section
universe u
namespace EnvelopeProperty.DI.ActualWittHigherSheafCartier
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EnvelopeProperty EnvelopeProperty.DI EnvelopeProperty.Cartier
open EnvelopeProperty.DeligneIllusie
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem single_comparison {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] (q : ℕ) (M : C) :
    (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) q (F.obj M)).inv ≫
        HomologicalComplex.homologyMap
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) q).app M).inv q ≫
        LeftExactHomologyComparison.map
          (((HomologicalComplex.single C (.up ℕ) q).obj M).sc q) F =
      F.map (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) q M).inv := by
  let S := (HomologicalComplex.single C (.up ℕ) q).obj M
  let S' := (HomologicalComplex.single D (.up ℕ) q).obj (F.obj M)
  let α := ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) q).app M).inv
  let ℓ := (HomologicalComplex.singleObjCyclesSelfIso (.up ℕ) q (F.obj M)).inv ≫
    HomologicalComplex.cyclesMap α q ≫
      (LeftExactHomologyComparison.cyclesIso (S.sc q) F).hom
  have hℓ : ℓ = F.map (HomologicalComplex.singleObjCyclesSelfIso (.up ℕ) q M).inv := by
    let : Mono (F.map (S.iCycles q)) := mono_of_isLimit_fork
      (isLimitForkMapOfIsLimit' F (S.sc q).iCycles_g (S.sc q).cyclesIsKernel)
    apply (cancel_mono (F.map (S.iCycles q))).mp
    calc
      _ = (HomologicalComplex.singleObjCyclesSelfIso (.up ℕ) q (F.obj M)).inv ≫
          HomologicalComplex.cyclesMap α q ≫
            ((LeftExactHomologyComparison.cyclesIso (S.sc q) F).hom ≫ F.map (S.sc q).iCycles) := by
        simp only [ℓ, Category.assoc]
        rfl
      _ = (HomologicalComplex.singleObjCyclesSelfIso (.up ℕ) q (F.obj M)).inv ≫
          HomologicalComplex.cyclesMap α q ≫ ((S.sc q).map F).iCycles :=
        congrArg (fun t =>
          (HomologicalComplex.singleObjCyclesSelfIso (.up ℕ) q (F.obj M)).inv ≫
            HomologicalComplex.cyclesMap α q ≫ t)
          (LeftExactHomologyComparison.cyclesIso_hom_iCycles (S.sc q) F)
      _ = (HomologicalComplex.singleObjCyclesSelfIso (.up ℕ) q (F.obj M)).inv ≫
          S'.iCycles q ≫ α.f q :=
        congrArg (fun t =>
          (HomologicalComplex.singleObjCyclesSelfIso (.up ℕ) q (F.obj M)).inv ≫ t)
          (HomologicalComplex.cyclesMap_i α q)
      _ = (HomologicalComplex.singleObjXSelf (.up ℕ) q (F.obj M)).inv ≫ α.f q :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ α.f q)
          (HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles (.up ℕ) q (F.obj M)))
      _ = F.map (HomologicalComplex.singleObjXSelf (.up ℕ) q M).inv := by
        rw [show α.f q =
          (HomologicalComplex.singleObjXSelf (.up ℕ) q (F.obj M)).hom ≫
            F.map (HomologicalComplex.singleObjXSelf (.up ℕ) q M).inv from
          HomologicalComplex.singleMapHomologicalComplex_inv_app_self F (.up ℕ) q M,
          Iso.inv_hom_id_assoc]
      _ = _ := (congrArg F.map
        (HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles (.up ℕ) q M)).symm.trans
          (F.map_comp _ _)
  have hσ := HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ (.up ℕ) q (F.obj M)
  calc
    _ = ((HomologicalComplex.singleObjCyclesSelfIso (.up ℕ) q (F.obj M)).inv ≫
        S'.homologyπ q) ≫ HomologicalComplex.homologyMap α q ≫
          LeftExactHomologyComparison.map (S.sc q) F :=
      congrArg (fun t => t ≫ HomologicalComplex.homologyMap α q ≫
        LeftExactHomologyComparison.map (S.sc q) F) hσ.symm
    _ = (HomologicalComplex.singleObjCyclesSelfIso (.up ℕ) q (F.obj M)).inv ≫
        HomologicalComplex.cyclesMap α q ≫
          (((S.sc q).map F).homologyπ ≫ LeftExactHomologyComparison.map (S.sc q) F) := by
      simp only [Category.assoc]
      exact congrArg (fun t =>
        (HomologicalComplex.singleObjCyclesSelfIso (.up ℕ) q (F.obj M)).inv ≫ t)
        (HomologicalComplex.homologyπ_naturality_assoc α q
          (LeftExactHomologyComparison.map (S.sc q) F))
    _ = ℓ ≫ F.map (S.homologyπ q) := by
      rw [LeftExactHomologyComparison.homologyπ_map]
      simp only [ℓ, Category.assoc]
      rfl
    _ = _ := (congrArg (fun t => t ≫ F.map (S.homologyπ q)) hℓ).trans
      ((F.map_comp _ _).symm.trans (congrArg F.map
        (HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ (.up ℕ) q M)))

section OriginalReadback
variable {Z : Scheme.{u}} {W : Z.Opens} (hW : IsAffineOpen W)
local notation "L" => Scheme.Modules.restrictFunctor W.ι
local notation "I" => Scheme.Modules.restrictFunctor hW.isoSpec.inv
local notation "J" => Scheme.Modules.restrictFunctor hW.fromSpec
private abbrev gammaFunctor : (Spec (Z.presheaf.obj (op W))).Modules ⥤
    ModuleCat (Z.presheaf.obj (op W)) := moduleSpecΓFunctor
local notation "G" => gammaFunctor (W := W)

private def readbackFunctorIso : (L) ⋙ (I) ≅ (J) :=
  NatIso.ofComponents (AffineLocalMapRestriction.specReadbackIso hW) (by
    intro M N a
    exact AffineLocalMapRestriction.specReadback_naturality hW M N a)

private theorem readback_homology (K : CochainComplex Z.Modules ℕ) (q : ℕ) :
    HomologicalComplex.homologyMap (AffineLocalCochainEvaluation.specComplexIso hW K).hom q ≫
        (SchemeOpenRestrictionHomology.homologyIso hW.fromSpec K q).hom =
      (SchemeOpenRestrictionHomology.homologyIso hW.isoSpec.inv
        (SchemeOpenRestrictionHomology.restrictedComplex W.ι K) q).hom ≫
        (I).map (SchemeOpenRestrictionHomology.homologyIso W.ι K q).hom ≫
          (AffineLocalMapRestriction.specReadbackIso hW ((K).homology q)).hom := by
  let : PreservesLimits (L) := Scheme.Modules.restrictFunctor_preservesLimits W.ι
  let : PreservesLimits (I) :=
    Scheme.Modules.restrictFunctor_preservesLimits hW.isoSpec.inv
  let : PreservesLimits (J) :=
    Scheme.Modules.restrictFunctor_preservesLimits hW.fromSpec
  let : PreservesFiniteLimits ((L) ⋙ (I)) := comp_preservesFiniteLimits _ _
  let : (L).PreservesHomology := SchemeOpenRestrictionHomology.preservesHomology W.ι
  let : (I).PreservesHomology :=
    SchemeOpenRestrictionHomology.preservesHomology hW.isoSpec.inv
  let : (J).PreservesHomology :=
    SchemeOpenRestrictionHomology.preservesHomology hW.fromSpec
  let S := K.sc q
  have hκ : ShortComplex.homologyMap (S.mapNatTrans (readbackFunctorIso hW).hom) =
      HomologicalComplex.homologyMap (AffineLocalCochainEvaluation.specComplexIso hW K).hom q := rfl
  have h := LeftExactHomologyComparison.natTrans_naturality
    (S := S) (J) (readbackFunctorIso hW).hom
  rw [hκ, LeftExactHomologyCoherence.map_comp,
    LeftExactHomologyCoherence.map_eq_mapHomologyIso,
    LeftExactHomologyCoherence.map_eq_mapHomologyIso,
    LeftExactHomologyCoherence.map_eq_mapHomologyIso] at h
  exact h

private theorem original_class_readback (q : ℕ) (M : Z.Modules)
    (K : CochainComplex Z.Modules ℕ)
    (φ : (HomologicalComplex.single W.toScheme.Modules (.up ℕ) q).obj
        (M.restrict W.ι) ⟶ SchemeOpenRestrictionHomology.restrictedComplex W.ι K) :
    AffineLocalCochainHomology.specHomologyReadback hW q M K φ =
      AffineLocalMapRestriction.sectionReadback hW M ((K).homology q)
        ((HomologicalComplex.singleObjHomologySelfIso (.up ℕ) q (M.restrict W.ι)).inv ≫
          HomologicalComplex.homologyMap φ q ≫
            (SchemeOpenRestrictionHomology.homologyIso W.ι K q).hom) := by
  let : PreservesLimits (I) :=
    Scheme.Modules.restrictFunctor_preservesLimits hW.isoSpec.inv
  let : (I).PreservesHomology :=
    SchemeOpenRestrictionHomology.preservesHomology hW.isoSpec.inv
  let rM := AffineLocalMapRestriction.specReadbackIso hW M
  let rH := AffineLocalMapRestriction.specReadbackIso hW ((K).homology q)
  let KW := SchemeOpenRestrictionHomology.restrictedComplex W.ι K
  let α := ((HomologicalComplex.singleMapHomologicalComplex (I) (.up ℕ) q).app
    (M.restrict W.ι)).inv
  have hs := single_comparison (I) q (M.restrict W.ι)
  rw [LeftExactHomologyCoherence.map_eq_mapHomologyIso] at hs
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor W.toScheme.Modules (.up ℕ) q).map φ) (I)
  have hn' : HomologicalComplex.homologyMap
      (((I).mapHomologicalComplex (.up ℕ)).map φ) q ≫
        (SchemeOpenRestrictionHomology.homologyIso hW.isoSpec.inv KW q).hom =
      (ShortComplex.mapHomologyIso
        (((HomologicalComplex.single W.toScheme.Modules (.up ℕ) q).obj
          (M.restrict W.ι)).sc q) (I)).hom ≫
        (I).map (HomologicalComplex.homologyMap φ q) := hn
  have h :
      (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) q
        (M.restrict hW.fromSpec)).inv ≫
        HomologicalComplex.homologyMap
          (AffineLocalCochainEvaluation.specRepresentative hW q M K φ) q ≫
        (SchemeOpenRestrictionHomology.homologyIso hW.fromSpec K q).hom =
      rM.inv ≫ (I).map
        ((HomologicalComplex.singleObjHomologySelfIso (.up ℕ) q (M.restrict W.ι)).inv ≫
          HomologicalComplex.homologyMap φ q ≫
            (SchemeOpenRestrictionHomology.homologyIso W.ι K q).hom) ≫ rH.hom := by
    simp only [AffineLocalCochainEvaluation.specRepresentative,
      HomologicalComplex.homologyMap_comp, Category.assoc,
      HomologicalComplex.singleObjHomologySelfIso_inv_naturality_assoc]
    rw [readback_homology, reassoc_of% hn', reassoc_of% hs]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  have hΓ := congrArg (fun t =>
    (GeometricAffineHomology.moduleSectionsIso hW M).inv ≫ (G).map t ≫
      (GeometricAffineHomology.moduleSectionsIso hW ((K).homology q)).hom) h
  simpa only [AffineLocalCochainHomology.specHomologyReadback,
    AffineLocalMapRestriction.sectionReadback, Functor.map_comp, Category.assoc] using hΓ

end OriginalReadback

variable (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p] [PerfectRing κ p]
  {Xtilde : Scheme.{u}} (f : Xtilde ⟶ Spec (.of (WittTwo.Ring p κ)))
  (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f]
local notation "Y" => ActualWittCechOneMap.twist p κ f
local notation "U" => ActualWittCechOneMap.cover p κ f n
local notation "K" => ActualWittCechOneMap.targetComplex p κ f n
local notation "M" r => CanonicalGeometry.exteriorCotangentSheaf
  (ActualWittCechOneMap.twistMap p κ f) (r+1)
private instance specialFibreSmooth :
    SmoothOfRelativeDimension n (ActualWittCechOneMap.specialFibreMap p κ f) :=
  WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n

def actualMemberMap (r : ℕ) (i : ActualWittCechOneMap.CoverIndex p κ f n) :
    (HomologicalComplex.single (U i).toScheme.Modules (.up ℕ) (r+1)).obj
        ((Scheme.Modules.restrictFunctor (U i).ι).obj (M r)) ⟶
      SchemeOpenRestrictionHomology.restrictedComplex (U i).ι K :=
  ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.restrictFunctor (U i).ι) (.up ℕ) (r+1)).app (M r)).inv ≫
    (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex (.up ℕ)).map
      (ActualWittHigherExteriorMaps.higherCochainMap p κ f n r)) ≫
      DeligneIllusieCechTotalEvaluation.localEvaluation U K i

private def memberExterior (r : ℕ) (i : ActualWittCechOneMap.CoverIndex p κ f n) :=
  ActualWittExteriorCartier.exteriorSections p κ f n i.property.1
    (DeligneIllusieWittGlobalDescent.coordinates p κ f n i)
    (DeligneIllusieWittGlobalDescent.coordinates_etale p κ f n i)
    (DeligneIllusieWittGlobalDescent.coverLift p κ f n i)
    (DeligneIllusieWittGlobalDescent.coverLift_reduction p κ f n i) (r+1)

private theorem memberClass_of_evaluation (r : ℕ) (i : ActualWittCechOneMap.CoverIndex p κ f n)
    (heval : (CechTotalCup.memberEvaluation (ActualWittCechOneMap.specialFibreMap p κ f)
        p n U (r+1) i).comp
          ((ActualWittHigherExteriorMaps.higherMap p κ f n r).val.app (op (U i))).hom =
      (memberExterior p κ f n r i).hom) :
    (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) (r+1)
        ((Scheme.Modules.restrictFunctor (U i).ι).obj (M r))).inv ≫
      HomologicalComplex.homologyMap (actualMemberMap p κ f n r i) (r+1) ≫
        (SchemeOpenRestrictionHomology.homologyIso (U i).ι K (r+1)).hom =
    (Scheme.Modules.restrictFunctor (U i).ι).map
      (GeometricSheafCartier.inverseCartierIso
        (ActualWittCechOneMap.specialFibreMap p κ f) p n (r+1)).hom := by
  let hW : IsAffineOpen (U i) := RelativeTwistedAffineBasis.twistedOpen_isAffine
    (ActualWittCechOneMap.specialFibreMap p κ f) p
    (DeligneIllusieWittGlobalDescent.sourceOpen p κ f n i)
    (DeligneIllusieWittGlobalDescent.sourceOpen_affine p κ f n i)
  let φ := actualMemberMap p κ f n r i
  let a := (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) (r+1)
    ((M r).restrict (U i).ι)).inv ≫ HomologicalComplex.homologyMap φ (r+1) ≫
      (SchemeOpenRestrictionHomology.homologyIso (U i).ι K (r+1)).hom
  let b := (Scheme.Modules.restrictFunctor (U i).ι).map
    (GeometricSheafCartier.inverseCartierIso
      (ActualWittCechOneMap.specialFibreMap p κ f) p n (r+1)).hom
  have hf : (HomologicalComplex.singleObjXSelf (.up ℕ) (r+1)
      ((M r).restrict (U i).ι)).inv ≫ φ.f (r+1) =
      (Scheme.Modules.restrictFunctor (U i).ι).map
        (ActualWittHigherExteriorMaps.higherMap p κ f n r) ≫
          (DeligneIllusieCechTotalEvaluation.localEvaluation U K i).f (r+1) := by
    simp only [φ, actualMemberMap, HomologicalComplex.comp_f, Iso.app_inv,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      Functor.mapHomologicalComplex,
      ActualWittHigherExteriorMaps.higherCochainMap_f_self, Functor.map_comp,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc]
  have hr : AffineLocalMapRestriction.sectionReadback hW (M r) ((K).X (r+1))
      ((HomologicalComplex.singleObjXSelf (.up ℕ) (r+1)
        ((M r).restrict (U i).ι)).inv ≫ φ.f (r+1)) = memberExterior p κ f n r i := by
    rw [hf]
    apply ModuleCat.hom_ext
    exact (CechTotalCup.memberEvaluation_sectionReadback
      (ActualWittCechOneMap.specialFibreMap p κ f) p n U (r+1) i hW (M r)
      (ActualWittHigherExteriorMaps.higherMap p κ f n r)).symm.trans heval
  have he : AffineLocalCochainEvaluation.evaluateCochain hW (r+1) (M r) K φ =
      ActualWittExteriorCartier.representative p κ f n i.property.1
        (DeligneIllusieWittGlobalDescent.coordinates p κ f n i)
        (DeligneIllusieWittGlobalDescent.coordinates_etale p κ f n i)
        (DeligneIllusieWittGlobalDescent.coverLift p κ f n i)
        (DeligneIllusieWittGlobalDescent.coverLift_reduction p κ f n i) (r+1) := by
    apply HomologicalComplex.from_single_hom_ext
    rw [AffineLocalCochainEvaluation.evaluateCochain_f, hr,
      ActualWittExteriorCartier.representative_f]
    rfl
  let : ∀ q, ((K).X q).IsQuasicoherent := fun q =>
    GeometricRelativeFrobeniusQuasicoherent.complex_term_isQuasicoherent
      (ActualWittCechOneMap.specialFibreMap p κ f) p n q
  have hc : AffineLocalMapRestriction.sectionReadback hW (M r) ((K).homology (r+1)) a =
      (GeometricSheafCartier.inverseCartierIso
        (ActualWittCechOneMap.specialFibreMap p κ f) p n (r+1)).hom.val.app (op (U i)) := by
    rw [← original_class_readback hW (r+1) (M r) K φ,
      ← AffineLocalCochainHomology.canonical_class hW (r+1) (M r) K φ,
      he, ← GeometricHomologyNaturality.homologySectionsIso_hom_eq hW K (r+1)]
    exact (ActualWittExteriorCartier.classSections_eq_homologyRepresentative p κ f n
      i.property.1 (DeligneIllusieWittGlobalDescent.coordinates p κ f n i)
      (DeligneIllusieWittGlobalDescent.coordinates_etale p κ f n i)
      (DeligneIllusieWittGlobalDescent.coverLift p κ f n i)
      (DeligneIllusieWittGlobalDescent.coverLift_reduction p κ f n i) (r+1)).symm.trans
      (ActualWittExteriorCartier.classSections_eq_inverseCartier p κ f n
        i.property.1 (DeligneIllusieWittGlobalDescent.coordinates p κ f n i)
        (DeligneIllusieWittGlobalDescent.coordinates_etale p κ f n i)
        (DeligneIllusieWittGlobalDescent.coverLift p κ f n i)
        (DeligneIllusieWittGlobalDescent.coverLift_reduction p κ f n i) (r+1))
  have hread : AffineLocalMapRestriction.sectionReadback hW (M r) ((K).homology (r+1)) a =
      AffineLocalMapRestriction.sectionReadback hW (M r) ((K).homology (r+1)) b :=
    hc.trans (AffineLocalMapRestriction.sectionReadback_restrict hW (M r)
      ((K).homology (r+1)) _).symm
  let J := Scheme.Modules.restrictFunctor hW.fromSpec
  let KC := SchemeOpenRestrictionHomology.restrictedComplex hW.fromSpec K
  let : ∀ q, (KC.X q).IsQuasicoherent := by
    intro q
    let : ((K).X q).IsQuasicoherent := (inferInstance : ∀ s, ((K).X s).IsQuasicoherent) q
    change (((K).X q).restrict hW.fromSpec).IsQuasicoherent
    infer_instance
  let : (KC.homology (r+1)).IsQuasicoherent :=
    AffineQuasicoherentComplexHomology.homology_isQuasicoherent Γ(Y,U i) KC (r+1)
  let e := J.mapIso (GeometricSheafCartier.inverseCartierIso
    (ActualWittCechOneMap.specialFibreMap p κ f) p n (r+1)) ≪≫
      (SchemeOpenRestrictionHomology.homologyIso hW.fromSpec K (r+1)).symm
  let : (J.obj (M r)).IsQuasicoherent :=
    (Scheme.Modules.isQuasicoherent (Spec Γ(Y,U i))).prop_of_iso e.symm inferInstance
  apply AffineLocalMapRestriction.localMap_ext_of_adjoint_at_affine hW le_rfl
    (M r) ((K).homology (r+1)) a b
  rw [AffineLocalMapRestriction.localAdjoint_sections hW (M r) ((K).homology (r+1)) a,
    AffineLocalMapRestriction.localAdjoint_sections hW (M r) ((K).homology (r+1)) b, hread]

/-- The entire actual original higher sheaf homology class is inverse Cartier. -/
theorem memberClass (r : ℕ) (hr : r+1 < p)
    (i : ActualWittCechOneMap.CoverIndex p κ f n) :
    (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) (r+1)
        ((Scheme.Modules.restrictFunctor (U i).ι).obj (M r))).inv ≫
      HomologicalComplex.homologyMap (actualMemberMap p κ f n r i) (r+1) ≫
        (SchemeOpenRestrictionHomology.homologyIso (U i).ι K (r+1)).hom =
    (Scheme.Modules.restrictFunctor (U i).ι).map
      (GeometricSheafCartier.inverseCartierIso
        (ActualWittCechOneMap.specialFibreMap p κ f) p n (r+1)).hom := by
  apply memberClass_of_evaluation p κ f n r i
  have actualHigherEvaluationProof :=
    ActualWittHigherExteriorEvaluation.memberHigher p κ f n i r hr
  run_tac Lean.Elab.Tactic.withMainContext do
    let mut proof : Option Lean.Expr := none
    for d in (← Lean.getLCtx) do
      if d.userName.eraseMacroScopes.toString == "actualHigherEvaluationProof" then
        proof := some d.toExpr
    let some proofExpr := proof | throwError "Actual higher evaluation proof was not found"
    (← Lean.Elab.Tactic.getMainGoal).assign proofExpr

end EnvelopeProperty.DI.ActualWittHigherSheafCartier
