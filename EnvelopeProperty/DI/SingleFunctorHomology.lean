import EnvelopeProperty.DI.LeadingCartierCycleTransport
import EnvelopeProperty.Algebra.LeftExactHomologyComparison

/-! # The SAME actual single-source map under a genuine left exact functor -/
noncomputable section
namespace EnvelopeProperty.DI.SingleFunctorHomology
open CategoryTheory CategoryTheory.Limits
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type v} [Category.{w} C] [Abelian C]
  {A : Type u} [CommRing A] (F : C ⥤ ModuleCat A)
  [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
private abbrev sectionComplex (K : CochainComplex C ℕ) :=
  (F.mapHomologicalComplex (.up ℕ)).obj K
variable (q : ℕ) (M : C) (K : CochainComplex C ℕ)
  (φ : (HomologicalComplex.single C (.up ℕ) q).obj M ⟶ K)

/-- The SAME original degree component, evaluated after its original single-source unit. -/
def sectionComponent : F.obj M ⟶ (sectionComplex F K).X q :=
  F.map ((HomologicalComplex.singleObjXSelf (.up ℕ) q M).inv ≫ φ.f q)

omit [PreservesFiniteLimits F] in
/-- Its closedness is the original cochain-map identity, with no supplied cycle certificate. -/
theorem sectionComponent_closed : ∀ j, (ComplexShape.up ℕ).Rel q j →
    sectionComponent F q M K φ ≫ (sectionComplex F K).d q j = 0 := by
  intro j _
  change F.map _ ≫ F.map (K.d q j) = 0
  rw [← Functor.map_comp]
  have h : ((HomologicalComplex.singleObjXSelf (.up ℕ) q M).inv ≫ φ.f q) ≫ K.d q j = 0 := by
    rw [Category.assoc, φ.comm q j, ← Category.assoc]
    change ((HomologicalComplex.singleObjXSelf (.up ℕ) q M).inv ≫ 0) ≫ φ.f j = 0
    rw [comp_zero, zero_comp]
  rw [h, Functor.map_zero]

/-- The ENTIRE actual homology map is retained by the original canonical comparison. -/
theorem singleClassMap_evaluation :
    LeadingCartierCycleTransport.singleClassMap q (F.obj M)
        (sectionComplex F K) (sectionComponent F q M K φ)
        (sectionComponent_closed F q M K φ) ≫ LeftExactHomologyComparison.map (K.sc q) F =
      F.map ((HomologicalComplex.singleObjHomologySelfIso (.up ℕ) q M).inv ≫
        HomologicalComplex.homologyMap φ q) := by
  let KΓ := sectionComplex F K
  let L := KΓ.liftCycles (sectionComponent F q M K φ) (q+1) (by simp)
    (sectionComponent_closed F q M K φ (q+1) (by simp))
  let : Mono (F.map (K.iCycles q)) := mono_of_isLimit_fork
    (isLimitForkMapOfIsLimit' F (K.sc q).iCycles_g (K.sc q).cyclesIsKernel)
  have hc : L ≫ (LeftExactHomologyComparison.cyclesIso (K.sc q) F).hom =
      F.map ((HomologicalComplex.singleObjCyclesSelfIso (.up ℕ) q M).inv ≫
        HomologicalComplex.cyclesMap φ q) := by
    apply (cancel_mono (F.map (K.iCycles q))).mp
    calc
      _ = L ≫ ((K.sc q).map F).iCycles :=
        (Category.assoc _ _ _).trans
          (congrArg (fun t => L ≫ t)
            (LeftExactHomologyComparison.cyclesIso_hom_iCycles (K.sc q) F))
      _ = sectionComponent F q M K φ := KΓ.liftCycles_i _ _ _ _
      _ = F.map (((HomologicalComplex.singleObjCyclesSelfIso (.up ℕ) q M).inv ≫
          HomologicalComplex.cyclesMap φ q) ≫ K.iCycles q) := by
        apply congrArg F.map
        rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
          HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles]
      _ = _ := F.map_comp _ _

  have hn : ((HomologicalComplex.singleObjCyclesSelfIso (.up ℕ) q M).inv ≫
      HomologicalComplex.cyclesMap φ q) ≫ K.homologyπ q =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) q M).inv ≫
        HomologicalComplex.homologyMap φ q := by
    rw [Category.assoc, ← HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ]
  rw [LeadingCartierCycleTransport.singleClassMap_eq_liftCycles]
  change (L ≫ KΓ.homologyπ q) ≫ LeftExactHomologyComparison.map (K.sc q) F = _
  calc
    _ = L ≫ ((LeftExactHomologyComparison.cyclesIso (K.sc q) F).hom ≫
        F.map (K.sc q).homologyπ) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun t => L ≫ t) (LeftExactHomologyComparison.homologyπ_map (K.sc q) F))
    _ = (L ≫ (LeftExactHomologyComparison.cyclesIso (K.sc q) F).hom) ≫
        F.map (K.sc q).homologyπ := (Category.assoc _ _ _).symm
    _ = F.map ((HomologicalComplex.singleObjCyclesSelfIso (.up ℕ) q M).inv ≫
        HomologicalComplex.cyclesMap φ q) ≫ F.map (K.sc q).homologyπ :=
      congrArg (fun t => t ≫ F.map (K.sc q).homologyπ) hc
    _ = F.map (((HomologicalComplex.singleObjCyclesSelfIso (.up ℕ) q M).inv ≫
        HomologicalComplex.cyclesMap φ q) ≫ K.homologyπ q) := (F.map_comp _ _).symm
    _ = _ := congrArg F.map hn
end EnvelopeProperty.DI.SingleFunctorHomology
