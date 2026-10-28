import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechResolution
import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechTotalAugmentation
import ModularCurves.ForMathlib.TotalComplexUpNatDecomposition

/-! # Actual degree-zero quasi-isomorphism of the SAME original module total augmentation -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechTotalDegreeZero
open CategoryTheory Category Limits AlgebraicGeometry TopologicalSpace
open DeligneIllusieLocalContinuationCechAugmentation DeligneIllusieLocalContinuationCechBicomplex
open DeligneIllusieLocalContinuationCechTotalAugmentation DeligneIllusieLocalContinuationCechResolution
universe u
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (E : CochainComplex X.Modules ℕ)

private theorem d_zero_pi_inner :
    (totalComplex U E).d 0 1 ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 1 1 =
      HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 0 0 ≫ ((bicomplex U E).X 0).d 0 1 := by
  simpa [totalComplex] using HomologicalComplex₂.total_d_πTotalUpNat (bicomplex U E) 0 0 1 rfl

private theorem d_zero_pi_outer :
    (totalComplex U E).d 0 1 ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) 1 0 1 =
      HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 0 0 ≫ ((bicomplex U E).d 0 1).f 0 := by
  simpa [totalComplex] using HomologicalComplex₂.total_d_πTotalUpNat (bicomplex U E) 0 1 0 rfl

private theorem zero_component_inner_closed :
    ((totalComplex U E).iCycles 0 ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 0 0) ≫
      ((bicomplex U E).X 0).d 0 1 = 0 := by
  calc
    _ = (totalComplex U E).iCycles 0 ≫
        (HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 0 0 ≫ ((bicomplex U E).X 0).d 0 1) :=
      Category.assoc _ _ _
    _ = (totalComplex U E).iCycles 0 ≫
        ((totalComplex U E).d 0 1 ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 1 1) :=
      congrArg (fun z => (totalComplex U E).iCycles 0 ≫ z) (d_zero_pi_inner U E).symm
    _ = ((totalComplex U E).iCycles 0 ≫ (totalComplex U E).d 0 1) ≫
        HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 1 1 := (Category.assoc _ _ _).symm
    _ = 0 := by
      rw [HomologicalComplex.iCycles_d]
      exact zero_comp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def axisLiftZero (hU : ⨆ i, U i = ⊤) : (totalComplex U E).cycles 0 ⟶ E.X 0 := by
  have : Mono (augmentation U (E.X 0)) := augmentation_mono (E.X 0) U hU
  exact (augmentation_exact (E.X 0) U hU).lift
    ((totalComplex U E).iCycles 0 ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 0 0)
    (zero_component_inner_closed U E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem axisLiftZero_augmentation (hU : ⨆ i, U i = ⊤) :
    axisLiftZero U E hU ≫ augmentation U (E.X 0) =
      (totalComplex U E).iCycles 0 ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 0 0 := by
  have : Mono (augmentation U (E.X 0)) := augmentation_mono (E.X 0) U hU
  exact (augmentation_exact (E.X 0) U hU).lift_f
    ((totalComplex U E).iCycles 0 ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 0 0)
    (zero_component_inner_closed U E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem axisLiftZero_closed (hU : ⨆ i, U i = ⊤) :
    axisLiftZero U E hU ≫ E.d 0 1 = 0 := by
  have : Mono (augmentation U (E.X 1)) := augmentation_mono (E.X 1) U hU
  have hnat : augmentation U (E.X 0) ≫ ((bicomplex U E).d 0 1).f 0 =
      E.d 0 1 ≫ augmentation U (E.X 1) := augmentation_naturality U (E.d 0 1)
  apply (cancel_mono (augmentation U (E.X 1))).mp
  calc
    (axisLiftZero U E hU ≫ E.d 0 1) ≫ augmentation U (E.X 1) =
        axisLiftZero U E hU ≫ (E.d 0 1 ≫ augmentation U (E.X 1)) := Category.assoc _ _ _
    _ = axisLiftZero U E hU ≫
        (augmentation U (E.X 0) ≫ ((bicomplex U E).d 0 1).f 0) :=
      congrArg (fun z => axisLiftZero U E hU ≫ z) hnat.symm
    _ = (axisLiftZero U E hU ≫ augmentation U (E.X 0)) ≫
        ((bicomplex U E).d 0 1).f 0 := (Category.assoc _ _ _).symm
    _ = ((totalComplex U E).iCycles 0 ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 0 0) ≫
        ((bicomplex U E).d 0 1).f 0 :=
      congrArg (fun z => z ≫ ((bicomplex U E).d 0 1).f 0) (axisLiftZero_augmentation U E hU)
    _ = (totalComplex U E).iCycles 0 ≫
        ((totalComplex U E).d 0 1 ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) 1 0 1) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun z => (totalComplex U E).iCycles 0 ≫ z) (d_zero_pi_outer U E).symm)
    _ = 0 ≫ augmentation U (E.X 1) := by
      rw [← Category.assoc, HomologicalComplex.iCycles_d, zero_comp, zero_comp]

private def cyclesInverseZero (hU : ⨆ i, U i = ⊤) : (totalComplex U E).cycles 0 ⟶ E.cycles 0 :=
  E.liftCycles (axisLiftZero U E hU) 1 (by simp) (axisLiftZero_closed U E hU)

private theorem cyclesInverseZero_iCycles (hU : ⨆ i, U i = ⊤) :
    cyclesInverseZero U E hU ≫ E.iCycles 0 = axisLiftZero U E hU :=
  E.liftCycles_i (axisLiftZero U E hU) 1 (by simp) (axisLiftZero_closed U E hU)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual native cycles map of the SAME original total augmentation is the forward isomorphism. -/
def cyclesIsoZero (hU : ⨆ i, U i = ⊤) : E.cycles 0 ≅ (totalComplex U E).cycles 0 where
  hom := HomologicalComplex.cyclesMap (totalAugmentation U E) 0
  inv := cyclesInverseZero U E hU
  hom_inv_id := by
    have : Mono (augmentation U (E.X 0)) := augmentation_mono (E.X 0) U hU
    apply (cancel_mono (E.iCycles 0 ≫ augmentation U (E.X 0))).mp
    calc
      _ = HomologicalComplex.cyclesMap (totalAugmentation U E) 0 ≫
          ((cyclesInverseZero U E hU ≫ E.iCycles 0) ≫ augmentation U (E.X 0)) := by
        simp only [Category.assoc]
      _ = HomologicalComplex.cyclesMap (totalAugmentation U E) 0 ≫
          (axisLiftZero U E hU ≫ augmentation U (E.X 0)) :=
        congrArg (fun z => HomologicalComplex.cyclesMap (totalAugmentation U E) 0 ≫
          (z ≫ augmentation U (E.X 0))) (cyclesInverseZero_iCycles U E hU)
      _ = HomologicalComplex.cyclesMap (totalAugmentation U E) 0 ≫
          ((totalComplex U E).iCycles 0 ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 0 0) :=
        congrArg (fun z => HomologicalComplex.cyclesMap (totalAugmentation U E) 0 ≫ z)
          (axisLiftZero_augmentation U E hU)
      _ = (E.iCycles 0 ≫ (totalAugmentation U E).f 0) ≫
          HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 0 0 :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 0 0)
            (HomologicalComplex.cyclesMap_i (totalAugmentation U E) 0))
      _ = E.iCycles 0 ≫ augmentation U (E.X 0) := by
        rw [totalAugmentation_f]
        calc
          _ = (E.iCycles 0 ≫ augmentation U (E.X 0)) ≫
              (HomologicalComplex₂.ιTotal (bicomplex U E) (.up ℕ) 0 0 0 rfl ≫
                HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 0 0) := by
            simp only [Category.assoc]
          _ = (E.iCycles 0 ≫ augmentation U (E.X 0)) ≫ 𝟙 _ :=
            congrArg (fun z => (E.iCycles 0 ≫ augmentation U (E.X 0)) ≫ z)
              (HomologicalComplex₂.ιTotal_πTotalUpNat_self (bicomplex U E) 0 0)
          _ = E.iCycles 0 ≫ augmentation U (E.X 0) := Category.comp_id _
      _ = 𝟙 _ ≫ (E.iCycles 0 ≫ augmentation U (E.X 0)) := (Category.id_comp _).symm
  inv_hom_id := by
    apply (cancel_mono ((totalComplex U E).iCycles 0)).mp
    calc
      _ = cyclesInverseZero U E hU ≫
          (E.iCycles 0 ≫ (totalAugmentation U E).f 0) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun z => cyclesInverseZero U E hU ≫ z)
            (HomologicalComplex.cyclesMap_i (totalAugmentation U E) 0))
      _ = axisLiftZero U E hU ≫ (totalAugmentation U E).f 0 :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ (totalAugmentation U E).f 0) (cyclesInverseZero_iCycles U E hU))
      _ = ((totalComplex U E).iCycles 0 ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 0 0) ≫
          HomologicalComplex₂.ιTotal (bicomplex U E) (.up ℕ) 0 0 0 rfl := by
        rw [totalAugmentation_f, ← Category.assoc, axisLiftZero_augmentation]
      _ = (totalComplex U E).iCycles 0 := by
        rw [Category.assoc, HomologicalComplex₂.totalUpNat_zero_decomposition]
        exact Category.comp_id _
      _ = 𝟙 _ ≫ (totalComplex U E).iCycles 0 := (Category.id_comp _).symm

/-- Actual degree-zero quasi-isomorphism; all row exactness/monicity are DERIVED from the honest cover. -/
theorem totalAugmentation_quasiIsoAt_zero (hU : ⨆ i, U i = ⊤) :
    QuasiIsoAt (totalAugmentation U E) 0 := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : IsIso (HomologicalComplex.cyclesMap (totalAugmentation U E) 0) :=
    (cyclesIsoZero U E hU).isIso_hom
  have hcomp : IsIso (HomologicalComplex.homologyMap (totalAugmentation U E) 0 ≫
      (totalComplex U E).isoHomologyπ₀.inv) := by
    rw [CochainComplex.isoHomologyπ₀_inv_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap (totalAugmentation U E) 0)
    (totalComplex U E).isoHomologyπ₀.inv

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechTotalDegreeZero
