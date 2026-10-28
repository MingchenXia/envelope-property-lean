import EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverCharts
import EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverChartsRoots

/-! # Every original factor and coefficient-root map in the genuine whole chart -/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverCharts
open NadelAuxiliaryMulticover CyclicSectionAlgebra
variable {X : Scheme.{u}} (U : X.Opens)

/-- The actual original quotient-factor ring map at EVERY original list position. -/
def factorRingMap : (D : List (AuxiliarySection X)) → (e : Frames U D) → (i : Fin D.length) →
    CommRingCat.of (RootRing (D.get i).degree (coefficients U D e i)) ⟶ ring U D e
  | [], _, i => Fin.elim0 i
  | E :: D, e, i => Fin.cases (headMap U E D e)
      (fun j => factorRingMap D (fun k => e k.succ) j ≫ tailMap U E D e) i

/-- Every original quotient-root maps to its SAME original whole-chart root. -/
theorem factorRingMap_root (D : List (AuxiliarySection X)) (e : Frames U D) (i : Fin D.length) :
    factorRingMap U D e i (CyclicSectionAlgebra.root (D.get i).degree (coefficients U D e i)) =
      root U D e i := by
  induction D with
  | nil => exact Fin.elim0 i
  | cons E D ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · dsimp only [factorRingMap, Fin.cases_zero, headMap]
        exact CyclicSectionBaseChange.coefficientMap_root _ _ _ rfl
      · exact congrArg (fun z => tailMap U E D e z) (ih (fun k => e k.succ) j)

variable [IsAffine U.toScheme]

/-- Every original factor of the global multicover is retained by the SAME
whole affine chart, with its actual original frame and root-quotient map. -/
theorem chartMap_factor (D : List (AuxiliarySection X)) (e : Frames U D) (i : Fin D.length) :
    chartMap U D e ≫ factorMap D i =
      Spec.map (factorRingMap U D e i) ≫ singleMap U (D.get i) (e i) := by
  induction D with
  | nil => exact Fin.elim0 i
  | cons E D ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd _ _ = _
        exact Limits.pullback.lift_snd _ _ _
      · change chartMap U (E :: D) e ≫ (tailProjection E D ≫ factorMap D j) = _
        have ht : chartMap U (E :: D) e ≫ tailProjection E D =
            Spec.map (tailMap U E D e) ≫ chartMap U D (fun k => e k.succ) :=
          Limits.pullback.lift_fst _ _ _
        rw [← Category.assoc, ht, Category.assoc, ih]
        change _ = Spec.map (factorRingMap U D (fun k => e k.succ) j ≫ tailMap U E D e) ≫
          singleMap U (D.get j) (e j.succ)
        rw [Spec.map_comp]
        exact (Category.assoc _ _ _).symm

end EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverCharts
