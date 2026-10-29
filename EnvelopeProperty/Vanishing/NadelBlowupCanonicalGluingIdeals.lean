import EnvelopeProperty.Vanishing.NadelBlowupCanonicalSheafOriginal
import EnvelopeProperty.AlgGeom.SchemeTensorIdealPullback
import Hironaka.Scheme.BlowUp.CoordinateSubspace.Exceptional
import Hironaka.Scheme.BlowUp.Transform.StrictTransform

/-! # The actual exceptional powers and whole tensor-ideal maps on native model charts -/

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalGluingIdeals
open CoordinateSubspace Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n r : ℕ) (j : Fin n) (hj : j.val < r)

theorem exceptionalPowerChart_eq (d : ℕ) :
    ((affineBlowUp.exceptionalIdeal (centerIdeal k n r)) ^ d).comap
        (modelChart k n r j hj) =
      ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv.hom
        (X j ^ d)}) := by
  rw [comap_pow, comap_exceptionalIdeal_modelChart]
  apply le_antisymm <;> apply Scheme.IdealSheafData.le_of_isAffine
  all_goals
    rw [ideal_pow, Pi.pow_apply, ofIdealTop_ideal_top, ofIdealTop_ideal_top,
      Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow, map_pow]

/-- The Jacobian image ideal is the SAME actual original exceptional power
under the actual model chart, as a whole geometric ideal sheaf. -/
theorem exceptionalJacobianChart_eq :
    ((affineBlowUp.exceptionalIdeal (centerIdeal k n r)) ^ (r - 1)).comap
        (modelChart k n r j hj) = NadelBlowupCanonicalSheafChart.imageIdeal k n r j :=
  exceptionalPowerChart_eq k n r j hj (r - 1)

private theorem tensorIdeal_eq_transport {X : Scheme.{u}} (B : X.Modules)
    {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg (fun K : X.IdealSheafData => tensorObj B K.toModules) h)).hom ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap B J.toModules J.toModulesInclusion =
      SchemeTensorObjMorphisms.tensorObjIdealMap B I.toModules I.toModulesInclusion := by
  subst J
  exact Category.id_comp _

private def idealTensorTransport {X Y : Scheme.{u}} (q : Y ⟶ X)
    [IsOpenImmersion q] (B : X.Modules) (J : X.IdealSheafData)
    (I : Y.IdealSheafData) (h : J.comap q = I) :
    (pullback q).obj (tensorObj B J.toModules) ≅
      tensorObj ((pullback q).obj B) I.toModules :=
  SchemeTensorIdealPullback.idealTensorOpenPullbackIso q B J ≪≫
    eqToIso (congrArg (fun K : Y.IdealSheafData =>
      tensorObj ((pullback q).obj B) K.toModules) h)

private theorem idealTensorTransport_inclusion {X Y : Scheme.{u}} (q : Y ⟶ X)
    [IsOpenImmersion q] (B : X.Modules) (J : X.IdealSheafData)
    (I : Y.IdealSheafData) (h : J.comap q = I) :
    (idealTensorTransport q B J I h).hom ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap _ _ I.toModulesInclusion =
      (pullback q).map (SchemeTensorObjMorphisms.tensorObjIdealMap B _ J.toModulesInclusion) := by
  dsimp only [idealTensorTransport]
  rw [Iso.trans_hom, Category.assoc, tensorIdeal_eq_transport _ h]
  exact SchemeTensorIdealPullback.idealTensorOpenPullbackIso_inclusion q B J

/-- Whole native chart pullback of the actual exceptional-power tensor,
with the internally computed actual Jacobian ideal. -/
def exceptionalTensorChartIso (B : (modelBlowUp k n r).Modules) :
    (pullback (modelChart k n r j hj)).obj
        (tensorObj B ((affineBlowUp.exceptionalIdeal (centerIdeal k n r)) ^ (r - 1)).toModules) ≅
      tensorObj ((pullback (modelChart k n r j hj)).obj B)
        (NadelBlowupCanonicalSheafChart.imageIdeal k n r j).toModules :=
  idealTensorTransport (modelChart k n r j hj) B _ _
    (exceptionalJacobianChart_eq k n r j hj)

/-- The ENTIRE original exceptional-power inclusion is retained under the
actual native chart tensor comparison, not merely a generator or support. -/
theorem exceptionalTensorChartIso_inclusion (B : (modelBlowUp k n r).Modules) :
    (exceptionalTensorChartIso k n r j hj B).hom ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap _ _
          (NadelBlowupCanonicalSheafChart.imageIdeal k n r j).toModulesInclusion =
      (pullback (modelChart k n r j hj)).map
        (SchemeTensorObjMorphisms.tensorObjIdealMap B _
          ((affineBlowUp.exceptionalIdeal (centerIdeal k n r)) ^ (r - 1)).toModulesInclusion) := by
  exact idealTensorTransport_inclusion (modelChart k n r j hj) B _ _
    (exceptionalJacobianChart_eq k n r j hj)

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalGluingIdeals
