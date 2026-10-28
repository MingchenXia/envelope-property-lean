import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingChangeRing
import EnvelopeProperty.Vanishing.NadelMixedKummerPresentation

/-! # The literal original whole scheme chart over its SAME SNC coordinate ring

The original common-frame algebra, its complete variable-degree quotient,
and the original open-subscheme top-section isomorphism construct the actual
whole scheme chart. Every original root and coefficient triangle is proved.
-/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.WholeChart
open NadelAuxiliaryMulticover NadelMixedKummer
variable {X : Scheme.{u}} (U : X.affineOpens) (D : List (AuxiliarySection X))
  (e : NadelAuxiliaryMulticoverCharts.Frames U.1 D)

/-- The SAME original framed coefficients in the SAME original SNC ring Γ(X,U). -/
def coefficients (i : Fin D.length) : Γ(X, U.1) :=
  U.1.topIso.commRingCatIsoToRingEquiv.toRingHom (NadelAuxiliaryMulticoverCharts.coefficients U.1 D e i)

/-- The literal WHOLE original root quotient over its SAME SNC coordinate ring. -/
abbrev Ring := NadelMixedKummer.Ring (OriginalChart.degree D) (coefficients U D e)

/-- The actual whole original chart algebra is the quotient over the SAME
original SNC ring, constructed from the native original root chart maps. -/
def ringEquiv : NadelAuxiliaryMulticoverCharts.ring U.1 D e ≃+* Ring U D e :=
  (OriginalChart.equiv U.1 D e).trans
    (ChangeRing.equiv (OriginalChart.degree D) (NadelAuxiliaryMulticoverCharts.coefficients U.1 D e)
      U.1.topIso.commRingCatIsoToRingEquiv)

/-- The actual original whole affine-open multicover restriction, with
EVERY original component and nilpotent, is this literal SNC-ring quotient. -/
def schemeIso : Spec (.of (Ring U D e)) ≅ Limits.pullback (projection D) U.1.ι := by
  let : IsAffine U.1.toScheme := U.2
  exact Scheme.Spec.mapIso
    (ChangeRing.equiv (OriginalChart.degree D) (NadelAuxiliaryMulticoverCharts.coefficients U.1 D e)
      U.1.topIso.commRingCatIsoToRingEquiv).toCommRingCatIso.op ≪≫ OriginalChart.schemeIso U.1 D e

/-- The SAME original coefficient-ring triangle of the WHOLE original chart. -/
theorem ringEquiv_structure : (ringEquiv U D e).toRingHom.comp
    (NadelAuxiliaryMulticoverCharts.structureMap U.1 D e).hom =
    (algebraMap Γ(X, U.1) (Ring U D e)).comp U.1.topIso.commRingCatIsoToRingEquiv.toRingHom := by
  change ((ChangeRing.equiv _ _ _).toRingHom.comp (OriginalChart.fromChart U.1 D e)).comp _ = _
  rw [RingHom.comp_assoc]
  have heq : (OriginalChart.fromChart U.1 D e).comp
      (NadelAuxiliaryMulticoverCharts.structureMap U.1 D e).hom =
      algebraMap (NadelAuxiliaryMulticoverCharts.baseRing U.1) (OriginalChart.Ring U.1 D e) :=
    NadelAuxiliaryMulticoverCharts.evaluate_structure _ _ _ _ _ _
  rw [heq]
  exact ChangeRing.equiv_structure _ _ _

/-- EVERY SAME original raw cyclic root retains its actual whole root
coordinate under the original chart comparison. -/
theorem ringEquiv_root (i : Fin D.length) :
    ringEquiv U D e (NadelAuxiliaryMulticoverCharts.root U.1 D e i) =
      root (OriginalChart.degree D) (coefficients U D e) i := by
  change ChangeRing.equiv _ _ _ (OriginalChart.fromChart U.1 D e _) = _
  rw [show OriginalChart.fromChart U.1 D e (NadelAuxiliaryMulticoverCharts.root U.1 D e i) =
      root (OriginalChart.degree D) (NadelAuxiliaryMulticoverCharts.coefficients U.1 D e) i from
    NadelAuxiliaryMulticoverCharts.evaluate_root _ _ _ _ _ _ i]
  exact ChangeRing.equiv_root _ _ _ _

end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.WholeChart
