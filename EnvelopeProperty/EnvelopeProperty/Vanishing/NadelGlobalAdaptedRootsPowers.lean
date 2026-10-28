import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsRowIdeals
import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverRootSectionPowers
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps

/-! # Actual powers of original normalized root zero ideals

The native tensor-power equation of the SAME normalized root computes its
entire original zero-ideal power. The original row/copy label then retains
the original divisor and original auxiliary section ideal in the product.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules TopologicalSpace
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open SchemeLineSectionEvaluation NadelBertiniFibreIdeals
open SchemeGlobalSectionTensorPowerNorms SchemeTensorPowerFrames SchemePulledPowerFrames
open CyclicSectionGlobalCoverRootSectionPowers
attribute [local instance] Scheme.Modules.monoidalCategory

private theorem power_unitEnd_sectionAtOne {Y : Scheme.{u}} (r : Γ(Y, ⊤)) :
    sectionAtOne (ModularCurves.unitEndomorphismOfTopSection r) = r := by
  change 1 * Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op r = r
  simp

/-- Native coefficient and pullback-power coherence compute the whole zero
ideal power on arbitrary schemes, without a regularity hypothesis. -/
private theorem rootZeroIdeal_power {Y : Scheme.{u}} (M : Y.Modules)
    (hM : IsInvertible M) (s : unitObj Y ⟶ M) (q : ℕ) :
    LineSectionZeroIdeal.zeroIdeal (bundleTensorPower M q)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM q)
        (powerSectionHom s q) =
      LineSectionZeroIdeal.zeroIdeal M hM s ^ q := by
  classical
  choose U hx eU using fun y : Y => exists_affine_frame M hM y
  have hcover : (⨆ y, (U y).1) = ⊤ := by
    apply top_le_iff.mp
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hx y⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hcover
  intro y
  let f := (U y).1.ι
  let e := (eU y).some
  let r : Γ((U y).1.toScheme, ⊤) :=
    sectionAtOne (pullbackSectionHom f s ≫ e.hom)
  have hr : pullbackSectionHom f s ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection r := unitHom_eq_globalScalar _
  let E := pullbackPowerFrame f e q
  have hpower : pullbackSectionHom f (powerSectionHom s q) ≫ E.hom =
      ModularCurves.unitEndomorphismOfTopSection (r ^ q) := by
    simp only [E, pullbackPowerFrame, Iso.trans_hom, ← Category.assoc]
    rw [pullback_powerSectionHom]
    exact powerSectionHom_frame (pullbackSectionHom f s) e r hr q
  rw [SchemeLineZeroIdealNativeFrameOrders.zeroIdeal_ideal_of_pullback_frame
      (bundleTensorPower M q) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM q)
      (powerSectionHom s q) (U y) E,
    Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    SchemeLineZeroIdealNativeFrameOrders.zeroIdeal_ideal_of_pullback_frame M hM s (U y) e,
    hpower, hr, power_unitEnd_sectionAtOne, power_unitEnd_sectionAtOne,
    Ideal.span_singleton_pow, map_pow]

variable {X : Scheme.{u}} [IsIntegral X]

/-- Every SAME actual normalized root zero ideal has exactly the power of
its SAME original branch section pulled to the WHOLE normalization. -/
theorem normalizedRootIdeal_power (D : List (AuxiliarySection X)) (a : Fin D.length)
    (hE : IsInvertible (D.get a).line) :
    normalizedRootIdeal D a hE ^ (D.get a).degree =
      (LineSectionZeroIdeal.zeroIdeal (bundleTensorPower (D.get a).line (D.get a).degree)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hE (D.get a).degree)
        (D.get a).sectionHom).comap (normalizedToOriginal D) := by
  unfold normalizedRootIdeal
  rw [← rootZeroIdeal_power, normalizedRoot_power]
  unfold normalizedSectionPower
  have hi := zeroIdeal_iso
    ((pullback (normalizedToOriginal D)).obj
      (bundleTensorPower (D.get a).line (D.get a).degree))
    (bundleTensorPower (normalizedLine D a) (D.get a).degree)
    ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hE (D.get a).degree).pullback
      (normalizedToOriginal D))
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible
      (hE.pullback (normalizedToOriginal D)) (D.get a).degree)
    (BundleTensorPowerPullback.pullbackIso (normalizedToOriginal D)
      (D.get a).line (D.get a).degree)
    (pullbackSectionHom (normalizedToOriginal D) (D.get a).sectionHom)
  exact hi.symm.trans (zeroIdeal_comap (normalizedToOriginal D)
    (bundleTensorPower (D.get a).line (D.get a).degree)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hE (D.get a).degree)
    (D.get a).sectionHom).symm

/-- The actual power of EVERY original row/copy root ideal retains its SAME
original divisor times its SAME original auxiliary section ideal. -/
theorem originalRowRootIdeal_power (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
    (i : F.ι) (j : Fin (n + 1)) :
    normalizedRootIdeal (OriginalData.data F n L m σ) (rowPosition F n L m σ i j)
        (OriginalData.get_isInvertible F n L m σ hL (rowPosition F n L m σ i j)) ^ m i =
      (F.component i * OriginalData.ideals F n L m σ hL hD i j).comap
        (normalizedToOriginal (OriginalData.data F n L m σ)) := by
  have hd : ((OriginalData.data F n L m σ).get (rowPosition F n L m σ i j)).degree = m i := by
    rw [OriginalData.get_degree, position_rowPosition]
  rw [← hd, normalizedRootIdeal_power]
  apply congrArg (fun I : X.IdealSheafData =>
    I.comap (normalizedToOriginal (OriginalData.data F n L m σ)))
  simpa only [position_rowPosition] using
    OriginalData.get_branch F n L m σ hL hD (rowPosition F n L m σ i j)

end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
