import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsRatio
import EnvelopeProperty.Vanishing.NadelBertiniFibreIdeals

/-! # The actual entire normalized row ideal uses every original root section

The ideal is literally the sum of ALL original normalized root zero ideals.
Its actual factor/pullback identity is proved through native module coherence;
no Cartier property or desired ideal power identity is a definition or premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open SchemeLineSectionEvaluation NadelBertiniFibreIdeals

/-- Actual zero ideals retain the original root through the original factor
triangle, including the native pullback/module-composition coherence. -/
theorem transportedRoot_zeroIdeal {X T : Scheme.{u}} (E : AuxiliarySection X)
    (hE : IsInvertible E.line) (t : T ⟶ factorCover E) (π : T ⟶ X)
    (ht : t ≫ factorProjection E = π) :
    LineSectionZeroIdeal.zeroIdeal ((pullback π).obj E.line) (hE.pullback π)
      (transportedRoot E t π ht) =
      (LineSectionZeroIdeal.zeroIdeal ((pullback (factorProjection E)).obj E.line)
        (hE.pullback (factorProjection E))
        (CyclicSectionGlobalCoverRootSection.tautologicalRoot E.line E.degree E.sectionHom)).comap t := by
  let τ := CyclicSectionGlobalCoverRootSection.tautologicalRoot E.line E.degree E.sectionHom
  have hp := zeroIdeal_comap t ((pullback (factorProjection E)).obj E.line)
    (hE.pullback (factorProjection E)) τ
  have hi := zeroIdeal_iso ((pullback t).obj ((pullback (factorProjection E)).obj E.line))
    ((pullback π).obj E.line) ((hE.pullback (factorProjection E)).pullback t) (hE.pullback π)
    (frameFactorIso t (factorProjection E) π ht E.line) (pullbackSectionHom t τ)
  exact (hp.trans hi).symm

variable {X : Scheme.{u}} [IsIntegral X]

/-- The literal zero ideal of the SAME original normalized root section. -/
def normalizedRootIdeal (D : List (AuxiliarySection X)) (i : Fin D.length)
    (hE : IsInvertible (D.get i).line) : (normalizedScheme D).IdealSheafData :=
  LineSectionZeroIdeal.zeroIdeal (normalizedLine D i) (hE.pullback (normalizedToOriginal D))
    (normalizedRoot D i)

/-- Every actual normalized root ideal is the original factor root ideal
pulled through its SAME actual normalized factor map. -/
theorem normalizedRootIdeal_factor (D : List (AuxiliarySection X)) (i : Fin D.length)
    (hE : IsInvertible (D.get i).line) :
    normalizedRootIdeal D i hE =
      (LineSectionZeroIdeal.zeroIdeal ((pullback (factorProjection (D.get i))).obj (D.get i).line)
        (hE.pullback (factorProjection (D.get i)))
        (CyclicSectionGlobalCoverRootSection.tautologicalRoot
          (D.get i).line (D.get i).degree (D.get i).sectionHom)).comap (normalizedFactorMap D i) :=
  transportedRoot_zeroIdeal (D.get i) hE (normalizedFactorMap D i)
    (normalizedToOriginal D) (normalizedFactorMap_over D i)

/-- The actual global J_i is the sum of ALL SAME original normalized row-root
zero ideals, with every original copy retained. No Cartier or power conclusion
is inserted as a structure field or hypothesis. -/
def wholeRowIdeal (F : X.DivisorFamily) (n : ℕ) (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (i : F.ι) :
    (normalizedScheme (OriginalData.data F n L m σ)).IdealSheafData :=
  ⨆ j, normalizedRootIdeal (OriginalData.data F n L m σ) (rowPosition F n L m σ i j)
    (OriginalData.get_isInvertible F n L m σ hL (rowPosition F n L m σ i j))

end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
