import EnvelopeProperty.Vanishing.NadelNefBigGlobalPairClosed
import EnvelopeProperty.AlgGeom.CartierPullbackTensorCoherence
import EnvelopeProperty.Alterations.Geometry.ProjectiveSpaceBaseChange

/-! # The same original generated pair on an entire original affine base open

The source is the actual whole affine-base blowup, not a pivot source chart.
The target identification and its two readbacks are internally obtained from
the native Cartesian coefficient square. No monomorphism, comparison map or
generator-matching certificate is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
universe u

namespace EnvelopeProperty.Vanishing.NadelNefBigGlobalPairBaseOpen

open NadelNefBigGlobalPairClosed
open Alterations Alterations.Geometry.BlowupProjectiveEmbedding
open Alterations.Geometry.ProjectiveSpaceBaseChange

attribute [local instance] Scheme.Modules.monoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The original whole blowup chart is the actual base change over the
original spectrum-of-sections base open. -/
theorem source_isPullback (D : X.IdealSheafData) (U : X.affineOpens) :
    IsPullback (affineBlowUp.π (D.ideal U)) (Scheme.IdealSheafData.blowUp.ι D U)
      U.2.fromSpec D.blowUpπ := by
  apply (Scheme.IdealSheafData.blowUp.isPullback_ι D U).of_iso
    (Iso.refl _) U.2.isoSpec (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simpa only [Iso.refl_hom, Category.comp_id] using U.2.isoSpec_hom_fromSpec.symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The actual target base change of the original product, on the entire
original affine base open. -/
abbrev baseTarget (p : X ⟶ Spec (.of k)) (m : ℕ) (U : X.affineOpens) : Scheme :=
  Limits.pullback (Limits.pullback.fst p (projectiveSpaceStructure k m)) U.2.fromSpec

/-- The genuine original coefficient morphism makes this whole target chart
a Cartesian projective coefficient square. -/
theorem baseTarget_isPullback (p : X ⟶ Spec (.of k)) (m : ℕ) (U : X.affineOpens) :
    IsPullback
      (Limits.pullback.fst (Limits.pullback.fst p (projectiveSpaceStructure k m))
        U.2.fromSpec ≫ Limits.pullback.snd p (projectiveSpaceStructure k m))
      (Limits.pullback.snd (Limits.pullback.fst p (projectiveSpaceStructure k m)) U.2.fromSpec)
      (projectiveSpaceStructure k m)
      (Spec.map (CommRingCat.ofHom (affineBaseCoefficients p U))) := by
  have H := (IsPullback.of_hasPullback
    (Limits.pullback.fst p (projectiveSpaceStructure k m)) U.2.fromSpec).paste_horiz
      (IsPullback.of_hasPullback p (projectiveSpaceStructure k m)).flip
  rw [affineBaseCoefficients_structure]
  exact H

/-- Internally produced identification with projective space over the SAME
original affine section ring. -/
def baseTargetProjectiveIso (p : X ⟶ Spec (.of k)) (m : ℕ) (U : X.affineOpens) :
    baseTarget p m U ≅ projectiveSpace Γ(X, U.1) m :=
  (baseTarget_isPullback p m U).isoIsPullback _ _
    (isPullback_projectiveCoefficientMap (affineBaseCoefficients p U) m)

/-- The whole target isomorphism preserves the original coefficient map. -/
theorem baseTargetProjectiveIso_hom_coeff
    (p : X ⟶ Spec (.of k)) (m : ℕ) (U : X.affineOpens) :
    (baseTargetProjectiveIso p m U).hom ≫
        projectiveCoefficientMap (affineBaseCoefficients p U) m =
      Limits.pullback.fst (Limits.pullback.fst p (projectiveSpaceStructure k m)) U.2.fromSpec ≫
        Limits.pullback.snd p (projectiveSpaceStructure k m) :=
  (baseTarget_isPullback p m U).isoIsPullback_hom_fst _ _ _

/-- The whole target isomorphism preserves the original affine structure map. -/
theorem baseTargetProjectiveIso_hom_structure
    (p : X ⟶ Spec (.of k)) (m : ℕ) (U : X.affineOpens) :
    (baseTargetProjectiveIso p m U).hom ≫ projectiveSpaceStructure Γ(X, U.1) m =
      Limits.pullback.snd (Limits.pullback.fst p (projectiveSpaceStructure k m)) U.2.fromSpec :=
  (baseTarget_isPullback p m U).isoIsPullback_hom_snd _ _ _

variable (D : X.IdealSheafData) (p : X ⟶ Spec (.of k))
  (B : X.Modules) (hB : IsInvertible B)
  (G : (D.toModules ⊗ B).GeneratingSections) [Fintype G.I]

/-- The SAME global pair restricted to the entire original affine base
blowup, constructed through the actual target pullback. -/
def basePair (U : X.affineOpens) :
    affineBlowUp (D.ideal U) ⟶ baseTarget p (Fintype.card G.I) U :=
  Limits.pullback.lift
    (Scheme.IdealSheafData.blowUp.ι D U ≫ globalPair D p B hB G)
    (affineBlowUp.π (D.ideal U)) (by
      rw [Category.assoc, globalPair_fst]
      exact (source_isPullback D U).w.symm)

/-- Its first projection is the original global pair composed with the
original whole affine blowup inclusion. -/
theorem basePair_fst (U : X.affineOpens) :
    basePair D p B hB G U ≫ Limits.pullback.fst _ _ =
      Scheme.IdealSheafData.blowUp.ι D U ≫ globalPair D p B hB G :=
  Limits.pullback.lift_fst _ _ _

/-- Its second projection is the SAME original local blowup projection. -/
theorem basePair_snd (U : X.affineOpens) :
    basePair D p B hB G U ≫ Limits.pullback.snd _ _ = affineBlowUp.π (D.ideal U) :=
  Limits.pullback.lift_snd _ _ _

/-- This is the actual whole target-base change of the SAME global pair. -/
theorem basePair_isPullback (U : X.affineOpens) :
    IsPullback (basePair D p B hB G U) (Scheme.IdealSheafData.blowUp.ι D U)
      (Limits.pullback.fst (Limits.pullback.fst p
        (projectiveSpaceStructure k (Fintype.card G.I))) U.2.fromSpec)
      (globalPair D p B hB G) := by
  have H : IsPullback
      (basePair D p B hB G U ≫ Limits.pullback.snd
        (Limits.pullback.fst p (projectiveSpaceStructure k (Fintype.card G.I))) U.2.fromSpec)
      (Scheme.IdealSheafData.blowUp.ι D U) U.2.fromSpec
      (globalPair D p B hB G ≫ Limits.pullback.fst p
        (projectiveSpaceStructure k (Fintype.card G.I))) := by
    simpa only [basePair_snd, globalPair_fst] using source_isPullback D U
  exact H.of_right (basePair_fst D p B hB G U)
    (IsPullback.of_hasPullback (Limits.pullback.fst p
      (projectiveSpaceStructure k (Fintype.card G.I))) U.2.fromSpec).flip

/-- The SAME restricted pair, in its internally constructed projective
target over the original affine base. -/
def baseProjectivePair (U : X.affineOpens) :
    affineBlowUp (D.ideal U) ⟶ projectiveSpace Γ(X, U.1) (Fintype.card G.I) :=
  basePair D p B hB G U ≫ (baseTargetProjectiveIso p (Fintype.card G.I) U).hom

/-- Its original coefficient image is the SAME original global generated map. -/
theorem baseProjectivePair_coeff (U : X.affineOpens) :
    baseProjectivePair D p B hB G U ≫
        projectiveCoefficientMap (affineBaseCoefficients p U) (Fintype.card G.I) =
      Scheme.IdealSheafData.blowUp.ι D U ≫ globalMap D p B hB G := by
  rw [baseProjectivePair, Category.assoc, baseTargetProjectiveIso_hom_coeff,
    ← Category.assoc, basePair_fst, Category.assoc, globalPair_snd]

/-- Its original coefficient-base structure is the SAME local projection. -/
theorem baseProjectivePair_structure (U : X.affineOpens) :
    baseProjectivePair D p B hB G U ≫
        projectiveSpaceStructure Γ(X, U.1) (Fintype.card G.I) =
      affineBlowUp.π (D.ideal U) := by
  rw [baseProjectivePair, Category.assoc, baseTargetProjectiveIso_hom_structure, basePair_snd]

end EnvelopeProperty.Vanishing.NadelNefBigGlobalPairBaseOpen
