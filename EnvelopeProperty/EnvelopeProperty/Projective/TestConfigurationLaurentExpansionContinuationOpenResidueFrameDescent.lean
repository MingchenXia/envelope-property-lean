import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussPowerNativeWeights
import EnvelopeProperty.Berkovich.GeneratedLineGenericFrameNorms

/-! # Actual original open residue square, whole frame descent and genuine unit-section norm

The canonical original total-support residue morphism factors through a genuine
original open. Native open monomorphism and pullback coherence prove its complete
field/frame square; native model norms then use the SAME original inverse frame
unit section. No comparison or total-center-in-open assumption is accepted.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped NNReal Classical
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich SchemeLineSectionEvaluation Scheme.Modules SchemeLineSectionUnitFrames
open SchemeModuleFrameCoefficients

variable {K : Type u} [Field K] {Y : Scheme.{u}}
  (U : Y.Opens) (g : Spec (CommRingCat.of K) ⟶ U.toScheme)

/-- The ACTUAL original support lies in the genuine open, constructing its canonical residue factor. -/
def originalOpenFieldResidueFactor :
    Spec (CommRingCat.of (Y.residueField (Scheme.SpecToEquivOfField K Y (g ≫ U.ι)).1)) ⟶
      U.toScheme :=
  IsOpenImmersion.lift U.ι
    (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y (g ≫ U.ι)).1) (by
      rintro z ⟨s, rfl⟩
      refine ⟨g (IsLocalRing.closedPoint K), ?_⟩
      exact (Y.fromSpecResidueField_apply _ s).symm)

/-- The derived canonical original residue/open factor has the ENTIRE genuine scheme triangle. -/
theorem originalOpenFieldResidueFactor_comp :
    originalOpenFieldResidueFactor U g ≫ U.ι =
      Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y (g ≫ U.ι)).1 := by
  unfold originalOpenFieldResidueFactor
  apply IsOpenImmersion.lift_fac

/-- The actual field-point embedding and actual open residue factor recover the ENTIRE SAME g. -/
theorem originalOpenFieldResidueFactor_field :
    Spec.map (Scheme.SpecToEquivOfField K Y (g ≫ U.ι)).2 ≫
      originalOpenFieldResidueFactor U g = g := by
  apply (cancel_mono U.ι).1
  rw [Category.assoc, originalOpenFieldResidueFactor_comp]
  exact originalFieldResidueFactorization (g ≫ U.ι)

/-- An actual original open frame constructs the SAME original total-support residue-line frame. -/
def originalOpenFieldResidueFrame {M : Y.Modules}
    (a : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    (pullback (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y (g ≫ U.ι)).1)).obj M ≅
      unitObj (Spec (CommRingCat.of
        (Y.residueField (Scheme.SpecToEquivOfField K Y (g ≫ U.ι)).1))) :=
  frameViaFactor (originalOpenFieldResidueFactor U g) U.ι
    (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y (g ≫ U.ι)).1)
    (originalOpenFieldResidueFactor_comp U g) a

/-- The CONSTRUCTED actual residue frame descends the SAME direct field/open frame as a WHOLE iso. -/
theorem originalOpenFieldResidueFrame_field {M : Y.Modules}
    (a : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    originalFieldResidueLineFrame (g ≫ U.ι) (originalOpenFieldResidueFrame U g a) =
      frameViaFactor g U.ι (g ≫ U.ι) rfl a := by
  change frameViaFactor (Spec.map (Scheme.SpecToEquivOfField K Y (g ≫ U.ι)).2)
    (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y (g ≫ U.ι)).1)
    (g ≫ U.ι) (originalFieldResidueFactorization (g ≫ U.ι))
      (frameViaFactor (originalOpenFieldResidueFactor U g) U.ι
        (Y.fromSpecResidueField (Scheme.SpecToEquivOfField K Y (g ≫ U.ι)).1)
        (originalOpenFieldResidueFactor_comp U g) a) = _
  rw [frameViaFactor_comp]
  simp only [originalOpenFieldResidueFactor_field]

section ActualNorm
variable {R : Type u} [CommRing R] {vR : Valuation R ℝ≥0}
  (q : Y ⟶ Spec (CommRingCat.of R)) [IsProper q]
  (hb : ∀ r, vR r ≤ 1) (w : Valuation K ℝ≥0)
  (hbase : SchemeValuedPoint.map q (originalFieldValuedPoint (g ≫ U.ι) w) =
    SchemeValuedPoint.basePoint vR)
  {M : Y.Modules} (hM : IsInvertible M)
  (a : (pullback U.ι).obj M ≅ unitObj U.toScheme)

/-- The ACTUAL original generic inverse-unit norm is nonzero and computes EVERY original generic
section from its SAME genuine direct field/open-frame coefficient. The total center may be outside U. -/
theorem originalOpenFieldResidueFrame_modelNorm :
    let y : RelativeSchemeValuedPoint vR q := ⟨originalFieldValuedPoint (g ≫ U.ι) w, hbase⟩
    RelativeSchemeValuedPoint.modelLineNorm hb y hM
        (unitSection (originalOpenFieldResidueFrame U g a)) ≠ 0 ∧
      ∀ β : unitObj (Spec (CommRingCat.of (Y.residueField y.1.point))) ⟶
          RelativeSchemeValuedPoint.genericLineModule y M,
        RelativeSchemeValuedPoint.modelLineNorm hb y hM (sectionAtOne β) =
          w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom
            (frameScalar (frameViaFactor g U.ι (g ≫ U.ι) rfl a)
              (originalFieldResidueSectionHom (g ≫ U.ι) β))) *
            RelativeSchemeValuedPoint.modelLineNorm hb y hM
              (unitSection (originalOpenFieldResidueFrame U g a)) := by
  dsimp only
  let y : RelativeSchemeValuedPoint vR q := ⟨originalFieldValuedPoint (g ≫ U.ι) w, hbase⟩
  refine ⟨RelativeSchemeValuedPoint.modelLineNorm_genericFrameUnit_ne_zero hb y hM
    (originalOpenFieldResidueFrame U g a), fun β => ?_⟩
  have hc := originalFieldResidueSectionHom_value (g ≫ U.ι) w
    (originalOpenFieldResidueFrame U g a) β
  rw [originalOpenFieldResidueFrame_field] at hc
  rw [← originalFrameScalar_apply] at hc
  have hproject {B : Scheme.{u}} {N : B.Modules}
      (E : N ≅ unitObj B) (α : unitObj B ⟶ N) :
      coefficient E (sectionAtOne α) = frameScalar E α :=
    (originalFrameScalar_apply E α).symm
  have hn := RelativeSchemeValuedPoint.modelLineNorm_eq_genericFrameCoefficient_mul hb y hM
    (originalOpenFieldResidueFrame U g a) (sectionAtOne β)
  simp only [RelativeSchemeValuedPoint.genericFrameCoefficient, hproject] at hn
  exact hn.trans (congrArg (fun b : ℝ≥0 => b *
    RelativeSchemeValuedPoint.modelLineNorm hb y hM
      (unitSection (originalOpenFieldResidueFrame U g a))) hc.symm)

/-- EVERY SAME actual original whole Gamma section retains the ACTUAL native total-support norm
and the SAME original inverse-frame unit norm, with no supplied section or norm comparison. -/
theorem originalOpenFieldResidueFrame_whole_modelNorm (s : Γ(M, ⊤)) :
    let y : RelativeSchemeValuedPoint vR q := ⟨originalFieldValuedPoint (g ≫ U.ι) w, hbase⟩
    RelativeSchemeValuedPoint.modelLineNorm hb y hM
        (sectionAtOne (pullbackSectionHom (Y.fromSpecResidueField y.1.point) (topSectionHom M s))) =
      w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom
        (frameScalar (frameViaFactor g U.ι (g ≫ U.ι) rfl a)
          (pullbackSectionHom (g ≫ U.ι) (topSectionHom M s)))) *
        RelativeSchemeValuedPoint.modelLineNorm hb y hM
          (unitSection (originalOpenFieldResidueFrame U g a)) := by
  have h := (originalOpenFieldResidueFrame_modelNorm U g q hb w hbase hM a).2
    (pullbackSectionHom
      (Y.fromSpecResidueField (originalFieldValuedPoint (g ≫ U.ι) w).point) (topSectionHom M s))
  have hwhole := originalFieldResidueSectionHom_global (g ≫ U.ι) (topSectionHom M s)
  change originalFieldResidueSectionHom (g ≫ U.ι)
      (pullbackSectionHom
        (Y.fromSpecResidueField (originalFieldValuedPoint (g ≫ U.ι) w).point)
        (topSectionHom M s)) = pullbackSectionHom (g ≫ U.ι) (topSectionHom M s) at hwhole
  rw [hwhole] at h
  exact h
end ActualNorm

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
