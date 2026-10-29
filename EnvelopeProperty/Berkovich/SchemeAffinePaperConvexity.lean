import EnvelopeProperty.Berkovich.SchemeAffineLocalPSH
import EnvelopeProperty.Berkovich.PaperLocalPSH

/-! # Genuine affine native regular-unit convexity and the original paper class -/
open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Classical
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- The actual original affine native-point space is the original trivial-field
Berkovich space, retaining the whole point and every original ring value. -/
def affineBerkHomeomorph :
    RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0)
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) ≃ₜ Berk k A :=
  affineSpectrumHomeomorph.trans Berk.relativeSpectrumHomeomorph.symm

/-- Its inverse is the canonical actual affine native point of the SAME original seminorm. -/
theorem affineBerkHomeomorph_symm_coe (z : Berk k A) :
    (affineBerkHomeomorph.symm z).1 =
      SchemeValuedPoint.spectrumHomeomorph.symm (Berk.toSpectrum z) := rfl

/-- Original finite-coefficient convexity yields actual native regular-unit
presentations on the same whole original affine locus. -/
theorem IsConvexPLOn.of_paperAffine {U : Set (Berk k A)} {u : Berk k A → EReal}
    (hu : EnvelopeProperty.IsConvexPLOn U u) :
    IsConvexPLOn (affineBerkHomeomorph ⁻¹' U) (fun y => u (affineBerkHomeomorph y)) := by
  have hr : RelativeSpectrum.IsConvexPLOn
      (Berk.relativeSpectrumHomeomorph.symm ⁻¹' U)
      (fun y => u (Berk.relativeSpectrumHomeomorph.symm y)) := by
    apply EnvelopeProperty.isConvexPLOn_relativeSpectrum_iff.mpr
    simpa only [Set.preimage_preimage, Function.comp_def,
      Homeomorph.symm_apply_apply, Set.preimage_id'] using hu
  exact IsConvexPLOn.of_affineSpectrum hr

/-- Every actual original affine native regular-unit presentation is an original
finite-coefficient convex presentation, including its whole analytic neighborhood. -/
theorem IsConvexPLOn.to_paperAffine
    {U : Set (RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0)
      (Spec.map (CommRingCat.ofHom (algebraMap k A))))}
    {u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0)
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) → EReal}
    (hu : IsConvexPLOn U u) :
    EnvelopeProperty.IsConvexPLOn (affineBerkHomeomorph.symm ⁻¹' U)
      (fun y => u (affineBerkHomeomorph.symm y)) := by
  exact EnvelopeProperty.isConvexPLOn_relativeSpectrum_iff.mp hu.to_affineSpectrum

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
