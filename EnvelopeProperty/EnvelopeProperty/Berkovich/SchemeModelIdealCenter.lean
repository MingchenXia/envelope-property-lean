/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeModelIdeals
import EnvelopeProperty.Berkovich.SchemeIdealPullback

/-! # Intrinsic ideal norms on the whole actual proper valuative pullback -/

open scoped NNReal ENNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- The original residue valuation on the ENTIRE global-section ring of
its actual original valuation-ring spectrum. -/
def centerTopSpectrum (y : RelativeSchemeValuedPoint v f) :
    Spectrum Γ(Spec (CommRingCat.of (CenterRing y)), ⊤) :=
  Spectrum.ofValuation (y.1.residueVal.comap
    ((algebraMap (CenterRing y) (X.residueField y.1.point)).comp
      (Scheme.ΓSpecIso (CommRingCat.of (CenterRing y))).hom.hom))

/-- Every ACTUAL original center-ring global section has value at most one. -/
theorem isBounded_centerTopSpectrum (y : RelativeSchemeValuedPoint v f) :
    Spectrum.IsBounded (centerTopSpectrum y) := by
  intro s
  exact (Valuation.valuationSubring.integers y.1.residueVal).map_le_one _

/-- Pullback by the ACTUAL proper valuative lift agrees on the WHOLE
original section spectrum with the original native residue evaluation. -/
theorem centerTopSpectrum_comap_centerLift [IsProper f] (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (U : X.Opens) (hc : center hb y ∈ U) :
    Spectrum.comap ((centerLift hb y).appLE U ⊤ (by
      rw [Scheme.preimage_eq_top_of_closedPoint_mem (centerLift hb y) hc])).hom
      (centerTopSpectrum y) =
    (sectionSpectrum y U (support_mem_of_center_mem hb y U hc)).1 := by
  apply Spectrum.ext_val
  intro s
  exact congrArg y.1.residueVal (centerSectionMap_coe hb y U hc s)

/-- The intrinsic original model ideal norm is the norm of the ENTIRE
actual geometric ideal pulled back to the original proper valuation center. -/
theorem modelIdealNorm_eq_centerPullback [IsProper f] (I : X.IdealSheafData)
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    modelIdealNorm I hb y =
      Spectrum.idealNorm ((I.comap (centerLift hb y)).ideal
        ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of (CenterRing y)))⟩)
        (centerTopSpectrum y) := by
  obtain ⟨W, hW, hc, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := center hb y) trivial
  let U : X.affineOpens := ⟨W, hW⟩
  have hp : (⊤ : (Spec (CommRingCat.of (CenterRing y))).Opens) ≤
      centerLift hb y ⁻¹ᵁ U.1 := by
    rw [Scheme.preimage_eq_top_of_closedPoint_mem (centerLift hb y) hc]
  rw [I.comap_ideal_of_affine_opens (centerLift hb y)
    ⟨⊤, isAffineOpen_top _⟩ U hp,
    Spectrum.idealNorm_map _ _ (isBounded_centerTopSpectrum y),
    centerTopSpectrum_comap_centerLift hb y U.1 hc]
  exact modelIdealNorm_eq_affine I hb y U hc

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
