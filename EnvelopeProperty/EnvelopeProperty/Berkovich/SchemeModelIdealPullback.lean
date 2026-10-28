/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeIdealPullback
import EnvelopeProperty.Berkovich.SchemeModelIdeals
import EnvelopeProperty.Berkovich.SchemeCenterFunctor
import EnvelopeProperty.Berkovich.SchemeRelativeAtlas

/-!
# Genuine model ideal function pullback consistency

Whole native section-spectrum naturality, actual proper-center functoriality
and the derived geometric ideal-image formula prove intrinsic model norm
and logarithm pullback consistency. Prescribed coefficient boundedness and
both proper structure morphisms are explicit; finite generation, flatness,
Noetherianity and birationality are unnecessary.
-/


open scoped NNReal ENNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X Y : Scheme.{u}}
variable {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}

/-- The entire native section-spectrum pullback is the genuine local section homomorphism. -/
theorem sectionSpectrum_comap_appLE (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (y : RelativeSchemeValuedPoint v fX) (U : X.Opens) (V : Y.Opens)
    (h : U ≤ g ⁻¹ᵁ V) (hy : y.1.point ∈ U) :
    Spectrum.comap (g.appLE V U h).hom (sectionSpectrum y U hy).1 =
      (sectionSpectrum (map g hg y) V (h hy)).1 := by
  apply Spectrum.ext_val
  intro s
  change SchemeValuedPoint.eval y.1 U hy (g.appLE V U h s) =
    SchemeValuedPoint.eval (SchemeValuedPoint.map g y.1) V (h hy) s
  rw [SchemeValuedPoint.eval_map]
  simpa only [Scheme.Hom.appLE, CommRingCat.comp_apply] using
    SchemeValuedPoint.eval_restrict y.1 (g ⁻¹ᵁ V) U h hy (g.app V s)

/-- The actual geometric ideal pullback preserves intrinsic model norms under every commuting morphism of proper models. -/
theorem modelIdealNorm_comap [IsProper fX] [IsProper fY] (I : Y.IdealSheafData)
    (g : X ⟶ Y) (hg : g ≫ fY = fX) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v fX) :
    modelIdealNorm (I.comap g) hb y = modelIdealNorm I hb (map g hg y) := by
  obtain ⟨V, hV, hcV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (U := ⊤) (x := center hb (map g hg y)) trivial
  have hcXV : center hb y ∈ g ⁻¹ᵁ V := by
    change g (center hb y) ∈ V
    rw [center_map g hg hb y]
    exact hcV
  obtain ⟨U, hU, hcU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := g ⁻¹ᵁ V) (x := center hb y) hcXV
  let U' : X.affineOpens := ⟨U, hU⟩
  let V' : Y.affineOpens := ⟨V, hV⟩
  rw [modelIdealNorm_eq_affine (I.comap g) hb y U' hcU,
    I.comap_ideal_of_affine_opens g U' V' hUV,
    Spectrum.idealNorm_map _ _ (isBounded_sectionSpectrum_of_center_mem hb y U hcU),
    sectionSpectrum_comap_appLE g hg y U V hUV,
    ← modelIdealNorm_eq_affine I hb (map g hg y) V' hcV]

/-- Genuine logarithmic model ideal functions commute with actual proper-model pullback, including zero and negative infinity. -/
theorem modelIdealLog_comap [IsProper fX] [IsProper fY] (I : Y.IdealSheafData)
    (g : X ⟶ Y) (hg : g ≫ fY = fX) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v fX) :
    modelIdealLog (I.comap g) hb y = modelIdealLog I hb (map g hg y) :=
  congrArg ENNReal.log (modelIdealNorm_comap I g hg hb y)
end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
