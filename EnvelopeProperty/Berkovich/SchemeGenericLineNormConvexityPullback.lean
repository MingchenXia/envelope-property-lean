import EnvelopeProperty.Berkovich.SchemeGenericLineNormPullback
import EnvelopeProperty.Berkovich.SchemeConvexPLAlgebra

/-! # True intrinsic convexity of actual generic-section model weights under pullback -/
open scoped NNReal ENNReal
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R S : Type u} [CommRing R] [CommRing S]
variable {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}
variable {X Y : Scheme.{u}}
variable {fX : X ⟶ Spec (CommRingCat.of S)} {fY : Y ⟶ Spec (CommRingCat.of R)}
variable [IsProper fX] [IsProper fY]

/-- Every TRUE intrinsic convex model norm weight of an arbitrary original
family of generic-fibre sections pulls back to the TRUE norm weight of their
actual native residue-field pullbacks. No global section extension or metric
preservation premise is supplied. -/
theorem IsConvexPLOn.pullback_genericSectionWeight
    (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r) (g : X ⟶ Y)
    (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (hbR : ∀ r, v r ≤ 1) (hbS : ∀ s, w s ≤ 1)
    {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
    (σ : ∀ z : RelativeSchemeValuedPoint v fY, Γ(genericLineModule z M, ⊤))
    {U : Set (RelativeSchemeValuedPoint v fY)}
    (hu : IsConvexPLOn U (fun z => -ENNReal.log (modelLineNorm hbR z hM (σ z) : ℝ≥0∞))) :
    IsConvexPLOn (mapOverBase φ hφ g hg ⁻¹' U)
      (fun y => -ENNReal.log (modelLineNorm hbS y (hM.pullback g)
        (SchemeValuedPoint.pullbackResidueSection g y.1.point (σ (mapOverBase φ hφ g hg y))) : ℝ≥0∞)) := by
  apply (hu.comp_mapOverBase φ hφ g hg).congr
  intro y _
  exact congrArg (fun t : ℝ≥0 => -ENNReal.log (t : ℝ≥0∞))
    (modelLineNorm_pullbackResidueSection_eq_overBase φ hφ g hg hbR hbS y hM
      (σ (mapOverBase φ hφ g hg y))).symm

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
