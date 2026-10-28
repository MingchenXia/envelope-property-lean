import EnvelopeProperty.Local.PLProductPointRestriction
import EnvelopeProperty.Projective.NativeCoefficientNaturality
import EnvelopeProperty.AlgGeom.NativeProjectiveVarietyAnalytic

/-! # Literal original product projection is the whole original analytic restriction -/
open scoped Classical Polynomial NNReal ENNReal Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The literal canonical projection from the ORIGINAL variety product to
the SAME original native variety, through the actual ideal-comap pullback. -/
def nativeProductOriginalProjection : X.NativeProductModel ⟶ X.NativeScheme :=
  (X.nativeIdeal.comapIso _).hom ≫ pullback.snd _ _

/-- The literal original projection commutes with the SAME original ambient
closed inclusion as an equality of WHOLE genuine scheme morphisms. -/
theorem nativeProductOriginalProjection_inclusion :
    X.nativeProductOriginalProjection ≫ X.nativeInclusion =
      X.nativeProductInclusion ≫ pullback.fst (nativeStructureMap (R := k) (n := M))
        (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) := by
  dsimp only [nativeProductOriginalProjection, nativeInclusion]
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]
  rfl

/-- Actual original variety projection preserves the WHOLE original base
square over the literal original coefficient inclusion k→k[t]. -/
theorem nativeProductOriginalProjection_over_base :
    X.nativeProductOriginalProjection ≫ X.nativeStructure =
      X.nativeProductStructure ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) := by
  change (X.nativeProductOriginalProjection ≫ X.nativeInclusion) ≫ nativeStructureMap = _
  rw [X.nativeProductOriginalProjection_inclusion, Category.assoc, pullback.condition]
  rfl

/-- The derived original analytic restriction of EVERY genuine product point
is EXACTLY its literal original scheme projection, as a WHOLE prescribed-base
native point, retaining the actual original residue valuation. -/
theorem nativeAnalyticHomeomorph_nativeProductBaseRestriction
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      X.nativeProductStructure) :
    X.nativeAnalyticHomeomorph (X.nativeProductBaseRestriction y) =
      RelativeSchemeValuedPoint.mapOverBase Polynomial.C
        (fun a => Spectrum.gauss_val_C (Spectrum.ofValuation (1 : Valuation k ℝ≥0)) gaussRadius a)
        X.nativeProductOriginalProjection (X.nativeProductOriginalProjection_over_base) y := by
  apply Subtype.ext
  apply SchemeValuedPoint.map_injective_of_isClosedImmersion X.nativeInclusion
  have hinc := congrArg Subtype.val
    (X.nativeAnalyticHomeomorph_inclusion (X.nativeProductBaseRestriction y))
  change SchemeValuedPoint.map X.nativeInclusion _ = _ at hinc
  rw [hinc]
  have hcoef := congrArg Subtype.val
    (RelativeNormalizedProjectiveSpectrum.nativeHomeomorph_polynomialRestriction
      (1 : Valuation k ℝ≥0) gaussRadius (X.nativeProductNormalizedPoint y))
  have hfst := nativePolynomialLineProductPoint_fst (X.nativeProductNormalizedPoint y)
  rw [X.nativePolynomialLineProductPoint_nativeProductNormalizedPoint] at hfst
  have hw : normalizedSpectrumHomeomorph (X.nativeProductBaseRestriction y).1 =
      RelativeNormalizedProjectiveSpectrum.polynomialRestriction
        (1 : Valuation k ℝ≥0) gaussRadius (X.nativeProductNormalizedPoint y) :=
    normalizedSpectrumHomeomorph.apply_symm_apply _
  change (ProjBerk.nativeHomeomorph (X.nativeProductBaseRestriction y).1).1 = _
  change (RelativeNormalizedProjectiveSpectrum.nativeHomeomorph (1 : Valuation k ℝ≥0)
    (normalizedSpectrumHomeomorph (X.nativeProductBaseRestriction y).1)).1 = _
  rw [hw,hcoef]
  change SchemeValuedPoint.map (nativeCoefficientMap Polynomial.C) _ =
    SchemeValuedPoint.map X.nativeInclusion (SchemeValuedPoint.map X.nativeProductOriginalProjection y.1)
  rw [← SchemeValuedPoint.map_comp, X.nativeProductOriginalProjection_inclusion,
    SchemeValuedPoint.map_comp]
  exact hfst.symm
end EnvelopeProperty.ProjSubvariety
