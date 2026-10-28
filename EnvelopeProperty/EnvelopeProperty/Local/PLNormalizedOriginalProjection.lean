import EnvelopeProperty.Local.PLProductNativeProjection
import EnvelopeProperty.Local.PLNormalizedFullPointRatioMetric
import EnvelopeProperty.Local.PLIdealNormalizedPolarization

/-! # Literal normalized-model projection retains the whole original point -/
open scoped Classical Polynomial NNReal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk
variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  RelativeSchemeValuedPoint.modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)

/-- The SAME already constructed polarized-model projection is literally
normalization, simultaneous blowup, then the original product projection. -/
theorem normalizedSimultaneousOriginalProjection_eq :
    X.normalizedSimultaneousOriginalProjection I J hfin =
      X.normalizedSimultaneousIdealBlowupProjection I J hfin ≫
        X.simultaneousIdealBlowupProjection I J ≫ X.nativeProductOriginalProjection := by
  dsimp only [normalizedSimultaneousOriginalProjection,simultaneousOriginalProjection,
    nativeProductModelIso,Iso.trans_hom,nativeStructure,nativeProductOriginalProjection,nativeInclusion]
  simp only [Category.assoc,pullbackRightPullbackFstIso_hom_fst]
  erw [pullbackSymmetry_hom_comp_fst]

/-- The actual whole original normalized-model projection retains the literal
original coefficient-base square k→k[t]. -/
theorem normalizedSimultaneousOriginalProjection_over_base :
    X.normalizedSimultaneousOriginalProjection I J hfin ≫ X.nativeStructure =
      X.normalizedSimultaneousIdealBlowupStructure I J hfin ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) := by
  rw [X.normalizedSimultaneousOriginalProjection_eq I J hfin]
  dsimp only [normalizedSimultaneousIdealBlowupStructure,simultaneousIdealBlowupStructure]
  simp only [Category.assoc,X.nativeProductOriginalProjection_over_base]

/-- At EVERY actual normalized-model point, the derived original analytic
restriction is EXACTLY the whole literal scheme projection, including its
original residue-field valuation. -/
theorem nativeAnalyticHomeomorph_normalizedSimultaneousBaseRestrictionAt
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : _root_.Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin)) :
    X.nativeAnalyticHomeomorph (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) =
      RelativeSchemeValuedPoint.mapOverBase Polynomial.C
        (fun c => Spectrum.gauss_val_C (Spectrum.ofValuation (1 : _root_.Valuation k ℝ≥0)) gaussRadius c)
        (X.normalizedSimultaneousOriginalProjection I J hfin)
        (X.normalizedSimultaneousOriginalProjection_over_base I J hfin) y := by
  rw [normalizedSimultaneousBaseRestrictionAt,X.nativeAnalyticHomeomorph_nativeProductBaseRestriction]
  apply Subtype.ext
  change SchemeValuedPoint.map X.nativeProductOriginalProjection
    (SchemeValuedPoint.map (X.simultaneousIdealBlowupProjection I J)
      (SchemeValuedPoint.map (X.normalizedSimultaneousIdealBlowupProjection I J hfin) y.1)) = _
  rw [← SchemeValuedPoint.map_comp,← SchemeValuedPoint.map_comp]
  change SchemeValuedPoint.map
    (X.normalizedSimultaneousIdealBlowupProjection I J hfin ≫
      X.simultaneousIdealBlowupProjection I J ≫ X.nativeProductOriginalProjection) y.1 =
    SchemeValuedPoint.map (X.normalizedSimultaneousOriginalProjection I J hfin) y.1
  rw [X.normalizedSimultaneousOriginalProjection_eq I J hfin]

end EnvelopeProperty.ProjSubvariety
