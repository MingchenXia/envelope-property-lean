import EnvelopeProperty.Local.PLNormalizedFullPointRatioMetric
import EnvelopeProperty.Local.PLIdealNormalizedPolarizedMetric

/-! # True original polarized section weights on the WHOLE normal model -/
open scoped Classical Polynomial NNReal ENNReal
open CategoryTheory AlgebraicGeometry Opposite
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich.RelativeSchemeValuedPoint
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
private local instance normalizedProper :
    IsProper (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
  X.normalizedSimultaneousIdealBlowupStructure_isProper I J hfin
private local instance polynomialProper :
    IsProper (nativeStructureMap (R := k[X]) (n := M)) := nativeStructureMap_isProper

/-- The actual polynomial projection of EVERY original normal-model point
is the WHOLE normalized polynomial point of its SAME projected product point. -/
theorem map_normalizedSimultaneousPolynomialProjection_at
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin)) :
    RelativeSchemeValuedPoint.map (X.normalizedSimultaneousPolynomialProjection I J hfin)
      (X.normalizedSimultaneousPolynomialProjection_over_base I J hfin) y =
    RelativeNormalizedProjectiveSpectrum.nativeHomeomorph _
      (X.nativeProductNormalizedPoint (X.normalizedSimultaneousProductPointAt I J hfin y)) := by
  dsimp only [nativeProductNormalizedPoint]
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  change SchemeValuedPoint.map _ _ = _
  dsimp only [normalizedSimultaneousPolynomialProjection, nativeProductPolynomialInclusion,
    normalizedSimultaneousProductPointAt]
  simp only [SchemeValuedPoint.map_comp]
  rfl

/-- TRUE norm of the actual original pulled homogeneous section at ANY
original normalized-model point, on the SAME original polynomial O(d). -/
def normalizedSimultaneousHomogeneousSectionNormAt
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin))
    (j : Fin (M+1)) (d : ℕ) (F : MvPolynomial (Fin (M+1)) k) (hF : F.IsHomogeneous d) : ℝ≥0 :=
  modelLineNorm gaussModelCoefficient_le_one y
    ((MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible (R := k[X]) j d).pullback
      (X.normalizedSimultaneousPolynomialProjection I J hfin))
    (fibreSection y (SchemeLineSectionEvaluation.pullbackSectionHom
      (X.normalizedSimultaneousPolynomialProjection I J hfin)
      (ProjectiveHomogeneousSections.sectionHom j d (MvPolynomial.map Polynomial.C F)
        (hF.map Polynomial.C))))

/-- The ACTUAL whole-point section norm is the SAME full original form value
at the derived ORIGINAL analytic restriction, including vanishing forms. -/
theorem normalizedSimultaneousHomogeneousSectionNormAt_eq_val
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin))
    (j : Fin (M+1)) (d : ℕ) (F : MvPolynomial (Fin (M+1)) k) (hF : F.IsHomogeneous d) :
    X.normalizedSimultaneousHomogeneousSectionNormAt I J hfin y j d F hF =
      (X.normalizedSimultaneousBaseRestrictionAt I J hfin y).1.1.val F := by
  let g := X.normalizedSimultaneousPolynomialProjection I J hfin
  have hg := X.normalizedSimultaneousPolynomialProjection_over_base I J hfin
  have h := modelLineNorm_pullbackSection_eq_overBase (RingHom.id k[X]) (fun _ => rfl) g
    (by simpa only [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id] using hg)
    gaussModelCoefficient_le_one gaussModelCoefficient_le_one y
    (MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible (R := k[X]) j d)
    (ProjectiveHomogeneousSections.sectionHom j d (MvPolynomial.map Polynomial.C F)
      (hF.map Polynomial.C))
  rw [mapOverBase_id g hg, X.map_normalizedSimultaneousPolynomialProjection_at I J hfin y] at h
  change X.normalizedSimultaneousHomogeneousSectionNormAt I J hfin y j d F hF = _ at h
  rw [RelativeNormalizedProjectiveSpectrum.homogeneousSection_modelLineNorm] at h
  exact h.trans (X.nativeProductBaseRestriction_val
    (X.normalizedSimultaneousProductPointAt I J hfin y) F).symm

/-- Actual generic pure tensor of the SAME original homogeneous section and
SAME actual canonical ratio section, at EVERY admissible normal-model point. -/
def normalizedSimultaneousPolynomialRatioSectionAt
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin))
    (hnI : modelIdealLog I gaussModelCoefficient_le_one
      (X.normalizedSimultaneousProductPointAt I J hfin y) ≠ ⊥)
    (j : Fin (M+1)) (d : ℕ) (F : MvPolynomial (Fin (M+1)) k) (hF : F.IsHomogeneous d) :
    Γ(genericLineModule y (X.normalizedSimultaneousPolynomialRatioLine I J hfin j d), ⊤) :=
  genericTensorSection y
    (fibreSection y (SchemeLineSectionEvaluation.pullbackSectionHom
      (X.normalizedSimultaneousPolynomialProjection I J hfin)
      (ProjectiveHomogeneousSections.sectionHom j d (MvPolynomial.map Polynomial.C F)
        (hF.map Polynomial.C))))
    (X.normalizedSimultaneousRatioSectionAt I J hfin y hnI)

/-- TRUE actual weight of the SAME original polarized tensor section at an
arbitrary actual normal-model point, with no metric identity supplied. -/
def normalizedSimultaneousPolynomialRatioWeightAt
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin))
    (hnI : modelIdealLog I gaussModelCoefficient_le_one
      (X.normalizedSimultaneousProductPointAt I J hfin y) ≠ ⊥)
    (j : Fin (M+1)) (d : ℕ) (F : MvPolynomial (Fin (M+1)) k) (hF : F.IsHomogeneous d) : EReal :=
  -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y
    (X.normalizedSimultaneousPolynomialRatioLine_isInvertible I J hfin j d)
    (X.normalizedSimultaneousPolynomialRatioSectionAt I J hfin y hnI j d F hF) : ℝ≥0∞)

/-- At EVERY genuine actual model point, the SAME true polarized weight is
EXACTLY the original ratio weight minus the ORIGINAL homogeneous logAbs of
its SAME derived analytic restriction, including zero sections. -/
theorem normalizedSimultaneousPolynomialRatioWeightAt_eq
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin))
    (hnI : modelIdealLog I gaussModelCoefficient_le_one
      (X.normalizedSimultaneousProductPointAt I J hfin y) ≠ ⊥)
    (j : Fin (M+1)) (d : ℕ) (F : MvPolynomial (Fin (M+1)) k) (hF : F.IsHomogeneous d) :
    X.normalizedSimultaneousPolynomialRatioWeightAt I J hfin y hnI j d F hF =
      X.normalizedSimultaneousRatioWeightAt I J hfin y hnI -
        ProjBerk.logAbs F (X.normalizedSimultaneousBaseRestrictionAt I J hfin y).1 := by
  unfold normalizedSimultaneousPolynomialRatioWeightAt normalizedSimultaneousPolynomialRatioSectionAt
  rw [modelLineNorm_genericTensorSection]
  change -ENNReal.log ((X.normalizedSimultaneousHomogeneousSectionNormAt I J hfin y j d F hF : ℝ≥0∞) *
    (modelLineNorm gaussModelCoefficient_le_one y
      (X.normalizedSimultaneousRatioLine_isInvertible I J hfin)
      (X.normalizedSimultaneousRatioSectionAt I J hfin y hnI) : ℝ≥0∞)) = _
  rw [X.normalizedSimultaneousHomogeneousSectionNormAt_eq_val I J hfin y j d F hF,
    ENNReal.log_mul_add]
  have hnotop (a : ℝ≥0) : ENNReal.log (a : ℝ≥0∞) ≠ ⊤ :=
    fun h => ENNReal.coe_ne_top (ENNReal.log_eq_top_iff.mp h)
  let w := X.normalizedSimultaneousBaseRestrictionAt I J hfin y
  let b : ℝ≥0 := modelLineNorm gaussModelCoefficient_le_one y
    (X.normalizedSimultaneousRatioLine_isInvertible I J hfin)
    (X.normalizedSimultaneousRatioSectionAt I J hfin y hnI)
  change -(ENNReal.log (w.1.1.val F : ℝ≥0∞) + ENNReal.log (b : ℝ≥0∞)) =
    -ENNReal.log (b : ℝ≥0∞) - ENNReal.log (w.1.1.val F : ℝ≥0∞)
  exact (EReal.neg_add (Or.inr (hnotop b)) (Or.inl (hnotop (w.1.1.val F)))).trans
    (add_comm _ _)
end EnvelopeProperty.ProjSubvariety
