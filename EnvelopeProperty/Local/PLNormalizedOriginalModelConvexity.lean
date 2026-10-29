import EnvelopeProperty.Local.PLNormalizedModelConvexity
import EnvelopeProperty.Local.PLNormalizedPolarizationComparison
import EnvelopeProperty.Berkovich.SchemeLineModelIsometries

/-! # True intrinsic convexity on the SAME original O(d) tensor ratio line -/
open scoped Classical Polynomial NNReal ENNReal
open CategoryTheory AlgebraicGeometry Opposite
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich.RelativeSchemeValuedPoint
variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
private local instance modelProper : IsProper (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
  X.normalizedSimultaneousIdealBlowupStructure_isProper I J hfin

/-- The SAME genuine polarized generic section, transported by the constructed
whole line isomorphism to the accepted ORIGINAL O(d) tensor Cartier ratio line. -/
def normalizedSimultaneousOriginalRatioSectionAt
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin))
    (hnI : modelIdealLog I gaussModelCoefficient_le_one
      (X.normalizedSimultaneousProductPointAt I J hfin y) ≠ ⊥)
    (j : Fin (n+1)) (d : ℕ) (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous d) :
    Γ(genericLineModule y (X.normalizedSimultaneousTwistedRatioLine I J hfin j d), ⊤) :=
  ((Scheme.Modules.pullback
    ((X.normalizedSimultaneousIdealBlowup I J hfin).fromSpecResidueField y.1.point)).map
      (X.normalizedSimultaneousPolynomialRatioLineIso I J hfin j d).hom).val.app (op ⊤)
        (X.normalizedSimultaneousPolynomialRatioSectionAt I J hfin y hnI j d F hF)

/-- The TRUE actual negative-log model norm on the SAME original prescribed
O(d) tensor Cartier-ratio line, with no metric-identification premise. -/
def normalizedSimultaneousOriginalRatioWeightAt
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin))
    (hnI : modelIdealLog I gaussModelCoefficient_le_one
      (X.normalizedSimultaneousProductPointAt I J hfin y) ≠ ⊥)
    (j : Fin (n+1)) (d : ℕ) (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous d) : EReal :=
  -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y
    (X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d)
    (X.normalizedSimultaneousOriginalRatioSectionAt I J hfin y hnI j d F hF) : ℝ≥0∞)

/-- The derived whole original line comparison is a TRUE model isometry at
EVERY actual model point, so the SAME actual section weight is retained. -/
theorem normalizedSimultaneousOriginalRatioWeightAt_eq
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin))
    (hnI : modelIdealLog I gaussModelCoefficient_le_one
      (X.normalizedSimultaneousProductPointAt I J hfin y) ≠ ⊥)
    (j : Fin (n+1)) (d : ℕ) (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous d) :
    X.normalizedSimultaneousOriginalRatioWeightAt I J hfin y hnI j d F hF =
      X.normalizedSimultaneousPolynomialRatioWeightAt I J hfin y hnI j d F hF := by
  exact congrArg (fun t : ℝ≥0 => -ENNReal.log (t : ℝ≥0∞))
    (modelLineNorm_mapIso gaussModelCoefficient_le_one y
      (X.normalizedSimultaneousPolynomialRatioLine_isInvertible I J hfin j d)
      (X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d)
      (X.normalizedSimultaneousPolynomialRatioLineIso I J hfin j d)
      (X.normalizedSimultaneousPolynomialRatioSectionAt I J hfin y hnI j d F hF)).symm

/-- ORIGINAL local O(a)-convexity constructs a normal model whose TRUE weights
on the accepted ORIGINAL O(d) tensor ratio line are genuinely intrinsically
convex at ALL actual model points, retaining EXACT original class d=r*a.
No arbitrary line comparison, metric or nef/slope certificate is assumed. -/
theorem IsLocallyConvexAll.exists_prescribedClass_intrinsicConvex_originalModelMetric
    (hX : X.IsProjNormal) {a : ℚ} (ha : 0 < a) {φ : X.an → ℝ}
    (hconv : X.IsLocallyConvexAll a φ) :
    ∃ (r d : ℕ) (_hr : 0 < r) (_hd : 0 < d), (d : ℚ) = r*a ∧
      ∃ (C : ℤ) (I J : X.NativeProductModel.IdealSheafData)
        (hfinAll : ∀ z : RelativeSchemeValuedPoint
            (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
          modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
          modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥),
        let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
        (∀ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
            (X.normalizedSimultaneousIdealBlowupStructure I J hfin),
          (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) : ℝ) : EReal) =
            X.normalizedSimultaneousRatioWeightAt I J hfin y
              (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 + ((C : ℝ) : EReal)) ∧
        ∀ (j : Fin (n+1)) (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous d),
          F ∉ X.ideal → RelativeSchemeValuedPoint.IsConvexPLOn
            (X.normalizedSimultaneousAdmissibleAnalyticLocus I J hfin F)
            (fun y => X.normalizedSimultaneousOriginalRatioWeightAt I J hfin y
              (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 j d F hF) := by
  obtain ⟨r,d,hr,hd,hda,C,I,J,hfinAll,heq,hweights⟩ :=
    hconv.exists_prescribedClass_intrinsicConvex_normalizedRatioMetric X hX ha
  refine ⟨r,d,hr,hd,hda,C,I,J,hfinAll,heq,?_⟩
  intro j F hF hFI
  apply (hweights j F hF hFI).congr
  intro y _
  exact (X.normalizedSimultaneousOriginalRatioWeightAt_eq I J _ y _ j d F hF).symm

end EnvelopeProperty.ProjSubvariety
