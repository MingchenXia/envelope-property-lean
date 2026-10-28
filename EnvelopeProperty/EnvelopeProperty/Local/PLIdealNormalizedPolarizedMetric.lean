import EnvelopeProperty.Local.PLIdealNormalizedSectionNorms
import EnvelopeProperty.Berkovich.SchemeLineModelTensorNorms

/-! # True actual local weights on the SAME polynomial-polarized normal ratio line -/
open scoped Classical Polynomial NNReal ENNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)

/-- The SAME normalized model's actual polynomial O(d) tensor Cartier ratio line. -/
def normalizedSimultaneousPolynomialRatioLine (j : Fin (M+1)) (d : ℕ) :
    (X.normalizedSimultaneousIdealBlowup I J hfin).Modules :=
  Scheme.Modules.tensorObj
    ((Scheme.Modules.pullback (X.normalizedSimultaneousPolynomialProjection I J hfin)).obj
      (MvPolynomial.coordinateHyperplanePoleSheafPower (R := k[X]) j d))
    (X.normalizedSimultaneousRatioLine I J hfin)

/-- Invertibility of the SAME genuine factors derives invertibility of the
SAME actual polarized ratio line, with no supplied polarization certificate. -/
theorem normalizedSimultaneousPolynomialRatioLine_isInvertible (j : Fin (M+1)) (d : ℕ) :
    Scheme.Modules.IsInvertible (X.normalizedSimultaneousPolynomialRatioLine I J hfin j d) :=
  ((MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible (R := k[X]) j d).pullback _).tensorObj
    (X.normalizedSimultaneousRatioLine_isInvertible I J hfin)

private local instance normalizedPolarizedMetricProper :
    IsProper (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
  X.normalizedSimultaneousIdealBlowupStructure_isProper I J hfin

/-- The genuine generic pure tensor of the ORIGINAL pulled homogeneous
section with the SAME ACTUAL canonical original ratio section. -/
def normalizedSimultaneousPolynomialRatioSection (hX : X.IsProjNormal)
    (j : Fin (M+1)) (d : ℕ) (F : MvPolynomial (Fin (M+1)) k) (hF : F.IsHomogeneous d)
    (w : X.an) :
    Γ(genericLineModule (X.normalizedSimultaneousGaussPoint I J hfin hX w)
      (X.normalizedSimultaneousPolynomialRatioLine I J hfin j d), ⊤) :=
  genericTensorSection (X.normalizedSimultaneousGaussPoint I J hfin hX w)
    (fibreSection (X.normalizedSimultaneousGaussPoint I J hfin hX w)
      (SchemeLineSectionEvaluation.pullbackSectionHom
        (X.normalizedSimultaneousPolynomialProjection I J hfin)
        (ProjectiveHomogeneousSections.sectionHom j d (MvPolynomial.map Polynomial.C F)
          (hF.map Polynomial.C))))
    (X.normalizedSimultaneousRatioSection I J hfin hX w)

/-- ACTUAL local weight, defined by the TRUE norm of the SAME actual tensor section. -/
def normalizedSimultaneousPolynomialRatioWeight (hX : X.IsProjNormal)
    (j : Fin (M+1)) (d : ℕ) (F : MvPolynomial (Fin (M+1)) k) (hF : F.IsHomogeneous d)
    (w : X.an) : EReal :=
  -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one
    (X.normalizedSimultaneousGaussPoint I J hfin hX w)
    (X.normalizedSimultaneousPolynomialRatioLine_isInvertible I J hfin j d)
    (X.normalizedSimultaneousPolynomialRatioSection I J hfin hX j d F hF w) : ℝ≥0∞)

/-- The TRUE normalized polarized weight equals EXACTLY the ORIGINAL ratio
model weight minus the ORIGINAL homogeneous logAbs, including vanishing F. -/
theorem normalizedSimultaneousPolynomialRatioWeight_eq (hX : X.IsProjNormal)
    (j : Fin (M+1)) (d : ℕ) (F : MvPolynomial (Fin (M+1)) k) (hF : F.IsHomogeneous d)
    (w : X.an) :
    X.normalizedSimultaneousPolynomialRatioWeight I J hfin hX j d F hF w =
      X.normalizedSimultaneousRatioWeight I J hfin hX w - ProjBerk.logAbs F w.1 := by
  unfold normalizedSimultaneousPolynomialRatioWeight normalizedSimultaneousPolynomialRatioSection
  rw [modelLineNorm_genericTensorSection]
  change -ENNReal.log ((X.normalizedSimultaneousHomogeneousSectionNorm I J hfin hX j d F hF w : ℝ≥0∞) *
    (modelLineNorm gaussModelCoefficient_le_one (X.normalizedSimultaneousGaussPoint I J hfin hX w)
      (X.normalizedSimultaneousRatioLine_isInvertible I J hfin)
      (X.normalizedSimultaneousRatioSection I J hfin hX w) : ℝ≥0∞)) = _
  rw [X.normalizedSimultaneousHomogeneousSectionNorm_eq_val I J hfin hX j d F hF w,
    ENNReal.log_mul_add]
  have hnotop (a : ℝ≥0) : ENNReal.log (a : ℝ≥0∞) ≠ ⊤ :=
    fun h => ENNReal.coe_ne_top (ENNReal.log_eq_top_iff.mp h)
  let b : ℝ≥0 := modelLineNorm gaussModelCoefficient_le_one
    (X.normalizedSimultaneousGaussPoint I J hfin hX w)
    (X.normalizedSimultaneousRatioLine_isInvertible I J hfin)
    (X.normalizedSimultaneousRatioSection I J hfin hX w)
  change -(ENNReal.log (w.1.1.val F : ℝ≥0∞) + ENNReal.log (b : ℝ≥0∞)) =
    -ENNReal.log (b : ℝ≥0∞) - ENNReal.log (w.1.1.val F : ℝ≥0∞)
  exact (EReal.neg_add (Or.inr (hnotop b)) (Or.inl (hnotop (w.1.1.val F)))).trans
    (add_comm _ _)

end EnvelopeProperty.ProjSubvariety
