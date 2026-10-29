import EnvelopeProperty.AlgGeom.ProjectiveTwistCoefficientPullback
import EnvelopeProperty.Local.PLNormalizedOriginalProjection
import EnvelopeProperty.Local.PLIdealNormalizedPolarizedMetric

/-! # The SAME prescribed-class normal-model line in its original polarization -/
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

/-- The actual original product's polynomial projective inclusion commutes
with the SAME original whole variety projection and closed inclusion. -/
theorem nativeProductPolynomialInclusion_coefficientMap :
    X.nativeProductPolynomialInclusion ≫ nativeCoefficientMap (Polynomial.C : k →+* k[X]) =
      X.nativeProductOriginalProjection ≫ X.nativeInclusion := by
  rw [X.nativeProductOriginalProjection_inclusion]
  dsimp only [nativeProductPolynomialInclusion]
  rw [Category.assoc]
  have h := nativeCoefficientBaseChangeIso_hom_fst (n := n) (Polynomial.C : k →+* k[X])
  have hi : (nativePolynomialLineProductIso k n).inv ≫
      nativeCoefficientMap (Polynomial.C : k →+* k[X]) =
        pullback.fst (nativeStructureMap (R := k) (n := n))
          (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) := by
    rw [← h]
    exact (nativePolynomialLineProductIso k n).inv_hom_id_assoc _
  rw [hi]

variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  RelativeSchemeValuedPoint.modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)

/-- The literal actual polynomial projective projection of the SAME normal
model equals its original variety projection followed by original inclusion,
after the actual coefficient map. -/
theorem normalizedSimultaneousPolynomialProjection_coefficientMap :
    X.normalizedSimultaneousPolynomialProjection I J hfin ≫
        nativeCoefficientMap (Polynomial.C : k →+* k[X]) =
      X.normalizedSimultaneousOriginalProjection I J hfin ≫ X.nativeInclusion := by
  rw [X.normalizedSimultaneousOriginalProjection_eq I J hfin]
  dsimp only [normalizedSimultaneousPolynomialProjection]
  simp only [Category.assoc,X.nativeProductPolynomialInclusion_coefficientMap]

/-- The SAME whole actual polynomial O(d) pullback is the true original
O(d) pulled along the SAME original variety projection. The exponent d
is retained exactly; no polarization-comparison premise is supplied. -/
def normalizedSimultaneousPolynomialTwistIso (j : Fin (n+1)) (d : ℕ) :
    (Scheme.Modules.pullback (X.normalizedSimultaneousPolynomialProjection I J hfin)).obj
      (MvPolynomial.coordinateHyperplanePoleSheafPower (R := k[X]) j d) ≅
    (Scheme.Modules.pullback (X.normalizedSimultaneousOriginalProjection I J hfin)).obj
      (X.nativeTwistLineSheaf j d) :=
  (Scheme.Modules.pullback (X.normalizedSimultaneousPolynomialProjection I J hfin)).mapIso
      (ProjectiveTwistCoefficientPullback.coordinatePolePowerPullbackIso
        (Polynomial.C : k →+* k[X]) j d).symm ≪≫
    (Scheme.Modules.pullbackComp (X.normalizedSimultaneousPolynomialProjection I J hfin)
      (nativeCoefficientMap (Polynomial.C : k →+* k[X]))).app _ ≪≫
    eqToIso (congrArg (fun g => (Scheme.Modules.pullback g).obj
      (MvPolynomial.coordinateHyperplanePoleSheafPower (R := k) j d))
      (X.normalizedSimultaneousPolynomialProjection_coefficientMap I J hfin)) ≪≫
    ((Scheme.Modules.pullbackComp (X.normalizedSimultaneousOriginalProjection I J hfin)
      X.nativeInclusion).app _).symm

/-- The SAME actual polynomial-polarized Cartier ratio line is the accepted
whole original O(d) tensor the SAME original Cartier ratio, on the SAME model.
This derives the genuine line comparison needed for original curve degrees. -/
def normalizedSimultaneousPolynomialRatioLineIso (j : Fin (n+1)) (d : ℕ) :
    X.normalizedSimultaneousPolynomialRatioLine I J hfin j d ≅
      X.normalizedSimultaneousTwistedRatioLine I J hfin j d :=
  Scheme.Modules.tensorObjCongr (X.normalizedSimultaneousPolynomialTwistIso I J hfin j d)
    (Iso.refl (X.normalizedSimultaneousRatioLine I J hfin))

end EnvelopeProperty.ProjSubvariety
