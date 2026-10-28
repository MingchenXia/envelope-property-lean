import EnvelopeProperty.Local.PLOriginalModelCompatibilityOriginalProjection

/-! # Whole action comparison on the same original normalized twisted ratio line -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped Polynomial LaurentPolynomial CategoryTheory.MonObj
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

namespace EnvelopeProperty.PLOriginalModelCompatibility
open Scheme.Modules

/-- The canonical whole comparison on a pullback from the same original
target, from equality of the actual entire composed morphisms. -/
def invariantProjectionLineComparison {P N X : Scheme.{u}} (a p : P ⟶ N)
    (q : N ⟶ X) (h : a ≫ q = p ≫ q) (L : X.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L) ≅
      (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj L) :=
  (pullbackComp a q).app L ≪≫ (pullbackCongr h).app L ≪≫
    ((pullbackComp p q).app L).symm

end EnvelopeProperty.PLOriginalModelCompatibility

namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint NativeTestConfiguration
open Scheme.Modules
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : HomogeneousIdeal (ProjectiveGrading k[X] M))
variable (hI : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
variable (hJ : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
variable (hfin : ∀ w : X.an,
  modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥)

/-- Whole comparison of the actual unchanged original twist pullback,
using the proved whole invariance of the original projection. -/
def normalizedSimultaneousOriginalTwistNativeGmComparison (j : Fin (M+1)) (n : ℕ) :
    letI := X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
    let N := totalOver k (X.normalizedSimultaneousIdealBlowupStructure
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)
    (Scheme.Modules.pullback (cartierActionMap (nativeMultiplicativeGroup k) N)).obj
        ((Scheme.Modules.pullback (X.normalizedSimultaneousOriginalProjection
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).obj
            (X.nativeTwistLineSheaf j n)) ≅
      (Scheme.Modules.pullback (cartierProjectionMap (nativeMultiplicativeGroup k) N)).obj
        ((Scheme.Modules.pullback (X.normalizedSimultaneousOriginalProjection
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).obj
            (X.nativeTwistLineSheaf j n)) := by
  let : ModObj (nativeMultiplicativeGroup k)
      (totalOver k (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)) :=
    X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
  exact PLOriginalModelCompatibility.invariantProjectionLineComparison _ _ _
    (X.normalizedSimultaneousNativeOriginalProjection_invariant I J hI hJ hfin)
    (X.nativeTwistLineSheaf j n)

/-- The actual original twisted ratio line has its entire group comparison,
constructed from the fixed original twist and canonical invariant ratio;
no desired line comparison is an input. -/
def normalizedSimultaneousTwistedRatioNativeGmComparison (j : Fin (M+1)) (n : ℕ) :
    letI := X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
    let N := totalOver k (X.normalizedSimultaneousIdealBlowupStructure
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)
    (Scheme.Modules.pullback (cartierActionMap (nativeMultiplicativeGroup k) N)).obj
        (X.normalizedSimultaneousTwistedRatioLine
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin j n) ≅
      (Scheme.Modules.pullback (cartierProjectionMap (nativeMultiplicativeGroup k) N)).obj
        (X.normalizedSimultaneousTwistedRatioLine
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin j n) := by
  let : ModObj (nativeMultiplicativeGroup k)
      (totalOver k (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)) :=
    X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
  exact canonicalTensorPullbackIso _ _ _ ≪≫
    tensorObjCongr
      (X.normalizedSimultaneousOriginalTwistNativeGmComparison I J hI hJ hfin j n)
      (X.normalizedSimultaneousRatioNativeGmLinearization I J hI hJ hfin) ≪≫
    (canonicalTensorPullbackIso _ _ _).symm

end EnvelopeProperty.ProjSubvariety
