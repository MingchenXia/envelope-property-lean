/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealNormalizedPolarization
import EnvelopeProperty.AlgGeom.NormalizationCartierModulePullback

/-! # Whole normalization pullback of the same original PL ratio lines -/

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped Polynomial
noncomputable section
universe u

namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint IntegralSchemeNormalization

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)

/-- The same original ratio line pulls back to the actual normalized ratio
through the canonical maps of the two original ideal modules. -/
def normalizedSimultaneousRatioPullbackIso :
    (pullback (X.normalizedSimultaneousIdealBlowupProjection I J hfin)).obj
        (X.simultaneousRatioModelSheaf I J) ≅
      X.normalizedSimultaneousRatioLine I J hfin := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) :=
    X.simultaneousIdealBlowup_isIntegral_of_finiteLogs I J X.triv
      (hfin X.triv).1 (hfin X.triv).2
  let μ := X.simultaneousIdealBlowupProjection I J
  let ν := X.normalizedSimultaneousIdealBlowupProjection I J hfin
  let K := I.comap μ
  let L := J.comap μ
  have hK : K.IsInvertible := (X.simultaneousIdealBlowup_isInvertible I J).1
  have hL : L.IsInvertible := (X.simultaneousIdealBlowup_isInvertible I J).2
  let : IsIso (K.toModulesComapPullbackMap ν) :=
    cartierModuleComparison_isIso (X.simultaneousIdealBlowup I J) hK
  let : IsIso (L.toModulesComapPullbackMap ν) :=
    cartierModuleComparison_isIso (X.simultaneousIdealBlowup I J) hL
  exact K.ratioPullbackIso L hL ν ≪≫
    tensorObjCongr (asIso (K.toModulesComapPullbackMap ν))
      (dualIsoObj (asIso (L.toModulesComapPullbackMap ν)).symm)

/-- Whole pullback preserves the same original projective twist and ratio,
using the original normalized projection and the same coordinate and power. -/
def normalizedSimultaneousTwistedRatioPullbackIso (j : Fin (M+1)) (n : ℕ) :
    (pullback (X.normalizedSimultaneousIdealBlowupProjection I J hfin)).obj
        (X.simultaneousTwistedRatioModelSheaf I J j n) ≅
      X.normalizedSimultaneousTwistedRatioLine I J hfin j n :=
  canonicalTensorPullbackIso _ _ _ ≪≫
    tensorObjCongr
      ((pullbackComp (X.normalizedSimultaneousIdealBlowupProjection I J hfin)
        (X.simultaneousOriginalProjection I J)).app (X.nativeTwistLineSheaf j n))
      (X.normalizedSimultaneousRatioPullbackIso I J hfin)

end EnvelopeProperty.ProjSubvariety
