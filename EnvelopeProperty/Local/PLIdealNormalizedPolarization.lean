/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealNormalizedNoncentral
import EnvelopeProperty.Local.PLIdealTwistedModelSheaves

/-! # Actual original projective polarization on the SAME normal PL models -/

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Classical Polynomial NNReal ENNReal
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint IntegralSchemeNormalization
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)

/-- The entire actual noncentral open of the SAME original normalized model. -/
def normalizedSimultaneousNoncentralOpen : (X.normalizedSimultaneousIdealBlowup I J hfin).Opens :=
  X.normalizedSimultaneousIdealBlowupStructure I J hfin ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : k[X])

omit I J hfin in
/-- Actual parameter powers yield the WHOLE original noncentral trivialization
of the SAME actual ratio line on the SAME original normalized model. -/
def normalizedSimultaneousRatioParameterIso
    (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)) (A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal)
    (hfin : ∀ w : X.an,
      modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥) :
    (Scheme.Modules.pullback (X.normalizedSimultaneousNoncentralOpen
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin).ι).obj
        (X.normalizedSimultaneousRatioLine (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin) ≅
      Scheme.Modules.unitObj (X.normalizedSimultaneousNoncentralOpen
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin).toScheme := by
  let μ := X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J)
  let ν := X.normalizedSimultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
  refine (((X.nativeProductIdeal I).comap μ).comap ν).ratioPullbackUnitIsoOfLeComplSupport
    (((X.nativeProductIdeal J).comap μ).comap ν)
    (X.normalizedSimultaneousNoncentralOpen (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin) ?_ ?_
  · intro y hy
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
    exact X.parameterOpen_le_compl_nativeProductIdeal_support I A hA hy
  · intro y hy
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
    exact X.parameterOpen_le_compl_nativeProductIdeal_support J B hB hy

/-- The SAME actual normal model's whole original projection to the
SAME original closed projective variety. -/
def normalizedSimultaneousOriginalProjection :
    X.normalizedSimultaneousIdealBlowup I J hfin ⟶ X.NativeScheme :=
  X.normalizedSimultaneousIdealBlowupProjection I J hfin ≫ X.simultaneousOriginalProjection I J

/-- The actual original O(n) pullback tensor the actual original Cartier ratio,
on the SAME true original normal proper model. -/
def normalizedSimultaneousTwistedRatioLine (j : Fin (M+1)) (n : ℕ) :
    (X.normalizedSimultaneousIdealBlowup I J hfin).Modules :=
  Scheme.Modules.tensorObj
    ((Scheme.Modules.pullback (X.normalizedSimultaneousOriginalProjection I J hfin)).obj
      (X.nativeTwistLineSheaf j n)) (X.normalizedSimultaneousRatioLine I J hfin)

/-- Invertibility of BOTH actual original factors proves invertibility of
the actual original polarized line on the SAME original normal model. -/
theorem normalizedSimultaneousTwistedRatioLine_isInvertible (j : Fin (M+1)) (n : ℕ) :
    Scheme.Modules.IsInvertible (X.normalizedSimultaneousTwistedRatioLine I J hfin j n) :=
  ((X.nativeTwistLineSheaf_isInvertible j n).pullback _).tensorObj
    (X.normalizedSimultaneousRatioLine_isInvertible I J hfin)

omit I J hfin in
/-- The entire actual original noncentral restriction of the SAME normalized
polarized line is the SAME original O(n) pullback along the actual open-to-X map. -/
def normalizedSimultaneousTwistedRatioParameterIso
    (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)) (j : Fin (M+1)) (n A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal)
    (hfin : ∀ w : X.an,
      modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥) :
    (Scheme.Modules.pullback (X.normalizedSimultaneousNoncentralOpen
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin).ι).obj
        (X.normalizedSimultaneousTwistedRatioLine (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin j n) ≅
      (Scheme.Modules.pullback ((X.normalizedSimultaneousNoncentralOpen
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin).ι ≫
          X.normalizedSimultaneousOriginalProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).obj
        (X.nativeTwistLineSheaf j n) :=
  Scheme.Modules.canonicalTensorPullbackIso _ _ _ ≪≫
    Scheme.Modules.tensorObjCongr (Iso.refl _)
      (X.normalizedSimultaneousRatioParameterIso I J A B hA hB hfin) ≪≫
    Scheme.Modules.tensorObjUnitIso _ ≪≫ (Scheme.Modules.pullbackComp _ _).app _

end EnvelopeProperty.ProjSubvariety
