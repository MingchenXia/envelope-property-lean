import EnvelopeProperty.Local.PLOriginalModelCompatibilityFibreOne
import EnvelopeProperty.Local.PLOriginalModelCompatibilityGmTwistedLine
import EnvelopeProperty.Local.PLOriginalModelCompatibilityParameterEquivariance
import EnvelopeProperty.Local.PLIdealNormalizedProjectivity
import EnvelopeProperty.Local.PLNormalizedModelFlat
import EnvelopeProperty.AlgGeom.NativeProjectivityFromPolynomialFactorization
import EnvelopeProperty.Global.NativeTestConfigurationLineTrivialization

/-! # The same original normalized PL model as an actual native test configuration -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped Polynomial LaurentPolynomial CategoryTheory.MonObj
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}

/-- An invariant original projection determines exactly the same original
variety projection in the action-derived whole noncentral trivialization. -/
theorem unitOpenOriginalProjection_eq_of_invariant (C : TestConfiguration k X)
    (q : C.total ⟶ X.left)
    (hq : C.lineActionMap ≫ q = C.lineProjectionMap ≫ q)
    (hf : C.fibreOneIso.hom.left = C.fibreOneInclusion.left ≫ q) :
    C.unitOpenOriginalProjection.left = C.unitOpenInclusion.left ≫ q := by
  calc
    C.unitOpenOriginalProjection.left =
        C.unitOpenFibreProjection.left ≫ C.fibreOneIso.hom.left :=
      C.lineActionLift_original.symm
    _ = C.unitOpenFibreProjection.left ≫ C.fibreOneInclusion.left ≫ q := by rw [hf]
    _ = C.unitOpenActionLift.left ≫ C.lineProjectionMap ≫ q := by
      rw [← Category.assoc, ← C.lineActionLift_projection, Category.assoc]
    _ = C.unitOpenActionLift.left ≫ C.lineActionMap ≫ q := by rw [← hq]
    _ = C.unitOpenInclusion.left ≫ q := by rw [← Category.assoc, C.lineActionLift_action]

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration

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
variable (A B : ℕ) (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
  (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal) (hX : X.IsProjNormal)

/-- The same unchanged actual normalized simultaneous PL model is an
actual test configuration; its action, equivariance and original fibre-one
identification are constructed from the original ideal inputs. -/
def normalizedSimultaneousNativeTestConfiguration :
    TestConfiguration k (Over.mk X.nativeStructure) where
  total := X.normalizedSimultaneousIdealBlowup (X.nativeProductIdeal I)
      (X.nativeProductIdeal J) hfin
  projection := X.normalizedSimultaneousIdealBlowupStructure
    (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
  flat := X.normalizedSimultaneousStructure_isFlat_anyField
    (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
  projective := NativeProjectivityFromPolynomialFactorization.of_isProjectiveFactorization _
    (X.normalizedSimultaneousIdealBlowupStructure_isProjectiveFactorization
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)
  action := X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
  equivariant := X.normalizedSimultaneousNativeParameterOver_isModHom I J hI hJ hfin
  fibreOneIso := X.normalizedSimultaneousFibreOneOverIso I J A B hA hB hfin hX

/-- The actual normalized test configuration uses precisely the unchanged
original projection on its entire action-derived noncentral trivialization. -/
theorem normalizedSimultaneousNativeTestConfiguration_originalProjection :
    let C := X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A B hA hB hX
    C.unitOpenOriginalProjection.left =
      C.unitOpenInclusion.left ≫ X.normalizedSimultaneousOriginalProjection
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin := by
  let C := X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A B hA hB hX
  apply C.unitOpenOriginalProjection_eq_of_invariant
  · exact X.normalizedSimultaneousNativeOriginalProjection_invariant I J hI hJ hfin
  · exact X.normalizedSimultaneousFibreOneNativeIso_hom I J A B hA hB hfin hX

/-- The unchanged original polarized line provides the actual whole action
comparison consumed by the same test configuration's native line API. -/
def normalizedSimultaneousNativeTestConfigurationLineComparison
    (j : Fin (M+1)) (n : ℕ) :
    let C := X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A B hA hB hX
    let L := X.normalizedSimultaneousTwistedRatioLine
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin j n
    (Scheme.Modules.pullback C.lineActionMap).obj L ≅
        (Scheme.Modules.pullback C.lineProjectionMap).obj L :=
  X.normalizedSimultaneousTwistedRatioNativeGmComparison I J hI hJ hfin j n

/-- The same original fibre-one identification supplies the exact native
line input for the unchanged actual normalized test configuration. -/
def normalizedSimultaneousNativeTestConfigurationFibreOneLineIso
    (j : Fin (M+1)) (n : ℕ) :
    let C := X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A B hA hB hX
    let L := X.normalizedSimultaneousTwistedRatioLine
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin j n
    (Scheme.Modules.pullback C.fibreOneInclusion.left).obj L ≅
      (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj (X.nativeTwistLineSheaf j n) :=
  X.normalizedSimultaneousTwistedRatioFibreOneIdentification I J j n A B hA hB hfin hX

/-- The actual native whole noncentral line construction now applies to
the same original normalized test configuration and original polarized line. -/
def normalizedSimultaneousNativeTestConfigurationUnitOpenLineIso
    (j : Fin (M+1)) (n : ℕ) :
    let C := X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A B hA hB hX
    let L := X.normalizedSimultaneousTwistedRatioLine
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin j n
    (Scheme.Modules.pullback C.unitOpenInclusion.left).obj L ≅
      (Scheme.Modules.pullback C.unitOpenOriginalProjection.left).obj
          (X.nativeTwistLineSheaf j n) :=
  let C := X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A B hA hB hX
  C.unitOpenLineIso _ _
    (X.normalizedSimultaneousNativeTestConfigurationLineComparison I J hI hJ hfin
      A B hA hB hX j n)
    (X.normalizedSimultaneousNativeTestConfigurationFibreOneLineIso I J hI hJ hfin
      A B hA hB hX j n)

end EnvelopeProperty.ProjSubvariety
