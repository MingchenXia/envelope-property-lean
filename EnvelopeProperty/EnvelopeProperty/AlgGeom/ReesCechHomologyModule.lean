import EnvelopeProperty.AlgGeom.ReesCechDegreeHomology
import EnvelopeProperty.AlgGeom.FormalFunctionsReesCohomologyFinite
import Mathlib.Algebra.Module.TransferInstance

/-! # The actual finite Rees action on original ideal-power cohomology -/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules
open scoped DirectSum
noncomputable section
universe u
namespace EnvelopeProperty.FcReesCechHomologyModule

open FcReesCechDegreeComplex

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
variable [X.IsSeparated] {ι : Type u} [LinearOrder ι] [Fintype ι]
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))

private abbrev originalComplex :=
  orderedBaseCechComplex (FcReesFormalFamily.familyProjection I f)
    (unitObj (FcReesFormalFamily.family I f))
    (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j)

/-- The actual degree cohomologies with their unchanged original R-module structure. -/
abbrev degreeHomology (n : ℕ) : ModuleCat R :=
  ModuleCat.of R (⨁ d : ℕ, (degreeComplex I f U hU d).homology n)

/-- Genuine exact restriction of original coefficients commutes with the
actual original structure-module Rees Cech homology. -/
def scalarHomologyIso (n : ℕ) :
    (((ModuleCat.restrictScalars (baseScalar I)).mapHomologicalComplex (.up ℕ)).obj
      (originalComplex I f U)).homology n ≅
      (ModuleCat.restrictScalars (baseScalar I)).obj ((originalComplex I f U).homology n) :=
  ((originalComplex I f U).sc n).mapHomologyIso
    (ModuleCat.restrictScalars (baseScalar I))

/-- The actual original coefficient-linear cohomology comparison on whole classes. -/
def homologyEquiv (n : ℕ) :
    ((ModuleCat.restrictScalars (baseScalar I)).obj
      ((originalComplex I f U).homology n)) ≃ₗ[R] degreeHomology I f U hU n :=
  ((scalarHomologyIso I f U n).symm ≪≫
    FcReesCechDegreeHomology.orderedHomologyIso I f U hU n).toLinearEquiv

/-- Transfer the ACTUAL original coefficient action to the SAME additive
sum of genuine original ideal-power cohomology modules. -/
@[instance_reducible]
def coefficientModule (n : ℕ) :
    Module Γ(Spec (.of (reesAlgebra I)), ⊤) (degreeHomology I f U hU n) := by
  let : Module Γ(Spec (.of (reesAlgebra I)), ⊤)
      ((ModuleCat.restrictScalars (baseScalar I)).obj
        ((originalComplex I f U).homology n)) :=
    ((originalComplex I f U).homology n).isModule
  exact (homologyEquiv I f U hU n).symm.toAddEquiv.module
    Γ(Spec (.of (reesAlgebra I)), ⊤)

/-- The genuine whole comparison is linear for the ACTUAL transported
coefficient action, with the same original cohomology classes. -/
def coefficientEquiv (n : ℕ) :
    letI := coefficientModule I f U hU n
    (originalComplex I f U).homology n ≃ₗ[Γ(Spec (.of (reesAlgebra I)), ⊤)]
      degreeHomology I f U hU n := by
  let : Module Γ(Spec (.of (reesAlgebra I)), ⊤)
      ((ModuleCat.restrictScalars (baseScalar I)).obj
        ((originalComplex I f U).homology n)) :=
    ((originalComplex I f U).homology n).isModule
  exact ((homologyEquiv I f U hU n).symm.toAddEquiv.linearEquiv
    Γ(Spec (.of (reesAlgebra I)), ⊤)).symm

/-- The ACTUAL Rees ring acts through its genuine affine global-section isomorphism. -/
@[instance_reducible]
def reesModule (n : ℕ) : Module (reesAlgebra I) (degreeHomology I f U hU n) := by
  letI := coefficientModule I f U hU n
  exact Module.compHom (degreeHomology I f U hU n)
    (Scheme.ΓSpecIso (.of (reesAlgebra I))).inv.hom

/-- EVERY original Rees scalar acts on EVERY original cohomology class via
its genuine original coefficient action and the genuine whole comparison. -/
theorem reesModule_smul (n : ℕ) (p : reesAlgebra I) (x : degreeHomology I f U hU n) :
    letI := coefficientModule I f U hU n
    letI := reesModule I f U hU n
    p • x = coefficientEquiv I f U hU n
      ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv.hom p •
        (coefficientEquiv I f U hU n).symm x) := by
  let := coefficientModule I f U hU n
  let := reesModule I f U hU n
  rfl

/-- Restricting the genuine transported Rees action to an original scalar
recovers the SAME unchanged original R-module action on every class. -/
theorem reesModule_originalScalar (n : ℕ) (r : R) (x : degreeHomology I f U hU n) :
    letI := reesModule I f U hU n
    algebraMap R (reesAlgebra I) r • x = r • x := by
  let := reesModule I f U hU n
  change homologyEquiv I f U hU n
      (r • (homologyEquiv I f U hU n).symm x) = r • x
  simpa only [LinearEquiv.apply_symm_apply] using
    (homologyEquiv I f U hU n).map_smul r ((homologyEquiv I f U hU n).symm x)

/-- The actual Rees action is compatible with the original coefficient
scalar tower, keeping the original R-module structure unchanged. -/
theorem originalScalarTower (n : ℕ) :
    letI := reesModule I f U hU n
    IsScalarTower R (reesAlgebra I) (degreeHomology I f U hU n) := by
  let := reesModule I f U hU n
  constructor
  intro r p x
  rw [Algebra.smul_def r p, mul_smul, reesModule_originalScalar]

/-- Actual projective coherent cohomology finiteness proves the SAME whole
original ideal-power cohomology sum finite over the ACTUAL Rees algebra. -/
theorem finiteReesHomology [IsNoetherianRing R] (hf : IsProjectiveFactorization f)
    (hcover : IsOpenCover U) (n : ℕ) :
    letI := reesModule I f U hU n
    Module.Finite (reesAlgebra I) (degreeHomology I f U hU n) := by
  let G := Γ(Spec (.of (reesAlgebra I)), ⊤)
  let : Module.Finite G ((originalComplex I f U).homology n) :=
    FormalFunctionsReesCohomologyFinite.orderedReesCech_finite I f hf U hcover hU n
  let := coefficientModule I f U hU n
  let : Module.Finite G (degreeHomology I f U hU n) :=
    Module.Finite.equiv (coefficientEquiv I f U hU n)
  let := reesModule I f U hU n
  let : Algebra (reesAlgebra I) G :=
    (Scheme.ΓSpecIso (.of (reesAlgebra I))).inv.hom.toAlgebra
  let : IsScalarTower (reesAlgebra I) G (degreeHomology I f U hU n) :=
    ⟨fun a b x => mul_smul _ _ _⟩
  have hsurj : Function.Surjective (algebraMap (reesAlgebra I) G) :=
    (Scheme.ΓSpecIso (.of (reesAlgebra I))).commRingCatIsoToRingEquiv.symm.surjective
  let : Module.Finite (reesAlgebra I) G :=
    Module.Finite.of_surjective (Algebra.linearMap (reesAlgebra I) G) hsurj
  exact Module.Finite.trans (R := reesAlgebra I) G (degreeHomology I f U hU n)

end EnvelopeProperty.FcReesCechHomologyModule
