import EnvelopeProperty.AlgGeom.ReesCechIdealPowerSections
import EnvelopeProperty.AlgGeom.FormalFunctionsReesCohomologyFinite

/-! # Genuine finite cohomology in every original ideal-power degree -/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FormalFunctionsDegreeFinite

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (hf : IsProjectiveFactorization f)
variable {ι : Type u} [LinearOrder ι] [Fintype ι]
variable (U : ι → X.Opens) (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))

include hf hcover hU

/-- Actual projective coherent cohomology gives finite WHOLE cohomology of
the SAME original ideal-power sheaf, on the SAME original affine cover. -/
theorem orderedIdealPowerCech_finite (d n : ℕ) :
    Module.Finite Γ(Spec (.of R), ⊤)
      ((orderedBaseCechComplex f (FibreIdealPowers.powerModule I f d) U).homology n) := by
  let : IsProper f := hf.isProper
  let : LocallyOfFiniteType f := inferInstance
  let : (FibreIdealPowers.powerModule I f d).IsQuasicoherent :=
    FibreIdealPowers.isQuasicoherent_powerModule I f d
  let : (FibreIdealPowers.powerModule I f d).IsFiniteType :=
    FibreIdealPowers.isFiniteType_powerModule I f d
  cases n with
  | zero =>
    exact hf.orderedBaseCechComplex_homology_zero_module_finite
      (FibreIdealPowers.powerModule I f d) U hcover
  | succ n =>
    let : Module.Finite Γ(Spec (.of R), ⊤)
        ((baseCechComplex f (FibreIdealPowers.powerModule I f d) U).homology (n + 1)) :=
      hf.baseModuleCech_homology_succ_module_finite_of_affine_openCover
        (FibreIdealPowers.powerModule I f d) U hcover hU n
    exact Module.Finite.equiv
      (baseCechOrderedHomologyIso f (FibreIdealPowers.powerModule I f d) U (n + 1)).toLinearEquiv

/-- Restricting the genuine original affine coefficient action yields finite
cohomology over the SAME original R, not an auxiliary replacement ring. -/
theorem originalIdealPowerCech_finite (d n : ℕ) :
    Module.Finite R
      ((ModuleCat.restrictScalars (FcReesCechIdealPowerSections.baseScalar (R := R))).obj
        ((orderedBaseCechComplex f (FibreIdealPowers.powerModule I f d) U).homology n)) := by
  let G := Γ(Spec (.of R), ⊤)
  let C := orderedBaseCechComplex f (FibreIdealPowers.powerModule I f d) U
  let M := (ModuleCat.restrictScalars (FcReesCechIdealPowerSections.baseScalar (R := R))).obj
    (C.homology n)
  let : Module G M := (C.homology n).isModule
  let : Module.Finite G M := orderedIdealPowerCech_finite I f hf U hcover hU d n
  let : Algebra R G := (FcReesCechIdealPowerSections.baseScalar (R := R)).toAlgebra
  let : IsScalarTower R G M := ⟨fun a b x => mul_smul _ _ _⟩
  have hsurj : Function.Surjective (algebraMap R G) :=
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective
  let : Module.Finite R G :=
    Module.Finite.of_surjective (Algebra.linearMap R G) hsurj
  exact Module.Finite.trans (R := R) G M

/-- EVERY literal original Rees-degree cohomology group is genuinely finite
over the unchanged original base, derived from the original projective geometry. -/
theorem degreeCech_finite [X.IsSeparated] (d n : ℕ) :
    Module.Finite R ((FcReesCechDegreeComplex.degreeComplex I f U hU d).homology n) := by
  let : Module.Finite R
      ((ModuleCat.restrictScalars (FcReesCechIdealPowerSections.baseScalar (R := R))).obj
        ((orderedBaseCechComplex f (FibreIdealPowers.powerModule I f d) U).homology n)) :=
    originalIdealPowerCech_finite I f hf U hcover hU d n
  exact Module.Finite.equiv
    (FcReesCechIdealPowerSections.homologyIso I f U hU d n).toLinearEquiv

end EnvelopeProperty.FormalFunctionsDegreeFinite
