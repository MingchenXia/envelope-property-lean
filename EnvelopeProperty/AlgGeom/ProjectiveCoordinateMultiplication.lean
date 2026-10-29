import EnvelopeProperty.AlgGeom.ProjectiveTwistTensorAddition
import EnvelopeProperty.AlgGeom.ProjectiveTwistGlobalGeneration

/-! # Actual coordinate multiplication between every integer projective twist -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules MvPolynomial
noncomputable section
universe u

namespace EnvelopeProperty.ProjectiveCoordinateMultiplication

attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra

private theorem restrict_whiskerLeft_isIso {X : Scheme.{u}} (U : X.Opens)
    (M : X.Modules) {N P : X.Modules} (f : N ⟶ P)
    (hf : IsIso ((restrictFunctor U.ι).map f)) :
    IsIso ((restrictFunctor U.ι).map (M ◁ f)) := by
  let F := restrictFunctor U.ι
  let : (Scheme.Modules.pullback U.ι).Monoidal := Scheme.Modules.pullbackMonoidal U.ι
  let : F.Monoidal := Functor.Monoidal.transport (restrictFunctorIsoPullback U.ι).symm
  let : IsIso (F.map f) := hf
  change IsIso (F.map (M ◁ f))
  rw [Functor.Monoidal.map_whiskerLeft]
  infer_instance

variable {R : Type u} [CommRing R] {σ : Type}

/-- Multiply an actual integer twist by the original ith degree-one coordinate
section, using the actual projective tensor-addition isomorphism. -/
def coordinateMul (j i : σ) (a : ℤ) :
    coordinateHyperplaneTwist (R := R) j a ⟶
      coordinateHyperplaneTwist (R := R) j (a + 1) :=
  (ρ_ (coordinateHyperplaneTwist (R := R) j a)).inv ≫
    (coordinateHyperplaneTwist (R := R) j a ◁
      ((ModularCurves.monoidalUnitObjIso (Proj (homogeneousSubmodule σ R))).hom ≫
        ProjectiveTwistGlobalGeneration.coordinateSectionHom j i 1)) ≫
    (ProjectiveTwistTensorAddition.tensorIso j j j a 1).hom

/-- Original coordinate multiplication trivializes every integer twist on the
coordinate's own standard open. -/
theorem coordinateMul_isIso_on_own_chart (j i : σ) (a : ℤ) :
    IsIso ((restrictFunctor (coordinateOpen (R := R) i).ι).map
      (coordinateMul (R := R) j i a)) := by
  let F := restrictFunctor (coordinateOpen (R := R) i).ι
  have hs : IsIso (F.map
      ((ModularCurves.monoidalUnitObjIso (Proj (homogeneousSubmodule σ R))).hom ≫
        ProjectiveTwistGlobalGeneration.coordinateSectionHom (R := R) j i 1)) := by
    rw [F.map_comp]
    let := ProjectiveTwistGlobalGeneration.coordinateSectionHom_isIso_on_own_chart
      (R := R) j i 1
    infer_instance
  have hw := restrict_whiskerLeft_isIso (coordinateOpen (R := R) i)
    (coordinateHyperplaneTwist (R := R) j a) _ hs
  let := hw
  change IsIso (F.map (coordinateMul j i a))
  unfold coordinateMul
  rw [F.map_comp, F.map_comp]
  infer_instance

/-- The actual coordinate multiplication on the original module twist. -/
def moduleCoordinateMul (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j i : σ) (a : ℤ) :
    M ⊗ coordinateHyperplaneTwist (R := R) j a ⟶
      M ⊗ coordinateHyperplaneTwist (R := R) j (a + 1) :=
  M ◁ coordinateMul j i a

/-- Tensoring by any module preserves the coordinate chart isomorphism;
no quasicoherence, finite-type or flatness assumption is needed. -/
theorem moduleCoordinateMul_isIso_on_own_chart
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (j i : σ) (a : ℤ) :
    IsIso ((restrictFunctor (coordinateOpen (R := R) i).ι).map
      (moduleCoordinateMul M j i a)) :=
  restrict_whiskerLeft_isIso (coordinateOpen (R := R) i) M _
    (coordinateMul_isIso_on_own_chart j i a)

/-- Sum all original coordinate multiplications on the module twist. -/
def coordinateEvaluation (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j : σ) (a : ℤ) :
    (∐ fun _ : ULift.{u} σ => M ⊗ coordinateHyperplaneTwist (R := R) j a) ⟶
      M ⊗ coordinateHyperplaneTwist (R := R) j (a + 1) :=
  Sigma.desc (fun i : ULift.{u} σ => moduleCoordinateMul M j i.down a)

/-- The actual coordinate evaluation is an epimorphism in every integer degree,
for every original module. The cover and local epimorphisms are derived. -/
theorem coordinateEvaluation_epi
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) (a : ℤ) :
    Epi (coordinateEvaluation M j a) := by
  apply Scheme.Modules.epi_of_restrictFunctor_map_epi_of_iSup_eq_top
    (fun i : σ => coordinateOpen (R := R) i) (iSup_coordinateOpen_eq_top (R := R))
  intro i
  let F := restrictFunctor (coordinateOpen (R := R) i).ι
  let := moduleCoordinateMul_isIso_on_own_chart M j i a
  have hfac : F.map (Sigma.ι
      (fun _ : ULift.{u} σ => M ⊗ coordinateHyperplaneTwist (R := R) j a)
      (ULift.up i)) ≫ F.map (coordinateEvaluation M j a) =
      F.map (moduleCoordinateMul M j i a) := by
    rw [← F.map_comp]
    simp only [coordinateEvaluation, Sigma.ι_desc]
  exact epi_of_epi_fac hfac

end EnvelopeProperty.ProjectiveCoordinateMultiplication
