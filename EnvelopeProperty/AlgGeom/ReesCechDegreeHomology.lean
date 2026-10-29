import EnvelopeProperty.AlgGeom.ReesCechDegreeComplex
import EnvelopeProperty.AlgGeom.FormalFunctionsDirectSum

/-! # Genuine original ideal-power decomposition on Rees Cech cohomology -/

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
open scoped DirectSum
noncomputable section
universe u

namespace EnvelopeProperty.FcReesCechDegreeHomology

open FcReesCechDegreeComplex

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
variable [X.IsSeparated] {ι : Type u} [LinearOrder ι] [Fintype ι]
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))

/-- Every actual differential, including the degree-zero incoming map and
all off-shape maps, retains each original ideal-power coordinate. -/
theorem graded_d_apply (n m : ℕ) (x : gradedTerm I f U hU n) (d : ℕ) :
    (show gradedTerm I f U hU m from ((gradedComplex I f U hU).d n m).hom x) d =
      ((degreeComplex I f U hU d).d n m).hom (x d) := by
  by_cases h : n + 1 = m
  · subst m
    simp only [gradedComplex, degreeComplex, CochainComplex.of_d]
    exact gradedDifferential_apply I f U hU n x d
  · rw [(gradedComplex I f U hU).shape n m h,
      (degreeComplex I f U hU d).shape n m h]
    rfl

/-- Every whole term has the genuine original direct-sum term structure. -/
def termIso (n : ℕ) :
    (gradedComplex I f U hU).X n ≅
      ModuleCat.of R (⨁ d : ℕ, (degreeComplex I f U hU d).X n) := by
  dsimp only [gradedComplex, degreeComplex, CochainComplex.of_X, gradedTerm]
  exact Iso.refl _

/-- The original homology short complex is literally the direct sum of
the actual original ideal-power homology short complexes. -/
def shortComplexIso (n : ℕ) :
    (gradedComplex I f U hU).sc n ≅
      FormalFunctionsDirectSum.directSum (fun d => (degreeComplex I f U hU d).sc n) := by
  refine ShortComplex.isoMk (termIso I f U hU _) (termIso I f U hU _) (termIso I f U hU _) ?_ ?_
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DirectSum.ext
    intro d
    exact (graded_d_apply I f U hU _ _ x d).symm
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DirectSum.ext
    intro d
    exact (graded_d_apply I f U hU _ _ x d).symm

/-- Actual Rees degree-complex cohomology is the direct sum of the genuine
original ideal-power cohomologies, at every cohomological degree. -/
def gradedHomologyIso (n : ℕ) :
    (gradedComplex I f U hU).homology n ≅
      ModuleCat.of R (⨁ d : ℕ, (degreeComplex I f U hU d).homology n) :=
  (ShortComplex.homologyFunctor (ModuleCat.{u} R)).mapIso (shortComplexIso I f U hU n) ≪≫
    FormalFunctionsDirectSum.homologyIso (fun d => (degreeComplex I f U hU d).sc n)

/-- The entire ACTUAL ordered structure-module Rees Cech cohomology,
restricted along the genuine original scalar map, has the actual
original ideal-power degree decomposition. -/
def orderedHomologyIso (n : ℕ) :
    (((ModuleCat.restrictScalars (baseScalar I)).mapHomologicalComplex (.up ℕ)).obj
      (orderedBaseCechComplex (FcReesFormalFamily.familyProjection I f)
        (unitObj (FcReesFormalFamily.family I f))
        (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j))).homology n ≅
      ModuleCat.of R (⨁ d : ℕ, (degreeComplex I f U hU d).homology n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).mapIso
      (orderedDegreeComplexIso I f U hU) ≪≫
    gradedHomologyIso I f U hU n

end EnvelopeProperty.FcReesCechDegreeHomology
