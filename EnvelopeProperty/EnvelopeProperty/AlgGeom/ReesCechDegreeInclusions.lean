import EnvelopeProperty.AlgGeom.ReesCechDegreeHomology
import EnvelopeProperty.AlgGeom.FormalFunctionsDirectSumNaturality

/-! # Genuine original degree inclusions in actual Rees Cech cohomology -/

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
open scoped DirectSum
noncomputable section
universe u
namespace EnvelopeProperty.FcReesCechDegreeInclusions

open FcReesCechDegreeComplex

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
variable [X.IsSeparated] {ι : Type u} [LinearOrder ι] [Fintype ι]
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))

/-- Include each actual original ideal-power degree as its literal
summand in the whole original Rees degree cochain complex. -/
def degreeInclusion (d : ℕ) : degreeComplex I f U hU d ⟶ gradedComplex I f U hU where
  f n := by
    let : ∀ k : ℕ, Module R (degreeTerm I f U hU k n) :=
      fun k => (degreeTerm I f U hU k n).isModule
    exact ModuleCat.ofHom (DirectSum.lof R ℕ (fun k => degreeTerm I f U hU k n) d)
  comm' n m hnm := by
    have hm : n + 1 = m := hnm
    subst m
    let : ∀ k : ℕ, Module R (degreeTerm I f U hU k n) :=
      fun k => (degreeTerm I f U hU k n).isModule
    let : ∀ k : ℕ, Module R (degreeTerm I f U hU k (n + 1)) :=
      fun k => (degreeTerm I f U hU k (n + 1)).isModule
    simp only [gradedComplex, degreeComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DirectSum.ext
    intro k
    change (gradedDifferential I f U hU n).hom
        (DirectSum.lof R ℕ (fun j => degreeTerm I f U hU j n) d x) k =
      (DirectSum.lof R ℕ (fun j => degreeTerm I f U hU j (n + 1)) d
        ((degreeDifferential I f U hU d n).hom x)) k
    rw [gradedDifferential_apply]
    by_cases hk : k = d
    · subst k
      rw [DirectSum.lof_apply, DirectSum.lof_apply]
    · simp only [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hk, map_zero]

/-- At every cohomological degree, the associated actual homology short
complex map is exactly the original direct-sum summand inclusion. -/
theorem shortComplexInclusion (d n : ℕ) :
    (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n).map
        (degreeInclusion I f U hU d) ≫
      (FcReesCechDegreeHomology.shortComplexIso I f U hU n).hom =
    FormalFunctionsDirectSumNaturality.inclusion
      (fun j => (degreeComplex I f U hU j).sc n) d := by
  apply ShortComplex.Hom.ext
  · exact (FormalFunctionsDirectSumNaturality.inclusion_left (R := R)
      (fun j => (degreeComplex I f U hU j).sc n) d).symm
  · exact (FormalFunctionsDirectSumNaturality.inclusion_middle (R := R)
      (fun j => (degreeComplex I f U hU j).sc n) d).symm
  · exact (FormalFunctionsDirectSumNaturality.inclusion_right (R := R)
      (fun j => (degreeComplex I f U hU j).sc n) d).symm

private theorem comparison_assoc {C : Type*} [Category C]
    {A B D E : C} (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ D) (t : D ⟶ E) (z : A ⟶ E)
    (h : a ≫ b = c) (hc : c ≫ t = z) : a ≫ b ≫ t = z := by
  rw [← Category.assoc, h, hc]

/-- The genuine original cohomology decomposition preserves the ENTIRE
actual original ideal-power cohomology summand inclusion. -/
theorem homologyInclusion (d n : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).map
        (degreeInclusion I f U hU d) ≫
      (FcReesCechDegreeHomology.gradedHomologyIso I f U hU n).hom =
      ModuleCat.ofHom (DirectSum.lof R ℕ
        (fun j => (degreeComplex I f U hU j).homology n) d) := by
  have h := congrArg (fun a => ShortComplex.homologyMap a)
    (shortComplexInclusion I f U hU d n)
  have h' := (ShortComplex.homologyMap_comp _ _).symm.trans h
  exact comparison_assoc _ _ _ _ _ h'
    (FormalFunctionsDirectSumNaturality.inclusion_homology
      (fun j => (degreeComplex I f U hU j).sc n) d)

end EnvelopeProperty.FcReesCechDegreeInclusions
