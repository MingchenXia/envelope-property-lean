import EnvelopeProperty.Vanishing.SpecializationDerivedNatural
import Mathlib.RingTheory.Flat.Stability
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Actual coefficient restriction along the original ring isomorphism

This retains the literal original module actions and derives the hypotheses
needed by the constructed cochain specialization producer.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.SpecializationDerivedScalarCoefficients

variable {R A : Type u} [CommRing R] [CommRing A]

/-- Finite modules remain finite after restriction along an actual ring isomorphism. -/
theorem finite_restrictScalars (e : R ≃+* A) (M : ModuleCat.{u} A)
    [Module.Finite A M] :
    Module.Finite R ((ModuleCat.restrictScalars e.toRingHom).obj M) := by
  let : Algebra R A := e.toRingHom.toAlgebra
  let N := (ModuleCat.restrictScalars e.toRingHom).obj M
  let : Module A N := M.isModule
  let : Module.Finite A N := inferInstanceAs (Module.Finite A M)
  let : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module.Finite R A := Module.Finite.equiv
    (ModuleCat.restrictScalarsIsoOfEquiv e).symm.toLinearEquiv
  exact Module.Finite.trans A N

/-- Flat modules remain flat after restriction along an actual ring isomorphism. -/
theorem flat_restrictScalars (e : R ≃+* A) (M : ModuleCat.{u} A)
    [Module.Flat A M] :
    Module.Flat R ((ModuleCat.restrictScalars e.toRingHom).obj M) := by
  let : Algebra R A := e.toRingHom.toAlgebra
  let N := (ModuleCat.restrictScalars e.toRingHom).obj M
  let : Module A N := M.isModule
  let : Module.Flat A N := inferInstanceAs (Module.Flat A M)
  let : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module.Flat R A := Module.Flat.of_linearEquiv
    (ModuleCat.restrictScalarsIsoOfEquiv e).toLinearEquiv
  exact Module.Flat.trans R A N

/-- The actual coefficient-restricted cochain complex. -/
def restrictComplex (e : R ≃+* A) (K : CochainComplex (ModuleCat.{u} A) ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  ((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℕ)).obj K

/-- The coefficient-restricted original terms are flat for the literal original action. -/
theorem restrictComplex_X_flat (e : R ≃+* A)
    (K : CochainComplex (ModuleCat.{u} A) ℕ) [∀ n, Module.Flat A (K.X n)] (n : ℕ) :
    Module.Flat R ((restrictComplex e K).X n) := flat_restrictScalars e (K.X n)

/-- Native homology is transported by the actual coefficient equivalence. -/
def restrictComplexHomologyIso (e : R ≃+* A)
    (K : CochainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    (restrictComplex e K).homology n ≅
      (ModuleCat.restrictScalars e.toRingHom).obj (K.homology n) :=
  (K.sc n).mapHomologyIso (ModuleCat.restrictScalars e.toRingHom)

/-- The actual module carrier detects zero before and after coefficient restriction. -/
theorem restrictScalars_isZero_iff (e : R ≃+* A) (M : ModuleCat.{u} A) :
    IsZero ((ModuleCat.restrictScalars e.toRingHom).obj M) ↔ IsZero M := by
  constructor
  · intro h
    have hs : Subsingleton ((ModuleCat.restrictScalars e.toRingHom).obj M) :=
      ModuleCat.subsingleton_of_isZero h
    let : Subsingleton M := ⟨fun x y => hs.elim x y⟩
    exact ModuleCat.isZero_of_subsingleton M
  · exact (ModuleCat.restrictScalars e.toRingHom).map_isZero

/-- Zero native homology is exactly retained with the original ring action. -/
theorem restrictComplex_homology_isZero_iff (e : R ≃+* A)
    (K : CochainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    IsZero ((restrictComplex e K).homology n) ↔ IsZero (K.homology n) := by
  let eH := restrictComplexHomologyIso e K n
  constructor
  · intro h
    exact (restrictScalars_isZero_iff e (K.homology n)).mp (h.of_iso eH.symm)
  · intro h
    exact ((restrictScalars_isZero_iff e (K.homology n)).mpr h).of_iso eH

/-- Independently finite native homology remains finite over the literal original ring. -/
theorem restrictComplex_homology_finite (e : R ≃+* A)
    (K : CochainComplex (ModuleCat.{u} A) ℕ) [∀ n, Module.Finite A (K.homology n)]
    (n : ℕ) : Module.Finite R ((restrictComplex e K).homology n) := by
  let : Module.Finite R ((ModuleCat.restrictScalars e.toRingHom).obj (K.homology n)) :=
    finite_restrictScalars e (K.homology n)
  exact Module.Finite.equiv (restrictComplexHomologyIso e K n).symm.toLinearEquiv

/-- The original upper zero term remains zero under the actual coefficient functor. -/
theorem restrictComplex_X_isZero (e : R ≃+* A)
    (K : CochainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) (h : IsZero (K.X n)) :
    IsZero ((restrictComplex e K).X n) :=
  (ModuleCat.restrictScalars e.toRingHom).map_isZero h

end EnvelopeProperty.Vanishing.SpecializationDerivedScalarCoefficients
