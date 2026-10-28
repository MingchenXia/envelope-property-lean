import EnvelopeProperty.AlgGeom.IntegralLineImageModules
import EnvelopeProperty.AlgGeom.SchemeGeneratingSectionsUnit
import EnvelopeProperty.AlgGeom.ProjectiveTwistGlobalGeneration

/-! # Genuine nonzero original sections from actual projective generation -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
open Scheme.Modules MvPolynomial
universe u
namespace EnvelopeProperty.SchemeLineNonzeroGenerators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra

/-- An original line on a nonempty original scheme is genuinely nonzero. -/
theorem id_ne_zero {X : Scheme.{u}} [Nonempty X] (M : X.Modules) (hM : IsInvertible M) :
    (𝟙 M : M ⟶ M) ≠ 0 := by
  intro hz
  let x : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨U, hxU, ⟨e⟩⟩ := IntegralLineImageModules.exists_affine_frame M hM x
  let : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  have hlocal : (𝟙 (M.over U.1) : M.over U.1 ⟶ M.over U.1) = 0 := by
    have h := congrArg (fun q => (SheafOfModules.overFunctor X.ringCatSheaf U.1).map q) hz
    change (𝟙 (M.over U.1) : M.over U.1 ⟶ M.over U.1) = 0 at h
    exact h
  have hunit : (𝟙 (SheafOfModules.unit (X.ringCatSheaf.over U.1)) :
      SheafOfModules.unit (X.ringCatSheaf.over U.1) ⟶ _) = 0 := by
    calc
      _ = e.inv ≫ (𝟙 (M.over U.1)) ≫ e.hom := by simp
      _ = 0 := by rw [hlocal]; simp
  have hc := congrArg (fun q => q.val.app (op (Over.mk (𝟙 U.1))) (1 : Γ(X, U))) hunit
  change (1 : Γ(X, U)) = 0 at hc
  exact one_ne_zero hc

/-- EVERY genuine generating family of an original line on a nonempty
original scheme contains an ACTUAL nonzero original global section. -/
theorem exists_generatorHom_ne_zero {X : Scheme.{u}} [Nonempty X]
    (M : X.Modules) (hM : IsInvertible M) (G : M.GeneratingSections) :
    ∃ i : G.I, SchemeGeneratingSectionsUnit.generatorHom G i ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hp : G.π = 0 := by
    apply Sigma.hom_ext
    intro i
    exact (h i).trans comp_zero.symm
  have hi : (𝟙 M : M ⟶ M) = 0 := by
    apply G.epi.left_cancellation
    exact (Category.comp_id G.π).trans (hp.trans comp_zero.symm)
  exact id_ne_zero M hM hi

/-- Actual global generation DERIVES an original nonzero whole section map. -/
theorem exists_section_ne_zero {X : Scheme.{u}} [Nonempty X]
    (M : X.Modules) (hM : IsInvertible M) (G : M.GeneratingSections) :
    ∃ s : unitObj X ⟶ M, s ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_generatorHom_ne_zero M hM G
  exact ⟨SchemeGeneratingSectionsUnit.generatorHom G i, hi⟩

/-- The SAME actual pulled projective twist has actual nonzero sections
for EVERY nonnegative degree, derived from genuine coordinate generation. -/
theorem exists_pullback_twist_section_ne_zero {R : Type u} [CommRing R]
    {σ : Type} [Fintype σ] {X : Scheme.{u}} [Nonempty X]
    (i : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (d : ℕ) :
    ∃ s : unitObj X ⟶ (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) j (d : ℤ)), s ≠ 0 := by
  let L := coordinateHyperplaneTwist (R := R) j (d : ℤ)
  have hL : IsInvertible ((Scheme.Modules.pullback i).obj L) :=
    (coordinateHyperplaneTwist_isInvertible j (d : ℤ)).pullback i
  exact exists_section_ne_zero _ hL (ClosedProjectiveGlobalGeneration.pullback_generatingSections i
    (ProjectiveTwistGlobalGeneration.generatingSections (R := R) j d))

/-- Eventual projective generation DERIVES actual nonzero global sections
of every sufficiently large twist of ANY SAME original invertible line. -/
theorem exists_eventual_twist_section_ne_zero {R : Type u} [CommRing R]
    {σ : Type} [Fintype σ] {X : Scheme.{u}} [Nonempty X]
    (i : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion i]
    (M : X.Modules) (hM : IsInvertible M) (j : σ) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ s : unitObj X ⟶ M ⊗ (Scheme.Modules.pullback i).obj
        (coordinateHyperplaneTwist (R := R) j (d : ℤ)), s ≠ 0 := by
  let : M.IsQuasicoherent := hM.isQuasicoherent
  let : M.IsFinitePresentation := hM.isFinitePresentation
  let : M.IsFiniteType := inferInstance
  obtain ⟨N, hN⟩ := ClosedProjectiveGlobalGeneration.exists_eventual_generatingSections i M j
  refine ⟨N, fun d hd => ?_⟩
  obtain ⟨G, _⟩ := hN d hd
  let B := (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) j (d : ℤ))
  have hB : IsInvertible B := (coordinateHyperplaneTwist_isInvertible j (d : ℤ)).pullback i
  have hT : IsInvertible (M ⊗ B) :=
    (hM.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso M B)
  exact exists_section_ne_zero (M ⊗ B) hT G

end EnvelopeProperty.SchemeLineNonzeroGenerators
