import EnvelopeProperty.Vanishing.NadelNefBigGlobalGenerators

/-! # Actual source Serre families with their exact canonical comap transport -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigGlobalSerreGenerators
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra

private theorem finiteType_of_finitePresentation {V : Scheme.{u}} (M : V.Modules)
    [hM : M.IsFinitePresentation] : M.IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  constructor
  refine ⟨q.localGeneratorsData.shrink, ?_⟩
  constructor
  intro i
  exact (hq.isFinite_presentation i.2.choose).isFiniteType_generators

theorem exists_eventual_controlled_generators {R : Type u} [CommRing R]
    {σ : Type} [Fintype σ] {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (j : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion j]
    (D : X.IdealSheafData) (f : Y ⟶ X) (i₀ : σ) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      let B := (pullback j).obj (coordinateHyperplaneTwist (R := R) i₀ (d : ℤ))
      let hB := (coordinateHyperplaneTwist_isInvertible (R := R) i₀ (d : ℤ)).pullback j
      ∃ G : (D.toModules ⊗ B).GeneratingSections, G.IsFiniteType ∧
        (NadelNefBigGlobalGenerators.comapGenerators D f B hB G).IsFiniteType := by
  let : D.toModules.IsQuasicoherent := D.isQuasicoherent_toModules
  let hFP : D.toModules.IsFinitePresentation := D.isFinitePresentation_toModules
  let : D.toModules.IsFiniteType := @finiteType_of_finitePresentation X D.toModules hFP
  obtain ⟨N, hN⟩ := ClosedProjectiveGlobalGeneration.exists_eventual_generatingSections j D.toModules i₀
  refine ⟨N, ?_⟩
  intro d hd
  obtain ⟨G, hG⟩ := hN d hd
  exact ⟨G, hG, NadelNefBigGlobalGenerators.generators_isFiniteType D f _ _ G (hG := hG)⟩
end EnvelopeProperty.Vanishing.NadelNefBigGlobalSerreGenerators
