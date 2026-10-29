import EnvelopeProperty.AlgGeom.ClosedProjectiveGlobalGeneration
import EnvelopeProperty.AlgGeom.IdealModulePullbackEpimorphism

/-! # Actual globally generated geometric ideal-pullback polarizations -/
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules MvPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.IdealModulePullbackGlobalGeneration
attribute [local instance] Scheme.Modules.monoidalCategory
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The SAME original geometric ideal comap, twisted by the ACTUAL pulled
polynomial polarization, is globally generated for EVERY sufficiently large
twist. All generators and their free evaluation epimorphism are derived.
The original morphism f is arbitrary, including nonflat morphisms. -/
theorem exists_eventual_generatingSections {R : Type u} [CommRing R]
    {σ : Type} [Fintype σ] {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion i]
    (I : X.IdealSheafData) (f : Z ⟶ X) (j : σ) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ G : ((I.comap f).toModules ⊗ (pullback (f ≫ i)).obj
        (coordinateHyperplaneTwist (R := R) j (d : ℤ))).GeneratingSections,
        G.IsFiniteType := by
  let : I.toModules.IsQuasicoherent := I.isQuasicoherent_toModules
  let : I.toModules.IsFinitePresentation := I.isFinitePresentation_toModules
  obtain ⟨N, hN⟩ := ClosedProjectiveGlobalGeneration.exists_eventual_generatingSections
    i I.toModules j
  refine ⟨N, ?_⟩
  intro d hd
  obtain ⟨G, hG⟩ := hN d hd
  let : G.IsFiniteType := hG
  let L := coordinateHyperplaneTwist (R := R) j (d : ℤ)
  let A := (pullback i).obj L
  let B := (pullback f).obj A
  have hB : IsInvertible B :=
    ((coordinateHyperplaneTwist_isInvertible j (d : ℤ)).pullback i).pullback f
  let : (tensorRight B).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence B hB
  let p := I.toModulesComapPullbackMap f
  let : Epi p := I.toModulesComapPullbackMap_epi f
  let : (pullback f).Monoidal := pullbackMonoidal f
  have hp : Epi ((tensorRight B).map p) := inferInstance
  let e : (I.comap f).toModules ⊗ B ≅
      (I.comap f).toModules ⊗ (pullback (f ≫ i)).obj L :=
    Iso.refl _ ⊗ᵢ (pullbackComp f i).app L
  let q : (pullback f).obj (I.toModules ⊗ A) ⟶
      (I.comap f).toModules ⊗ (pullback (f ≫ i)).obj L :=
    (Functor.Monoidal.μIso (pullback f) I.toModules A).inv ≫
      (tensorRight B).map p ≫ e.hom
  have hq : Epi q := by
    let : Epi ((tensorRight B).map p) := hp
    exact CategoryTheory.epi_comp (Functor.Monoidal.μIso (pullback f) I.toModules A).inv
      ((tensorRight B).map p ≫ e.hom)
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections f G
  let : H.IsFiniteType :=
    ClosedProjectiveGlobalGeneration.pullback_generatingSections_isFiniteType f G
  let : Epi q := hq
  exact ⟨H.ofEpi q, inferInstance⟩

end EnvelopeProperty.IdealModulePullbackGlobalGeneration
