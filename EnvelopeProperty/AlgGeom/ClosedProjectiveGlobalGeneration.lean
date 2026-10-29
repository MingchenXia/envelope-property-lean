import EnvelopeProperty.AlgGeom.CoherentProjectiveGlobalGeneration
import ModularCurves.ForMathlib.PullbackTensorGeneral
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Genuine Serre generation on the same original closed projective scheme -/
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules MvPolynomial Topology
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ClosedProjectiveGlobalGeneration
attribute [local instance] Scheme.Modules.monoidalCategory
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Original topological induction makes the ACTUAL module pushforward faithful. -/
theorem pushforward_faithful_of_isInducing {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsInducing f) : (pushforward f).Faithful where
  map_injective := by
    intro M N a b hab
    apply Scheme.Modules.hom_ext
    intro U
    obtain ⟨V, hV, hVU⟩ := hf.isOpen_iff.mp U.isOpen
    have he : f ⁻¹ᵁ (⟨V, hV⟩ : Y.Opens) = U := TopologicalSpace.Opens.ext hVU
    have h := congrArg (fun q => q.app (⟨V, hV⟩ : Y.Opens)) hab
    change a.app (f ⁻¹ᵁ (⟨V, hV⟩ : Y.Opens)) =
      b.app (f ⁻¹ᵁ (⟨V, hV⟩ : Y.Opens)) at h
    exact Eq.mp (congrArg (fun W => a.app W = b.app W) he) h

/-- The TRUE original pullback-pushforward counit is epic for every original
module under a topologically inducing scheme morphism. -/
theorem counit_epi_of_isInducing {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsInducing f) (M : X.Modules) :
    Epi ((pullbackPushforwardAdjunction f).counit.app M) := by
  let : (pushforward f).Faithful := pushforward_faithful_of_isInducing f hf
  infer_instance

/-- Genuine pullback of the original generating family, retaining its ACTUAL
index set and original free evaluation map. -/
def pullback_generatingSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    {N : Y.Modules} (G : N.GeneratingSections) :
    ((pullback f).obj N).GeneratingSections := by
  let : CategoryTheory.Limits.PreservesColimitsOfSize.{u,u} (pullback f) :=
    (pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  exact G.map (pullback f) (pullbackUnitIso f).symm

/-- The same original finite index set makes the actual pulled-back family finite. -/
theorem pullback_generatingSections_isFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    {N : Y.Modules} (G : N.GeneratingSections) [G.IsFiniteType] :
    (pullback_generatingSections f G).IsFiniteType := by
  unfold pullback_generatingSections
  infer_instance

/-- EVERY sufficiently large original pulled-back polynomial projective twist
of the SAME original finite-type quasicoherent module on an ACTUAL closed
projective subscheme has genuine finite global generating sections. -/
theorem exists_eventual_generatingSections {R : Type u} [CommRing R]
    {σ : Type} [Fintype σ] {X : Scheme.{u}}
    (i : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion i]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ G : (M ⊗ (pullback i).obj
        (coordinateHyperplaneTwist (R := R) j (d : ℤ))).GeneratingSections,
        G.IsFiniteType := by
  let P := Proj (homogeneousSubmodule σ R)
  let Q := (pushforward i).obj M
  let : Q.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom i
  let : Q.IsFiniteType := isFiniteType_pushforward_of_isClosedImmersion i
  obtain ⟨N, hN⟩ := CoherentProjectiveGlobalGeneration.exists_eventual_generatingSections Q j
  refine ⟨N, ?_⟩
  intro d hd
  obtain ⟨G, hG⟩ := hN d hd
  let : G.IsFiniteType := hG
  let L := coordinateHyperplaneTwist (R := R) j (d : ℤ)
  let B := (pullback i).obj L
  have hB : IsInvertible B :=
    (coordinateHyperplaneTwist_isInvertible j (d : ℤ)).pullback i
  let : (tensorRight B).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence B hB
  let e := (pullbackPushforwardAdjunction i).counit.app M
  let : Epi e := counit_epi_of_isInducing i i.isClosedEmbedding.isInducing M
  let : (pullback i).Monoidal := pullbackMonoidal i
  have he : Epi ((tensorRight B).map e) := inferInstance
  let q : (pullback i).obj (Q ⊗ L) ⟶ M ⊗ B :=
    (Functor.Monoidal.μIso (pullback i) Q L).inv ≫ (tensorRight B).map e
  have hq : Epi q := by
    let : Epi ((tensorRight B).map e) := he
    exact CategoryTheory.epi_comp (Functor.Monoidal.μIso (pullback i) Q L).inv
      ((tensorRight B).map e)
  let H := pullback_generatingSections i G
  let : H.IsFiniteType := pullback_generatingSections_isFiniteType i G
  let : Epi q := hq
  exact ⟨H.ofEpi q, inferInstance⟩

end EnvelopeProperty.ClosedProjectiveGlobalGeneration
