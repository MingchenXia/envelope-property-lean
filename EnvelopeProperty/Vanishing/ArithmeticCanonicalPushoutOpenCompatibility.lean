import EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutOpenGeometry

/-! # Actual local invertibility of the original global arithmetic differential

The whole universal-square equality and the original-map identification are
proved separately. This module consumes those proved maps on the literal
native arithmetic fibres, without a global comparison certificate.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutOpenCompatibility

open ArithmeticCanonicalGlobal ArithmeticCanonicalGlobalBaseChange

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    {X V : Scheme.{u}} (f : X ⟶ Spec (.of R)) (g : V ⟶ X)

/-- The actual local fibre differential gives invertibility of the actual
open pullback of the same original global fibre differential. -/
theorem isIso_pullback_exteriorPullbackMap [IsOpenImmersion g] (q : ℕ)
    [IsIso (exteriorPullbackMap S (g ≫ f) q)] :
    IsIso ((Scheme.Modules.pullback (fiberMap S f g)).map (exteriorPullbackMap S f q)) := by
  have : IsIso (ArithmeticCanonicalPushoutDifferential.exteriorPullbackMap
      (CommRingCat.ofHom (algebraMap R S)) (g ≫ f) (fiberStructure S (g ≫ f))
      (fiberProjection S (g ≫ f))
      (ArithmeticCanonicalPushoutDifferential.fiberCoefficientSquare S (g ≫ f)) q) :=
    ArithmeticCanonicalPushoutDifferential.isIso_of_eq
      (ArithmeticCanonicalPushoutDifferential.exteriorPullbackMap_baseChange S (g ≫ f) q).symm
  have := ArithmeticCanonicalPushoutDifferential.isIso_pullback_exteriorPullbackMap_of_local
    (CommRingCat.ofHom (algebraMap R S)) f (fiberStructure S f) (g ≫ f)
    (fiberStructure S (g ≫ f)) (fiberProjection S f) (fiberMap S f g) g
    (fiberProjection S (g ≫ f))
    (ArithmeticCanonicalPushoutDifferential.fiberCoefficientSquare S f)
    (fiberOpenCoefficientSquare S f g)
    (ArithmeticCanonicalPushoutDifferential.openCoefficientSquare f g)
    (ArithmeticCanonicalPushoutDifferential.fiberCoefficientSquare S (g ≫ f))
    (fiberMap_fst S f g) (fiberMap_snd S f g) rfl q
  exact ArithmeticCanonicalPushoutDifferential.isIso_of_eq
    (congrArg ((Scheme.Modules.pullback (fiberMap S f g)).map)
      (ArithmeticCanonicalPushoutDifferential.exteriorPullbackMap_baseChange S f q))

end EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutOpenCompatibility
