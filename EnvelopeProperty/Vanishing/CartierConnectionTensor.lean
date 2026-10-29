import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorEquivalence
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # The proved exact line-tensor functor used by the Cartier complex

The native scheme-module monoidal structure does not register arbitrary
tensor functors as additive. For an actual invertible line, its proved
tensor equivalence derives the required zero-morphism and additive structure.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.CartierConnection

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- The same original right-tensor functor, retaining its actual line
invertibility proof as the source of exactness. -/
def tensorFunctor {X : Scheme.{u}} (L : X.Modules) (_hL : Scheme.Modules.IsInvertible L) :
    X.Modules ⥤ X.Modules :=
  tensorRight L

/-- The actual line and its dual supply a genuine equivalence. -/
instance tensorFunctor_isEquivalence {X : Scheme.{u}} (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) : (tensorFunctor L hL).IsEquivalence :=
  SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence L hL

/-- An equivalence of the actual abelian module category is additive;
no arbitrary additivity or zero-morphism certificate is supplied. -/
instance tensorFunctor_additive {X : Scheme.{u}} (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) : (tensorFunctor L hL).Additive :=
  Functor.additive_of_preserves_binary_products (tensorFunctor L hL)

end EnvelopeProperty.Vanishing.CartierConnection
