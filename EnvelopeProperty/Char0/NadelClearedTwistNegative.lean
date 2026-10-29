import EnvelopeProperty.Char0.NadelClearedTwistProjective
import EnvelopeProperty.Char0.AmpleNadelInput

/-! # The literal negative regularity twist is the SAME original Nadel module

The original canonical sheaf, line power and all-DVR multiplier ideal are
unchanged. Every comparison is actual native coherence or projective twist
addition, in the direction used by the original CM cohomology consumer.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules MvPolynomial
universe u
namespace EnvelopeProperty.Char0.NadelClearedTwist
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
  MvPolynomial.gradedAlgebra

/-- Actual native coherence moves the SAME last factor past the SAME middle one. -/
def tensorSwapRightIso {X : Scheme.{u}} (A B C : X.Modules) :
    (A ⊗ B) ⊗ C ≅ (A ⊗ C) ⊗ B :=
  (α_ A B C) ≪≫ (Iso.refl A ⊗ᵢ β_ B C) ≪≫ (α_ A C B).symm

def lineNegativeTwistIso {R : Type u} [CommRing R] {N : ℕ} {X : Scheme.{u}}
    (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) (L : X.Modules)
    (m q : ℕ) (hq : q ≤ N + 1) :
    line (hyperplane i) L (N + 1) m ⊗
        (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (-(q : ℤ))) ≅
      line (hyperplane i) L (N + 1 - q) m :=
  tensorSwapRightIso (bundleTensorPower (hyperplane i) (N + 1)) (bundleTensorPower L m) _ ≪≫
    (negativeHyperplaneIso i q hq ⊗ᵢ Iso.refl _)

/-- FROM the literal ordinary target tensor the original negative projective
twist TO the SAME native Nadel module at the positive remaining H power.
No desired negative-twist, ideal or canonical comparison is a premise. -/
def nadelNegativeTwistIso {k : Type u} [Field k] [CharZero k]
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X] {N : ℕ}
    (f : X ⟶ Spec (.of k)) [Smooth f] (n : ℕ)
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥) (c : ℚ)
    (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) (L : X.Modules)
    (m q : ℕ) (hq : q ≤ N + 1) :
    nadelTwistedModule f n I hI c (line (hyperplane i) L (N + 1) m) ⊗
        (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (-(q : ℤ))) ≅
      nadelTwistedModule f n I hI c (line (hyperplane i) L (N + 1 - q) m) := by
  let Ω := canonicalLineSheaf f n
  let A := line (hyperplane i) L (N + 1) m
  let J := (schemeMultiplierIdealSheaf f I hI c).toModules
  let T := (Scheme.Modules.pullback i).obj
    (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (-(q : ℤ)))
  exact tensorSwapRightIso (Ω ⊗ A) J T ≪≫
    (((α_ Ω A T) ≪≫ (Iso.refl Ω ⊗ᵢ lineNegativeTwistIso i L m q hq)) ⊗ᵢ Iso.refl J)

end EnvelopeProperty.Char0.NadelClearedTwist
