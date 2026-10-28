import EnvelopeProperty.AlgGeom.Canonical.CanonicalLineSheaf
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness
import EnvelopeProperty.Char0.SchemeMultiplierIdealSheaf

/-! # The explicit Nadel input for the characteristic-zero envelope proof

The input is a genuine relative ample ideal-power Nadel vanishing statement.
It contains no generation, asymptotic approximation, or envelope conclusion.
It is a proposition parameter, with no axiom and no global instance.

Relative ampleness is expressed by an actual positive cleared power and an
actual ample line. The canonical module is the top exterior cotangent module
over the original field, and the multiplier ideal is the original all-DVR ideal.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Char0

attribute [local instance] Scheme.Modules.monoidalCategory

/-- The SAME original canonical-twisted multiplier module. -/
def nadelTwistedModule {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [Smooth p]
    (n : ℕ) (I : X.IdealSheafData)
    (hI : I.stalkIdeal (genericPoint X) ≠ ⊥) (c : ℚ) (A : X.Modules) :
    X.Modules :=
  (CanonicalGeometry.canonicalLineSheaf p n ⊗ A) ⊗
    (schemeMultiplierIdealSheaf p I hI c).toModules

/-- Relative ample Nadel vanishing over an affine finite-type base.

The actual power identity says that `A - c B` is ample over the original
affine base: `d c = t` and `A^d = C ⊗ B^t`, with `C` actually ample.
The base can be the original field or the original polynomial ring `k[t]`.
Every consumer must construct this geometry and this identity internally.
-/
def RelativeAmpleNadelVanishingInput (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ {R : Type u} [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [Smooth p]
    (π : X ⟶ Spec (.of R))
    (_hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = p)
    (_hp : IsProjectiveFactorization π)
    (n : ℕ) (_hn : SmoothOfRelativeDimension n p)
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (A B : X.Modules) (_hA : IsInvertible A) (_hB : IsInvertible B)
    (_hG : ∃ G : (I.toModules ⊗ B).GeneratingSections, G.IsFiniteType)
    (c : ℚ) (_hc : 0 ≤ c) (d t : ℕ) (_hd : 0 < d)
    (_hdt : (d : ℚ) * c = (t : ℚ))
    (C : X.Modules) (_hC : SchemeLineAmpleness.IsAmple π C)
    (_e : Nonempty (CanonicalGeometry.bundleTensorPower A d ≅
      C ⊗ CanonicalGeometry.bundleTensorPower B t))
    (q : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (nadelTwistedModule p n I hI c A)) (q + 1))

end EnvelopeProperty.Char0
