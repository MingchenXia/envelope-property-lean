import EnvelopeProperty.Char0.NadelClearedTwistNegative

/-! # The actual regularity line consumes only the named ample Nadel input

The original projective factorization, hyperplane ampleness, positive
clearing, actual C and genuine power iso are ALL constructed internally.
No generation or target cohomology conclusion is supplied as an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules MvPolynomial
universe u
namespace EnvelopeProperty.Char0.NadelClearedTwist
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra

theorem regularityCleared_isAmple {R : Type u} [CommRing R] {N : ℕ}
    {X : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) [IsClosedImmersion i]
    (π : X ⟶ Spec (.of R))
    (hbase : i ≫ homogeneousProjπ (R := R) (σ := Fin (N + 1)) = π)
    (j p : ℕ) (hj : j < N + 1) (hp : 0 < p) :
    SchemeLineAmpleness.IsAmple π (clearedLine (hyperplane i) (N + 1 - j) p) :=
  clearedLine_isAmple π (hyperplane i) (hyperplane_isAmple_over i π hbase)
    (N + 1 - j) p (Nat.sub_pos_of_lt hj) hp

/-- The original finiteGG of I tensor L^p and the explicitly named relative
ample Nadel proposition imply the SAME native positive H vanishing. All
clearing, ampleness and projective geometry obligations are discharged
internally; no desired power iso or target vanishing is a consumer premise. -/
theorem regularityLine_vanishing {k : Type u} [Field k] [CharZero k]
    {R : Type u} [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    {X : Scheme.{u}} [IsIntegral X] {N : ℕ}
    (hNadel : RelativeAmpleNadelVanishingInput k)
    (f : X ⟶ Spec (.of k)) [Smooth f] (π : X ⟶ Spec (.of R))
    (hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f)
    (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) [IsClosedImmersion i]
    (hbase : i ≫ homogeneousProjπ (R := R) (σ := Fin (N + 1)) = π)
    (n : ℕ) (hn : SmoothOfRelativeDimension n f)
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (L : X.Modules) (hL : IsInvertible L) (m powerIndex : ℕ) (hp : 0 < powerIndex)
    (hG : ∃ G : (I.toModules ⊗ polarization L powerIndex).GeneratingSections, G.IsFiniteType)
    (j : ℕ) (hj : j < N + 1) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj
        (nadelTwistedModule f n I hI ((m : ℚ) / powerIndex)
          (line (hyperplane i) L (N + 1 - j) m))) (q + 1)) := by
  have hH := hyperplane_isAmple_over i π hbase
  have hi : IsClosedImmersion i := inferInstance
  have hproj : IsProjectiveFactorization π := ⟨N, i, hi, hbase⟩
  exact hNadel f π hπ hproj n hn I hI
    (line (hyperplane i) L (N + 1 - j) m) (polarization L powerIndex)
    (line_isInvertible (hyperplane i) L hH.isInvertible hL (N + 1 - j) m)
    (polarization_isInvertible L hL powerIndex) hG
    ((m : ℚ) / powerIndex) (coefficient_nonneg m powerIndex)
    powerIndex m hp (clearingCoefficient_eq m powerIndex hp)
    (clearedLine (hyperplane i) (N + 1 - j) powerIndex)
    (regularityCleared_isAmple i π hbase j powerIndex hj hp)
    ⟨clearingIso (hyperplane i) L (N + 1 - j) m powerIndex⟩ q

end EnvelopeProperty.Char0.NadelClearedTwist
