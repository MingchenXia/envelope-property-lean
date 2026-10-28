import EnvelopeProperty.Char0.NadelClearedTwist
import EnvelopeProperty.Char0.MultiplierUniformGenerationRegularity
import EnvelopeProperty.Char0.MultiplierUniformGenerationBuffer

/-! # One actual projective twist generates every original multiplier module

The only unproved input is the explicitly supplied relative ample Nadel
vanishing proposition. Every finite generating family below is constructed.
The canonical line is over the original total field structure, even over k[t].
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open Scheme.Modules MvPolynomial
noncomputable section
universe u

namespace EnvelopeProperty.Char0.MultiplierUniformGeneration
open CanonicalGeometry NadelClearedTwist
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
  MvPolynomial.gradedAlgebra

variable {k R : Type u} [Field k] [CharZero k] [CommRing R]
  [Algebra k R] [Algebra.FiniteType k R]
  {X : Scheme.{u}} [IsIntegral X] {N : ℕ}

/-- The original negative regularity twists vanish for EVERY original m,
including zero, with the same total canonical/hyperplane buffer. -/
theorem subsingleton_H_negativeTwist
    (hNadel : RelativeAmpleNadelVanishingInput k)
    (p : X ⟶ Spec (.of k)) [Smooth p] (π : X ⟶ Spec (.of R))
    (hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = p)
    (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) [IsClosedImmersion i]
    (hbase : i ≫ homogeneousProjπ (R := R) (σ := Fin (N + 1)) = π)
    (n : ℕ) (hn : SmoothOfRelativeDimension n p)
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (L : X.Modules) (hL : IsInvertible L) (m a : ℕ) (ha : 0 < a)
    (hG : ∃ G : (I.toModules ⊗ bundleTensorPower L a).GeneratingSections, G.IsFiniteType)
    (q : ℕ) (hq : 0 < q) (hqN : q < N + 1) :
    Subsingleton (CategoryTheory.Sheaf.H
      (nadelTwistedModule p n I hI ((m : ℚ) / a)
        (line (hyperplane i) L (N + 1) m) ⊗
        (pullback i).obj (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (-(q : ℤ)))).sheaf q) := by
  cases q with
  | zero => omega
  | succ q =>
    have hv := regularityLine_vanishing hNadel p π hπ i hbase n hn I hI L hL m a ha hG
      (q + 1) hqN q
    exact MultiplierUniformGenerationRegularity.subsingleton_H_of_iso
      (nadelNegativeTwistIso p n I hI ((m : ℚ) / a) i L m (q + 1) (Nat.le_of_lt hqN))
      (q + 1) hv

/-- A SAME fixed canonical-hyperplane buffer constructs finite generators
for ALL original ideal-power multiplier modules, over any affine finite-type
base. The final global generation conclusion is never an input. -/
theorem exists_generatingSections
    (hNadel : RelativeAmpleNadelVanishingInput k)
    (p : X ⟶ Spec (.of k)) [Smooth p] (π : X ⟶ Spec (.of R))
    (hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = p)
    (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) [IsClosedImmersion i]
    (hbase : i ≫ homogeneousProjπ (R := R) (σ := Fin (N + 1)) = π)
    (n : ℕ) (hn : SmoothOfRelativeDimension n p)
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (L : X.Modules) (hL : IsInvertible L) (m a : ℕ) (ha : 0 < a)
    (hG : ∃ G : (I.toModules ⊗ bundleTensorPower L a).GeneratingSections, G.IsFiniteType) :
    ∃ G : (nadelTwistedModule p n I hI ((m : ℚ) / a)
      (line (hyperplane i) L (N + 1) m)).GeneratingSections, G.IsFiniteType := by
  let : SmoothOfRelativeDimension n p := hn
  have hH : IsInvertible (hyperplane i) := (hyperplane_isVeryAmple i).isInvertible
  exact MultiplierUniformGenerationRegularity.exists_generatingSections_of_regularity
    p n i I hI ((m : ℚ) / a) (line (hyperplane i) L (N + 1) m)
    (line_isInvertible (hyperplane i) L hH hL (N + 1) m)
    (fun q hq hqN => subsingleton_H_negativeTwist hNadel p π hπ i hbase n hn
      I hI L hL m a ha hG q hq hqN)

/-- One pure hyperplane exponent is selected BEFORE every varying original
line, ideal, denominator and multiplier index. The inverse-canonical buffer
is chosen once by actual Serre generation and is then cancelled internally. -/
theorem exists_uniform_pure_power_generatingSections
    (hNadel : RelativeAmpleNadelVanishingInput k)
    (p : X ⟶ Spec (.of k)) [Smooth p] (π : X ⟶ Spec (.of R))
    (hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = p)
    (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) [IsClosedImmersion i]
    (hbase : i ≫ homogeneousProjπ (R := R) (σ := Fin (N + 1)) = π)
    (n : ℕ) (hn : SmoothOfRelativeDimension n p) :
    ∃ s : ℕ, ∀ (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
      (L : X.Modules) (_hL : IsInvertible L) (m a : ℕ) (_ha : 0 < a),
      (∃ G : (I.toModules ⊗ bundleTensorPower L a).GeneratingSections, G.IsFiniteType) →
      ∃ G : ((bundleTensorPower (hyperplane i) (N + 1 + s) ⊗ bundleTensorPower L m) ⊗
        (schemeMultiplierIdealSheaf p I hI ((m : ℚ) / a)).toModules).GeneratingSections,
        G.IsFiniteType := by
  let : SmoothOfRelativeDimension n p := hn
  have hH := hyperplane_isAmple_over i π hbase
  obtain ⟨s, Gs, hGs⟩ := MultiplierUniformGenerationBuffer.exists_fixed_inverse_canonical_buffer
    π p n (hyperplane i) hH
  refine ⟨s, fun I hI L hL m a ha hG => ?_⟩
  have hM := exists_generatingSections hNadel p π hπ i hbase n hn I hI L hL m a ha hG
  exact MultiplierUniformGenerationBuffer.exists_generatingSections_remove_canonical
    (canonicalLineSheaf p n) (hyperplane i) L
    (schemeMultiplierIdealSheaf p I hI ((m : ℚ) / a)).toModules
    (canonicalLineSheaf_isInvertible p n) hH.isInvertible (N + 1) s m hM ⟨Gs, hGs⟩

end EnvelopeProperty.Char0.MultiplierUniformGeneration
