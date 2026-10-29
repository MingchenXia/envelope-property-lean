/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.ClosedCharts
import EnvelopeProperty.Projective.PolynomialGrading
import EnvelopeProperty.Berkovich.Reduction
import EnvelopeProperty.Berkovich.SpectrumGrading

/-!
# Homogeneous prime supports of normalized projective seminorms

The actual prime kernel of a normalized graded seminorm is homogeneous and
does not contain the irrelevant ideal. This defines a continuous, surjective
map to Mathlib's projective spectrum of the polynomial ring with its total-degree
grading. It constructs genuine projective-spectrum points, without assuming a
scheme analytification or a structure-sheaf comparison.
-/

open scoped NNReal Topology
open Topology Classical

noncomputable section

namespace EnvelopeProperty.ProjBerk

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {n : ℕ}

/-- Normalized graded projective points are relevant graded points of the absolute spectrum. -/
def toRelevantGradedSpectrum (v : ProjBerk k n) :
    Berkovich.RelevantGradedSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) :=
  ⟨v.1.toSpectrum, by
    constructor
    · intro F d
      rw [proj_eq_homogeneousComponent]
      exact (isGraded_iff v.1).1 v.isGraded F d
    · intro h
      obtain ⟨j, hj⟩ := exists_val_X_eq_one v
      have hX := h (HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < (1 : ℕ))
        (MvPolynomial.isHomogeneous_X k j))
      change v.1.val (MvPolynomial.X j) = 0 at hX
      exact one_ne_zero (hj.symm.trans hX)⟩

@[fun_prop]
theorem continuous_toRelevantGradedSpectrum :
    Continuous (toRelevantGradedSpectrum : ProjBerk k n →
      Berkovich.RelevantGradedSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) :=
  (Berk.continuous_toSpectrum.comp continuous_val).subtype_mk _

/-- The genuine relevant homogeneous prime kernel of a normalized projective point. -/
def support (v : ProjBerk k n) :
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) :=
  Berkovich.RelevantGradedSpectrum.support (toRelevantGradedSpectrum v)

@[simp]
theorem support_toIdeal (v : ProjBerk k n) :
    (support v).asHomogeneousIdeal.toIdeal = v.1.val.supp := rfl

@[simp]
theorem mem_support (v : ProjBerk k n) (F : MvPolynomial (Fin (n + 1)) k) :
    F ∈ (support v).asHomogeneousIdeal ↔ v.1.val F = 0 := Iff.rfl

/-- The projective support map is continuous for the projective Zariski topology. -/
@[fun_prop]
theorem continuous_support : Continuous (support : ProjBerk k n →
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) :=
  Berkovich.RelevantGradedSpectrum.continuous_support.comp continuous_toRelevantGradedSpectrum

/-- Projective analytic evaluation zero loci are the inverse images of their Zariski loci. -/
theorem preimage_support_zeroLocus (J : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    (support : ProjBerk k n → _) ⁻¹'
      ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (J : Set _) =
        projectiveZeroLocus J := rfl

/-- Relevance of a polynomial homogeneous prime excludes at least one coordinate variable. -/
theorem exists_X_not_mem (p :
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) :
    ∃ j, MvPolynomial.X j ∉ p.asHomogeneousIdeal := by
  by_contra! h
  apply p.not_irrelevant_le
  change (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).toIdeal ≤
    p.asHomogeneousIdeal.toIdeal
  rw [irrelevant_eq_idealOfVars, MvPolynomial.idealOfVars, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact h j

/-- The trivial seminorm of a relevant homogeneous prime quotient is already graded
and normalized, so defines a projective-model point. -/
def homogeneousPrimePoint (p :
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) : ProjBerk k n :=
  ⟨Berk.primePoint ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩, by
    constructor
    · rw [isGraded_iff]
      intro F d
      have h := Berkovich.Spectrum.primePoint_isGraded
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
        (⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩ : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k))
        p.asHomogeneousIdeal.isHomogeneous F d
      rwa [proj_eq_homogeneousComponent] at h
    · apply le_antisymm
      · exact Finset.sup_le fun i _ => Berkovich.Spectrum.primePoint_val_le_one
          (⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩ : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k))
          (MvPolynomial.X i)
      · obtain ⟨j, hj⟩ := exists_X_not_mem p
        have hv : (Berk.primePoint (k := k)
            (⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩ : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k))).val
              (MvPolynomial.X j) = 1 :=
          Berkovich.Spectrum.primePoint_val_eq_one_of_not_mem
            (⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩ : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k)) hj
        rw [← hv]
        exact Finset.le_sup (f := fun i : Fin (n + 1) =>
            (Berk.primePoint (k := k)
              (⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩ : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k))).val
                (MvPolynomial.X i)) (Finset.mem_univ j)⟩

@[simp]
theorem support_homogeneousPrimePoint (p :
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) :
    support (homogeneousPrimePoint p) = p := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  exact congrArg PrimeSpectrum.asIdeal (Berk.support_primePoint (k := k)
    (⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩ : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k)))

/-- Every relevant homogeneous prime of the polynomial ring occurs as a projective analytic support. -/
theorem support_surjective : Function.Surjective (support : ProjBerk k n →
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) :=
  fun p => ⟨homogeneousPrimePoint p, support_homogeneousPrimePoint p⟩

end EnvelopeProperty.ProjBerk
