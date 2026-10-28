/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.ActualReesTree
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Monomial
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Centers
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.IsoLocus
import Hironaka.Scheme.Snc.EmptyFamily
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Actual affine principalization inputs and their Rees trees

The actual BP input is built from a nonzero ideal on a smooth affine domain, with
the empty initial boundary. Its nonempty isomorphism open is proved internally.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Scheme.BlowUpSequence
open scoped Classical

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-- A genuine nonzero ideal in an affine domain is nonzero in every actual stalk. -/
theorem specIdealSheaf_isNonzeroEverywhere (I : Ideal R) (hI : I ≠ ⊥) :
    (specIdealSheaf I).IsNonzeroEverywhere := by
  obtain ⟨a, ha, ha0⟩ := I.ne_bot_iff.mp hI
  intro x hx
  let U : (Spec (.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let s : Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).inv a
  have hs : s ∈ (specIdealSheaf I).ideal U := by
    change s ∈ (specIdealSheaf I).ideal ⟨⊤, isAffineOpen_top _⟩
    rw [specIdealSheaf_ideal_top]
    exact Ideal.mem_map_of_mem _ ha
  have hmem : (Spec (.of R)).presheaf.germ ⊤ x (show x ∈ U.1 from Set.mem_univ _) s ∈
      (specIdealSheaf I).stalkIdeal x :=
    (specIdealSheaf I).map_germ_le_stalkIdeal U (Set.mem_univ _)
      (Ideal.mem_map_of_mem _ hs)
  rw [hx] at hmem
  have hs0 : s = 0 := (germ_injective_of_isIntegral (Spec (.of R)) x
    (show x ∈ U.1 from Set.mem_univ _))
    ((Ideal.mem_bot.mp hmem).trans (map_zero _).symm)
  apply ha0
  have ha' := congrArg (Scheme.ΓSpecIso (.of R)).hom hs0
  simpa only [s, Iso.inv_hom_id_apply, map_zero] using ha'

/-- The complement of a nonzero affine centre contains the actual zero prime. -/
theorem nonempty_compl_support_specIdealSheaf (I : Ideal R) (hI : I ≠ ⊥) :
    (((specIdealSheaf I).support.compl : (Spec (.of R)).Opens) :
      Set (Spec (.of R))).Nonempty := by
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  change (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∉
    ((specIdealSheaf I).support : Set (Spec (.of R)))
  rw [support_specIdealSheaf]
  exact fun h => hI (le_bot_iff.mp h)

variable {k : Type u} [Field k]

/-- The actual smooth affine domain, its actual nonzero ideal sheaf and the empty boundary
form a genuine input of algebraic principalization. -/
def affinePrincipalizationTriple (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (I : Ideal R) (hI : I ≠ ⊥) : Triple k := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  exact
    { X := .ofHom f inferInstance inferInstance
      smoothOfRelativeDimension := ⟨n, by change SmoothOfRelativeDimension n f; infer_instance⟩
      I := specIdealSheaf I
      isNonzeroEverywhere := specIdealSheaf_isNonzeroEverywhere I hI
      E := Scheme.DivisorFamily.empty _
      isSnc := isSnc_empty_of_smooth f }

/-- The actual BP sequence for the constructed triple is isomorphic off the original ideal. -/
theorem affinePrincipalization_isIso_restrict [CharZero k]
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    IsIso ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ∣_
      (specIdealSheaf I).support.compl) := by
  have h := Hironaka.Sequence.BP_isIso_restrict (affinePrincipalizationTriple f n I hI)
  have hempty : (Scheme.DivisorFamily.empty (Spec (.of R))).singularLocus = ⊥ := by
    simp [Scheme.DivisorFamily.singularLocus, Scheme.DivisorFamily.empty]
  change IsIso ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ∣_
    ((specIdealSheaf I).support ⊔
      (Scheme.DivisorFamily.empty (Spec (.of R))).singularLocus).compl) at h
  rw [hempty, sup_bot_eq] at h
  exact h

/-- The actual total transform of the original nonzero ideal is an SNC divisor ideal. -/
theorem affinePrincipalization_isIdealOfSncDivisor [CharZero k]
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    ((specIdealSheaf I).comap
      (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite).IsIdealOfSncDivisor :=
  Hironaka.Sequence.BP_isIdealOfSncDivisor (affinePrincipalizationTriple f n I hI)

/-- Smooth centres preserve the original pure dimension throughout the actual BP sequence. -/
theorem affinePrincipalization_smoothOfRelativeDimension [CharZero k]
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    SmoothOfRelativeDimension n
      ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) := by
  have hs : (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).IsSmooth f := by
    intro i
    exact (Hironaka.Sequence.BP_center_smooth_hasSncWith (affinePrincipalizationTriple f n I hI) i).1
  exact IsSmooth.smoothOfRelativeDimension_stageMap (f := f) (n := n) hs (Fin.last _)

variable {K : Type u} [Field K] [Algebra k K]

/-- Actual algebraic principalization, with its internally proved nonempty open, produces the
actual finite Rees cover, smooth final scheme and SNC total transform. -/
theorem exists_affinePrincipalization_rees_cover [CharZero k]
    (C : Subalgebra k K) (hC : C.FG) (f : Spec (.of C) ⟶ Spec (.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f] (I : Ideal C) (hI : I ≠ ⊥) :
    let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)
    ∃ (T : ReesChartTree k K C)
      (φ : (i : T.LeafIndex) → Spec (.of (T.leafAlgebra i)) ⟶ S.last),
      (∀ i, IsOpenImmersion (φ i)) ∧
      (∀ i, φ i ≫ S.composite =
        subalgebraSpecMap (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) ∧
      (∀ x : S.last, ∃ (i : T.LeafIndex) (y : Spec (.of (T.leafAlgebra i))), φ i y = x) ∧
      SmoothOfRelativeDimension n (S.composite ≫ f) ∧
      ((specIdealSheaf I).comap S.composite).IsIdealOfSncDivisor := by
  let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)
  let U := (specIdealSheaf I).support.compl
  have hiso : IsIso (S.composite ∣_ U) := affinePrincipalization_isIso_restrict f n I hI
  obtain ⟨T, φ, hopen, htriangle, hcover⟩ := @exists_actual_rees_cover k K _ _ _ _ C hC S U
    (nonempty_compl_support_specIdealSheaf I hI) hiso
  exact ⟨T, φ, hopen, htriangle, hcover,
    affinePrincipalization_smoothOfRelativeDimension f n I hI,
    affinePrincipalization_isIdealOfSncDivisor f n I hI⟩

end EnvelopeProperty.Char0
