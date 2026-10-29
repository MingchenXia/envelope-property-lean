/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumSupport

/-!
# Homogeneous supports of arbitrary graded seminorm spectra

Gradedness is expressed by the value of every homogeneous projection being
at most the original value. Its actual valuation kernel is homogeneous.
For an internally ℕ-graded commutative ring, relevant graded seminorms map
continuously and surjectively to Mathlib's projective spectrum. No coefficient
field or prescribed scalar seminorm is needed for this absolute construction.
-/

open scoped NNReal Topology
open Topology Classical

noncomputable section

namespace EnvelopeProperty.Berkovich

namespace Spectrum

section Grading

variable {ι σ A : Type*} [CommRing A] [DecidableEq ι] [AddMonoid ι]
    [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

/-- A seminorm is graded when each homogeneous projection has at most the original value. -/
def IsGraded (x : Spectrum A) : Prop := ∀ a i, x.val (GradedRing.proj 𝒜 i a) ≤ x.val a

/-- The actual prime kernel of a graded seminorm is homogeneous. -/
theorem supp_isHomogeneous (x : Spectrum A) (hx : IsGraded 𝒜 x) :
    x.val.supp.IsHomogeneous 𝒜 := by
  intro i a ha
  change x.val (GradedRing.proj 𝒜 i a) = 0
  exact le_zero_iff.1 ((hx a i).trans_eq ha)

/-- Bundle the valuation kernel with its proved homogeneous-ideal property. -/
def homogeneousSupport (x : Spectrum A) (hx : IsGraded 𝒜 x) : HomogeneousIdeal 𝒜 :=
  ⟨x.val.supp, supp_isHomogeneous 𝒜 x hx⟩

@[simp]
theorem homogeneousSupport_toIdeal (x : Spectrum A) (hx : IsGraded 𝒜 x) :
    (homogeneousSupport 𝒜 x hx).toIdeal = x.val.supp := rfl

/-- Prime-quotient points take value one outside the prime. -/
theorem primePoint_val_eq_one_of_not_mem (p : PrimeSpectrum A) {a : A} (ha : a ∉ p.asIdeal) :
    (primePoint p).val a = 1 := by
  change (1 : Valuation (A ⧸ p.asIdeal) ℝ≥0) (Ideal.Quotient.mk p.asIdeal a) = 1
  exact Valuation.one_apply_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.1 ha)

/-- Every evaluation of a prime-quotient point is at most one. -/
theorem primePoint_val_le_one (p : PrimeSpectrum A) (a : A) : (primePoint p).val a ≤ 1 := by
  by_cases ha : a ∈ p.asIdeal
  · rw [(primePoint_val_eq_zero_iff p a).2 ha]
    exact zero_le
  · rw [primePoint_val_eq_one_of_not_mem p ha]

/-- The trivial seminorm of a homogeneous prime quotient is graded. -/
theorem primePoint_isGraded (p : PrimeSpectrum A) (hp : p.asIdeal.IsHomogeneous 𝒜) :
    IsGraded 𝒜 (primePoint p) := by
  intro a i
  by_cases ha : a ∈ p.asIdeal
  · have hi : GradedRing.proj 𝒜 i a ∈ p.asIdeal := hp i ha
    rw [(primePoint_val_eq_zero_iff p a).2 ha,
      (primePoint_val_eq_zero_iff p _).2 hi]
  · rw [primePoint_val_eq_one_of_not_mem p ha]
    exact primePoint_val_le_one p _

end Grading

section Projective

variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A relevant graded seminorm defines its actual homogeneous prime projective support. -/
def projectiveSupport (x : Spectrum A) (hx : IsGraded 𝒜 x)
    (hrel : ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ x.val.supp) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := homogeneousSupport 𝒜 x hx
  isPrime := by change x.val.supp.IsPrime; infer_instance
  not_irrelevant_le := hrel

@[simp]
theorem projectiveSupport_toIdeal (x : Spectrum A) (hx : IsGraded 𝒜 x)
    (hrel : ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ x.val.supp) :
    (projectiveSupport 𝒜 x hx hrel).asHomogeneousIdeal.toIdeal = x.val.supp := rfl

end Projective

end Spectrum

/-- Real seminorms that are graded and whose kernels avoid the irrelevant ideal. -/
abbrev RelevantGradedSpectrum {σ A : Type*} [CommRing A] [SetLike σ A]
    [AddSubmonoidClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :=
  {x : Spectrum A // Spectrum.IsGraded 𝒜 x ∧
    ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ x.val.supp}

namespace RelevantGradedSpectrum

variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- The homogeneous prime support of a relevant graded seminorm. -/
def support (x : RelevantGradedSpectrum 𝒜) : ProjectiveSpectrum 𝒜 :=
  Spectrum.projectiveSupport 𝒜 x.1 x.2.1 x.2.2

@[simp]
theorem support_toIdeal (x : RelevantGradedSpectrum 𝒜) :
    (support x).asHomogeneousIdeal.toIdeal = x.1.val.supp := rfl

@[simp]
theorem mem_support (x : RelevantGradedSpectrum 𝒜) (a : A) :
    a ∈ (support x).asHomogeneousIdeal ↔ x.1.val a = 0 := Iff.rfl

/-- The homogeneous support map is continuous for the projective Zariski topology. -/
@[fun_prop]
theorem continuous_support : Continuous (support : RelevantGradedSpectrum 𝒜 → ProjectiveSpectrum 𝒜) := by
  rw [continuous_iff_isClosed]
  intro Z hZ
  obtain ⟨E, rfl⟩ := (ProjectiveSpectrum.isClosed_iff_zeroLocus 𝒜 Z).1 hZ
  have heq : support ⁻¹' ProjectiveSpectrum.zeroLocus 𝒜 E =
      ⋂ a ∈ E, {x : RelevantGradedSpectrum 𝒜 | x.1.val a = 0} := by
    ext x
    simp only [Set.mem_preimage, ProjectiveSpectrum.mem_zeroLocus, Set.subset_def,
      SetLike.mem_coe, mem_support, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [heq]
  exact isClosed_biInter fun a _ =>
    isClosed_eq ((Spectrum.continuous_abs a).comp continuous_subtype_val) continuous_const

/-- A relevant homogeneous prime has a genuine trivial prime-quotient seminorm above it. -/
def primePoint (p : ProjectiveSpectrum 𝒜) : RelevantGradedSpectrum 𝒜 :=
  ⟨Spectrum.primePoint ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩,
    Spectrum.primePoint_isGraded 𝒜 _ p.asHomogeneousIdeal.isHomogeneous,
    by
      rw [← Spectrum.support_asIdeal, Spectrum.support_primePoint,
        toIdeal_le_toIdeal_iff]
      exact p.not_irrelevant_le⟩

@[simp]
theorem support_primePoint (p : ProjectiveSpectrum 𝒜) : support (primePoint p) = p := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  exact congrArg PrimeSpectrum.asIdeal (Spectrum.support_primePoint
    (⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩ : PrimeSpectrum A))

/-- Every projective-spectrum prime is the support of a relevant graded seminorm. -/
theorem support_surjective : Function.Surjective
    (support : RelevantGradedSpectrum 𝒜 → ProjectiveSpectrum 𝒜) :=
  fun p => ⟨primePoint p, support_primePoint p⟩

end RelevantGradedSpectrum

end EnvelopeProperty.Berkovich
