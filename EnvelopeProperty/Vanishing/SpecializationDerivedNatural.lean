import EnvelopeProperty.Vanishing.SpecializationDerivedReversal
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Actual positive natural-cochain homology specialization

Extension by zero and all three positive-degree term comparisons are
constructed on the original complex before applying the reversal producer.
-/

open CategoryTheory CategoryTheory.Limits TensorProduct

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.SpecializationDerivedNatural

open SpecializationDerivedReplacementStep SpecializationDerivedReversal

variable {R : Type u} [CommRing R]

/-- The actual original natural cochain complex extended by zero. -/
def toInteger (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    CochainComplex (ModuleCat.{u} R) ℤ := K.extend ComplexShape.embeddingUpNat

/-- The actual extended terms remain flat, with negative terms zero. -/
theorem toInteger_X_flat (K : CochainComplex (ModuleCat.{u} R) ℕ)
    [∀ n, Module.Flat R (K.X n)] (i : ℤ) :
    Module.Flat R ((toInteger K).X i) := by
  by_cases hi : 0 ≤ i
  · have he : ComplexShape.embeddingUpNat.f i.toNat = i := by
      change (i.toNat : ℤ) = i
      exact Int.toNat_of_nonneg hi
    exact Module.Flat.of_linearEquiv (K.extendXIso ComplexShape.embeddingUpNat he).toLinearEquiv
  · have hz : IsZero ((toInteger K).X i) := K.isZero_extend_X
      ComplexShape.embeddingUpNat i (fun n hn => by change (n : ℤ) = i at hn; omega)
    let : Subsingleton ((toInteger K).X i) := ModuleCat.subsingleton_of_isZero hz
    infer_instance

/-- Native extended homology finiteness is derived from actual original homology
in nonnegative degrees and actual zero terms in negative degrees. -/
theorem toInteger_homology_finite (K : CochainComplex (ModuleCat.{u} R) ℕ)
    [∀ n, Module.Finite R (K.homology n)] (i : ℤ) :
    Module.Finite R ((toInteger K).homology i) := by
  by_cases hi : 0 ≤ i
  · have he : ComplexShape.embeddingUpNat.f i.toNat = i := by
      change (i.toNat : ℤ) = i
      exact Int.toNat_of_nonneg hi
    exact Module.Finite.equiv
      (K.extendHomologyIso ComplexShape.embeddingUpNat he).symm.toLinearEquiv
  · have hz : IsZero ((toInteger K).X i) := K.isZero_extend_X
      ComplexShape.embeddingUpNat i (fun n hn => by change (n : ℤ) = i at hn; omega)
    have hH : IsZero ((toInteger K).homology i) :=
      ShortComplex.isZero_homology_of_isZero_X₂ ((toInteger K).sc i) hz
    let : Subsingleton ((toInteger K).homology i) := ModuleCat.subsingleton_of_isZero hH
    infer_instance

/-- The actual original upper zero term supplies the extended upper zero term. -/
theorem toInteger_next_isZero (K : CochainComplex (ModuleCat.{u} R) ℕ)
    (N : ℕ) (hnext : IsZero (K.X (N + 1))) :
    IsZero ((toInteger K).X ((N : ℤ) + 1)) :=
  hnext.of_iso (K.extendXIso ComplexShape.embeddingUpNat (by
    change ((N + 1 : ℕ) : ℤ) = (N : ℤ) + 1
    omega))

/-- The actual original natural three terms in a positive cochain degree. -/
def naturalSegment (K : CochainComplex (ModuleCat.{u} R) ℕ) (t : ℕ) :
    ShortComplex (ModuleCat.{u} R) := K.sc' (t - 1) t (t + 1)

/-- All three positive-degree original terms and maps are retained under the
actual extension, with the original reversal bound. -/
def positiveSegmentIso (K : CochainComplex (ModuleCat.{u} R) ℕ)
    (N t : ℕ) (ht : 0 < t) (htN : t ≤ N) :
    originalSegment (toInteger K) (N : ℤ) (N - t) ≅ naturalSegment K t := by
  have hi : ComplexShape.embeddingUpNat.f (t - 1) = (N : ℤ) - (N - t : ℕ) - 1 := by
    change ((t - 1 : ℕ) : ℤ) = (N : ℤ) - (N - t : ℕ) - 1
    omega
  have hj : ComplexShape.embeddingUpNat.f t = (N : ℤ) - (N - t : ℕ) := by
    change (t : ℤ) = (N : ℤ) - (N - t : ℕ)
    omega
  have hk : ComplexShape.embeddingUpNat.f (t + 1) = (N : ℤ) - (N - t : ℕ) + 1 := by
    change ((t + 1 : ℕ) : ℤ) = (N : ℤ) - (N - t : ℕ) + 1
    omega
  refine ShortComplex.isoMk (K.extendXIso ComplexShape.embeddingUpNat hi)
    (K.extendXIso ComplexShape.embeddingUpNat hj)
    (K.extendXIso ComplexShape.embeddingUpNat hk) ?_ ?_
  · change (K.extendXIso ComplexShape.embeddingUpNat hi).hom ≫ K.d (t - 1) t =
      (K.extend ComplexShape.embeddingUpNat).d _ _ ≫
        (K.extendXIso ComplexShape.embeddingUpNat hj).hom
    rw [K.extend_d_eq ComplexShape.embeddingUpNat hi hj]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · change (K.extendXIso ComplexShape.embeddingUpNat hj).hom ≫ K.d t (t + 1) =
      (K.extend ComplexShape.embeddingUpNat).d _ _ ≫
        (K.extendXIso ComplexShape.embeddingUpNat hk).hom
    rw [K.extend_d_eq ComplexShape.embeddingUpNat hj hk]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable [IsNoetherianRing R]

/-- Actual positive native homology of the original natural cochain tensor
complex vanishes on a produced principal neighborhood of an original closed fibre. -/
theorem exists_natural_homology_zero_neighborhood
    (K : CochainComplex (ModuleCat.{u} R) ℕ)
    [∀ n, Module.Flat R (K.X n)] [∀ n, Module.Finite R (K.homology n)]
    (N : ℕ) (hnext : IsZero (K.X (N + 1))) (t : ℕ) (ht : 0 < t) (htN : t ≤ N)
    (p : Ideal R) [p.IsMaximal]
    (hzero : IsZero (baseChangeComplex (naturalSegment K t) p.ResidueField).homology) :
    ∃ r : R, r ∉ p ∧ ∀ (F : Type u) [Field F] [Algebra R F],
      algebraMap R F r ≠ 0 →
        IsZero (baseChangeComplex (naturalSegment K t) F).homology := by
  let L := toInteger K
  let : ∀ i, Module.Flat R (L.X i) := fun i => toInteger_X_flat K i
  let : ∀ i, Module.Finite R (L.homology i) := fun i => toInteger_homology_finite K i
  let e := positiveSegmentIso K N t ht htN
  have hL : IsZero (baseChangeComplex
      (originalSegment L (N : ℤ) (N - t)) p.ResidueField).homology :=
    hzero.of_iso (ShortComplex.homologyMapIso (baseChangeIso e p.ResidueField))
  obtain ⟨r, hr, hfield⟩ := exists_cochain_homology_zero_neighborhood L (N : ℤ)
    (toInteger_next_isZero K N hnext) p (N - t) hL
  exact ⟨r, hr, fun F _ _ hF =>
    (hfield F hF).of_iso (ShortComplex.homologyMapIso (baseChangeIso e F)).symm⟩

/-- Positive native homology of the same original natural tensor complex
vanishes over the original fraction field if it vanishes on an original closed fibre. -/
theorem generic_natural_homology_isZero_of_closed_fibre [IsDomain R]
    (K : CochainComplex (ModuleCat.{u} R) ℕ)
    [∀ n, Module.Flat R (K.X n)] [∀ n, Module.Finite R (K.homology n)]
    (N : ℕ) (hnext : IsZero (K.X (N + 1))) (t : ℕ) (ht : 0 < t) (htN : t ≤ N)
    (p : Ideal R) [p.IsMaximal]
    (hzero : IsZero (baseChangeComplex (naturalSegment K t) p.ResidueField).homology)
    (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F] :
    IsZero (baseChangeComplex (naturalSegment K t) F).homology := by
  obtain ⟨r, hr, hfield⟩ := exists_natural_homology_zero_neighborhood
    K N hnext t ht htN p hzero
  apply hfield F
  intro h
  have hrzero : r = 0 :=
    IsFractionRing.injective R F (h.trans (map_zero (algebraMap R F)).symm)
  exact hr (hrzero ▸ p.zero_mem)

end EnvelopeProperty.Vanishing.SpecializationDerivedNatural
