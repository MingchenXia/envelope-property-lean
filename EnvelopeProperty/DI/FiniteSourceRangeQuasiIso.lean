import EnvelopeProperty.DI.FiniteSourceAssembly

/-! # Range quasi-isomorphisms for the original finite-source good truncation

This is a general abelian-category support lemma. It supplies no actual DI map
or geometric homology comparison, and reuses the original good truncation.
-/
noncomputable section
namespace EnvelopeProperty.DI.FiniteSourceRangeQuasiIso
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] {p : ℕ} (M : Fin p → C)
local notation "S" => Cartier.DeligneIllusieGradedSourceHomology.gradedSource
  (ComplexShape.up ℕ) Fin.val M

/-- Comparisons in the original finite source range imply a quasi-isomorphism
of its SAME canonical map into the original good truncation. -/
theorem quasiIso_truncatedMap_of_range {T : CochainComplex C ℕ} (a : S ⟶ T)
    (h : ∀ q, q < p → QuasiIsoAt a q) :
    QuasiIso (FiniteSourceAssembly.truncatedMap M a) := by
  have ht : QuasiIso
      (CochainComplex.truncLEMap (extendMap a ComplexShape.embeddingUpNat) ((p : ℤ) - 1)) := by
    rw [CochainComplex.quasiIso_truncLEMap_iff]
    intro z hz
    cases z with
    | ofNat q =>
      simp only [Int.ofNat_eq_natCast] at hz
      have hqp : q < p := by omega
      exact (quasiIsoAt_extendMap_iff a ComplexShape.embeddingUpNat
        (j := q) (hj' := rfl)).mpr (h q hqp)
    | negSucc q =>
      have hs : ((S).extend ComplexShape.embeddingUpNat).ExactAt (Int.negSucc q) :=
        extend_exactAt _ _ _ (by
          intro j
          change (j : ℤ) ≠ Int.negSucc q
          omega)
      have hT : (T.extend ComplexShape.embeddingUpNat).ExactAt (Int.negSucc q) :=
        extend_exactAt _ _ _ (by
          intro j
          change (j : ℤ) ≠ Int.negSucc q
          omega)
      exact (quasiIsoAt_iff_exactAt (extendMap a ComplexShape.embeddingUpNat)
        (Int.negSucc q) hs).mpr hT
  let := ht
  change QuasiIso ((FiniteSourceAssembly.sourceTruncationIso M).inv ≫
    CochainComplex.truncLEMap (extendMap a ComplexShape.embeddingUpNat) ((p : ℤ) - 1))
  infer_instance

end EnvelopeProperty.DI.FiniteSourceRangeQuasiIso
