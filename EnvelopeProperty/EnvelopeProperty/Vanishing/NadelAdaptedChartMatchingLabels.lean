import EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsSnc
import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingFrames

/-! # The SAME actual original and auxiliary SNC labels in the ratio chart

The actual original row/copy indices construct the whole ratio labels and
prove their injection. No disjointness or coordinate-matching certificate is
supplied as a new input.
-/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.Joined
open NadelAuxiliaryBranchSectionsSnc NadelBertiniAuxiliaryFamilyIndexed
variable {X : Scheme.{u}} (F : X.DivisorFamily) (n : ℕ)
  (A : F.ι → Fin (n + 1) → X.IdealSheafData) (j₀ : F.ι → Fin (n + 1))

/-- SAME actual original row and copy labels, with no component selection. -/
abbrev Index := F.ι × Fin (n + 1)

/-- At the distinguished original copy take the original D_i; at EVERY
other copy retain the SAME actual auxiliary H_ij. -/
def label (ij : Index F n) : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).ι :=
  if ij.2 = j₀ ij.1 then originalIndex F n A ij.1 else auxiliaryIndex F n A ij.1 ij.2

/-- The actual original labels are distinct, internally proved from the
actual joined-family construction and original row/copy labels. -/
theorem label_injective : Function.Injective (label F n A j₀) := by
  classical
  rintro ⟨i, a⟩ ⟨j, b⟩ hij
  have hhead (i : F.ι) (a : Fin (n + 1)) (ha : a = j₀ i) :
      label F n A j₀ (i, a) = originalIndex F n A i := if_pos ha
  have htail (i : F.ι) (a : Fin (n + 1)) (ha : a ≠ j₀ i) :
      label F n A j₀ (i, a) = auxiliaryIndex F n A i a := if_neg ha
  by_cases ha : a = j₀ i <;> by_cases hb : b = j₀ j
  · rw [hhead i a ha, hhead j b hb] at hij
    have he : i = j := Sum.inl.inj (toLex.injective hij)
    exact Prod.ext he (ha.trans ((congrArg j₀ he).trans hb.symm))
  · rw [hhead i a ha, htail j b hb] at hij
    cases (toLex.injective hij)
  · rw [htail i a ha, hhead j b hb] at hij
    cases (toLex.injective hij)
  · rw [htail i a ha, htail j b hb] at hij
    exact memberIndex_injective F (fun ij : Index F n => A ij.1 ij.2) hij

/-- The actual finite ordering of ALL original row/copy positions. -/
abbrev ordering : Index F n ≃ Fin (Fintype.card (Index F n)) := Fintype.equivFin _

/-- The actual original row at every whole quotient position. -/
def row (i : Fin (Fintype.card (Index F n))) : F.ι := ((ordering F n).symm i).1

/-- The actual original copy at every whole quotient position. -/
def copy (i : Fin (Fintype.card (Index F n))) : Fin (n + 1) := ((ordering F n).symm i).2

/-- The distinguished copy in the SAME original row, as a whole quotient index. -/
def head (i : Fin (Fintype.card (Index F n))) : Fin (Fintype.card (Index F n)) :=
  ordering F n (row F n i, j₀ (row F n i))

/-- This actual original row selection is a retraction, not a chosen algebra component. -/
theorem head_head (i : Fin (Fintype.card (Index F n))) :
    head F n j₀ (head F n j₀ i) = head F n j₀ i := by
  simp only [head, row, Equiv.symm_apply_apply]

/-- All original head roots retain the SAME original row. -/
theorem row_head (i : Fin (Fintype.card (Index F n))) :
    row F n (head F n j₀ i) = row F n i := by
  simp only [head, row, Equiv.symm_apply_apply]

/-- The internally ordered whole labels remain injective. -/
def orderedLabel : Fin (Fintype.card (Index F n)) ↪
    (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).ι :=
  ⟨fun i => label F n A j₀ ((ordering F n).symm i), by
    intro i j hij
    apply (ordering F n).symm.injective
    exact label_injective F n A j₀ hij⟩

/-- Empty original row intersections INTERNALLY produce the original absent
copies needed by every row at the SAME specified original point. -/
theorem exists_absent_copies (hRows : ∀ i, (⨆ j, A i j) = ⊤) (y : X) :
    ∃ j₀ : F.ι → Fin (n + 1), ∀ i, y ∉ (A i (j₀ i)).support := by
  classical
  choose j₀ hj₀ using fun i : F.ι => exists_absent_member (A i) (hRows i) y
  exact ⟨j₀, hj₀⟩

end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.Joined
