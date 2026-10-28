import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Actual finite joining of divisor families retains every whole original member -/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamilyIndices
variable {X : Scheme.{u}}

/-- The actual original family and actual finite ideals, with their original labels. -/
def joinedFin (F : X.DivisorFamily) {r : ℕ} (A : Fin r → X.IdealSheafData) : X.DivisorFamily where
  ι := F.ι ⊕ₗ Fin r
  component := fun i => Sum.elim F.component A (ofLex i)

/-- The actual singleton appended to the tail is the new zeroth finite member. -/
def consEquiv (F : X.DivisorFamily) {r : ℕ} (A : Fin r → X.IdealSheafData)
    (H : X.IdealSheafData) :
    ((joinedFin F A).append H).ι ≃ (joinedFin F (Fin.cons H A)).ι :=
  ofLex.trans ((Equiv.sumCongr ofLex (Equiv.refl PUnit)).trans
    ((Equiv.sumAssoc F.ι (Fin r) PUnit).trans
      ((Equiv.sumCongr (Equiv.refl F.ι)
        ((Equiv.optionEquivSumPUnit (Fin r)).symm.trans (finSuccEquiv r).symm)).trans toLex)))

/-- This actual relabelling retains the entire actual ideal of every member. -/
theorem consEquiv_component (F : X.DivisorFamily) {r : ℕ} (A : Fin r → X.IdealSheafData)
    (H : X.IdealSheafData) (i : ((joinedFin F A).append H).ι) :
    (joinedFin F (Fin.cons H A)).component (consEquiv F A H i) =
      ((joinedFin F A).append H).component i := by
  obtain ⟨i, rfl⟩ := toLex.surjective i
  rcases i with i | ⟨⟩
  · obtain ⟨i, rfl⟩ := toLex.surjective i
    rcases i with i | i
    · rfl
    · change (Fin.cons H A : Fin (r + 1) → X.IdealSheafData) ((finSuccEquiv r).symm (some i)) = A i
      rw [finSuccEquiv_symm_some]
      rfl
  · change (Fin.cons H A : Fin (r + 1) → X.IdealSheafData) ((finSuccEquiv r).symm none) = H
    rw [finSuccEquiv_symm_none]
    rfl

/-- Joining no new ideals retains original SNC with the exact old components. -/
theorem joinedFin_zero_isSnc (F : X.DivisorFamily) (hF : F.IsSnc)
    (A : Fin 0 → X.IdealSheafData) : (joinedFin F A).IsSnc :=
  isSnc_of_equiv ((Equiv.sumEmpty F.ι (Fin 0)).symm.trans toLex) (fun _ => rfl) hF

/-- Genuine append-by-one SNC gives SNC of the same entire original finite join. -/
theorem joinedFin_cons_isSnc (F : X.DivisorFamily) {r : ℕ} (A : Fin r → X.IdealSheafData)
    (H : X.IdealSheafData) (h : ((joinedFin F A).append H).IsSnc) :
    (joinedFin F (Fin.cons H A)).IsSnc :=
  isSnc_of_equiv (consEquiv F A H) (consEquiv_component F A H) h

end EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamilyIndices
