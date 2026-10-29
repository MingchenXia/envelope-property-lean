import EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamilyFinite

/-! # The actual finite ORIGINAL line indices and all their original section ideals -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamilyIndexed
open NadelBertiniAuxiliaryFamilyIndices
variable {X : Scheme.{u}} {I : Type u} [Fintype I]

/-- Join the same actual original finite ideals; the finite equivalence only orders
these original member labels and does not alter any original ideal. -/
def joined (F : X.DivisorFamily) (A : I → X.IdealSheafData) : X.DivisorFamily :=
  joinedFin F (fun j => A ((Fintype.equivFin I).symm j))

/-- The actual label of each same original newly joined ideal. -/
def memberIndex (F : X.DivisorFamily) (A : I → X.IdealSheafData) (i : I) : (joined F A).ι :=
  toLex (Sum.inr ((Fintype.equivFin I) i))

theorem memberIndex_injective (F : X.DivisorFamily) (A : I → X.IdealSheafData) :
    Function.Injective (memberIndex F A) := by
  intro i j hij
  exact (Fintype.equivFin I).injective (Sum.inr.inj (toLex.injective hij))

/-- Every newly joined label retains the WHOLE same original ideal. -/
theorem component_memberIndex (F : X.DivisorFamily) (A : I → X.IdealSheafData) (i : I) :
    (joined F A).component (memberIndex F A i) = A i := by
  exact congrArg A ((Fintype.equivFin I).symm_apply_apply i)

/-- Internally construct actual original sections for the entire ORIGINAL finite
line family, retaining all its actual indices and whole section zero ideals. -/
theorem exists_indexed_snc_sections {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [Smooth p] (F : X.DivisorFamily) (hF : F.IsSnc)
    (M : I → X.Modules) (hM : ∀ i, SchemeLineAmpleness.IsVeryAmple p (M i)) :
    ∃ σ : ∀ i, unitObj X ⟶ M i,
      (∀ i, (LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i)).IsInvertible ∧
        Smooth ((LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i)).subschemeι ≫ p)) ∧
      (joined F (fun i => LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i))).IsSnc := by
  let e := Fintype.equivFin I
  let M' : Fin (Fintype.card I) → X.Modules := fun j => M (e.symm j)
  let hM' : ∀ j, SchemeLineAmpleness.IsVeryAmple p (M' j) := fun j => hM (e.symm j)
  obtain ⟨τ, hτ, hSnc⟩ := NadelBertiniAuxiliaryFamilyFinite.exists_fin_snc_sections
    p F hF (Fintype.card I) M' hM'
  let σ : ∀ i, unitObj X ⟶ M i := fun i =>
    τ (e i) ≫ eqToHom (congrArg M (e.symm_apply_apply i))
  let A : I → X.IdealSheafData := fun i =>
    LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i)
  let B : Fin (Fintype.card I) → X.IdealSheafData := fun j =>
    LineSectionZeroIdeal.zeroIdeal (M' j) (hM' j).isInvertible (τ j)
  have hA : ∀ i, A i = B (e i) := by
    intro i
    exact (NadelBertiniFibreIdeals.zeroIdeal_iso (M' (e i)) (M i)
      (hM' (e i)).isInvertible (hM i).isInvertible
      (eqToIso (congrArg M (e.symm_apply_apply i))) (τ (e i))).symm
  refine ⟨σ, ?_, ?_⟩
  · intro i
    change (A i).IsInvertible ∧ Smooth ((A i).subschemeι ≫ p)
    rw [hA]
    exact hτ (e i)
  · have hAB : (fun j => A (e.symm j)) = B := by
      funext j
      rw [hA, e.apply_symm_apply]
    change (joinedFin F (fun j => A (e.symm j))).IsSnc
    rw [hAB]
    exact hSnc

end EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamilyIndexed
