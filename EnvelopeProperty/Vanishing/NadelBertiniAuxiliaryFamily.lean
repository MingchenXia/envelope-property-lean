import EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamilyDimension
import EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamilyIndexed

/-! # Actual auxiliary Cartier divisors of ALL original very-ample lines

The original n-smooth structure, original SNC family and original finite very-ample
lines internally produce n+1 actual sections per line, their whole zero ideals,
SNC of the whole joined family and whole empty row intersections.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamily
open NadelBertiniAuxiliaryFamilyIndexed
variable {X : Scheme.{u}} {I : Type u} [Fintype I]

/-- The original family joined with ALL actual original auxiliary zero ideals,
retaining the actual original line and copy indices. -/
def auxiliaryFamily (F : X.DivisorFamily) (n : ℕ)
    (A : I → Fin (n + 1) → X.IdealSheafData) : X.DivisorFamily :=
  joined F (fun ij : I × Fin (n + 1) => A ij.1 ij.2)

/-- Genuine finite auxiliary-family Bertini. Parameters, original sections,
Cartier witnesses, whole-family SNC and whole row-intersection emptiness are ALL
internally produced from only the ORIGINAL n-smooth scheme, SNC family and finite
original very-ample lines. No desired auxiliary-divisor certificate is an input. -/
theorem exists_veryAmple_auxiliary_family {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n p]
    (F : X.DivisorFamily) (hF : F.IsSnc) (M : I → X.Modules)
    (hM : ∀ i, SchemeLineAmpleness.IsVeryAmple p (M i)) :
    ∃ σ : ∀ i, Fin (n + 1) → (unitObj X ⟶ M i),
      (∀ i j, (LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i j)).IsInvertible ∧
        Smooth ((LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i j)).subschemeι ≫ p)) ∧
      (auxiliaryFamily F n (fun i j =>
        LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i j))).IsSnc ∧
      ∀ i, (⨆ j, LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i j)) = ⊤ := by
  let : Smooth p := SmoothOfRelativeDimension.smooth n p
  obtain ⟨τ, hτ, hSNC⟩ := exists_indexed_snc_sections (I := I × Fin (n + 1)) p F hF
    (fun ij => M ij.1) (fun ij => hM ij.1)
  let σ : ∀ i, Fin (n + 1) → (unitObj X ⟶ M i) := fun i j => τ (i, j)
  let A : I → Fin (n + 1) → X.IdealSheafData := fun i j =>
    LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i j)
  let B : I × Fin (n + 1) → X.IdealSheafData := fun ij => A ij.1 ij.2
  refine ⟨σ, (fun i j => hτ (i, j)), hSNC, ?_⟩
  intro i
  let v : Fin (n + 1) → (joined F B).ι := fun j => memberIndex F B (i, j)
  have hv : Function.Injective v := by
    intro j j' h
    exact congrArg Prod.snd (memberIndex_injective F B h)
  have hzero := NadelBertiniAuxiliaryFamilyDimension.sum_eq_top_of_injective_succ
    p n (joined F B) hSNC v hv
  have hcomp : (⨆ j, (joined F B).component (v j)) = ⨆ j, A i j :=
    iSup_congr (fun j => component_memberIndex F B (i, j))
  rw [hcomp] at hzero
  exact hzero

end EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamily
