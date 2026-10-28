import EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamilySection
import EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamilyIndices

/-! # Actual sections of an entire finite original very-ample line family -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamilyFinite
open NadelBertiniAuxiliaryFamilyIndices
variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}

/-- Genuine finite repetition: every actual section, original whole zero ideal,
Cartier witness and SNC coordinate system is internally produced. -/
theorem exists_fin_snc_sections (p : X ⟶ Spec (.of k)) [Smooth p]
    (F : X.DivisorFamily) (hF : F.IsSnc) (r : ℕ) :
    ∀ (M : Fin r → X.Modules) (hM : ∀ i, SchemeLineAmpleness.IsVeryAmple p (M i)),
    ∃ σ : ∀ i, unitObj X ⟶ M i,
      (∀ i, (LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i)).IsInvertible ∧
        Smooth ((LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i)).subschemeι ≫ p)) ∧
      (joinedFin F (fun i => LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i))).IsSnc := by
  induction r with
  | zero =>
    intro M hM
    refine ⟨fun i => i.elim0, fun i => i.elim0, ?_⟩
    exact joinedFin_zero_isSnc F hF _
  | succ r ih =>
    intro M hM
    obtain ⟨τ, hτ, htail⟩ := ih (fun i => M i.succ) (fun i => hM i.succ)
    let A : Fin r → X.IdealSheafData := fun i =>
      LineSectionZeroIdeal.zeroIdeal (M i.succ) (hM i.succ).isInvertible (τ i)
    obtain ⟨σ₀, hCartier, hSmooth, hAppend, _⟩ :=
      NadelBertiniAuxiliaryFamilySection.exists_veryAmple_snc_section
        p (joinedFin F A) htail (M 0) (hM 0)
    let H := LineSectionZeroIdeal.zeroIdeal (M 0) (hM 0).isInvertible σ₀
    let σ : ∀ i, unitObj X ⟶ M i := Fin.cons σ₀ τ
    refine ⟨σ, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hCartier, hSmooth⟩
      · exact hτ j
    · have hA : (fun i => LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i)) =
          Fin.cons H A := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      rw [hA]
      exact joinedFin_cons_isSnc F A H hAppend

end EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamilyFinite
