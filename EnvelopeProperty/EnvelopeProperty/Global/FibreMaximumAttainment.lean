import EnvelopeProperty.Global.BlowupWholeFibrePSH

/-! # Actual compact completed fibres and finite original psh maxima

All statements use the original whole analytic fibre and its actual native
completed scheme comparison. No countability or connectedness is assumed.
-/

open scoped NNReal Topology Classical
open Topology CategoryTheory AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u

namespace EnvelopeProperty.ProjSubvariety.BlowupCenter

variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
  (B : V.BlowupCenter M') (t : V.an)

/-- Actual original fibre compactness transports through the exact native
completed-field scheme homeomorphism, without any model hypothesis. -/
theorem fcAffineCompletedFibre_compactSpace
    (i : Fin (M + 1)) (hi : (t : ProjBerk k M).1.val (MvPolynomial.X i) = 1) :
    CompactSpace (RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H
      (V.chartMap (MvPolynomial.X i) 1 t (hi.trans_ne one_ne_zero)).toSpectrum))
      (B.fcAffineCompletedFibreStructure t i hi)) := by
  have : CompactSpace {y : B.an // B.proj y = t} :=
    isCompact_iff_compactSpace.mp (B.fc_isCompact_fibre t)
  exact (B.fcAffineCompletedFibreHomeomorph t i hi).symm.compactSpace

/-- Every original whole analytic fibre has an actual attained psh maximum,
derived from actual proper projection geometry and original global usc. -/
theorem fc_exists_isMaxOn_fibre {θ : Fin 2 → ℝ} {φ : B.an → EReal}
    (h : B.IsPSH θ φ) : ∃ y : B.an, B.proj y = t ∧ IsMaxOn φ (B.proj ⁻¹' {t}) y := by
  obtain ⟨a, ha⟩ := B.proj_surjective t
  have hne : (B.proj ⁻¹' {t}).Nonempty := ⟨a, ha⟩
  have husc := FSSystem.IsPSH.upperSemicontinuous h
  obtain ⟨y, hy, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn hne
    (B.fc_isCompact_fibre t) (husc.upperSemicontinuousOn _)
  exact ⟨y, hy, hmax⟩

/-- The literal whole actual completed scheme fibre has an attained original
psh maximum, without a countability, topology or point-lift certificate. -/
theorem fc_exists_isMaxOn_wholeCompletedFibre
    (i : Fin (M + 1)) (hi : (t : ProjBerk k M).1.val (MvPolynomial.X i) = 1)
    {θ : Fin 2 → ℝ} {φ : B.an → EReal} (h : B.IsPSH θ φ) :
    ∃ y : RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H
      (V.chartMap (MvPolynomial.X i) 1 t (hi.trans_ne one_ne_zero)).toSpectrum))
      (B.fcAffineCompletedFibreStructure t i hi),
      IsMaxOn (fun z => φ (B.fcAffineCompletedFibreHomeomorph t i hi z).1) Set.univ y := by
  obtain ⟨a, ha, hamax⟩ := B.fc_exists_isMaxOn_fibre t h
  let y := (B.fcAffineCompletedFibreHomeomorph t i hi).symm ⟨a, ha⟩
  refine ⟨y, ?_⟩
  intro z hz
  change φ (B.fcAffineCompletedFibreHomeomorph t i hi z).1 ≤
    φ (B.fcAffineCompletedFibreHomeomorph t i hi y).1
  rw [show B.fcAffineCompletedFibreHomeomorph t i hi y = ⟨a, ha⟩ from
    (B.fcAffineCompletedFibreHomeomorph t i hi).apply_symm_apply _]
  exact hamax (B.fcAffineCompletedFibreHomeomorph t i hi z).2

/-- The original whole-fibre source dichotomy is derived: either every value
is minus infinity, or an actual finite real global maximum is attained. -/
theorem fc_fibre_eq_bot_or_exists_finite_maximum
    {θ : Fin 2 → ℝ} {φ : B.an → EReal} (h : B.IsPSH θ φ) :
    (∀ y : B.an, B.proj y = t → φ y = ⊥) ∨
      ∃ (y : B.an) (r : ℝ), B.proj y = t ∧ φ y = (r : EReal) ∧
        ∀ z : B.an, B.proj z = t → φ z ≤ (r : EReal) := by
  by_cases hall : ∀ y : B.an, B.proj y = t → φ y = ⊥
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨a, ha, hane⟩ := hall
    obtain ⟨y, hy, hmax⟩ := B.fc_exists_isMaxOn_fibre t h
    have hytop : φ y ≠ ⊤ := FSSystem.IsPSH.ne_top h y
    have hybot : φ y ≠ ⊥ := ne_bot_of_le_ne_bot hane (hmax ha)
    lift φ y to ℝ using ⟨hytop, hybot⟩ with r hr
    exact Or.inr ⟨y, r, hy, hr.symm, fun z hz => (hmax hz).trans_eq hr.symm⟩

end EnvelopeProperty.ProjSubvariety.BlowupCenter
