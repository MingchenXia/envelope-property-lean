import EnvelopeProperty.Vanishing.NadelBertiniSncFlatBertini
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness

/-! # An original very-ample line internally produces its actual SNC section -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamilySection
open NadelBertiniFibreSection NadelBertiniFibreSmooth NadelBertiniUniversal
variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual embedding, whole original line iso, rational tuple and original
section are internally obtained from the ORIGINAL very-ampleness proof. -/
theorem exists_veryAmple_snc_section (p : X ⟶ Spec (.of k)) [Smooth p]
    (F : X.DivisorFamily) (hF : F.IsSnc) (M : X.Modules)
    (hM : SchemeLineAmpleness.IsVeryAmple p M) :
    ∃ σ : unitObj X ⟶ M,
      (LineSectionZeroIdeal.zeroIdeal M hM.isInvertible σ).IsInvertible ∧
      Smooth ((LineSectionZeroIdeal.zeroIdeal M hM.isInvertible σ).subschemeι ≫ p) ∧
      (F.append (LineSectionZeroIdeal.zeroIdeal M hM.isInvertible σ)).IsSnc ∧
      F.HasSncWith (LineSectionZeroIdeal.zeroIdeal M hM.isInvertible σ) := by
  have hMI := hM.isInvertible
  obtain ⟨m, j, hj, hjp, ⟨e⟩⟩ := hM
  let : Smooth (j ≫ DeJongAlterations.projectiveSpaceStructure k m) := by
    rw [hjp]
    infer_instance
  obtain ⟨a, _, hCartier, hSmooth, hSnc, hWith⟩ :=
    NadelBertiniSncFlatBertini.exists_projective_snc_selected j F hF
  let α : unitObj X ⟶ projectiveLine j := SchemeModuleGlobalSections.sectionHom
    (projectiveLine j) (selectedSection (j ≫ DeJongAlterations.projectiveSpaceStructure k m)
      a (projectiveLine j) (projectiveSections j))
  let σ : unitObj X ⟶ M := α ≫ e.hom
  have hEq : projectiveSelectedIdeal j a =
      LineSectionZeroIdeal.zeroIdeal M hMI σ :=
    NadelBertiniFibreIdeals.zeroIdeal_iso (projectiveLine j) M
      ((MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := k) (0 : Fin (m + 1)) 1).pullback j)
      hMI e α
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · rw [← hEq]
    exact hCartier
  · rw [← hEq, ← hjp]
    exact hSmooth
  · rw [← hEq]
    exact hSnc
  · rw [← hEq]
    exact hWith

end EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamilySection
