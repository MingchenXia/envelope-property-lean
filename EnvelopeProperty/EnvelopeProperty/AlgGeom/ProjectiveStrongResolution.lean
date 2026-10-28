import EnvelopeProperty.AlgGeom.ProjectiveBlowupSequence
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Theorem36

/-! # Smooth integral polynomially projective native strong resolutions -/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveStrongResolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Nonemptiness of the actual original blowup forces a proper-support centre;
the actual native global blowup integrality theorem then applies. -/
theorem isIntegral_blowup_of_nonempty {X : Scheme.{u}} [IsIntegral X]
    (D : X.IdealSheafData) [Nonempty D.blowUp] : IsIntegral D.blowUp := by
  have hD : D.support ≠ ⊤ := by
    intro h
    have hz : D = ⊥ := Scheme.IdealSheafData.support_eq_top_iff.mp h
    have he : IsEmpty D.blowUp := hz ▸ Scheme.IdealSheafData.blowUp.isEmpty_bot
    exact he.false (Classical.choice inferInstance)
  let : IsIntegral (DeJongAlterations.Geometry.BlowupGluing.blowup D) :=
    DeJongAlterations.Geometry.BlowupIntegral.isIntegral_blowup D hD
  exact IsIntegral.of_isIso (HironakaDeJongBlowupComparison.globalIso D).hom

/-- A nonempty final stage of an actual original blowup sequence on an integral
original scheme is integral; intermediate nonemptiness is derived from its actual maps. -/
theorem isIntegral_last {X : Scheme.{u}} (S : X.BlowUpSequence) [IsIntegral X]
    [Nonempty S.last] : IsIntegral S.last := by
  rename_i hX hN
  revert hX hN
  induction S with
  | nil Y =>
    intro hY _
    change IsIntegral Y
    exact hY
  | cons Y D rest ih =>
    intro hY hN
    let : IsIntegral Y := hY
    let : Nonempty rest.last := hN
    let : Nonempty D.blowUp := Nonempty.map rest.composite inferInstance
    let : IsIntegral D.blowUp := isIntegral_blowup_of_nonempty D
    exact ih

/-- Genuine characteristic-zero strong resolution produces an actual smooth
integral projective original scheme with finite polynomial coordinates over the
SAME original field; neither the resolution nor its coordinates are assumed. -/
theorem exists_projective_strong_resolution {k : Type u} [Field k] [CharZero k]
    (X : AlgScheme k) [IsIntegral X.left] (hp : IsProjectiveFactorization X.hom) :
    ∃ S : X.left.BlowUpSequence, S.IsStrongResolution ∧ IsIntegral S.last ∧
      IsProjectiveFactorization (S.composite ≫ X.hom) := by
  obtain ⟨S, hS⟩ := exists_strong_resolution X
  obtain ⟨U, hU, hIso⟩ := hS.exists_dense_isIso
  let := hIso
  have hUn : Nonempty U := by
    exact Set.nonempty_coe_sort.mpr hU.nonempty
  let : Nonempty (S.composite ⁻¹ᵁ U) :=
    Nonempty.map (inv (S.composite ∣_ U)) hUn
  let : Nonempty S.last := Nonempty.map (S.composite ⁻¹ᵁ U).ι inferInstance
  exact ⟨S, hS, isIntegral_last S,
    ProjectiveBlowupSequence.composite_isProjectiveFactorization S X.hom hp⟩

end EnvelopeProperty.ProjectiveStrongResolution
