import Hironaka.Scheme.Modules.IdealSheafFinite
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Admissible

/-!
# Genuine extended ideal-power module sheaves and whole affine sections

Every original coefficient ideal gives its actual geometric extended ideal
and every whole ideal power on the original scheme. Genuine affine section
and restriction comparisons and noetherian finite presentation are derived
for these SAME module sheaves, with no coherence/comparison certificate.
-/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u

namespace EnvelopeProperty.FibreIdealPowers

variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The actual original geometric extension of I, with its ENTIRE d-th ideal power. -/
abbrev extendedPower (d : ℕ) : X.IdealSheafData := ((specIdealSheaf I).comap f)^d

/-- The genuine module sheaf of the SAME original ideal power. -/
abbrev powerModule (d : ℕ) : X.Modules := (extendedPower I f d).toModules

/-- On EVERY original affine open, the same ideal power is the actual original coefficient ideal image power. -/
theorem extendedPower_ideal (d : ℕ) (U : X.affineOpens) :
    (extendedPower I f d).ideal U = (I.map (sectionsHom f U.1))^d := by
  change (((specIdealSheaf I).comap f).ideal U)^d = _
  rw [ideal_comap_specIdealSheaf]

/-- The WHOLE affine sections of the actual ideal-power module sheaf are its entire original coefficient ideal power. -/
def affineSectionsEquiv (d : ℕ) (U : X.affineOpens) :
    Γ(powerModule I f d, U) ≃ₗ[Γ(X, U)] ↥((I.map (sectionsHom f U.1))^d) :=
  ((extendedPower I f d).toModulesSectionsEquiv U).trans
    (LinearEquiv.ofEq _ _ (extendedPower_ideal I f d U))

/-- The actual whole ideal-power section equivalence retains EVERY original ambient function. -/
theorem affineSectionsEquiv_apply (d : ℕ) (U : X.affineOpens)
    (s : Γ(powerModule I f d, U)) :
    ((affineSectionsEquiv I f d U s : ↥((I.map (sectionsHom f U.1))^d)) : Γ(X, U)) =
      ((extendedPower I f d).toModulesSectionsEquiv U s : Γ(X, U)) := rfl

/-- EVERY whole original ideal-power restriction is the literal original affine function restriction. -/
theorem affineSectionsEquiv_restriction (d : ℕ) {U V : X.affineOpens} (h : U ≤ V)
    (s : Γ(powerModule I f d, V)) :
    ((affineSectionsEquiv I f d U ((powerModule I f d).presheaf.map (homOfLE h).op s) :
        ↥((I.map (sectionsHom f U.1))^d)) : Γ(X, U)) =
      X.presheaf.map (homOfLE h).op
        ((affineSectionsEquiv I f d V s : ↥((I.map (sectionsHom f V.1))^d)) : Γ(X, V)) := rfl

variable [IsNoetherianRing R] [LocallyOfFiniteType f]

/-- Actual noetherian finite-type geometry derives finite presentation of EVERY genuine original ideal-power module sheaf. -/
theorem isFinitePresentation_powerModule (d : ℕ) :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (powerModule I f d) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact (extendedPower I f d).isFinitePresentation_toModules

/-- The SAME original ideal-power module sheaf is genuinely quasi-coherent. -/
theorem isQuasicoherent_powerModule (d : ℕ) :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (powerModule I f d) := by
  let : SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (powerModule I f d) :=
    isFinitePresentation_powerModule I f d
  obtain ⟨σ, _⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData (powerModule I f d)
  exact σ.isQuasicoherent

set_option backward.isDefEq.respectTransparency false in
/-- The SAME original ideal-power module sheaf has actual finite type. -/
theorem isFiniteType_powerModule (d : ℕ) :
    SheafOfModules.IsFiniteType (R := X.ringCatSheaf) (powerModule I f d) := by
  refine { exists_localGeneratorsData := ?_ }
  let : SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (powerModule I f d) :=
    isFinitePresentation_powerModule I f d
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData (powerModule I f d)
  let : σ.IsFinitePresentation := hσ
  exact ⟨σ.localGeneratorsData, inferInstance⟩

end EnvelopeProperty.FibreIdealPowers
