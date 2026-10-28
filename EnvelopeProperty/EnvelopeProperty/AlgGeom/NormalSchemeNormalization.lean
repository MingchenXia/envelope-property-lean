/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeNormalStalks
import EnvelopeProperty.Algebra.NormalizationFinite

/-! # Normality of EVERY actual original normalization local stalk -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.IntegralSchemeNormalization
variable (X : Scheme.{u}) [IsIntegral X]

/-- EVERY ACTUAL original local stalk of the ORIGINAL normalization
is integrally closed, without finite normalization or Noetherian hypotheses. -/
theorem stalk_isIntegrallyClosed (z : normalization X) :
    IsIntegrallyClosed ((normalization X).presheaf.stalk z) := by
  obtain ⟨U, hU, hz, _⟩ := exists_isAffineOpen_mem_and_subset
    (show projection X z ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨projection X z, hz⟩⟩
  have : IsOpenImmersion (chartMap X U hU) := chartMap_isOpenImmersion X U hU
  have hm : z ∈ (chartMap X U hU).opensRange := by
    rw [chartMap_opensRange X U hU]
    exact hz
  obtain ⟨q, hq⟩ := hm
  rw [← hq]
  let A := Γ(X, U)
  let B := integralClosure A (FractionRing A)
  have : IsIntegrallyClosed B := isIntegrallyClosed_integralClosure A (FractionRing A)
  have : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q.asIdeal)
      q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv
    ((Spec.stalkIso (CommRingCat.of B) q).commRingCatIsoToRingEquiv.symm.trans
      (asIso ((chartMap X U hU).stalkMap q)).commRingCatIsoToRingEquiv.symm)

/-- The SAME actual original normalization has the STANDARD structural
geometric-unibranch property from its genuinely normal ORIGINAL local stalks. -/
theorem normalization_isGeometricallyUnibranch : IsGeometricallyUnibranchScheme (normalization X) :=
  IsGeometricallyUnibranchScheme.of_normal_stalks (normalization X)
    (fun _ => inferInstance) (stalk_isIntegrallyClosed X)

end EnvelopeProperty.IntegralSchemeNormalization
