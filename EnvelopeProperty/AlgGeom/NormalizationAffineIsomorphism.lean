/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeNormalStalks

/-! # Actual normalization isomorphisms on original normal affine opens -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.IntegralSchemeNormalization
variable (X : Scheme.{u}) [IsIntegral X]

/-- Normality at the ACTUAL original stalks on an ACTUAL affine open
proves integral closedness of its SAME original affine section ring. -/
theorem affine_sections_isIntegrallyClosed_on (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hN : ∀ (x : X), x ∈ U → IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosed Γ(X, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  let q : PrimeSpectrum Γ(X, U) := ⟨p, inferInstance⟩
  have hm : hU.fromSpec q ∈ U := by
    have hs : hU.fromSpec q ∈ Set.range hU.fromSpec := ⟨q, rfl⟩
    exact Eq.mp (congrArg (fun S : Set X => hU.fromSpec q ∈ S) hU.range_fromSpec) hs
  let : IsIntegrallyClosed (X.presheaf.stalk (hU.fromSpec q)) := hN _ hm
  exact IsIntegrallyClosed.of_equiv
    ((asIso (hU.fromSpec.stalkMap q)).commRingCatIsoToRingEquiv.trans
      (Spec.stalkIso Γ(X, U) q).commRingCatIsoToRingEquiv)

/-- The ACTUAL WHOLE normalization projection is an isomorphism over
EVERY ACTUAL original normal affine open, with no finite-normalization premise. -/
theorem projection_isIso_on_affine (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsIntegrallyClosed Γ(X, U)] : IsIso (projection X ∣_ U) := by
  have hcoeff : IsIso (DomainNormalization.projection Γ(X, U)) :=
    isIso_SpecMap_iff.mpr
      (LocalNormalization.algebraMap_integralClosure_bijective_of_isIntegrallyClosed
        Γ(X, U) (FractionRing Γ(X, U)))
  have : IsOpenImmersion (chartMap X U hU) := chartMap_isOpenImmersion X U hU
  let e := IsOpenImmersion.isoOfRangeEq ((projection X) ⁻¹ᵁ U).ι (chartMap X U hU)
    (by simpa only [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange] using
      (congrArg (fun V : (normalization X).Opens => (V : Set (normalization X)))
        (chartMap_opensRange X U hU).symm))
  change (MorphismProperty.isomorphisms _) (projection X ∣_ U)
  rw [← MorphismProperty.cancel_left_of_respectsIso (.isomorphisms _) e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso (.isomorphisms _) _ hU.isoSpec.hom]
  convert! hcoeff
  rw [← cancel_mono hU.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, chartMap_comp_projection]

/-- ACTUAL original affine-open stalk normality derives the TRUE WHOLE
normalization isomorphism there, without a chart-normality certificate. -/
theorem projection_isIso_on_normal_affine (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hN : ∀ (x : X), x ∈ U → IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIso (projection X ∣_ U) := by
  let : IsIntegrallyClosed Γ(X, U) := affine_sections_isIntegrallyClosed_on X U hU hN
  exact projection_isIso_on_affine X U hU

end EnvelopeProperty.IntegralSchemeNormalization
