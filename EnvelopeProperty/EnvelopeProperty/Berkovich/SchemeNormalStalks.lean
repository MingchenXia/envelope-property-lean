/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.NormalLocalUnibranch
import EnvelopeProperty.Berkovich.SchemeIntegralNormalization
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Actual normal stalks and the genuine original normalization

There is no new scheme-normality endpoint predicate. The hypotheses are
actual domains and integral closedness of the ORIGINAL local stalk rings.
All affine section and normalization properties are derived from those.
-/
open CategoryTheory AlgebraicGeometry
open scoped Topology
universe u
noncomputable section
namespace EnvelopeProperty

/-- Actual normality of EVERY original scheme stalk derives the STANDARD structural scheme class. -/
theorem IsGeometricallyUnibranchScheme.of_normal_stalks (X : Scheme.{u})
    (hD : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (hN : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsGeometricallyUnibranchScheme X where
  isGeometricallyUnibranch_stalk x := by
    let : IsDomain (X.presheaf.stalk x) := hD x
    let : IsIntegrallyClosed (X.presheaf.stalk x) := hN x
    exact IsGeometricallyUnibranchLocalRing.of_isIntegrallyClosed _

namespace IntegralSchemeNormalization
variable (X : Scheme.{u}) [IsIntegral X]

set_option backward.isDefEq.respectTransparency false in
/-- Genuine normal stalks DERIVE integral closedness of the SAME original nonempty affine section ring. -/
theorem affine_sections_isIntegrallyClosed
    (hN : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] : IsIntegrallyClosed Γ(X, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  let q : PrimeSpectrum Γ(X, U) := ⟨p, inferInstance⟩
  let : IsIntegrallyClosed (X.presheaf.stalk (hU.fromSpec q)) := hN _
  exact IsIntegrallyClosed.of_equiv
    ((asIso (hU.fromSpec.stalkMap q)).commRingCatIsoToRingEquiv.trans
      (Spec.stalkIso Γ(X, U) q).commRingCatIsoToRingEquiv)

set_option backward.isDefEq.respectTransparency false in
/-- Actual normal stalks make the ORIGINAL global integral normalization projection an actual isomorphism. -/
theorem projection_isIso_of_normal_stalks
    (hN : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIso (projection X) := by
  change (MorphismProperty.isomorphisms _) (projection X)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _) _
    (iSup_nonemptyAffineOpen_eq_top X)]
  rintro ⟨⟨U, hU⟩, hne⟩
  let : Nonempty U := hne
  let : IsIntegrallyClosed Γ(X, U) := affine_sections_isIntegrallyClosed X hN U hU
  have hcoeff : IsIso (DomainNormalization.projection Γ(X, U)) :=
    isIso_SpecMap_iff.mpr
      (LocalNormalization.algebraMap_integralClosure_bijective_of_isIntegrallyClosed
        Γ(X, U) (FractionRing Γ(X, U)))
  have : IsOpenImmersion (chartMap X U hU) := chartMap_isOpenImmersion X U hU
  let e := IsOpenImmersion.isoOfRangeEq ((projection X) ⁻¹ᵁ U).ι (chartMap X U hU)
    (by simpa only [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange] using
      (congrArg (fun V : (normalization X).Opens => (V : Set (normalization X)))
        (chartMap_opensRange X U hU).symm))
  rw [← MorphismProperty.cancel_left_of_respectsIso (.isomorphisms _) e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso (.isomorphisms _) _ hU.isoSpec.hom]
  convert! hcoeff
  rw [← cancel_mono hU.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, chartMap_comp_projection]

end IntegralSchemeNormalization
end EnvelopeProperty
