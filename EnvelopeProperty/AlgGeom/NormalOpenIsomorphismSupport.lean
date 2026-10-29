/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.NormalizationAffineIsomorphism

/-! # Actual normal affine support through genuine original open isomorphisms -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.Hom
variable {Y Z : Scheme.{u}} (μ : Z ⟶ Y) (W : Y.Opens) [IsIso (μ ∣_ W)]

/-- Every actual original local ring over an actual original open
isomorphism is normal when the corresponding original target local rings are normal. -/
theorem stalk_isIntegrallyClosed_of_restrictIso
    (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (z : Z) (hz : z ∈ μ ⁻¹ᵁ W) : IsIntegrallyClosed (Z.presheaf.stalk z) := by
  let q : (μ ⁻¹ᵁ W).toScheme := ⟨z, hz⟩
  let : IsIntegrallyClosed (Y.presheaf.stalk (W.ι ((μ ∣_ W) q))) := hN _
  have : IsIntegrallyClosed (W.toScheme.presheaf.stalk ((μ ∣_ W) q)) :=
    IsIntegrallyClosed.of_equiv (asIso (W.ι.stalkMap ((μ ∣_ W) q))).commRingCatIsoToRingEquiv
  have : IsIntegrallyClosed ((μ ⁻¹ᵁ W).toScheme.presheaf.stalk q) :=
    IsIntegrallyClosed.of_equiv (asIso ((μ ∣_ W).stalkMap q)).commRingCatIsoToRingEquiv
  exact IsIntegrallyClosed.of_equiv
    (asIso ((μ ⁻¹ᵁ W).ι.stalkMap q)).commRingCatIsoToRingEquiv.symm

/-- An actual point over a genuine original normal-target open isomorphism
has an ACTUAL normal affine neighborhood in the SAME original integral source. -/
theorem exists_normal_affine_neighborhood_of_restrictIso [IsIntegral Z]
    (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (z : Z) (hz : z ∈ μ ⁻¹ᵁ W) :
    ∃ (U : Z.Opens) (_ : IsAffineOpen U), z ∈ U ∧ IsIntegrallyClosed Γ(Z, U) := by
  obtain ⟨U, hU, hzU, hUW⟩ := exists_isAffineOpen_mem_and_subset hz
  let : Nonempty U := ⟨⟨z, hzU⟩⟩
  exact ⟨U, hU, hzU,
    EnvelopeProperty.IntegralSchemeNormalization.affine_sections_isIntegrallyClosed_on Z U hU
      (fun x hx => μ.stalk_isIntegrallyClosed_of_restrictIso W hN x (hUW hx))⟩

end AlgebraicGeometry.Scheme.Hom
