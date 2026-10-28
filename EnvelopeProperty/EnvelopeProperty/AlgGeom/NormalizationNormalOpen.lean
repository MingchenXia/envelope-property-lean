/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.NormalizationAffineIsomorphism

/-! # Actual whole normalization isomorphisms on original normal opens -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.IntegralSchemeNormalization
variable (Z : Scheme.{u}) [IsIntegral Z]

/-- The ACTUAL WHOLE original normalization is an isomorphism over EVERY
original open whose original stalks are normal. No finite normalization,
nonempty-open or supplied projection-isomorphism hypothesis is needed. -/
theorem projection_isIso_on_normal_open (W : Z.Opens)
    (hN : ∀ z : Z, z ∈ W → IsIntegrallyClosed (Z.presheaf.stalk z)) :
    IsIso (projection Z ∣_ W) := by
  change (MorphismProperty.isomorphisms _) (projection Z ∣_ W)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _) _
    (iSup_nonemptyAffineOpen_eq_top W.toScheme)]
  rintro ⟨⟨V, hV⟩, hne⟩
  let U : Z.Opens := W.ι ''ᵁ V
  let : Nonempty U := by
    let x : V := Classical.choice hne
    exact ⟨⟨W.ι (x : W.toScheme), (x : W.toScheme), x.property, rfl⟩⟩
  have hUW : U ≤ W := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact x.property
  have : IsIso (projection Z ∣_ U) := projection_isIso_on_normal_affine Z U
    (hV.image_of_isOpenImmersion W.ι) (fun z hz => hN z (hUW hz))
  exact (MorphismProperty.arrow_mk_iso_iff (.isomorphisms _)
    (morphismRestrictRestrict (projection Z) W V)).mpr inferInstance

end EnvelopeProperty.IntegralSchemeNormalization
