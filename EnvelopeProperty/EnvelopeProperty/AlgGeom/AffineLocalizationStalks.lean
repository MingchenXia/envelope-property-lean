import EnvelopeProperty.AlgGeom.SpecLocalizationStalks

/-! # True ORIGINAL affine localization stalk and residue maps -/
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.AffineLocalizationStalks
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : Y ⟶ X)

/-- A literal original affine section localization derives isomorphism of
EVERY SAME native original stalk map, without any stalk comparison input. -/
theorem stalkMap_isIso (M : Submonoid Γ(X, ⊤))
    (h : letI := g.appTop.hom.toAlgebra; IsLocalization M Γ(Y, ⊤)) (y : Y) :
    IsIso (g.stalkMap y) := by
  let := g.appTop.hom.toAlgebra
  let := h
  let q : Spec Γ(Y, ⊤) ⟶ Spec Γ(X, ⊤) := Spec.map g.appTop
  let : IsIso (q.stalkMap (Y.isoSpec.hom y)) :=
    SpecLocalizationStalks.stalkMap_isIso M (Y.isoSpec.hom y)
  let : IsIso ((Y.isoSpec.hom ≫ q).stalkMap y) := by
    rw [Scheme.Hom.stalkMap_comp]
    infer_instance
  have hh : IsIso ((g ≫ X.isoSpec.hom).stalkMap y) := by
    rw [Scheme.Hom.stalkMap_congr_hom _ _ (Scheme.isoSpec_hom_naturality g).symm]
    infer_instance
  rw [Scheme.Hom.stalkMap_comp] at hh
  exact (isIso_comp_left_iff _ _).mp hh

/-- The SAME original affine localization map derives every actual native
residue-field isomorphism, without a supplied residue-degree or action match. -/
theorem residueFieldMap_isIso (M : Submonoid Γ(X, ⊤))
    (h : letI := g.appTop.hom.toAlgebra; IsLocalization M Γ(Y, ⊤)) (y : Y) :
    IsIso (g.residueFieldMap y) := by
  let := stalkMap_isIso g M h y
  exact (IsLocalRing.ResidueField.mapEquiv
    (asIso (g.stalkMap y)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

end EnvelopeProperty.AffineLocalizationStalks
