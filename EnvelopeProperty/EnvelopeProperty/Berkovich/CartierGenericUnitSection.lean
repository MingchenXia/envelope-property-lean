/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLineGenericIsomorphisms

/-! # Canonical genuine Cartier generic unit sections and original model norms -/

open scoped NNReal ENNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
variable [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)

/-- The ACTUAL whole generic Cartier inclusion, with true native unit
comparison, is a genuine frame whenever its intrinsic ideal norm is nonzero. -/
def genericIdealInclusionIso (I : X.IdealSheafData) (hI : I.IsInvertible)
    (hn : modelIdealNorm I hb y ≠ 0) :
    genericLineModule y I.toModules ≅ Scheme.Modules.unitObj
      (Spec (CommRingCat.of (X.residueField y.1.point))) := by
  have := (modelIdealNorm_ne_zero_iff_isIso_genericInclusion hb y I hI).mp hn
  exact asIso ((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map I.toModulesInclusion) ≪≫
    Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField y.1.point)

/-- The derived ACTUAL original frame is the whole genuine pulled inclusion. -/
theorem genericIdealInclusionIso_hom (I : X.IdealSheafData) (hI : I.IsInvertible)
    (hn : modelIdealNorm I hb y ≠ 0) :
    (genericIdealInclusionIso hb y I hI hn).hom =
      (Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map I.toModulesInclusion ≫
        (Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField y.1.point)).hom := rfl

/-- The canonical ACTUAL original generic Cartier section with true
original rational inclusion coefficient one. -/
def genericIdealUnitSection (I : X.IdealSheafData) (hI : I.IsInvertible)
    (hn : modelIdealNorm I hb y ≠ 0) : Γ(genericLineModule y I.toModules, ⊤) :=
  ((genericIdealInclusionIso hb y I hI hn).inv.val.app (op ⊤)).hom
    (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤))

/-- The TRUE whole original inclusion frame maps the canonical ACTUAL
original generic Cartier section to the original unit section. -/
theorem genericIdealUnitSection_coefficient (I : X.IdealSheafData) (hI : I.IsInvertible)
    (hn : modelIdealNorm I hb y ≠ 0) :
    (((genericIdealInclusionIso hb y I hI hn).hom.val.app (op ⊤)).hom
      (genericIdealUnitSection hb y I hI hn) : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤)) =
      (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤)) :=
  congrArg (fun q => (q.val.app (op ⊤)).hom
    (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤)))
    (genericIdealInclusionIso hb y I hI hn).inv_hom_id

/-- The true original inclusion norm times the genuine norm of the
canonical ACTUAL generic Cartier unit section is exactly one. -/
theorem modelLineNorm_genericIdealUnitSection_mul (I : X.IdealSheafData) (hI : I.IsInvertible)
    (hn : modelIdealNorm I hb y ≠ 0) :
    modelHomNorm hb y hI.isInvertibleModule_toModules
        (Scheme.Modules.isInvertible_unit (X := X)) I.toModulesInclusion *
      modelLineNorm hb y hI.isInvertibleModule_toModules (genericIdealUnitSection hb y I hI hn) = 1 := by
  have h := modelLineNorm_mapHom_eq hb y hI.isInvertibleModule_toModules
    (Scheme.Modules.isInvertible_unit (X := X)) I.toModulesInclusion
    (genericIdealUnitSection hb y I hI hn)
  have hi := genericIdealUnitSection_coefficient hb y I hI hn
  rw [genericIdealInclusionIso_hom] at hi
  rw [modelLineNorm_unit] at h
  change (Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField y.1.point)).hom.val.app (op ⊤)
      (((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map I.toModulesInclusion).val.app (op ⊤)
        (genericIdealUnitSection hb y I hI hn)) = (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤)) at hi
  have hv := congrArg (fun a : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤) =>
    y.1.residueVal ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom a)) hi
  simp only [map_one] at hv
  exact h.symm.trans hv

/-- The ACTUAL original canonical generic Cartier section has model
norm reciprocal to the derived original Cartier inclusion norm. -/
theorem modelLineNorm_genericIdealUnitSection (I : X.IdealSheafData) (hI : I.IsInvertible)
    (hn : modelIdealNorm I hb y ≠ 0) :
    modelLineNorm hb y hI.isInvertibleModule_toModules (genericIdealUnitSection hb y I hI hn) =
      (modelHomNorm hb y hI.isInvertibleModule_toModules
        (Scheme.Modules.isInvertible_unit (X := X)) I.toModulesInclusion)⁻¹ := by
  have ha : modelHomNorm hb y hI.isInvertibleModule_toModules
      (Scheme.Modules.isInvertible_unit (X := X)) I.toModulesInclusion ≠ 0 := by
    intro h
    apply hn
    rw [← modelHomNorm_idealInclusion I hI hb y, h, ENNReal.coe_zero]
  apply mul_left_cancel₀ ha
  rw [mul_inv_cancel₀ ha]
  exact modelLineNorm_genericIdealUnitSection_mul hb y I hI hn

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
