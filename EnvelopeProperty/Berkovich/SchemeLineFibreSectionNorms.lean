/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLineSectionEvaluation
import EnvelopeProperty.Berkovich.SchemeLineDualTransposeNorms

/-! # Actual original global section norms on the true original generic fiber -/

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

/-- The TRUE original generic section of an actual whole original
unit-to-line morphism has norm EXACTLY its genuine model morphism norm. -/
theorem modelLineNorm_fibreSection {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (σ : Scheme.Modules.unitObj X ⟶ M) :
    modelLineNorm hb y hM (fibreSection y σ) =
      modelHomNorm hb y (Scheme.Modules.isInvertible_unit (X := X)) hM σ := by
  let e := Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField y.1.point)
  let u : Γ(genericLineModule y (Scheme.Modules.unitObj X), ⊤) :=
    (e.inv.val.app (op ⊤)).hom (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤))
  have hi : (e.hom.val.app (op ⊤)).hom u =
      (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤)) :=
    congrArg (fun q => (q.val.app (op ⊤)).hom
      (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤))) e.inv_hom_id
  have hv := congrArg (fun a : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤) =>
    y.1.residueVal ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom a)) hi
  simp only [map_one] at hv
  have hu : modelLineNorm hb y (Scheme.Modules.isInvertible_unit (X := X)) u = 1 :=
    (modelLineNorm_unit hb y u).trans hv
  have h := modelLineNorm_mapHom_eq hb y (Scheme.Modules.isInvertible_unit (X := X)) hM σ u
  rw [hu, mul_one] at h
  exact h

/-- The ACTUAL original fiber section of the canonical dual Cartier
inclusion has EXACTLY its intrinsic original ideal norm. -/
theorem modelLineNorm_dualCartierFibreSection (I : X.IdealSheafData) (hI : I.IsInvertible) :
    (modelLineNorm hb y hI.isInvertibleModule_toModules.dual
      (fibreSection y (hI.isInvertibleModule_toModules.dualTranspose I.toModulesInclusion)) : ℝ≥0∞) =
      modelIdealNorm I hb y := by
  rw [modelLineNorm_fibreSection]
  exact modelHomNorm_dualCartierInclusion hb y I hI

/-- The TRUE actual dual Cartier fiber section logarithmic norm is the
intrinsic original model ideal logarithm, including zero norms. -/
theorem modelLineNorm_dualCartierFibreSection_log (I : X.IdealSheafData) (hI : I.IsInvertible) :
    ENNReal.log (modelLineNorm hb y hI.isInvertibleModule_toModules.dual
      (fibreSection y (hI.isInvertibleModule_toModules.dualTranspose I.toModulesInclusion)) : ℝ≥0∞) =
      modelIdealLog I hb y :=
  congrArg ENNReal.log (modelLineNorm_dualCartierFibreSection hb y I hI)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
