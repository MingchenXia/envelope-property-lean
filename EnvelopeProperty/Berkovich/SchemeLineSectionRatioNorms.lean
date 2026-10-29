import EnvelopeProperty.AlgGeom.SchemeSectionTensorDivision
import EnvelopeProperty.Berkovich.SchemeLineModelTensorNorms
import EnvelopeProperty.Berkovich.GeneratedLineGenericFrameNorms

/-! # Same actual original section ratio and its genuine proper-model norm -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
open scoped NNReal
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) : (pullback f).Monoidal :=
  Scheme.Modules.pullbackMonoidal f
open SchemeLineSectionEvaluation SchemeModuleFrameCoefficients SchemeSectionTensorDivision
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f]
    (hb : ∀ a, v a ≤ 1) (y : RelativeSchemeValuedPoint v f)
    {M T : X.Modules}

include hb in
/-- Nonvanishing of the SAME actual denominator fibre derives the true whole denominator fibre isomorphism. -/
theorem genericSection_isIso_of_ne_zero (hT : IsInvertible T) (β : unitObj X ⟶ T)
    (hβ : fibreSection y β ≠ 0) : IsIso (pullbackSectionHom (X.fromSpecResidueField y.1.point) β) := by
  let e := Classical.choice (exists_centerLineUnitIso hb y hT)
  let d := centerFrameGenericIso hb y e
  let b := pullbackSectionHom (X.fromSpecResidueField y.1.point) β
  let r := SchemeLineSectionUnitFrames.frameScalar d b
  have hr : r ≠ 0 := by
    intro hz
    apply hβ
    have hc : coefficient d (fibreSection y β) = r := rfl
    rw [eq_coefficient_smul_unitSection d (fibreSection y β),hc,hz,zero_smul]
  have hrF : (Scheme.ΓSpecIso (.of (X.residueField y.1.point))).hom.hom r ≠ 0 :=
    (map_ne_zero_iff _ (Scheme.ΓSpecIso (.of (X.residueField y.1.point))).commRingCatIsoToRingEquiv.injective).mpr hr
  have hunit : IsUnit r := by
    have h := (isUnit_iff_ne_zero.mpr hrF).map
      (Scheme.ΓSpecIso (.of (X.residueField y.1.point))).inv.hom
    simpa only [← CommRingCat.comp_apply, Iso.hom_inv_id_apply] using h
  have hu : IsIso (ModularCurves.unitEndomorphismOfTopSection r) := by
    rw [← hunit.unit_spec]
    exact (ModularCurves.unitAutomorphismOfTopUnit hunit.unit).isIso_hom
  have : IsIso (b ≫ d.hom) := by
    rw [SchemeLineSectionUnitFrames.frameScalar_identity]
    exact hu
  exact IsIso.of_isIso_comp_right b d.hom

/-- The actual whole ratio fibre map, constructed by the SAME original numerator/denominator and native tensorator. -/
def fibreRatioHom (hT : IsInvertible T) (α : unitObj X ⟶ M ⊗ T) (β : unitObj X ⟶ T)
    (hβ : fibreSection y β ≠ 0) : unitObj (Spec (X.residueField y.1.point)) ⟶ genericLineModule y M :=
  letI := genericSection_isIso_of_ne_zero hb y hT β hβ
  divide (pullbackSectionHom (X.fromSpecResidueField y.1.point) α ≫ (Functor.Monoidal.μIso (pullback (X.fromSpecResidueField y.1.point)) M T).inv)
    (asIso (pullbackSectionHom (X.fromSpecResidueField y.1.point) β))

/-- The actual SAME original residue-fibre section ratio. -/
def fibreRatio (hT : IsInvertible T) (α : unitObj X ⟶ M ⊗ T) (β : unitObj X ⟶ T)
    (hβ : fibreSection y β ≠ 0) : Γ(genericLineModule y M,⊤) :=
  sectionAtOne (fibreRatioHom hb y hT α β hβ)

/-- The actual original numerator is the native tensor of its genuine ratio and SAME denominator fibres. -/
theorem fibreRatio_tensor (hT : IsInvertible T) (α : unitObj X ⟶ M ⊗ T) (β : unitObj X ⟶ T)
    (hβ : fibreSection y β ≠ 0) :
    ((Functor.Monoidal.μIso (pullback (X.fromSpecResidueField y.1.point)) M T).hom.val.app (op ⊤)).hom
      (ModularCurves.tensorSection _ _ ⊤ (fibreRatio hb y hT α β hβ) (fibreSection y β)) =
      fibreSection y α := by
  let := genericSection_isIso_of_ne_zero hb y hT β hβ
  have h := tensorRight_divide
    (pullbackSectionHom (X.fromSpecResidueField y.1.point) α ≫ (Functor.Monoidal.μIso (pullback (X.fromSpecResidueField y.1.point)) M T).inv)
    (asIso (pullbackSectionHom (X.fromSpecResidueField y.1.point) β))
  have ht := congrArg sectionAtOne h
  rw [sectionAtOne_tensorRight] at ht
  change ModularCurves.tensorSection _ _ ⊤ (fibreRatio hb y hT α β hβ) (fibreSection y β) =
    sectionAtOne (pullbackSectionHom (X.fromSpecResidueField y.1.point) α ≫ (Functor.Monoidal.μIso (pullback (X.fromSpecResidueField y.1.point)) M T).inv) at ht
  refine (congrArg (fun s => ((Functor.Monoidal.μIso (pullback
    (X.fromSpecResidueField y.1.point)) M T).hom.val.app (op ⊤)).hom s) ht).trans ?_
  change sectionAtOne ((pullbackSectionHom (X.fromSpecResidueField y.1.point) α ≫
    (Functor.Monoidal.μIso (pullback (X.fromSpecResidueField y.1.point)) M T).inv) ≫
      (Functor.Monoidal.μIso (pullback (X.fromSpecResidueField y.1.point)) M T).hom) = fibreSection y α
  rw [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rfl

/-- True SAME-numerator model norm equals the product of the actual ratio and SAME-denominator model norms. -/
theorem modelLineNorm_fibreRatio_mul (hM : IsInvertible M) (hT : IsInvertible T)
    (α : unitObj X ⟶ M ⊗ T) (β : unitObj X ⟶ T) (hβ : fibreSection y β ≠ 0) :
    modelLineNorm hb y (hM.monoidalTensor hT) (fibreSection y α) =
      modelLineNorm hb y hM (fibreRatio hb y hT α β hβ) * modelLineNorm hb y hT (fibreSection y β) := by
  have h := modelLineNorm_tensor hb y hM hT (fibreRatio hb y hT α β hβ) (fibreSection y β)
  rw [fibreRatio_tensor] at h
  exact h

/-- Exact original ratio model norm, with denominator nonvanishing derived from its genuine native fibre. -/
theorem modelLineNorm_fibreRatio (hM : IsInvertible M) (hT : IsInvertible T)
    (α : unitObj X ⟶ M ⊗ T) (β : unitObj X ⟶ T) (hβ : fibreSection y β ≠ 0) :
    modelLineNorm hb y hM (fibreRatio hb y hT α β hβ) =
      modelLineNorm hb y (hM.monoidalTensor hT) (fibreSection y α) /
        modelLineNorm hb y hT (fibreSection y β) := by
  have hn : modelLineNorm hb y hT (fibreSection y β) ≠ 0 := by
    exact fun hz => hβ ((modelLineNorm_eq_zero_iff hb y hT _).mp hz)
  exact (eq_div_iff hn).mpr (modelLineNorm_fibreRatio_mul hb y hM hT α β hβ).symm

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
