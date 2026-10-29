import EnvelopeProperty.AlgGeom.SchemeProjectiveSectionOpenBasis

/-! # Actual products of original line sections have intersection nonzero opens

Whole native tensor-section pullback, actual local original line frames and
native residue multiplication derive the SAME original product-open law.
Original power addition then retains literal original tensor-power lines.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open MvPolynomial Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeLineSectionProductOpens
open CanonicalGeometry SchemeLineSectionEvaluation SchemeLineSectionUnitFrames
open SchemeModuleCechLineSectionLocalization SchemeTensorSectionHoms
open SchemeProjectiveSectionOpenBasis
attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private noncomputable instance productPullbackMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullback f).Monoidal := pullbackMonoidal f

private theorem tensorSection_frame {X : Scheme.{u}} {M N : X.Modules}
    (a : unitObj X ⟶ M) (b : unitObj X ⟶ N)
    (e : M ≅ unitObj X) (d : N ≅ unitObj X) :
    tensorSectionHom a b ≫ (SchemeTensorPowerFrames.tensorFrame e d).hom =
      ModularCurves.unitEndomorphismOfTopSection (frameScalar e a * frameScalar d b) := by
  have h := tensorSectionHom_precomp_scalars (𝟙 (unitObj X)) (𝟙 (unitObj X))
    (frameScalar e a) (frameScalar d b)
  simp only [Category.comp_id] at h
  change tensorSectionHom a b ≫ (e.hom ⊗ₘ d.hom) ≫
    (ModularCurves.unitObjTensorIso X).hom = _
  rw [← Category.assoc, tensorSectionHom_comp,
    frameScalar_identity e a, frameScalar_identity d b, h]
  simp only [tensorSectionHom, id_tensorHom_id, Category.comp_id,
    Category.assoc, Iso.inv_hom_id]

private theorem sectionAtOne_scalar {X : Scheme.{u}} (r : Γ(X, ⊤)) :
    sectionAtOne (ModularCurves.unitEndomorphismOfTopSection r) = r := by
  change (1 : Γ(X, ⊤)) * X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op r = r
  simp

/-- The literal nonzero-open of the SAME actual native tensor section is
exactly the intersection of the literal original section opens. All local
frames, coefficients and residue-field multiplication are derived internally. -/
theorem tensorSectionHom_open {X : Scheme.{u}} (M N : X.Modules)
    (hM : IsInvertible M) (hN : IsInvertible N)
    (a : unitObj X ⟶ M) (b : unitObj X ⟶ N) :
    sectionOpen (M ⊗ N) (hM.monoidalTensor hN) (tensorSectionHom a b) =
      sectionOpen M hM a ⊓ sectionOpen N hN b := by
  ext x
  obtain ⟨U, hx, _hU, ⟨e⟩, ⟨d⟩⟩ :=
    SchemeCommonAffineLineFrames.exists_in_open M N hM hN x ⊤ (by trivial)
  let E := (Functor.Monoidal.μIso (pullback U.1.ι) M N).symm ≪≫
    SchemeTensorPowerFrames.tensorFrame e d
  let c := frameScalar e (pullbackSectionHom U.1.ι a)
  let r := frameScalar d (pullbackSectionHom U.1.ι b)
  have hc : pullbackSectionHom U.1.ι (tensorSectionHom a b) ≫ E.hom =
      ModularCurves.unitEndomorphismOfTopSection (c * r) := by
    change pullbackSectionHom U.1.ι (tensorSectionHom a b) ≫
      (Functor.Monoidal.μIso (pullback U.1.ι) M N).inv ≫
        (SchemeTensorPowerFrames.tensorFrame e d).hom = _
    rw [← Category.assoc, pullback_tensorSectionHom, tensorSection_frame]
  change (x ∉ (LineSectionZeroIdeal.zeroIdeal (M ⊗ N) (hM.monoidalTensor hN)
      (tensorSectionHom a b)).support) ↔
    (x ∉ (LineSectionZeroIdeal.zeroIdeal M hM a).support ∧
      x ∉ (LineSectionZeroIdeal.zeroIdeal N hN b).support)
  rw [SchemeLineZeroSupportPullback.mem_support_iff_pullback_frame_zero
      (M ⊗ N) (hM.monoidalTensor hN) (tensorSectionHom a b) U.1 x hx E,
    SchemeLineZeroSupportPullback.mem_support_iff_pullback_frame_zero M hM a U.1 x hx e,
    SchemeLineZeroSupportPullback.mem_support_iff_pullback_frame_zero N hN b U.1 x hx d,
    hc, sectionAtOne_scalar]
  change (¬ X.evaluation U.1 x hx (U.1.topIso.hom (c * r)) = 0) ↔
    (¬ X.evaluation U.1 x hx (U.1.topIso.hom c) = 0 ∧
      ¬ X.evaluation U.1 x hx (U.1.topIso.hom r) = 0)
  rw [map_mul, map_mul, mul_eq_zero, not_or]

/-- The actual product of SAME original H-power sections, using the native
whole tensorPowerAddIso into literal H^(m+n). -/
def powerSectionProduct {X : Scheme.{u}} (H : X.Modules) (m n : ℕ)
    (s : unitObj X ⟶ bundleTensorPower H m) (t : unitObj X ⟶ bundleTensorPower H n) :
    unitObj X ⟶ bundleTensorPower H (m + n) :=
  tensorSectionHom s t ≫ (TensorPowerBaseIdealGrading.tensorPowerAddIso H m n).hom

/-- SAME actual original power-section product has EXACTLY the intersection
of SAME actual factor nonzero opens, with no supplied matching equation. -/
theorem powerSectionProduct_open {X : Scheme.{u}} (H : X.Modules) (hH : IsInvertible H)
    (m n : ℕ) (s : unitObj X ⟶ bundleTensorPower H m) (t : unitObj X ⟶ bundleTensorPower H n) :
    sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (m + n))
      (powerSectionProduct H m n s t) =
    sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH m) s ⊓
      sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH n) t :=
  (sectionOpen_postcompose_iso
    ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hH m).monoidalTensor
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH n))
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (m + n))
    (tensorSectionHom s t) (TensorPowerBaseIdealGrading.tensorPowerAddIso H m n)).trans
      (tensorSectionHom_open _ _
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH m)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH n) s t)

end EnvelopeProperty.SchemeLineSectionProductOpens
