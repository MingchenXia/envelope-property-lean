import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussOriginalLineFrame

/-! # Actual uniform frame-unit factors for the SAME native original model norm

Two genuine whole frames internally construct ONE original global unit.
The original proper-model valuative frame then computes the original norm
in the actual constructed polarization field frame. No coefficient, metric,
unit-open isometry or center-in-unit comparison is assumed.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped NNReal LaurentPolynomial Classical
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich SchemeLineSectionEvaluation Scheme.Modules SchemeLineSectionUnitFrames

/-- Two ACTUAL whole frames derive ONE original unit, uniformly for EVERY original section. -/
theorem originalWholeFrames_unit_coefficient {B : Scheme.{u}} {N : B.Modules}
    (E E' : N ≅ unitObj B) :
    ∃ u : Γ(B, ⊤)ˣ, ∀ α : unitObj B ⟶ N,
      frameScalar E' α = (u : Γ(B, ⊤)) * frameScalar E α := by
  obtain ⟨u, hu⟩ := unitIso_eq_globalUnit (E.symm ≪≫ E')
  have he : E'.hom = E.hom ≫ ModularCurves.unitEndomorphismOfTopSection (u : Γ(B, ⊤)) := by
    have h := congrArg (fun q : unitObj B ≅ unitObj B => E.hom ≫ q.hom) hu
    simpa only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc,
      ModularCurves.unitAutomorphismOfTopUnit_hom] using h
  have hscalar (a r : Γ(B, ⊤)) :
      (ModularCurves.unitEndomorphismOfTopSection r).val.app (op ⊤) a = a * r := by
    rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
    simp only [homOfLE_refl, op_id]
    change a * B.presheaf.map (𝟙 (op (⊤ : B.Opens))) r = a * r
    exact congrArg (fun q : Γ(B, ⊤) ⟶ Γ(B, ⊤) => a * q r)
      (B.presheaf.map_id (op ⊤))
  refine ⟨u, fun α => ?_⟩
  unfold frameScalar
  rw [he]
  change (ModularCurves.unitEndomorphismOfTopSection (u : Γ(B, ⊤))).val.app (op ⊤)
      (show Γ(B, ⊤) from sectionAtOne (α ≫ E.hom)) =
    (u : Γ(B, ⊤)) * (show Γ(B, ⊤) from sectionAtOne (α ≫ E.hom))
  rw [hscalar, mul_comm]

/-- The value of an ACTUAL original field-frame global unit is nonzero. -/
theorem originalFieldFrameUnit_value_ne_zero {K : Type u} [Field K]
    (w : Valuation K ℝ≥0) (u : Γ(Spec (CommRingCat.of K), ⊤)ˣ) :
    w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (u : Γ(Spec (CommRingCat.of K), ⊤))) ≠ 0 :=
  w.ne_zero_of_isUnit _ (u.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom)

variable {K : Type u} [Field K] {Y : Scheme.{u}}
  (f : Spec (CommRingCat.of K) ⟶ Y)

/-- Literal code for the SAME native norm in an actual field frame, including
its original generic and whole section morphisms. This is PROVED below,
never an incoming factor or comparison certificate. -/
def originalFieldModelNormFrameFactorFormula
    {R : Type u} [CommRing R] {vR : Valuation R ℝ≥0}
    (q : Y ⟶ Spec (CommRingCat.of R)) [IsProper q]
    (hb : ∀ a, vR a ≤ 1) (w : Valuation K ℝ≥0)
    (hbase : SchemeValuedPoint.map q (originalFieldValuedPoint f w) =
      SchemeValuedPoint.basePoint vR)
    {M : Y.Modules} (hM : IsInvertible M)
    (E : (pullback f).obj M ≅ unitObj (Spec (CommRingCat.of K))) : Prop :=
  let y : RelativeSchemeValuedPoint vR q := ⟨originalFieldValuedPoint f w, hbase⟩
  ∃ u : Γ(Spec (CommRingCat.of K), ⊤)ˣ,
    w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (u : Γ(Spec (CommRingCat.of K), ⊤))) ≠ 0 ∧
    (∀ β : unitObj (Spec (CommRingCat.of (Y.residueField y.1.point))) ⟶
        RelativeSchemeValuedPoint.genericLineModule y M,
      RelativeSchemeValuedPoint.modelLineNorm hb y (M := M) hM (sectionAtOne β) =
        w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom
          (frameScalar E (originalFieldResidueSectionHom f (M := M) β))) *
        w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (u : Γ(Spec (CommRingCat.of K), ⊤)))) ∧
    (∀ α : unitObj Y ⟶ M,
      RelativeSchemeValuedPoint.modelLineNorm hb y (M := M) hM
          (sectionAtOne (pullbackSectionHom (Y.fromSpecResidueField y.1.point) α)) =
        w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom
          (frameScalar E (pullbackSectionHom f α))) *
        w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (u : Γ(Spec (CommRingCat.of K), ⊤))))

/-- Original properness and invertibility INTERNALLY construct the SAME
nonzero actual frame-unit value, uniformly for ALL original sections. -/
theorem originalFieldModelNorm_frameFactor
    {R : Type u} [CommRing R] {vR : Valuation R ℝ≥0}
    (q : Y ⟶ Spec (CommRingCat.of R)) [IsProper q]
    (hb : ∀ a, vR a ≤ 1) (w : Valuation K ℝ≥0)
    (hbase : SchemeValuedPoint.map q (originalFieldValuedPoint f w) =
      SchemeValuedPoint.basePoint vR)
    {M : Y.Modules} (hM : IsInvertible M)
    (E : (pullback f).obj M ≅ unitObj (Spec (CommRingCat.of K))) :
    originalFieldModelNormFrameFactorFormula f q hb w hbase hM E := by
  dsimp only [originalFieldModelNormFrameFactorFormula]
  let y : RelativeSchemeValuedPoint vR q := ⟨originalFieldValuedPoint f w, hbase⟩
  have hn := originalFieldModelNorm_sectionHom f q hb w hbase hM
  dsimp only [originalFieldModelNormSectionHomFormula] at hn
  obtain ⟨e, he⟩ := hn
  let E_c := originalFieldResidueLineFrame f (M := M)
    (RelativeSchemeValuedPoint.centerFrameGenericIso hb y (M := M) e)
  obtain ⟨u, hu⟩ := originalWholeFrames_unit_coefficient E E_c
  have hframeApply {B : Scheme.{u}} {N : B.Modules}
      (F : N ≅ unitObj B) (α : unitObj B ⟶ N) :
      frameScalar F α = F.hom.val.app (op ⊤) (sectionAtOne α) := by
    rfl
  have hgeneric (β : unitObj (Spec (CommRingCat.of (Y.residueField y.1.point))) ⟶
      RelativeSchemeValuedPoint.genericLineModule y M) :
      RelativeSchemeValuedPoint.modelLineNorm hb y (M := M) hM (sectionAtOne β) =
        w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom
          (frameScalar E (originalFieldResidueSectionHom f (M := M) β))) *
        w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (u : Γ(Spec (CommRingCat.of K), ⊤))) := by
    have hp := congrArg (fun a : Γ(Spec (CommRingCat.of K), ⊤) =>
        w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom a))
      (hframeApply E_c (originalFieldResidueSectionHom f (M := M) β)).symm
    have hv := congrArg (fun a : Γ(Spec (CommRingCat.of K), ⊤) =>
        w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom a))
      (hu (originalFieldResidueSectionHom f (M := M) β))
    rw [map_mul, map_mul, mul_comm] at hv
    exact (he β).trans (hp.trans hv)
  refine ⟨u, originalFieldFrameUnit_value_ne_zero w u, hgeneric, fun α => ?_⟩
  have h := hgeneric (pullbackSectionHom (Y.fromSpecResidueField y.1.point) α)
  have hc := congrArg (fun β : unitObj (Spec (CommRingCat.of K)) ⟶ (pullback f).obj M =>
      w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (frameScalar E β)) *
        w ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (u : Γ(Spec (CommRingCat.of K), ⊤))))
    (originalFieldResidueSectionHom_global f (M := M) α)
  exact h.trans hc

attribute [local instance] originalGaussModelProjectionIsProper

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X)
  (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
  (M : C.total.Modules) (L : X.left.Modules) (hM : IsInvertible M)
  (linearization :
    (pullback (originalTestConfigurationTotalAction C).left).obj M ≅
      (pullback
        (CartesianMonoidalCategory.snd (ProjBerk.nativeMultiplicativeGroup k)
          (NativeTestConfiguration.totalOver k C.projection)).left).obj M)
  (fibreOneIdentification :
    (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L)
  (e : (pullback (X.left.fromSpecResidueField x.1.point)).obj L ≅
    unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point))))
  (r : ℝ≥0) (hr : 0 < r) (hr₁ : r ≤ 1)

/-- The ORIGINAL total model has this uniform nonzero factor in its
ACTUAL CONSTRUCTED polarization field frame. The valuative center may lie
outside the unit open; the factor is not assumed to be one. -/
theorem originalTestConfigurationGaussField_modelNorm_polarizationFactor :
    originalFieldModelNormFrameFactorFormula
      (originalTestConfigurationGaussFieldMorph C x r hr)
      (R := Polynomial k) (vR := gaussValuation (1 : Valuation k ℝ≥0) r) C.projection
      (originalTrivialPolynomialGauss_bounded (k := k) r hr₁)
      (originalNativeLaurentGaussPoint x.1.residueVal r hr).residueVal
      (originalTestConfigurationGaussFieldRelativePoint C x r hr).property hM
      (originalTestConfigurationGaussFieldPolarizationFrame C x M L linearization
        fibreOneIdentification e r hr) :=
  originalFieldModelNorm_frameFactor
    (originalTestConfigurationGaussFieldMorph C x r hr)
    (R := Polynomial k) (vR := gaussValuation (1 : Valuation k ℝ≥0) r) C.projection
    (originalTrivialPolynomialGauss_bounded (k := k) r hr₁)
    (originalNativeLaurentGaussPoint x.1.residueVal r hr).residueVal
    (originalTestConfigurationGaussFieldRelativePoint C x r hr).property hM
    (originalTestConfigurationGaussFieldPolarizationFrame C x M L linearization
      fibreOneIdentification e r hr)

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
