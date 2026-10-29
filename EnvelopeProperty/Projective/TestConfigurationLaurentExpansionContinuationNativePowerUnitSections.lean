import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationOriginalResiduePowerFrames

/-! # Actual native inverse-unit sections are genuine generic powers -/
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open scoped NNReal TensorProduct Classical
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich Scheme.Modules CanonicalGeometry TestConfigurationSectionTransport
open SchemeModuleFrameCoefficients

/-- The TRUE actual explicit left unit evaluates every literal original pure section tensor. -/
theorem originalBundleTensorLeftUnitIso_tensorSection {Y : Scheme.{u}}
    (M : Y.Modules) (U : Y.Opens) (a : Γ(Y, U)) (s : Γ(M, U)) :
    (bundleTensorLeftUnitIso M).hom.val.app (op U)
      (tensorSection (unitObj Y) M U a s) = a • s := by
  let : MonoidalCategory Y.PresheafOfModules := PresheafOfModules.monoidalCategory (R := Y.sheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  have he := (adj.homEquiv (bundleTensorPresheaf (unitObj Y) M) M).apply_symm_apply
    (MonoidalCategory.leftUnitor M.val).hom
  have hs := congrArg (fun α => (α.app (op U)).hom (a ⊗ₜ[Γ(Y, U)] s)) he
  change (bundleTensorLeftUnitIso M).hom.val.app (op U)
    (tensorSection (unitObj Y) M U a s) =
      (MonoidalCategory.leftUnitor (ModuleCat.of Γ(Y, U) (Γ(M, U)))).hom
        (a ⊗ₜ[Γ(Y, U)] s) at hs
  exact hs.trans (ModuleCat.MonoidalCategory.leftUnitor_hom_apply a s)

/-- The actual coherent tensor section maps to the SAME original sheafification-unit pure tensor. -/
theorem originalMonoidalTensorSection_explicit {Y : Scheme.{u}}
    (M N : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    (ModularCurves.monoidalTensorObjIso M N).hom.val.app (op U)
      (ModularCurves.tensorSection M N U s t) = tensorSection M N U s t := by
  exact congrArg (fun q => q.val.app (op U) (tensorSection M N U s t))
    (ModularCurves.monoidalTensorObjIso M N).inv_hom_id

section Generic
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {Y : Scheme.{u}} {q : Y ⟶ Spec (CommRingCat.of R)}
  (y : RelativeSchemeValuedPoint v q)

/-- The TRUE native pullback tensorator transports the SAME actual generic pure section. -/
theorem originalCanonicalPullback_genericTensorSection {M N : Y.Modules}
    (s : Γ(RelativeSchemeValuedPoint.genericLineModule y M, ⊤))
    (t : Γ(RelativeSchemeValuedPoint.genericLineModule y N, ⊤)) :
    (canonicalTensorPullbackIso (Y.fromSpecResidueField y.1.point) M N).hom.val.app (op ⊤)
        (RelativeSchemeValuedPoint.genericTensorSection y s t) =
      tensorSection (RelativeSchemeValuedPoint.genericLineModule y M)
        (RelativeSchemeValuedPoint.genericLineModule y N) ⊤ s t := by
  let f := Y.fromSpecResidueField y.1.point
  let : MonoidalCategory Y.Modules := Scheme.Modules.monoidalCategory Y
  let : MonoidalCategory (Spec (CommRingCat.of (Y.residueField y.1.point))).Modules :=
    Scheme.Modules.monoidalCategory _
  let : (pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
  let μ := Functor.Monoidal.μIso (pullback f) M N
  let k := ModularCurves.monoidalTensorObjIso M N
  let kx := ModularCurves.monoidalTensorObjIso ((pullback f).obj M) ((pullback f).obj N)
  have hc : (μ.hom ≫ (pullback f).map k.hom) ≫ (canonicalTensorPullbackIso f M N).hom = kx.hom := by
    change (μ.hom ≫ (pullback f).map k.hom) ≫
      ((pullback f).map k.inv ≫ μ.inv ≫ kx.hom) = kx.hom
    have hk : (pullback f).map k.hom ≫ (pullback f).map k.inv ≫ μ.inv ≫ kx.hom = μ.inv ≫ kx.hom :=
      Iso.hom_inv_id_assoc ((pullback f).mapIso k) _
    calc
      _ = μ.hom ≫ ((pullback f).map k.hom ≫ (pullback f).map k.inv ≫ μ.inv ≫ kx.hom) := by
        simp only [Category.assoc]
      _ = μ.hom ≫ μ.inv ≫ kx.hom := congrArg (fun a => μ.hom ≫ a) hk
      _ = _ := Iso.hom_inv_id_assoc μ _
  have hv := congrArg (fun a => a.val.app (op ⊤)
    (ModularCurves.tensorSection ((pullback f).obj M) ((pullback f).obj N) ⊤ s t)) hc
  exact hv.trans (originalMonoidalTensorSection_explicit _ _ ⊤ s t)

/-- Literal coefficients in the actual constructed explicit tensor frame multiply. -/
theorem originalGenericTensorFrame_coefficient {M N : Y.Modules}
    (e : RelativeSchemeValuedPoint.genericLineModule y M ≅ unitObj (Spec (CommRingCat.of (Y.residueField y.1.point))))
    (d : RelativeSchemeValuedPoint.genericLineModule y N ≅ unitObj (Spec (CommRingCat.of (Y.residueField y.1.point))))
    (s : Γ(RelativeSchemeValuedPoint.genericLineModule y M, ⊤))
    (t : Γ(RelativeSchemeValuedPoint.genericLineModule y N, ⊤)) :
    coefficient (canonicalTensorPullbackIso (Y.fromSpecResidueField y.1.point) M N ≪≫
        tensorObjCongr e d ≪≫ bundleTensorLeftUnitIso (unitObj (Spec (CommRingCat.of (Y.residueField y.1.point)))))
      (RelativeSchemeValuedPoint.genericTensorSection y s t) = coefficient e s * coefficient d t := by
  change (bundleTensorLeftUnitIso _).hom.val.app (op ⊤)
      ((bundleTensorIso e d).hom.val.app (op ⊤)
        ((canonicalTensorPullbackIso _ M N).hom.val.app (op ⊤)
          (RelativeSchemeValuedPoint.genericTensorSection y s t))) = _
  erw [originalCanonicalPullback_genericTensorSection y s t, bundleTensorIso_tensorSection,
    originalBundleTensorLeftUnitIso_tensorSection]
  rfl

/-- The SAME actual generic power section has original coefficient one in its actual power frame. -/
theorem originalGenericPowerFrame_coefficient_unit {M : Y.Modules}
    (e : RelativeSchemeValuedPoint.genericLineModule y M ≅ unitObj (Spec (CommRingCat.of (Y.residueField y.1.point))))
    (m : ℕ) :
    coefficient (tensorPowerPullbackIso (Y.fromSpecResidueField y.1.point) M m ≪≫
        bundleTensorPowerTrivialization e m)
      (ModelNorm.genericPowerSection y (unitSection e) m) = 1 := by
  induction m with
  | zero =>
    exact congrArg (fun a => a.val.app (op ⊤) (1 : Γ(Spec (CommRingCat.of (Y.residueField y.1.point)), ⊤)))
      (pullbackUnitIso (Y.fromSpecResidueField y.1.point)).inv_hom_id
  | succ m ih =>
    let f := Y.fromSpecResidueField y.1.point
    let em := tensorPowerPullbackIso f M m ≪≫ bundleTensorPowerTrivialization e m
    have he : tensorPowerPullbackIso f M (m + 1) ≪≫ bundleTensorPowerTrivialization e (m + 1) =
        canonicalTensorPullbackIso f (bundleTensorPower M m) M ≪≫ tensorObjCongr em e ≪≫
          bundleTensorLeftUnitIso (unitObj (Spec (CommRingCat.of (Y.residueField y.1.point)))) := by
      change (canonicalTensorPullbackIso f (bundleTensorPower M m) M ≪≫
          tensorObjCongr (tensorPowerPullbackIso f M m) (Iso.refl _)) ≪≫
            (tensorObjCongr (bundleTensorPowerTrivialization e m) e ≪≫ bundleTensorLeftUnitIso _) = _
      have ht := tensorObjCongr_trans (tensorPowerPullbackIso f M m)
        (bundleTensorPowerTrivialization e m) (Iso.refl ((pullback f).obj M)) e
      rw [show tensorObjCongr em e = tensorObjCongr (tensorPowerPullbackIso f M m) (Iso.refl _) ≪≫
        tensorObjCongr (bundleTensorPowerTrivialization e m) e from by
          simpa only [em, f, RelativeSchemeValuedPoint.genericLineModule, Iso.refl_trans] using ht]
      exact Iso.trans_assoc _ _ _
    rw [he]
    change coefficient (canonicalTensorPullbackIso f (bundleTensorPower M m) M ≪≫ tensorObjCongr em e ≪≫
        bundleTensorLeftUnitIso _) (RelativeSchemeValuedPoint.genericTensorSection y
          (ModelNorm.genericPowerSection y (unitSection e) m) (unitSection e)) = 1
    rw [originalGenericTensorFrame_coefficient, coefficient_unitSection, mul_one]
    exact ih

/-- The TRUE inverse-unit power-frame section is the SAME actual native generic power section. -/
theorem originalGenericPowerFrame_unitSection {M : Y.Modules}
    (e : RelativeSchemeValuedPoint.genericLineModule y M ≅ unitObj (Spec (CommRingCat.of (Y.residueField y.1.point))))
    (m : ℕ) :
    unitSection (tensorPowerPullbackIso (Y.fromSpecResidueField y.1.point) M m ≪≫
        bundleTensorPowerTrivialization e m) = ModelNorm.genericPowerSection y (unitSection e) m := by
  have h := eq_coefficient_smul_unitSection
    (tensorPowerPullbackIso (Y.fromSpecResidueField y.1.point) M m ≪≫ bundleTensorPowerTrivialization e m)
    (ModelNorm.genericPowerSection y (unitSection e) m)
  rw [originalGenericPowerFrame_coefficient_unit, one_smul] at h
  exact h.symm

/-- Genuine native proper-model inverse-unit norms are actual degree-one M-frame norm powers, ALL m0. -/
theorem originalGenericPowerFrame_unitSection_modelNorm [IsProper q]
    (hb : ∀ a, v a ≤ 1) {M : Y.Modules} (hM : IsInvertible M)
    (e : RelativeSchemeValuedPoint.genericLineModule y M ≅ unitObj (Spec (CommRingCat.of (Y.residueField y.1.point))))
    (m : ℕ) :
    RelativeSchemeValuedPoint.modelLineNorm hb y (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m)
      (unitSection (tensorPowerPullbackIso (Y.fromSpecResidueField y.1.point) M m ≪≫
        bundleTensorPowerTrivialization e m)) =
      (RelativeSchemeValuedPoint.modelLineNorm hb y hM (unitSection e)) ^ m := by
  rw [originalGenericPowerFrame_unitSection]
  exact ModelNorm.modelLineNorm_genericPowerSection hb y hM (unitSection e) m

end Generic
end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
