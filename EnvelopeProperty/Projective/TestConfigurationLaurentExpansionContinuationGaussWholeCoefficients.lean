import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussSectionEvaluation
import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussOriginalLineFrame

/-! # Actual original whole H0 in the original model-power Laurent frame

The original native section-Hom and actual whole Gamma values are inverse.
Genuine pullback comparison/unit laws transport the original model-power H0;
the original geometric source data internally construct its actual frames.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped NNReal LaurentPolynomial Classical
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich SchemeLineSectionEvaluation Scheme.Modules SchemeLineSectionUnitFrames CanonicalGeometry

/-- The actual original whole section-Hom recovers EVERY original section morphism. -/
theorem originalTopSectionHom_sectionAtOne {B : Scheme.{u}} {N : B.Modules}
    (α : unitObj B ⟶ N) : topSectionHom N (sectionAtOne α) = α := by
  apply SheafOfModules.hom_ext
  ext U
  let i := (homOfLE (le_top : U.unop ≤ (⊤ : B.Opens))).op
  change (1 : Γ(B, U.unop)) • N.presheaf.map i (sectionAtOne α) =
    α.val.app U (show Γ(B, U.unop) from 1)
  rw [one_smul]
  have hn := PresheafOfModules.naturality_apply α.val i (show Γ(B, ⊤) from 1)
  change α.val.app U (B.presheaf.map i (show Γ(B, ⊤) from 1)) =
    N.presheaf.map i (sectionAtOne α) at hn
  have hi : B.presheaf.map i (show Γ(B, ⊤) from 1) =
      (show Γ(B, U.unop) from 1) := map_one _
  rw [hi] at hn
  exact hn.symm

/-- The SAME original adjunction-unit whole section is the actual pulled section Hom. -/
theorem originalTopSectionHom_pullbackUnit {A B : Scheme.{u}} (g : B ⟶ A)
    (M : A.Modules) (s : Γ(M, ⊤)) :
    topSectionHom ((pullback g).obj M) (affinePullbackUnitTop g M s) =
      pullbackSectionHom g (topSectionHom M s) := by
  rw [← originalPullbackUnitTop_sectionAtOne g M s]
  exact originalTopSectionHom_sectionAtOne _

/-- Genuine module isomorphisms preserve the SAME original framed whole section values. -/
theorem originalFramedGlobalPullback_moduleIso {A B : Scheme.{u}} (g : B ⟶ A)
    {M N : A.Modules} (σ : M ≅ N)
    (E : (pullback g).obj N ≅ unitObj B) (s : Γ(M, ⊤)) :
    originalFramedGlobalPullback g M ((pullback g).mapIso σ ≪≫ E) s =
      originalFramedGlobalPullback g N E (σ.hom.val.app (op ⊤) s) := by
  rw [originalFramedGlobalPullback_apply, originalFramedGlobalPullback_apply,
    ← originalTopSectionHom_postcomp σ.hom s]
  simp only [frameScalar, pullbackSectionHom, Functor.map_comp, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]

/-- Genuine original pullbackComp preserves the actual whole-adjunction-unit section. -/
theorem originalFramedGlobalPullback_comp {A B D : Scheme.{u}}
    (g : B ⟶ A) (p : A ⟶ D) (L : D.Modules)
    (E : (pullback (g ≫ p)).obj L ≅ unitObj B) (s : Γ(L, ⊤)) :
    originalFramedGlobalPullback g ((pullback p).obj L)
        ((pullbackComp g p).app L ≪≫ E) (affinePullbackUnitTop p L s) =
      originalFramedGlobalPullback (g ≫ p) L E s := by
  rw [originalFramedGlobalPullback_apply, originalFramedGlobalPullback_apply,
    originalTopSectionHom_pullbackUnit p L s]
  simp only [frameScalar, Iso.trans_hom, Iso.app_hom, ← Category.assoc]
  rw [pullbackSectionHom_comp]

/-- Project an actual frame at the SAME original section value, first at abstract schemes. -/
theorem originalFrameScalar_apply {B : Scheme.{u}} {N : B.Modules}
    (E : N ≅ unitObj B) (α : unitObj B ⟶ N) :
    frameScalar E α = E.hom.val.app (op ⊤) (sectionAtOne α) := by
  rfl

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X) {v : Valuation k ℝ≥0}
  (x : RelativeSchemeValuedPoint v X.hom)
  (M : C.total.Modules) (L : X.left.Modules)
  (linearization :
    (pullback (originalTestConfigurationTotalAction C).left).obj M ≅
      (pullback
        (CartesianMonoidalCategory.snd (ProjBerk.nativeMultiplicativeGroup k)
          (NativeTestConfiguration.totalOver k C.projection)).left).obj M)
  (fibreOneIdentification :
    (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L)
  (m : ℕ)
  (e : (pullback (X.left.fromSpecResidueField x.1.point)).obj (bundleTensorPower L m) ≅
    unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point))))

/-- Original geometric source data construct the ACTUAL Laurent frame in EVERY power, including0. -/
def originalTestConfigurationGaussModelPowerFrame :
    (pullback (originalTestConfigurationGaussMorph C x ≫ C.unitOpen.ι)).obj
        (bundleTensorPower M m) ≅
      unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])) :=
  ((pullbackComp (originalTestConfigurationGaussMorph C x) C.unitOpen.ι).app
      (bundleTensorPower M m)).symm ≪≫
    (pullback (originalTestConfigurationGaussMorph C x)).mapIso
      (originalTestConfigurationModelPowerUnitIso C M L linearization fibreOneIdentification m) ≪≫
    (pullbackComp (originalTestConfigurationGaussMorph C x)
      (originalTestConfigurationUnitProjection C)).app (bundleTensorPower L m) ≪≫
    originalTestConfigurationGaussProjectionLineFrame C x (bundleTensorPower L m) e

/-- EVERY original model-power section retains its SAME actual section/unit pairing. -/
theorem originalTestConfigurationGaussModelPowerFrame_sectionHom
    (α : unitObj C.total ⟶ bundleTensorPower M m) :
    pullbackSectionHom (originalTestConfigurationGaussMorph C x ≫ C.unitOpen.ι) α ≫
        (originalTestConfigurationGaussModelPowerFrame C x M L linearization
          fibreOneIdentification m e).hom =
      pullbackSectionHom (originalTestConfigurationGaussMorph C x)
          (pullbackSectionHom C.unitOpen.ι α ≫
            (originalTestConfigurationModelPowerUnitIso C M L linearization
              fibreOneIdentification m).hom) ≫
        ((pullbackComp (originalTestConfigurationGaussMorph C x)
          (originalTestConfigurationUnitProjection C)).app (bundleTensorPower L m) ≪≫
          originalTestConfigurationGaussProjectionLineFrame C x (bundleTensorPower L m) e).hom := by
  rw [← pullbackSectionHom_comp (originalTestConfigurationGaussMorph C x) C.unitOpen.ι α]
  simp only [originalTestConfigurationGaussModelPowerFrame, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.app_inv, Iso.hom_inv_id_app_assoc, pullbackSectionHom,
    Functor.map_comp]

/-- The ACTUAL original whole H0 power map retains the SAME constructed Laurent frame. -/
theorem originalTestConfigurationGaussModelPowerFrame_whole
    (s : Γ(bundleTensorPower M m, ⊤)) :
    originalFramedGlobalPullback (originalTestConfigurationGaussMorph C x ≫ C.unitOpen.ι)
        (bundleTensorPower M m)
        (originalTestConfigurationGaussModelPowerFrame C x M L linearization
          fibreOneIdentification m e) s =
      originalFramedGlobalPullback (originalTestConfigurationGaussMorph C x)
        ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m))
        ((pullbackComp (originalTestConfigurationGaussMorph C x)
          (originalTestConfigurationUnitProjection C)).app (bundleTensorPower L m) ≪≫
          originalTestConfigurationGaussProjectionLineFrame C x (bundleTensorPower L m) e)
        ((originalTestConfigurationModelPowerSectionsIso C M L linearization
          fibreOneIdentification m).hom (affinePullbackUnitTop C.unitOpen.ι
            (bundleTensorPower M m) s)) := by
  change _ = originalFramedGlobalPullback (originalTestConfigurationGaussMorph C x)
    ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m)) _
    ((originalTestConfigurationModelPowerUnitIso C M L linearization
      fibreOneIdentification m).hom.val.app (op ⊤)
        (affinePullbackUnitTop C.unitOpen.ι (bundleTensorPower M m) s))
  rw [originalFramedGlobalPullback_apply, originalFramedGlobalPullback_apply,
    ← originalTopSectionHom_postcomp
      (originalTestConfigurationModelPowerUnitIso C M L linearization
        fibreOneIdentification m).hom
      (affinePullbackUnitTop C.unitOpen.ι (bundleTensorPower M m) s),
    originalTopSectionHom_pullbackUnit C.unitOpen.ι (bundleTensorPower M m) s]
  exact congrArg (fun α : unitObj (Spec (CommRingCat.of
      (X.left.residueField x.1.point)[T;T⁻¹])) ⟶ unitObj (Spec (CommRingCat.of
      (X.left.residueField x.1.point)[T;T⁻¹])) => sectionAtOne α)
    (originalTestConfigurationGaussModelPowerFrame_sectionHom C x M L linearization
      fibreOneIdentification m e (topSectionHom (bundleTensorPower M m) s))

/-- The ENTIRE actual original parameter coefficient map pulls back by the genuine Gauss square. -/
theorem originalTestConfigurationGauss_parameter_coefficient (F : k[T;T⁻¹]) :
    (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom
        ((originalTestConfigurationGaussMorph C x).appTop.hom
          (ProperBirationalSections.coefficientMap (originalTestConfigurationUnitParameter C) F)) =
      AddMonoidAlgebra.mapRingHom ℤ (RelativeSchemeValuedPoint.residueBaseMap x) F := by
  have hq : (originalTestConfigurationUnitParameter C).appTop ≫
      (originalTestConfigurationGaussMorph C x).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom =
    (Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).hom ≫ CommRingCat.ofHom
      (AddMonoidAlgebra.mapRingHom ℤ (RelativeSchemeValuedPoint.residueBaseMap x)) := by
    rw [← Category.assoc, ← Scheme.Hom.comp_appTop,
      originalTestConfigurationGaussMorph_parameter, Scheme.ΓSpecIso_naturality]
  have ht := congrArg
    (fun a : Γ(Spec (CommRingCat.of k[T;T⁻¹]), ⊤) ⟶
        CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹] =>
      a ((Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).inv F)) hq
  change (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom
      ((originalTestConfigurationGaussMorph C x).appTop
        ((originalTestConfigurationUnitParameter C).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).inv F))) =
    AddMonoidAlgebra.mapRingHom ℤ (RelativeSchemeValuedPoint.residueBaseMap x)
      ((Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).hom
        ((Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).inv F)) at ht
  have hi : (Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).hom
      ((Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).inv F) = F :=
    (Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).commRingCatIsoToRingEquiv.apply_symm_apply F
  rw [hi] at ht
  exact ht

/-- EVERY actual original pulled power-section monomial has its literal original Laurent scalar. -/
theorem originalTestConfigurationGauss_power_monomial_coefficient (n : ℤ)
    (a : originalBaseSections X.hom (bundleTensorPower L m)) :
    (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom
      (originalFramedGlobalPullback (originalTestConfigurationGaussMorph C x)
        ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m))
        ((pullbackComp (originalTestConfigurationGaussMorph C x)
          (originalTestConfigurationUnitProjection C)).app (bundleTensorPower L m) ≪≫
          originalTestConfigurationGaussProjectionLineFrame C x (bundleTensorPower L m) e)
        ((LaurentPolynomial.T n : k[T;T⁻¹]) •
          (show originalBaseSections (originalTestConfigurationUnitParameter C)
            ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m)) from
              affinePullbackUnitTop (originalTestConfigurationUnitProjection C) (bundleTensorPower L m) a))) =
      LaurentPolynomial.C
        ((Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point))).hom
          (frameScalar e (pullbackSectionHom (X.left.fromSpecResidueField x.1.point)
            (topSectionHom (bundleTensorPower L m) a)))) * LaurentPolynomial.T n := by
  let g := originalTestConfigurationGaussMorph C x
  let p := originalTestConfigurationUnitProjection C
  let E := (pullbackComp g p).app (bundleTensorPower L m) ≪≫
    originalTestConfigurationGaussProjectionLineFrame C x (bundleTensorPower L m) e
  let b : originalBaseSections (originalTestConfigurationUnitParameter C)
      ((pullback p).obj (bundleTensorPower L m)) := affinePullbackUnitTop p (bundleTensorPower L m) a
  have hs := originalFramedGlobalPullback_base_smul g ((pullback p).obj (bundleTensorPower L m)) E
    (ProperBirationalSections.coefficientMap (originalTestConfigurationUnitParameter C)
      (LaurentPolynomial.T n)) b
  change originalFramedGlobalPullback g ((pullback p).obj (bundleTensorPower L m)) E
      ((LaurentPolynomial.T n : k[T;T⁻¹]) • b) = _ at hs
  have ht := congrArg (fun a : Γ(Spec (CommRingCat.of
      (X.left.residueField x.1.point)[T;T⁻¹]), ⊤) =>
        (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom a) hs
  rw [map_mul, originalTestConfigurationGauss_parameter_coefficient,
    originalLaurentCoefficientMap_T] at ht
  have hb : (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom
      (originalFramedGlobalPullback g ((pullback p).obj (bundleTensorPower L m)) E b) =
    LaurentPolynomial.C
      ((Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point))).hom
        (frameScalar e (pullbackSectionHom (X.left.fromSpecResidueField x.1.point)
          (topSectionHom (bundleTensorPower L m) a)))) := by
    change (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom
      (originalFramedGlobalPullback g ((pullback p).obj (bundleTensorPower L m))
        ((pullbackComp g p).app (bundleTensorPower L m) ≪≫
          originalTestConfigurationGaussProjectionLineFrame C x (bundleTensorPower L m) e)
        (affinePullbackUnitTop p (bundleTensorPower L m) a)) = _
    rw [originalFramedGlobalPullback_comp, originalFramedGlobalPullback_apply,
      originalFrameScalar_apply]
    exact originalTestConfigurationGaussProjectionLineFrame_coefficient C x
      (bundleTensorPower L m) e (topSectionHom (bundleTensorPower L m) a)
  exact ht.trans (by rw [hb, mul_comm])

/-- EVERY SAME original whole model-power section INTERNALLY derives UNIQUE original
finite coefficients AND its literal actual Laurent-frame scalar. No decomposition is an input. -/
theorem exists_unique_original_testConfiguration_whole_power_frame_coefficients
    [IsProper X.hom] (hL : IsInvertible L) (s : Γ(bundleTensorPower M m, ⊤)) :
    ∃! c : ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m),
      (c.sum (fun n a => (LaurentPolynomial.T n : k[T;T⁻¹]) •
        (show originalBaseSections (originalTestConfigurationUnitParameter C)
          ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m)) from
            affinePullbackUnitTop (originalTestConfigurationUnitProjection C) (bundleTensorPower L m) a)) =
        (originalTestConfigurationModelPowerSectionsIso C M L linearization
          fibreOneIdentification m).hom (affinePullbackUnitTop C.unitOpen.ι (bundleTensorPower M m) s)) ∧
      (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom
        (originalFramedGlobalPullback (originalTestConfigurationGaussMorph C x ≫ C.unitOpen.ι)
          (bundleTensorPower M m)
          (originalTestConfigurationGaussModelPowerFrame C x M L linearization
            fibreOneIdentification m e) s) =
        c.sum (fun n a => LaurentPolynomial.C
          ((Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point))).hom
            (frameScalar e (pullbackSectionHom (X.left.fromSpecResidueField x.1.point)
              (topSectionHom (bundleTensorPower L m) a)))) * LaurentPolynomial.T n) := by
  classical
  let t := (originalTestConfigurationModelPowerSectionsIso C M L linearization
    fibreOneIdentification m).hom (affinePullbackUnitTop C.unitOpen.ι (bundleTensorPower M m) s)
  obtain ⟨c, hc, huniq⟩ := exists_unique_original_testConfiguration_unit_power_laurent_expansion
    C L hL m t
  refine ⟨c, ⟨hc, ?_⟩, fun d hd => huniq d hd.1⟩
  let E := (pullbackComp (originalTestConfigurationGaussMorph C x)
      (originalTestConfigurationUnitProjection C)).app (bundleTensorPower L m) ≪≫
    originalTestConfigurationGaussProjectionLineFrame C x (bundleTensorPower L m) e
  have hs := congrArg
    (fun q : originalBaseSections (originalTestConfigurationUnitParameter C)
        ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m)) =>
      (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom
        (originalFramedGlobalPullback (originalTestConfigurationGaussMorph C x)
          ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m)) E q)) hc
  have hv : (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom
      (originalFramedGlobalPullback (originalTestConfigurationGaussMorph C x)
        ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m)) E t) =
    c.sum (fun n a => LaurentPolynomial.C
      ((Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point))).hom
        (frameScalar e (pullbackSectionHom (X.left.fromSpecResidueField x.1.point)
          (topSectionHom (bundleTensorPower L m) a)))) * LaurentPolynomial.T n) := by
    simpa only [E, Finsupp.sum, map_sum,
      originalTestConfigurationGauss_power_monomial_coefficient C x L m e] using hs.symm
  exact (congrArg
    (fun a : Γ(Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹]), ⊤) =>
      (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom a)
    (originalTestConfigurationGaussModelPowerFrame_whole C x M L linearization
      fibreOneIdentification m e s)).trans hv

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
