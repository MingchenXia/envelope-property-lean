import EnvelopeProperty.AlgGeom.SchemeModuleLaurentEvaluation
import EnvelopeProperty.Berkovich.SchemePointLaurentGauss
import EnvelopeProperty.Berkovich.SchemeLinePullbackSections
import EnvelopeProperty.AlgGeom.UnitModuleAutomorphisms

/-! # Native original product-section evaluation in actual original line frames -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped LaurentPolynomial TensorProduct Classical NNReal
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemePointLaurentModuleEvaluation
open SchemeLineSectionEvaluation

private def unitTop {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) :
    Γ(M, ⊤) →+ Γ((Scheme.Modules.pullback g).obj M, ⊤) :=
  (((Scheme.Modules.pullback g).obj M).presheaf.map
    (eqToHom (show (⊤ : Y.Opens) = g ⁻¹ᵁ (⊤ : X.Opens) by simp)).op).hom.comp
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤).hom

private theorem unitTop_smul {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules)
    (r : Γ(X, ⊤)) (m : Γ(M, ⊤)) :
    unitTop g M (r • m) = g.appTop r • unitTop g M m := by
  let N := (Scheme.Modules.pullback g).obj M
  let a := (eqToHom (show (⊤ : Y.Opens) = g ⁻¹ᵁ (⊤ : X.Opens) by simp)).op
  change N.presheaf.map a
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (op ⊤) (r • m)) = _
  erw [(((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (op ⊤)).hom.map_smul]
  erw [N.map_smul]
  apply congrArg (fun z => z • unitTop g M m)
  change g.appLE ⊤ ⊤ (by simp) r = g.appTop r
  erw [← Scheme.Hom.app_eq_appLE]

private theorem unitTop_sectionHom {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules)
    (m : Γ(M, ⊤)) :
    unitTop g M m = sectionAtOne (pullbackSectionHom g (Scheme.Modules.topSectionHom M m)) := by
  let α := pullbackSectionHom g (Scheme.Modules.topSectionHom M m)
  let a := (eqToHom (show (⊤ : Y.Opens) = g ⁻¹ᵁ (⊤ : X.Opens) by simp)).op
  change ((Scheme.Modules.pullback g).obj M).presheaf.map a
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (op ⊤) m) = _
  erw [Scheme.Modules.pullback_unit_app_top_applyT]
  have h := PresheafOfModules.naturality_apply α.val a
    (g.app (⊤ : X.Opens) (show Γ(X, ⊤) from 1))
  change α.val.app (op ⊤)
    (Y.presheaf.map a (g.app (⊤ : X.Opens) (show Γ(X, ⊤) from 1))) = _ at h
  rw [map_one, map_one] at h
  erw [map_one]
  exact h.symm

private theorem unitHom_ext {Z : Scheme.{u}} {N : Z.Modules}
    {α β : Scheme.Modules.unitObj Z ⟶ N}
    (h : sectionAtOne α = sectionAtOne β) : α = β := by
  apply SheafOfModules.hom_ext
  ext V
  let i := (homOfLE (le_top : V.unop ≤ (⊤ : Z.Opens))).op
  have ha := PresheafOfModules.naturality_apply α.val i (show Γ(Z, ⊤) from 1)
  have hb := PresheafOfModules.naturality_apply β.val i (show Γ(Z, ⊤) from 1)
  change α.val.app V (Z.presheaf.map i (show Γ(Z, ⊤) from 1)) =
    N.presheaf.map i (sectionAtOne α) at ha
  change β.val.app V (Z.presheaf.map i (show Γ(Z, ⊤) from 1)) =
    N.presheaf.map i (sectionAtOne β) at hb
  rw [map_one] at ha hb
  exact ha.trans ((congrArg (fun z => N.presheaf.map i z) h).trans hb.symm)

private theorem topSectionHom_sectionAtOne {Z : Scheme.{u}} {N : Z.Modules}
    (α : Scheme.Modules.unitObj Z ⟶ N) :
    Scheme.Modules.topSectionHom N (sectionAtOne α) = α := by
  apply unitHom_ext
  exact Scheme.Modules.topSectionHom_app_top_apply_one N _

private theorem unitTop_hom {Z W : Scheme.{u}} (g : W ⟶ Z) {N : Z.Modules}
    (α : Scheme.Modules.unitObj Z ⟶ N) :
    unitTop g N (sectionAtOne α) = sectionAtOne (pullbackSectionHom g α) := by
  rw [unitTop_sectionHom, topSectionHom_sectionAtOne]

private theorem unitTop_comp {Z W V : Scheme.{u}} (i : V ⟶ W) (g : W ⟶ Z)
    (M : Z.Modules) (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp i g).hom.app M).app ⊤
      (unitTop i ((Scheme.Modules.pullback g).obj M) (unitTop g M m)) =
      unitTop (i ≫ g) M m := by
  rw [unitTop_sectionHom g M m, unitTop_hom, unitTop_sectionHom (i ≫ g) M m]
  exact congrArg sectionAtOne
    (pullbackSectionHom_comp i g (Scheme.Modules.topSectionHom M m))

private def frameCoefficient {B : Type u} [CommRing B] {Z : Scheme.{u}}
    (h : Spec (.of B) ⟶ Z) (M : Z.Modules)
    (e : (Scheme.Modules.pullback h).obj M ≅ Scheme.Modules.unitObj (Spec (.of B))) :
    Γ(M, ⊤) →+ B :=
  (Scheme.ΓSpecIso (.of B)).hom.hom.toAddMonoidHom.comp
    ((e.hom.app ⊤).hom.comp (unitTop h M))

private theorem frameCoefficient_smul {B : Type u} [CommRing B] {Z : Scheme.{u}}
    (h : Spec (.of B) ⟶ Z) (M : Z.Modules)
    (e : (Scheme.Modules.pullback h).obj M ≅ Scheme.Modules.unitObj (Spec (.of B)))
    (r : Γ(Z, ⊤)) (m : Γ(M, ⊤)) :
    frameCoefficient h M e (r • m) =
      (Scheme.ΓSpecIso (.of B)).hom (h.appTop r) * frameCoefficient h M e m := by
  change (Scheme.ΓSpecIso (.of B)).hom
    (e.hom.val.app (op ⊤) (unitTop h M (r • m))) = _
  erw [unitTop_smul, (e.hom.val.app (op ⊤)).hom.map_smul]
  change (Scheme.ΓSpecIso (.of B)).hom (h.appTop r * (show Γ(Spec (.of B), ⊤) from e.hom.val.app (op ⊤) (unitTop h M m))) = _
  exact map_mul (Scheme.ΓSpecIso (.of B)).hom.hom _ _

private theorem unitTop_frameScalar {Z W : Scheme.{u}} (h : W ⟶ Z)
    (M : Z.Modules) (e : (Scheme.Modules.pullback h).obj M ≅ Scheme.Modules.unitObj W)
    (m : Γ(M, ⊤)) :
    pullbackSectionHom h (Scheme.Modules.topSectionHom M m) ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection
        (e.hom.val.app (op ⊤) (unitTop h M m)) := by
  have he := Scheme.Modules.unitHom_eq_globalScalar
    (pullbackSectionHom h (Scheme.Modules.topSectionHom M m) ≫ e.hom)
  refine he.trans ?_
  apply congrArg ModularCurves.unitEndomorphismOfTopSection
  change e.hom.val.app (op ⊤)
    (sectionAtOne (pullbackSectionHom h (Scheme.Modules.topSectionHom M m))) = _
  rw [← unitTop_sectionHom]

private def compFrame {A B : Type u} [CommRing A] [CommRing B] {Z W : Scheme.{u}}
    (ψ : A →+* B) (h : Spec (.of A) ⟶ Z) (g : W ⟶ Z) (b : Spec (.of B) ⟶ W)
    (ha : Spec.map (CommRingCat.ofHom ψ) ≫ h = b ≫ g) (M : Z.Modules)
    (e : (Scheme.Modules.pullback h).obj M ≅ Scheme.Modules.unitObj (Spec (.of A))) :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback g).obj M) ≅
      Scheme.Modules.unitObj (Spec (.of B)) :=
  (Scheme.Modules.pullbackComp b g).app M ≪≫
    Scheme.Modules.frameViaFactor (Spec.map (CommRingCat.ofHom ψ)) h (b ≫ g) ha e

private theorem frameCoefficient_constant_pullback
    {A B : Type u} [CommRing A] [CommRing B] {Z W : Scheme.{u}}
    (ψ : A →+* B) (h : Spec (.of A) ⟶ Z) (g : W ⟶ Z) (b : Spec (.of B) ⟶ W)
    (ha : Spec.map (CommRingCat.ofHom ψ) ≫ h = b ≫ g) (M : Z.Modules)
    (e : (Scheme.Modules.pullback h).obj M ≅ Scheme.Modules.unitObj (Spec (.of A)))
    (m : Γ(M, ⊤)) :
    frameCoefficient b ((Scheme.Modules.pullback g).obj M)
      (compFrame ψ h g b ha M e) (unitTop g M m) = ψ (frameCoefficient h M e m) := by
  let α := Scheme.Modules.topSectionHom M m
  let r : Γ(Spec (.of A), ⊤) := e.hom.val.app (op ⊤) (unitTop h M m)
  have hr := unitTop_frameScalar h M e m
  have hs := frameViaFactor_sectionHom_scalar_apply (Spec.map (CommRingCat.ofHom ψ)) h
    (b ≫ g) ha e α r hr
  change (Scheme.ΓSpecIso (.of B)).hom
    ((Scheme.Modules.frameViaFactor (Spec.map (CommRingCat.ofHom ψ)) h (b ≫ g) ha e).hom.val.app
      (op ⊤) (((Scheme.Modules.pullbackComp b g).hom.app M).app ⊤
        (unitTop b ((Scheme.Modules.pullback g).obj M) (unitTop g M m)))) = _
  let ef := (Scheme.Modules.frameViaFactor (Spec.map (CommRingCat.ofHom ψ)) h
    (b ≫ g) ha e).hom.app ⊤
  have hc := congrArg (fun z : Γ((Scheme.Modules.pullback (b ≫ g)).obj M, ⊤) =>
    (Scheme.ΓSpecIso (.of B)).hom (ef z)) (unitTop_comp b g M m)
  have hu := congrArg (fun z : Γ((Scheme.Modules.pullback (b ≫ g)).obj M, ⊤) =>
    (Scheme.ΓSpecIso (.of B)).hom (ef z)) (unitTop_sectionHom (b ≫ g) M m)
  have hv := congrArg (fun z : Γ(Spec (.of B), ⊤) => (Scheme.ΓSpecIso (.of B)).hom z) hs
  have hn := congrArg (fun k : Γ(Spec (.of A), ⊤) ⟶ CommRingCat.of B => k.hom r)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
  exact hc.trans (hu.trans (hv.trans hn))


variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (x : RelativeSchemeValuedPoint v p)

private def productSourceMap :
    Spec (.of (SchemeValuedPoint.H x.1)[T;T⁻¹]) ⟶
      FlatGlobalSections.baseChange (S := R[T;T⁻¹]) p :=
  (SchemePointLaurentGauss.productMap p x).left

private theorem productSourceMap_fst :
    productSourceMap p x ≫ FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p =
      SchemePointLaurentGauss.originalProjection p x := by
  exact congrArg Over.Hom.left (SchemePointLaurentGauss.productMap_fst p x)


private theorem productSourceMap_snd :
    productSourceMap p x ≫ FlatGlobalSections.structureMap (S := R[T;T⁻¹]) p =
      SchemePointLaurentGauss.parameterProjection p x := by
  exact congrArg Over.Hom.left (SchemePointLaurentGauss.productMap_snd p x)

private theorem parameterCoefficient (F : R[T;T⁻¹]) :
    (Scheme.ΓSpecIso (.of (SchemeValuedPoint.H x.1)[T;T⁻¹])).hom
      ((productSourceMap p x).appTop
        (ProperBirationalSections.coefficientMap
          (FlatGlobalSections.structureMap (S := R[T;T⁻¹]) p) F)) =
      Spectrum.laurentCoefficientHom (SchemePointLaurentGauss.coefficientMap p x) F := by
  let ψ := Spectrum.laurentCoefficientHom (SchemePointLaurentGauss.coefficientMap p x)
  have he : Spec.map (CommRingCat.ofHom ψ) =
      productSourceMap p x ≫ FlatGlobalSections.structureMap (S := R[T;T⁻¹]) p :=
    (productSourceMap_snd p x).symm
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  rw [he, Scheme.Hom.comp_appTop] at h
  have hh := congrArg (fun k => (Scheme.ΓSpecIso (.of R[T;T⁻¹])).inv ≫ k) h
  simp only [Iso.inv_hom_id_assoc] at hh
  exact congrArg (fun k : CommRingCat.of R[T;T⁻¹] ⟶
    CommRingCat.of (SchemeValuedPoint.H x.1)[T;T⁻¹] => k.hom F) hh


private theorem fieldCoefficient (r : R) :
    (Scheme.ΓSpecIso (.of (SchemeValuedPoint.H x.1))).hom
      ((SchemeValuedPoint.fieldPoint x.1).appTop
        (ProperBirationalSections.coefficientMap p r)) =
      SchemePointLaurentGauss.coefficientMap p x r := by
  have h := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (SchemePointLaurentGauss.coefficientMap p x))
  rw [SchemePointLaurentGauss.coefficientMap_spec, Scheme.Hom.comp_appTop] at h
  have hh := congrArg (fun k => (Scheme.ΓSpecIso (.of R)).inv ≫ k) h
  simp only [Iso.inv_hom_id_assoc] at hh
  exact congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of (SchemeValuedPoint.H x.1) => k.hom r) hh

noncomputable local instance pointFieldAlgebra : Algebra R (SchemeValuedPoint.H x.1) :=
  (SchemePointLaurentGauss.coefficientMap p x).toAlgebra

/-- An actual frame of the original completed-point pullback gives the
honest original linear functional on the original whole section module. -/
def frameFunctional (M : X.Modules)
    (e : (Scheme.Modules.pullback (SchemeValuedPoint.fieldPoint x.1)).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1)))) :
    AffineModuleFlatBaseChange.sections p M →ₗ[R] SchemeValuedPoint.H x.1 := by
  exact
    { toAddHom := (frameCoefficient (SchemeValuedPoint.fieldPoint x.1) M e).toAddHom
      map_smul' := fun r m => by
        change frameCoefficient (SchemeValuedPoint.fieldPoint x.1) M e
          (ProperBirationalSections.coefficientMap p r • m) =
          SchemePointLaurentGauss.coefficientMap p x r *
            frameCoefficient (SchemeValuedPoint.fieldPoint x.1) M e m
        exact (frameCoefficient_smul _ M e _ m).trans
          (congrArg (fun z => z * frameCoefficient (SchemeValuedPoint.fieldPoint x.1) M e m)
            (fieldCoefficient p x r)) }


/-- The actual source frame is derived from the original completed-point
frame, actual product first projection and native pullback composition. -/
def sourceFrame (M : X.Modules)
    (e : (Scheme.Modules.pullback (SchemeValuedPoint.fieldPoint x.1)).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1)))) :
    (Scheme.Modules.pullback (productSourceMap p x)).obj
      ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p)).obj M) ≅
        Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1)[T;T⁻¹])) :=
  compFrame LaurentPolynomial.C (SchemeValuedPoint.fieldPoint x.1)
    (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p) (productSourceMap p x)
    (productSourceMap_fst p x).symm M e

/-- The actual original coefficient polynomial is obtained by native
pullback of the original whole section and the derived actual source frame. -/
def sourceCoefficient (M : X.Modules)
    (e : (Scheme.Modules.pullback (SchemeValuedPoint.fieldPoint x.1)).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1)))) :
    SchemeModuleLaurentCoefficients.pulledSections p M →+ (SchemeValuedPoint.H x.1)[T;T⁻¹] :=
  frameCoefficient (productSourceMap p x)
    ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p)).obj M)
    (sourceFrame p x M e)


private theorem sourceCoefficient_unit (M : X.Modules)
    (e : (Scheme.Modules.pullback (SchemeValuedPoint.fieldPoint x.1)).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1))))
    (m : AffineModuleFlatBaseChange.sections p M) :
    sourceCoefficient p x M e
      (Scheme.Modules.affinePullbackUnitTop
        (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p) M m) =
      LaurentPolynomial.C (frameFunctional p x M e m) :=
  frameCoefficient_constant_pullback LaurentPolynomial.C (SchemeValuedPoint.fieldPoint x.1)
    (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p) (productSourceMap p x)
    (productSourceMap_fst p x).symm M e m


private theorem sourceCoefficient_monomial (M : X.Modules)
    (e : (Scheme.Modules.pullback (SchemeValuedPoint.fieldPoint x.1)).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1))))
    (i : ℤ) (m : AffineModuleFlatBaseChange.sections p M) :
    sourceCoefficient p x M e
      ((ProperBirationalSections.coefficientMap
        (FlatGlobalSections.structureMap (S := R[T;T⁻¹]) p) (LaurentPolynomial.T i)) •
        Scheme.Modules.affinePullbackUnitTop
          (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p) M m) =
      LaurentPolynomial.C (frameFunctional p x M e m) * LaurentPolynomial.T i := by
  calc
    _ = (Scheme.ΓSpecIso (.of (SchemeValuedPoint.H x.1)[T;T⁻¹])).hom
        ((productSourceMap p x).appTop
          (ProperBirationalSections.coefficientMap
            (FlatGlobalSections.structureMap (S := R[T;T⁻¹]) p) (LaurentPolynomial.T i))) *
        sourceCoefficient p x M e
          (Scheme.Modules.affinePullbackUnitTop
            (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p) M m) :=
      frameCoefficient_smul _ _ _ _ _
    _ = LaurentPolynomial.T i * LaurentPolynomial.C (frameFunctional p x M e m) := by
      rw [parameterCoefficient, Spectrum.laurentCoefficientHom_T, sourceCoefficient_unit]
    _ = _ := mul_comm _ _

private theorem evaluate_eq_sum [CompactSpace X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent]
    (φ : AffineModuleFlatBaseChange.sections p M →ₗ[R] SchemeValuedPoint.H x.1)
    (σ : SchemeModuleLaurentCoefficients.pulledSections p M) :
    SchemeModuleLaurentEvaluation.evaluate p M φ σ =
      (SchemeModuleLaurentCoefficients.coefficients p M σ).sum
        (fun i m => LaurentPolynomial.C (φ m) * LaurentPolynomial.T i) := by
  change LaurentModuleExpansion.evaluate φ
      ((FlatModuleGlobalSections.tensorEquiv (S := R[T;T⁻¹]) p M).symm σ) =
    (LaurentModuleExpansion.coefficients
      ((FlatModuleGlobalSections.tensorEquiv (S := R[T;T⁻¹]) p M).symm σ)).sum
        (fun i m => LaurentPolynomial.C (φ m) * LaurentPolynomial.T i)
  have h := congrArg (LaurentModuleExpansion.evaluate φ)
    (LaurentModuleExpansion.eq_sum_T_tmul
      ((FlatModuleGlobalSections.tensorEquiv (S := R[T;T⁻¹]) p M).symm σ))
  simpa only [Finsupp.sum, map_sum, LaurentModuleExpansion.evaluate_T_tmul] using h

/-- EVERY actual original product-line section has its actual native
source-frame coefficient equal to its genuine original Laurent evaluation.
No evaluation square, expansion or coefficient matching is supplied. -/
theorem sourceCoefficient_eq_evaluate [CompactSpace X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent]
    (e : (Scheme.Modules.pullback (SchemeValuedPoint.fieldPoint x.1)).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1))))
    (σ : SchemeModuleLaurentCoefficients.pulledSections p M) :
    sourceCoefficient p x M e σ =
      SchemeModuleLaurentEvaluation.evaluate p M (frameFunctional p x M e) σ := by
  rw [evaluate_eq_sum p x]
  have h := congrArg (sourceCoefficient p x M e)
    (SchemeModuleLaurentCoefficients.eq_sum_monomial p M σ)
  rw [Finsupp.sum] at h
  erw [map_sum] at h
  simpa only [Finsupp.sum, sourceCoefficient_monomial] using h


/-- The actual native source frame coefficient of EVERY original product
section has the true weighted maximum of its original coefficients. -/
theorem sourceCoefficient_laurentGauss [CompactSpace X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent]
    (e : (Scheme.Modules.pullback (SchemeValuedPoint.fieldPoint x.1)).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1))))
    (r : ℝ≥0) (hr : 0 < r) (σ : SchemeModuleLaurentCoefficients.pulledSections p M) :
    (Spectrum.laurentGauss (NormedField.valuation (K := SchemeValuedPoint.H x.1)) r hr).val
      (sourceCoefficient p x M e σ) =
      (SchemeModuleLaurentCoefficients.coefficients p M σ).support.sup
        (fun i => ‖frameFunctional p x M e
          (SchemeModuleLaurentCoefficients.coefficients p M σ i)‖₊ * r ^ i) := by
  rw [sourceCoefficient_eq_evaluate]
  exact SchemeModuleLaurentEvaluation.laurentGauss_evaluate p M (frameFunctional p x M e)
    (NormedField.valuation (K := SchemeValuedPoint.H x.1)) r hr σ

/-- The SAME original finite coefficient/weight family is fixed BEFORE
all original points, actual frames and positive Laurent radii. -/
theorem sourceCoefficient_finite_family [CompactSpace X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent]
    (G : Finset (SchemeModuleLaurentCoefficients.pulledSections p M))
    (e : (Scheme.Modules.pullback (SchemeValuedPoint.fieldPoint x.1)).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1))))
    (r : ℝ≥0) (hr : 0 < r) :
    G.sup (fun σ =>
      (Spectrum.laurentGauss (NormedField.valuation (K := SchemeValuedPoint.H x.1)) r hr).val
        (sourceCoefficient p x M e σ)) =
      (SchemeModuleLaurentCoefficients.terms p M G).sup
        (fun t => ‖frameFunctional p x M e t.1‖₊ * r ^ t.2) := by
  simp only [sourceCoefficient_eq_evaluate]
  exact SchemeModuleLaurentEvaluation.laurentGauss_finite_family p M G (frameFunctional p x M e)
    (NormedField.valuation (K := SchemeValuedPoint.H x.1)) r hr


/-- The actual original frame section, retaining its native affine section
carrier before converting it to an original Laurent polynomial. -/
def sourceFrameSection (M : X.Modules)
    (e : (Scheme.Modules.pullback (SchemeValuedPoint.fieldPoint x.1)).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1)))) :
    SchemeModuleLaurentCoefficients.pulledSections p M →+
      Γ(Spec (.of (SchemeValuedPoint.H x.1)[T;T⁻¹]), ⊤) :=
  ((sourceFrame p x M e).hom.app ⊤).hom.comp
    (unitTop (productSourceMap p x)
      ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p)).obj M))

private theorem affineSection_eval {A : Type u} [CommRing A]
    (z : SchemeValuedPoint (Spec (.of A))) (s : Γ(Spec (.of A), ⊤)) :
    SchemeValuedPoint.eval z ⊤ trivial s =
      (SchemeValuedPoint.spectrumHomeomorph z).val ((Scheme.ΓSpecIso (.of A)).hom s) := by
  have h := SchemeValuedPoint.spectrumHomeomorph_val_apply z ((Scheme.ΓSpecIso (.of A)).hom s)
  simpa only [Iso.hom_inv_id_apply] using h.symm

/-- Evaluation of the actual native source-frame section at the actual
native Laurent Gauss point equals the original weighted coefficient maximum. -/
theorem sourceFrameSection_value [CompactSpace X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent]
    (e : (Scheme.Modules.pullback (SchemeValuedPoint.fieldPoint x.1)).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1))))
    (r : ℝ≥0) (hr : 0 < r) (σ : SchemeModuleLaurentCoefficients.pulledSections p M) :
    SchemeValuedPoint.eval (SchemePointLaurentGauss.point p x r hr) ⊤ trivial
      (sourceFrameSection p x M e σ) =
      (SchemeModuleLaurentCoefficients.coefficients p M σ).support.sup
        (fun i => ‖frameFunctional p x M e
          (SchemeModuleLaurentCoefficients.coefficients p M σ i)‖₊ * r ^ i) := by
  have h := affineSection_eval (SchemePointLaurentGauss.point p x r hr)
    (sourceFrameSection p x M e σ)
  simp only [SchemePointLaurentGauss.point, Homeomorph.apply_symm_apply] at h
  exact h.trans (sourceCoefficient_laurentGauss p x M e r hr σ)

end EnvelopeProperty.Berkovich.SchemePointLaurentModuleEvaluation
