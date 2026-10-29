import EnvelopeProperty.AlgGeom.SchemeModuleGlobalSections
import EnvelopeProperty.Berkovich.SchemeLinePullbackSections
import ModularCurves.ForMathlib.PullbackUnitMonoidal

/-! # Actual original whole tensor sections and native strong-monoidal pullback -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeTensorSectionHoms
open SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f

/-- The actual whole original tensor section, using true structure multiplication. -/
def tensorSectionHom {X : Scheme.{u}} {M N : X.Modules}
    (a : unitObj X ⟶ M) (b : unitObj X ⟶ N) : unitObj X ⟶ M ⊗ N :=
  (ModularCurves.unitObjTensorIso X).inv ≫ (a ⊗ₘ b)

/-- Actual whole tensor section morphisms retain the genuine original pure tensor section. -/
theorem tensorSectionHom_sectionHom {X : Scheme.{u}} (M N : X.Modules)
    (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) :
    tensorSectionHom (SchemeModuleGlobalSections.sectionHom M s)
      (SchemeModuleGlobalSections.sectionHom N t) =
        SchemeModuleGlobalSections.sectionHom (M ⊗ N) (ModularCurves.tensorSection M N ⊤ s t) := by
  exact (ModularCurves.topSectionHom_tensorSection M N s t).symm

/-- Whole original tensor sections are natural in BOTH actual factor morphisms. -/
theorem tensorSectionHom_comp {X : Scheme.{u}} {M N M' N' : X.Modules}
    (a : unitObj X ⟶ M) (b : unitObj X ⟶ N) (f : M ⟶ M') (g : N ⟶ N') :
    tensorSectionHom a b ≫ (f ⊗ₘ g) = tensorSectionHom (a ≫ f) (b ≫ g) := by
  simp only [tensorSectionHom, Category.assoc, tensorHom_comp_tensorHom]

/-- A pair of genuine original section frames has a genuine whole tensor frame. -/
theorem tensorSectionHom_isIso {X : Scheme.{u}} {M N : X.Modules}
    (a : unitObj X ⟶ M) (b : unitObj X ⟶ N) [IsIso a] [IsIso b] :
    IsIso (tensorSectionHom a b) := by
  unfold tensorSectionHom
  infer_instance

/-- Original whole scalar coefficients multiply under the SAME actual tensor section. -/
theorem tensorSectionHom_precomp_scalars {X : Scheme.{u}} {M N : X.Modules}
    (a : unitObj X ⟶ M) (b : unitObj X ⟶ N) (r s : Γ(X, ⊤)) :
    tensorSectionHom (ModularCurves.unitEndomorphismOfTopSection r ≫ a)
      (ModularCurves.unitEndomorphismOfTopSection s ≫ b) =
        ModularCurves.unitEndomorphismOfTopSection (r * s) ≫ tensorSectionHom a b := by
  have hu : (ModularCurves.unitObjTensorIso X).inv ≫
      (ModularCurves.unitEndomorphismOfTopSection r ⊗ₘ
        ModularCurves.unitEndomorphismOfTopSection s) =
      ModularCurves.unitEndomorphismOfTopSection (r * s) ≫
        (ModularCurves.unitObjTensorIso X).inv := by
    apply (cancel_mono (ModularCurves.unitObjTensorIso X).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ModularCurves.unitObjTensorIso_hom_comp_scalars, Iso.inv_hom_id_assoc]
  simp only [tensorSectionHom, ← tensorHom_comp_tensorHom, ← Category.assoc, hu]

private theorem pullbackUnit_hom {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullbackUnitIso f).hom =
      (Scheme.Modules.pullback f).map (ModularCurves.monoidalUnitObjIso X).inv ≫
        Functor.OplaxMonoidal.η (Scheme.Modules.pullback f) ≫
          (ModularCurves.monoidalUnitObjIso Y).hom := by
  have h := congrArg Iso.hom (Scheme.Modules.pullback_monoidalUnitObjIso f)
  change Functor.OplaxMonoidal.η (Scheme.Modules.pullback f) ≫
    (ModularCurves.monoidalUnitObjIso Y).hom =
      (Scheme.Modules.pullback f).map (ModularCurves.monoidalUnitObjIso X).hom ≫
        (pullbackUnitIso f).hom at h
  rw [h, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    (Scheme.Modules.pullback f).map_id, Category.id_comp]

private theorem unitMultiplication_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) (unitObj X) (unitObj X) ≫
      ((pullbackUnitIso f).hom ⊗ₘ (pullbackUnitIso f).hom) ≫
        (ModularCurves.unitObjTensorIso Y).hom =
    (Scheme.Modules.pullback f).map (ModularCurves.unitObjTensorIso X).hom ≫
      (pullbackUnitIso f).hom := by
  let F := Scheme.Modules.pullback f
  let uX := ModularCurves.monoidalUnitObjIso X
  let uY := ModularCurves.monoidalUnitObjIso Y
  have hmX : (ModularCurves.unitObjTensorIso X).hom ≫ uX.inv =
      (uX.inv ⊗ₘ uX.inv) ≫ (λ_ (𝟙_ X.Modules)).hom := by
    simp only [ModularCurves.unitObjTensorIso, Iso.trans_hom, Iso.symm_hom,
      tensorIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id, uX]
  have hmY : (uY.hom ⊗ₘ uY.hom) ≫ (ModularCurves.unitObjTensorIso Y).hom =
      (λ_ (𝟙_ Y.Modules)).hom ≫ uY.hom := by
    simp only [ModularCurves.unitObjTensorIso, Iso.trans_hom, Iso.symm_hom,
      tensorIso_hom, ← Category.assoc, tensorHom_comp_tensorHom, Iso.hom_inv_id,
      tensorHom_id, MonoidalCategory.id_whiskerRight, Category.id_comp, uY]
  have hunit : Functor.OplaxMonoidal.δ F (𝟙_ X.Modules) (𝟙_ X.Modules) ≫
      (Functor.OplaxMonoidal.η F ⊗ₘ Functor.OplaxMonoidal.η F) ≫
        (λ_ (𝟙_ Y.Modules)).hom =
      F.map (λ_ (𝟙_ X.Modules)).hom ≫ Functor.OplaxMonoidal.η F := by
    rw [MonoidalCategory.tensorHom_def]
    simp only [Category.assoc]
    rw [MonoidalCategory.leftUnitor_naturality,
      Functor.OplaxMonoidal.left_unitality_hom_assoc]
  calc
    _ = Functor.OplaxMonoidal.δ F (unitObj X) (unitObj X) ≫
        (F.map uX.inv ⊗ₘ F.map uX.inv) ≫
        (Functor.OplaxMonoidal.η F ⊗ₘ Functor.OplaxMonoidal.η F) ≫
        (uY.hom ⊗ₘ uY.hom) ≫ (ModularCurves.unitObjTensorIso Y).hom := by
      rw [pullbackUnit_hom f]
      simp only [← tensorHom_comp_tensorHom, Category.assoc, F, uX, uY]
    _ = F.map (uX.inv ⊗ₘ uX.inv) ≫
        Functor.OplaxMonoidal.δ F (𝟙_ X.Modules) (𝟙_ X.Modules) ≫
        (Functor.OplaxMonoidal.η F ⊗ₘ Functor.OplaxMonoidal.η F) ≫
          (λ_ (𝟙_ Y.Modules)).hom ≫ uY.hom := by
      rw [hmY, Functor.OplaxMonoidal.δ_natural_assoc]
    _ = F.map (uX.inv ⊗ₘ uX.inv) ≫ F.map (λ_ (𝟙_ X.Modules)).hom ≫
        Functor.OplaxMonoidal.η F ≫ uY.hom := by
      simpa only [Category.assoc] using congrArg
        (fun q => F.map (uX.inv ⊗ₘ uX.inv) ≫ q ≫ uY.hom) hunit
    _ = F.map (ModularCurves.unitObjTensorIso X).hom ≫ (pullbackUnitIso f).hom := by
      rw [pullbackUnit_hom f, ← Category.assoc, ← F.map_comp, ← hmX]
      simp only [F.map_comp, Category.assoc, F, uX, uY]

private theorem unitInverseMultiplication_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullbackUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map (ModularCurves.unitObjTensorIso X).inv ≫
        Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) (unitObj X) (unitObj X) =
      (ModularCurves.unitObjTensorIso Y).inv ≫
        ((pullbackUnitIso f).inv ⊗ₘ (pullbackUnitIso f).inv) := by
  have he : (Functor.Monoidal.μIso (Scheme.Modules.pullback f) (unitObj X) (unitObj X)).symm ≪≫
      (pullbackUnitIso f ⊗ᵢ pullbackUnitIso f) ≪≫ ModularCurves.unitObjTensorIso Y =
      (Scheme.Modules.pullback f).mapIso (ModularCurves.unitObjTensorIso X) ≪≫ pullbackUnitIso f := by
    apply Iso.ext
    exact unitMultiplication_pullback f
  have h := congrArg Iso.inv he
  have hh := congrArg (fun q => q ≫
    Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) (unitObj X) (unitObj X)) h
  simpa only [Iso.trans_inv, Iso.symm_inv, tensorIso_inv, Functor.mapIso_inv,
    Category.assoc, Functor.Monoidal.μIso_hom, Functor.Monoidal.μ_δ,
    Category.comp_id] using hh.symm

/-- EVERY actual native scheme pullback preserves the SAME whole original tensor section. -/
theorem pullback_tensorSectionHom {X Y : Scheme.{u}} (f : Y ⟶ X) {M N : X.Modules}
    (a : unitObj X ⟶ M) (b : unitObj X ⟶ N) :
    pullbackSectionHom f (tensorSectionHom a b) ≫
      (Functor.Monoidal.μIso (Scheme.Modules.pullback f) M N).inv =
        tensorSectionHom (pullbackSectionHom f a) (pullbackSectionHom f b) := by
  unfold pullbackSectionHom tensorSectionHom
  rw [Functor.map_comp]
  change (pullbackUnitIso f).inv ≫
    (Scheme.Modules.pullback f).map (ModularCurves.unitObjTensorIso X).inv ≫
    (Scheme.Modules.pullback f).map (a ⊗ₘ b) ≫
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M N = _
  rw [← Functor.OplaxMonoidal.δ_natural]
  have h := congrArg (fun q => q ≫
    ((Scheme.Modules.pullback f).map a ⊗ₘ (Scheme.Modules.pullback f).map b))
      (unitInverseMultiplication_pullback f)
  simpa only [Category.assoc, tensorHom_comp_tensorHom] using h
end EnvelopeProperty.SchemeTensorSectionHoms
