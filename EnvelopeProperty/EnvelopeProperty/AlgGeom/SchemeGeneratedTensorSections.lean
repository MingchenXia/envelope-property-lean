import EnvelopeProperty.AlgGeom.SchemeTensorSectionHoms
import EnvelopeProperty.AlgGeom.SchemeGeneratingSectionsUnit
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorEquivalence

/-! # Genuine original tensor generators on arbitrary schemes -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
noncomputable section
universe u
namespace EnvelopeProperty.SchemeGeneratedTensorSections
open Scheme.Modules SchemeGeneratingSectionsUnit SchemeTensorSectionHoms

@[instance_reducible] private noncomputable def originalSchemeMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X
attribute [local instance] originalSchemeMonoidal

private def unitTensorIso {X : Scheme.{u}} (N : X.Modules) : unitObj X ⊗ N ≅ N :=
  ((ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl N) ≪≫ λ_ N

private theorem unit_tensor_factor {C : Type*} [Category C] [MonoidalCategory C]
    {U M N : C} (e : 𝟙_ C ≅ U) (a : U ⟶ M) (b : U ⟶ N) :
    (((e.symm ⊗ᵢ e.symm) ≪≫ λ_ (𝟙_ C) ≪≫ e).inv ≫ (a ⊗ₘ b)) =
      b ≫ (((e.symm ⊗ᵢ Iso.refl N) ≪≫ λ_ N).inv) ≫ a ▷ N := by
  calc
    _ = e.inv ≫ (λ_ (𝟙_ C)).inv ≫ ((e.hom ≫ a) ⊗ₘ (e.hom ≫ b)) := by
      simp only [Iso.trans_inv, Iso.symm_inv, tensorIso_inv,
        Category.assoc, tensorHom_comp_tensorHom]
    _ = b ≫ (λ_ N).inv ≫ (e.hom ▷ N) ≫ (a ▷ N) := by
      rw [leftUnitor_inv_comp_tensorHom]
      simp only [comp_whiskerRight, Category.assoc, Iso.inv_hom_id_assoc]
    _ = _ := by
      simp only [Iso.trans_inv, Iso.symm_inv, tensorIso_inv, Iso.refl_inv,
        MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_id,
        Category.comp_id, Category.assoc]

private theorem tensorSectionHom_right_factor {X : Scheme.{u}} {M N : X.Modules}
    (a : unitObj X ⟶ M) (b : unitObj X ⟶ N) :
    tensorSectionHom a b = b ≫ (unitTensorIso N).inv ≫ a ▷ N :=
  unit_tensor_factor (ModularCurves.monoidalUnitObjIso X) a b

/-- The actual original pair-family evaluation, indexed by precisely the pair of indices. -/
def tensorEvaluation {X : Scheme.{u}} {M N : X.Modules}
    (G : M.GeneratingSections) (H : N.GeneratingSections) :
    SheafOfModules.free (R := X.ringCatSheaf) (G.I × H.I) ⟶
      (tensorRight (C := X.Modules) N).obj M :=
  Sigma.desc (C := X.Modules) (fun ij : G.I × H.I =>
    @tensorSectionHom X M N (generatorHom G ij.1) (generatorHom H ij.2))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Genuine original generating families derive epimorphic tensor evaluation internally. -/
theorem tensorEvaluation_epi {X : Scheme.{u}} {M N : X.Modules}
    (hN : IsInvertible N) (G : M.GeneratingSections) (H : N.GeneratingSections) :
    Epi (tensorEvaluation G H) := by
  let F := tensorRight (C := X.Modules) N
  let : F.IsEquivalence := SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence N hN
  let : Epi G.π := G.epi
  let : Epi H.π := H.epi
  have hG : Epi G.π := G.epi
  let : Epi (F.map G.π) := by
    exact @Functor.map_epi X.Modules _ X.Modules _ F _ _ _ G.π hG
  constructor
  intro Z a b hab
  apply (cancel_epi (F.map G.π)).mp
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit F (fun _ : G.I => unitObj X)
      (fun i => SheafOfModules.ιFree i) (SheafOfModules.isColimitFreeCofan G.I))
  intro i
  change (F.map (SheafOfModules.ιFree i) ≫ F.map G.π) ≫ a =
    (F.map (SheafOfModules.ιFree i) ≫ F.map G.π) ≫ b
  have left (z : F.obj M ⟶ Z) :
      (F.map (SheafOfModules.ιFree i) ≫ F.map G.π) ≫ z =
        F.map (generatorHom G i) ≫ z :=
    congrArg (fun q => q ≫ z) (F.map_comp (SheafOfModules.ιFree i) G.π).symm
  refine Eq.trans (left a) (Eq.trans ?_ (left b).symm)
  change (generatorHom G i ▷ N) ≫ a = (generatorHom G i ▷ N) ≫ b
  apply (cancel_epi (H.π ≫ (unitTensorIso N).inv)).mp
  apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan H.I)
  intro j
  have h := congrArg (fun q => SheafOfModules.ιFree (i, j) ≫ q) hab
  have hij : SheafOfModules.ιFree (i, j) ≫ tensorEvaluation G H =
      tensorSectionHom (generatorHom G i) (generatorHom H j) :=
    Sigma.ι_desc (C := X.Modules)
      (fun ij : G.I × H.I =>
        @tensorSectionHom X M N (generatorHom G ij.1) (generatorHom H ij.2)) (i, j)
  have h' : tensorSectionHom (generatorHom G i) (generatorHom H j) ≫ a =
      tensorSectionHom (generatorHom G i) (generatorHom H j) ≫ b := by
    simpa only [← Category.assoc, hij] using h
  simpa only [tensorSectionHom_right_factor, generatorHom,
    SheafOfModules.freeCofan_inj, Category.assoc] using h'

/-- The actual pair-family gives genuine global generators of the original tensor. -/
def generatingSections {X : Scheme.{u}} {M N : X.Modules}
    (hN : IsInvertible N) (G : M.GeneratingSections) (H : N.GeneratingSections) :
    (M ⊗ N).GeneratingSections where
  I := G.I × H.I
  s := (M ⊗ N).freeHomEquiv (tensorEvaluation G H)
  epi := by
    simpa only [Equiv.symm_apply_apply] using tensorEvaluation_epi hN G H

/-- Every original generator is literally the tensor of the two original generator morphisms. -/
theorem generatorHom_generatingSections {X : Scheme.{u}} {M N : X.Modules}
    (hN : IsInvertible N) (G : M.GeneratingSections) (H : N.GeneratingSections)
    (i : G.I) (j : H.I) :
    generatorHom (generatingSections hN G H) (i, j) =
      tensorSectionHom (generatorHom G i) (generatorHom H j) := by
  change SheafOfModules.ιFree (i, j) ≫
    (M ⊗ N).freeHomEquiv.symm ((M ⊗ N).freeHomEquiv (tensorEvaluation G H)) = _
  rw [Equiv.symm_apply_apply]
  exact Sigma.ι_desc (C := X.Modules)
    (fun ij : G.I × H.I =>
      @tensorSectionHom X M N (generatorHom G ij.1) (generatorHom H ij.2)) (i, j)

/-- Finite original families yield a finite original pair-family on the tensor. -/
theorem generatingSections_isFiniteType {X : Scheme.{u}} {M N : X.Modules}
    (hN : IsInvertible N) (G : M.GeneratingSections) (H : N.GeneratingSections)
    [hG : G.IsFiniteType] [hH : H.IsFiniteType] :
    (generatingSections hN G H).IsFiniteType := by
  refine ⟨?_⟩
  change Finite (G.I × H.I)
  let : Finite G.I := hG.finite
  let : Finite H.I := hH.finite
  infer_instance

end EnvelopeProperty.SchemeGeneratedTensorSections
