import EnvelopeProperty.AlgGeom.CoordinateTupleComplex
import EnvelopeProperty.AlgGeom.SchemeTensorSectionHoms

/-! # Original coordinate products and actual tensor-section morphisms -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules MvPolynomial
noncomputable section
universe u v
namespace EnvelopeProperty.ProjectiveCoordinateTensorProducts
open CoordinateTupleComplex SchemeTensorSectionHoms
private theorem pure_right {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {U Q L : C} (e : 𝟙_ C ≅ U) (a : U ⟶ Q) (b : U ⟶ L) :
    (((e.symm ⊗ᵢ e.symm) ≪≫ λ_ (𝟙_ C) ≪≫ e).inv ≫ (a ⊗ₘ b)) =
      a ≫ (ρ_ Q).inv ≫ Q ◁ (e.hom ≫ b) := by
  calc
    _ = e.inv ≫ (λ_ (𝟙_ C)).inv ≫ ((e.hom ≫ a) ⊗ₘ (e.hom ≫ b)) := by
      simp only [Iso.trans_inv, Iso.symm_inv, tensorIso_inv, Category.assoc, tensorHom_comp_tensorHom]
    _ = _ := by
      rw [unitors_inv_equal, rightUnitor_inv_comp_tensorHom]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem tensor_step {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (M A L : C) (s : 𝟙_ C ⟶ L) :
    (ρ_ (M ⊗ A)).inv ≫ ((M ⊗ A) ◁ s) ≫ (α_ M A L).hom =
      M ◁ ((ρ_ A).inv ≫ (A ◁ s)) := by
  rw [rightUnitor_tensor_inv]
  simp only [Category.assoc, ← tensor_whiskerLeft_symm, whiskerLeft_comp]

private def tensorStepIso {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (M A L B Y : C) (e : A ⊗ L ≅ B) (f : M ⊗ B ≅ Y) : (M ⊗ A) ⊗ L ≅ Y :=
  α_ M A L ≪≫ (Iso.refl M ⊗ᵢ e) ≪≫ f


private theorem insertion_step {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (M A L B Y : C) (e : A ⊗ L ≅ B) (f : M ⊗ B ≅ Y) (s : 𝟙_ C ⟶ L) :
    (ρ_ (M ⊗ A)).inv ≫ ((M ⊗ A) ◁ s) ≫ (tensorStepIso M A L B Y e f).hom =
      M ◁ ((ρ_ A).inv ≫ (A ◁ s) ≫ e.hom) ≫ f.hom := by
  simpa only [tensorStepIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
    MonoidalCategory.tensorHom_def, MonoidalCategory.id_whiskerRight,
    Category.id_comp, Category.assoc, whiskerLeft_comp]
    using congrArg (fun h => h ≫ M ◁ e.hom ≫ f.hom) (tensor_step M A L s)

attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra

private theorem scheme_pure_right {X : Scheme.{u}} (Q L : X.Modules)
    (q : unitObj X ⟶ Q) (s : unitObj X ⟶ L) :
    tensorSectionHom q s = q ≫ (ρ_ Q).inv ≫ Q ◁ ((ModularCurves.monoidalUnitObjIso X).hom ≫ s) :=
  pure_right (ModularCurves.monoidalUnitObjIso X) q s

private theorem scheme_insertion_step {X : Scheme.{u}} (M A L B Y : X.Modules)
    (e : A ⊗ L ≅ B) (f : M ⊗ B ≅ Y) (s : 𝟙_ X.Modules ⟶ L) :
    (ρ_ (M ⊗ A)).inv ≫ ((M ⊗ A) ◁ s) ≫ (tensorStepIso M A L B Y e f).hom =
      M ◁ ((ρ_ A).inv ≫ (A ◁ s) ≫ e.hom) ≫ f.hom :=
  insertion_step M A L B Y e f s

private theorem scheme_factor_of_maps {X : Scheme.{u}} (M A L B Y : X.Modules)
    (e : A ⊗ L ≅ B) (f : M ⊗ B ≅ Y) (s : 𝟙_ X.Modules ⟶ L)
    (c : A ⟶ B) (h : M ⊗ A ⟶ Y) (k : (M ⊗ A) ⊗ L ⟶ Y)
    (hc : c = (ρ_ A).inv ≫ (A ◁ s) ≫ e.hom)
    (hh : h = M ◁ c ≫ f.hom)
    (hk : k = (tensorStepIso M A L B Y e f).hom) :
    h = (ρ_ (M ⊗ A)).inv ≫ ((M ⊗ A) ◁ s) ≫ k := by
  rw [hh, hc, hk]
  exact (scheme_insertion_step M A L B Y e f s).symm

private theorem scheme_pure_of_factor {X : Scheme.{u}} (Q L Y : X.Modules)
    (s : unitObj X ⟶ L) (g : Q ⟶ Y) (f : Q ⊗ L ⟶ Y)
    (hg : g = (ρ_ Q).inv ≫ Q ◁ ((ModularCurves.monoidalUnitObjIso X).hom ≫ s) ≫ f)
    (q : unitObj X ⟶ Q) : tensorSectionHom q s ≫ f = q ≫ g := by
  rw [scheme_pure_right, hg]
  simp only [Category.assoc]

variable {R : Type u} [CommRing R] {σ : Type}

private theorem lower_whisker_def (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j i : σ) (t : ℤ) :
    coordinateLowerMul M j i t =
      M ◁ ProjectiveCoordinateMultiplication.coordinateMul j i (t - 1) ≫
      (eqToIso (congrArg (fun a : ℤ => M ⊗ coordinateHyperplaneTwist (R := R) j a)
        (sub_add_cancel t 1))).hom := rfl

private theorem coordinate_mul_def (j i : σ) (a : ℤ) :
    ProjectiveCoordinateMultiplication.coordinateMul (R := R) j i a =
      (ρ_ (coordinateHyperplaneTwist (R := R) j a)).inv ≫
      (coordinateHyperplaneTwist (R := R) j a ◁
        ((ModularCurves.monoidalUnitObjIso (Proj (homogeneousSubmodule σ R))).hom ≫
          ProjectiveTwistGlobalGeneration.coordinateSectionHom j i 1)) ≫
      (ProjectiveTwistTensorAddition.tensorIso j j j a 1).hom := rfl

/-- The original descending tensor-addition isomorphism, with literal target M(t). -/
def lowerTensorIso (M : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) (t : ℤ) :
    ((M ⊗ coordinateHyperplaneTwist (R := R) j (t - 1)) ⊗
      coordinateHyperplaneTwist (R := R) j 1) ≅ M ⊗ coordinateHyperplaneTwist (R := R) j t :=
  tensorStepIso M _ _ _ _ (ProjectiveTwistTensorAddition.tensorIso j j j (t - 1) 1)
    (eqToIso (congrArg (fun a : ℤ => M ⊗ coordinateHyperplaneTwist (R := R) j a) (sub_add_cancel t 1)))


private theorem lower_iso_hom (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j : σ) (t : ℤ) :
    (lowerTensorIso M j t).hom =
      (tensorStepIso M (coordinateHyperplaneTwist (R := R) j (t - 1))
        (coordinateHyperplaneTwist (R := R) j (1 : ℤ))
        (coordinateHyperplaneTwist (R := R) j (t - 1 + 1))
        (M ⊗ coordinateHyperplaneTwist (R := R) j t)
        (ProjectiveTwistTensorAddition.tensorIso j j j (t - 1) 1)
        (eqToIso (congrArg (fun a : ℤ => M ⊗ coordinateHyperplaneTwist (R := R) j a)
          (sub_add_cancel t 1)))).hom := rfl

/-- The original coordinate arrow factors through the actual right-unit insertion and tensor addition. -/
theorem coordinateLowerMul_factor (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j i : σ) (t : ℤ) :
    coordinateLowerMul M j i t =
      (ρ_ (M ⊗ coordinateHyperplaneTwist (R := R) j (t - 1))).inv ≫
      ((M ⊗ coordinateHyperplaneTwist (R := R) j (t - 1)) ◁
        ((ModularCurves.monoidalUnitObjIso (Proj (homogeneousSubmodule σ R))).hom ≫
          ProjectiveTwistGlobalGeneration.coordinateSectionHom j i 1)) ≫
      (lowerTensorIso M j t).hom := by
  exact scheme_factor_of_maps (X := Proj (homogeneousSubmodule σ R)) M
    (coordinateHyperplaneTwist (R := R) j (t - 1))
    (coordinateHyperplaneTwist (R := R) j (1 : ℤ))
    (coordinateHyperplaneTwist (R := R) j (t - 1 + 1))
    (M ⊗ coordinateHyperplaneTwist (R := R) j t)
    (ProjectiveTwistTensorAddition.tensorIso j j j (t - 1) 1)
    (eqToIso (congrArg (fun a : ℤ => M ⊗ coordinateHyperplaneTwist (R := R) j a)
      (sub_add_cancel t 1)))
    ((ModularCurves.monoidalUnitObjIso (Proj (homogeneousSubmodule σ R))).hom ≫
      ProjectiveTwistGlobalGeneration.coordinateSectionHom j i 1)
    (ProjectiveCoordinateMultiplication.coordinateMul j i (t - 1))
    (coordinateLowerMul M j i t) (lowerTensorIso M j t).hom
    (coordinate_mul_def (R := R) j i (t - 1))
    (lower_whisker_def (R := R) M j i t) (lower_iso_hom (R := R) M j t)

/-- The actual tensor product with an original coordinate is precisely the original coordinate multiplication. -/
theorem tensorSectionHom_coordinate (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j i : σ) (t : ℤ)
    (q : unitObj (Proj (homogeneousSubmodule σ R)) ⟶
      M ⊗ coordinateHyperplaneTwist (R := R) j (t - 1)) :
    tensorSectionHom (N := coordinateHyperplaneTwist (R := R) j (1 : ℤ)) q
      (ProjectiveTwistGlobalGeneration.coordinateSectionHom j i 1) ≫
      (lowerTensorIso M j t).hom = q ≫ coordinateLowerMul M j i t := by
  exact scheme_pure_of_factor (X := Proj (homogeneousSubmodule σ R))
    (M ⊗ coordinateHyperplaneTwist (R := R) j (t - 1))
    (coordinateHyperplaneTwist (R := R) j (1 : ℤ))
    (M ⊗ coordinateHyperplaneTwist (R := R) j t)
    (ProjectiveTwistGlobalGeneration.coordinateSectionHom j i 1)
    (coordinateLowerMul M j i t) (lowerTensorIso M j t).hom
    (coordinateLowerMul_factor (R := R) M j i t) q

end EnvelopeProperty.ProjectiveCoordinateTensorProducts
