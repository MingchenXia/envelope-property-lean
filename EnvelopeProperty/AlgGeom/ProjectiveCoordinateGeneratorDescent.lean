import EnvelopeProperty.AlgGeom.ProjectiveRegularitySections
import EnvelopeProperty.AlgGeom.ProjectiveCoordinateTensorProducts
import EnvelopeProperty.AlgGeom.SchemeFiniteTensorGeneratorDescent
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Finite generators descend through original coordinate evaluation -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules MvPolynomial
noncomputable section
universe u v
namespace EnvelopeProperty.ProjectiveCoordinateGeneratorDescent
open CoordinateTupleComplex ProjectiveRegularitySections ProjectiveCoordinateTensorProducts
open SchemeGeneratingSectionsUnit SchemeTensorSectionHoms
private theorem coproduct_decomposition {C : Type u} [Category.{v} C]
    [Preadditive C] [HasFiniteCoproducts C] [HasFiniteBiproducts C] {I : Type} [Fintype I]
    (A : I → C) {U : C} (f : U ⟶ ∐ A) :
    f = ∑ i : I, (f ≫ (biproduct.isoCoproduct A).inv ≫ biproduct.π A i) ≫ Sigma.ι A i := by
  let e := biproduct.isoCoproduct A
  calc
    f = (f ≫ e.inv) ≫ (𝟙 (⨁ A)) ≫ e.hom := by simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := by
      rw [← biproduct.total]
      simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc,
        e, biproduct.isoCoproduct_hom, biproduct.ι_desc]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unitHom_lift {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (h : Function.Surjective (SheafOfModules.sectionsMap f)) (q : unitObj X ⟶ N) :
    ∃ p : unitObj X ⟶ M, p ≫ f = q := by
  obtain ⟨s, hs⟩ := h (N.unitHomEquiv q)
  refine ⟨M.unitHomEquiv.symm s, ?_⟩
  apply N.unitHomEquiv.injective
  rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply, hs]

attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual coordinate section surjectivity descends finite global generators by one original twist. -/
theorem exists_generatingSections_predecessor
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] (j : σ)
    (hM : ∀ q : ℕ, 0 < q → Subsingleton (CategoryTheory.Sheaf.H
      (M ⊗ coordinateHyperplaneTwist (R := R) j (-(q : ℤ))).sheaf q)) (b : ℕ)
    (G : (M ⊗ coordinateHyperplaneTwist (R := R) j ((b + 1 : ℕ) : ℤ)).GeneratingSections)
    [hGG : G.IsFiniteType] :
    ∃ H : (M ⊗ coordinateHyperplaneTwist (R := R) j (b : ℤ)).GeneratingSections, H.IsFiniteType := by
  classical
  let X := Proj (homogeneousSubmodule σ R)
  let t : ℤ := ((b + 1 : ℕ) : ℤ)
  let Q : X.Modules := M ⊗ coordinateHyperplaneTwist (R := R) j (t - 1)
  let L : X.Modules := coordinateHyperplaneTwist (R := R) j 1
  let I := Fin 1 → σ
  let A : I → X.Modules := fun _ => Q
  let : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteCoproducts
  let aug := coordinateTupleAugmentation M j id t
  have hs := coordinateTupleAugmentation_sections_surjective M j hM b
  choose z hz using fun k : G.I => unitHom_lift aug hs (generatorHom G k)
  let a : G.I → I → (unitObj X ⟶ Q) :=
    fun k i => z k ≫ (biproduct.isoCoproduct A).inv ≫ biproduct.π A i
  have hc (k : G.I) : generatorHom G k =
      ∑ i : I, a k i ≫ coordinateLowerMul M j (i 0) t := by
    calc
      generatorHom G k = z k ≫ aug := (hz k).symm
      _ = (∑ i : I, (a k i ≫ Sigma.ι A i)) ≫ aug :=
        congrArg (fun f => f ≫ aug) (coproduct_decomposition A (z k))
      _ = _ := by
        rw [Preadditive.sum_comp]
        apply Finset.sum_congr rfl
        intro i _
        exact (Category.assoc _ _ _).trans
          (congrArg (fun f => a k i ≫ f) (coordinateTupleAugmentation_ι M j id t i))
  let e := lowerTensorIso M j t
  let H := G.ofEpi e.inv
  let : H.IsFiniteType := by dsimp only [H]; infer_instance
  have hH (k : H.I) : generatorHom H k =
      ∑ i : I, tensorSectionHom (a k i)
        (ProjectiveTwistGlobalGeneration.coordinateSectionHom j (i 0) 1) := by
    rw [generatorHom_ofEpi, hc k, Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    have hp := tensorSectionHom_coordinate M j (i 0) t (a k i)
    have hh := congrArg (fun f => f ≫ e.inv) hp
    simpa only [e, Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh.symm
  have result := SchemeFiniteTensorGeneratorDescent.exists_generatingSections_of_tensor_expansions Q L
    (coordinateHyperplaneTwist_isInvertible j 1) H a
    (fun _ i => ProjectiveTwistGlobalGeneration.coordinateSectionHom j (i 0) 1) hH
  have he : t - 1 = (b : ℤ) := by dsimp [t]; omega
  change ∃ H : (M ⊗ coordinateHyperplaneTwist (R := R) j (t - 1)).GeneratingSections,
    H.IsFiniteType at result
  rw [he] at result
  exact result

end EnvelopeProperty.ProjectiveCoordinateGeneratorDescent
