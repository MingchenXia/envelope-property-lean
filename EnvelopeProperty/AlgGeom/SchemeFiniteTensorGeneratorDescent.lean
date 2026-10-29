import EnvelopeProperty.AlgGeom.SchemeGeneratedTensorSections

/-! # Finite original generators descend through an invertible tensor factor -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeFiniteTensorGeneratorDescent
open SchemeTensorSectionHoms SchemeGeneratingSectionsUnit
attribute [local instance] Scheme.Modules.monoidalCategory

private theorem tensorSectionHom_comp_whisker {X : Scheme.{u}} {A B L : X.Modules}
    (a : unitObj X ⟶ A) (b : unitObj X ⟶ L) (f : A ⟶ B) :
    tensorSectionHom a b ≫ f ▷ L = tensorSectionHom (a ≫ f) b := by
  simpa only [MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_id, Category.comp_id]
    using tensorSectionHom_comp a b f (𝟙 L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- If finite tensor-product generators have finite actual pure-tensor
expansions, their coefficient sections generate the original module. -/
theorem exists_generatingSections_of_tensor_expansions {X : Scheme.{u}} (Q L : X.Modules)
    (hL : IsInvertible L) (G : (Q ⊗ L).GeneratingSections) [hGG : G.IsFiniteType]
    {I : Type} [Fintype I] (a : G.I → I → (unitObj X ⟶ Q))
    (b : G.I → I → (unitObj X ⟶ L))
    (hG : ∀ j, generatorHom G j = ∑ i : I, tensorSectionHom (a j i) (b j i)) :
    ∃ H : Q.GeneratingSections, H.IsFiniteType := by
  classical
  let K := G.I × I
  let A : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) K
  let B : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) G.I
  let f : A ⟶ Q := Sigma.desc (C := X.Modules) fun ji : K => a ji.1 ji.2
  let g : B ⟶ A ⊗ L :=
    Sigma.desc (C := X.Modules) fun j => ∑ i : I, (show unitObj X ⟶ A ⊗ L from tensorSectionHom (SheafOfModules.ιFree (j, i)) (b j i))
  have hfac : g ≫ f ▷ L = G.π := by
    apply Sigma.hom_ext (C := X.Modules)
    intro j
    rw [← Category.assoc, Sigma.ι_desc, Preadditive.sum_comp]
    change (∑ i : I, tensorSectionHom (SheafOfModules.ιFree (j, i)) (b j i) ≫ f ▷ L) = generatorHom G j
    rw [hG j]
    apply Finset.sum_congr rfl
    intro i _
    rw [tensorSectionHom_comp_whisker]
    congr 1
    exact Sigma.ι_desc (fun ji : K => a ji.1 ji.2) (j, i)
  let F := tensorRight (C := X.Modules) L
  let : F.IsEquivalence := SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence L hL
  let : Epi G.π := G.epi
  have hf : Epi (f ▷ L) := epi_of_epi_fac hfac
  have hf' : Epi f := F.epi_of_epi_map hf
  let H : Q.GeneratingSections :=
    { I := K
      s := Q.freeHomEquiv f
      epi := by
        rw [Equiv.symm_apply_apply]
        exact hf' }
  refine ⟨H, ⟨?_⟩⟩
  change Finite (G.I × I)
  let : Finite G.I := hGG.finite
  infer_instance

end EnvelopeProperty.SchemeFiniteTensorGeneratorDescent
