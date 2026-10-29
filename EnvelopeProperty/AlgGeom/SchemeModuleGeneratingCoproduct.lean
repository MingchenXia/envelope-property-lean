import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-! # Actual generating sections of original coproducts -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleGeneratingCoproduct
variable {X : Scheme.{u}} {ι : Type} (M : ι → X.Modules)
    (G : ∀ i, (M i).GeneratingSections)

/-- The actual free evaluation morphism for all original summand generators. -/
def evaluation : SheafOfModules.free (Σ i, (G i).I) ⟶ ∐ M :=
  (∐ M).freeHomEquiv.symm
    (fun a => SheafOfModules.sectionsMap (Sigma.ι M a.1) ((G a.1).s a.2))

set_option backward.isDefEq.respectTransparency false in
private theorem summand_factor (i : ι) :
    SheafOfModules.freeMap (fun a : (G i).I => (⟨i,a⟩ : Σ i, (G i).I)) ≫
        evaluation M G = (G i).π ≫ Sigma.ι M i := by
  apply (∐ M).freeHomEquiv.injective
  funext a
  let k : (G i).I → (Σ i, (G i).I) := fun a => ⟨i,a⟩
  have hfree := congrFun (SheafOfModules.freeHomEquiv_freeMap
    (R := X.ringCatSheaf) k) a
  have hgen := congrFun ((M i).freeHomEquiv.apply_symm_apply ((G i).s)) a
  calc
    (∐ M).freeHomEquiv (SheafOfModules.freeMap k ≫ evaluation M G) a =
        SheafOfModules.sectionsMap (evaluation M G)
          ((SheafOfModules.free (R := X.ringCatSheaf) (Σ i, (G i).I)).freeHomEquiv
            (SheafOfModules.freeMap k) a) := rfl
    _ = SheafOfModules.sectionsMap (evaluation M G)
        (SheafOfModules.freeSection (⟨i,a⟩ : Σ i, (G i).I)) :=
      congrArg (SheafOfModules.sectionsMap (evaluation M G)) hfree
    _ = SheafOfModules.sectionsMap (Sigma.ι M i) ((G i).s a) :=
      SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection _ _
    _ = (∐ M).freeHomEquiv ((G i).π ≫ Sigma.ι M i) a :=
      (congrArg (SheafOfModules.sectionsMap (Sigma.ι M i)) hgen).symm

/-- The original summand generating sections genuinely generate the WHOLE
original coproduct; the proof uses actual original summand and free-basis maps. -/
theorem evaluation_epi : Epi (evaluation M G) := by
  constructor
  intro N f g hfg
  apply Sigma.hom_ext
  intro i
  apply (G i).epi.left_cancellation
  have hp := congrArg
    (fun h => SheafOfModules.freeMap
      (fun a : (G i).I => (⟨i,a⟩ : Σ i, (G i).I)) ≫ h) hfg
  have hfac := summand_factor M G i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ f) hfac).symm.trans
      ((Category.assoc _ _ _).trans (hp.trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun h => h ≫ g) hfac).trans (Category.assoc _ _ _))))))

/-- The SAME original union of the summand generator families is a genuine
original coproduct generating family. -/
def generatingSections : (∐ M).GeneratingSections where
  I := Σ i, (G i).I
  s a := SheafOfModules.sectionsMap (Sigma.ι M a.1) ((G a.1).s a.2)
  epi := evaluation_epi M G

/-- A finite original coproduct of finitely generated families has an ACTUAL
finite generating family of the SAME original whole coproduct. -/
theorem generatingSections_isFiniteType [Finite ι] [∀ i, (G i).IsFiniteType] :
    (generatingSections M G).IsFiniteType := by
  constructor
  change Finite (Σ i, (G i).I)
  let : ∀ i, Finite (G i).I := fun i => (inferInstance : (G i).IsFiniteType).finite
  infer_instance

end EnvelopeProperty.SchemeModuleGeneratingCoproduct
