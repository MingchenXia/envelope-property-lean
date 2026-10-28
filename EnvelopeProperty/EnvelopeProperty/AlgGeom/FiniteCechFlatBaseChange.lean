import EnvelopeProperty.Algebra.FlatKernelBaseChange
import ModularCurves.ForMathlib.SheafModuleCechSectionsExact
import ModularCurves.ForMathlib.SheafModuleCechSectionsDifferential
import Mathlib.LinearAlgebra.TensorProduct.Pi
import ModularCurves.ForMathlib.SchemeModuleCechRestrict

/-! # Finite actual sheaf Cech kernels under flat scalar extension -/
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.FiniteCechFlatBaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
/-- Scalar extension using the literal original R-algebra action. -/
def tensorFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} S where
  obj M := ModuleCat.of S (S ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.baseChange S)
  map_id M := by
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_comp f.hom g.hom

variable {T : TopCat.{u}}
variable (F : TopCat.Sheaf (ModuleCat.{u} R) T)
variable (G : TopCat.Sheaf (ModuleCat.{u} S) T)
variable (ψ : F.obj ⋙ tensorFunctor (R := R) (S := S) ⟶ G.obj)
variable {ι : Type u} (U : ι → Opens T)

/-- The original natural comparison on the original entire open-section module. -/
def componentMap (W : Opens T) :
    S ⊗[R] F.obj.obj (op W) →ₗ[S] G.obj.obj (op W) := (ψ.app (op W)).hom

/-- Naturality retains every original restricted pure tensor. -/
theorem componentMap_restrict {V W : Opens T} (h : V ≤ W)
    (s : S) (m : F.obj.obj (op W)) :
    (G.obj.map (homOfLE h).op).hom (componentMap F G ψ W (s ⊗ₜ[R] m)) =
      componentMap F G ψ V (s ⊗ₜ[R] (F.obj.map (homOfLE h).op).hom m) :=
  (ConcreteCategory.congr_hom (ψ.naturality (homOfLE h).op) (s ⊗ₜ[R] m)).symm

private def componentEquiv (W : Opens T) [IsIso (ψ.app (op W))] :
    S ⊗[R] F.obj.obj (op W) ≃ₗ[S] G.obj.obj (op W) :=
  (asIso (ψ.app (op W))).toLinearEquiv

private def termEquiv [Finite ι] (n : ℕ) (W : Opens T)
    [∀ i : Fin (n + 1) → ι,
      IsIso (ψ.app (op (W ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))))] :
    S ⊗[R] (TopCat.Sheaf.moduleCechTerm F U n).obj.obj (op W) ≃ₗ[S]
      (TopCat.Sheaf.moduleCechTerm G U n).obj.obj (op W) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  exact (TopCat.Sheaf.moduleCechTermSectionsLinearEquiv F U n W).baseChange R S ≪≫ₗ
    TensorProduct.piRight R S S
      (fun i : Fin (n + 1) → ι =>
        F.obj.obj (op (W ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k)))) ≪≫ₗ
    LinearEquiv.piCongrRight
      (fun i => componentEquiv F G ψ (W ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))) ≪≫ₗ
    (TopCat.Sheaf.moduleCechTermSectionsLinearEquiv G U n W).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem termEquiv_tmul [Finite ι] (n : ℕ) (W : Opens T)
    [∀ i : Fin (n + 1) → ι,
      IsIso (ψ.app (op (W ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))))]
    (s : S) (x : (TopCat.Sheaf.moduleCechTerm F U n).obj.obj (op W))
    (i : Fin (n + 1) → ι) :
    TopCat.Sheaf.moduleCechTermSectionsLinearEquiv G U n W
        (termEquiv F G ψ U n W (s ⊗ₜ[R] x)) i =
      componentMap F G ψ (W ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))
        (s ⊗ₜ[R] TopCat.Sheaf.moduleCechTermSectionsLinearEquiv F U n W x i) := by
  classical
  simp only [termEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.baseChange_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
    LinearEquiv.piCongrRight_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem differentialSquare [Finite ι] (W : Opens T)
    [∀ i : Fin 1 → ι,
      IsIso (ψ.app (op (W ⊓ ∏ᶜ fun k : Fin 1 => U (i k))))]
    [∀ i : Fin 2 → ι,
      IsIso (ψ.app (op (W ⊓ ∏ᶜ fun k : Fin 2 => U (i k))))] :
    ((TopCat.Sheaf.moduleCechDifferential G U 0).hom.app (op W)).hom.comp
        (termEquiv F G ψ U 0 W).toLinearMap =
      (termEquiv F G ψ U 1 W).toLinearMap.comp
        (AlgebraTensorModule.lTensor S S
          ((TopCat.Sheaf.moduleCechDifferential F U 0).hom.app (op W)).hom) := by
  let : Module R ((TopCat.Sheaf.moduleCechTerm G U 1).obj.obj (op W)) :=
    Module.compHom _ (algebraMap R S)
  let : IsScalarTower R S ((TopCat.Sheaf.moduleCechTerm G U 1).obj.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  apply AlgebraTensorModule.ext
  intro s x
  apply (TopCat.Sheaf.moduleCechTermSectionsLinearEquiv G U 1 W).injective
  funext i
  change TopCat.Sheaf.moduleCechTermSectionsLinearEquiv G U 1 W
      (((TopCat.Sheaf.moduleCechDifferential G U 0).hom.app (op W))
        (termEquiv F G ψ U 0 W (s ⊗ₜ[R] x))) i =
    TopCat.Sheaf.moduleCechTermSectionsLinearEquiv G U 1 W
      (termEquiv F G ψ U 1 W
        (s ⊗ₜ[R] ((TopCat.Sheaf.moduleCechDifferential F U 0).hom.app (op W)) x)) i
  erw [TopCat.Sheaf.moduleCechDifferential_apply, termEquiv_tmul,
    TopCat.Sheaf.moduleCechDifferential_apply, TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  erw [termEquiv_tmul, TensorProduct.tmul_smul, map_zsmul,
    componentMap_restrict]
  rfl

private def sectionsKernelMap (W : Opens T) :
    F.obj.obj (op W) →ₗ[R]
      LinearMap.ker ((TopCat.Sheaf.moduleCechDifferential F U 0).hom.app (op W)).hom :=
  ((TopCat.Sheaf.moduleCechAugmentation F U).hom.app (op W)).hom.codRestrict _
    (fun x => by
      exact (TopCat.Sheaf.moduleCechAugmentedShortComplexApp F U W).moduleCat_zero_apply x)

private def sectionsKernelEquiv (hU : ⨆ i, U i = ⊤) (W : Opens T) :
    F.obj.obj (op W) ≃ₗ[R]
      LinearMap.ker ((TopCat.Sheaf.moduleCechDifferential F U 0).hom.app (op W)).hom := by
  have hmono := TopCat.Sheaf.moduleCechAugmentation_app_mono F U W hU
  have hi := (ModuleCat.mono_iff_injective _).mp hmono
  have he := (ShortComplex.moduleCat_exact_iff _).mp
    (TopCat.Sheaf.moduleCechAugmentedShortComplexApp_exact F U W hU)
  apply LinearEquiv.ofBijective (sectionsKernelMap F U W)
  constructor
  · intro x y h
    exact hi (congrArg Subtype.val h)
  · intro z
    obtain ⟨x, hx⟩ := he
      (z : (TopCat.Sheaf.moduleCechTerm F U 0).obj.obj (op W)) z.property
    exact ⟨x, Subtype.ext hx⟩

private theorem sectionsKernelEquiv_apply (hU : ⨆ i, U i = ⊤) (W : Opens T)
    (m : F.obj.obj (op W)) :
    (sectionsKernelEquiv F U hU W m :
        (TopCat.Sheaf.moduleCechTerm F U 0).obj.obj (op W)) =
      (TopCat.Sheaf.moduleCechAugmentation F U).hom.app (op W) m := rfl

/-- Actual flatness and a natural section comparison on the two finite
intersection families derive the whole open-section equivalence. -/
def tensorEquiv [Module.Flat R S] [Finite ι] (hU : ⨆ i, U i = ⊤) (W : Opens T)
    [∀ i : Fin 1 → ι,
      IsIso (ψ.app (op (W ⊓ ∏ᶜ fun k : Fin 1 => U (i k))))]
    [∀ i : Fin 2 → ι,
      IsIso (ψ.app (op (W ⊓ ∏ᶜ fun k : Fin 2 => U (i k))))] :
    S ⊗[R] F.obj.obj (op W) ≃ₗ[S] G.obj.obj (op W) :=
  (sectionsKernelEquiv F U hU W).baseChange R S ≪≫ₗ
    FlatKernelBaseChange.kernelEquiv
      ((TopCat.Sheaf.moduleCechDifferential F U 0).hom.app (op W)).hom
      ((TopCat.Sheaf.moduleCechDifferential G U 0).hom.app (op W)).hom
      (termEquiv F G ψ U 0 W) (termEquiv F G ψ U 1 W)
      (differentialSquare F G ψ U W) ≪≫ₗ
    (sectionsKernelEquiv G U hU W).symm

private theorem tensorEquiv_augmentation [Module.Flat R S] [Finite ι]
    (hU : ⨆ i, U i = ⊤) (W : Opens T)
    [∀ i : Fin 1 → ι,
      IsIso (ψ.app (op (W ⊓ ∏ᶜ fun k : Fin 1 => U (i k))))]
    [∀ i : Fin 2 → ι,
      IsIso (ψ.app (op (W ⊓ ∏ᶜ fun k : Fin 2 => U (i k))))]
    (s : S) (m : F.obj.obj (op W)) :
    (TopCat.Sheaf.moduleCechAugmentation G U).hom.app (op W)
        (tensorEquiv F G ψ U hU W (s ⊗ₜ[R] m)) =
      termEquiv F G ψ U 0 W
        (s ⊗ₜ[R] (TopCat.Sheaf.moduleCechAugmentation F U).hom.app (op W) m) := by
  have hh := (sectionsKernelEquiv G U hU W).apply_symm_apply
    (FlatKernelBaseChange.kernelEquiv
      ((TopCat.Sheaf.moduleCechDifferential F U 0).hom.app (op W)).hom
      ((TopCat.Sheaf.moduleCechDifferential G U 0).hom.app (op W)).hom
      (termEquiv F G ψ U 0 W) (termEquiv F G ψ U 1 W)
      (differentialSquare F G ψ U W)
      (((sectionsKernelEquiv F U hU W).baseChange R S _ _) (s ⊗ₜ[R] m)))
  have hc := congrArg Subtype.val hh
  change (sectionsKernelEquiv G U hU W
      (tensorEquiv F G ψ U hU W (s ⊗ₜ[R] m)) :
        (TopCat.Sheaf.moduleCechTerm G U 0).obj.obj (op W)) = _ at hc
  rw [sectionsKernelEquiv_apply, LinearEquiv.baseChange_tmul,
    FlatKernelBaseChange.kernelEquiv_tmul, sectionsKernelEquiv_apply] at hc
  exact hc

/-- The equivalence is the original comparison on EVERY original pure tensor. -/
theorem tensorEquiv_tmul [Module.Flat R S] [Finite ι]
    (hU : ⨆ i, U i = ⊤) (W : Opens T)
    [∀ i : Fin 1 → ι,
      IsIso (ψ.app (op (W ⊓ ∏ᶜ fun k : Fin 1 => U (i k))))]
    [∀ i : Fin 2 → ι,
      IsIso (ψ.app (op (W ⊓ ∏ᶜ fun k : Fin 2 => U (i k))))]
    (s : S) (m : F.obj.obj (op W)) :
    tensorEquiv F G ψ U hU W (s ⊗ₜ[R] m) =
      componentMap F G ψ W (s ⊗ₜ[R] m) := by
  apply (ModuleCat.mono_iff_injective _).mp
    (TopCat.Sheaf.moduleCechAugmentation_app_mono G U W hU)
  apply (TopCat.Sheaf.moduleCechTermSectionsLinearEquiv G U 0 W).injective
  funext i
  rw [tensorEquiv_augmentation, termEquiv_tmul,
    TopCat.Sheaf.moduleCechAugmentation_apply, TopCat.Sheaf.moduleCechAugmentation_apply]
  exact (componentMap_restrict F G ψ inf_le_left s m).symm

/-- In particular the ACTUAL original natural component on the whole
section module is an isomorphism; no H0 or Cech matching premise. -/
theorem isIso_component [Module.Flat R S] [Finite ι]
    (hU : ⨆ i, U i = ⊤) (W : Opens T)
    [∀ i : Fin 1 → ι,
      IsIso (ψ.app (op (W ⊓ ∏ᶜ fun k : Fin 1 => U (i k))))]
    [∀ i : Fin 2 → ι,
      IsIso (ψ.app (op (W ⊓ ∏ᶜ fun k : Fin 2 => U (i k))))] :
    IsIso (ψ.app (op W)) := by
  have he : (tensorEquiv F G ψ U hU W).toLinearMap = componentMap F G ψ W := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s m => exact tensorEquiv_tmul F G ψ U hU W s m
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (componentMap F G ψ W)
  rw [← he]
  exact (tensorEquiv F G ψ U hU W).bijective

end EnvelopeProperty.FiniteCechFlatBaseChange
