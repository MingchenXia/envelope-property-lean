import EnvelopeProperty.Algebra.ModuleComplexNativeCycleClasses
import Mathlib.Algebra.Homology.SingleHomology

/-! # The actual single-complex homology map retains its original native cycle -/
noncomputable section
namespace EnvelopeProperty.DI.LeadingCartierCycleTransport
open CategoryTheory CategoryTheory.Limits
universe u
variable {A : Type u} [CommRing A]

/-- The genuine homology map of the SAME whole map out of the native single source. -/
def singleClassMap (q : ℕ) (M : ModuleCat A) (E : CochainComplex (ModuleCat A) ℕ)
    (φ : M ⟶ E.X q) (hφ : ∀ j, (ComplexShape.up ℕ).Rel q j → φ ≫ E.d q j = 0) :
    M ⟶ E.homology q :=
  (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) q M).inv ≫
    HomologicalComplex.homologyMap (HomologicalComplex.mkHomFromSingle φ hφ) q

theorem singleClassMap_eq_liftCycles (q : ℕ) (M : ModuleCat A)
    (E : CochainComplex (ModuleCat A) ℕ) (φ : M ⟶ E.X q)
    (hφ : ∀ j, (ComplexShape.up ℕ).Rel q j → φ ≫ E.d q j = 0) :
    singleClassMap q M E φ hφ =
      E.liftCycles φ (q+1) (by simp) (hφ (q+1) (by simp)) ≫ E.homologyπ q := by
  let H := HomologicalComplex.mkHomFromSingle φ hφ
  let e := HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) q M
  have hcycles : HomologicalComplex.cyclesMap H q =
      e.hom ≫ E.liftCycles φ (q+1) (by simp) (hφ (q+1) (by simp)) := by
    apply (cancel_mono (E.iCycles q)).mp
    rw [HomologicalComplex.cyclesMap_i, Category.assoc, HomologicalComplex.liftCycles_i]
    change ((HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) q).obj M).iCycles q ≫
      (HomologicalComplex.mkHomFromSingle φ hφ).f q = e.hom ≫ φ
    rw [HomologicalComplex.mkHomFromSingle_f]
    exact (Category.assoc _ _ _).symm
  unfold singleClassMap
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc,
    HomologicalComplex.singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv,
    HomologicalComplex.homologyπ_naturality, hcycles, Category.assoc]

/-- Its value is the class of the original cycle in the SAME actual whole target complex. -/
theorem singleClassMap_cycleClass (q : ℕ) (M : ModuleCat A) (E : CochainComplex (ModuleCat A) ℕ)
    (φ : M ⟶ E.X q) (hφ : ∀ j, (ComplexShape.up ℕ).Rel q j → φ ≫ E.d q j = 0)
    (x : M) (z : LinearMap.ker (E.sc q).g.hom) (hz : φ x = z.val) :
    (singleClassMap q M E φ hφ).hom x = ModuleComplexNativeCycleClasses.cycleClass E q z := by
  rw [singleClassMap_eq_liftCycles]
  have hi := congrArg (fun L : M ⟶ E.X q => L x)
    (E.liftCycles_i φ (q+1) (by simp) (hφ (q+1) (by simp)))
  change E.iCycles q (E.liftCycles φ (q+1) (by simp) (hφ (q+1) (by simp)) x) = φ x at hi
  have hc := (E.sc q).moduleCatCyclesIso_inv_iCycles_apply z
  have heq : E.liftCycles φ (q+1) (by simp) (hφ (q+1) (by simp)) x =
      (E.sc q).moduleCatCyclesIso.inv z := by
    apply (ModuleCat.mono_iff_injective (E.iCycles q)).mp inferInstance
    exact hi.trans (hz.trans hc.symm)
  exact congrArg (E.homologyπ q) heq
end EnvelopeProperty.DI.LeadingCartierCycleTransport
