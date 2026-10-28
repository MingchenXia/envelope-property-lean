import EnvelopeProperty.Algebra.ModuleHomologyScalarRestriction
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Native whole-complex maps retain every actual original module cycle class -/
noncomputable section
namespace EnvelopeProperty.ModuleComplexNativeCycleClasses
open CategoryTheory
universe u
private theorem actualClass_map {A : Type u} [CommRing A]
    {S T : ShortComplex (ModuleCat A)} (φ : S ⟶ T)
    (z : LinearMap.ker S.g.hom) (w : LinearMap.ker T.g.hom)
    (hzw : φ.τ₂ z.val = w.val) :
    ShortComplex.homologyMap φ (S.homologyπ (S.moduleCatCyclesIso.inv z)) =
      T.homologyπ (T.moduleCatCyclesIso.inv w) := by
  have hc : ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv z) =
      T.moduleCatCyclesIso.inv w := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    have h := congrArg (fun F : S.cycles ⟶ T.X₂ => F (S.moduleCatCyclesIso.inv z))
      (ShortComplex.cyclesMap_i φ)
    change T.iCycles (ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv z)) =
      φ.τ₂ (S.iCycles (S.moduleCatCyclesIso.inv z)) at h
    exact h.trans ((congrArg φ.τ₂ (S.moduleCatCyclesIso_inv_iCycles_apply z)).trans
      (hzw.trans (T.moduleCatCyclesIso_inv_iCycles_apply w).symm))
  have h := congrArg (fun F : S.cycles ⟶ T.homology => F (S.moduleCatCyclesIso.inv z))
    (ShortComplex.homologyπ_naturality φ)
  change ShortComplex.homologyMap φ (S.homologyπ (S.moduleCatCyclesIso.inv z)) =
    T.homologyπ (ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv z)) at h
  exact h.trans (congrArg T.homologyπ hc)

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The actual class of EVERY original native kernel cycle in the SAME whole cochain complex. -/
def cycleClass (K : CochainComplex (ModuleCat A) ℕ) (q : ℕ)
    (z : LinearMap.ker (K.sc q).g.hom) : K.homology q :=
  K.homologyπ q ((K.sc q).moduleCatCyclesIso.inv z)

/-- The ACTUAL native HomologicalComplex homology functor preserves EVERY whole original
cycle class, not just a separately constructed quotient map. -/
theorem homologyMap_cycleClass {K L : CochainComplex (ModuleCat A) ℕ} (φ : K ⟶ L) (q : ℕ)
    (z : LinearMap.ker (K.sc q).g.hom) (w : LinearMap.ker (L.sc q).g.hom)
    (hzw : φ.f q z.val = w.val) :
    (HomologicalComplex.homologyMap φ q).hom (cycleClass K q z) = cycleClass L q w :=
  actualClass_map ((HomologicalComplex.shortComplexFunctor (ModuleCat A) (ComplexShape.up ℕ) q).map φ)
    z w hzw

/-- GENUINE native homology preservation of scalar restriction for the SAME whole cochain
complex, using the actual native row on its actual predecessor and successor. -/
def restrictionHomologyIso (f : A →+* B) (K : CochainComplex (ModuleCat B) ℕ) (q : ℕ) :
    (((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology q ≅
      (ModuleCat.restrictScalars f).obj (K.homology q) :=
  ModuleHomologyScalarRestriction.homologyIso f (K.sc q)

/-- EVERY original native whole-complex cycle retains its SAME entire element under actual
native scalar-restriction homology preservation. -/
theorem restrictionHomologyIso_cycleClass (f : A →+* B) (K : CochainComplex (ModuleCat B) ℕ)
    (q : ℕ)
    (z : LinearMap.ker
      ((((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc q).g.hom)
    (w : LinearMap.ker (K.sc q).g.hom) (hzw : z.val = w.val) :
    (restrictionHomologyIso f K q).hom.hom
      (cycleClass (((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) q z) =
      cycleClass K q w :=
  ModuleHomologyScalarRestriction.cycleClass_comparison f (K.sc q) z w hzw

/-- Every original cycle of an ACTUAL consecutive differential is the SAME original native
kernel cycle of the SAME whole cochain complex, with target-index transport derived internally. -/
def ofCycle (X : ℕ → ModuleCat A) (d : ∀ q, X q ⟶ X (q+1))
    (sq : ∀ q, d q ≫ d (q+1) = 0) (q : ℕ) (z : LinearMap.ker (d q).hom) :
    LinearMap.ker ((CochainComplex.of X d sq).sc q).g.hom :=
  ⟨z.val, by
    change (CochainComplex.of X d sq).d q ((ComplexShape.up ℕ).next q) z.val = 0
    rw [CochainComplex.next ℕ q]
    change CochainComplex.of.d X d q (q+1) z.val = 0
    rw [CochainComplex.of_d]
    exact z.property⟩

/-- This true native cycle comparison retains the ENTIRE SAME original element. -/
theorem ofCycle_val (X : ℕ → ModuleCat A) (d : ∀ q, X q ⟶ X (q+1))
    (sq : ∀ q, d q ≫ d (q+1) = 0) (q : ℕ) (z : LinearMap.ker (d q).hom) :
    (ofCycle X d sq q z).val = z.val := rfl

end EnvelopeProperty.ModuleComplexNativeCycleClasses
