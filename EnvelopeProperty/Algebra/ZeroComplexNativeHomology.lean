import EnvelopeProperty.Algebra.ModuleComplexNativeCycleClasses

/-! # Actual entire native homology of zero-differential module complexes -/
noncomputable section
namespace EnvelopeProperty.ZeroComplexNativeHomology
open CategoryTheory
universe u
variable {R : Type u} [CommRing R]

private theorem squareZero (X : ℕ → ModuleCat.{u} R) :
    ∀ q, (0 : X q ⟶ X (q+1)) ≫ (0 : X (q+1) ⟶ X (q+1+1)) = 0 := fun _ => by simp

/-- The actual original modules with genuine zero consecutive differentials. -/
def complex (X : ℕ → ModuleCat.{u} R) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of X (fun _ => 0) (squareZero X)

/-- EVERY actual native whole differential of this SAME complex is zero. -/
theorem d_eq_zero (X : ℕ → ModuleCat.{u} R) (i j : ℕ) : (complex X).d i j = 0 := by
  by_cases h : i+1 = j
  · subst j
    exact CochainComplex.of_d X (fun _ => 0) i
  · exact CochainComplex.of_d_ne X (fun _ => 0) h

/-- The ENTIRE original object is exactly its SAME actual whole native cycle kernel. -/
def cycleEquiv (X : ℕ → ModuleCat.{u} R) (q : ℕ) :
    X q ≃ₗ[R] LinearMap.ker ((complex X).sc q).g.hom where
  toFun w := ModuleComplexNativeCycleClasses.ofCycle X (fun _ => 0) (squareZero X) q
    ⟨w, by change (0 : X q →ₗ[R] X (q+1)) w = 0; rfl⟩
  invFun z := z.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- EVERY original actual native cycle retains its SAME underlying original element. -/
theorem cycleEquiv_value (X : ℕ → ModuleCat.{u} R) (q : ℕ) (w : X q) :
    (cycleEquiv X q w).val = w := rfl

private def rowClassLinear (S : ShortComplex (ModuleCat.{u} R)) :
    LinearMap.ker S.g.hom →ₗ[R] S.homology :=
  S.moduleCatHomologyIso.inv.hom.comp (LinearMap.range S.moduleCatToCycles).mkQ

private theorem rowClassLinear_value (S : ShortComplex (ModuleCat.{u} R))
    (z : LinearMap.ker S.g.hom) : rowClassLinear S z =
      S.homologyπ (S.moduleCatCyclesIso.inv z) :=
  (S.moduleCatCyclesIso_inv_π_apply z).symm

private theorem rowClassLinear_bijective (S : ShortComplex (ModuleCat.{u} R)) (hf : S.f = 0) :
    Function.Bijective (rowClassLinear S) := by
  have hr : LinearMap.range S.moduleCatToCycles = ⊥ := by
    apply LinearMap.range_eq_bot.mpr
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change S.f a = 0
    rw [hf]
    rfl
  have hq : Function.Bijective (LinearMap.range S.moduleCatToCycles).mkQ := by
    constructor
    · intro z w h
      have hm := (Submodule.Quotient.eq (LinearMap.range S.moduleCatToCycles)).mp h
      rw [hr] at hm
      exact sub_eq_zero.mp hm
    · exact Submodule.mkQ_surjective _
  exact S.moduleCatHomologyIso.symm.toLinearEquiv.bijective.comp hq

/-- The SAME actual original whole native class as a linear map on the ENTIRE original object. -/
def classMap (X : ℕ → ModuleCat.{u} R) (q : ℕ) : X q →ₗ[R] (complex X).homology q :=
  (rowClassLinear ((complex X).sc q)).comp (cycleEquiv X q).toLinearMap

/-- EVERY original element has EXACTLY its SAME actual whole native cycleClass. -/
theorem classMap_value (X : ℕ → ModuleCat.{u} R) (q : ℕ) (w : X q) :
    classMap X q w = ModuleComplexNativeCycleClasses.cycleClass (complex X) q (cycleEquiv X q w) :=
  rowClassLinear_value ((complex X).sc q) _

/-- The actual original native class projection is bijective on EVERY entire original object. -/
theorem classMap_bijective (X : ℕ → ModuleCat.{u} R) (q : ℕ) : Function.Bijective (classMap X q) := by
  have hf : ((complex X).sc q).f = 0 := by
    change (complex X).d ((ComplexShape.up ℕ).prev q) q = 0
    exact d_eq_zero X _ _
  unfold classMap
  exact (rowClassLinear_bijective ((complex X).sc q) hf).comp (cycleEquiv X q).bijective

/-- Genuine whole native cycle-class equivalence, constructed from SAME actual class map. -/
def cycleClassEquiv (X : ℕ → ModuleCat.{u} R) (q : ℕ) : X q ≃ₗ[R] (complex X).homology q :=
  LinearEquiv.ofBijective (classMap X q) (classMap_bijective X q)

/-- EVERY original element retains its SAME genuine actual native class under that equivalence. -/
theorem cycleClassEquiv_value (X : ℕ → ModuleCat.{u} R) (q : ℕ) (w : X q) :
    cycleClassEquiv X q w = ModuleComplexNativeCycleClasses.cycleClass
      (complex X) q (cycleEquiv X q w) := classMap_value X q w

/-- The true original native whole homology isomorphism back to its ENTIRE original object. -/
def homologyIso (X : ℕ → ModuleCat.{u} R) (q : ℕ) :
    (complex X).homology q ≅ X q := (cycleClassEquiv X q).symm.toModuleIso

/-- The SAME actual native homology isomorphism recovers EVERY actual original element's class. -/
theorem homologyIso_cycleClass (X : ℕ → ModuleCat.{u} R) (q : ℕ) (w : X q) :
    (homologyIso X q).hom (ModuleComplexNativeCycleClasses.cycleClass
      (complex X) q (cycleEquiv X q w)) = w := by
  rw [← cycleClassEquiv_value]
  exact (cycleClassEquiv X q).symm_apply_apply w
end EnvelopeProperty.ZeroComplexNativeHomology
