import EnvelopeProperty.DeligneIllusie.WittTwoExteriorLiftMaps
import EnvelopeProperty.Algebra.ModuleComplexNativeCycleClasses

/-!
# Witt Two Native Cycle Classes

Actual SAME whole native cycles, boundaries and homology classes of original divided exterior maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.DeligneIllusie.WittTwoNativeCycleClasses
open CategoryTheory Limits
open scoped TensorProduct
universe u

/-- The SAME actual native whole cycle-class function as a genuine entire linear map. -/
def classLinear {A : Type u} [CommRing A] (K : CochainComplex (ModuleCat A) ℕ) (q : ℕ) :
    LinearMap.ker (K.sc q).g.hom →ₗ[A] K.homology q :=
  (K.homologyπ q).hom.comp (K.sc q).moduleCatCyclesIso.inv.hom

/-- EVERY actual whole cycle retains EXACTLY its SAME original native cycle class. -/
theorem classLinear_value {A : Type u} [CommRing A] (K : CochainComplex (ModuleCat A) ℕ)
    (q : ℕ) (z : LinearMap.ker (K.sc q).g.hom) :
    classLinear K q z = ModuleComplexNativeCycleClasses.cycleClass K q z := rfl

/-- EVERY actual incoming boundary has zero SAME ORIGINAL whole native homology class. -/
theorem classLinear_boundary {A : Type u} [CommRing A] (K : CochainComplex (ModuleCat A) ℕ)
    (q : ℕ) (a : (K.sc q).X₁) :
    classLinear K q ((K.sc q).moduleCatToCycles a) = 0 := by
  change (K.sc q).homologyπ
    ((K.sc q).moduleCatCyclesIso.inv ((K.sc q).moduleCatToCycles a)) = 0
  rw [ShortComplex.moduleCatCyclesIso_inv_π_apply]
  have hz : (Submodule.Quotient.mk ((K.sc q).moduleCatToCycles a) :
      LinearMap.ker (K.sc q).g.hom ⧸ LinearMap.range (K.sc q).moduleCatToCycles) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ a)
  change (K.sc q).moduleCatHomologyIso.inv.hom
    (Submodule.Quotient.mk ((K.sc q).moduleCatToCycles a)) = 0
  rw [hz]
  exact map_zero _

/-- A genuine original boundary difference gives equality of SAME actual native whole classes. -/
theorem classLinear_eq_of_boundary {A : Type u} [CommRing A] (K : CochainComplex (ModuleCat A) ℕ)
    (q : ℕ) (z w : LinearMap.ker (K.sc q).g.hom) (a : (K.sc q).X₁)
    (h : z-w = (K.sc q).moduleCatToCycles a) : classLinear K q z = classLinear K q w := by
  have he := congrArg (classLinear K q) h
  rw [map_sub, classLinear_boundary] at he
  exact sub_eq_zero.mp he

/-- EVERY genuine native whole cochain map induces the actual linear map on ORIGINAL cycle kernels. -/
def mapCycleLinear {A : Type u} [CommRing A] {K L : CochainComplex (ModuleCat A) ℕ}
    (φ : K ⟶ L) (q : ℕ) : LinearMap.ker (K.sc q).g.hom →ₗ[A] LinearMap.ker (L.sc q).g.hom where
  toFun z := ⟨φ.f q z.val, by
    have h := ConcreteCategory.congr_hom (φ.comm q ((ComplexShape.up ℕ).next q)) z.val
    change L.d q ((ComplexShape.up ℕ).next q) (φ.f q z.val) =
      φ.f ((ComplexShape.up ℕ).next q) (K.d q ((ComplexShape.up ℕ).next q) z.val) at h
    exact h.trans ((congrArg (φ.f ((ComplexShape.up ℕ).next q)) z.property).trans (map_zero _))⟩
  map_add' z w := Subtype.ext ((φ.f q).hom.map_add z.val w.val)
  map_smul' a z := Subtype.ext ((φ.f q).hom.map_smul a z.val)

/-- EVERY actual native image cycle retains the SAME entire original component value. -/
theorem mapCycleLinear_value {A : Type u} [CommRing A] {K L : CochainComplex (ModuleCat A) ℕ}
    (φ : K ⟶ L) (q : ℕ) (z : LinearMap.ker (K.sc q).g.hom) :
    (mapCycleLinear φ q z).val = φ.f q z.val := rfl

private theorem nativeZeroSquare {A : Type u} [CommRing A] (X : ℕ → ModuleCat.{u} A) :
    ∀ q, (0 : X q ⟶ X (q+1)) ≫ (0 : X (q+1) ⟶ X (q+1+1)) = 0 := fun _ => by simp

private def nativeZeroCycle {A : Type u} [CommRing A] (X : ℕ → ModuleCat.{u} A) (q : ℕ) :
    X q →ₗ[A] LinearMap.ker ((CochainComplex.of X (fun _ => 0) (nativeZeroSquare X)).sc q).g.hom where
  toFun w := ModuleComplexNativeCycleClasses.ofCycle X (fun _ => 0) (nativeZeroSquare X) q
    ⟨w, by change (0 : X q →ₗ[A] X (q+1)) w = 0; exact LinearMap.zero_apply _⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
  WittTwoLiftDifference.frobeniusAlgebra
  WittTwoOriginalCotangentMaps.originalResidueRing WittTwoOriginalCotangentMaps.residueAlgebra
  WittTwoExteriorLiftMaps.originalCommSemiring WittTwoExteriorLiftMaps.originalSemiring
variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A]
private abbrev B := WittTwoSmoothDifferentials.ResidueAlgebra p k A
private abbrev N := KaehlerDifferential k (B p k A)

/-- EVERY original exterior form is an ACTUAL entire native cycle of the SAME zero-differential source. -/
def sourceCycle (q : ℕ) : (⋀[B p k A]^q (N p k A)) →ₗ[B p k A]
    LinearMap.ker ((WittTwoExteriorLiftMaps.zeroComplex p k A).sc q).g.hom :=
  nativeZeroCycle (fun q => ModuleCat.of (B p k A) (⋀[B p k A]^q (N p k A))) q

omit [CharP k p] [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A] in
/-- The SAME source native cycle retains its entire original exterior form. -/
theorem sourceCycle_value (q : ℕ) (w : ⋀[B p k A]^q (N p k A)) :
    (sourceCycle p k A q w).val = w := rfl

variable (f : WittTwoLiftDifference.Lift p k A)
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable {n : ℕ} (v : Fin n → B p k A)
  (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)

/-- The SAME actual exterior cochain map supplies an actual whole native cycle for EVERY original form. -/
def cycleMap (q : ℕ) : (⋀[B p k A]^q (N p k A)) →ₗ[B p k A]
    LinearMap.ker ((Cartier.EtaleAlgebraFrobeniusComplex.complex v hv p).sc q).g.hom :=
  (mapCycleLinear (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv) q).comp (sourceCycle p k A q)

/-- EVERY original divided native cycle has EXACTLY the SAME actual exterior-map value. -/
theorem cycleMap_value (q : ℕ) (w : ⋀[B p k A]^q (N p k A)) :
    (cycleMap p k A f hf v hv q w).val = WittTwoExteriorLiftMaps.formMap p k A f hf q w := rfl

/-- The SAME actual original divided exterior cycles have their genuine WHOLE native homology classes. -/
def classMap (q : ℕ) : (⋀[B p k A]^q (N p k A)) →ₗ[B p k A]
    (Cartier.EtaleAlgebraFrobeniusComplex.complex v hv p).homology q :=
  (classLinear (Cartier.EtaleAlgebraFrobeniusComplex.complex v hv p) q).comp (cycleMap p k A f hf v hv q)

/-- EVERY original form has exactly its SAME actual native whole-complex divided cycle class. -/
theorem classMap_value (q : ℕ) (w : ⋀[B p k A]^q (N p k A)) :
    classMap p k A f hf v hv q w = ModuleComplexNativeCycleClasses.cycleClass
      (Cartier.EtaleAlgebraFrobeniusComplex.complex v hv p) q (cycleMap p k A f hf v hv q w) := rfl

/-- The ACTUAL native homology functor sends EVERY original source class to its SAME genuine divided class. -/
theorem homologyMap_sourceClass (q : ℕ) (w : ⋀[B p k A]^q (N p k A)) :
    (HomologicalComplex.homologyMap (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv) q).hom
      (ModuleComplexNativeCycleClasses.cycleClass (WittTwoExteriorLiftMaps.zeroComplex p k A) q
        (sourceCycle p k A q w)) = classMap p k A f hf v hv q w := by
  rw [classMap_value]
  apply ModuleComplexNativeCycleClasses.homologyMap_cycleClass
  rw [sourceCycle_value, cycleMap_value]
  rfl
end EnvelopeProperty.DeligneIllusie.WittTwoNativeCycleClasses
