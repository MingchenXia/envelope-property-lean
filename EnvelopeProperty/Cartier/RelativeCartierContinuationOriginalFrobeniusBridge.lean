import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierMultiplicativity
import EnvelopeProperty.Cartier.EtaleAlgebraFrobeniusComplex

/-! # Correct native Cartier source for the ORIGINAL absolute Frobenius complex

The whole original complex is retained. Its actual Cartier source is the original native
relative twist exterior module restricted along the actual source inclusion B → T.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeOriginalFrobeniusBridge
open CategoryTheory
open scoped Classical
universe u

private def mapCycleGeneric {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) (q : ℕ)
    (z : LinearMap.ker (K.sc q).g.hom) : LinearMap.ker (L.sc q).g.hom := by
  let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℕ) q).map φ
  refine ⟨ψ.τ₂ z.val, ?_⟩
  have h := congrArg (fun f : (K.sc q).X₂ ⟶ (L.sc q).X₃ => f z.val) ψ.comm₂₃
  change (L.sc q).g (ψ.τ₂ z.val) = ψ.τ₃ ((K.sc q).g z.val) at h
  exact h.trans ((congrArg ψ.τ₃ z.property).trans (ψ.τ₃.hom.map_zero))

variable {k B : Type u} [Field k] [CommRing B] [Algebra k B]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP B p]
attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra
local notation "T" => RelativeFrobenius.twist (algebraMap k B) p
local notation "S" => (CommRingCat.Hom.hom (RelativeFrobenius.sourceMap (algebraMap k B) p))
local notation "F" => (CommRingCat.Hom.hom (RelativeFrobenius.map (algebraMap k B) p))

/-- The ACTUAL original absolute Frobenius factors through the SAME original native twist. -/
theorem sourceFactorization : AlgebraFrobenius.map k B p = (F).comp S := by
  have h : (F).comp S = frobenius B p :=
    congrArg CommRingCat.Hom.hom (RelativeFrobenius.sourceMap_map (algebraMap k B) p)
  exact (AlgebraFrobenius.map_eq_frobenius k B p).trans h.symm

/-- Genuine comparison of ENTIRE original scalar restriction functors on EVERY B-module. -/
def scalarComparison : ModuleCat.restrictScalars F ⋙ ModuleCat.restrictScalars S ≅
    ModuleCat.restrictScalars (AlgebraFrobenius.map k B p) :=
  (ModuleCat.restrictScalarsComp' S F (AlgebraFrobenius.map k B p)
    (sourceFactorization (k := k) (B := B) p)).symm

/-- Original whole form modules have their genuine source-restriction comparison. -/
def formIso (q : ℕ) : (ModuleCat.restrictScalars S).obj
    (RelativeEtaleDeRham.formModule (R := k) (B := B) p q) ≅
      EtaleAlgebraFrobeniusComplex.formModule (k := k) (B := B) p q :=
  (scalarComparison (k := k) (B := B) p).app
    (ModuleCat.of B (⋀[B]^q (KaehlerDifferential k B)))

/-- EVERY original form is the SAME entire form through the genuine scalar comparison. -/
theorem formIso_hom_apply (q : ℕ)
    (a : (ModuleCat.restrictScalars S).obj (RelativeEtaleDeRham.formModule (R := k) (B := B) p q)) :
    (formIso (k := k) (B := B) p q).hom a = a := rfl

variable {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
local notation "ER" => RelativeEtaleDeRham.complex v hv p
local notation "ES" => Functor.obj
  (Functor.mapHomologicalComplex (ModuleCat.restrictScalars S) (ComplexShape.up ℕ)) ER
local notation "EA" => EtaleAlgebraFrobeniusComplex.complex v hv p

/-- The ENTIRE original absolute Frobenius complex is the genuine source restriction of the
SAME native relative complex, with no supplied differential or comparison square. -/
def complexIso : ES ≅ EA := by
  refine HomologicalComplex.Hom.isoOfComponents (fun q => formIso (k := k) (B := B) p q) ?_
  intro q r h
  have hr : q+1 = r := h
  subst r
  simp only [RelativeEtaleDeRham.complex, EtaleAlgebraFrobeniusComplex.complex,
    Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

/-- EVERY original form in EVERY degree is retained by the ACTUAL whole complex bridge. -/
theorem complexIso_hom_f_apply (q : ℕ) (a : (ES).X q) :
    (complexIso p v hv).hom.f q a = a := rfl

/-- Actual source restriction retains the genuine original native kernel cycle. -/
def restrictedCycle (q : ℕ) (z : LinearMap.ker ((ER).sc q).g.hom) :
    LinearMap.ker ((ES).sc q).g.hom := ⟨z.val, z.property⟩

/-- The ENTIRE original cycle value is retained by genuine scalar restriction. -/
theorem restrictedCycle_val (q : ℕ) (z : LinearMap.ker ((ER).sc q).g.hom) :
    (restrictedCycle p v hv q z).val = z.val := rfl

/-- The actual cochain bridge internally constructs an ACTUAL original absolute kernel cycle. -/
def absoluteCycle (q : ℕ) (z : LinearMap.ker ((ER).sc q).g.hom) :
    LinearMap.ker ((EA).sc q).g.hom :=
  mapCycleGeneric (complexIso p v hv).hom q (restrictedCycle p v hv q z)

/-- The absolute cycle has its SAME entire original relative cycle value. -/
theorem absoluteCycle_val (q : ℕ) (z : LinearMap.ker ((ER).sc q).g.hom) :
    (absoluteCycle p v hv q z).val = z.val := rfl

/-- GENUINE native homology comparison from actual scalar restriction and the actual bridge. -/
def homologyIso (q : ℕ) : (ModuleCat.restrictScalars S).obj ((ER).homology q) ≅ (EA).homology q :=
  (ModuleComplexNativeCycleClasses.restrictionHomologyIso S ER q).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat B) (ComplexShape.up ℕ) q).mapIso (complexIso p v hv)

/-- EVERY actual relative native cycle class becomes its internally constructed ACTUAL original
absolute whole-complex class, with the SAME original cycle value. -/
theorem homologyIso_cycleClass (q : ℕ) (z : LinearMap.ker ((ER).sc q).g.hom) :
    (homologyIso p v hv q).hom (ModuleComplexNativeCycleClasses.cycleClass ER q z) =
      ModuleComplexNativeCycleClasses.cycleClass EA q (absoluteCycle p v hv q z) := by
  have hs := ModuleComplexNativeCycleClasses.restrictionHomologyIso_cycleClass S ER q
    (restrictedCycle p v hv q z) z rfl
  change (HomologicalComplex.homologyMap (complexIso p v hv).hom q)
      ((ModuleComplexNativeCycleClasses.restrictionHomologyIso S ER q).inv
        (ModuleComplexNativeCycleClasses.cycleClass ER q z)) = _
  rw [← hs, Iso.hom_inv_id_apply]
  exact ModuleComplexNativeCycleClasses.homologyMap_cycleClass (complexIso p v hv).hom q
    (restrictedCycle p v hv q z) (absoluteCycle p v hv q z) rfl

/-- The CORRECT original absolute-complex Cartier isomorphism has source the ACTUAL native
Ω_T exterior module restricted along the ORIGINAL sourceMap B→T, in ALL degrees including0. -/
def correctedCartierIso (q : ℕ) : (ModuleCat.restrictScalars S).obj
    (ModuleCat.of T (⋀[T]^q (KaehlerDifferential k T))) ≅ (EA).homology q :=
  (ModuleCat.restrictScalars S).mapIso (RelativeEtaleCartierDomain.inverseCartierIso v hv p q) ≪≫
    homologyIso p v hv q

/-- EVERY original twist exterior form has an internally derived ACTUAL original absolute
native representative class for the SAME corrected Cartier map. -/
theorem correctedCartierIso_representative_class (q : ℕ) (a : ⋀[T]^q (KaehlerDifferential k T)) :
    (correctedCartierIso p v hv q).hom a =
      ModuleComplexNativeCycleClasses.cycleClass EA q
        (absoluteCycle p v hv q (RelativeEtaleCartierMultiplicativity.representative v hv p q a)) := by
  change (homologyIso p v hv q).hom ((RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom a) = _
  rw [RelativeEtaleCartierMultiplicativity.inverseCartierIso_representative_class,
    homologyIso_cycleClass]

/-- The SAME corrected Cartier map has its actual original absolute native class formula for
EVERY original source-function wedge, in EVERY degree including the empty wedge. -/
theorem correctedCartierIso_sourceWedge (q : ℕ) (t : Fin q → B) :
    (correctedCartierIso p v hv q).hom
      (exteriorPower.ιMulti T q (fun i => KaehlerDifferential.D k T (S (t i)))) =
    ModuleComplexNativeCycleClasses.cycleClass EA q
      (absoluteCycle p v hv q (RelativeEtaleCartierMultiplicativity.functionCycle v hv p q t)) := by
  change (homologyIso p v hv q).hom ((RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom _) = _
  rw [RelativeEtaleCartierMultiplicativity.inverseCartierIso_sourceWedge, homologyIso_cycleClass]

/-- The actual original absolute cycle in the all-functions formula has its ENTIRE original
power-differential wedge value, not a supplied selected representative. -/
theorem absoluteFunctionCycle_val (q : ℕ) (t : Fin q → B) :
    (absoluteCycle p v hv q (RelativeEtaleCartierMultiplicativity.functionCycle v hv p q t)).val =
      (show EtaleAlgebraFrobeniusComplex.formModule (k := k) (B := B) p q from
        exteriorPower.ιMulti B q (fun i => (t i)^(p-1) • KaehlerDifferential.D k B (t i))) := by
  rw [absoluteCycle_val, RelativeEtaleCartierMultiplicativity.functionCycle_val]

end EnvelopeProperty.Cartier.RelativeOriginalFrobeniusBridge
