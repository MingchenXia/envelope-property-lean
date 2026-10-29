import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleComplexBaseChange
import EnvelopeProperty.Algebra.FlatModuleHomologyCycleClasses
import EnvelopeProperty.Algebra.ModuleComplexNativeCycleClasses

/-! # Every actual native class under genuine relative etale homology transport

Cycles are produced from the SAME actual extended differential and actual chain
isomorphism. The native homology exchange retains the original entire cycle class.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeEtaleNativeClasses
open CategoryTheory Limits
open scoped TensorProduct ChangeOfRings
universe u

private def extendedCycleGeneric {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (K : CochainComplex (ModuleCat.{u} A) ℕ) (q : ℕ) (b : B)
    (z : LinearMap.ker (K.sc q).g.hom) :
    LinearMap.ker ((((ModuleCat.extendScalars f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).sc q).g.hom :=
  ⟨b ⊗ₜ[A,f] z.val, by
    change (ModuleCat.extendScalars f).map (K.sc q).g (b ⊗ₜ[A,f] z.val) = 0
    have hz : (b ⊗ₜ[A,f] (0 : (K.sc q).X₃) :
        (ModuleCat.extendScalars f).obj (K.sc q).X₃) = 0 := by
      let : Module A B := Module.compHom B f
      exact TensorProduct.tmul_zero _ _
    exact (ModuleCat.ExtendScalars.map_tmul f (K.sc q).g b z.val).trans
      ((congrArg (fun m : (K.sc q).X₃ => b ⊗ₜ[A,f] m) z.property).trans hz)⟩

private def mapCycleGeneric {A : Type u} [CommRing A]
    {K L : CochainComplex (ModuleCat.{u} A) ℕ} (φ : K ⟶ L) (q : ℕ)
    (z : LinearMap.ker (K.sc q).g.hom) : LinearMap.ker (L.sc q).g.hom := by
  let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat A) (ComplexShape.up ℕ) q).map φ
  refine ⟨ψ.τ₂ z.val, ?_⟩
  have h := congrArg (fun a : (K.sc q).X₂ ⟶ (L.sc q).X₃ => a z.val) ψ.comm₂₃
  change (L.sc q).g (ψ.τ₂ z.val) = ψ.τ₃ ((K.sc q).g z.val) at h
  exact h.trans ((congrArg ψ.τ₃ z.property).trans (ψ.τ₃.hom.map_zero))

private def flatIsoGeneric {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (K : CochainComplex (ModuleCat.{u} A) ℕ) (q : ℕ) :
    (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology q ≅
      (ModuleCat.extendScalars f).obj (K.homology q) := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u} f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact (K.sc q).mapHomologyIso (ModuleCat.extendScalars f)

private theorem flatIsoGeneric_cycleClass {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (K : CochainComplex (ModuleCat.{u} A) ℕ) (q : ℕ) (b : B)
    (z : LinearMap.ker (K.sc q).g.hom) :
    (flatIsoGeneric f hf K q).hom
      (ModuleComplexNativeCycleClasses.cycleClass
        (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) q
        (extendedCycleGeneric f K q b z)) =
      b ⊗ₜ[A,f] ModuleComplexNativeCycleClasses.cycleClass K q z :=
  FlatModuleHomologyCycleClasses.cycleClass_tmul f hf (K.sc q)
    (extendedCycleGeneric f K q b z) b z rfl

private theorem transport_cycleClass_apply {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (K : CochainComplex (ModuleCat.{u} A) ℕ)
    (L : CochainComplex (ModuleCat.{u} B) ℕ)
    (e : ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ≅ L)
    (q : ℕ) (b : B) (z : LinearMap.ker (K.sc q).g.hom) :
    (flatIsoGeneric f hf K q).hom
      (((HomologicalComplex.homologyFunctor (ModuleCat B) (ComplexShape.up ℕ) q).mapIso e).inv
        (ModuleComplexNativeCycleClasses.cycleClass L q
          (mapCycleGeneric e.hom q (extendedCycleGeneric f K q b z)))) =
      b ⊗ₜ[A,f] ModuleComplexNativeCycleClasses.cycleClass K q z := by
  let eh := (HomologicalComplex.homologyFunctor (ModuleCat B) (ComplexShape.up ℕ) q).mapIso e
  let ze := extendedCycleGeneric f K q b z
  have hm := ModuleComplexNativeCycleClasses.homologyMap_cycleClass e.hom q ze
    (mapCycleGeneric e.hom q ze) rfl
  change eh.hom (ModuleComplexNativeCycleClasses.cycleClass _ q ze) =
    ModuleComplexNativeCycleClasses.cycleClass L q (mapCycleGeneric e.hom q ze) at hm
  have hi : eh.inv (ModuleComplexNativeCycleClasses.cycleClass L q (mapCycleGeneric e.hom q ze)) =
      ModuleComplexNativeCycleClasses.cycleClass _ q ze :=
    (congrArg eh.inv hm.symm).trans (Iso.hom_inv_id_apply eh _)
  exact (congrArg (flatIsoGeneric f hf K q).hom hi).trans
    (flatIsoGeneric_cycleClass f hf K q b z)

private theorem iso_inv_value {A : Type u} [CommRing A] {M N : ModuleCat.{u} A}
    (e : M ≅ N) (x : M) (y : N) (h : e.hom x = y) : e.inv y = x :=
  (congrArg e.inv h.symm).trans (Iso.hom_inv_id_apply e x)

variable {k B : Type u} [Field k] [CommRing B] [Algebra k B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP B p]
local notation "P" => MvPolynomial (Fin n) k
local notation "TP" => RelativeFrobenius.twist (algebraMap k P) p
local notation "TB" => RelativeFrobenius.twist (algebraMap k B) p
local notation "KP" => RelativeEtaleDeRham.complex (MvPolynomial.X : Fin n → P)
  (RelativePolynomialCartier.polynomialEtale k n) p
local notation "KB" => RelativeEtaleDeRham.complex v hv p

/-- Every original native polynomial cycle gives an actual native scalar-extended cycle. -/
def extendedCycle (q : ℕ) (t : TB) (z : LinearMap.ker ((KP).sc q).g.hom) :
    LinearMap.ker ((RelativeEtaleComplexBaseChange.extendedComplex (k := k) v p).sc q).g.hom :=
  extendedCycleGeneric (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom KP q t z

omit [CharP B p] in
/-- The actual native extended cycle has precisely the SAME original pure-tensor value. -/
theorem extendedCycle_val (q : ℕ) (t : TB) (z : LinearMap.ker ((KP).sc q).g.hom) :
    let _ := (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
    (extendedCycle (k := k) v p q t z).val = t ⊗ₜ[TP] z.val := rfl

/-- The actual whole-complex isomorphism produces the SAME original native etale cycle. -/
def etaleCycle (q : ℕ) (t : TB) (z : LinearMap.ker ((KP).sc q).g.hom) :
    LinearMap.ker ((KB).sc q).g.hom :=
  mapCycleGeneric (RelativeEtaleComplexBaseChange.complexIso v hv p).hom q
    (extendedCycle (k := k) v p q t z)

/-- Every native etale image cycle has its SAME original pulled form and actual relative coefficient. -/
theorem etaleCycle_val (q : ℕ) (t : TB) (z : LinearMap.ker ((KP).sc q).g.hom) :
    (etaleCycle v hv p q t z).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := B) p q from
        (RelativeFrobenius.map (algebraMap k B) p).hom t •
          EtaleDeRham.polynomialFormMap v hv q z.val) := by
  change (RelativeEtaleComplexBaseChange.formIso v hv p q).hom
    (t ⊗ₜ[TP,(RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom] z.val) = _
  exact RelativeEtaleComplexBaseChange.formIso_tmul v hv p q t z.val

/-- Coefficient-one native cycle images retain the SAME entire original pulled form. -/
theorem etaleCycle_one_val (q : ℕ) (z : LinearMap.ker ((KP).sc q).g.hom) :
    (etaleCycle v hv p q (1 : TB) z).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := B) p q from
        EtaleDeRham.polynomialFormMap v hv q z.val) := by
  simpa only [map_one, one_smul] using etaleCycle_val v hv p q (1 : TB) z

/-- Every original coefficient gives its SAME original scalar on the actual native cycle. -/
theorem etaleCycle_coefficient_val (q : ℕ) (a : k) (z : LinearMap.ker ((KP).sc q).g.hom) :
    (etaleCycle v hv p q ((RelativeFrobenius.coefficientMap (algebraMap k B) p).hom a) z).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := B) p q from
        (algebraMap k B a) • EtaleDeRham.polynomialFormMap v hv q z.val) := by
  have h := congrArg (fun h : CommRingCat.of k ⟶ CommRingCat.of B => h.hom a)
    (RelativeFrobenius.coefficientMap_map (algebraMap k B) p)
  exact (etaleCycle_val v hv p q _ z).trans
    (congrArg (fun b : B => (show RelativeEtaleDeRham.formModule (R := k) (B := B) p q from
      b • EtaleDeRham.polynomialFormMap v hv q z.val)) h)

/-- The SAME actual native homology exchange preserves EVERY original cycle class. -/
theorem homologyIso_cycleClass (q : ℕ) (t : TB) (z : LinearMap.ker ((KP).sc q).g.hom) :
    let _ := (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
    (RelativeEtaleComplexBaseChange.homologyIso v hv p q).hom
      (ModuleComplexNativeCycleClasses.cycleClass KB q (etaleCycle v hv p q t z)) =
      t ⊗ₜ[TP] ModuleComplexNativeCycleClasses.cycleClass KP q z :=
  transport_cycleClass_apply (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp
      (RelativeEtaleComplexBaseChange.chartTwistMap_etale v hv p)).1 KP KB
    (RelativeEtaleComplexBaseChange.complexIso v hv p) q t z

/-- Every original tensor of a native class maps inversely to its SAME actual etale cycle class. -/
theorem homologyIso_inv_tmul_cycleClass (q : ℕ) (t : TB)
    (z : LinearMap.ker ((KP).sc q).g.hom) :
    let _ := (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
    (RelativeEtaleComplexBaseChange.homologyIso v hv p q).inv
      (t ⊗ₜ[TP] ModuleComplexNativeCycleClasses.cycleClass KP q z) =
      ModuleComplexNativeCycleClasses.cycleClass KB q (etaleCycle v hv p q t z) :=
  iso_inv_value (RelativeEtaleComplexBaseChange.homologyIso v hv p q) _ _
    (homologyIso_cycleClass v hv p q t z)

/-- The ORIGINAL actual whole-complex cycle-class map is genuinely native T_B-linear. -/
def nativeCycleClassLinear (q : ℕ) : LinearMap.ker ((KB).sc q).g.hom →ₗ[TB] (KB).homology q :=
  ((KB).homologyπ q).hom.comp (((KB).sc q).moduleCatCyclesIso.inv.hom)

/-- Every actual native cycle retains the SAME original native class. -/
theorem nativeCycleClassLinear_apply (q : ℕ) (z : LinearMap.ker ((KB).sc q).g.hom) :
    nativeCycleClassLinear v hv p q z = ModuleComplexNativeCycleClasses.cycleClass KB q z := rfl

/-- Every actual incoming boundary in the SAME original whole complex has zero native class. -/
theorem nativeCycleClassLinear_boundary (q : ℕ) (w : ((KB).sc q).X₁) :
    nativeCycleClassLinear v hv p q (((KB).sc q).moduleCatToCycles w) = 0 := by
  let S := (KB).sc q
  have h := S.moduleCatCyclesIso_inv_π_apply (S.moduleCatToCycles w)
  have hz : (Submodule.Quotient.mk (S.moduleCatToCycles w) :
      LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ w)
  exact h.trans ((congrArg S.moduleCatHomologyIso.inv hz).trans (S.moduleCatHomologyIso.inv.hom.map_zero))

end EnvelopeProperty.Cartier.RelativeEtaleNativeClasses
