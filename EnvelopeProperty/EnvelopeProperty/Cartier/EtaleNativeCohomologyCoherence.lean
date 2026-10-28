import EnvelopeProperty.Cartier.EtaleCartierCoefficientNaturality
import EnvelopeProperty.Algebra.ModuleComplexNativeCycleClasses

/-! # The genuine original quotient comparisons coincide with native homology functors -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleNativeCohomologyCoherence
open CategoryTheory Limits
universe u
private def nativeClass {A : Type u} [CommRing A] (S : ShortComplex (ModuleCat A))
    (z : LinearMap.ker S.g.hom) : S.homology :=
  S.homologyπ (S.moduleCatCyclesIso.inv z)

private theorem actualClass_map {A : Type u} [CommRing A]
    {S T : ShortComplex (ModuleCat A)} (φ : S ⟶ T)
    (z : LinearMap.ker S.g.hom) (w : LinearMap.ker T.g.hom)
    (hzw : φ.τ₂ z.val = w.val) :
    ShortComplex.homologyMap φ (nativeClass S z) = nativeClass T w := by
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
  change ShortComplex.homologyMap φ (nativeClass S z) =
    T.homologyπ (ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv z)) at h
  exact h.trans (congrArg T.homologyπ hc)

private theorem composedClass_map {A : Type u} [CommRing A]
    {S T U : ShortComplex (ModuleCat A)} (e : S ≅ T) (e' : T ≅ U)
    (z : LinearMap.ker S.g.hom) (w : LinearMap.ker U.g.hom)
    (hzw : (e.hom ≫ e'.hom).τ₂ z.val = w.val) :
    (ShortComplex.homologyMapIso e ≪≫ ShortComplex.homologyMapIso e').hom.hom
      (nativeClass S z) = nativeClass U w := by
  have hc := actualClass_map (e.hom ≫ e'.hom) z w hzw
  have hm := congrArg (fun F : S.homology ⟶ U.homology => F (nativeClass S z))
    (ShortComplex.homologyMap_comp e.hom e'.hom)
  exact hm.symm.trans hc

private def ofPositiveShortIso {C : Type*} [Category C] [HasZeroMorphisms C]
    (X : ℕ → C) (d : ∀ q, X q ⟶ X (q+1)) (sq : ∀ q, d q ≫ d (q+1) = 0) (q : ℕ) :
    (CochainComplex.of X d sq).sc' q (q+1) (q+1+1) ≅
      ShortComplex.mk (d q) (d (q+1)) (sq q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, CochainComplex.of_d])
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, CochainComplex.of_d])

private def ofZeroShortIso {C : Type*} [Category C] [HasZeroMorphisms C]
    (X : ℕ → C) (d : ∀ q, X q ⟶ X (q+1)) (sq : ∀ q, d q ≫ d (q+1) = 0) :
    (CochainComplex.of X d sq).sc' 0 0 1 ≅
      ShortComplex.mk (0 : X 0 ⟶ X 0) (d 0) zero_comp :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
        CochainComplex.of_d_ne _ _ (by decide : 0+1 ≠ (0:ℕ))])
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      change (𝟙 (X 0)) ≫ d 0 = CochainComplex.of.d X d 0 (0+1) ≫ 𝟙 (X (0+1))
      rw [Category.id_comp, Category.comp_id, CochainComplex.of_d])

private theorem rowClass_quotient {A : Type u} [CommRing A]
    (S : ShortComplex (ModuleCat A)) (N : Submodule A (LinearMap.ker S.g.hom))
    (h : LinearMap.range S.moduleCatToCycles = N) (z : LinearMap.ker S.g.hom) :
    (S.moduleCatHomologyIso ≪≫ (Submodule.quotEquivOfEq _ _ h).toModuleIso).hom.hom
      (nativeClass S z) = Submodule.Quotient.mk z := by
  have hn : nativeClass S z = S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z) :=
    S.moduleCatCyclesIso_inv_π_apply z
  rw [hn]
  change (Submodule.quotEquivOfEq _ _ h)
    (S.moduleCatHomologyIso.hom.hom (S.moduleCatHomologyIso.inv.hom
      (Submodule.Quotient.mk z))) = _
  exact (congrArg (Submodule.quotEquivOfEq _ _ h)
    (Iso.inv_hom_id_apply S.moduleCatHomologyIso (Submodule.Quotient.mk z))).trans rfl

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {n : ℕ} (v : Fin n → A) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP A p]

private theorem differential_square (q : ℕ) :
    EtaleDeRham.frobeniusDifferential v hv p q ≫
      EtaleDeRham.frobeniusDifferential v hv p (q+1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact EtaleDeRham.differential_square v hv q a

/-- EVERY actual original quotient cycle is the SAME genuine native whole-complex cycle. -/
def nativeCycle (q : ℕ) (z : EtaleCohomologyProducts.cycles v hv p q) :
    LinearMap.ker ((EtaleDeRham.frobeniusComplex v hv p).sc q).g.hom :=
  ModuleComplexNativeCycleClasses.ofCycle
    (fun q => EtaleDeRham.frobeniusModule (R := R) (B := A) p q)
    (EtaleDeRham.frobeniusDifferential v hv p) (differential_square v hv p) q z

/-- The ACTUAL original cohomologyIso takes EVERY native whole-complex cycle class to its
SAME original quotient class; both positive and zero incoming rows are retained. -/
theorem cohomologyIso_cycleClass (q : ℕ) (z : EtaleCohomologyProducts.cycles v hv p q) :
    (EtaleCohomologyProducts.cohomologyIso v hv p q).hom.hom
      (ModuleComplexNativeCycleClasses.cycleClass (EtaleDeRham.frobeniusComplex v hv p) q
        (nativeCycle v hv p q z)) = Submodule.Quotient.mk z := by
  let X := fun q => EtaleDeRham.frobeniusModule (R := R) (B := A) p q
  let d := EtaleDeRham.frobeniusDifferential v hv p
  let sq := differential_square v hv p
  let K := CochainComplex.of X d sq
  cases q with
  | zero =>
    let S := EtaleCohomologyProducts.zeroShortComplex v hv p
    have h := composedClass_map
      (K.isoSc' 0 0 1 CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0))
      (ofZeroShortIso X d sq) (nativeCycle v hv p 0 z) z rfl
    have hr : LinearMap.range S.moduleCatToCycles = ⊥ := by
      apply LinearMap.range_eq_bot.mpr
      apply LinearMap.ext
      intro a
      apply Subtype.ext
      rfl
    exact (congrArg (EtaleCohomologyProducts.zeroShortHomologyIso v hv p).hom.hom h).trans
      (rowClass_quotient S ⊥ hr z)
  | succ q =>
    let S := EtaleCohomologyProducts.positiveShortComplex v hv p q
    have h := composedClass_map
      (K.isoSc' q (q+1) (q+1+1) (CochainComplex.prev_nat_succ q) (CochainComplex.next ℕ (q+1)))
      (ofPositiveShortIso X d sq q) (nativeCycle v hv p (q+1) z) z rfl
    have hn : nativeClass S z = S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z) :=
      S.moduleCatCyclesIso_inv_π_apply z
    have he := congrArg S.moduleCatHomologyIso.hom.hom hn
    exact (congrArg S.moduleCatHomologyIso.hom.hom h).trans
      (he.trans (Iso.inv_hom_id_apply S.moduleCatHomologyIso _))

/-- The pre-existing original native cycle-class map is EXACTLY the class obtained by
native whole-complex cycle inclusion and homology projection, on EVERY original cycle. -/
theorem nativeCycleClass_eq (q : ℕ) (z : EtaleCohomologyProducts.cycles v hv p q) :
    EtaleCohomologyProducts.nativeCycleClass v hv p q z =
      ModuleComplexNativeCycleClasses.cycleClass (EtaleDeRham.frobeniusComplex v hv p) q
        (nativeCycle v hv p q z) := by
  apply (ModuleCat.mono_iff_injective (EtaleCohomologyProducts.cohomologyIso v hv p q).hom).mp
    inferInstance
  exact (Iso.inv_hom_id_apply (EtaleCohomologyProducts.cohomologyIso v hv p q)
    (Submodule.Quotient.mk z)).trans (cohomologyIso_cycleClass v hv p q z).symm

variable {B : Type u} [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
variable {m : ℕ} (w : Fin m → B) (hw : (MvPolynomial.aeval (R := R) w).toRingHom.Etale)
variable [CharP B p]

/-- The ACTUAL native homology-functor map of the SAME original complex morphism, followed
by genuine native scalar-restriction preservation. It is not defined through a quotient map. -/
def nativeFunctorHomologyMap (q : ℕ) : (EtaleDeRham.frobeniusComplex v hv p).homology q ⟶
    (ModuleCat.restrictScalars (algebraMap A B)).obj
      ((EtaleDeRham.frobeniusComplex w hw p).homology q) :=
  HomologicalComplex.homologyMap (EtaleDifferentialNaturality.frobeniusComplexMap v hv w hw p) q ≫
    (ModuleComplexNativeCycleClasses.restrictionHomologyIso (algebraMap A B)
      (EtaleDeRham.frobeniusComplex w hw p) q).hom

/-- The ACTUAL native functor retains EVERY SAME original entire cycle class. -/
theorem nativeFunctorHomologyMap_cycleClass (q : ℕ)
    (z : EtaleCohomologyProducts.cycles v hv p q) :
    (nativeFunctorHomologyMap v hv p w hw q).hom
      (EtaleCohomologyProducts.nativeCycleClass v hv p q z) =
    EtaleCohomologyProducts.nativeCycleClass w hw p q
      ((EtaleCohomologyCoefficientMaps.cycleMap v hv w hw p q).hom z) := by
  let F := ModuleCat.restrictScalars (algebraMap A B)
  let K := EtaleDeRham.frobeniusComplex w hw p
  let z' := nativeCycle w hw p q ((EtaleCohomologyCoefficientMaps.cycleMap v hv w hw p q).hom z)
  let t : LinearMap.ker (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc q).g.hom :=
    ⟨z'.val, z'.property⟩
  have h := ModuleComplexNativeCycleClasses.homologyMap_cycleClass
    (EtaleDifferentialNaturality.frobeniusComplexMap v hv w hw p) q
    (nativeCycle v hv p q z) t rfl
  have hr := ModuleComplexNativeCycleClasses.restrictionHomologyIso_cycleClass
    (algebraMap A B) K q t z' rfl
  have h0 := congrArg (nativeFunctorHomologyMap v hv p w hw q).hom
    (nativeCycleClass_eq v hv p q z)
  have h1 := congrArg (ModuleComplexNativeCycleClasses.restrictionHomologyIso
    (algebraMap A B) K q).hom.hom h
  exact h0.trans (h1.trans (hr.trans (nativeCycleClass_eq w hw p q
    ((EtaleCohomologyCoefficientMaps.cycleMap v hv w hw p q).hom z)).symm))

/-- The ENTIRE original quotient-sandwich map is the ACTUAL native homology-functor map,
with its genuine native scalar comparison, not just an unrelated class-preserving morphism. -/
theorem nativeFunctorHomologyMap_eq (q : ℕ) :
    nativeFunctorHomologyMap v hv p w hw q =
      EtaleCohomologyCoefficientMaps.nativeHomologyMap v hv w hw p q := by
  apply (cancel_epi (EtaleCohomologyProducts.cohomologyIso v hv p q).inv).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  induction c using Submodule.Quotient.induction_on with
  | _ z =>
    exact (nativeFunctorHomologyMap_cycleClass v hv p w hw q z).trans
      (EtaleCohomologyCoefficientMaps.nativeHomologyMap_cycleClass v hv w hw p q z).symm

/-- The SAME pre-existing canonical inverse Cartier maps commute with the ACTUAL native
homology functor in EVERY degree and on EVERY original form, without a comparison premise. -/
theorem inverseCartier_nativeFunctor_naturality (q : ℕ) :
    ModuleCat.ofHom (EtaleCartierCycleRepresentatives.inverseCartier v hv p q) ≫
      nativeFunctorHomologyMap v hv p w hw q =
    EtaleCartierCoefficientNaturality.formMap (R := R) (A := A) (B := B) q ≫
      (ModuleCat.restrictScalars (algebraMap A B)).map
        (ModuleCat.ofHom (EtaleCartierCycleRepresentatives.inverseCartier w hw p q)) :=
  (congrArg (fun F => ModuleCat.ofHom (EtaleCartierCycleRepresentatives.inverseCartier v hv p q) ≫ F)
    (nativeFunctorHomologyMap_eq v hv p w hw q)).trans
      (EtaleCartierCoefficientNaturality.inverseCartier_naturality v hv w hw p q)

end EnvelopeProperty.Cartier.EtaleNativeCohomologyCoherence
