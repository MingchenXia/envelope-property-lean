import EnvelopeProperty.Cartier.EtaleCartierCycleRepresentatives
import EnvelopeProperty.Algebra.ModuleComplexNativeCycleClasses

/-! # SAME original etale Cartier representatives as actual whole native homology classes -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleNativeCycleClass
open CategoryTheory
universe u
private def rowClass {A : Type u} [CommRing A] (S : ShortComplex (ModuleCat A))
    (z : LinearMap.ker S.g.hom) : S.homology :=
  S.homologyπ (S.moduleCatCyclesIso.inv z)

private theorem rowClass_map {A : Type u} [CommRing A]
    {S T : ShortComplex (ModuleCat A)} (φ : S ⟶ T)
    (z : LinearMap.ker S.g.hom) (w : LinearMap.ker T.g.hom)
    (hzw : φ.τ₂ z.val = w.val) :
    (ShortComplex.homologyMap φ).hom (rowClass S z) = rowClass T w := by
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
  change (ShortComplex.homologyMap φ).hom (rowClass S z) =
    T.homologyπ (ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv z)) at h
  exact h.trans (congrArg T.homologyπ hc)

private theorem wholeRow_class {A : Type u} [CommRing A]
    (K : CochainComplex (ModuleCat A) ℕ) (i j l : ℕ)
    (hi : (ComplexShape.up ℕ).prev j = i) (hl : (ComplexShape.up ℕ).next j = l)
    (z : LinearMap.ker (K.sc j).g.hom) (w : LinearMap.ker (K.sc' i j l).g.hom)
    (hzw : z.val = w.val) :
    (K.homologyIsoSc' i j l hi hl).hom.hom
      (ModuleComplexNativeCycleClasses.cycleClass K j z) = rowClass (K.sc' i j l) w := by
  apply rowClass_map (K.isoSc' i j l hi hl).hom z w
  change z.val = w.val
  exact hzw

private theorem rowClass_eq_quotient {A : Type u} [CommRing A]
    (S : ShortComplex (ModuleCat A)) (z : LinearMap.ker S.g.hom) :
    rowClass S z = S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z) :=
  S.moduleCatCyclesIso_inv_π_apply z

private theorem composite_class {A : Type u} [CommRing A]
    {H M : ModuleCat A} {S T : ShortComplex (ModuleCat A)}
    (a : H ≅ S.homology) (e : S ≅ T) (c : T.homology ≅ M) (x : H) (v : M)
    (z : LinearMap.ker S.g.hom) (w : LinearMap.ker T.g.hom)
    (hx : a.hom.hom x = rowClass S z) (hzw : e.hom.τ₂ z.val = w.val)
    (hw : c.hom.hom (rowClass T w) = v) :
    (a ≪≫ ShortComplex.homologyMapIso e ≪≫ c).hom.hom x = v := by
  have hfirst := congrArg (fun y : S.homology =>
    c.hom.hom ((ShortComplex.homologyMapIso e).hom.hom y)) hx
  have hsecond := congrArg c.hom.hom (rowClass_map e.hom z w hzw)
  exact hfirst.trans (hsecond.trans hw)

private theorem rowClass_to_quotient {A : Type u} [CommRing A]
    (S : ShortComplex (ModuleCat A)) (z : LinearMap.ker S.g.hom) :
    S.moduleCatHomologyIso.hom.hom (rowClass S z) = Submodule.Quotient.mk z := by
  have h := congrArg S.moduleCatHomologyIso.hom.hom (rowClass_eq_quotient S z)
  exact h.trans (Iso.inv_hom_id_apply S.moduleCatHomologyIso _)

private theorem rowClass_to_quotientOfEq {A : Type u} [CommRing A]
    (S : ShortComplex (ModuleCat A)) (N : Submodule A (LinearMap.ker S.g.hom))
    (h : LinearMap.range S.moduleCatToCycles = N) (z : LinearMap.ker S.g.hom) :
    (S.moduleCatHomologyIso ≪≫ (Submodule.quotEquivOfEq _ _ h).toModuleIso).hom.hom
      (rowClass S z) = Submodule.Quotient.mk z := by
  change (Submodule.quotEquivOfEq _ _ h) (S.moduleCatHomologyIso.hom.hom (rowClass S z)) = _
  exact (congrArg (Submodule.quotEquivOfEq _ _ h) (rowClass_to_quotient S z)).trans rfl

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A] {n : ℕ}
variable (v : Fin n → A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP A p]
local notation "W" => KaehlerDifferential k A
local notation "L" => EtaleDeRham.frobeniusComplex v hv p

private theorem old_square (q : ℕ) :
    EtaleDeRham.frobeniusDifferential v hv p q ≫
      EtaleDeRham.frobeniusDifferential v hv p (q+1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact EtaleDeRham.differential_square v hv q

def nativeCycle (q : ℕ) (z : EtaleCohomologyProducts.cycles v hv p q) :
    LinearMap.ker ((L).sc q).g.hom :=
  ModuleComplexNativeCycleClasses.ofCycle (EtaleDeRham.frobeniusModule (R := k) (B := A) p)
    (EtaleDeRham.frobeniusDifferential v hv p) (old_square v hv p) q z

/-- The actual whole native cycle retains EVERY original underlying form. -/
theorem nativeCycle_value (q : ℕ) (z : EtaleCohomologyProducts.cycles v hv p q) :
    (nativeCycle v hv p q z).val = z.val := rfl

private def specifiedCycle (i q : ℕ) (z : EtaleCohomologyProducts.cycles v hv p q) :
    LinearMap.ker ((L).sc' i q (q+1)).g.hom :=
  ⟨z.val, by
    change (L).d q (q+1) z.val = 0
    rw [show (L).d q (q+1) = EtaleDeRham.frobeniusDifferential v hv p q from
      CochainComplex.of_d _ _ q]
    exact z.property⟩

private theorem zeroRow_class (z : EtaleCohomologyProducts.cycles v hv p 0) :
    (EtaleCohomologyProducts.zeroShortHomologyIso v hv p).hom.hom
      (rowClass (EtaleCohomologyProducts.zeroShortComplex v hv p) z) =
        Submodule.Quotient.mk z := by
  have hz : LinearMap.range (EtaleCohomologyProducts.zeroShortComplex v hv p).moduleCatToCycles = ⊥ := by
    apply LinearMap.range_eq_bot.mpr
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    rfl
  unfold EtaleCohomologyProducts.zeroShortHomologyIso
  exact rowClass_to_quotientOfEq (EtaleCohomologyProducts.zeroShortComplex v hv p) ⊥ hz z

theorem cohomologyIso_nativeCycle (q : ℕ)
    (z : EtaleCohomologyProducts.cycles v hv p q) :
    (EtaleCohomologyProducts.cohomologyIso v hv p q).hom.hom
      (ModuleComplexNativeCycleClasses.cycleClass (L) q (nativeCycle v hv p q z)) =
        Submodule.Quotient.mk z := by
  cases q with
  | zero =>
    unfold EtaleCohomologyProducts.cohomologyIso
    refine composite_class _ _ _ _ _ (specifiedCycle v hv p 0 0 z) z ?_ ?_ ?_
    · exact wholeRow_class (L) 0 0 1 CochainComplex.prev_nat_zero
        (CochainComplex.next ℕ 0) _ _ rfl
    · rfl
    · exact zeroRow_class v hv p z
  | succ q =>
    unfold EtaleCohomologyProducts.cohomologyIso
    refine composite_class _ _ _ _ _ (specifiedCycle v hv p q (q+1) z) z ?_ ?_ ?_
    · exact wholeRow_class (L) q (q+1) (q+1+1)
        (CochainComplex.prev_nat_succ q) (CochainComplex.next ℕ (q+1)) _ _ rfl
    · rfl
    · exact rowClass_to_quotient (EtaleCohomologyProducts.positiveShortComplex v hv p q) z

/-- EVERY existing original native cycleClass is the SAME actual whole native cycle class. -/
theorem nativeCycleClass_eq_native (q : ℕ) (z : EtaleCohomologyProducts.cycles v hv p q) :
    EtaleCohomologyProducts.nativeCycleClass v hv p q z =
      ModuleComplexNativeCycleClasses.cycleClass (L) q (nativeCycle v hv p q z) := by
  have h := cohomologyIso_nativeCycle v hv p q z
  have hi := congrArg (EtaleCohomologyProducts.cohomologyIso v hv p q).inv.hom h.symm
  exact hi.trans (Iso.hom_inv_id_apply (EtaleCohomologyProducts.cohomologyIso v hv p q) _)

/-- The SAME original inverse Cartier is the actual whole native class of its SAME original
internally constructed cycle representative, in EVERY degree and on EVERY form. -/
theorem inverseCartier_cycleClass (q : ℕ) (a : ⋀[A]^q W) :
    EtaleCartierCycleRepresentatives.inverseCartier v hv p q a =
      ModuleComplexNativeCycleClasses.cycleClass (L) q
        (nativeCycle v hv p q (EtaleCartierCycleRepresentatives.cycleRepresentative v hv p q a)) :=
  nativeCycleClass_eq_native v hv p q _

end EnvelopeProperty.Cartier.EtaleNativeCycleClass
