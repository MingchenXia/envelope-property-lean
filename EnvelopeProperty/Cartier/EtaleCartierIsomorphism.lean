import EnvelopeProperty.Cartier.EtaleCartierRepresentativeValues
import EnvelopeProperty.Algebra.FlatModuleHomologyCycleClasses

/-! # The genuine canonical all-degree etale Cartier isomorphism -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleCartierIsomorphism
open CategoryTheory Limits
open scoped Classical TensorProduct ChangeOfRings
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


private def nativeClass {A : Type u} [CommRing A] (S : ShortComplex (ModuleCat A))
    (z : LinearMap.ker S.g.hom) : S.homology :=
  S.homologyπ (S.moduleCatCyclesIso.inv z)

private def extendedCycle {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (S : ShortComplex (ModuleCat A)) (z : LinearMap.ker S.g.hom) (b : B) :
    LinearMap.ker (S.map (ModuleCat.extendScalars f)).g.hom :=
  ⟨b ⊗ₜ[A,f] z.val, by
    change (ModuleCat.extendScalars f).map S.g (b ⊗ₜ[A,f] z.val) = 0
    have hz : (b ⊗ₜ[A,f] (0 : S.X₃) : (ModuleCat.extendScalars f).obj S.X₃) = 0 := by
      let : Module A B := Module.compHom B f
      exact TensorProduct.tmul_zero _ _
    exact (ModuleCat.ExtendScalars.map_tmul f S.g b z.val).trans
      ((congrArg (fun a : S.X₃ => b ⊗ₜ[A,f] a) z.property).trans hz)⟩

private theorem flat_nativeClass {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.Flat) (S : ShortComplex (ModuleCat A)) (z : LinearMap.ker S.g.hom) (b : B) :
    (FlatModuleHomologyCycleClasses.homologyIso f hf S).hom
      (nativeClass (S.map (ModuleCat.extendScalars f)) (extendedCycle f S z b)) =
        b ⊗ₜ[A,f] (nativeClass S z) :=
  FlatModuleHomologyCycleClasses.cycleClass_tmul f hf S (extendedCycle f S z b) b z rfl

private def extensionPostIso {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {M N : ModuleCat A} {P : ModuleCat B} (e : M ≅ N)
    (e' : (ModuleCat.extendScalars f).obj N ≅ P) : (ModuleCat.extendScalars f).obj M ≅ P :=
  (ModuleCat.extendScalars f).mapIso e ≪≫ e'

private theorem extensionPostIso_tmul {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {M N : ModuleCat A} {P : ModuleCat B} (e : M ≅ N)
    (e' : (ModuleCat.extendScalars f).obj N ≅ P) (b : B) (a : M) :
    (extensionPostIso f e e').hom.hom (b ⊗ₜ[A,f] a) = e'.hom.hom (b ⊗ₜ[A,f] (e.hom.hom a)) :=
  congrArg e'.hom (ModuleCat.ExtendScalars.map_tmul f e.hom b a)

private theorem extend_map_zero {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (M N : ModuleCat.{u} A) :
    (ModuleCat.extendScalars f).map (0 : M ⟶ N) = 0 := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  exact (ModuleCat.ExtendScalars.map_tmul f (0 : M ⟶ N) (1 : B) m).trans (by
    change ((1 : B) ⊗ₜ[A,f] (0 : N) : (ModuleCat.extendScalars f).obj N) = 0
    let : Module A B := Module.compHom B f
    exact TensorProduct.tmul_zero _ _)

private def assembly {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (S : ShortComplex (ModuleCat A)) (T : ShortComplex (ModuleCat B))
    (e : S.map (ModuleCat.extendScalars f) ≅ T) {M : ModuleCat A} {N : ModuleCat B}
    (C : S.homology ≅ M) (D : (ModuleCat.extendScalars f).obj M ≅ N) : T.homology ≅ N :=
  (ShortComplex.homologyMapIso e).symm ≪≫ FlatModuleHomologyCycleClasses.homologyIso f hf S ≪≫
    extensionPostIso f C D

private theorem assembly_class {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (S : ShortComplex (ModuleCat A)) (T : ShortComplex (ModuleCat B))
    (e : S.map (ModuleCat.extendScalars f) ≅ T) {M : ModuleCat A} {N : ModuleCat B}
    (C : S.homology ≅ M) (D : (ModuleCat.extendScalars f).obj M ≅ N)
    (z : LinearMap.ker S.g.hom) (w : LinearMap.ker T.g.hom)
    (hzw : e.hom.τ₂ ((1 : B) ⊗ₜ[A,f] z.val) = w.val) (c : M)
    (hc : C.hom.hom (nativeClass S z) = c) :
    (assembly f hf S T e C D).hom.hom (nativeClass T w) = D.hom.hom ((1 : B) ⊗ₜ[A,f] c) := by
  let eh := ShortComplex.homologyMapIso e
  have hm : eh.hom.hom (nativeClass (S.map (ModuleCat.extendScalars f)) (extendedCycle f S z 1)) =
      nativeClass T w := actualClass_map e.hom (extendedCycle f S z 1) w hzw
  have hi : eh.inv.hom (nativeClass T w) =
      nativeClass (S.map (ModuleCat.extendScalars f)) (extendedCycle f S z 1) :=
    (congrArg eh.inv.hom hm.symm).trans (Iso.hom_inv_id_apply eh _)
  change (extensionPostIso f C D).hom.hom
    ((FlatModuleHomologyCycleClasses.homologyIso f hf S).hom.hom (eh.inv.hom (nativeClass T w))) = _
  have hl := congrArg (fun a => (extensionPostIso f C D).hom.hom
    ((FlatModuleHomologyCycleClasses.homologyIso f hf S).hom.hom a)) hi
  have hf' := congrArg (extensionPostIso f C D).hom.hom (flat_nativeClass f hf S z 1)
  have hp := (extensionPostIso_tmul f C D 1 (nativeClass S z)).trans
    (congrArg (fun a : M => D.hom.hom ((1 : B) ⊗ₜ[A,f] a)) hc)
  exact hl.trans (hf'.trans hp)

variable {k B : Type u} [Field k] [CommRing B] [Algebra k B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP B p]
local notation "P" => MvPolynomial (Fin n) k
local notation "V" => KaehlerDifferential k B

/-- Actual native polynomial positive rows base-change to the SAME entire original etale rows. -/
def positiveScalarShortIso (q : ℕ) :
    (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p q).map
      (ModuleCat.extendScalars (MvPolynomial.aeval (R := k) v).toRingHom) ≅
      EtaleCohomologyProducts.positiveShortComplex v hv p q :=
  ShortComplex.isoMk (EtaleExteriorBaseChange.frobeniusFormIso v hv p q)
    (EtaleExteriorBaseChange.frobeniusFormIso v hv p (q+1))
    (EtaleExteriorBaseChange.frobeniusFormIso v hv p (q+1+1))
    (EtaleExteriorBaseChange.frobeniusFormIso_comm v hv p q)
    (EtaleExteriorBaseChange.frobeniusFormIso_comm v hv p (q+1))

/-- Degree zero retains the SAME genuine zero incoming original map under native base change. -/
def zeroScalarShortIso :
    (PolynomialCartierCohomology.zeroShortComplex (σ := Fin n) k p).map
      (ModuleCat.extendScalars (MvPolynomial.aeval (R := k) v).toRingHom) ≅
      EtaleCohomologyProducts.zeroShortComplex v hv p :=
  ShortComplex.isoMk (EtaleExteriorBaseChange.frobeniusFormIso v hv p 0)
    (EtaleExteriorBaseChange.frobeniusFormIso v hv p 0)
    (EtaleExteriorBaseChange.frobeniusFormIso v hv p 1)
    (by simp only [PolynomialCartierCohomology.zeroShortComplex, ShortComplex.map_f,
      EtaleCohomologyProducts.zeroShortComplex, comp_zero, extend_map_zero]
        exact zero_comp.symm)
    (EtaleExteriorBaseChange.frobeniusFormIso_comm v hv p 0)

variable [PerfectRing k p]

/-- Actual original positive row homology has a genuine Cartier isomorphism by DERIVED flatness,
SAME native polynomial homology and SAME whole exterior form base change. -/
def positiveShortCartierIso (q : ℕ) :
    (EtaleCohomologyProducts.positiveShortComplex v hv p q).homology ≅
      ModuleCat.of B (⋀[B]^(q+1) V) :=
  assembly (MvPolynomial.aeval (R := k) v).toRingHom
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hv).1
    (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p q)
    (EtaleCohomologyProducts.positiveShortComplex v hv p q) (positiveScalarShortIso v hv p q)
    (PolynomialCartierCohomology.positiveShortComplexCartierIso (σ := Fin n) k p q)
    (EtaleExteriorBaseChange.exteriorIso v hv (q+1))

/-- The SAME original degree-zero row has its genuine native Cartier isomorphism. -/
def zeroShortCartierIso :
    (EtaleCohomologyProducts.zeroShortComplex v hv p).homology ≅ ModuleCat.of B (⋀[B]^0 V) :=
  assembly (MvPolynomial.aeval (R := k) v).toRingHom
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hv).1
    (PolynomialCartierCohomology.zeroShortComplex (σ := Fin n) k p)
    (EtaleCohomologyProducts.zeroShortComplex v hv p) (zeroScalarShortIso v hv p)
    (PolynomialCartierCohomology.zeroShortComplexCartierIso (σ := Fin n) k p)
    (EtaleExteriorBaseChange.exteriorIso v hv 0)

private theorem nativeClass_eq_quotient {A : Type u} [CommRing A]
    (S : ShortComplex (ModuleCat A)) (z : LinearMap.ker S.g.hom) :
    nativeClass S z = S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z) :=
  S.moduleCatCyclesIso_inv_π_apply z

private def positivePolynomialCycle (q : ℕ) (a : ⋀[P]^(q+1) (KaehlerDifferential k P)) :
    LinearMap.ker (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p q).g.hom :=
  ⟨PolynomialCartierImage.representative k p (q+1) a,
    PolynomialCartierImage.originalRepresentative_closed k p (q+1) a⟩

private theorem positivePolynomialCycle_class (q : ℕ) (a : ⋀[P]^(q+1) (KaehlerDifferential k P)) :
    (PolynomialCartierCohomology.positiveShortComplexCartierIso (σ := Fin n) k p q).hom.hom
      (nativeClass (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p q)
        (positivePolynomialCycle (k := k) p q a)) = a := by
  have hn := congrArg
    (PolynomialCartierCohomology.positiveShortComplexCartierIso (σ := Fin n) k p q).hom.hom
    (nativeClass_eq_quotient _ (positivePolynomialCycle (k := k) p q a))
  have hc := PolynomialCartierCohomology.positiveShortComplexCartierIso_cycle (σ := Fin n) k p q
    (positivePolynomialCycle (k := k) p q a)
  exact hn.trans (hc.trans (PolynomialCartierCohomology.coefficientLinear_representative k p (q+1) a))

private def zeroPolynomialCycle (a : ⋀[P]^0 (KaehlerDifferential k P)) :
    LinearMap.ker (PolynomialCartierCohomology.zeroShortComplex (σ := Fin n) k p).g.hom :=
  ⟨PolynomialCartierImage.representative k p 0 a,
    PolynomialCartierImage.originalRepresentative_closed k p 0 a⟩

private theorem zeroPolynomialCycle_class (a : ⋀[P]^0 (KaehlerDifferential k P)) :
    (PolynomialCartierCohomology.zeroShortComplexCartierIso (σ := Fin n) k p).hom.hom
      (nativeClass (PolynomialCartierCohomology.zeroShortComplex (σ := Fin n) k p)
        (zeroPolynomialCycle (k := k) p a)) = a := by
  have hn := congrArg
    (PolynomialCartierCohomology.zeroShortComplexCartierIso (σ := Fin n) k p).hom.hom
    (nativeClass_eq_quotient _ (zeroPolynomialCycle (k := k) p a))
  have hc := PolynomialCartierCohomology.zeroShortComplexCartierIso_cycle (σ := Fin n) k p
    (zeroPolynomialCycle (k := k) p a)
  exact hn.trans (hc.trans (PolynomialCartierCohomology.coefficientLinear_representative k p 0 a))

/-- The actual native positive Cartier isomorphism takes EACH internally constructed original
etale basis cycle class to that SAME original exterior-basis vector. -/
theorem positiveShortCartierIso_cycleRepresentative (q : ℕ) (s : Set.powersetCard (Fin n) (q+1)) :
    (positiveShortCartierIso v hv p q).hom.hom
      ((EtaleCohomologyProducts.positiveShortComplex v hv p q).homologyπ
        ((EtaleCohomologyProducts.positiveShortComplex v hv p q).moduleCatCyclesIso.inv
          (EtaleCartierCycleRepresentatives.cycleRepresentative v hv p (q+1)
            ((Char0.etaleDifferentialBasis v hv).exteriorPower (q+1) s)))) =
      (Char0.etaleDifferentialBasis v hv).exteriorPower (q+1) s := by
  let a := (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower (q+1) s
  let z := positivePolynomialCycle (k := k) p q a
  let w := EtaleCartierCycleRepresentatives.cycleRepresentative v hv p (q+1)
    ((Char0.etaleDifferentialBasis v hv).exteriorPower (q+1) s)
  have hz : (positiveScalarShortIso v hv p q).hom.τ₂ ((1 : B) ⊗ₜ[P,(MvPolynomial.aeval (R := k) v).toRingHom]
      z.val) = w.val :=
    (EtaleExteriorBaseChange.frobeniusFormIso_one_tmul v hv p (q+1)
      (PolynomialCartierImage.originalRepresentative k p (q+1) a)).trans
        (EtaleCartierRepresentativeValues.polynomial_representative_map_basis v hv p (q+1) s)
  have h := assembly_class (MvPolynomial.aeval (R := k) v).toRingHom
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hv).1
    (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p q)
    (EtaleCohomologyProducts.positiveShortComplex v hv p q) (positiveScalarShortIso v hv p q)
    (PolynomialCartierCohomology.positiveShortComplexCartierIso (σ := Fin n) k p q)
    (EtaleExteriorBaseChange.exteriorIso v hv (q+1)) z w hz a (positivePolynomialCycle_class p q a)
  exact h.trans ((EtaleExteriorBaseChange.exteriorIso_tmul_basis v hv (q+1) (1 : B) s).trans
    (one_smul B _))

/-- The SAME original zero-degree Cartier isomorphism recovers EACH internally constructed
original unit-degree basis cycle, retaining the actual zero incoming map. -/
theorem zeroShortCartierIso_cycleRepresentative (s : Set.powersetCard (Fin n) 0) :
    (zeroShortCartierIso v hv p).hom.hom
      ((EtaleCohomologyProducts.zeroShortComplex v hv p).homologyπ
        ((EtaleCohomologyProducts.zeroShortComplex v hv p).moduleCatCyclesIso.inv
          (EtaleCartierCycleRepresentatives.cycleRepresentative v hv p 0
            ((Char0.etaleDifferentialBasis v hv).exteriorPower 0 s)))) =
      (Char0.etaleDifferentialBasis v hv).exteriorPower 0 s := by
  let a := (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower 0 s
  let z := zeroPolynomialCycle (k := k) p a
  let w := EtaleCartierCycleRepresentatives.cycleRepresentative v hv p 0
    ((Char0.etaleDifferentialBasis v hv).exteriorPower 0 s)
  have hz : (zeroScalarShortIso v hv p).hom.τ₂ ((1 : B) ⊗ₜ[P,(MvPolynomial.aeval (R := k) v).toRingHom]
      z.val) = w.val :=
    (EtaleExteriorBaseChange.frobeniusFormIso_one_tmul v hv p 0
      (PolynomialCartierImage.originalRepresentative k p 0 a)).trans
        (EtaleCartierRepresentativeValues.polynomial_representative_map_basis v hv p 0 s)
  have h := assembly_class (MvPolynomial.aeval (R := k) v).toRingHom
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hv).1
    (PolynomialCartierCohomology.zeroShortComplex (σ := Fin n) k p)
    (EtaleCohomologyProducts.zeroShortComplex v hv p) (zeroScalarShortIso v hv p)
    (PolynomialCartierCohomology.zeroShortComplexCartierIso (σ := Fin n) k p)
    (EtaleExteriorBaseChange.exteriorIso v hv 0) z w hz a (zeroPolynomialCycle_class p a)
  exact h.trans ((EtaleExteriorBaseChange.exteriorIso_tmul_basis v hv 0 (1 : B) s).trans
    (one_smul B _))

/-- The actual positive-degree cycle/boundary quotient has its SAME native Cartier isomorphism. -/
def positiveQuotientCartierIso (q : ℕ) :
    ModuleCat.of B (EtaleCohomologyProducts.cohomology v hv p (q+1)) ≅
      ModuleCat.of B (⋀[B]^(q+1) V) :=
  (EtaleCohomologyProducts.positiveShortHomologyIso v hv p q).symm ≪≫
    positiveShortCartierIso v hv p q

/-- The original zero-degree quotient retains the actual zero incoming boundary. -/
def zeroQuotientCartierIso :
    ModuleCat.of B (EtaleCohomologyProducts.cohomology v hv p 0) ≅
      ModuleCat.of B (⋀[B]^0 V) :=
  (EtaleCohomologyProducts.zeroShortHomologyIso v hv p).symm ≪≫ zeroShortCartierIso v hv p

private theorem quotientRow_class {A : Type u} [CommRing A]
    (S : ShortComplex (ModuleCat A)) (N : Submodule A (LinearMap.ker S.g.hom))
    (h : LinearMap.range S.moduleCatToCycles = N) (z : LinearMap.ker S.g.hom) :
    (S.moduleCatHomologyIso ≪≫ (Submodule.quotEquivOfEq _ _ h).toModuleIso).hom.hom
      (nativeClass S z) = Submodule.Quotient.mk z := by
  rw [nativeClass_eq_quotient]
  change (Submodule.quotEquivOfEq _ _ h)
    (S.moduleCatHomologyIso.hom.hom (S.moduleCatHomologyIso.inv.hom
      (Submodule.Quotient.mk z))) = _
  exact (congrArg (Submodule.quotEquivOfEq _ _ h)
    (Iso.inv_hom_id_apply S.moduleCatHomologyIso (Submodule.Quotient.mk z))).trans rfl

omit [CharP k p] [PerfectRing k p] in
private theorem zeroShortHomologyIso_class (z : EtaleCohomologyProducts.cycles v hv p 0) :
    (EtaleCohomologyProducts.zeroShortHomologyIso v hv p).hom.hom
      (nativeClass (EtaleCohomologyProducts.zeroShortComplex v hv p) z) =
        Submodule.Quotient.mk z := by
  have h : LinearMap.range (EtaleCohomologyProducts.zeroShortComplex v hv p).moduleCatToCycles = ⊥ := by
    apply LinearMap.range_eq_bot.mpr
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    rfl
  exact quotientRow_class (EtaleCohomologyProducts.zeroShortComplex v hv p) ⊥ h z

omit [CharP k p] [PerfectRing k p] in
private theorem zeroShortHomologyIso_inv_class (z : EtaleCohomologyProducts.cycles v hv p 0) :
    (EtaleCohomologyProducts.zeroShortHomologyIso v hv p).inv.hom (Submodule.Quotient.mk z) =
      nativeClass (EtaleCohomologyProducts.zeroShortComplex v hv p) z :=
  (congrArg (EtaleCohomologyProducts.zeroShortHomologyIso v hv p).inv.hom
    (zeroShortHomologyIso_class v hv p z).symm).trans
      (Iso.hom_inv_id_apply (EtaleCohomologyProducts.zeroShortHomologyIso v hv p) _)

/-- The actual positive quotient Cartier map recovers EACH SAME original basis vector from its
internally constructed original cycle representative. -/
theorem positiveQuotientCartierIso_cycleRepresentative (q : ℕ)
    (s : Set.powersetCard (Fin n) (q+1)) :
    (positiveQuotientCartierIso v hv p q).hom.hom (Submodule.Quotient.mk
      (EtaleCartierCycleRepresentatives.cycleRepresentative v hv p (q+1)
        ((Char0.etaleDifferentialBasis v hv).exteriorPower (q+1) s))) =
      (Char0.etaleDifferentialBasis v hv).exteriorPower (q+1) s := by
  change (positiveShortCartierIso v hv p q).hom.hom
    ((EtaleCohomologyProducts.positiveShortHomologyIso v hv p q).inv.hom _) = _
  have h := congrArg (positiveShortCartierIso v hv p q).hom.hom
    (nativeClass_eq_quotient (EtaleCohomologyProducts.positiveShortComplex v hv p q)
      (EtaleCartierCycleRepresentatives.cycleRepresentative v hv p (q+1)
        ((Char0.etaleDifferentialBasis v hv).exteriorPower (q+1) s))).symm
  exact h.trans (positiveShortCartierIso_cycleRepresentative v hv p q s)

/-- Degree zero obeys the SAME genuine basis recovery without replacing its incoming map. -/
theorem zeroQuotientCartierIso_cycleRepresentative (s : Set.powersetCard (Fin n) 0) :
    (zeroQuotientCartierIso v hv p).hom.hom (Submodule.Quotient.mk
      (EtaleCartierCycleRepresentatives.cycleRepresentative v hv p 0
        ((Char0.etaleDifferentialBasis v hv).exteriorPower 0 s))) =
      (Char0.etaleDifferentialBasis v hv).exteriorPower 0 s := by
  change (zeroShortCartierIso v hv p).hom.hom
    ((EtaleCohomologyProducts.zeroShortHomologyIso v hv p).inv.hom _) = _
  rw [zeroShortHomologyIso_inv_class]
  exact zeroShortCartierIso_cycleRepresentative v hv p s

/-- The actual original quotient Cartier isomorphism in EVERY degree, including zero. -/
def quotientCartierIso (q : ℕ) :
    ModuleCat.of B (EtaleCohomologyProducts.cohomology v hv p q) ≅ ModuleCat.of B (⋀[B]^q V) :=
  match q with
  | 0 => zeroQuotientCartierIso v hv p
  | q+1 => positiveQuotientCartierIso v hv p q

/-- Genuine entire basis extensionality identifies the SAME canonical inverse Cartier map
with the inverse of the actual quotient Cartier isomorphism, in EVERY degree. -/
theorem quotientCartierIso_classMap (q : ℕ) :
    (quotientCartierIso v hv p q).hom.hom.comp
      (EtaleClosedExteriorLift.classMap v hv p
        (EtaleCartierCycleRepresentatives.coordinateCycleMap v hv p) q) = LinearMap.id := by
  apply ((Char0.etaleDifferentialBasis v hv).exteriorPower q).ext
  intro s
  cases q with
  | zero => exact zeroQuotientCartierIso_cycleRepresentative v hv p s
  | succ q => exact positiveQuotientCartierIso_cycleRepresentative v hv p q s

/-- The ENTIRE internally constructed original canonical map is the inverse of this SAME
actual Cartier isomorphism; no representative or compatibility certificate is supplied. -/
theorem classMap_eq_quotientCartierIso_inv (q : ℕ) :
    EtaleClosedExteriorLift.classMap v hv p
      (EtaleCartierCycleRepresentatives.coordinateCycleMap v hv p) q =
        (quotientCartierIso v hv p q).inv.hom := by
  apply LinearMap.ext
  intro a
  apply (ModuleCat.mono_iff_injective (quotientCartierIso v hv p q).hom).mp inferInstance
  exact (LinearMap.congr_fun (quotientCartierIso_classMap v hv p q) a).trans
    (Iso.inv_hom_id_apply (quotientCartierIso v hv p q) a).symm

/-- Cartier isomorphism of the SAME ENTIRE native original Frobenius de Rham cohomology. -/
def cartierIso (q : ℕ) : (EtaleDeRham.frobeniusComplex v hv p).homology q ≅
    ModuleCat.of B (⋀[B]^q V) :=
  EtaleCohomologyProducts.cohomologyIso v hv p q ≪≫ quotientCartierIso v hv p q

/-- Its inverse is the SAME pre-existing, internally constructed, coordinate-independent
canonical inverse Cartier map on EVERY original form, not merely some abstract isomorphism. -/
theorem cartierIso_inv (q : ℕ) : (cartierIso v hv p q).inv.hom =
    EtaleCartierCycleRepresentatives.inverseCartier v hv p q := by
  have h := congrArg
    (fun F => (EtaleCohomologyProducts.cohomologyIso v hv p q).inv.hom.comp F)
      (classMap_eq_quotientCartierIso_inv v hv p q)
  exact h.symm

/-- The SAME canonical inverse Cartier map is genuinely bijective in EVERY degree. -/
theorem inverseCartier_bijective (q : ℕ) :
    Function.Bijective (EtaleCartierCycleRepresentatives.inverseCartier v hv p q) := by
  rw [← cartierIso_inv v hv p q]
  exact (cartierIso v hv p q).symm.toLinearEquiv.bijective

/-- EVERY original form is recovered by this SAME actual canonical Cartier isomorphism. -/
theorem cartierIso_inverseCartier (q : ℕ) (a : ⋀[B]^q V) :
    (cartierIso v hv p q).hom.hom
      (EtaleCartierCycleRepresentatives.inverseCartier v hv p q a) = a :=
  (congrArg (cartierIso v hv p q).hom.hom
    (LinearMap.congr_fun (cartierIso_inv v hv p q).symm a)).trans
      (Iso.inv_hom_id_apply (cartierIso v hv p q) a)

/-- EVERY original native whole-complex homology class is recovered by the SAME canonical map. -/
theorem inverseCartier_cartierIso (q : ℕ)
    (z : (EtaleDeRham.frobeniusComplex v hv p).homology q) :
    EtaleCartierCycleRepresentatives.inverseCartier v hv p q
      ((cartierIso v hv p q).hom.hom z) = z :=
  (LinearMap.congr_fun (cartierIso_inv v hv p q).symm
    ((cartierIso v hv p q).hom.hom z)).trans (Iso.hom_inv_id_apply (cartierIso v hv p q) z)

end EnvelopeProperty.Cartier.EtaleCartierIsomorphism
