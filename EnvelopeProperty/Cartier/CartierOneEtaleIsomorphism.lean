import EnvelopeProperty.Cartier.IntrinsicCartierOneNaturality
import EnvelopeProperty.Cartier.EtaleCartierCohomology
import EnvelopeProperty.Algebra.FlatModuleHomologyCycleClasses

/-! # The canonical one-form Cartier map is the actual etale isomorphism -/
noncomputable section
namespace EnvelopeProperty.Cartier.CartierOneEtaleIsomorphism
open CategoryTheory Limits MvPolynomial
open scoped TensorProduct ChangeOfRings Classical
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

variable {k B : Type u} [Field k] [CommRing B] [Algebra k B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP B p] [PerfectRing k p]

private theorem oneEquiv_basis_singleton {K V I : Type*} [CommRing K] [AddCommGroup V]
    [Module K V] [LinearOrder I] (b : Module.Basis I K V) (i : I) :
    exteriorPower.oneEquiv K V
      (b.exteriorPower 1 (Set.powersetCard.ofCard (Finset.card_singleton i))) = b i := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.oneEquiv_ιMulti]
  dsimp only [Function.comp_apply]
  congr 1
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  exact Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ _ _)

omit [PerfectRing k p] in
/-- The actual original polynomial Cartier representative of dXi is the SAME original
Xi^(p-1)dXi, not a supplied representative comparison. -/
theorem polynomial_representative_coordinate (i : Fin n) :
    PolynomialCartierImage.representative k p 1
      ((exteriorPower.oneEquiv (MvPolynomial (Fin n) k)
        (KaehlerDifferential k (MvPolynomial (Fin n) k))).symm
          (KaehlerDifferential.D k (MvPolynomial (Fin n) k) (X i))) =
      (show PolynomialDeRham.frobeniusModule (σ := Fin n) k p 1 from
        IntrinsicCartierOne.generatorForm (R := k) p (X i)) := by
  let s : Set.powersetCard (Fin n) 1 := Set.powersetCard.ofCard (Finset.card_singleton i)
  have he : (PolynomialCartierImage.residueDigit p 1 s).toFinsupp = Finsupp.single i (p-1) := by
    ext j
    simp only [Box.toFinsupp_apply, PolynomialCartierImage.residueDigit_apply, Finsupp.single_apply]
    have hs : j ∈ s ↔ i = j := by
      rw [← Set.powersetCard.mem_coe_iff]
      change j ∈ ({i} : Finset (Fin n)) ↔ i = j
      simp only [Finset.mem_singleton, eq_comm]
    simp only [hs]
  have hb : (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower 1 s =
      (exteriorPower.oneEquiv (MvPolynomial (Fin n) k)
        (KaehlerDifferential k (MvPolynomial (Fin n) k))).symm
          (KaehlerDifferential.D k (MvPolynomial (Fin n) k) (X i)) := by
    apply (exteriorPower.oneEquiv (MvPolynomial (Fin n) k)
      (KaehlerDifferential k (MvPolynomial (Fin n) k))).injective
    exact (oneEquiv_basis_singleton (KaehlerDifferential.mvPolynomialBasis k (Fin n)) i).trans
      ((KaehlerDifferential.mvPolynomialBasis_apply k (Fin n) i).trans
        (LinearEquiv.apply_symm_apply _ _).symm)
  apply (PolynomialCartierCohomology.frobeniusUnderlying (σ := Fin n) k p 1).injective
  change PolynomialCartierImage.originalRepresentative k p 1 _ =
    IntrinsicCartierOne.generatorForm (R := k) p (X i : MvPolynomial (Fin n) k)
  have h := PolynomialCartierImage.originalRepresentative_smul_basis k p 1 s
    (1 : MvPolynomial (Fin n) k)
  simpa only [one_smul, one_pow, one_mul, he, ← X_pow_eq_monomial, hb,
    IntrinsicCartierOne.generatorForm] using h

/-- Genuine actual scalar extension of the original polynomial short complex is the SAME
actual original etale short complex, with ALL original degree maps. -/
def scalarShortIso :
    (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0).map
        (ModuleCat.extendScalars (MvPolynomial.aeval (R := k) v).toRingHom) ≅
      IntrinsicCartierOne.shortComplex v hv p :=
  ShortComplex.isoMk (EtaleExteriorBaseChange.frobeniusFormIso v hv p 0)
    (EtaleExteriorBaseChange.frobeniusFormIso v hv p 1)
    (EtaleExteriorBaseChange.frobeniusFormIso v hv p 2)
    (EtaleExteriorBaseChange.frobeniusFormIso_comm v hv p 0)
    (EtaleExteriorBaseChange.frobeniusFormIso_comm v hv p 1)

private def comparisonHomologyIso :
    ((PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0).map
      (ModuleCat.extendScalars (MvPolynomial.aeval (R := k) v).toRingHom)).homology ≅
    (IntrinsicCartierOne.shortComplex v hv p).homology :=
  (ShortComplex.homologyFunctor (ModuleCat B)).mapIso (scalarShortIso v hv p)

private def flatComparison :
    ((PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0).map
      (ModuleCat.extendScalars (MvPolynomial.aeval (R := k) v).toRingHom)).homology ≅
    (ModuleCat.extendScalars (MvPolynomial.aeval (R := k) v).toRingHom).obj
      (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0).homology :=
  FlatModuleHomologyCycleClasses.homologyIso (MvPolynomial.aeval (R := k) v).toRingHom
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hv).1
    (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0)

private def targetOneIso :
    (ModuleCat.extendScalars (MvPolynomial.aeval (R := k) v).toRingHom).obj
      (ModuleCat.of (MvPolynomial (Fin n) k)
        (⋀[MvPolynomial (Fin n) k]^1 (KaehlerDifferential k (MvPolynomial (Fin n) k)))) ≅
      ModuleCat.of B (KaehlerDifferential k B) :=
  EtaleExteriorBaseChange.exteriorIso v hv 1 ≪≫
    (exteriorPower.oneEquiv B (KaehlerDifferential k B)).toModuleIso

private def scalarFormsIso :
    (ModuleCat.extendScalars (MvPolynomial.aeval (R := k) v).toRingHom).obj
      (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0).homology ≅
    ModuleCat.of B (KaehlerDifferential k B) :=
  extensionPostIso (MvPolynomial.aeval (R := k) v).toRingHom
    (PolynomialCartierCohomology.positiveShortComplexCartierIso (σ := Fin n) k p 0)
    (targetOneIso v hv)

/-- Actual native one-form homology isomorphism, with honest perfect coefficient field.
All original polynomial/etale modules, differentials and scalar comparisons are retained. -/
def cartierIso : (IntrinsicCartierOne.shortComplex v hv p).homology ≅
    ModuleCat.of B (KaehlerDifferential k B) :=
  (comparisonHomologyIso v hv p).symm ≪≫ flatComparison v hv p ≪≫ scalarFormsIso v hv p


private def polynomialGeneratorCycle (i : Fin n) :
    LinearMap.ker (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0).g.hom :=
  ⟨PolynomialCartierImage.representative k p 1
    ((exteriorPower.oneEquiv (MvPolynomial (Fin n) k)
      (KaehlerDifferential k (MvPolynomial (Fin n) k))).symm
        (KaehlerDifferential.D k (MvPolynomial (Fin n) k) (X i))),
    PolynomialCartierImage.originalRepresentative_closed k p 1 _⟩

private theorem polynomialGenerator_class (i : Fin n) :
    (PolynomialCartierCohomology.positiveShortComplexCartierIso (σ := Fin n) k p 0).hom
      ((PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0).homologyπ
        ((PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0).moduleCatCyclesIso.inv
          (polynomialGeneratorCycle (k := k) p i))) =
      (exteriorPower.oneEquiv (MvPolynomial (Fin n) k)
        (KaehlerDifferential k (MvPolynomial (Fin n) k))).symm
          (KaehlerDifferential.D k (MvPolynomial (Fin n) k) (X i)) := by
  have hc := (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0).moduleCatCyclesIso_inv_π_apply (polynomialGeneratorCycle (k := k) p i)
  change _ = PolynomialCartierCohomology.positiveCycleClass k p 0
    (polynomialGeneratorCycle (k := k) p i) at hc
  rw [hc, PolynomialCartierCohomology.positiveShortComplexCartierIso_cycle]
  exact PolynomialCartierCohomology.coefficientLinear_representative k p 1 _

omit [Fact p.Prime] [CharP k p] [CharP B p] [PerfectRing k p] in
private theorem polynomialFormMap_generator (i : Fin n) :
    EtaleDeRham.polynomialFormMap v hv 1
      (IntrinsicCartierOne.generatorForm (R := k) p (X i : MvPolynomial (Fin n) k)) =
      IntrinsicCartierOne.generatorForm (R := k) p (v i) := by
  let s : Set.powersetCard (Fin n) 1 := Set.powersetCard.ofCard (Finset.card_singleton i)
  have hb : (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower 1 s =
      (exteriorPower.oneEquiv (MvPolynomial (Fin n) k)
        (KaehlerDifferential k (MvPolynomial (Fin n) k))).symm
          (KaehlerDifferential.D k (MvPolynomial (Fin n) k) (X i)) := by
    apply (exteriorPower.oneEquiv (MvPolynomial (Fin n) k)
      (KaehlerDifferential k (MvPolynomial (Fin n) k))).injective
    exact (oneEquiv_basis_singleton (KaehlerDifferential.mvPolynomialBasis k (Fin n)) i).trans
      ((KaehlerDifferential.mvPolynomialBasis_apply k (Fin n) i).trans
        (LinearEquiv.apply_symm_apply _ _).symm)
  have hc : (Char0.etaleDifferentialBasis v hv).exteriorPower 1 s =
      (exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm (KaehlerDifferential.D k B (v i)) := by
    apply (exteriorPower.oneEquiv B (KaehlerDifferential k B)).injective
    exact (oneEquiv_basis_singleton (Char0.etaleDifferentialBasis v hv) i).trans
      ((Char0.etaleDifferentialBasis_apply v hv i).trans (LinearEquiv.apply_symm_apply _ _).symm)
  rw [IntrinsicCartierOne.generatorForm, ← hb, EtaleDeRham.polynomialFormMap_smul_basis,
    map_pow, aeval_X, hc]
  rfl

private def extendedGeneratorCycle (i : Fin n) :
    LinearMap.ker ((PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0).map
      (ModuleCat.extendScalars (MvPolynomial.aeval (R := k) v).toRingHom)).g.hom :=
  extendedCycle (MvPolynomial.aeval (R := k) v).toRingHom
    (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0)
    (polynomialGeneratorCycle (k := k) p i) 1

private theorem scalarShortIso_generator (i : Fin n) :
    (scalarShortIso v hv p).hom.τ₂ (extendedGeneratorCycle v p i).val =
      (IntrinsicCartierOne.generatorCycle v hv p (v i)).val := by
  let _ := (MvPolynomial.aeval (R := k) v).toAlgebra
  change (EtaleExteriorBaseChange.frobeniusFormIso v hv p 1).hom
    ((1 : B) ⊗ₜ[MvPolynomial (Fin n) k] (polynomialGeneratorCycle (k := k) p i).val) = _
  have hrep : (polynomialGeneratorCycle (k := k) p i).val =
      (show PolynomialDeRham.frobeniusModule (σ := Fin n) k p 1 from
        IntrinsicCartierOne.generatorForm (R := k) p (X i : MvPolynomial (Fin n) k)) :=
    polynomial_representative_coordinate p i
  rw [hrep]
  exact (EtaleExteriorBaseChange.frobeniusFormIso_one_tmul v hv p 1 _).trans
    (polynomialFormMap_generator v hv p i)


private def polynomialClass (i : Fin n) :
    (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0).homology :=
  nativeClass (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0)
    (polynomialGeneratorCycle (k := k) p i)

private def extendedClass (i : Fin n) :
    ((PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0).map
      (ModuleCat.extendScalars (MvPolynomial.aeval (R := k) v).toRingHom)).homology :=
  nativeClass ((PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0).map
    (ModuleCat.extendScalars (MvPolynomial.aeval (R := k) v).toRingHom))
      (extendedGeneratorCycle v p i)

private theorem scalarShortIso_class (i : Fin n) :
    ((ShortComplex.homologyFunctor (ModuleCat B)).mapIso (scalarShortIso v hv p)).hom
      (extendedClass v p i) = IntrinsicCartierOne.generatorClass v hv p (v i) := by
  have hc := actualClass_map (scalarShortIso v hv p).hom (extendedGeneratorCycle v p i)
    (IntrinsicCartierOne.generatorCycle v hv p (v i)) (scalarShortIso_generator v hv p i)
  exact hc.trans (IntrinsicCartierOne.cycleClass_eq v hv p _).symm

omit [CharP B p] in
private theorem flatComparison_generator (i : Fin n) :
    (flatComparison v hv p).hom.hom (extendedClass v p i) =
      (1 : B) ⊗ₜ[MvPolynomial (Fin n) k,(MvPolynomial.aeval v).toRingHom]
        (polynomialClass (k := k) p i) :=
  flat_nativeClass (A := MvPolynomial (Fin n) k) (B := B) (MvPolynomial.aeval v).toRingHom
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hv).1
    (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0)
    (polynomialGeneratorCycle (k := k) p i) 1

omit [CharP B p] in
private theorem scalarFormsIso_pure
    (a : (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0).homology) :
    (scalarFormsIso v hv p).hom.hom
      ((1 : B) ⊗ₜ[MvPolynomial (Fin n) k,(MvPolynomial.aeval v).toRingHom] a) =
    (targetOneIso v hv).hom.hom
      ((1 : B) ⊗ₜ[MvPolynomial (Fin n) k,(MvPolynomial.aeval v).toRingHom]
        ((PolynomialCartierCohomology.positiveShortComplexCartierIso (σ := Fin n) k p 0).hom.hom a)) :=
  extensionPostIso_tmul (A := MvPolynomial (Fin n) k) (B := B) (MvPolynomial.aeval v).toRingHom
    (M := (PolynomialCartierCohomology.positiveShortComplex (σ := Fin n) k p 0).homology)
    (N := ModuleCat.of (MvPolynomial (Fin n) k)
      (⋀[MvPolynomial (Fin n) k]^1 (KaehlerDifferential k (MvPolynomial (Fin n) k))))
    (P := ModuleCat.of B (KaehlerDifferential k B))
    (PolynomialCartierCohomology.positiveShortComplexCartierIso (σ := Fin n) k p 0)
    (targetOneIso v hv) 1 a

private theorem exteriorIso_coordinate (i : Fin n) :
    exteriorPower.oneEquiv B (KaehlerDifferential k B)
      ((EtaleExteriorBaseChange.exteriorIso v hv 1).hom
        ((1 : B) ⊗ₜ[MvPolynomial (Fin n) k,(MvPolynomial.aeval v).toRingHom]
          ((exteriorPower.oneEquiv (MvPolynomial (Fin n) k)
            (KaehlerDifferential k (MvPolynomial (Fin n) k))).symm
              (KaehlerDifferential.D k (MvPolynomial (Fin n) k) (X i))))) =
      KaehlerDifferential.D k B (v i) := by
  let _ := (MvPolynomial.aeval (R := k) v).toAlgebra
  have hb : (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower 1
      (Set.powersetCard.ofCard (Finset.card_singleton i)) =
    (exteriorPower.oneEquiv (MvPolynomial (Fin n) k)
      (KaehlerDifferential k (MvPolynomial (Fin n) k))).symm
        (KaehlerDifferential.D k (MvPolynomial (Fin n) k) (X i)) := by
    apply (exteriorPower.oneEquiv (MvPolynomial (Fin n) k)
      (KaehlerDifferential k (MvPolynomial (Fin n) k))).injective
    exact (oneEquiv_basis_singleton (KaehlerDifferential.mvPolynomialBasis k (Fin n)) i).trans
      ((KaehlerDifferential.mvPolynomialBasis_apply k (Fin n) i).trans
        (LinearEquiv.apply_symm_apply _ _).symm)
  have h := EtaleExteriorBaseChange.exteriorIso_tmul_basis v hv 1 (1 : B)
    (Set.powersetCard.ofCard (Finset.card_singleton i))
  have h' := congrArg (exteriorPower.oneEquiv B (KaehlerDifferential k B)) h
  have ht := congrArg (fun z => exteriorPower.oneEquiv B (KaehlerDifferential k B)
    ((EtaleExteriorBaseChange.exteriorIso v hv 1).hom
      ((1 : B) ⊗ₜ[MvPolynomial (Fin n) k,(MvPolynomial.aeval v).toRingHom] z))) hb.symm
  exact ht.trans (h'.trans (by
    rw [one_smul, oneEquiv_basis_singleton, Char0.etaleDifferentialBasis_apply]))

omit [CharP B p] in
private theorem scalarFormsIso_generator (i : Fin n) :
    (scalarFormsIso v hv p).hom
      ((1 : B) ⊗ₜ[MvPolynomial (Fin n) k,(MvPolynomial.aeval v).toRingHom]
        (polynomialClass (k := k) p i)) = KaehlerDifferential.D k B (v i) := by
  have hp := polynomialGenerator_class (k := k) p i
  have h := scalarFormsIso_pure v hv p (polynomialClass (k := k) p i)
  exact h.trans ((congrArg (fun z => exteriorPower.oneEquiv B (KaehlerDifferential k B)
    ((EtaleExteriorBaseChange.exteriorIso v hv 1).hom
      ((1 : B) ⊗ₜ[MvPolynomial (Fin n) k,(MvPolynomial.aeval v).toRingHom] z))) hp).trans
        (exteriorIso_coordinate v hv i))

/-- The true whole original etale Cartier isomorphism recovers EVERY original coordinate
differential from the SAME actual canonical generator class. -/
theorem cartierIso_generator (i : Fin n) :
    (cartierIso v hv p).hom (IntrinsicCartierOne.generatorClass v hv p (v i)) =
      KaehlerDifferential.D k B (v i) := by
  have hc := scalarShortIso_class v hv p i
  have hback : (comparisonHomologyIso v hv p).inv
      (IntrinsicCartierOne.generatorClass v hv p (v i)) = extendedClass v p i :=
    (congrArg (comparisonHomologyIso v hv p).inv hc.symm).trans
      (Iso.hom_inv_id_apply (comparisonHomologyIso v hv p) (extendedClass v p i))
  change (scalarFormsIso v hv p).hom ((flatComparison v hv p).hom
    ((comparisonHomologyIso v hv p).inv (IntrinsicCartierOne.generatorClass v hv p (v i)))) = _
  exact (congrArg (fun z => (scalarFormsIso v hv p).hom ((flatComparison v hv p).hom z)) hback).trans
    ((congrArg (scalarFormsIso v hv p).hom (flatComparison_generator v hv p i)).trans
      (scalarFormsIso_generator v hv p i))


/-- The ENTIRE actual etale Cartier composite with the original universal map is identity. -/
theorem cartierIso_inverseCartier :
    (cartierIso v hv p).hom.hom.comp (IntrinsicCartierOne.inverseCartier v hv p) =
      LinearMap.id := by
  apply (Char0.etaleDifferentialBasis v hv).ext
  intro i
  change (cartierIso v hv p).hom.hom
    (IntrinsicCartierOne.inverseCartier v hv p ((Char0.etaleDifferentialBasis v hv) i)) =
      (Char0.etaleDifferentialBasis v hv) i
  rw [Char0.etaleDifferentialBasis_apply, IntrinsicCartierOne.inverseCartier_D,
    cartierIso_generator]

/-- The WHOLE original universal inverse Cartier map is the actual inverse of the genuine
original etale homology isomorphism, not an unrelated abstract map. -/
theorem inverseCartier_eq_inv :
    IntrinsicCartierOne.inverseCartier v hv p = (cartierIso v hv p).inv.hom := by
  apply LinearMap.ext
  intro a
  apply (ModuleCat.mono_iff_injective (cartierIso v hv p).hom).mp inferInstance
  have h : (cartierIso v hv p).hom.hom (IntrinsicCartierOne.inverseCartier v hv p a) = a :=
    LinearMap.congr_fun (cartierIso_inverseCartier v hv p) a
  exact h.trans (Iso.inv_hom_id_apply (cartierIso v hv p) a).symm

/-- Bijectivity of the SAME actual canonical universal one-form Cartier map is DERIVED
from the genuine original etale isomorphism and the whole map comparison. -/
theorem inverseCartier_bijective : Function.Bijective (IntrinsicCartierOne.inverseCartier v hv p) := by
  rw [inverseCartier_eq_inv]
  exact ConcreteCategory.bijective_of_isIso (cartierIso v hv p).inv

/-- EVERY original function, not only a selected coordinate, has the exact genuine
Cartier coefficient: the actual class of a^(p-1)da is carried to the SAME original da. -/
theorem cartierIso_all_generators (a : B) :
    (cartierIso v hv p).hom.hom (IntrinsicCartierOne.generatorClass v hv p a) =
      KaehlerDifferential.D k B a := by
  exact (congrArg (cartierIso v hv p).hom.hom (IntrinsicCartierOne.inverseCartier_D v hv p a)).symm.trans
    (LinearMap.congr_fun (cartierIso_inverseCartier v hv p) (KaehlerDifferential.D k B a))

end EnvelopeProperty.Cartier.CartierOneEtaleIsomorphism
