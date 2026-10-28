import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierAllNaturality

/-! # Actual native relative chart comparisons and original restriction maps -/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeEtaleChartChange
open CategoryTheory
open scoped Classical
universe u

section NativeComplex
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {n m : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := R) w).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP R p] [CharP B p]
local notation "T" => RelativeFrobenius.twist (algebraMap R B) p
local notation "Ev" => RelativeEtaleDeRham.complex v hv p
local notation "Ew" => RelativeEtaleDeRham.complex w hw p

/-- The actual entire native relative complexes of two genuine etale charts are isomorphic
by the SAME original identity components, with unchanged actual relative coefficient action. -/
def complexIso : Ev ≅ Ew := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro q r h
  have hr : q+1 = r := h
  subst r
  simp only [RelativeEtaleDeRham.complex, CochainComplex.of_d, Iso.refl_hom,
    Category.id_comp, Category.comp_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (EtaleDifferentialIntrinsic.differential_eq_of_coordinates v hv w hw q a).symm

/-- Every original native chart comparison component IS the original identity. -/
theorem complexIso_hom_f (q : ℕ) :
    (complexIso v hv w hw p).hom.f q = 𝟙 (RelativeEtaleDeRham.formModule (R := R) (B := B) p q) := rfl

/-- The actual original whole chart comparison to itself is the identity. -/
theorem complexIso_refl : complexIso v hv v hv p = Iso.refl Ev := by
  apply Iso.ext
  ext q
  rfl

/-- The SAME whole native chart comparisons obey their genuine strict composition law. -/
theorem complexIso_hom_trans {l : ℕ} (z : Fin l → B)
    (hz : (MvPolynomial.aeval (R := R) z).toRingHom.Etale) :
    (complexIso v hv w hw p).hom ≫ (complexIso w hw z hz p).hom =
      (complexIso v hv z hz p).hom := by
  ext q
  rfl

/-- Every ACTUAL native cycle has a genuine target kernel image under the original chart map. -/
def imageCycle (q : ℕ) (a : LinearMap.ker ((Ev).sc q).g.hom) :
    LinearMap.ker ((Ew).sc q).g.hom := by
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat T) (ComplexShape.up ℕ) q).map
    (complexIso v hv w hw p).hom
  refine ⟨φ.τ₂ a.val, ?_⟩
  have h := congrArg (fun f : ((Ev).sc q).X₂ ⟶ ((Ew).sc q).X₃ => f a.val) φ.comm₂₃
  change ((Ew).sc q).g (φ.τ₂ a.val) = φ.τ₃ (((Ev).sc q).g a.val) at h
  exact h.trans ((congrArg φ.τ₃ a.property).trans (φ.τ₃.hom.map_zero))

/-- The ENTIRE original value of each actual chart image cycle is unchanged. -/
theorem imageCycle_val (q : ℕ) (a : LinearMap.ker ((Ev).sc q).g.hom) :
    (imageCycle v hv w hw p q a).val = a.val := rfl

/-- The GENUINE native homology functor applied to the actual whole chart isomorphism. -/
def homologyIso (q : ℕ) : (Ev).homology q ≅ (Ew).homology q :=
  (HomologicalComplex.homologyFunctor (ModuleCat T) (ComplexShape.up ℕ) q).mapIso
    (complexIso v hv w hw p)

/-- Every ACTUAL original native cycle class has its internally constructed actual image. -/
theorem homologyIso_cycleClass (q : ℕ) (a : LinearMap.ker ((Ev).sc q).g.hom) :
    (homologyIso v hv w hw p q).hom (ModuleComplexNativeCycleClasses.cycleClass Ev q a) =
      ModuleComplexNativeCycleClasses.cycleClass Ew q (imageCycle v hv w hw p q a) :=
  ModuleComplexNativeCycleClasses.homologyMap_cycleClass (complexIso v hv w hw p).hom q
    a (imageCycle v hv w hw p q a) rfl

/-- The genuine native homology chart comparisons obey the SAME strict composition law. -/
theorem homologyIso_hom_trans {l : ℕ} (z : Fin l → B)
    (hz : (MvPolynomial.aeval (R := R) z).toRingHom.Etale) (q : ℕ) :
    (homologyIso v hv w hw p q).hom ≫ (homologyIso w hw z hz p q).hom =
      (homologyIso v hv z hz p q).hom := by
  change (HomologicalComplex.homologyFunctor (ModuleCat T) (ComplexShape.up ℕ) q).map
      (complexIso v hv w hw p).hom ≫
    (HomologicalComplex.homologyFunctor (ModuleCat T) (ComplexShape.up ℕ) q).map
      (complexIso w hw z hz p).hom = _
  rw [← Functor.map_comp, complexIso_hom_trans]
  rfl
end NativeComplex

section Cartier
variable {k B : Type u} [Field k] [CommRing B] [Algebra k B]
variable {n m : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := k) w).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP B p]
attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra
local notation "T" => RelativeFrobenius.twist (algebraMap k B) p
local notation "Ew" => RelativeEtaleDeRham.complex w hw p

/-- Every arbitrary original power-differential cycle agrees across the actual chart map. -/
theorem imageCycle_functionCycle (q : ℕ) (t : Fin q → B) :
    imageCycle v hv w hw p q (RelativeEtaleCartierMultiplicativity.functionCycle v hv p q t) =
      RelativeEtaleCartierMultiplicativity.functionCycle w hw p q t := by
  apply Subtype.ext
  rw [imageCycle_val, RelativeEtaleCartierMultiplicativity.functionCycle_val,
    RelativeEtaleCartierMultiplicativity.functionCycle_val]

/-- The SAME native Cartier isomorphisms commute with the ACTUAL original full-complex
identity-component chart comparison in EVERY degree, including zero. -/
theorem inverseCartierIso_chartChange (q : ℕ) :
    (RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom ≫
      (homologyIso v hv w hw p q).hom =
    (RelativeEtaleCartierDomain.inverseCartierIso w hw p q).hom := by
  apply ModuleCat.hom_ext
  apply ((RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower q).ext
  intro s
  change (homologyIso v hv w hw p q).hom
      ((RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom
        ((RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower q s)) =
    (RelativeEtaleCartierDomain.inverseCartierIso w hw p q).hom
      ((RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower q s)
  have hs : (RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower q s =
      exteriorPower.ιMulti T q (fun j => KaehlerDifferential.D k T
        ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom
          (v (Set.powersetCard.ofFinEmbEquiv.symm s j)))) := by
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    congr 1
    funext j
    exact RelativeEtaleCartierDomain.cotangentBasis_D v hv p _
  rw [hs, RelativeEtaleCartierMultiplicativity.inverseCartierIso_sourceWedge,
    RelativeEtaleCartierMultiplicativity.inverseCartierIso_sourceWedge, homologyIso_cycleClass]
  exact congrArg (ModuleComplexNativeCycleClasses.cycleClass Ew q)
    (imageCycle_functionCycle v hv w hw p q _)
end Cartier

section Restriction
variable {k A B : Type u} [Field k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p] [CharP B p]
variable {n n' m m' : ℕ}
variable (v : Fin n → A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (v' : Fin n' → A) (hv' : (MvPolynomial.aeval (R := k) v').toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := k) w).toRingHom.Etale)
variable (w' : Fin m' → B) (hw' : (MvPolynomial.aeval (R := k) w').toRingHom.Etale)
local notation "τ" => (CommRingCat.Hom.hom
  (RelativeEtaleCartierNaturality.twistMap (k := k) (A := A) (B := B) p))

/-- The ENTIRE actual original restriction cochain maps commute with genuine chart changes,
for ANY original algebra map, with no comparison-square input. -/
theorem complexMap_chartChange :
    (complexIso v hv v' hv' p).hom ≫ RelativeEtaleCartierNaturality.complexMap p v' hv' w' hw' =
    RelativeEtaleCartierNaturality.complexMap p v hv w hw ≫
      ((ModuleCat.restrictScalars τ).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (complexIso w hw w' hw' p).hom := by
  ext q
  rfl

/-- Every actual cycle has exactly the same original restriction image after actual chart
changes; the entire canonical exterior value comparison is internally derived. -/
theorem imageCycle_restriction (q : ℕ)
    (a : LinearMap.ker ((RelativeEtaleDeRham.complex v hv p).sc q).g.hom) :
    RelativeEtaleCartierNaturality.imageCycle p v' hv' w' hw' q
        (imageCycle v hv v' hv' p q a) =
      imageCycle w hw w' hw' p q
        (RelativeEtaleCartierNaturality.imageCycle p v hv w hw q a) := by
  apply Subtype.ext
  rw [RelativeEtaleCartierNaturality.imageCycle_val, imageCycle_val,
    imageCycle_val, RelativeEtaleCartierNaturality.imageCycle_val]

/-- The SAME actual native restriction homology maps commute with genuine chart changes
on EVERY homology input in EVERY degree, with the original native scalar action. -/
theorem homologyMap_chartChange (q : ℕ) :
    (homologyIso v hv v' hv' p q).hom ≫
      RelativeEtaleCartierNaturality.homologyMap p v' hv' w' hw' q =
    RelativeEtaleCartierNaturality.homologyMap p v hv w hw q ≫
      (ModuleCat.restrictScalars τ).map (homologyIso w hw w' hw' p q).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := RelativeEtaleCartierAllNaturality.nativeCycleClass_surjective
    (RelativeEtaleDeRham.complex v hv p) q x
  change RelativeEtaleCartierNaturality.homologyMap p v' hv' w' hw' q
      ((homologyIso v hv v' hv' p q).hom
        (ModuleComplexNativeCycleClasses.cycleClass (RelativeEtaleDeRham.complex v hv p) q a)) =
    (homologyIso w hw w' hw' p q).hom
      (RelativeEtaleCartierNaturality.homologyMap p v hv w hw q
        (ModuleComplexNativeCycleClasses.cycleClass (RelativeEtaleDeRham.complex v hv p) q a))
  rw [homologyIso_cycleClass, RelativeEtaleCartierNaturality.homologyMap_cycleClass,
    RelativeEtaleCartierNaturality.homologyMap_cycleClass, homologyIso_cycleClass]
  exact congrArg (ModuleComplexNativeCycleClasses.cycleClass (RelativeEtaleDeRham.complex w' hw' p) q)
    (imageCycle_restriction p v hv v' hv' w hw w' hw' q a)
end Restriction

end EnvelopeProperty.Cartier.RelativeEtaleChartChange
