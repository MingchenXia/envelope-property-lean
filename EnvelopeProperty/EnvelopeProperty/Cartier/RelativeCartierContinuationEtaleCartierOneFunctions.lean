import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierRepresentatives
import EnvelopeProperty.Cartier.IntrinsicCartierOne

/-! # Native relative Cartier classes of original functions

The original integral primitive and Frobenius Leibniz identity are used only
as equalities of original forms. Every class below lies in the actual native
relative whole complex, with its unchanged coefficient inclusion.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeEtaleCartierOneFunctions
open CategoryTheory Limits
open scoped TensorProduct ChangeOfRings Classical
universe u

private theorem nativeClass_of_boundary {A : Type u} [CommRing A]
    (K : CochainComplex (ModuleCat A) ℕ) (i j : ℕ)
    (z : LinearMap.ker (K.sc j).g.hom) (w : K.X i)
    (hzw : z.val = K.d i j w) :
    ModuleComplexNativeCycleClasses.cycleClass K j z = 0 := by
  have hc : (K.sc j).moduleCatCyclesIso.inv z = K.toCycles i j w := by
    apply (ModuleCat.mono_iff_injective (K.iCycles j)).mp inferInstance
    have ht := congrArg (fun f : K.X i ⟶ K.X j => f w) (K.toCycles_i i j)
    change K.iCycles j (K.toCycles i j w) = K.d i j w at ht
    exact ((K.sc j).moduleCatCyclesIso_inv_iCycles_apply z).trans (hzw.trans ht.symm)
  have hz := congrArg (fun f : K.X i ⟶ K.homology j => f w)
    (K.toCycles_comp_homologyπ i j)
  change K.homologyπ j (K.toCycles i j w) = 0 at hz
  exact (congrArg (K.homologyπ j) hc).trans hz

private theorem consecutive_apply {A : Type u} [CommRing A]
    (X : ℕ → ModuleCat A) (d : ∀ q, X q ⟶ X (q+1))
    (sq : ∀ q, d q ≫ d (q+1) = 0) (q : ℕ) (w : X q) :
    (CochainComplex.of X d sq).d q (q+1) w = d q w := by
  change CochainComplex.of.d X d q (q+1) w = d q w
  rw [CochainComplex.of_d]

variable {k B : Type u} [Field k] [CommRing B] [Algebra k B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP B p]
local notation "TB" => RelativeFrobenius.twist (algebraMap k B) p
local notation "KB" => RelativeEtaleDeRham.complex v hv p
local notation "P" => MvPolynomial (Fin n) k
local notation "TP" => RelativeFrobenius.twist (algebraMap k P) p
attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra

private theorem nativeSquare (q : ℕ) :
    RelativeEtaleDeRham.differential v hv p q ≫
      RelativeEtaleDeRham.differential v hv p (q+1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  exact EtaleDeRham.differential_square v hv q w

/-- Every original function gives its actual native closed Cartier generator. -/
def generatorCycle (b : B) : LinearMap.ker ((KB).sc 1).g.hom :=
  ModuleComplexNativeCycleClasses.ofCycle _ _ (nativeSquare v hv p) 1
    ⟨IntrinsicCartierOne.generatorForm (R := k) p b,
      (IntrinsicCartierOne.generatorCycle v hv p b).property⟩

/-- Its entire value is the SAME original form b^(p-1) db. -/
theorem generatorCycle_val (b : B) : (generatorCycle v hv p b).val =
    (show RelativeEtaleDeRham.formModule (R := k) (B := B) p 1 from
      b^(p-1) • (exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm
        (KaehlerDifferential.D k B b)) := rfl

/-- The actual native whole-complex class of the original Cartier generator. -/
def generatorClass (b : B) : ((KB).homology 1) :=
  RelativeEtaleNativeClasses.nativeCycleClassLinear v hv p 1 (generatorCycle v hv p b)

private def boundaryCycle (w : RelativeEtaleDeRham.formModule (R := k) (B := B) p 0) :
    LinearMap.ker ((KB).sc 1).g.hom :=
  ModuleComplexNativeCycleClasses.ofCycle _ _ (nativeSquare v hv p) 1
    ⟨(RelativeEtaleDeRham.differential v hv p 0).hom w,
      EtaleDeRham.differential_square v hv 0 w⟩

private theorem boundaryClass_zero
    (w : RelativeEtaleDeRham.formModule (R := k) (B := B) p 0) :
    RelativeEtaleNativeClasses.nativeCycleClassLinear v hv p 1 (boundaryCycle v hv p w) = 0 :=
  nativeClass_of_boundary KB 0 1 (boundaryCycle v hv p w) w
    (consecutive_apply _ _ (nativeSquare v hv p) 0 w).symm

/-- The integral primitive proves additivity in the SAME actual native relative H¹. -/
theorem generatorClass_add (a b : B) :
    generatorClass v hv p (a+b) = generatorClass v hv p a + generatorClass v hv p b := by
  let w : RelativeEtaleDeRham.formModule (R := k) (B := B) p 0 :=
    (exteriorPower.zeroEquiv B (KaehlerDifferential k B)).symm
      (CartierAdditivePrimitive.primitive p a b)
  have hc : generatorCycle v hv p (a+b) - generatorCycle v hv p a - generatorCycle v hv p b =
      boundaryCycle v hv p w := by
    apply Subtype.ext
    have h := congrArg Subtype.val (IntrinsicCartierOne.generatorCycle_add_difference v hv p a b)
    exact h
  have h := (congrArg (RelativeEtaleNativeClasses.nativeCycleClassLinear v hv p 1) hc).trans
    (boundaryClass_zero v hv p w)
  simp only [map_sub] at h
  change generatorClass v hv p (a+b) - generatorClass v hv p a - generatorClass v hv p b = 0 at h
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp h)).trans (add_comm _ _)

/-- The source inclusion gives the genuine Frobenius Leibniz identity in native H¹. -/
theorem generatorClass_mul (a b : B) :
    generatorClass v hv p (a*b) =
      (RelativeFrobenius.sourceMap (algebraMap k B) p).hom a • generatorClass v hv p b +
      (RelativeFrobenius.sourceMap (algebraMap k B) p).hom b • generatorClass v hv p a := by
  have hc : generatorCycle v hv p (a*b) =
      (RelativeFrobenius.sourceMap (algebraMap k B) p).hom a • generatorCycle v hv p b +
      (RelativeFrobenius.sourceMap (algebraMap k B) p).hom b • generatorCycle v hv p a := by
    apply Subtype.ext
    have h := congrArg Subtype.val (IntrinsicCartierOne.generatorCycle_mul v hv p a b)
    change IntrinsicCartierOne.generatorForm (R := k) p (a*b) =
      a^p • IntrinsicCartierOne.generatorForm (R := k) p b +
        b^p • IntrinsicCartierOne.generatorForm (R := k) p a at h
    change (show RelativeEtaleDeRham.formModule (R := k) (B := B) p 1 from
      IntrinsicCartierOne.generatorForm (R := k) p (a*b)) =
      (RelativeFrobenius.sourceMap (algebraMap k B) p).hom a •
        (show RelativeEtaleDeRham.formModule (R := k) (B := B) p 1 from
          IntrinsicCartierOne.generatorForm (R := k) p b) +
      (RelativeFrobenius.sourceMap (algebraMap k B) p).hom b •
        (show RelativeEtaleDeRham.formModule (R := k) (B := B) p 1 from
          IntrinsicCartierOne.generatorForm (R := k) p a)
    rw [RelativeEtaleDeRham.source_smul, RelativeEtaleDeRham.source_smul]
    exact h
  exact (congrArg (RelativeEtaleNativeClasses.nativeCycleClassLinear v hv p 1) hc).trans
    (by rw [map_add, map_smul, map_smul]; rfl)

/-- Every original base coefficient has zero actual native generator class. -/
theorem generatorClass_algebraMap (a : k) : generatorClass v hv p (algebraMap k B a) = 0 := by
  have hc : generatorCycle v hv p (algebraMap k B a) = 0 := by
    apply Subtype.ext
    change IntrinsicCartierOne.generatorForm (R := k) p (algebraMap k B a) = 0
    simp only [IntrinsicCartierOne.generatorForm, Derivation.map_algebraMap, map_zero, smul_zero]
  exact (congrArg (RelativeEtaleNativeClasses.nativeCycleClassLinear v hv p 1) hc).trans
    (RelativeEtaleNativeClasses.nativeCycleClassLinear v hv p 1).map_zero

/-- The actual native degree-one Cartier equivalence on the original cotangent module. -/
def inverseCartierOneEquiv : KaehlerDifferential k TB ≃ₗ[TB] ((KB).homology 1) :=
  (exteriorPower.oneEquiv TB (KaehlerDifferential k TB)).symm.trans
    (RelativeEtaleCartierDomain.inverseCartierIso v hv p 1).toLinearEquiv

private def generatorDerivation :
    letI : Module B ((KB).homology 1) := Module.compHom ((KB).homology 1) (RelativeFrobenius.sourceMap (algebraMap k B) p).hom
    letI : Module k ((KB).homology 1) := Module.compHom ((KB).homology 1) (algebraMap k B)
    Derivation k B ((KB).homology 1) := by
  letI : Module B ((KB).homology 1) := Module.compHom ((KB).homology 1) (RelativeFrobenius.sourceMap (algebraMap k B) p).hom
  letI : Module k ((KB).homology 1) := Module.compHom ((KB).homology 1) (algebraMap k B)
  exact
    { toFun := generatorClass v hv p
      map_add' := generatorClass_add v hv p
      map_smul' := fun a b => by
        rw [Algebra.smul_def]
        change generatorClass v hv p ((algebraMap k B a)*b) =
          (RelativeFrobenius.sourceMap (algebraMap k B) p).hom (algebraMap k B a) •
            generatorClass v hv p b
        rw [generatorClass_mul, generatorClass_algebraMap, smul_zero, add_zero]
      map_one_eq_zero' := by
        change generatorClass v hv p (1 : B) = 0
        simpa only [map_one] using generatorClass_algebraMap v hv p (1 : k)
      leibniz' := generatorClass_mul v hv p }

private theorem oneEquiv_basis_singleton {R V I : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [LinearOrder I] (b : Module.Basis I R V) (i : I) :
    exteriorPower.oneEquiv R V
      (b.exteriorPower 1 (Set.powersetCard.ofCard (Finset.card_singleton i))) = b i := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.oneEquiv_ιMulti]
  dsimp only [Function.comp_apply]
  congr 1
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  exact Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ _ _)

omit [Fact p.Prime] [CharP k p] [CharP B p] in
private theorem polynomialFormMap_generator (i : Fin n) :
    EtaleDeRham.polynomialFormMap v hv 1
      (IntrinsicCartierOne.generatorForm (R := k) p (MvPolynomial.X i : P)) =
      IntrinsicCartierOne.generatorForm (R := k) p (v i) := by
  let s : Set.powersetCard (Fin n) 1 := Set.powersetCard.ofCard (Finset.card_singleton i)
  have hb : (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower 1 s =
      (exteriorPower.oneEquiv P (KaehlerDifferential k P)).symm
        (KaehlerDifferential.D k P (MvPolynomial.X i)) := by
    apply (exteriorPower.oneEquiv P (KaehlerDifferential k P)).injective
    exact (oneEquiv_basis_singleton (KaehlerDifferential.mvPolynomialBasis k (Fin n)) i).trans
      ((KaehlerDifferential.mvPolynomialBasis_apply k (Fin n) i).trans
        (LinearEquiv.apply_symm_apply _ _).symm)
  have hc : (Char0.etaleDifferentialBasis v hv).exteriorPower 1 s =
      (exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm
        (KaehlerDifferential.D k B (v i)) := by
    apply (exteriorPower.oneEquiv B (KaehlerDifferential k B)).injective
    exact (oneEquiv_basis_singleton (Char0.etaleDifferentialBasis v hv) i).trans
      ((Char0.etaleDifferentialBasis_apply v hv i).trans (LinearEquiv.apply_symm_apply _ _).symm)
  rw [IntrinsicCartierOne.generatorForm, ← hb, EtaleDeRham.polynomialFormMap_smul_basis,
    map_pow, MvPolynomial.aeval_X, hc]
  rfl

private theorem polynomialNativeGenerator_val (i : Fin n) :
    (RelativePolynomialCartier.nativeCycle k p n 1
      ((exteriorPower.oneEquiv TP (KaehlerDifferential k TP)).symm
        (RelativePolynomialCartier.twistBasis k p n i))).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := P) p 1 from
        IntrinsicCartierOne.generatorForm (R := k) p (MvPolynomial.X i)) := by
  change RelativePolynomialCartier.originalExteriorRepresentative k p n 1
      ((exteriorPower.oneEquiv TP (KaehlerDifferential k TP)).symm
        (RelativePolynomialCartier.twistBasis k p n i)) = _
  rw [RelativePolynomialCartier.oneRepresentative_exterior,
    RelativePolynomialCartier.twistBasis_apply, RelativePolynomialCartier.oneRepresentative_D,
    RelativePolynomialCartier.oneCoordinateCycle_val]
  rfl

omit [CharP B p] in
private theorem exteriorIso_one (w : KaehlerDifferential k TP) :
    letI := (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
    (RelativeEtaleCartierDomain.exteriorIso v hv p 1).hom
      ((1 : TB) ⊗ₜ[TP] (exteriorPower.oneEquiv TP (KaehlerDifferential k TP)).symm w) =
      (exteriorPower.oneEquiv TB (KaehlerDifferential k TB)).symm
        ((RelativeEtaleCartierDomain.cotangentIso v hv p).hom ((1 : TB) ⊗ₜ[TP] w)) := by
  let := (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
  change (RelativeEtaleCartierDomain.exteriorIso v hv p 1).hom
      ((1 : TB) ⊗ₜ[TP] exteriorPower.ιMulti TP 1 (fun _ => w)) =
    exteriorPower.ιMulti TB 1 (fun _ =>
      (RelativeEtaleCartierDomain.cotangentIso v hv p).hom ((1 : TB) ⊗ₜ[TP] w))
  exact RelativeEtaleCartierDomain.exteriorIso_wedge v hv p 1 (fun _ => w)

omit [CharP B p] in
private theorem cotangentIso_basis (i : Fin n) :
    letI := (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
    (RelativeEtaleCartierDomain.cotangentIso v hv p).hom
      ((1 : TB) ⊗ₜ[TP] RelativePolynomialCartier.twistBasis k p n i) =
      RelativeEtaleCartierDomain.cotangentBasis v hv p i := by
  let := (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
  let := RelativeEtaleCartierDomain.coefficient_scalarTower (k := k) v p
  have h := RelativeEtaleCartierDomain.cotangentIso_tmul v hv p (1 : TB)
    (RelativePolynomialCartier.twistBasis k p n i)
  exact (h.trans (one_smul TB _)).trans
    (RelativeEtaleCartierDomain.cotangentBasis_apply v hv p i).symm

/-- The actual native equivalence has the specified original class on every chart coordinate. -/
theorem inverseCartierOneEquiv_coordinate (i : Fin n) :
    inverseCartierOneEquiv v hv p
      (KaehlerDifferential.D k TB ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom (v i))) =
      generatorClass v hv p (v i) := by
  let := (RelativeEtaleComplexBaseChange.chartTwistMap (k := k) v p).hom.toAlgebra
  let w := (exteriorPower.oneEquiv TP (KaehlerDifferential k TP)).symm
    (RelativePolynomialCartier.twistBasis k p n i)
  have he := exteriorIso_one v hv p (RelativePolynomialCartier.twistBasis k p n i)
  have he' := he.trans (congrArg (exteriorPower.oneEquiv TB (KaehlerDifferential k TB)).symm
    ((cotangentIso_basis v hv p i).trans (RelativeEtaleCartierDomain.cotangentBasis_D v hv p i)))
  have hc := RelativeEtaleCartierRepresentatives.inverseCartierIso_tmul_class v hv p 1 (1 : TB) w
  have hz : RelativeEtaleCartierRepresentatives.nativeCycle v hv p 1 (1 : TB) w =
      generatorCycle v hv p (v i) := by
    apply Subtype.ext
    have h := RelativeEtaleNativeClasses.etaleCycle_one_val v hv p 1
      (RelativePolynomialCartier.nativeCycle k p n 1 w)
    exact h.trans ((congrArg (EtaleDeRham.polynomialFormMap v hv 1)
      (polynomialNativeGenerator_val (k := k) p i)).trans (polynomialFormMap_generator v hv p i))
  change (RelativeEtaleCartierDomain.inverseCartierIso v hv p 1).hom
      ((exteriorPower.oneEquiv TB (KaehlerDifferential k TB)).symm
        (KaehlerDifferential.D k TB ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom (v i)))) =
    ModuleComplexNativeCycleClasses.cycleClass KB 1 (generatorCycle v hv p (v i))
  exact ((congrArg (RelativeEtaleCartierDomain.inverseCartierIso v hv p 1).hom he').symm.trans hc).trans
    (congrArg (ModuleComplexNativeCycleClasses.cycleClass KB 1) hz)

omit [CharP B p] in
private theorem source_algebraMap (a : k) :
    (RelativeFrobenius.sourceMap (algebraMap k B) p).hom (algebraMap k B a) =
      algebraMap k TB (a^p) := by
  have h := congrArg (fun f : CommRingCat.of k ⟶ TB => f.hom a)
    (pushout.condition (f := CommRingCat.ofHom (frobenius k p))
      (g := CommRingCat.ofHom (algebraMap k B)))
  exact h.symm

private def cartierSource (b : B) : (KB).homology 1 :=
  inverseCartierOneEquiv v hv p
    (KaehlerDifferential.D k TB ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom b))

private theorem cartierSource_add (a b : B) :
    cartierSource v hv p (a+b) = cartierSource v hv p a + cartierSource v hv p b := by
  unfold cartierSource
  rw [map_add, map_add, map_add]

private theorem cartierSource_mul (a b : B) :
    cartierSource v hv p (a*b) =
      (RelativeFrobenius.sourceMap (algebraMap k B) p).hom a • cartierSource v hv p b +
      (RelativeFrobenius.sourceMap (algebraMap k B) p).hom b • cartierSource v hv p a := by
  unfold cartierSource
  rw [map_mul, Derivation.leibniz, map_add, map_smul, map_smul]

private theorem cartierSource_algebraMap (a : k) : cartierSource v hv p (algebraMap k B a) = 0 := by
  unfold cartierSource
  rw [source_algebraMap, Derivation.map_algebraMap, map_zero]

private def cartierSourceDerivation :
    letI : Module B ((KB).homology 1) := Module.compHom ((KB).homology 1) (RelativeFrobenius.sourceMap (algebraMap k B) p).hom
    letI : Module k ((KB).homology 1) := Module.compHom ((KB).homology 1) (algebraMap k B)
    Derivation k B ((KB).homology 1) := by
  letI : Module B ((KB).homology 1) := Module.compHom ((KB).homology 1) (RelativeFrobenius.sourceMap (algebraMap k B) p).hom
  letI : Module k ((KB).homology 1) := Module.compHom ((KB).homology 1) (algebraMap k B)
  exact
    { toFun := cartierSource v hv p
      map_add' := cartierSource_add v hv p
      map_smul' := fun a b => by
        rw [Algebra.smul_def]
        change cartierSource v hv p ((algebraMap k B a)*b) =
          (RelativeFrobenius.sourceMap (algebraMap k B) p).hom (algebraMap k B a) •
            cartierSource v hv p b
        rw [cartierSource_mul, cartierSource_algebraMap, smul_zero, add_zero]
      map_one_eq_zero' := by
        change cartierSource v hv p (1 : B) = 0
        simpa only [map_one] using cartierSource_algebraMap v hv p (1 : k)
      leibniz' := cartierSource_mul v hv p }

/-- EVERY original function has its specified actual native relative Cartier class. -/
theorem inverseCartierOneEquiv_D_source (b : B) :
    inverseCartierOneEquiv v hv p
      (KaehlerDifferential.D k TB ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom b)) =
      ModuleComplexNativeCycleClasses.cycleClass KB 1 (generatorCycle v hv p b) := by
  change cartierSource v hv p b = generatorClass v hv p b
  let : Module B ((KB).homology 1) := Module.compHom ((KB).homology 1) (RelativeFrobenius.sourceMap (algebraMap k B) p).hom
  let : Module k ((KB).homology 1) := Module.compHom ((KB).homology 1) (algebraMap k B)
  let : IsScalarTower k B ((KB).homology 1) := IsScalarTower.of_compHom k B ((KB).homology 1)
  have hl : (cartierSourceDerivation v hv p).liftKaehlerDifferential =
      (generatorDerivation v hv p).liftKaehlerDifferential := by
    apply (Char0.etaleDifferentialBasis v hv).ext
    intro i
    rw [Char0.etaleDifferentialBasis_apply, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact inverseCartierOneEquiv_coordinate v hv p i
  have h := congrArg
    (fun f : KaehlerDifferential k B →ₗ[B] ((KB).homology 1) => f (KaehlerDifferential.D k B b)) hl
  simp only [Derivation.liftKaehlerDifferential_comp_D] at h
  change cartierSource v hv p b = generatorClass v hv p b at h
  exact h

end EnvelopeProperty.Cartier.RelativeEtaleCartierOneFunctions
