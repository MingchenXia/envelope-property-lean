import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierOneFunctions
import EnvelopeProperty.Cartier.IntrinsicCartierOneNaturality

/-! # Native relative complex and degree-one Cartier naturality

The actual native twists retain the original base maps and coefficients.
The intervening original algebra map need not be etale or flat.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeEtaleCartierNaturality
open CategoryTheory Limits
universe u

private def twistOver {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    (α : k →+* A) (β : k →+* B) (f : A →+* B) (h : f.comp α = β)
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    RelativeFrobenius.twist α p ⟶ RelativeFrobenius.twist β p := by
  subst β
  exact RelativeEtaleBaseChange.twistMap α f p

private theorem twistOver_coefficient {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    (α : k →+* A) (β : k →+* B) (f : A →+* B) (h : f.comp α = β)
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    RelativeFrobenius.coefficientMap α p ≫ twistOver α β f h p =
      RelativeFrobenius.coefficientMap β p := by
  subst β
  exact RelativeEtaleBaseChange.coefficientMap_twistMap α f p

private theorem twistOver_source {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    (α : k →+* A) (β : k →+* B) (f : A →+* B) (h : f.comp α = β)
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    RelativeFrobenius.sourceMap α p ≫ twistOver α β f h p =
      CommRingCat.ofHom f ≫ RelativeFrobenius.sourceMap β p := by
  subst β
  exact RelativeEtaleBaseChange.sourceMap_twistMap α f p

private theorem twistOver_frobenius {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    (α : k →+* A) (β : k →+* B) (f : A →+* B) (h : f.comp α = β)
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p] [CharP B p] :
    twistOver α β f h p ≫ RelativeFrobenius.map β p =
      RelativeFrobenius.map α p ≫ CommRingCat.ofHom f := by
  subst β
  exact RelativeEtaleBaseChange.twistMap_map α f p

private def mapCycleGeneric {A : Type u} [CommRing A]
    {K L : CochainComplex (ModuleCat.{u} A) ℕ} (φ : K ⟶ L) (q : ℕ)
    (z : LinearMap.ker (K.sc q).g.hom) : LinearMap.ker (L.sc q).g.hom := by
  let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat A) (ComplexShape.up ℕ) q).map φ
  refine ⟨ψ.τ₂ z.val, ?_⟩
  have h := congrArg (fun a : (K.sc q).X₂ ⟶ (L.sc q).X₃ => a z.val) ψ.comm₂₃
  change (L.sc q).g (ψ.τ₂ z.val) = ψ.τ₃ ((K.sc q).g z.val) at h
  exact h.trans ((congrArg ψ.τ₃ z.property).trans (ψ.τ₃.hom.map_zero))

variable {k A B : Type u} [Field k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "TA" => RelativeFrobenius.twist (algebraMap k A) p
local notation "TB" => RelativeFrobenius.twist (algebraMap k B) p

private theorem originalBase_comp : (algebraMap A B).comp (algebraMap k A) = algebraMap k B := by
  ext a
  exact (IsScalarTower.algebraMap_apply k A B a).symm

/-- The original algebra map induces the actual map of native twists, with original base maps. -/
def twistMap : TA ⟶ TB :=
  twistOver (algebraMap k A) (algebraMap k B) (algebraMap A B)
    (originalBase_comp (k := k) (A := A) (B := B)) p

/-- The actual native twist map retains the entire original coefficient inclusion. -/
theorem twistMap_coefficient : RelativeFrobenius.coefficientMap (algebraMap k A) p ≫
    twistMap (k := k) (A := A) (B := B) p = RelativeFrobenius.coefficientMap (algebraMap k B) p :=
  twistOver_coefficient _ _ _ _ p

/-- The actual native twist map preserves the entire original source inclusion. -/
theorem twistMap_source : RelativeFrobenius.sourceMap (algebraMap k A) p ≫
    twistMap (k := k) (A := A) (B := B) p =
      CommRingCat.ofHom (algebraMap A B) ≫ RelativeFrobenius.sourceMap (algebraMap k B) p :=
  twistOver_source _ _ _ _ p

variable [CharP A p] [CharP B p]

/-- The actual native relative Frobenius maps commute with the original algebra map. -/
theorem twistMap_frobenius : twistMap (k := k) (A := A) (B := B) p ≫
    RelativeFrobenius.map (algebraMap k B) p =
      RelativeFrobenius.map (algebraMap k A) p ≫ CommRingCat.ofHom (algebraMap A B) :=
  twistOver_frobenius _ _ _ _ p

private def originalFormMap (q : ℕ) :
    ModuleCat.of A (⋀[A]^q (KaehlerDifferential k A)) ⟶
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B (⋀[B]^q (KaehlerDifferential k B))) :=
  ModuleCat.ofHom (Char0.canonicalDifferentialLinearMap (k := k) (R := A) (A := B) q)

private theorem nativeCoefficientSquare :
    (algebraMap A B).comp (RelativeFrobenius.map (algebraMap k A) p).hom =
      (RelativeFrobenius.map (algebraMap k B) p).hom.comp
        (twistMap (k := k) (A := A) (B := B) p).hom :=
  (congrArg CommRingCat.Hom.hom (twistMap_frobenius (k := k) (A := A) (B := B) p)).symm

/-- Every original canonical exterior map is genuinely linear over the actual native twist map. -/
def formMap (q : ℕ) : RelativeEtaleDeRham.formModule (R := k) (B := A) p q ⟶
    (ModuleCat.restrictScalars (twistMap (k := k) (A := A) (B := B) p).hom).obj
      (RelativeEtaleDeRham.formModule (R := k) (B := B) p q) :=
  (ModuleCat.restrictScalars (RelativeFrobenius.map (algebraMap k A) p).hom).map
      (originalFormMap (k := k) (A := A) (B := B) q) ≫
    (ModuleCat.restrictScalarsComp (RelativeFrobenius.map (algebraMap k A) p).hom
      (algebraMap A B)).inv.app _ ≫
    (ModuleCat.restrictScalarsCongr (nativeCoefficientSquare (k := k) (A := A) (B := B) p)).hom.app _ ≫
    (ModuleCat.restrictScalarsComp (twistMap (k := k) (A := A) (B := B) p).hom
      (RelativeFrobenius.map (algebraMap k B) p).hom).hom.app _

/-- Every original native form has its same entire original canonical pullback. -/
theorem formMap_apply (q : ℕ) (z : RelativeEtaleDeRham.formModule (R := k) (B := A) p q) :
    formMap (k := k) (A := A) (B := B) p q z =
      Char0.canonicalDifferentialLinearMap (k := k) (R := A) (A := B) q z := rfl

variable {n m : ℕ} (v : Fin n → A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := k) w).toRingHom.Etale)
local notation "KA" => RelativeEtaleDeRham.complex v hv p
local notation "KB" => RelativeEtaleDeRham.complex w hw p

/-- The actual original exterior maps give a morphism of the whole native relative complexes. -/
def complexMap : KA ⟶
    ((ModuleCat.restrictScalars (twistMap (k := k) (A := A) (B := B) p).hom).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj KB where
  f q := formMap (k := k) (A := A) (B := B) p q
  comm' q r h := by
    have hr : q+1 = r := h
    subst r
    simp only [RelativeEtaleDeRham.complex, Functor.mapHomologicalComplex_obj_d,
      CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact EtaleDifferentialNaturality.differential_canonicalMap v hv w hw q z

/-- The genuine complex map internally produces a target cycle from every actual source cycle. -/
def imageCycle (q : ℕ) (z : LinearMap.ker ((KA).sc q).g.hom) :
    LinearMap.ker ((KB).sc q).g.hom :=
  let z' := mapCycleGeneric (complexMap p v hv w hw) q z
  ⟨z'.val, z'.property⟩

/-- Every actual image cycle retains the entire original canonical pullback of its value. -/
theorem imageCycle_val (q : ℕ) (z : LinearMap.ker ((KA).sc q).g.hom) :
    (imageCycle p v hv w hw q z).val =
      Char0.canonicalDifferentialLinearMap (k := k) (R := A) (A := B) q z.val := rfl

/-- The actual native homology map, with genuine homology preservation under scalar restriction. -/
def homologyMap (q : ℕ) : (KA).homology q ⟶
    (ModuleCat.restrictScalars (twistMap (k := k) (A := A) (B := B) p).hom).obj ((KB).homology q) :=
  HomologicalComplex.homologyMap (complexMap p v hv w hw) q ≫
    (ModuleComplexNativeCycleClasses.restrictionHomologyIso
      (twistMap (k := k) (A := A) (B := B) p).hom KB q).hom

/-- Every actual source cycle class maps to its internally produced actual target cycle class. -/
theorem homologyMap_cycleClass (q : ℕ) (z : LinearMap.ker ((KA).sc q).g.hom) :
    homologyMap p v hv w hw q (ModuleComplexNativeCycleClasses.cycleClass KA q z) =
      ModuleComplexNativeCycleClasses.cycleClass KB q (imageCycle p v hv w hw q z) := by
  let f := (twistMap (k := k) (A := A) (B := B) p).hom
  let L := ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj KB
  let t := mapCycleGeneric (complexMap p v hv w hw) q z
  have h := ModuleComplexNativeCycleClasses.homologyMap_cycleClass (complexMap p v hv w hw)
    q z t rfl
  exact (congrArg (ModuleComplexNativeCycleClasses.restrictionHomologyIso f KB q).hom h).trans
    (ModuleComplexNativeCycleClasses.restrictionHomologyIso_cycleClass f KB q t
      (imageCycle p v hv w hw q z) rfl)

/-- The actual native homology map preserves every original degree-one generator class. -/
theorem generatorClass_map (a : A) :
    homologyMap p v hv w hw 1 (RelativeEtaleCartierOneFunctions.generatorClass v hv p a) =
      RelativeEtaleCartierOneFunctions.generatorClass w hw p (algebraMap A B a) := by
  have hc : imageCycle p v hv w hw 1 (RelativeEtaleCartierOneFunctions.generatorCycle v hv p a) =
      RelativeEtaleCartierOneFunctions.generatorCycle w hw p (algebraMap A B a) := by
    apply Subtype.ext
    exact IntrinsicCartierOneNaturality.generatorForm_map p a
  exact (homologyMap_cycleClass p v hv w hw 1
    (RelativeEtaleCartierOneFunctions.generatorCycle v hv p a)).trans
    (congrArg (ModuleComplexNativeCycleClasses.cycleClass KB 1) hc)

attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra

omit [CharP A p] [CharP B p] in
/-- The actual coefficient triangle gives the genuine scalar tower on the native twists. -/
theorem coefficient_scalarTower :
    let := (twistMap (k := k) (A := A) (B := B) p).hom.toAlgebra
    IsScalarTower k TA TB := by
  let := (twistMap (k := k) (A := A) (B := B) p).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  exact (congrArg CommRingCat.Hom.hom (twistMap_coefficient (k := k) (A := A) (B := B) p)).symm

omit [CharP A p] [CharP B p] in
/-- The actual native cotangent map over the unchanged original coefficient inclusion. -/
def cotangentMap : ModuleCat.of TA (KaehlerDifferential k TA) ⟶
    (ModuleCat.restrictScalars (twistMap (k := k) (A := A) (B := B) p).hom).obj
      (ModuleCat.of TB (KaehlerDifferential k TB)) := by
  let := (twistMap (k := k) (A := A) (B := B) p).hom.toAlgebra
  let := coefficient_scalarTower (k := k) (A := A) (B := B) p
  exact ModuleCat.ofHom
    { toFun := fun z => KaehlerDifferential.map k k TA TB z
      map_add' := (KaehlerDifferential.map k k TA TB).map_add
      map_smul' := fun a z => ((KaehlerDifferential.map k k TA TB).map_smul a z).trans
        (IsScalarTower.algebraMap_smul TB a _).symm }

omit [CharP A p] [CharP B p] in
/-- Every actual source differential has its same actual native target differential. -/
theorem cotangentMap_D (t : TA) : cotangentMap (k := k) (A := A) (B := B) p
    (KaehlerDifferential.D k TA t) =
      KaehlerDifferential.D k TB ((twistMap (k := k) (A := A) (B := B) p).hom t) := by
  let := (twistMap (k := k) (A := A) (B := B) p).hom.toAlgebra
  let := coefficient_scalarTower (k := k) (A := A) (B := B) p
  exact KaehlerDifferential.map_D k k TA TB t

/-- The whole native degree-one Cartier equivalence is natural for every original algebra map. -/
theorem inverseCartierOne_naturality :
    ModuleCat.ofHom (RelativeEtaleCartierOneFunctions.inverseCartierOneEquiv v hv p).toLinearMap ≫
      homologyMap p v hv w hw 1 =
    cotangentMap (k := k) (A := A) (B := B) p ≫
      (ModuleCat.restrictScalars (twistMap (k := k) (A := A) (B := B) p).hom).map
        (ModuleCat.ofHom (RelativeEtaleCartierOneFunctions.inverseCartierOneEquiv w hw p).toLinearMap) := by
  apply ModuleCat.hom_ext
  apply (RelativeEtaleCartierDomain.cotangentBasis v hv p).ext
  intro i
  change homologyMap p v hv w hw 1
      (RelativeEtaleCartierOneFunctions.inverseCartierOneEquiv v hv p
        (RelativeEtaleCartierDomain.cotangentBasis v hv p i)) =
    RelativeEtaleCartierOneFunctions.inverseCartierOneEquiv w hw p
      (cotangentMap (k := k) (A := A) (B := B) p
        (RelativeEtaleCartierDomain.cotangentBasis v hv p i))
  rw [RelativeEtaleCartierDomain.cotangentBasis_D,
    RelativeEtaleCartierOneFunctions.inverseCartierOneEquiv_D_source, cotangentMap_D]
  have hs := congrArg (fun f : CommRingCat.of A ⟶ TB => f.hom (v i))
    (twistMap_source (k := k) (A := A) (B := B) p)
  change (twistMap (k := k) (A := A) (B := B) p).hom
    ((RelativeFrobenius.sourceMap (algebraMap k A) p).hom (v i)) =
      (RelativeFrobenius.sourceMap (algebraMap k B) p).hom (algebraMap A B (v i)) at hs
  rw [hs, RelativeEtaleCartierOneFunctions.inverseCartierOneEquiv_D_source]
  exact generatorClass_map p v hv w hw (v i)

end EnvelopeProperty.Cartier.RelativeEtaleCartierNaturality
