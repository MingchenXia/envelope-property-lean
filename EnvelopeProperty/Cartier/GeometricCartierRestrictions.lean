import EnvelopeProperty.Cartier.GeometricHomologyNaturality
import EnvelopeProperty.Cartier.RelativeCartierContinuationNativeAllAlgebraNaturality

/-! # Actual Cartier overlap squares from original cycle and unit restriction -/
noncomputable section
namespace EnvelopeProperty.Cartier.GeometricCartierRestrictions
open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
universe u

private theorem preimage_restrict {X Y : Scheme.{u}} (g : X ⟶ Y)
    {U V : Y.Opens} {U' V' : X.Opens} (i : U ⟶ V) (j : U' ⟶ V')
    (hU : g ⁻¹ᵁ U = U') (hV : g ⁻¹ᵁ V = V') (M : X.Modules) (s : Γ(M, V')) :
    M.presheaf.map ((Opens.map g.base).map i).op
        (M.presheaf.map (eqToHom hV).op s) =
      M.presheaf.map (eqToHom hU).op (M.presheaf.map j.op s) :=
  (ConcreteCategory.congr_hom
    (M.presheaf.map_comp (eqToHom hV).op ((Opens.map g.base).map i).op) s).symm.trans
    ((congrArg (fun a => M.presheaf.map a s)
      (show (eqToHom hV).op ≫ ((Opens.map g.base).map i).op =
        j.op ≫ (eqToHom hU).op from Subsingleton.elim _ _)).trans
        (ConcreteCategory.congr_hom (M.presheaf.map_comp j.op (eqToHom hU).op) s))

private theorem sectionRestriction_cycleClass {Z : Scheme.{u}}
    (K : CochainComplex Z.Modules ℕ) {U V : Z.Opens} (i : U ⟶ V) (q : ℕ)
    (z : LinearMap.ker ((SchemeSectionHomology.sectionComplex K V).sc q).g.hom)
    (w : LinearMap.ker ((SchemeSectionHomology.sectionComplex K U).sc q).g.hom)
    (hzw : (K.X q).presheaf.map i.op z.val = w.val) :
    (SchemeSectionHomologyRestriction.restrictionHomologyMap K i q).hom
        (ModuleComplexNativeCycleClasses.cycleClass (SchemeSectionHomology.sectionComplex K V) q z) =
      ModuleComplexNativeCycleClasses.cycleClass (SchemeSectionHomology.sectionComplex K U) q w := by
  let r := (Z.presheaf.map i.op).hom
  let L := ((ModuleCat.restrictScalars r).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (SchemeSectionHomology.sectionComplex K U)
  let w' : LinearMap.ker (L.sc q).g.hom := ⟨w.val, w.property⟩
  have h := ModuleComplexNativeCycleClasses.homologyMap_cycleClass
    (SchemeSectionHomology.restrictionComplexMap K i) q z w'
      ((SchemeSectionHomology.restrictionComplexMap_f_apply K i q z.val).trans hzw)
  exact (congrArg
    (ModuleComplexNativeCycleClasses.restrictionHomologyIso r
      (SchemeSectionHomology.sectionComplex K U) q).hom.hom h).trans
      (ModuleComplexNativeCycleClasses.restrictionHomologyIso_cycleClass r
        (SchemeSectionHomology.sectionComplex K U) q w' w rfl)

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
variable (n : ℕ) [SmoothOfRelativeDimension n f]
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "Fr" => SchemeRelativeFrobenius.map p f
local notation "W[" U "]" => RelativeTwistedAffineBasis.twistedOpen f p U
local notation "K" => SchemeRelativeFrobeniusBasisDifferential.complex f p n
variable {U V : X.Opens} (i : U ⟶ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
local notation "I" => GeometricTwistedChartRestrictions.twistedInclusion f p i
variable (v : Fin n → Γ(X, V))
variable (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
  (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (w : Fin n → Γ(X, U))
variable (hw : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
  (MvPolynomial.aeval (R := k) w).toRingHom.Etale)

/-- Every original form keeps its original geometric restriction under the entire form exchange. -/
theorem formIso_restrict (q : ℕ)
    (ω : (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V)) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V;
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    ((K).X q).presheaf.map (I).op
        ((GeometricComplexExchange.formIso f p n hV v hv q).hom.hom ω) =
      (GeometricComplexExchange.formIso f p n hU w hw q).hom.hom
        ((CanonicalGeometry.exteriorCotangentPresheaf f q).map i.op ω) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let Ω := CanonicalGeometry.exteriorCotangentSheaf f q
  have hVf := GeometricComplexExchange.formIso_apply f p n hV v hv q ω
  have hUf := GeometricComplexExchange.formIso_apply f p n hU w hw q
    ((CanonicalGeometry.exteriorCotangentPresheaf f q).map i.op ω)
  have hu := EtaleAffineSectionDifferential.unitEquiv_restrict f hV v hv hU i w hw q ω
  have hp := preimage_restrict (Fr) (I) i
    (RelativeTwistedAffineBasis.relative_preimage f p U)
    (RelativeTwistedAffineBasis.relative_preimage f p V) Ω
    (EtaleAffineSectionDifferential.unitEquiv f hV v hv q ω)
  exact (congrArg (((K).X q).presheaf.map (I).op) hVf).trans
    (hp.trans ((congrArg (Ω.presheaf.map
      (eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U)).op) hu).trans hUf.symm))

local notation "Kv" => SchemeRelativeFrobeniusAffineDeRham.complex v hv p
local notation "Kw" => SchemeRelativeFrobeniusAffineDeRham.complex w hw p

/-- The original native geometric-beta homology map with the original twist scalar restriction. -/
def nativeHomologyRestriction (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V;
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (Kv).homology q ⟶
      (ModuleCat.restrictScalars
        (GeometricTwistedChartRestrictions.twistRestrictionMap f p i).hom).obj ((Kw).homology q) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f V
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  letI := (EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).toAlgebra
  letI : IsScalarTower k Γ(X, V) Γ(X, U) := IsScalarTower.of_algebraMap_eq
    fun a => ((EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).commutes a).symm
  exact RelativeNativeAllAlgebraNaturality.homologyMap p v hv w hw q

private def nativeImageCycle (q : ℕ)
    (z : letI := CanonicalGeometry.cotangentOpenAlgebra f V; LinearMap.ker ((Kv).sc q).g.hom) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U; LinearMap.ker ((Kw).sc q).g.hom := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f V
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  letI := (EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).toAlgebra
  letI : IsScalarTower k Γ(X, V) Γ(X, U) := IsScalarTower.of_algebraMap_eq
    fun a => ((EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).commutes a).symm
  exact RelativeNativeAllAlgebraNaturality.imageCycle p v hv w hw q z

omit [SmoothOfRelativeDimension n f] in
private theorem nativeImageCycle_val (q : ℕ)
    (z : letI := CanonicalGeometry.cotangentOpenAlgebra f V; LinearMap.ker ((Kv).sc q).g.hom) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V;
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (nativeImageCycle f p n i v hv w hw q z).val =
      (CanonicalGeometry.exteriorCotangentPresheaf f q).map i.op z.val := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let := (EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).toAlgebra
  let : IsScalarTower k Γ(X, V) Γ(X, U) := IsScalarTower.of_algebraMap_eq
    fun a => ((EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).commutes a).symm
  exact (RelativeNativeAllAlgebraNaturality.imageCycle_val p v hv w hw q z).trans
    (EtaleSchemeSectionDifferential.exterior_restrict f i q z.val).symm

omit [SmoothOfRelativeDimension n f] in
private theorem nativeRestriction_cycleClass (q : ℕ)
    (z : letI := CanonicalGeometry.cotangentOpenAlgebra f V; LinearMap.ker ((Kv).sc q).g.hom) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V;
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (nativeHomologyRestriction f p n i v hv w hw q).hom
        (ModuleComplexNativeCycleClasses.cycleClass (Kv) q z) =
      ModuleComplexNativeCycleClasses.cycleClass (Kw) q (nativeImageCycle f p n i v hv w hw q z) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let := (EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).toAlgebra
  let : IsScalarTower k Γ(X, V) Γ(X, U) := IsScalarTower.of_algebraMap_eq
    fun a => ((EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).commutes a).symm
  exact RelativeNativeAllAlgebraNaturality.homologyMap_cycleClass p v hv w hw q z

/-- Every original native homology element retains its same actual geometric restriction. -/
theorem homologyTransferIso_restrict (q : ℕ)
    (x : letI := CanonicalGeometry.cotangentOpenAlgebra f V; (Kv).homology q) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V;
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (SchemeSectionHomologyRestriction.restrictionHomologyMap (K) (I) q).hom
        ((GeometricLocalCartier.homologyTransferIso f p hV n v hv q).hom.hom x) =
      (GeometricLocalCartier.homologyTransferIso f p hU n w hw q).hom.hom
        ((nativeHomologyRestriction f p n i v hv w hw q).hom x) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  obtain ⟨z, rfl⟩ := RelativeEtaleCartierAllNaturality.nativeCycleClass_surjective (Kv) q x
  have hz : ((K).X q).presheaf.map (I).op
      (GeometricLocalCartier.imageCycle f p hV n v hv q z).val =
      (GeometricLocalCartier.imageCycle f p hU n w hw q
        (nativeImageCycle f p n i v hv w hw q z)).val := by
    change ((K).X q).presheaf.map (I).op
      ((GeometricComplexExchange.formIso f p n hV v hv q).hom.hom z.val) =
      (GeometricComplexExchange.formIso f p n hU w hw q).hom.hom
        (nativeImageCycle f p n i v hv w hw q z).val
    exact (formIso_restrict f p n i hU hV v hv w hw q z.val).trans
      (congrArg (GeometricComplexExchange.formIso f p n hU w hw q).hom.hom
        (nativeImageCycle_val f p n i v hv w hw q z).symm)
  have hcV := GeometricLocalCartier.homologyTransferIso_cycleClass f p hV n v hv q z
  have hcU := GeometricLocalCartier.homologyTransferIso_cycleClass f p hU n w hw q
    (nativeImageCycle f p n i v hv w hw q z)
  have hn := nativeRestriction_cycleClass f p n i v hv w hw q z
  have hs := sectionRestriction_cycleClass (K) (I) q
    (GeometricLocalCartier.imageCycle f p hV n v hv q z)
    (GeometricLocalCartier.imageCycle f p hU n w hw q
      (nativeImageCycle f p n i v hv w hw q z)) hz
  exact (congrArg (SchemeSectionHomologyRestriction.restrictionHomologyMap (K) (I) q).hom hcV).trans
    (hs.trans (hcU.symm.trans
      (congrArg (GeometricLocalCartier.homologyTransferIso f p hU n w hw q).hom.hom hn.symm)))

local notation "g" => pullback.snd f (SchemeRelativeFrobenius.baseMap (k := k) p)

/-- The entire actual evaluated Cartier map commutes with original restriction on every source section. -/
theorem inverseCartierIso_restrict (q : ℕ)
    (s : (CanonicalGeometry.exteriorCotangentSheaf g q).val.obj (op (W[V]))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V;
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (SchemeSectionHomologyRestriction.restrictionHomologyMap (K) (I) q).hom
        ((GeometricLocalCartier.inverseCartierIso f p hV n v hv q).hom.hom s) =
      (GeometricLocalCartier.inverseCartierIso f p hU n w hw q).hom.hom
        ((CanonicalGeometry.exteriorCotangentSheaf g q).presheaf.map (I).op s) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let := (EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).toAlgebra
  let : IsScalarTower k Γ(X, V) Γ(X, U) := IsScalarTower.of_algebraMap_eq
    fun a => ((EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).commutes a).symm
  let uV := GeometricLocalCartier.twistedUnitIso f p hV n v hv q
  let uU := GeometricLocalCartier.twistedUnitIso f p hU n w hw q
  let ω := uV.inv.hom s
  have hω : uV.hom.hom ω = s := Iso.inv_hom_id_apply uV s
  have huV : (GeometricLocalCartier.inverseCartierIso f p hV n v hv q).hom.hom
        (uV.hom.hom ω) =
      (GeometricLocalCartier.homologyTransferIso f p hV n v hv q).hom.hom
        ((RelativeNativeAllAlgebraCartier.inverseCartierIso v hv p q).hom.hom
          ((GeometricLocalCartier.rawDomainIso f p hV q).hom.hom ω)) :=
    GeometricLocalCartier.inverseCartierIso_unit f p hV n v hv q ω
  have huU : (GeometricLocalCartier.inverseCartierIso f p hU n w hw q).hom.hom
        (uU.hom.hom ((CanonicalGeometry.exteriorCotangentPresheaf g q).map (I).op ω)) =
      (GeometricLocalCartier.homologyTransferIso f p hU n w hw q).hom.hom
        ((RelativeNativeAllAlgebraCartier.inverseCartierIso w hw p q).hom.hom
          ((GeometricLocalCartier.rawDomainIso f p hU q).hom.hom
            ((CanonicalGeometry.exteriorCotangentPresheaf g q).map (I).op ω))) :=
    GeometricLocalCartier.inverseCartierIso_unit f p hU n w hw q _
  have hn := ConcreteCategory.congr_hom
    (RelativeNativeAllAlgebraNaturality.inverseCartierIso_naturality p v hv w hw q)
    ((GeometricLocalCartier.rawDomainIso f p hV q).hom.hom ω)
  have ht := homologyTransferIso_restrict f p n i hU hV v hv w hw q
    ((RelativeNativeAllAlgebraCartier.inverseCartierIso v hv p q).hom.hom
      ((GeometricLocalCartier.rawDomainIso f p hV q).hom.hom ω))
  have hr := GeometricCotangentRestrictions.rawDomainIso_restrict f p i hU hV q ω
  have hunit := GeometricCotangentRestrictions.twistedUnitIso_restrict f p i hU hV v hv w hw q ω
  have hu : (SchemeSectionHomologyRestriction.restrictionHomologyMap (K) (I) q).hom
        ((GeometricLocalCartier.inverseCartierIso f p hV n v hv q).hom.hom (uV.hom.hom ω)) =
      (GeometricLocalCartier.inverseCartierIso f p hU n w hw q).hom.hom
        ((CanonicalGeometry.exteriorCotangentSheaf g q).presheaf.map (I).op (uV.hom.hom ω)) :=
    (congrArg (SchemeSectionHomologyRestriction.restrictionHomologyMap (K) (I) q).hom huV).trans
      (ht.trans ((congrArg (GeometricLocalCartier.homologyTransferIso f p hU n w hw q).hom.hom hn).trans
        ((congrArg (fun a => (GeometricLocalCartier.homologyTransferIso f p hU n w hw q).hom.hom
            ((RelativeNativeAllAlgebraCartier.inverseCartierIso w hw p q).hom.hom a)) hr).trans
          (huU.symm.trans (congrArg (GeometricLocalCartier.inverseCartierIso f p hU n w hw q).hom.hom
            hunit.symm)))))
  exact (congrArg (fun a => (SchemeSectionHomologyRestriction.restrictionHomologyMap (K) (I) q).hom
    ((GeometricLocalCartier.inverseCartierIso f p hV n v hv q).hom.hom a)) hω).symm.trans
      (hu.trans (congrArg (fun a => (GeometricLocalCartier.inverseCartierIso f p hU n w hw q).hom.hom
        ((CanonicalGeometry.exteriorCotangentSheaf g q).presheaf.map (I).op a)) hω))

/-- The original local Cartier maps into the same global homology sheaf agree on every overlap. -/
theorem localSheafCartierSectionsIso_restrict (q : ℕ)
    (s : (CanonicalGeometry.exteriorCotangentSheaf g q).val.obj (op (W[V]))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V;
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    ((K).homology q).presheaf.map (I).op
        ((GeometricAffineHomology.localSheafCartierSectionsIso f p n hV v hv q).hom.hom s) =
      (GeometricAffineHomology.localSheafCartierSectionsIso f p n hU w hw q).hom.hom
        ((CanonicalGeometry.exteriorCotangentSheaf g q).presheaf.map (I).op s) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let : ∀ r, ((K).X r).IsQuasicoherent :=
    fun r => GeometricRelativeFrobeniusQuasicoherent.complex_term_isQuasicoherent f p n r
  have hh := ConcreteCategory.congr_hom
    (GeometricHomologyNaturality.homologySectionsIso_restrict (I)
      (RelativeTwistedAffineBasis.twistedOpen_isAffine f p U hU)
      (RelativeTwistedAffineBasis.twistedOpen_isAffine f p V hV) (K) q)
    ((GeometricLocalCartier.inverseCartierIso f p hV n v hv q).hom.hom s)
  exact hh.symm.trans (congrArg (GeometricAffineHomology.geometricHomologySectionsIso f p n hU q).hom.hom
    (inverseCartierIso_restrict f p n i hU hV v hv w hw q s))

end EnvelopeProperty.Cartier.GeometricCartierRestrictions
