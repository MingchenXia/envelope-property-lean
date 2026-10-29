import EnvelopeProperty.Cartier.GeometricLocalCartier
import EnvelopeProperty.Cartier.GeometricTwistedChartRestrictions
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierAllNaturality

/-! # Cotangent and exterior restriction on the original geometric twist -/

noncomputable section
namespace EnvelopeProperty.Cartier.GeometricCotangentRestrictions
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "g" => pullback.snd f (SchemeRelativeFrobenius.baseMap (k := k) p)
local notation "W[" U "]" => RelativeTwistedAffineBasis.twistedOpen f p U
local notation "B[" U "]" => X.presheaf.obj (op U)
local notation "A[" U "]" => Γ(Y, W[U])
local notation "α[" U "]" => @CommRingCat.Hom.hom (CommRingCat.of k)
  (X.presheaf.obj (op U)) (NatTrans.app (CanonicalGeometry.schemeConstantPresheafMap f) (op U))
local notation "T[" U "]" => RelativeFrobenius.twist (α[U]) p
local notation "c[" U "]" => RelativeFrobenius.coefficientMap (α[U]) p
local notation "δ[" U "]" => RelativeTwistedAffineSections.coefficientSectionMap f p U
@[instance_reducible]
private def nativeCoefficientAlgebra (U : X.Opens) : Algebra k (T[U]) :=
  (c[U]).hom.toAlgebra
attribute [local instance] nativeCoefficientAlgebra

variable {U V : X.Opens} (i : U ⟶ V)
local notation "I" => GeometricTwistedChartRestrictions.twistedInclusion f p i
local notation "τ" => GeometricTwistedChartRestrictions.twistRestrictionMap f p i

/-- The original native cotangent map along the original twisted section restriction. -/
def nativeCotangentRestriction : ModuleCat.of (T[V]) (KaehlerDifferential k (T[V])) ⟶
    (ModuleCat.restrictScalars (τ).hom).obj
      (ModuleCat.of (T[U]) (KaehlerDifferential k (T[U]))) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f V
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  letI := (EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).toAlgebra
  letI : IsScalarTower k (B[V]) (B[U]) := IsScalarTower.of_algebraMap_eq
    fun a => ((EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).commutes a).symm
  exact RelativeEtaleCartierNaturality.cotangentMap (k := k) (A := B[V]) (B := B[U]) p

/-- Every original native differential keeps the original native restriction value. -/
theorem nativeCotangentRestriction_D (t : T[V]) :
    nativeCotangentRestriction f p i (KaehlerDifferential.D k (T[V]) t) =
      KaehlerDifferential.D k (T[U]) ((τ).hom t) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let := (EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).toAlgebra
  let : IsScalarTower k (B[V]) (B[U]) := IsScalarTower.of_algebraMap_eq
    fun a => ((EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).commutes a).symm
  exact RelativeEtaleCartierNaturality.cotangentMap_D (k := k) (A := B[V]) (B := B[U]) p t

/-- The genuine universal cotangent isomorphism of the original geometric coefficient square. -/
def rawCotangentIso (hU : IsAffineOpen U) :
    (CanonicalGeometry.cotangentPresheaf g).obj (op (W[U])) ≅
      (ModuleCat.restrictScalars (RelativeTwistedAffineCharts.sectionsIso f p U hU).hom.hom).obj
        (ModuleCat.of (T[U]) (KaehlerDifferential k (T[U]))) :=
  RelativeGlobalCotangentExchange.cotangentIso (δ[U]) (c[U])
    (RelativeTwistedAffineCharts.sectionsIso f p U hU)
    (RelativeTwistedAffineSections.sectionsIso_coefficient f p U hU)

/-- The same cotangent isomorphism preserves every original universal differential. -/
theorem rawCotangentIso_D (hU : IsAffineOpen U) (a : A[U]) :
    (rawCotangentIso f p hU).hom.hom (CommRingCat.KaehlerDifferential.d a) =
      KaehlerDifferential.D k (T[U])
        ((RelativeTwistedAffineCharts.sectionsIso f p U hU).hom a) :=
  RelativeGlobalCotangentExchange.cotangentIso_D (δ[U]) (c[U])
    (RelativeTwistedAffineCharts.sectionsIso f p U hU)
    (RelativeTwistedAffineSections.sectionsIso_coefficient f p U hU) a

/-- The whole original raw cotangent square, derived from the actual whole section-ring square. -/
theorem rawCotangentIso_restrict (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (m : (CanonicalGeometry.cotangentPresheaf g).obj (op (W[V]))) :
    nativeCotangentRestriction f p i ((rawCotangentIso f p hV).hom.hom m) =
      (rawCotangentIso f p hU).hom.hom ((CanonicalGeometry.cotangentPresheaf g).map (I).op m) := by
  let σU : A[U] ≅ T[U] := RelativeTwistedAffineCharts.sectionsIso f p U hU
  let σV : A[V] ≅ T[V] := RelativeTwistedAffineCharts.sectionsIso f p V hV
  let r := (Y).presheaf.map (I).op
  have hσ : r ≫ σU.hom = σV.hom ≫ τ :=
    GeometricTwistedChartRestrictions.sectionsIso_naturality f p i hU hV
  let N := ModuleCat.of (T[U]) (KaehlerDifferential k (T[U]))
  let P := (ModuleCat.restrictScalars ((τ).hom.comp σV.hom.hom)).obj N
  let : Module (A[V]) P := P.isModule
  let L : (CanonicalGeometry.cotangentPresheaf g).obj (op (W[V])) ⟶ P :=
    (rawCotangentIso f p hV).hom ≫
      (ModuleCat.restrictScalars σV.hom.hom).map (nativeCotangentRestriction f p i) ≫
      (ModuleCat.restrictScalarsComp' σV.hom.hom (τ).hom
        ((τ).hom.comp σV.hom.hom) rfl).inv.app N
  let R : (CanonicalGeometry.cotangentPresheaf g).obj (op (W[V])) ⟶ P :=
    (CanonicalGeometry.cotangentPresheaf g).map (I).op ≫
      (ModuleCat.restrictScalars r.hom).map (rawCotangentIso f p hU).hom ≫
      (ModuleCat.restrictScalarsComp' r.hom σU.hom.hom
        (σU.hom.hom.comp r.hom) rfl).inv.app N ≫
      (ModuleCat.restrictScalarsCongr (congrArg CommRingCat.Hom.hom hσ)).hom.app N
  have h : L = R := by
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    change nativeCotangentRestriction f p i
        ((rawCotangentIso f p hV).hom.hom (CommRingCat.KaehlerDifferential.d a)) =
      (rawCotangentIso f p hU).hom.hom
        ((CanonicalGeometry.cotangentPresheaf g).map (I).op (CommRingCat.KaehlerDifferential.d a))
    have hd := PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d
      (CanonicalGeometry.schemeConstantPresheafMap g) (I).op a
    exact (congrArg (nativeCotangentRestriction f p i).hom (rawCotangentIso_D f p hV a)).trans
      ((nativeCotangentRestriction_D f p i (σV.hom a)).trans
        ((congrArg (KaehlerDifferential.D k (T[U]))
          (ConcreteCategory.congr_hom hσ a).symm).trans
          ((rawCotangentIso_D f p hU (r a)).symm.trans
            (congrArg (rawCotangentIso f p hU).hom.hom hd.symm))))
  exact ConcreteCategory.congr_hom h m

/-- The original cotangent sheafification unit retains its actual restriction on every raw section. -/
theorem cotangent_unit_restrict
    (m : (CanonicalGeometry.cotangentPresheaf g).obj (op (W[V]))) :
    (CanonicalGeometry.cotangentSheaf g).val.map (I).op
        ((CanonicalGeometry.cotangentSheafificationMap g).app (op (W[V])) m) =
      (CanonicalGeometry.cotangentSheafificationMap g).app (op (W[U]))
        ((CanonicalGeometry.cotangentPresheaf g).map (I).op m) :=
  (PresheafOfModules.naturality_apply (CanonicalGeometry.cotangentSheafificationMap g) (I).op m).symm

/-- The original exterior unit commutes with the same geometric restriction in every degree. -/
theorem exterior_unit_restrict (q : ℕ)
    (ω : (CanonicalGeometry.exteriorCotangentPresheaf g q).obj (op (W[V]))) :
    (CanonicalGeometry.exteriorCotangentSheaf g q).val.map (I).op
        ((CanonicalGeometry.exteriorSheafificationMap
          (CanonicalGeometry.cotangentPresheaf g) q).app (op (W[V])) ω) =
      (CanonicalGeometry.exteriorSheafificationMap
        (CanonicalGeometry.cotangentPresheaf g) q).app (op (W[U]))
          ((CanonicalGeometry.exteriorCotangentPresheaf g q).map (I).op ω) :=
  (PresheafOfModules.naturality_apply (CanonicalGeometry.exteriorSheafificationMap
    (CanonicalGeometry.cotangentPresheaf g) q) (I).op ω).symm

/-- The original affine exterior unit isomorphisms satisfy the same whole restriction square. -/
theorem twistedUnitIso_restrict (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    {n m : ℕ} (v : Fin n → Γ(X, V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (w : Fin m → Γ(X, U))
    (hw : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      (MvPolynomial.aeval (R := k) w).toRingHom.Etale)
    (q : ℕ) (ω : (CanonicalGeometry.exteriorCotangentPresheaf g q).obj (op (W[V]))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V;
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (CanonicalGeometry.exteriorCotangentSheaf g q).val.map (I).op
        ((GeometricLocalCartier.twistedUnitIso f p hV n v hv q).hom ω) =
      (GeometricLocalCartier.twistedUnitIso f p hU m w hw q).hom
        ((CanonicalGeometry.exteriorCotangentPresheaf g q).map (I).op ω) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact exterior_unit_restrict f p i q ω

/-- The original native all-degree exterior map along the same original twist restriction. -/
def nativeExteriorRestriction (q : ℕ) :
    ModuleCat.of (T[V]) (⋀[T[V]]^q (KaehlerDifferential k (T[V]))) ⟶
      (ModuleCat.restrictScalars (τ).hom).obj
        (ModuleCat.of (T[U]) (⋀[T[U]]^q (KaehlerDifferential k (T[U])))) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f V
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  letI := (EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).toAlgebra
  letI : IsScalarTower k (B[V]) (B[U]) := IsScalarTower.of_algebraMap_eq
    fun a => ((EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).commutes a).symm
  exact RelativeEtaleCartierAllNaturality.exteriorMap (k := k) (A := B[V]) (B := B[U]) p q

/-- Every native pure wedge retains the wedge of the same native cotangent restrictions. -/
theorem nativeExteriorRestriction_wedge (q : ℕ) (m : Fin q → KaehlerDifferential k (T[V])) :
    nativeExteriorRestriction f p i q (exteriorPower.ιMulti (T[V]) q m) =
      exteriorPower.ιMulti (T[U]) q (fun j => nativeCotangentRestriction f p i (m j)) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let := (EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).toAlgebra
  let : IsScalarTower k (B[V]) (B[U]) := IsScalarTower.of_algebraMap_eq
    fun a => ((EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).commutes a).symm
  change CanonicalGeometry.exteriorSemilinearMap (τ).hom
    (RelativeEtaleCartierAllNaturality.cotangentSemilinear (k := k) (A := B[V]) (B := B[U]) p) q _ = _
  exact CanonicalGeometry.exteriorSemilinearMap_ιMulti _ _ q m

/-- The whole original raw exterior square holds in every degree, including the empty wedge. -/
theorem rawDomainIso_restrict (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (q : ℕ) (ω : (CanonicalGeometry.exteriorCotangentPresheaf g q).obj (op (W[V]))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V;
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    nativeExteriorRestriction f p i q ((GeometricLocalCartier.rawDomainIso f p hV q).hom.hom ω) =
      (GeometricLocalCartier.rawDomainIso f p hU q).hom.hom
        ((CanonicalGeometry.exteriorCotangentPresheaf g q).map (I).op ω) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let : Module (A[V]) (CommRingCat.KaehlerDifferential (δ[V])) :=
    (CommRingCat.KaehlerDifferential (δ[V])).isModule
  let : Module (A[U]) (CommRingCat.KaehlerDifferential (δ[U])) :=
    (CommRingCat.KaehlerDifferential (δ[U])).isModule
  let σU : A[U] ≅ T[U] := RelativeTwistedAffineCharts.sectionsIso f p U hU
  let σV : A[V] ≅ T[V] := RelativeTwistedAffineCharts.sectionsIso f p V hV
  let r := (Y).presheaf.map (I).op
  have hσ : r ≫ σU.hom = σV.hom ≫ τ :=
    GeometricTwistedChartRestrictions.sectionsIso_naturality f p i hU hV
  let N := ModuleCat.of (T[U]) (⋀[T[U]]^q (KaehlerDifferential k (T[U])))
  let P := (ModuleCat.restrictScalars ((τ).hom.comp σV.hom.hom)).obj N
  let : Module (A[V]) P := P.isModule
  let L : (CanonicalGeometry.exteriorCotangentPresheaf g q).obj (op (W[V])) ⟶ P :=
    (GeometricLocalCartier.rawDomainIso f p hV q).hom ≫
      (ModuleCat.restrictScalars σV.hom.hom).map (nativeExteriorRestriction f p i q) ≫
      (ModuleCat.restrictScalarsComp' σV.hom.hom (τ).hom
        ((τ).hom.comp σV.hom.hom) rfl).inv.app N
  let R : (CanonicalGeometry.exteriorCotangentPresheaf g q).obj (op (W[V])) ⟶ P :=
    (CanonicalGeometry.exteriorCotangentPresheaf g q).map (I).op ≫
      (ModuleCat.restrictScalars r.hom).map (GeometricLocalCartier.rawDomainIso f p hU q).hom ≫
      (ModuleCat.restrictScalarsComp' r.hom σU.hom.hom
        (σU.hom.hom.comp r.hom) rfl).inv.app N ≫
      (ModuleCat.restrictScalarsCongr (congrArg CommRingCat.Hom.hom hσ)).hom.app N
  have h : L = R := by
    apply ModuleCat.hom_ext
    change (show (⋀[A[V]]^q (CommRingCat.KaehlerDifferential (δ[V]))) →ₗ[A[V]] P from L.hom) =
      (show (⋀[A[V]]^q (CommRingCat.KaehlerDifferential (δ[V]))) →ₗ[A[V]] P from R.hom)
    apply LinearMap.ext_on_range
      (exteriorPower.ιMulti_span (A[V]) q (CommRingCat.KaehlerDifferential (δ[V])))
    intro m
    change nativeExteriorRestriction f p i q
        ((GeometricLocalCartier.rawDomainIso f p hV q).hom.hom
          (exteriorPower.ιMulti (A[V]) q (M := CommRingCat.KaehlerDifferential (δ[V])) m)) =
      (GeometricLocalCartier.rawDomainIso f p hU q).hom.hom
        ((CanonicalGeometry.exteriorCotangentPresheaf g q).map (I).op
          (exteriorPower.ιMulti (A[V]) q (M := CommRingCat.KaehlerDifferential (δ[V])) m))
    have hVw := GeometricLocalCartier.rawDomainIso_wedge f p hV q m
    have hUw := GeometricLocalCartier.rawDomainIso_wedge f p hU q
      (fun j => (CanonicalGeometry.cotangentPresheaf g).map (I).op (m j))
    have hr := CanonicalGeometry.exteriorPresheaf_map_mk
      (CanonicalGeometry.cotangentPresheaf g) q (I).op m
    have hm : (fun j : Fin q => nativeCotangentRestriction f p i
        ((rawCotangentIso f p hV).hom.hom (m j))) =
        (fun j : Fin q => (rawCotangentIso f p hU).hom.hom
          ((CanonicalGeometry.cotangentPresheaf g).map (I).op (m j))) := by
      funext j
      exact rawCotangentIso_restrict f p i hU hV (m j)
    exact (congrArg (nativeExteriorRestriction f p i q) hVw).trans
      ((nativeExteriorRestriction_wedge f p i q _).trans
        ((congrArg (exteriorPower.ιMulti (T[U]) q) hm).trans
          (hUw.symm.trans (congrArg (GeometricLocalCartier.rawDomainIso f p hU q).hom.hom hr.symm))))
  exact ConcreteCategory.congr_hom h ω

end EnvelopeProperty.Cartier.GeometricCotangentRestrictions
