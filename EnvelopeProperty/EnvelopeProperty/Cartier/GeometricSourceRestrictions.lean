import EnvelopeProperty.Cartier.GeometricCotangentRestrictions

/-! # Actual exterior source and degree-one cotangent restrictions -/
noncomputable section
namespace EnvelopeProperty.Cartier.GeometricSourceRestrictions
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "g" => pullback.snd f (SchemeRelativeFrobenius.baseMap (k := k) p)
local notation "W[" U "]" => RelativeTwistedAffineBasis.twistedOpen f p U
local notation "α[" U "]" => @CommRingCat.Hom.hom (CommRingCat.of k)
  (X.presheaf.obj (op U)) (NatTrans.app (CanonicalGeometry.schemeConstantPresheafMap f) (op U))
local notation "T[" U "]" => RelativeFrobenius.twist (α[U]) p

@[instance_reducible]
private def nativeCoefficientAlgebra (U : X.Opens) : Algebra k (T[U]) :=
  (RelativeFrobenius.coefficientMap (α[U]) p).hom.toAlgebra
attribute [local instance] nativeCoefficientAlgebra

variable {U V : X.Opens} (i : U ⟶ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
local notation "I" => GeometricTwistedChartRestrictions.twistedInclusion f p i

private theorem native_one_restrict (ω : ⋀[T[V]]^1 (KaehlerDifferential k (T[V]))) :
    GeometricCotangentRestrictions.nativeCotangentRestriction f p i
        (exteriorPower.oneEquiv (T[V]) (KaehlerDifferential k (T[V])) ω) =
      exteriorPower.oneEquiv (T[U]) (KaehlerDifferential k (T[U]))
        (GeometricCotangentRestrictions.nativeExteriorRestriction f p i 1 ω) := by
  let τ := GeometricTwistedChartRestrictions.twistRestrictionMap f p i
  let a : ModuleCat.of (T[V]) (⋀[T[V]]^1 (KaehlerDifferential k (T[V]))) ⟶
      ModuleCat.of (T[V]) (KaehlerDifferential k (T[V])) :=
    ModuleCat.ofHom (exteriorPower.oneEquiv (T[V]) (KaehlerDifferential k (T[V]))).toLinearMap
  let b : ModuleCat.of (T[U]) (⋀[T[U]]^1 (KaehlerDifferential k (T[U]))) ⟶
      ModuleCat.of (T[U]) (KaehlerDifferential k (T[U])) :=
    ModuleCat.ofHom (exteriorPower.oneEquiv (T[U]) (KaehlerDifferential k (T[U]))).toLinearMap
  let N := (ModuleCat.restrictScalars τ.hom).obj
    (ModuleCat.of (T[U]) (KaehlerDifferential k (T[U])))
  let : Module (T[V]) N := N.isModule
  let L : ModuleCat.of (T[V]) (⋀[T[V]]^1 (KaehlerDifferential k (T[V]))) ⟶ N :=
    a ≫ GeometricCotangentRestrictions.nativeCotangentRestriction f p i
  let R : ModuleCat.of (T[V]) (⋀[T[V]]^1 (KaehlerDifferential k (T[V]))) ⟶ N :=
    GeometricCotangentRestrictions.nativeExteriorRestriction f p i 1 ≫
      (ModuleCat.restrictScalars τ.hom).map b
  have h : L = R := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_on_range (exteriorPower.ιMulti_span (T[V]) 1 (KaehlerDifferential k (T[V])))
    intro m
    change GeometricCotangentRestrictions.nativeCotangentRestriction f p i
        (exteriorPower.oneEquiv (T[V]) (KaehlerDifferential k (T[V])) (exteriorPower.ιMulti (T[V]) 1 m)) =
      exteriorPower.oneEquiv (T[U]) (KaehlerDifferential k (T[U]))
        (GeometricCotangentRestrictions.nativeExteriorRestriction f p i 1 (exteriorPower.ιMulti (T[V]) 1 m))
    exact (congrArg (GeometricCotangentRestrictions.nativeCotangentRestriction f p i).hom
      (exteriorPower.oneEquiv_ιMulti (R := T[V]) (M := KaehlerDifferential k (T[V])) m)).trans
        ((exteriorPower.oneEquiv_ιMulti (R := T[U]) (M := KaehlerDifferential k (T[U]))
          (fun j => GeometricCotangentRestrictions.nativeCotangentRestriction f p i (m j))).symm.trans
          (congrArg (exteriorPower.oneEquiv (T[U]) (KaehlerDifferential k (T[U])))
            (GeometricCotangentRestrictions.nativeExteriorRestriction_wedge f p i 1 m).symm))
  exact ConcreteCategory.congr_hom h ω

variable {n m : ℕ} (v : Fin n → Γ(X, V))
variable (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
  (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (w : Fin m → Γ(X, U))
variable (hw : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
  (MvPolynomial.aeval (R := k) w).toRingHom.Etale)

private theorem domain_unit {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (v : Fin n → Γ(X, U))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (q : ℕ)
    (ω : (CanonicalGeometry.exteriorCotangentPresheaf g q).obj (op (W[U]))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (GeometricLocalCartier.domainIso f p hU n v hv q).hom.hom
        ((GeometricLocalCartier.twistedUnitIso f p hU n v hv q).hom.hom ω) =
      (GeometricLocalCartier.rawDomainIso f p hU q).hom.hom ω := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact congrArg (GeometricLocalCartier.rawDomainIso f p hU q).hom.hom
    (Iso.hom_inv_id_apply (GeometricLocalCartier.twistedUnitIso f p hU n v hv q) ω)

/-- Every actual original source section retains its original native exterior restriction. -/
theorem domainIso_restrict (q : ℕ)
    (s : (CanonicalGeometry.exteriorCotangentSheaf g q).val.obj (op (W[V]))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V;
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    GeometricCotangentRestrictions.nativeExteriorRestriction f p i q
        ((GeometricLocalCartier.domainIso f p hV n v hv q).hom.hom s) =
      (GeometricLocalCartier.domainIso f p hU m w hw q).hom.hom
        ((CanonicalGeometry.exteriorCotangentSheaf g q).presheaf.map (I).op s) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let uV := GeometricLocalCartier.twistedUnitIso f p hV n v hv q
  let ω := uV.inv.hom s
  have hω : uV.hom.hom ω = s := Iso.inv_hom_id_apply uV s
  have hunitV := domain_unit f p hV v hv q ω
  have hunitU := domain_unit f p hU w hw q
    ((CanonicalGeometry.exteriorCotangentPresheaf g q).map (I).op ω)
  have hr := GeometricCotangentRestrictions.rawDomainIso_restrict f p i hU hV q ω
  have hu := GeometricCotangentRestrictions.twistedUnitIso_restrict f p i hU hV v hv w hw q ω
  have h : GeometricCotangentRestrictions.nativeExteriorRestriction f p i q
        ((GeometricLocalCartier.domainIso f p hV n v hv q).hom.hom (uV.hom.hom ω)) =
      (GeometricLocalCartier.domainIso f p hU m w hw q).hom.hom
        ((CanonicalGeometry.exteriorCotangentSheaf g q).presheaf.map (I).op (uV.hom.hom ω)) :=
    (congrArg (GeometricCotangentRestrictions.nativeExteriorRestriction f p i q) hunitV).trans
      (hr.trans (hunitU.symm.trans (congrArg (GeometricLocalCartier.domainIso f p hU m w hw q).hom.hom hu.symm)))
  exact (congrArg (fun a => GeometricCotangentRestrictions.nativeExteriorRestriction f p i q
    ((GeometricLocalCartier.domainIso f p hV n v hv q).hom.hom a)) hω).symm.trans
      (h.trans (congrArg (fun a => (GeometricLocalCartier.domainIso f p hU m w hw q).hom.hom
        ((CanonicalGeometry.exteriorCotangentSheaf g q).presheaf.map (I).op a)) hω))

/-- The entire original source exchange followed by native oneEquiv has its same cotangent restriction. -/
theorem domainIso_oneEquiv_restrict
    (s : (CanonicalGeometry.exteriorCotangentSheaf g 1).val.obj (op (W[V]))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V;
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    GeometricCotangentRestrictions.nativeCotangentRestriction f p i
        (exteriorPower.oneEquiv (T[V]) (KaehlerDifferential k (T[V]))
          ((GeometricLocalCartier.domainIso f p hV n v hv 1).hom.hom s)) =
      exteriorPower.oneEquiv (T[U]) (KaehlerDifferential k (T[U]))
        ((GeometricLocalCartier.domainIso f p hU m w hw 1).hom.hom
          ((CanonicalGeometry.exteriorCotangentSheaf g 1).presheaf.map (I).op s)) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact (native_one_restrict f p i
    ((GeometricLocalCartier.domainIso f p hV n v hv 1).hom.hom s)).trans
      (congrArg (exteriorPower.oneEquiv (T[U]) (KaehlerDifferential k (T[U])))
        (domainIso_restrict f p i hU hV v hv w hw 1 s))

end EnvelopeProperty.Cartier.GeometricSourceRestrictions
