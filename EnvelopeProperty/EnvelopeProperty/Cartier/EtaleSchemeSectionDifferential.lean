import EnvelopeProperty.Cartier.EtaleDifferentialNaturality
import EnvelopeProperty.AlgGeom.Canonical.ExteriorSheaf

/-! # The SAME original raw section restrictions and intrinsic exterior differential -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleSchemeSectionDifferential
open AlgebraicGeometry CategoryTheory Opposite
universe u
private theorem transfer_differential {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    {n m : ℕ} (v : Fin n → A) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
    (w : Fin m → B) (hw : (MvPolynomial.aeval (R := R) w).toRingHom.Etale) (q : ℕ)
    (r : (⋀[A]^q (KaehlerDifferential R A)) → (⋀[B]^q (KaehlerDifferential R B)))
    (s : (⋀[A]^(q+1) (KaehlerDifferential R A)) → (⋀[B]^(q+1) (KaehlerDifferential R B)))
    (hr : ∀ a, r a = Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) q a)
    (hs : ∀ a, s a = Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) (q+1) a)
    (a : ⋀[A]^q (KaehlerDifferential R A)) :
    EtaleDeRham.differential w hw q (r a) = s (EtaleDeRham.differential v hv q a) := by
  rw [hr, hs]
  exact EtaleDifferentialNaturality.differential_canonicalMap v hv w hw q a

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
variable {U V : X.Opens} (i : U ⟶ V)

/-- The ACTUAL original section restriction, with its SAME structural scalar actions. -/
def restrictionAlgebraHom :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V
    letI := CanonicalGeometry.cotangentOpenAlgebra f U
    Γ(X, V) →ₐ[k] Γ(X, U) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f V
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  refine { toRingHom := (X.presheaf.map i.op).hom, commutes' := ?_ }
  intro a
  exact (ConcreteCategory.congr_hom
    ((CanonicalGeometry.schemeConstantPresheafMap f).naturality i.op) a).symm

/-- ENTIRE original cotangent presheaf restriction equals SAME native Kaehler map. -/
theorem cotangent_restrict
    (a : letI := CanonicalGeometry.cotangentOpenAlgebra f V; KaehlerDifferential k Γ(X, V)) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V
    letI := CanonicalGeometry.cotangentOpenAlgebra f U
    letI := (restrictionAlgebraHom f i).toAlgebra
    letI : IsScalarTower k Γ(X, V) Γ(X, U) :=
      IsScalarTower.of_algebraMap_eq fun a => ((restrictionAlgebraHom f i).commutes a).symm
    (CanonicalGeometry.cotangentPresheaf f).map i.op a =
      KaehlerDifferential.map k k Γ(X, V) Γ(X, U) a := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let := (restrictionAlgebraHom f i).toAlgebra
  let : IsScalarTower k Γ(X, V) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq fun a => ((restrictionAlgebraHom f i).commutes a).symm
  let L : KaehlerDifferential k Γ(X, V) →ₗ[Γ(X, V)] KaehlerDifferential k Γ(X, U) :=
    { toFun := (CanonicalGeometry.cotangentPresheaf f).map i.op
      map_add' := ((CanonicalGeometry.cotangentPresheaf f).map i.op).hom.map_add
      map_smul' := ((CanonicalGeometry.cotangentPresheaf f).map i.op).hom.map_smul }
  have h : L = KaehlerDifferential.map k k Γ(X, V) Γ(X, U) := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation k Γ(X, V))
    rintro _ ⟨b, rfl⟩
    exact (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d
      (CanonicalGeometry.schemeConstantPresheafMap f) i.op b).trans
        (KaehlerDifferential.map_D k k Γ(X, V) Γ(X, U) b).symm
  exact LinearMap.congr_fun h a

/-- ENTIRE original exterior restriction equals SAME actual canonical exterior map. -/
theorem exterior_restrict (q : ℕ)
    (a : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      ⋀[Γ(X, V)]^q (KaehlerDifferential k Γ(X, V))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V
    letI := CanonicalGeometry.cotangentOpenAlgebra f U
    letI := (restrictionAlgebraHom f i).toAlgebra
    letI : IsScalarTower k Γ(X, V) Γ(X, U) :=
      IsScalarTower.of_algebraMap_eq fun a => ((restrictionAlgebraHom f i).commutes a).symm
    (CanonicalGeometry.exteriorCotangentPresheaf f q).map i.op a =
      Char0.canonicalDifferentialLinearMap (k := k) (R := Γ(X, V)) (A := Γ(X, U)) q a := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let := (restrictionAlgebraHom f i).toAlgebra
  let : IsScalarTower k Γ(X, V) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq fun a => ((restrictionAlgebraHom f i).commutes a).symm
  let L : (⋀[Γ(X, V)]^q (KaehlerDifferential k Γ(X, V))) →ₗ[Γ(X, V)]
      (⋀[Γ(X, U)]^q (KaehlerDifferential k Γ(X, U))) :=
    { toFun := (CanonicalGeometry.exteriorCotangentPresheaf f q).map i.op
      map_add' := ((CanonicalGeometry.exteriorCotangentPresheaf f q).map i.op).hom.map_add
      map_smul' := ((CanonicalGeometry.exteriorCotangentPresheaf f q).map i.op).hom.map_smul }
  have h : L = Char0.canonicalDifferentialLinearMap
      (k := k) (R := Γ(X, V)) (A := Γ(X, U)) q := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span Γ(X, V) q (KaehlerDifferential k Γ(X, V)))
    rintro _ ⟨m, rfl⟩
    change (CanonicalGeometry.exteriorCotangentPresheaf f q).map i.op
      (exteriorPower.ιMulti Γ(X, V) q m) = _
    have hl := CanonicalGeometry.exteriorPresheaf_map_mk
      (CanonicalGeometry.cotangentPresheaf f) q i.op m
    have hr := Char0.canonicalDifferentialLinearMap_wedge
      (k := k) (R := Γ(X, V)) (A := Γ(X, U)) q m
    refine hl.trans ((congrArg (exteriorPower.ιMulti Γ(X, U) q) ?_).trans hr.symm)
    funext j
    exact cotangent_restrict f i (m j)
  exact LinearMap.congr_fun h a

/-- EVERY actual original form differential commutes with SAME original restriction. -/
theorem differential_restrict {n m : ℕ} (v : Fin n → Γ(X, V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (w : Fin m → Γ(X, U))
    (hw : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      (MvPolynomial.aeval (R := k) w).toRingHom.Etale) (q : ℕ)
    (a : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      ⋀[Γ(X, V)]^q (KaehlerDifferential k Γ(X, V))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V
    letI := CanonicalGeometry.cotangentOpenAlgebra f U
    EtaleDeRham.differential w hw q
      ((CanonicalGeometry.exteriorCotangentPresheaf f q).map i.op a) =
      (CanonicalGeometry.exteriorCotangentPresheaf f (q+1)).map i.op
        (EtaleDeRham.differential v hv q a) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let := (restrictionAlgebraHom f i).toAlgebra
  let : IsScalarTower k Γ(X, V) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq fun a => ((restrictionAlgebraHom f i).commutes a).symm
  exact transfer_differential v hv w hw q
    (fun a => (CanonicalGeometry.exteriorCotangentPresheaf f q).map i.op a)
    (fun a => (CanonicalGeometry.exteriorCotangentPresheaf f (q+1)).map i.op a)
    (exterior_restrict f i q) (exterior_restrict f i (q+1)) a

end EnvelopeProperty.Cartier.EtaleSchemeSectionDifferential
