import EnvelopeProperty.Cartier.RelativeCartierContinuationNativePrincipalExteriorLocalization
import EnvelopeProperty.Cartier.RelativeCartierContinuationNativeAllAlgebraNaturality
import EnvelopeProperty.Char0.AffineOpenChartMaps

/-! # Actual native homology and the SAME Cartier square at original principal opens -/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeNativePrincipalCartierLocalization
open CategoryTheory Limits
universe u
variable {k B : Type u} [Field k] [CommRing B] [Algebra k B]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "T" => RelativeFrobenius.twist (algebraMap k B) p
local notation "bP" z => CommRingCat.Hom.hom
  (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k B) p) z
local notation "L" z => Localization.Away (bP z)
local notation "αP" z => RingHom.comp (algebraMap B (L z)) (algebraMap k B)
local notation "TP" z => RelativeFrobenius.twist (algebraMap k (L z)) p

attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra
local notation "τ" z => RelativeEtaleCartierNaturality.twistMap (k := k) (A := B) (B := L z) p

variable {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)

include hv in
/-- The actual original image tuple is INTERNALLY etale, including zero localizations. -/
theorem localizedTuple_etale (t : T) :
    (MvPolynomial.aeval (R := k) (fun i => algebraMap B (L t) (v i))).toRingHom.Etale := by
  let : Algebra.Etale B (L t) := Algebra.Etale.of_isLocalizationAway (bP t)
  exact Char0.etale_aeval_algebraMap v hv (RingHom.etale_algebraMap.mpr inferInstance)

private theorem coefficient_eqToIso {C : Type u} [CommRing C]
    (α β : k →+* C) (h : α = β) :
    RelativeFrobenius.coefficientMap α p ≫
      (eqToIso (congrArg (fun a : k →+* C => RelativeFrobenius.twist a p) h)).hom =
      RelativeFrobenius.coefficientMap β p := by
  subst β
  rfl

private theorem source_eqToIso {C : Type u} [CommRing C]
    (α β : k →+* C) (h : α = β) :
    RelativeFrobenius.sourceMap α p ≫
      (eqToIso (congrArg (fun a : k →+* C => RelativeFrobenius.twist a p) h)).hom =
      RelativeFrobenius.sourceMap β p := by
  subst β
  rfl

/-- The native Away structural map is compared by its DERIVED whole base equation. -/
private def baseTwistIso (t : T) :
    (TP t) ≅ RelativeFrobenius.twist (αP t) p :=
  eqToIso (congrArg (fun a : k →+* (L t) => RelativeFrobenius.twist a p)
    (IsScalarTower.algebraMap_eq k B (L t)))

/-- The WHOLE actual Nat14 numerator retains the original principal numerator,
through only the genuine equality of the ORIGINAL native structural maps. -/
theorem twistMap_eq (t : T) :
    (τ t) ≫ (baseTwistIso p t).hom =
      RelativeEtaleBaseChange.twistMap (algebraMap k B) (algebraMap B (L t)) p := by
  apply pushout.hom_ext
  · change RelativeFrobenius.coefficientMap (algebraMap k B) p ≫ _ = _
    rw [← Category.assoc, RelativeEtaleCartierNaturality.twistMap_coefficient]
    exact (coefficient_eqToIso p _ _ (IsScalarTower.algebraMap_eq k B (L t))).trans
      (RelativeEtaleBaseChange.coefficientMap_twistMap (algebraMap k B)
        (algebraMap B (L t)) p).symm
  · change RelativeFrobenius.sourceMap (algebraMap k B) p ≫ _ = _
    rw [← Category.assoc, RelativeEtaleCartierNaturality.twistMap_source, Category.assoc]
    exact (congrArg (fun F => CommRingCat.ofHom (algebraMap B (L t)) ≫ F)
      (source_eqToIso p _ _ (IsScalarTower.algebraMap_eq k B (L t)))).trans
      (RelativeEtaleBaseChange.sourceMap_twistMap (algebraMap k B)
        (algebraMap B (L t)) p).symm

/-- The SAME actual numerator used by the ORIGINAL cochain restriction. -/
private instance twistAlgebra (t : T) : Algebra (T) (TP t) := (τ t).hom.toAlgebra

/-- The actual Nat14 numerator genuinely localizes the original native twist. -/
theorem twist_isLocalization (t : T) : IsLocalization (Submonoid.powers t) (TP t) := by
  let e := baseTwistIso p t ≪≫
    RelativeTwistPrincipalLocalization.principalIso (algebraMap k B) p t
  have he : (τ t) ≫ e.hom = CommRingCat.ofHom (algebraMap (T) (Localization.Away t)) := by
    change (τ t) ≫ ((baseTwistIso p t).hom ≫
      (RelativeTwistPrincipalLocalization.principalIso (algebraMap k B) p t).hom) = _
    rw [← Category.assoc, twistMap_eq p t,
      RelativeTwistPrincipalLocalization.principalIso_twistMap]
  let a : (TP t) ≃ₐ[T] Localization.Away t :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := fun x => congrArg (fun F : (T) ⟶ CommRingCat.of (Localization.Away t) =>
        F.hom x) he }
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers t) a.symm

/-- The ORIGINAL coefficient triangle supplies precisely this original scalar tower. -/
private instance twistCoefficientTower (t : T) : IsScalarTower k (T) (TP t) :=
  RelativeEtaleCartierNaturality.coefficient_scalarTower (k := k) (A := B) (B := L t) p

include v hv in
/-- The SAME original ALL-degree Cartier-domain restriction genuinely localizes. -/
theorem exteriorMap_isLocalizedModule (t : T) (q : ℕ) :
    IsLocalizedModule (Submonoid.powers t)
      (RelativeEtaleCartierAllNaturality.exteriorMap (k := k) (A := B) (B := L t) p q).hom := by
  let : IsLocalization (Submonoid.powers t) (TP t) := twist_isLocalization p t
  change IsLocalizedModule (Submonoid.powers t)
    (CanonicalGeometry.algebraExteriorLinearMap (B := TP t)
      (KaehlerDifferential.map k k (T) (TP t)) q)
  exact CanonicalGeometry.algebraExteriorLinearMap_isLocalizedModule (Submonoid.powers t)
    (RelativeEtaleCartierDomain.cotangentBasis v hv p)
    (KaehlerDifferential.map k k (T) (TP t)) q

/-- The ACTUAL native homology of the ORIGINAL cochain restriction genuinely localizes;
Cartier is used only via its PROVED naturality square, never to define this map. -/
theorem homologyMap_isLocalizedModule (t : T) (q : ℕ) :
    IsLocalizedModule (Submonoid.powers t)
      (RelativeNativeAllAlgebraNaturality.homologyMap p v hv
        (fun i => algebraMap B (L t) (v i)) (localizedTuple_etale p v hv t) q).hom := by
  let w := fun i => algebraMap B (L t) (v i)
  let hw := localizedTuple_etale p v hv t
  let c := (RelativeNativeAllAlgebraCartier.inverseCartierIso v hv p q).toLinearEquiv
  let e := ((ModuleCat.restrictScalars (τ t).hom).mapIso
    (RelativeNativeAllAlgebraCartier.inverseCartierIso w hw p q)).toLinearEquiv
  let f := (RelativeEtaleCartierAllNaturality.exteriorMap
    (k := k) (A := B) (B := L t) p q).hom
  let g := (RelativeNativeAllAlgebraNaturality.homologyMap p v hv w hw q).hom
  have hf : IsLocalizedModule (Submonoid.powers t) f := exteriorMap_isLocalizedModule p v hv t q
  let := hf
  have h : g.comp c.toLinearMap = e.toLinearMap.comp f := by
    exact congrArg ModuleCat.Hom.hom
      (RelativeNativeAllAlgebraNaturality.inverseCartierIso_naturality p v hv w hw q)
  apply (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers t)
    c.toLinearMap c.bijective).mp
  rw [h]
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers t) f e

end EnvelopeProperty.Cartier.RelativeNativePrincipalCartierLocalization
