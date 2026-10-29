import EnvelopeProperty.DeligneIllusie.ActualWittGeometricXiHomotopy
import EnvelopeProperty.Cartier.GeometricSourceRestrictions
import EnvelopeProperty.Cartier.GeometricCartierRestrictions

/-! # Restrictions of the same actual geometric Witt divided forms and homotopies -/
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.DeligneIllusie.ActualWittGeometricXiHomotopy

section GeometricSectionValues
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
  (n : ℕ) [SmoothOfRelativeDimension n f]
attribute [local instance] Cartier.RelativeEtaleCartierDomain.coefficientAlgebra
local notation "Y" => Cartier.SchemeRelativeFrobenius.twist p f
local notation "g" => pullback.snd f (Cartier.SchemeRelativeFrobenius.baseMap (k := k) p)
local notation "W[" U "]" => Cartier.RelativeTwistedAffineBasis.twistedOpen f p U
local notation "α[" U "]" => @CommRingCat.Hom.hom (CommRingCat.of k)
  (X.presheaf.obj (op U)) (NatTrans.app (CanonicalGeometry.schemeConstantPresheafMap f) (op U))
local notation "T[" U "]" => Cartier.RelativeFrobenius.twist (α[U]) p
private abbrev sectionNativeCoefficientAlgebra (U : X.Opens) : Algebra k (T[U]) :=
  (Cartier.RelativeFrobenius.coefficientMap (α[U]) p).hom.toAlgebra
attribute [local instance] sectionNativeCoefficientAlgebra
local notation "M" => CanonicalGeometry.exteriorCotangentSheaf g 1
local notation "E" q => Cartier.SchemeRelativeFrobeniusDeRham.formModule f p q

private def geometricSectionValue {U : X.Opens} (hU : IsAffineOpen U)
    (v : Fin n → Γ(X,U))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (q : ℕ)
    (φ : KaehlerDifferential k (T[U]) →
      (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op U))
    (s : (M).val.obj (op (W[U]))) : (E q).val.obj (op (W[U])) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  exact (Cartier.GeometricComplexExchange.formIso f p n hU v hv q).hom.hom
    (φ (exteriorPower.oneEquiv (T[U]) (KaehlerDifferential k (T[U]))
      ((Cartier.GeometricLocalCartier.domainIso f p hU n v hv 1).hom.hom s)))

private theorem geometricSectionValue_restrict {U V : X.Opens} (i : U ⟶ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (v : Fin n → Γ(X,V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (w : Fin n → Γ(X,U))
    (hw : letI := CanonicalGeometry.cotangentOpenAlgebra f U
      (MvPolynomial.aeval (R := k) w).toRingHom.Etale) (q : ℕ)
    (φV : KaehlerDifferential k (T[V]) →
      (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V))
    (φU : KaehlerDifferential k (T[U]) →
      (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op U))
    (hφ : ∀ η, (CanonicalGeometry.exteriorCotangentPresheaf f q).map i.op (φV η) =
      φU (Cartier.GeometricCotangentRestrictions.nativeCotangentRestriction f p i η))
    (s : (M).val.obj (op (W[V]))) :
    (E q).presheaf.map (Cartier.GeometricTwistedChartRestrictions.twistedInclusion f p i).op
      (geometricSectionValue f p n hV v hv q φV s) =
    geometricSectionValue f p n hU w hw q φU
      ((M).presheaf.map (Cartier.GeometricTwistedChartRestrictions.twistedInclusion f p i).op s) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let η := exteriorPower.oneEquiv (T[V]) (KaehlerDifferential k (T[V]))
    ((Cartier.GeometricLocalCartier.domainIso f p hV n v hv 1).hom.hom s)
  have hs := Cartier.GeometricSourceRestrictions.domainIso_oneEquiv_restrict
    f p i hU hV v hv w hw s
  have ht := Cartier.GeometricCartierRestrictions.formIso_restrict
    f p n i hU hV v hv w hw q (φV η)
  exact ht.trans (congrArg (Cartier.GeometricComplexExchange.formIso f p n hU w hw q).hom.hom
    ((hφ η).trans (congrArg φU hs)))

end GeometricSectionValues

section ActualWittSectionRestrictions
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
  {Xtilde : Scheme.{u}} (f : Xtilde ⟶ Spec (.of (WittTwo.Ring p k)))
  (n : ℕ) [SmoothOfRelativeDimension n f]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
  Cartier.RelativeEtaleCartierDomain.coefficientAlgebra
private abbrev specialFibre := WittTwoSpecialFibreOpens.specialFibre p k f
private abbrev specialFibreMap : specialFibre p k f ⟶ Spec (.of k) :=
  pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f
private abbrev specialOpen (U : Xtilde.Opens) := WittTwoSpecialFibreOpens.residueOpen p k f U
private abbrev geometricSections (U : Xtilde.Opens) : CommRingCat :=
  (specialFibre p k f).presheaf.obj (op (specialOpen p k f U))
private abbrev twistedOpen (U : Xtilde.Opens) :=
  Cartier.RelativeTwistedAffineBasis.twistedOpen (specialFibreMap p k f) p (specialOpen p k f U)
private abbrev geometricSource := CanonicalGeometry.exteriorCotangentSheaf
  (pullback.snd (specialFibreMap p k f) (Cartier.SchemeRelativeFrobenius.baseMap (k := k) p)) 1
private abbrev geometricTarget (q : ℕ) :=
  Cartier.SchemeRelativeFrobeniusDeRham.formModule (specialFibreMap p k f) p q
private abbrev residueAlgebra (U : Xtilde.Opens) :=
  letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Xtilde,U)
variable {U V : Xtilde.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : U ⟶ V)
  (v : Fin n → geometricSections p k f V)
  (hv : letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f V)
    (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
  (w : Fin n → geometricSections p k f U)
  (hw : letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
    (MvPolynomial.aeval (R := k) w).toRingHom.Etale)
local notation "r" => WittTwoSpecialFibreReduction.residueInclusion p k f i
local notation "I" => Cartier.GeometricTwistedChartRestrictions.twistedInclusion (specialFibreMap p k f) p r
variable (F G : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    WittTwoLiftDifference.Lift p k Γ(Xtilde,V))
  (hF : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    ∀ t, algebraMap Γ(Xtilde,V) (residueAlgebra p k f V) (F t) =
      WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,V) t)
  (hG : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    ∀ t, algebraMap Γ(Xtilde,V) (residueAlgebra p k f V) (G t) =
      WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,V) t)

/-- Restrict the SAME actual individual divided map, using the internally produced original restricted lift. -/
theorem xiSectionMap_restrict
    (s : (geometricSource p k f).val.obj (op (twistedOpen p k f V))) :
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hV
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
    let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i
    let hβ := WittTwoSchemeAffineRestrictions.restriction_etale hU hV i
    let Fr := WittTwoEtaleRestrictionCoherence.restrictedLift p k β F hF hβ
    let hFr := WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β F hF hβ
    (geometricTarget p k f 1).presheaf.map (I).op
      ((xiSectionMap p k f n hV v hv F hF).hom s) =
    (xiSectionMap p k f n hU w hw Fr hFr).hom
      ((geometricSource p k f).presheaf.map (I).op s) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hV
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f V)
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
  let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i
  let hβ := WittTwoSchemeAffineRestrictions.restriction_etale hU hV i
  let Fr := WittTwoEtaleRestrictionCoherence.restrictedLift p k β F hF hβ
  let hFr := WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β F hF hβ
  let φV := WittTwoNativeTwistRestriction.oneFormAlongEquiv p k
    (WittTwoGeometricDifferential.sectionEquiv p k f hV) F hF
  let φU := WittTwoNativeTwistRestriction.oneFormAlongEquiv p k
    (WittTwoGeometricDifferential.sectionEquiv p k f hU) Fr hFr
  let ψ := Cartier.EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p k f) r
  let := ψ.toAlgebra
  let : IsScalarTower k (geometricSections p k f V) (geometricSections p k f U) :=
    IsScalarTower.of_algebraMap_eq fun d => (ψ.commutes d).symm
  have hn := WittTwoNativeTwistRestriction.sectionOneFormMap_restrictedLift
    p k f hU hV i F hF
  apply geometricSectionValue_restrict (specialFibreMap p k f) p n r
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hV) v hv w hw 1 φV φU
  intro η
  have hnη := ConcreteCategory.congr_hom hn η
  change Cartier.RelativeNativeAllAlgebraNaturality.formMap
      (k := k) (A := geometricSections p k f V) (B := geometricSections p k f U) p 1 (φV η) =
    φU (Cartier.GeometricCotangentRestrictions.nativeCotangentRestriction (specialFibreMap p k f) p r η) at hnη
  have he := Cartier.EtaleSchemeSectionDifferential.exterior_restrict (specialFibreMap p k f) r 1 (φV η)
  have hf := Cartier.RelativeNativeAllAlgebraNaturality.formMap_apply
    (k := k) (A := geometricSections p k f V) (B := geometricSections p k f U) p 1 (φV η)
  exact he.trans (hf.symm.trans hnη)

/-- Restrict the SAME actual canonical homotopy term, using the internally produced original restricted lift. -/
theorem homotopySectionMap_restrict
    (s : (geometricSource p k f).val.obj (op (twistedOpen p k f V))) :
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hV
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
    let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i
    let hβ := WittTwoSchemeAffineRestrictions.restriction_etale hU hV i
    let Fr := WittTwoEtaleRestrictionCoherence.restrictedLift p k β F hF hβ
    let hFr := WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β F hF hβ
    let Gr := WittTwoEtaleRestrictionCoherence.restrictedLift p k β G hG hβ
    let hGr := WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β G hG hβ
    (geometricTarget p k f 0).presheaf.map (I).op
      ((homotopySectionMap p k f n hV v hv F G hF hG).hom s) =
    (homotopySectionMap p k f n hU w hw Fr Gr hFr hGr).hom
      ((geometricSource p k f).presheaf.map (I).op s) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hV
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f V)
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
  let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i
  let hβ := WittTwoSchemeAffineRestrictions.restriction_etale hU hV i
  let Fr := WittTwoEtaleRestrictionCoherence.restrictedLift p k β F hF hβ
  let hFr := WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β F hF hβ
  let Gr := WittTwoEtaleRestrictionCoherence.restrictedLift p k β G hG hβ
  let hGr := WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β G hG hβ
  let φV := WittTwoNativeTwistRestriction.zeroFormAlongEquiv p k
    (WittTwoGeometricDifferential.sectionEquiv p k f hV) F G hF hG
  let φU := WittTwoNativeTwistRestriction.zeroFormAlongEquiv p k
    (WittTwoGeometricDifferential.sectionEquiv p k f hU) Fr Gr hFr hGr
  let ψ := Cartier.EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p k f) r
  let := ψ.toAlgebra
  let : IsScalarTower k (geometricSections p k f V) (geometricSections p k f U) :=
    IsScalarTower.of_algebraMap_eq fun d => (ψ.commutes d).symm
  have hn := WittTwoNativeTwistRestriction.sectionZeroFormTerm_restrictedLift
    p k f hU hV i F G hF hG
  apply geometricSectionValue_restrict (specialFibreMap p k f) p n r
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hV) v hv w hw 0 φV φU
  intro η
  have hnη := ConcreteCategory.congr_hom hn η
  change Cartier.RelativeNativeAllAlgebraNaturality.formMap
      (k := k) (A := geometricSections p k f V) (B := geometricSections p k f U) p 0 (φV η) =
    φU (Cartier.GeometricCotangentRestrictions.nativeCotangentRestriction (specialFibreMap p k f) p r η) at hnη
  have he := Cartier.EtaleSchemeSectionDifferential.exterior_restrict (specialFibreMap p k f) r 0 (φV η)
  have hf := Cartier.RelativeNativeAllAlgebraNaturality.formMap_apply
    (k := k) (A := geometricSections p k f V) (B := geometricSections p k f U) p 0 (φV η)
  exact he.trans (hf.symm.trans hnη)

end ActualWittSectionRestrictions

end EnvelopeProperty.DeligneIllusie.ActualWittGeometricXiHomotopy
