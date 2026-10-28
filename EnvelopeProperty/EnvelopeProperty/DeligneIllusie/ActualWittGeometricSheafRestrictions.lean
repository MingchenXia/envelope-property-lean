import EnvelopeProperty.DeligneIllusie.ActualWittGeometricXiRestrictions
import EnvelopeProperty.DeligneIllusie.ActualWittGeometricXiEquations
import EnvelopeProperty.DI.AffineLocalMapLocality
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical TensorProduct
open EnvelopeProperty.DI
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.DeligneIllusie.ActualWittGeometricXiHomotopy
section ActualWittSheafRestrictions
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


/-- The SAME original actual xi sheaf map restricts to the map of its internally produced same restricted lift. -/
theorem xiSheafMap_restrict :
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hV
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
    let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i
    let hβ := WittTwoSchemeAffineRestrictions.restriction_etale hU hV i
    let Fr := WittTwoEtaleRestrictionCoherence.restrictedLift p k β F hF hβ
    let hFr := WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β F hF hβ
    CechDegreeOneDescent.localRestrict (I).le
      (xiSheafMap p k f n hV v hv F hF) =
        xiSheafMap p k f n hU w hw Fr hFr := by
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
  let : SmoothOfRelativeDimension n
      (pullback.snd (specialFibreMap p k f) (Cartier.SchemeRelativeFrobenius.baseMap (k := k) p)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
      (IsPullback.of_hasPullback (specialFibreMap p k f)
        (Cartier.SchemeRelativeFrobenius.baseMap (k := k) p)) inferInstance
  let : (geometricSource p k f).IsQuasicoherent :=
    Cartier.SmoothExteriorQuasicoherent.exterior_isQuasicoherent
      (pullback.snd (specialFibreMap p k f) (Cartier.SchemeRelativeFrobenius.baseMap (k := k) p)) n 1
  let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hU
  let hV₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hV
  let hWU := Cartier.RelativeTwistedAffineBasis.twistedOpen_isAffine (specialFibreMap p k f) p
    (specialOpen p k f U) hU₀
  let hWV := Cartier.RelativeTwistedAffineBasis.twistedOpen_isAffine (specialFibreMap p k f) p
    (specialOpen p k f V) hV₀
  change CechDegreeOneDescent.localRestrict (I).le
      (AffineLocalMapRestriction.affineLocalMap hWV (geometricSource p k f) (geometricTarget p k f 1)
        (xiSectionMap p k f n hV v hv F hF)) =
    AffineLocalMapRestriction.affineLocalMap hWU (geometricSource p k f) (geometricTarget p k f 1)
      (xiSectionMap p k f n hU w hw Fr hFr)
  apply AffineLocalMapRestriction.affineLocalMap_restrict hWV hWU (I).le
  intro s
  exact xiSectionMap_restrict p k f n hU hV i v hv w hw F hF s

/-- The SAME original actual homotopy sheaf map restricts to the map of its internally produced same restricted lift. -/
theorem homotopySheafMap_restrict :
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
    CechDegreeOneDescent.localRestrict (I).le
      (homotopySheafMap p k f n hV v hv F G hF hG) =
        homotopySheafMap p k f n hU w hw Fr Gr hFr hGr := by
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
  let : SmoothOfRelativeDimension n
      (pullback.snd (specialFibreMap p k f) (Cartier.SchemeRelativeFrobenius.baseMap (k := k) p)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
      (IsPullback.of_hasPullback (specialFibreMap p k f)
        (Cartier.SchemeRelativeFrobenius.baseMap (k := k) p)) inferInstance
  let : (geometricSource p k f).IsQuasicoherent :=
    Cartier.SmoothExteriorQuasicoherent.exterior_isQuasicoherent
      (pullback.snd (specialFibreMap p k f) (Cartier.SchemeRelativeFrobenius.baseMap (k := k) p)) n 1
  let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hU
  let hV₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hV
  let hWU := Cartier.RelativeTwistedAffineBasis.twistedOpen_isAffine (specialFibreMap p k f) p
    (specialOpen p k f U) hU₀
  let hWV := Cartier.RelativeTwistedAffineBasis.twistedOpen_isAffine (specialFibreMap p k f) p
    (specialOpen p k f V) hV₀
  change CechDegreeOneDescent.localRestrict (I).le
      (AffineLocalMapRestriction.affineLocalMap hWV (geometricSource p k f) (geometricTarget p k f 0)
        (homotopySectionMap p k f n hV v hv F G hF hG)) =
    AffineLocalMapRestriction.affineLocalMap hWU (geometricSource p k f) (geometricTarget p k f 0)
      (homotopySectionMap p k f n hU w hw Fr Gr hFr hGr)
  apply AffineLocalMapRestriction.affineLocalMap_restrict hWV hWU (I).le
  intro s
  exact homotopySectionMap_restrict p k f n hU hV i v hv w hw F G hF hG s

end ActualWittSheafRestrictions
end EnvelopeProperty.DeligneIllusie.ActualWittGeometricXiHomotopy
