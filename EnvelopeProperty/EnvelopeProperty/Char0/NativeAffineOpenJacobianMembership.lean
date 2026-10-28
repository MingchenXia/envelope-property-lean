import EnvelopeProperty.Char0.NativeSNCDefaultJacobianTransport
import EnvelopeProperty.Char0.NativeAffineOpenJacobian
import EnvelopeProperty.Char0.ResolutionScalarTowers
import EnvelopeProperty.Char0.EtaleSourceInputs

/-! # Original affine-open determinant and whole arbitrary native weighted-germ membership -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EnvelopeProperty.Char0.NativeAffineOpenJacobianMembership
open CategoryTheory AlgebraicGeometry BingWangEntropy Filter
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open SGPT.Okounkov NativeEtaleCoordinates NativeSNCDefaultJacobianTransport
open NativeAffineOpenJacobian NativePreferredJacobian
open scoped Topology Manifold ContDiff

variable {R : Type} [CommRing R] [hCR : Algebra ℂ R] {Y : Scheme}
    (π : Y ⟶ Spec (.of R)) (n : ℕ) (U : Y.affineOpens)
    (v : Fin n → Γ(Y,U.1))
    (hv : Etale (toAffineSpace (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) U.1 v))
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)

/-- The actual original relative determinant with ORIGINAL section C/R actions and genuine bases. -/
def affineOpenDet : Γ(Y,U.1) := by
  let := (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))).sectionsAlgebra U.1
  let : Algebra R Γ(Y,U.1) := (sectionsHom π U.1).toAlgebra
  let := isScalarTower_base_resolutionSections (k := ℂ) π U.1
  exact relativeDifferentialDet (etaleDifferentialBasis z hz)
    (schemeEtaleDifferentialBasis (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) U v hv)

/-- The existing all-source theorem gives the WHOLE original ideal of this actual determinant. -/
theorem affineOpenJacobianIdeal_eq_span_det :
    affineOpenJacobianIdeal (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π n U v hv =
      Ideal.span {affineOpenDet π n U v hv z hz} := by
  let := (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))).sectionsAlgebra U.1
  let : Algebra R Γ(Y,U.1) := (sectionsHom π U.1).toAlgebra
  let := isScalarTower_base_resolutionSections (k := ℂ) π U.1
  exact affineRelativeJacobianIdeal_eq_span z hz
    (schemeEtaleDifferentialBasis (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) U v hv)

private theorem canonicalFieldAlgebra_eq :
    affinePointFieldAlgebra (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) = hCR := by
  apply Algebra.algebra_ext
  intro c
  change (Spec.preimage (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))).hom c = algebraMap ℂ R c
  rw [Spec.preimage_map]
  rfl

variable [SmoothOfRelativeDimension n (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
  [IsSeparated (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
  [QuasiCompact (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
private instance restrictedSmooth : SmoothOfRelativeDimension n
    ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) := by
  rw [Category.assoc]
  exact (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp
    (f := U.2.fromSpec) (n := 0) (m := n) (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
local instance baseAffine : IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) :=
  isAffineHom_of_isAffine _
local instance restrictedAffine : IsAffineHom
    ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) :=
  isAffineHom_of_isAffine _
local instance sourceTopology : TopologicalSpace (SchemeComplexPoint
    (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := schemeAnalyticPointTopology _
local instance sourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint
    (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := schemeAnalyticTNChartedSpace _ n
local instance sourceManifold : IsComplexManifold n (SchemeComplexPoint
    (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := schemeAnalyticTN_isComplexManifold _ n
local instance baseTopology : TopologicalSpace (SchemeComplexPoint
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := schemeAnalyticPointTopology _
local instance baseCharts
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))] :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := schemeAnalyticTNChartedSpace _ n
local instance baseManifold
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))] :
    IsComplexManifold n (SchemeComplexPoint
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := schemeAnalyticTN_isComplexManifold _ n

omit [IsSeparated (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
  [QuasiCompact (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))] in
/-- ENTIRE actual original coefficient determinant ideal equals the SAME restricted default Jacobian ideal. -/
theorem span_coefficientDet_eq_span_restricted
    (q : SchemeComplexPoint ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    Ideal.span {coefficientGerm ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n q
      (affineOpenDet π n U v hv z hz)} =
        Ideal.span {preferredJacobian (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) (U.2.fromSpec ≫ π) n q} := by
  let := smoothOfRelativeDimension_of_etale_coordinates z hz
  have hz' : letI := affinePointFieldAlgebra (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
      (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale := by
    rw [canonicalFieldAlgebra_eq]
    exact hz
  have he := affineOpenJacobianIdeal_map_eq_span_preferred
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π n U v hv q z hz'
  rw [affineOpenJacobianIdeal_eq_span_det π n U v hv z hz,
    Ideal.map_span,Set.image_singleton] at he
  exact he

/-- WHOLE original determinant ideal equals the actual original-open pullback of the WHOLE global Jacobian ideal. -/
theorem span_coefficientDet_eq_map_global
    (q : SchemeComplexPoint ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    Ideal.span {coefficientGerm ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n q
      (affineOpenDet π n U v hv z hz)} =
      (Ideal.span {preferredJacobian (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π n
        (affineOpenPointMap (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec q)}).map
          (affineOpenGermPullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec n q).toRingHom := by
  let := smoothOfRelativeDimension_of_etale_coordinates z hz
  exact (span_coefficientDet_eq_span_restricted π n U v hv z hz q).trans
    (span_preferredJacobian_affineOpen (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec n q)

private theorem mul_mem_iff_of_span_eq {A : Type} [CommRing A]
    (K : Ideal A) (a b g : A) (h : Ideal.span {a} = Ideal.span {b}) :
    g * a ∈ K ↔ g * b ∈ K := by
  have he := congrArg (fun J : Ideal A => K.colon (J : Set A)) h
  have hm := congrArg (fun J : Ideal A => g ∈ J) he
  exact Iff.of_eq (by simpa only [Ideal.colon_span,Submodule.mem_colon_singleton,smul_eq_mul] using hm)

/-- Every WHOLE global source germ has the actual original determinant/global-Jacobian membership equivalence. -/
theorem openPullback_mul_det_mem_iff
    (q : SchemeComplexPoint ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
    (K : Ideal (HolGerm (ComplexModel n))) (H : HolGerm (ComplexModel n)) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    affineOpenGermPullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec n q H *
      coefficientGerm ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n q
        (affineOpenDet π n U v hv z hz) ∈ K ↔
    affineOpenGermPullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec n q
      (H * preferredJacobian (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π n
        (affineOpenPointMap (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec q)) ∈ K := by
  let := smoothOfRelativeDimension_of_etale_coordinates z hz
  have hspan := span_coefficientDet_eq_map_global π n U v hv z hz q
  rw [Ideal.map_span,Set.image_singleton] at hspan
  change Ideal.span {_} = Ideal.span {
    affineOpenGermPullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec n q
      (preferredJacobian (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π n
        (affineOpenPointMap (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec q))} at hspan
  rw [map_mul]
  exact mul_mem_iff_of_span_eq K _ _
    (affineOpenGermPullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec n q H) hspan

/-- In particular EVERY original base native analytic germ is pulled through the SAME original π;
no algebraic-test, determinant matching or input-point comparison premise is supplied. -/
theorem baseNativePullback_mul_det_mem_iff
    (q : SchemeComplexPoint ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
    (K : Ideal (HolGerm (ComplexModel n))) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    ∀ g : NativeHolGerm n (SchemeComplexPoint (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
      (schemeComplexPointMap (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π rfl
        (affineOpenPointMap (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec q)),
    let H := NativeHolGerm.chartEquiv (affineOpenPointMap (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec q)
      (schemeMorphismNativeGermPullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π n n
        (affineOpenPointMap (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec q) g)
    affineOpenGermPullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec n q H *
      coefficientGerm ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n q
        (affineOpenDet π n U v hv z hz) ∈ K ↔
    affineOpenGermPullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec n q
      (H * preferredJacobian (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π n
        (affineOpenPointMap (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec q)) ∈ K := by
  let := smoothOfRelativeDimension_of_etale_coordinates z hz
  intro g
  exact openPullback_mul_det_mem_iff π n U v hv z hz q K _

end EnvelopeProperty.Char0.NativeAffineOpenJacobianMembership
