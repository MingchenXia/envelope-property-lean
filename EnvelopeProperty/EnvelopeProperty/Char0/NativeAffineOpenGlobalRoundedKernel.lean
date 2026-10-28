import EnvelopeProperty.Char0.AffineOpenGlobalRoundedKernel
import EnvelopeProperty.Char0.NativeAffineOpenJacobianMembership

/-! # The SAME whole global quotient on the actual canonical original affine open -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeAffineOpenGlobalRoundedKernel

open AlgebraicGeometry CategoryTheory Opposite
open RoundedCanonicalModule NativeAffineOpenJacobianMembership
open AffineOpenGlobalRoundedKernel

variable {R : Type} [CommRing R] [Algebra ℂ R] {Y : Scheme}

private def originalOpenCoefficientHom (π : Y ⟶ Spec (.of R)) (U : Y.affineOpens) :
    letI := (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))).sectionsAlgebra U.1
    R →ₐ[ℂ] Γ(Y,U.1) := by
  letI := (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))).sectionsAlgebra U.1
  exact { sectionsHom π U.1 with commutes' := fun r =>
    (RingHom.congr_fun (sectionsHom_comp_specMap π (algebraMap ℂ R) U.1) r).symm }

/-- The SAME whole GLOBAL quotient and its actual original unit pullback have the
ENTIRE original rounded affine ideal colon the SAME original determinant as kernel.
All original actions, coefficient factorization and rounded comparisons are derived. -/
theorem affineOpenGlobalQuotient_sectionKernel_eq_det_colon
    (π : Y ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
    (U : Y.affineOpens) (v : Fin n → Γ(Y,U.1))
    (hv : Etale (toAffineSpace (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) U.1 v))
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (r : ℚ) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
    letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
    letI : Smooth (π ≫ f) := SmoothOfRelativeDimension.smooth n (π ≫ f)
    let Q := quotient (k := ℂ) f π n J hJ r
    let M := (Scheme.Modules.pullback U.2.fromSpec).obj Q
    let μ : AffineModuleFlatBaseChange.sections (R := Γ(Y,U.1))
        (𝟙 (Spec Γ(Y,U.1))) M :=
      Scheme.Modules.affinePullbackUnitTop U.2.fromSpec Q
        ((quotientDifferentialSection (k := ℂ) f π n J hJ r).val.app (.op ⊤) (1 : Γ(Y,⊤)))
    FlatSectionKernel.sectionKernel (R := Γ(Y,U.1)) (𝟙 (Spec Γ(Y,U.1))) M μ =
      ((RoundedSncIdealSheaf.rounded J hJ r).ideal U).colon
        {affineOpenDet π n U v hv z hz} := by
  intro f
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  let : Smooth (π ≫ f) := SmoothOfRelativeDimension.smooth n (π ≫ f)
  let := (π ≫ f).sectionsAlgebra U.1
  let φ := originalOpenCoefficientHom π U
  have hc : U.2.fromSpec ≫ π = Spec.map (CommRingCat.ofHom φ.toRingHom) :=
    fromSpec_comp_eq_specMap_sectionsHom π U
  have hv' : (MvPolynomial.aeval (R := ℂ) v).toRingHom.Etale :=
    (etale_toAffineSpace_iff (π ≫ f) U.2 v).mp hv
  let : SmoothOfRelativeDimension n (π ≫ CanonicalGeometry.affineStructuralMap ℂ (.of R)) := by
    change SmoothOfRelativeDimension n (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
    infer_instance
  let : Smooth (π ≫ CanonicalGeometry.affineStructuralMap ℂ (.of R)) :=
    SmoothOfRelativeDimension.smooth n _
  have hk := sourceAffineGlobalQuotient_sectionKernel_eq_jacobian_colon
    (.of R) Γ(Y,U.1) φ z hz π U.2.fromSpec hc v hv' J hJ r
  let : Algebra R Γ(Y,U.1) := (sectionsHom π U.1).toAlgebra
  change _ = _ at hk
  rw [← RoundedSncIdealSheaf.rounded_comap
    (π ≫ CanonicalGeometry.affineStructuralMap ℂ (.of R)) U.2.fromSpec J hJ r,
    idealOfSpecSheaf_comap_fromSpec] at hk
  exact hk

end EnvelopeProperty.Char0.NativeAffineOpenGlobalRoundedKernel
