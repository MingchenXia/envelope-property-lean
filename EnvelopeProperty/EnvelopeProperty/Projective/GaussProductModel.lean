/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeBaseChange
import EnvelopeProperty.Projective.GaussModelBridge
import EnvelopeProperty.Berkovich.SchemeModelIdealPullback

/-!
# Genuine polynomial-Gauss model functions on the actual product scheme

The actual projective model over R[t] is transported through the proved
whole scheme base-change isomorphism to the actual product over Spec R.
Its genuine kernel IdealSheafData is pulled back by the inverse isomorphism;
the entire fixed-base valued point and intrinsic proper-center ideal norm
and logarithm commute. Specializing the true bounded k[t] Gauss point gives
the existing whole phiNorm and phiIdeal of the original homogeneous ideal
image. No bound on an entire nontrivially valued field, radical replacement,
product certificate or analytic coherent-sheaf comparison is asserted.
-/

open scoped Classical Polynomial NNReal ENNReal Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjBerk
variable {R : Type u} [CommRing R] {n : ℕ}

/-- The actual projective-space product with the polynomial coefficient base. -/
abbrev NativePolynomialLineProduct (R : Type u) [CommRing R] (n : ℕ) : Scheme.{u} :=
  pullback (nativeStructureMap (R := R) (n := n))
    (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))

/-- The actual product's structure morphism to the whole polynomial base ring. -/
def nativePolynomialLineProductStructure : NativePolynomialLineProduct R n ⟶ Spec (CommRingCat.of R[X]) :=
  pullback.snd _ _

/-- The whole product isomorphism preserves the actual polynomial coefficient structure. -/
theorem nativePolynomialLineProductIso_over_base :
    (nativePolynomialLineProductIso R n).hom ≫ nativePolynomialLineProductStructure =
      nativeStructureMap := nativeCoefficientBaseChangeIso_hom_snd Polynomial.C

/-- The inverse whole product isomorphism preserves the same actual base structure. -/
theorem nativePolynomialLineProductIso_inv_over_base :
    (nativePolynomialLineProductIso R n).inv ≫ nativeStructureMap =
      nativePolynomialLineProductStructure := by
  rw [← nativePolynomialLineProductIso_over_base (R := R) (n := n),
    Iso.inv_hom_id_assoc]

/-- Actual projective properness and the genuine product isomorphism make the whole polynomial-base product model proper. -/
theorem nativePolynomialLineProductStructure_isProper :
    IsProper (nativePolynomialLineProductStructure (R := R) (n := n)) := by
  have := nativeStructureMap_isProper (R := R[X]) (n := n)
  have h : IsProper ((nativePolynomialLineProductIso R n).inv ≫ nativeStructureMap) := by
    infer_instance
  rwa [nativePolynomialLineProductIso_inv_over_base] at h

private local instance productPolynomialModelProper :
    IsProper (nativePolynomialLineProductStructure (R := R) (n := n)) :=
  nativePolynomialLineProductStructure_isProper
private local instance productProjectiveModelProper :
    IsProper (nativeStructureMap (R := R[X]) (n := n)) := nativeStructureMap_isProper

/-- The actual original homogeneous kernel ideal sheaf transported to the genuine product. -/
def nativePolynomialLineProductIdeal (J : HomogeneousIdeal (ProjectiveGrading R[X] n)) :
    (NativePolynomialLineProduct R n).IdealSheafData :=
  (nativeHomogeneousIdealSheaf J).comap (nativePolynomialLineProductIso R n).inv

set_option backward.isDefEq.respectTransparency false in
/-- The transported genuine kernel sheaf is exactly the kernel of the actual original quotient map into the product, retaining the original nilpotents. -/
theorem nativePolynomialLineProductIdeal_eq_kernel
    (J : HomogeneousIdeal (ProjectiveGrading R[X] n)) :
    nativePolynomialLineProductIdeal J =
      (GradedQuotient.quotientSchemeMap (ProjectiveGrading R[X] n) J ≫
        (nativePolynomialLineProductIso R n).hom).ker := by
  let q := GradedQuotient.quotientSchemeMap (ProjectiveGrading R[X] n) J
  let e := nativePolynomialLineProductIso R n
  have hs : IsPullback (𝟙 _) (q ≫ e.hom) q e.inv :=
    IsPullback.of_horiz_isIso ⟨by simp only [Category.id_comp, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]⟩
  have h := hs.flip
  change q.ker.comap e.inv = _
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion q e.inv,
    ← Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom (pullback.fst e.inv q),
    h.isoPullback_hom_fst]

/-- The entire normalized polynomial-base point is transported through the actual scheme isomorphism. -/
def nativePolynomialLineProductPoint {v : Valuation R[X] ℝ≥0}
    (x : RelativeNormalizedProjectiveSpectrum v n) :
    RelativeSchemeValuedPoint v (nativePolynomialLineProductStructure (R := R) (n := n)) :=
  RelativeSchemeValuedPoint.map (nativePolynomialLineProductIso R n).hom
    nativePolynomialLineProductIso_over_base
    (RelativeNormalizedProjectiveSpectrum.nativeHomeomorph v x)

/-- The whole first native projection is the original actual graded coefficient map of the entire projective model point. -/
theorem nativePolynomialLineProductPoint_fst {v : Valuation R[X] ℝ≥0}
    (x : RelativeNormalizedProjectiveSpectrum v n) :
    SchemeValuedPoint.map (pullback.fst (nativeStructureMap (R := R) (n := n))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))))
      (nativePolynomialLineProductPoint x).1 =
      SchemeValuedPoint.map (nativeCoefficientMap Polynomial.C)
        (RelativeNormalizedProjectiveSpectrum.nativeHomeomorph v x).1 := by
  change SchemeValuedPoint.map _ (SchemeValuedPoint.map _ _) = _
  rw [← SchemeValuedPoint.map_comp, nativePolynomialLineProductIso,
    nativeCoefficientBaseChangeIso_hom_fst]

/-- The entire second native projection is the original prescribed polynomial coefficient base point, not only its parameter value. -/
theorem nativePolynomialLineProductPoint_base {v : Valuation R[X] ℝ≥0}
    (x : RelativeNormalizedProjectiveSpectrum v n) :
    SchemeValuedPoint.map nativePolynomialLineProductStructure (nativePolynomialLineProductPoint x).1 =
      SchemeValuedPoint.basePoint v := (nativePolynomialLineProductPoint x).2

/-- Whole inverse scheme maps recover the entire original fixed-base native point. -/
theorem nativePolynomialLineProductPoint_inverse {v : Valuation R[X] ℝ≥0}
    (x : RelativeNormalizedProjectiveSpectrum v n) :
    RelativeSchemeValuedPoint.map (nativePolynomialLineProductIso R n).inv
      nativePolynomialLineProductIso_inv_over_base (nativePolynomialLineProductPoint x) =
        RelativeNormalizedProjectiveSpectrum.nativeHomeomorph v x := by
  apply Subtype.ext
  change SchemeValuedPoint.map _ (SchemeValuedPoint.map _ _) = _
  rw [← SchemeValuedPoint.map_comp, Iso.hom_inv_id, SchemeValuedPoint.map_id]

/-- The true proper-model center is the actual image of the original projective-model center. -/
theorem center_nativePolynomialLineProductPoint {v : Valuation R[X] ℝ≥0}
    (hb : ∀ p, v p ≤ 1) (x : RelativeNormalizedProjectiveSpectrum v n) :
    (nativePolynomialLineProductIso R n).hom
      (RelativeSchemeValuedPoint.center hb (RelativeNormalizedProjectiveSpectrum.nativeHomeomorph v x)) =
        RelativeSchemeValuedPoint.center hb (nativePolynomialLineProductPoint x) :=
  RelativeSchemeValuedPoint.center_map _ nativePolynomialLineProductIso_over_base hb _

/-- The genuine polynomial product valued point varies continuously in its entire normalized model point. -/
@[fun_prop]
theorem continuous_nativePolynomialLineProductPoint (v : Valuation R[X] ℝ≥0) :
    Continuous (nativePolynomialLineProductPoint (R := R) (n := n) (v := v)) :=
  (RelativeSchemeValuedPoint.continuous_map _ _).comp
    (RelativeNormalizedProjectiveSpectrum.nativeHomeomorph v).continuous

/-- Genuine geometric ideal pullback preserves the entire intrinsic polynomial-model ideal norm on the actual product. -/
theorem modelIdealNorm_nativePolynomialLineProductPoint
    {v : Valuation R[X] ℝ≥0} (hb : ∀ p, v p ≤ 1)
    (J : HomogeneousIdeal (ProjectiveGrading R[X] n)) (x : RelativeNormalizedProjectiveSpectrum v n) :
    RelativeSchemeValuedPoint.modelIdealNorm (nativePolynomialLineProductIdeal J) hb
      (nativePolynomialLineProductPoint x) = Spectrum.idealNorm J.toIdeal x.1.1 := by
  rw [nativePolynomialLineProductIdeal, RelativeSchemeValuedPoint.modelIdealNorm_comap
    (nativeHomogeneousIdealSheaf J) (nativePolynomialLineProductIso R n).inv
    nativePolynomialLineProductIso_inv_over_base hb (nativePolynomialLineProductPoint x),
    nativePolynomialLineProductPoint_inverse]
  exact RelativeNormalizedProjectiveSpectrum.modelIdealNorm_quotient_eq_idealNorm v hb J x

/-- The actual product's intrinsic logarithmic model ideal function preserves the original whole ideal, including zero and negative infinity. -/
theorem modelIdealLog_nativePolynomialLineProductPoint
    {v : Valuation R[X] ℝ≥0} (hb : ∀ p, v p ≤ 1)
    (J : HomogeneousIdeal (ProjectiveGrading R[X] n)) (x : RelativeNormalizedProjectiveSpectrum v n) :
    RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal J) hb
      (nativePolynomialLineProductPoint x) = Spectrum.idealLog J.toIdeal x.1.1 :=
  congrArg ENNReal.log (modelIdealNorm_nativePolynomialLineProductPoint hb J x)

section Paper
variable {k : Type u} [Field k]

/-- The old entire Gauss model point as a genuine point of the actual projective-affine-line product over its bounded polynomial coefficient valuation. -/
def gaussProductPoint (x : ProjBerk k n) :
    RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (nativePolynomialLineProductStructure (R := k) (n := n)) :=
  nativePolynomialLineProductPoint (gaussModelPoint x)

/-- The actual product point is continuous in the original normalized projective point. -/
@[fun_prop]
theorem continuous_gaussProductPoint : Continuous (gaussProductPoint (k := k) (n := n)) :=
  (continuous_nativePolynomialLineProductPoint _).comp continuous_gaussModelPoint

/-- The actual product's true homogeneous kernel model norm is the original entire old Gauss ideal norm. -/
theorem phiNorm_eq_gaussProductModelIdealNorm
    (J : HomogeneousIdeal (ProjectiveGrading k[X] n)) (x : ProjBerk k n) :
    phiNorm (J.toIdeal.map (polynomialCoefficientSwap k (Fin (n + 1))).toRingHom) x =
      RelativeSchemeValuedPoint.modelIdealNorm (nativePolynomialLineProductIdeal J)
        gaussModelCoefficient_le_one (gaussProductPoint x) := by
  change _ = RelativeSchemeValuedPoint.modelIdealNorm (nativePolynomialLineProductIdeal J)
    gaussModelCoefficient_le_one (nativePolynomialLineProductPoint (gaussModelPoint x))
  rw [modelIdealNorm_nativePolynomialLineProductPoint,
    phiNorm_eq_nativeModelIdealNorm, RelativeNormalizedProjectiveSpectrum.modelIdealNorm_quotient_eq_idealNorm]

/-- The actual product's intrinsic logarithmic kernel model function equals the old phi_I of the full original ideal image, including negative infinity. -/
theorem phiIdeal_eq_gaussProductModelIdealLog
    (J : HomogeneousIdeal (ProjectiveGrading k[X] n)) (x : ProjBerk k n) :
    phiIdeal (J.toIdeal.map (polynomialCoefficientSwap k (Fin (n + 1))).toRingHom) x =
      RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal J)
        gaussModelCoefficient_le_one (gaussProductPoint x) := by
  rw [phiIdeal_eq_log_phiNorm]
  exact congrArg ENNReal.log (phiNorm_eq_gaussProductModelIdealNorm J x)

end Paper
end EnvelopeProperty.ProjBerk
