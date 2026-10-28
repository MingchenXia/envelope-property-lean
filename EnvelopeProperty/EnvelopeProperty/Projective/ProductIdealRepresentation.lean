/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.ModelIdealRepresentation
import EnvelopeProperty.Projective.GaussProductModel

/-!
# Arbitrary actual product ideal sheaves and original whole Gauss model functions

The true polynomial-line scheme isomorphism transports every actual ideal
sheaf to its genuinely constructed homogeneous representative. Bounded MODEL
coefficients and true native centers give exact intrinsic norm and logarithm
identities, with chart-finite global continuity without Noetherianity. Over
k[t], its actual Noetherian coefficient ring gives the paper phi functions
and continuity for every actual product ideal sheaf. No bound on an entire
nontrivially valued field, radical replacement or analytic coherent-sheaf
identification is asserted.
-/

open scoped Classical Polynomial NNReal ENNReal Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjBerk
variable {R : Type u} [CommRing R] {n : ℕ}
private local instance representationProductProjectiveProper :
    IsProper (nativeStructureMap (R := R[X]) (n := n)) := nativeStructureMap_isProper
private local instance representationProductProper :
    IsProper (nativePolynomialLineProductStructure (R := R) (n := n)) :=
  nativePolynomialLineProductStructure_isProper

/-- The actual original homogeneous representative of any actual ideal sheaf on the genuine polynomial-line product. -/
def nativePolynomialLineProductRepresentative
    (I : (NativePolynomialLineProduct R n).IdealSheafData) :
    HomogeneousIdeal (ProjectiveGrading R[X] n) :=
  nativeHomogeneousRepresentative (I.comap (nativePolynomialLineProductIso R n).hom)

set_option backward.isDefEq.respectTransparency false in
/-- The actual constructed representative recovers the entire original ideal sheaf under the true scheme product isomorphism. -/
theorem nativePolynomialLineProductRepresentative_ideal_eq
    (I : (NativePolynomialLineProduct R n).IdealSheafData) :
    nativePolynomialLineProductIdeal (nativePolynomialLineProductRepresentative I) = I := by
  change (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R[X] n)
    (nativeHomogeneousRepresentative (I.comap (nativePolynomialLineProductIso R n).hom))).comap
      (nativePolynomialLineProductIso R n).inv = _
  rw [nativeHomogeneousRepresentative_quotientIdealSheaf,
    ← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

/-- An arbitrary actual product ideal sheaf has the genuine whole model norm of its constructed original homogeneous representative. -/
theorem modelIdealNorm_product_eq_homogeneousRepresentative
    {v : Valuation R[X] ℝ≥0} (hb : ∀ p, v p ≤ 1)
    (I : (NativePolynomialLineProduct R n).IdealSheafData)
    (x : RelativeNormalizedProjectiveSpectrum v n) :
    RelativeSchemeValuedPoint.modelIdealNorm I hb (nativePolynomialLineProductPoint x) =
      Spectrum.idealNorm (nativePolynomialLineProductRepresentative I).toIdeal x.1.1 := by
  have h := modelIdealNorm_nativePolynomialLineProductPoint hb
    (nativePolynomialLineProductRepresentative I) x
  rwa [nativePolynomialLineProductRepresentative_ideal_eq] at h

/-- The entire logarithmic model function of an arbitrary actual product ideal sheaf is the original homogeneous representative logarithm. -/
theorem modelIdealLog_product_eq_homogeneousRepresentative
    {v : Valuation R[X] ℝ≥0} (hb : ∀ p, v p ≤ 1)
    (I : (NativePolynomialLineProduct R n).IdealSheafData)
    (x : RelativeNormalizedProjectiveSpectrum v n) :
    RelativeSchemeValuedPoint.modelIdealLog I hb (nativePolynomialLineProductPoint x) =
      Spectrum.idealLog (nativePolynomialLineProductRepresentative I).toIdeal x.1.1 :=
  congrArg ENNReal.log (modelIdealNorm_product_eq_homogeneousRepresentative hb I x)

set_option backward.isDefEq.respectTransparency false in
/-- Actual coordinate finite generation after the true scheme product pullback gives global intrinsic ideal-norm continuity over any bounded polynomial coefficient ring. -/
theorem continuous_modelIdealNorm_product_of_coordinate_fg
    {v : Valuation R[X] ℝ≥0} (hb : ∀ p, v p ≤ 1)
    (I : (NativePolynomialLineProduct R n).IdealSheafData)
    (hfg : ∀ j : Fin (n + 1), (nativeCoordinateIdeal
      (I.comap (nativePolynomialLineProductIso R n).hom) j).FG) :
    Continuous (RelativeSchemeValuedPoint.modelIdealNorm I hb :
      RelativeSchemeValuedPoint v (nativePolynomialLineProductStructure (R := R) (n := n)) → ℝ≥0∞) := by
  let e := nativePolynomialLineProductIso R n
  let invMap := RelativeSchemeValuedPoint.map (v := v) e.inv nativePolynomialLineProductIso_inv_over_base
  have hc := (RelativeNormalizedProjectiveSpectrum.continuous_modelIdealNorm_of_coordinate_fg
    v hb (I.comap e.hom) hfg).comp
      (RelativeSchemeValuedPoint.continuous_map e.inv nativePolynomialLineProductIso_inv_over_base)
  refine hc.congr fun y => ?_
  have h := RelativeSchemeValuedPoint.modelIdealNorm_comap I e.hom
    nativePolynomialLineProductIso_over_base hb (invMap y)
  refine h.trans ?_
  congr 1
  apply Subtype.ext
  change SchemeValuedPoint.map e.hom (SchemeValuedPoint.map e.inv y.1) = y.1
  rw [← SchemeValuedPoint.map_comp, Iso.inv_hom_id, SchemeValuedPoint.map_id]

/-- Actual chart finite generation gives global logarithmic continuity on the true polynomial product, including zero ideals and negative infinity. -/
theorem continuous_modelIdealLog_product_of_coordinate_fg
    {v : Valuation R[X] ℝ≥0} (hb : ∀ p, v p ≤ 1)
    (I : (NativePolynomialLineProduct R n).IdealSheafData)
    (hfg : ∀ j : Fin (n + 1), (nativeCoordinateIdeal
      (I.comap (nativePolynomialLineProductIso R n).hom) j).FG) :
    Continuous (RelativeSchemeValuedPoint.modelIdealLog I hb :
      RelativeSchemeValuedPoint v (nativePolynomialLineProductStructure (R := R) (n := n)) → EReal) :=
  ENNReal.continuous_log.comp (continuous_modelIdealNorm_product_of_coordinate_fg hb I hfg)


section Paper
variable {k : Type u} [Field k]

/-- Every actual product ideal sheaf's true Gauss model norm is an original whole phiNorm with genuinely constructed homogeneous coefficients. -/
theorem modelIdealNorm_gaussProductPoint_eq_phiNorm
    (I : (NativePolynomialLineProduct k n).IdealSheafData) (x : ProjBerk k n) :
    RelativeSchemeValuedPoint.modelIdealNorm I gaussModelCoefficient_le_one (gaussProductPoint x) =
      phiNorm ((nativePolynomialLineProductRepresentative I).toIdeal.map
        (polynomialCoefficientSwap k (Fin (n + 1))).toRingHom) x := by
  have h := phiNorm_eq_gaussProductModelIdealNorm (nativePolynomialLineProductRepresentative I) x
  rw [nativePolynomialLineProductRepresentative_ideal_eq] at h
  exact h.symm

/-- Every actual product ideal sheaf's true Gauss model logarithm is an original whole phiIdeal, retaining zero ideals and negative infinity. -/
theorem modelIdealLog_gaussProductPoint_eq_phiIdeal
    (I : (NativePolynomialLineProduct k n).IdealSheafData) (x : ProjBerk k n) :
    RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one (gaussProductPoint x) =
      phiIdeal ((nativePolynomialLineProductRepresentative I).toIdeal.map
        (polynomialCoefficientSwap k (Fin (n + 1))).toRingHom) x := by
  have h := phiIdeal_eq_gaussProductModelIdealLog (nativePolynomialLineProductRepresentative I) x
  rw [nativePolynomialLineProductRepresentative_ideal_eq] at h
  exact h.symm

/-- The entire true-center Gauss logarithmic model function of any actual product ideal sheaf is represented by an original polynomial ideal. -/
theorem exists_phiIdeal_modelIdealLog
    (I : (NativePolynomialLineProduct k n).IdealSheafData) :
    ∃ J : Ideal (MvPolynomial (Fin (n + 1)) k)[X],
      ∀ x : ProjBerk k n,
        RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one (gaussProductPoint x) =
          phiIdeal J x :=
  ⟨(nativePolynomialLineProductRepresentative I).toIdeal.map
      (polynomialCoefficientSwap k (Fin (n + 1))).toRingHom,
    modelIdealLog_gaussProductPoint_eq_phiIdeal I⟩

/-- Every actual product ideal sheaf has a continuous true Gauss model norm on the original paper projective point space. -/
theorem continuous_modelIdealNorm_gaussProductPoint
    (I : (NativePolynomialLineProduct k n).IdealSheafData) :
    Continuous fun x : ProjBerk k n =>
      RelativeSchemeValuedPoint.modelIdealNorm I gaussModelCoefficient_le_one (gaussProductPoint x) :=
  (continuous_modelIdealNorm_product_of_coordinate_fg gaussModelCoefficient_le_one I
    (nativeCoordinateIdeal_fg (I.comap (nativePolynomialLineProductIso k n).hom))).comp
      continuous_gaussProductPoint

/-- Every actual product ideal sheaf has a continuous true Gauss logarithmic model function on the original paper projective point space, including negative infinity. -/
theorem continuous_modelIdealLog_gaussProductPoint
    (I : (NativePolynomialLineProduct k n).IdealSheafData) :
    Continuous fun x : ProjBerk k n =>
      RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one (gaussProductPoint x) :=
  ENNReal.continuous_log.comp (continuous_modelIdealNorm_gaussProductPoint I)

end Paper
end EnvelopeProperty.ProjBerk
