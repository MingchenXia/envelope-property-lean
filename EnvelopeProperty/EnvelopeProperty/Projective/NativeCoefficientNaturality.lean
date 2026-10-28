import EnvelopeProperty.Projective.NormalizedCoefficientMap
import EnvelopeProperty.Projective.NativeBaseChange
import EnvelopeProperty.Projective.IdealRepresentation
import EnvelopeProperty.Berkovich.SchemeRelativeBaseChange

/-! # Whole actual native projective points commute with coefficient restriction -/
open scoped Classical Polynomial NNReal Topology
open CategoryTheory AlgebraicGeometry
open EnvelopeProperty.ProjBerk
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Berkovich.NormalizedProjectiveSpectrum
variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}

private theorem chart_value_coefficientComap (φ : R →+* S) (x : NormalizedProjectiveSpectrum S n)
    (j : Fin (n+1)) (hj : x.1.val (MvPolynomial.X j) = 1) (a : CoordinateRing R j) :
    (coordinateChartMap j
      ⟨coefficientComap φ x, by
        change x.1.val (MvPolynomial.map φ (MvPolynomial.X j)) ≠ 0
        rw [MvPolynomial.map_X,hj]; exact one_ne_zero⟩).val a =
    (coordinateChartMap j
      ⟨x, by change x.1.val (MvPolynomial.X j) ≠ 0; rw [hj]; exact one_ne_zero⟩).val
        (MvPolynomial.map φ a) := by
  obtain ⟨d,F,hF,rfl⟩ := exists_homogeneous_coordinateDehom j a
  have hR := coordinateChartMap_val_dehom_homogeneousComponent j
    (⟨coefficientComap φ x, by
      change x.1.val (MvPolynomial.map φ (MvPolynomial.X j)) ≠ 0
      rw [MvPolynomial.map_X,hj]; exact one_ne_zero⟩) F d
  have hS := coordinateChartMap_val_dehom_homogeneousComponent j
    (⟨x, by change x.1.val (MvPolynomial.X j) ≠ 0; rw [hj]; exact one_ne_zero⟩)
      (MvPolynomial.map φ F) d
  rw [MvPolynomial.homogeneousComponent_eq_self hF] at hR
  simp only [MvPolynomial.homogeneousComponent_eq_self (hF.map φ),hj,one_pow,mul_one] at hS
  have hjR : (coefficientComap φ x).1.val (MvPolynomial.X j) = 1 := by
    change x.1.val (MvPolynomial.map φ (MvPolynomial.X j)) = 1
    rw [MvPolynomial.map_X,hj]
  simp only [hjR,one_pow,mul_one] at hR
  rw [← coordinateDehom_map]
  exact hR.trans hS.symm

/-- Actual whole native residue-field-valued projective points commute with
EVERY genuine coefficient homomorphism. Original commutative rings are
arbitrary; no field, boundedness, injectivity or pointwise certificate. -/
theorem nativePoint_coefficientComap (φ : R →+* S) (x : NormalizedProjectiveSpectrum S n) :
    nativePoint (coefficientComap φ x) = SchemeValuedPoint.map (nativeCoefficientMap φ) (nativePoint x) := by
  obtain ⟨j,hj⟩ := exists_val_X_eq_one x
  have hx : (nativePoint x).point ∈ nativeCoordinateOpen (R := S) j := by
    change x.1.val (MvPolynomial.X j) ≠ 0
    rw [hj]; exact one_ne_zero
  have hle : nativeCoordinateOpen (R := S) j ≤
      (nativeCoefficientMap φ) ⁻¹ᵁ nativeCoordinateOpen (R := R) j := by
    rw [nativeCoefficientMap_preimage_coordinateOpen]
  have hy : (SchemeValuedPoint.map (nativeCoefficientMap φ) (nativePoint x)).point ∈
      nativeCoordinateOpen (R := R) j := hle hx
  have hz : (nativePoint (coefficientComap φ x)).point ∈ nativeCoordinateOpen (R := R) j := by
    change x.1.val (MvPolynomial.map φ (MvPolynomial.X j)) ≠ 0
    rw [MvPolynomial.map_X,hj]; exact one_ne_zero
  have h := (nativeAbsoluteCoordinateHomeomorph (R := R) j).injective
    (show nativeAbsoluteCoordinateHomeomorph j ⟨nativePoint (coefficientComap φ x),hz⟩ =
        nativeAbsoluteCoordinateHomeomorph j
          ⟨SchemeValuedPoint.map (nativeCoefficientMap φ) (nativePoint x),hy⟩ from by
      apply Spectrum.ext_val
      intro a
      rw [nativeAbsoluteCoordinateHomeomorph_val_apply,
        nativePoint_eval_coordinateChart, nativeAbsoluteCoordinateHomeomorph_val_apply]
      have heval := SchemeValuedPoint.eval_map (nativeCoefficientMap φ) (nativePoint x)
        (nativeCoordinateOpen (R := R) j) hy ((nativeCoordinateSectionsIso j).hom a)
      have hres := SchemeValuedPoint.eval_restrict (nativePoint x)
        ((nativeCoefficientMap φ) ⁻¹ᵁ nativeCoordinateOpen (R := R) j)
        (nativeCoordinateOpen (R := S) j) hle hx
        ((nativeCoefficientMap φ).app (nativeCoordinateOpen (R := R) j)
          ((nativeCoordinateSectionsIso j).hom a))
      have hs := congrArg (fun f => f.hom a) (nativeCoefficientMap_coordinateSections φ j)
      change (nativeCoefficientMap φ).appLE _ _ hle ((nativeCoordinateSectionsIso j).hom a) =
        (nativeCoordinateSectionsIso j).hom (MvPolynomial.map φ a) at hs
      have hev : SchemeValuedPoint.eval
          (SchemeValuedPoint.map (nativeCoefficientMap φ) (nativePoint x))
          (nativeCoordinateOpen (R := R) j) hy ((nativeCoordinateSectionsIso j).hom a) =
        SchemeValuedPoint.eval (nativePoint x) (nativeCoordinateOpen (R := S) j) hx
          ((nativeCoordinateSectionsIso j).hom (MvPolynomial.map φ a)) := by
        rw [heval,← hres]
        exact congrArg (SchemeValuedPoint.eval (nativePoint x)
          (nativeCoordinateOpen (R := S) j) hx) hs
      rw [hev,nativePoint_eval_coordinateChart]
      exact chart_value_coefficientComap φ x j hj a)
  exact congrArg Subtype.val h
end EnvelopeProperty.Berkovich.NormalizedProjectiveSpectrum

namespace EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}
variable {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}

/-- The actual whole relative normalized point restricts along EVERY genuine
coefficient map preserving the original prescribed base valuations. -/
def coefficientComap (φ : R →+* S) (hφ : ∀ a, w (φ a) = v a)
    (x : RelativeNormalizedProjectiveSpectrum w n) : RelativeNormalizedProjectiveSpectrum v n :=
  ⟨NormalizedProjectiveSpectrum.coefficientComap φ x.1, by
    intro a
    change x.1.1.val (MvPolynomial.map φ (MvPolynomial.C a)) = v a
    rw [MvPolynomial.map_C,x.2,hφ]⟩

/-- EVERY original form retains its full actual coefficient-pullback value. -/
theorem coefficientComap_val (φ : R →+* S) (hφ : ∀ a, w (φ a) = v a)
    (x : RelativeNormalizedProjectiveSpectrum w n) (F : MvPolynomial (Fin (n+1)) R) :
    (coefficientComap φ hφ x).1.1.val F = x.1.1.val (MvPolynomial.map φ F) := rfl

/-- Whole original prescribed-base native points commute with actual
coefficient pullback, preserving the SAME original residue valuation. -/
theorem nativeHomeomorph_coefficientComap (φ : R →+* S) (hφ : ∀ a, w (φ a) = v a)
    (x : RelativeNormalizedProjectiveSpectrum w n) :
    nativeHomeomorph v (coefficientComap φ hφ x) =
      RelativeSchemeValuedPoint.mapOverBase φ hφ (nativeCoefficientMap φ)
        (nativeCoefficientMap_over_base φ) (nativeHomeomorph w x) :=
  Subtype.ext (NormalizedProjectiveSpectrum.nativePoint_coefficientComap φ x.1)

/-- The original polynomialRestriction of EVERY actual Gauss-base point is
EXACTLY its literal native coefficient-scheme projection over the original
base, including the whole residue valuation, not only original form values. -/
theorem nativeHomeomorph_polynomialRestriction (v : Valuation R ℝ≥0) (r : ℝ≥0)
    (x : RelativeNormalizedProjectiveSpectrum (gaussValuation v r) n) :
    nativeHomeomorph v (polynomialRestriction v r x) =
      RelativeSchemeValuedPoint.mapOverBase Polynomial.C
        (fun a => Spectrum.gauss_val_C (Spectrum.ofValuation v) r a)
        (nativeCoefficientMap Polynomial.C) (nativeCoefficientMap_over_base Polynomial.C)
        (nativeHomeomorph (gaussValuation v r) x) :=
  Subtype.ext (NormalizedProjectiveSpectrum.nativePoint_coefficientComap Polynomial.C x.1)
end EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
