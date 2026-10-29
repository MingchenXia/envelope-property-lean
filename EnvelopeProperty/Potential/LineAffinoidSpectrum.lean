import EnvelopeProperty.Potential.LineAffinoidAlgebra

/-! # The whole original bounded spectrum of a standard-affinoid function ring -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)
local instance : Fintype U.boundary := U.rationalBoundaryFintype

/-- The ORIGINAL polynomial map into the actual seminormed rational copy. -/
def normedPolynomialMap : K[X] →+* U.NormedRationalFunctions :=
  U.normedRationalEquiv.symm.toRingHom.comp (algebraMap K[X] U.RationalFunctions)

/-- The actual product of all the other original coordinates, retaining their original indices. -/
def holeComplementPolynomial (j : Fin m) : K[X] :=
  ∏ i ∈ Finset.univ.erase j, (X-C (U.holeCenter i))

theorem holeCoordinate_mul_complement (j : Fin m) :
    (X-C (U.holeCenter j))*U.holeComplementPolynomial j = U.denominatorPolynomial := by
  classical
  exact Finset.mul_prod_erase Finset.univ (fun i => X-C (U.holeCenter i)) (Finset.mem_univ j)

/-- The genuine coordinate inverse is the original complementary product divided by the original total product. -/
def rationalHoleInverse (j : Fin m) : U.RationalFunctions :=
  algebraMap K[X] U.RationalFunctions (U.holeComplementPolynomial j) *
    IsLocalization.Away.invSelf U.denominatorPolynomial

theorem holeCoordinate_mul_rationalHoleInverse (j : Fin m) :
    algebraMap K[X] U.RationalFunctions (X-C (U.holeCenter j))*U.rationalHoleInverse j = 1 := by
  rw [rationalHoleInverse,← mul_assoc,← map_mul,U.holeCoordinate_mul_complement,
    IsLocalization.Away.mul_invSelf]

def normedHoleInverse (j : Fin m) : U.NormedRationalFunctions :=
  U.normedRationalEquiv.symm (U.rationalHoleInverse j)

theorem normedPolynomialMap_mul_holeInverse (j : Fin m) :
    U.normedPolynomialMap (X-C (U.holeCenter j))*U.normedHoleInverse j = 1 := by
  apply U.normedRationalEquiv.injective
  rw [map_mul,map_one]
  change U.normedRationalEquiv (U.normedRationalEquiv.symm
    (algebraMap K[X] U.RationalFunctions (X-C (U.holeCenter j)))) *
    U.normedRationalEquiv (U.normedRationalEquiv.symm (U.rationalHoleInverse j)) = 1
  rw [RingEquiv.apply_symm_apply,RingEquiv.apply_symm_apply]
  exact U.holeCoordinate_mul_rationalHoleInverse j

theorem rationalValue_holeInverse (j : Fin m) (x : U.carrier) :
    U.rationalValue (U.rationalHoleInverse j) x = (val x.1 (X-C (U.holeCenter j)))⁻¹ := by
  have h := congrArg ((U.rationalPoint x).1.val) (U.holeCoordinate_mul_rationalHoleInverse j)
  rw [map_mul,map_one] at h
  change U.rationalValue (algebraMap K[X] U.RationalFunctions (X-C (U.holeCenter j))) x *
    U.rationalValue (U.rationalHoleInverse j) x = 1 at h
  rw [U.rationalValue_polynomial] at h
  apply eq_inv_of_mul_eq_one_left
  simpa only [mul_comm] using h

theorem nnnorm_normedHoleInverse_le (j : Fin m) :
    ‖U.normedHoleInverse j‖₊ ≤ (U.holeRadius j)⁻¹ := by
  rw [U.nnnorm_normedRationalFunctions]
  apply Finset.sup_le
  intro z _
  change U.rationalValue (U.rationalHoleInverse j) ⟨z.1,U.boundary_subset z.2⟩ ≤ _
  rw [U.rationalValue_holeInverse]
  have hcoord := (U.boundary_subset z.2).2 j
  exact (inv_le_inv₀ ((U.holeRadius_pos j).trans_le hcoord) (U.holeRadius_pos j)).mpr hcoord

theorem nnnorm_normedPolynomialMap_outer_le :
    ‖U.normedPolynomialMap (X-C U.center)‖₊ ≤ U.radius := by
  rw [U.nnnorm_normedRationalFunctions]
  apply Finset.sup_le
  intro z _
  change U.rationalValue (algebraMap K[X] U.RationalFunctions (X-C U.center))
    ⟨z.1,U.boundary_subset z.2⟩ ≤ U.radius
  rw [U.rationalValue_polynomial]
  exact (U.boundary_subset z.2).1

/-- EVERY original rational seminorm is determined by ALL original polynomial values. -/
theorem comap_normedPolynomialMap_injective : Function.Injective (Spectrum.comap U.normedPolynomialMap) := by
  intro x y h
  let ex := Spectrum.comap U.normedRationalEquiv.symm.toRingHom x
  let ey := Spectrum.comap U.normedRationalEquiv.symm.toRingHom y
  have he : ex = ey := by
    apply Spectrum.Away.comap_injective U.RationalFunctions U.denominatorPolynomial
    exact h
  apply Spectrum.ext_val
  intro f
  have hf := congrArg (fun z : Spectrum U.RationalFunctions => z.val (U.normedRationalEquiv f)) he
  change x.val (U.normedRationalEquiv.symm (U.normedRationalEquiv f)) =
    y.val (U.normedRationalEquiv.symm (U.normedRationalEquiv f)) at hf
  simpa only [RingEquiv.symm_apply_apply] using hf

variable [IsAlgClosed K]

/-- The whole actual prescribed-base bounded spectrum of the seminormed original rational ring. -/
abbrev RationalBoundedSpectrum := RelativeNormBoundedSpectrum w U.rationalCoefficients

/-- The genuine original point's contractive rational extension, with every original coefficient value. -/
def boundedRationalPoint (x : U.carrier) : U.RationalBoundedSpectrum :=
  ⟨⟨Spectrum.comap U.normedRationalEquiv.toRingHom (U.rationalPoint x).1,fun f => by
    exact (U.nnnorm_rationalEvaluation x (U.normedRationalEquiv f)).symm.le.trans
      (U.nnnorm_rationalEvaluation_le x f)⟩,fun a => by
    change U.rationalValue (algebraMap K[X] U.RationalFunctions (C a)) x = w a
    rw [U.rationalValue_polynomial]
    exact x.1.2 a⟩

theorem boundedRationalPoint_val (x : U.carrier) (f : U.NormedRationalFunctions) :
    (U.boundedRationalPoint x).1.1.val f = U.rationalValue (U.normedRationalEquiv f) x := rfl

theorem continuous_boundedRationalPoint : Continuous U.boundedRationalPoint := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  rw [Spectrum.continuous_iff]
  intro f
  exact U.continuous_rationalValue (U.normedRationalEquiv f)

/-- The whole actual polynomial point obtained by restricting an original bounded rational seminorm. -/
def rationalSpectrumPolynomial (y : U.RationalBoundedSpectrum) : RelativeSpectrum w K[X] :=
  ⟨Spectrum.comap U.normedPolynomialMap y.1.1,fun a => y.2 a⟩

omit [IsAlgClosed K] in
theorem rationalSpectrumPolynomial_mem (y : U.RationalBoundedSpectrum) :
    U.rationalSpectrumPolynomial y ∈ U.carrier := by
  constructor
  · exact (y.1.2 (U.normedPolynomialMap (X-C U.center))).trans U.nnnorm_normedPolynomialMap_outer_le
  · intro j
    have hinv := (y.1.2 (U.normedHoleInverse j)).trans (U.nnnorm_normedHoleInverse_le j)
    have hmul := congrArg y.1.1.val (U.normedPolynomialMap_mul_holeInverse j)
    rw [map_mul,map_one] at hmul
    have hone : (1 : ℝ≥0) ≤ y.1.1.val (U.normedPolynomialMap (X-C (U.holeCenter j))) /
        U.holeRadius j := by
      rw [div_eq_mul_inv]
      exact hmul.symm.le.trans (mul_le_mul' le_rfl hinv)
    change U.holeRadius j ≤ y.1.1.val (U.normedPolynomialMap (X-C (U.holeCenter j)))
    simpa only [one_mul] using (le_div_iff₀ (U.holeRadius_pos j)).mp hone

/-- The actual inverse map retains the whole original polynomial point. -/
def rationalSpectrumRestrict (y : U.RationalBoundedSpectrum) : U.carrier :=
  ⟨U.rationalSpectrumPolynomial y,U.rationalSpectrumPolynomial_mem y⟩

theorem rationalSpectrumRestrict_boundedRationalPoint (x : U.carrier) :
    U.rationalSpectrumRestrict (U.boundedRationalPoint x) = x := by
  apply Subtype.ext
  apply RelativeSpectrum.ext_val
  intro p
  exact U.rationalValue_polynomial p x

theorem boundedRationalPoint_rationalSpectrumRestrict (y : U.RationalBoundedSpectrum) :
    U.boundedRationalPoint (U.rationalSpectrumRestrict y) = y := by
  apply Subtype.ext
  apply Subtype.ext
  apply U.comap_normedPolynomialMap_injective
  apply Spectrum.ext_val
  intro p
  exact U.rationalValue_polynomial p (U.rationalSpectrumRestrict y)

/-- The entire original bounded rational spectrum is the actual affinoid, via ORIGINAL polynomial restriction. -/
def rationalSpectrumHomeomorph : U.RationalBoundedSpectrum ≃ₜ U.carrier := by
  let _ : CompactSpace U.carrier := isCompact_iff_compactSpace.mp U.isCompact_carrier
  exact (Continuous.homeoOfEquivCompactToT2 (f := Equiv.mk U.boundedRationalPoint
    U.rationalSpectrumRestrict U.rationalSpectrumRestrict_boundedRationalPoint
    U.boundedRationalPoint_rationalSpectrumRestrict) U.continuous_boundedRationalPoint).symm

/-- The ENTIRE actual prescribed-base bounded spectrum of the genuine completion. -/
abbrev AnalyticBoundedSpectrum := RelativeNormBoundedSpectrum w U.analyticCoefficients

/-- The entire actual bounded completion spectrum, identified by ORIGINAL polynomial restriction. -/
def analyticSpectrumHomeomorph : U.AnalyticBoundedSpectrum ≃ₜ U.carrier :=
  (RelativeNormBoundedSpectrum.completionHomeomorph w U.rationalCoefficients).trans
    U.rationalSpectrumHomeomorph

/-- The SAME original H(x)-evaluation gives the whole actual bounded completion point. -/
def boundedAnalyticPoint (x : U.carrier) : U.AnalyticBoundedSpectrum :=
  ⟨⟨Spectrum.ofValuation ((NormedField.valuation (K := x.1.1.H)).comap (U.evaluationToH x)),
    fun f => U.nnnorm_evaluationToH_le x f⟩,fun a => by
    change ‖U.evaluationToH x (U.analyticCoefficients a)‖₊ = w a
    have hc : U.analyticCoefficients a =
        U.rationalMap (algebraMap K[X] U.RationalFunctions (C a)) := rfl
    rw [hc,U.evaluationToH_rationalMap,U.nnnorm_rationalEvaluation,U.rationalValue_polynomial]
    exact x.1.2 a⟩

theorem completionHomeomorph_boundedAnalyticPoint (x : U.carrier) :
    RelativeNormBoundedSpectrum.completionHomeomorph w U.rationalCoefficients
      (U.boundedAnalyticPoint x) = U.boundedRationalPoint x := by
  apply Subtype.ext
  apply Subtype.ext
  apply Spectrum.ext_val
  intro f
  change ‖U.evaluationToH x (f : U.AnalyticFunctions)‖₊ =
    U.rationalValue (U.normedRationalEquiv f) x
  rw [U.evaluationToH_coe]
  exact U.nnnorm_rationalEvaluation x (U.normedRationalEquiv f)

theorem analyticSpectrumHomeomorph_boundedAnalyticPoint (x : U.carrier) :
    U.analyticSpectrumHomeomorph (U.boundedAnalyticPoint x) = x := by
  change U.rationalSpectrumHomeomorph
    (RelativeNormBoundedSpectrum.completionHomeomorph w U.rationalCoefficients
      (U.boundedAnalyticPoint x)) = x
  rw [U.completionHomeomorph_boundedAnalyticPoint]
  exact U.rationalSpectrumRestrict_boundedRationalPoint x

/-- EVERY completed value on the actual point is the norm of its evaluator in the SAME original H(x). -/
theorem analyticSpectrumHomeomorph_symm_val (x : U.carrier) (f : U.AnalyticFunctions) :
    (U.analyticSpectrumHomeomorph.symm x).1.1.val f = U.analyticValue f x := by
  have he : U.analyticSpectrumHomeomorph.symm x = U.boundedAnalyticPoint x := by
    apply U.analyticSpectrumHomeomorph.injective
    rw [Homeomorph.apply_symm_apply,U.analyticSpectrumHomeomorph_boundedAnalyticPoint]
  rw [he]
  rfl

/-- Whole completed-spectrum identification retains EVERY original rational value. -/
theorem analyticSpectrumHomeomorph_val_rationalMap (y : U.AnalyticBoundedSpectrum)
    (f : U.RationalFunctions) :
    y.1.1.val (U.rationalMap f) = U.rationalValue f (U.analyticSpectrumHomeomorph y) := by
  have he := U.analyticSpectrumHomeomorph_symm_val (U.analyticSpectrumHomeomorph y) (U.rationalMap f)
  rw [Homeomorph.symm_apply_apply] at he
  exact he.trans (U.analyticValue_rationalMap f _)

/-- Whole completed-spectrum identification retains EVERY original polynomial value. -/
theorem analyticSpectrumHomeomorph_val_polynomial (y : U.AnalyticBoundedSpectrum) (p : K[X]) :
    y.1.1.val (U.rationalMap (algebraMap K[X] U.RationalFunctions p)) =
      val (U.analyticSpectrumHomeomorph y).1 p := by
  rw [U.analyticSpectrumHomeomorph_val_rationalMap,U.rationalValue_polynomial]

/-- Every WHOLE completed function has continuous values on the SAME original affinoid point set. -/
theorem continuous_analyticValue (f : U.AnalyticFunctions) : Continuous (U.analyticValue f) := by
  have he : U.analyticValue f = fun x => (U.analyticSpectrumHomeomorph.symm x).1.1.val f :=
    funext fun x => (U.analyticSpectrumHomeomorph_symm_val x f).symm
  rw [he]
  exact (Spectrum.continuous_val_apply f).comp
    (continuous_subtype_val.comp (continuous_subtype_val.comp U.analyticSpectrumHomeomorph.symm.continuous))
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
