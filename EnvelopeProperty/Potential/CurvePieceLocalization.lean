import EnvelopeProperty.Potential.CurveIdempotentUnits
import EnvelopeProperty.Potential.CurveAnalyticSpectrumSpecialization
import EnvelopeProperty.Berkovich.SpectrumLocalization

/-! # Actual principal localization into the genuine analytic quotient summand -/

open scoped NNReal Polynomial TensorProduct Classical
open Polynomial
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)
variable {B ι : Type*} [CommRing B] [Algebra K[X] B] [Fintype ι]

/-- The actual original function map to the genuine quotient summand. -/
def curveIdempotentQuotientMap (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) :
    B →+* IdempotentSummand.Summand (U.curveAnalyticOriginalEquiv basis e) :=
  (IdempotentSummand.quotient (R := U.AnalyticFunctions) (U.curveAnalyticOriginalEquiv basis e)).toRingHom.comp
    (Algebra.TensorProduct.includeRight : B →ₐ[K[X]] U.CurveAnalyticTensor B).toRingHom

/-- The universal map is an actual principal localization, using the actual quotient unit. -/
def curveIdempotentLocalizedMap (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) (g : B)
    (hg : IsUnit (U.curveIdempotentQuotientMap basis e g)) :
    Localization.Away g →+* IdempotentSummand.Summand (U.curveAnalyticOriginalEquiv basis e) :=
  IsLocalization.lift (M := Submonoid.powers g) (g := U.curveIdempotentQuotientMap basis e) (by
    rintro ⟨_,n,rfl⟩
    simpa only [map_pow] using hg.pow n)

omit [IsAlgClosed K] [Fintype ι] in
theorem curveIdempotentLocalizedMap_algebraMap (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) (g : B)
    (hg : IsUnit (U.curveIdempotentQuotientMap basis e g)) (b : B) :
    U.curveIdempotentLocalizedMap basis e g hg (algebraMap B (Localization.Away g) b) =
      U.curveIdempotentQuotientMap basis e b := IsLocalization.lift_eq _ b

/-- Choose a genuine whole analytic representative of each actual localized quotient value. -/
def curveIdempotentLocalizedLift (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) (g : B)
    (hg : IsUnit (U.curveIdempotentQuotientMap basis e g)) (b : Localization.Away g) :
    U.CurveAnalyticAlgebra basis :=
  (U.curveAnalyticOriginalEquiv basis).symm
    (Classical.choose (Ideal.Quotient.mkₐ_surjective U.AnalyticFunctions _
      (U.curveIdempotentLocalizedMap basis e g hg b)))

omit [IsAlgClosed K] [Fintype ι] in
theorem quotient_curveIdempotentLocalizedLift (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) (g : B)
    (hg : IsUnit (U.curveIdempotentQuotientMap basis e g)) (b : Localization.Away g) :
    IdempotentSummand.quotient (R := U.AnalyticFunctions) (U.curveAnalyticOriginalEquiv basis e)
      (U.curveAnalyticOriginalEquiv basis (U.curveIdempotentLocalizedLift basis e g hg b)) =
        U.curveIdempotentLocalizedMap basis e g hg b := by
  rw [curveIdempotentLocalizedLift,AlgEquiv.apply_symm_apply]
  exact Classical.choose_spec (Ideal.Quotient.mkₐ_surjective U.AnalyticFunctions _ _)

variable [Algebra K B] [IsScalarTower K K[X] B]

omit [Fintype ι] in
/-- At an actual original selected point, the genuine idempotent has value ONE
in the SAME original completed residue field, not just norm one. -/
theorem curveOriginalEvaluation_idempotent_eq_one (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (y : U.CurvePreimage (B := B)) (hy : y ∈ U.curveIdempotentOriginalPiece basis e) :
    U.curveOriginalEvaluation basis y e = 1 := by
  have hn : ‖U.curveOriginalEvaluation basis y e‖₊ = 1 := by
    rw [U.curveOriginalEvaluation_specialization basis y e]
    exact hy
  have hh := he.map (U.curveOriginalEvaluation basis y)
  have hfactor : U.curveOriginalEvaluation basis y e*(U.curveOriginalEvaluation basis y e-1) = 0 := by
    rw [mul_sub,mul_one,hh.eq,sub_self]
  rcases mul_eq_zero.mp hfactor with hz | ho
  · rw [hz,nnnorm_zero] at hn
    exact False.elim (zero_ne_one hn)
  · exact sub_eq_zero.mp ho

/-- The actual evaluator factors through the true quotient at every selected original point. -/
def curveIdempotentQuotientEvaluation (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (y : U.CurvePreimage (B := B)) (hy : y ∈ U.curveIdempotentOriginalPiece basis e) :
    IdempotentSummand.Summand (U.curveAnalyticOriginalEquiv basis e) →+* Spectrum.H y.1.1 :=
  Ideal.Quotient.lift _ (U.curveOriginalTensorEvaluation y) (by
    have hker : Ideal.span {1-U.curveAnalyticOriginalEquiv basis e} ≤
        RingHom.ker (U.curveOriginalTensorEvaluation y) := by
      apply Ideal.span_le.mpr
      rintro a (rfl : a = 1-U.curveAnalyticOriginalEquiv basis e)
      change U.curveOriginalTensorEvaluation y (1-U.curveAnalyticOriginalEquiv basis e) = 0
      rw [map_sub,map_one]
      change 1-U.curveOriginalEvaluation basis y e = 0
      rw [U.curveOriginalEvaluation_idempotent_eq_one basis he y hy,sub_self]
    exact fun a ha => hker ha)

omit [Fintype ι] in
theorem curveIdempotentQuotientEvaluation_quotient (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (y : U.CurvePreimage (B := B)) (hy : y ∈ U.curveIdempotentOriginalPiece basis e)
    (a : U.CurveAnalyticTensor B) :
    U.curveIdempotentQuotientEvaluation basis he y hy
      (IdempotentSummand.quotient (R := U.AnalyticFunctions) (U.curveAnalyticOriginalEquiv basis e) a) =
        U.curveOriginalTensorEvaluation y a := rfl

omit [Fintype ι] in
theorem curveIdempotentQuotientEvaluation_originalMap (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (y : U.CurvePreimage (B := B)) (hy : y ∈ U.curveIdempotentOriginalPiece basis e) (b : B) :
    U.curveIdempotentQuotientEvaluation basis he y hy
      (U.curveIdempotentQuotientMap basis e b) = Spectrum.toH y.1.1 b := by
  change U.curveOriginalTensorEvaluation y ((1 : U.AnalyticFunctions) ⊗ₜ[K[X]] b) = _
  rw [U.curveOriginalTensorEvaluation_tmul,map_one,one_mul]

omit [Fintype ι] in
/-- An ACTUAL quotient unit forces original nonvanishing at every actual selected point. -/
theorem curveIdempotentOriginalPiece_val_ne_zero (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (g : B)
    (hg : IsUnit (U.curveIdempotentQuotientMap basis e g))
    (y : U.CurvePreimage (B := B)) (hy : y ∈ U.curveIdempotentOriginalPiece basis e) :
    y.1.1.val g ≠ 0 := by
  have hunit := hg.map (U.curveIdempotentQuotientEvaluation basis he y hy)
  rw [U.curveIdempotentQuotientEvaluation_originalMap basis he y hy] at hunit
  rw [← Spectrum.nnnorm_toH y.1.1 g]
  exact nnnorm_ne_zero_iff.mpr hunit.ne_zero

omit [Fintype ι] in
/-- Every chosen analytic representative has exactly the ORIGINAL localized seminorm value. -/
theorem nnnorm_curveIdempotentLocalizedLift_evaluation (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (g : B)
    (hg : IsUnit (U.curveIdempotentQuotientMap basis e g))
    (y : U.CurvePreimage (B := B)) (hy : y ∈ U.curveIdempotentOriginalPiece basis e)
    (b : Localization.Away g) :
    ‖U.curveOriginalEvaluation basis y (U.curveIdempotentLocalizedLift basis e g hg b)‖₊ =
      (Spectrum.awayLift g y.1.1
        (U.curveIdempotentOriginalPiece_val_ne_zero basis he g hg y hy)).val b := by
  let f := (U.curveIdempotentQuotientEvaluation basis he y hy).comp
    (U.curveIdempotentLocalizedMap basis e g hg)
  let z : Spectrum (Localization.Away g) := Spectrum.ofValuation (NormedField.valuation.comap f)
  have hz : Spectrum.awayComap g z = y.1.1 := by
    apply Spectrum.ext_val
    intro a
    change ‖f (algebraMap B (Localization.Away g) a)‖₊ = y.1.1.val a
    change ‖U.curveIdempotentQuotientEvaluation basis he y hy
      (U.curveIdempotentLocalizedMap basis e g hg (algebraMap B (Localization.Away g) a))‖₊ = _
    rw [U.curveIdempotentLocalizedMap_algebraMap,U.curveIdempotentQuotientEvaluation_originalMap,
      Spectrum.nnnorm_toH]
  have hzeq : z = Spectrum.awayLift g y.1.1
      (U.curveIdempotentOriginalPiece_val_ne_zero basis he g hg y hy) := by
    apply Spectrum.Away.comap_injective (Localization.Away g) g
    exact hz.trans (Spectrum.Away.comap_lift _ _ _ _).symm
  have heval : U.curveOriginalEvaluation basis y (U.curveIdempotentLocalizedLift basis e g hg b) = f b := by
    change U.curveOriginalTensorEvaluation y
      (U.curveAnalyticOriginalEquiv basis (U.curveIdempotentLocalizedLift basis e g hg b)) = _
    rw [← U.curveIdempotentQuotientEvaluation_quotient basis he y hy,
      U.quotient_curveIdempotentLocalizedLift]
    rfl
  rw [heval]
  exact congrArg (fun q : Spectrum (Localization.Away g) => q.val b) hzeq

/-- The ORIGINAL localization evaluator in the SAME original completed residue field. -/
def curveOriginalLocalizedEvaluation (g : B) (y : Spectrum B) (hy : y.val g ≠ 0) :
    Localization.Away g →+* Spectrum.H y :=
  IsLocalization.lift (M := Submonoid.powers g) (g := Spectrum.toH y) (by
    rintro ⟨_,n,rfl⟩
    rw [map_pow]
    apply IsUnit.pow
    apply isUnit_iff_ne_zero.mpr
    apply nnnorm_ne_zero_iff.mp
    rw [Spectrum.nnnorm_toH]
    exact hy)

omit [IsAlgClosed K] [Fintype ι] in
theorem curveOriginalLocalizedEvaluation_algebraMap (g : B) (y : Spectrum B) (hy : y.val g ≠ 0) (b : B) :
    curveOriginalLocalizedEvaluation g y hy (algebraMap B (Localization.Away g) b) =
      Spectrum.toH y b := IsLocalization.lift_eq _ b

omit [Fintype ι] in
/-- The representatives retain the ENTIRE original localized value in the SAME H(y). -/
theorem curveOriginalEvaluation_curveIdempotentLocalizedLift (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (g : B)
    (hg : IsUnit (U.curveIdempotentQuotientMap basis e g))
    (y : U.CurvePreimage (B := B)) (hy : y ∈ U.curveIdempotentOriginalPiece basis e)
    (b : Localization.Away g) :
    U.curveOriginalEvaluation basis y (U.curveIdempotentLocalizedLift basis e g hg b) =
      curveOriginalLocalizedEvaluation g y.1.1
        (U.curveIdempotentOriginalPiece_val_ne_zero basis he g hg y hy) b := by
  have hhom : (U.curveIdempotentQuotientEvaluation basis he y hy).comp
      (U.curveIdempotentLocalizedMap basis e g hg) =
        curveOriginalLocalizedEvaluation g y.1.1
          (U.curveIdempotentOriginalPiece_val_ne_zero basis he g hg y hy) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,U.curveIdempotentLocalizedMap_algebraMap,
      U.curveIdempotentQuotientEvaluation_originalMap,curveOriginalLocalizedEvaluation_algebraMap]
  change U.curveOriginalTensorEvaluation y
      (U.curveAnalyticOriginalEquiv basis (U.curveIdempotentLocalizedLift basis e g hg b)) = _
  rw [← U.curveIdempotentQuotientEvaluation_quotient basis he y hy,
    U.quotient_curveIdempotentLocalizedLift]
  exact RingHom.congr_fun hhom b

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
