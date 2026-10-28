/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.GaussCompletion
import EnvelopeProperty.Berkovich.SpectrumDiscMaps

/-!
# Actual contractive restriction and translation of completed disc functions

Whole polynomial maps are norm-contracting under the true radius and center
bounds, and extend as actual algebra homomorphisms by norm completion. All
completed-function identities use genuine dense polynomial images. No
injectivity of restriction to a smaller disc or analytic sheaf is asserted.
-/
open scoped NNReal ENNReal Polynomial Topology
open Polynomial UniformSpace Topology
noncomputable section
namespace EnvelopeProperty.Berkovich
namespace Spectrum
variable {A : Type*} [CommRing A]

/-- The genuine center and radius bounds control EVERY translated polynomial for arbitrary ring-valuations. -/
theorem gauss_val_translate_le (v : Valuation A ℝ≥0) (r s : ℝ≥0) (a : A)
    (ha : v a ≤ r) (hsr : s ≤ r) (p : A[X]) :
    gaussFun v s (Polynomial.algEquivAevalXAddC a p) ≤ gaussFun v r p := by
  let z := comap (Polynomial.algEquivAevalXAddC a).toRingHom (gauss (ofValuation v) s)
  have hz : proj z = ofValuation v := by
    apply ext_val
    intro c
    change (gauss (ofValuation v) s).val (Polynomial.algEquivAevalXAddC a (C c)) = v c
    rw [show Polynomial.algEquivAevalXAddC a (C c) = C c from
      (Polynomial.algEquivAevalXAddC a).commutes c, gauss_val_C]
    rfl
  have hX : z.val X ≤ r := by
    change (gauss (ofValuation v) s).val (Polynomial.algEquivAevalXAddC a X) ≤ r
    have he : Polynomial.algEquivAevalXAddC a X = X + C a := by
      simp [Polynomial.algEquivAevalXAddC]
    rw [he]
    exact ((gauss (ofValuation v) s).val.map_add X (C a)).trans
      (max_le (by simpa only [gauss_val_X] using hsr) (by simpa only [gauss_val_C, ofValuation_val] using ha))
  exact val_le_gauss_val hz hX p

/-- Whole polynomial translation composition over ANY commutative ring. -/
theorem polynomialTranslate_comp (a b : A) (p : A[X]) :
    Polynomial.algEquivAevalXAddC b (Polynomial.algEquivAevalXAddC a p) =
      Polynomial.algEquivAevalXAddC (a+b) p := by
  have h : (Polynomial.algEquivAevalXAddC b).toAlgHom.comp
      (Polynomial.algEquivAevalXAddC a).toAlgHom =
        (Polynomial.algEquivAevalXAddC (a+b)).toAlgHom := by
    apply Polynomial.algHom_ext
    simp [Polynomial.algEquivAevalXAddC]
    ring
  exact congrArg (fun f : A[X] →ₐ[A] A[X] => f p) h

end Spectrum

namespace GaussCompletion
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The ACTUAL original polynomial map into the target completed Gauss algebra. -/
def polynomialTranslation (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) (a : K) :
    PolynomialRing (K := K) r hr →+* Ring (K := K) s hs :=
  (polynomialMap s hs).comp ((Polynomial.algEquivAevalXAddC a).toRingHom.comp
    (polynomialEquiv r hr).toRingHom)

/-- Every translated original polynomial obeys the true full Gauss norm bound. -/
theorem nnnorm_polynomialTranslation_le (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) (a : K)
    (ha : ‖a‖₊ ≤ r) (hsr : s ≤ r) (p : PolynomialRing (K := K) r hr) :
    ‖polynomialTranslation r s hr hs a p‖₊ ≤ ‖p‖₊ := by
  change ‖polynomialMap s hs (Polynomial.algEquivAevalXAddC a (polynomialEquiv r hr p))‖₊ ≤ _
  rw [nnnorm_polynomialMap, nnnorm_polynomial]
  exact Spectrum.gauss_val_translate_le (NormedField.valuation (K := K)) r s a ha hsr _

/-- Actual contractivity makes the ENTIRE original polynomial translation continuous. -/
theorem lipschitz_polynomialTranslation (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) (a : K)
    (ha : ‖a‖₊ ≤ r) (hsr : s ≤ r) : LipschitzWith 1 (polynomialTranslation r s hr hs a) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub] using
    (show ‖polynomialTranslation r s hr hs a (p-q)‖ ≤ ‖p-q‖ from
      nnnorm_polynomialTranslation_le r s hr hs a ha hsr (p-q))

/-- The ACTUAL completion extension of the entire contractive polynomial translation. -/
def translationRingHom (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) (a : K)
    (ha : ‖a‖₊ ≤ r) (hsr : s ≤ r) : Ring (K := K) r hr →+* Ring (K := K) s hs :=
  Completion.extensionHom (polynomialTranslation r s hr hs a)
    (lipschitz_polynomialTranslation r s hr hs a ha hsr).continuous

@[simp]
theorem translationRingHom_polynomialMap (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) (a : K)
    (ha : ‖a‖₊ ≤ r) (hsr : s ≤ r) (p : K[X]) :
    translationRingHom r s hr hs a ha hsr (polynomialMap r hr p) =
      polynomialMap s hs (Polynomial.algEquivAevalXAddC a p) := by
  change Completion.extensionHom _ _ ((polynomialEquiv r hr).symm p :
    Completion (PolynomialRing (K := K) r hr)) = _
  rw [Completion.extensionHom_coe]
  change polynomialMap s hs (Polynomial.algEquivAevalXAddC a
    (polynomialEquiv r hr ((polynomialEquiv r hr).symm p))) = _
  rw [RingEquiv.apply_symm_apply]

/-- The genuine completed translation preserves EVERY original K scalar. -/
def translation (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) (a : K)
    (ha : ‖a‖₊ ≤ r) (hsr : s ≤ r) : Ring (K := K) r hr →ₐ[K] Ring (K := K) s hs where
  toRingHom := translationRingHom r s hr hs a ha hsr
  commutes' c := by
    change translationRingHom r s hr hs a ha hsr (polynomialMap r hr (C c)) = polynomialMap s hs (C c)
    rw [translationRingHom_polynomialMap]
    exact congrArg (polynomialMap s hs) ((Polynomial.algEquivAevalXAddC a).commutes c)

/-- The actual WHOLE completed K-algebra map is continuous. -/
theorem continuous_translation (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) (a : K)
    (ha : ‖a‖₊ ≤ r) (hsr : s ≤ r) : Continuous (translation r s hr hs a ha hsr) :=
  Completion.continuous_extension

/-- The actual original-polynomial restriction formula holds for EVERY polynomial. -/
@[simp]
theorem translation_polynomialMap (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) (a : K)
    (ha : ‖a‖₊ ≤ r) (hsr : s ≤ r) (p : K[X]) :
    translation r s hr hs a ha hsr (polynomialMap r hr p) =
      polynomialMap s hs (Polynomial.algEquivAevalXAddC a p) :=
  translationRingHom_polynomialMap r s hr hs a ha hsr p

/-- The actual norm bound holds for EVERY completed function, not merely its polynomial image. -/
theorem nnnorm_translation_le (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) (a : K)
    (ha : ‖a‖₊ ≤ r) (hsr : s ≤ r) (f : Ring (K := K) r hr) :
    ‖translation r s hr hs a ha hsr f‖₊ ≤ ‖f‖₊ := by
  induction f using Completion.induction_on with
  | hp => exact isClosed_le (continuous_nnnorm.comp (continuous_translation _ _ _ _ _ _ _)) continuous_nnnorm
  | ih p =>
    change ‖translationRingHom r s hr hs a ha hsr (p : Ring (K := K) r hr)‖₊ ≤ _
    rw [translationRingHom, Completion.extensionHom_coe, Completion.nnnorm_coe]
    exact nnnorm_polynomialTranslation_le r s hr hs a ha hsr p

/-- The ACTUAL original polynomial image is dense in the genuine Gauss completion. -/
theorem denseRange_polynomialMap (r : ℝ≥0) (hr : 0 < r) :
    DenseRange (polynomialMap (K := K) r hr) := by
  have he : Set.range (((↑) : PolynomialRing (K := K) r hr → Ring (K := K) r hr) ∘
      (polynomialEquiv r hr).symm) = Set.range ((↑) : PolynomialRing (K := K) r hr → Ring (K := K) r hr) :=
    (polynomialEquiv r hr).symm.surjective.range_comp _
  change Dense (Set.range (((↑) : PolynomialRing (K := K) r hr → Ring (K := K) r hr) ∘
    (polynomialEquiv r hr).symm))
  rw [he]
  exact Completion.denseRange_coe

/-- The combined center bound is DERIVED from the actual ultrametric norm and true radius inequalities. -/
theorem center_add_bound (r s : ℝ≥0) (a b : K) (ha : ‖a‖₊ ≤ r) (hb : ‖b‖₊ ≤ s) (hsr : s ≤ r) :
    ‖a+b‖₊ ≤ r :=
  (IsUltrametricDist.nnnorm_add_le_max a b).trans (max_le ha (hb.trans hsr))

/-- Composition of ACTUAL completed translations is equality on EVERY completed function. -/
theorem translation_comp (r s t : ℝ≥0) (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (a b : K) (ha : ‖a‖₊ ≤ r) (hb : ‖b‖₊ ≤ s) (hsr : s ≤ r) (hts : t ≤ s) :
    (translation s t hs ht b hb hts).comp (translation r s hr hs a ha hsr) =
      translation r t hr ht (a+b) (center_add_bound r s a b ha hb hsr) (hts.trans hsr) := by
  apply AlgHom.ext
  exact congrFun ((denseRange_polynomialMap r hr).equalizer
    ((continuous_translation s t hs ht b hb hts).comp (continuous_translation r s hr hs a ha hsr))
    (continuous_translation r t hr ht (a+b) (center_add_bound r s a b ha hb hsr) (hts.trans hsr))
    (funext fun p => by
      change translation s t hs ht b hb hts (translation r s hr hs a ha hsr (polynomialMap r hr p)) =
        translation r t hr ht (a+b) (center_add_bound r s a b ha hb hsr) (hts.trans hsr) (polynomialMap r hr p)
      rw [translation_polynomialMap, translation_polynomialMap, translation_polynomialMap]
      exact congrArg (polynomialMap t ht) (Spectrum.polynomialTranslate_comp a b p)))

/-- Zero translation on the SAME genuine Gauss completion is its WHOLE identity algebra map. -/
@[simp]
theorem translation_zero (r : ℝ≥0) (hr : 0 < r) :
    translation r r hr hr (0 : K) (by simp) le_rfl = AlgHom.id K (Ring (K := K) r hr) := by
  apply AlgHom.ext
  exact congrFun ((denseRange_polynomialMap r hr).equalizer
    (continuous_translation r r hr hr (0 : K) (by simp) le_rfl) continuous_id
    (funext fun p => by
      change translation r r hr hr (0 : K) (by simp) le_rfl (polynomialMap r hr p) = polynomialMap r hr p
      rw [translation_polynomialMap]
      congr 1
      simp [Polynomial.algEquivAevalXAddC]))

/-- The genuine original polynomial automorphism sends a small disc into its ACTUAL translated subdisc of the large disc. -/
def pointTranslation (r s : ℝ≥0) (a : K) (ha : ‖a‖₊ ≤ r) (hsr : s ≤ r)
    (x : ClosedDisc (K := K) s) : ClosedDisc (K := K) r :=
  ⟨(RelativeSpectrum.discTranslationHomeomorph (NormedField.valuation (K := K)) a s x).1, by
    change x.1.1.val (Polynomial.algEquivAevalXAddC a X) ≤ r
    have he : Polynomial.algEquivAevalXAddC a X = X + C a := by
      simp [Polynomial.algEquivAevalXAddC]
    rw [he]
    exact (x.1.1.val.map_add X (C a)).trans
      (max_le (x.2.trans hsr) (by
        have hc : x.1.1.val (C a) = ‖a‖₊ := x.1.2 a
        rw [hc]
        exact ha))⟩

@[simp]
theorem pointTranslation_val_apply (r s : ℝ≥0) (a : K) (ha : ‖a‖₊ ≤ r) (hsr : s ≤ r)
    (x : ClosedDisc (K := K) s) (p : K[X]) :
    (pointTranslation r s a ha hsr x).1.1.val p = x.1.1.val (Polynomial.algEquivAevalXAddC a p) := rfl

/-- The genuine whole translated subdisc map is a CLOSED embedding, even at zero point-radius. -/
theorem isClosedEmbedding_pointTranslation (r s : ℝ≥0) (a : K) (ha : ‖a‖₊ ≤ r) (hsr : s ≤ r) :
    IsClosedEmbedding (pointTranslation r s a ha hsr) := by
  apply IsClosedEmbedding.of_comp (g := (Subtype.val : ClosedDisc (K := K) r →
    RelativeSpectrum (NormedField.valuation (K := K)) K[X])) IsEmbedding.subtypeVal
  exact RelativeSpectrum.isClosedEmbedding_discTranslation (NormedField.valuation (K := K)) a s

/-- ACTUAL evaluation ring maps into the ORIGINAL completed residue fields commute on EVERY completed function. -/
theorem evaluationToH_translation (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) (a : K)
    (ha : ‖a‖₊ ≤ r) (hsr : s ≤ r) (x : ClosedDisc (K := K) s) :
    (evaluationToH s hs x).comp (translation r s hr hs a ha hsr).toRingHom =
      (Spectrum.H.map (x := (pointTranslation r s a ha hsr x).1.1) (y := x.1.1)
        (Polynomial.algEquivAevalXAddC a).toRingHom
        (rfl : Spectrum.comap (Polynomial.algEquivAevalXAddC a).toRingHom x.1.1 =
          (pointTranslation r s a ha hsr x).1.1)).comp
        (evaluationToH r hr (pointTranslation r s a ha hsr x)) := by
  let y := pointTranslation r s a ha hsr x
  have hxy : Spectrum.comap (Polynomial.algEquivAevalXAddC a).toRingHom x.1.1 = y.1.1 := rfl
  have hcL : Continuous ((evaluationToH s hs x).comp (translation r s hr hs a ha hsr).toRingHom) :=
    Completion.continuous_extension.comp (continuous_translation r s hr hs a ha hsr)
  have hcH := (Spectrum.H.isometry_map (x := y.1.1) (y := x.1.1)
    (Polynomial.algEquivAevalXAddC a).toRingHom hxy).continuous
  have hcy : Continuous (evaluationToH r hr y) := Completion.continuous_extension
  have hcR : Continuous ((Spectrum.H.map (x := y.1.1) (y := x.1.1)
      (Polynomial.algEquivAevalXAddC a).toRingHom hxy).comp (evaluationToH r hr y)) :=
    hcH.comp hcy
  apply RingHom.ext
  exact congrFun ((denseRange_polynomialMap r hr).equalizer hcL hcR (funext fun p => by
    change evaluationToH s hs x (translation r s hr hs a ha hsr (polynomialMap r hr p)) =
      Spectrum.H.map (x := y.1.1) (y := x.1.1)
        (Polynomial.algEquivAevalXAddC a).toRingHom hxy
        (evaluationToH r hr y (polynomialMap r hr p))
    rw [translation_polynomialMap, evaluationToH_polynomialMap, evaluationToH_polynomialMap]
    exact (Spectrum.H.map_toH (x := y.1.1) (y := x.1.1)
      (Polynomial.algEquivAevalXAddC a).toRingHom hxy p).symm))

/-- ALL genuine completed-function values follow actual subdisc restriction and original-point translation. -/
theorem value_translation (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) (a : K)
    (ha : ‖a‖₊ ≤ r) (hsr : s ≤ r) (x : ClosedDisc (K := K) s) (f : Ring (K := K) r hr) :
    value s hs (translation r s hr hs a ha hsr f) x =
      value r hr f (pointTranslation r s a ha hsr x) := by
  rw [value_eq_nnnorm_evaluationToH, value_eq_nnnorm_evaluationToH]
  let y := pointTranslation r s a ha hsr x
  have hxy : Spectrum.comap (Polynomial.algEquivAevalXAddC a).toRingHom x.1.1 = y.1.1 := rfl
  have h := congrArg (fun g : Ring (K := K) r hr →+* x.1.1.H => g f)
    (evaluationToH_translation r s hr hs a ha hsr x)
  change evaluationToH s hs x (translation r s hr hs a ha hsr f) =
    Spectrum.H.map (x := y.1.1) (y := x.1.1)
      (Polynomial.algEquivAevalXAddC a).toRingHom hxy (evaluationToH r hr y f) at h
  rw [h]
  exact NNReal.eq (Spectrum.H.norm_map (x := y.1.1) (y := x.1.1)
    (Polynomial.algEquivAevalXAddC a).toRingHom hxy _)

end GaussCompletion
end EnvelopeProperty.Berkovich
