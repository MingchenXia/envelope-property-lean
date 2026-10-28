import EnvelopeProperty.Berkovich.SpectrumGauss
import EnvelopeProperty.Berkovich.SpectrumLocalization
import EnvelopeProperty.Berkovich.SpectrumSupport
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Genuine whole Gauss rays in actual principal-open lines

Actual polynomial translation and the whole Gauss construction give continuous,
injective radius paths, with radius zero equal to entire evaluation pullback.
The original evaluation lower bound lifts the entire ray to an actual principal
localization. Positive radii over a field have zero support, derived from all
nonzero original function values. The actual evaluation lift is not isolated and
is approached through that generic-support locus. No complete, algebraically
closed, infinite or nontrivially valued field, model bound, subharmonic principle
or density inference from scheme support is assumed.
-/

open scoped NNReal Topology Polynomial
open Topology Polynomial
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {v : Valuation R ℝ≥0}

/-- A genuine translated whole Gauss point retaining every prescribed coefficient value. -/
def centeredGauss (y : RelativeSpectrum v A) (a : A) (r : ℝ≥0) :
    RelativeSpectrum v A[X] :=
  comap ((Polynomial.algEquivAevalXAddC a).toAlgHom.restrictScalars R) (gauss y r)

/-- Whole polynomial values come from the actual translation isomorphism. -/
theorem centeredGauss_val_apply (y : RelativeSpectrum v A) (a : A) (r : ℝ≥0) (p : A[X]) :
    val (centeredGauss y a r) p =
      val (gauss y r) (Polynomial.algEquivAevalXAddC a p) := rfl

/-- The centered coordinate has precisely the whole original radius value. -/
theorem centeredGauss_val_X_sub_C (y : RelativeSpectrum v A) (a : A) (r : ℝ≥0) :
    val (centeredGauss y a r) (X - C a) = r := by
  rw [centeredGauss_val_apply]
  have h : Polynomial.algEquivAevalXAddC a (X - C a) = X := by
    simp [Polynomial.algEquivAevalXAddC]
  rw [h, gauss_val_X]

/-- Radius zero is the entire actual evaluation pullback, not only its support. -/
theorem centeredGauss_zero (y : RelativeSpectrum v A) (a : A) :
    centeredGauss y a 0 = comap ((Polynomial.aeval a).restrictScalars R) y := by
  apply ext_val
  intro p
  rw [centeredGauss_val_apply, gauss_zero_val_apply, comap_val_apply]
  congr 1
  rw [Polynomial.algEquivAevalXAddC_apply, Polynomial.coeff_zero_eq_eval_zero]
  change eval 0 (p.comp (X + C a)) = eval a p
  rw [Polynomial.eval_comp]
  simp

/-- The entire translated Gauss family is jointly continuous. -/
@[fun_prop]
theorem continuous_centeredGauss_prod (a : A) :
    Continuous fun p : RelativeSpectrum v A × ℝ≥0 => centeredGauss p.1 a p.2 :=
  (continuous_comap _).comp continuous_gauss_prod

/-- A fixed entire base point gives a continuous actual radius path. -/
@[fun_prop]
theorem continuous_centeredGauss (y : RelativeSpectrum v A) (a : A) :
    Continuous (centeredGauss y a) := by
  rw [RelativeSpectrum.continuous_iff]
  intro p
  simp only [centeredGauss_val_apply]
  have h : Continuous (fun r : ℝ≥0 => Spectrum.gauss y.1 r) :=
    Spectrum.continuous_gauss_prod.comp (continuous_const.prodMk continuous_id)
  exact (Spectrum.continuous_val_apply (Polynomial.algEquivAevalXAddC a p)).comp h

/-- Distinct radii are distinguished by the actual centered-coordinate value. -/
theorem centeredGauss_injective (y : RelativeSpectrum v A) (a : A) :
    Function.Injective (centeredGauss y a) := by
  intro r s h
  have := congrArg (fun z => val z (X - C a)) h
  simpa only [centeredGauss_val_X_sub_C] using this

/-- Every whole original evaluation value is a lower bound along the entire centered Gauss ray. -/
theorem eval_val_le_centeredGauss (y : RelativeSpectrum v A) (a : A) (r : ℝ≥0) (p : A[X]) :
    val y (p.eval a) ≤ val (centeredGauss y a r) p := by
  have h := Spectrum.le_gauss_val y.1 r (Polynomial.algEquivAevalXAddC a p) 0
  simp only [pow_zero, mul_one] at h
  have hc : (Polynomial.algEquivAevalXAddC a p).coeff 0 = p.eval a := by
    rw [Polynomial.algEquivAevalXAddC_apply, Polynomial.coeff_zero_eq_eval_zero]
    change eval 0 (p.comp (X + C a)) = eval a p
    rw [Polynomial.eval_comp]
    simp
  rw [centeredGauss_val_apply]
  change y.1.val (p.eval a) ≤ (Spectrum.gauss y.1 r).val (Polynomial.algEquivAevalXAddC a p)
  rw [← hc]
  exact h

/-- A polynomial nonvanishing at the actual evaluation point never vanishes anywhere on the centered ray. -/
theorem centeredGauss_val_ne_zero_of_eval (y : RelativeSpectrum v A) (a : A)
    (g : A[X]) (hg : val y (g.eval a) ≠ 0) (r : ℝ≥0) :
    val (centeredGauss y a r) g ≠ 0 := by
  intro h
  exact hg (le_zero_iff.mp (h ▸ eval_val_le_centeredGauss y a r g))

section field
variable {K : Type*} [Field K] [Algebra R K]

/-- A positive actual radius gives nonzero value on every nonzero original polynomial. -/
theorem centeredGauss_val_ne_zero (y : RelativeSpectrum v K) (a : K)
    (r : ℝ≥0) (hr : 0 < r) (p : K[X]) (hp : p ≠ 0) :
    val (centeredGauss y a r) p ≠ 0 := by
  let e := Polynomial.algEquivAevalXAddC a
  have hep : e p ≠ 0 := fun h => hp (e.injective (h.trans e.map_zero.symm))
  obtain ⟨i, hi⟩ : ∃ i, (e p).coeff i ≠ 0 := by
    by_contra! h
    exact hep (Polynomial.ext fun i => by simpa using h i)
  have hval : val y ((e p).coeff i) ≠ 0 := by
    exact (val y).ne_zero_iff.mpr hi
  have hpos : 0 < val y ((e p).coeff i) * r ^ i :=
    mul_pos (pos_iff_ne_zero.mpr hval) (pow_pos hr i)
  have hle := Spectrum.le_gauss_val y.1 r (e p) i
  intro h
  change val y ((e p).coeff i) * r ^ i ≤ val (centeredGauss y a r) p at hle
  rw [h] at hle
  exact not_le_of_gt hpos hle

/-- Positive radii have genuine generic scheme support, derived from every whole polynomial value. -/
theorem centeredGauss_support_eq_bot (y : RelativeSpectrum v K) (a : K)
    (r : ℝ≥0) (hr : 0 < r) : (support (centeredGauss y a r)).asIdeal = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro p hp
  change p = 0
  by_contra h
  exact centeredGauss_val_ne_zero y a r hr p h hp

end field

section localization
variable (B : Type*) [CommRing B] [Algebra A[X] B] [Algebra R B]
  [IsScalarTower R A[X] B]
variable (g : A[X]) [IsLocalization.Away g B]

/-- The entire centered Gauss ray lives in the actual principal localization when its center does. -/
def centeredGaussAway (y : RelativeSpectrum v A) (a : A)
    (hg : val y (g.eval a) ≠ 0) (r : ℝ≥0) : RelativeSpectrum v B :=
  Away.lift v B g (centeredGauss y a r) (centeredGauss_val_ne_zero_of_eval y a g hg r)

/-- Every original polynomial value survives the actual localization lift. -/
theorem centeredGaussAway_val_algebraMap (y : RelativeSpectrum v A) (a : A)
    (hg : val y (g.eval a) ≠ 0) (r : ℝ≥0) (p : A[X]) :
    val (centeredGaussAway B g y a hg r) (algebraMap A[X] B p) =
      val (centeredGauss y a r) p :=
  Away.lift_val_algebraMap v B g _ _ p

/-- The actual localized centered-coordinate value is exactly the chosen radius. -/
theorem centeredGaussAway_val_X_sub_C (y : RelativeSpectrum v A) (a : A)
    (hg : val y (g.eval a) ≠ 0) (r : ℝ≥0) :
    val (centeredGaussAway B g y a hg r) (algebraMap A[X] B (X - C a)) = r := by
  rw [centeredGaussAway_val_algebraMap, centeredGauss_val_X_sub_C]

/-- The actual localization homeomorphism makes the whole lifted ray continuous. -/
@[fun_prop]
theorem continuous_centeredGaussAway (y : RelativeSpectrum v A) (a : A)
    (hg : val y (g.eval a) ≠ 0) : Continuous (centeredGaussAway B g y a hg) := by
  rw [RelativeSpectrum.continuous_iff]
  intro b
  obtain ⟨p, n, rfl⟩ := Spectrum.Away.exists_eq_mk' B g b
  simp only [centeredGaussAway, val_apply, Away.lift_val_mk']
  exact ((continuous_val_apply p).comp (continuous_centeredGauss y a)).div₀
    (((continuous_val_apply g).comp (continuous_centeredGauss y a)).pow n)
    (fun r => pow_ne_zero n (centeredGauss_val_ne_zero_of_eval y a g hg r))

/-- The literal localized ray remains injective on its radii. -/
theorem centeredGaussAway_injective (y : RelativeSpectrum v A) (a : A)
    (hg : val y (g.eval a) ≠ 0) : Function.Injective (centeredGaussAway B g y a hg) := by
  intro r s h
  have := congrArg (fun z => val z (algebraMap A[X] B (X - C a))) h
  simpa only [centeredGaussAway_val_X_sub_C] using this

/-- Every neighborhood of the whole evaluation lift contains a distinct positive-radius point of the actual line open. -/
theorem exists_centeredGaussAway_ne_in_nhds (y : RelativeSpectrum v A) (a : A)
    (hg : val y (g.eval a) ≠ 0) (U : Set (RelativeSpectrum v B))
    (hU : U ∈ 𝓝 (centeredGaussAway B g y a hg 0)) :
    ∃ r : ℝ≥0, 0 < r ∧ centeredGaussAway B g y a hg r ∈ U ∧
      centeredGaussAway B g y a hg r ≠ centeredGaussAway B g y a hg 0 := by
  have h0 : (0 : ℝ≥0) ∈ closure (Set.Ioi (0 : ℝ≥0)) := by
    rw [closure_Ioi (0 : ℝ≥0)]
    exact (le_rfl : (0 : ℝ≥0) ≤ 0)
  have hf := (mem_closure_iff_frequently.mp h0).and_eventually
    ((continuous_centeredGaussAway B g y a hg).continuousAt.eventually hU)
  obtain ⟨r, hr, hrU⟩ := hf.exists
  exact ⟨r, hr, hrU, fun h => hr.ne' (centeredGaussAway_injective B g y a hg h)⟩

/-- The entire actual radius-zero evaluation point is not isolated in the principal-open spectrum. -/
theorem not_isOpen_singleton_centeredGaussAway_zero (y : RelativeSpectrum v A) (a : A)
    (hg : val y (g.eval a) ≠ 0) :
    ¬ IsOpen ({centeredGaussAway B g y a hg 0} : Set (RelativeSpectrum v B)) := by
  intro h
  obtain ⟨r, _, hr, hne⟩ := exists_centeredGaussAway_ne_in_nhds B g y a hg
    {centeredGaussAway B g y a hg 0} (h.mem_nhds (by simp))
  exact hne (Set.mem_singleton_iff.mp hr)

end localization

section fieldLocalization
variable {K : Type*} [Field K] [Algebra R K]
variable (B : Type*) [CommRing B] [Algebra K[X] B] [Algebra R B]
  [IsScalarTower R K[X] B]
variable (g : K[X]) [IsLocalization.Away g B]

/-- Every nonzero whole localized function has positive-radius nonzero value. -/
theorem centeredGaussAway_val_ne_zero (y : RelativeSpectrum v K) (a : K)
    (hg : val y (g.eval a) ≠ 0) (r : ℝ≥0) (hr : 0 < r) (b : B) (hb : b ≠ 0) :
    val (centeredGaussAway B g y a hg r) b ≠ 0 := by
  obtain ⟨p, n, rfl⟩ := Spectrum.Away.exists_eq_mk' B g b
  have hp : p ≠ 0 := by
    intro h
    exact hb (by simp [h])
  simp only [centeredGaussAway, val_apply, Away.lift_val_mk']
  exact div_ne_zero (centeredGauss_val_ne_zero y a r hr p hp)
    (pow_ne_zero n (centeredGauss_val_ne_zero_of_eval y a g hg r))

/-- The positive-radius localized points have actual generic scheme support. -/
theorem centeredGaussAway_support_eq_bot (y : RelativeSpectrum v K) (a : K)
    (hg : val y (g.eval a) ≠ 0) (r : ℝ≥0) (hr : 0 < r) :
    (support (centeredGaussAway B g y a hg r)).asIdeal = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro b hb
  change b = 0
  by_contra h
  exact centeredGaussAway_val_ne_zero B g y a hg r hr b h hb

/-- The whole actual evaluation point is approached through the generic-support locus of the genuine principal-open line. -/
theorem centeredGaussAway_zero_mem_closure_generic (y : RelativeSpectrum v K) (a : K)
    (hg : val y (g.eval a) ≠ 0) :
    centeredGaussAway B g y a hg 0 ∈
      closure {x : RelativeSpectrum v B | (support x).asIdeal = ⊥} := by
  have h0 : (0 : ℝ≥0) ∈ closure (Set.Ioi (0 : ℝ≥0)) := by
    rw [closure_Ioi (0 : ℝ≥0)]
    exact (le_rfl : (0 : ℝ≥0) ≤ 0)
  have hm := mem_closure_image (continuous_centeredGaussAway B g y a hg).continuousAt h0
  apply closure_mono (s := (centeredGaussAway B g y a hg) '' Set.Ioi (0 : ℝ≥0)) ?_ hm
  rintro _ ⟨r, hr, rfl⟩
  exact centeredGaussAway_support_eq_bot B g y a hg r hr

end fieldLocalization

end EnvelopeProperty.Berkovich.RelativeSpectrum
