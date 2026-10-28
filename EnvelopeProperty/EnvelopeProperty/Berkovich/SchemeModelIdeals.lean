/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeIdealStalk
import EnvelopeProperty.Berkovich.SchemeCenter

/-!
# Intrinsic genuine ideal-sheaf-data model norms at actual proper centers

The genuine all-affine stalk ideal and actual bounded center-stalk valuation
define the intrinsic model norm and logarithm. Actual bounded ideal-map
pullback identifies them with the genuine ideal on ANY affine center
neighborhood. Explicit local finite generators give the same original
section-value maximum across different neighborhoods; actual ideal arithmetic
supplies zero, unit, sums, products and all powers.

The original object is Mathlib's actual IdealSheafData, with ideals on every
affine open and their true localization law. No assumption that the model
function exists, coherence, Noetherian condition, arbitrary affine action,
global continuity, center anti-continuity or analytic sheaf realization is
introduced. All prescribed coefficients are explicitly bounded and the true
structure morphism is proper; finite generators are optional supplied data.
-/

open scoped NNReal ENNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite

universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- The actual bounded seminorm point of the genuine model-center stalk. -/
def centerStalkSpectrum [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    Spectrum (X.presheaf.stalk (center hb y)) := Spectrum.ofValuation (centerStalkVal hb y)

/-- Genuine center valuation-ring pullback, rather than an assumed affine action, supplies boundedness. -/
theorem isBounded_centerStalkSpectrum [IsProper f] (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) : Spectrum.IsBounded (centerStalkSpectrum hb y) :=
  centerStalkVal_le_one hb y

/-- The entire stalk-spectrum restriction agrees with actual native section evaluation near the center. -/
theorem centerStalkSpectrum_comap_germ [IsProper f] (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (U : X.Opens) (hc : center hb y ∈ U) :
    Spectrum.comap (X.presheaf.germ U (center hb y) hc).hom (centerStalkSpectrum hb y) =
      (sectionSpectrum y U (support_mem_of_center_mem hb y U hc)).1 :=
  Spectrum.ext_val (centerStalkVal_germ hb y U hc)

/-- Intrinsic genuine ideal-sheaf-data norm at the actual proper model center. -/
def modelIdealNorm [IsProper f] (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) : ℝ≥0∞ :=
  Spectrum.idealNorm (I.stalkIdeal (center hb y)) (centerStalkSpectrum hb y)

/-- The genuine logarithmic model-ideal function, from the actual stalk ideal rather than chosen generators. -/
def modelIdealLog [IsProper f] (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) : EReal := ENNReal.log (modelIdealNorm I hb y)

/-- Intrinsic stalk evaluation equals the ideal norm on ANY actual affine center neighborhood. -/
theorem modelIdealNorm_eq_affine [IsProper f] (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (U : X.affineOpens) (hc : center hb y ∈ U.1) :
    modelIdealNorm I hb y = Spectrum.idealNorm (I.ideal U)
      (sectionSpectrum y U.1 (support_mem_of_center_mem hb y U.1 hc)).1 := by
  rw [modelIdealNorm, I.stalkIdeal_eq_affine (center hb y) U hc,
    Spectrum.idealNorm_map _ _ (isBounded_centerStalkSpectrum hb y), centerStalkSpectrum_comap_germ]

/-- Logarithmic ideal evaluation also agrees on every genuine affine center neighborhood. -/
theorem modelIdealLog_eq_affine [IsProper f] (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (U : X.affineOpens) (hc : center hb y ∈ U.1) :
    modelIdealLog I hb y = Spectrum.idealLog (I.ideal U)
      (sectionSpectrum y U.1 (support_mem_of_center_mem hb y U.1 hc)).1 :=
  congrArg ENNReal.log (modelIdealNorm_eq_affine I hb y U hc)

/-- Proper model ideal norms are bounded by one, with no local finite-generation assumption. -/
theorem modelIdealNorm_le_one [IsProper f] (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) : modelIdealNorm I hb y ≤ 1 :=
  Spectrum.idealNorm_le_one _ (isBounded_centerStalkSpectrum hb y)

/-- Genuine logarithmic model ideals have values at most zero, including the zero-ideal bottom value. -/
theorem modelIdealLog_le_zero [IsProper f] (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) : modelIdealLog I hb y ≤ 0 :=
  Spectrum.idealLog_le_zero _ (isBounded_centerStalkSpectrum hb y)

/-- Actual finite generators on an affine center neighborhood compute the intrinsic ideal norm. -/
theorem modelIdealNorm_eq_generators [IsProper f] (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (U : X.affineOpens) (hc : center hb y ∈ U.1)
    (S : Finset Γ(X, U)) (hS : I.ideal U = Ideal.span (S : Set Γ(X, U))) :
    modelIdealNorm I hb y =
      ((S.sup fun s => SchemeValuedPoint.eval y.1 U.1
        (support_mem_of_center_mem hb y U.1 hc) s : ℝ≥0) : ℝ≥0∞) := by
  rw [modelIdealNorm_eq_affine I hb y U hc, hS,
    Spectrum.idealNorm_span_finset (isBounded_sectionSpectrum_of_center_mem hb y U.1 hc)]
  rfl

/-- Different genuine affine neighborhoods and their actual generators give the SAME intrinsic model ideal norm. -/
theorem modelIdeal_generators_eq [IsProper f] (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (U V : X.affineOpens)
    (hU : center hb y ∈ U.1) (hV : center hb y ∈ V.1)
    (S : Finset Γ(X, U)) (T : Finset Γ(X, V))
    (hS : I.ideal U = Ideal.span (S : Set Γ(X, U)))
    (hT : I.ideal V = Ideal.span (T : Set Γ(X, V))) :
    S.sup (fun s => SchemeValuedPoint.eval y.1 U.1 (support_mem_of_center_mem hb y U.1 hU) s) =
      T.sup (fun t => SchemeValuedPoint.eval y.1 V.1 (support_mem_of_center_mem hb y V.1 hV) t) := by
  apply ENNReal.coe_injective
  exact (modelIdealNorm_eq_generators I hb y U hU S hS).symm.trans
    (modelIdealNorm_eq_generators I hb y V hV T hT)

/-- The genuine zero model ideal has zero intrinsic norm. -/
@[simp]
theorem modelIdealNorm_bot [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    modelIdealNorm (⊥ : X.IdealSheafData) hb y = 0 := by simp [modelIdealNorm]

/-- The genuine unit model ideal has norm one, from actual model-stalk boundedness. -/
theorem modelIdealNorm_top [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    modelIdealNorm (⊤ : X.IdealSheafData) hb y = 1 := by
  rw [modelIdealNorm, Scheme.IdealSheafData.paperStalkIdeal_top]
  exact Spectrum.idealNorm_top (isBounded_centerStalkSpectrum hb y)

/-- Actual model ideal sums give maxima of their intrinsic norms. -/
theorem modelIdealNorm_sup [IsProper f] (I J : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) :
    modelIdealNorm (I ⊔ J) hb y = max (modelIdealNorm I hb y) (modelIdealNorm J hb y) := by
  rw [modelIdealNorm, Scheme.IdealSheafData.paperStalkIdeal_sup, Spectrum.idealNorm_sup]
  rfl

/-- Actual model ideal products multiply their intrinsic norms. -/
theorem modelIdealNorm_mul [IsProper f] (I J : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) :
    modelIdealNorm (I * J) hb y = modelIdealNorm I hb y * modelIdealNorm J hb y := by
  rw [modelIdealNorm, Scheme.IdealSheafData.paperStalkIdeal_mul, Spectrum.idealNorm_mul]
  rfl

/-- All actual model ideal powers obey the intrinsic norm law, including the unit zeroth power. -/
theorem modelIdealNorm_pow [IsProper f] (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (n : ℕ) :
    modelIdealNorm (I ^ n) hb y = modelIdealNorm I hb y ^ n := by
  rw [modelIdealNorm, Scheme.IdealSheafData.paperStalkIdeal_pow,
    Spectrum.idealNorm_pow (isBounded_centerStalkSpectrum hb y)]
  rfl

/-- The zero model ideal has the actual negative-infinite logarithmic value. -/
@[simp]
theorem modelIdealLog_bot [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    modelIdealLog (⊥ : X.IdealSheafData) hb y = ⊥ := by simp [modelIdealLog]

/-- The unit model ideal has logarithmic value zero. -/
theorem modelIdealLog_top [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    modelIdealLog (⊤ : X.IdealSheafData) hb y = 0 := by
  simp only [modelIdealLog, modelIdealNorm_top, ENNReal.log_one]

/-- Actual model ideal sums take the maximum of their logarithmic functions. -/
theorem modelIdealLog_sup [IsProper f] (I J : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) :
    modelIdealLog (I ⊔ J) hb y = max (modelIdealLog I hb y) (modelIdealLog J hb y) := by
  exact congrArg ENNReal.log (modelIdealNorm_sup I J hb y) |>.trans
    ENNReal.log_monotone.map_max

/-- Actual model ideal products add logarithmic functions, including negative-infinite values. -/
theorem modelIdealLog_mul [IsProper f] (I J : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) :
    modelIdealLog (I * J) hb y = modelIdealLog I hb y + modelIdealLog J hb y := by
  simp only [modelIdealLog, modelIdealNorm_mul, ENNReal.log_mul_add]

/-- All model ideal powers satisfy the true extended-real scaling law. -/
theorem modelIdealLog_pow [IsProper f] (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (n : ℕ) :
    modelIdealLog (I ^ n) hb y = (n : EReal) * modelIdealLog I hb y := by
  simp only [modelIdealLog, modelIdealNorm_pow, ENNReal.log_pow]

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
