/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumNormedCompletion
import EnvelopeProperty.Berkovich.SpectrumGauss
import Mathlib.Analysis.Normed.Ring.WithAbs

/-!
# Actual weighted polynomial Gauss completions

The actual Gauss absolute value defines a normed polynomial copy, then its genuine
ring completion. Its norm-bounded prescribed-base spectrum is the true closed
affine disc. The algebra is DEFINED by norm completion; no separate
restricted formal-power-series presentation, analytic structure sheaf or
harmonicity is asserted.
-/
open scoped Polynomial NNReal ENNReal Topology
open Polynomial UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich
namespace GaussCompletion
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The faithful actual Gauss valuation at a positive radius gives a real absolute value on ALL polynomials. -/
def polynomialAbs (r : ℝ≥0) (hr : 0 < r) : AbsoluteValue K[X] ℝ where
  toFun p := gaussFun (NormedField.valuation (K := K)) r p
  map_mul' p q := by exact_mod_cast gaussFun_mul (NormedField.valuation (K := K)) r p q
  nonneg' p := NNReal.coe_nonneg _
  eq_zero' p := by
    constructor
    · intro h
      apply Polynomial.ext
      intro i
      have he : gaussFun (NormedField.valuation (K := K)) r p = 0 := by exact_mod_cast h
      have hb : ‖p.coeff i‖₊ * r ^ i ≤ 0 := by
        simpa only [he, NormedField.valuation_apply] using
          le_gaussFun (NormedField.valuation (K := K)) r p i
      have hcoeff : ‖p.coeff i‖₊ = 0 :=
        (mul_eq_zero.mp (le_zero_iff.mp hb)).resolve_right (pow_ne_zero i hr.ne')
      simpa only [coeff_zero] using nnnorm_eq_zero.mp hcoeff
    · intro h
      simp [h, gaussFun]
  add_le' p q := by
    have h := gaussFun_add_le (NormedField.valuation (K := K)) r p q
    exact (show (gaussFun (NormedField.valuation (K := K)) r (p+q) : ℝ) ≤
      max (gaussFun (NormedField.valuation (K := K)) r p : ℝ)
        (gaussFun (NormedField.valuation (K := K)) r q : ℝ) from h).trans
      (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

/-- An ACTUAL copy of K[T] endowed with the full weighted coefficient maximum norm. -/
abbrev PolynomialRing (r : ℝ≥0) (hr : 0 < r) := WithAbs (polynomialAbs (K := K) r hr)

instance polynomialNormedCommRing (r : ℝ≥0) (hr : 0 < r) :
    NormedCommRing (PolynomialRing (K := K) r hr) where
  __ : NormedRing (PolynomialRing (K := K) r hr) := inferInstance
  __ : CommRing (PolynomialRing (K := K) r hr) := inferInstance

instance polynomialNormedAlgebra (r : ℝ≥0) (hr : 0 < r) :
    NormedAlgebra K (PolynomialRing (K := K) r hr) where
  __ : Algebra K (PolynomialRing (K := K) r hr) := inferInstance
  norm_smul_le a p := by
    change (gaussFun (NormedField.valuation (K := K)) r (a • p.ofAbs) : ℝ) ≤ _
    rw [Polynomial.smul_eq_C_mul, gaussFun_mul, gaussFun_C]
    exact le_rfl

instance polynomialIsUltrametricDist (r : ℝ≥0) (hr : 0 < r) :
    IsUltrametricDist (PolynomialRing (K := K) r hr) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun p q => by
    change (gaussFun (NormedField.valuation (K := K)) r (p.ofAbs + q.ofAbs) : ℝ) ≤ _
    exact_mod_cast gaussFun_add_le (NormedField.valuation (K := K)) r p.ofAbs q.ofAbs

instance polynomialNormMulClass (r : ℝ≥0) (hr : 0 < r) :
    NormMulClass (PolynomialRing (K := K) r hr) where
  norm_mul p q := (polynomialAbs r hr).map_mul p.ofAbs q.ofAbs

instance polynomialNormOneClass (r : ℝ≥0) (hr : 0 < r) :
    NormOneClass (PolynomialRing (K := K) r hr) where
  norm_one := (polynomialAbs r hr).map_one

/-- The true original polynomial ring equivalence, preserving EVERY original polynomial element. -/
def polynomialEquiv (r : ℝ≥0) (hr : 0 < r) : PolynomialRing (K := K) r hr ≃+* K[X] :=
  WithAbs.equiv _

@[simp]
theorem nnnorm_polynomial (r : ℝ≥0) (hr : 0 < r) (p : PolynomialRing (K := K) r hr) :
    ‖p‖₊ = gaussFun (NormedField.valuation (K := K)) r (polynomialEquiv r hr p) := rfl

/-- The genuine separated Banach ring completion of the actual weighted Gauss polynomial ring. -/
abbrev Ring (r : ℝ≥0) (hr : 0 < r) := Completion (PolynomialRing (K := K) r hr)

instance normMulClass (r : ℝ≥0) (hr : 0 < r) : NormMulClass (Ring (K := K) r hr) where
  norm_mul a b := by
    induction a, b using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih a b => simp only [← Completion.coe_mul, Completion.norm_coe, norm_mul]

instance normOneClass (r : ℝ≥0) (hr : 0 < r) : NormOneClass (Ring (K := K) r hr) where
  norm_one := by
    rw [← Completion.coe_one, Completion.norm_coe, norm_one]

/-- The original polynomial map into its ACTUAL completion. -/
def polynomialMap (r : ℝ≥0) (hr : 0 < r) : K[X] →+* Ring (K := K) r hr :=
  Completion.coeRingHom.comp (polynomialEquiv r hr).symm.toRingHom

@[simp]
theorem nnnorm_polynomialMap (r : ℝ≥0) (hr : 0 < r) (p : K[X]) :
    ‖polynomialMap r hr p‖₊ = gaussFun (NormedField.valuation (K := K)) r p := by
  change ‖((polynomialEquiv r hr).symm p : Completion (PolynomialRing (K := K) r hr))‖₊ = _
  rw [Completion.nnnorm_coe, nnnorm_polynomial, RingEquiv.apply_symm_apply]

/-- The genuine coefficient map into the weighted normed polynomial copy. -/
def coefficients (r : ℝ≥0) (hr : 0 < r) : K →+* PolynomialRing (K := K) r hr :=
  (polynomialEquiv r hr).symm.toRingHom.comp C

@[simp]
theorem nnnorm_coefficients (r : ℝ≥0) (hr : 0 < r) (a : K) :
    ‖coefficients r hr a‖₊ = ‖a‖₊ := by
  rw [nnnorm_polynomial]
  change gaussFun (NormedField.valuation (K := K)) r (C a) = ‖a‖₊
  rw [gaussFun_C, NormedField.valuation_apply]

/-- The prescribed completion coefficient homomorphism is the ACTUAL K-algebra structure map. -/
theorem coefficientMap_eq_algebraMap (r : ℝ≥0) (hr : 0 < r) :
    (Completion.coeRingHom : PolynomialRing (K := K) r hr →+* Ring (K := K) r hr).comp (coefficients r hr) =
      algebraMap K (Ring (K := K) r hr) := rfl

/-- The actual existing affine closed radius-r disc with EVERY coefficient value fixed. -/
abbrev ClosedDisc (r : ℝ≥0) :=
  {x : RelativeSpectrum (NormedField.valuation (K := K)) K[X] // x.1.val X ≤ r}

/-- The true original Gauss point is a genuine witness in every closed disc, including trivial field norms. -/
def gaussPoint (r : ℝ≥0) : ClosedDisc (K := K) r :=
  ⟨RelativeSpectrum.gauss (RelativeSpectrum.self (NormedField.valuation (K := K))) r,
    (RelativeSpectrum.gauss_val_X _ r).le⟩

instance closedDiscNonempty (r : ℝ≥0) : Nonempty (ClosedDisc (K := K) r) := ⟨gaussPoint (K := K) r⟩

/-- Actual norm-bounded polynomial points with the ORIGINAL coefficient map prescribed. -/
abbrev PolynomialSpectrum (r : ℝ≥0) (hr : 0 < r) :=
  RelativeNormBoundedSpectrum (NormedField.valuation (K := K)) (coefficients r hr)

/-- Actual contractive completion points with the ORIGINAL coefficient map prescribed. -/
abbrev CompletionSpectrum (r : ℝ≥0) (hr : 0 < r) :=
  RelativeNormBoundedSpectrum (NormedField.valuation (K := K))
    ((Completion.coeRingHom : PolynomialRing (K := K) r hr →+* Ring (K := K) r hr).comp (coefficients r hr))

/-- The WHOLE polynomial restriction of an actual bounded Gauss-polynomial point. -/
def polynomialRestrict (r : ℝ≥0) (hr : 0 < r) (x : PolynomialSpectrum (K := K) r hr) :
    ClosedDisc (K := K) r :=
  ⟨⟨Spectrum.comap (polynomialEquiv r hr).symm.toRingHom x.1.1, fun a => x.2 a⟩, by
    change x.1.1.val ((polynomialEquiv r hr).symm X) ≤ r
    simpa only [nnnorm_polynomial, RingEquiv.apply_symm_apply, gaussFun_X] using
      x.1.2 ((polynomialEquiv r hr).symm X)⟩

/-- The actual closed-disc bound controls EVERY polynomial, hence yields a true norm-bounded copy point. -/
def polynomialExtend (r : ℝ≥0) (hr : 0 < r) (x : ClosedDisc (K := K) r) :
    PolynomialSpectrum (K := K) r hr :=
  ⟨⟨Spectrum.comap (polynomialEquiv r hr).toRingHom x.1.1, fun p => by
      rw [nnnorm_polynomial]
      change x.1.1.val (polynomialEquiv r hr p) ≤ gaussFun _ r _
      exact Spectrum.val_le_gauss_val (Spectrum.ext_val fun a => x.1.2 a) x.2 _⟩,
    fun a => x.1.2 a⟩

@[simp]
theorem polynomialRestrict_polynomialExtend (r : ℝ≥0) (hr : 0 < r) (x : ClosedDisc (K := K) r) :
    polynomialRestrict r hr (polynomialExtend r hr x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  apply Spectrum.ext_val
  intro p
  change x.1.1.val (polynomialEquiv r hr ((polynomialEquiv r hr).symm p)) = x.1.1.val p
  rw [RingEquiv.apply_symm_apply]

@[simp]
theorem polynomialExtend_polynomialRestrict (r : ℝ≥0) (hr : 0 < r)
    (x : PolynomialSpectrum (K := K) r hr) :
    polynomialExtend r hr (polynomialRestrict r hr x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  apply Spectrum.ext_val
  intro p
  change x.1.1.val ((polynomialEquiv r hr).symm (polynomialEquiv r hr p)) = x.1.1.val p
  rw [RingEquiv.symm_apply_apply]

/-- Original polynomial restriction is genuinely continuous in the existing evaluation topologies. -/
theorem continuous_polynomialRestrict (r : ℝ≥0) (hr : 0 < r) :
    Continuous (polynomialRestrict (K := K) r hr) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (Spectrum.continuous_comap (polynomialEquiv r hr).symm.toRingHom).comp
    (continuous_subtype_val.comp continuous_subtype_val)

/-- The actual weighted normed polynomial spectrum is exactly the genuine closed disc. -/
def polynomialSpectrumHomeomorph (r : ℝ≥0) (hr : 0 < r) :
    PolynomialSpectrum (K := K) r hr ≃ₜ ClosedDisc (K := K) r :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.mk (polynomialRestrict r hr) (polynomialExtend r hr)
    (polynomialExtend_polynomialRestrict r hr) (polynomialRestrict_polynomialExtend r hr))
    (continuous_polynomialRestrict r hr)

/-- The ACTUAL completed Gauss algebra spectrum is homeomorphic to the existing affine closed disc. -/
def discHomeomorph (r : ℝ≥0) (hr : 0 < r) :
    CompletionSpectrum (K := K) r hr ≃ₜ ClosedDisc (K := K) r :=
  (RelativeNormBoundedSpectrum.completionHomeomorph
    (NormedField.valuation (K := K)) (coefficients r hr)).trans (polynomialSpectrumHomeomorph r hr)

@[simp]
theorem discHomeomorph_val_polynomialMap (r : ℝ≥0) (hr : 0 < r)
    (x : CompletionSpectrum (K := K) r hr) (p : K[X]) :
    (discHomeomorph r hr x).1.1.val p = x.1.1.val (polynomialMap r hr p) := rfl

/-- Actual compactness of the genuine positive-radius closed affine disc. -/
theorem compactSpace_closedDisc (r : ℝ≥0) (hr : 0 < r) : CompactSpace (ClosedDisc (K := K) r) :=
  (discHomeomorph r hr).compactSpace

/-- The genuine normed-copy evaluation into the completed residue field of the ORIGINAL polynomial disc point. -/
def originalEvaluation (r : ℝ≥0) (hr : 0 < r) (x : ClosedDisc (K := K) r) :
    PolynomialRing (K := K) r hr →+* x.1.1.H :=
  x.1.1.toH.comp (polynomialEquiv r hr).toRingHom

/-- The true original-point evaluator is contractive on EVERY normed polynomial. -/
theorem nnnorm_originalEvaluation_le (r : ℝ≥0) (hr : 0 < r) (x : ClosedDisc (K := K) r)
    (p : PolynomialRing (K := K) r hr) : ‖originalEvaluation r hr x p‖₊ ≤ ‖p‖₊ := by
  rw [nnnorm_polynomial]
  change ‖x.1.1.toH (polynomialEquiv r hr p)‖₊ ≤ _
  rw [Spectrum.nnnorm_toH]
  exact (polynomialExtend r hr x).1.2 p

/-- Actual contractivity supplies continuity without a linear topology on K or H(x). -/
theorem lipschitz_originalEvaluation (r : ℝ≥0) (hr : 0 < r) (x : ClosedDisc (K := K) r) :
    LipschitzWith 1 (originalEvaluation r hr x) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub] using
    (show ‖originalEvaluation r hr x (p-q)‖ ≤ ‖p-q‖ from nnnorm_originalEvaluation_le r hr x (p-q))

/-- The ACTUAL completed-function ring map into H(x) of the ORIGINAL affine disc point. -/
def evaluationToH (r : ℝ≥0) (hr : 0 < r) (x : ClosedDisc (K := K) r) :
    Ring (K := K) r hr →+* x.1.1.H :=
  Completion.extensionHom (originalEvaluation r hr x) (lipschitz_originalEvaluation r hr x).continuous

@[simp]
theorem evaluationToH_polynomialMap (r : ℝ≥0) (hr : 0 < r) (x : ClosedDisc (K := K) r) (p : K[X]) :
    evaluationToH r hr x (polynomialMap r hr p) = x.1.1.toH p := by
  change Completion.extensionHom _ _ ((polynomialEquiv r hr).symm p :
    Completion (PolynomialRing (K := K) r hr)) = _
  rw [Completion.extensionHom_coe]
  change x.1.1.toH (polynomialEquiv r hr ((polynomialEquiv r hr).symm p)) = _
  rw [RingEquiv.apply_symm_apply]

/-- Every completed function retains the actual contractive H(x) evaluation bound. -/
theorem nnnorm_evaluationToH_le (r : ℝ≥0) (hr : 0 < r) (x : ClosedDisc (K := K) r)
    (f : Ring (K := K) r hr) : ‖evaluationToH r hr x f‖₊ ≤ ‖f‖₊ := by
  induction f using Completion.induction_on with
  | hp => exact isClosed_le (continuous_nnnorm.comp Completion.continuous_extension) continuous_nnnorm
  | ih p =>
    change ‖Completion.extensionHom _ _ (p : Completion (PolynomialRing (K := K) r hr))‖₊ ≤ _
    rw [Completion.extensionHom_coe, Completion.nnnorm_coe]
    exact nnnorm_originalEvaluation_le r hr x p

/-- Original polynomial values determine the WHOLE continuous completed-function ring homomorphism into the actual original H(x). -/
theorem evaluationToH_unique (r : ℝ≥0) (hr : 0 < r) (x : ClosedDisc (K := K) r)
    (g : Ring (K := K) r hr →+* x.1.1.H) (hg : Continuous g)
    (h : ∀ p : K[X], g (polynomialMap r hr p) = x.1.1.toH p) : g = evaluationToH r hr x := by
  apply RingHom.ext
  exact congrFun (Completion.denseRange_coe.equalizer hg Completion.continuous_extension (funext fun p => by
    have he : polynomialMap r hr (polynomialEquiv r hr p) = (p : Ring (K := K) r hr) := by
      exact congrArg (fun q : PolynomialRing (K := K) r hr => (q : Ring (K := K) r hr))
        ((polynomialEquiv r hr).symm_apply_apply p)
    change g (p : Ring (K := K) r hr) = evaluationToH r hr x (p : Ring (K := K) r hr)
    rw [← he, evaluationToH_polynomialMap]
    exact h _))

/-- Actual absolute values of genuine completed disc functions, furnished by the full spectrum homeomorphism. -/
def value (r : ℝ≥0) (hr : 0 < r) (f : Ring (K := K) r hr) (x : ClosedDisc (K := K) r) : ℝ≥0 :=
  ((discHomeomorph r hr).symm x).1.1.val f

@[simp]
theorem value_polynomialMap (r : ℝ≥0) (hr : 0 < r) (p : K[X]) (x : ClosedDisc (K := K) r) :
    value r hr (polynomialMap r hr p) x = x.1.1.val p := by
  have h := discHomeomorph_val_polynomialMap r hr ((discHomeomorph r hr).symm x) p
  rw [(discHomeomorph r hr).apply_symm_apply] at h
  exact h.symm

/-- Every ACTUAL completed disc function has a continuous absolute-value function on the whole genuine disc. -/
theorem continuous_value (r : ℝ≥0) (hr : 0 < r) (f : Ring (K := K) r hr) :
    Continuous (value r hr f) :=
  (Spectrum.continuous_val_apply f).comp (continuous_subtype_val.comp
    (continuous_subtype_val.comp (discHomeomorph r hr).symm.continuous))

/-- Extended logarithms of all actual completed disc functions are continuous, including zero and negative infinity. -/
theorem continuous_logValue (r : ℝ≥0) (hr : 0 < r) (f : Ring (K := K) r hr) :
    Continuous (fun x => ENNReal.log (value r hr f x : ℝ≥0∞)) :=
  ENNReal.continuous_log.comp (ENNReal.continuous_coe.comp (continuous_value r hr f))

/-- The entire spectral value is EXACTLY the norm of evaluation in the ORIGINAL point's actual completed residue field. -/
theorem value_eq_nnnorm_evaluationToH (r : ℝ≥0) (hr : 0 < r) (x : ClosedDisc (K := K) r)
    (f : Ring (K := K) r hr) : value r hr f x = ‖evaluationToH r hr x f‖₊ := by
  have he := Completion.denseRange_coe.equalizer
    (((discHomeomorph r hr).symm x).1.1.continuous_val_of_isNormBounded
      ((discHomeomorph r hr).symm x).1.2)
    (continuous_nnnorm.comp Completion.continuous_extension) (funext fun p => by
      have hp : polynomialMap r hr (polynomialEquiv r hr p) = (p : Ring (K := K) r hr) := by
        exact congrArg (fun q : PolynomialRing (K := K) r hr => (q : Ring (K := K) r hr))
          ((polynomialEquiv r hr).symm_apply_apply p)
      change value r hr (p : Ring (K := K) r hr) x = ‖evaluationToH r hr x (p : Ring (K := K) r hr)‖₊
      rw [← hp, value_polynomialMap, evaluationToH_polynomialMap, Spectrum.nnnorm_toH])
  exact congrFun he f

/-- The ACTUAL original Gauss point realizes the genuine norm of EVERY completed function. -/
theorem value_gaussPoint (r : ℝ≥0) (hr : 0 < r) (f : Ring (K := K) r hr) :
    value r hr f (gaussPoint (K := K) r) = ‖f‖₊ := by
  have he := Completion.denseRange_coe.equalizer
    (((discHomeomorph r hr).symm (gaussPoint (K := K) r)).1.1.continuous_val_of_isNormBounded
      ((discHomeomorph r hr).symm (gaussPoint (K := K) r)).1.2) continuous_nnnorm (funext fun p => by
      have hp : polynomialMap r hr (polynomialEquiv r hr p) = (p : Ring (K := K) r hr) := by
        exact congrArg (fun q : PolynomialRing (K := K) r hr => (q : Ring (K := K) r hr))
          ((polynomialEquiv r hr).symm_apply_apply p)
      change value r hr (p : Ring (K := K) r hr) (gaussPoint (K := K) r) = ‖(p : Ring (K := K) r hr)‖₊
      rw [← hp, value_polynomialMap, nnnorm_polynomialMap]
      rfl)
  exact congrFun he f

/-- Actual completed-function values on the whole disc are dominated by the genuine Gauss point. -/
theorem value_le_gaussPoint (r : ℝ≥0) (hr : 0 < r) (f : Ring (K := K) r hr)
    (x : ClosedDisc (K := K) r) : value r hr f x ≤ value r hr f (gaussPoint (K := K) r) := by
  rw [value_gaussPoint]
  exact ((discHomeomorph r hr).symm x).1.2 f

end GaussCompletion
end EnvelopeProperty.Berkovich
