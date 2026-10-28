import EnvelopeProperty.Potential.LineAffinoidUnits

/-! # Actual restriction homomorphisms for arbitrary standard-affinoid containments -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m n : ℕ}
variable (U : FCStandardAffinoid w m) (V : FCStandardAffinoid w n)
variable (hVU : V.carrier ⊆ U.carrier)
local instance : Fintype V.boundary := V.rationalBoundaryFintype

/-- The ORIGINAL polynomial map into the genuine completed function ring. -/
def polynomialAnalyticMap : K[X] →+* U.AnalyticFunctions :=
  U.rationalMap.comp (algebraMap K[X] U.RationalFunctions)

include hVU in
/-- Actual containment and the proved whole unit criterion CONSTRUCT the denominator unit. -/
theorem isUnit_restriction_denominator : IsUnit (V.polynomialAnalyticMap U.denominatorPolynomial) := by
  apply (V.analyticFunctions_isUnit_iff _).mpr
  intro x
  change V.analyticValue (V.rationalMap (algebraMap K[X] V.RationalFunctions U.denominatorPolynomial)) x ≠ 0
  rw [V.analyticValue_rationalMap,V.rationalValue_polynomial]
  exact U.denominatorPolynomial_val_ne_zero ⟨x.1,hVU x.2⟩

/-- The genuine localization map into the SAME actual target completion, using its DERIVED denominator unit. -/
def rationalRestriction : U.RationalFunctions →+* V.AnalyticFunctions :=
  IsLocalization.lift (M := Submonoid.powers U.denominatorPolynomial)
    (g := V.polynomialAnalyticMap) (by
      rintro ⟨_,k,rfl⟩
      simpa only [map_pow] using (U.isUnit_restriction_denominator V hVU).pow k)

theorem rationalRestriction_polynomial (p : K[X]) :
    U.rationalRestriction V hVU (algebraMap K[X] U.RationalFunctions p) = V.polynomialAnalyticMap p := by
  rw [rationalRestriction,IsLocalization.lift_eq]

/-- The whole rational restriction retains the actual evaluator into the SAME ORIGINAL H(x). -/
theorem rationalRestriction_evaluation (x : V.carrier) (f : U.RationalFunctions) :
    V.evaluationToH x (U.rationalRestriction V hVU f) = U.rationalEvaluation ⟨x.1,hVU x.2⟩ f := by
  have he : (V.evaluationToH x).comp (U.rationalRestriction V hVU) =
      U.rationalEvaluation ⟨x.1,hVU x.2⟩ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers U.denominatorPolynomial)
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply,U.rationalRestriction_polynomial,polynomialAnalyticMap,
      V.evaluationToH_rationalMap,V.rationalEvaluation_polynomial,U.rationalEvaluation_polynomial]
  exact congrArg (fun g => g f) he

/-- No boundary-norm certificate is assumed: every target boundary point is an ORIGINAL point of U. -/
theorem nnnorm_rationalRestriction_le (f : U.NormedRationalFunctions) :
    ‖U.rationalRestriction V hVU (U.normedRationalEquiv f)‖₊ ≤ ‖f‖₊ := by
  rw [V.nnnorm_eq_boundary_max]
  apply Finset.sup_le
  intro z _
  change ‖V.evaluationToH ⟨z.1,V.boundary_subset z.2⟩
    (U.rationalRestriction V hVU (U.normedRationalEquiv f))‖₊ ≤ ‖f‖₊
  rw [U.rationalRestriction_evaluation]
  exact U.nnnorm_rationalEvaluation_le _ f

def normedRationalRestriction : U.NormedRationalFunctions →+* V.AnalyticFunctions :=
  (U.rationalRestriction V hVU).comp U.normedRationalEquiv.toRingHom

theorem lipschitz_normedRationalRestriction : LipschitzWith 1 (U.normedRationalRestriction V hVU) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hle : ‖U.normedRationalRestriction V hVU (a-b)‖ ≤ ‖a-b‖ :=
    U.nnnorm_rationalRestriction_le V hVU (a-b)
  simpa only [NNReal.coe_one,one_mul,dist_eq_norm,← map_sub] using hle

/-- The ACTUAL whole completion restriction for every genuine containment, with no hole-list compatibility assumption. -/
def analyticRestriction : U.AnalyticFunctions →+* V.AnalyticFunctions :=
  Completion.extensionHom (U.normedRationalRestriction V hVU)
    (U.lipschitz_normedRationalRestriction V hVU).continuous

theorem analyticRestriction_rationalMap (f : U.RationalFunctions) :
    U.analyticRestriction V hVU (U.rationalMap f) = U.rationalRestriction V hVU f := by
  change U.analyticRestriction V hVU (U.normedRationalEquiv.symm f : U.AnalyticFunctions) = _
  rw [analyticRestriction,Completion.extensionHom_coe]
  change U.rationalRestriction V hVU (U.normedRationalEquiv (U.normedRationalEquiv.symm f)) = _
  rw [RingEquiv.apply_symm_apply]

theorem analyticRestriction_polynomial (p : K[X]) :
    U.analyticRestriction V hVU (U.polynomialAnalyticMap p) = V.polynomialAnalyticMap p := by
  exact (U.analyticRestriction_rationalMap V hVU _).trans (U.rationalRestriction_polynomial V hVU p)

theorem continuous_analyticRestriction : Continuous (U.analyticRestriction V hVU) :=
  Completion.continuous_extension

theorem nnnorm_analyticRestriction_le (f : U.AnalyticFunctions) :
    ‖U.analyticRestriction V hVU f‖₊ ≤ ‖f‖₊ := by
  induction f using Completion.induction_on with
  | hp => exact isClosed_le (continuous_nnnorm.comp (U.continuous_analyticRestriction V hVU)) continuous_nnnorm
  | ih f =>
    rw [analyticRestriction,Completion.extensionHom_coe,Completion.nnnorm_coe]
    exact U.nnnorm_rationalRestriction_le V hVU f

/-- Equality of the WHOLE original completed evaluator, rather than merely equality of its norm. -/
theorem analyticRestriction_evaluation (x : V.carrier) (f : U.AnalyticFunctions) :
    V.evaluationToH x (U.analyticRestriction V hVU f) = U.evaluationToH ⟨x.1,hVU x.2⟩ f := by
  have he := U.evaluationToH_unique ⟨x.1,hVU x.2⟩
    ((V.evaluationToH x).comp (U.analyticRestriction V hVU))
    ((V.continuous_evaluationToH x).comp (U.continuous_analyticRestriction V hVU))
    (fun p => by rw [RingHom.comp_apply,U.analyticRestriction_rationalMap,U.rationalRestriction_evaluation])
  exact congrArg (fun g => g f) he

theorem analyticValue_analyticRestriction (f : U.AnalyticFunctions) (x : V.carrier) :
    V.analyticValue (U.analyticRestriction V hVU f) x = U.analyticValue f ⟨x.1,hVU x.2⟩ := by
  rw [analyticValue,analyticValue,U.analyticRestriction_evaluation]

theorem analyticRestriction_algebraMap (a : K) :
    U.analyticRestriction V hVU (algebraMap K U.AnalyticFunctions a) = algebraMap K V.AnalyticFunctions a :=
  U.analyticRestriction_polynomial V hVU (C a)

/-- The constructed whole restriction retains the ORIGINAL coefficient algebra structures. -/
def analyticRestrictionAlgHom : U.AnalyticFunctions →ₐ[K] V.AnalyticFunctions where
  __ := U.analyticRestriction V hVU
  commutes' := U.analyticRestriction_algebraMap V hVU

omit [IsAlgClosed K] in
/-- Actual localization uniqueness and density give the universal ORIGINAL-polynomial test for continuous maps. -/
theorem analyticRingHom_ext_on_polynomials {A : Type*} [CommRing A] [TopologicalSpace A] [T2Space A]
    (f g : U.AnalyticFunctions →+* A) (hf : Continuous f) (hg : Continuous g)
    (hpoly : ∀ p : K[X], f (U.polynomialAnalyticMap p) = g (U.polynomialAnalyticMap p)) : f = g := by
  have hr : f.comp U.rationalMap = g.comp U.rationalMap := by
    apply IsLocalization.ringHom_ext (Submonoid.powers U.denominatorPolynomial)
    exact RingHom.ext hpoly
  apply RingHom.ext
  exact congrFun (U.denseRange_rationalMap.equalizer hf hg
    (funext fun p => congrArg (fun q => q p) hr))

theorem analyticRestriction_self : U.analyticRestriction U (fun _ h => h) = RingHom.id U.AnalyticFunctions := by
  apply U.analyticRingHom_ext_on_polynomials _ _ (U.continuous_analyticRestriction U _) continuous_id
  intro p
  exact U.analyticRestriction_polynomial U _ p

theorem analyticRestriction_comp {l : ℕ} (W : FCStandardAffinoid w l) (hWV : W.carrier ⊆ V.carrier) :
    (V.analyticRestriction W hWV).comp (U.analyticRestriction V hVU) =
      U.analyticRestriction W (hWV.trans hVU) := by
  apply U.analyticRingHom_ext_on_polynomials _ _
    ((V.continuous_analyticRestriction W hWV).comp (U.continuous_analyticRestriction V hVU))
    (U.continuous_analyticRestriction W _)
  intro p
  simp only [RingHom.comp_apply,U.analyticRestriction_polynomial,V.analyticRestriction_polynomial]
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
