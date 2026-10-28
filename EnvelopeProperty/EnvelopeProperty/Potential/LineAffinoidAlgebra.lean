import EnvelopeProperty.Potential.LineRationalFunctions
import EnvelopeProperty.Berkovich.SpectrumNormedCompletion
import Mathlib.Analysis.Normed.Ring.Basic

/-! # The genuine finite-boundary norm completion of original rational functions -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

/-- The actual finite Gauss boundary, with duplicates already identified as points. -/
@[instance_reducible] def rationalBoundaryFintype : Fintype U.boundary := U.finite_boundary.fintype

local instance : Fintype U.boundary := U.rationalBoundaryFintype
local instance : Nonempty U.boundary := ⟨⟨U.outerGauss,Set.mem_insert _ _⟩⟩

/-- A copy of the ORIGINAL rational algebra carrying its actual finite-boundary seminorm. -/
def NormedRationalFunctions : Type _ := U.RationalFunctions

instance normedRationalFunctionsCommRing : CommRing U.NormedRationalFunctions :=
  inferInstanceAs (CommRing U.RationalFunctions)

/-- The whole original ring identification before taking the genuine completion. -/
def normedRationalEquiv : U.NormedRationalFunctions ≃+* U.RationalFunctions := RingEquiv.refl _

/-- The prescribed ORIGINAL coefficient map in the seminormed rational copy. -/
def rationalCoefficients : K →+* U.NormedRationalFunctions :=
  U.normedRationalEquiv.symm.toRingHom.comp ((algebraMap K[X] U.RationalFunctions).comp C)

instance normedRationalFunctionsAlgebra : Algebra K U.NormedRationalFunctions :=
  U.rationalCoefficients.toAlgebra

/-- Evaluate in the finite product of the ORIGINAL completed residue fields. -/
def rationalBoundaryEvaluation : U.NormedRationalFunctions →+* (∀ z : U.boundary, z.1.1.H) where
  toFun f z := U.rationalEvaluation ⟨z.1,U.boundary_subset z.2⟩ (U.normedRationalEquiv f)
  map_one' := by funext z; exact map_one _
  map_mul' f g := by funext z; exact map_mul _ _ _
  map_zero' := by funext z; exact map_zero _
  map_add' f g := by funext z; exact map_add _ _ _

instance normedRationalFunctionsSeminormedCommRing : SeminormedCommRing U.NormedRationalFunctions :=
  SeminormedCommRing.induced _ _ U.rationalBoundaryEvaluation

instance normedRationalFunctionsNormOneClass : NormOneClass U.NormedRationalFunctions :=
  NormOneClass.induced _ _ U.rationalBoundaryEvaluation

instance normedRationalFunctionsIsUltrametricDist : IsUltrametricDist U.NormedRationalFunctions :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun a b => by
    change ‖U.rationalBoundaryEvaluation (a+b)‖ ≤
      max ‖U.rationalBoundaryEvaluation a‖ ‖U.rationalBoundaryEvaluation b‖
    rw [map_add]
    exact IsUltrametricDist.norm_add_le_max _ _

omit [IsAlgClosed K] in
/-- The entire original rational norm is EXACTLY its actual finite boundary maximum. -/
theorem nnnorm_normedRationalFunctions (f : U.NormedRationalFunctions) :
    ‖f‖₊ = Finset.univ.sup (fun z : U.boundary =>
      U.rationalValue (U.normedRationalEquiv f) ⟨z.1,U.boundary_subset z.2⟩) := by
  change ‖U.rationalBoundaryEvaluation f‖₊ = _
  rw [Pi.nnnorm_def]
  congr 1
  funext z
  exact U.nnnorm_rationalEvaluation _ _

omit [IsAlgClosed K] in
theorem nnnorm_rationalCoefficients (a : K) : ‖U.rationalCoefficients a‖₊ = w a := by
  rw [U.nnnorm_normedRationalFunctions]
  have he (z : U.boundary) : U.rationalValue (U.normedRationalEquiv (U.rationalCoefficients a))
      ⟨z.1,U.boundary_subset z.2⟩ = w a := by
    change U.rationalValue (algebraMap K[X] U.RationalFunctions (C a)) _ = w a
    rw [U.rationalValue_polynomial]
    exact z.1.2 a
  simp only [he,Finset.sup_const Finset.univ_nonempty]

/-- The derived actual rational maximum modulus bounds every ORIGINAL evaluator. -/
theorem nnnorm_rationalEvaluation_le (x : U.carrier) (f : U.NormedRationalFunctions) :
    ‖U.rationalEvaluation x (U.normedRationalEquiv f)‖₊ ≤ ‖f‖₊ := by
  rw [U.nnnorm_rationalEvaluation,U.nnnorm_normedRationalFunctions]
  obtain ⟨z,hz⟩ := U.rationalValue_exists_boundary_max (U.normedRationalEquiv f)
  exact (hz x).trans (Finset.le_sup (f := fun z : U.boundary =>
    U.rationalValue (U.normedRationalEquiv f) ⟨z.1,U.boundary_subset z.2⟩) (Finset.mem_univ z))

/-- The original whole rational evaluator on the seminormed copy, into the SAME original H(x). -/
def normedRationalEvaluation (x : U.carrier) : U.NormedRationalFunctions →+* x.1.1.H :=
  (U.rationalEvaluation x).comp U.normedRationalEquiv.toRingHom

theorem lipschitz_normedRationalEvaluation (x : U.carrier) :
    LipschitzWith 1 (U.normedRationalEvaluation x) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hle : ‖U.normedRationalEvaluation x (a-b)‖ ≤ ‖a-b‖ :=
    U.nnnorm_rationalEvaluation_le x (a-b)
  simpa only [NNReal.coe_one,one_mul,dist_eq_norm,← map_sub] using hle

/-- The GENUINE separated norm completion of the ORIGINAL rational ring with its actual boundary norm. -/
abbrev AnalyticFunctions := Completion U.NormedRationalFunctions

instance analyticFunctionsNormOneClass : NormOneClass U.AnalyticFunctions where
  norm_one := by rw [← Completion.coe_one,Completion.norm_coe,norm_one]

/-- The coefficient map in the TRUE completion is the original coefficient map followed by completion. -/
def analyticCoefficients : K →+* U.AnalyticFunctions :=
  Completion.coeRingHom.comp U.rationalCoefficients

instance analyticFunctionsAlgebra : Algebra K U.AnalyticFunctions := U.analyticCoefficients.toAlgebra

omit [IsAlgClosed K] in
theorem nnnorm_algebraMap_analyticFunctions (a : K) :
    ‖algebraMap K U.AnalyticFunctions a‖₊ = w a := by
  change ‖(U.rationalCoefficients a : U.AnalyticFunctions)‖₊ = _
  rw [Completion.nnnorm_coe,U.nnnorm_rationalCoefficients]

/-- The original entire rational algebra maps densely into its true norm completion. -/
def rationalMap : U.RationalFunctions →+* U.AnalyticFunctions :=
  Completion.coeRingHom.comp U.normedRationalEquiv.symm.toRingHom

omit [IsAlgClosed K] in
theorem denseRange_rationalMap : DenseRange U.rationalMap := by
  change Dense (Set.range (((↑) : U.NormedRationalFunctions → U.AnalyticFunctions) ∘
    U.normedRationalEquiv.symm))
  rw [U.normedRationalEquiv.symm.surjective.range_comp]
  exact Completion.denseRange_coe

omit [IsAlgClosed K] in
theorem nnnorm_rationalMap (f : U.RationalFunctions) :
    ‖U.rationalMap f‖₊ = Finset.univ.sup (fun z : U.boundary =>
      U.rationalValue f ⟨z.1,U.boundary_subset z.2⟩) := by
  change ‖(U.normedRationalEquiv.symm f : U.AnalyticFunctions)‖₊ = _
  rw [Completion.nnnorm_coe,U.nnnorm_normedRationalFunctions,RingEquiv.apply_symm_apply]

/-- Every original point evaluates the WHOLE actual completion in its ORIGINAL completed residue field. -/
def evaluationToH (x : U.carrier) : U.AnalyticFunctions →+* x.1.1.H :=
  Completion.extensionHom (U.normedRationalEvaluation x)
    (U.lipschitz_normedRationalEvaluation x).continuous

theorem evaluationToH_coe (x : U.carrier) (f : U.NormedRationalFunctions) :
    U.evaluationToH x (f : U.AnalyticFunctions) = U.normedRationalEvaluation x f :=
  Completion.extensionHom_coe _ _ f

theorem evaluationToH_rationalMap (x : U.carrier) (f : U.RationalFunctions) :
    U.evaluationToH x (U.rationalMap f) = U.rationalEvaluation x f := by
  change U.evaluationToH x (U.normedRationalEquiv.symm f : U.AnalyticFunctions) = _
  rw [U.evaluationToH_coe]
  change U.rationalEvaluation x (U.normedRationalEquiv (U.normedRationalEquiv.symm f)) = _
  rw [RingEquiv.apply_symm_apply]

theorem continuous_evaluationToH (x : U.carrier) : Continuous (U.evaluationToH x) :=
  Completion.continuous_extension

theorem evaluationToH_unique (x : U.carrier) (g : U.AnalyticFunctions →+* x.1.1.H)
    (hg : Continuous g) (h : ∀ f : U.RationalFunctions, g (U.rationalMap f) = U.rationalEvaluation x f) :
    g = U.evaluationToH x := by
  apply RingHom.ext
  exact congrFun (U.denseRange_rationalMap.equalizer hg (U.continuous_evaluationToH x)
    (funext fun f => (h f).trans (U.evaluationToH_rationalMap x f).symm))

theorem nnnorm_evaluationToH_le (x : U.carrier) (f : U.AnalyticFunctions) :
    ‖U.evaluationToH x f‖₊ ≤ ‖f‖₊ := by
  induction f using Completion.induction_on with
  | hp => exact isClosed_le (continuous_nnnorm.comp (U.continuous_evaluationToH x)) continuous_nnnorm
  | ih f =>
    rw [U.evaluationToH_coe,Completion.nnnorm_coe]
    exact U.nnnorm_rationalEvaluation_le x f

/-- The actual value of a completed function at an original point. -/
def analyticValue (f : U.AnalyticFunctions) (x : U.carrier) : ℝ≥0 := ‖U.evaluationToH x f‖₊

theorem analyticValue_rationalMap (f : U.RationalFunctions) (x : U.carrier) :
    U.analyticValue (U.rationalMap f) x = U.rationalValue f x := by
  rw [analyticValue,U.evaluationToH_rationalMap,U.nnnorm_rationalEvaluation]

theorem analyticValue_le_nnnorm (f : U.AnalyticFunctions) (x : U.carrier) :
    U.analyticValue f x ≤ ‖f‖₊ := U.nnnorm_evaluationToH_le x f

/-- The original finite-boundary norm identity holds on EVERY element of the actual completion. -/
theorem nnnorm_eq_boundary_nnnorm (f : U.AnalyticFunctions) :
    ‖f‖₊ = ‖(fun z : U.boundary => U.evaluationToH ⟨z.1,U.boundary_subset z.2⟩ f)‖₊ := by
  induction f using Completion.induction_on with
  | hp =>
    apply isClosed_eq continuous_nnnorm
    exact continuous_nnnorm.comp (continuous_pi fun z => U.continuous_evaluationToH _)
  | ih f =>
    rw [Completion.nnnorm_coe]
    simp only [U.evaluationToH_coe]
    rfl

/-- The true finite-boundary maximum formula for the WHOLE actual function algebra. -/
theorem nnnorm_eq_boundary_max (f : U.AnalyticFunctions) :
    ‖f‖₊ = Finset.univ.sup (fun z : U.boundary =>
      U.analyticValue f ⟨z.1,U.boundary_subset z.2⟩) := by
  rw [U.nnnorm_eq_boundary_nnnorm,Pi.nnnorm_def]
  rfl

/-- One ORIGINAL Gauss boundary point realizes the norm of every completed function. -/
theorem analyticValue_exists_boundary_norm (f : U.AnalyticFunctions) :
    ∃ z : U.boundary, U.analyticValue f ⟨z.1,U.boundary_subset z.2⟩ = ‖f‖₊ := by
  have hne : (Finset.univ : Finset U.boundary).Nonempty :=
    ⟨⟨U.outerGauss,Set.mem_insert _ _⟩,Finset.mem_univ _⟩
  obtain ⟨z,_,hz⟩ := Finset.exists_mem_eq_sup Finset.univ hne
    (fun z : U.boundary => U.analyticValue f ⟨z.1,U.boundary_subset z.2⟩)
  exact ⟨z,hz.symm.trans (U.nnnorm_eq_boundary_max f).symm⟩

theorem analyticValue_exists_boundary_max (f : U.AnalyticFunctions) :
    ∃ z : U.boundary, ∀ x : U.carrier,
      U.analyticValue f x ≤ U.analyticValue f ⟨z.1,U.boundary_subset z.2⟩ := by
  obtain ⟨z,hz⟩ := U.analyticValue_exists_boundary_norm f
  exact ⟨z,fun x => (U.analyticValue_le_nnnorm f x).trans_eq hz.symm⟩

/-- Power multiplicativity is derived from actual original boundary evaluations. -/
theorem nnnorm_pow_analyticFunctions (f : U.AnalyticFunctions) (n : ℕ) :
    ‖f^n‖₊ = ‖f‖₊^n := by
  apply le_antisymm (nnnorm_pow_le f n)
  obtain ⟨z,hz⟩ := U.analyticValue_exists_boundary_norm f
  have hb := U.analyticValue_le_nnnorm (f^n) ⟨z.1,U.boundary_subset z.2⟩
  change ‖U.evaluationToH ⟨z.1,U.boundary_subset z.2⟩ (f^n)‖₊ ≤ _ at hb
  rw [map_pow,nnnorm_pow] at hb
  exact (congrArg (fun t : ℝ≥0 => t^n) hz).symm.le.trans hb
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
