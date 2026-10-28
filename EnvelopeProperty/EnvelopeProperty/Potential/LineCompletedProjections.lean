import EnvelopeProperty.Potential.LinePrincipalProjections
import Mathlib.Analysis.Normed.Group.HomCompletion

/-! # Genuine completed extensions of actual original rational principal projections -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

/-- `none` denotes the original polynomial component and `some j` the original hole component. -/
def rationalComponentLinearMap (i : Option (Fin m)) : U.RationalFunctions →ₗ[K] U.RationalFunctions :=
  match i with
  | none => U.rationalPolynomialLinearMap
  | some j => U.rationalPrincipalLinearMap j

theorem nnnorm_rationalComponent_le (i : Option (Fin m)) (f : U.RationalFunctions) :
    ‖U.normedRationalEquiv.symm (U.rationalComponentLinearMap i f)‖₊ ≤
      ‖U.normedRationalEquiv.symm f‖₊ := by
  cases i with
  | none => exact U.nnnorm_rationalPolynomialProjection_le f
  | some j => exact U.nnnorm_rationalPrincipalProjection_le j f

/-- The actual original component, transferred to the genuine boundary-seminormed rational copy. -/
def normedRationalComponent (i : Option (Fin m)) :
    NormedAddGroupHom U.NormedRationalFunctions U.NormedRationalFunctions where
  toFun f := U.normedRationalEquiv.symm (U.rationalComponentLinearMap i (U.normedRationalEquiv f))
  map_add' f g := by rw [map_add,map_add,map_add]
  bound' := ⟨1,fun f => by
    have hb := U.nnnorm_rationalComponent_le i (U.normedRationalEquiv f)
    rw [RingEquiv.symm_apply_apply] at hb
    simpa only [one_mul] using (show ‖U.normedRationalEquiv.symm
      (U.rationalComponentLinearMap i (U.normedRationalEquiv f))‖ ≤ ‖f‖ from hb)⟩

theorem normedRationalComponent_apply (i : Option (Fin m)) (f : U.NormedRationalFunctions) :
    U.normedRationalComponent i f =
      U.normedRationalEquiv.symm (U.rationalComponentLinearMap i (U.normedRationalEquiv f)) := rfl

theorem nnnorm_normedRationalComponent_le (i : Option (Fin m)) (f : U.NormedRationalFunctions) :
    ‖U.normedRationalComponent i f‖₊ ≤ ‖f‖₊ := by
  have hb := U.nnnorm_rationalComponent_le i (U.normedRationalEquiv f)
  rw [U.normedRationalComponent_apply]
  simpa only [RingEquiv.symm_apply_apply] using hb

theorem lipschitz_normedRationalComponent (i : Option (Fin m)) :
    LipschitzWith 1 (U.normedRationalComponent i) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have hb : ‖U.normedRationalComponent i (f-g)‖ ≤ ‖f-g‖ :=
    U.nnnorm_normedRationalComponent_le i (f-g)
  simpa only [NNReal.coe_one,one_mul,dist_eq_norm,← map_sub] using hb

/-- The GENUINE extension to the whole original separated norm completion. -/
def analyticComponent (i : Option (Fin m)) : NormedAddGroupHom U.AnalyticFunctions U.AnalyticFunctions :=
  (U.normedRationalComponent i).completion

theorem continuous_analyticComponent (i : Option (Fin m)) : Continuous (U.analyticComponent i) :=
  (U.analyticComponent i).continuous

theorem analyticComponent_rationalMap (i : Option (Fin m)) (f : U.RationalFunctions) :
    U.analyticComponent i (U.rationalMap f) = U.rationalMap (U.rationalComponentLinearMap i f) := by
  change (U.normedRationalComponent i).completion (U.normedRationalEquiv.symm f : U.AnalyticFunctions) = _
  rw [NormedAddGroupHom.completion_coe]
  change (U.normedRationalEquiv.symm
    (U.rationalComponentLinearMap i (U.normedRationalEquiv (U.normedRationalEquiv.symm f))) :
      U.AnalyticFunctions) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem nnnorm_analyticComponent_le (i : Option (Fin m)) (f : U.AnalyticFunctions) :
    ‖U.analyticComponent i f‖₊ ≤ ‖f‖₊ := by
  induction f using Completion.induction_on with
  | hp => exact isClosed_le (continuous_nnnorm.comp (U.continuous_analyticComponent i)) continuous_nnnorm
  | ih f =>
    change ‖(U.normedRationalComponent i).completion (f : U.AnalyticFunctions)‖₊ ≤ _
    rw [NormedAddGroupHom.completion_coe,Completion.nnnorm_coe,Completion.nnnorm_coe]
    exact U.nnnorm_normedRationalComponent_le i f

theorem rationalMap_original_coefficient (a : K) :
    U.rationalMap (algebraMap K U.RationalFunctions a) = algebraMap K U.AnalyticFunctions a := by
  rw [IsScalarTower.algebraMap_apply K K[X] U.RationalFunctions]
  rfl

/-- Original coefficients remain the same on completion, so the actual extension is K-linear. -/
theorem analyticComponent_coefficient_mul (i : Option (Fin m)) (a : K) (f : U.AnalyticFunctions) :
    U.analyticComponent i (algebraMap K U.AnalyticFunctions a*f) =
      algebraMap K U.AnalyticFunctions a*U.analyticComponent i f := by
  have hcont : Continuous (fun g : U.AnalyticFunctions => algebraMap K U.AnalyticFunctions a*g) :=
    continuous_const.mul continuous_id
  have he := U.denseRange_rationalMap.equalizer
    ((U.continuous_analyticComponent i).comp hcont)
    (hcont.comp (U.continuous_analyticComponent i)) (by
      funext g
      simp only [Function.comp_apply]
      rw [← U.rationalMap_original_coefficient a,← map_mul,U.analyticComponent_rationalMap,
        U.analyticComponent_rationalMap]
      have hg := (U.rationalComponentLinearMap i).map_smul a g
      simp only [Algebra.smul_def] at hg
      rw [hg,map_mul])
  exact congrFun he f

/-- Actual original-field linear maps on the whole original analytic algebra. -/
def analyticComponentLinearMap (i : Option (Fin m)) : U.AnalyticFunctions →ₗ[K] U.AnalyticFunctions where
  toFun := U.analyticComponent i
  map_add' := map_add (U.analyticComponent i)
  map_smul' a f := by
    simpa only [Algebra.smul_def,RingHom.id_apply] using U.analyticComponent_coefficient_mul i a f

theorem rationalComponent_sum (f : U.RationalFunctions) :
    f = U.rationalComponentLinearMap none f+∑ j, U.rationalComponentLinearMap (some j) f := by
  simpa [rationalComponentLinearMap,rationalPolynomialLinearMap,rationalPrincipalLinearMap] using
    U.rationalProjections_sum f

theorem rationalComponent_comp (i j : Option (Fin m)) (f : U.RationalFunctions) :
    U.rationalComponentLinearMap i (U.rationalComponentLinearMap j f) =
      if i = j then U.rationalComponentLinearMap j f else 0 := by
  classical
  cases i with
  | none =>
    cases j with
    | none => simpa [rationalComponentLinearMap,rationalPolynomialLinearMap] using U.rationalPolynomialProjection_comp f
    | some j => simpa [rationalComponentLinearMap,rationalPolynomialLinearMap,rationalPrincipalLinearMap] using
        U.rationalPolynomialProjection_principal j f
  | some i =>
    cases j with
    | none => simpa [rationalComponentLinearMap,rationalPolynomialLinearMap,rationalPrincipalLinearMap] using
        U.rationalPrincipalProjection_polynomial i f
    | some j => simpa [rationalComponentLinearMap,rationalPrincipalLinearMap] using
        U.rationalPrincipalProjection_comp i j f

/-- A whole finite decomposition in the GENUINE original completed algebra. -/
theorem analyticComponent_sum (f : U.AnalyticFunctions) :
    f = U.analyticComponent none f+∑ j, U.analyticComponent (some j) f := by
  have hcont : Continuous (fun g : U.AnalyticFunctions =>
      U.analyticComponent none g+∑ j, U.analyticComponent (some j) g) :=
    (U.continuous_analyticComponent none).add (continuous_finsetSum _ fun j _ => U.continuous_analyticComponent (some j))
  have he := U.denseRange_rationalMap.equalizer continuous_id hcont (by
    funext g
    simp_rw [Function.comp_apply,U.analyticComponent_rationalMap]
    rw [← map_sum,← map_add,← U.rationalComponent_sum g]
    rfl)
  exact congrFun he f

/-- All WHOLE completed projections remain idempotent and mutually annihilating. -/
theorem analyticComponent_comp (i j : Option (Fin m)) (f : U.AnalyticFunctions) :
    U.analyticComponent i (U.analyticComponent j f) =
      if i = j then U.analyticComponent j f else 0 := by
  classical
  have hright : Continuous (fun g : U.AnalyticFunctions => if i = j then U.analyticComponent j g else 0) := by
    split_ifs
    · exact U.continuous_analyticComponent j
    · exact continuous_const
  have he := U.denseRange_rationalMap.equalizer
    ((U.continuous_analyticComponent i).comp (U.continuous_analyticComponent j)) hright (by
      funext g
      simp_rw [Function.comp_apply,U.analyticComponent_rationalMap]
      rw [U.rationalComponent_comp]
      split_ifs <;> simp only [map_zero])
  exact congrFun he f

theorem nnnorm_analyticComponents (f : U.AnalyticFunctions) :
    ‖f‖₊ = max ‖U.analyticComponent none f‖₊
      (Finset.univ.sup fun j => ‖U.analyticComponent (some j) f‖₊) := by
  have hcont : Continuous (fun g : U.AnalyticFunctions =>
      max ‖U.analyticComponent none g‖₊
        (Finset.univ.sup fun j => ‖U.analyticComponent (some j) g‖₊)) :=
    (continuous_nnnorm.comp (U.continuous_analyticComponent none)).max
      (Continuous.finset_sup_apply (s := Finset.univ) fun j _ =>
        continuous_nnnorm.comp (U.continuous_analyticComponent (some j)))
  have he := U.denseRange_rationalMap.equalizer continuous_nnnorm hcont (by
    funext g
    simp_rw [Function.comp_apply,U.analyticComponent_rationalMap]
    have hnorm (a : U.RationalFunctions) : ‖U.rationalMap a‖₊ = ‖U.normedRationalEquiv.symm a‖₊ :=
      Completion.nnnorm_coe _
    simp_rw [hnorm]
    simpa [rationalComponentLinearMap,rationalPolynomialLinearMap,rationalPrincipalLinearMap] using
      U.nnnorm_rationalProjections g)
  exact congrFun he f

/-- The ACTUAL original polynomial/proper-fraction subset, rather than an abstract summand certificate. -/
def rationalComponentSet (i : Option (Fin m)) : Set U.AnalyticFunctions :=
  match i with
  | none => Set.range U.polynomialAnalyticMap
  | some j => {g | ∃ (p : K[X]) (n : ℕ), p.degree < n ∧ U.rationalMap (U.properRationalPart p j n) = g}

theorem rationalComponent_rationalMap_mem (i : Option (Fin m)) (f : U.RationalFunctions) :
    U.rationalMap (U.rationalComponentLinearMap i f) ∈ U.rationalComponentSet i := by
  cases i with
  | none => exact ⟨U.rationalPolynomialPart f,rfl⟩
  | some j => exact ⟨U.rationalPrincipalNumerator f j,U.rationalPresentationExponent f,
      U.rationalPrincipalNumerator_degree_lt f j,rfl⟩

/-- Every completed component lies in the closure of its ACTUAL original polynomial or proper-fraction space. -/
theorem analyticComponent_mem_closure (i : Option (Fin m)) (f : U.AnalyticFunctions) :
    U.analyticComponent i f ∈ closure (U.rationalComponentSet i) := by
  induction f using Completion.induction_on with
  | hp => exact isClosed_closure.preimage (U.continuous_analyticComponent i)
  | ih f =>
    change U.analyticComponent i (U.rationalMap (U.normedRationalEquiv f)) ∈ _
    rw [U.analyticComponent_rationalMap]
    exact subset_closure (U.rationalComponent_rationalMap_mem i _)

theorem rationalComponentSet_has_preimage (i : Option (Fin m)) (g : U.AnalyticFunctions)
    (hg : g ∈ U.rationalComponentSet i) :
    ∃ f : U.RationalFunctions, U.rationalMap (U.rationalComponentLinearMap i f) = g := by
  cases i with
  | none =>
    rcases hg with ⟨P,rfl⟩
    refine ⟨algebraMap K[X] U.RationalFunctions P,?_⟩
    change U.rationalMap (algebraMap K[X] U.RationalFunctions
      (U.rationalPolynomialPart (algebraMap K[X] U.RationalFunctions P))) = _
    rw [(U.rationalPolynomialPart_of_polynomial P).1]
    rfl
  | some j =>
    rcases hg with ⟨p,n,hp,hg⟩
    refine ⟨U.properRationalPart p j n,?_⟩
    change U.rationalMap (U.rationalPrincipalProjection j (U.properRationalPart p j n)) = _
    rw [(U.rationalProjections_of_properRationalPart p j n hp).2 j,if_pos rfl]
    exact hg

/-- The actual closed component spaces are fixed pointwise, and annihilated by every other component. -/
theorem analyticComponent_of_mem_closure (i j : Option (Fin m)) (g : U.AnalyticFunctions)
    (hg : g ∈ closure (U.rationalComponentSet j)) :
    U.analyticComponent i g = if i = j then g else 0 := by
  classical
  have hright : Continuous (fun a : U.AnalyticFunctions => if i = j then a else 0) := by
    split_ifs
    · exact continuous_id
    · exact continuous_const
  have hsub : U.rationalComponentSet j ⊆
      {a | U.analyticComponent i a = if i = j then a else 0} := by
    intro a ha
    obtain ⟨f,rfl⟩ := U.rationalComponentSet_has_preimage j a ha
    change U.analyticComponent i (U.rationalMap (U.rationalComponentLinearMap j f)) =
      if i = j then U.rationalMap (U.rationalComponentLinearMap j f) else 0
    rw [← U.analyticComponent_rationalMap j f,U.analyticComponent_comp]
  exact closure_minimal hsub (isClosed_eq (U.continuous_analyticComponent i) hright) hg

/-- The image is exactly the closure of the ACTUAL original polynomial or proper-fraction functions. -/
theorem range_analyticComponent (i : Option (Fin m)) :
    Set.range (U.analyticComponent i) = closure (U.rationalComponentSet i) := by
  apply Set.Subset.antisymm
  · rintro g ⟨f,rfl⟩
    exact U.analyticComponent_mem_closure i f
  · intro g hg
    refine ⟨g,?_⟩
    simpa using U.analyticComponent_of_mem_closure i i g hg

theorem isClosed_range_analyticComponent (i : Option (Fin m)) :
    IsClosed (Set.range (U.analyticComponent i)) := by
  rw [U.range_analyticComponent]
  exact isClosed_closure

/-- Uniqueness of completed decompositions in the ACTUAL original component closures. -/
theorem analyticComponents_unique (f P : U.AnalyticFunctions) (R : Fin m → U.AnalyticFunctions)
    (hP : P ∈ closure (U.rationalComponentSet none))
    (hR : ∀ j, R j ∈ closure (U.rationalComponentSet (some j)))
    (he : f = P+∑ j, R j) :
    U.analyticComponent none f = P ∧ ∀ j, U.analyticComponent (some j) f = R j := by
  classical
  have hcomp (i : Option (Fin m)) : U.analyticComponent i f =
      (if i = none then P else 0)+∑ j, if i = some j then R j else 0 := by
    rw [he,map_add,map_sum,U.analyticComponent_of_mem_closure i none P hP]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact U.analyticComponent_of_mem_closure i (some j) (R j) (hR j)
  refine ⟨?_,fun j => ?_⟩
  · simpa using hcomp none
  · simpa using hcomp (some j)
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
