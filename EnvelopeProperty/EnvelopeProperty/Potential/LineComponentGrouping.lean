import EnvelopeProperty.Potential.LineHoleRouting
import EnvelopeProperty.Potential.LineOuterComponentTransport

/-! # Actual finite grouping of WHOLE restricted completed components -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] {m n : ℕ}
variable (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)
variable (W : FCStandardAffinoid (NormedField.valuation (K := K)) n)
variable (hWU : W.carrier ⊆ U.carrier)

/-- EVERY WHOLE actual source principal closure restricts into the target component DERIVED from original hole geometry. -/
theorem analyticRestriction_principal_closure_routed (i : Fin m) (f : U.AnalyticFunctions)
    (hf : f ∈ closure (U.rationalComponentSet (some i))) :
    U.analyticRestriction W hWU f ∈ closure (W.rationalComponentSet (W.restrictionHoleIndex U hWU i)) := by
  cases hi : W.restrictionHoleIndex U hWU i with
  | none =>
    exact U.analyticRestriction_principal_closure_of_hole_disjoint_outer W hWU i
      ((W.restrictionHoleIndex_eq_none_iff U hWU i).mp hi) f hf
  | some j =>
    exact U.analyticRestriction_principal_closure_of_hole_subset W hWU i j
      ((W.restrictionHoleIndex_eq_some_iff U hWU i j).mp hi) f hf

/-- A WHOLE actual restricted source component is fixed or annihilated by the original target projection according to its DERIVED geometric route. -/
theorem analyticComponent_restriction_principal (k : Option (Fin n)) (i : Fin m) (f : U.AnalyticFunctions) :
    W.analyticComponent k (U.analyticRestriction W hWU (U.analyticComponent (some i) f)) =
      if k = W.restrictionHoleIndex U hWU i then
        U.analyticRestriction W hWU (U.analyticComponent (some i) f) else 0 := by
  classical
  exact W.analyticComponent_of_mem_closure k (W.restrictionHoleIndex U hWU i) _
    (U.analyticRestriction_principal_closure_routed W hWU i _ (U.analyticComponent_mem_closure (some i) f))

/-- Actual polynomial restrictions are fixed by the original polynomial target projection and annihilated by every principal target projection. -/
theorem analyticComponent_restriction_polynomial (k : Option (Fin n)) (f : U.AnalyticFunctions) :
    W.analyticComponent k (U.analyticRestriction W hWU (U.analyticComponent none f)) =
      if k = none then U.analyticRestriction W hWU (U.analyticComponent none f) else 0 := by
  classical
  exact W.analyticComponent_of_mem_closure k none _
    (U.analyticRestriction_polynomial_closure W hWU _ (U.analyticComponent_mem_closure none f))

/-- EVERY target component of a WHOLE completed restriction is the finite sum of EXACTLY its geometrically routed original components. -/
theorem analyticComponent_analyticRestriction_grouped (k : Option (Fin n)) (f : U.AnalyticFunctions) :
    W.analyticComponent k (U.analyticRestriction W hWU f) =
      (if k = none then U.analyticRestriction W hWU (U.analyticComponent none f) else 0)+
        ∑ i, if k = W.restrictionHoleIndex U hWU i then
          U.analyticRestriction W hWU (U.analyticComponent (some i) f) else 0 := by
  classical
  have he := congrArg (fun g : U.AnalyticFunctions => W.analyticComponent k (U.analyticRestriction W hWU g))
    (U.analyticComponent_sum f)
  simpa only [map_add,map_sum,U.analyticComponent_restriction_polynomial W hWU,
    U.analyticComponent_restriction_principal W hWU] using he
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
