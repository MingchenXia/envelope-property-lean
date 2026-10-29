import EnvelopeProperty.Potential.LinePrincipalTransport

/-! # Whole original principal components detected at their ACTUAL original Gauss boundary -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] {m n : ℕ}
variable (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)

/-- EVERY WHOLE actual principal component has exact norm equal to evaluation at its ORIGINAL hole Gauss point. -/
theorem nnnorm_principal_closure_eq_boundary_value (i : Fin m) (f : U.AnalyticFunctions)
    (hf : f ∈ closure (U.rationalComponentSet (some i))) :
    ‖f‖₊ = U.analyticValue f ⟨U.holeBoundaryPoint i,U.holeGauss_mem i⟩ := by
  apply closure_minimal (t := {g | ‖g‖₊ = U.analyticValue g ⟨U.holeBoundaryPoint i,U.holeGauss_mem i⟩}) _
    (isClosed_eq continuous_nnnorm (continuous_nnnorm.comp (U.continuous_evaluationToH _))) hf
  rintro g ⟨p,k,hp,rfl⟩
  change ‖U.rationalMap (U.properRationalPart p i k)‖₊ =
    U.analyticValue (U.rationalMap (U.properRationalPart p i k)) ⟨U.holeBoundaryPoint i,U.holeGauss_mem i⟩
  rw [U.properRationalPart_eq_inversePolynomial p i k hp,U.analyticValue_rationalMap,
    U.nnnorm_inverseRationalPolynomial,U.inverseRationalPolynomial_boundary_value]

variable (W : FCStandardAffinoid (NormedField.valuation (K := K)) n)
variable (hWU : W.carrier ⊆ U.carrier)

/-- A surviving ORIGINAL source-hole boundary derives exact restriction norm on the WHOLE principal closure, even at differing target centres. -/
theorem nnnorm_restriction_principal_of_boundary_mem (i : Fin m)
    (hboundary : U.holeBoundaryPoint i ∈ W.carrier)
    (f : U.AnalyticFunctions) (hf : f ∈ closure (U.rationalComponentSet (some i))) :
    ‖U.analyticRestriction W hWU f‖₊ = ‖f‖₊ := by
  apply le_antisymm (U.nnnorm_analyticRestriction_le W hWU f)
  rw [U.nnnorm_principal_closure_eq_boundary_value i f hf]
  have h := W.analyticValue_le_nnnorm (U.analyticRestriction W hWU f) ⟨U.holeBoundaryPoint i,hboundary⟩
  rw [U.analyticValue_analyticRestriction W hWU] at h
  exact h

/-- The ACTUAL original surviving boundary detects zero of the WHOLE principal component. -/
theorem principal_eq_zero_of_restriction_eq_zero (i : Fin m)
    (hboundary : U.holeBoundaryPoint i ∈ W.carrier)
    (f : U.AnalyticFunctions) (hf : f ∈ closure (U.rationalComponentSet (some i)))
    (hz : U.analyticRestriction W hWU f = 0) : f = 0 := by
  have h := U.nnnorm_restriction_principal_of_boundary_mem W hWU i hboundary f hf
  rw [hz,nnnorm_zero] at h
  exact nnnorm_eq_zero.mp h.symm
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
