import EnvelopeProperty.Potential.LinePrincipalComponent

/-! # Whole actual original inverse-coordinate restriction identities -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] {m n : ℕ}
variable (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)
variable (V : FCStandardAffinoid (NormedField.valuation (K := K)) n)
variable (hVU : V.carrier ⊆ U.carrier)

/-- The genuine rational map retains the ORIGINAL coefficient algebra. -/
def rationalMapAlgHom : U.RationalFunctions →ₐ[K] U.AnalyticFunctions where
  __ := U.rationalMap
  commutes' := U.rationalMap_original_coefficient

theorem analyticRestriction_holeInverse (j : Fin m) (k : Fin n) (hc : U.holeCenter j = V.holeCenter k) :
    U.analyticRestriction V hVU (U.rationalMap (U.rationalHoleInverse j)) =
      V.rationalMap (V.rationalHoleInverse k) := by
  have hU := congrArg (U.analyticRestriction V hVU)
    (congrArg U.rationalMap (U.holeCoordinate_mul_rationalHoleInverse j))
  simp only [map_mul,map_one] at hU
  change U.analyticRestriction V hVU (U.polynomialAnalyticMap (X-C (U.holeCenter j)))*
    U.analyticRestriction V hVU (U.rationalMap (U.rationalHoleInverse j)) = 1 at hU
  rw [U.analyticRestriction_polynomial V hVU] at hU
  have hV := congrArg V.rationalMap (V.holeCoordinate_mul_rationalHoleInverse k)
  simp only [map_mul,map_one] at hV
  change V.polynomialAnalyticMap (X-C (V.holeCenter k))*V.rationalMap (V.rationalHoleInverse k) = 1 at hV
  have hpoly : X-C (V.holeCenter k) = X-C (U.holeCenter j) := congrArg (fun a : K => X-C a) hc.symm
  rw [hpoly] at hV
  calc
    U.analyticRestriction V hVU (U.rationalMap (U.rationalHoleInverse j)) =
      U.analyticRestriction V hVU (U.rationalMap (U.rationalHoleInverse j))*
        (V.polynomialAnalyticMap (X-C (U.holeCenter j))*V.rationalMap (V.rationalHoleInverse k)) := by
      rw [hV,mul_one]
    _ = (V.polynomialAnalyticMap (X-C (U.holeCenter j))*
      U.analyticRestriction V hVU (U.rationalMap (U.rationalHoleInverse j)))*
        V.rationalMap (V.rationalHoleInverse k) := by ring
    _ = _ := by rw [hU,one_mul]

theorem analyticRestriction_inversePolynomial (j : Fin m) (k : Fin n)
    (hc : U.holeCenter j = V.holeCenter k) (p : K[X]) :
    U.analyticRestriction V hVU (U.rationalMap (U.inverseRationalPolynomial j p)) =
      V.rationalMap (V.inverseRationalPolynomial k p) := by
  have he : (U.analyticRestrictionAlgHom V hVU).comp
      (U.rationalMapAlgHom.comp (U.inverseRationalPolynomial j)) =
        V.rationalMapAlgHom.comp (V.inverseRationalPolynomial k) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply,inverseRationalPolynomial,Polynomial.aeval_X]
    exact U.analyticRestriction_holeInverse V hVU j k hc
  exact congrArg (fun g : K[X] →ₐ[K] V.AnalyticFunctions => g p) he

theorem analyticRestriction_properRationalPart (j : Fin m) (k : Fin n)
    (hc : U.holeCenter j = V.holeCenter k) (p : K[X]) (q : ℕ) :
    U.analyticRestriction V hVU (U.rationalMap (U.properRationalPart p j q)) =
      V.rationalMap (V.properRationalPart p k q) := by
  simp only [properRationalPart,map_mul,map_pow]
  change U.analyticRestriction V hVU
    (U.polynomialAnalyticMap (Polynomial.algEquivAevalXAddC (-U.holeCenter j) p))*
      (U.analyticRestriction V hVU (U.rationalMap (U.rationalHoleInverse j)))^q =
        V.polynomialAnalyticMap (Polynomial.algEquivAevalXAddC (-V.holeCenter k) p)*
          (V.rationalMap (V.rationalHoleInverse k))^q
  rw [U.analyticRestriction_polynomial V hVU,U.analyticRestriction_holeInverse V hVU j k hc,hc]

/-- Actual restriction transports the closure of ORIGINAL polynomial functions to the corresponding actual closure. -/
theorem analyticRestriction_polynomial_closure (f : U.AnalyticFunctions)
    (hf : f ∈ closure (U.rationalComponentSet none)) :
    U.analyticRestriction V hVU f ∈ closure (V.rationalComponentSet none) := by
  apply closure_mono _ (mem_closure_image (U.continuous_analyticRestriction V hVU).continuousAt hf)
  rintro g ⟨a,ha,rfl⟩
  rcases ha with ⟨p,rfl⟩
  rw [U.analyticRestriction_polynomial V hVU]
  exact ⟨p,rfl⟩

/-- Actual whole proper-fraction closures restrict using only actual containment and the original center equality. -/
theorem analyticRestriction_principal_closure (j : Fin m) (k : Fin n)
    (hc : U.holeCenter j = V.holeCenter k) (f : U.AnalyticFunctions)
    (hf : f ∈ closure (U.rationalComponentSet (some j))) :
    U.analyticRestriction V hVU f ∈ closure (V.rationalComponentSet (some k)) := by
  apply closure_mono _ (mem_closure_image (U.continuous_analyticRestriction V hVU).continuousAt hf)
  rintro g ⟨a,ha,rfl⟩
  rcases ha with ⟨p,q,hp,rfl⟩
  rw [U.analyticRestriction_properRationalPart V hVU j k hc]
  exact ⟨p,q,hp,rfl⟩
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
