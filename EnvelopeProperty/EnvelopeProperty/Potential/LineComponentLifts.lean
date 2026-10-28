import EnvelopeProperty.Potential.LineInverseRestrictions

/-! # Actual completed component lifts with retained original boundary data -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] {m n : ℕ}
variable (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)
variable (W : FCStandardAffinoid (NormedField.valuation (K := K)) n)
variable (hWU : W.carrier ⊆ U.carrier)

omit [IsAlgClosed K] in
private theorem polynomial_nnnorm_gauss (p : K[X]) :
    ‖U.polynomialAnalyticMap p‖₊ = gaussFun (NormedField.valuation (K := K)) U.radius
      (Polynomial.algEquivAevalXAddC U.center p) := by
  have h := U.nnnorm_outerTranslatedPolynomial (Polynomial.algEquivAevalXAddC U.center p)
  rwa [← Polynomial.algEquivAevalXAddC_symm U.center,AlgEquiv.symm_apply_apply] at h

/-- Actual restriction preserves the exact norm on the WHOLE original polynomial closure, including radius zero. -/
theorem nnnorm_restriction_polynomial_closure (hc : U.center = W.center) (hr : U.radius = W.radius)
    (f : U.AnalyticFunctions) (hf : f ∈ closure (U.rationalComponentSet none)) :
    ‖U.analyticRestriction W hWU f‖₊ = ‖f‖₊ := by
  apply closure_minimal (t := {g | ‖U.analyticRestriction W hWU g‖₊ = ‖g‖₊}) _
    (isClosed_eq (continuous_nnnorm.comp (U.continuous_analyticRestriction W hWU)) continuous_nnnorm) hf
  rintro g ⟨p,rfl⟩
  change ‖U.analyticRestriction W hWU (U.polynomialAnalyticMap p)‖₊ = ‖U.polynomialAnalyticMap p‖₊
  rw [U.analyticRestriction_polynomial W hWU,polynomial_nnnorm_gauss,polynomial_nnnorm_gauss,hc,hr]

/-- Actual restriction preserves the exact norm on a WHOLE retained ORIGINAL principal closure. -/
theorem nnnorm_restriction_principal_closure (i : Fin m) (j : Fin n)
    (hc : U.holeCenter i = W.holeCenter j) (hr : U.holeRadius i = W.holeRadius j)
    (f : U.AnalyticFunctions) (hf : f ∈ closure (U.rationalComponentSet (some i))) :
    ‖U.analyticRestriction W hWU f‖₊ = ‖f‖₊ := by
  apply closure_minimal (t := {g | ‖U.analyticRestriction W hWU g‖₊ = ‖g‖₊}) _
    (isClosed_eq (continuous_nnnorm.comp (U.continuous_analyticRestriction W hWU)) continuous_nnnorm) hf
  rintro g ⟨p,k,hp,rfl⟩
  change ‖U.analyticRestriction W hWU (U.rationalMap (U.properRationalPart p i k))‖₊ =
    ‖U.rationalMap (U.properRationalPart p i k)‖₊
  rw [U.analyticRestriction_properRationalPart W hWU i j hc,
    U.properRationalPart_eq_inversePolynomial p i k hp,
    W.properRationalPart_eq_inversePolynomial p j k hp,
    U.nnnorm_inverseRationalPolynomial,W.nnnorm_inverseRationalPolynomial,hr]

private theorem closed_component_restriction_range (i : Option (Fin m))
    (hn : ∀ f ∈ closure (U.rationalComponentSet i),
      ‖U.analyticRestriction W hWU f‖₊ = ‖f‖₊) :
    IsClosed (U.analyticRestriction W hWU '' closure (U.rationalComponentSet i)) := by
  let C := closure (U.rationalComponentSet i)
  have : IsClosed C := isClosed_closure
  let F : C → W.AnalyticFunctions := fun f => U.analyticRestriction W hWU f.1
  have hiso : Isometry F := by
    intro a b
    have hsub : a.1-b.1 ∈ C := by
      have ha : a.1 ∈ Set.range (U.analyticComponent i) := by
        rw [U.range_analyticComponent]
        exact a.2
      have hb : b.1 ∈ Set.range (U.analyticComponent i) := by
        rw [U.range_analyticComponent]
        exact b.2
      obtain ⟨a',ha⟩ := ha
      obtain ⟨b',hb⟩ := hb
      change a.1-b.1 ∈ closure (U.rationalComponentSet i)
      rw [← U.range_analyticComponent]
      exact ⟨a'-b',by rw [map_sub,ha,hb]⟩
    have h : ‖U.analyticRestriction W hWU (a.1-b.1)‖ = ‖a.1-b.1‖ :=
      congrArg NNReal.toReal (hn (a.1-b.1) hsub)
    change edist (U.analyticRestriction W hWU a.1) (U.analyticRestriction W hWU b.1) = edist a.1 b.1
    rw [edist_dist,edist_dist,dist_eq_norm,dist_eq_norm,← map_sub,h]
  have he : Set.range F = U.analyticRestriction W hWU '' C := by
    ext g
    constructor
    · rintro ⟨f,rfl⟩
      exact ⟨f.1,f.2,rfl⟩
    · rintro ⟨f,hf,rfl⟩
      exact ⟨⟨f,hf⟩,rfl⟩
  rw [← he]
  exact hiso.isClosedEmbedding.isClosed_range

/-- EVERY actual polynomial component on the target has a WHOLE exact-norm source lift, including radius zero. -/
theorem exists_polynomial_component_lift (hc : U.center = W.center) (hr : U.radius = W.radius)
    (f : W.AnalyticFunctions) :
    ∃ g : U.AnalyticFunctions, g ∈ closure (U.rationalComponentSet none) ∧
      U.analyticRestriction W hWU g = W.analyticComponent none f ∧
      ‖g‖₊ = ‖W.analyticComponent none f‖₊ := by
  have hclosed := U.closed_component_restriction_range W hWU none
    (fun g hg => U.nnnorm_restriction_polynomial_closure W hWU hc hr g hg)
  have hsub : W.rationalComponentSet none ⊆
      U.analyticRestriction W hWU '' closure (U.rationalComponentSet none) := by
    rintro g ⟨p,rfl⟩
    exact ⟨U.polynomialAnalyticMap p,subset_closure ⟨p,rfl⟩,U.analyticRestriction_polynomial W hWU p⟩
  obtain ⟨g,hg,he⟩ := closure_minimal hsub hclosed (W.analyticComponent_mem_closure none f)
  refine ⟨g,hg,he,?_⟩
  exact (U.nnnorm_restriction_polynomial_closure W hWU hc hr g hg).symm.trans (congrArg nnnorm he)

/-- EVERY actual retained principal component has a WHOLE exact-norm lift in its ORIGINAL source component. -/
theorem exists_principal_component_lift (i : Fin m) (j : Fin n)
    (hc : U.holeCenter i = W.holeCenter j) (hr : U.holeRadius i = W.holeRadius j)
    (f : W.AnalyticFunctions) :
    ∃ g : U.AnalyticFunctions, g ∈ closure (U.rationalComponentSet (some i)) ∧
      U.analyticRestriction W hWU g = W.analyticComponent (some j) f ∧
      ‖g‖₊ = ‖W.analyticComponent (some j) f‖₊ := by
  have hclosed := U.closed_component_restriction_range W hWU (some i)
    (fun g hg => U.nnnorm_restriction_principal_closure W hWU i j hc hr g hg)
  have hsub : W.rationalComponentSet (some j) ⊆
      U.analyticRestriction W hWU '' closure (U.rationalComponentSet (some i)) := by
    rintro g ⟨p,k,hp,rfl⟩
    exact ⟨U.rationalMap (U.properRationalPart p i k),subset_closure ⟨p,k,hp,rfl⟩,
      U.analyticRestriction_properRationalPart W hWU i j hc p k⟩
  obtain ⟨g,hg,he⟩ := closure_minimal hsub hclosed (W.analyticComponent_mem_closure (some j) f)
  refine ⟨g,hg,he,?_⟩
  exact (U.nnnorm_restriction_principal_closure W hWU i j hc hr g hg).symm.trans (congrArg nnnorm he)
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
