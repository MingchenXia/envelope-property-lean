import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceOriginalPointNormalization
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceChartOriginalCancellation
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRegularPulledLineRestriction
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRationalCapturedCompatibility

/-!
# The point candidates factor the rational canonical trace

Let `π : Y' → X` be the normalized adapted Kummer cover, `γ : Spec K(X) → X` the generic point,
`ι : ω_X ↪ γ_* γ^* ω_X` the generic inclusion (`genericCanonicalInclusion`) and
`Tr_rat : π_* ω_{Y'} ⟶ γ_* γ^* ω_X` the rational canonical trace (`genericRationalCanonicalTrace`:
the inverse of the generically invertible differential followed by the field trace of
`K(Y')/K(X)`).

Main result, `producedOriginalCanonicalCandidate_regularFactor`: under
`MixedCanonicalCandidateNormalization k`, at every point `x` the point candidate `θ_x` on the
chart base `U ∋ x` is a regular factor of the rational trace:
`θ_x ≫ ι|_U = (Tr_rat)|_U`.

Proof. Restricted to `U`, the pushed differential `(π_* dπ)|_U` is cancellable on the left for
maps into restrictions of `γ_*` (`wholeFreeChart_restrictedOriginalDifferential_hom_ext`: `dπ`
is an isomorphism on a dense étale open of the chart, and `γ_*`-valued maps are determined
there). After precomposition with `(π_* dπ)|_U` both sides agree:
`(π_* dπ)|_U ≫ θ_x ≫ ι|_U = (T_π ≫ ι)|_U = (π_* dπ ≫ Tr_rat)|_U`, by the point normalization,
the rational restriction of the pulled-line trace
(`regularPulledCanonicalTrace_rational_restriction`) and the rational compatibility of the
differential (`differential_comp_genericRationalCanonicalTrace_captured`). The equation holds on
the whole chart, including its branch locus.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules CanonicalGeometry
open NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedModel
open NadelGlobalStructureTrace
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- In an arbitrary category: if `r(D) ≫ θ = r(R)`, `R ≫ ι = Q` and `D ≫ ρ = Q`, then
`r(D) ≫ (θ ≫ r(ι)) = r(D) ≫ r(ρ)`. -/
private theorem regular_factor_assembly {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    (r : C₁ ⥤ C₂) {P M I G : C₁} (D : P ⟶ M) (R : P ⟶ I) (ι : I ⟶ G) (ρ : M ⟶ G)
    (Q : P ⟶ G) (θ : r.obj M ⟶ r.obj I)
    (hdiff : r.map D ≫ θ = r.map R) (hrat : R ≫ ι = Q) (hcomp : D ≫ ρ = Q) :
    r.map D ≫ (θ ≫ r.map ι) = r.map D ≫ r.map ρ := by
  rw [← Category.assoc, hdiff, ← r.map_comp, ← r.map_comp, hrat, hcomp]

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
    {k : Type u} [Field k] [PerfectField k] [CharZero k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))
    (hmix : MixedCanonicalCandidateNormalization k)

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)
local notation "γ" => X.fromSpecStalk (genericPoint X)
local notation "ωX" => canonicalLineSheaf f n
local notation "𝒞" x:max => producedCanonicalCandidateChart F n L m σ hL hD f hG hRows hm hfield x

include hL hD f hG hRows hm hfield hmix

/-- **Regular local factor.** Under the normalization of the mixed candidate, the point
candidate at `x` is a regular factor, on the chart base `U ∋ x`, of the rational canonical
trace: `θ_x ≫ ι|_U = (Tr_rat)|_U`. -/
theorem producedOriginalCanonicalCandidate_regularFactor (x : X) :
    producedOriginalCanonicalCandidate F n L m σ hL hD f hG hRows hm hfield x ≫
        (restrictFunctor (𝒞 x).base.2.fromSpec).map (genericCanonicalInclusion f n) =
      (restrictFunctor (𝒞 x).base.2.fromSpec).map
        (genericRationalCanonicalTrace F n L m σ hL hD f hG hRows hm hfield) := by
  have : Nonempty (𝒞 x).base.1 :=
    ⟨⟨x, mem_producedCanonicalCandidateChart F n L m σ hL hD f hG hRows hm hfield x⟩⟩
  apply wholeFreeChart_restrictedOriginalDifferential_hom_ext
    F n L m σ hL hD f hG hRows hm hfield (𝒞 x) ((pullback γ).obj ωX)
  exact regular_factor_assembly _ _ _ _ _ _ _
    (producedOriginalCanonicalCandidate_differential F n L m σ hL hD f hG hRows hm hfield hmix x)
    (regularPulledCanonicalTrace_rational_restriction F n L m σ hL hD f hG hRows hm hfield)
    (differential_comp_genericRationalCanonicalTrace_captured
      F n L m σ hL hD f hG hRows hm hfield)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
