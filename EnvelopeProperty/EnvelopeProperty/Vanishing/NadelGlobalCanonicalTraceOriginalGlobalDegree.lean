import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceOriginalGlobal
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRegularPulledLineDegree

/-!
# The degree identity of the canonical trace

Let `π : Y' → X` be the normalized adapted Kummer cover, of degree `D`
(`NadelWholeCoverDegree.degree (Joined.degree F n m)`), and `T : π_* ω_{Y'} ⟶ ω_X` its canonical
trace (`originalCanonicalTrace`). Under `MixedCanonicalCandidateNormalization k`:

* `differential_comp_originalCanonicalTrace`: `π_*(dπ) ≫ T = T_π`, the regular pulled-line
  trace (the structure-sheaf trace of `π` tensored with `ω_X`). Both sides have the same
  composite with the generic monomorphism `ι : ω_X ↪ γ_* γ^* ω_X`.
* `unit_comp_originalCanonicalTrace`: `η ≫ π_*(dπ) ≫ T = D • 𝟙`, where `η : ω_X ⟶ π_* π^* ω_X`
  is the unit of `π^* ⊣ π_*`. This follows from the degree identity of the structure-sheaf
  trace (`unit_comp_regularPulledCanonicalTrace`).

This is the trace with `unit ≫ π_*(dπ) ≫ T = deg π • 𝟙` used by the cyclic covering trick
(Esnault–Viehweg, *Lectures on vanishing theorems*, §3; Kollár–Mori, Prop. 2.64): since `D` is
invertible in characteristic zero, `ω_X` is a direct summand of `π_* ω_{Y'}`.
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
local notation "ωX" => canonicalLineSheaf f n

include hL hD f hG hRows hm hfield hmix

/-- The pushed canonical differential followed by the canonical trace is the regular
pulled-line trace: `π_*(dπ) ≫ T = T_π`. -/
theorem differential_comp_originalCanonicalTrace :
    (pushforward π).map (exteriorCotangentSheafPullbackMap f π n) ≫
        originalCanonicalTrace F n L m σ hL hD f hG hRows hm hfield hmix =
      regularPulledCanonicalTrace F n L m σ hL hD f hG hRows hm hfield := by
  have : Mono (genericCanonicalInclusion f n) := genericCanonicalInclusion_mono f n
  refine (cancel_mono (genericCanonicalInclusion f n)).mp ?_
  rw [Category.assoc,
    originalCanonicalTrace_factor F n L m σ hL hD f hG hRows hm hfield hmix,
    regularPulledCanonicalTrace_rational_restriction F n L m σ hL hD f hG hRows hm hfield]
  exact differential_comp_genericRationalCanonicalTrace_captured
    F n L m σ hL hD f hG hRows hm hfield

/-- **Degree identity of the canonical trace.** The unit of `π^* ⊣ π_*`, the pushed canonical
differential and the canonical trace compose to the degree of the cover:
`η ≫ π_*(dπ) ≫ T = D • 𝟙_{ω_X}`. -/
theorem unit_comp_originalCanonicalTrace :
    (pullbackPushforwardAdjunction π).unit.app ωX ≫
      (pushforward π).map (exteriorCotangentSheafPullbackMap f π n) ≫
        originalCanonicalTrace F n L m σ hL hD f hG hRows hm hfield hmix =
      NadelWholeCoverDegree.degree (NadelAdaptedChartMatching.Joined.degree F n m) • 𝟙 ωX := by
  rw [differential_comp_originalCanonicalTrace F n L m σ hL hD f hG hRows hm hfield hmix]
  exact unit_comp_regularPulledCanonicalTrace F n L m σ hL hD f hG hRows hm hfield

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
