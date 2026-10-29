import EnvelopeProperty.Vanishing.NadelBoundedCanonicalPushforward
import EnvelopeProperty.Vanishing.NadelBoundedCanonicalDegreeScalar

/-! # The canonical trace on every normalized adapted cover

Let `g : Y → Spec k` be smooth of relative dimension `n`, with `Y` integral. An
adapted SNC datum `(F, L, σ)` with common root degree `a.den` determines the
normalized adapted Kummer cover `π : Y' → Y` (`normalizedToOriginal`). The
canonical trace of such a cover is a morphism `T : π_* ω_{Y'} ⟶ ω_Y` whose
composite with the unit and the pushed-forward differential
`ω_Y → π_* π^* ω_Y → π_* ω_{Y'}` is multiplication by the degree of the cover
(the cyclic covers of Esnault–Viehweg, *Lectures on vanishing theorems*, §3).

This file only states the proposition `CoverCanonicalTraceInput k`, the
existence of such a trace on every adapted cover. It is the single remaining
input of the relative Nadel assembly
(`RelativeNadelAssembly.relativeAmpleNadelVanishingInput_of_coverTrace`).
No instance or proof of it is declared here.

The statement is local and contains no cohomology. It uses neither properness
nor projectivity of `Y`.
-/

open AlgebraicGeometry CategoryTheory Scheme.Modules
noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.RelativeNadelAssembly
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization

set_option autoImplicit false

/-- **Canonical trace on every normalized adapted cover.** For every smooth
integral `Y/k` of relative dimension `n` and every adapted SNC datum
`(F, L, σ)` of common root degree `a.den` with SNC auxiliary family and
generating rows, the normalized adapted cover `π` carries a morphism
`T : π_* ω_{Y'} ⟶ ω_Y` with `unit ≫ π_*(dπ) ≫ T = deg π • 𝟙`.

This is the only hypothesis of the relative Nadel assembly. Mathematically `T`
is the trace of differential forms along the finite flat cover `π` of smooth
`k`-schemes: the field trace of the generically étale extension of function
fields maps regular forms to regular forms, which is checked on the local
Kummer charts of the adapted cover. -/
def CoverCanonicalTraceInput (k : Type u) [Field k] : Prop :=
  ∀ {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n g]
    (F : Y.DivisorFamily) (a : ℚ) (L : F.ι → Y.Modules) (hL : ∀ i, IsInvertible (L i))
    (hD : ∀ i, (F.component i).IsInvertible)
    (σ : ∀ i, Fin (n + 1) → (unitObj Y ⟶
      Scheme.Modules.tensorObj (bundleTensorPower (L i) a.den) (F.component i).toModules)),
    (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L (fun _ => a.den) σ hL hD)).IsSnc →
    (∀ i, (⨆ j, OriginalData.ideals F n L (fun _ => a.den) σ hL hD i j) = ⊤) →
    let π := normalizedToOriginal (OriginalData.data F n L (fun _ => a.den) σ)
    ∃ T : (pushforward π).obj (canonicalLineSheaf (π ≫ g) n) ⟶ canonicalLineSheaf g n,
      (pullbackPushforwardAdjunction π).unit.app (canonicalLineSheaf g n) ≫
        (pushforward π).map (exteriorCotangentSheafPullbackMap g π n) ≫ T =
          NadelWholeCoverDegree.degree
            (NadelAdaptedChartMatching.Joined.degree F n (fun _ => a.den)) •
              𝟙 (canonicalLineSheaf g n)

end EnvelopeProperty.Vanishing.RelativeNadelAssembly
