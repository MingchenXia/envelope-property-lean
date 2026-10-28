import EnvelopeProperty.Vanishing.RelativeNadelCoverTraceInput
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceOriginalGlobalDegree
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCounitNormalizationCandidate

/-!
# The canonical trace input of the relative Nadel assembly

`CoverCanonicalTraceInput k` asks for a trace `T : π_* ω_{Y'} ⟶ ω_Y` with
`η ≫ π_*(dπ) ≫ T = deg π • 𝟙` on every normalized adapted Kummer cover `π : Y' → Y` (of common
root degree `a.den`) of a smooth integral `k`-scheme `Y`. The canonical trace
`NadelGlobalCanonicalTrace.originalCanonicalTrace` and its degree identity
`unit_comp_originalCanonicalTrace` provide it, in characteristic zero (which makes `k` perfect
and the root degrees `a.den` invertible in `k`). This is the trace of the cyclic covering trick
(Esnault–Viehweg, *Lectures on vanishing theorems*, §3; Kollár–Mori, Prop. 2.64).

## Main results

* `coverCanonicalTraceInput_of_mixedCanonicalCandidateNormalization`:
  `MixedCanonicalCandidateNormalization k → CoverCanonicalTraceInput k` for every field `k` of
  characteristic zero. The hypothesis is the algebraic normalization `τ(b · β^* w) = Tr(b) · w`
  of the explicit mixed canonical candidate on the explicit mixed Kummer charts.
* `coverCanonicalTraceInput`: `CoverCanonicalTraceInput k` for every field `k` of
  characteristic zero, from the proved normalization `mixedCanonicalCandidate_native`
  (Euler's lemma on the purified Kummer charts).
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.RelativeNadelAssembly
open AlgebraicGeometry CategoryTheory Scheme.Modules
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
universe u
set_option autoImplicit false

/-- **The canonical trace on adapted covers, from the mixed normalization.** In characteristic
zero, the normalization of the mixed canonical candidate gives the canonical trace with the
degree identity on every normalized adapted cover. -/
theorem coverCanonicalTraceInput_of_mixedCanonicalCandidateNormalization
    {k : Type u} [Field k] [CharZero k]
    (hmix : NadelGlobalCanonicalTrace.MixedCanonicalCandidateNormalization k) :
    CoverCanonicalTraceInput k := by
  intro Y _ g n _ F a L hL hD σ hG hRows
  have hm : ∀ _ : F.ι, 0 < a.den := fun _ => a.den_pos
  have hfield : ∀ _ : F.ι, IsUnit (a.den : k) :=
    fun _ => isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr a.den_ne_zero)
  exact ⟨NadelGlobalCanonicalTrace.originalCanonicalTrace F n L (fun _ => a.den) σ hL hD g
      hG hRows hm hfield hmix,
    NadelGlobalCanonicalTrace.unit_comp_originalCanonicalTrace F n L (fun _ => a.den) σ hL hD g
      hG hRows hm hfield hmix⟩

/-- **The canonical trace on every normalized adapted cover** (characteristic zero). Every
normalized adapted Kummer cover `π : Y' → Y` of a smooth integral `k`-scheme carries a trace
`T : π_* ω_{Y'} ⟶ ω_Y` with `η ≫ π_*(dπ) ≫ T = deg π • 𝟙`: the canonical trace, whose
regularity on the mixed Kummer charts is `mixedCanonicalCandidate_native`. -/
theorem coverCanonicalTraceInput (k : Type u) [Field k] [CharZero k] :
    CoverCanonicalTraceInput k :=
  coverCanonicalTraceInput_of_mixedCanonicalCandidateNormalization
    fun x N I σ u hx hN htame b w =>
      NadelGlobalCanonicalTrace.mixedCanonicalCandidate_native (k := k) x N I σ u hx hN htame b w

end EnvelopeProperty.Vanishing.RelativeNadelAssembly
