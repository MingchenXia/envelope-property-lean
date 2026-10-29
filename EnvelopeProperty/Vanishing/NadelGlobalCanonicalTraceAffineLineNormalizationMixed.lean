import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationDifferential
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedSheafCandidate
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationPullback

/-!
# The normalization criterion on a mixed Kummer chart

Let `A` be a `k`-algebra with étale coordinates `x`, `B = mixedRing x N I σ u` the mixed Kummer
algebra and `β : Spec B → Spec A`.  If the mixed sheaf candidate
`T = mixedCanonicalSheafCandidate : β_* Ω^n_B ⟶ Ω^n_A` sends every section `b · φ^* w` to
`Tr_{B/A}(b) · w`, then `T ∘ β_*(dβ)` is the affine pulled-line trace of `Ω^n_A`
(Esnault–Viehweg, *Lectures on vanishing theorems*, §3).

This is the abstract criterion `affinePushforward_comp_eq_of_values` instantiated on the chart.
The morphisms `β_*(dβ)`, `T` and the pulled-line trace are read off the goal by unification, so
that the kernel only compares structurally identical terms; the side conditions are closed by
the value lemmas `affineAlgebraCanonicalDifferential_unitTop` and
`affinePulledLineTrace_trace_value`.  The hypothesis `hnative` is the value statement of the
candidate (the consequence of the normalization `mixedCanonicalCandidate_native` of the
module-level candidate); it is not proved here.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules
open NadelCanonicalMixed
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k A : Type u} [Field k] [CharZero k] [CommRing A] [Algebra k A] [Nontrivial A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

local notation "Bₘ" => mixedRing x N I σ u
local notation "φ" => CommRingCat.ofHom (algebraMap A Bₘ)
local notation "β" => Spec.map φ
local notation "ωA" => exteriorCotangentSheaf (affineStructuralMap k (CommRingCat.of A)) n
local notation "ωB" => exteriorCotangentSheaf (mixedStructure (k := k) x N I σ u) n

/-- If the mixed sheaf candidate sends `b · φ^* w` to `Tr_{B/A}(b) · w` on top sections, then the
pushed affine canonical differential followed by the candidate is the affine pulled-line trace
of `Ω^n_A`. -/
theorem mixedCanonicalSheafCandidate_differential_of_native
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (hnative : ∀ (b : Bₘ) (w : (moduleSpecΓFunctor (R := CommRingCat.of A)).obj ωA),
      (mixedCanonicalSheafCandidate x N I σ u hx hN htame).app ⊤
        (affinePushforwardRawSection φ ωB
          (ModuleSpecGammaCarrier.toRaw (.of Bₘ) ωB
            (b • (show mixedCanonicalModule (k := k) x N I σ u from
              mixedNativeCanonicalPullback (k := k) x N I σ u hx w)))) =
        ModuleSpecGammaCarrier.toRaw (.of A) ωA (Algebra.trace A Bₘ b • w)) :
    letI : Module.Free A Bₘ :=
      NadelAdaptedChartMatching.VaryingFinite.free N (NadelMixedKummer.mixedCoefficient x I σ u) hN
    letI : Module.Finite A Bₘ :=
      NadelAdaptedChartMatching.VaryingFinite.finite N
          (NadelMixedKummer.mixedCoefficient x I σ u) hN
    letI : SmoothOfRelativeDimension n (affineStructuralMap k (.of A)) :=
      coordinateStructure_smooth x hx
    (pushforward β).map
        (affineAlgebraCanonicalDifferential k (.of A) (.of Bₘ)
          (IsScalarTower.toAlgHom k A Bₘ) n) ≫
      mixedCanonicalSheafCandidate x N I σ u hx hN htame =
    affinePulledLineTrace (.of A) (.of Bₘ) ωA
      (canonicalLineSheaf_isInvertible (affineStructuralMap k (.of A)) n) := by
  let : Module.Free A Bₘ :=
    NadelAdaptedChartMatching.VaryingFinite.free N (NadelMixedKummer.mixedCoefficient x I σ u) hN
  let : Module.Finite A Bₘ :=
    NadelAdaptedChartMatching.VaryingFinite.finite N (NadelMixedKummer.mixedCoefficient x I σ u) hN
  let : SmoothOfRelativeDimension n (affineStructuralMap k (.of A)) :=
    coordinateStructure_smooth x hx
  have : (ωA).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible (affineStructuralMap k (.of A)) n).isQuasicoherent
  refine affinePushforward_comp_eq_of_values _ _ _ _
    (fun w => (show mixedCanonicalModule (k := k) x N I σ u from
      mixedNativeCanonicalPullback (k := k) x N I σ u hx w))
    (Algebra.trace A Bₘ) ?_ hnative ?_
  · intro w
    exact affineAlgebraCanonicalDifferential_unitTop _ _ _ _ w
  · intro r m
    exact affinePulledLineTrace_trace_value _ _ _ _ r m

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
