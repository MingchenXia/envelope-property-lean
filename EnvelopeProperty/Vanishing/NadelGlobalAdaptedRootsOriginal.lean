import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsRelabel

/-! # Original geometry internally constructs the canonical whole rooted chart

The original section/SNC producer supplies the actual frames, coordinates and
unit equations. The whole quotient construction then proves every canonical
original root formula, rather than assuming any expected matching.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
open CanonicalGeometry NadelAuxiliaryMulticover NadelAdaptedChartMatching NadelMixedKummer
open NadelGlobalNormalization NadelGlobalNormalization.OriginalData CyclicSectionSNCUniformFramedCharts
variable {X : Scheme.{u}} (F : X.DivisorFamily) (n : ℕ) (L : F.ι → X.Modules) (m : F.ι → ℕ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶ tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
  (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)

/-- Actual original sections and joined SNC internally produce the whole raw
chart WITH every canonical original root formula. No root-matching certificate
or desired isomorphism is a geometric input. -/
theorem exists_rooted_raw_equiv_at_closed [IsIntegral X] {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (ideals F n L m σ hL hD)).IsSnc)
    {y : X} (hy : IsClosed ({y} : Set X)) :
    ∃ (U : X.affineOpens) (v : Fin n → Γ(X, U.1)), y ∈ U.1 ∧
      Etale (toAffineSpace f U.1 v) ∧
      ∃ (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (data F n L m σ))
        (c : {i : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (ideals F n L m σ hL hD)).ι //
          y ∈ ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (ideals F n L m σ hL hD)).component i).support} → Fin n),
        Function.Injective c ∧
        (∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (ideals F n L m σ hL hD)).component i.1).ideal U =
          Ideal.span {v (c i)}) ∧
        (∀ i, y ∉ ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (ideals F n L m σ hL hD)).component i).support →
          ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (ideals F n L m σ hL hD)).component i).comap U.1.ι = ⊤) ∧
        ∃ w : Fin (data F n L m σ).length → (Γ(X, U.1))ˣ,
          (∀ i, WholeChart.coefficients U (data F n L m σ) e i =
            (w i : Γ(X, U.1)) * uniformBranches y U v c (branchIndex F n L m σ hL hD i) *
              uniformBranches y U v c (auxiliaryIndex F n L m σ hL hD i)) ∧
          ∃ eRaw : WholeChart.Ring U (data F n L m σ) e ≃ₐ[Γ(X, U.1)]
            Ring (Joined.degree F n m) (rawCoefficients F n L m σ hL hD y U v c w),
            ∀ i, eRaw (NadelMixedKummer.root (OriginalChart.degree (data F n L m σ))
              (WholeChart.coefficients U (data F n L m σ) e) i) =
              NadelMixedKummer.root (Joined.degree F n m)
                (rawCoefficients F n L m σ hL hD y U v c w) (ordinal F n L m σ i) := by
  obtain ⟨U, v, hyU, het, e, c, hcinj, hcomp, habsent, w, hw⟩ :=
    exists_framed_coefficients_at_closed F n L m σ hL hD f hG hy
  exact ⟨U, v, hyU, het, e, c, hcinj, hcomp, habsent, w, hw,
    rawEquiv F n L m σ hL hD y U v c e w hw,
    rawEquiv_root F n L m σ hL hD y U v c e w hw⟩

end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
