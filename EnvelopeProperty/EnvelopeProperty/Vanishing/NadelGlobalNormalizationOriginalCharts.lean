import EnvelopeProperty.Vanishing.NadelGlobalNormalizationOriginalData
import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingWholeChart

/-! # The ORIGINAL global auxiliary sections PRODUCE their actual common SNC charts

The actual original finite raw list, all original branch ideals and original
joined SNC family internally supply every frame, coordinate and unit factor.
No coefficient matching or adapted-chart certificate is a hypothesis.
-/

open AlgebraicGeometry CategoryTheory Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalNormalization.OriginalData
open CanonicalGeometry NadelAuxiliaryMulticover NadelAdaptedChartMatching CyclicSectionSNCUniformFramedCharts
variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
  (L : F.ι → X.Modules) (m : F.ι → ℕ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶ tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
  (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)

/-- The SAME actual original global auxiliary sections and their original
joined-family SNC PRODUCE actual common line frames and every unit coefficient
identity on a genuine original etale chart at each original closed point. -/
theorem exists_framed_coefficients_at_closed {k : Type u} [Field k] [PerfectField k]
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
        ∃ w : Fin (data F n L m σ).length → (Γ(X, U.1))ˣ, ∀ i,
          WholeChart.coefficients U (data F n L m σ) e i =
            (w i : Γ(X, U.1)) * uniformBranches y U v c (branchIndex F n L m σ hL hD i) *
              uniformBranches y U v c (auxiliaryIndex F n L m σ hL hD i) := by
  exact exists_original_framed_coefficients_at_closed f n _ hG (data F n L m σ)
    (get_isInvertible F n L m σ hL) (branchIndex F n L m σ hL hD) (auxiliaryIndex F n L m σ hL hD)
    (get_joined_branch F n L m σ hL hD) hy

end EnvelopeProperty.Vanishing.NadelGlobalNormalization.OriginalData
