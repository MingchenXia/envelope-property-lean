import EnvelopeProperty.Vanishing.NadelGlobalNormalizationOriginalRaw

/-! # Canonical whole original root relabelling with every original generator

Equality transport retains the actual root formulas of the whole quotient
universal-property construction. The geometric producer obtains the actual
coefficient equations internally from the original sections and SNC chart.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
open CanonicalGeometry NadelAuxiliaryMulticover NadelAdaptedChartMatching NadelMixedKummer
open NadelGlobalNormalization CyclicSectionSNCUniformFramedCharts

namespace Relabel
variable {R : Type u} [CommRing R] {q r : ℕ}
  (N : Fin q → ℕ) (a : Fin q → R) (e : Fin q ≃ Fin r)
  (M : Fin r → ℕ) (b : Fin r → R)
  (hN : (fun j => N (e.symm j)) = M) (ha : (fun j => a (e.symm j)) = b)

/-- Actual whole root relabelling transported through proved data equalities. -/
def toData : Ring N a ≃ₐ[R] Ring M b := by
  subst M
  subst b
  exact NadelGlobalNormalization.Relabel.algEquiv N a e

/-- EVERY original root retains its actual original position. -/
theorem toData_root (i : Fin q) : toData N a e M b hN ha (root N a i) = root M b (e i) := by
  subst M
  subst b
  exact NadelGlobalNormalization.Relabel.algEquiv_root N a e i

end Relabel

variable {X : Scheme.{u}} (F : X.DivisorFamily) (n : ℕ) (L : F.ι → X.Modules) (m : F.ι → ℕ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶ tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
  (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
  (y : X) (U : X.affineOpens) (v : Fin n → Γ(X, U.1))
  (c : {i : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).ι //
    y ∈ ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).component i).support} → Fin n)
  (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
  (w : Fin (OriginalData.data F n L m σ).length → (Γ(X, U.1))ˣ)
  (hw : ∀ i, WholeChart.coefficients U (OriginalData.data F n L m σ) e i =
    (w i : Γ(X, U.1)) * uniformBranches y U v c (OriginalData.branchIndex F n L m σ hL hD i) *
      uniformBranches y U v c (OriginalData.auxiliaryIndex F n L m σ hL hD i))

include hw in
private theorem coefficients_ordered (j : Fin (Fintype.card (Joined.Index F n))) :
    WholeChart.coefficients U (OriginalData.data F n L m σ) e
      ((OriginalData.ordinal F n L m σ).symm j) =
      OriginalData.rawCoefficients F n L m σ hL hD y U v c w j := by
  rw [hw]
  simp only [OriginalData.branchIndex, OriginalData.auxiliaryIndex, OriginalData.position_ordinal_symm]
  rfl

/-- The canonical comparison is CONSTRUCTED from the actual original list,
its true ordering, and the derived section coefficient equations. -/
def rawEquiv : WholeChart.Ring U (OriginalData.data F n L m σ) e ≃ₐ[Γ(X, U.1)]
    Ring (Joined.degree F n m) (OriginalData.rawCoefficients F n L m σ hL hD y U v c w) :=
  Relabel.toData (OriginalChart.degree (OriginalData.data F n L m σ))
    (WholeChart.coefficients U (OriginalData.data F n L m σ) e) (OriginalData.ordinal F n L m σ)
    (Joined.degree F n m) (OriginalData.rawCoefficients F n L m σ hL hD y U v c w)
    (funext (OriginalData.degree_ordinal_symm F n L m σ))
    (funext (coefficients_ordered F n L m σ hL hD y U v c e w hw))

/-- Every SAME original raw root retains its canonical original row/copy index. -/
theorem rawEquiv_root (i : Fin (OriginalData.data F n L m σ).length) :
    rawEquiv F n L m σ hL hD y U v c e w hw
      (root (OriginalChart.degree (OriginalData.data F n L m σ))
        (WholeChart.coefficients U (OriginalData.data F n L m σ) e) i) =
      root (Joined.degree F n m) (OriginalData.rawCoefficients F n L m σ hL hD y U v c w)
        (OriginalData.ordinal F n L m σ i) :=
  Relabel.toData_root _ _ _ _ _ _ _ i

end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
