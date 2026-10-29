import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsOriginal
import EnvelopeProperty.Vanishing.NadelGlobalAdaptedModelAlgebra

/-! # Every canonical original row root has its actual whole ratio monomial

The actual original quotient relabelling is followed by the actual whole
common-branch map. Every non-distinguished unit-root factor remains present.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
open CanonicalGeometry NadelAuxiliaryMulticover NadelAdaptedChartMatching NadelMixedKummer
open NadelGlobalNormalization NadelGlobalAdaptedModel CyclicSectionSNCUniformFramedCharts

variable {X : Scheme.{u}} (F : X.DivisorFamily) (n : ℕ) (L : F.ι → X.Modules) (m : F.ι → ℕ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶ tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))

/-- The actual original raw-list position of the SAME original row/copy. -/
def rowPosition (i : F.ι) (j : Fin (n + 1)) : Fin (OriginalData.data F n L m σ).length :=
  (OriginalData.ordinal F n L m σ).symm (Joined.ordering F n (i, j))

/-- Every row position evaluates to the SAME original row/copy datum. -/
theorem position_rowPosition (i : F.ι) (j : Fin (n + 1)) :
    OriginalData.position F n L m σ (rowPosition F n L m σ i j) = (i, j) := by
  rw [rowPosition, OriginalData.position_ordinal_symm, Equiv.symm_apply_apply]

variable (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
  (y : X) (U : X.affineOpens) (v : Fin n → Γ(X, U.1))
  (c : {i : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).ι //
    y ∈ ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).component i).support} → Fin n)
  (j₀ : F.ι → Fin (n + 1))
  (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
  (w : Fin (OriginalData.data F n L m σ).length → (Γ(X, U.1))ˣ)
  (hw : ∀ i, WholeChart.coefficients U (OriginalData.data F n L m σ) e i =
    (w i : Γ(X, U.1)) * uniformBranches y U v c (OriginalData.branchIndex F n L m σ hL hD i) *
      uniformBranches y U v c (OriginalData.auxiliaryIndex F n L m σ hL hD i))
  (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support)

/-- The actual WHOLE branch-product to ratio map, with all original factors. -/
def ratioMap :
    Ring (Joined.degree F n m) (OriginalData.rawCoefficients F n L m σ hL hD y U v c w) →ₐ[Γ(X, U.1)]
      RatioRing F n L m σ hL hD y U v c j₀ w :=
  MultiRatio.rawAlgHom (Joined.degree F n m)
    (OriginalData.rawCoefficients F n L m σ hL hD y U v c w)
    (ratioCoefficients F n L m σ hL hD y U v c j₀ w) (Joined.head F n j₀)
    (Joined.degree_head F n j₀ m)
    (BranchRatios.coefficient_head _ _ _ _ (Joined.head_head F n j₀)
      (Joined.auxiliaryGenerator_head F n (OriginalData.ideals F n L m σ hL hD) j₀ y U v c habsent))
    (BranchRatios.raw_mul_ratio _ _ _ _
      (Joined.branchGenerator_head F n (OriginalData.ideals F n L m σ hL hD) j₀ y U v c)
      (Joined.auxiliaryGenerator_head F n (OriginalData.ideals F n L m σ hL hD) j₀ y U v c habsent))

/-- The actual whole map from the SAME original raw chart to its ratio model,
using the CONSTRUCTED canonical original-root ordering. -/
def originalToRatio : WholeChart.Ring U (OriginalData.data F n L m σ) e →ₐ[Γ(X, U.1)]
    RatioRing F n L m σ hL hD y U v c j₀ w :=
  (ratioMap F n L m σ hL hD y U v c j₀ w habsent).comp
    (rawEquiv F n L m σ hL hD y U v c e w hw).toAlgHom

/-- EVERY original raw root has its actual whole monomial value. -/
theorem originalToRatio_root (i : Fin (OriginalData.data F n L m σ).length) :
    originalToRatio F n L m σ hL hD y U v c j₀ e w hw habsent
      (root (OriginalChart.degree (OriginalData.data F n L m σ))
        (WholeChart.coefficients U (OriginalData.data F n L m σ) e) i) =
      MultiRatio.forwardRoots (Joined.degree F n m)
        (ratioCoefficients F n L m σ hL hD y U v c j₀ w) (Joined.head F n j₀)
        (OriginalData.ordinal F n L m σ i) := by
  change ratioMap F n L m σ hL hD y U v c j₀ w habsent
    (rawEquiv F n L m σ hL hD y U v c e w hw _) = _
  rw [rawEquiv_root]
  exact MultiRatio.rawToRatio_root (Joined.degree F n m)
    (OriginalData.rawCoefficients F n L m σ hL hD y U v c w)
    (ratioCoefficients F n L m σ hL hD y U v c j₀ w) (Joined.head F n j₀)
    (Joined.degree_head F n j₀ m)
    (BranchRatios.coefficient_head _ _ _ _ (Joined.head_head F n j₀)
      (Joined.auxiliaryGenerator_head F n (OriginalData.ideals F n L m σ hL hD) j₀ y U v c habsent))
    (BranchRatios.raw_mul_ratio _ _ _ _
      (Joined.branchGenerator_head F n (OriginalData.ideals F n L m σ hL hD) j₀ y U v c)
      (Joined.auxiliaryGenerator_head F n (OriginalData.ideals F n L m σ hL hD) j₀ y U v c habsent))
    (OriginalData.ordinal F n L m σ i)

/-- The distinguished SAME original row root maps to its actual branch root. -/
theorem originalToRatio_head_root (i : F.ι) :
    originalToRatio F n L m σ hL hD y U v c j₀ e w hw habsent
      (root (OriginalChart.degree (OriginalData.data F n L m σ))
        (WholeChart.coefficients U (OriginalData.data F n L m σ) e)
        (rowPosition F n L m σ i (j₀ i))) =
      root (Joined.degree F n m) (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
        (Joined.ordering F n (i, j₀ i)) := by
  rw [originalToRatio_root]
  simp only [rowPosition, Equiv.apply_symm_apply, MultiRatio.forwardRoots, Joined.head,
    Joined.row, Equiv.symm_apply_apply, ↓reduceIte]

/-- EVERY other SAME original row root is the branch root times its ENTIRE
actual ratio root; no root value or disconnected unit factor is selected. -/
theorem originalToRatio_other_root (i : F.ι) (j : Fin (n + 1)) (hj : j ≠ j₀ i) :
    originalToRatio F n L m σ hL hD y U v c j₀ e w hw habsent
      (root (OriginalChart.degree (OriginalData.data F n L m σ))
        (WholeChart.coefficients U (OriginalData.data F n L m σ) e)
        (rowPosition F n L m σ i j)) =
      root (Joined.degree F n m) (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
        (Joined.ordering F n (i, j₀ i)) *
      root (Joined.degree F n m) (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
        (Joined.ordering F n (i, j)) := by
  rw [originalToRatio_root]
  have hne : Joined.ordering F n (i, j) ≠ Joined.ordering F n (i, j₀ i) := by
    intro h
    exact hj (congrArg Prod.snd ((Joined.ordering F n).injective h))
  simp only [rowPosition, Equiv.apply_symm_apply, MultiRatio.forwardRoots, Joined.head,
    Joined.row, Equiv.symm_apply_apply, if_neg hne]

end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
