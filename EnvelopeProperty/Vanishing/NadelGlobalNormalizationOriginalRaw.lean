import EnvelopeProperty.Vanishing.NadelGlobalNormalizationOriginalCharts
import EnvelopeProperty.Vanishing.NadelGlobalNormalizationRelabel
import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingJoinedNormalization

/-! # The actual original whole raw chart matches its SAME original branch-product algebra

Finite relabelling is constructed from the ORIGINAL list's original row/copy
ordering. Actual native section coefficients and original branch ideals produce
the comparison; no expected whole chart equivalence is an input.
-/

open AlgebraicGeometry CategoryTheory Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalNormalization.OriginalData
open CanonicalGeometry NadelAuxiliaryMulticover NadelAdaptedChartMatching NadelMixedKummer
open CyclicSectionSNCUniformFramedCharts
variable {X : Scheme.{u}} (F : X.DivisorFamily) (n : ℕ) (L : F.ι → X.Modules) (m : F.ι → ℕ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶ tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))

/-- The internally constructed bijection retains ALL original raw-list positions. -/
def ordinal : Fin (data F n L m σ).length ≃ Fin (Fintype.card (Joined.Index F n)) :=
  finCongr (length_data F n L m σ)

/-- The SAME actual original row/copy ordering, after the actual list-length cast. -/
theorem position_ordinal_symm (j : Fin (Fintype.card (Joined.Index F n))) :
    position F n L m σ ((ordinal F n L m σ).symm j) = (Joined.ordering F n).symm j := by
  simp [position, ordinal]

/-- Every original root degree retains its SAME original row degree in the whole ordering. -/
theorem degree_ordinal_symm (j : Fin (Fintype.card (Joined.Index F n))) :
    ((data F n L m σ).get ((ordinal F n L m σ).symm j)).degree = Joined.degree F n m j := by
  rw [get_degree, position_ordinal_symm]
  rfl

variable (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
  (y : X) (U : X.affineOpens) (v : Fin n → Γ(X, U.1))
  (c : {i : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (ideals F n L m σ hL hD)).ι //
    y ∈ ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (ideals F n L m σ hL hD)).component i).support} → Fin n)

/-- The SAME derived original frame units at every ordered original row/copy. -/
def orderedUnits (w : Fin (data F n L m σ).length → (Γ(X, U.1))ˣ)
    (j : Fin (Fintype.card (Joined.Index F n))) : (Γ(X, U.1))ˣ := w ((ordinal F n L m σ).symm j)

/-- The literal original branch-product coefficients, with EVERY original
row/copy generator and its SAME actual original frame unit. -/
def rawCoefficients (w : Fin (data F n L m σ).length → (Γ(X, U.1))ˣ) :
    Fin (Fintype.card (Joined.Index F n)) → Γ(X, U.1) :=
  BranchRatios.rawCoefficient (Joined.branchGenerator F n (ideals F n L m σ hL hD) y U v c)
    (Joined.auxiliaryGenerator F n (ideals F n L m σ hL hD) y U v c) (orderedUnits F n L m σ U w)

private theorem rawCoefficient_of_original
    (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (data F n L m σ))
    (w : Fin (data F n L m σ).length → (Γ(X, U.1))ˣ)
    (hw : ∀ i, WholeChart.coefficients U (data F n L m σ) e i =
      (w i : Γ(X, U.1)) * uniformBranches y U v c (branchIndex F n L m σ hL hD i) *
        uniformBranches y U v c (auxiliaryIndex F n L m σ hL hD i))
    (j : Fin (Fintype.card (Joined.Index F n))) :
    WholeChart.coefficients U (data F n L m σ) e ((ordinal F n L m σ).symm j) =
      rawCoefficients F n L m σ hL hD y U v c w j := by
  rw [hw]
  simp only [branchIndex, auxiliaryIndex, position_ordinal_symm]
  rfl

private def rawEquiv_of_original
    (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (data F n L m σ))
    (w : Fin (data F n L m σ).length → (Γ(X, U.1))ˣ)
    (hw : ∀ i, WholeChart.coefficients U (data F n L m σ) e i =
      (w i : Γ(X, U.1)) * uniformBranches y U v c (branchIndex F n L m σ hL hD i) *
        uniformBranches y U v c (auxiliaryIndex F n L m σ hL hD i)) :
    WholeChart.Ring U (data F n L m σ) e ≃ₐ[Γ(X, U.1)]
      Ring (Joined.degree F n m) (rawCoefficients F n L m σ hL hD y U v c w) := by
  have hN : (fun j => OriginalChart.degree (data F n L m σ) ((ordinal F n L m σ).symm j)) =
      Joined.degree F n m := funext (degree_ordinal_symm F n L m σ)
  have hC : (fun j => WholeChart.coefficients U (data F n L m σ) e ((ordinal F n L m σ).symm j)) =
      rawCoefficients F n L m σ hL hD y U v c w :=
    funext (rawCoefficient_of_original F n L m σ hL hD y U v c e w hw)
  have eraw := Relabel.algEquiv (OriginalChart.degree (data F n L m σ))
    (WholeChart.coefficients U (data F n L m σ) e) (ordinal F n L m σ)
  rw [hN, hC] at eraw
  exact eraw

/-- The SAME original global sections, branch ideals and joined SNC data
INTERNALLY PRODUCE the actual WHOLE raw chart equivalence. The expected
coefficient matching and whole algebra comparison are NOT hypotheses. -/
theorem exists_whole_raw_equiv_at_closed [IsIntegral X] {k : Type u} [Field k] [PerfectField k]
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
          Nonempty (WholeChart.Ring U (data F n L m σ) e ≃ₐ[Γ(X, U.1)]
            Ring (Joined.degree F n m) (rawCoefficients F n L m σ hL hD y U v c w)) := by
  obtain ⟨U, v, hyU, het, e, c, hcinj, hcomp, habsent, w, hw⟩ :=
    exists_framed_coefficients_at_closed F n L m σ hL hD f hG hy
  exact ⟨U, v, hyU, het, e, c, hcinj, hcomp, habsent, w, hw,
    ⟨rawEquiv_of_original F n L m σ hL hD y U v c e w hw⟩⟩

end EnvelopeProperty.Vanishing.NadelGlobalNormalization.OriginalData
