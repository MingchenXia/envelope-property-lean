import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingLabels
import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingMixed
import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingBranchRatios

/-! # Actual joined SNC coordinates match the WHOLE original ratio source

The same original D_i and EVERY original auxiliary H_ij supply the genuine
mixed coefficients. All row labels and all absent unit-root factors remain.
-/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.Joined
open NadelAuxiliaryBranchSectionsSnc CyclicSectionSNCUniformFramedCharts
variable {X : Scheme.{u}} (F : X.DivisorFamily) (n : ℕ)
  (A : F.ι → Fin (n + 1) → X.IdealSheafData) (j₀ : F.ι → Fin (n + 1))
  (y : X) (U : X.affineOpens) (v : Fin n → Γ(X, U.1))
  (c : {i : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).ι //
    y ∈ ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).component i).support} → Fin n)

/-- The SAME original branch generator at EVERY original row/copy position. -/
def branchGenerator (i : Fin (Fintype.card (Index F n))) : Γ(X, U.1) :=
  uniformBranches y U v c (originalIndex F n A (row F n i))

/-- The SAME original auxiliary generator at EVERY original row/copy position. -/
def auxiliaryGenerator (i : Fin (Fintype.card (Index F n))) : Γ(X, U.1) :=
  uniformBranches y U v c (auxiliaryIndex F n A (row F n i) (copy F n i))

/-- The actual whole head selection preserves each SAME original branch generator. -/
theorem branchGenerator_head (i : Fin (Fintype.card (Index F n))) :
    branchGenerator F n A y U v c (head F n j₀ i) = branchGenerator F n A y U v c i := by
  rw [branchGenerator, row_head]
  rfl

/-- The actual head retains the SAME distinguished original copy. -/
theorem copy_head (i : Fin (Fintype.card (Index F n))) :
    copy F n (head F n j₀ i) = j₀ (row F n i) := by
  simp only [copy, head, Equiv.symm_apply_apply]

/-- The whole quotient index is distinguished exactly when its SAME
original row/copy label is distinguished. -/
theorem head_iff_copy (i : Fin (Fintype.card (Index F n))) :
    i = head F n j₀ i ↔ copy F n i = j₀ (row F n i) := by
  constructor
  · intro hi
    exact (congrArg (copy F n) hi).trans (copy_head F n j₀ i)
  · intro hi
    apply (ordering F n).symm.injective
    change ((ordering F n).symm i) = (ordering F n).symm (ordering F n (row F n i, j₀ (row F n i)))
    rw [Equiv.symm_apply_apply]
    exact Prod.ext rfl hi

/-- Actual absence of the SAME original auxiliary divisor makes its head
generator literally 1, on the entire original affine chart. -/
theorem auxiliaryGenerator_head
    (habsent : ∀ i, y ∉ (A i (j₀ i)).support) (i : Fin (Fintype.card (Index F n))) :
    auxiliaryGenerator F n A y U v c (head F n j₀ i) = 1 := by
  rw [auxiliaryGenerator, row_head, copy_head]
  have hi : y ∉ ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).component
      (auxiliaryIndex F n A (row F n i) (j₀ (row F n i)))).support := by
    rw [component_auxiliaryIndex]
    exact habsent (row F n i)
  exact dif_neg hi

/-- The actual ratio generator is the SAME original joined-family generator
at the internally constructed injective original label. -/
theorem ratioGenerator_eq (i : Fin (Fintype.card (Index F n))) :
    BranchRatios.ratioGenerator (head F n j₀) (branchGenerator F n A y U v c)
      (auxiliaryGenerator F n A y U v c) i =
      uniformBranches y U v c (orderedLabel F n A j₀ i) := by
  classical
  by_cases hi : i = head F n j₀ i
  · have hcopy := (head_iff_copy F n j₀ i).mp hi
    change (if i = head F n j₀ i then _ else _) =
      uniformBranches y U v c (label F n A j₀ ((ordering F n).symm i))
    rw [if_pos hi]
    have hl : label F n A j₀ ((ordering F n).symm i) = originalIndex F n A (row F n i) := if_pos hcopy
    rw [hl]
    rfl
  · have hcopy : copy F n i ≠ j₀ (row F n i) := mt (head_iff_copy F n j₀ i).mpr hi
    change (if i = head F n j₀ i then _ else _) =
      uniformBranches y U v c (label F n A j₀ ((ordering F n).symm i))
    rw [if_neg hi]
    have hl : label F n A j₀ ((ordering F n).symm i) =
        auxiliaryIndex F n A (row F n i) (copy F n i) := if_neg hcopy
    rw [hl]
    rfl

/-- All actual whole ratio coefficients match their internally constructed
mixed original-generator coefficients, without a matching hypothesis. -/
theorem ratioCoefficient_eq (w : Fin (Fintype.card (Index F n)) → (Γ(X, U.1))ˣ)
    (i : Fin (Fintype.card (Index F n))) :
    BranchRatios.coefficient (head F n j₀) (branchGenerator F n A y U v c)
      (auxiliaryGenerator F n A y U v c) w i =
      OriginalMixed.coefficient (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A)
        y U v c (orderedLabel F n A j₀) (BranchRatios.ratioUnit (head F n j₀) w) i := by
  rw [BranchRatios.coefficient, ratioGenerator_eq]
  rfl

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
  (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
  (N : Fin (Fintype.card (Index F n)) → ℕ)
  (w : Fin (Fintype.card (Index F n)) → (Γ(X, U.1))ˣ)
  (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : Γ(X, U.1)))

include het hcinj hN htame in
/-- The WHOLE actual original joined-family ratio source is smooth of the
SAME original dimension. Every complete absent unit-root factor remains. -/
theorem ratio_smoothOfRelativeDimension :
    let _ := f.sectionsAlgebra U.1
    SmoothOfRelativeDimension n (NadelMixedKummer.Dimension.SmoothSourceDimension.structureMap (k := k) N
      (BranchRatios.coefficient (head F n j₀) (branchGenerator F n A y U v c)
        (auxiliaryGenerator F n A y U v c) w)) := by
  let _ := f.sectionsAlgebra U.1
  have heq := funext (ratioCoefficient_eq F n A j₀ y U v c w)
  rw [heq]
  exact OriginalMixed.smoothOfRelativeDimension _ y U v c hcinj (orderedLabel F n A j₀)
    f het N (BranchRatios.ratioUnit (head F n j₀) w) hN htame

end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.Joined
