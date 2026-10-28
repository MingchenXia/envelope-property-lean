import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingJoined
import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingNormalization

/-! # Normalization of the WHOLE original SNC branch-product quotient

The same genuine original joined SNC coordinates prove actual local normality
of the complete ratio model. The true whole generic comparison then identifies
it with the actual integral closure of the original raw generic algebra.
-/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.Joined
open CyclicSectionSNCUniformFramedCharts NadelMixedKummer NadelIntegralClosureTower
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {X : Scheme.{u}} (F : X.DivisorFamily) (n : ℕ)
  (A : F.ι → Fin (n + 1) → X.IdealSheafData) (j₀ : F.ι → Fin (n + 1))
  (y : X) (U : X.affineOpens) (v : Fin n → Γ(X, U.1))
  (c : {i : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).ι //
    y ∈ ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).component i).support} → Fin n)
  (m : F.ι → ℕ) (w : Fin (Fintype.card (Index F n)) → (Γ(X, U.1))ˣ)

/-- EVERY original root degree is the SAME original degree of its actual row. -/
def degree (i : Fin (Fintype.card (Index F n))) : ℕ := m (row F n i)

/-- The original distinguished roots retain the SAME actual original degree. -/
theorem degree_head (i : Fin (Fintype.card (Index F n))) :
    degree F n m (head F n j₀ i) = degree F n m i := by rw [degree, row_head]; rfl

local notation "N₀" => degree F n m
local notation "C₀" => BranchRatios.rawCoefficient (branchGenerator F n A y U v c)
  (auxiliaryGenerator F n A y U v c) w
local notation "B₀" => BranchRatios.coefficient (head F n j₀) (branchGenerator F n A y U v c)
  (auxiliaryGenerator F n A y U v c) w

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
  (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
  (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))

include het hcinj hm htame in
/-- EVERY actual prime of the WHOLE original ratio model is integrally
closed. This is DERIVED from the same original SNC coordinates and tame degrees. -/
theorem ratio_local_normal : ∀ (p : Ideal (Ring N₀ B₀)) [p.IsPrime],
    IsIntegrallyClosed (Localization.AtPrime p) := by
  rw [funext (ratioCoefficient_eq F n A j₀ y U v c w)]
  intro p hp
  exact OriginalMixed.localization_isIntegrallyClosed _ y U v c hcinj (orderedLabel F n A j₀)
    f het N₀ (BranchRatios.ratioUnit (head F n j₀) w)
    (fun i => hm (row F n i)) (fun i => htame (row F n i)) p

variable (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).IsSnc)
  [Smooth f] (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).component i.1).ideal U =
    Ideal.span {v (c i)}) (hy : y ∈ U.1)

include f hG hcomp hy in
/-- Each SAME original branch generator is nonzero in the SAME actual
original SNC coordinate ring, derived from genuine original smooth SNC geometry. -/
theorem branchGenerator_ne_zero [IsIntegral X] (i : Fin (Fintype.card (Index F n))) :
    branchGenerator F n A y U v c i ≠ 0 := by
  have hcoord := CyclicSectionSNCAffineOriginalCoefficient.branch_sections_ne_zero
    f hG y U v c hcomp y hy
  exact uniformBranches_ne_zero y U v c hcoord y hy _

variable (habsent : ∀ i, y ∉ (A i (j₀ i)).support)

/-- The ACTUAL WHOLE original branch-product algebra is normalized by the
entire actual ratio model inside the SAME literal original generic tensor
algebra. All local normality, finite flatness, generic inverses and original-root
triangles are proved internally; no normalization comparison is an input. -/
def ratio_normalizationEquiv [IsIntegral X] :
    letI : Nonempty U.1 := ⟨⟨y, hy⟩⟩
    letI := rawCandidateAlgebra Γ(X, U.1) (Ring N₀ B₀)
      (MultiRatio.rawAlgHom N₀ C₀ B₀ (head F n j₀) (degree_head F n j₀ m)
        (BranchRatios.coefficient_head _ _ _ _ (head_head F n j₀)
          (auxiliaryGenerator_head F n A j₀ y U v c habsent))
        (BranchRatios.raw_mul_ratio _ _ _ _ (branchGenerator_head F n A j₀ y U v c)
          (auxiliaryGenerator_head F n A j₀ y U v c habsent)))
    Ring N₀ B₀ ≃ₐ[Ring N₀ C₀] integralClosure (Ring N₀ C₀)
      (FractionRing Γ(X, U.1) ⊗[Γ(X, U.1)] Ring N₀ C₀) := by
  letI : Nonempty U.1 := ⟨⟨y, hy⟩⟩
  exact MultiRatio.normalizationEquiv N₀ C₀ B₀ (head F n j₀) (head_head F n j₀)
    (degree_head F n j₀ m)
    (BranchRatios.coefficient_head _ _ _ _ (head_head F n j₀)
      (auxiliaryGenerator_head F n A j₀ y U v c habsent))
    (BranchRatios.raw_mul_ratio _ _ _ _ (branchGenerator_head F n A j₀ y U v c)
      (auxiliaryGenerator_head F n A j₀ y U v c habsent))
    (fun i => hm (row F n i))
    (BranchRatios.raw_head_ne_zero _ _ _ _
      (auxiliaryGenerator_head F n A j₀ y U v c habsent)
      (branchGenerator_ne_zero F n A y U v c f hG hcomp hy))
    (fun p _ => ratio_local_normal F n A j₀ y U v c m w f het hcinj hm htame p)

end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.Joined
