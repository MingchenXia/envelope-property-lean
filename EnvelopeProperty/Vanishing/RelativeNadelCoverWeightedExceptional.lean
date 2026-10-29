import EnvelopeProperty.Vanishing.NadelRelativePrincipalization
import Hironaka.Resolution.Algebraic.Kol07.ExceptionalMonomial
import Hironaka.Resolution.Algebraic.Kol07.Thm36.CentersOverSupport

/-! # Actual weighted exceptional ideals on the SAME original BP last scheme

Native original exceptional ideals and partial composites determine the
entire weighted ideal. Cartierness and its support inside the literal
original total transform are proved internally; no exceptional family,
comparison, admissibility or support certificate is supplied.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData Scheme.BlowUpSequence
open scoped BigOperators
universe u

namespace EnvelopeProperty.Vanishing.RelativeNadelCoverWeightedExceptional

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [FiniteType f] [IsSeparated f]
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
local notation "S" => NadelRelativePrincipalization.sequence f n I hI

/-- The literal original finite product of powers of the actual original
step exceptional ideals pulled to the SAME original BP last scheme. -/
def weightedIdeal (w : Fin (S).length → ℕ) : (S).last.IdealSheafData :=
  ∏ i, (((S).exceptionalAt i).comap
    ((S).stageMapBetween (Fin.last _) i.succ (Fin.le_last _))) ^ w i

/-- The SAME original weighted exceptional ideal is Cartier, from native
original step Cartierness and actual native later partial composites. -/
theorem weightedIdeal_isInvertible (w : Fin (S).length → ℕ) :
    (weightedIdeal f n I hI w).IsInvertible := by
  unfold weightedIdeal
  refine Finset.prod_induction _
    (fun J : (S).last.IdealSheafData => J.IsInvertible)
    (fun _ _ h₁ h₂ => h₁.mul h₂) (one_eq_top ▸ isInvertible_top) ?_
  intro i _
  exact isInvertible_pow
    (Hironaka.Sequence.isInvertible_comap_stageMapBetween S (Fin.le_last _)
      (Hironaka.Sequence.isInvertible_exceptionalAt S i)) (w i)

/-- Actual positive original integer weights retain exactly the original
union of all step exceptional supports on the SAME original last scheme. -/
theorem weightedIdeal_support_of_positive (w : Fin (S).length → ℕ)
    (hw : ∀ i, 0 < w i) :
    (weightedIdeal f n I hI w).support =
      ⨆ i, (((S).exceptionalAt i).comap
        ((S).stageMapBetween (Fin.last _) i.succ (Fin.le_last _))).support := by
  rw [weightedIdeal, Hironaka.Sequence.support_finset_prod]
  simp only [Finset.mem_univ, iSup_pos]
  apply iSup_congr
  intro i
  exact support_pow _ _ (Nat.ne_of_gt (hw i))

private theorem pulledExceptional_support_le (i : Fin (S).length) :
    (((S).exceptionalAt i).comap
      ((S).stageMapBetween (Fin.last _) i.succ (Fin.le_last _))).support ≤
        (I.comap (S).composite).support := by
  apply SetLike.le_def.mpr
  intro y hy
  have hexc := (mem_support_comap_iff_apply ((S).exceptionalAt i) _ y).mp hy
  have hcenter := (mem_support_exceptionalAt_iff S i _).mp hexc
  have hE : IsEmpty (NadelRelativePrincipalization.originalTriple f n I hI).E.ι := by
    change IsEmpty PEmpty
    infer_instance
  have hsource := Hironaka.Resolution.stageMap_mem_support_of_mem_center_BP
    (NadelRelativePrincipalization.originalTriple f n I hI) hE i hcenter
  have hcomp : (S).stageMapBetween (Fin.last _) i.succ (Fin.le_last _) ≫
      (S).step i ≫ (S).stageMap i.castSucc = (S).composite := by
    rw [← stageMap_succ S i, stageMapBetween_comp_stageMap S (Fin.le_last _)]
    rfl
  apply (mem_support_comap_iff_apply I (S).composite y).mpr
  exact (congrArg (fun a => a y) hcomp) ▸ hsource

/-- The actual weighted exceptional ideal is supported on the literal
original total-transform ideal of the SAME whole original BP composite.
The original BP center-support theorem and all stage triangles are internal. -/
theorem weightedIdeal_support_le_totalTransform (w : Fin (S).length → ℕ) :
    (weightedIdeal f n I hI w).support ≤ (I.comap (S).composite).support := by
  rw [weightedIdeal, Hironaka.Sequence.support_finset_prod]
  refine iSup₂_le fun i _ => ?_
  by_cases hi : w i = 0
  · simp only [hi, pow_zero, one_eq_top, support_top]
    exact bot_le
  · rw [support_pow _ _ hi]
    exact pulledExceptional_support_le f n I hI i

end EnvelopeProperty.Vanishing.RelativeNadelCoverWeightedExceptional
