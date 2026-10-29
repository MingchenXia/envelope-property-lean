import EnvelopeProperty.Vanishing.RelativeNadelCoverWeightedExceptional
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitSupport
import Hironaka.Resolution.Algebraic.Snc.MonomialComponents
import Hironaka.Resolution.Algebraic.Snc.SncInvertible

/-! # One actual SNC family for the SAME original F and weighted exceptional E

The literal original total-transform ideal and the actual original weighted
exceptional ideal acquire one internally produced native component family.
Both coefficient families are their native orders; no factorization or
coefficient-matching certificate is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData
open scoped BigOperators
universe u

namespace EnvelopeProperty.Vanishing.RelativeNadelCoverWeightedExceptionalSnc
open RelativeNadelCoverWeightedExceptional

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem product_support_le_family {Y : Scheme.{u}} (F : Y.DivisorFamily)
    (b : F.ι → ℕ) : (∏ i, F.component i ^ b i).support ≤ F.support := by
  rw [Hironaka.Sequence.support_finset_prod]
  refine iSup₂_le fun i _ => ?_
  by_cases hi : b i = 0
  · simp only [hi, pow_zero, one_eq_top, support_top]
    exact bot_le
  · rw [support_pow _ _ hi]
    exact le_iSup (fun j => (F.component j).support) i

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [FiniteType f] [IsSeparated f]
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
local notation "S" => NadelRelativePrincipalization.sequence f n I hI

/-- The literal original whole total-transform ideal and SAME actual weighted
exceptional ideal have one internally produced native SNC component family.
The actual family and both native-order coefficient families are outputs. -/
theorem exists_common_snc_presentation (w : Fin (S).length → ℕ) :
    ∃ (F : (S).last.DivisorFamily) (b e : F.ι → ℕ), F.IsSnc ∧
      I.comap (S).composite = ∏ i, F.component i ^ b i ∧
      weightedIdeal f n I hI w = ∏ i, F.component i ^ e i := by
  let Y := (S).last
  let g := (S).composite ≫ f
  let J := I.comap (S).composite
  let K := weightedIdeal f n I hI w
  let : SmoothOfRelativeDimension n g :=
    NadelRelativePrincipalization.stage_smoothOfRelativeDimension f n I hI (Fin.last _)
  let : Smooth g := SmoothOfRelativeDimension.smooth n g
  let : IsProper (S).composite := NadelRelativePrincipalization.composite_isProper f n I hI
  let : FiniteType g := inferInstance
  let : IsLocallyNoetherian Y := g.isLocallyNoetherian_of_field
  let : CompactSpace Y := (quasiCompact_iff_compactSpace g).mp inferInstance
  let : IsNoetherian Y := ⟨⟩
  let : NoetherianSpace Y := inferInstance
  have hJsnc : J.IsIdealOfSncDivisor :=
    NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI
  have hJ : J.IsInvertible := hJsnc.isInvertible g
  have hK : K.IsInvertible := weightedIdeal_isInvertible f n I hI w
  obtain ⟨F, b, hF, hJF⟩ := hJsnc
  have hJFsupport : J.support ≤ F.support := by
    rw [hJF]
    exact product_support_le_family F b
  have hKFsupport : K.support ≤ F.support :=
    (weightedIdeal_support_le_totalTransform f n I hI w).trans hJFsupport
  have hJmono : J = F.monomial (fun η => (J.ord η).toNat) :=
    (Hironaka.BMO.Snc.eq_monomialPart_of_isInvertible_of_support_le g F hF hJ hJFsupport).trans
      (Hironaka.BMO.monomialPart_eq_monomial J F)
  have hKmono : K = F.monomial (fun η => (K.ord η).toNat) :=
    (Hironaka.BMO.Snc.eq_monomialPart_of_isInvertible_of_support_le g F hF hK hKFsupport).trans
      (Hironaka.BMO.monomialPart_eq_monomial K F)
  refine ⟨F.components, (fun p => (J.ord (ofLex p).2.1).toNat),
    (fun p => (K.ord (ofLex p).2.1).toNat), Hironaka.Snc.isSnc_components hF, ?_, ?_⟩
  · exact hJmono.trans (F.monomial_eq_prod_components (fun η => (J.ord η).toNat))
  · exact hKmono.trans (F.monomial_eq_prod_components (fun η => (K.ord η).toNat))

end EnvelopeProperty.Vanishing.RelativeNadelCoverWeightedExceptionalSnc
