import EnvelopeProperty.AlgGeom.CurveCartierIdealDegrees
import EnvelopeProperty.AlgGeom.LineSectionZeroIdeal

/-! # Actual dimension decrease for proper closed Cartier cuts -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Order
open Scheme.Modules
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion

theorem properClosed_dimension_drop {X : Type u} [TopologicalSpace X]
    [IrreducibleSpace X] (Z : Closeds X) (hZ : Z ≠ ⊤) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ)) :
    topologicalKrullDim Z ≤ d := by
  let T : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  let m : IrreducibleCloseds Z → IrreducibleCloseds X :=
    IrreducibleCloseds.map Subtype.val continuous_subtype_val
  have hm : StrictMono m := IrreducibleCloseds.map_strictMono_of_isInducing
    IsInducing.subtypeVal
  have hproper (C : IrreducibleCloseds Z) : m C < T := by
    have hsub : (m C : Set X) ⊆ (Z : Set X) :=
      closure_minimal (by rintro x ⟨y, _hy, rfl⟩; exact y.property) Z.isClosed
    refine lt_of_le_of_ne (show m C ≤ T from Set.subset_univ _) ?_
    intro heq
    apply hZ
    apply SetLike.coe_injective
    apply Set.eq_univ_of_univ_subset
    intro x _hx
    apply hsub
    rw [heq]
    trivial
  change (⨆ l : LTSeries (IrreducibleCloseds Z),
    (l.length : WithBot ℕ∞)) ≤ (d : WithBot ℕ∞)
  apply iSup_le
  intro l
  let q := l.map m hm
  let p : LTSeries (IrreducibleCloseds X) := q.snoc T (hproper l.last)
  have hlen := (Order.LTSeries.length_le_krullDim p).trans hdim
  change ((l.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) at hlen
  have hn : l.length + 1 ≤ d + 1 := by exact_mod_cast hlen
  exact_mod_cast Nat.le_of_add_le_add_right hn

theorem sectionZero_dimension_drop {X : Scheme.{u}} [IsIntegral X]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ))
    (A : X.Modules) (hA : IsInvertible A) (s : unitObj X ⟶ A) (hs : s ≠ 0) :
    topologicalKrullDim (LineSectionZeroIdeal.zeroIdeal A hA s).subscheme ≤ d := by
  let I := LineSectionZeroIdeal.zeroIdeal A hA s
  have hI : I.IsInvertible := LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero A hA s hs
  exact properClosed_dimension_drop I.support (CurveCartierIdealDegrees.support_ne_top I hI) d hdim

end EnvelopeProperty.SeshadriAmplenessCriterion
