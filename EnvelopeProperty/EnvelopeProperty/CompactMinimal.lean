/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Zorn

open Set
noncomputable section
namespace EnvelopeProperty

/-- Every genuine nonempty compact set in a space with closed order has an actual minimal element. -/
theorem exists_minimal_mem_of_isCompact {X : Type*} [TopologicalSpace X] [Preorder X]
    [OrderClosedTopology X] {s : Set X} (hs : IsCompact s) (hne : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, y ≤ x → x ≤ y := by
  classical
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let : Nonempty (OrderDual s) := hne.to_subtype
  obtain ⟨m, hm⟩ := zorn_le_nonempty (α := OrderDual s) fun c hc hcn => by
    let : Nonempty c := hcn.to_subtype
    let D : c → Set s := fun h => {g | g ≤ (show s from h.1)}
    have hdir : Directed (· ⊇ ·) D := by
      intro i j
      rcases hc.total i.2 j.2 with hij | hji
      · refine ⟨j, ?_, subset_rfl⟩
        exact fun g hg => hg.trans hij
      · refine ⟨i, subset_rfl, ?_⟩
        exact fun g hg => hg.trans hji
    have hn : ∀ i, (D i).Nonempty := fun i => ⟨i.1, le_rfl⟩
    have hclosed : ∀ i, IsClosed (D i) := fun i => isClosed_le continuous_id continuous_const
    obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      D hdir hn (fun i => (hclosed i).isCompact) hclosed
    refine ⟨(show OrderDual s from b), ?_⟩
    intro j hj
    exact Set.mem_iInter.mp hb ⟨j, hj⟩
  refine ⟨m.1, m.2, ?_⟩
  intro y hy hym
  have hy' : m ≤ (⟨y, hy⟩ : OrderDual s) := hym
  exact hm hy'

end EnvelopeProperty
