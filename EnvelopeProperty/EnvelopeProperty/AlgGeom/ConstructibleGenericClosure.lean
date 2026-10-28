import Mathlib.Topology.Constructible
import Mathlib.Topology.Sober

/-! # Constructible sets retain generic points under closure

At a generic point of the whole space, every constructible set is locally
constant as a membership predicate. Consequently taking closure cannot
introduce that generic point. No properness or Noetherian hypothesis is
needed for this topological statement.
-/
namespace EnvelopeProperty.ConstructibleGenericClosure
open Set TopologicalSpace Topology
universe u
set_option autoImplicit false

variable {T : Type u} [TopologicalSpace T]

/-- A constructible membership predicate is constant on some original
open neighborhood of the original whole-space generic point. -/
theorem exists_open_deciding (η : T) (hη : IsGenericPoint η (univ : Set T))
    {s : Set T} (hs : IsConstructible s) :
    ∃ U : Set T, IsOpen U ∧ η ∈ U ∧ ∀ x ∈ U, (x ∈ s ↔ η ∈ s) := by
  classical
  refine IsConstructible.empty_union_induction
    (p := fun s _ => ∃ U : Set T, IsOpen U ∧ η ∈ U ∧
      ∀ x ∈ U, (x ∈ s ↔ η ∈ s)) ?_ ?_ ?_ hs
  · intro U hU _hretro
    by_cases hηU : η ∈ U
    · exact ⟨U, hU, hηU, fun x hx => ⟨fun _ => hηU, fun _ => hx⟩⟩
    · refine ⟨univ, isOpen_univ, mem_univ η, fun x _ => ?_⟩
      exact iff_of_false
        (fun hx => hηU ((hη.specializes (mem_univ x)).mem_open hU hx)) hηU
  · intro s _hs t _ht ihs iht
    obtain ⟨U, hU, hηU, hUs⟩ := ihs
    obtain ⟨V, hV, hηV, hVt⟩ := iht
    refine ⟨U ∩ V, hU.inter hV, ⟨hηU, hηV⟩, fun x hx => ?_⟩
    exact or_congr (hUs x hx.1) (hVt x hx.2)
  · intro s _hs ih
    obtain ⟨U, hU, hηU, hUs⟩ := ih
    exact ⟨U, hU, hηU, fun x hx => not_congr (hUs x hx)⟩

/-- Closure adds no whole-space generic point to a constructible set. -/
theorem mem_closure_iff_of_constructible (η : T)
    (hη : IsGenericPoint η (univ : Set T)) {s : Set T} (hs : IsConstructible s) :
    η ∈ closure s ↔ η ∈ s := by
  refine ⟨fun h => ?_, fun h => subset_closure h⟩
  obtain ⟨U, hU, hηU, hUs⟩ := exists_open_deciding η hη hs
  obtain ⟨x, hxU, hxs⟩ := mem_closure_iff.mp h U hU hηU
  exact (hUs x hxU).mp hxs

/-- The same statement for the canonical generic point of the original space. -/
theorem genericPoint_mem_closure_iff [QuasiSober T] [IrreducibleSpace T]
    {s : Set T} (hs : IsConstructible s) :
    genericPoint T ∈ closure s ↔ genericPoint T ∈ s :=
  mem_closure_iff_of_constructible (genericPoint T) (genericPoint_spec T) hs

/-- Avoiding a constructible set at the actual generic point gives an
actual open neighborhood avoiding its entire original set. -/
theorem exists_open_avoiding (η : T) (hη : IsGenericPoint η (univ : Set T))
    {s : Set T} (hs : IsConstructible s) (hnot : η ∉ s) :
    ∃ U : Opens T, η ∈ U ∧ ∀ x ∈ U, x ∉ s := by
  refine ⟨⟨(closure s)ᶜ, isClosed_closure.isOpen_compl⟩, ?_, ?_⟩
  · exact fun h => hnot ((mem_closure_iff_of_constructible η hη hs).mp h)
  · intro x hx hxs
    exact hx (subset_closure hxs)

end EnvelopeProperty.ConstructibleGenericClosure
