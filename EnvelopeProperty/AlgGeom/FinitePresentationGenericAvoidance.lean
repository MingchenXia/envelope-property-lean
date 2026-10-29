import EnvelopeProperty.AlgGeom.ConstructibleGenericClosure
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Topology.NoetherianSpace

/-! # Actual generic avoidance for nonproper finite-presentation maps

Chevalley's theorem supplies the actual constructible image. Taking its
closure then gives a genuine open avoiding the entire bad set. No proper
map, closed-image certificate or supplied target open is used.
-/
namespace EnvelopeProperty.FinitePresentationGenericAvoidance
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set
universe u
set_option autoImplicit false

variable {X Y : Scheme.{u}}

/-- The actual complement of the closure of the actual whole bad image. -/
def avoidingOpen (f : X ⟶ Y) (s : Set X) : Y.Opens :=
  ⟨(closure (f '' s))ᶜ, isClosed_closure.isOpen_compl⟩

/-- Every point over the actual avoiding open avoids the original bad set. -/
theorem preimage_avoidingOpen_le_compl (f : X ⟶ Y) (s : Set X) :
    (f ⁻¹ᵁ avoidingOpen f s : Set X) ⊆ sᶜ := by
  intro x hx hxs
  exact hx (subset_closure ⟨x, hxs, rfl⟩)

/-- The actual generic point belongs to this open if the original locally
constructible bad set has no point over it. Chevalley is internal. -/
theorem genericPoint_mem_avoidingOpen [IsIntegral Y] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
    (s : Set X) (hs : IsLocallyConstructible s) (hη : genericPoint Y ∉ f '' s) :
    genericPoint Y ∈ avoidingOpen f s := by
  have hImage : IsConstructible (f '' s) :=
    (f.isLocallyConstructible_image hs).isConstructible
  exact fun h => hη ((ConstructibleGenericClosure.genericPoint_mem_closure_iff hImage).mp h)

/-- A closed bad set in an original Noetherian source is constructible,
without using properness of any morphism. -/
theorem isLocallyConstructible_of_isClosed [NoetherianSpace X]
    (s : Set X) (hs : IsClosed s) : IsLocallyConstructible s := by
  have hr : IsRetrocompact sᶜ := fun _U _hcompact _hopen =>
    NoetherianSpace.isCompact _
  simpa only [compl_compl] using
    (hr.isConstructible hs.isOpen_compl).compl.isLocallyConstructible

/-- Original finite-presentation geometry and generic avoidance internally
produce a nonempty dense target open avoiding an entire original CLOSED
bad set, even when the original map is not proper. -/
theorem exists_dense_open_avoiding_closed [IsIntegral Y] [IsAffine Y]
    [NoetherianSpace X] (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f]
    (s : Set X) (hs : IsClosed s) (hη : genericPoint Y ∉ f '' s) :
    ∃ U : Y.Opens, genericPoint Y ∈ U ∧ Nonempty U ∧ Dense (U : Set Y) ∧
      (f ⁻¹ᵁ U : Set X) ⊆ sᶜ := by
  let U := avoidingOpen f s
  have hmem : genericPoint Y ∈ U := genericPoint_mem_avoidingOpen f s
    (isLocallyConstructible_of_isClosed s hs) hη
  exact ⟨U, hmem, ⟨⟨genericPoint Y, hmem⟩⟩,
    U.isOpen.dense ⟨genericPoint Y, hmem⟩, preimage_avoidingOpen_le_compl f s⟩

end EnvelopeProperty.FinitePresentationGenericAvoidance
