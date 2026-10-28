import EnvelopeProperty.Vanishing.DeligneIllusieInput
import EnvelopeProperty.DI.ActualWittGlobalDecomposition

/-! # The actual Witt decomposition supplies the vanishing input

The source and target used by the vanishing argument are the same complexes
as those in the proved global Deligne--Illusie decomposition. The dimension
bound therefore supplies the decomposition without a caller-provided input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u w

namespace EnvelopeProperty.Vanishing.DeligneIllusieInput

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The previously explicit Witt input follows from the actual global
decomposition, for every original smooth separated Witt-two model. -/
theorem provedWittDecompositionInput (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p] : WittDecompositionInput.{u,w} p k := by
  intro _ Xtilde f n _ _ _ hn
  exact ⟨EnvelopeProperty.DI.ActualWittDecomposition.fullDerivedIso p k f n hn⟩

end EnvelopeProperty.Vanishing.DeligneIllusieInput
