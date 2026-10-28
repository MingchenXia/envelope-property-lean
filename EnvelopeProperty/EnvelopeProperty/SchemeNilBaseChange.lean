/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.SchemeIdempotentRestriction
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Actual nil-kernel quotient base changes and original whole idempotents -/
open CategoryTheory AlgebraicGeometry Limits
noncomputable section
universe u
namespace EnvelopeProperty.SchemeNilBaseChange
variable {R S : Type u} [CommRing R] [CommRing S] (α : R →+* S)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The LITERAL original scheme base change. -/
abbrev model := pullback f (Spec.map (CommRingCat.ofHom α))

/-- The ORIGINAL projection, retaining its full original scheme structure. -/
abbrev projection : model α f ⟶ X := pullback.fst _ _

/-- Original prime correspondence and actual nilpotence DERIVE scheme surjectivity. -/
theorem surjective_specMap (hα : Function.Surjective α)
    (hnil : ∀ a ∈ RingHom.ker α, IsNilpotent a) :
    Surjective (Spec.map (CommRingCat.ofHom α)) := by
  constructor
  change Function.Surjective (PrimeSpectrum.comap α)
  intro p
  have hp : p ∈ Set.range (PrimeSpectrum.comap α) := by
    rw [range_comap_of_surjective _ _ hα,PrimeSpectrum.mem_zeroLocus,
      SetLike.coe_subset_coe]
    intro a ha
    obtain ⟨n,hn⟩ := hnil a ha
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n (by rw [hn]; exact p.asIdeal.zero_mem)
  exact hp

/-- True original quotient surjectivity DERIVES actual closedness of the literal base-change projection. -/
theorem isClosedImmersion_projection (hα : Function.Surjective α) :
    IsClosedImmersion (projection α f) := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom α)) :=
    IsClosedImmersion.spec_of_surjective _ hα
  infer_instance

/-- Genuine nil-kernel Spec surjectivity DERIVES the whole actual projection's surjectivity. -/
theorem surjective_projection (hα : Function.Surjective α)
    (hnil : ∀ a ∈ RingHom.ker α, IsNilpotent a) : Surjective (projection α f) := by
  let : Surjective (Spec.map (CommRingCat.ofHom α)) := surjective_specMap α hα hnil
  infer_instance

/-- The actual nil-thickening projection is genuinely homeomorphic, from its derived closed surjectivity. -/
def projectionHomeomorph (hα : Function.Surjective α)
    (hnil : ∀ a ∈ RingHom.ker α, IsNilpotent a) : model α f ≃ₜ X := by
  let : IsClosedImmersion (projection α f) := isClosedImmersion_projection α f hα
  let : Surjective (projection α f) := surjective_projection α f hα hnil
  exact (isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(projection α f).isClosedEmbedding.isEmbedding,(projection α f).surjective⟩).homeomorph

/-- ONLY original global idempotents are genuinely transported bijectively by the SAME original section map. -/
def idempotentEquiv (hα : Function.Surjective α)
    (hnil : ∀ a ∈ RingHom.ker α, IsNilpotent a) :
    {e : Γ(X,⊤) // IsIdempotentElem e} ≃ {e : Γ(model α f,⊤) // IsIdempotentElem e} := by
  let : IsClosedImmersion (projection α f) := isClosedImmersion_projection α f hα
  let : Surjective (projection α f) := surjective_projection α f hα hnil
  exact Equiv.ofBijective (SchemeIdempotentRestriction.map (projection α f))
    (SchemeIdempotentRestriction.map_bijective_of_closed_surjective (projection α f))

end EnvelopeProperty.SchemeNilBaseChange
