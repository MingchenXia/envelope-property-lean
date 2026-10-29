/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Projective.HomogeneousQuotient
import EnvelopeProperty.Alterations.Geometry.ProjIntegral

/-!
# Integrality of original homogeneous quotient kernel subschemes

The existing integral-Proj producer applies to the actual domain quotient.
The genuine closed immersion's original image isomorphism then gives the
integrality of its literal kernel subscheme. No saturation or reduced-support
replacement and no field or Noetherian assumption is used.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace EnvelopeProperty.GradedQuotient

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- A relevant original homogeneous prime quotient has an integral actual
projective kernel subscheme, with its unchanged structure sheaf. -/
theorem isIntegral_quotientKernelSubscheme
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (J : HomogeneousIdeal 𝒜)
    [J.toIdeal.IsPrime] {d : ℕ} {a : A} (hd : 0 < d) (ha : a ∈ 𝒜 d)
    (haJ : a ∉ J.toIdeal) : IsIntegral (quotientSchemeMap 𝒜 J).ker.subscheme := by
  have hirr : HomogeneousIdeal.irrelevant (grading 𝒜 J.toIdeal) ≠ ⊥ := by
    intro h
    have hm := HomogeneousIdeal.mem_irrelevant_of_mem (grading 𝒜 J.toIdeal)
      hd ((gradedMk 𝒜 J.toIdeal).map_mem ha)
    rw [h] at hm
    have hz : Ideal.Quotient.mk J.toIdeal a = 0 := hm
    exact haJ (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  let : IsIntegral (Proj (grading 𝒜 J.toIdeal)) :=
    Alterations.Geometry.ProjIntegral.isIntegral_proj _ hirr
  exact IsIntegral.of_isIso (quotientSchemeMap 𝒜 J).toImage

end EnvelopeProperty.GradedQuotient
