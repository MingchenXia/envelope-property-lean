/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.SchemeGroupActionFlat
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Actual schematic dominance on the whole flat product

The whole original product morphism is a genuine base change. This is the
scheme-image equivariance prerequisite; no invariant-image certificate is assumed.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory
noncomputable section
universe u
namespace EnvelopeProperty.SchemeFlatProductDominance

variable {S : Scheme.{u}} (G : Over S) {A B : Over S} (f : A ⟶ B)

/-- The actual whole product map is the original flat-base-change square. -/
theorem isPullback_whiskerLeft :
    IsPullback (G ◁ f).left (pullback.snd G.hom A.hom)
      (pullback.snd G.hom B.hom) f.left := by
  have h : IsPullback ((G ◁ f).left ≫ pullback.fst G.hom B.hom)
      (pullback.snd G.hom A.hom) G.hom (f.left ≫ B.hom) := by
    simpa only [Over.whiskerLeft_left_fst, f.w] using
      (IsPullback.of_hasPullback G.hom A.hom)
  exact h.of_right (Over.whiskerLeft_left_snd f) (IsPullback.of_hasPullback G.hom B.hom)

/-- Schematic dominance survives the SAME whole product with the actual flat group/base. -/
theorem isSchemeTheoreticallyDominant_whiskerLeft [Flat G.hom]
    [IsSchemeTheoreticallyDominant f.left] [QuasiCompact f.left] :
    IsSchemeTheoreticallyDominant (G ◁ f).left := by
  exact IsSchemeTheoreticallyDominant.of_isPullback (isPullback_whiskerLeft G f).flip

end EnvelopeProperty.SchemeFlatProductDominance
