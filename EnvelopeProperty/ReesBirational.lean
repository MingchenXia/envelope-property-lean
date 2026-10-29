/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.ReesGoodOpenDensity
import Mathlib.AlgebraicGeometry.Birational.Birational

/-! # Genuine whole Rees birational data over a regular ORIGINAL generator -/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.ReesPresentation
variable {A ι : Type u} [CommRing A] (g : ι → A)

private local instance baseOpenImmersion (j : ι) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (g j))))) :=
  IsOpenImmersion.of_isLocalization (g j)

/-- ORIGINAL regularity and actual whole good-open ranges construct the genuine dense-open inverse data. -/
def generatorPartialIso (j : ι) (hj : g j ∈ nonZeroDivisors A) :
    Scheme.PartialIso (Scheme g) (Spec (CommRingCat.of A)) where
  source := (goodOpenLift g j).opensRange
  dense_source := by
    change Dense (Set.range (goodOpenLift g j))
    rw [range_goodOpenLift]
    exact dense_projection_preimage_basicOpen g j hj
  target := (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (g j))))).opensRange
  dense_target := by
    change Dense (Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away (g j)))))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (g j)) (g j)]
    exact dense_basicOpen_of_mem_nonZeroDivisors (g j) hj
  iso := (goodOpenLift g j).isoOpensRange.symm ≪≫
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (g j))))).isoOpensRange

/-- The constructed actual birational record retains the ENTIRE original coefficient projection triangle. -/
theorem generatorPartialIso_isOver (j : ι) (hj : g j ∈ nonZeroDivisors A) :
    (generatorPartialIso g j hj).IsOver (projection g) (𝟙 (Spec (CommRingCat.of A))) := by
  change ((goodOpenLift g j).isoOpensRange.inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (g j))))).isoOpensRange.hom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (g j))))).opensRange.ι ≫
        𝟙 _ = (goodOpenLift g j).opensRange.ι ≫ projection g
  simp only [Category.comp_id, Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  rw [← goodOpenLift_comp_projection g j, ← Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp]

/-- Genuine dense-open data proves actual over-base birationality with no supplied birational certificate. -/
theorem birationalOver_projection (j : ι) (hj : g j ∈ nonZeroDivisors A) :
    Scheme.BirationalOver (projection g) (𝟙 (Spec (CommRingCat.of A))) :=
  ⟨generatorPartialIso g j hj, generatorPartialIso_isOver g j hj⟩

end EnvelopeProperty.ReesPresentation
