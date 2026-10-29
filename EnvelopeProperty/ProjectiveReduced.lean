/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Genuine reducedness of original graded Proj schemes -/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty

set_option backward.isDefEq.respectTransparency false in
/-- Every genuinely reduced graded ring has an actually reduced ORIGINAL Proj scheme. -/
theorem proj_isReduced {R σ : Type u} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] [_root_.IsReduced R] : IsReduced (Proj 𝒜) := by
  apply +allowSynthFailures isReduced_of_isReduced_stalk
  intro x
  let S := x.asHomogeneousIdeal.toIdeal.primeCompl
  let : _root_.IsReduced (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
    isReduced_of_injective
      (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S))
      (HomogeneousLocalization.val_injective S)
  exact isReduced_of_injective (Proj.stalkIso 𝒜 x).hom.hom
    (Proj.stalkIso 𝒜 x).commRingCatIsoToRingEquiv.injective

end EnvelopeProperty
