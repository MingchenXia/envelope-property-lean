/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.PartialIsoFractionLift

/-! # Density of the genuine fraction-field inverse of actual partial isomorphisms -/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty
variable {A K : Type u} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
namespace PartialIso
variable {Y : AlgebraicGeometry.Scheme.{u}}

/-- ACTUAL dense partial-isomorphism opens derive density of the whole constructed generic inverse. -/
theorem denseRange_fractionLift (e : Scheme.PartialIso Y (Spec (CommRingCat.of A))) :
    DenseRange (fractionLift (K := K) e) := by
  let l := IsOpenImmersion.lift e.target.ι (Spec.map (CommRingCat.ofHom (algebraMap A K)))
    (by rw [Scheme.Opens.range_ι]; exact fractionSpec_range_subset_denseOpen e.target e.dense_target)
  have hl : l ≫ e.target.ι = Spec.map (CommRingCat.ofHom (algebraMap A K)) :=
    IsOpenImmersion.lift_fac _ _ _
  have hd : DenseRange (Spec.map (CommRingCat.ofHom (algebraMap A K))) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr (by
      change RingHom.ker (algebraMap A K) ≤ nilradical A
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective A K)]
      exact bot_le)
  have hld : DenseRange l := by
    change Dense (Set.range l)
    apply e.target.ι.isOpenEmbedding.isInducing.dense_iff.mpr
    intro x
    rw [← Set.range_comp]
    change e.target.ι x ∈ closure (Set.range (l ≫ e.target.ι))
    rw [hl, hd.closure_range]
    trivial
  have hs : DenseRange e.source.ι := by
    change DenseRange ((↑) : e.source → Y)
    exact e.dense_source.denseRange_val
  exact hs.comp (e.iso.inv.denseRange.comp hld e.iso.inv.continuous) e.source.ι.continuous

end PartialIso

end EnvelopeProperty
