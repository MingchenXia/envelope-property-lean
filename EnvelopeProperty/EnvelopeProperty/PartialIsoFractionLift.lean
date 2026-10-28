/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.RingTheory.Localization.FractionRing

/-! # Actual whole fraction-field inverse from genuine dense-open birational data -/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty
variable {A K : Type u} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

set_option backward.isDefEq.respectTransparency false in
/-- EVERY original fraction-field point lies in an actual dense base open, by genuine density and field uniqueness. -/
theorem fractionSpec_range_subset_denseOpen (U : (Spec (CommRingCat.of A)).Opens)
    (hU : Dense (U : Set (Spec (CommRingCat.of A)))) :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap A K))) ⊆ U := by
  have hd : DenseRange (PrimeSpectrum.comap (algebraMap A K)) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective A K)]
      exact bot_le)
  obtain ⟨q, hq⟩ := hd.exists_mem_open U.isOpen hU.nonempty
  rintro _ ⟨z, rfl⟩
  change PrimeSpectrum.comap (algebraMap A K) z ∈ U
  rw [Subsingleton.elim z q]
  exact hq

namespace PartialIso
variable {Y : Scheme.{u}} (e : Scheme.PartialIso Y (Spec (CommRingCat.of A)))

/-- The genuine partial inverse defines an ACTUAL whole generic scheme map, without a generic inverse certificate. -/
def fractionLift : Spec (CommRingCat.of K) ⟶ Y :=
  IsOpenImmersion.lift e.target.ι (Spec.map (CommRingCat.ofHom (algebraMap A K)))
    (by rw [Scheme.Opens.range_ι]; exact fractionSpec_range_subset_denseOpen e.target e.dense_target) ≫
      e.iso.inv ≫ e.source.ι

/-- Actual OVER compatibility retains the ENTIRE original generic coefficient triangle. -/
theorem fractionLift_comp (f : Y ⟶ Spec (CommRingCat.of A))
    (he : e.IsOver f (𝟙 (Spec (CommRingCat.of A)))) :
    fractionLift (K := K) e ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A K)) := by
  change e.iso.hom ≫ e.target.ι ≫ 𝟙 _ = e.source.ι ≫ f at he
  have hs : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι := by
    simpa only [Category.comp_id] using (Eq.symm he)
  simp only [fractionLift, Category.assoc, hs, Iso.inv_hom_id_assoc]
  exact IsOpenImmersion.lift_fac _ _ _

end PartialIso
end EnvelopeProperty
