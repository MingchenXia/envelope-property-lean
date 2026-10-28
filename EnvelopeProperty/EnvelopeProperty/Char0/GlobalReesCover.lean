/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.HironakaReesCover
import EnvelopeProperty.Char0.AffineBlowupComparison
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finite Rees covers of actual affine scheme blowups

An arbitrary actual ideal sheaf on a spectrum is normalized to its actual ring ideal. Its
finite ratio charts are then an actual affine cover of its scheme blowup, with the correct
structure morphisms. Nonzero finite generators are produced from Noetherianity and an actual
point of the blowup, rather than assumed as a chart-existence certificate.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory
open scoped Classical

universe u

/-- Noetherianity gives finite generators, and an actual blowup point forces a nonzero member. -/
theorem exists_finite_generators_of_blowUp_point {R : Type u} [CommRing R]
    [IsNoetherianRing R] (J : (Spec (.of R)).IdealSheafData) (p : J.blowUp) :
    ∃ (n : ℕ) (g : Fin n → R), Ideal.span (Set.range g) = idealOfSpecSheaf J ∧
      ∃ i, g i ≠ 0 := by
  have hfg : (idealOfSpecSheaf J).FG := IsNoetherian.noetherian _
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  refine ⟨n, g, hg, ?_⟩
  by_contra hzero
  push Not at hzero
  apply idealOfSpecSheaf_ne_bot_of_blowUp_point J p
  rw [← hg]
  apply Ideal.span_eq_bot.mpr
  rintro _ ⟨i, rfl⟩
  exact hzero i

/-- A finite generating family presents the actual scheme blowup without changing its centre. -/
theorem exists_affineBlowUp_center_iso_of_span {R : Type u} [CommRing R]
    (J : (Spec (.of R)).IdealSheafData) {n : ℕ} (g : Fin n → R)
    (hg : Ideal.span (Set.range g) = idealOfSpecSheaf J) :
    ∃ e : affineBlowUp (Ideal.span (Set.range g)) ≅ J.blowUp,
      e.hom ≫ J.blowUpπ = affineBlowUp.π (Ideal.span (Set.range g)) := by
  have hJ : specIdealSheaf (Ideal.span (Set.range g)) = J := by
    rw [hg]
    exact specIdealSheaf_idealOfSpecSheaf J
  have hglobal : IsBlowUp (specIdealSheaf (Ideal.span (Set.range g))) J.blowUpπ := by
    rw [hJ]
    exact Scheme.IdealSheafData.blowUp.isBlowUp J
  exact exists_iso_of_isBlowUp (affineBlowUp_isBlowUp _) hglobal

/-- Transport actual affine chart maps through an actual isomorphism on their target. -/
def affineOpenCoverTransportIso {X Y : Scheme.{u}} (𝒰 : X.AffineOpenCover) (e : X ≅ Y) :
    Y.AffineOpenCover where
  I₀ := 𝒰.I₀
  X := 𝒰.X
  f i := 𝒰.f i ≫ e.hom
  idx y := 𝒰.idx (e.inv y)
  covers y := by
    obtain ⟨p, hp⟩ := 𝒰.covers (e.inv y)
    refine ⟨p, ?_⟩
    rw [Scheme.Hom.comp_apply, hp]
    exact congrArg (fun φ : Y ⟶ Y => φ y) e.inv_hom_id

/-- Transporting the target preserves finiteness of the cover's index set. -/
instance finite_affineOpenCoverTransportIso_index {X Y : Scheme.{u}}
    (𝒰 : X.AffineOpenCover) [Finite 𝒰.I₀] (e : X ≅ Y) :
    Finite (affineOpenCoverTransportIso 𝒰 e).I₀ := by
  change Finite 𝒰.I₀
  infer_instance

variable {B K : Type u} [CommRing B] [Field K] [Algebra B K]

/-- The actual global blowup is identified internally with the generated affine Rees blowup. -/
def globalReesBlowUpIso (C : Subalgebra B K) (J : (Spec (.of C)).IdealSheafData)
    {n : ℕ} (g : Fin n → C) (hg : Ideal.span (Set.range g) = idealOfSpecSheaf J) :
    affineBlowUp (Ideal.span (Set.range g)) ≅ J.blowUp :=
  (exists_affineBlowUp_center_iso_of_span J g hg).choose

/-- The internally produced comparison identifies the actual projections. -/
theorem globalReesBlowUpIso_hom_π (C : Subalgebra B K)
    (J : (Spec (.of C)).IdealSheafData) {n : ℕ} (g : Fin n → C)
    (hg : Ideal.span (Set.range g) = idealOfSpecSheaf J) :
    (globalReesBlowUpIso C J g hg).hom ≫ J.blowUpπ =
      affineBlowUp.π (Ideal.span (Set.range g)) :=
  (exists_affineBlowUp_center_iso_of_span J g hg).choose_spec

/-- An actual ratio chart on the global scheme blowup. -/
def globalReesBlowUpChart (C : Subalgebra B K) (J : (Spec (.of C)).IdealSheafData)
    {n : ℕ} (g : Fin n → C) (hg : Ideal.span (Set.range g) = idealOfSpecSheaf J)
    (i : Fin n) (hi : g i ≠ 0) : Spec (.of (reesTreeChart C g i)) ⟶ J.blowUp :=
  reesAffineBlowUpChart C g i hi ≫ (globalReesBlowUpIso C J g hg).hom

/-- The actual global ratio charts are open immersions. -/
instance isOpenImmersion_globalReesBlowUpChart (C : Subalgebra B K)
    (J : (Spec (.of C)).IdealSheafData) {n : ℕ} (g : Fin n → C)
    (hg : Ideal.span (Set.range g) = idealOfSpecSheaf J) (i : Fin n) (hi : g i ≠ 0) :
    IsOpenImmersion (globalReesBlowUpChart C J g hg i hi) := by
  unfold globalReesBlowUpChart
  infer_instance

/-- Each global ratio chart maps to the original spectrum by the actual algebra inclusion. -/
theorem globalReesBlowUpChart_π (C : Subalgebra B K) (J : (Spec (.of C)).IdealSheafData)
    {n : ℕ} (g : Fin n → C) (hg : Ideal.span (Set.range g) = idealOfSpecSheaf J)
    (i : Fin n) (hi : g i ≠ 0) :
    globalReesBlowUpChart C J g hg i hi ≫ J.blowUpπ =
      Spec.map (CommRingCat.ofHom (reesTreeChartIncl C g i).toRingHom) := by
  rw [globalReesBlowUpChart, Category.assoc, globalReesBlowUpIso_hom_π,
    reesAffineBlowUpChart_π]

/-- The actual global scheme blowup has the actual finite nonzero ratio-chart cover. -/
def globalReesBlowUpOpenCover (C : Subalgebra B K) (J : (Spec (.of C)).IdealSheafData)
    {n : ℕ} (g : Fin n → C) (hg : Ideal.span (Set.range g) = idealOfSpecSheaf J) :
    J.blowUp.AffineOpenCover :=
  affineOpenCoverTransportIso (reesAffineBlowUpOpenCover C g) (globalReesBlowUpIso C J g hg)

/-- Its chart maps are exactly the global ratio charts above. -/
theorem globalReesBlowUpOpenCover_f (C : Subalgebra B K)
    (J : (Spec (.of C)).IdealSheafData) {n : ℕ} (g : Fin n → C)
    (hg : Ideal.span (Set.range g) = idealOfSpecSheaf J) (i : {i : Fin n // g i ≠ 0}) :
    (globalReesBlowUpOpenCover C J g hg).f i = globalReesBlowUpChart C J g hg i.1 i.2 := rfl

/-- The global scheme comparison preserves the finite nonzero generator index set. -/
instance finite_globalReesBlowUpOpenCover_index (C : Subalgebra B K)
    (J : (Spec (.of C)).IdealSheafData) {n : ℕ} (g : Fin n → C)
    (hg : Ideal.span (Set.range g) = idealOfSpecSheaf J) :
    Finite (globalReesBlowUpOpenCover C J g hg).I₀ := by
  change Finite {i : Fin n // g i ≠ 0}
  infer_instance

end EnvelopeProperty.Char0
